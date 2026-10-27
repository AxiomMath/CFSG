module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma411
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

variable {G : Type} [Group G]

theorem comm_of_mem_conjugate {X : Subgroup G} {b y : G} (hyb : y * b = b * y)
    (hX : ∀ x ∈ X, x * y = y * x) {x : G} (hx : x ∈ conjugate X b) : x * y = y * x := by
  rw [conjugate, Subgroup.mem_map] at hx
  obtain ⟨x, hx, rfl⟩ := hx
  have hyb' : b⁻¹ * y = y * b⁻¹ := by
    calc b⁻¹ * y = b⁻¹ * (y * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * y) * b⁻¹ := by rw [hyb]
      _ = y * b⁻¹ := by group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc b⁻¹ * x * b * y = b⁻¹ * x * (b * y) := by group
    _ = b⁻¹ * x * (y * b) := by rw [hyb]
    _ = b⁻¹ * (x * y) * b := by group
    _ = b⁻¹ * (y * x) * b := by rw [hX x hx]
    _ = (b⁻¹ * y) * x * b := by group
    _ = (y * b⁻¹) * x * b := by rw [hyb']
    _ = y * (b⁻¹ * x * b) := by group

theorem conjugate_conjugate_self (M : Subgroup G) {b : G} (hb : b * b = 1) :
    conjugate (conjugate M b) b = M := by
  rw [LocalCores.conjugate_conjugate, hb, conjugate]
  convert Subgroup.map_id M
  ext x
  simp

theorem mem_conjugate_of_comm {M : Subgroup G} {b x : G} (hx : x ∈ M) (hxb : x * b = b * x) :
    x ∈ conjugate M b := by
  rw [conjugate, Subgroup.mem_map]
  refine ⟨x, hx, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc b⁻¹ * x * b = b⁻¹ * (x * b) := by group
    _ = b⁻¹ * (b * x) := by rw [hxb]
    _ = x := by group

variable [Finite G]

theorem map_conj_sup_eq {M : Subgroup G} (hM : IsComponent M) {b y : G} (hb : b * b = 1)
    (hyb : y * b = b * y) {K : Subgroup G} (hKI : K ≤ M ⊔ conjugate M b) (hyK : y ∈ K)
    (hyc : ∃ k ∈ K, k * y ≠ y * k) {v : G} (hv : v * y = y * v) :
    (M ⊔ conjugate M b).map (MulAut.conj v).toMonoidHom = M ⊔ conjugate M b := by
  set M' := conjugate M b with hM'def
  have hM' : IsComponent M' := LocalCores.isComponent_map_mulEquiv (MulAut.conj b⁻¹) hM
  have hMv : IsComponent (M.map (MulAut.conj v).toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv (MulAut.conj v) hM
  have hM'v : IsComponent (M'.map (MulAut.conj v).toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv (MulAut.conj v) hM'
  set U := (M ⊔ M').map (MulAut.conj v).toMonoidHom with hUdef
  have hUeq : U = M.map (MulAut.conj v).toMonoidHom ⊔ M'.map (MulAut.conj v).toMonoidHom :=
    Subgroup.map_sup _ _ _
  have hyU : y ∈ U := by
    refine ⟨y, hKI hyK, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hv, mul_inv_cancel_right]
  have hcommU : ∀ X : Subgroup G, IsComponent X → X ≠ M.map (MulAut.conj v).toMonoidHom →
      X ≠ M'.map (MulAut.conj v).toMonoidHom → ∀ x ∈ X, x * y = y * x := by
    intro X hX h1 h2 x hx
    have hc1 := (LocalCores.distinct_components_commute hX hMv).resolve_left h1
    have hc2 := (LocalCores.distinct_components_commute hX hM'v).resolve_left h2
    rw [commutator_eq_bot_iff_le_centralizer] at hc1 hc2
    have hle : M.map (MulAut.conj v).toMonoidHom ⊔ M'.map (MulAut.conj v).toMonoidHom ≤
        centralizer ({x} : Set G) := by
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hc1 hx) u hu)
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hc2 hx) u hu)
    rw [← hUeq] at hle
    exact (mem_centralizer_singleton_iff.mp (hle hyU)).symm
  have hbad : (∀ x ∈ M, x * y = y * x) → False := by
    intro hMy
    have hM'y : ∀ x ∈ M', x * y = y * x := fun x hx => comm_of_mem_conjugate hyb hMy hx
    have hle : M ⊔ M' ≤ centralizer ({y} : Set G) :=
      sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hMy x hx))
        (fun x hx => mem_centralizer_singleton_iff.mpr (hM'y x hx))
    obtain ⟨k, hk, hky⟩ := hyc
    exact hky (mem_centralizer_singleton_iff.mp (hle (hKI hk)))
  have hbad' : (∀ x ∈ M', x * y = y * x) → False := by
    intro hM'y
    apply hbad
    intro x hx
    have hx' : x ∈ conjugate M' b := by
      rw [hM'def, conjugate_conjugate_self M hb]
      exact hx
    exact comm_of_mem_conjugate hyb hM'y hx'
  have hMU : M ≤ U := by
    by_cases h1 : M = M.map (MulAut.conj v).toMonoidHom
    · rw [hUeq, ← h1]
      exact le_sup_left
    by_cases h2 : M = M'.map (MulAut.conj v).toMonoidHom
    · rw [hUeq, ← h2]
      exact le_sup_right
    exact absurd (hcommU M hM h1 h2) hbad
  have hM'U : M' ≤ U := by
    by_cases h1 : M' = M.map (MulAut.conj v).toMonoidHom
    · rw [hUeq, ← h1]
      exact le_sup_left
    by_cases h2 : M' = M'.map (MulAut.conj v).toMonoidHom
    · rw [hUeq, ← h2]
      exact le_sup_right
    exact absurd (hcommU M' hM' h1 h2) hbad'
  have hle : M ⊔ M' ≤ U := sup_le hMU hM'U
  exact (eq_of_le_of_card_ge hle (by
    rw [hUdef, Subgroup.card_map_of_injective (MulAut.conj v).injective])).symm

theorem card_le_relIndex_mul {V W P : Subgroup G} (hPV : P ≤ V) :
    Nat.card P ≤ W.relIndex V * Nat.card ↥(P ⊓ W) := by
  have h1 := Subgroup.relIndex_mul_card W P
  have h2 : W.relIndex P ≤ W.relIndex V :=
    Subgroup.relIndex_le_of_le_right hPV (relIndex_ne_zero_of_finite _ _)
  rw [inf_comm] at h1
  calc Nat.card P = W.relIndex P * Nat.card ↥(P ⊓ W) := h1.symm
    _ ≤ W.relIndex V * Nat.card ↥(P ⊓ W) := Nat.mul_le_mul_right _ h2

theorem isSylowOf_inf_inf {V I M : Subgroup G} (hV : IsSylowOf 2 V ⊤)
    (hVI : V ≤ normalizer (I : Set G)) (hMI : M ≤ I) (hIM : I ≤ normalizer (M : Set G)) :
    IsSylowOf 2 (V ⊓ I ⊓ M) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsSylowOf 2 V (V ⊔ I) := hV.of_le le_sup_left le_top
  have h2 : IsSylowOf 2 (V ⊓ I) I :=
    h1.inf_of_le_normalizer le_sup_right (sup_le hVI le_normalizer)
  exact h2.inf_of_le_normalizer hMI hIM

theorem false_of_swap {M : Subgroup G} (hM : IsComponent M) {b : G}
    (hne : M ≠ conjugate M b) {K : Subgroup G} (hKI : K ≤ M ⊔ conjugate M b)
    (hKb : K ≤ centralizer {b}) {Q : Subgroup G} (hQK : Q ≤ K) (hQ2 : IsPGroup 2 Q)
    (hQ8 : 8 ≤ Nat.card Q) (hQZ : ∀ q ∈ Q, (∀ k ∈ K, q * k = k * q) → q = 1)
    {P : Subgroup G} (hPsyl : IsSylowOf 2 P M)
    (hP4 : Nat.card P ≤ 4 * Nat.card ↥(P ⊓ centralizer {b})) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M' := conjugate M b with hM'def
  have hM' : IsComponent M' := LocalCores.isComponent_map_mulEquiv (MulAut.conj b⁻¹) hM
  have hc := (LocalCores.distinct_components_commute hM hM').resolve_left hne
  rw [commutator_eq_bot_iff_le_centralizer] at hc
  have hMM' : ∀ m ∈ M, ∀ m' ∈ M', m * m' = m' * m := fun m hm m' hm' =>
    (mem_centralizer_iff.mp (hc hm) m' hm').symm
  have hDc : ∀ d ∈ M ⊓ M', ∀ k ∈ K, d * k = k * d := by
    intro d hd k hk
    have hle : M ⊔ M' ≤ centralizer ({d} : Set G) := by
      refine sup_le (fun x hx => mem_centralizer_singleton_iff.mpr ?_)
        (fun x hx => mem_centralizer_singleton_iff.mpr ?_)
      · exact (hMM' x hx d (mem_inf.mp hd).2)
      · exact (hMM' d (mem_inf.mp hd).1 x hx).symm
    exact (mem_centralizer_singleton_iff.mp (hle (hKI hk))).symm
  have hPM : P ≤ M := hPsyl.le
  have hPD : P ⊓ centralizer {b} ≤ P ⊓ (M ⊓ M') := by
    intro x hx
    refine mem_inf.mpr ⟨(mem_inf.mp hx).1, mem_inf.mpr ⟨hPM (mem_inf.mp hx).1, ?_⟩⟩
    exact mem_conjugate_of_comm (hPM (mem_inf.mp hx).1)
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2)
  have hP4' : Nat.card P ≤ 4 * Nat.card ↥(P ⊓ (M ⊓ M')) :=
    hP4.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hPD))
  have hQM : Q ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hqK := hQK (mem_inf.mp hq).1
    have hqb := mem_centralizer_singleton_iff.mp (hKb hqK)
    have hqD : q ∈ M ⊓ M' := mem_inf.mpr ⟨(mem_inf.mp hq).2,
      mem_conjugate_of_comm (mem_inf.mp hq).2 hqb⟩
    exact (Subgroup.mem_bot).mpr (hQZ q (mem_inf.mp hq).1 (hDc q hqD))
  set I := M ⊔ M' with hIdef
  have hMIn : ((M.subgroupOf I).Normal) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer ?_)
    have hle : M' ≤ centralizer (M : Set G) := fun m' hm' =>
      mem_centralizer_iff.mpr fun m hm => hMM' m hm m' hm'
    exact hle.trans (Subgroup.centralizer_le_normalizer _)
  have hQI : Q ≤ I := hQK.trans hKI
  have h1 : (M.subgroupOf I).relIndex (Q.subgroupOf I) = Nat.card Q := by
    have h2 := Subgroup.relIndex_mul_card (M.subgroupOf I) (Q.subgroupOf I)
    have h3 : M.subgroupOf I ⊓ Q.subgroupOf I = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (x : G) ∈ Q ⊓ M := mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp hx).1⟩
      rw [hQM, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
    rw [h3, Subgroup.card_bot, mul_one,
      Nat.card_congr (subgroupOfEquivOfLe hQI).toEquiv] at h2
    exact h2
  have h4 : Nat.card Q ∣ (M.subgroupOf I).index := by
    rw [← h1, ← Subgroup.relIndex_sup_right]
    exact Subgroup.relIndex_dvd_index_of_le le_sup_right
  have h5 := (M.subgroupOf I).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : M ≤ I)).toEquiv] at h5
  have h6 : Nat.card Q * Nat.card M ∣ Nat.card I := by
    rw [← h5]
    exact Nat.mul_dvd_mul_right h4 _
  have h7 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute M M' hMM').1
  have h8 : Nat.card M' = Nat.card M := by
    rw [hM'def, conjugate, Subgroup.card_map_of_injective (MulAut.conj b⁻¹).injective]
  rw [h8] at h7
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have h9 : Nat.card Q * Nat.card ↥(M ⊓ M') ∣ Nat.card M := by
    have h10 : Nat.card Q * Nat.card M * Nat.card ↥(M ⊓ M') ∣ Nat.card M * Nat.card M := by
      rw [← h7]
      exact Nat.mul_dvd_mul_right h6 _
    rw [mul_comm (Nat.card Q) (Nat.card M), mul_assoc] at h10
    exact Nat.dvd_of_mul_dvd_mul_left hMpos h10
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
  have hD2 : Nat.card ↥(P ⊓ (M ⊓ M')) ≤ 2 ^ (Nat.card ↥(M ⊓ M')).factorization 2 :=
    card_le_twoPart (hPsyl.isPGroup.to_le inf_le_left) inf_le_right
  have h11 : 2 ^ (k + (Nat.card ↥(M ⊓ M')).factorization 2) ∣ Nat.card M := by
    rw [pow_add, ← hk]
    exact (Nat.mul_dvd_mul_left _ (Nat.ordProj_dvd _ _)).trans h9
  have h12 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hMpos.ne').mp h11
  have h13 : Nat.card P = 2 ^ (Nat.card M).factorization 2 := hPsyl.card_eq
  have h14 : 2 ^ (k + (Nat.card ↥(M ⊓ M')).factorization 2) ≤ Nat.card P := by
    rw [h13]
    exact Nat.pow_le_pow_right (by norm_num) h12
  rw [pow_add] at h14
  have h15 : 8 ≤ 2 ^ k := by rw [← hk]; exact hQ8
  have hpos : 0 < Nat.card ↥(P ⊓ (M ⊓ M')) := Nat.card_pos
  have h16 : 8 * Nat.card ↥(P ⊓ (M ⊓ M')) ≤
      2 ^ k * 2 ^ (Nat.card ↥(M ⊓ M')).factorization 2 :=
    Nat.mul_le_mul h15 hD2
  omega

end L415

end CFSG.ComponentClassification.HarrisLit
