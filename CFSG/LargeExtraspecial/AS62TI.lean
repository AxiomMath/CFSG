module

public import CFSG.LargeExtraspecial.AS62Inv
public import CFSG.LargeExtraspecial.AS62Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace AS62

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem inf_orthogonal_eq_bot_of_forall {K : Submodule (ZMod 2) V} (hK2 : finrank (ZMod 2) K = 2)
    (hsing : ∀ v ∈ K ⊓ LinearMap.BilinForm.orthogonal q.polarBilin K, q v = 0 → v = 0) :
    K ⊓ LinearMap.BilinForm.orthogonal q.polarBilin K = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  by_contra hv0
  have hqv : q v = 1 := eq_one_of_ne_zero_zmod2 fun h => hv0 (hsing v hv h)
  obtain ⟨hvK, hvK'⟩ := Submodule.mem_inf.mp hv
  obtain ⟨k, hkK, hkv⟩ : ∃ k ∈ K, k ∉ (ZMod 2 ∙ v) := by
    by_contra! h
    have := Submodule.finrank_mono (show K ≤ ZMod 2 ∙ v from h)
    rw [hK2, finrank_span_singleton hv0] at this
    omega
  have hk0 : k ≠ 0 := by rintro rfl; exact hkv (Submodule.zero_mem _)
  have hvk : v ≠ k := by rintro rfl; exact hkv (Submodule.mem_span_singleton_self _)
  have hpol : polar q k v = 0 := by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvK') k hkK
    rwa [polarBilin_apply_apply] at this
  have hKeq := sup_span_eq_of_ne hK2 hvK hkK hv0 hk0 hvk
  obtain ⟨s, hsK, hs0, hsq, hsv, hsk⟩ : ∃ s ∈ K, s ≠ 0 ∧ q s = 0 ∧ polar q v s = 0 ∧
      polar q k s = 0 := by
    rcases zmod2_cases (q k) with h0 | h1
    · exact ⟨k, hkK, hk0, h0, by rw [QuadraticMap.polar_comm]; exact hpol,
        polar_self_eq_zero q k⟩
    · refine ⟨k + v, K.add_mem hkK hvK, fun h => hvk ?_, ?_, ?_, ?_⟩
      · refine (sub_eq_zero.mp ?_)
        rw [sub_eq_add_vec (ZMod 2), add_comm]
        exact h
      · rw [map_add_eq, h1, hqv, hpol]
        decide
      · rw [polar_add_right, QuadraticMap.polar_comm _ v k, hpol, polar_self_eq_zero, add_zero]
      · rw [polar_add_right, polar_self_eq_zero, hpol, add_zero]
  have hsK' : s ∈ LinearMap.BilinForm.orthogonal q.polarBilin K := by
    rw [← hKeq]
    exact mem_orthogonal_sup_span_iff.mpr ⟨hsv, hsk⟩
  exact hs0 (hsing s (Submodule.mem_inf.mpr ⟨hsK, hsK'⟩) hsq)

end Quadratic

end AS62

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem four_le_card_cqx (hw : S.width = 2) {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1)
    (hxQ : x ∉ S.QG) : 4 ≤ Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  have hle := S.finrank_commSpace_le_two hw hxM hxx
  have h32 := S.card_QG_of_width_two hw
  have h8 : 2 ^ (finrank (ZMod 2) (commSpace (S.rhoL hxM)) + 1) ≤ 8 :=
    (Nat.pow_le_pow_right (by norm_num) (by omega : _ ≤ 3)).trans (by norm_num)
  have h4 : 2 ^ finrank (ZMod 2) (commSpace (S.rhoL hxM)) ≤ 8 :=
    (Nat.pow_le_pow_right (by norm_num) (by omega : _ ≤ 3)).trans (by norm_num)
  have key : Nat.card S.QG ≤ 8 * Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
    rcases S.fourFive hxM hxx hxQ with ⟨-, hk, -⟩ | ⟨-, hk, -, -⟩ | ⟨-, hk, -, -⟩
    · rw [hk]
      exact Nat.mul_le_mul_right _ h4
    · rw [hk]
      exact Nat.mul_le_mul_right _ h8
    · rw [hk]
      exact Nat.mul_le_mul_right _ h8
  omega

theorem isTypeC_of_inf_eq_bot (hw : S.width = 2)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {g t : G} (hgM : g ∉ S.M)
    (hgt : g * S.z * g⁻¹ = t) (htM : t ∈ S.M) (hI : S.QG ⊓ S.Qa g = ⊥) :
    IsTypeC S.q (S.rhoL htM) 2 := by
  subst hgt
  have hne := S.conj_z_ne_of_not_mem_M hgM
  have htQ : g * S.z * g⁻¹ ∉ S.QG := fun h => hne (hW g h)
  have htt := S.conj_mul_self g
  have hTw : (S.conjBy g).width = 2 := by rw [S.width_conjBy, hw]
  have hzT : S.z ∈ (S.conjBy g).M :=
    mem_centralizer_singleton_iff.mpr (S.mem_M_iff.mp htM).symm
  have hzTQ : S.z ∉ (S.conjBy g).QG := S.z_not_mem_Qa hW hne
  have hP4 : 4 ≤ Nat.card ↥(S.Qa g ⊓ S.M) :=
    (S.conjBy g).four_le_card_cqx hTw hzT S.z_mul_z hzTQ
  have hPM : S.Qa g ⊓ S.M ≤ S.M := inf_le_right
  have hPQ : S.Qa g ⊓ S.M ⊓ S.QG = ⊥ := by
    rw [eq_bot_iff, ← hI]
    exact fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).1⟩
  have hP2 : IsPGroup 2 ↥(S.Qa g ⊓ S.M) := (S.conjBy g).isPGroup_QG.to_le inf_le_left
  have hfixC : ∀ x (hx : x ∈ S.Qa g ⊓ S.M),
      ∀ r ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G),
      S.rhoL (hPM hx) (S.cl r) = S.cl r := by
    intro x hx r hr
    rw [S.rhoL_cl (hPM hx) (mem_inf.mp hr).1]
    congr 1
    calc x * r * x⁻¹ = r * x * x⁻¹ := by rw [S.commute_of_inf_Qa_eq_bot hI hx hr]
      _ = r := by group
  have hnotA : ∀ m, ¬ IsTypeA S.q (S.rhoL htM) m := by
    intro m hA
    have hcq := S.cqx_eq_clPre_of_typeA hw htM htt htQ hA
    have h2 := S.card_le_two_of_rhoL_fix_tsPlane hw (U := commSpace (S.rhoL htM))
      (hA.2.2.2.1.trans (S.eq_two_of_typeA hw htM hA)) hA.2.2.2.2 hPM hPQ fun x hx u hu => by
        obtain ⟨r, hrQ, rfl⟩ := S.exists_cl u
        exact hfixC x hx r (by rw [hcq]; exact S.mem_clPre.mpr ⟨hrQ, hu⟩)
    omega
  rcases S.fourFive htM htt htQ with ⟨hA, -, -⟩ | ⟨hBC, hk, hΩ, -⟩ | ⟨hA, -, -, -⟩
  · exact absurd hA (hnotA _)
  · rcases hBC with hB | hC
    ·
      exfalso
      obtain ⟨-, -, -, hodd⟩ := hB
      have h1 : finrank (ZMod 2) (commSpace (S.rhoL htM)) = 1 := by
        have := S.finrank_commSpace_le_two hw htM htt
        obtain ⟨k, hk'⟩ := hodd
        omega
      rw [h1] at hk hΩ
      have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
      have hK2 : finrank (ZMod 2) (S.cqxSub (g * S.z * g⁻¹)) = 2 := by
        have h1' := S.card_clPre (S.cqxSub (g * S.z * g⁻¹))
        rw [S.clPre_cqxSub htM, S.card_submodule] at h1'
        rw [S.card_QG_of_width_two hw, show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at hk
        have h3 : 2 ^ finrank (ZMod 2) (S.cqxSub (g * S.z * g⁻¹)) = 2 ^ 2 := by omega
        exact Nat.pow_right_injective le_rfl h3
      have hKnd : S.cqxSub (g * S.z * g⁻¹) ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin
          (S.cqxSub (g * S.z * g⁻¹)) = ⊥ := by
        refine AS62.inf_orthogonal_eq_bot_of_forall hK2 fun v hv hqv => ?_
        have hΩ' := S.ncard_omegaOne_center htM
        rw [hΩ, pow_one] at hΩ'
        have hfr : finrank (ZMod 2) ↥(S.singSub (S.cqxSub (g * S.z * g⁻¹) ⊓
            LinearMap.BilinForm.orthogonal S.q.polarBilin (S.cqxSub (g * S.z * g⁻¹)))
            (S.isotropic_inf_orthogonal (S.cqxSub (g * S.z * g⁻¹)))) = 0 := by
          have h5 : 2 ^ finrank (ZMod 2) ↥(S.singSub (S.cqxSub (g * S.z * g⁻¹) ⊓
              LinearMap.BilinForm.orthogonal S.q.polarBilin (S.cqxSub (g * S.z * g⁻¹)))
              (S.isotropic_inf_orthogonal (S.cqxSub (g * S.z * g⁻¹)))) = 2 ^ 0 := by
            rw [pow_zero]
            omega
          exact Nat.pow_right_injective le_rfl h5
        have hvs := (S.mem_singSub (hW := S.isotropic_inf_orthogonal
          (S.cqxSub (g * S.z * g⁻¹)))).mpr ⟨hv, hqv⟩
        rw [Submodule.finrank_eq_zero.mp hfr, Submodule.mem_bot] at hvs
        exact hvs
      have h2 := S.card_le_two_of_rhoL_fix_nondeg hw hK2 hKnd hPM hPQ hP2 fun x hx v hv => by
        obtain ⟨r, hrC, hrQ, rfl⟩ := S.mem_clSub_iff.mp hv
        exact hfixC x hx r hrC
      omega
    · have h2 := S.eq_two_of_typeC hw htM htt hC
      rw [h2] at hC
      exact hC
  · exact absurd hA (hnotA _)

theorem isTypeC_mirror_of_inf_eq_bot (hw : S.width = 2)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {g : G} (hgM : g ∉ S.M)
    (hI : S.QG ⊓ S.Qa g = ⊥) (hzM : S.z ∈ (S.conjBy g).M) :
    IsTypeC (S.conjBy g).q ((S.conjBy g).rhoL hzM) 2 := by
  obtain ⟨hgT, hgz, hII⟩ := S.mirror_data hgM
  exact (S.conjBy g).isTypeC_of_inf_eq_bot (by rw [S.width_conjBy, hw])
    (S.weaklyClosed_conjBy hW g) hgT hgz hzM (by rw [hII]; exact hI)

theorem exists_conj_mem_M_ne_of (hn : 2 ≤ S.width)
    (hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t) (hZ : S.z ∉ center G) :
    ∃ g : G, g ∉ S.M ∧ g * S.z * g⁻¹ ∈ S.M := by
  by_contra! hiso
  obtain ⟨N, hNn, hNodd, hN⟩ := S10.exists_odd_normal_of_isolated S.z S.z_ne_one S.z_mul_z
    (fun g hg => by
      by_cases hgM : g ∈ S.M
      · rw [S.mem_M_iff.mp hgM]
        group
      · exact absurd (S.mem_M_iff.mpr hg) (hiso g hgM))
  have hN1 := S.eq_bot_of_normal_odd hn hO hNn hNodd
  apply hZ
  rw [mem_center_iff]
  intro g
  have h := hN g
  rw [hN1, mem_bot, mul_inv_eq_one] at h
  calc g * S.z = g * S.z * g⁻¹ * g := by group
    _ = S.z * g := by rw [h]

end Setting

namespace AS62

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_conj_mem_M_ne (h : W2Hyp S) : ∃ g : G, g ∉ S.M ∧ g * S.z * g⁻¹ ∈ S.M :=
  S.exists_conj_mem_M_ne_of (by rw [h.hw]) h.hO fun hz => S.z_ne_one (by
    have hzc : S.z ∈ centralizer (S.zGen : Set G) :=
      mem_centralizer_iff.mpr fun x _ => mem_center_iff.mp hz x
    rw [h.hC, mem_bot] at hzc
    exact hzc)

theorem false_of_TI (h : W2Hyp S) (hTI : ∀ g : G, g ∉ S.M → S.QG ⊓ S.Qa g = ⊥) : False := by
  obtain ⟨g, hgM, htM⟩ := exists_conj_mem_M_ne h
  have hI := hTI g hgM
  have htt := S.conj_mul_self g
  have htC := S.isTypeC_of_inf_eq_bot h.hw h.hW hgM rfl htM hI
  have hzT : S.z ∈ (S.conjBy g).M :=
    mem_centralizer_singleton_iff.mpr (S.mem_M_iff.mp htM).symm
  have hzC := S.isTypeC_mirror_of_inf_eq_bot h.hw h.hW hgM hI hzT
  have hTw : (S.conjBy g).width = 2 := by rw [S.width_conjBy, h.hw]
  obtain ⟨w, hwC, hww, hw1, hwz⟩ := S.exists_mem_cqx_of_typeC h.hw htM htt htC
  obtain ⟨hwQ, hwt⟩ := mem_inf.mp hwC
  have hwt' : w * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * w := mem_centralizer_singleton_iff.mp hwt
  have hCw : ∀ c : G, c * w = w * c → c ∈ S.M := by
    intro c hc
    by_contra hcM
    have hmem : w ∈ S.QG ⊓ S.Qa c := mem_inf.mpr ⟨hwQ, S.mem_Qa_of_commute hwQ hc⟩
    rw [hTI c hcM, mem_bot] at hmem
    exact hw1 hmem
  have hwTM : w ∈ (S.conjBy g).M := hwt
  have hwTQ : w ∉ (S.conjBy g).QG := fun h' => hw1 (by
    have hmem : w ∈ S.QG ⊓ S.Qa g := mem_inf.mpr ⟨hwQ, h'⟩
    rwa [hI, mem_bot] at hmem)
  have hPeq : (S.conjBy g).QG ⊓ centralizer ({w} : Set G) =
      (S.conjBy g).QG ⊓ centralizer ({S.z} : Set G) := by
    apply le_antisymm
    · intro p hp
      obtain ⟨hpT, hpw⟩ := mem_inf.mp hp
      exact mem_inf.mpr ⟨hpT, hCw p (mem_centralizer_singleton_iff.mp hpw)⟩
    · intro p hp
      obtain ⟨hpT, hpz⟩ := mem_inf.mp hp
      exact mem_inf.mpr ⟨hpT, mem_centralizer_singleton_iff.mpr
        (S.commute_of_inf_Qa_eq_bot hI (mem_inf.mpr ⟨hpT, hpz⟩) hwC)⟩
  have hk8 := (S.conjBy g).card_QG_eq_eight_mul_of_typeC hTw hzT S.z_mul_z hzC
  have hconj : IsConj w ((g * S.z * g⁻¹) * w) := by
    rcases (S.conjBy g).fourFive hwTM hww hwTQ with ⟨-, hk, -⟩ | ⟨-, -, -, hc⟩ | ⟨-, -, -, hc⟩
    · exfalso
      rw [hPeq, hk8] at hk
      have hle := (S.conjBy g).finrank_commSpace_le_two hTw hwTM hww
      have hpos : 0 < Nat.card ↥((S.conjBy g).QG ⊓ centralizer ({S.z} : Set G)) := Nat.card_pos
      have h8 := Nat.eq_of_mul_eq_mul_right hpos hk
      have h4 : 2 ^ finrank (ZMod 2) (commSpace ((S.conjBy g).rhoL hwTM)) ≤ 4 :=
        (Nat.pow_le_pow_right (by norm_num) hle).trans (by norm_num)
      omega
    · rw [Setting.conjBy_z, hwt'] at hc
      exact hc
    · rw [Setting.conjBy_z] at hc
      exact hc
  obtain ⟨y, -, hy⟩ := S.exists_conj_mul_of_typeC h.hw htM htt htC hwC
  have hzw : IsConj S.z w :=
    ((isConj_iff.mpr ⟨g, rfl⟩).trans (isConj_iff.mpr ⟨y, hy⟩)).trans hconj.symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hzw
  exact hwz (hc.symm.trans (h.hW c (by rw [hc]; exact hwQ)))

theorem exists_inf_Qa_ne_bot (h : W2Hyp S) : ∃ g : G, g ∉ S.M ∧ S.QG ⊓ S.Qa g ≠ ⊥ := by
  by_contra! hTI
  exact false_of_TI h hTI

end AS62

end CFSG.LargeExtraspecial
