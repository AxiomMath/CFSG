module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnWeyl
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSubB
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnV
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG

theorem mp_plane_decomp {Y : Type} [Group Y] {T : Subgroup Y} {m : Y} (hmT : m ∉ T)
    (hm3 : m ^ 3 ∈ T) (hmn : ∀ t ∈ T, m * t * m⁻¹ ∈ T) {E : Subgroup Y}
    [IsElementaryAbelian 3 E] (hEc : Nat.card E = 9) (hEN : E ≤ T ⊔ Subgroup.zpowers m)
    (hET : ¬ E ≤ T) :
    ∃ v n : Y, v ∈ E ∧ v ∈ T ∧ v ≠ 1 ∧ n ∈ E ∧ n ∉ T ∧ n * v = v * n ∧ v ^ 3 = 1 ∧
      n ^ 3 = 1 ∧ ∀ x ∈ E, ∃ i j : ℤ, x = v ^ i * n ^ j := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  obtain ⟨n, hnE, hnT⟩ := IsConcreteLE.not_le_iff_exists.1 hET
  have hn3 : n ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian n hnE
  obtain ⟨e, heE, hen⟩ := exists_not_mem_zpowers_of_card_nine E hEc hn3
  obtain ⟨j, hj⟩ := mnWeyl_exists_zpow_mul_mem hmT hm3 hmn (hEN heE) (hEN hnE) hnT
  set v : Y := e * n ^ j with hv
  have hvE : v ∈ E := mul_mem heE (zpow_mem hnE j)
  have hv1 : v ≠ 1 := by
    intro h
    apply hen
    have : e = (n ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, ← zpow_neg]
    exact Subgroup.zpow_mem_zpowers n _
  have hv3 : v ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian v hvE
  have hcomm : n * v = v * n := mul_comm_of_mem_isElementaryAbelian (p := 3) hnE hvE
  refine ⟨v, n, hvE, hj, hv1, hnE, hnT, hcomm, hv3, hn3, ?_⟩
  have hordv : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hfinS : Finite ↥(E ⊓ T) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : E ⊓ T ≤ E))
      (Subgroup.inclusion_injective _)
  have hS3 : Nat.card ↥(E ⊓ T) = 3 := by
    have hd : Nat.card ↥(E ⊓ T) ∣ 9 := hEc ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(E ⊓ T) ≠ 9 := by
      intro h
      apply hET
      have : E ⊓ T = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hEc])
      rw [← this]
      exact inf_le_right
    have h3d : 3 ∣ Nat.card ↥(E ⊓ T) := by
      rw [← hordv, ← Subgroup.orderOf_mk v (Subgroup.mem_inf.2 ⟨hvE, hj⟩)]
      exact orderOf_dvd_natCard _
    have hd' : Nat.card ↥(E ⊓ T) ∣ 3 ^ 2 := by
      have : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [this]
      exact hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd'
    interval_cases k
    · rw [hk'] at h3d
      norm_num at h3d
    · simpa using hk'
    · exact absurd (by rw [hk']; norm_num) hne
  have hzS : Subgroup.zpowers v = E ⊓ T := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact (Subgroup.zpowers_le).2 (Subgroup.mem_inf.2 ⟨hvE, hj⟩)
    · rw [hS3, Nat.card_zpowers, hordv]
  intro x hx
  obtain ⟨k, hk⟩ := mnWeyl_exists_zpow_mul_mem hmT hm3 hmn (hEN hx) (hEN hnE) hnT
  have hu : x * n ^ k ∈ Subgroup.zpowers v := by
    rw [hzS]
    exact Subgroup.mem_inf.2 ⟨mul_mem hx (zpow_mem hnE k), hk⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hu
  refine ⟨i, -k, ?_⟩
  rw [hi, zpow_neg]
  group


end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut

theorem mp_plane_data_or {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L p] {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE : IsElementaryAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) :
    (∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∀ e ∈ E,
      d4MinusPsi σ L g₀ (β⁻¹ e) ∈ twistedTorusOf (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L p f))) ∨
    ∃ (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ x ∈ E.map (β⁻¹).toMonoidHom, ∃ i j : ℤ, x = v ^ i * n ^ j) ∧
      d4MinusPsi σ L g₀ v ∈ twistedTorusOf (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L p f)) ∧
      v ≠ 1 ∧ v ^ 3 = 1 ∧ n ^ 3 = 1 ∧ n * v = v * n ∧
      d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L ∧
      d4MinusPsi σ L g₀ n ∉ torusGroup TwistTag.D4.tag L := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨T', m', hT', hm'T, hm'3, hm'n, -, -, hidx, hNmono, -, -⟩ :=
    d4Minus_exists_N' hf hq hK hσ hg₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card hEc
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup_three (T' ⊔ Subgroup.zpowers m') hidx E hEp
  set β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.conj g with hβ
  have hβinv : ∀ x, (β⁻¹) x = g⁻¹ * x * g := fun x => by
    rw [hβ, ← map_inv, MulAut.conj_apply, inv_inv]
  set E' := E.map (β⁻¹).toMonoidHom with hE'
  have hE'mem : ∀ x ∈ E', ∃ y ∈ E, x = g⁻¹ * y * g := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, hβinv y⟩
  have hE'N : E' ≤ T' ⊔ Subgroup.zpowers m' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hE'mem x hx
    exact hg y hy
  have hE'c : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (β⁻¹).injective, hEc]
    norm_num
  have := hE
  have hE'e : IsElementaryAbelian 3 E' := IsElementaryAbelian.map (β⁻¹).toMonoidHom
  by_cases hE'T : E' ≤ T'
  · left
    exact ⟨β, fun e he => (hT' _).1 (hE'T ⟨e, he, rfl⟩)⟩
  · right
    obtain ⟨v, n, hvE, hvT, hv1, hnE, hnT, hnv, hv3, hn3, hgen⟩ :=
      mp_plane_decomp (E := E') hm'T hm'3 hm'n hE'c hE'N hE'T
    refine ⟨β, v, n, hgen, (hT' v).1 hvT, hv1, hv3, hn3, hnv, (hNmono n (hE'N hnE)).1, ?_⟩
    intro htor
    exact hnT ((hT' n).2 ((hNmono n (hE'N hnE)).2 htor))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
