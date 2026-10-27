module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidStd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinPsi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidAutInv

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)

section Conj

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem exists_map_stdW_eq_conj (hf : 2 ≤ f) (hε : 3 ≤ ε)
    (hW : ⁅stdW (ε := ε) h, stdW (ε := ε) h⁆ = stdW h) (β : MulAut (stabE (ε := ε) h)) :
    ∃ g₀ : stabE (ε := ε) h,
      (stdW h).map β.toMonoidHom = (stdW h).map (MulAut.conj g₀).toMonoidHom := by
  obtain ⟨z, hzn, hzc, hzS⟩ := exists_zt h hε
  have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  obtain ⟨hH', hS', hC', hSC', hzH', hzS'⟩ := module_hyps_map h hf (by omega) β hW
    (finrank_commSub_stdW h (by omega)) (finrank_fixSub_stdW h (by omega))
    (commSub_inf_fixSub_stdW h (by omega)) hodd hzn hzc hzS
  obtain ⟨g₀, hg₀⟩ := exists_conj_le_stdW h (by omega) hH' hS' hC' hSC' hzH' hzS'
  refine ⟨g₀, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro x hx
    refine ⟨g₀⁻¹ * x * g₀, hg₀ x hx, ?_⟩
    change g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ = x
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective,
      Subgroup.card_map_of_injective β.injective]

omit [Finite K] in
theorem center_stabE_le_tvSub : center (stabE (ε := ε) h) ≤ tvSub h := by
  intro z hz
  have hρ : rmat h z = 1 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    obtain ⟨x, hx, hxv⟩ := exists_mem_ker_avec_eq h (ε := ε) (Pi.single j 1)
    have h1 := avec_conj h hx z
    rw [(mem_center_iff.mp hz x).symm, mul_inv_cancel_right, hxv] at h1
    rw [one_mulVec, ← h1]
  have hzk : z ∈ (zBlockHom h).ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (Units.ext hρ)
  rw [← centralizer_inf_ker_eq_tvSub]
  exact Subgroup.mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y _ => mem_center_iff.mp hz y, hzk⟩

omit [Finite K] in
theorem eq_one_of_mem_center_stabE {z : stabE (ε := ε) h} (hz : z ∈ center (stabE h)) {m : ℕ}
    (hm : Odd m) (hzm : z ^ m = 1) : z = 1 := by
  have h2 : z ^ 2 = 1 := by
    rw [sq]
    exact mul_self_eq_one_of_mem_tvSub h (center_stabE_le_tvSub h hz)
  have h1 := orderOf_dvd_of_pow_eq_one h2
  have h3 := orderOf_dvd_of_pow_eq_one hzm
  have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h3)

end Conj

section Theta

variable {K : Type} [Field K] [CharP K 2] [Finite K] {k f : ℕ} (h : UnitaryFieldData 2 f K)
  {R : Matrix (Fin (2 * 1 + k)) (HypIndex 1 k) K} (hR : IsHypTransport h R)
  {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + k) (2 ^ f) K)}

theorem map_perfectCore_eq_range_psiU (hf : 2 ≤ f) (hk : 2 ≤ k) (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A)
    (hp2 : p ^ 2 = 1) {c : K} (hc : h.bar c = c) (hc0 : c ≠ 0)
    (hθp : θ ⟨p, hpA⟩ = psiU h hR ⟨tz h hc, tz_mem_stabE h hc⟩) :
    (perfectCore (centralizer ({⟨p, hpA⟩} : Set ↥A))).map θ = (psiU h hR).range := by
  have hx2 : (⟨p, hpA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hp2)
  rw [map_perfectCore_centralizer_eq_of_quot hθ hker hodd hx2, hθp,
    perfectCore_centralizer_psiU h hR hf hk hc hc0]

theorem exists_theta_stabE (hf : 2 ≤ f) (hk : 2 ≤ k) (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A)
    (hp2 : p ^ 2 = 1) {c : K} (hc : h.bar c = c) (hc0 : c ≠ 0)
    (hθp : θ ⟨p, hpA⟩ = psiU h hR ⟨tz h hc, tz_mem_stabE h hc⟩) :
    ∃ Θ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* stabE (ε := k) h,
      Function.Surjective Θ ∧
        ∀ x, psiU h hR (Θ x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x) := by
  have hmap := map_perfectCore_eq_range_psiU h hR hf hk hθ hker hodd hpA hp2 hc hc0 hθp
  have hX : perfectCore (A ⊓ centralizer ({p} : Set G)) =
      (perfectCore (centralizer ({⟨p, hpA⟩} : Set ↥A))).map A.subtype :=
    perfectCore_inf_centralizer_eq_map ⟨p, hpA⟩
  have hmem : ∀ x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))),
      θ (Subgroup.inclusion (perfectCore_inf_le A p) x) ∈ (psiU h hR).range := by
    intro x
    rw [← hmap]
    obtain ⟨y, hy, hyx⟩ : (x : G) ∈
        (perfectCore (centralizer ({⟨p, hpA⟩} : Set ↥A))).map A.subtype := by
      rw [← hX]
      exact x.2
    refine ⟨y, hy, ?_⟩
    congr 1
    exact Subtype.ext hyx
  set e := MonoidHom.ofInjective (psiU_injective h hR)
  set Θ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* stabE (ε := k) h :=
    e.symm.toMonoidHom.comp
      ((θ.comp (Subgroup.inclusion (perfectCore_inf_le A p))).codRestrict _ hmem)
  have hΘ : ∀ x, psiU h hR (Θ x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x) := by
    intro x
    change psiU h hR (e.symm _) = _
    rw [← MonoidHom.ofInjective_apply (psiU_injective h hR), MulEquiv.apply_symm_apply]
    rfl
  refine ⟨Θ, fun g => ?_, hΘ⟩
  have hg : psiU h hR g ∈ (perfectCore (centralizer ({⟨p, hpA⟩} : Set ↥A))).map θ := by
    rw [hmap]
    exact ⟨g, rfl⟩
  obtain ⟨y, hy, hyg⟩ := hg
  have hyX : (y : G) ∈ perfectCore (A ⊓ centralizer ({p} : Set G)) := by
    rw [hX]
    exact ⟨y, hy, rfl⟩
  refine ⟨⟨y, hyX⟩, psiU_injective h hR ?_⟩
  rw [hΘ, ← hyg]
  rfl

omit [Finite K] [Finite G] in
theorem theta_eq_one_of_mem_center {X : Type*} [Group X] {Θ : X →* stabE (ε := k) h}
    (hΘ : Function.Surjective Θ) {x : X} (hx : x ∈ center X) (hodd : Odd (orderOf x)) :
    Θ x = 1 := by
  have hc : Θ x ∈ center (stabE (ε := k) h) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hΘ g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
  exact eq_one_of_mem_center_stabE h hc hodd (by rw [← map_pow, pow_orderOf_eq_one, map_one])

end Theta

end CFSG.ComponentClassification.RankTwoClassical.URigid
