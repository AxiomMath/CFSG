module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem eq_of_normal_perfect_of_quasisimple {Q : Type*} [Group Q] {I M : Subgroup Q}
    (hI : CFSG.Open.IsQuasisimple ↥I) (hMI : M ≤ I) (hn : (M.subgroupOf I).Normal)
    (hperf : ⁅M, M⁆ = M) (hM1 : M ≠ ⊥) : M = I := by
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hI
      (M.subgroupOf I) with hc | htop
  · exfalso
    refine hM1 ?_
    rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    have hcx := Subgroup.mem_center_iff.1 (hc ((Subgroup.mem_subgroupOf).2 hx : (⟨x, hMI hx⟩ : ↥I) ∈
      M.subgroupOf I)) ⟨y, hMI hy⟩
    have hxy : y * x = x * y := congrArg Subtype.val hcx
    rw [Subgroup.mem_bot, commutatorElement_def, ← hxy]
    group
  · exact le_antisymm hMI (Subgroup.subgroupOf_eq_top.1 htop)

private theorem isSubnormal_of_le_normalizer {Q : Type*} [Group Q] {C M : Subgroup Q}
    (hMC : M ≤ C) (hn : C ≤ Subgroup.normalizer (M : Set Q)) : IsSubnormal M C :=
  IsSubnormal.step hMC ((Subgroup.normal_subgroupOf_iff_le_normalizer hMC).2 hn)
    (IsSubnormal.refl C)

private theorem barX_mono_aux {Q : Type*} [Group Q] {C S T : Subgroup Q} (h : S ≤ T) :
    barX 3 C S ≤ barX 3 C T :=
  Subgroup.map_mono fun _ hx => (Subgroup.mem_subgroupOf).2 (h ((Subgroup.mem_subgroupOf).1 hx))

private theorem isSubnormal_barX_top {Q : Type*} [Group Q] {C M : Subgroup Q}
    (hsn : IsSubnormal M C) : IsSubnormal (barX 3 C M) ⊤ := by
  have h := isSubnormal_map' (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C))
    (isSubnormal_comap' C.subtype hsn)
  have htop : (C.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  rw [← htop]
  exact h

private theorem isQuasisimple_of_isLThreeFour {X : Type*} [Group X] (h : IsLThreeFour X) :
    CFSG.Open.IsQuasisimple X := by
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := h
  have hP : IsLThreeFour (StatedProj (StatedSL 3 K)) := ⟨K, hK, hKf, hcard, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hs, a, b, hab⟩ := isSimpleGroup_of_isLThreeFour hP
  have := hs
  have : Group.IsPerfect (StatedProj (StatedSL 3 K)) := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (StatedProj (StatedSL 3 K)))
      with h | h
    · exfalso
      have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [commutator_def] at h
      rw [h, Subgroup.mem_bot] at hmem
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 hmem)
    · exact h
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e
    (CFSG.ComponentClassification.Quasisimple.simple_of_perfect _)

theorem glaPComponent_of_normal_generated {Q : Type*} [Group Q] [Finite Q] {C M : Subgroup Q}
    (hMC : M ≤ C) (hn : C ≤ Subgroup.normalizer (M : Set Q))
    (hgen : M = Subgroup.closure {g : Q | g ∈ M ∧ IsPGroup 3 (Subgroup.zpowers g)})
    (hL : IsLThreeFour (↥M ⧸ GLAPPrimeCore 3 ↥M)) : GLAPComponent 3 C M := by
  have hsn : IsSubnormal M C := isSubnormal_of_le_normalizer hMC hn
  refine ⟨hMC, hsn, ⟨le_top, isSubnormal_barX_top hsn, ?_⟩, ?_⟩
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (quotEquivBarX Nat.prime_three hMC hsn).symm (isQuasisimple_of_isLThreeFour hL)
  · intro J hJ hJsn heq
    have hJM : IsSubnormal J M := isSubnormal_of_le_of_le hJsn hJ.le hMC
    obtain ⟨M', hJM', hM'M, hM'ne, hM'n, -⟩ := isSubnormal_exists_normal hJM hJ.ne
    have hle : barX 3 C M ≤ barX 3 C M' := by
      have h2 : barX 3 C J = barX 3 C M := heq
      rw [← h2]
      exact barX_mono_aux hJM'
    have h3 : ∀ g ∈ {g : Q | g ∈ M ∧ IsPGroup 3 (Subgroup.zpowers g)}, g ∈ M' := by
      rintro g ⟨hgM, hg3⟩
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨j, hjM', hjo⟩ := exists_of_barX_le hle hgM (hMC hgM)
      have hjM : j ∈ M := hM'M hjM'
      have ho : j⁻¹ * g ∈ GLAPPrimeCoreOf 3 M := by
        rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hsn]
        exact ⟨M.mul_mem (M.inv_mem hjM) hgM, hjo⟩
      obtain ⟨k, hk⟩ := hg3.exists_card_eq
      have hord : orderOf g = 3 ^ k := by
        rw [← Nat.card_zpowers]; exact hk
      set φ := QuotientGroup.mk' (M'.subgroupOf M) with hφ
      have hg' : φ ⟨g, hgM⟩ = φ ⟨j⁻¹ * g, M.mul_mem (M.inv_mem hjM) hgM⟩ := by
        have hj1 : φ ⟨j⁻¹, M.inv_mem hjM⟩ = 1 := by
          rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact (Subgroup.mem_subgroupOf).2 (M'.inv_mem hjM')
        have : (⟨j⁻¹ * g, M.mul_mem (M.inv_mem hjM) hgM⟩ : ↥M) =
            ⟨j⁻¹, M.inv_mem hjM⟩ * ⟨g, hgM⟩ := rfl
        rw [this, map_mul, hj1, one_mul]
      have hd1 : orderOf (φ ⟨g, hgM⟩) ∣ 3 ^ k := by
        rw [← hord, ← Subgroup.orderOf_mk g hgM]
        exact orderOf_map_dvd φ _
      have hd2 : orderOf (φ ⟨j⁻¹ * g, M.mul_mem (M.inv_mem hjM) hgM⟩) ∣
          Nat.card (GLAPPrimeCoreOf 3 M) := by
        refine (orderOf_map_dvd φ _).trans ?_
        rw [Subgroup.orderOf_mk]
        exact Subgroup.orderOf_dvd_natCard _ ho
      rw [hg'] at hd1
      have h1 : orderOf (φ ⟨j⁻¹ * g, M.mul_mem (M.inv_mem hjM) hgM⟩) = 1 := by
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd1
        by_contra hne
        have hi0 : i ≠ 0 := fun h0 => hne (by simp [hi, h0])
        exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three M
          ((dvd_pow_self 3 hi0).trans (hi ▸ hd2))
      rw [orderOf_eq_one_iff, ← hg', hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact (Subgroup.mem_subgroupOf).1 h1
    exact hM'ne (le_antisymm hM'M (hgen ▸ (Subgroup.closure_le M').2 h3))

theorem glaPPrimeCoreOf_eq_bot_of_isSubnormal {G : Type} [Group G] [Finite G] {N : Subgroup G}
    {M : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)} (hM : IsSubnormal M ⊤) :
    GLAPPrimeCoreOf 3 M = ⊥ := by
  have hle := glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hM
  have htop : GLAPPrimeCoreOf 3 (⊤ : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)) = ⊥ := by
    have h := glaPPrimeCore_map_iso 3 (Subgroup.topEquiv (G := ↥N ⧸ GLAPPrimeCore 3 ↥N)).symm
    rw [glaPPrimeCore_quotient_eq_bot Nat.prime_three, Subgroup.map_bot] at h
    unfold GLAPPrimeCoreOf
    rw [← h, Subgroup.map_bot]
  exact le_bot_iff.1 (htop ▸ hle)

theorem glaPPrimeCore_eq_bot_of_isSubnormal {G : Type} [Group G] [Finite G] {N : Subgroup G}
    {M : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)} (hM : IsSubnormal M ⊤) :
    GLAPPrimeCore 3 ↥M = ⊥ := by
  have h := glaPPrimeCoreOf_eq_bot_of_isSubnormal hM
  unfold GLAPPrimeCoreOf at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 h

theorem pRank_mulAut_le_two_of_quot {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (h : IsLThreeFour (X ⧸ Subgroup.center X)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 2 :=
  (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (quotientCenterAut' X)
    (quotientCenterAut'_injective hperf)).trans (pRank_mulAut_le_two_of_isLThreeFour h)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
