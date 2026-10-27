module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryCover
import CFSG.Adapters.StatedSmallProjOrders
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

theorem heisU_ne_three_two {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hsimple : IsSimpleGroup (L ⧸ Subgroup.center L)) {n f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU n (2 ^ f) K)) : (n, 2 ^ f) ≠ (3, 2) := by
  intro h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have hf : f = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h2)
  subst hf
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK, pow_one]
  have hcardX : Nat.card (L ⧸ Subgroup.center L) = 72 := by
    rw [Nat.card_congr e.toEquiv]
    have := CFSG.Open.StatedAPI.card_statedProj_statedSU_three_of_prime (K := K) Nat.prime_two hK'
    rw [pow_one, this]
    norm_num
  haveI := Fintype.ofFinite (L ⧸ Subgroup.center L)
  have hsolv : Group.IsSolvable (L ⧸ Subgroup.center L) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 2)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcardX]; norm_num)
  haveI := hperf
  haveI := hsimple
  exact Group.IsPerfect.not_isSolvable (L ⧸ Subgroup.center L) hsolv

theorem heisU_exists_cover
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) (hsimple : IsSimpleGroup (L ⧸ Subgroup.center L))
    {n f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 3 ≤ n)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU n (2 ^ f) K)) :
    ∃ ρ : StatedSU n (2 ^ f) K →* L, Function.Surjective ρ ∧
      ∀ g, ρ g ∈ Subgroup.center L ↔ (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K := by
  have hnq := heisU_ne_three_two hperf hsimple hK e
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  let e₀ : (⊤ : Subgroup L) ≃* L := Subgroup.topEquiv
  have hmap : (Subgroup.center ↥(⊤ : Subgroup L)).map e₀.toMonoidHom = Subgroup.center L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ Subgroup.center ↥(⊤ : Subgroup L) := hy
      rw [Subgroup.mem_center_iff] at hy'
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e₀.surjective g
      have := hy' g'
      change e₀ g' * e₀ y = e₀ y * e₀ g'
      rw [← map_mul, ← map_mul, this]
    · intro hx
      refine ⟨e₀.symm x, ?_, by simp⟩
      have hx' := Subgroup.mem_center_iff.1 hx
      show e₀.symm x ∈ Subgroup.center ↥(⊤ : Subgroup L)
      rw [Subgroup.mem_center_iff]
      intro g
      apply e₀.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx' (e₀ g)
  let ι : ↥(⊤ : Subgroup L) ⧸ Subgroup.center ↥(⊤ : Subgroup L) ≃* L ⧸ Subgroup.center L :=
    QuotientGroup.congr _ _ e₀ hmap
  have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup L)) = Nat.card (Subgroup.center L) :=
    Nat.card_congr (Subgroup.centerCongr e₀).toEquiv
  have hcomp : IsComponentOf (⊤ : Subgroup L) ⊤ := ⟨le_rfl, IsSubnormal.refl _,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv
      ⟨hperf.commutator_eq_top, hsimple⟩⟩
  obtain ⟨ρ₀, hρ₀, -, hρ₀e⟩ := CFSG.AGLEmbedding.kFactCoverUnitary L ⊤ hcomp (hcard ▸ hodd) n
    (2 ^ f) K hK hn hnq (ι.trans e)
  refine ⟨e₀.toMonoidHom.comp ρ₀, e₀.surjective.comp hρ₀, fun g => ?_⟩
  have h1 : e (QuotientGroup.mk (e₀ (ρ₀ g))) = QuotientGroup.mk g := by
    have := hρ₀e g
    rw [MulEquiv.trans_apply] at this
    rwa [show ι (QuotientGroup.mk (ρ₀ g)) = QuotientGroup.mk (e₀ (ρ₀ g)) from
      QuotientGroup.congr_mk _ _ _ _ _] at this
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← QuotientGroup.eq_one_iff,
    ← e.map_eq_one_iff, h1, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem heisU_card_center_dvd {L : Type} [Group L] {n f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 1 ≤ n) (ρ : StatedSU n (2 ^ f) K →* L)
    (hρ : Function.Surjective ρ)
    (hZ : ∀ g, ρ g ∈ Subgroup.center L ↔ (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K) :
    Nat.card (Subgroup.center L) ∣ Nat.gcd n (2 ^ f + 1) ∧
      Nat.card ρ.ker ∣ Nat.gcd n (2 ^ f + 1) := by
  set D := (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) with hDdef
  have hD : Nat.card D = Nat.gcd n (2 ^ f + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn).2.2
  have hmap : D.map ρ = Subgroup.center L := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hZ g).2 (Subgroup.mem_subgroupOf.1 hg)
    · intro hx
      obtain ⟨g, rfl⟩ := hρ x
      exact ⟨g, Subgroup.mem_subgroupOf.2 ((hZ g).1 hx), rfl⟩
  have hker : ρ.ker ≤ D := fun g hg =>
    Subgroup.mem_subgroupOf.2 ((hZ g).1 (by rw [MonoidHom.mem_ker.1 hg]; exact Subgroup.one_mem _))
  refine ⟨?_, ?_⟩
  · rw [← hmap, ← hD]
    exact Subgroup.card_map_dvd D ρ
  · rw [← hD]
    exact Subgroup.card_dvd_of_le hker

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
