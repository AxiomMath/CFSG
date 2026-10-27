module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G] [Finite G]

open SuzukiAut CFSG.BenderSuzuki.MatrixGroups in
theorem sq_mem_sylowCenter_of_sz {X : Type*} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* Sz a) (R : Sylow 2 X) :
    ∀ x ∈ (R : Subgroup X), x ^ 2 ∈ sylowCenter (R : Subgroup X) := by
  classical
  set e' : X ≃* SuzukiMatrixGroup a := e.trans (suzukiEquiv a).symm with he'
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e' e'.surjective
  obtain ⟨S₀, hS₀⟩ := exists_sylow_eq_rootSub a (by omega)
  set S : Sylow 2 (SuzukiMatrixGroup a) := R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hS : (S : Subgroup (SuzukiMatrixGroup a)) = (R : Subgroup X).map e'.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup a) S₀ S
  have hmem : ∀ s, s ∈ (S : Subgroup (SuzukiMatrixGroup a)) ↔ g⁻¹ * s * g ∈ rootSub a := by
    intro s
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS₀]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  have hroot : ∀ r ∈ rootSub a, ∀ s ∈ rootSub a, s * r ^ 2 = r ^ 2 * s := by
    intro r hr s hs
    obtain ⟨u, v, rfl⟩ := (mem_rootSub a).mp hr
    have hsq : root a u v ^ 2 = root a 0 (u * tits a u) := by
      rw [sq, root_mul a (by omega), CharTwo.add_self_eq_zero u, CharTwo.add_self_eq_zero v,
        zero_add]
    rw [hsq]
    exact (mem_sylowCenter.mp ((mem_sylowCenter_rootSub a (by omega)).mpr ⟨_, rfl⟩)).2 s hs
  have hR : ∀ x ∈ (R : Subgroup X), g⁻¹ * e' x * g ∈ rootSub a := fun x hx =>
    (hmem _).mp (hS ▸ ⟨x, hx, rfl⟩)
  intro x hx
  refine mem_sylowCenter.mpr ⟨pow_mem hx 2, fun t ht => e'.injective ?_⟩
  have h1 := hroot _ (hR x hx) _ (hR t ht)
  have h2 : (g⁻¹ * e' x * g) ^ 2 = g⁻¹ * e' x ^ 2 * g := by
    rw [sq, sq]
    group
  rw [h2] at h1
  rw [map_mul, map_mul, map_pow]
  calc e' t * e' x ^ 2 = g * ((g⁻¹ * e' t * g) * (g⁻¹ * e' x ^ 2 * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * e' x ^ 2 * g) * (g⁻¹ * e' t * g)) * g⁻¹ := by rw [h1]
    _ = e' x ^ 2 * e' t := by group

theorem sq_mem_of_sz {L P : Subgroup G} (hZ : Odd (Nat.card (center L))) {a : ℕ} (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) (hP : IsSylowOf 2 P L) :
    ∀ x ∈ P, x ^ 2 ∈ P ⊓ centralizer (P : Set G) := by
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hcen := mem_center_iff_sylowProj hZ hP hR
  have hρR : ∀ p, sylowProj hP.le p ∈ (R : Subgroup (rankTwoQuot L)) := fun p => hR ▸ ⟨p, rfl⟩
  intro x hx
  have h1 := sq_mem_sylowCenter_of_sz ha e R _ (hρR ⟨x, hx⟩)
  rw [← map_pow] at h1
  exact (hcen _).mpr h1

namespace Sec3

variable {L T : Subgroup G}

theorem facts_of_sz (h : Sec3 G L T)
    (hF : Foundation) (hZ : Odd (Nat.card (center L))) {a : ℕ} (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) : Facts L T (2 ^ (2 * a + 1)) := by
  have hB := Asc76X.fusionBenderBorel_of_mulEquiv_sz ha e
  have hq : 8 ≤ 2 ^ (2 * a + 1) :=
    (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨by omega, hZ, ⟨2, hB⟩, sq_mem_of_sz hZ ha e h.isSylowOf_T₁, fun z hz => ?_⟩
  obtain ⟨-, hVel, hVW, -, hΩ⟩ := h.vFacts hF hZ (by omega) hB
  have hTW : T = gmsW L T := h.eq_sup_of_sz ha e
  have hle : rightConjugate (gmsV L T) z ≤ gmsV L T := by
    intro v hv
    have hvT : v ∈ T := hz ((map_mono hVW : rightConjugate (gmsV L T) z ≤
      rightConjugate (gmsW L T) z) hv)
    rw [hTW] at hvT
    exact hΩ v hvT ((isElemAbelian_map _ hVel).2 v hv)
  exact eq_of_le_of_card_ge hle (by rw [rightConjugate_card])

theorem lemma313_of_sz_of_odd
    (h : Sec3 G L T) (hF : Foundation) (hZ : Odd (Nat.card (center L))) {a : ℕ} (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) : Lemma313 L T (2 ^ (2 * a + 1)) := by
  have hq : 8 ≤ 2 ^ (2 * a + 1) :=
    (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hT₁, hA₁, -⟩ := sylow_of_benderBorel hZ (by omega)
    (Asc76X.fusionBenderBorel_of_mulEquiv_sz ha e) h.isSylowOf_T₁
  refine (h.facts_of_sz hF hZ ha e).lemma313 h hF ?_
  rw [hT₁, hA₁, sq]
  exact lt_mul_left (by omega) (by omega)

end Sec3

end CFSG.ComponentClassification.GMS78
