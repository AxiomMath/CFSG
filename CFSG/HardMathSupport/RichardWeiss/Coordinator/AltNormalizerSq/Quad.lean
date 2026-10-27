module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Transfer

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

section WN

variable {n : ℕ}

theorem mem_ker_wAction_iff (hι : 2 ≤ Fintype.card (Fin n)) (x : ↥(wN d8 (Fin n))) :
    x ∈ (wAction wreathHyp_d8 hι).ker ↔ x.1 ∈ wR d8 (Fin n) := by
  constructor
  · intro hx
    exact mem_wR.2 (mem_wFix_of_mem_ker wreathHyp_d8 hι hx)
  · intro hx
    rw [MonoidHom.mem_ker]
    ext a
    have h1 := wAction_apply wreathHyp_d8 hι x (a, 0)
    have h2 := wFix_apply_fst (mem_wR.1 hx) (a, 0)
    simp only at h1 h2
    rw [h1, h2]
    rfl

theorem wAction_surjective_d8 (hι : 2 ≤ Fintype.card (Fin n)) :
    Function.Surjective (wAction wreathHyp_d8 hι) := by
  intro π
  refine ⟨⟨_, wLift_mem_wN (D := d8) (by decide) π⟩, ?_⟩
  refine Equiv.ext fun a => ?_
  have h := wAction_apply wreathHyp_d8 hι ⟨_, wLift_mem_wN (D := d8) (by decide) π⟩ (a, 0)
  simp only at h
  rw [h]
  rfl

theorem mem_wN_of_mem_normalizer_wN (hn : n = 3 ∨ 5 ≤ n) {σ : AltW (Fin n) (Fin 4)}
    (hσ : σ ∈ Subgroup.normalizer ((wN d8 (Fin n) : Subgroup (AltW (Fin n) (Fin 4))) : Set _)) :
    σ ∈ wN d8 (Fin n) := by
  have hι : 2 ≤ Fintype.card (Fin n) := by simp; omega
  set N := wN d8 (Fin n) with hN
  have hcore : CFSG.pCore 2 ↥N = (wAction wreathHyp_d8 hι).ker :=
    pCore_eq_ker_of_perm hn _ (wAction_surjective_d8 hι) (isPGroup_ker_wAction wreathHyp_d8 hι)
  have claimA : ∀ τ ∈ Subgroup.normalizer (N : Set (AltW (Fin n) (Fin 4))),
      ∀ x ∈ wR d8 (Fin n), τ * x * τ⁻¹ ∈ wR d8 (Fin n) := by
    intro τ hτ x hx
    have hxN : x ∈ N := Subgroup.le_normalizer hx
    have hxk : (⟨x, hxN⟩ : ↥N) ∈ CFSG.pCore 2 ↥N := by
      rw [hcore]; exact (mem_ker_wAction_iff hι _).2 hx
    have hmap := CFSG.pCore_map_iso 2 (conjOnSub N hτ)
    have hmem : conjOnSub N hτ ⟨x, hxN⟩ ∈ CFSG.pCore 2 ↥N := by
      rw [← hmap]; exact ⟨_, hxk, rfl⟩
    rw [hcore] at hmem
    have := (mem_ker_wAction_iff hι _).1 hmem
    simpa [coe_conjOnSub] using this
  show σ ∈ Subgroup.normalizer ((wR d8 (Fin n) : Subgroup (AltW (Fin n) (Fin 4))) : Set _)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => claimA σ hσ h hh, fun hh => ?_⟩
  have := claimA σ⁻¹ (inv_mem hσ) _ hh
  simpa [mul_assoc] using this

end WN

section Case

variable {G : Type} [Group G]

theorem quad_case {M S L : Subgroup G} {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : n = 3 ∨ 5 ≤ n)
    (hlt : ∀ (k : ℕ)
      (ρ : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →* Perm (Fin k)),
      Function.Surjective ρ → k < 2 * p)
    (φ : ↥(barM M L) ≃* AltW (Fin n) (Fin 4))
    (hB : ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).map
      φ.toMonoidHom = wN d8 (Fin n))
    {U : Subgroup G} (hUM : U ≤ M) (hUS : U ≤ Subgroup.normalizer (S : Set G))
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hUp : IsPGroup p U) :
    (U ⊓ blockCentralizer M L).relIndex U ≤ p := by
  have hBC : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L :=
    AGLEmbedding.barM_mono inf_le_right
  have hι : 2 ≤ Fintype.card (Fin n) := by simp; omega
  have hk : n < 2 * p := by
    obtain ⟨ρ, hρs, -⟩ := exists_quadAction hBC (by omega) φ hB
    exact hlt n ρ hρs
  have hcard : Fintype.card (Fin n × Fin 4) = 4 * n := by simp [mul_comm]
  obtain ⟨π, hπ, hker⟩ := exists_block_action (by omega) (by omega) φ hUM hUL
  have hAlt : ∀ u, π u ∈ alternatingGroup (Fin n × Fin 4) :=
    mem_alternatingGroup_of_isPGroup hp hp2 hUp π
  have hN : ∀ u : ↥U, (⟨π u, hAlt u⟩ : AltW (Fin n) (Fin 4)) ∈ wN d8 (Fin n) := by
    intro u
    have hu1 : (u : G) ∈ Subgroup.normalizer ((Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) :
        Set G) := mem_normalizer_inf (Subgroup.le_normalizer (hUS u.2)) (hUL u.2)
    exact mem_wN_of_mem_normalizer_wN hn (perm_mem_normalizer φ (wN d8 (Fin n)) hB
      (mk_mem_normalizer_barM (hUM u.2) (hUL u.2)) (mk_mem_normalizer_barM (hUM u.2) hu1) (hπ u)
      (hAlt u))
  let πA : ↥U →* AltW (Fin n) (Fin 4) := π.codRestrict (alternatingGroup _) hAlt
  have h := index_ker_le_of_two_kernel hp hp2 hk hUp πA (T := wN d8 (Fin n)) hN
    (wAction wreathHyp_d8 hι) (isPGroup_ker_wAction wreathHyp_d8 hι)
  have hkerA : πA.ker = π.ker := MonoidHom.ker_codRestrict _ _ _
  rw [hkerA, hker] at h
  exact h

end Case

end CFSG.HardMathSupport.RichardWeiss.Coordinator
