module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Transfer

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G]

theorem pair_case {M S L : Subgroup G} {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    (hlt : ∀ (k : ℕ)
      (ρ : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →* Perm (Fin k)),
      Function.Surjective ρ → k < 2 * p)
    (φ : ↥(barM M L) ≃* AltB (Fin n))
    (hE : ((barM M (S ⊓ L)).subgroupOf (barM M L)).map φ.toMonoidHom = EA (Fin n))
    (hB : ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).map
      φ.toMonoidHom = NA (Fin n))
    {U : Subgroup G} (hUM : U ≤ M) (hUS : U ≤ Subgroup.normalizer (S : Set G))
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hUp : IsPGroup p U) :
    (U ⊓ blockCentralizer M L).relIndex U ≤ p := by
  have hBC : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L := AGLEmbedding.barM_mono inf_le_right
  have hcard : Fintype.card (Fin n × Bool) = 2 * n := by simp [mul_comm]
  have hk : n < 2 * p := by
    let ψB := sectionEquiv hBC φ (NA (Fin n)) hB
    exact hlt n (blockAction.comp ψB.toMonoidHom) (blockAction_surjective.comp ψB.surjective)
  obtain ⟨π, hπ, hker⟩ := exists_block_action (by omega) (by omega) φ hUM hUL
  have hAlt : ∀ u, π u ∈ alternatingGroup (Fin n × Bool) :=
    mem_alternatingGroup_of_isPGroup hp hp2 hUp π
  have hNA : ∀ u : ↥U, (⟨π u, hAlt u⟩ : AltB (Fin n)) ∈ NA (Fin n) := by
    intro u
    have h1 := perm_mem_normalizer φ (EA (Fin n)) hE
      (mk_mem_normalizer_barM (hUM u.2) (hUL u.2))
      (mk_mem_normalizer_barM (hUM u.2) (mem_normalizer_inf (hUS u.2) (hUL u.2))) (hπ u) (hAlt u)
    rwa [normalizer_EA (by simp; omega)] at h1
  let πA : ↥U →* AltB (Fin n) := π.codRestrict (alternatingGroup _) hAlt
  have hker2 : IsPGroup 2 (blockAction (ι := Fin n)).ker := by
    rw [ker_blockAction]
    exact isPGroup_two_EA_subgroupOf
  have h := index_ker_le_of_two_kernel hp hp2 hk hUp πA (T := NA (Fin n)) hNA blockAction hker2
  have hkerA : πA.ker = π.ker := MonoidHom.ker_codRestrict _ _ _
  rw [hkerA, hker] at h
  exact h

end CFSG.HardMathSupport.RichardWeiss.Coordinator
