module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviCentral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.KFactLevi

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open

section Quasi

theorem isQuasisimple_of_central_quotient {E Ē : Type*} [Group E] [Group Ē]
    (hE : Open.IsQuasisimple E) (ψ : E →* Ē) (hψ : Function.Surjective ψ)
    (hcentral : ∀ e ∈ ψ.ker, e ∈ Subgroup.center E) : Open.IsQuasisimple Ē := by
  obtain ⟨hp, hs⟩ := hE
  obtain ⟨e⟩ := centerQuotientEquiv ψ hψ hcentral hp
  refine ⟨?_, ?_⟩
  · rw [_root_.commutator_def] at hp ⊢
    rw [← Subgroup.map_top_of_surjective ψ hψ, ← Subgroup.map_commutator, hp]
  · have := hs
    exact e.symm.isSimpleGroup

theorem isQuasisimple_top {E : Type} [Group E] (hE : Open.IsQuasisimple E) :
    Open.IsQuasisimple ↥(⊤ : Subgroup E) :=
  isQuasisimple_of_mulEquiv_open Subgroup.topEquiv.symm hE

theorem normal_le_center_or_eq_top {E : Type} [Group E] (hE : Open.IsQuasisimple E)
    (N : Subgroup E) [N.Normal] : N ≤ Subgroup.center E ∨ N = ⊤ := by
  have hN : (⊤ : Subgroup E) ≤ Subgroup.normalizer (N : Set E) := fun x _ =>
    (Subgroup.normalizer_eq_top_iff.mpr ‹N.Normal›) ▸ Subgroup.mem_top x
  rcases le_centerOf_or_eq_of_isQuasisimple (isQuasisimple_top hE) le_top hN with h | h
  · left
    intro x hx
    exact Subgroup.mem_center_iff.2 fun y => (Subgroup.mem_centralizer_iff.1 (h hx).2 y
      (Subgroup.mem_top y))
  · right
    exact h

theorem isQuasisimple_quot_pCore_of_normal_two {G : Type} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hN : IsPGroup 2 ↥N) (hq : Open.IsQuasisimple (G ⧸ N)) :
    Open.IsQuasisimple (G ⧸ CFSG.pCore 2 G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : N ≤ CFSG.pCore 2 G := le_sSup ⟨‹N.Normal›, hN⟩
  have hle' : N ≤ (CFSG.pCore 2 G).comap (MonoidHom.id G) := hle
  let ψ : G ⧸ N →* G ⧸ CFSG.pCore 2 G := QuotientGroup.map N (CFSG.pCore 2 G) (MonoidHom.id G) hle'
  have hψ : Function.Surjective ψ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g => exact ⟨g, rfl⟩
  set K₂ : Subgroup (G ⧸ N) := (CFSG.pCore 2 G).map (QuotientGroup.mk' N) with hK₂
  have hK₂n : K₂.Normal := CFSG.pCore_normal.map _ (QuotientGroup.mk'_surjective N)
  have hK₂p : IsPGroup 2 ↥K₂ := CFSG.pCore_isPGroup.map _
  have hker : ψ.ker ≤ K₂ := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H g =>
      have : g ∈ CFSG.pCore 2 G := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
      exact ⟨g, this, rfl⟩
  rcases normal_le_center_or_eq_top hq K₂ with hc | ht
  · exact isQuasisimple_of_central_quotient hq ψ hψ fun e he => hc (hker he)
  · exfalso
    have h1 : IsPGroup 2 ↥(⊤ : Subgroup (G ⧸ N)) := ht ▸ hK₂p
    have hnt := nontrivial_of_isQuasisimple (isQuasisimple_top hq)
    exact false_of_isPGroup_of_perfect h1 (isQuasisimple_top hq).1

theorem leviAlt_of_central_quotient {A Ā : Type} [Group A] [Finite A] [Group Ā] (φ : A →* Ā)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A) (h : LeviAlt A) :
    LeviAlt Ā := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Ā := Finite.of_surjective φ hφ
  rcases h with hs | hq
  · left
    exact Group.isSolvable_of_surjective hφ
  · right
    set pA := CFSG.pCore 2 A with hpA
    set pB := CFSG.pCore 2 Ā with hpB
    have hmap : pA.map φ ≤ pB :=
      le_sSup ⟨CFSG.pCore_normal.map φ hφ, CFSG.pCore_isPGroup.map φ⟩
    have hle : pA ≤ pB.comap φ := Subgroup.map_le_iff_le_comap.1 hmap
    let ψ : A ⧸ pA →* Ā ⧸ pB := QuotientGroup.map pA pB φ hle
    have hψ : Function.Surjective ψ := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H b =>
        obtain ⟨a, rfl⟩ := hφ b
        exact ⟨a, rfl⟩
    have hcentral : ∀ e ∈ ψ.ker, e ∈ Subgroup.center (A ⧸ pA) := by
      intro e he
      induction e using QuotientGroup.induction_on with
      | H n =>
        have hn : φ n ∈ pB := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 he)
        obtain ⟨y, hy, z, hz, -, rfl⟩ := exists_decomp_of_map_mem_pCore φ hφ hker hn
        have e : (QuotientGroup.mk (y * z) : A ⧸ pA) = QuotientGroup.mk z := by
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul]
        refine Subgroup.mem_center_iff.2 fun g => ?_
        induction g using QuotientGroup.induction_on with
        | H g =>
          rw [e, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            Subgroup.mem_center_iff.1 (hker hz) g]
    exact isQuasisimple_of_central_quotient hq ψ hψ hcentral

end Quasi

end CFSG.AGLEmbeddingD2.Tits.GN516
