module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecP3

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open scoped MatrixGroups Matrix IsMulCommutative

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

section Core

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {N : Type} [Group N] [Finite N]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem section_core {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (ρ : N →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ) (L : Subgroup N) [L.Normal]
    (hLq : CFSG.IsQuasisimple ↥L) {φ : SL(3, F) →* ↥L} (h : Cover φ)
    (hex : ∃ (g : N) (B : GL (Fin 3) F) (j : ℕ), ∀ x : SL(3, F),
      g * ((φ x : ↥L) : N) * g⁻¹ = ((φ (graphFieldHom B j x) : ↥L) : N))
    {A : Subgroup N} (hAne : A ≠ ⊥) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hLA : ⁅L, A⁆ = L)
    (hoff : Nat.card W ≤ weight ρ A)
    (hstrict : ∀ D : Subgroup N, ⊥ < D → D < A → weight ρ D < weight ρ A)
    (hquad : QuadAct ρ A) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module (ZMod 2) U) (_ : Finite U)
      (ρL : Representation (ZMod 2) ↥L U) (A' : Subgroup (U ≃ₗ[ZMod 2] U)),
      (∀ x : SL(3, F), ρL (φ x) = 1 → x ∈ scalars 3 F) ∧
      Representation.IsIrreducible (ρL.comp φ) ∧
      Nonempty (Representation.Equiv (ρL.comp φ) (Representation.dual (ρL.comp φ))) ∧
      CFSG.IsElementaryAbelian 2 ↥A' ∧ A' ≠ ⊥ ∧
      (∀ a ∈ A', ∀ x : SL(3, F), ∃ y : SL(3, F), Intertwines (ρL.comp φ) a x y) ∧
      Nat.card U ≤ Nat.card A' * Nat.card {u : U // ∀ a ∈ A', a u = u} := by
  classical
  have : Group.IsPerfect ↥L := hLq.1
  have hf1 : 1 ≤ f := by omega
  have hA2 : ∀ a : N, a ∈ A → a * a = 1 := fun a ha => sq_of_mem ha
  obtain ⟨B, Z, hos⟩ := orbitSemisimpleSection ρ L A hρ hLq hAne hAel hLA hoff hstrict
  obtain ⟨hMA, hoffM⟩ := hos.offender_M
  obtain ⟨𝒰, h𝒰, hfam, hsup⟩ := hos.family
  have hUM : ∀ U ∈ 𝒰, U ≤ B.map (fixSub ρ L).mkQ := fun U hU => by
    rw [← hsup]
    exact Finset.le_sup (f := id) hU
  have hquad' : QuadAct (cvAct ρ L) A := by
    intro b hb c hc v
    obtain ⟨w, rfl⟩ := (fixSub ρ L).mkQ_surjective v
    have h1 : cvAct ρ L b ((fixSub ρ L).mkQ w) - (fixSub ρ L).mkQ w =
        (fixSub ρ L).mkQ (ρ b w - w) := by
      rw [cvAct_mkQ, map_sub]
    rw [h1, cvAct_mkQ, hquad b hb c hc w]
  have h𝒰ne : 𝒰.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hos.M_ne_bot
    intro b hb
    have hmem : (fixSub ρ L).mkQ b ∈ B.map (fixSub ρ L).mkQ := ⟨b, hb, rfl⟩
    rw [← hsup, hemp, Finset.sup_empty, Submodule.mem_bot] at hmem
    exact (Submodule.Quotient.mk_eq_zero _).1 hmem
  obtain ⟨U₀, h0⟩ := h𝒰ne
  have hsd := selfDual_of_mem hf hF (cvAct ρ L) L hLq h hquad' hex hos.not_central hMA hoffM
    hos.ker_M 𝒰 h𝒰 hfam hUM h0
  have hU₀ : IsNontrivialLSimple (cvAct ρ L) L U₀ := (h𝒰 U₀ h0).1
  have hU₀A : Offender.IsInvariant (cvAct ρ L) A U₀ := (h𝒰 U₀ h0).2
  have hU₀L : Offender.IsInvariant (cvAct ρ L) L U₀ := hU₀.1.1
  have hker : centSub ((cvAct ρ L).comp A.subtype) U₀ =
      centSub ((cvAct ρ L).comp A.subtype) (B.map (fixSub ρ L).mkQ) := by
    rw [centSub_eq_of_simple (cvAct ρ L) L hLq hU₀ hU₀A]
    ext a
    rw [mem_centSub, Subgroup.mem_subgroupOf]
    exact (hos.ker_M a a.2).symm
  have hoffU := offender_of_sub (cvAct ρ L) A hMA hU₀A (hUM U₀ h0) hker hoffM
  refine ⟨↥U₀, inferInstance, inferInstance, inferInstance,
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (resSub (cvAct ρ L) L U₀ hU₀L), (resSub (cvAct ρ L) A U₀ hU₀A).range, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x hx
    exact srep_ker_scalars (cvAct ρ L) L hLq h hU₀ x hx
  · exact srep_isIrreducible (cvAct ρ L) L φ h.surjective U₀ hU₀L hU₀.1
  · exact hsd
  · refine isElementaryAbelian_two_of_forall' _ ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
      rw [← map_mul, ← map_mul, show a * c = c * a from Subtype.ext (comm_of_mem a.2 c.2)]
    · rintro _ ⟨a, rfl⟩
      rw [← map_mul, show a * a = 1 from Subtype.ext (hA2 a a.2), map_one]
  · intro hbot
    obtain ⟨a₀, ha₀, ha₀c⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (L : Set N) := by
      by_contra hcon
      push Not at hcon
      exact hos.not_central hcon
    have hmem : resSub (cvAct ρ L) A U₀ hU₀A ⟨a₀, ha₀⟩ ∈
        (resSub (cvAct ρ L) A U₀ hU₀A).range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply ha₀c
    refine (fix_iff_centralizer (cvAct ρ L) L hLq hU₀ (hA2 a₀ ha₀) (fun u hu => hU₀A a₀ ha₀ u hu)).1
      fun u hu => ?_
    have h2 := congrArg (fun g : ↥U₀ ≃ₗ[ZMod 2] ↥U₀ => g ⟨u, hu⟩) hmem
    have h3 := congrArg Subtype.val h2
    rw [resSub_apply] at h3
    exact h3
  · rintro _ ⟨a, rfl⟩ x
    obtain ⟨y, hy⟩ := h.surjective ⟨(a : N) * ((φ x : ↥L) : N) * (a : N)⁻¹,
      Subgroup.Normal.conj_mem inferInstance _ (φ x).2 (a : N)⟩
    refine ⟨y, fun u => ?_⟩
    apply Subtype.ext
    have hy' : ((φ y : ↥L) : N) = (a : N) * ((φ x : ↥L) : N) * (a : N)⁻¹ :=
      congrArg (fun l : ↥L => (l : N)) hy
    show (cvAct ρ L (a : N)) (cvAct ρ L ((φ x : ↥L) : N) (u : _)) =
      (cvAct ρ L ((φ y : ↥L) : N)) (cvAct ρ L (a : N) (u : _))
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hy']
    congr 2
    group
  · have h1 : Nat.card ↥(fixSub (MonoidHom.id (↥U₀ ≃ₗ[ZMod 2] ↥U₀))
        (resSub (cvAct ρ L) A U₀ hU₀A).range) =
        Nat.card {u : ↥U₀ // ∀ a ∈ (resSub (cvAct ρ L) A U₀ hU₀A).range, a u = u} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => Iff.rfl)
    unfold weight at hoffU
    rw [h1] at hoffU
    exact hoffU

end Core

end CFSG.QuasithinUnique.Setup.X7Sec
