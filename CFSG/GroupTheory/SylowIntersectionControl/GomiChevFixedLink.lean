module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Tools
import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup

@[expose] def GomiChevFixedLink {G : Type} [Group G] (L I V W : Subgroup G) : Prop :=
  IsSylowOf 2 V L ∧ IsSylowOf 2 W L ∧ ∃ P : Subgroup G, I ≤ normalizer (P : Set G) ∧
    L ⊓ normalizer (V : Set G) ≤ P ∧ L ⊓ normalizer (W : Set G) ≤ P ∧ P < L

private theorem le_of_isSylowOf_of_le_normalizer {G : Type} [Group G] {p : ℕ} {S K X : Subgroup G}
    (hS : IsSylowOf p S K) (hXK : X ≤ K) (hX : IsPGroup p X)
    (hKX : K ≤ normalizer (X : Set G)) : X ≤ S := by
  obtain ⟨Q, rfl⟩ := hS
  have hn : (X.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  intro x hx
  have hX' : IsPGroup p (X.subgroupOf K) := hX.comap_subtype
  have hxQ : (⟨x, hXK hx⟩ : K) ∈ (Q : Subgroup K) :=
    IsPGroup.le_sylow_of_normal (N := X.subgroupOf K) hX' Q
      (show (⟨x, hXK hx⟩ : K) ∈ X.subgroupOf K from hx)
  exact ⟨_, hxQ, rfl⟩

private theorem exists_isSylowOf_le_inf_centralizer {G : Type} [Group G] [Finite G]
    {L I S : Subgroup G} (hI : IsPGroup 2 I) (hIL : I ≤ normalizer (L : Set G))
    (hS : IsSylowOf 2 S (L ⊓ centralizer (I : Set G))) :
    ∃ V : Subgroup G, IsSylowOf 2 V L ∧ I ≤ normalizer (V : Set G) ∧ S ≤ V ∧
      S = V ⊓ centralizer (I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : S ≤ L := hS.le.trans inf_le_left
  have hSC : S ≤ centralizer (I : Set G) := hS.le.trans inf_le_right
  have hIS : I ≤ normalizer (S : Set G) := by
    rw [Subgroup.le_centralizer_iff] at hSC
    exact hSC.trans (Subgroup.centralizer_le_normalizer (S : Set G))
  have hSI : IsPGroup 2 (S ⊔ I : Subgroup G) := IsPGroup.to_sup_of_normal_left' hS.isPGroup hI hIS
  have hSIL : (S ⊔ I : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le (hSK.trans Subgroup.le_normalizer) hIL
  obtain ⟨V, hV, hVnorm⟩ :=
    CFSG.ComponentClassification.Asc76.Sec4.exists_isSylowOf_normalized hSI hSIL
  have hSVnorm : S ≤ normalizer (V : Set G) :=
    fun x hx => hVnorm ((le_sup_left : S ≤ (S ⊔ I : Subgroup G)) hx)
  have hVS : IsPGroup 2 (V ⊔ S : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hV.isPGroup hS.isPGroup hSVnorm
  have hVSL : (V ⊔ S : Subgroup G) ≤ L := sup_le hV.le hSK
  have hVeq : (V ⊔ S : Subgroup G) = V := IsSylowOf.eq_of_le hV le_sup_left hVSL hVS
  have hSV : S ≤ V := (le_sup_right : S ≤ V ⊔ S).trans (le_of_eq hVeq)
  have hIV : I ≤ normalizer (V : Set G) := fun x hx => hVnorm ((le_sup_right : I ≤ S ⊔ I) hx)
  refine ⟨V, hV, hIV, hSV, ?_⟩
  have hQ : IsPGroup 2 (V ⊓ centralizer (I : Set G) : Subgroup G) := hV.isPGroup.to_inf_left
  have hQK : (V ⊓ centralizer (I : Set G) : Subgroup G) ≤ L ⊓ centralizer (I : Set G) :=
    inf_le_inf hV.le le_rfl
  exact (IsSylowOf.eq_of_le hS (le_inf hSV hSC) hQK hQ).symm

private theorem exists_ne_bot_le_inf_centralizer_of_gomiChevFixedLink {G : Type} [Group G]
    [Finite G] (hRad : GomiChevRadical) {L I V W : Subgroup G} (hI : IsPGroup 2 I)
    (hL : IsGomiChevTwo ↥L)
    (hlink : GomiChevFixedLink L I V W) :
    ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ V ⊓ centralizer (I : Set G) ∧
      X ≤ W ⊓ centralizer (I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hW, P, hIP, hVP, hWP, hPL⟩ := hlink
  have hYne : pCoreOf 2 P ≠ ⊥ := (hRad G L V P hL hV hVP hPL).1
  have hVLP : V ≤ P := (le_inf hV.le Subgroup.le_normalizer).trans hVP
  have hWLP : W ≤ P := (le_inf hW.le Subgroup.le_normalizer).trans hWP
  have hYV : pCoreOf 2 P ≤ V :=
    le_of_isSylowOf_of_le_normalizer (hV.of_le hVLP hPL.le)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 P) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hYW : pCoreOf 2 P ≤ W :=
    le_of_isSylowOf_of_le_normalizer (hW.of_le hWLP hPL.le)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 P) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hIY : I ≤ normalizer (pCoreOf 2 P : Set G) :=
    hIP.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P)
  refine ⟨pCoreOf 2 P ⊓ centralizer (I : Set G), ?_, ?_, ?_⟩
  · exact CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot
      Nat.prime_two hI (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) hYne hIY
  · exact le_inf (inf_le_left.trans hYV) inf_le_right
  · exact le_inf (inf_le_left.trans hYW) inf_le_right

private def GomiApprox {G : Type} [Group G] (K C : Subgroup G)
    (R : Subgroup G → Subgroup G → Prop) (V W : Subgroup G) : Prop :=
  V = W ∨ ∀ S₁ S₂ : Subgroup G, IsSylowOf 2 S₁ K → IsSylowOf 2 S₂ K →
    V ⊓ C ≤ S₁ → W ⊓ C ≤ S₂ → Relation.EqvGen R S₁ S₂

private theorem GomiApprox.symm {G : Type} [Group G] {K C : Subgroup G}
    {R : Subgroup G → Subgroup G → Prop} {V W : Subgroup G} (h : GomiApprox K C R V W) :
    GomiApprox K C R W V := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr fun S₁ S₂ hS₁ hS₂ hW₁ hV₂ => ?_
    exact (h S₂ S₁ hS₂ hS₁ hV₂ hW₁).symm

private theorem GomiApprox.trans {G : Type} [Group G] {K C : Subgroup G}
    {R : Subgroup G → Subgroup G → Prop} {σ : Set (Subgroup G)}
    (hC : ∀ B : Subgroup G, B ∈ σ → ∃ S' : Subgroup G, IsSylowOf 2 S' K ∧ B ⊓ C ≤ S')
    {A B D : Subgroup G} (hB : B ∈ σ) (hAB : GomiApprox K C R A B)
    (hBD : GomiApprox K C R B D) : GomiApprox K C R A D := by
  rcases hAB with hAB | hAB
  · rw [hAB]; exact hBD
  rcases hBD with hBD | hBD
  · rw [← hBD]; exact Or.inr hAB
  obtain ⟨S', hS', hBS'⟩ := hC B hB
  refine Or.inr fun S₁ S₂ hS₁ hS₂ hA₁ hD₂ => ?_
  exact Relation.EqvGen.trans S₁ S' S₂ (hAB S₁ S' hS₁ hS' hA₁ hBS')
    (hBD S' S₂ hS' hS₂ hBS' hD₂)

private theorem GomiApprox.of_eqvGen {G : Type} [Group G] {K C : Subgroup G}
    {R : Subgroup G → Subgroup G → Prop} {σ : Set (Subgroup G)}
    {link : Subgroup G → Subgroup G → Prop}
    (hσlink : ∀ A B, link A B → A ∈ σ ∧ B ∈ σ)
    (hC : ∀ B, B ∈ σ → ∃ S' : Subgroup G, IsSylowOf 2 S' K ∧ B ⊓ C ≤ S')
    (hlink : ∀ A B, link A B → GomiApprox K C R A B) :
    ∀ A B, Relation.EqvGen link A B → A ∈ σ → B ∈ σ → GomiApprox K C R A B := by
  have hmem : ∀ A B, Relation.EqvGen link A B → (A ∈ σ ↔ B ∈ σ) := by
    intro A B h
    induction h with
    | rel a b hab => exact ⟨fun _ => (hσlink a b hab).2, fun _ => (hσlink a b hab).1⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  intro A B h
  induction h with
  | rel a b hab => intro _ _; exact hlink a b hab
  | refl a => intro _ _; exact Or.inl rfl
  | symm a b _ ih => intro ha hb; exact (ih hb ha).symm
  | trans a b c h1 h2 ih1 ih2 =>
      intro ha hc
      have hb : b ∈ σ := (hmem b c h2).mpr hc
      exact GomiApprox.trans hC hb (ih1 ha hb) (ih2 hb hc)

theorem not_isPIsolatedOver_of_eqvGen_gomiChevFixedLink (hRad : GomiChevRadical) {G : Type}
    [Group G] [Finite G] {L I U : Subgroup G} (hL : IsGomiChevTwo ↥L) (hI : IsPGroup 2 I)
    (hIL : I ≤ normalizer (L : Set G))
    (hconn : ∀ V : Subgroup G, IsSylowOf 2 V L → I ≤ normalizer (V : Set G) →
      Relation.EqvGen (GomiChevFixedLink L I) U V) :
    ¬ IsPIsolatedOver 2 (L ⊓ centralizer (I : Set G)) ⊥ := by
  intro hiso
  obtain ⟨S, T, hS, hT, hne⟩ := hiso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer (I : Set G)
  let K : Subgroup G := L ⊓ C
  let R : Subgroup G → Subgroup G → Prop := fun A B =>
    IsSylowOf 2 A K ∧ IsSylowOf 2 B K ∧ ⊥ < A ⊓ B
  let σ : Set (Subgroup G) := {V | IsSylowOf 2 V L}
  obtain ⟨V, hVL, hIV, hSV, hSVe⟩ := exists_isSylowOf_le_inf_centralizer hI hIL hS
  obtain ⟨W, hWL, hIW, hTW, hTWe⟩ := exists_isSylowOf_le_inf_centralizer hI hIL hT
  have hVW : Relation.EqvGen (GomiChevFixedLink L I) V W :=
    Relation.EqvGen.trans V U W (hconn V hVL hIV).symm (hconn W hWL hIW)
  have hσC : ∀ B : Subgroup G, B ∈ σ → ∃ S' : Subgroup G, IsSylowOf 2 S' K ∧ B ⊓ C ≤ S' := by
    intro B hB
    obtain ⟨S', hS', hle⟩ := CFSG.ComponentClassification.Asc76.Sec4.exists_isSylowOf_le
      (Q := B ⊓ C) (K := K) hB.isPGroup.to_inf_left (inf_le_inf hB.le le_rfl)
    exact ⟨S', hS', hle⟩
  have hlink : ∀ A B : Subgroup G, GomiChevFixedLink L I A B → GomiApprox K C R A B := by
    intro A B hAB
    by_cases hEq : A = B
    · exact Or.inl hEq
    · refine Or.inr fun S₁ S₂ hS₁ hS₂ hA₁ hB₂ => ?_
      obtain ⟨X, hXne, hXA, hXB⟩ :=
        exists_ne_bot_le_inf_centralizer_of_gomiChevFixedLink hRad hI hL hAB
      have hXlt : ⊥ < S₁ ⊓ S₂ := lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hXne)
        (le_inf (hXA.trans hA₁) (hXB.trans hB₂))
      exact Relation.EqvGen.rel S₁ S₂ ⟨hS₁, hS₂, hXlt⟩
  have happrox : GomiApprox K C R V W :=
    GomiApprox.of_eqvGen (K := K) (C := C) (R := R) (σ := σ) (link := GomiChevFixedLink L I)
      (fun A B h => ⟨h.1, h.2.1⟩) hσC hlink V W hVW hVL hWL
  rcases happrox with hVW' | hrel
  · have hST : S = T := by rw [hSVe, hTWe, hVW']
    exact hne (hST ▸ Relation.EqvGen.refl S)
  · exact hne (hrel S T hS hT (le_of_eq hSVe.symm) (le_of_eq hTWe.symm))

end CFSG.GroupTheory
