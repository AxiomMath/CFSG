module

public import CFSG.GH74.GLS.C3.Layer2.L5C18
public import CFSG.GH74.GLS.C3.Layer2.L5B15
public import CFSG.GH74.GLS.C3.Layer2.L5C16

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

@[expose] def Rec1Stmt : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (ι : ↥T5 →* S) (ρ : S →* Perm (Fin 16)),
    Nat.card S = 128 → Function.Injective ι →
    (∀ s i, s * ι (elT i) * s⁻¹ = ι (elT (ρ s i))) → (∀ s, ρ s ∈ d8L) →
    (∀ d ∈ d8L, ∃ s, ρ s = d) → (∀ s, ρ s = 1 → ∃ i, s = ι (elT i)) →
    (∃ ψ : S ≃* ↥Sh0, ∀ t, (ψ (ι t) : Perm (Fin 16)) = emb48 tr16 yHat t) ∨
    (∃ ψ : S ≃* ↥Sh1, ∀ t, (ψ (ι t) : Perm (Fin 16)) = emb48 tr1 yHat1 t)

structure Case48Facts
    {ι : Type} (X : ι → Type) [∀ ty, Group (X ty)] [∀ ty, Finite (X ty)]
    (inc : ∀ ty, ↥Sh0 →* X ty) : Prop where
  c1 : C1Facts
  c2 : C1Facts2
  rec1 : Rec1Stmt
  sh2 : Sh2Contract X inc
  aut1 : ∀ γ : ↥Sh1 ≃* ↥Sh1, ∀ r : ↥Sh1, (r : Perm (Fin 16)) ∈ RsubP1 →
    ((γ r : ↥Sh1) : Perm (Fin 16)) ∈ RsubP1
  e16_1 : ∀ B : Subgroup (Perm (Fin 16)), B ≤ Sh1 → Nat.card B = 16 → (∀ b ∈ B, b * b = 1) →
    (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → B = RsubP1
  noCHat : ¬ ∃ γ : ↥S0subP1 ≃* ↥S0subP1, ∀ (s : ↥S0subP1) (i : Fin 16),
    (s : Perm (Fin 16)) = tr1 i → ((γ s : ↥S0subP1) : Perm (Fin 16)) = tr1 (cHat i)
  notge : ¬ RsubP0 ≤ R1subP
  engine0 : ∀ E : ↥Sh0 → ↥Sh0 → Prop, FusionHyp ↥Sh0 embHom0 E →
    ∀ a b : ↥Sh0, (a : Perm (Fin 16)) ∈ R1subP → a * a = 1 → b * b = 1 → E a b →
      (b : Perm (Fin 16)) ∈ R1subP
  engine1 : ∀ E : ↥Sh1 → ↥Sh1 → Prop, FusionHyp ↥Sh1 embHom1 E →
    (∀ a b : Fin 16, E (embHom1 (elT a)) (embHom1 (elT b)) → ∃ A ∈ n24L, A a = b) → False

section Assembly

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} {S₁ : Subgroup G}

theorem Coord5.exists_model
    (hrec1 : Rec1Stmt) (hS : c.S1Data S₁) :
    Nonempty (c.ModelIso hS Sh0 tr16 yHat) ∨ Nonempty (c.ModelIso hS Sh1 tr1 yHat1) := by
  have hconj : ∀ (s : ↥S₁) (i : Fin 16), s * c.iotaS1 hS.hT (elT i) * s⁻¹ =
      c.iotaS1 hS.hT (elT (c.rhoS1 hS.hN s i)) := by
    intro s i
    apply Subtype.ext
    show (s : G) * c.iotaT (elT i) * (s : G)⁻¹ = c.iotaT (elT (c.rhoG ⟨s, hS.hN s.2⟩ i))
    rw [c.iotaT_elT, c.iotaT_elT]
    exact (Coord5.rhoG_spec c ⟨s, hS.hN s.2⟩ i).symm
  have hrange : ∀ s : ↥S₁, c.rhoS1 hS.hN s ∈ d8L := fun s => by
    have := hS.range s s.2
    rwa [Coord5.rhoT_of_mem (hS.hN s.2)] at this
  have hsurj : ∀ d ∈ d8L, ∃ s : ↥S₁, c.rhoS1 hS.hN s = d := fun d hd => by
    obtain ⟨s, hs, hsd⟩ := hS.surj d hd
    rw [Coord5.rhoT_of_mem (hS.hN hs)] at hsd
    exact ⟨⟨s, hs⟩, hsd⟩
  have hker : ∀ s : ↥S₁, c.rhoS1 hS.hN s = 1 → ∃ i, s = c.iotaS1 hS.hT (elT i) := fun s hs1 => by
    have hs2 : c.rhoT (s : G) = 1 := by
      rw [Coord5.rhoT_of_mem (hS.hN s.2)]
      exact hs1
    have hR := hS.ker s s.2 hs2
    refine ⟨idx16 (c.rco s), Subtype.ext ?_⟩
    show (s : G) = c.iotaT (elT (idx16 (c.rco s)))
    rw [c.iotaT_elT]
    exact Coord5.exists_liftEl c hR
  rcases hrec1 ↥S₁ (c.iotaS1 hS.hT) (c.rhoS1 hS.hN) hS.card (c.iotaS1_injective hS.hT) hconj
      hrange hsurj hker with ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩
  · exact Or.inl ⟨⟨ψ, hψ⟩⟩
  · exact Or.inr ⟨⟨ψ, hψ⟩⟩

theorem Coord5.case48_false
    {ι : Type} {X : ι → Type} [∀ ty, Group (X ty)] [∀ ty, Finite (X ty)]
    {inc : ∀ ty, ↥Sh0 →* X ty} (F : Case48Facts X inc) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hRed : c.Red) : False := by
  have hT : IsPGroup 2 ↥T := (isSylowOf_iff.1 h.sylowT).2.1
  obtain ⟨S₁, hS⟩ := Coord5.exists_S1Data F.c2 hT hRed.nbar
  rcases Coord5.exists_model F.rec1 hS with ⟨⟨Ψ⟩⟩ | ⟨⟨Ψ⟩⟩
  · by_cases hsyl : IsSylow2In S₁ ⊤
    · have hFus : FusionHyp ↥Sh0 embHom0 (Erel Ψ.ψ) :=
        c.fusionHyp_of_model hs hnab hRed.nbar hsyl hS.hT Ψ.ψ embHom0
          (fun t => Subtype.ext (Ψ.spec t))
      exact c.class0_false_of_sylow hsyl hs hnab Ψ (F.engine0 _ hFus) F.notge
    · exact c.class0_false_of_not_sylow F.sh2 F.c2 hRed hs hnab Ψ hsyl
  · have hsyl : IsSylow2In S₁ ⊤ := c.class1_sylow F.c2 hRed F.aut1 Ψ
    have hFus : FusionHyp ↥Sh1 embHom1 (Erel Ψ.ψ) :=
      c.fusionHyp_of_model hs hnab hRed.nbar hsyl hS.hT Ψ.ψ embHom1
        (fun t => Subtype.ext (Ψ.spec t))
    have hrho : ∀ n : ↥c.N, c.rhoG n ∈ n24L := fun n =>
      c.class1_rho_mem F.c2 hRed F.noCHat Ψ n
    have hweak : ∀ g : G, (c.lift Rm).map (MulAut.conj g).toMonoidHom ≤ S₁ →
        (c.lift Rm).map (MulAut.conj g).toMonoidHom = c.lift Rm := fun g hg =>
      c.class1_weak F.e16_1 Ψ g hg
    refine F.engine1 _ hFus ?_
    intro i j hij
    have hsymm : ∀ t : ↥T5, ((Ψ.ψ.symm (embHom1 t) : ↥S₁) : G) = c.iotaT t := fun t => by
      have : Ψ.ψ (c.iotaS1 hS.hT t) = embHom1 t := Subtype.ext (Ψ.spec t)
      rw [← this, MulEquiv.symm_apply_apply]
      rfl
    have hij' : IsConj ((Ψ.ψ.symm (embHom1 (elT i)) : ↥S₁) : G)
        ((Ψ.ψ.symm (embHom1 (elT j)) : ↥S₁) : G) := hij
    rw [hsymm, hsymm, c.iotaT_elT, c.iotaT_elT] at hij'
    exact c.class1_RExact hS hsyl hweak hrho i j (isConj_iff.1 hij')

end Assembly

end CFSG.GH74.GLS.C3.Layer2.L5

namespace CFSG.GH74.GLS

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Prop121

theorem s_case48_of_facts
    {ι : Type} {X : ι → Type} [∀ ty, Group (X ty)] [∀ ty, Finite (X ty)]
    {inc : ∀ ty, ↥Sh0 →* X ty} (F : Case48Facts X inc) : S_Case48 := by
  intro G _ _ hG x K T Q S a h c hcase
  obtain ⟨hs, hnab, -⟩ := isKProperSimple_iff.1 hG.kproper
  obtain ⟨c', hRed⟩ := exists_red F.c1 c hG.pRank_eq_four.le hcase.1 hcase.2
  exact c'.case48_false F hs hnab hRed

end CFSG.GH74.GLS
