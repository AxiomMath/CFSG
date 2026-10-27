module

public import CFSG.GH74.GLS.C3.Layer1.BkW5Class
public import CFSG.GH74.GLS.C3.Layer2.L5C20

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.W5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
open scoped commutatorElement
open CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfigW 5 x K T Q S a}

namespace Coord

theorem exists_model
    {c : Coord h} {S₁ : Subgroup G} (hrec1 : Rec1Stmt) (hS : c.S1Data S₁) :
    Nonempty (c.ModelIso hS Sh0 tr16 yHat) ∨ Nonempty (c.ModelIso hS Sh1 tr1 yHat1) := by
  have hconj : ∀ (s : ↥S₁) (i : Fin 16), s * c.iotaS1 hS.hT (elT i) * s⁻¹ =
      c.iotaS1 hS.hT (elT (c.rhoS1 hS.hN s i)) := by
    intro s i
    apply Subtype.ext
    show (s : G) * c.iotaT (elT i) * (s : G)⁻¹ = c.iotaT (elT (c.rhoG ⟨s, hS.hN s.2⟩ i))
    rw [c.iotaT_elT, c.iotaT_elT]
    exact (rhoG_spec c ⟨s, hS.hN s.2⟩ i).symm
  have hrange : ∀ s : ↥S₁, c.rhoS1 hS.hN s ∈ d8L := fun s => by
    have := hS.range s s.2
    rwa [rhoT_of_mem (hS.hN s.2)] at this
  have hsurj : ∀ d ∈ d8L, ∃ s : ↥S₁, c.rhoS1 hS.hN s = d := fun d hd => by
    obtain ⟨s, hs, hsd⟩ := hS.surj d hd
    rw [rhoT_of_mem (hS.hN hs)] at hsd
    exact ⟨⟨s, hs⟩, hsd⟩
  have hker : ∀ s : ↥S₁, c.rhoS1 hS.hN s = 1 → ∃ i, s = c.iotaS1 hS.hT (elT i) := fun s hs1 => by
    have hs2 : c.rhoT (s : G) = 1 := by
      rw [rhoT_of_mem (hS.hN s.2)]
      exact hs1
    have hR := hS.ker s s.2 hs2
    refine ⟨idx16 (c.rco s), Subtype.ext ?_⟩
    show (s : G) = c.iotaT (elT (idx16 (c.rco s)))
    rw [c.iotaT_elT]
    exact exists_liftEl c hR
  rcases hrec1 ↥S₁ (c.iotaS1 hS.hT) (c.rhoS1 hS.hN) hS.card (c.iotaS1_injective hS.hT) hconj
      hrange hsurj hker with ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩
  · exact Or.inl ⟨⟨ψ, hψ⟩⟩
  · exact Or.inr ⟨⟨ψ, hψ⟩⟩

theorem case48_false
    
    {ι : Type} {X : ι → Type} [∀ ty, Group (X ty)] [∀ ty, Finite (X ty)]
    {inc : ∀ ty, ↥Sh0 →* X ty} (F : Case48Facts X inc) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {c : Coord h} (hRed : c.Red) : False := by
  have hT : IsPGroup 2 ↥T := (isSylowOf_iff.1 h.sylowT).2.1
  obtain ⟨S₁, hS⟩ := exists_S1Data F.c2 hT hRed.nbar
  rcases exists_model F.rec1 hS with ⟨⟨Ψ⟩⟩ | ⟨⟨Ψ⟩⟩
  · by_cases hsyl : IsSylow2In S₁ ⊤
    · have hFus : FusionHyp ↥Sh0 embHom0 (Erel Ψ.ψ) :=
        fusionHyp_of_model c hs hnab hRed.nbar hsyl hS.hT Ψ.ψ embHom0
          (fun t => Subtype.ext (Ψ.spec t))
      exact class0_false_of_sylow hsyl hs hnab Ψ (F.engine0 _ hFus) F.notge
    · exact class0_false_of_not_sylow F.sh2 F.c2 hRed hs hnab Ψ hsyl
  · have hsyl : IsSylow2In S₁ ⊤ := class1_sylow F.c2 hRed F.aut1 Ψ
    have hFus : FusionHyp ↥Sh1 embHom1 (Erel Ψ.ψ) :=
      fusionHyp_of_model c hs hnab hRed.nbar hsyl hS.hT Ψ.ψ embHom1
        (fun t => Subtype.ext (Ψ.spec t))
    have hrho : ∀ n : ↥c.N, c.rhoG n ∈ n24L := fun n =>
      class1_rho_mem F.c2 hRed F.noCHat Ψ n
    have hweak : ∀ g : G, (c.lift Rm).map (MulAut.conj g).toMonoidHom ≤ S₁ →
        (c.lift Rm).map (MulAut.conj g).toMonoidHom = c.lift Rm := fun g hg =>
      class1_weak F.e16_1 Ψ g hg
    refine F.engine1 _ hFus ?_
    intro i j hij
    have hsymm : ∀ t : ↥T5, ((Ψ.ψ.symm (embHom1 t) : ↥S₁) : G) = c.iotaT t := fun t => by
      have : Ψ.ψ (c.iotaS1 hS.hT t) = embHom1 t := Subtype.ext (Ψ.spec t)
      rw [← this, MulEquiv.symm_apply_apply]
      rfl
    have hij' : IsConj ((Ψ.ψ.symm (embHom1 (elT i)) : ↥S₁) : G)
        ((Ψ.ψ.symm (embHom1 (elT j)) : ↥S₁) : G) := hij
    rw [hsymm, hsymm, c.iotaT_elT, c.iotaT_elT] at hij'
    exact class1_RExact hS hsyl hweak hrho i j (isConj_iff.1 hij')

end Coord

end CFSG.GH74.GLS.C3.Layer1.Bk.W5

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Prop121

theorem aconfigW_five_shadow_false

    {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G)
    {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a)
    (hnP : ∀ g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G),
      conjugate Q g ≠ T ⊓ K) : False := by
  obtain ⟨y, _, _, _, _, q, _, hyq⟩ := aconfigW_five_y h
  have hnab : ∃ u v : G, u * v ≠ v * u := ⟨y, q, hyq⟩
  obtain ⟨c⟩ := W5.exists_coord h
  obtain ⟨hP, hncard⟩ := W5.Coord.fam_shadow c hnP
  obtain ⟨c', hRed⟩ := W5.Coord.exists_red c1facts c hP hncard
  exact W5.Coord.case48_false case48Facts hs hnab hRed

theorem b_P46_shadow_proof
    : B_P46_shadow := by
  intro G _ _ hG x K T Q S a h hnP
  exact aconfigW_five_shadow_false (isKProperSimple_iff.1 hG.kproper).1 h hnP

end CFSG.GH74.GLS.C3.Layer1.Bk
