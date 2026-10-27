module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3H13
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Count
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X5

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {H : Type} [Group H]

structure D4Section (ρ : H →* (W ≃ₗ[ZMod 2] W)) (L A : Subgroup H) [L.Normal] where
  M : Submodule (ZMod 2) (W ⧸ fixSub ρ L)
  s : Finset (Submodule (ZMod 2) (W ⧸ fixSub ρ L))
  sind : s.SupIndep id
  ssup : s.sup id = M
  ssimple : ∀ U ∈ s, IsNontrivialLSimple (cvAct ρ L) L U
  Minv : ∀ n, ∀ m ∈ M, cvAct ρ L n m ∈ M
  M_ne_bot : M ≠ ⊥
  fix_bot : M ⊓ fixSub (cvAct ρ L) L = ⊥
  A_faithful : ∀ a ∈ A, (∀ m ∈ M, cvAct ρ L a m = m) → a = 1
  offender : Nat.card ↥M ≤ Nat.card ↥A * Nat.card ↥(M ⊓ fixSub (cvAct ρ L) A)

variable [Finite W] [Finite H]

omit [Finite W] [Finite H] in
theorem eq_one_of_mem_center_of_sq {L A : Subgroup H} (hcent : Subgroup.centralizer (L : Set H) =
    (Subgroup.center ↥L).map L.subtype) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hel : CFSG.IsElementaryAbelian 2 ↥A) {a : H} (ha : a ∈ A)
    (hac : a ∈ Subgroup.centralizer (L : Set H)) : a = 1 := by
  have h2 : a * a = 1 := by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    simpa [pow_two] using this
  rw [hcent] at hac
  have hoddm : Odd (Nat.card ((Subgroup.center ↥L).map L.subtype)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]; exact hodd
  exact eq_one_of_involution_mem_odd hoddm hac h2

theorem exists_d4Section (ρ : H →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ)
    (L A : Subgroup H) [L.Normal] (hL : CFSG.IsQuasisimple ↥L)
    (hcent : Subgroup.centralizer (L : Set H) = (Subgroup.center ↥L).map L.subtype)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (hne : A ≠ ⊥)
    (hel : CFSG.IsElementaryAbelian 2 ↥A) (hLA : ⁅L, A⁆ = L) (hoff : Nat.card W ≤ weight ρ A)
    (hstrict : ∀ D : Subgroup H, ⊥ < D → D < A → weight ρ D < weight ρ A) :
    Nonempty (D4Section ρ L A) := by
  classical
  obtain ⟨B, Z, hsec⟩ := orbitSemisimpleSection ρ L A hρ hL hne hel hLA hoff hstrict
  obtain ⟨s, hsind, hssup, hsimple⟩ := hsec.semisimple
  have hMA : Offender.IsInvariant (cvAct ρ L) A (B.map (fixSub ρ L).mkQ) := fun a _ m hm =>
    hsec.invariant_M a m hm
  have hfaith : ∀ a ∈ A, (∀ m ∈ B.map (fixSub ρ L).mkQ, cvAct ρ L a m = m) → a = 1 := by
    intro a ha hfix
    exact eq_one_of_mem_center_of_sq hcent hodd hel ha ((hsec.ker_M a ha).1 hfix)
  refine ⟨⟨B.map (fixSub ρ L).mkQ, s, hsind, hssup, hsimple, hsec.invariant_M, ?_, ?_, hfaith, ?_⟩⟩
  · intro hbot
    apply hsec.M_ne_bot
    intro b hb
    have : (fixSub ρ L).mkQ b ∈ B.map (fixSub ρ L).mkQ := ⟨b, hb, rfl⟩
    rw [hbot] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 ((Submodule.mem_bot _).1 this)
  · rw [← hssup]
    exact fixSub_sup_eq_bot s hsind hsimple
  · obtain ⟨hMA', hoff'⟩ := hsec.offender_M
    have hcs : centSub ((cvAct ρ L).comp A.subtype) (B.map (fixSub ρ L).mkQ) = ⊥ := by
      ext a
      simp only [mem_centSub, Subgroup.mem_bot]
      constructor
      · intro h
        exact Subtype.ext (hfaith a.1 a.2 (fun m hm => h m hm))
      · rintro rfl u _
        simp
    have hw := weightId_range ((cvAct ρ L).comp A.subtype) (B.map (fixSub ρ L).mkQ)
      (fun a w hw => hMA a a.2 w hw)
    rw [hcs, Subgroup.index_bot] at hw
    have hfix : fixSub ((cvAct ρ L).comp A.subtype) ⊤ = fixSub (cvAct ρ L) A := by
      ext v
      simp only [mem_fixSub, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_top,
        forall_const]
      constructor
      · intro h a ha
        exact h ⟨a, ha⟩
      · intro h a
        exact h a.1 a.2
    rw [hfix] at hw
    exact hoff'.trans_eq hw

end CFSG.QuasithinUnique.Setup.X3
