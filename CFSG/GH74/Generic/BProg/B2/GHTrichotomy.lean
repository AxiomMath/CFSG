module

public import CFSG.GH74.Generic.BProg.Stage2Defs
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

namespace GHTrichotomy

theorem center_eq_bot_of_simple_nonab {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hn : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  obtain ⟨a, b, hab⟩ := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hb | ht
  · exact hb
  · exfalso
    have ha : a ∈ center X := by rw [ht]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem ofLieType_of_lieModel {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hn : ∃ a b : X, a * b ≠ b * a) {t : StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) :
    OfLieType X := by
  have hc : center X = ⊥ := center_eq_bot_of_simple_nonab hs hn
  let e : X ≃* X ⧸ center X :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact ⟨t, n, p, f, CFSG.GH74.lieModel_of_mulEquiv e h⟩

theorem not_isSolvable_of_isQuasisimple {C : Type*} [Group C] (hQ : CFSG.IsQuasisimple C) :
    ¬ Group.IsSolvable C := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have : Nontrivial C := (QuotientGroup.mk_surjective (s := Subgroup.center C)).nontrivial
  exact Group.IsPerfect.not_isSolvable C

theorem isSolvable_of_eq_generalizedFitting {Y : Type} [Group Y] [Finite Y] {F : Subgroup Y}
    (hF : F = generalizedFitting Y) (hsimple : IsSimpleGroup ↥F)
    (hcomm : ∀ a b : ↥F, a * b = b * a) : Group.IsSolvable Y := by
  subst hF
  have hFn : (generalizedFitting Y).Normal := (CFSG.LocalCores.generalized_fitting_characteristic).2
  have : IsMulCommutative ↥(generalizedFitting Y) := ⟨⟨hcomm⟩⟩
  have : IsCyclic ↥(generalizedFitting Y) := by
    have hp : (Nat.card ↥(generalizedFitting Y)).Prime := (Group.is_simple_iff_prime_card).1 hsimple
    have : Fact (Nat.card ↥(generalizedFitting Y)).Prime := ⟨hp⟩
    exact isCyclic_of_prime_card rfl
  have : Group.IsSolvable ↥(generalizedFitting Y) := inferInstance
  have : Group.IsSolvable (MulAut ↥(generalizedFitting Y)) := by
    have e := IsCyclic.mulAutMulEquiv (G := ↥(generalizedFitting Y))
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  refine Group.isSolvable_of_ker_le_range (generalizedFitting Y).subtype
    (MulAut.conjNormal : Y →* MulAut ↥(generalizedFitting Y)) ?_
  intro g hg
  have hg' : ∀ f : ↥(generalizedFitting Y), g * f * g⁻¹ = f := by
    intro f
    have := congrArg (fun φ : MulAut ↥(generalizedFitting Y) => ((φ f : ↥(generalizedFitting Y)) : Y))
      (MonoidHom.mem_ker.1 hg)
    simpa [MulAut.conjNormal_apply] using this
  have hcent : g ∈ Subgroup.centralizer (generalizedFitting Y : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := hg' ⟨h, hh⟩
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  exact ⟨⟨g, centralizer_generalizedFitting_le Y hcent⟩, rfl⟩

theorem isSolvable_of_quotient_pPrimeCore {M : Type} [Group M] [Finite M]
    (h : Group.IsSolvable (M ⧸ pPrimeCore 2 M)) : Group.IsSolvable M := by
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 M)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hsolv : Group.IsSolvable ↥(pPrimeCore 2 M) := CFSG.Milestones.odd_order_solvable hodd
  refine Group.isSolvable_of_ker_le_range (pPrimeCore 2 M).subtype
    (QuotientGroup.mk' (pPrimeCore 2 M)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

end GHTrichotomy

theorem ghList_trichotomy {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hn : ∃ a b : X, a * b ≠ b * a) (h : GHList X) :
    OfLieType X ∨ (∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      (∃ s : TauCeti.SporadicName, s ∈ ({.M11, .M12, .M22, .M23, .J1, .J2, .J3, .McL, .Ly} :
        Finset TauCeti.SporadicName) ∧ NativeSporadic.IsSporadic X s) := by
  rcases h with ⟨n, hn7, hn11, he⟩ | (h | h | h | h | h | h | h | h | h) |
      ⟨p, f, hp, hf, hrow⟩
  · exact Or.inr (Or.inl ⟨n, hn7, hn11, he⟩)
  · exact Or.inr (Or.inr ⟨.M11, by simp, h⟩)
  · exact Or.inr (Or.inr ⟨.M12, by simp, h⟩)
  · exact Or.inr (Or.inr ⟨.M22, by simp, h⟩)
  · exact Or.inr (Or.inr ⟨.M23, by simp, h⟩)
  · exact Or.inr (Or.inr ⟨.J1, by simp, h⟩)
  · exact Or.inr (Or.inr ⟨.J2, by simp, h⟩)
  · exact Or.inr (Or.inr ⟨.J3, by simp, h⟩)
  · exact Or.inr (Or.inr ⟨.McL, by simp, h⟩)
  · exact Or.inr (Or.inr ⟨.Ly, by simp, h⟩)
  · refine Or.inl ?_
    rcases hrow with ⟨-, h | h | h | h | h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h |
      ⟨-, h | h | h | h | h⟩
    all_goals exact GHTrichotomy.ofLieType_of_lieModel hs hn h

theorem barIn_nonabelian {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h3 : Stage3A x A M H) :
    ∃ a b : ↥(barIn M H), a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a b : ↥(barIn M H), a * b = b * a := fun a b => by
    by_contra h
    exact hcon ⟨a, b, h⟩
  obtain ⟨hF, hsimple⟩ := h3.H_simple
  have hsolvbar : Group.IsSolvable (Mbar M) :=
    GHTrichotomy.isSolvable_of_eq_generalizedFitting hF hsimple hcomm
  have hsolvM : Group.IsSolvable ↥M := GHTrichotomy.isSolvable_of_quotient_pPrimeCore hsolvbar
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hs.pair.1.1.1.2.2
  have hKM : K ≤ M := hK.1.trans h3.Cx_le
  have hsolvK : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKM)
      (Subgroup.inclusion_injective hKM)
  exact GHTrichotomy.not_isSolvable_of_isQuasisimple (TwoThin.isQuasisimple_hat hK) inferInstance

theorem ghList_barIn {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h3 : Stage3A x A M H) : GHList ↥(barIn M H) :=
  GLS.IVK.ghList_of_subgroup_of_quotient hs.hyp.kgh hs.maxM.1
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (QuotientGroup.mk'_surjective _) (barIn M H)
    h3.H_simple.2 (barIn_nonabelian hs h3)

theorem barIn_trichotomy {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h3 : Stage3A x A M H) :
    OfLieType ↥(barIn M H) ∨
      (∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ Nonempty (↥(barIn M H) ≃* alternatingGroup (Fin n))) ∨
      (∃ s : TauCeti.SporadicName, s ∈ ({.M11, .M12, .M22, .M23, .J1, .J2, .J3, .McL, .Ly} :
        Finset TauCeti.SporadicName) ∧ NativeSporadic.IsSporadic ↥(barIn M H) s) :=
  ghList_trichotomy h3.H_simple.2 (barIn_nonabelian hs h3) (ghList_barIn hs h3)

end CFSG.GH74.Generic.BProg.B2
