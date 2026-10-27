module

public import CFSG.Sporadic.Co1Block.TwoACent
public import CFSG.Sporadic.Co1Block.TwoCCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

section SubgroupForm

variable {X W : Type*} [Group X] [Group W] (H : Subgroup W)

theorem exists_mulEquiv_map_eq (e : X ≃* H) (a : X) (b : H) (h : IsConj (e a) b) :
    ∃ φ : X ≃* H, φ a = b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact ⟨e.trans (MulAut.conj c), hc⟩

theorem card_centralizer_eq_of_mulEquiv_sub (e : X ≃* H) (a : X) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set X)) =
      Nat.card ↥(Subgroup.centralizer ({e a} : Set H)) :=
  card_centralizer_eq_of_mulEquiv e a

theorem exists_centralizer_mulEquiv (e : X ≃* H) (a : X) (b : H) (h : IsConj (e a) b) :
    Nonempty (↥(Subgroup.centralizer ({a} : Set X)) ≃* ↥(Subgroup.centralizer ({b} : Set H))) := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq H e a b h
  have key : ∀ x : X, x ∈ Subgroup.centralizer ({a} : Set X) ↔
      φ x ∈ Subgroup.centralizer ({b} : Set H) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← hφ,
      ← map_mul, ← map_mul]
    exact φ.injective.eq_iff.symm
  refine ⟨{
    toFun := fun x => ⟨φ x.1, (key x.1).1 x.2⟩
    invFun := fun y => ⟨φ.symm y.1, (key (φ.symm y.1)).2 (by
      rw [MulEquiv.apply_symm_apply]
      exact y.2)⟩
    left_inv := fun x => Subtype.ext (φ.symm_apply_apply _)
    right_inv := fun y => Subtype.ext (φ.apply_symm_apply _)
    map_mul' := fun x y => Subtype.ext (map_mul φ _ _) }⟩

theorem Quot2Data.comp_equiv_sub {C' Y : Type*} [Group C'] [Group Y] {φ : ↥H →* Y}
    {D : Subgroup Y} (h : Quot2Data φ D) (ζ : C' ≃* ↥H) : Quot2Data (φ.comp ζ.toMonoidHom) D :=
  h.comp_equiv ζ

theorem exists_hom_of_mulEquiv_sub (e : X ≃* H) :
    ∃ Ψ : X →* W, Function.Injective Ψ ∧ (∀ x, Ψ x ∈ H) ∧ (∀ y ∈ H, ∃ x, Ψ x = y) ∧
      ∀ x, Ψ x = ((e x : H) : W) := by
  refine ⟨H.subtype.comp e.toMonoidHom, H.subtype_injective.comp e.injective, fun x => (e x).2,
    fun y hy => ?_, fun x => rfl⟩
  obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val hx⟩

end SubgroupForm

section Class


theorem co1_isConj_a₁ {s : GA} (hs : orderOf s = 2)
    (hdvd : 251596800 ∣ Nat.card (Subgroup.centralizer ({s} : Set GA))) : IsConj s a₁ := by
  rcases involution_classes.1 s hs with h | h | h
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have h1 := card_centralizer_eq_of_mulEquiv (MulAut.conj c) s
    have e1 : (MulAut.conj c) s = aC := hc
    rw [e1, card_centralizer_GA aC, coe_aC, card_cent_aG] at h1
    rw [h1] at hdvd
    omega
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have h1 := card_centralizer_eq_of_mulEquiv (MulAut.conj c) s
    have e1 : (MulAut.conj c) s = cC := hc
    rw [e1, card_centralizer_GA cC, coe_cC, card_cent_cG] at h1
    rw [h1] at hdvd
    omega
  · exact h

end Class

end CFSG.EvenSporadicStandard.Solomon78
