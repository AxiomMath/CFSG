module

public import CFSG.CGT.PushingUpLit.ThmOne.OmegaNormAmb
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeSixMap
public import CFSG.Quasithin.Background.B6Offenders
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.PushingUpLit.ThmOne.SchurAut

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ThreeTen.card_mul_lt_of_isNatBy {W D B : Subgroup G} (hW : IsElemAbelian 2 W)
    (hDW : D ≤ Subgroup.normalizer (W : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNatBy (omegaPlusAct n) D W ∨ IsNatBy (omegaMinusAct n) D W)
    (hWC : W ⊓ Subgroup.centralizer (D : Set G) = ⊥) (hWD : ⁅D, W⁆ = W)
    (hB : IsElemAbelian 2 B) (hBD : B ≤ Subgroup.normalizer (D : Set G))
    (hBW : B ≤ Subgroup.normalizer (W : Set G)) (hne : ¬ B ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card B * Nat.card ↥(W ⊓ Subgroup.centralizer (B : Set G)) <
      Nat.card W * Nat.card ↥(B ⊓ Subgroup.centralizer (W : Set G)) := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  have hW2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW.2 v v.2)
  have hWp : IsPGroup 2 ↥W := fun v => ⟨1, by rw [pow_one]; exact hW2 v⟩
  have hmod := hnat.imp (fun h => OmegaNorm.exists_mulEquiv_isModelAct hDW h hWC)
    (fun h => OmegaNorm.exists_mulEquiv_isModelAct hDW h hWC)
  have hirr := (OmegaNorm.omega_isIrrSec_card (S := autOn D W) (by omega) hmod).1
  have hfac : ∀ w ∈ W, ∃ p ∈ (⁅D, W⁆ : Subgroup G),
      ∃ c ∈ W ⊓ Subgroup.centralizer (D : Set G), w = p * c :=
    fun w hw => ⟨w, hWD.symm ▸ hw, 1, one_mem _, (mul_one w).symm⟩
  have hZ : commV (autOn D W) ⊓ fixV (autOn D W) = ⊥ := by
    have h1 : fixOn hW D = ⊥ := by
      rw [fixOn_eq hW hDW, ← Subgroup.inf_subgroupOf_left, hWC, Subgroup.bot_subgroupOf]
    show commOn hW D ⊓ fixOn hW D = ⊥
    rw [h1, inf_bot_eq]
  have hnatE : IsNatSectionBy (omegaPlusAct n) (autOn D W) (commV (autOn D W))
        (commV (autOn D W) ⊓ fixV (autOn D W)) ∨
      IsNatSectionBy (omegaMinusAct n) (autOn D W) (commV (autOn D W))
        (commV (autOn D W) ⊓ fixV (autOn D W)) :=
    hnat.imp (fun h => isNatSectionBy_autOn hW hDW h hWD.le hfac rfl)
      (fun h => isNatSectionBy_autOn hW hDW h hWD.le hfac rfl)
  by_contra hlt
  rw [not_lt] at hlt
  have hrel := Subgroup.relIndex_mul_card (B ⊓ Subgroup.centralizer (W : Set G)) B
  rw [inf_of_le_left inf_le_left] at hrel
  have hd : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (W : Set G)) := Nat.card_pos
  have hcard : Nat.card ↥W ≤ Nat.card ↥(autOn B W) * Nat.card ↥(fixV (autOn B W)) := by
    rw [card_autOn_eq_relIndex hBW, card_fixV_autOn_eq hW hBW]
    rw [← hrel, mul_right_comm] at hlt
    exact Nat.le_of_mul_le_mul_right hlt hd
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender (X := autOn B W)
    ⟨autOn B W, le_rfl, autOn_ne_bot_of_not_le_centralizer hBW hne, isElemAbelian2_autOn hW hB hBW,
      hcard⟩
  have hAN : autOn B W ≤ Subgroup.normalizer (autOn D W : Set (MulAut ↥W)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_autOn_iff.mp hx
    exact OmegaNorm.conjAct_normalizes_autOn a.2 (hBD ha)
  have h28 := aschbacherTwoEight_holds ↥W hW2 (autOn D W) A n hn (hA.1.trans hAN)
    (offender_iff.mp hA).2 hnatE hZ
  refine hA.2.1 ((Subgroup.eq_bot_iff_forall A).2 fun t ht => ?_)
  have hcomm : ∀ s ∈ autOn D W, s * t = t * s := fun s hs => by
    have h := Subgroup.commutator_mem_commutator hs ht
    rwa [h28, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact eq_one_of_commute_irreducible_of_pow_two_pow hWp hirr hcomm (k := 1)
    (by rw [pow_one]; exact hA.2.2.1.2 t ht)

omit [Finite G] in
theorem ThreeTen.isElemAbelian_two_map_of_hom {Γ : Type} [Group Γ] (f : G →* Γ) {W : Subgroup G}
    (hW : IsElemAbelian 2 W) : IsElemAbelian 2 (W.map f) := CFSG.Open.IsElemAbelian.map hW _

theorem ThreeTen.le_centralizer_of_isNatBy {W D : Subgroup G} (hW : IsElemAbelian 2 W)
    (hDW : D ≤ Subgroup.normalizer (W : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNatBy (omegaPlusAct n) D W ∨ IsNatBy (omegaMinusAct n) D W)
    (hWC : W ⊓ Subgroup.centralizer (D : Set G) = ⊥) (hWD : ⁅D, W⁆ = W) {k : G}
    (h1 : W.map (MulAut.conj k).toMonoidHom ≤
      Subgroup.normalizer (D : Set G) ⊓ Subgroup.normalizer (W : Set G))
    (h2 : W.map (MulAut.conj k⁻¹).toMonoidHom ≤
      Subgroup.normalizer (D : Set G) ⊓ Subgroup.normalizer (W : Set G)) :
    W.map (MulAut.conj k).toMonoidHom ≤ Subgroup.centralizer (W : Set G) := by
  set f : G →* G := (MulAut.conj k).toMonoidHom with hf_def
  have hf : Function.Injective f := (MulAut.conj k).injective
  have hW' : IsElemAbelian 2 (W.map f) := ThreeTen.isElemAbelian_two_map_of_hom f hW
  by_contra hne
  have hlt1 := ThreeTen.card_mul_lt_of_isNatBy hW hDW hn hnat hWC hWD hW'
    (h1.trans inf_le_left) (h1.trans inf_le_right) hne
  have hDW' : D.map f ≤ Subgroup.normalizer ((W.map f : Subgroup G) : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    exact (ThreeSix.map_mem_normalizer_map_iff hf W d).mpr (hDW hd)
  have hnat' := hnat.imp (ThreeSix.isNatBy_map hf) (ThreeSix.isNatBy_map hf)
  have hWC' : W.map f ⊓ Subgroup.centralizer ((D.map f : Subgroup G) : Set G) = ⊥ := by
    rw [← ThreeSix.map_inf_centralizer_eq_inf_centralizer_map hf, hWC, Subgroup.map_bot]
  have hWD' : ⁅D.map f, W.map f⁆ = W.map f := by rw [← Subgroup.map_commutator, hWD]
  have hback : ∀ w ∈ W, f (k⁻¹ * w * k) = w ∧
      k⁻¹ * w * k ∈ Subgroup.normalizer (D : Set G) ⊓ Subgroup.normalizer (W : Set G) := by
    intro w hw
    refine ⟨by simp [hf_def, MulAut.conj_apply, mul_assoc], h2 ⟨w, hw, ?_⟩⟩
    simp
  have hBD' : W ≤ Subgroup.normalizer ((D.map f : Subgroup G) : Set G) := fun w hw => by
    rw [← (hback w hw).1]
    exact (ThreeSix.map_mem_normalizer_map_iff hf D _).mpr (Subgroup.mem_inf.mp (hback w hw).2).1
  have hBW' : W ≤ Subgroup.normalizer ((W.map f : Subgroup G) : Set G) := fun w hw => by
    rw [← (hback w hw).1]
    exact (ThreeSix.map_mem_normalizer_map_iff hf W _).mpr (Subgroup.mem_inf.mp (hback w hw).2).2
  have hne' : ¬ W ≤ Subgroup.centralizer ((W.map f : Subgroup G) : Set G) :=
    fun h => hne (Subgroup.le_centralizer_iff.mp h)
  have hlt2 := ThreeTen.card_mul_lt_of_isNatBy hW' hDW' hn hnat' hWC' hWD' hW hBD' hBW' hne'
  exact lt_asymm hlt1 hlt2

end CFSG.CGT.PushingUpLit.ThmOne
