module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAdm
public import CFSG.CGT.PushingUpLit.CGT6.EmbConjMod
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructureAux
public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeAux

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Act

variable {V : Type} [CommGroup V] (Y : Subgroup (MulAut V))

@[expose] def yuAct : ↥(yuHol Y) →* Equiv.Perm ↥(commV Y) where
  toFun x :=
    { toFun := fun w => ⟨x.1.left * (x.1.right : MulAut V) (w : V),
        mul_mem x.2.1 (apply_mem_commV_self Y x.2.2 w.2)⟩
      invFun := fun w => ⟨((x.1.right)⁻¹ : MulAut V) ((x.1.left)⁻¹ * (w : V)),
        apply_mem_commV_self Y (Y.inv_mem x.2.2) (mul_mem (inv_mem x.2.1) w.2)⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  map_one' := by
    ext w
    simp
  map_mul' x z := by
    ext w
    simp [mul_assoc, MulAut.mul_apply]

end Act

section Faithful

variable {V : Type} [CommGroup V] (Y : Subgroup (MulAut V))

theorem yuAct_injective (hV : ∀ v : V, v ^ 2 = 1) (h3 : Nat.card ↥Y = 3) :
    Function.Injective (yuAct Y) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ∀ w : ↥(commV Y), x.1.left * (x.1.right : MulAut V) (w : V) = (w : V) := fun w =>
    congrArg Subtype.val (Equiv.congr_fun hx w)
  have hu : x.1.left = 1 := by simpa using h1 1
  have hα : ∀ w : ↥(commV Y), (x.1.right : MulAut V) (w : V) = (w : V) := fun w => by
    simpa [hu] using h1 w
  have hα2 : (x.1.right : MulAut V) ^ 2 = 1 := by
    refine MulEquiv.ext fun v => ?_
    have hcU : (x.1.right : MulAut V) v * v⁻¹ ∈ commV Y := commV_mem_of_apply Y ⟨_, x.2.2⟩ v
    have e1 := hα ⟨_, hcU⟩
    simp only [map_mul, map_inv] at e1
    have h2 : ((x.1.right : MulAut V) v) ^ 2 = 1 := hV _
    have h3' : v ^ 2 = 1 := hV v
    have e2 : (x.1.right : MulAut V) ((x.1.right : MulAut V) v) = v := by
      calc (x.1.right : MulAut V) ((x.1.right : MulAut V) v)
          = ((x.1.right : MulAut V) ((x.1.right : MulAut V) v) * ((x.1.right : MulAut V) v)⁻¹) *
              (x.1.right : MulAut V) v := by group
        _ = ((x.1.right : MulAut V) v * v⁻¹) * (x.1.right : MulAut V) v := by rw [e1]
        _ = ((x.1.right : MulAut V) v) ^ 2 * v⁻¹ := by rw [pow_two]; ac_rfl
        _ = v⁻¹ := by rw [h2, one_mul]
        _ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h3')
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    exact e2
  have hα3 : (x.1.right : MulAut V) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Y) (x := (⟨x.1.right, x.2.2⟩ : ↥Y))
    rw [h3] at this
    exact congrArg Subtype.val this
  have hα1 : (x.1.right : MulAut V) = 1 := by
    have : (x.1.right : MulAut V) = (x.1.right ^ 3) * (x.1.right ^ 2)⁻¹ := by group
    rw [this, hα3, hα2]
    simp
  exact Subtype.ext (SemidirectProduct.ext hu hα1)

theorem card_yuHol : Nat.card ↥(yuHol Y) = Nat.card ↥(commV Y) * Nat.card ↥Y := by
  have h := Subgroup.card_ker_mul_card_of_surjective (yuProj_surjective Y)
  rw [ker_yuProj] at h
  rw [← h, Nat.card_congr (MonoidHom.ofInjective (yuInc_injective Y)).toEquiv.symm]

end Faithful

section Sign

variable {V : Type} [CommGroup V] [Finite V] (Y : Subgroup (MulAut V))

theorem sign_yuAct (hV : ∀ v : V, v ^ 2 = 1) (h3 : Nat.card ↥Y = 3) [Fintype ↥(commV Y)]
    [DecidableEq ↥(commV Y)] (x : ↥(yuHol Y)) : Equiv.Perm.sign (yuAct Y x) = 1 := by
  let χ : ↥(yuHol Y) →* ℤˣ := Equiv.Perm.sign.comp (yuAct Y)
  show χ x = 1
  have hsec : ∀ α : ↥Y, χ (yuSec Y α) = 1 := by
    intro α
    have h : α ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥Y) (x := α)
      rwa [h3] at this
    have h0 : (yuSec Y α) ^ 3 = 1 := by rw [← map_pow, h, map_one]
    have h1 : χ (yuSec Y α) ^ 3 = 1 := by rw [← map_pow, h0, map_one]
    have h2 : χ (yuSec Y α) ^ 2 = 1 := Int.units_sq _
    calc χ (yuSec Y α) = χ (yuSec Y α) ^ 3 * (χ (yuSec Y α) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h1, h2]; simp
  have hinc : ∀ u : ↥(commV Y), χ (yuInc Y u) = 1 := by
    have hUS : USelf Y := USelf_of_odd hV (by rw [h3]; exact ⟨1, rfl⟩)
    let N : Subgroup V := ((χ.comp (yuInc Y)).ker).map (commV Y).subtype
    have hN : ∀ g ∈ Y, ∀ u ∈ commV Y, g u * u⁻¹ ∈ N := by
      intro g hg u hu
      have hmem : g u * u⁻¹ ∈ commV Y := commV_mem_of_apply Y ⟨g, hg⟩ u
      refine ⟨⟨g u * u⁻¹, hmem⟩, ?_, rfl⟩
      have hc := comm_yuInc_yuSec Y ⟨g, hg⟩ (⟨u, hu⟩ : ↥(commV Y))⁻¹
      have heq : (⟨g u * u⁻¹, hmem⟩ : ↥(commV Y)) = ⟨((⟨u, hu⟩ : ↥(commV Y))⁻¹ : ↥(commV Y)) *
          (g : MulAut V) (((⟨u, hu⟩ : ↥(commV Y))⁻¹ : ↥(commV Y)) : V)⁻¹,
          mul_mem (inv_mem hu) (apply_mem_commV_self Y hg (inv_mem (inv_mem hu)))⟩ := by
        apply Subtype.ext
        show g u * u⁻¹ = u⁻¹ * g (u⁻¹)⁻¹
        rw [inv_inv, mul_comm]
      show χ (yuInc Y ⟨g u * u⁻¹, hmem⟩) = 1
      rw [heq, ← hc, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
    intro u
    obtain ⟨u', hu', hu'u⟩ := hUS N hN u.2
    have : u' = u := Subtype.ext hu'u
    rw [← this]
    exact hu'
  rw [yu_eq_inc_mul_sec Y x, map_mul, hinc, hsec, one_mul]

end Sign

section Equiv

variable {V : Type} [CommGroup V] [Finite V] (Y : Subgroup (MulAut V))

theorem yuHol_mulEquiv_alt (hV : ∀ v : V, v ^ 2 = 1) (h3 : Nat.card ↥Y = 3)
    (h4 : Nat.card ↥(commV Y) = 4) : Nonempty (↥(yuHol Y) ≃* alternatingGroup (Fin 4)) := by
  classical
  have : Fintype ↥(commV Y) := Fintype.ofFinite _
  have hc : Fintype.card ↥(commV Y) = 4 := by rw [← Nat.card_eq_fintype_card]; exact h4
  let e : ↥(commV Y) ≃ Fin 4 := Fintype.equivFinOfCardEq hc
  let φ : ↥(yuHol Y) →* alternatingGroup (Fin 4) :=
    (e.permCongrHom.toMonoidHom.comp (yuAct Y)).codRestrict (alternatingGroup (Fin 4))
      (fun x => by
        rw [Equiv.Perm.mem_alternatingGroup]
        show Equiv.Perm.sign (e.permCongr (yuAct Y x)) = 1
        rw [Equiv.Perm.sign_permCongr]
        exact sign_yuAct Y hV h3 x)
  have hinj : Function.Injective φ := fun a b hab =>
    yuAct_injective Y hV h3 (e.permCongrHom.injective (congrArg Subtype.val hab))
  have hcard : Nat.card (alternatingGroup (Fin 4)) ≤ Nat.card ↥(yuHol Y) := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
      card_yuHol, h3, h4]
    decide
  exact ⟨MulEquiv.ofBijective φ (hinj.bijective_of_nat_card_le hcard)⟩

end Equiv

section Glue

variable {V : Type} [CommGroup V] [Finite V]

theorem inClassX_yuHol_of_card_three (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (h3 : Nat.card ↥Y = 3) (h4 : Nat.card ↥(commV Y) = 4) : InClassX ↥(yuHol Y) :=
  CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock
    (CFSG.AGLEmbedding.inClassXBlock_of_mulEquiv_alternatingFour (yuHol_mulEquiv_alt Y hV h3 h4))

theorem Lift5.of_subnormal (hV : ∀ v : V, v ^ 2 = 1) {G Y : Subgroup (MulAut V)}
    (h3 : Nat.card ↥Y = 3) (h4 : Nat.card ↥(commV Y) = 4) (hYG : Y ≤ G)
    (hsub : (Y.subgroupOf G).IsSubnormal) : Lift5 G Y Y :=
  ⟨le_rfl, hYG, hsub, inClassX_yuHol_of_card_three hV h3 h4, Or.inl rfl⟩

end Glue

end CFSG.CGT.PushingUpLit.CGT6
