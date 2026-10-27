module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cAltCard
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cAltPerm
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)

theorem altS_card_pSimple_dvd {Y : Type} [Group Y] [Finite Y] (p : ℕ) (J : Subgroup Y) :
    Nat.card (PSimple p J) ∣ Nat.card Y := by
  have hsurj : Function.Surjective ((QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J))) :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  exact (Subgroup.card_dvd_of_surjective hsurj).trans (Subgroup.card_subgroup_dvd_card J)

theorem altS_fixSubgroup_eq {Y : Type} [Group Y] (α : MulAut Y) :
    CFSG.LocalAnalysis.GLTheoremA.fixSubgroup α =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α :=
  Subgroup.ext fun _ => Iff.rfl

private theorem altS_fixSubgroup_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (α : MulAut S) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.congr e α) =
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    have h2 : e (α (e.symm y)) = y := hy
    refine ⟨e.symm y, ?_, by simp⟩
    show α (e.symm y) = e.symm y
    have h3 := congrArg e.symm h2
    simpa using h3
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    show e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx']

theorem altS_eight_le
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) {n : ℕ} (hn : 5 ≤ n)
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin n)) {J : Subgroup Y}
    (hT : catalogIs (PSimple 3 J) S8.L84.isType1430) : 8 ≤ n := by
  by_contra hlt
  have hn7 : n ≤ 7 := by omega
  obtain ⟨i, hi, ⟨f⟩⟩ := hT
  have h5 := altS_card_of_isType1430 i f hi
  have hdvd : Nat.card (PSimple 3 J) ∣ Nat.card Y := altS_card_pSimple_dvd 3 J
  have hZ : Nat.card (Subgroup.center Y) ∣ (if n = 6 ∨ n = 7 then 6 else 2) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.card_center_dvd_of_isAltType hq ⟨e⟩
  have hZle : Nat.card (Subgroup.center Y) ≤ 6 := by
    refine (Nat.le_of_dvd (by split_ifs <;> norm_num) hZ).trans ?_
    split_ifs <;> norm_num
  have hAle : Nat.card (alternatingGroup (Fin n)) ≤ 2520 := by
    have h := altS_two_mul_card_alt (m := n) (by omega)
    have h7 : Nat.factorial n ≤ Nat.factorial 7 := Nat.factorial_le hn7
    rw [show Nat.factorial 7 = 5040 from by decide] at h7
    omega
  have hY : Nat.card Y = Nat.card (Y ⧸ Subgroup.center Y) * Nat.card (Subgroup.center Y) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [Nat.card_congr e.toEquiv] at hY
  have hYle : Nat.card Y ≤ 2520 * 6 := by
    rw [hY]
    exact Nat.mul_le_mul hAle hZle
  have hle : Nat.card (PSimple 3 J) ≤ Nat.card Y := Nat.le_of_dvd Nat.card_pos hdvd
  omega

theorem altS_center_eq_bot
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore 3 Y = ⊥)
    {n : ℕ} (hn : 8 ≤ n) (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin n)) :
    Subgroup.center Y = ⊥ := by
  rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.center_eq_bot_or_of_isAltType
      Nat.prime_three (by norm_num) hq hO ⟨e⟩ with hZ | ⟨-, h67⟩
  · exact hZ
  · omega

theorem altS_twelve_le
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 5 ≤ n) (φ : Y ≃* alternatingGroup (Fin n))
    {ξ : MulAut Y} (hξ3 : ξ ^ 3 = 1) (hξ1 : ξ ≠ 1) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (CFSG.LocalAnalysis.GLTheoremA.fixSubgroup ξ) J)
    (hT : catalogIs (PSimple 3 J) S8.L84.isType1430) :
    12 ≤ n := by
  have hα3 : MulAut.congr φ ξ ^ 3 = 1 := by rw [← map_pow, hξ3, map_one]
  have hα1 : MulAut.congr φ ξ ≠ 1 := by
    intro h
    apply hξ1
    apply (MulAut.congr φ).injective
    rw [h, map_one]
  have hJ' : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ξ) J := by
    rw [← altS_fixSubgroup_eq]
    exact hJ
  have hI : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.congr φ ξ)) (J.map φ.toMonoidHom) := by
    rw [altS_fixSubgroup_congr]
    exact (T123C.glaPComponent_map_iff (f := φ.toMonoidHom) φ.injective 3 _ _).2 hJ'
  obtain ⟨m, hm, hmn, ⟨g⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.kdAltDown_holds n 3 hn Nat.prime_three (by norm_num)
      (MulAut.congr φ ξ) hα3 hα1 _ hI
  have hm5 : 5 ≤ m := le_trans (by norm_num) hm
  have e1 : PSimple 3 J ≃* alternatingGroup (Fin m) :=
    (T123C.pSimpleEquiv 3 (f := φ.toMonoidHom) φ.injective J).trans g
  have hm9 := altS_eq_nine_of_isType1430 hT hm5 e1
  omega

theorem altS_le_twelve {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (φ : Y ≃* alternatingGroup (Fin n)) (hZ : Subgroup.center Y = ⊥) (hRk : RkY Y) : n ≤ 12 := by
  by_contra hlt
  have h13 : 13 ≤ n := by omega
  have hι : Function.Injective (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h13)) :=
    Equiv.Perm.viaEmbeddingHom_injective _
  have hsign : ∀ x : alternatingGroup (Fin 13),
      Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h13) (x : Equiv.Perm (Fin 13)) ∈
        alternatingGroup (Fin n) := by
    intro x
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.viaEmbeddingHom_apply]
    unfold Equiv.Perm.viaEmbedding
    rw [Equiv.Perm.sign_extendDomain]
    exact Equiv.Perm.mem_alternatingGroup.1 x.2
  let Θ : alternatingGroup (Fin 13) →* alternatingGroup (Fin n) :=
    ((Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h13)).comp
      (alternatingGroup (Fin 13)).subtype).codRestrict (alternatingGroup (Fin n)) hsign
  have hΘ : Function.Injective Θ := fun x y h =>
    Subtype.ext (hι (congrArg Subtype.val h))
  have hΞ : Function.Injective (φ.symm.toMonoidHom.comp Θ) := φ.symm.injective.comp hΘ
  obtain ⟨U, E, hU, hU2, hEN, hE, hcard⟩ := altS_exists_rank_four_config _ hΞ
  have h27 := (hRk U hU hU2 E hEN hE).2 (by rw [hZ]; exact inf_bot_eq E)
  omega

theorem altS_core
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore 3 Y = ⊥)
    (hRk : RkY Y) {n : ℕ} (hn : 5 ≤ n) (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin n))
    {ξ : MulAut Y} (hξ3 : ξ ^ 3 = 1) (hξ1 : ξ ≠ 1) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (CFSG.LocalAnalysis.GLTheoremA.fixSubgroup ξ) J)
    (hT : catalogIs (PSimple 3 J) S8.L84.isType1430) :
    n = 12 := by
  have hn8 := altS_eight_le hq hn e hT
  have hZ := altS_center_eq_bot hq hO hn8 e
  let φ : Y ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have h12 := altS_twelve_le hn φ hξ3 hξ1 hJ hT
  have h12' := altS_le_twelve φ hZ hRk
  omega

theorem i1431AltS_holds
    : I1431AltS := by
  intro Y _ _ hq hO hRk n hn ξ hξ3 hξ1 J hJ hT
  obtain ⟨i, hi, ⟨e⟩⟩ := hn
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating m hm =>
    have hmn : m = n := hi
    have := altS_core hq hO hRk hm e hξ3 hξ1 hJ hT.1
    omega
  | lie _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
