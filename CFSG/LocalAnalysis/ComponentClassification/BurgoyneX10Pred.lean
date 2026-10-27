module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Typed
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecConf
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

structure CompPred where
  P : ℕ → (L : Type) → [Group L] → Prop
  of_mulEquiv : ∀ {p : ℕ} {L M : Type} [Group L] [Group M], (L ≃* M) → P p M → P p L
  of_model : ∀ {p : ℕ} {L : Type} [Group L], p ≠ 2 → ExcCompModel p L → P p L
  of_central : ∀ {p : ℕ} {C K : Type} [Group C] [Group K] [Finite C], IsQuasisimple C →
    ∀ φ : C →* K, Function.Surjective φ → φ.ker ≤ center C → P p K → P p C

theorem CompPred.of_component_equiv (P : CompPred) {X Y : Type} [Group X] [Group Y]
    (Φ : X ≃* Y) {p : ℕ} (h : ∀ M : Subgroup Y, IsComponent M → P.P p M) {L : Subgroup X}
    (hL : IsComponent L) : P.P p L :=
  P.of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (h _ (LocalCores.isComponent_map_mulEquiv Φ hL))

@[expose] def CompPred.model : CompPred where
  P := ExcCompModel
  of_mulEquiv e h := ExcCompModel.of_mulEquiv e h
  of_model _ h := h
  of_central hq φ hφ hker h := by
    obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hq φ hφ hker
    exact ExcCompModel.of_centerQuotient_equiv e h

@[expose] def NoPSp4Odd (p : ℕ) (L : Type) [Group L] : Prop :=
  ∀ f : ℕ, 5 ≤ p ^ f → Odd (Nat.card (center L)) → ¬ LieModel (L ⧸ center L) .PSp 2 p f

theorem NoPSp4.toOdd {p : ℕ} {L : Type} [Group L] (h : NoPSp4 p L) : NoPSp4Odd p L :=
  fun f h5 _ => h f h5

theorem NoPSp4Odd.of_mulEquiv {p : ℕ} {L M : Type} [Group L] [Group M] (e : L ≃* M)
    (h : NoPSp4Odd p M) : NoPSp4Odd p L := by
  intro f h5 hodd hL
  have hc : Nat.card (center M) = Nat.card (center L) :=
    (Nat.card_congr ((MulEquiv.subgroupCongr (Subgroup.map_center_eq e)).symm.trans
      ((center L).equivMapOfInjective e.toMonoidHom e.injective).symm).toEquiv)
  exact h f h5 (hc ▸ hodd) (LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hL)

theorem odd_card_center_of_surjective {C K : Type} [Group C] [Group K] (hq : IsQuasisimple C)
    (φ : C →* K) (hφ : Function.Surjective φ) (hker : φ.ker ≤ center C)
    (hodd : Odd (Nat.card (center C))) : Odd (Nat.card (center K)) := by
  have : Group.IsPerfect C := hq.1
  have hcomap := Quasisimple.center_comap_of_central_kernel φ hφ hker
  have hmap : center K = (center C).map φ := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective hφ]
  rw [hmap]
  exact Odd.of_dvd_nat hodd (Subgroup.card_map_dvd (center C) φ)

@[expose] def CompPred.noPSp4Odd (hO : LieOrderFormulasInput) : CompPred where
  P := NoPSp4Odd
  of_mulEquiv e h := NoPSp4Odd.of_mulEquiv e h
  of_model hp2 h := (h.noPSp4 hO hp2).toOdd
  of_central hq φ hφ hker h := by
    intro f h5 hodd hC
    obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hq φ hφ hker
    exact h f h5 (odd_card_center_of_surjective hq φ hφ hker hodd)
      (LieType.CurtisTits.lieModel_of_mulEquiv e hC)

theorem four_dvd_card_of_psp4 (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hX : LieModel X .PSp 2 p f) :
    4 ∣ Nat.card X := by
  have hc := (card_of_psp4 hO hp hp2 hf hX).1
  obtain ⟨k, hk⟩ : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h8 : 8 ∣ (p ^ f) ^ 2 - 1 := by
    rw [hk]
    have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      rw [show (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 by ring, Nat.add_sub_cancel]
    rw [this]
    obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    rw [hm]
    exact ⟨m, by ring⟩
  have h16 : 8 ∣ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right h8 _) _
  rw [← hc] at h16
  omega

theorem center_eq_pPrimeCore_of_odd (hO : LieOrderFormulasInput) {K : Type} [Group K] [Finite K]
    (hq : IsQuasisimple K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hodd : Odd (Nat.card (center K))) (hm : LieModel (K ⧸ center K) .PSp 2 p f) :
    center K = pPrimeCore 2 K := by
  refine le_antisymm (le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hodd⟩) ?_
  rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (pPrimeCore 2 K) with h | h
  · exact h
  · exfalso
    have hcop := pPrimeCore_coprime_card (p := 2) (G := K)
    rw [h, Subgroup.card_top] at hcop
    have h4 := four_dvd_card_of_psp4 hO hp hp2 hf hm
    have hdvd : Nat.card (K ⧸ center K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
    have h2 : 2 ∣ Nat.card K := (Dvd.dvd.trans (by norm_num : 2 ∣ 4) h4).trans hdvd
    exact absurd (Nat.Coprime.coprime_dvd_right h2 hcop) (by norm_num)

theorem noPSp4Odd_of_rowLin (hO : LieOrderFormulasInput) (hLin : GSThmB.CF81X10RowLin)
    {J : Type} [Group J] {τ : StatedLieTag} {n p f : ℕ} (hτ : τ = .PSL ∨ τ = .PSU) (hn4 : n ≠ 4)
    (hn5 : n ≠ 5) (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible τ n p f)
    (hm : LieModel J τ n p f) {α : MulAut J} (hα : orderOf α = 2)
    {Kc : Subgroup (fixedSubgroup α)} (hKc : IsComponent Kc) : NoPSp4Odd p Kc := by
  intro f' h5 hodd hKm
  have hfin : Finite J := (hO J τ n p f hadm hm).1
  have hf' : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h0 | h0
    · rw [h0, pow_zero] at h5
      omega
    · exact h0
  have hαα : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα
    exact absurd hα (by norm_num)
  have hZ := center_eq_pPrimeCore_of_odd hO hKc.1 hp hp2 hf' hodd hKm
  have hKO : LieModel (↥Kc ⧸ pPrimeCore 2 ↥Kc) .PSp 2 p f' :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ) hKm
  rcases (hLin J τ n p f f' hp hp2 hτ hadm hm hf' h5 α hαα hα1 Kc
    (isPComponent_two_of_isComponent hKc)).1 hKO with ⟨rfl, -⟩ | rfl
  · exact hn4 rfl
  · exact hn5 rfl

end CFSG.ComponentClassification.Burgoyne.X10
