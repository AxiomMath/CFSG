module

public import CFSG.GH74.Generic.BProg.B3.S45TableA
public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B2.PumpupTable
public import CFSG.GH74.Generic.BProg.B3.L2CompOrders
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.GH74.Generic.S45.LLinFour
public import CFSG.GH74.Generic.S45.LPsuCover
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.Generic.BProg.B3.S45TableA

namespace S45EvenSp4

theorem exists_two_ne_one {W : Type} [Group W] [Finite W] (h : 3 ≤ Nat.card W) :
    ∃ a b : W, a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a := by
  classical
  have := Fintype.ofFinite W
  have hc : 3 ≤ Fintype.card W := by rwa [← Nat.card_eq_fintype_card]
  have h1 : 1 < ((Finset.univ : Finset W).erase 1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp only [Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1
  exact ⟨a, b, (Finset.mem_erase.1 ha).1, (Finset.mem_erase.1 hb).1, hab.symm⟩

theorem sq_eq_one_of_exponent_two {W : Type} [Group W] (h : Monoid.exponent W = 2) (w : W) :
    w * w = 1 := by
  have := Monoid.pow_exponent_eq_one w
  rwa [h, pow_two] at this

theorem comm_of_exponent_two {W : Type} [Group W] (h : Monoid.exponent W = 2) (a b : W) :
    a * b = b * a := by
  have h1 := sq_eq_one_of_exponent_two h (a * b)
  have h2 := sq_eq_one_of_exponent_two h a
  have h3 := sq_eq_one_of_exponent_two h b
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right h2
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right h3
  have h4 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, ha, hb] at h4
  exact h4.symm

theorem mem_center_of_coe_eq_neg_one {F : Type} [Field F] {w : ↥(StatedSp 2 F)}
    (hw : (w : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) = -1) :
    w ∈ Subgroup.center ↥(StatedSp 2 F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hw, mul_neg, neg_mul, mul_one, one_mul]

end S45EvenSp4

theorem N2_sp4 {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] (hF2 : ringChar F ≠ 2)
    (e : X ≃* ↥(StatedSp 2 F)) {y : MulAut X} (hd : Datum X y) : False := by
  classical
  obtain ⟨V, Q, _, _, π, ψ, -, hker, hψ, hodd, hQ⟩ := hd
  obtain ⟨hQs, hQn, -, -⟩ := S45.LAlt.hasL2Model_data hQ
  have hQf : Finite Q := finite_Q hQ
  have hVf : Finite V := finite_V ψ hψ hodd hQ
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  obtain ⟨W, hW⟩ := L2CompL2.exists_kleinFour_of_hasL2Model hQ
  have hW2 : IsPGroup 2 ↥W := IsPGroup.of_card (n := 2) (by rw [hW.card_four]; rfl)
  obtain ⟨P, hPp, hPmap⟩ := FalseCtxS45.exists_pGroup_lift ψ W hW2
    (by rw [MonoidHom.range_eq_top_of_surjective ψ hψ]; exact le_top)
  have hPinj : ∀ p ∈ P, ψ p = 1 → p = 1 := by
    intro p hp hψp
    obtain ⟨k, hk⟩ := hPp ⟨p, hp⟩
    exact eq_one_of_two_pow_of_mem_odd hodd (MonoidHom.mem_ker.2 hψp) (k := k)
      (congrArg Subtype.val hk)
  obtain ⟨a, b, ha1, hb1, hba⟩ := S45EvenSp4.exists_two_ne_one (W := ↥W) (by rw [hW.card_four]; norm_num)
  have hlift : ∀ w : ↥W, ∃ p ∈ P, ψ p = (w : Q) := fun w => by
    have : (w : Q) ∈ P.map ψ := hPmap ▸ w.2
    obtain ⟨p, hp, h⟩ := this
    exact ⟨p, hp, h⟩
  obtain ⟨p₁, hp₁P, hp₁⟩ := hlift a
  obtain ⟨p₂, hp₂P, hp₂⟩ := hlift b
  have haa : (a : Q) * (a : Q) = 1 := congrArg Subtype.val (S45EvenSp4.sq_eq_one_of_exponent_two hW.exponent_two a)
  have hbb : (b : Q) * (b : Q) = 1 := congrArg Subtype.val (S45EvenSp4.sq_eq_one_of_exponent_two hW.exponent_two b)
  have hab : (a : Q) * (b : Q) = (b : Q) * (a : Q) :=
    congrArg Subtype.val (S45EvenSp4.comm_of_exponent_two hW.exponent_two a b)
  have hp₁sq : p₁ * p₁ = 1 :=
    hPinj _ (P.mul_mem hp₁P hp₁P) (by rw [map_mul, hp₁, haa])
  have hp₂sq : p₂ * p₂ = 1 :=
    hPinj _ (P.mul_mem hp₂P hp₂P) (by rw [map_mul, hp₂, hbb])
  have hp₁₂ : p₁ * p₂ = p₂ * p₁ := by
    have hc : p₁ * p₂ * (p₂ * p₁)⁻¹ = 1 :=
      hPinj _ (P.mul_mem (P.mul_mem hp₁P hp₂P) (P.inv_mem (P.mul_mem hp₂P hp₁P)))
        (by rw [map_mul, map_inv, map_mul, map_mul, hp₁, hp₂, hab, mul_inv_cancel])
    exact mul_inv_eq_one.1 hc
  have hψp₁ : ψ p₁ ≠ 1 := by
    rw [hp₁]
    exact fun h => ha1 (Subtype.ext h)
  have hψp₂ : ψ p₂ ≠ 1 := by
    rw [hp₂]
    exact fun h => hb1 (Subtype.ext h)
  have hw₁sq : e (π p₁) * e (π p₁) = 1 := by
    rw [← map_mul, ← map_mul, hp₁sq, map_one, map_one]
  have hw₂sq : e (π p₂) * e (π p₂) = 1 := by
    rw [← map_mul, ← map_mul, hp₂sq, map_one, map_one]
  have hw₁₂ : e (π p₁) * e (π p₂) = e (π p₂) * e (π p₁) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hp₁₂]
  have hw₁1 : e (π p₁) ≠ 1 := by
    intro h
    apply hψp₁
    have h1 : π p₁ = 1 := e.injective (by rw [h, map_one])
    exact MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 h1))
  have hw₂1 : e (π p₂) ≠ 1 := by
    intro h
    apply hψp₂
    have h1 : π p₂ = 1 := e.injective (by rw [h, map_one])
    exact MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 h1))
  have hw₁₂ne : e (π p₁) ≠ e (π p₂) := by
    intro h
    have h1 : π p₁ = π p₂ := e.injective h
    have h2' : p₁⁻¹ * p₂ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := MonoidHom.mem_ker.1 (hker h2')
    rw [map_mul, map_inv, hp₁, hp₂] at h3
    exact hba (Subtype.ext (inv_mul_eq_one.1 h3).symm)
  have hcentral : ∀ p : V, e (π p) ∈ Subgroup.center ↥(StatedSp 2 F) → ψ p = 1 := by
    intro p hp
    apply psi_eq_one_of_mem_center hker hψ hQs hQn
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hp (e g)
  rcases CFSG.RankThree.SubgroupLists.neg_one_mem_of_commute_involutions h2 (e (π p₁)).2 (e (π p₂)).2
      (by rw [← Subgroup.coe_mul, hw₁sq, Subgroup.coe_one])
      (by rw [← Subgroup.coe_mul, hw₂sq, Subgroup.coe_one])
      (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hw₁₂])
      (fun h => hw₁1 (Subtype.ext h)) (fun h => hw₂1 (Subtype.ext h))
      (fun h => hw₁₂ne (Subtype.ext h)) with h | h | h
  · exact hψp₁ (hcentral p₁ (S45EvenSp4.mem_center_of_coe_eq_neg_one h))
  · exact hψp₂ (hcentral p₂ (S45EvenSp4.mem_center_of_coe_eq_neg_one h))
  · have h12 : e (π (p₁ * p₂)) ∈ Subgroup.center ↥(StatedSp 2 F) := by
      have : e (π (p₁ * p₂)) = e (π p₁) * e (π p₂) := by rw [map_mul, map_mul]
      rw [this]
      exact S45EvenSp4.mem_center_of_coe_eq_neg_one (by rw [Subgroup.coe_mul]; exact h)
    have h3 := hcentral (p₁ * p₂) h12
    rw [map_mul, hp₁, hp₂] at h3
    apply hba
    have h' : (a : Q) = (b : Q)⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [inv_eq_of_mul_eq_one_right hbb] at h'
    exact Subtype.ext h'.symm

end CFSG.GH74.Generic.BProg.B3
