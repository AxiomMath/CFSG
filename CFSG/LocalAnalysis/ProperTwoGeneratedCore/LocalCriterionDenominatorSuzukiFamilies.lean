module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiDerangementCount
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_11_15
public import Certificates.Certificate43
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External
open scoped BigOperators

variable (m : ℕ)

local notation "SzG" => SuzukiMatrixGroup m

@[expose] def suzukiDerangementCentralizers :=
  {A : Subgroup SzG // ∃ g : SzG, suzukiDerangement m g ∧
    A = Subgroup.centralizer ({g} : Set SzG)}

@[expose, instance_reducible] def suzukiDerangementCentralizerAction :
    MulAction SzG (suzukiDerangementCentralizers m) where
  smul s A := ⟨A.val.map (MulAut.conj s).toMonoidHom, by
    obtain ⟨g, hg, hA⟩ := A.property
    refine ⟨(MulAut.conj s) g, suzuki_derangement_conjugate m g hg s, ?_⟩
    rw [hA]
    exact (xi1115_centralizer_conj_eq g s).symm⟩
  one_smul A := by
    apply Subtype.ext
    change A.val.map (MulAut.conj (1 : SzG)).toMonoidHom = A.val
    rw [show (MulAut.conj (1 : SzG)).toMonoidHom = MonoidHom.id SzG by ext x; simp]
    simp
  mul_smul s t A := by
    apply Subtype.ext
    change A.val.map (MulAut.conj (s * t)).toMonoidHom =
      (A.val.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

local instance : MulAction SzG (suzukiDerangementCentralizers m) :=
  suzukiDerangementCentralizerAction m

instance suzukiDerangementCentralizers_finite : Finite (suzukiDerangementCentralizers m) := by
  unfold suzukiDerangementCentralizers
  infer_instance

@[expose] def suzukiDerangementCentralizerClasses :=
  Quotient (MulAction.orbitRel SzG (suzukiDerangementCentralizers m))

instance suzukiDerangementCentralizerClasses_finite :
    Finite (suzukiDerangementCentralizerClasses m) := by
  unfold suzukiDerangementCentralizerClasses
  infer_instance

@[expose] def suzukiDerangementCentralizerRepresentative
    (c : suzukiDerangementCentralizerClasses m) : suzukiDerangementCentralizers m :=
  Quotient.out c

@[expose] def suzukiDerangementCentralizerFamily (c : suzukiDerangementCentralizerClasses m) :=
  {W : Subgroup SzG // ∃ s : SzG,
    W = (suzukiDerangementCentralizerRepresentative m c).val.map
      (MulAut.conj s).toMonoidHom}

instance suzukiDerangementCentralizerFamily_finite (c : suzukiDerangementCentralizerClasses m) :
    Finite (suzukiDerangementCentralizerFamily m c) := by
  unfold suzukiDerangementCentralizerFamily
  infer_instance

theorem suzuki_derangement_family_member (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) (x : SzG) (hx : x ∈ A.val) (hx1 : x ≠ 1) :
    suzukiDerangement m x := by
  obtain ⟨g, hg, hA⟩ := A.property
  rw [hA] at hx
  exact suzuki_derangement_centralizer_member m hm g hg x hx hx1

theorem suzuki_derangement_family_centralizer_exact (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) (x : SzG) (hx : x ∈ A.val) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set SzG) = A.val := by
  obtain ⟨g, hg, hA⟩ := A.property
  rw [hA] at hx ⊢
  exact suzuki_derangement_centralizer_exact m hm g hg x hx hx1

theorem suzuki_derangement_family_card_gt_one (A : suzukiDerangementCentralizers m) :
    1 < Nat.card A.val := by
  apply (Subgroup.one_lt_card_iff_ne_bot A.val).mpr
  intro hbot
  obtain ⟨g, hg, hA⟩ := A.property
  have hgmem : g ∈ A.val := hA ▸ Subgroup.mem_centralizer_singleton_iff.mpr rfl
  rw [hbot] at hgmem
  exact suzuki_derangement_ne_one m g hg (Subgroup.mem_bot.mp hgmem)

theorem suzuki_derangement_family_card_dvd (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) : Nat.card A.val ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  obtain ⟨g, hg, hA⟩ := A.property
  rw [hA]
  exact suzuki_ovoid_derangement_full_centralizer_card_dvd m hm g hg

theorem suzuki_derangement_family_cyclic_odd (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) : IsCyclic A.val ∧ Odd (Nat.card A.val) := by
  obtain ⟨g, hg, hA⟩ := A.property
  rw [hA]
  exact suzuki_degree_divisor_centralizer_cyclic_odd m hm g
    (suzuki_derangement_ne_one m g hg) (suzuki_derangement_order_dvd m hm g hg)

theorem suzuki_derangement_family_normalizer_index_dvd_four
    (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) :
    A.val.relIndex (Subgroup.normalizer (A.val : Set SzG)) ∣ 4 := by
  obtain ⟨g, hg, hA⟩ := A.property
  rw [hA]
  exact suzuki_degree_divisor_full_normalizer_index_dvd_four m hm g
    (suzuki_derangement_ne_one m g hg) (suzuki_derangement_order_dvd m hm g hg)

theorem suzuki_derangement_family_hall (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) : Nat.Coprime (Nat.card A.val) A.val.index := by
  obtain ⟨g, hg, hA⟩ := A.property
  rw [hA]
  exact suzuki_derangement_centralizer_hall m hm g hg

theorem suzuki_derangement_conjugate_family_actual
    (c : suzukiDerangementCentralizerClasses m) (W : suzukiDerangementCentralizerFamily m c) :
    ∃ g : SzG, suzukiDerangement m g ∧ W.val = Subgroup.centralizer ({g} : Set SzG) := by
  obtain ⟨s, hs⟩ := W.property
  exact hs ▸ (s • suzukiDerangementCentralizerRepresentative m c).property

theorem suzuki_derangement_conjugate_family_class
    (c : suzukiDerangementCentralizerClasses m)
    (A : suzukiDerangementCentralizers m)
    (hA : ∃ s : SzG, A.val =
      (suzukiDerangementCentralizerRepresentative m c).val.map (MulAut.conj s).toMonoidHom) :
    (Quotient.mk'' A : suzukiDerangementCentralizerClasses m) = c := by
  obtain ⟨s, hs⟩ := hA
  have hrel : Quotient.mk (MulAction.orbitRel SzG (suzukiDerangementCentralizers m)) A =
      Quotient.mk (MulAction.orbitRel SzG (suzukiDerangementCentralizers m))
        (suzukiDerangementCentralizerRepresentative m c) :=
    Quotient.sound ⟨s, Subtype.ext hs.symm⟩
  exact hrel.trans (Quotient.out_eq c)

theorem suzuki_derangement_conjugate_family_punctured_card
    (c : suzukiDerangementCentralizerClasses m) :
    Nat.card (Σ W : suzukiDerangementCentralizerFamily m c,
      {x : W.val // (x : SzG) ≠ 1}) =
      (Subgroup.normalizer ((suzukiDerangementCentralizerRepresentative m c).val : Set SzG)).index *
        (Nat.card (suzukiDerangementCentralizerRepresentative m c).val - 1) :=
  xi1115_conjugate_family_punctured_card _

theorem suzuki_derangement_family_partition_count (hm : 0 < m) :
    letI := Fintype.ofFinite (suzukiDerangementCentralizerClasses m)
    Nat.card {g : SzG // suzukiDerangement m g} =
      ∑ c : suzukiDerangementCentralizerClasses m,
        (Subgroup.normalizer ((suzukiDerangementCentralizerRepresentative m c).val : Set SzG)).index *
          (Nat.card (suzukiDerangementCentralizerRepresentative m c).val - 1) := by
  classical
  let := Fintype.ofFinite (suzukiDerangementCentralizerClasses m)
  let Piece := Σ c : suzukiDerangementCentralizerClasses m,
    Σ W : suzukiDerangementCentralizerFamily m c, {x : W.val // (x : SzG) ≠ 1}
  let decode : Piece → {g : SzG // suzukiDerangement m g} := fun z =>
    ⟨z.2.2.val.val, suzuki_derangement_family_member m hm
      ⟨z.2.1.val, suzuki_derangement_conjugate_family_actual m z.1 z.2.1⟩
      z.2.2.val.val z.2.2.val.property z.2.2.property⟩
  have hinj : Function.Injective decode := by
    rintro ⟨c, W, x⟩ ⟨d, V, y⟩ hxy
    have hval : (x : SzG) = (y : SzG) := congrArg Subtype.val hxy
    let A : suzukiDerangementCentralizers m :=
      ⟨W.val, suzuki_derangement_conjugate_family_actual m c W⟩
    let B : suzukiDerangementCentralizers m :=
      ⟨V.val, suzuki_derangement_conjugate_family_actual m d V⟩
    have hWV : W.val = V.val := by
      exact (suzuki_derangement_family_centralizer_exact m hm A (x : SzG)
        x.val.property x.property).symm.trans
        (hval ▸ suzuki_derangement_family_centralizer_exact m hm B (y : SzG)
          y.val.property y.property)
    have hAB : A = B := Subtype.ext hWV
    have hcd : c = d := by
      exact (suzuki_derangement_conjugate_family_class m c A W.property).symm.trans
        (hAB ▸ suzuki_derangement_conjugate_family_class m d B V.property)
    subst d
    have hWVe : W = V := Subtype.ext hWV
    subst V
    have hxye : x = y := Subtype.ext (Subtype.ext hval)
    subst y
    rfl
  have hsurj : Function.Surjective decode := by
    intro g
    let A : suzukiDerangementCentralizers m :=
      ⟨Subgroup.centralizer ({g.val} : Set SzG), g.val, g.property, rfl⟩
    let c : suzukiDerangementCentralizerClasses m := Quotient.mk'' A
    have hrel : (MulAction.orbitRel SzG (suzukiDerangementCentralizers m))
        A (suzukiDerangementCentralizerRepresentative m c) :=
      Quotient.exact (Quotient.out_eq c).symm
    obtain ⟨s, hs⟩ := hrel
    let W : suzukiDerangementCentralizerFamily m c :=
      ⟨A.val, s, (congrArg Subtype.val hs).symm⟩
    let x : {x : W.val // (x : SzG) ≠ 1} :=
      ⟨⟨g.val, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
        suzuki_derangement_ne_one m g.val g.property⟩
    exact ⟨⟨c, W, x⟩, Subtype.ext rfl⟩
  calc
    Nat.card {g : SzG // suzukiDerangement m g} = Nat.card Piece :=
      (Nat.card_congr (Equiv.ofBijective decode ⟨hinj, hsurj⟩)).symm
    _ = ∑ c : suzukiDerangementCentralizerClasses m,
        Nat.card (Σ W : suzukiDerangementCentralizerFamily m c,
          {x : W.val // (x : SzG) ≠ 1}) := Nat.card_sigma
    _ = _ := by simp_rw [suzuki_derangement_conjugate_family_punctured_card]

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
