module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.Shape240

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

private theorem grpInvol_coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem grpInvol_sigmaC2_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide

private theorem grpInvol_sigmaC2_inv :
    (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide

private theorem grpInvol_sigmaC2_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

private def grpInvolSwap : A5WrTwo := ⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩

@[simp] private theorem grpInvolSwap_left : grpInvolSwap.left = 1 := rfl

@[simp] private theorem grpInvolSwap_right :
    grpInvolSwap.right = Multiplicative.ofAdd (1 : ZMod 2) := rfl

private theorem grpInvolSwap_mul_self : grpInvolSwap * grpInvolSwap = 1 := by
  apply RegularWreathProduct.ext
  · funext i
    simp [grpInvolSwap, RegularWreathProduct.mul_def]
  · simp [grpInvolSwap, RegularWreathProduct.mul_def, grpInvol_sigmaC2_mul_self]

private theorem grpInvolSwap_sq : grpInvolSwap ^ 2 = 1 := by
  rw [pow_two]
  exact grpInvolSwap_mul_self

private theorem grpInvolSwap_notMem : grpInvolSwap ∉ commutator A5WrTwo := by
  rw [A5WrTwo.commutator_eq_ker]
  intro h
  exact grpInvol_sigmaC2_ne_one (by simpa [grpInvolSwap, RegularWreathProduct.rightHom] using h)

private theorem grpInvol_sq_eq_one (r : Multiplicative (ZMod 2)) : r * r = 1 := by
  rcases grpInvol_coord_cases r with rfl | rfl
  · simp
  · exact grpInvol_sigmaC2_mul_self

private noncomputable def grpInvol_conjCentralizerMulEquiv (b u : A5WrTwo) :
    ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) ≃*
      ↥(Subgroup.centralizer ({b * u * b⁻¹} : Set A5WrTwo)) where
  toFun k := ⟨b * k * b⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : (k : A5WrTwo) * u = u * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc (b * k * b⁻¹) * (b * u * b⁻¹) = b * (k * u) * b⁻¹ := by group
      _ = b * (u * k) * b⁻¹ := by rw [hk]
      _ = (b * u * b⁻¹) * (b * k * b⁻¹) := by group⟩
  invFun k := ⟨b⁻¹ * k * b, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : (k : A5WrTwo) * (b * u * b⁻¹) = (b * u * b⁻¹) * k :=
      Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc (b⁻¹ * k * b) * u = b⁻¹ * (k * (b * u * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * u * b⁻¹) * k) * b := by rw [hk]
      _ = u * (b⁻¹ * k * b) := by group⟩
  left_inv k := Subtype.ext (by group)
  right_inv k := Subtype.ext (by group)
  map_mul' k l := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem grpInvol_left_const_of_mem (w : A5WrTwo)
    (hw : w ∈ Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo)) :
    ∀ x, w.left x = w.left 1 := by
  have hcomm : w * grpInvolSwap = grpInvolSwap * w :=
    Subgroup.mem_centralizer_singleton_iff.mp hw
  have hσ : w.left (Multiplicative.ofAdd (1 : ZMod 2)) = w.left 1 := by
    have h := congrArg (fun z : A5WrTwo => z.left (Multiplicative.ofAdd (1 : ZMod 2))) hcomm
    simpa only [RegularWreathProduct.mul_left, Pi.mul_apply, grpInvolSwap_left,
      grpInvolSwap_right, Pi.one_apply, one_mul, mul_one, grpInvol_sigmaC2_inv,
      grpInvol_sigmaC2_mul_self] using h
  intro x
  rcases grpInvol_coord_cases x with rfl | rfl
  · rfl
  · exact hσ

private noncomputable def grpInvolProj :
    ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo)) →* alternatingGroup (Fin 5) where
  toFun w := w.val.left 1
  map_one' := rfl
  map_mul' w w' := by
    have hw' := grpInvol_left_const_of_mem w'.val w'.property
    show ((w * w' : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))) : A5WrTwo).left 1
      = (w : A5WrTwo).left 1 * (w' : A5WrTwo).left 1
    rw [Subgroup.coe_mul, RegularWreathProduct.mul_left, Pi.mul_apply]
    rw [hw' (w.val.right⁻¹ * 1)]

private theorem grpInvolProj_ker_sq (k : ↥grpInvolProj.ker) :
    ((k : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))) ^ 2 = 1) := by
  have hk1 :
      (((k : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))) : A5WrTwo)).left 1 = 1 :=
    MonoidHom.mem_ker.mp k.property
  have hconst := grpInvol_left_const_of_mem
    ((k : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))) : A5WrTwo)
    (k : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))).property
  have hleft :
      (((k : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))) : A5WrTwo)).left = 1 := by
    funext x
    rw [hconst x, hk1, Pi.one_apply]
  let r : Multiplicative (ZMod 2) :=
    ((k : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))) : A5WrTwo).right
  have hw : ((k : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))) : A5WrTwo) =
      ⟨1, r⟩ := by
    apply RegularWreathProduct.ext
    · exact hleft
    · rfl
  have hsq :
      (((k : ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo))) : A5WrTwo)) ^ 2 = 1 := by
    rw [hw, pow_two, RegularWreathProduct.mul_def]
    apply RegularWreathProduct.ext
    · funext x
      simp
    · simp [grpInvol_sq_eq_one r]
  exact Subtype.ext hsq

private theorem grpInvol_elem2_sq (a : Elem2 2) : a * a = 1 := by
  apply Multiplicative.ext
  rw [toAdd_mul, toAdd_one]
  funext i
  simpa using CharTwo.add_self_eq_zero (a.toAdd i)

theorem cSide_cent_invol_hom {u : A5WrTwo} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ φ : ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) →* alternatingGroup (Fin 5),
      IsPGroup 2 φ.ker := by
  rcases involution_cases_of_mulEquiv (MulEquiv.refl A5WrTwo) hu2 hu1 with
    ⟨hu_out, _h120⟩ | ⟨hu_in, h240⟩ | ⟨_, h32⟩
  · obtain ⟨b, _hb, hbu⟩ :=
      A5WrTwo.exists_conj_of_outer_involutions hu_out grpInvolSwap_notMem hu2 grpInvolSwap_sq
    let e : ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) ≃*
        ↥(Subgroup.centralizer ({grpInvolSwap} : Set A5WrTwo)) :=
      (grpInvol_conjCentralizerMulEquiv b u).trans (MulEquiv.subgroupCongr (by rw [hbu]))
    refine ⟨grpInvolProj.comp e.toMonoidHom, ?_⟩
    intro g
    have hg : grpInvolProj (e g) = 1 := MonoidHom.mem_ker.mp g.property
    have hsq : (e g) ^ 2 = 1 :=
      grpInvolProj_ker_sq ⟨e g, MonoidHom.mem_ker.mpr hg⟩
    have h2 : e (g ^ 2) = 1 := by rw [map_pow, hsq]
    have hg2 : ((g : ↥(Subgroup.centralizer ({u} : Set A5WrTwo))) ^ 2 = 1) :=
      (MulEquiv.map_eq_one_iff e).mp h2
    exact ⟨1, by simpa using (Subtype.ext hg2 : g ^ 2 = 1)⟩
  · obtain ⟨f⟩ := gz9_isShapeTwoTwoTimesA5_wr hu_in hu2 h240
    refine ⟨(MonoidHom.snd _ _).comp f.toMonoidHom, ?_⟩
    intro g
    have hg2 : (f g).2 = 1 := MonoidHom.mem_ker.mp g.property
    have hfg : (f g) ^ 2 = 1 := by
      rw [pow_two, Prod.ext_iff]
      exact ⟨grpInvol_elem2_sq (f g).1, by
        show (f g).2 * (f g).2 = 1
        rw [hg2, one_mul]⟩
    have h2 : f (g ^ 2) = 1 := by rw [map_pow, hfg]
    have hg_sq : ((g : ↥(Subgroup.centralizer ({u} : Set A5WrTwo))) ^ 2 = 1) :=
      (MulEquiv.map_eq_one_iff f).mp h2
    exact ⟨1, by simpa using (Subtype.ext hg_sq : g ^ 2 = 1)⟩
  · refine ⟨1, ?_⟩
    rw [MonoidHom.ker_one]
    refine IsPGroup.of_card (n := 5) ?_
    rw [Subgroup.card_top, h32]
    norm_num

end CFSG.EvenSporadicStandard.HNRecog.CSide
