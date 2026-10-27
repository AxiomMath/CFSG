module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Alt8Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Alt8Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBMatGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBCent
public import Certificates.Certificate24856
public import Certificates.Certificate24858
public import Certificates.Certificate24860

public section

namespace CFSG.EvenSporadicStandard.M24Std.Alt8

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint
  CFSG.Certificates CFSG.EvenSporadicStandard.M24Std.SplitB Matrix

theorem octIdx_octPt : ∀ i : Fin 8, octIdx (octPt i) = i := by decide

theorem inO_octPt (i : Fin 8) : InO (octPt i) := by
  show octPt (octIdx (octPt i)) = octPt i
  rw [octIdx_octPt]

@[expose] def octAct (x : Equiv.Perm (Fin 24)) (hx : ∀ i, InO (x (octPt i)))
    (hx' : ∀ i, InO (x⁻¹ (octPt i))) : Equiv.Perm (Fin 8) where
  toFun i := octIdx (x (octPt i))
  invFun i := octIdx (x⁻¹ (octPt i))
  left_inv i := by
    have h1 : octPt (octIdx (x (octPt i))) = x (octPt i) := hx i
    show octIdx (x⁻¹ (octPt (octIdx (x (octPt i))))) = i
    rw [h1, Equiv.Perm.inv_def, Equiv.symm_apply_apply, octIdx_octPt]
  right_inv i := by
    have h1 : octPt (octIdx (x⁻¹ (octPt i))) = x⁻¹ (octPt i) := hx' i
    show octIdx (x (octPt (octIdx (x⁻¹ (octPt i))))) = i
    rw [h1, Equiv.Perm.inv_def, Equiv.apply_symm_apply, octIdx_octPt]

section Pinned


theorem inO_of_norm {x : S24} (hx : ∀ y ∈ m24B0l, x⁻¹ * y * x ∈ m24B0l) (i : Fin 8) :
    InO ((x : Equiv.Perm (Fin 24)) (octPt i)) := by
  obtain ⟨h1, h2, -⟩ := Certificates.certificate24860
  apply h2
  intro b hb
  have h3 := h1 _ (hx b hb) i
  have e : (b : Equiv.Perm (Fin 24)) ((x : Equiv.Perm (Fin 24)) (octPt i)) =
      (x : Equiv.Perm (Fin 24)) (((x⁻¹ * b * x : S24) : Equiv.Perm (Fin 24)) (octPt i)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.apply_symm_apply]
  rw [e, h3]

theorem inO_of_norm' {x : S24} (hx : ∀ y ∈ m24B0l, x * y * x⁻¹ ∈ m24B0l) (i : Fin 8) :
    InO ((x : Equiv.Perm (Fin 24))⁻¹ (octPt i)) := by
  have h := inO_of_norm (x := x⁻¹) (fun y hy => by rw [inv_inv]; exact hx y hy) i
  simpa only [Subgroup.coe_inv] using h

theorem mem_B0_of_fix (x : S24)
    (hx : ∀ i : Fin 8, (x : Equiv.Perm (Fin 24)) (octPt i) = octPt i) : x ∈ m24B0l := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := Certificates.certificate24860
  have hp : ¬ InO ((x : Equiv.Perm (Fin 24)) octP0) := by
    intro h
    apply h4
    have e1 : (x : Equiv.Perm (Fin 24)) octP0 =
        (x : Equiv.Perm (Fin 24)) (octPt (octIdx ((x : Equiv.Perm (Fin 24)) octP0))) := by
      rw [hx]
      exact h.symm
    have e2 := (x : Equiv.Perm (Fin 24)).injective e1
    have h6 := inO_octPt (octIdx ((x : Equiv.Perm (Fin 24)) octP0))
    rwa [← e2] at h6
  obtain ⟨b, hb, hbp⟩ := h3 _ hp
  obtain ⟨y, hy⟩ : ∃ y : S24, y = b⁻¹ * x := ⟨_, rfl⟩
  have hyO : ∀ i, (y : Equiv.Perm (Fin 24)) (octPt i) = octPt i := by
    intro i
    have hb1 := h1 b hb i
    rw [hy]
    change (b : Equiv.Perm (Fin 24))⁻¹ ((x : Equiv.Perm (Fin 24)) (octPt i)) = octPt i
    rw [hx i, Equiv.Perm.inv_eq_iff_eq]
    exact hb1.symm
  have hyp : (y : Equiv.Perm (Fin 24)) octP0 = octP0 := by
    rw [hy]
    change (b : Equiv.Perm (Fin 24))⁻¹ ((x : Equiv.Perm (Fin 24)) octP0) = octP0
    rw [← hbp, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hz : (m24Cj octConjW)⁻¹ * y * m24Cj octConjW = 1 := by
    refine eq_one_of_fix_base _ fun j hj => ?_
    have hgj : (y : Equiv.Perm (Fin 24)) ((m24Cj octConjW : Equiv.Perm (Fin 24)) j) =
        (m24Cj octConjW : Equiv.Perm (Fin 24)) j := by
      rcases h5 j hj with h | h
      · have e : (m24Cj octConjW : Equiv.Perm (Fin 24)) j =
            octPt (octIdx ((m24Cj octConjW : Equiv.Perm (Fin 24)) j)) := h.symm
        rw [e, hyO]
      · rw [h, hyp]
    change ((m24Cj octConjW : Equiv.Perm (Fin 24))⁻¹ * (y : Equiv.Perm (Fin 24)) *
      (m24Cj octConjW : Equiv.Perm (Fin 24))) j = j
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgj, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply]
  have hy1 : y = 1 := by
    have : y = m24Cj octConjW * ((m24Cj octConjW)⁻¹ * y * m24Cj octConjW) *
        (m24Cj octConjW)⁻¹ := by group
    rw [this, hz]
    group
  have hxb : x = b := by
    have : x = b * y := by rw [hy]; group
    rw [this, hy1, mul_one]
  rw [hxb]
  exact hb

theorem closure_octSig :
    Subgroup.closure {g | g ∈ (List.finRange 12).map octSig} = alternatingGroup (Fin 8) := by
  obtain ⟨-, -, -, -, -, -, hsign, hvalid, hord⟩ := Certificates.certificate24860
  have hcert : alt8Cert.originalSubgroup =
      Subgroup.closure {g | g ∈ (List.finRange 12).map octSig} :=
    certificate_originalSubgroup _ _ _ _ _
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    exact Equiv.Perm.mem_alternatingGroup.2 (hsign k)
  · rw [← hcert, ← RawSchreierDatum.orderCertificate_eq_card _ hvalid, hord,
      Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide

end Pinned

variable {G : Type} [Group G] {L B : Subgroup G}

theorem egNL_le (L B : Subgroup G) : egNL L B ≤ L := inf_le_right

@[expose] def xE (e : L ≃* NativeSporadic.M24) : egNL L B →* S24 :=
  e.toMonoidHom.comp (Subgroup.inclusion (egNL_le L B))

theorem iotaE_xE (e : L ≃* NativeSporadic.M24) (h : egNL L B) : iotaE e (xE e h) = h := by
  show ((e.symm (e (Subgroup.inclusion (egNL_le L B) h)) : L) : G) = h
  rw [MulEquiv.symm_apply_apply]
  rfl

section Abstract

variable {e : L ≃* NativeSporadic.M24}
  (he : ∀ x : L, (x : G) ∈ B ↔ ((e x : NativeSporadic.M24) : S24) ∈ m24B0l)
include he

theorem xE_norm (h : egNL L B) : ∀ y ∈ m24B0l, (xE e h)⁻¹ * y * xE e h ∈ m24B0l := by
  intro y hy
  rw [← iotaE_mem_B_iff he, map_mul, map_mul, map_inv, iotaE_xE]
  exact (Subgroup.mem_normalizer_iff''.1 (Subgroup.mem_inf.1 h.2).1 _).1
    ((iotaE_mem_B_iff he y).2 hy)

theorem xE_norm' (h : egNL L B) : ∀ y ∈ m24B0l, xE e h * y * (xE e h)⁻¹ ∈ m24B0l := by
  intro y hy
  rw [← iotaE_mem_B_iff he, map_mul, map_mul, map_inv, iotaE_xE]
  exact (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 h.2).1 _).1
    ((iotaE_mem_B_iff he y).2 hy)


@[expose] def sigmaE : egNL L B →* Equiv.Perm (Fin 8) where
  toFun h := octAct (xE e h) (inO_of_norm (xE_norm he h)) (inO_of_norm' (xE_norm' he h))
  map_one' := by
    refine Equiv.Perm.ext fun i => ?_
    show octIdx ((xE e 1 : Equiv.Perm (Fin 24)) (octPt i)) = i
    rw [map_one, Subgroup.coe_one, Equiv.Perm.one_apply, octIdx_octPt]
  map_mul' h h' := by
    refine Equiv.Perm.ext fun i => ?_
    have h1 : octPt (octIdx ((xE e h' : Equiv.Perm (Fin 24)) (octPt i))) =
        (xE e h' : Equiv.Perm (Fin 24)) (octPt i) := inO_of_norm (xE_norm he h') i
    show octIdx ((xE e (h * h') : Equiv.Perm (Fin 24)) (octPt i)) =
      octIdx ((xE e h : Equiv.Perm (Fin 24))
        (octPt (octIdx ((xE e h' : Equiv.Perm (Fin 24)) (octPt i)))))
    rw [h1, map_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply]

theorem sigmaE_apply (h : egNL L B) (i : Fin 8) :
    sigmaE he h i = octIdx ((xE e h : Equiv.Perm (Fin 24)) (octPt i)) := rfl

theorem sigmaE_eq_one_iff (h : egNL L B) :
    sigmaE he h = 1 ↔ (h : G) ∈ B := by
  constructor
  · intro h1
    have hfix : ∀ i, (xE e h : Equiv.Perm (Fin 24)) (octPt i) = octPt i := by
      intro i
      have h2 : octIdx ((xE e h : Equiv.Perm (Fin 24)) (octPt i)) = i := by
        rw [← sigmaE_apply he, h1, Equiv.Perm.one_apply]
      have h3 : octPt (octIdx ((xE e h : Equiv.Perm (Fin 24)) (octPt i))) =
          (xE e h : Equiv.Perm (Fin 24)) (octPt i) := inO_of_norm (xE_norm he h) i
      rw [← h3, h2]
    exact (he _).2 (mem_B0_of_fix _ hfix)
  · intro hB
    have hx : xE e h ∈ m24B0l := (he _).1 hB
    refine Equiv.Perm.ext fun i => ?_
    rw [sigmaE_apply, Certificates.certificate24860.1 _ hx i, octIdx_octPt,
      Equiv.Perm.one_apply]


@[expose] def letterE (hBL : B ≤ L) (k : Fin 12) : egNL L B :=
  ⟨iotaE e (tvEl k), iotaE_mem_egNL hBL he (Certificates.certificate24858 k).1⟩

theorem xE_letterE (hBL : B ≤ L) (k : Fin 12) : xE e (letterE he hBL k) = tvEl k := by
  have h1 : Subgroup.inclusion (egNL_le L B) (letterE he hBL k) = e.symm (tvEl k) :=
    Subtype.ext rfl
  show e (Subgroup.inclusion (egNL_le L B) (letterE he hBL k)) = tvEl k
  rw [h1, MulEquiv.apply_symm_apply]

theorem sigmaE_letterE (hBL : B ≤ L) (k : Fin 12) : sigmaE he (letterE he hBL k) = octSig k := by
  refine Equiv.Perm.ext fun i => ?_
  rw [sigmaE_apply, xE_letterE, Certificates.certificate24860.2.2.2.2.2.1 k i,
    octIdx_octPt]

theorem alt_le_range (hBL : B ≤ L) : alternatingGroup (Fin 8) ≤ (sigmaE he).range := by
  rw [← closure_octSig, Subgroup.closure_le]
  intro g hg
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  exact MonoidHom.mem_range.2 ⟨letterE he hBL k, sigmaE_letterE he hBL k⟩

theorem sigmaE_mem_alt
    (hBL : B ≤ L)
    (hcentL : ∀ l ∈ L, (∀ b ∈ B, l * b = b * l) → l ∈ B) (h : egNL L B) :
    sigmaE he h ∈ alternatingGroup (Fin 8) := by
  obtain ⟨-, hinj, hadd, hmem, hsurj⟩ := Certificates.certificate24856
  have hlet := Certificates.certificate24858
  have hE : EpsHyp B (fun c => iotaE e (ebasis4 fB c)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c d
      show iotaE e (ebasis4 fB (c + d)) = iotaE e (ebasis4 fB c) * iotaE e (ebasis4 fB d)
      rw [← hadd, map_mul]
    · intro c d hcd
      exact hinj c d (iotaE_injective e hcd)
    · intro c
      exact (iotaE_mem_B_iff he _).2 (hmem c)
    · intro u hu
      obtain ⟨y, rfl⟩ := exists_iotaE_eq e (hBL hu)
      obtain ⟨c, hc⟩ := hsurj y ((iotaE_mem_B_iff he y).1 hu)
      exact ⟨c, show iotaE e (ebasis4 fB c) = iotaE e y by rw [hc]⟩
  obtain ⟨l, hl⟩ := hE.exists_word_mul (H := egNL L B) (g := fun k => iotaE e (tvEl k))
    (A := Atv) (fun x hx u hu => (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hx).1 u).1 hu)
    (fun k => iotaE_mem_egNL hBL he (hlet k).1)
    (fun x hx hxc => hcentL x (Subgroup.mem_inf.1 hx).2 hxc) exists_word_of_mul_eq_one
    (fun k c => by
      show iotaE e (tvEl k) * iotaE e (ebasis4 fB c) * (iotaE e (tvEl k))⁻¹ =
        iotaE e (ebasis4 fB (c ᵥ* Atv k))
      rw [← map_inv, ← map_mul, ← map_mul, (hlet k).2 c]) h.2
  obtain ⟨w, hwdef⟩ : ∃ w : egNL L B, w = (l.map (letterE he hBL)).prod := ⟨_, rfl⟩
  have hw : (w : G) = (l.map fun k => iotaE e (tvEl k)).prod := by
    rw [hwdef, show (((l.map (letterE he hBL)).prod : egNL L B) : G) =
      (egNL L B).subtype (l.map (letterE he hBL)).prod from rfl, map_list_prod, List.map_map]
    rfl
  have hu : sigmaE he (w⁻¹ * h) = 1 := by
    rw [sigmaE_eq_one_iff he]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hw]
    exact hl
  have hwh : sigmaE he h = sigmaE he w := by
    have e1 : h = w * (w⁻¹ * h) := by group
    rw [e1, map_mul, hu, mul_one]
  rw [hwh, hwdef, map_list_prod, List.map_map]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  rw [Function.comp_apply, sigmaE_letterE]
  exact Equiv.Perm.mem_alternatingGroup.2 (Certificates.certificate24860.2.2.2.2.2.2.1 k)

end Abstract

end CFSG.EvenSporadicStandard.M24Std.Alt8

namespace CFSG.EvenSporadicStandard.M24Std

open Alt8

variable {G : Type} [Group G]

theorem alt8Data_of_type
    {L B : Subgroup G} (h : OctadType L B) : Alt8Data L B := by
  have hcentL := cent_of_octadType h
  obtain ⟨hBL, e, he⟩ := h
  refine ⟨(sigmaE he).codRestrict (alternatingGroup (Fin 8))
    (sigmaE_mem_alt he hBL hcentL), ?_, ?_⟩
  · intro a
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (alt_le_range he hBL a.2)
    exact ⟨x, Subtype.ext hx⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← sigmaE_eq_one_iff he]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1

end CFSG.EvenSporadicStandard.M24Std
