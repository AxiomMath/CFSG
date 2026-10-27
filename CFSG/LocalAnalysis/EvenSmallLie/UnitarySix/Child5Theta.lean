module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5ThetaGen
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5ThetaMat
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Defs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DCoord
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSU

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaSec3
open CFSG.Fischer

variable {G : Type} [Group G] {L : Subgroup G}
variable (e : L ≃* T46) (t : G)

theorem coordHyp₁ : CoordHyp (sK₁ e) (sA₁ e) (zpowers (sec3DData e t).z) (kappaN e) where
  add := kappaN_mul
  ker := kappaN_eq_zero_iff (t := t)
  surj := kappaN_surj
  norm := fun k hk a ha => (mem_normalizer_iff.mp (toG_le_normalizer (e := e)
    (grp_le_T46 gensOK_chK1) (grp_le_T46 gensOK_chA1) chK1_le_normalizer_A1 hk) a).mp ha
  normZ := fun k hk y hy => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    have hkz : k * (sec3DData e t).z = (sec3DData e t).z * k :=
      mem_centralizer_singleton_iff.mp (d_K₁_cent_z (e := e) (t := t) hk)
    rw [(Commute.zpow_right hkz n).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) n

@[expose] noncomputable def rep₁ : sK₁ e →* GL (Fin 8) (ZMod 2) := (coordHyp₁ e t).rep

theorem rep₁_spec (k : sK₁ e) {a : G} (ha : a ∈ sA₁ e) :
    kappaN e ((k : G) * a * (k : G)⁻¹) =
      ((rep₁ e t k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ kappaN e a :=
  (coordHyp₁ e t).κ_conj_rep k ha

theorem rep₁_gK₁ (j : Fin 5) :
    ((rep₁ e t ⟨gK₁ j, gK₁_mem j⟩ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      YamadaD.wedgeMatN j := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨a, ha, rfl⟩ := kappaN_surj (e := e) v
  rw [← rep₁_spec e t ⟨gK₁ j, gK₁_mem j⟩ ha]
  exact kappaN_conj j a ha

section Conj

@[expose] noncomputable def Pm : GL (Fin 8) (ZMod 2) :=
  ⟨toMat 8 8 PBits, toMat 8 8 PinvBits, toMat_P_mul, toMat_Pinv_mul⟩

@[expose] noncomputable def thetaK₁' : sK₁ e →* GL (Fin 8) (ZMod 2) :=
  (MulAut.conj Pm).toMonoidHom.comp (rep₁ e t)

theorem coe_thetaK₁' (k : sK₁ e) :
    ((thetaK₁' e t k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      toMat 8 8 PBits * ((rep₁ e t k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
        toMat 8 8 PinvBits := by
  simp only [thetaK₁', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Units.val_mul]
  rfl

theorem thetaK₁'_gK₁ (j : Fin 5) :
    ((thetaK₁' e t ⟨gK₁ j, gK₁_mem j⟩ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      toMat 8 8 (cBits j) := by
  rw [coe_thetaK₁', rep₁_gK₁, toMat_cBits]

@[expose] noncomputable def gK₁' (j : ℕ) : sK₁ e := ⟨gK₁ (Fin.ofNat 5 j), gK₁_mem _⟩

theorem thetaK₁'_gK₁' {j : ℕ} (hj : j < 5) :
    ((thetaK₁' e t (gK₁' e j) : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      toMat 8 8 (cBits j) := by
  rw [gK₁', thetaK₁'_gK₁]
  congr 2
  simp [Nat.mod_eq_of_lt hj]

@[expose] noncomputable def gK₁W (w : List ℕ) : sK₁ e := (w.map (gK₁' e)).prod

theorem thetaK₁'_gK₁W : ∀ w : List ℕ, (∀ j ∈ w, j < 5) →
    ((thetaK₁' e t (gK₁W e w) : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      toMat 8 8 (cWord w)
  | [], _ => by
    rw [gK₁W, List.map_nil, List.prod_nil, map_one, Units.val_one, toMat_cWord_nil]
  | j :: w, hw => by
    rw [gK₁W, List.map_cons, List.prod_cons, map_mul, Units.val_mul, ← gK₁W,
      thetaK₁'_gK₁' e t (hw j List.mem_cons_self),
      thetaK₁'_gK₁W w fun i hi => hw i (List.mem_cons_of_mem j hi), toMat_cWord_cons]

end Conj

section Members

theorem gK₁'_mem_K₂ {j : ℕ} (hj : j = 0 ∨ j = 1 ∨ j = 3) : (gK₁' e j : G) ∈ sK₂ e := by
  rcases hj with rfl | rfl | rfl
  · exact gw_mem_ch (by decide)
  · exact gw_mem_ch (by decide)
  · exact gw_mem_ch (by decide)

theorem gK₁'_two_mem_A₂ : (gK₁' e 2 : G) ∈ sA₂ e := gw_mem_ch (by decide)

theorem gK₁W_mem_K₂ : ∀ w : List ℕ, (∀ j ∈ w, j = 0 ∨ j = 1 ∨ j = 3) → (gK₁W e w : G) ∈ sK₂ e
  | [], _ => by rw [gK₁W, List.map_nil, List.prod_nil]; exact one_mem _
  | j :: w, hw => by
    rw [gK₁W, List.map_cons, List.prod_cons, ← gK₁W, Subgroup.coe_mul]
    exact mul_mem (gK₁'_mem_K₂ e (hw j List.mem_cons_self))
      (gK₁W_mem_K₂ w fun i hi => hw i (List.mem_cons_of_mem j hi))

theorem sK₂_le_normalizer_sA₂ : sK₂ e ≤ normalizer (sA₂ e : Set G) :=
  toG_le_normalizer (grp_le_T46 gensOK_chK2) (grp_le_T46 gensOK_chA2) chK2_le_normalizer_A2

@[expose] noncomputable def termsElt (l : List (List ℕ)) : sK₁ e :=
  (l.map fun c => gK₁W e c * gK₁' e 2 * (gK₁W e c)⁻¹).prod

theorem termsElt_mem_A₂ : ∀ l : List (List ℕ), (∀ c ∈ l, ∀ j ∈ c, j = 0 ∨ j = 1 ∨ j = 3) →
    (termsElt e l : G) ∈ sA₂ e
  | [], _ => by rw [termsElt, List.map_nil, List.prod_nil]; exact one_mem _
  | c :: l, hl => by
    rw [termsElt, List.map_cons, List.prod_cons, ← termsElt, Subgroup.coe_mul]
    refine mul_mem ?_ (termsElt_mem_A₂ l fun c' hc' => hl c' (List.mem_cons_of_mem c hc'))
    have hc := gK₁W_mem_K₂ e c (hl c List.mem_cons_self)
    have h1 := (mem_normalizer_iff.mp (sK₂_le_normalizer_sA₂ e hc) _).mp (gK₁'_two_mem_A₂ e)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1

end Members

section Iso

theorem thetaK₁'_gK₁_mem (j : Fin 5) : thetaK₁' e t ⟨gK₁ j, gK₁_mem j⟩ ∈ SU42b := by
  have h : thetaK₁' e t ⟨gK₁ j, gK₁_mem j⟩ = wordGL (wordA j) :=
    Units.ext (by rw [thetaK₁'_gK₁, coe_wordGL_wordA j.2])
  rw [h]
  exact wordGL_mem _

theorem thetaK₁'_mem (k : sK₁ e) : thetaK₁' e t k ∈ SU42b := by
  set X : Subgroup G := (SU42b.comap (thetaK₁' e t)).map (sK₁ e).subtype
  have hgen : ∀ j : Fin 5, gK₁ (e := e) j ∈ X := fun j =>
    ⟨⟨gK₁ j, gK₁_mem j⟩, thetaK₁'_gK₁_mem e t j, rfl⟩
  have hle : sK₁ e ≤ X := by
    refine toG_le_of_gens gensOK_chK1 fun w hw => ?_
    simp only [chK1, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact hgen 0
    · exact hgen 1
    · exact hgen 2
    · exact hgen 3
    · exact hgen 4
  obtain ⟨k', hk', hkk'⟩ := hle k.2
  have : k' = k := Subtype.ext hkk'
  rw [← this]
  exact hk'

@[expose] noncomputable def thetaK₁'' : sK₁ e →* SU42b :=
  (thetaK₁' e t).codRestrict SU42b (thetaK₁'_mem e t)

theorem thetaK₁''_surj : Function.Surjective (thetaK₁'' e t) := by
  have hx : ∀ s : ℕ, s < 2 → genGL (Fin.ofNat 3 s) ∈ (thetaK₁' e t).range := fun s hs => by
    refine ⟨gK₁W e (wordB s), Units.ext ?_⟩
    have hw : ∀ j ∈ wordB s, j < 5 := by
      interval_cases s <;> decide
    rw [thetaK₁'_gK₁W e t _ hw, coe_genGL]
    interval_cases s
    · rw [thetaCheck_parts.2.2.2.2.1]; rfl
    · rw [thetaCheck_parts.2.2.2.2.2.1]; rfl
  have hle : SU42b ≤ (thetaK₁' e t).range := by
    rw [SU42b, closure_le]
    rintro g (rfl | rfl)
    · exact hx 0 (by norm_num)
    · exact hx 1 (by norm_num)
  intro g
  obtain ⟨k, hk⟩ := hle g.2
  exact ⟨k, Subtype.ext hk⟩

theorem card_sK₁_eq : Nat.card (sK₁ e) = 25920 := by
  rw [sK₁, card_toG_ch gensOK_chK1, card_chK1]

theorem thetaK₁''_bij : Function.Bijective (thetaK₁'' e t) := by
  have : Finite (sK₁ e) := Nat.finite_of_card_ne_zero (by rw [card_sK₁_eq]; norm_num)
  exact (thetaK₁''_surj e t).bijective_of_nat_card_le (by rw [card_SU42b, card_sK₁_eq])

@[expose] noncomputable def thetaK₁ : sK₁ e ≃* SU42b :=
  MulEquiv.ofBijective (thetaK₁'' e t) (thetaK₁''_bij e t)

theorem coe_thetaK₁ (k : sK₁ e) :
    ((thetaK₁ e t k : SU42b) : GL (Fin 8) (ZMod 2)) = thetaK₁' e t k := rfl

theorem thetaK₁'_inv_gK₁W (w : List ℕ) (hw : ∀ j ∈ w, j < 5) :
    ((thetaK₁' e t (gK₁W e w)⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      toMat 8 8 (cWord w.reverse) := by
  rw [map_inv]
  set u := thetaK₁' e t (gK₁W e w)
  have hu : (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = toMat 8 8 (cWord w) :=
    thetaK₁'_gK₁W e t w hw
  have h1 : (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) * toMat 8 8 (cWord w.reverse) = 1 := by
    rw [hu]
    exact toMat_cWord_mul_reverse w hw
  calc ((u⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))
      = ((u⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
          ((u : Matrix (Fin 8) (Fin 8) (ZMod 2)) * toMat 8 8 (cWord w.reverse)) := by
        rw [h1, mul_one]
    _ = toMat 8 8 (cWord w.reverse) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem thetaK₁'_termsElt : ∀ l : List (List ℕ), (∀ c ∈ l, ∀ j ∈ c, j < 5) →
    ((thetaK₁' e t (termsElt e l) : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      toMat 8 8 (termsProd l)
  | [], _ => by
    rw [termsElt, List.map_nil, List.prod_nil, map_one, Units.val_one, termsProd, toMat_id8]
  | c :: l, hl => by
    have hc : ∀ j ∈ c, j < 5 := hl c List.mem_cons_self
    rw [termsElt, List.map_cons, List.prod_cons, ← termsElt, map_mul, Units.val_mul,
      thetaK₁'_termsElt l fun c' hc' => hl c' (List.mem_cons_of_mem c hc'), termsProd, toMat_bmul,
      conjTerm, toMat_bmul, toMat_bmul, map_mul, map_mul, Units.val_mul, Units.val_mul,
      thetaK₁'_gK₁W e t c hc, thetaK₁'_gK₁' e t (by norm_num : 2 < 5), thetaK₁'_inv_gK₁W e t c hc]

end Iso

section Coords

@[expose] noncomputable def ιK₁ (u : Fin 8 → ZMod 2) : G :=
  (coordHyp₁ e t).ι (toMat 8 8 PinvBits *ᵥ u)

theorem ιK₁_mem (u : Fin 8 → ZMod 2) : ιK₁ e t u ∈ sA₁ e := (coordHyp₁ e t).ι_mem _

theorem κ_ιK₁ (u : Fin 8 → ZMod 2) : kappaN e (ιK₁ e t u) = toMat 8 8 PinvBits *ᵥ u :=
  (coordHyp₁ e t).κ_ι _

theorem thetaK₁_symm_eq {k : sK₁ e} {g : SU42b}
    (h : ((thetaK₁' e t k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      ((g : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) :
    (thetaK₁ e t).symm g = k := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (Units.ext h.symm)

theorem K₁_ι_aux (k : sK₁ e) (u : Fin 8 → ZMod 2) :
    ((k : G) * ιK₁ e t u * (k : G)⁻¹)⁻¹ * ιK₁ e t
      (((thetaK₁ e t k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u) ∈
      zpowers (sec3DData e t).z := by
  have hk := (coordHyp₁ e t).norm _ k.2 _ (ιK₁_mem e t u)
  refine (coordHyp₁ e t).mem_of_κ_eq hk (ιK₁_mem e t _) ?_
  rw [rep₁_spec e t k (ιK₁_mem e t u), κ_ιK₁, κ_ιK₁, coe_thetaK₁, coe_thetaK₁',
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    toMat_Pinv_mul, Matrix.one_mul]

theorem E_mem_aux {m : ℕ} (hm : m < 4) :
    (((thetaK₁ e t).symm (eSU m) : sK₁ e) : G) ∈ sA₂ e := by
  have hl : ∀ c ∈ eDec m, ∀ j ∈ c, j = 0 ∨ j = 1 ∨ j = 3 := by
    interval_cases m <;> decide
  have hl5 : ∀ c ∈ eDec m, ∀ j ∈ c, j < 5 := fun c hc j hj => by
    rcases hl c hc j hj with rfl | rfl | rfl <;> norm_num
  rw [thetaK₁_symm_eq e t (k := termsElt e (eDec m)) (by
    rw [thetaK₁'_termsElt e t _ hl5, coe_eSU m hm, thetaCheck_parts.2.2.2.2.2.2.1 m hm])]
  exact termsElt_mem_A₂ e _ hl

theorem ν_mem_aux {j : ℕ} (hj : j < 2) :
    (((thetaK₁ e t).symm (nuSU j) : sK₁ e) : G) ∈ sK₂ e ⊔ sA₂ e := by
  have hl : ∀ c ∈ (nuDec j).1, ∀ i ∈ c, i = 0 ∨ i = 1 ∨ i = 3 := by
    interval_cases j <;> decide
  have hw : ∀ i ∈ (nuDec j).2, i = 0 ∨ i = 1 ∨ i = 3 := by
    interval_cases j <;> decide
  have hl5 : ∀ c ∈ (nuDec j).1, ∀ i ∈ c, i < 5 := fun c hc i hi => by
    rcases hl c hc i hi with rfl | rfl | rfl <;> norm_num
  have hw5 : ∀ i ∈ (nuDec j).2, i < 5 := fun i hi => by
    rcases hw i hi with rfl | rfl | rfl <;> norm_num
  rw [thetaK₁_symm_eq e t (k := termsElt e (nuDec j).1 * gK₁W e (nuDec j).2) (by
    rw [map_mul, Units.val_mul, thetaK₁'_termsElt e t _ hl5, thetaK₁'_gK₁W e t _ hw5,
      ← toMat_bmul, coe_nuSU j hj, thetaCheck_parts.2.2.2.2.2.2.2 j hj])]
  rw [Subgroup.coe_mul]
  exact mul_mem (mem_sup_right (termsElt_mem_A₂ e _ hl)) (mem_sup_left (gK₁W_mem_K₂ e _ hw))

theorem y13Coords : Y13Coords (sec3DData e t) (thetaK₁ e t) (ιK₁ e t) where
  ι_mem u := ιK₁_mem e t u
  ι_add u v := by
    refine (coordHyp₁ e t).mem_of_κ_eq (mul_mem (ιK₁_mem e t u) (ιK₁_mem e t v))
      (ιK₁_mem e t _) ?_
    rw [(coordHyp₁ e t).add _ (ιK₁_mem e t u) _ (ιK₁_mem e t v), κ_ιK₁, κ_ιK₁, κ_ιK₁,
      Matrix.mulVec_add]
  ι_inj u hu := by
    have h0 : kappaN e (ιK₁ e t u) = 0 := ((coordHyp₁ e t).ker _ (ιK₁_mem e t u)).mpr hu
    rw [κ_ιK₁] at h0
    calc u = (toMat 8 8 PBits * toMat 8 8 PinvBits) *ᵥ u := by rw [toMat_P_mul, Matrix.one_mulVec]
      _ = toMat 8 8 PBits *ᵥ (toMat 8 8 PinvBits *ᵥ u) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  K₁_ι k u := K₁_ι_aux e t k u
  E_mem m hm := E_mem_aux e t hm
  ν_mem j hj := ν_mem_aux e t hj

end Coords

end CFSG.EvenSmallLie.UnitarySix.Child5
