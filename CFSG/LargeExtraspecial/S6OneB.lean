module

public import CFSG.LargeExtraspecial.S4SevenAMain
public import CFSG.LargeExtraspecial.S6Fix
public import CFSG.LargeExtraspecial.S6Mod
public import CFSG.LargeExtraspecial.S6Swap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem resV_aV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hth : t ∈ S.Lbar ((h : G) * g)) :
    resV haQ t ⟨S.ρ h, hh⟩ (aV ht) = bV hth :=
  Subtype.ext (by rw [coe_resV_apply, coe_bV]; exact ρ_cl_conj_z S h haQ)

theorem LhmodN_eq_pointRadical (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hth : t ∈ S.Lbar ((h : G) * g))
    {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
    (hX : RmodN S g t = omegaGroup Q hQ) (hE : LmodN S g t = pointRadical Q (aV ht)) :
    LhmodN S g t h = pointRadical Q (bV hth) := by
  set e := resV H.conj_mem t ⟨S.ρ h, hh⟩ with he
  have heR : e ∈ RmodN S g t := by rw [← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  have heO : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (mem_omegaGroup.mp (hX ▸ heR)).1
  have hea : e (aV ht) = bV hth := resV_aV H.conj_mem ht hh hth
  rw [LhmodN_eq_map_conj H ht hth heR hea, hE]
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := conj_mem_pointRadical heO hw
    rwa [hea] at this
  · intro w hw
    refine ⟨e⁻¹ * w * e, ?_, by simp [mul_assoc]⟩
    have hb' : e⁻¹ (bV hth) = aV ht := by
      rw [← hea]
      exact e.symm_apply_apply _
    have h1 := conj_mem_pointRadical (inv_mem heO) hw
    rwa [inv_inv, hb'] at h1

variable (S g) in
@[expose] noncomputable def wvRep (H : Hyp4 S g) (t : S.O)
    (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) :
    Y →* (↥((Wt S g t).map (Vt S g t).mkQ) ≃ₗ[ZMod 2] ↥((Wt S g t).map (Vt S g t).mkQ)) :=
  (secRep S g H.conj_mem t (Vt S g t) (Wt S g t)
    (fun _ hx _ hv => apply_mem_Vt_of_mem_Rbar H.conj_mem hx hv)
    (fun _ hx _ hv => apply_mem_Wt H hx hv) hN).comp
    (MulEquiv.subgroupCongr hY.symm).toMonoidHom

theorem wvRep_apply (H : Hyp4 S g) {t : S.O}
    (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) {e : Y}
    {x : Rbar S g t} (hex : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x)
    {w : S.Qt} (hw : w ∈ Wt S g t) :
    ((wvRep S g H t hN hY e (secMk (Vt S g t) hw) :
      ↥((Wt S g t).map (Vt S g t).mkQ)) : S.Qt ⧸ Vt S g t) =
      (Vt S g t).mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
  unfold wvRep
  rw [MonoidHom.comp_apply, secRep_resV H.conj_mem _ _ _
    (e := (MulEquiv.subgroupCongr hY.symm).toMonoidHom e) hex]
  rfl

theorem mem_fixOf_wvRep_iff (H : Hyp4 S g) {t : S.O}
    (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y)
    {T : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} {K : Set S.O} (hKR : K ⊆ Rbar S g t)
    (hT : ∀ e ∈ Y, e ∈ T ↔ ∃ x, ∃ hx : x ∈ K, e = resV H.conj_mem t ⟨x, hKR hx⟩)
    {w : S.Qt} (hw : w ∈ Wt S g t) :
    secMk (Vt S g t) hw ∈ S2.fixOf (wvRep S g H t hN hY) T ↔
      ∀ x ∈ K, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  rw [S2.mem_fixOf]
  constructor
  · intro hfix x hx
    have he : resV H.conj_mem t ⟨x, hKR hx⟩ ∈ Y := by
      rw [← hY, ← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
    have h1 := hfix ⟨_, he⟩ ((hT _ he).mpr ⟨x, hx, rfl⟩)
    have h2 := congrArg (fun m : ↥((Wt S g t).map (Vt S g t).mkQ) => (m : S.Qt ⧸ Vt S g t)) h1
    rw [wvRep_apply H hN hY (x := ⟨x, hKR hx⟩) rfl hw, coe_secMk, Submodule.mkQ_apply,
      Submodule.mkQ_apply, Submodule.Quotient.eq] at h2
    exact h2
  · intro hK e he
    obtain ⟨x, hx, hex⟩ := (hT e e.2).mp he
    apply Subtype.ext
    rw [wvRep_apply H hN hY hex hw, coe_secMk, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    exact hK x hx

noncomputable abbrev secSub (t : S.O) (A : Submodule (ZMod 2) S.Qt) :
    Submodule (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ) :=
  (A.map (Vt S g t).mkQ).comap ((Wt S g t).map (Vt S g t).mkQ).subtype

theorem fixOf_eq_secSub {t : S.O}
    {ρ : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t) → Submodule (ZMod 2)
      ↥((Wt S g t).map (Vt S g t).mkQ)} {T : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    {A : Submodule (ZMod 2) S.Qt} (hVA : Vt S g t ≤ A)
    (h : ∀ w (hw : w ∈ Wt S g t), secMk (Vt S g t) hw ∈ ρ T ↔ w ∈ A) :
    ρ T = secSub (g := g) t A := by
  ext m
  obtain ⟨w, hw, rfl⟩ := exists_secMk (Vt S g t) m
  rw [h w hw]
  constructor
  · intro hwA
    exact ⟨w, hwA, rfl⟩
  · rintro ⟨w', hw'A, hw'⟩
    change (Vt S g t).mkQ w' = (Vt S g t).mkQ w at hw'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hw'
    have := add_mem hw'A (hVA (neg_mem hw'))
    rwa [neg_sub, add_sub_cancel] at this

section Two

variable (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
  (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) (hPI : PairInt S g t)
  (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
  {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y)

include hh hb in
theorem pairInt_ab (hPI : PairInt S g t) :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t := by
  have := hPI 1 h (by rw [map_one]; exact one_mem _) hh (by simpa using hb)
  simpa using this

include H hNo C ht ht1 hVQ hh hb hPI

theorem fixOf_wvRep_LmodN :
    S2.fixOf (wvRep S g H t hN hY) (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      secSub (g := g) t ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) := by
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    have := four_le_finrank_Vt H C ht ht1 hVQ hNo
    omega
  obtain ⟨y, hyL, hyb⟩ := exists_L0_not_mem_Qa H C ht ht1 hVQ h3 hh hb
  refine fixOf_eq_secSub le_sup_right fun w hw => ?_
  rw [mem_fixOf_wvRep_iff H hN hY (K := (S.Lbar g : Set S.O)) (fun x hx => Lbar_le_Rbar ht hx)
    (fun e he => ?_) hw]
  · have hyhR : S.ρ (y * h) ∈ Rbar S g t := by
      rw [map_mul]; exact mul_mem (Lbar_le_Rbar ht (ρ_mem_Lbar S hyL)) hh
    have hP := hPI h (y * h) hh hyhR (by simpa [mul_assoc] using hyb)
    simp only [Subgroup.coe_mul, mul_assoc] at hP
    exact forall_apply_sub_mem_Vt_iff H C ht ht1 hVQ hh hyL hyb hP hw
  · rw [SetLike.mem_coe, ← map_subgroupOf_resV H.conj_mem ht]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨_, hl, rfl⟩

theorem fixOf_wvRep_LhmodN :
    S2.fixOf (wvRep S g H t hN hY) (LhmodN S g t h : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      secSub (g := g) t ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) := by
  have hth := mem_Lbar_of_pair H ht hh
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    have := four_le_finrank_Vt H C ht ht1 hVQ hNo
    omega
  have hVQ₁ := not_V_le_Qa_mul H hVQ hh
  have hh₁ : S.ρ h⁻¹ ∈ Rbar S ((h : G) * g) t := ρ_inv_mem_Rbar hh
  have hab : g * S.z * g⁻¹ ≠ (h : G) * g * S.z * ((h : G) * g)⁻¹ := fun e =>
    hb (e ▸ S.conj_z_mem_Qa g)
  have hb₁ : ((h⁻¹ : S.M) : G) * ((h : G) * g) * S.z * (((h⁻¹ : S.M) : G) * ((h : G) * g))⁻¹ ∉
      S.Qa ((h : G) * g) := by
    rw [inv_mul_coe]
    exact fun hmem => hb (S.mem_Qa_symm hab hmem)
  have h3' : 3 ≤ finrank (ZMod 2) (Vt S ((h : G) * g) t) := by rwa [Vt_mul]
  obtain ⟨y, hyL, hyb⟩ := exists_L0_not_mem_Qa (H.mul h) (C.mul h) hth ht1 hVQ₁ h3' hh₁ hb₁
  refine fixOf_eq_secSub le_sup_right fun w hw => ?_
  have hw₁ : w ∈ Wt S ((h : G) * g) t := by rwa [Wt_mul]
  have hyR : S.ρ y ∈ Rbar S g t := by
    have := Lbar_le_Rbar hth (ρ_mem_Lbar S hyL)
    rwa [Rbar_mul] at this
  have hP := hPI 1 y (by rw [map_one]; exact one_mem _) hyR (by
    have := hyb
    rw [inv_mul_coe] at this
    simpa using this)
  have hP' : S.clSub (S.QG ⊓ S.Qa (((h⁻¹ : S.M) : G) * ((h : G) * g))) ⊓
      S.clSub (S.QG ⊓ S.Qa ((y : G) * (((h⁻¹ : S.M) : G) * ((h : G) * g)))) ≤
        Vt S ((h : G) * g) t := by
    rw [inv_mul_coe, Vt_mul]
    simpa using hP
  have key := forall_apply_sub_mem_Vt_iff (H.mul h) (C.mul h) hth ht1 hVQ₁ hh₁ hyL hyb hP' hw₁
  rw [Wt_mul, Vt_mul] at key
  rw [mem_fixOf_wvRep_iff H hN hY (K := (S.Lbar ((h : G) * g) : Set S.O))
    (fun x hx => Lbar_mul_le_Rbar hth hx) (fun e he => ?_) hw]
  · exact key
  · constructor
    · rintro ⟨x, hx, hex⟩
      refine ⟨x, hx, LinearEquiv.ext fun v => Subtype.ext ?_⟩
      rw [hex v]
      rfl
    · rintro ⟨x, hx, rfl⟩
      exact resV_mem_LhmodN H.conj_mem hth hx

theorem isCompl_fixOf_wvRep :
    IsCompl (S2.fixOf (wvRep S g H t hN hY) (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)))
      (S2.fixOf (wvRep S g H t hN hY) (LhmodN S g t h : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t))) := by
  have hP := pairInt_ab hh hb hPI
  rw [fixOf_wvRep_LmodN H hNo C ht ht1 hVQ hh hb hPI hN hY,
    fixOf_wvRep_LhmodN H hNo C ht ht1 hVQ hh hb hPI hN hY]
  refine isCompl_comap_map le_sup_right ?_ (sup_Vt_inf_sup_Vt H C ht ht1 hVQ hh hb hP)
  refine le_antisymm (sup_le (sup_le inf_le_right (Vt_le_Wt H ht1))
    (sup_le inf_le_right (Vt_le_Wt H ht1))) ?_
  conv_lhs => rw [← sup_eq_Wt H C ht ht1 hVQ hh hb hP]
  exact sup_le_sup le_sup_left le_sup_left

end Two

end CFSG.LargeExtraspecial.S6
