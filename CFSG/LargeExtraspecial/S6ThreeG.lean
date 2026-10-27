module

public import CFSG.LargeExtraspecial.S6ThreeF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def secRepZ (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O)
    (X Y : Submodule (ZMod 2) S.Qt)
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y)
    (hN : ∀ x ∈ Nbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ X)
    {Z : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hZ : RmodN S g t = Z) :
    Z →* (↥(Y.map X.mkQ) ≃ₗ[ZMod 2] ↥(Y.map X.mkQ)) :=
  (secRep S g haQ t X Y hX hY hN).comp (MulEquiv.subgroupCongr hZ.symm).toMonoidHom

section SecRep

variable (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {X Y : Submodule (ZMod 2) S.Qt}
  (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
  (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y)
  (hN : ∀ x ∈ Nbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ X)
  {Z : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hZ : RmodN S g t = Z)

theorem secRepZ_apply {e : Z} {x : Rbar S g t}
    (hex : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t x) {w : S.Qt} (hw : w ∈ Y) :
    ((secRepZ S g haQ t X Y hX hY hN hZ e (secMk X hw) : ↥(Y.map X.mkQ)) : S.Qt ⧸ X) =
      X.mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
  unfold secRepZ
  rw [MonoidHom.comp_apply, secRep_resV haQ hX hY hN
    (e := (MulEquiv.subgroupCongr hZ.symm).toMonoidHom e) hex]
  rfl

theorem mem_fixOf_secRepZ_iff {T : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} {K : Set S.O}
    (hKR : K ⊆ Rbar S g t)
    (hT : ∀ e ∈ Z, e ∈ T ↔ ∃ x, ∃ hx : x ∈ K, e = resV haQ t ⟨x, hKR hx⟩)
    {w : S.Qt} (hw : w ∈ Y) :
    secMk X hw ∈ S2.fixOf (secRepZ S g haQ t X Y hX hY hN hZ) T ↔
      ∀ x ∈ K, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X := by
  rw [S2.mem_fixOf]
  constructor
  · intro hfix x hx
    have he : resV haQ t ⟨x, hKR hx⟩ ∈ Z := by
      rw [← hZ, ← range_resV haQ t]; exact ⟨_, rfl⟩
    have h1 := hfix ⟨_, he⟩ ((hT _ he).mpr ⟨x, hx, rfl⟩)
    have h2 := congrArg (fun m : ↥(Y.map X.mkQ) => (m : S.Qt ⧸ X)) h1
    rw [secRepZ_apply haQ hX hY hN hZ (x := ⟨x, hKR hx⟩) rfl hw, coe_secMk, Submodule.mkQ_apply,
      Submodule.mkQ_apply, Submodule.Quotient.eq] at h2
    exact h2
  · intro hK e he
    obtain ⟨x, hx, hex⟩ := (hT e e.2).mp he
    apply Subtype.ext
    rw [secRepZ_apply haQ hX hY hN hZ hex hw, coe_secMk, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    exact hK x hx

omit [Finite G] hX hY hN hZ in
theorem eq_comap_map_of_iff {D : Submodule (ZMod 2) ↥(Y.map X.mkQ)}
    {A : Submodule (ZMod 2) S.Qt} (hXA : X ≤ A) (h : ∀ w (hw : w ∈ Y), secMk X hw ∈ D ↔ w ∈ A) :
    D = (A.map X.mkQ).comap (Y.map X.mkQ).subtype := by
  ext m
  obtain ⟨w, hw, rfl⟩ := exists_secMk X m
  rw [h w hw]
  constructor
  · intro hwA
    exact ⟨w, hwA, rfl⟩
  · rintro ⟨w', hw'A, hw'⟩
    change X.mkQ w' = X.mkQ w at hw'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hw'
    have := add_mem hw'A (hXA (neg_mem hw'))
    rwa [neg_sub, add_sub_cancel] at this

end SecRep

section Sp

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem clSub_inf_Wt_le_Wone_of_pair {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) :
    S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t ≤ Wone S g t g ((h : G) * g) := by
  rw [← Wone_pair_eq hCE H hNo C ht ht1 hVQ hSp hh hb hk hk' hkk']
  exact clSub_inf_Wt_le_Wone_pair H C ht ht1 hVQ hk hk' hkk'

theorem finrank_sup_Vone {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) :
    finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g)) = S.width := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have e1 : S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g) =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t :=
    le_antisymm (inf_le_inf_left _ (Wone_le_Wt _ _))
      (le_inf inf_le_left (clSub_inf_Wt_le_Wone_of_pair hCE H hNo C ht ht1 hVQ hSp hh hb hk hk'
        hkk'))
  have d1 := finrank_clSub_inf_Wt (H.mul k) (C.mul k) htk ht1 (not_V_le_Qa_mul H hVQ hk)
  rw [Wt_mul] at d1
  have d2 := finrank_clSub_inf_Vone H C ht ht1 hVQ hk ((k' : G) * g)
  rw [Vone_pair_eq hCE H hNo C ht ht1 hVQ hSp hh hb hk hk' hkk'] at d2
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g))
    (Vone S g t g ((h : G) * g))
  have e2 : S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g) ⊓
      Vone S g t g ((h : G) * g) =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vone S g t g ((h : G) * g) := by
    rw [inf_assoc, inf_eq_right.mpr (Vone_le_Wone H C ht ht1 hVQ hh hb)]
  rw [e2, e1] at hs
  rw [e1]
  omega

theorem sup_clSub_inf_Wone {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) :
    (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wone S g t g ((h : G) * g)) =
      Wone S g t g ((h : G) * g) := by
  have hdec := Wone_eq_sup_pair hCE H hNo C ht ht1 hVQ hSp hk hk' hkk'
  rw [Wone_pair_eq hCE H hNo C ht ht1 hVQ hSp hh hb hk hk' hkk'] at hdec
  refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
  conv_lhs => rw [← hdec]
  exact sup_le_sup (le_inf inf_le_left (clSub_inf_Wt_le_Wone_of_pair hCE H hNo C ht ht1 hVQ hSp
      hh hb hk hk' hkk'))
    (le_inf inf_le_left (clSub_inf_Wt_le_Wone_of_pair hCE H hNo C ht ht1 hVQ hSp hh hb hk'
      hk (not_mem_Qa_symm hkk')))

theorem sup_Vone_inf_sup_Vone {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) :
    ((S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g)) ⊓
      ((S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g)) = Vone S g t g ((h : G) * g) := by
  have dA := finrank_sup_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hk hk' hkk'
  have dB := finrank_sup_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hk' hk (not_mem_Qa_symm hkk')
  have dW := finrank_Wone (S := S) (g := g) (t := t) g ((h : G) * g)
  have dQ := S.finrank_Qt_eq_two_mul_width
  have hVW := Vone_le_Wone H C ht ht1 hVQ hh hb
  have hsup : ((S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g)) ⊔
      ((S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g)) = Wone S g t g ((h : G) * g) := by
    refine le_antisymm (sup_le (sup_le inf_le_right hVW) (sup_le inf_le_right hVW)) ?_
    conv_lhs => rw [← sup_clSub_inf_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hk hk' hkk']
    exact sup_le_sup le_sup_left le_sup_left
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    ((S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g))
    ((S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g))
  rw [hsup] at hs
  refine (Submodule.eq_of_le_of_finrank_le (le_inf le_sup_right le_sup_right) ?_).symm
  omega

theorem mem_sup_Vone_of_fix {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) {y : S.M}
    (hyL : (y : G) ∈ S.L0 ((k : G) * g))
    (hyd : ((y * k' : S.M) : G) * g * S.z * (((y * k' : S.M) : G) * g)⁻¹ ∉ S.Qa ((k' : G) * g))
    {w : S.Qt} (hw : w ∈ Wone S g t g ((h : G) * g))
    (hfix : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g)) :
    w ∈ (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have hyLb : S.ρ y ∈ S.Lbar ((k : G) * g) := ρ_mem_Lbar S hyL
  have hyR : S.ρ y ∈ Rbar S g t := Lbar_mul_le_Rbar htk hyLb
  have hyk' : S.ρ (y * k') ∈ Rbar S g t := by rw [map_mul]; exact mul_mem hyR hk'
  have hcoe : (y : G) * ((k' : G) * g) = ((y * k' : S.M) : G) * g := by simp [mul_assoc]
  have hdecW := sup_clSub_inf_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hk' hyk' hyd
  set V1 := Vone S g t g ((h : G) * g) with hV1
  set W1 := Wone S g t g ((h : G) * g) with hW1
  set ψ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hψ
  have hyy : S.ρ y * S.ρ y = 1 := mul_self_of_mem_Lbar S (H.mul k).conj_mem hyLb
  have hinv : (S.ρ y)⁻¹ = S.ρ y := inv_eq_of_mul_eq_one_right hyy
  have hψψ : ∀ u, ψ (ψ u) = u := fun u => by
    rw [hψ, ← coe_mul_apply, hyy]
    rfl
  have hψV : ∀ v ∈ V1, ψ v ∈ V1 := fun v hv =>
    apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hyR hv
  have hψW : ∀ v ∈ W1, ψ v ∈ W1 := fun v hv =>
    apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hyR hv
  set A := (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ W1) ⊔ V1 with hA
  set B := (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ W1) ⊔ V1 with hB
  set B' := (S.clSub (S.QG ⊓ S.Qa (((y * k' : S.M) : G) * g)) ⊓ W1) ⊔ V1 with hB'
  have hVW : V1 ≤ W1 := Vone_le_Wone H C ht ht1 hVQ hh hb
  have hsup : B ⊔ B' = W1 := by
    refine le_antisymm (sup_le (sup_le inf_le_right hVW) (sup_le inf_le_right hVW)) ?_
    conv_lhs => rw [← hdecW]
    exact sup_le_sup le_sup_left le_sup_left
  have hinf : B ⊓ B' = V1 := sup_Vone_inf_sup_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hk' hyk' hyd
  have hψB : ∀ u ∈ B, ψ u ∈ B' := by
    intro u hu
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    have hx1 := apply_mem_clSub_Qa_mul y hx.1
    rw [hcoe] at hx1
    exact add_mem (Submodule.mem_sup_left ⟨hx1, hψW x hx.2⟩) (Submodule.mem_sup_right (hψV v hv))
  have hψB' : ∀ u ∈ B', ψ u ∈ B := by
    intro u hu
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    refine add_mem (Submodule.mem_sup_left ⟨?_, hψW x hx.2⟩) (Submodule.mem_sup_right (hψV v hv))
    have hx1 : x ∈ S.clSub (S.QG ⊓ S.Qa ((y : G) * ((k' : G) * g))) := by
      rw [hcoe]
      exact hx.1
    rw [mem_clSub_Qa_mul_iff y, hinv] at hx1
    exact hx1
  set F := W1 ⊓ V1.comap ((ψ : S.Qt →ₗ[ZMod 2] S.Qt) - LinearMap.id) with hF
  have hFle := finrank_le_of_swap (ψ : S.Qt →ₗ[ZMod 2] S.Qt) hψψ hψV le_sup_right hsup hinf
    hψB hψB' (inf_le_left : F ≤ W1) fun w hw => hw.2
  have hcV : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ V1 :=
    Vt_le_Vone _ _ (cl_mem_Vt htk)
  have hAF : A ≤ F := by
    intro u hu
    refine ⟨sup_le inf_le_right hVW hu, ?_⟩
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    change ψ (x + v) - (x + v) ∈ V1
    rw [map_add, show ψ x + ψ v - (x + v) = (ψ x - x) + (ψ v - v) by abel]
    refine add_mem ?_ (sub_mem (hψV v hv) hv)
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hcV
      (Lbar_apply_sub_mem_span' (H.mul k).conj_mem hx.1 hyLb)
  have dA := finrank_sup_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hk hk' hkk'
  have dB := finrank_sup_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hk' hyk' hyd
  have hAF' : A = F := Submodule.eq_of_le_of_finrank_le hAF (hFle.trans (dB.trans dA.symm).le)
  rw [hAF']
  exact ⟨hw, hfix⟩

theorem forall_apply_sub_mem_Vone_iff {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g))
    {w : S.Qt} (hw : w ∈ Wone S g t g ((h : G) * g)) :
    (∀ l ∈ S.Lbar ((k : G) * g),
        (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g)) ↔
      w ∈ (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  constructor
  · intro hl
    have h3 : 3 ≤ finrank (ZMod 2) (Vt S ((k : G) * g) t) := by
      have := four_le_finrank_Vt H C ht ht1 hVQ hNo
      rw [Vt_mul]
      omega
    obtain ⟨y, hyL, hyb⟩ := exists_L0_not_mem_Qa (H.mul k) (C.mul k) htk ht1
      (not_V_le_Qa_mul H hVQ hk) h3 (mul_inv_mem_Rbar_mul hk hk')
      (by rw [coe_mul_inv_mul]; exact hkk')
    rw [coe_mul_inv_mul] at hyb
    have hyd : ((y * k' : S.M) : G) * g * S.z * (((y * k' : S.M) : G) * g)⁻¹ ∉
        S.Qa ((k' : G) * g) := by
      simpa [mul_assoc] using hyb
    exact mem_sup_Vone_of_fix hCE H hNo C ht ht1 hVQ hSp hh hb hk hk' hkk' hyL hyd hw
      (hl _ (ρ_mem_Lbar S hyL))
  · intro hu l hl
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, show (l : S.Qt ≃ₗ[ZMod 2] S.Qt) x + (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - (x + v) =
      ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) by abel]
    refine add_mem ?_ (sub_mem (apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb
      (Lbar_mul_le_Rbar htk hl) hv) hv)
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Vt_le_Vone _ _ (cl_mem_Vt htk))
      (Lbar_apply_sub_mem_span' (H.mul k).conj_mem hx.1 hl)

end Sp

end CFSG.LargeExtraspecial.S6
