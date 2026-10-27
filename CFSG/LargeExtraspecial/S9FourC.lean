module

public import CFSG.LargeExtraspecial.S6ThreeG
public import CFSG.LargeExtraspecial.S9Fus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Forms

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem false_of_three_forms [FiniteDimensional (ZMod 2) U] {X B : Submodule (ZMod 2) U}
    (hXB : X ≤ B) (hdim : finrank (ZMod 2) X + 2 = finrank (ZMod 2) B)
    (P : LinearMap.BilinForm (ZMod 2) U) (φ : Fin 3 → U → U)
    (hzero : ∀ i, ∀ w ∈ B, P (φ i w) w = 0)
    (hX : ∀ i, ∀ w ∈ B, ∀ x ∈ X, P (φ i w) x = 0)
    (hnd : ∀ i, ∀ w ∈ B, (∀ w' ∈ B, P (φ i w) w' = 0) → w ∈ X)
    (hadd : ∀ w ∈ B, ∀ w' ∈ B, P (φ 2 w) w' = P (φ 0 w) w' + P (φ 1 w) w') : False := by
  obtain ⟨w₁, hw₁B, hw₁X⟩ : ∃ w ∈ B, w ∉ X := by
    by_contra hcon
    push Not at hcon
    have := Submodule.finrank_mono (show B ≤ X from hcon)
    omega
  have hX'dim : finrank (ZMod 2) ↥(X ⊔ (ZMod 2) ∙ w₁) ≤ finrank (ZMod 2) X + 1 := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank X ((ZMod 2) ∙ w₁)
    have h2 := finrank_span_le_card (R := ZMod 2) ({w₁} : Set U)
    rw [Set.toFinset_singleton, Finset.card_singleton] at h2
    omega
  obtain ⟨X', hX'⟩ : ∃ X' : Submodule (ZMod 2) U, X' = X ⊔ (ZMod 2) ∙ w₁ := ⟨_, rfl⟩
  rw [← hX'] at hX'dim
  have hX'B : X' ≤ B := hX' ▸ sup_le hXB ((Submodule.span_singleton_le_iff_mem _ _).mpr hw₁B)
  obtain ⟨w₂, hw₂B, hw₂X⟩ : ∃ w ∈ B, w ∉ X' := by
    by_contra hcon
    push Not at hcon
    have := Submodule.finrank_mono (show B ≤ X' from hcon)
    omega
  have hsup : X' ⊔ (ZMod 2) ∙ w₂ = B := by
    refine Submodule.eq_of_le_of_finrank_le
      (sup_le hX'B ((Submodule.span_singleton_le_iff_mem _ _).mpr hw₂B)) ?_
    have hlt : X' < X' ⊔ (ZMod 2) ∙ w₂ :=
      lt_of_le_of_ne le_sup_left fun h => hw₂X (h ▸ Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self w₂))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have hlt' : X < X' := by
      rw [hX']
      exact lt_of_le_of_ne le_sup_left fun h => hw₁X (h ▸ Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self w₁))
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt'
    omega
  have key : ∀ i, P (φ i w₁) w₂ = 1 := by
    intro i
    rcases zmod2_eq_zero_or_eq_one (P (φ i w₁) w₂) with h0 | h1
    · exfalso
      refine hw₁X (hnd i w₁ hw₁B fun w' hw' => ?_)
      rw [← hsup] at hw'
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw'
      rw [hX'] at hy
      obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [map_add, map_add, map_smul, map_smul, hX i w₁ hw₁B x hx, hzero i w₁ hw₁B, h0,
        smul_zero, smul_zero, add_zero, add_zero]
    · exact h1
  have := hadd w₁ hw₁B w₂ hw₂B
  rw [key 0, key 1, key 2] at this
  exact absurd this (by decide)

end Forms

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_Vone_of_polar_eq_zero {t : S.O} (g₁ g₂ : G) {u : S.Qt}
    (hu : ∀ w ∈ Wone S g t g₁ g₂, polar S.q u w = 0) : u ∈ Vone S g t g₁ g₂ := by
  set Z := LinearMap.BilinForm.orthogonal S.q.polarBilin (Wone S g t g₁ g₂) with hZ
  have hVZ : Vone S g t g₁ g₂ ≤ Z := by
    intro v hv
    rw [hZ, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [polarBilin_apply_apply, polar_comm]
    exact mem_Wone.mp hw v hv
  have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (Wone S g t g₁ g₂)
  have h2 := finrank_Wone (S := S) (g := g) (t := t) g₁ g₂
  have hZV : Z = Vone S g t g₁ g₂ :=
    (Submodule.eq_of_le_of_finrank_le hVZ (by rw [← hZ] at h1; omega)).symm
  rw [← hZV, hZ, LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  rw [polarBilin_apply_apply, polar_comm]
  exact hu w hw

theorem apply_spRho_one_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {f : LinearMap.BilinForm (ZMod 2) V} (hf : f.IsAlt) {c e : V} (hce : f c e = 0) {v : V}
    (hv : f v c = 1) : f v (spRho hf hce 1 v) = 1 := by
  rw [spRho_apply, map_add, map_add, map_smul, map_smul, hf.self_eq_zero, hv, smul_eq_mul,
    smul_eq_mul]
  ring_nf
  generalize f v e = a
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;> decide

theorem q_eq_zero_of_mem_sup {t : S.O} {h : S.M} (H : Hyp4 S g) (C : Cons311 S g)
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {P : Submodule (ZMod 2) S.Qt}
    (hP : ∀ p ∈ P, S.q p = 0) {w : S.Qt}
    (hw : w ∈ (P ⊓ Wone S g t g ((h : G) * g)) ⊔ Vone S g t g ((h : G) * g)) : S.q w = 0 := by
  obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
  have hpv : polar S.q p v = 0 := by
    rw [polar_comm]
    exact mem_Wone.mp hp.2 v hv
  have : S.q (p + v) = S.q p + S.q v + polar S.q p v := by
    rw [polar]
    abel
  rw [this, hP p hp.1, q_eq_zero_of_mem_Vone H C ht ht1 hVQ hh hb hv, hpv, add_zero, add_zero]

theorem polar_eq_zero_of_q_eq_zero {X : Submodule (ZMod 2) S.Qt} (hX : ∀ x ∈ X, S.q x = 0)
    {u v : S.Qt} (hu : u ∈ X) (hv : v ∈ X) : polar S.q u v = 0 := by
  rw [polar, hX _ (add_mem hu hv), hX u hu, hX v hv]
  simp

section Main

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ)
include hCE H hNo C ht ht1 hVQ hSp

omit hCE hNo hSp in
theorem not_mem_Qa_of_spRho_one {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {y : S.M} {e : Vt S g t}
    (he : beta H C ht ht1 hVQ (aV ht) e = 0)
    (hye : ∀ v : Vt S g t, ((spRho (beta_isAlt H C ht ht1 hVQ) he 1 v : Vt S g t) : S.Qt) =
      ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) :
    ((y * h : S.M) : G) * g * S.z * (((y * h : S.M) : G) * g)⁻¹ ∉ S.Qa ((h : G) * g) := by
  have haQ := H.conj_mem
  have hth := mem_Lbar_of_pair H ht hh
  intro hmem
  have hQ := conj_mem_QG' S (y * h).2 haQ
  have h1 := S.cl_mem_clSub (Subgroup.mem_inf.mpr ⟨hQ, hmem⟩) hQ
  have hcl : S.cl (((y * h : S.M) : G) * g * S.z * (((y * h : S.M) : G) * g)⁻¹) =
      ((S.ρ (y * h) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) :=
    (ρ_cl_conj_z S (y * h) haQ).symm
  rw [map_mul, coe_mul_apply, ρ_cl_conj_z S h haQ, ← coe_bV hth, ← hye] at hcl
  rw [hcl] at h1
  have h2 := (beta_bV_eq_zero_iff H C ht ht1 hVQ hh hth _).mpr h1
  have hba : beta H C ht ht1 hVQ (bV hth) (aV ht) = 1 := by
    rw [beta_symm]
    exact beta_aV_bV H C ht ht1 hVQ hh hb
  rw [apply_spRho_one_eq_one (beta_isAlt H C ht ht1 hVQ) he hba] at h2
  exact one_ne_zero h2

section Forms

variable {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hh hb

omit hCE hNo hSp in
theorem apply_sub_mem_clSub_inf_Wone (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hSp : SpCase H C ht ht1 hVQ) {y : S.M} (hy : (y : G) ∈ S.L0 g) {w : S.Qt}
    (hw : w ∈ Wone S g t g ((h : G) * g)) :
    ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
      S.clSub (S.QG ⊓ S.Qa g) ⊓ Wone S g t g ((h : G) * g) := by
  have hyL := ρ_mem_Lbar S hy
  exact ⟨apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) H.conj_mem (Wone_le_Wt _ _ hw) hyL,
    sub_mem (apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb (Lbar_le_Rbar ht hyL) hw) hw⟩

theorem polar_sub_self_eq_zero {y : S.M} (hy : (y : G) ∈ S.L0 g) {w : S.Qt}
    (hw : w ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g)) :
    polar S.q (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) w = 0 := by
  have hwY : w ∈ Wone S g t g ((h : G) * g) :=
    sup_le inf_le_right (Vone_le_Wone H C ht ht1 hVQ hh hb) hw
  have h0 := S.q_eq_zero_of_mem_clSub_QG_inf_Qa H.conj_ne
    (apply_sub_mem_clSub_inf_Wone H C ht ht1 hVQ hh hb hCE hNo hSp hy hwY).1
  have hiso := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (S.ρ y).2 w
  have hBq := q_eq_zero_of_mem_sup H C ht ht1 hVQ hh hb
    (fun p hp => S.q_eq_zero_of_mem_clSub_QG_inf_Qa (conj_ne_z' S h.2 H.conj_ne) hp) hw
  rw [polar, sub_add_cancel, hiso, hBq, h0]
  simp

theorem polar_sub_eq_zero_of_mem_Vone {y : S.M} (hy : (y : G) ∈ S.L0 g) {w : S.Qt}
    (hw : w ∈ Wone S g t g ((h : G) * g)) {x : S.Qt} (hx : x ∈ Vone S g t g ((h : G) * g)) :
    polar S.q (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) x = 0 := by
  rw [polar_comm]
  exact mem_Wone.mp (apply_sub_mem_clSub_inf_Wone H C ht ht1 hVQ hh hb hCE hNo hSp hy hw).2 x hx

theorem mem_Vone_of_forall_polar {y : S.M} (hy : (y : G) ∈ S.L0 g)
    (hyd : ((y * h : S.M) : G) * g * S.z * (((y * h : S.M) : G) * g)⁻¹ ∉ S.Qa ((h : G) * g))
    {w : S.Qt}
    (hw : w ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g))
    (hw' : ∀ w' ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g),
        polar S.q (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) w' = 0) :
    w ∈ Vone S g t g ((h : G) * g) := by
  have h1 := pair_one (t := t) hb
  have hwY : w ∈ Wone S g t g ((h : G) * g) :=
    sup_le inf_le_right (Vone_le_Wone H C ht ht1 hVQ hh hb) hw
  have hu := apply_sub_mem_clSub_inf_Wone H C ht ht1 hVQ hh hb hCE hNo hSp hy hwY
  have hAq := fun w (hw : w ∈ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g)) =>
    q_eq_zero_of_mem_sup H C ht ht1 hVQ hh hb
      (fun p hp => S.q_eq_zero_of_mem_clSub_QG_inf_Qa H.conj_ne hp) hw
  have hdecW := sup_clSub_inf_Wone hCE H hNo C ht ht1 hVQ hSp hh hb h1.1 hh h1.2
  simp only [OneMemClass.coe_one, one_mul] at hdecW
  have huX : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g) := by
    refine mem_Vone_of_polar_eq_zero _ _ fun w'' hw'' => ?_
    rw [← hdecW] at hw''
    obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp hw''
    rw [polar_add_right, polar_eq_zero_of_q_eq_zero hAq (Submodule.mem_sup_left hu)
      (Submodule.mem_sup_left ha), hw' b (Submodule.mem_sup_left hb'), add_zero]
  have hwA := mem_sup_Vone_of_fix hCE H hNo C ht ht1 hVQ hSp hh hb h1.1 hh h1.2
    (y := y) (by simpa using hy) hyd hwY huX
  simp only [OneMemClass.coe_one, one_mul] at hwA
  have hAB := sup_Vone_inf_sup_Vone hCE H hNo C ht ht1 hVQ hSp hh hb h1.1 hh h1.2
  simp only [OneMemClass.coe_one, one_mul] at hAB
  rw [← hAB]
  exact ⟨hwA, hw⟩

omit hCE hNo hSp in
theorem polar_mul_sub (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hSp : SpCase H C ht ht1 hVQ) {y₁ y₂ : S.M} (hy₁ : (y₁ : G) ∈ S.L0 g)
    (hy₂ : (y₂ : G) ∈ S.L0 g) {w w' : S.Qt} (hw : w ∈ Wone S g t g ((h : G) * g))
    (hw' : w' ∈ Wone S g t g ((h : G) * g)) :
    polar S.q (((S.ρ (y₁ * y₂) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) w' =
      polar S.q (((S.ρ y₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) w' +
        polar S.q (((S.ρ y₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) w' := by
  have hu₂ := (apply_sub_mem_clSub_inf_Wone H C ht ht1 hVQ hh hb hCE hNo hSp hy₂ hw).1
  have hc := Lbar_apply_sub_mem_span' H.conj_mem hu₂ (ρ_mem_Lbar S hy₁)
  obtain ⟨c, hcc⟩ := Submodule.mem_span_singleton.mp hc
  have hpa : polar S.q (S.cl (g * S.z * g⁻¹)) w' = 0 :=
    mem_Wt.mp (Wone_le_Wt _ _ hw') _ (cl_a_mem_Vt ht)
  have e : ((S.ρ (y₁ * y₂) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
      c • S.cl (g * S.z * g⁻¹) + (((S.ρ y₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) +
        (((S.ρ y₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
    rw [hcc, map_mul, coe_mul_apply, map_sub]
    abel
  rw [e, polar_add_left, polar_add_left, polar_smul_left, hpa, smul_zero, zero_add, add_comm]

end Forms

theorem false_of_sp_four_seven (h4 : finrank (ZMod 2) (Vt S g t) = 4) (h7 : S.width = 7) :
    False := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have h1 := pair_one (t := t) hb
  have hβa := beta_isAlt H C ht ht1 hVQ
  obtain ⟨d, d', hd, hd', hdd'⟩ := exists_hyperbolic_perp hβa
    (beta_nondegenerate H C ht ht1 hVQ) (by omega) (aV_ne_zero H ht)
  have hdd'' : beta H C ht ht1 hVQ (aV ht) (d + d') = 0 := by rw [map_add, hd, hd', add_zero]
  have hlift : ∀ {e : Vt S g t} (he : beta H C ht ht1 hVQ (aV ht) e = 0), ∃ y : S.M,
      (y : G) ∈ S.L0 g ∧ ∀ v : Vt S g t, ((spRho hβa he 1 v : Vt S g t) : S.Qt) =
        ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro e he
    have hmem : spRho hβa he 1 ∈ LmodN S g t := by
      rw [hSp.LmodN_eq]
      exact spRho_mem_spPointRadical hβa he 1
    obtain ⟨l, hl, hle⟩ := hmem
    obtain ⟨y, hyL, rfl⟩ := (mem_Lbar S).mp hl
    exact ⟨y, hyL, hle⟩
  obtain ⟨y₁, hy₁L, hy₁⟩ := hlift hd
  obtain ⟨y₂, hy₂L, hy₂⟩ := hlift hd'
  have hy₃ : ∀ v : Vt S g t, ((spRho hβa hdd'' 1 v : Vt S g t) : S.Qt) =
      ((S.ρ (y₁ * y₂) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro v
    have e1 : spRho hβa hd 1 * spRho hβa hd' 1 = spRho hβa hdd'' 1 := by
      rw [spRho_mul hβa hd hd' 1 1 hdd'', hdd']
      rfl
    rw [← e1, LinearEquiv.mul_apply, hy₁, hy₂, map_mul, coe_mul_apply]
  have hy₃L : ((y₁ * y₂ : S.M) : G) ∈ S.L0 g := by
    rw [Subgroup.coe_mul]
    exact mul_mem hy₁L hy₂L
  have hBdim := finrank_sup_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hh h1.1 (not_mem_Qa_symm h1.2)
  have hXdim := finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb
  have hBY : (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
      Vone S g t g ((h : G) * g) ≤ Wone S g t g ((h : G) * g) :=
    sup_le inf_le_right (Vone_le_Wone H C ht ht1 hVQ hh hb)
  have hP : ∀ (y : S.M), (y : G) ∈ S.L0 g →
      ((y * h : S.M) : G) * g * S.z * (((y * h : S.M) : G) * g)⁻¹ ∉ S.Qa ((h : G) * g) →
      (∀ w ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g),
          S.q.polarBilin (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) w = 0) ∧
      (∀ w ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g), ∀ x ∈ Vone S g t g ((h : G) * g),
          S.q.polarBilin (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) x = 0) ∧
      (∀ w ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g),
          (∀ w' ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
            Vone S g t g ((h : G) * g),
              S.q.polarBilin (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) w' = 0) →
          w ∈ Vone S g t g ((h : G) * g)) := fun y hy hyd =>
    ⟨fun w hw => polar_sub_self_eq_zero hCE H hNo C ht ht1 hVQ hSp hh hb hy hw,
      fun w hw x hx => polar_sub_eq_zero_of_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hy
        (hBY hw) hx,
      fun w hw hw' => mem_Vone_of_forall_polar hCE H hNo C ht ht1 hVQ hSp hh hb hy hyd hw hw'⟩
  have hP₁ := hP y₁ hy₁L (not_mem_Qa_of_spRho_one H C ht ht1 hVQ hh hb hd hy₁)
  have hP₂ := hP y₂ hy₂L (not_mem_Qa_of_spRho_one H C ht ht1 hVQ hh hb hd' hy₂)
  have hP₃ := hP (y₁ * y₂) hy₃L (not_mem_Qa_of_spRho_one H C ht ht1 hVQ hh hb hdd'' hy₃)
  have hdim : finrank (ZMod 2) (Vone S g t g ((h : G) * g)) + 2 = finrank (ZMod 2)
      ↥((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wone S g t g ((h : G) * g)) ⊔
        Vone S g t g ((h : G) * g)) := by omega
  refine false_of_three_forms le_sup_right hdim S.q.polarBilin
    ![fun w => ((S.ρ y₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w,
      fun w => ((S.ρ y₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w,
      fun w => ((S.ρ (y₁ * y₂) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w] ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    exacts [hP₁.1, hP₂.1, hP₃.1]
  · intro i
    fin_cases i
    exacts [hP₁.2.1, hP₂.2.1, hP₃.2.1]
  · intro i
    fin_cases i
    exacts [hP₁.2.2, hP₂.2.2, hP₃.2.2]
  · intro w hw w' hw'
    exact polar_mul_sub H C ht ht1 hVQ hh hb hCE hNo hSp hy₁L hy₂L (hBY hw) (hBY hw')

end Main

end CFSG.LargeExtraspecial.S9
