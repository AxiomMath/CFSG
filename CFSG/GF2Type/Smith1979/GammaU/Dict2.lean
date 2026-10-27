module

public import CFSG.GF2Type.Smith1979.GammaU.Dict
public import CFSG.LargeExtraspecial.DWTrans
public import CFSG.GF2Type.Smith1979.GammaU.SettingBridge
public import CFSG.LargeExtraspecial.S4Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA Module
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

noncomputable abbrev Dt (S : Setting G) (g : G) : Submodule (ZMod 2) S.Qt := S.clSub (S.QG ⊓ S.Qa g)

noncomputable abbrev aT (S : Setting G) (g : G) : S.Qt := S.cl (g * S.z * g⁻¹)

noncomputable abbrev LbarL (S : Setting G) (g : G) : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  (S.Lbar g).map S.O.subtype

@[expose] noncomputable def Ltr (S : Setting G) (g : G) (φ : S.Qt ≃ₗ[ZMod 2] V12) :
    Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  (LbarL S g).map (trEquiv φ).toMonoidHom

theorem mem_Ltr {φ : S.Qt ≃ₗ[ZMod 2] V12} {l : V12 ≃ₗ[ZMod 2] V12} :
    l ∈ Ltr S g φ ↔ ∃ s ∈ S.Lbar g, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) = l := by
  simp only [Ltr, LbarL, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, ⟨s, hs, rfl⟩, rfl⟩

section

variable (H : Hyp4 S g) (C : Cons311 S g)
include H C

theorem maxEA_QG_inf_Qa : DW.MaxEA S (S.QG ⊓ S.Qa g) := ⟨inf_le_left, C.card_QG_inf_Qa⟩

theorem Dt_sing : ∀ v ∈ Dt S g, S.q v = 0 := fun _ hv => by
  haveI := S.isElementaryAbelian_QG_inf_Qa H.conj_ne
  exact DW.MaxEA.q_clSub (A := S.QG ⊓ S.Qa g) hv

theorem finrank_Dt : finrank (ZMod 2) (Dt S g) = S.width := by
  haveI := S.isElementaryAbelian_QG_inf_Qa H.conj_ne
  exact (maxEA_QG_inf_Qa H C).finrank_clSub

end

theorem conj_mem_Qa (g : G) : g * S.z * g⁻¹ ∈ S.Qa g := (S.conjBy g).z_mem_QG

theorem at_mem_Dt (H : Hyp4 S g) : aT S g ∈ Dt S g :=
  S.cl_mem_clSub ⟨H.conj_mem, conj_mem_Qa g⟩ H.conj_mem

theorem aT_ne_zero (H : Hyp4 S g) : aT S g ≠ 0 := cl_conj_z_ne_zero S H.conj_mem H.conj_ne

theorem q_aT (H : Hyp4 S g) : S.q (aT S g) = 0 := q_cl_conj_z S H.conj_mem

theorem Lbar_fix (H : Hyp4 S g) {s : S.O} (hs : s ∈ S.Lbar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) = aT S g := by
  have hmem : aT S g ∈ fixSub S (S.Lbar g) := by
    rw [H.fixSub_eq]
    exact Submodule.mem_span_singleton_self _
  exact (mem_fixSub S).1 hmem s hs

theorem Lbar_perp (H : Hyp4 S g) (C : Cons311 S g) {s : S.O} (hs : s ∈ S.Lbar g) {v : S.Qt}
    (hv : QuadraticMap.polar S.q v (aT S g) = 0) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Dt S g := by
  obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
  rw [S.polar_cl_eq_zero_iff hxQ H.conj_mem] at hv
  refine C.comm_le x ⟨hxQ, ?_⟩ s hs
  show x ∈ Subgroup.centralizer ({g * S.z * g⁻¹} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hv

theorem Lbar_comm (H : Hyp4 S g) {s : S.O} (hs : s ∈ S.Lbar g) {d : S.Qt} (hd : d ∈ Dt S g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) d - d = 0 ∨ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) d - d = aT S g := by
  obtain ⟨y, hy, rfl⟩ := (mem_Lbar S).1 hs
  obtain ⟨x, ⟨-, hxa⟩, hxQ, rfl⟩ := S.mem_clSub_iff.1 hd
  rw [S.ρ_cl y hxQ]
  have hyQ : (y : G) ∈ (S.conjBy g).QG := hy.1
  rcases (S.conjBy g).commutator_eq_one_or_z hyQ hxa with h | h
  · left
    have he : (y : G) * x * (y : G)⁻¹ = x := by
      calc (y : G) * x * (y : G)⁻¹ = (y : G) * x * (y : G)⁻¹ * x⁻¹ * x := by group
        _ = x := by rw [h, one_mul]
    rw [he, sub_self]
  · right
    have he : (y : G) * x * (y : G)⁻¹ = g * S.z * g⁻¹ * x := by
      calc (y : G) * x * (y : G)⁻¹ = (y : G) * x * (y : G)⁻¹ * x⁻¹ * x := by group
        _ = g * S.z * g⁻¹ * x := by rw [h]; rfl
    rw [he, S.cl_mul H.conj_mem hxQ, add_sub_cancel_right]

theorem card_Lbar (C : Cons311 S g) (hw : S.width = 6) : Nat.card (S.Lbar g) = 32 := by
  rw [C.card_Lbar, hw]
  norm_num

theorem f0_tr {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : ∀ v, q0 (φ v) = S.q v) (v w : S.Qt) :
    f0 (φ v) (φ w) = QuadraticMap.polar S.q v w := by
  rw [← polar_q0, QuadraticMap.polar, QuadraticMap.polar, ← map_add, hφ, hφ, hφ]

theorem hyp_tr (H : Hyp4 S g) (C : Cons311 S g) (hw : S.width = 6) {φ : S.Qt ≃ₗ[ZMod 2] V12}
    (hφ : ∀ v, q0 (φ v) = S.q v) (hle : Ltr S g φ ≤ gammaU) :
    Hyp (φ (aT S g)) ((Dt S g).map (φ : S.Qt →ₗ[ZMod 2] V12)) (Ltr S g φ) where
  ne_zero := fun h0 => aT_ne_zero H (φ.injective (h0.trans (map_zero φ).symm))
  q_eq := by rw [hφ, q_aT H]
  sing := by
    rintro _ ⟨d, hd, rfl⟩
    change q0 (φ d) = 0
    rw [hφ, Dt_sing H C d hd]
  finrank_eq := by rw [LinearEquiv.finrank_map_eq, finrank_Dt H C, hw]
  mem := ⟨aT S g, at_mem_Dt H, rfl⟩
  le := hle
  card := by
    rw [Ltr, LbarL, Subgroup.card_map_of_injective (trEquiv φ).injective,
      Subgroup.card_map_of_injective S.O.subtype_injective, card_Lbar C hw]
  fix := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := mem_Ltr.1 hl
    rw [trEquiv_apply_φ, Lbar_fix H hs]
  perp := by
    intro l hl x hx
    obtain ⟨s, hs, rfl⟩ := mem_Ltr.1 hl
    obtain ⟨v, rfl⟩ := φ.surjective x
    rw [f0_tr hφ] at hx
    refine ⟨(s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v, Lbar_perp H C hs hx, ?_⟩
    change φ ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) = _
    rw [map_sub, trEquiv_apply_φ]
  comm := by
    intro l hl d hd
    obtain ⟨s, hs, rfl⟩ := mem_Ltr.1 hl
    obtain ⟨d, hd, rfl⟩ := hd
    change trEquiv φ _ (φ d) - φ d = 0 ∨ trEquiv φ _ (φ d) - φ d = φ (aT S g)
    rw [trEquiv_apply_φ, ← map_sub]
    rcases Lbar_comm H hs hd with h | h
    · left
      rw [h, map_zero]
    · right
      rw [h]
  faithful := by
    intro l hl hfix
    obtain ⟨s, hs, rfl⟩ := mem_Ltr.1 hl
    have hs1 : s = 1 := C.faithful s hs fun v hv => by
      have := hfix (φ v) ⟨v, hv, rfl⟩
      rw [trEquiv_apply_φ] at this
      exact φ.injective this
    rw [hs1]
    exact map_one (trEquiv φ)

theorem mem_gammaU_of_conj {x : V12 ≃ₗ[ZMod 2] V12} (hq : ∀ v, q0 (x v) = q0 v)
    (h : x * thetaU * x⁻¹ = thetaU ∨ x * thetaU * x⁻¹ = thetaU⁻¹) : x ∈ gammaU := by
  refine ⟨hq, ?_⟩
  rcases h with h | h
  · left
    intro v
    have h' : x * thetaU = thetaU * x := by
      calc x * thetaU = x * thetaU * x⁻¹ * x := by group
        _ = thetaU * x := by rw [h]
    have := LinearEquiv.congr_fun h' v
    simpa only [LinearEquiv.mul_apply, thetaU_apply] using this
  · right
    intro v
    have h' : x * thetaU = thetaU⁻¹ * x := by
      calc x * thetaU = x * thetaU * x⁻¹ * x := by group
        _ = thetaU⁻¹ * x := by rw [h]
    have := LinearEquiv.congr_fun h' v
    simp only [LinearEquiv.mul_apply, thetaU_apply] at this
    rw [this, thetaU_inv_apply]

theorem conj_thetaU_tr {φ : S.Qt ≃ₗ[ZMod 2] V12} {θ : S.O} (hθ : ThetaCompat φ θ) {s : S.O}
    (hs : s * θ * s⁻¹ = θ ∨ s * θ * s⁻¹ = θ⁻¹) :
    trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) * thetaU * (trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt))⁻¹ =
        thetaU ∨
      trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) * thetaU * (trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt))⁻¹ =
        thetaU⁻¹ := by
  set X := trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
  set T := trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hXT : X * T * X⁻¹ = T ∨ X * T * X⁻¹ = T⁻¹ := by
    rcases hs with h | h
    · left
      have := congrArg (fun y : S.O => trEquiv φ (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) h
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using this
    · right
      have := congrArg (fun y : S.O => trEquiv φ (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) h
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using this
  rcases tr_theta hθ with hT | hT
  · have hT' : T = thetaU := hT
    rwa [hT'] at hXT
  · have hT' : T = thetaU⁻¹ := hT
    rw [hT', inv_inv] at hXT
    rcases hXT with h | h
    · left
      have := congrArg (·⁻¹) h
      simpa [mul_assoc] using this
    · right
      have := congrArg (·⁻¹) h
      simpa [mul_assoc] using this

theorem Ltr_le_gammaU {φ : S.Qt ≃ₗ[ZMod 2] V12} (hq : ∀ v, q0 (φ v) = S.q v) {θ : S.O}
    (hθ : ThetaCompat φ θ) (hLθ : ∀ s ∈ S.Lbar g, s * θ * s⁻¹ = θ ∨ s * θ * s⁻¹ = θ⁻¹) :
    Ltr S g φ ≤ gammaU := by
  intro l hl
  obtain ⟨s, hs, rfl⟩ := mem_Ltr.1 hl
  refine mem_gammaU_of_conj (fun v => ?_) (conj_thetaU_tr hθ (hLθ s hs))
  rw [trEquiv_apply, hq, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 s.2, ← hq,
    LinearEquiv.apply_symm_apply]

structure NormTr (S : Setting G) (g : G) (θ : S.O) (i : ℕ) (φ : S.Qt ≃ₗ[ZMod 2] V12) : Prop where
  isom : ∀ v, q0 (φ v) = S.q v
  theta : ThetaCompat φ θ
  base : φ (aT S g) = vecOf a0
  dmap : (Dt S g).map (φ : S.Qt →ₗ[ZMod 2] V12) = spanOf d0
  frame : ∀ l, l ∈ Ltr S g φ ↔ RowsSet (compOf i) l

theorem trEquiv_trans (φ : S.Qt ≃ₗ[ZMod 2] V12) (h : V12 ≃ₗ[ZMod 2] V12)
    (m : S.Qt ≃ₗ[ZMod 2] S.Qt) : trEquiv (φ.trans h) m = h * trEquiv φ m * h⁻¹ :=
  LinearEquiv.ext fun v => rfl

theorem Ltr_trans (φ : S.Qt ≃ₗ[ZMod 2] V12) (h : V12 ≃ₗ[ZMod 2] V12) :
    Ltr S g (φ.trans h) = (Ltr S g φ).map (MulAut.conj h).toMonoidHom := by
  ext l
  rw [mem_Ltr, mem_map_conj]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨_, mem_Ltr.2 ⟨s, hs, rfl⟩, (trEquiv_trans φ h _).symm⟩
  · rintro ⟨_, hl, rfl⟩
    obtain ⟨s, hs, rfl⟩ := mem_Ltr.1 hl
    exact ⟨s, hs, trEquiv_trans φ h _⟩

theorem exists_normTr
    (H : Hyp4 S g) (C : Cons311 S g) (hw : S.width = 6)
    {θ : S.O} (h3 : θ ^ 3 = 1) (hfix : ∀ v, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0)
    (hLθ : ∀ s ∈ S.Lbar g, s * θ * s⁻¹ = θ ∨ s * θ * s⁻¹ = θ⁻¹) :
    ∃ i, (i = 0 ∨ i = 1) ∧ ∃ φ, NormTr S g θ i φ := by
  obtain ⟨φ₀, hq, hθ⟩ := exists_isometry_theta0_of_setting S hw h3 hfix
  have hθ₀ : ThetaCompat φ₀ θ := Or.inl hθ
  obtain ⟨h, hh, ha, hD, i, hi, hL⟩ :=
    stepA_class (hyp_tr H C hw hq (Ltr_le_gammaU hq hθ₀ hLθ))
  refine ⟨i, hi, φ₀.trans h, ⟨fun v => ?_, ?_, ha, ?_, fun l => ?_⟩⟩
  · rw [LinearEquiv.trans_apply, hh.1, hq]
  · rcases hh.2 with hu | hu
    · left
      intro v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hθ, hu]
    · right
      intro v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hθ, hu]
  · rw [LinearEquiv.coe_trans, Submodule.map_comp, hD]
  · rw [Ltr_trans, hL]

end CFSG.GF2Type.Smith1979.GammaU.Dict
