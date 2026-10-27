module

public import CFSG.LargeExtraspecial.S12Fifteen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

universe u

theorem s12_mul_mem_of_relIndex_two {Y : Type*} [Group Y] {H K : Subgroup Y}
    (h : H.relIndex K = 2) {a b : Y} (ha : a ∈ K) (hb : b ∈ K) (haH : a ∉ H) (hbH : b ∉ H) :
    a * b ∈ H := by
  have h2 : (H.subgroupOf K).index = 2 := h
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr
    ⟨fun h' => absurd (mem_subgroupOf.mp h') haH, fun h' => absurd (mem_subgroupOf.mp h') hbH⟩
  exact mem_subgroupOf.mp this

namespace Setting

variable {G : Type u} [Group G] [Finite G] {S : Setting G}

theorem orbit_surj_of_relIndex (H : Subgroup S.O) {v : S.Qt} (hv : v ≠ 0)
    {W : Submodule (ZMod 2) S.Qt} (hW : ∀ h ∈ H, (h : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W)
    (hcard : (S.fixVec12 v).relIndex H + 1 = 2 ^ finrank (ZMod 2) W) :
    ∀ w ∈ W, w ≠ 0 → ∃ h ∈ H, (h : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w := by
  classical
  have : Finite S.Qt := Module.finite_of_finite (ZMod 2)
  set K := (S.fixVec12 v).subgroupOf H
  have hK : ∀ h₁ h₂ : H, ((h₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((h₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ↔ h₁⁻¹ * h₂ ∈ K := fun h₁ h₂ => s12_apply_eq_iff
  let φ : H ⧸ K → {w : W // w ≠ 0} := Quotient.lift
    (fun h : H => ⟨⟨((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, hW h h.2⟩, fun e =>
      hv (((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp (congrArg Subtype.val e))⟩)
    (fun h₁ h₂ hh => Subtype.ext (Subtype.ext
      ((hK h₁ h₂).mpr (QuotientGroup.leftRel_apply.mp hh))))
  have hφ : Function.Injective φ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H h₁ => ?_
    induction y using QuotientGroup.induction_on with | H h₂ => ?_
    exact QuotientGroup.eq.mpr ((hK h₁ h₂).mp
      (congrArg (fun w : {w : W // w ≠ 0} => ((w : W) : S.Qt)) hxy))
  have h2 : Nat.card {w : W // w ≠ 0} + 1 = Nat.card W := by
    have : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have : 0 < Fintype.card W := Fintype.card_pos
    omega
  have h3 : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hle : Nat.card {w : W // w ≠ 0} ≤ Nat.card (H ⧸ K) := by
    change _ ≤ (S.fixVec12 v).relIndex H
    omega
  have hbij := hφ.bijective_of_nat_card_le hle
  intro w hw hw0
  obtain ⟨c, hc⟩ := hbij.2 ⟨⟨w, hw⟩, fun e => hw0 (congrArg Subtype.val e)⟩
  induction c using QuotientGroup.induction_on with | H h => ?_
  exact ⟨h, h.2, congrArg (fun w : {w : W // w ≠ 0} => ((w : W) : S.Qt)) hc⟩

theorem q_spanOrbitX12_eq_zero {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hiso : ∀ v ∈ S.spanOrbitX12 g, ∀ w ∈ S.spanOrbitX12 g, polar S.q v w = 0) :
    ∀ v ∈ S.spanOrbitX12 g, S.q v = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (x : S.O).2]
    exact (S.q_cl_eq_zero_iff haQ).mpr (S.s12_conj_z_sq g)
  | zero => exact map_zero _
  | add x y hx hy ihx ihy =>
    have h1 : polar S.q x y = S.q (x + y) - S.q x - S.q y := rfl
    rw [hiso x hx y hy, ihx, ihy, sub_zero, sub_zero] at h1
    exact h1.symm
  | smul c x _ ih => rw [QuadraticMap.map_smul, ih, smul_zero]

theorem apply_mem_spanOrbitX12 {g : G} {x : S.O} (hx : x ∈ S.Xbar12 g) {v : S.Qt}
    (hv : v ∈ S.spanOrbitX12 g) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.spanOrbitX12 g := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, rfl⟩ := hw
    have := orbit_mem_spanOrbitX12 (S := S) ((S.Xbar12 g).mul_mem hx y.2)
    rwa [Subgroup.coe_mul, LinearEquiv.mul_apply] at this
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem relIndex_Xbar12_eq_two {g : G} {t : S.O} (hC1 : S.S12Case1 g t)
    (hXM : S.Xbar12 g ≠ S.Mbar) : (S.Xbar12 g).relIndex S.Mbar = 2 := by
  have h1 := hC1.index
  have h2 : (S.Xbar12 g).relIndex S.Mbar ≠ 1 := fun h =>
    hXM (le_antisymm Xbar12_le_Mbar (relIndex_eq_one.mp h))
  have h3 : (S.Xbar12 g).relIndex S.Mbar ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem case1_gammaL_structure {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (hC1 : S.S12Case1 g t) {m : ℕ}
    (hL : Nat.card (S.Lbar g) = 2 ^ (m - 1))
    (hidx : (normalizer (S.Lbar g : Set S.O)).relIndex (S.Xbar12 g) = 2 ^ m - 1)
    (hC : ∀ x ∈ S.Xbar12 g,
      (S.Lbar g).map (MulAut.conj x).toMonoidHom ⊓ normalizer (S.Lbar g : Set S.O) ≠ ⊥)
    (hXM : S.Xbar12 g ≠ S.Mbar) (hirr : ¬ S.IsReducible12) :
    (S.Xbar12 g).relIndex S.Mbar = 2 ∧ finrank (ZMod 2) (S.spanOrbitX12 g) = S.width ∧
      (∀ v ∈ S.spanOrbitX12 g, S.q v = 0) ∧
      (∀ w ∈ S.spanOrbitX12 g, w ≠ 0 →
        ∃ x ∈ S.Xbar12 g, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = w) ∧
      ∀ σ ∈ S.Mbar, σ ∉ S.Xbar12 g →
        S.spanOrbitX12 g ⊓
            (S.spanOrbitX12 g).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = ⊥ ∧
          S.spanOrbitX12 g ⊔
            (S.spanOrbitX12 g).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = ⊤ := by
  set A := S.spanOrbitX12 g with hA
  set a := S.cl (g * S.z * g⁻¹) with ha
  obtain ⟨hnm, hdim⟩ := case1_finrank haQ hne hn hL hidx hC
  replace hdim : finrank (ZMod 2) A = m := hdim
  have hiso := isotropic_span_orbit_Xbar12 haQ hne hn hC
  have ha0 : a ≠ 0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hind := relIndex_Xbar12_eq_two hC1 hXM
  have hsub : (normalizer (S.Lbar g : Set S.O)).subgroupOf (S.Xbar12 g) =
      (S.fixVec12 a).subgroupOf (S.Xbar12 g) := by
    ext x
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_Lbar_iff_fix haQ hne hn (Xbar12_le_Mbar x.2)
  have hfix : (S.fixVec12 a).relIndex (S.Xbar12 g) = 2 ^ m - 1 := by
    rw [Subgroup.relIndex, ← hsub, ← Subgroup.relIndex, hidx]
  have htrans : ∀ w ∈ A, w ≠ 0 → ∃ x ∈ S.Xbar12 g, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = w :=
    orbit_surj_of_relIndex (S.Xbar12 g) ha0 (fun x hx => orbit_mem_spanOrbitX12 hx)
      (by rw [hfix, hdim, ← hnm]; have := Nat.one_le_two_pow (n := S.width); omega)
  refine ⟨hind, hdim.trans hnm.symm, q_spanOrbitX12_eq_zero haQ hiso, htrans, fun σ hσ hσX => ?_⟩
  set B := A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) with hB
  have hBdim : finrank (ZMod 2) B = finrank (ZMod 2) A := LinearEquiv.finrank_map_eq _ _
  have hinf : A ⊓ B = ⊥ := by
    by_contra hU
    obtain ⟨u, ⟨huA, huB⟩, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have hXB : ∀ x ∈ S.Xbar12 g, ∀ v ∈ B, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ B := by
      intro x hx v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      have hx' : σ⁻¹ * x * σ⁻¹⁻¹ ∈ S.Xbar12 g :=
        (mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12 (S.Mbar.inv_mem hσ)) x).mp hx
      refine Submodule.mem_map.mpr ⟨((σ⁻¹ * x * σ⁻¹⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w,
        apply_mem_spanOrbitX12 hx' hw, ?_⟩
      change ((σ * (σ⁻¹ * x * σ⁻¹⁻¹) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = _
      rw [show σ * (σ⁻¹ * x * σ⁻¹⁻¹) = x * σ by group, Subgroup.coe_mul, LinearEquiv.mul_apply]
      rfl
    obtain ⟨x, hx, hxa⟩ := htrans u huA hu0
    have haAB : a ∈ A ⊓ B := by
      have h1 := apply_mem_spanOrbitX12 ((S.Xbar12 g).inv_mem hx) huA
      have h2 := hXB _ ((S.Xbar12 g).inv_mem hx) u huB
      rw [← hxa, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel] at h1 h2
      exact ⟨h1, h2⟩
    have hAB : A ≤ B := by
      rw [hA, spanOrbitX12, Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact hXB _ y.2 _ haAB.2
    have hBA : B = A := (Submodule.eq_of_le_of_finrank_eq hAB hBdim.symm).symm
    apply hirr
    refine ⟨A, fun h => ?_, fun h => ?_, fun m' v hv => ?_⟩
    · have h1 : ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a ∈ A :=
        orbit_mem_spanOrbitX12 (S.Xbar12 g).one_mem
      rw [h, Submodule.mem_bot] at h1
      exact ha0 h1
    · have h1 := S.finrank_Qt_eq_two_mul_width
      rw [h, finrank_top] at hdim
      omega
    · by_cases hm' : S.ρ m' ∈ S.Xbar12 g
      · exact apply_mem_spanOrbitX12 hm' hv
      · have hmσ : S.ρ m' * σ ∈ S.Xbar12 g :=
          s12_mul_mem_of_relIndex_two hind ⟨m', rfl⟩ hσ hm' hσX
        have hvB : v ∈ B := hBA ▸ hv
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hvB
        have := apply_mem_spanOrbitX12 hmσ hw
        rwa [Subgroup.coe_mul, LinearEquiv.mul_apply] at this
  refine ⟨hinf, ?_⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hinf, finrank_bot, add_zero, hBdim, hdim, ← hnm] at h
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [h, S.finrank_Qt_eq_two_mul_width]
  ring

end Setting

end CFSG.LargeExtraspecial
