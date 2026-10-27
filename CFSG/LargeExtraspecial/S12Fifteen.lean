module

public import CFSG.LargeExtraspecial.S12Elim
public import CFSG.LargeExtraspecial.S12Fourteen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

structure S12Case1 (g : G) (t : S.O) : Prop where
  normal : ∀ x ∈ S.Xbar12 g, x * t * x⁻¹ = t → x ∈ normalizer (S.Lbar g : Set S.O)
  index : (S.Xbar12 g).relIndex S.Mbar ≤ 2
  model : ∃ m : ℕ, 3 ≤ m ∧
    Nonempty (S.Xbar12 g ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) ∧
    ((Nat.card (S.Lbar g) = 2 ^ (m - 1) ∧
        (normalizer (S.Lbar g : Set S.O)).relIndex (S.Xbar12 g) = 2 ^ m - 1 ∧
        ∀ x ∈ S.Xbar12 g,
          (S.Lbar g).map (MulAut.conj x).toMonoidHom ⊓ normalizer (S.Lbar g : Set S.O) ≠ ⊥) ∨
      (m = 4 ∧ Nat.card (S.Lbar g) = 8 ∧ ∀ d ∈ S.Ebar12 g, d ∈ S.Lbar g → d = t))

@[expose] noncomputable def spanOrbitX12 (g : G) : Submodule (ZMod 2) S.Qt :=
  Submodule.span (ZMod 2)
    (Set.range fun x : S.Xbar12 g => ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))

variable {S}

theorem two_mul_finrank_le_of_isotropic {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ v ∈ W, ∀ w ∈ W, polar S.q v w = 0) :
    2 * finrank (ZMod 2) W ≤ finrank (ZMod 2) S.Qt := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W := fun v hv =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun w hw => by
      change S.q.polarBilin w v = 0
      exact hW w hw v hv
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate] at h1
  have h2 := Submodule.finrank_le W
  omega

theorem isotropic_span_of_pairwise {T : Set S.Qt} (hT : ∀ v ∈ T, ∀ w ∈ T, polar S.q v w = 0) :
    ∀ v ∈ Submodule.span (ZMod 2) T, ∀ w ∈ Submodule.span (ZMod 2) T, polar S.q v w = 0 := by
  have h1 : ∀ s ∈ T, Submodule.span (ZMod 2) T ≤ LinearMap.ker (S.q.polarBilin s) := by
    intro s hs
    rw [Submodule.span_le]
    intro w hw
    exact hT s hs w hw
  intro v hv w hw
  have h2 : Submodule.span (ZMod 2) T ≤ LinearMap.ker (S.q.polarBilin v) := by
    rw [Submodule.span_le]
    intro s hs
    change polar S.q v s = 0
    rw [polar_comm]
    exact h1 s hs hv
  exact h2 hw

theorem relIndex_fixVec12_le (H : Subgroup S.O) {v : S.Qt} (hv : v ≠ 0)
    {W : Submodule (ZMod 2) S.Qt} (hW : ∀ h ∈ H, (h : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) :
    (S.fixVec12 v).relIndex H + 1 ≤ 2 ^ finrank (ZMod 2) W := by
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
  have h1 : Nat.card (H ⧸ K) ≤ Nat.card {w : W // w ≠ 0} :=
    Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card {w : W // w ≠ 0} + 1 = Nat.card W := by
    have : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have : 0 < Fintype.card W := Fintype.card_pos
    omega
  have h3 : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  show Nat.card (H ⧸ K) + 1 ≤ _
  omega

theorem polar_orbit_Xbar12_eq_zero {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width)
    (hC : ∀ x ∈ S.Xbar12 g,
      (S.Lbar g).map (MulAut.conj x).toMonoidHom ⊓ normalizer (S.Lbar g : Set S.O) ≠ ⊥)
    {x : S.O} (hx : x ∈ S.Xbar12 g) :
    polar S.q (S.cl (g * S.z * g⁻¹)) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0 := by
  obtain ⟨h, rfl⟩ := Xbar12_le_Mbar hx
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hC _ hx)
  rw [← S.s12_Lbar_mul h g] at hy
  have hc := S.s12_commute_of_mem_Lbar_normalizer haQ hne hn h hy.1 hy.2
    (fun e => hy1 (Subtype.ext e))
  obtain ⟨hbQ, -⟩ := S.s12_conj_mem haQ hne h
  rw [rho_cl_conj haQ h]
  exact (S.polar_cl_eq_zero_iff haQ hbQ).mpr hc

theorem isotropic_span_orbit_Xbar12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width)
    (hC : ∀ x ∈ S.Xbar12 g,
      (S.Lbar g).map (MulAut.conj x).toMonoidHom ⊓ normalizer (S.Lbar g : Set S.O) ≠ ⊥) :
    ∀ v ∈ S.spanOrbitX12 g, ∀ w ∈ S.spanOrbitX12 g, polar S.q v w = 0 := by
  refine isotropic_span_of_pairwise ?_
  rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩
  set a := S.cl (g * S.z * g⁻¹)
  set y : S.O := ((x₁⁻¹ * x₂ : S.Xbar12 g) : S.O) with hy
  have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (x₁ : S.O).2 a
    ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) a)
  have e : ((x₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) a) =
      ((x₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by
    have e1 : (x₁ : S.O) * y = (x₂ : S.O) := by
      rw [hy, ← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, e1]
  change polar S.q (((x₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a)
    (((x₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _) = _ at hiso
  rw [e] at hiso
  rw [hiso]
  exact polar_orbit_Xbar12_eq_zero haQ hne hn hC (x₁⁻¹ * x₂).2

theorem orbit_mem_spanOrbitX12 {g : G} {x : S.O} (hx : x ∈ S.Xbar12 g) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈ S.spanOrbitX12 g :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem case1_finrank {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {m : ℕ}
    (hL : Nat.card (S.Lbar g) = 2 ^ (m - 1))
    (hidx : (normalizer (S.Lbar g : Set S.O)).relIndex (S.Xbar12 g) = 2 ^ m - 1)
    (hC : ∀ x ∈ S.Xbar12 g,
      (S.Lbar g).map (MulAut.conj x).toMonoidHom ⊓ normalizer (S.Lbar g : Set S.O) ≠ ⊥) :
    S.width = m ∧ finrank (ZMod 2) (S.spanOrbitX12 g) = m := by
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hsub : (normalizer (S.Lbar g : Set S.O)).subgroupOf (S.Xbar12 g) =
      (S.fixVec12 (S.cl (g * S.z * g⁻¹))).subgroupOf (S.Xbar12 g) := by
    ext x
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_Lbar_iff_fix haQ hne hn (Xbar12_le_Mbar x.2)
  have h1 := relIndex_fixVec12_le (S.Xbar12 g) ha0 (W := S.spanOrbitX12 g)
    fun x hx => orbit_mem_spanOrbitX12 hx
  rw [Subgroup.relIndex, ← hsub, ← Subgroup.relIndex, hidx] at h1
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : m ≤ finrank (ZMod 2) (S.spanOrbitX12 g) :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by omega)
  have h3 := two_mul_finrank_le_of_isotropic (isotropic_span_orbit_Xbar12 haQ hne hn hC)
  rw [S.finrank_Qt_eq_two_mul_width] at h3
  have h4 := S.card_Lbar_ge haQ hne
  rw [hL] at h4
  have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  omega

theorem isReducible12_of_case1 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {m : ℕ}
    (hL : Nat.card (S.Lbar g) = 2 ^ (m - 1))
    (hidx : (normalizer (S.Lbar g : Set S.O)).relIndex (S.Xbar12 g) = 2 ^ m - 1)
    (hC : ∀ x ∈ S.Xbar12 g,
      (S.Lbar g).map (MulAut.conj x).toMonoidHom ⊓ normalizer (S.Lbar g : Set S.O) ≠ ⊥)
    (hXM : S.Xbar12 g = S.Mbar) : S.IsReducible12 := by
  obtain ⟨hnm, hdim⟩ := case1_finrank haQ hne hn hL hidx hC
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  refine ⟨S.spanOrbitX12 g, fun h => ?_, fun h => ?_, fun m' v hv => ?_⟩
  · have := orbit_mem_spanOrbitX12 (S := S) (S.Xbar12 g).one_mem
    rw [h] at this
    exact ha0 ((Submodule.mem_bot _).mp this)
  · have h1 := S.finrank_Qt_eq_two_mul_width
    rw [h, finrank_top] at hdim
    omega
  · induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, rfl⟩ := hw
      have hmx : S.ρ m' * (x : S.O) ∈ S.Xbar12 g :=
        (S.Xbar12 g).mul_mem (hXM ▸ ⟨m', rfl⟩) x.2
      have := orbit_mem_spanOrbitX12 (S := S) hmx
      rwa [Subgroup.coe_mul, LinearEquiv.mul_apply] at this
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end Setting

end CFSG.LargeExtraspecial
