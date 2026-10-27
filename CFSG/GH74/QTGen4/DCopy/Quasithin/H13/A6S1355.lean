module

public import CFSG.Quasithin.H13.A6S1355
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem centralizer_V3_le_F4 (h13315 : Stmt13_3_15_F4) :
    Subgroup.centralizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  classical
  let X : Subgroup G := if IsHatA6 L then oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ else L₁Of L S.V2
  have hX₁ : IsHatA6 L → X = oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ := fun h => by simp [X, h]
  have hX₂ : ¬ IsHatA6 L → X = L₁Of L S.V2 := fun h => by simp [X, h]
  obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := h13315 G T L V S.V2 X _ S.h13 S.irr S.zv S.isV2
    S.not_iso_a5 hX₁ hX₂ rfl
  exact (h9 S.V3 S.V2_le_V3 S.V3_le_V S.T_le_normalizer_V3 S.card_V3).1

theorem G1_inf_G3_le_F4 (h13315 : Stmt13_3_15_F4) :
    S.G1 ⊓ Subgroup.normalizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rintro g ⟨hg1, hg3⟩
  have hgz : g * S.z * g⁻¹ = S.z := by
    have h : g * S.z = S.z * g := Subgroup.mem_centralizer_singleton_iff.mp hg1
    rw [h, mul_inv_cancel_right]
  have hconj : ∀ v : G, v ∈ S.V3 → g * v * g⁻¹ ∈ S.V3 := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hg3 v).mp hv
  have hpre : ∀ x : ↥W4, InW3 (x : P6) → ((S.frame.ψ.symm x : ↥V) : G) ∈ S.V3 := by
    intro x hx
    have e : S.frame.ψ ⟨((S.frame.ψ.symm x : ↥V) : G), (S.frame.ψ.symm x).2⟩ = x :=
      S.frame.ψ.apply_symm_apply x
    exact S.mem_pre.2 ⟨(S.frame.ψ.symm x).2, by rw [e]; exact hx⟩

  let β : ∀ x : ↥W4, InW3 (x : P6) → ↥W4 := fun x hx =>
    S.frame.ψ ⟨g * (S.frame.ψ.symm x : G) * g⁻¹, S.V3_le_V (hconj _ (hpre x hx))⟩
  have hβ3 : ∀ x hx, InW3 (β x hx : P6) := fun x hx => (S.mem_pre.1 (hconj _ (hpre x hx))).2
  have hβinj : ∀ x y hx hy, β x hx = β y hy → x = y := by
    intro x y hx hy h
    have h1 := congrArg Subtype.val (S.frame.ψ.injective h)
    simp only [mul_left_inj, mul_right_inj] at h1
    exact S.frame.ψ.symm.injective (Subtype.ext h1)
  have hβmul : ∀ x y hx hy hxy, β (x * y) hxy = β x hx * β y hy := by
    intro x y hx hy hxy
    simp only [β]
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    group
  have hβz : β ⟨e0123, e0123_mem_W4⟩ basis_facts.2.2.1 = ⟨e0123, e0123_mem_W4⟩ := by
    have h : (⟨g * (S.frame.ψ.symm ⟨e0123, e0123_mem_W4⟩ : G) * g⁻¹,
        S.V3_le_V (hconj _ (hpre _ basis_facts.2.2.1))⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
      Subtype.ext hgz
    exact (congrArg S.frame.ψ h).trans S.psi_z
  have hβ1 : β 1 (by decide) = 1 := by
    have h : (⟨g * (S.frame.ψ.symm 1 : G) * g⁻¹, S.V3_le_V (hconj _ (hpre 1 (by decide)))⟩ :
        ↥V) = 1 := Subtype.ext (by simp)
    exact (congrArg S.frame.ψ h).trans (map_one _)
  obtain ⟨b1, b2, b3, b12, n1, n2, n12, n1e, n2e, n12e⟩ := basis_facts
  set u1 : ↥W4 := ⟨dv 0 1, dv_mem 0 1⟩
  set u2 : ↥W4 := ⟨dv 0 2, dv_mem 0 2⟩
  set e3 : ↥W4 := ⟨e0123, e0123_mem_W4⟩

  have ha1 : (β u1 b1 : P6) ≠ 1 := fun h =>
    n1 (congrArg Subtype.val (hβinj u1 1 b1 (by decide) (by rw [hβ1]; exact Subtype.ext h)))
  have hb1 : (β u2 b2 : P6) ≠ 1 := fun h =>
    n2 (congrArg Subtype.val (hβinj u2 1 b2 (by decide) (by rw [hβ1]; exact Subtype.ext h)))
  have hab : (β u1 b1 : P6) ≠ β u2 b2 := fun h =>
    n12 (congrArg Subtype.val (hβinj u1 u2 b1 b2 (Subtype.ext h)))
  have hae : (β u1 b1 : P6) ≠ e0123 := fun h =>
    n1e (congrArg Subtype.val (hβinj u1 e3 b1 b3 (by rw [hβz]; exact Subtype.ext h)))
  have hbe : (β u2 b2 : P6) ≠ e0123 := fun h =>
    n2e (congrArg Subtype.val (hβinj u2 e3 b2 b3 (by rw [hβz]; exact Subtype.ext h)))
  have habe : (β u1 b1 : P6) * β u2 b2 ≠ e0123 := fun h =>
    n12e (congrArg Subtype.val (hβinj (u1 * u2) e3 b12 b3
      (by rw [hβz, hβmul u1 u2 b1 b2 b12]; exact Subtype.ext h)))
  obtain ⟨σ, hσ1, hσ2, hσz, hσs⟩ := stabWit _ _ ⟨⟨(β u1 b1).2, hβ3 u1 b1⟩,
    ⟨(β u2 b2).2, hβ3 u2 b2⟩, ha1, hb1, hab, hae, hbe, habe⟩
  obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσs)

  have hagree : ∀ x : ↥W4, ∀ hx : InW3 (x : P6), ((act4 σ x : ↥W4) : P6) = β x hx →
      g * (S.frame.ψ.symm x : G) * g⁻¹ = (l : G) * (S.frame.ψ.symm x : G) * (l : G)⁻¹ := by
    intro x hx h
    have h1 := S.psi_conj l (S.frame.ψ.symm x)
    rw [MulEquiv.apply_symm_apply, hl] at h1
    have h2 : S.frame.ψ ⟨(l : G) * (S.frame.ψ.symm x : G) * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp l.2 _).mp (S.frame.ψ.symm x).2⟩ = β x hx :=
      h1.trans (Subtype.ext h)
    exact (congrArg Subtype.val (S.frame.ψ.injective h2)).symm
  have hgen : ∀ x : ↥W4, x ∈ Subgroup.closure ({u1, u2, e3} : Set ↥W4) →
      g * (S.frame.ψ.symm x : G) * g⁻¹ = (l : G) * (S.frame.ψ.symm x : G) * (l : G)⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact hagree _ b1 hσ1
      · exact hagree _ b2 hσ2
      · exact hagree _ b3 (hσz.trans (congrArg Subtype.val hβz).symm)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul, Subgroup.coe_mul]
      have e1 : ∀ c a b : G, c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := fun c a b => by
        group
      rw [e1, e1, hx, hy]
    | inv x _ hx =>
      rw [map_inv, Subgroup.coe_inv]
      have e2 : ∀ c a : G, c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := fun c a => by group
      rw [e2, e2, hx]

  have hC : (l : G)⁻¹ * g ∈ Subgroup.centralizer (S.V3 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨hvV, hv3⟩ := S.mem_pre.1 hv
    have h := hgen _ (W3sub_le_closure hv3)
    rw [MulEquiv.symm_apply_apply] at h
    calc v * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * v * (l : G)⁻¹) * g := by group
      _ = (l : G)⁻¹ * (g * v * g⁻¹) * g := by rw [← h]
      _ = (l : G)⁻¹ * g * v := by group
  have := Subgroup.mul_mem _ l.2 (S.centralizer_V3_le_F4 h13315 hC)
  rwa [mul_inv_cancel_left] at this

end Setting4

end CFSG.Quasithin.H13.A6
