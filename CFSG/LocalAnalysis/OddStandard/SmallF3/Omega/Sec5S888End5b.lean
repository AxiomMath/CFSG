module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888YGold
public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldY

public section

open CFSG.Open CFSG.Goldschmidt Subgroup CFSG.GH74.GLS.Th2.P412

open scoped IsMulCommutative

namespace CFSG.OddStandard.SmallF3.Omega

private lemma orbit_rearr {G : Type*} [CommGroup G] (τ : G →* G) (a b a₁ b₁ : G)
    (h : (a⁻¹ * τ a) * ((τ b)⁻¹ * τ (τ b)) = (a₁⁻¹ * τ a₁) * ((τ b₁)⁻¹ * τ (τ b₁))) :
    (a * a₁⁻¹)⁻¹ * τ ((a * a₁⁻¹) * (b * b₁⁻¹)⁻¹) * τ (τ (b * b₁⁻¹)) = 1 := by
  have key : (a * a₁⁻¹)⁻¹ * τ ((a * a₁⁻¹) * (b * b₁⁻¹)⁻¹) * τ (τ (b * b₁⁻¹))
      = ((a⁻¹ * τ a) * ((τ b)⁻¹ * τ (τ b))) *
        (((a₁⁻¹ * τ a₁) * ((τ b₁)⁻¹ * τ (τ b₁))))⁻¹ := by
    simp only [map_mul, map_inv, map_one, mul_inv_rev, inv_inv]
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [key, h, mul_inv_cancel]

theorem card_inf_le_two_of_orbit {Y : Type} [Group Y] {D W : Subgroup Y} {τ : Y ≃* Y}
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hW : W ≤ D) (hWc : Nat.card W = 4)
    (hcube : ∀ y, τ (τ (τ y)) = y) (hτ : ∀ d ∈ D, τ d ∈ D) (hcom : ∀ d ∈ D, d⁻¹ * τ d ∈ W)
    {J : Subgroup Y}
    (hind : ∀ x ∈ J, ∀ y ∈ J.map τ.toMonoidHom, ∀ w ∈ (J.map τ.toMonoidHom).map τ.toMonoidHom,
      x * y * w = 1 → x = 1 ∧ y = 1 ∧ w = 1) :
    Nat.card ↥(D ⊓ J) ≤ 2 := by
  classical
  haveI hDcomm' : IsMulCommutative (D : Subgroup Y) :=
    ⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩
  let τD : ↥D →* ↥D :=
    { toFun := fun x => ⟨τ x, hτ x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  let φ : (↥(D ⊓ J) × ↥(D ⊓ J)) → ↥W := fun p =>
    ⟨(p.1 : Y)⁻¹ * τ (p.1 : Y) * ((τ (p.2 : Y))⁻¹ * τ (τ (p.2 : Y))), by
      have h1 : (p.1 : Y) ∈ D := p.1.2.1
      have h2 : (p.2 : Y) ∈ D := p.2.2.1
      exact mul_mem (hcom _ h1) (hcom _ (hτ _ h2))⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a₁, b₁⟩ hab
    have habY : (a : Y)⁻¹ * τ (a : Y) * ((τ (b : Y))⁻¹ * τ (τ (b : Y)))
        = (a₁ : Y)⁻¹ * τ (a₁ : Y) * ((τ (b₁ : Y))⁻¹ * τ (τ (b₁ : Y))) := by
      have h := congrArg Subtype.val hab
      simpa only [φ] using h
    have haD : (a : Y) ∈ D := a.2.1
    have hbD : (b : Y) ∈ D := b.2.1
    have ha₁D : (a₁ : Y) ∈ D := a₁.2.1
    have hb₁D : (b₁ : Y) ∈ D := b₁.2.1
    have hD : (⟨(a : Y), haD⟩⁻¹ * τD ⟨(a : Y), haD⟩) *
          ((τD ⟨(b : Y), hbD⟩)⁻¹ * τD (τD ⟨(b : Y), hbD⟩))
        = (⟨(a₁ : Y), ha₁D⟩⁻¹ * τD ⟨(a₁ : Y), ha₁D⟩) *
          ((τD ⟨(b₁ : Y), hb₁D⟩)⁻¹ * τD (τD ⟨(b₁ : Y), hb₁D⟩)) := by
      apply Subtype.ext
      exact habY
    have hprod : ((a : Y) * (a₁ : Y)⁻¹)⁻¹ *
          τ (((a : Y) * (a₁ : Y)⁻¹) * ((b : Y) * (b₁ : Y)⁻¹)⁻¹) *
          τ (τ ((b : Y) * (b₁ : Y)⁻¹)) = 1 := by
      have hd := orbit_rearr τD ⟨(a : Y), haD⟩ ⟨(b : Y), hbD⟩
        ⟨(a₁ : Y), ha₁D⟩ ⟨(b₁ : Y), hb₁D⟩ hD
      exact congrArg Subtype.val hd
    have hX : ((a : Y) * (a₁ : Y)⁻¹)⁻¹ ∈ J :=
      inv_mem (mul_mem a.2.2 (inv_mem a₁.2.2))
    have hY' : τ (((a : Y) * (a₁ : Y)⁻¹) * ((b : Y) * (b₁ : Y)⁻¹)⁻¹)
        ∈ J.map τ.toMonoidHom :=
      Subgroup.mem_map_of_mem τ.toMonoidHom
        (mul_mem (mul_mem a.2.2 (inv_mem a₁.2.2))
          (inv_mem (mul_mem b.2.2 (inv_mem b₁.2.2))))
    have hZ : τ (τ ((b : Y) * (b₁ : Y)⁻¹)) ∈ (J.map τ.toMonoidHom).map τ.toMonoidHom :=
      Subgroup.mem_map_of_mem τ.toMonoidHom
        (Subgroup.mem_map_of_mem τ.toMonoidHom (mul_mem b.2.2 (inv_mem b₁.2.2)))
    obtain ⟨hX1, -, hZ1⟩ := hind _ hX _ hY' _ hZ hprod
    have ha : (a : Y) = a₁ := mul_inv_eq_one.mp (inv_eq_one.mp hX1)
    have hb : (b : Y) = b₁ := by
      have h1 : τ (τ ((b : Y) * (b₁ : Y)⁻¹)) = τ (τ (1 : Y)) := by rw [hZ1]; simp
      exact mul_inv_eq_one.mp (τ.injective (τ.injective h1))
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hWfin : Finite ↥W :=
    Nat.finite_of_card_ne_zero (by rw [hWc]; norm_num)
  have hcard := Nat.card_le_card_of_injective φ hφinj
  rw [Nat.card_prod, hWc] at hcard
  nlinarith

theorem four_le_card_inf_component (hN11b : S_N11b) {Y : Type} [Group Y] [Finite Y]
    (hY : IsGoldSemisimple Y) (D : Sylow 2 Y)
    (hDcomm : ∀ a ∈ (D : Subgroup Y), ∀ b ∈ (D : Subgroup Y), a * b = b * a)
    {J : Subgroup Y} (hJ : IsComponentOf J ⊤) : 4 ≤ Nat.card ↥((D : Subgroup Y) ⊓ J) := by
  have hZY := GoldY.center_eq_bot hY.o2 hY.odd hY.layer
  have hZJ := GoldY.component_center_eq_bot hZY hY.layer hJ
  haveI hJnorm : J.Normal := GoldY.component_normal hY.layer hJ
  obtain ⟨TQ, -, hcardΩ, hcomm⟩ := GoldY.exists_sylow_quotient J hZJ D
  have htype := hY.comps J hJ
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  have hDcomm' : IsMulCommutative (D : Subgroup Y) :=
    ⟨⟨fun x y => Subtype.ext (hDcomm x x.2 y y.2)⟩⟩
  have hΩcomm : IsMulCommutative (Omega1 (D : Subgroup Y)) :=
    GoldY.isMulCommutative_of_le (CFSG.Goldschmidt.GoldType.omega1_le (D : Subgroup Y)) hDcomm'
  have h4 : 4 ≤ Nat.card (Omega1 (TQ : Subgroup (↥J ⧸ Subgroup.center ↥J))) :=
    (hN11b _ htype TQ (hcomm hΩcomm)).1
  rw [hcardΩ] at h4
  exact le_trans h4 (Subgroup.card_le_of_le (CFSG.Goldschmidt.GoldType.omega1_le _))

end CFSG.OddStandard.SmallF3.Omega
