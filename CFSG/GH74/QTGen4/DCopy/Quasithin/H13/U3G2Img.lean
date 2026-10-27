module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15U
public import CFSG.Quasithin.H13.U3G2Mdl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G]

namespace HullSetting_F4
open CFSG.Quasithin.H13.U3.HullSetting_F4

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

noncomputable def imgL_F4
    (S : HullSetting_F4 G T L V z) (X : Subgroup G) : Subgroup (W6 ≃ₗ[ZMod 2] W6) :=
  ((X.subgroupOf (normalizer (V : Set G))).map S.rho_F4).map glLin.toMonoidHom

theorem mem_imgL_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} {g : W6 ≃ₗ[ZMod 2] W6} :
    g ∈ S.imgL_F4 X ↔ ∃ (x : G) (hx : x ∈ normalizer (V : Set G)), x ∈ X ∧
      glLin (S.rho_F4 ⟨x, hx⟩) = g := by
  simp only [imgL_F4, Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨k, ⟨⟨x, hxN⟩, hxX, rfl⟩, rfl⟩
    exact ⟨x, hxN, hxX, rfl⟩
  · rintro ⟨x, hxN, hxX, rfl⟩
    exact ⟨_, ⟨⟨x, hxN⟩, hxX, rfl⟩, rfl⟩

theorem glLin_rho_mem_imgL_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} {x : G} (hxX : x ∈ X)
    (hxN : x ∈ normalizer (V : Set G)) : glLin (S.rho_F4 ⟨x, hxN⟩) ∈ S.imgL_F4 X :=
  S.mem_imgL_F4.2 ⟨x, hxN, hxX, rfl⟩

theorem imgL_mono_F4
    (S : HullSetting_F4 G T L V z) {X Y : Subgroup G} (h : X ≤ Y) : S.imgL_F4 X ≤ S.imgL_F4 Y :=
  fun g hg => by
    obtain ⟨x, hxN, hxX, rfl⟩ := S.mem_imgL_F4.1 hg
    exact S.glLin_rho_mem_imgL_F4 (h hxX) hxN

theorem imgL_le_S0L_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} (hXT : X ≤ T) : S.imgL_F4 X ≤ S0L := fun g hg => by
  obtain ⟨x, hxN, hxX, rfl⟩ := S.mem_imgL_F4.1 hg
  exact ⟨_, S.rho_T_mem_F4 (hXT hxX), rfl⟩

theorem card_imgL_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G)) :
    Nat.card (S.imgL_F4 X) = (X ⊓ centralizer (V : Set G)).relIndex X := by
  let φ : X →* (W6 ≃ₗ[ZMod 2] W6) :=
    glLin.toMonoidHom.comp (S.rho_F4.comp (Subgroup.inclusion hXN))
  have hrange : φ.range = S.imgL_F4 X := by
    ext g
    rw [MonoidHom.mem_range, S.mem_imgL_F4]
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hXN hx, hx, rfl⟩
    · rintro ⟨x, hxN, hxX, rfl⟩
      exact ⟨⟨x, hxX⟩, rfl⟩
  have hker : φ.ker = (X ⊓ centralizer (V : Set G)).subgroupOf X := by
    ext ⟨x, hx⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have e : φ ⟨x, hx⟩ = glLin (S.rho_F4 ⟨x, hXN hx⟩) := rfl
    rw [e, MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      exact ⟨hx, (mem_centralizer_V_iff (hXN hx) (S.rho_spec_F4 _)).2 h⟩
    · rintro ⟨-, h⟩
      exact (mem_centralizer_V_iff (hXN hx) (S.rho_spec_F4 _)).1 h
  rw [← hrange, ← Subgroup.index_ker, hker]
  rfl

theorem inf_centralizer_eq_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G)) :
    V ⊓ centralizer (X : Set G) = pullSub S.Φ (linFix (S.imgL_F4 X)) := by
  ext v
  rw [mem_inf, mem_pullSub]
  constructor
  · rintro ⟨hv, hvC⟩
    refine ⟨hv, mem_linFix_iff.2 fun g hg => ?_⟩
    obtain ⟨x, hxN, hxX, rfl⟩ := S.mem_imgL_F4.1 hg
    have h1 := phi_conj' hxN (S.rho_spec_F4 ⟨x, hxN⟩) hv
    have h2 : x * v * x⁻¹ = v := by
      rw [mem_centralizer_iff.1 hvC x hxX, mul_inv_cancel_right]
    rw [show (⟨x * v * x⁻¹, (mem_normalizer_iff.1 hxN v).1 hv⟩ : V) = ⟨v, hv⟩ from
      Subtype.ext h2] at h1
    exact h1.symm
  · rintro ⟨hv, hfix⟩
    refine ⟨hv, mem_centralizer_iff.2 fun x hxX => ?_⟩
    have hxN := hXN hxX
    have h1 := phi_conj' hxN (S.rho_spec_F4 ⟨x, hxN⟩) hv
    rw [mem_linFix_iff.1 hfix _ (S.glLin_rho_mem_imgL_F4 hxX hxN)] at h1
    have h2 := phi_injective' _ hv h1
    calc x * v = x * v * x⁻¹ * x := by group
      _ = v * x := by rw [h2]

theorem card_inf_centralizer_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G)) :
    Nat.card ↥(V ⊓ centralizer (X : Set G)) = Nat.card (linFix (S.imgL_F4 X)) := by
  rw [S.inf_centralizer_eq_F4 hXN, card_pullSub]

theorem isElementaryAbelian_imgL_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} (hX : IsElemAbelian 2 X) :
    IsElementaryAbelian 2 (S.imgL_F4 X) := by
  have hcomm : ∀ a b : S.imgL_F4 X, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨x, hxN, hxX, rfl⟩ := S.mem_imgL_F4.1 ha
    obtain ⟨y, hyN, hyX, rfl⟩ := S.mem_imgL_F4.1 hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (B2F.isElemAbelian_comm hX hxX hyX)
  have : IsMulCommutative (S.imgL_F4 X) := IsMulCommutative.of_comm hcomm
  refine ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨a, ha⟩ => ?_⟩
  obtain ⟨x, hxN, hxX, rfl⟩ := S.mem_imgL_F4.1 ha
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← map_pow, ← map_pow]
  have h2 : (⟨x, hxN⟩ : normalizer (V : Set G)) ^ 2 = 1 := Subtype.ext (hX.2 x hxX)
  rw [h2, map_one, map_one]

theorem card_mul_card_le_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} (hXT : X ≤ T) (hX : IsElemAbelian 2 X) :
    (X ⊓ centralizer (V : Set G)).relIndex X * Nat.card ↥(V ⊓ centralizer (X : Set G)) ≤ 64 := by
  have hXN : X ≤ normalizer (V : Set G) := hXT.trans S.hTV_F4
  have := S.isElementaryAbelian_imgL_F4 hX
  rw [← S.card_imgL_F4 hXN, S.card_inf_centralizer_F4 hXN]
  exact card_mul_card_linFix_le (S.imgL_le_S0L_F4 hXT) this

theorem phi_comm_F4
    (S : HullSetting_F4 G T L V z) {n v : G} (hn : n ∈ normalizer (V : Set G)) (hv : v ∈ V) :
    S.Φ (Additive.ofMul (⟨n * v * n⁻¹ * v⁻¹,
      V.mul_mem ((mem_normalizer_iff.1 hn v).1 hv) (V.inv_mem hv)⟩ : V)) =
      glLin (S.rho_F4 ⟨n, hn⟩) (S.Φ (Additive.ofMul (⟨v, hv⟩ : V))) -
        S.Φ (Additive.ofMul (⟨v, hv⟩ : V)) := by
  rw [phi_mul' ((mem_normalizer_iff.1 hn v).1 hv) (V.inv_mem hv),
    phi_conj' hn (S.rho_spec_F4 ⟨n, hn⟩) hv, phi_inv' hv, sub_eq_add_neg]

theorem comm_iff_fix_F4
    (S : HullSetting_F4 G T L V z) {n v : G} (hn : n ∈ normalizer (V : Set G)) (hv : v ∈ V) :
    n * v = v * n ↔ glLin (S.rho_F4 ⟨n, hn⟩) (S.Φ (Additive.ofMul (⟨v, hv⟩ : V))) =
      S.Φ (Additive.ofMul (⟨v, hv⟩ : V)) := by
  have h1 := phi_conj' hn (S.rho_spec_F4 ⟨n, hn⟩) hv
  constructor
  · intro h
    have h2 : n * v * n⁻¹ = v := by rw [h, mul_inv_cancel_right]
    rw [show (⟨n * v * n⁻¹, (mem_normalizer_iff.1 hn v).1 hv⟩ : V) = ⟨v, hv⟩ from
      Subtype.ext h2] at h1
    exact h1.symm
  · intro h
    rw [h] at h1
    have h2 := phi_injective' _ hv h1
    calc n * v = n * v * n⁻¹ * n := by group
      _ = v * n := by rw [h2]

end HullSetting_F4

end CFSG.Quasithin.H13.U3
