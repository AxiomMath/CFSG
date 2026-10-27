module

public import CFSG.Quasithin.H13.A6S1372L76Og3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Oe2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenTilde

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem false_of_levi_F4 (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (h1337 : Stmt13_3_7_F4) (hNS : ¬ LieModel G .PSp 3 2 1)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    {g₀ : ↥(Subgroup.normalizer (V : Set G))} (hgX : (g₀ : G) ∈ S.X1375)
    (hg : S.frame.ρ g₀ = swap 0 1 * swap 1 2) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F)
    {ι : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))} (hιinj : Function.Injective ι)
    (hιfix : ∀ A, ((ι A : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _)
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨S.v2, S.v2_mem_UH H⟩) *
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
          ⟨S.v2, S.v2_mem_UH H⟩)⁻¹ ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ∧
      ((ι A : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _)
        (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
          ⟨g₀, X1375_le_H hH hgX⟩ (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
            ⟨S.v2, S.v2_mem_UH H⟩)) *
        (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
          ⟨g₀, X1375_le_H hH hgX⟩ (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
            ⟨S.v2, S.v2_mem_UH H⟩))⁻¹ ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK

  let κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict _
      fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκ : ∀ k : ↥K, ((κ k : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) =
      A6Mod.secAct hHU hHV ⟨k, hKH k.2⟩ := fun k => rfl
  have hκs : Function.Surjective κ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hψ
    exact ⟨⟨f, hfK⟩, rfl⟩
  have hκ2 : ∀ k : ↥K, κ k = 1 → ∃ j : ℕ, k ^ (2 ^ j) = 1 := by
    intro k hk
    have h1 : A6Mod.secAct hHU hHV ⟨k, hKH k.2⟩ = 1 := by
      rw [← hκ]
      exact congrArg Subtype.val hk
    have h2 := (S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH (hKH k.2)).2
      ((A6Mod.secAct_eq_one_iff hHU hHV _).1 h1)
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, h2⟩
    exact ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩

  set Y₀ : Subgroup ↥K := Subgroup.closure {k | Odd (orderOf k) ∧ κ k ∈ ι.range} with hY₀
  have hgenV3 : ∀ k : ↥K, Odd (orderOf k) → κ k ∈ ι.range →
      ∀ u ∈ S.V3, (k : G) * u * (k : G)⁻¹ ∈ S.V3 := by
    intro k hk hkι
    obtain ⟨A, hA⟩ := hkι
    obtain ⟨h1, h2⟩ := hιfix A
    rw [hA] at h1 h2
    have hfix := S.fix_V3_of_odd hH hab hgX hg (κ k).2
      (Odd.of_dvd_nat hk (by rw [Subgroup.orderOf_coe]; exact orderOf_map_dvd κ k)) h1 h2
    exact S.conj_mem_V3_of_fix hH (hKH k.2) fun u hu => by rw [← hκ]; exact hfix u hu
  have hY₀N : ∀ k ∈ Y₀, (k : G) ∈ Subgroup.normalizer (S.V3 : Set G) := by
    have hle : Y₀ ≤ (Subgroup.normalizer (S.V3 : Set G)).comap K.subtype := by
      rw [hY₀, Subgroup.closure_le]
      rintro k ⟨hk, hkι⟩
      show (k : G) ∈ Subgroup.normalizer (S.V3 : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro u
      refine ⟨hgenV3 k hk hkι u, fun hu' => ?_⟩
      have hk' : Odd (orderOf k⁻¹) := by rwa [orderOf_inv]
      have hkι' : κ k⁻¹ ∈ ι.range := by
        rw [map_inv]
        exact ι.range.inv_mem hkι
      have h1 := hgenV3 k⁻¹ hk' hkι' _ hu'
      have e : ((k⁻¹ : ↥K) : G) * ((k : G) * u * (k : G)⁻¹) * ((k⁻¹ : ↥K) : G)⁻¹ = u := by
        simp only [InvMemClass.coe_inv, inv_inv]
        group
      rwa [e] at h1
    exact fun k hk => hle hk
  have hY₀NV : ∀ k ∈ Y₀, (k : G) ∈ Subgroup.normalizer (V : Set G) :=
    fun k hk => S.G1_inf_G3_le_F4 h13315 ⟨hH.2.1 (hKH k.2), hY₀N k hk⟩

  set X : Subgroup ↥K := Y₀ ⊓ (Subgroup.centralizer (V : Set G)).comap K.subtype with hX
  refine A6L76Og.false_of_sl2_image h4 hκs hιinj (Y₀ := Y₀) (X := X)
    (fun k hk hkι => Subgroup.subset_closure ⟨hk, hkι⟩) (fun k hk => ?_) (fun y hy x hx => ?_)
    (fun k hk => ?_) hκ2 ?_
  ·
    have hle : Y₀ ≤ ι.range.comap κ := by
      rw [hY₀, Subgroup.closure_le]
      rintro k ⟨-, hk⟩
      exact hk
    exact hle hk
  ·
    refine ⟨Y₀.mul_mem (Y₀.mul_mem hy hx.1) (Y₀.inv_mem hy), ?_⟩
    show ((y * x * y⁻¹ : ↥K) : G) ∈ Subgroup.centralizer (V : Set G)
    have hyV := hY₀NV y hy
    have hxV : ((x : ↥K) : G) ∈ Subgroup.centralizer (V : Set G) := hx.2
    rw [Subgroup.mem_centralizer_iff] at hxV ⊢
    intro v hv
    have hv' : ((y : ↥K) : G)⁻¹ * v * ((y : ↥K) : G)⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyV) v).mp hv
    have h1 := hxV _ hv'
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] at h1 ⊢
    calc v * ((y : G) * (x : G) * (y : G)⁻¹)
        = (y : G) * ((y : G)⁻¹ * v * (y : G) * (x : G)) * (y : G)⁻¹ := by group
      _ = (y : G) * ((x : G) * ((y : G)⁻¹ * v * (y : G))) * (y : G)⁻¹ := by rw [h1]
      _ = (y : G) * (x : G) * (y : G)⁻¹ * v := by group
  ·
    refine ⟨Y₀.pow_mem hk 48, ?_⟩
    show ((k ^ 48 : ↥K) : G) ∈ Subgroup.centralizer (V : Set G)
    have hz : (k : G) * S.z * (k : G)⁻¹ = S.z := by
      have h1 : (k : G) ∈ S.G1 := hH.2.1 (hKH k.2)
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
      rw [h1, mul_inv_cancel_right]
    have hmem : S.frame.ρ ⟨(k : G), hY₀NV k hk⟩ ∈ A6L76F.stabE := S.fix_e0123 _ hz
    have h := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥A6L76F.stabE)
    rw [A6L76F.card_stabE] at h
    have h2 := orderOf_dvd_iff_pow_eq_one.1 h
    have h3 : S.frame.ρ (⟨(k : G), hY₀NV k hk⟩ ^ 48) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val h2
    have h4 := (S.rho_eq_one_iff _).1 h3
    simpa using h4
  ·
    rcases h1337 G T L V S.h13 S.irr S.a6 with h3 | ⟨hhat, -, hl0⟩
    · left
      intro x hx hxo
      apply h3
      have h1 := Subgroup.orderOf_dvd_natCard _ (show ((x : ↥K) : G) ∈
        Subgroup.centralizer (V : Set G) from hx.2)
      rwa [Subgroup.orderOf_coe, hxo] at h1
    · right
      intro x₁ hx₁ x₂ hx₂ ho₁ ho₂
      have hmemL : ∀ x ∈ X, orderOf x = 3 → ((x : ↥K) : G) ∈ l0 L := by
        intro x hx hxo
        rw [hl0]
        exact Subgroup.subset_closure ⟨hx.2, by rw [Subgroup.orderOf_coe]; exact hxo⟩
      have hp : ((x₁ : ↥K) : G) * ((x₂ : ↥K) : G) ∈ o2Z L :=
        oTwoRes_le _ ((l0 L).mul_mem (hmemL x₁ hx₁ ho₁) (hmemL x₂ hx₂ ho₂))
      obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨_, cube_mem_of_o2Z hhat hp⟩
      exact ⟨j, Subtype.ext (by rw [pow_mul]; simpa using hj)⟩

theorem false_of_natSL3_ge_two_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (h1337 : Stmt13_3_7_F4) (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn2 : 2 ≤ n)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨g₀, hgX, hg⟩ := S.exists_X1375_c012
  obtain ⟨a, P, v₂, rfl, -, rfl, haY, -, hP2, hPodd, hPv, hPa, -, hv⟩ :=
    S.exists_odd_config_of_F4 hH hK rfl h139 h37 h38 h13315 hgX hg
  obtain ⟨ι, hιinj, hιfix⟩ := A6L76Og.exists_levi (S.isPerfect_tilde hH hK) hn2 hF hπ haY
    hP2 hPodd hPv hPa hv
  exact S.false_of_levi_F4 h13315 h1356two h1337 hNS hH hab hK hgX hg h4 hιinj hιfix

end Setting4

end CFSG.Quasithin.H13.A6
