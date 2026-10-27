module

public import CFSG.Quasithin.H13.L32A53a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

structure Ctx_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ Y : Subgroup G) : Prop where

  hyp : Hyp147 G T L V

  h1222 : Stmt12_2_2_F4

  h1332 : Stmt13_3_2_F4

  h1334 : A6.Stmt13_3_4_F4

  hV2 : A6.IsV2 T V V₂

  hYo : oTwoUpper Y = Y

  hYG1 : Y ≤ A6.g1 T V

  hTY : T ≤ Subgroup.normalizer (Y : Set G)

  hS3 : quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3))

  hcex : ¬ Concl T L V V₂ Y

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.T53.Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx_F4 G T L V V₂ Y)
include C

theorem isMulCommutative_V_F4 : IsMulCommutative ↥V :=
  (stmtL32NModule_of_inputs_F4 C.h1332 C.h1334 G T L V C.hyp.hyp C.hyp.fsu).1.1

theorem set14_F4 [IsMulCommutative ↥V] : L32NSet14.Setting_F4 G T L V V₂ :=
  C.hyp.set14_F4 C.h1222 C.h1332 C.h1334 C.hV2

theorem conjClosure_V1_X_F4 : conjClosure (fsuV1 T V) (xL L V₂) = V₂ := by
  have : IsMulCommutative ↥V := C.isMulCommutative_V_F4
  have S := C.set14_F4
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S.exists_basis_F4
  obtain ⟨l, hl, hla⟩ := S.exists_L2_F4 hz hz1 ha haV hb hbV
  have hle : conjClosure (fsuV1 T V) (xL L V₂) ≤ V₂ := by
    refine conjClosure_le fun x hx v hv => ?_
    have hxN : x ∈ Subgroup.normalizer (V₂ : Set G) := (oTwoRes_le _ hx).2
    exact (Subgroup.mem_normalizer_iff.mp hxN v).mp (C.hV2.1 hv)
  have hV1W : fsuV1 T V ≤ conjClosure (fsuV1 T V) (xL L V₂) := le_conjClosure _ _
  have haW : a ∈ conjClosure (fsuV1 T V) (xL L V₂) := by
    rw [← hla]
    exact mem_conjClosure hl hz
  have h2 : Nat.card (fsuV1 T V) = 2 := S.card_V1_F4
  have h4 : Nat.card V₂ = 4 := C.hV2.2.2.2
  have hd1 := Subgroup.card_dvd_of_le hV1W
  have hd2 := Subgroup.card_dvd_of_le hle
  rw [h2] at hd1
  rw [h4] at hd2
  have hne : Nat.card (conjClosure (fsuV1 T V) (xL L V₂)) ≠ 2 := by
    intro h
    exact haV (by rw [Subgroup.eq_of_le_of_card_ge hV1W (by rw [h, h2])]; exact haW)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h4]
  have hpos : 0 < Nat.card (conjClosure (fsuV1 T V) (xL L V₂)) := Nat.card_pos
  have hle4 := Nat.le_of_dvd (by norm_num) hd2
  obtain ⟨c, hc⟩ := hd1
  rw [hc] at hne hle4 hpos ⊢
  have : c ≠ 1 := fun h => hne (by rw [h])
  omega

theorem not_le_M_F4 : ¬ Y ≤ Subgroup.normalizer (L : Set G) := by
  intro hYM
  apply C.hcex
  have : IsMulCommutative ↥V := C.isMulCommutative_V_F4
  have S := C.set14_F4
  have h6 := lemma1433Six_of_inputs_F4 C.h1332 C.h1334 C.h1222 G T L V
    C.hyp.hyp C.hyp.fsu (fsuV1 T V) Y inf_le_left (fun h => by
      have := S.card_V1_F4
      rw [h, Subgroup.card_bot] at this
      exact absurd this (by norm_num)) C.hYG1
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := by
    have : Y ⊓ Subgroup.normalizer (L : Set G) = Y := inf_eq_left.mpr hYM
    rw [this] at h6
    exact h6 ▸ inf_le_right
  refine ⟨Or.inl hYM, fun _ => hYM, ?_⟩
  have hle : conjClosure V₂ Y ≤ V := conjClosure_le fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hYV hy) v).mp (C.hV2.2.1 hv)
  have hV1W : fsuV1 T V ≤ conjClosure V₂ Y := C.hV2.1.trans (le_conjClosure _ _)
  have h1 := Subgroup.relIndex_mul_relIndex (fsuV1 T V) (conjClosure V₂ Y) V hV1W hle
  have h2 : (fsuV1 T V).relIndex V = 4 := by
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V)
    rw [inf_eq_left.mpr (inf_le_left : fsuV1 T V ≤ V), S.card_V1_F4, S.card_V_F4] at this
    omega
  rw [h2] at h1
  intro h8
  rw [h8] at h1
  omega

theorem centralizes_V2_of_normalizes_F4 (hN : Y ≤ Subgroup.normalizer (V₂ : Set G)) :
    ⁅V₂, Y⁆ = ⊥ := by
  have : IsMulCommutative ↥V := C.isMulCommutative_V_F4
  have S := C.set14_F4
  have hZY : Y ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
    rw [← L32A.normalizer_eq_centralizer_of_card_two S.card_V1_F4]
    exact C.hYG1

  have hodd : ∀ y ∈ Y, Odd (orderOf y) → y ∈ Subgroup.centralizer (V₂ : Set G) := by
    intro y hy hyo
    obtain ⟨z, a, b, hz, hz1, ha, haV, -, -⟩ := S.exists_basis_F4
    have hc : ∀ {g w : G}, g * w * g⁻¹ = w → w * g = g * w := fun {g w} h => by
      calc w * g = g * w * g⁻¹ * g := by rw [h]
        _ = g * w := by group
    have hzc : ∀ w ∈ fsuV1 T V, y * w * y⁻¹ = w := fun w hw => by
      rw [← Subgroup.mem_centralizer_iff.mp (hZY hy) w hw, mul_inv_cancel_right]
    have hya : y * a * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hN hy) a).mp ha
    have hVab : ∀ x ∈ V, ∀ x' ∈ V, x * x' = x' * x := fun x hx x' hx' => S.comm_V_F4 hx hx'

    obtain ⟨w, hw, hyaw⟩ : ∃ w ∈ fsuV1 T V, y * a * y⁻¹ = a⁻¹ * w := by
      rcases S.mem_V2_F4 ha haV hya with h | h
      · exfalso
        apply haV
        have h1 : y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ ∈ fsuV1 T V := by
          have := Subgroup.mem_centralizer_iff.mp (hZY (inv_mem hy)) _ h
          rw [← this, mul_inv_cancel_right]
          exact h
        simpa [mul_assoc] using h1
      · exact ⟨a * (y * a * y⁻¹), h, by group⟩
    have haV' : a ∈ V := C.hV2.2.1 ha
    have hwV : w ∈ V := (Subgroup.mem_inf.mp hw).1

    have hy2 : y ^ 2 ∈ Subgroup.centralizer ({a} : Set G) := by
      have h1 : (y * y) * a * (y * y)⁻¹ = a := by
        calc (y * y) * a * (y * y)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by group
          _ = y * (a⁻¹ * w) * y⁻¹ := by rw [hyaw]
          _ = (y * a * y⁻¹)⁻¹ * (y * w * y⁻¹) := by group
          _ = (a⁻¹ * w)⁻¹ * w := by rw [hyaw, hzc w hw]
          _ = w⁻¹ * (a * w) := by group
          _ = a := by rw [hVab a haV' w hwV]; group
      rw [pow_two, Subgroup.mem_centralizer_singleton_iff]
      exact (hc h1).symm
    have hya1 : y ∈ Subgroup.centralizer ({a} : Set G) :=
      (Subgroup.zpowers_le.mpr hy2) (A4.mem_zpowers_pow_of_coprime
        (Nat.coprime_two_left.mpr hyo))
    have hya2 : y * a * y⁻¹ = a := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hya1
      rw [hya1, mul_inv_cancel_right]
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases S.mem_V2_F4 ha haV hv with h | h
    · exact hc (hzc v h)
    · refine hc ?_
      calc y * v * y⁻¹ = (y * a * y⁻¹)⁻¹ * (y * (a * v) * y⁻¹) := by group
        _ = v := by rw [hya2, hzc _ h]; group

  have hYC : Y ≤ Subgroup.centralizer (V₂ : Set G) := by
    rw [← C.hYo]
    exact (Subgroup.closure_le _).mpr fun y hy => hodd y hy.1 hy.2
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro v hv y hy
  rw [commutatorElement_def, Subgroup.mem_centralizer_iff.mp (hYC hy) v hv]
  simp

theorem inf_M_eq_F4 : Y ⊓ Subgroup.normalizer (L : Set G) = Y ⊓ Subgroup.normalizer (V : Set G) := by
  have : IsMulCommutative ↥V := C.isMulCommutative_V_F4
  have S := C.set14_F4
  exact lemma1433Six_of_inputs_F4 C.h1332 C.h1334 C.h1222 G T L V C.hyp.hyp C.hyp.fsu (fsuV1 T V) Y
    inf_le_left (fun h => by
      have := S.card_V1_F4
      rw [h, Subgroup.card_bot] at this
      exact absurd this (by norm_num)) C.hYG1

theorem not_le_normalizer_F4 :
    ¬ Y ≤ Subgroup.normalizer ((xL L V₂ ⊔ cH T L V V₂ Y : Subgroup G) : Set G) := by
  intro hN
  have : IsMulCommutative ↥V := C.isMulCommutative_V_F4
  have S := C.set14_F4
  have hZY : Y ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
    rw [← L32A.normalizer_eq_centralizer_of_card_two S.card_V1_F4]
    exact C.hYG1

  have hYV2 : Y ≤ Subgroup.normalizer (V₂ : Set G) := by
    intro y hy
    rw [← C.conjClosure_V1_X_F4]
    refine mem_normalizer_conjClosure_of fun x hx z hz => ?_
    have hyx : y * x * y⁻¹ ∈ ((xL L V₂ ⊔ cH T L V V₂ Y : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hN hy) x).mp (Subgroup.mem_sup_left hx)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ xL_le_normalizer_cH] at hyx
    obtain ⟨x', hx', c, hc, hxc⟩ := hyx
    have hxc' : x' * c = y * x * y⁻¹ := hxc
    have hzV : z ∈ vH T L V V₂ Y := le_conjClosure _ _ hz
    have hcz : c * z * c⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hc.2 z hzV, mul_inv_cancel_right]
    have hyz : y * z * y⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp (hZY hy) z hz, mul_inv_cancel_right]
    have e : y * (x * z * x⁻¹) * y⁻¹ = x' * (c * z * c⁻¹) * x'⁻¹ := by
      calc y * (x * z * x⁻¹) * y⁻¹ = (y * x * y⁻¹) * (y * z * y⁻¹) * (y * x * y⁻¹)⁻¹ := by
            group
        _ = (x' * c) * z * (x' * c)⁻¹ := by rw [hyz, hxc']
        _ = x' * (c * z * c⁻¹) * x'⁻¹ := by group
    rw [e, hcz]
    exact mem_conjClosure hx' hz
  have hV2Y := C.centralizes_V2_of_normalizes_F4 hYV2
  have hYC : Y ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : v * y * v⁻¹ * y⁻¹ ∈ ⁅V₂, Y⁆ := Subgroup.commutator_mem_commutator hv hy
    rw [hV2Y, Subgroup.mem_bot] at h1
    calc v * y = (v * y * v⁻¹ * y⁻¹) * y * v := by group
      _ = y * v := by rw [h1, one_mul]
  have hL1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _

  apply C.hcex
  refine ⟨Or.inr hV2Y, fun hLY => ?_, ?_⟩
  ·
    exfalso
    apply C.not_le_M_F4
    have hYV : Y ≤ Subgroup.normalizer (V : Set G) := by
      intro y hy
      rw [← S.gen_F4]
      refine mem_normalizer_conjClosure_of fun l hl w hw => ?_
      have hl' : l ∈ l1 T L V := hL1 ▸ hl
      have hyl : y * l ∈ (Y : Set G) * (l1 T L V : Set G) := Set.mul_mem_mul hy hl'
      rw [hLY] at hyl
      obtain ⟨l₂, hl₂, y₂, hy₂, hlye⟩ := hyl
      have hlye' : l₂ * y₂ = y * l := hlye
      have hyw : y₂ * w * y₂⁻¹ = w := by
        rw [← Subgroup.mem_centralizer_iff.mp (hYC hy₂) w hw, mul_inv_cancel_right]
      have hl₂' : l₂ ∈ L₁Of L (fsuV1 T V) := hL1 ▸ hl₂
      have e : y * (l * w * l⁻¹) * y⁻¹ = l₂ * (y₂ * w * y₂⁻¹) * l₂⁻¹ := by
        calc y * (l * w * l⁻¹) * y⁻¹ = (y * l) * w * (y * l)⁻¹ := by group
          _ = (l₂ * y₂) * w * (l₂ * y₂)⁻¹ := by rw [hlye']
          _ = l₂ * (y₂ * w * y₂⁻¹) * l₂⁻¹ := by group
      rw [e, hyw]
      exact mem_conjClosure hl₂' hw
    have h := C.inf_M_eq_F4
    rw [inf_eq_left.mpr hYV] at h
    exact inf_eq_left.mp h
  ·
    have hW : conjClosure V₂ Y = V₂ := by
      refine le_antisymm (conjClosure_le fun y hy v hv => ?_) (le_conjClosure _ _)
      rw [← Subgroup.mem_centralizer_iff.mp (hYC hy) v hv, mul_inv_cancel_right]
      exact hv
    rw [hW]
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V₂)
    rw [inf_eq_left.mpr C.hV2.1, S.card_V1_F4, C.hV2.2.2.2] at this
    omega

end Ctx_F4

end CFSG.Quasithin.H13.L32A.T53
