module

public import CFSG.Quasithin.H13.L32NLem14413d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14413c

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

structure XCtx_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ X : Subgroup G) (g : G) : Prop where

  hyp : Hyp14310One G T L V

  ext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)

  plane : IsL32NPlane T V V₂

  gP : g ∈ p128 T L V

  gH : g ∉ l32nH T V

  Y : IsY1442 T V V₂ g X

  zU : centerOf (fsuU T V) = fsuV1 T V

  V2X : V₂ ≤ ⁅V₂, X⁆

  s1282 : Setting1282One G T L V 3 (fsuV1 T V) V₂

  abs : L128A.Setting V₂ (fsuV1 T V) (oTwoUpper (p128 T L V)) T

  uA : L128A.uA V₂ (fsuV1 T V) = fsuU T V

  h1222 : Stmt12_2_2_F4

  cardV : Nat.card V = 8

  LTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G)

  elemE : IsElemAbelian 2 (l32nE T V V₂ g)

theorem XCtx_F4.mk'_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4) {T L V V₂ X : Subgroup G} {g : G}
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V)
    (hX : IsY1442 T V V₂ g X) : XCtx_F4 G T L V V₂ X g := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hs := h.setting1282One_F4 h13322 hV hV₂
  obtain ⟨-, hV8, hVN, -, -⟩ := hV G T L V h.hyp h.fsu
  exact ⟨h, hext, hV₂, hgP, hgH, hX, L1444.zU_eq_F4 h1332 h1334 h1222 h12213 h hext,
    fsuV2_le_commutator_F4 h1332 h1334 h1222 h12213 h12811 h hext hV₂ hgP hgH hX.2.1 hX.2.2.2.2.1
      hX.2.2.2.2.2, hs, L128P.setting128A_F4 h1222 h12213 hs,
    (lemma12_8_8_six_F4 h1222 hs).symm, h1222, hV8, hVN,
    (h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH).2.1⟩

namespace XCtx_F4
open CFSG.Quasithin.H13.L14413.XCtx_F4

variable {T L V V₂ X : Subgroup G} {g : G} (C : XCtx_F4 G T L V V₂ X g)
include C

theorem UT_F4 : fsuU T V ≤ T := C.uA ▸ C.abs.uA_le_T

theorem TV₂_F4 : T ≤ Subgroup.normalizer (V₂ : Set G) := C.plane.1.2.2

theorem V1X_F4 : fsuV1 T V ≤ ⁅V₂, X⁆ := C.plane.2.trans C.V2X

theorem VXE_F4 : ⁅V₂, X⁆ ≤ l32nE T V V₂ g := C.Y.2.2.2.2.2

theorem VXU_F4 : ⁅V₂, X⁆ ≤ fsuU T V := C.VXE_F4.trans (inf_le_left.trans inf_le_left)

theorem VXUg_F4 : ⁅V₂, X⁆ ≤ CFSG.conjugate (fsuU T V) g :=
  C.VXE_F4.trans (inf_le_right.trans (Subgroup.map_mono inf_le_left))

theorem gV₂_F4 : g ∈ Subgroup.normalizer (V₂ : Set G) :=
  L128P.p128_le_normalizer le_rfl C.plane.1 C.gP

theorem comm_mem_V1_F4 {u a : G} (hu : u ∈ fsuU T V) (ha : a ∈ fsuU T V) :
    u * a * u⁻¹ * a⁻¹ ∈ fsuV1 T V := by
  rw [← C.zU]
  exact L1444.comm_mem_centerOf C.ext _ hu _ ha

theorem U_le_normalizer_F4 : fsuU T V ≤ Subgroup.normalizer ((⁅V₂, X⁆ : Subgroup G) : Set G) := by
  intro u hu
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rw [show u * v * u⁻¹ = (u * v * u⁻¹ * v⁻¹) * v by group]
  exact Subgroup.mul_mem _ (C.V1X_F4 (C.comm_mem_V1_F4 hu (C.VXU_F4 hv))) hv

theorem conj_U_le_normalizer_F4 :
    CFSG.conjugate (fsuU T V) g ≤ Subgroup.normalizer ((⁅V₂, X⁆ : Subgroup G) : Set G) := by
  intro u hu
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  have hvU := C.VXUg_F4 hv
  rw [show CFSG.conjugate (fsuU T V) g = rconj (fsuU T V) g from rfl, mem_rconj] at hu hvU
  have h1 := C.comm_mem_V1_F4 hu hvU
  have h2 : g * (u * v * u⁻¹ * v⁻¹) * g⁻¹ ∈ fsuV1 T V := by
    rw [show g * (u * v * u⁻¹ * v⁻¹) * g⁻¹ =
      g * u * g⁻¹ * (g * v * g⁻¹) * (g * u * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ by group]
    exact h1
  have h3 : u * v * u⁻¹ * v⁻¹ ∈ V₂ := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem C.gV₂_F4)
      (g * (u * v * u⁻¹ * v⁻¹) * g⁻¹)).mp (C.plane.2 h2)
    simpa [mul_assoc] using this
  rw [show u * v * u⁻¹ = (u * v * u⁻¹ * v⁻¹) * v by group]
  exact Subgroup.mul_mem _ (C.V2X h3) hv

theorem sup_conj_eq_F4 :
    fsuU T V ⊔ CFSG.conjugate (fsuU T V) g = oTwoUpper (p128 T L V) ⊔ fsuU T V := by
  have hV := C.s1282
  have hTP : T ≤ p128 T L V := le_inf le_sup_right (le_iInf₂ fun Y ⟨_, _, hY⟩ => hY.2.2)
  obtain ⟨t, ht, g', hg', hg⟩ :=
    exists_mul_oTwoUpper (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow hTP) C.gP
  have htH : t ∈ l32nH T V := hV.v1.2.2 ht
  have hgood : L128A.Good (fsuV1 T V) (oTwoUpper (p128 T L V)) g' :=
    ⟨hg', fun hN => C.gH (hg ▸ (l32nH T V).mul_mem htH hN)⟩
  have hUg : rconj (L128A.uA V₂ (fsuV1 T V)) g' = CFSG.conjugate (fsuU T V) g := by
    ext x
    rw [show CFSG.conjugate (fsuU T V) g = rconj (fsuU T V) g from rfl, mem_rconj, mem_rconj,
      C.uA, hg, show t * g' * x * (t * g')⁻¹ = t * (g' * x * g'⁻¹) * t⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ htH) _)
  have hsup := C.abs.sup_rconj_uA_eq hgood
  rw [hUg, C.uA] at hsup
  exact hsup

theorem oTwoUpper_le_normalizer_F4 :
    oTwoUpper (p128 T L V) ≤ Subgroup.normalizer ((⁅V₂, X⁆ : Subgroup G) : Set G) :=
  (le_sup_left.trans C.sup_conj_eq_F4.ge).trans (sup_le C.U_le_normalizer_F4 C.conj_U_le_normalizer_F4)

theorem inf_normalizer_le_p128_F4 : L ⊓ Subgroup.normalizer (V₂ : Set G) ≤ p128 T L V := by
  rintro c ⟨hcL, hcN⟩
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hcL,
    Subgroup.mem_iInf.2 fun Y => Subgroup.mem_iInf.2 fun hY => ?_⟩
  obtain ⟨i, hi, hYi⟩ := hY
  rcases tinv_comparable_of_hyp1281One_F4 C.h1222 C.s1282.hyp hYi.1 C.plane.1.1 hYi.2.2
      C.plane.1.2.2 with hle | hle
  · have heq : Y = V₂ := Subgroup.eq_of_le_of_card_ge hle (by
      rw [C.plane.1.2.1, hYi.2.1]
      exact Nat.pow_le_pow_right (by norm_num) hi)
    rw [heq]
    exact hcN
  · have h8 : Nat.card Y ≤ 8 := by
      rw [← C.cardV]
      exact Subgroup.card_le_of_le hYi.1
    rw [hYi.2.1] at h8
    have hi3 : i ≤ 3 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      omega
    rcases (show i = 2 ∨ i = 3 by omega) with rfl | rfl
    · have heq : V₂ = Y := Subgroup.eq_of_le_of_card_ge hle (by rw [C.plane.1.2.1, hYi.2.1])
      rw [← heq]
      exact hcN
    · have heq : Y = V := Subgroup.eq_of_le_of_card_ge hYi.1 (by rw [C.cardV, hYi.2.1]; norm_num)
      rw [heq]
      exact C.LTV (Subgroup.mem_sup_left hcL)

theorem lTwo_le_normalizer_F4 :
    lOne L V₂ ≤ Subgroup.normalizer ((⁅V₂, X⁆ : Subgroup G) : Set G) :=
  (oTwoUpper_mono C.inf_normalizer_le_p128_F4).trans C.oTwoUpper_le_normalizer_F4

theorem H3_le_normalizer_F4 :
    lOne L V₂ ⊔ X ⊔ T ≤ Subgroup.normalizer ((⁅V₂, X⁆ : Subgroup G) : Set G) :=
  sup_le (sup_le C.lTwo_le_normalizer_F4 (le_normalizer_commutator_right V₂ X))
    fun _ ht => mem_normalizer_commutator (C.TV₂_F4 ht) (C.Y.2.1 ht)

end XCtx_F4

end CFSG.Quasithin.H13.L14413
