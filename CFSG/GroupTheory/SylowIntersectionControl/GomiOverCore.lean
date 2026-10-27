module

public import CFSG.GroupTheory.SylowIntersectionControl.CharPair
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
private theorem le_normalizer_gomiV_goc (G : Subgroup Ω) :
    G ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
  (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G).trans
    (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 G))

private def gocD_goc (G : Subgroup Ω) : Subgroup Ω where
  carrier := {x | x ∈ G ∧ x ∈ Subgroup.centralizer (gomiV G : Set Ω) ∧
    ∀ q ∈ pCoreOf 2 G, ⁅q, x⁆ ∈ gomiV G}
  one_mem' := ⟨G.one_mem, Subgroup.one_mem _, fun q _ => by
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨haG, haC, haQ⟩ ⟨hbG, hbC, hbQ⟩
    refine ⟨G.mul_mem haG hbG, Subgroup.mul_mem _ haC hbC, fun q hq => ?_⟩
    have hconj : a * ⁅q, b⁆ * a⁻¹ = ⁅q, b⁆ := by
      rw [← Subgroup.mem_centralizer_iff.mp haC _ (hbQ q hq), mul_assoc, mul_inv_cancel,
        mul_one]
    rw [commutatorElement_mul_right_eq_mul_conj,
      show ⁅q, a⁆ * a * ⁅q, b⁆ * a⁻¹ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) by group, hconj]
    exact Subgroup.mul_mem _ (haQ q hq) (hbQ q hq)
  inv_mem' := by
    rintro a ⟨haG, haC, haQ⟩
    refine ⟨G.inv_mem haG, Subgroup.inv_mem _ haC, fun q hq => ?_⟩
    have hconj : a⁻¹ * ⁅q, a⁆⁻¹ * a = ⁅q, a⁆⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.mp haC _ (Subgroup.inv_mem _ (haQ q hq))
      calc a⁻¹ * ⁅q, a⁆⁻¹ * a = a⁻¹ * (⁅q, a⁆⁻¹ * a) := by group
        _ = a⁻¹ * (a * ⁅q, a⁆⁻¹) := by rw [h]
        _ = ⁅q, a⁆⁻¹ := by group
    rw [commutatorElement_inv_right, ← commutatorElement_inv, hconj]
    exact Subgroup.inv_mem _ (haQ q hq)

omit [Finite Ω] in
private theorem gocD_sq_mem_goc (G : Subgroup Ω) (hchar : CharTwo G) {x : Ω}
    (hx : x ∈ gocD_goc G) : x ^ 2 ∈ pCoreOf 2 G := by
  obtain ⟨hxG, hxV, hxQ⟩ := hx
  refine hchar ⟨?_, ?_⟩
  · simpa [pow_two] using G.mul_mem hxG hxG
  refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
  have hv : ⁅q, x⁆ ∈ gomiV G := hxQ q hq
  have hv2 : ⁅q, x⁆ ^ 2 = 1 := CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hv
  have hxv : x * ⁅q, x⁆⁻¹ * x⁻¹ = ⁅q, x⁆⁻¹ := by
    rw [← Subgroup.mem_centralizer_iff.mp hxV _ (Subgroup.inv_mem _ hv), mul_assoc,
      mul_inv_cancel, mul_one]
  have hconj : x ^ 2 * q * (x ^ 2)⁻¹ = q := by
    have hxq : x * q * x⁻¹ = ⁅q, x⁆⁻¹ * q := by
      simp only [commutatorElement_def]
      group
    calc x ^ 2 * q * (x ^ 2)⁻¹ = x * (x * q * x⁻¹) * x⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
      _ = x * (⁅q, x⁆⁻¹ * q) * x⁻¹ := by rw [hxq]
      _ = (x * ⁅q, x⁆⁻¹ * x⁻¹) * (x * q * x⁻¹) := by group
      _ = ⁅q, x⁆⁻¹ * (⁅q, x⁆⁻¹ * q) := by rw [hxv, hxq]
      _ = q := by
        have hvv : ⁅q, x⁆⁻¹ * ⁅q, x⁆⁻¹ = 1 := by
          rw [← mul_inv_rev, ← pow_two, hv2, inv_one]
        rw [← mul_assoc, hvv, one_mul]
  show q * x ^ 2 = x ^ 2 * q
  calc q * x ^ 2 = (x ^ 2 * q * (x ^ 2)⁻¹) * x ^ 2 := by rw [hconj]
    _ = x ^ 2 * q := by group

private theorem gocD_isPGroup_goc (G : Subgroup Ω) (hchar : CharTwo G) :
    IsPGroup 2 (gocD_goc G) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro y
  have hy2Q : (y : Ω) ^ 2 ∈ pCoreOf 2 G := gocD_sq_mem_goc G hchar y.2
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one (p := 2) (G := ↥(pCoreOf 2 G))).mp
    hQ2 ⟨(y : Ω) ^ 2, hy2Q⟩
  have hk' : ((y : Ω) ^ 2) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  refine ⟨k + 1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_succ', pow_mul]
  exact hk'

omit [Finite Ω] in
private theorem gocD_normal_goc (G : Subgroup Ω) :
    G ≤ Subgroup.normalizer (gocD_goc G : Set Ω) := by
  have hGV : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := le_normalizer_gomiV_goc G
  have hGQ : G ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  have key : ∀ a ∈ G, ∀ x ∈ gocD_goc G, a * x * a⁻¹ ∈ gocD_goc G := by
    rintro a ha x ⟨hxG, hxC, hxQ⟩
    refine ⟨G.mul_mem (G.mul_mem ha hxG) (G.inv_mem ha),
      CFSG.Quasithin.B6.conj_mem_centralizer_of_mem_normalizer (hGV ha) hxC,
      fun q hq => ?_⟩
    have hq' : a⁻¹ * q * a ∈ pCoreOf 2 G :=
      (Subgroup.mem_normalizer_iff''.mp (hGQ ha) q).mp hq
    have hcomm : ⁅a⁻¹ * q * a, x⁆ ∈ gomiV G := hxQ _ hq'
    have hconjV : a * ⁅a⁻¹ * q * a, x⁆ * a⁻¹ ∈ gomiV G :=
      (Subgroup.mem_normalizer_iff.mp (hGV ha) _).mp hcomm
    have hconj' : a * ⁅a⁻¹ * q * a, x⁆ * a⁻¹ = ⁅q, a * x * a⁻¹⁆ := by
      rw [conjugate_commutatorElement]
      congr 1
      group
    rwa [← hconj']
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  have := key a⁻¹ (G.inv_mem ha) _ hx
  simpa [mul_assoc] using this

omit [Finite Ω] in
theorem omegaOneCenterOf_le_gomiV_of_pCoreOf_le {G T : Subgroup Ω} (hchar : CharTwo G)
    (hTG : T ≤ G) (hQT : pCoreOf 2 G ≤ T) : omegaOneCenterOf T ≤ gomiV G := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxT, hxC⟩, hx2⟩
  have hxCQ : x ∈ Subgroup.centralizer (pCoreOf 2 G : Set Ω) :=
    Subgroup.centralizer_le hQT hxC
  exact Subgroup.subset_closure
    ⟨⟨hchar ⟨hTG hxT, hxCQ⟩, hxCQ⟩, hx2⟩

theorem gomiV_le_gomiV_of_pCoreOf_le {G H : Subgroup Ω} (hchar : CharTwo G) (hHG : H ≤ G)
    (hQH : pCoreOf 2 G ≤ H) : gomiV H ≤ gomiV G := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hQH' : pCoreOf 2 G ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH
      (hHG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)) hQ2
  exact omegaOneCenterOf_le_gomiV_of_pCoreOf_le hchar
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHG) hQH'

theorem mem_pCoreOf_of_commutator_mem_gomiV {G : Subgroup Ω} (hchar : CharTwo G) {g : Ω}
    (hg : g ∈ G) (hgV : g ∈ centralizer (gomiV G : Set Ω))
    (hgQ : ∀ q ∈ pCoreOf 2 G, ⁅q, g⁆ ∈ gomiV G) : g ∈ pCoreOf 2 G := by
  have hgD : g ∈ gocD_goc G := ⟨hg, hgV, hgQ⟩
  have hD2 : IsPGroup 2 (gocD_goc G) := gocD_isPGroup_goc G hchar
  have hDle : gocD_goc G ≤ pCoreOf 2 G :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun _ hx => hx.1)
      (gocD_normal_goc G) hD2
  exact hDle hgD

theorem thompsonJ_eq_of_thompsonJ_le {G S T : Subgroup Ω} (hS : IsSylowTwoOf S G)
    (hTG : T ≤ G) (hT : IsPGroup 2 T) (hJ : thompsonJ S ≤ T) : thompsonJ T = thompsonJ S := by
  obtain ⟨S', hS', hTS'⟩ := CFSG.Quasithin.B6.exists_isSylowTwoOf_ge hT hTG
  obtain ⟨a, -, haS'⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hS hS'
  have hJle : thompsonJ S ≤ thompsonJ S' := by
    refine iSup₂_le fun A hA => ?_
    have hAG : IsMaxElemAbelian G A := CFSG.Quasithin.B6.isMaxElemAbelian_of_sylow hS hA
    have hAS' : IsMaxElemAbelian S' A :=
      ⟨(CFSG.Quasithin.B6.le_thompsonJ hA).trans (hJ.trans hTS'), hAG.2.1,
        fun B hBS' hB => hAG.2.2 B (hBS'.trans hS'.1) hB⟩
    exact CFSG.Quasithin.B6.le_thompsonJ hAS'
  have hcard : Nat.card (thompsonJ S') = Nat.card (thompsonJ S) := by
    rw [haS', CFSG.Quasithin.B6.thompsonJ_conjSub, CFSG.Quasithin.B6.card_conjSub]
  have hJS : thompsonJ S = thompsonJ S' :=
    Subgroup.eq_of_le_of_card_ge (H := thompsonJ S) (K := thompsonJ S') hJle
      (le_of_eq hcard)
  have hJ' : thompsonJ S' ≤ T := hJS.symm.le.trans hJ
  exact (CFSG.Quasithin.B6.thompsonJ_eq_of_le (S := S') (R := T) hJ' hTS').trans hJS.symm

end CFSG.GroupTheory