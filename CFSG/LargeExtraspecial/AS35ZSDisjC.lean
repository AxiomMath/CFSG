module

public import CFSG.LargeExtraspecial.AS35ZSDisjB
public import CFSG.LargeExtraspecial.AS35ZSSU3
import all CFSG.Fischer.F4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

@[expose] def gS : List (Fin 4 → F4) := [![0, 1, 1, 0], ![0, 1, F4.ω, 0], ![1, 0, 1, 0]]

@[expose] def words2 : List (List (Fin 4 → F4)) :=
  [[]] ++ gS.map (fun x => [x]) ++ gS.flatMap (fun x => gS.map fun y => [x, y])

@[expose] def units4 : List F4 := [1, F4.ω, w2]

@[expose] def U9 : List (Fin 4 → F4) :=
  [![0, 1, 1, 0], ![0, 1, F4.ω, 0], ![0, 1, w2, 0], ![1, 0, 1, 0], ![1, 0, F4.ω, 0],
    ![1, 0, w2, 0], ![1, 1, 0, 0], ![1, F4.ω, 0, 0], ![1, w2, 0, 0]]

theorem gS_spec : ∀ x ∈ gS, herm4 x x = 0 ∧ x 3 = 0 ∧ x ≠ 0 := by decide +kernel

theorem U9_spec : ∀ x ∈ U9, herm4 x x = 0 ∧ x 3 = 0 ∧ x ≠ 0 := by decide +kernel

theorem words2_spec : ∀ l ∈ words2, ∀ x ∈ l, x ∈ gS := by decide +kernel

theorem U_points_spec : ∀ q : Fin 4 → F4, q ≠ 0 → herm4 q q = 0 → q 3 = 0 →
    ∃ s ∈ gS, ∃ l ∈ words2, ∃ c ∈ units4, wordApply l s = c • q := by
  decide +kernel

theorem pairs_spec : ∀ q : Fin 4 → F4, herm4 q q = 0 → q 3 ≠ 0 →
    ∃ a ∈ U9, ∃ b ∈ U9, herm4 a b ≠ 0 ∧ herm4 q a = 0 ∧ herm4 q b = 0 := by
  decide +kernel

theorem perp_two_spec : ∀ y z : Fin 2 → F4, y ≠ 0 → herm4 y y = 0 → herm4 y z = 0 →
    ∃ c : F4, z = c • y := by
  decide +kernel

theorem herm4_eq_zero {x y : Fin n → F4} (h : herm frob (vecK x) (vecK y) = 0) :
    herm4 x y = 0 := by
  rw [herm_vecK] at h
  exact (map_eq_zero_iff eF4 eF4.injective).1 h

theorem perp_two {y z : Fin 2 → K} (hy0 : y ≠ 0) (hy : herm frob y y = 0)
    (hyz : herm frob y z = 0) : ∃ c : K, z = c • y := by
  rw [eq_vecK y] at hy0 hy hyz ⊢
  rw [eq_vecK z] at hyz ⊢
  have hy0' : (fun i => eF4.symm (y i)) ≠ 0 := fun h0 => hy0 (by rw [h0]; funext i; simp)
  obtain ⟨c, hc⟩ := perp_two_spec _ _ hy0' (herm4_eq_zero hy) (herm4_eq_zero hyz)
  exact ⟨eF4 c, by rw [hc, vecK_smul]⟩

theorem vecK_ne_zero {x : Fin n → F4} (hx : x ≠ 0) : vecK x ≠ 0 := fun h0 =>
  hx (vecK_injective (by rw [h0]; funext i; simp [vecK]))

theorem herm_vecK_self {x : Fin n → F4} (hx : herm4 x x = 0) : herm frob (vecK x) (vecK x) = 0 :=
  by rw [herm_vecK, hx, map_zero]

abbrev IsoVec (n : ℕ) := {x : Fin n → K // x ≠ 0 ∧ herm frob x x = 0}

namespace ZSHyp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem iSup_lineA_eq_top (h : ZSHyp n q ρ) : (⨆ x : IsoVec n, lineA ρ x.1) = ⊤ := by
  set W := ⨆ x : IsoVec n, lineA ρ x.1 with hW
  have hinv : ∀ g : PG n, ∀ w ∈ W, ρ g w ∈ W := by
    intro g w hw
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    refine Submodule.iSup_induction (fun y : IsoVec n => lineA ρ y.1)
      (motive := fun w => ρ (QuotientGroup.mk g') w ∈ W) hw ?_ ?_ ?_
    · intro x v hv
      have hgx : herm frob (g' • x.1) (g' • x.1) = 0 := by rw [herm_smul_smul, x.2.2]
      have hle := le_iSup (fun y : IsoVec n => lineA ρ y.1)
        ⟨g' • x.1, (smul_ne_zero_iff_ne g').2 x.2.1, hgx⟩
      exact hle (apply_mem_lineA g' x.2.2 hv)
    · simp only [map_zero]
      exact W.zero_mem
    · intro v w hv hw
      simp only [map_add]
      exact W.add_mem hv hw
  rcases h.irred W hinv with hbot | htop
  · exfalso
    have hn : 2 ≤ n := by have := h.four_le; omega
    apply h.lineA_ne_bot (isoVec_ne_zero hn) (isoVec_isotropic hn)
    rw [eq_bot_iff, ← hbot]
    exact le_iSup (fun y : IsoVec n => lineA ρ y.1) ⟨_, isoVec_ne_zero hn, isoVec_isotropic hn⟩
  · exact htop

omit [FiniteDimensional (ZMod 2) V] in
theorem inf_lineA_eq_bot_of_smul (g : SUid frob n) {x y : Fin n → K} (hx : herm frob x x = 0)
    (hy : herm frob y y = 0) (hg : lineA ρ (g • x) ⊓ lineA ρ (g • y) = ⊥) :
    lineA ρ x ⊓ lineA ρ y = ⊥ := by
  have hinj : Function.Injective (rs ρ g : V →ₗ[ZMod 2] V) := (rs ρ g).injective
  have hmap := Submodule.map_inf (rs ρ g : V →ₗ[ZMod 2] V) (p := lineA ρ x) (q := lineA ρ y)
    hinj
  rw [map_lineA g hx, map_lineA g hy, hg] at hmap
  rw [eq_bot_iff]
  intro v hv
  have hv' := Submodule.mem_map_of_mem (f := (rs ρ g : V →ₗ[ZMod 2] V)) hv
  rw [hmap, Submodule.mem_bot] at hv'
  rw [Submodule.mem_bot]
  exact hinj (by rw [hv', map_zero])

end ZSHyp

namespace ZSHyp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : PG (2 + 2) →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V} (h : ZSHyp (2 + 2) q ρ)
include h

theorem all_bad {y₀ : Fin 2 → K} (hy₀0 : y₀ ≠ 0) (hy₀ : herm frob y₀ y₀ = 0)
    (hbad : lineA ρ (ι 2 y₀) ≤ lineA ρ (v₀ 2) ⊔ lineA ρ (u₀ 2)) {a b w : Fin (2 + 2) → K}
    (ha0 : a ≠ 0) (ha : herm frob a a = 0) (hb : herm frob b b = 0) (hab : herm frob a b = 1)
    (hw0 : w ≠ 0) (hw : herm frob w w = 0) (haw : herm frob a w = 0)
    (hbw : herm frob b w = 0) : lineA ρ w ≤ lineA ρ a ⊔ lineA ρ b := by
  obtain ⟨g, hga, hgb⟩ := exists_smul_eq_hyp (n := 2) (by norm_num) ha0 ha hb hab
  have hv : herm frob (v₀ 2) (g • w) = 0 := by rw [← hga, herm_smul_smul, haw]
  have hu : herm frob (u₀ 2) (g • w) = 0 := by rw [← hgb, herm_smul_smul, hbw]
  set z := π 2 (g • w) with hzdef
  have hgw : g • w = ι 2 z := by
    have e := decomp (g • w)
    rw [hv, hu, zero_smul, zero_smul, zero_add, zero_add] at e
    exact e
  have hz : herm frob z z = 0 := by rw [← herm_ι_ι, ← hgw, herm_smul_smul, hw]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hw0
    rw [← smul_left_cancel_iff g, hgw, h0, map_zero, smul_zero]
  have hy₀' : herm frob (ι 2 y₀) (ι 2 y₀) = 0 := by rw [herm_ι_ι]; exact hy₀
  have hbadz : lineA ρ (ι 2 z) ≤ lineA ρ (v₀ 2) ⊔ lineA ρ (u₀ 2) := by
    by_cases hyz : herm frob y₀ z = 0
    · obtain ⟨c, hc⟩ := perp_two hy₀0 hy₀ hyz
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact hz0 hc
      rw [hc, map_smul, lineA_smul hy₀' hc0]
      exact hbad
    · exact h.le_of_le_of_herm_ne_zero v₀_ne_zero herm_v₀_v₀ u₀_ne_zero herm_u₀_u₀
        herm_v₀_u₀_ne_zero hy₀' (herm_v₀_ι _) (herm_u₀_ι _) (by rw [herm_ι_ι]; exact hz)
        (herm_v₀_ι _) (herm_u₀_ι _) (by rw [herm_ι_ι]; exact hyz) hbad
  have e1 : g⁻¹ • v₀ 2 = a := by rw [← hga, inv_smul_smul]
  have e2 : g⁻¹ • u₀ 2 = b := by rw [← hgb, inv_smul_smul]
  have hmap := map_vH (ρ := ρ) g⁻¹ (herm_v₀_v₀ (n := 2)) (herm_u₀_u₀ (n := 2))
  rw [e1, e2] at hmap
  have hgw' : herm frob (g • w) (g • w) = 0 := by rw [herm_smul_smul, hw]
  rw [← hmap, ← inv_smul_smul g w, ← map_lineA g⁻¹ hgw', hgw]
  exact Submodule.map_mono hbadz

noncomputable abbrev XU (ρ : PG (2 + 2) →* (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V :=
  lineA ρ (vecK ![0, 1, 1, 0]) ⊔ lineA ρ (vecK ![0, 1, F4.ω, 0]) ⊔ lineA ρ (vecK ![1, 0, 1, 0])

omit h [FiniteDimensional (ZMod 2) V] in
theorem lineA_gS_le {s : Fin 4 → F4} (hs : s ∈ gS) : lineA ρ (vecK s) ≤ XU ρ := by
  simp only [gS, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

omit h [FiniteDimensional (ZMod 2) V] in
theorem wordElt_apply_mem_XU {l : List (Fin 4 → F4)} (hl : ∀ x ∈ l, x ∈ gS) {v : V}
    (hv : v ∈ XU ρ) : rs ρ (wordElt l) v ∈ XU ρ := by
  induction l with
  | nil => simpa [wordElt] using hv
  | cons x l ih =>
    rw [wordElt, map_mul, LinearEquiv.mul_apply]
    have hw := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    set w := rs ρ (wordElt l) v
    rw [rs_tvU, show ρ (tq (vecK x)) w = (ρ (tq (vecK x)) w - w) + w by abel]
    exact (XU ρ).add_mem (lineA_gS_le (hl x List.mem_cons_self) (sub_mem_commSpace _ _)) hw

omit h [FiniteDimensional (ZMod 2) V] in
theorem lineA_word_le {l : List (Fin 4 → F4)} (hl : l ∈ words2) {s : Fin 4 → F4} (hs : s ∈ gS) :
    lineA ρ (vecK (wordApply l s)) ≤ XU ρ := by
  have hiso : ∀ x ∈ l, herm4 x x = 0 := fun x hx => (gS_spec x (words2_spec l hl x hx)).1
  rw [← wordElt_smul l hiso, ← map_lineA _ (herm_vecK_self (gS_spec s hs).1)]
  rintro _ ⟨v, hv, rfl⟩
  exact wordElt_apply_mem_XU (words2_spec l hl) (lineA_gS_le hs hv)

omit [FiniteDimensional (ZMod 2) V] h in
theorem lineA_le_XU (hall : ∀ a b w : Fin (2 + 2) → K, a ≠ 0 → herm frob a a = 0 →
      herm frob b b = 0 → herm frob a b = 1 → w ≠ 0 → herm frob w w = 0 →
      herm frob a w = 0 → herm frob b w = 0 → lineA ρ w ≤ lineA ρ a ⊔ lineA ρ b)
    (x : IsoVec (2 + 2)) : lineA ρ x.1 ≤ XU ρ := by
  have hU : ∀ p : Fin (2 + 2) → F4, p ≠ 0 → herm4 p p = 0 → p 3 = 0 →
      lineA ρ (vecK p) ≤ XU ρ := by
    intro p hp0 hp hp3
    obtain ⟨s, hs, l, hl, c, hc, he⟩ := U_points_spec p hp0 hp hp3
    have hc0 : c ≠ 0 := by
      simp only [units4, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> decide
    have := lineA_word_le (ρ := ρ) hl hs
    rwa [he, vecK_smul, lineA_smul (herm_vecK_self hp) ((map_ne_zero eF4).2 hc0)] at this
  set p := fun i => eF4.symm (x.1 i) with hp
  have hxp : x.1 = vecK p := eq_vecK x.1
  have hp0 : p ≠ 0 := fun h0 => x.2.1 (by rw [hxp, h0]; funext i; simp [vecK])
  have hpp : herm4 p p = 0 := herm4_eq_zero (by rw [← hxp]; exact x.2.2)
  rw [hxp]
  by_cases hp3 : p 3 = 0
  · exact hU p hp0 hpp hp3
  · obtain ⟨a, ha, b, hb, hab, hpa, hpb⟩ := pairs_spec p hpp hp3
    obtain ⟨haa, ha3, ha0⟩ := U9_spec a ha
    obtain ⟨hbb, hb3, hb0⟩ := U9_spec b hb
    set μ := eF4 (herm4 a b) with hμ
    have hμ0 : μ ≠ 0 := (map_ne_zero eF4).2 hab
    set b' := μ⁻¹ • vecK b with hb'
    have hb'b' : herm frob b' b' = 0 := herm_smul_smul_self (herm_vecK_self hbb) _
    have hab' : herm frob (vecK a) b' = 1 := by
      rw [hb', herm_smul_right, herm_vecK, ← hμ, inv_mul_cancel₀ hμ0]
    have hle := hall (vecK a) b' (vecK p) (vecK_ne_zero ha0) (herm_vecK_self haa) hb'b' hab'
      (vecK_ne_zero hp0) (herm_vecK_self hpp)
      (by rw [herm_conj frob frob_frob, herm_vecK, hpa, map_zero, map_zero])
      (by rw [hb', herm_smul_left, herm_conj frob frob_frob, herm_vecK, hpb, map_zero,
        map_zero, mul_zero])
    rw [hb', lineA_smul (herm_vecK_self hbb) (inv_ne_zero hμ0)] at hle
    exact hle.trans (sup_le (hU a ha0 haa ha3) (hU b hb0 hbb hb3))

theorem finrank_XU_le : finrank (ZMod 2) (XU ρ) ≤ 6 := by
  have h2 : ∀ s ∈ gS, finrank (ZMod 2) (lineA ρ (vecK s)) = 2 := fun s hs =>
    h.finrank_lineA (vecK_ne_zero (gS_spec s hs).2.2) (herm_vecK_self (gS_spec s hs).1)
  have e1 := h2 ![0, 1, 1, 0] (by simp [gS])
  have e2 := h2 ![0, 1, F4.ω, 0] (by simp [gS])
  have e3 := h2 ![1, 0, 1, 0] (by simp [gS])
  refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
  have := Submodule.finrank_add_le_finrank_add_finrank (lineA ρ (vecK ![0, 1, 1, 0]))
    (lineA ρ (vecK ![0, 1, F4.ω, 0]))
  omega

theorem false_of_all_bad (hall : ∀ a b w : Fin (2 + 2) → K, a ≠ 0 → herm frob a a = 0 →
      herm frob b b = 0 → herm frob a b = 1 → w ≠ 0 → herm frob w w = 0 →
      herm frob a w = 0 → herm frob b w = 0 → lineA ρ w ≤ lineA ρ a ⊔ lineA ρ b) : False := by
  have htop := h.iSup_lineA_eq_top
  have hle : (⨆ x : IsoVec (2 + 2), lineA ρ x.1) ≤ XU ρ := iSup_le (lineA_le_XU hall)
  rw [htop] at hle
  have h1 := Submodule.finrank_mono hle
  rw [finrank_top, h.finrank_eq] at h1
  have := h.finrank_XU_le
  omega

theorem inf_lineA_eq_bot_of_perp_four {x y : Fin (2 + 2) → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (hy : herm frob y y = 0) (hxy : herm frob x y = 0)
    (hyx : ∀ c : K, y ≠ c • x) : lineA ρ x ⊓ lineA ρ y = ⊥ := by
  obtain ⟨g, hgx, hgv, hgu⟩ := exists_std_pair (m := 2) le_rfl hx0 hx hxy hyx
  set y₀ := π 2 (g • y) with hy₀
  have hgy : g • y = ι 2 y₀ := by
    have e := decomp (g • y)
    rw [hgv, hgu, zero_smul, zero_smul, zero_add, zero_add] at e
    exact e
  have hy₀iso : herm frob y₀ y₀ = 0 := by rw [← herm_ι_ι, ← hgy, herm_smul_smul, hy]
  have hy₀0 : y₀ ≠ 0 := by
    intro h0
    apply hyx 0
    rw [zero_smul, ← smul_left_cancel_iff g, hgy, h0, map_zero, smul_zero]
  refine inf_lineA_eq_bot_of_smul g hx hy ?_
  rw [hgx, hgy]
  have hε0 : ι 2 y₀ ≠ 0 := ι_ne_zero' hy₀0
  have hεi : herm frob (ι 2 y₀) (ι 2 y₀) = 0 := by rw [herm_ι_ι]; exact hy₀iso
  rcases h.inf_eq_bot_or_le v₀_ne_zero herm_v₀_v₀ u₀_ne_zero herm_u₀_u₀ herm_v₀_u₀_ne_zero
      hε0 hεi (herm_v₀_ι _) (herm_u₀_ι _) with hg | hb
  · rw [eq_bot_iff, ← hg]
    exact fun v hv => Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hv).2,
      Submodule.mem_sup_left (Submodule.mem_inf.1 hv).1⟩
  · exact (h.false_of_all_bad fun a b w ha0 ha hb' hab hw0 hw haw hbw =>
      h.all_bad hy₀0 hy₀iso hb ha0 ha hb' hab hw0 hw haw hbw).elim

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
