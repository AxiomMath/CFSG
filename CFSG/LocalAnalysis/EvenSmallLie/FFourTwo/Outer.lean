module

public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Classes
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Setup
public import CFSG.LocalAnalysis.EvenSmallLie.FoursGroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.FFourTwo

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
open scoped commutatorElement

theorem dualRoot_vals :
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, 1, 0, 0]) =
      List.ofFn (![0, 0, 1, 0] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![1, 1, 0, 0]) =
      List.ofFn (![0, 0, 1, 1] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![-1, 0, 0, 0]) =
      List.ofFn (![0, 0, 0, -1] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, 0, 1, 0]) =
      List.ofFn (![0, 1, 0, 0] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, 0, 1, 1]) =
      List.ofFn (![1, 1, 0, 0] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, 0, 0, -1]) =
      List.ofFn (![-1, 0, 0, 0] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, 1, 1, 0]) =
      List.ofFn (![0, 1, 2, 0] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, 1, 1, 1]) =
      List.ofFn (![1, 1, 2, 0] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![1, 0, 0, 0]) =
      List.ofFn (![0, 0, 0, 1] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, -1, 0, 0]) =
      List.ofFn (![0, 0, -1, 0] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, 0, 0, 1]) =
      List.ofFn (![1, 0, 0, 0] : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (LieType.Ree.ReeTag.F4.dualRoot ![0, 0, -1, 0]) =
      List.ofFn (![0, -1, 0, 0] : Fin Tag.F4.rank → ℤ) := by
  decide +kernel

theorem decs :
    Cover.Dec ![0, 1, 0, 0] ![1, 1, 0, 0] ![-1, 0, 0, 0] ∧
    Cover.Dec ![0, 0, 1, 0] ![0, 0, 1, 1] ![0, 0, 0, -1] ∧
    Cover.Dec ![0, 1, 1, 0] ![0, 1, 1, 1] ![0, 0, 0, -1] ∧
    Cover.Dec ![0, 1, 2, 0] ![1, 1, 2, 0] ![-1, 0, 0, 0] ∧
    Cover.Dec ![1, 0, 0, 0] ![1, 1, 0, 0] ![0, -1, 0, 0] ∧
    Cover.Dec ![0, 0, 0, 1] ![0, 0, 1, 1] ![0, 0, -1, 0] := by
  refine ⟨Cover.dec_of_ofFn (by decide +kernel), Cover.dec_of_ofFn (by decide +kernel),
    Cover.dec_of_ofFn (by decide +kernel), Cover.dec_of_ofFn (by decide +kernel),
    Cover.dec_of_ofFn (by decide +kernel), Cover.dec_of_ofFn (by decide +kernel)⟩

namespace Cover

variable {K : Type} [Field K] {M : Type*} [Group M] (C : Cover K M)

theorem graph_gU
    {β : M →* M} {φ : adjointGroup .F4 K →* adjointGroup .F4 K}
    (hβ : ∀ m, C.π (β m) = φ (C.π m))
    (hφ : ∀ r, IsRoot .F4 r → φ (xr r) = xr (LieType.Ree.ReeTag.F4.dualRoot r)) :
    β (C.gU 2) = C.gU 1 ∧ β (C.gU 1) = C.gU 2 ∧ β (C.gU 5) = C.gU 8 ∧
      β (C.gU 3) = C.gU 0 ∧ β (C.gU 0) = C.gU 3 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := dualRoot_vals
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := decs
  rw [C.gU_lt (by norm_num : 2 < 24), C.gU_lt (by norm_num : 1 < 24),
    C.gU_lt (by norm_num : 5 < 24), C.gU_lt (by norm_num : 8 < 24),
    C.gU_lt (by norm_num : 3 < 24), C.gU_lt (by norm_num : 0 < 24)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := C.yhat_graph hβ hφ d1 (by rw [eq_of_ofFn v1, eq_of_ofFn v2, eq_of_ofFn v3]; exact d2)
    rwa [eq_of_ofFn v1] at h
  · have h := C.yhat_graph hβ hφ d2 (by rw [eq_of_ofFn v4, eq_of_ofFn v5, eq_of_ofFn v6]; exact d1)
    rwa [eq_of_ofFn v4] at h
  · have h := C.yhat_graph hβ hφ d3 (by rw [eq_of_ofFn v7, eq_of_ofFn v8, eq_of_ofFn v6]; exact d4)
    rwa [eq_of_ofFn v7] at h
  · have h := C.yhat_graph hβ hφ d5
      (by rw [eq_of_ofFn v9, eq_of_ofFn v2, eq_of_ofFn v10]; exact d6)
    rwa [eq_of_ofFn v9] at h
  · have h := C.yhat_graph hβ hφ d6
      (by rw [eq_of_ofFn v11, eq_of_ofFn v5, eq_of_ofFn v12]; exact d5)
    rwa [eq_of_ofFn v11] at h

end Cover

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  (S : Setup G L K)

theorem exists_graph
    {y : G} (hy : y ∈ centralizer ({S.t} : Set G)) (hy2 : y * y = 1)
    (hyM : y ∉ L ⊔ centralizer (L : Set G)) :
    ∃ b : L, ∃ φ : adjointGroup .F4 K →* adjointGroup .F4 K,
      (∀ r, IsRoot .F4 r → φ (xr r) = xr (LieType.Ree.ReeTag.F4.dualRoot r)) ∧
      ∀ (l : L) (hl : (b * y * b⁻¹ : G) * l * (b * y * b⁻¹ : G)⁻¹ ∈ L),
        S.π ⟨(b * y * b⁻¹ : G) * l * (b * y * b⁻¹ : G)⁻¹, hl⟩ = φ (S.π l) := by
  have := S.finite_K
  have := S.charP_K
  set α := S.act ⟨y, hy⟩
  have hα2 : α ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : centralizer ({S.t} : Set G)) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, sq, hy2]; rfl)
    rw [this, map_one]
  have hαo : α ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range :=
    fun h => hyM ((S.act_mem_inner_iff _).1 h)
  obtain ⟨ψ, hψ, -, hm, -⟩ := even_F4_all_outer_involutions_canonical (f := 1) le_rfl K
    (by rw [S.card_field, pow_one]) α hα2 hαo
  obtain ⟨hφR, ⟨x₀, hx₀⟩⟩ := hm 0 rfl
  obtain ⟨b, rfl⟩ := S.π_surjective x₀
  have hbL := S.le_centralizer_t b.2
  have hb : S.act ⟨b, hbL⟩ = ψ := (S.act_of_mem b).trans hx₀
  refine ⟨b, (LieType.Ree.ReeTag.F4.finiteExceptionalAut K ^ 1).toMonoidHom, fun r hr => ?_,
    fun l hl => ?_⟩
  · change (LieType.Ree.ReeTag.F4.finiteExceptionalAut K ^ 1) (xr r) = _
    rw [hφR]
    have := LieType.Ree.ReeTag.finiteReeAut_pinnedX_F4 (K := K) (a := 0) hr 1
    rw [one_pow] at this
    exact this
  · have hy' : (b * y * b⁻¹ : G) ∈ centralizer ({S.t} : Set G) :=
      mul_mem (mul_mem hbL hy) (inv_mem hbL)
    have he : (⟨(b * y * b⁻¹ : G), hy'⟩ : centralizer ({S.t} : Set G)) =
        ⟨b, hbL⟩ * ⟨y, hy⟩ * (⟨b, hbL⟩ : centralizer ({S.t} : Set G))⁻¹ := rfl
    have h1 : S.act ⟨_, hy'⟩ = S.act ⟨b, hbL⟩ * α * (S.act ⟨b, hbL⟩)⁻¹ := by
      rw [he, map_mul, map_mul, map_inv]
    have key : S.act ⟨_, hy'⟩ = LieType.Ree.ReeTag.F4.finiteExceptionalAut K ^ 1 :=
      h1.trans ((congrArg (fun φ' => φ' * α * φ'⁻¹) hb).trans hψ)
    exact (S.act_π ⟨_, hy'⟩ l hl).symm.trans (DFunLike.congr_fun key (S.π l))

theorem pc_facts
    [Group.IsPerfect L] :
    S.cover.gU 1 * S.cover.gU 2 * S.cover.gU 8 =
      S.cover.gU 2 * S.cover.gU 1 * S.cover.gU 5 * S.cover.z ∧
    S.cover.gU 0 * S.cover.gU 3 = S.cover.gU 3 * S.cover.gU 0 ∧
    S.cover.gU 3 * S.cover.gU 0 ≠ 1 ∧ S.cover.gU 3 * S.cover.gU 0 ≠ S.cover.z := by
  set C := S.cover
  have hP := C.pcData
  have e1 := small_spec.2.2.2.2
  obtain ⟨a1, -⟩ := C.nf_mulList_zero (l := [1, 2, 8]) (by simp) hP
  obtain ⟨a2, a3⟩ := C.nf_mulList_zero (l := [2, 1, 5]) (by simp) hP
  obtain ⟨a4, -⟩ := C.nf_mulU a3 (show 2 ^ 24 < 2 ^ 25 by norm_num)
  have h03 : C.gU 0 * C.gU 3 = C.gU 3 * C.gU 0 := by
    have h := hP.rel 0 3 (by norm_num) (by norm_num)
    rw [show cmF 3 0 = 0 by decide +kernel, Pc.nf_zero, mul_one] at h
    calc C.gU 0 * C.gU 3 = C.gU 0 * C.gU 3 * C.gU 0 * C.gU 0 := by
          rw [mul_assoc _ (C.gU 0), C.gU_mul_self (by norm_num), mul_one]
      _ = C.gU 3 * C.gU 0 := by rw [h]
  have h9 : Pc.nf C.gU 9 = C.gU 3 * C.gU 0 := by
    rw [Pc.nf_eq_prod C.gU 25 9 (by norm_num),
      show (List.range 25).filter (fun k => Nat.testBit 9 k) = [0, 3] by decide +kernel]
    simp [h03]
  refine ⟨?_, h03, fun h => ?_, fun h => ?_⟩
  · have := congrArg (Pc.nf C.gU) e1
    rw [a1, a4, a2, Pc.nf_two_pow, C.gU_24] at this
    simpa [mul_assoc] using this
  · rw [← h9, ← Pc.nf_zero C.gU] at h
    exact absurd (C.nf_inj (by norm_num) (by norm_num) h) (by norm_num)
  · rw [← h9, ← C.gU_24, ← Pc.nf_two_pow C.gU 24] at h
    exact absurd (C.nf_inj (by norm_num) (by norm_num) h) (by norm_num)

theorem exists_four
    {y : G} (hy : y ∈ centralizer ({S.t} : Set G))
    (hyM : y ∉ L ⊔ centralizer (L : Set G)) (hyc : IsConj S.t y) :
    ∃ V : Subgroup G, Nat.card V = 4 ∧ V ≤ centralizer ({y} : Set G) ∧
      ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y := by
  have := S.isPerfect
  have hy2 : y * y = 1 := by
    obtain ⟨g, rfl⟩ := isConj_iff.1 hyc
    rw [show g * S.t * g⁻¹ * (g * S.t * g⁻¹) = g * (S.t * S.t) * g⁻¹ by group, S.t_mul_t,
      mul_one, mul_inv_cancel]
  obtain ⟨b, φ, hφ, hπ⟩ := S.exists_graph hy hy2 hyM
  set y' : G := b * y * b⁻¹ with hy'_def
  have hbC := S.le_centralizer_t b.2
  have hy'C : y' ∈ centralizer ({S.t} : Set G) := mul_mem (mul_mem hbC hy) (inv_mem hbC)
  let β : L →* L :=
    { toFun := fun l => ⟨y' * l * y'⁻¹, S.conj_mem_L hy'C l.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l m => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hβ : ∀ m, S.cover.π (β m) = φ (S.cover.π m) := fun m => hπ m _
  have hβv : ∀ l : L, ((β l : L) : G) = y' * l * y'⁻¹ := fun _ => rfl
  obtain ⟨b2, b1, b5, b3, b0⟩ := S.cover.graph_gU hβ hφ
  obtain ⟨hw, h03, hv1, hvz⟩ := S.pc_facts
  set C := S.cover
  have ht : IsConj y' (S.t * y') := by
    have e : β (C.gU 2 * C.gU 1 * C.gU 5) = C.gU 2 * C.gU 1 * C.gU 5 * C.z := by
      rw [map_mul, map_mul, b2, b1, b5, hw]
    set w : G := ((C.gU 2 * C.gU 1 * C.gU 5 : L) : G)
    have e' : y' * w * y'⁻¹ = w * S.t := by
      rw [← hβv, e]; rfl
    refine isConj_iff.2 ⟨w⁻¹, ?_⟩
    calc w⁻¹ * y' * w⁻¹⁻¹ = w⁻¹ * (y' * w * y'⁻¹) * y' := by group
      _ = S.t * y' := by rw [e']; group
  set g3 : G := ((C.gU 3 : L) : G)
  set g0 : G := ((C.gU 0 : L) : G)
  set v : G := g3 * g0 with hv_def
  have hg3 : g3 * g3 = 1 := by
    show ((C.gU 3 * C.gU 3 : L) : G) = 1; rw [C.gU_mul_self (by norm_num)]; rfl
  have hg0 : g0 * g0 = 1 := by
    show ((C.gU 0 * C.gU 0 : L) : G) = 1; rw [C.gU_mul_self (by norm_num)]; rfl
  have h03' : g0 * g3 = g3 * g0 := by
    show ((C.gU 0 * C.gU 3 : L) : G) = ((C.gU 3 * C.gU 0 : L) : G); rw [h03]
  have hb3 : y' * g3 * y'⁻¹ = g0 := by rw [← hβv, b3]
  have hb0 : y' * g0 * y'⁻¹ = g3 := by rw [← hβv, b0]
  have hv2 : v * v = 1 := by
    calc v * v = g3 * (g0 * g3) * g0 := by rw [hv_def]; group
      _ = g3 * g3 * (g0 * g0) := by rw [h03']; group
      _ = 1 := by rw [hg3, hg0, mul_one]
  have htc : ∀ l : L, S.t * l = l * S.t := fun l => by
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 S.tL_mem_center l); exact this.symm
  have htv : S.t * v = v * S.t := htc (C.gU 3 * C.gU 0)
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have htv' : S.t ≠ v := fun h => hvz (Subtype.ext h.symm)
  have hvy : v * y' = y' * v := by
    have : y' * v * y'⁻¹ = v := by
      calc y' * v * y'⁻¹ = (y' * g3 * y'⁻¹) * (y' * g0 * y'⁻¹) := by rw [hv_def]; group
        _ = v := by rw [hb3, hb0, h03']
    calc v * y' = y' * v * y'⁻¹ * y' := by rw [this]
      _ = y' * v := by group
  have hg0i : g0⁻¹ = g0 := inv_eq_of_mul_eq_one_right hg0
  have hcv : IsConj y' (v * y') := by
    refine isConj_iff.2 ⟨g3, ?_⟩
    calc g3 * y' * g3⁻¹ = g3 * (y' * g3 * y'⁻¹)⁻¹ * y' := by group
      _ = v * y' := by rw [hb3, hg0i]
  have hctv : IsConj y' (S.t * v * y') := by
    refine ht.trans (isConj_iff.2 ⟨g3, ?_⟩)
    have hct : g3 * S.t = S.t * g3 := (htc (C.gU 3)).symm
    calc g3 * (S.t * y') * g3⁻¹ = S.t * (g3 * (y' * g3 * y'⁻¹)⁻¹ * y') := by
          rw [← mul_assoc, hct]; group
      _ = S.t * v * y' := by rw [hb3, hg0i, hv_def]; group
  obtain ⟨V, -, hV4, hVc, hVconj⟩ := exists_four_of_pair (N := ⊤) (y := y') S.t_mul_t hv2 htv
    S.t_ne_one hv1' htv' (by
      rintro w (rfl | rfl | rfl)
      · exact ⟨mem_top _, mem_centralizer_singleton_iff.1 hy'C |>.symm, ht.symm⟩
      · exact ⟨mem_top _, hvy, hcv.symm⟩
      · refine ⟨mem_top _, ?_, hctv.symm⟩
        change S.t * v * y' = y' * (S.t * v)
        rw [mul_assoc, hvy, ← mul_assoc, (mem_centralizer_singleton_iff.1 hy'C).symm, mul_assoc])
  have hyy : IsConj y' y :=
    isConj_iff.2 ⟨(b : G)⁻¹, by simp only [hy'_def, Subgroup.coe_inv]; group⟩
  obtain ⟨W, -, hW4, hWc, hWconj⟩ := exists_four_of_isConj (N := ⊤) hyy
    ⟨V, le_top, hV4, hVc, hVconj⟩
  exact ⟨W, hW4, hWc, hWconj⟩

end Setup

end CFSG.EvenSmallLie.FFourTwo
