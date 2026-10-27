module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWHom
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWSinger
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBMove
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBRad
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBMoveModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem exists_mulAut_map_eq_pointRadical_of_five_le {n : ℕ} {K : Type*} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 5 ≤ n) {z : LinearFlag.projectiveSL n K}
    (hz : IsInvolutionClass 1 z) {R : Subgroup (LinearFlag.projectiveSL n K)}
    (hRz : R ≤ centralizer {z})
    (hRn : centralizer {z} ≤ normalizer (R : Set (LinearFlag.projectiveSL n K)))
    (hRc : Nat.card R = 2 ^ (n - 1)) :
    ∃ (α : MulAut (LinearFlag.projectiveSL n K)) (d : Fin n),
      R.map α.toMonoidHom = pointRadical d := by
  obtain ⟨c, d, h | h⟩ := exists_conj_map_eq_pointRadical_or_dualAut hK hn hz hRz hRn hRc
  · exact ⟨MulAut.conj c, d, h⟩
  · exact ⟨LinearFlag.dualAut n K * MulAut.conj c, d, by rw [← h, Subgroup.map_map]; rfl⟩

theorem linearTwoMovesTAtInput_of_five_le {n₀ : ℕ} (hn : 5 ≤ n₀) : LinearTwoMovesTAtInput n₀ := by
  intro G _ _ L hset K _ _ hK e t ht hKt c
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  set V₁ : Subgroup G := modelToG e (pointRadical (K := K) c) with hV₁
  have hV₁L : V₁ ≤ L := modelToG_le e _
  have hV₁2 : ∀ v ∈ V₁, v * v = 1 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hv
    rw [← L.coe_mul, ← map_mul, pointRadOn_mul_self c _ ha, map_one, L.coe_one]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin n₀)) := by simp
  have hV₁c : Nat.card V₁ = 2 ^ (n₀ - 1) := by
    rw [hV₁, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v₀ ∈ pointRadical (K := K) c, v₀ ≠ 1 := by
    obtain ⟨v, hv, hv1⟩ := exists_mem_not_mem_finset (V := V₁) (S := {1})
      (by rw [hV₁c, Finset.card_singleton]; exact Nat.one_lt_two_pow (by omega))
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hv
    refine ⟨a, ha, fun h => hv1 ?_⟩
    rw [h, map_one, L.coe_one, Finset.mem_singleton]
  obtain ⟨x, z, hxz, hz, -, ⟨hxzL, hxzc⟩, hact⟩ :=
    exists_conj_eq_mul_transvection_twoSided_two hset (by omega) hK e htC ht
  have hab : (⟨0, by omega⟩ : Fin n₀) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨c₁, hc₁⟩ := exists_conj_eq_xab hab hz
  obtain ⟨c₂, hc₂⟩ := exists_conj_eq_xab hab (isInvolutionClass_one_of_mem_pointRadical hv₀ hv₀1)
  set m : L := e.symm (c₂⁻¹ * c₁) with hm
  have hmz : e (m * z * m⁻¹) = v₀ := by
    rw [map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply]
    calc c₂⁻¹ * c₁ * e z * (c₂⁻¹ * c₁)⁻¹ = c₂⁻¹ * (c₁ * e z * c₁⁻¹) * c₂ := by group
      _ = c₂⁻¹ * (c₂ * v₀ * c₂⁻¹) * c₂ := by rw [hc₁, hc₂]
      _ = v₀ := by group
  set z' : G := (m : G) * z * (m : G)⁻¹ with hz'
  set x' : G := x * (m : G)⁻¹ with hx'
  have hmt : (m : G) * t * (m : G)⁻¹ = t := by rw [hLt m m.2]; group
  have hz'L : z' ∈ L := mul_mem (mul_mem m.2 z.2) (inv_mem m.2)
  have hz'm : (⟨z', hz'L⟩ : L) = m * z * m⁻¹ := Subtype.ext rfl
  have hez' : e ⟨z', hz'L⟩ = v₀ := by rw [hz'm, hmz]
  have hz'V : z' ∈ V₁ := (mem_modelToG e).2 ⟨v₀, hv₀, by rw [← hez', MulEquiv.symm_apply_apply]⟩
  have hz'1 : z' ≠ 1 := fun h => hv₀1 (by
    rw [← hez']
    have h1 : (⟨z', hz'L⟩ : L) = 1 := Subtype.ext h
    rw [h1, map_one])
  have hxz' : x'⁻¹ * t * x' = t * z' := by
    calc x'⁻¹ * t * x' = (m : G) * (x⁻¹ * t * x) * (m : G)⁻¹ := by rw [hx']; group
      _ = (m : G) * t * (m : G)⁻¹ * ((m : G) * z * (m : G)⁻¹) := by rw [hxz]; group
      _ = t * z' := by rw [hmt]
  have hx'z' : x' * z' * x'⁻¹ = x * z * x⁻¹ := by rw [hx', hz']; group
  have hz'Lx : z' ∈ CFSG.conjugate L x' :=
    SeitzQ2.mem_conjugate_iff_conj_mem.2 (by rw [hx'z']; exact hxzL)
  have hact' : ∀ l ∈ CFSG.conjugate L x', t * l * t⁻¹ = z' * l * z'⁻¹ := by
    intro l hl
    have hl' : (m : G)⁻¹ * l * m ∈ CFSG.conjugate L x := by
      rw [SeitzQ2.mem_conjugate_iff_conj_mem] at hl ⊢
      have he : x * ((m : G)⁻¹ * l * m) * x⁻¹ = x' * l * x'⁻¹ := by rw [hx']; group
      rw [he]
      exact hl
    have h := hact _ hl'
    calc t * l * t⁻¹ = ((m : G) * t * (m : G)⁻¹) * l * ((m : G) * t * (m : G)⁻¹)⁻¹ := by
          rw [hmt]
      _ = (m : G) * (t * ((m : G)⁻¹ * l * m) * t⁻¹) * (m : G)⁻¹ := by group
      _ = (m : G) * ((z : G) * ((m : G)⁻¹ * l * m) * (z : G)⁻¹) * (m : G)⁻¹ := by rw [h]
      _ = z' * l * z'⁻¹ := by rw [hz']; group
  set e' : CFSG.conjugate L x' ≃* LinearFlag.projectiveSL n₀ K :=
    (conjugateMulEquiv L x').symm.trans e with he'
  have he'z : e' ⟨z', hz'Lx⟩ = e ⟨x * z * x⁻¹, hxzL⟩ := by
    rw [he', MulEquiv.trans_apply]
    congr 1
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_conjugateMulEquiv]
    show z' = x'⁻¹ * (x * z * x⁻¹) * x'
    rw [← hx'z']
    group
  have hz'c' : IsInvolutionClass 1 (e' ⟨z', hz'Lx⟩) := by rw [he'z]; exact hxzc
  have hz'cL : IsInvolutionClass 1 (e ⟨z', hz'L⟩) := by
    rw [hez']; exact isInvolutionClass_one_of_mem_pointRadical hv₀ hv₀1
  have hM := modelToG_centralizer_eq e ⟨z', hz'L⟩
  have hM' := modelToG_centralizer_eq e' ⟨z', hz'Lx⟩
  have hMp : ⁅L ⊓ centralizer ({z'} : Set G), L ⊓ centralizer ({z'} : Set G)⁆ =
      L ⊓ centralizer ({z'} : Set G) := by
    rw [← hM]
    exact modelToG_perfect e (centralizer_transvection_perfect_two hK (by omega) hz'cL).1
  have hM'p : ⁅CFSG.conjugate L x' ⊓ centralizer ({z'} : Set G),
      CFSG.conjugate L x' ⊓ centralizer ({z'} : Set G)⁆ =
      CFSG.conjugate L x' ⊓ centralizer ({z'} : Set G) := by
    rw [← hM']
    exact modelToG_perfect e' (centralizer_transvection_perfect_two hK (by omega) hz'c').1
  have hOut := isSolvable_outer_of_mulEquiv (by omega : 3 ≤ n₀) e
  have hLxs : ∀ g ∈ CFSG.conjugate L x', g * (x'⁻¹ * t * x') = (x'⁻¹ * t * x') * g := by
    intro g hg
    have h := hLt _ (SeitzQ2.mem_conjugate_iff_conj_mem.1 hg)
    calc g * (x'⁻¹ * t * x') = x'⁻¹ * ((x' * g * x'⁻¹) * t) * x' := by group
      _ = x'⁻¹ * (t * (x' * g * x'⁻¹)) * x' := by rw [h]
      _ = (x'⁻¹ * t * x') * g := by group
  have hMt : L ⊓ centralizer ({z'} : Set G) ≤ centralizer ({t} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.2 (hLt g (Subgroup.mem_inf.1 hg).1)
  have hMs : L ⊓ centralizer ({z'} : Set G) ≤ centralizer ({x'⁻¹ * t * x'} : Set G) := by
    intro g hg
    obtain ⟨hgL, hgz⟩ := Subgroup.mem_inf.1 hg
    rw [mem_centralizer_singleton_iff, hxz']
    have h1 := hLt g hgL
    have h2 := mem_centralizer_singleton_iff.1 hgz
    calc g * (t * z') = (g * t) * z' := by group
      _ = t * (g * z') := by rw [h1]; group
      _ = t * z' * g := by rw [h2]; group
  have hM't : CFSG.conjugate L x' ⊓ centralizer ({z'} : Set G) ≤ centralizer ({t} : Set G) := by
    intro g hg
    obtain ⟨hgL, hgz⟩ := Subgroup.mem_inf.1 hg
    have h1 := hact' g hgL
    have h2 := mem_centralizer_singleton_iff.1 hgz
    rw [mem_centralizer_singleton_iff]
    have h3 : z' * g * z'⁻¹ = g := by rw [← h2]; group
    rw [h3] at h1
    calc g * t = t * g * t⁻¹ * t := by rw [h1]
      _ = t * g := by group
  have hM's : CFSG.conjugate L x' ⊓ centralizer ({z'} : Set G) ≤
      centralizer ({x'⁻¹ * t * x'} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.2 (hLxs g (Subgroup.mem_inf.1 hg).1)
  have hMLx := std_perfect_le_inf_conjugate hset.standardSetting hOut htC ht x' hMp hMt hMs
  have hM'L := std_perfect_le_inf_conjugate hset.standardSetting hOut htC ht x' hM'p hM't hM's
  have hMM' : L ⊓ centralizer ({z'} : Set G) = CFSG.conjugate L x' ⊓ centralizer ({z'} : Set G) :=
    le_antisymm (le_inf (hMLx.trans inf_le_right) inf_le_right)
      (le_inf (hM'L.trans inf_le_left) inf_le_right)
  have hV₁M : V₁ ≤ L ⊓ centralizer ({z'} : Set G) := le_inf hV₁L fun v hv =>
    mem_centralizer_singleton_iff.2 (mul_comm_of_forall_mul_self_eq_one hV₁2 hv hz'V)
  have hV₁Lx : V₁ ≤ CFSG.conjugate L x' := (hV₁M.trans hMM'.le).trans inf_le_left
  have hMN : L ⊓ centralizer ({z'} : Set G) ≤ normalizer (V₁ : Set G) := by
    rw [← hM]
    apply modelToG_le_normalizer e
    rw [hez']
    exact centralizer_le_normalizer_pointRadical hK hv₀ hv₀1
  set R := (V₁.subgroupOf (CFSG.conjugate L x')).map e'.toMonoidHom with hR
  have hRz : R ≤ centralizer ({e' ⟨z', hz'Lx⟩} : Set (LinearFlag.projectiveSL n₀ K)) := by
    intro r hr
    have hr' := (mem_map_subgroupOf_iff e' V₁).1 hr
    rw [mem_centralizer_singleton_iff]
    have h : e'.symm r * ⟨z', hz'Lx⟩ = ⟨z', hz'Lx⟩ * e'.symm r :=
      Subtype.ext (mul_comm_of_forall_mul_self_eq_one hV₁2 hr' hz'V)
    have h2 := congrArg e' h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  have hRn : centralizer ({e' ⟨z', hz'Lx⟩} : Set (LinearFlag.projectiveSL n₀ K)) ≤
      normalizer (R : Set (LinearFlag.projectiveSL n₀ K)) := by
    intro y hy
    apply mem_normalizer_map_subgroupOf e' V₁
    apply hMN
    rw [hMM', ← hM']
    exact symm_mem_modelToG e' hy
  have hRc : Nat.card R = 2 ^ (n₀ - 1) := by rw [hR, natCard_map_subgroupOf e' hV₁Lx, hV₁c]
  obtain ⟨α, d, hαd⟩ := exists_mulAut_map_eq_pointRadical_of_five_le hK hn hz'c' hRz hRn hRc
  set e'' : CFSG.conjugate L x' ≃* LinearFlag.projectiveSL n₀ K := e'.trans α with he''
  have hV₁d : modelToG e'' (pointRadical (K := K) d) = V₁ := by
    rw [← hαd, he'', modelToG_trans_map, hR, modelToG_map_subgroupOf e' hV₁Lx]
  obtain ⟨hnorm, htrans₀, -, -⟩ := pointRadicalLeviInput n₀ K hK d
  have hL₁'N : modelToG e'' (blockSL (K := K) ({d}ᶜ : Finset (Fin n₀))) ≤
      normalizer (V₁ : Set G) := by
    rw [← hV₁d]
    exact modelToG_le_normalizer e'' hnorm
  have htrans : ∀ v ∈ V₁, ∀ w ∈ V₁, v ≠ 1 → w ≠ 1 →
      ∃ l ∈ modelToG e'' (blockSL (K := K) ({d}ᶜ : Finset (Fin n₀))), l * v * l⁻¹ = w := by
    intro v hv w hw hv1 hw1
    rw [← hV₁d] at hv hw
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e'').1 hv
    obtain ⟨b, hb, rfl⟩ := (mem_modelToG e'').1 hw
    have ha1 : a ≠ 1 := fun h => hv1 (by rw [h, map_one, Subgroup.coe_one])
    have hb1 : b ≠ 1 := fun h => hw1 (by rw [h, map_one, Subgroup.coe_one])
    obtain ⟨B, hB, hBab⟩ := htrans₀ a ha b hb ha1 hb1
    refine ⟨((e''.symm B : CFSG.conjugate L x') : G), symm_mem_modelToG e'' hB, ?_⟩
    rw [← hBab, map_mul, map_mul, map_inv]
    rfl
  obtain ⟨w, hwV, hw⟩ := exists_mem_not_mem_finset (V := V₁) (S := ({1, z'} : Finset G))
    (lt_of_le_of_lt (Finset.card_le_two)
      (by rw [hV₁c]; calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n₀ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hw1 : w ≠ 1 := fun h => hw (by rw [h]; simp)
  have hwz : w ≠ z' := fun h => hw (by rw [h]; simp)
  obtain ⟨l, hl, hlw⟩ := htrans z' hz'V w hwV hz'1 hw1
  have hlLx : l ∈ CFSG.conjugate L x' := modelToG_le e'' _ hl
  have hls : l * (t * z') = (t * z') * l := by
    have h := hLxs l hlLx
    rwa [hxz'] at h
  have hs2 : (t * z') * (t * z') = 1 := by
    rw [← hxz']
    have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
    calc x'⁻¹ * t * x' * (x'⁻¹ * t * x') = x'⁻¹ * (t * t) * x' := by group
      _ = 1 := by rw [ht2]; group
  have hsV : ∀ v ∈ V₁, v * (t * z') = (t * z') * v := by
    intro v hv
    calc v * (t * z') = (v * t) * z' := by group
      _ = t * (v * z') := by rw [hLt v (hV₁L hv)]; group
      _ = t * (z' * v) := by rw [mul_comm_of_forall_mul_self_eq_one hV₁2 hv hz'V]
      _ = t * z' * v := by group
  have hU : V₁ ⊔ zpowers t = V₁ ⊔ zpowers (t * z') := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [zpowers_le]
      have h2 := mul_mem (mem_sup_right (mem_zpowers (t * z')) :
        t * z' ∈ V₁ ⊔ zpowers (t * z')) (inv_mem (mem_sup_left hz'V))
      rwa [mul_inv_cancel_right] at h2
    · refine sup_le le_sup_left ?_
      rw [zpowers_le]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hz'V)
  refine ⟨l, ?_, fun hlt => hwz ?_⟩
  · rw [hU]
    exact mem_normalizer_sup_zpowers hs2 hsV (hL₁'N hl) hls
  ·
    rw [← hlw]
    calc l * z' * l⁻¹ = (l * t * l⁻¹)⁻¹ * (l * (t * z') * l⁻¹) := by group
      _ = t⁻¹ * (t * z') := by rw [hlt, hls]; group
      _ = z' := by group

theorem linearTwoMovesTAtInput_six : LinearTwoMovesTAtInput 6 :=
  linearTwoMovesTAtInput_of_five_le (by norm_num)

theorem linearTwoWOneAtInput_six_of_singer (hX : WOneOfXCardInput 5) : LinearTwoWOneAtInput 6 :=
  linearTwoWOneAtInput_six_of linearTwoMovesTAtInput_six hX

theorem linearTwoWOneAtInput_six : LinearTwoWOneAtInput 6 :=
  linearTwoWOneAtInput_six_of_singer wOneOfXCardInput_five

end CFSG.SeitzReduction.LinearPilot
