module

public import CFSG.LargeExtraspecial.DW2ASpData
public import CFSG.LargeExtraspecial.DW2AGL
public import CFSG.LargeExtraspecial.DW2ASpComb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

section Lin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem conj_apply_eq (f₁ f₂ : V ≃ₗ[ZMod 2] V) {c c' x : V} {a a' : ZMod 2}
    (h1x : f₁ x = x + a' • c') (h2x : f₂ x = x + a • c) (h2c' : f₂ c' = c' + c)
    (h1c : f₁ c = c + c') (h1c' : f₁ c' = c') :
    f₁ (f₂ (f₁ x)) = x + (a + a') • (c + c') := by
  simp only [h1x, map_add, map_smul, h2x, h2c', h1c, h1c']
  linear_combination (norm := module) congrArg (a' • ·) (add_self_zmod2 c')

theorem finrank_le_add_one_of_add_mem [FiniteDimensional (ZMod 2) V]
    {H P : Submodule (ZMod 2) V} (h : ∀ v ∈ P, ∀ v' ∈ P, v ∉ H → v' ∉ H → v + v' ∈ H) :
    finrank (ZMod 2) P ≤ finrank (ZMod 2) H + 1 := by
  by_cases hle : P ≤ H
  · exact (Submodule.finrank_mono hle).trans (Nat.le_succ _)
  obtain ⟨v₀, hv₀P, hv₀H⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  have hsub : P ≤ H ⊔ ZMod 2 ∙ v₀ := by
    intro v hv
    by_cases hvH : v ∈ H
    · exact Submodule.mem_sup_left hvH
    have e : v = (v + v₀) + v₀ := by rw [add_assoc, add_self_zmod2, add_zero]
    rw [e]
    exact add_mem (Submodule.mem_sup_left (h v hv v₀ hv₀P hvH hv₀H))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
  calc finrank (ZMod 2) P ≤ finrank (ZMod 2) (H ⊔ ZMod 2 ∙ v₀ : Submodule (ZMod 2) V) :=
        Submodule.finrank_mono hsub
    _ = finrank (ZMod 2) H + 1 := finrank_sup_span_singleton hv₀H

end Lin

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem Abar_sub_mem_span_of_perp (hWs : ∀ v ∈ spanD S, S.q v = 0) {h : G}
    (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z) {t : S.O}
    (ht : t ∈ Abar S (S.clPre (spanD S)) h) {v : S.Qt} (hv : v ∈ perp S (spanD S)) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ ZMod 2 ∙ S.cl (h * S.z * h⁻¹) := by
  obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
  exact ρ_sub_mem_span_of_mem_perp isMbarInvariant_spanD hDQ_spanD hWs hyQ
    (cl_conj_mem_spanD hyQ) hyz ha.1 hv

theorem eq_of_forall_spanD (hWs : ∀ v ∈ spanD S, S.q v = 0) {s t : S.O} (hs : s ∈ XbarD S)
    (ht : t ∈ XbarD S)
    (h : ∀ w ∈ spanD S, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) w = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) :
    s = t := by
  have h1 : s⁻¹ * t = 1 := XbarD_eq_one hWs ((XbarD S).mul_mem ((XbarD S).inv_mem hs) ht)
    fun w hw => by
      change ((s⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w
      rw [← h w hw]
      change ((s⁻¹ * s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
      rw [inv_mul_cancel]
      rfl
  exact inv_mul_eq_one.mp h1

theorem mem_fixD_of_forall_Abar {v : S.Qt} (hv : v ∈ perp S (spanD S))
    (h : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG → k * S.z * k⁻¹ ≠ S.z →
      ∀ t ∈ Abar S (S.clPre (spanD S)) k, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    v ∈ fixD S := by
  refine mem_fixD.mpr ⟨hv, fun t ht => ?_⟩
  induction ht using closure_induction with
  | mem t ht =>
    obtain ⟨k, hkQ, hkz, hkt⟩ := ht
    exact h k hkQ hkz t hkt
  | one => rfl
  | mul x y _ _ hx hy =>
    change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
    rw [hy, hx]
  | inv x _ hx =>
    have e : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
      change ((x⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
      rw [inv_mul_cancel]
      rfl
    rwa [hx] at e

section SpCase

variable (hWs : ∀ v ∈ spanD S, S.q v = 0)
  (hSp : ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
    finrank (ZMod 2) (spanD S) ≤ finrank (ZMod 2) (axisD S h) + 1)
include hWs hSp

theorem Abar_eq_one_or {h : G} (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z)
    {t : S.O} (ht : t ∈ Abar S (S.clPre (spanD S)) h) :
    t = 1 ∨ ∀ w ∈ spanD S, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
      w + spFun hWs (S.cl (h * S.z * h⁻¹)) w • S.cl (h * S.z * h⁻¹) := by
  set c := S.cl (h * S.z * h⁻¹) with hcdef
  have hc : c ∈ spanD S := cl_conj_mem_spanD hyQ
  have hc0 : c ≠ 0 := (cl_ne_zero_iff hyQ).mpr hyz
  obtain ⟨h1, h2, h3⟩ := spRep_spec hWs hc hc0
  have hax : axisD S (spRep hWs c) = axisD S h := axisD_eq_of_cl_eq hWs h1 h2 hyQ hyz h3
  have hfix : ∀ w ∈ spanD S, w ∈ axisD S h → (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w :=
    fun w hw hwa => ((mem_fixIn_Abar_iff hWs hyQ hyz hw).mpr hwa).2 _ ⟨t, ht, rfl⟩
  have hmove : ∀ w ∈ spanD S, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w →
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + c := by
    intro w hw hne
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (Abar_apply_spanD hWs hyQ hyz ht hw)
    rcases zmod2_cases μ with rfl | rfl
    · rw [zero_smul, eq_comm, sub_eq_zero] at hμ
      exact absurd hμ hne
    · rw [one_smul, eq_comm, sub_eq_iff_eq_add] at hμ
      rw [hμ, add_comm]
  by_cases hall : ∀ w ∈ spanD S, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
  · exact Or.inl (XbarD_eq_one hWs (Abar_le_XbarD hyQ hyz ht) hall)
  right
  push Not at hall
  obtain ⟨w₀, hw₀, hne⟩ := hall
  have hw₀a : w₀ ∉ axisD S h := fun hwa => hne (hfix w₀ hw₀ hwa)
  have ht₀ := hmove w₀ hw₀ hne
  intro w hw
  by_cases hwa : w ∈ axisD S h
  · have h0 : spFun hWs c w = 0 := (spFun_eq_zero_iff (hWs := hWs) hc0).mpr (by rwa [hax])
    rw [hfix w hw hwa, h0, zero_smul, add_zero]
  · have h01 : spFun hWs c w = 1 := (zmod2_cases _).resolve_left fun h0 =>
      hwa (by rw [← hax]; exact (spFun_eq_zero_iff (hWs := hWs) hc0).mp h0)
    rw [h01, one_smul]
    have hsum : w + w₀ ∈ axisD S h :=
      add_mem_of_not_mem_hyperplane (axisD_le_spanD h) (hSp h hyQ hyz) hw hw₀ hwa hw₀a
    have e := hfix _ (add_mem hw hw₀) hsum
    rw [map_add, ht₀] at e
    calc (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w
        = ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w + (w₀ + c)) + (w₀ + c) := by
          rw [add_assoc, add_self_zmod2, add_zero]
      _ = w + w₀ + (w₀ + c) := by rw [e]
      _ = w + c := by rw [add_assoc, ← add_assoc w₀, add_self_zmod2, zero_add]

theorem exists_spTrans (hlt : finrank (ZMod 2) (spanD S) < S.width) {c : S.Qt}
    (hc : c ∈ spanD S) (hc0 : c ≠ 0) :
    ∃ t ∈ Abar S (S.clPre (spanD S)) (spRep hWs c),
      ∀ w ∈ spanD S, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + spFun hWs c w • c := by
  obtain ⟨h1, h2, h3⟩ := spRep_spec hWs hc hc0
  obtain ⟨w, hw, hwa⟩ : ∃ w ∈ spanD S, w ∉ axisD S (spRep hWs c) := by
    by_contra hcon
    push Not at hcon
    exact axisD_ne_spanD hWs hlt h1 h2 (le_antisymm (axisD_le_spanD _) hcon)
  have hnf := mt (mem_fixIn_Abar_iff hWs h1 h2 hw).mp hwa
  rw [mem_fixIn] at hnf
  push Not at hnf
  obtain ⟨_, ⟨t, ht, rfl⟩, htw⟩ := hnf hw
  rcases Abar_eq_one_or hWs hSp h1 h2 ht with rfl | hT
  · exact absurd rfl htw
  · refine ⟨t, ht, ?_⟩
    rw [h3] at hT
    exact hT

theorem false_of_sp_of_nondeg [IsSimpleGroup G] (hn : 2 ≤ S.width)
    (hP : NondegWeaklyClosed S)
    (hlt : finrank (ZMod 2) (spanD S) < S.width) {g₀ : G} (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG)
    (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z) : False := by
  classical
  set W := spanD S with hWdef
  have hW := isMbarInvariant_spanD (S := S)
  have hWW : W ≤ perp S W := le_perp_of_forall_q hWs
  have hc₁0 : S.cl (g₀ * S.z * g₀⁻¹) ≠ 0 := (cl_ne_zero_iff hg₀Q).mpr hg₀
  have hW0 : W ≠ ⊥ := fun h => hc₁0 (by
    have h2 : S.cl (g₀ * S.z * g₀⁻¹) ∈ W := cl_conj_mem_spanD hg₀Q
    rw [h, Submodule.mem_bot] at h2
    exact h2)
  have hone : ∀ x : S.Qt, ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x := fun _ => rfl
  have hex : ∀ c : W, ∃ t : S.O, t ∈ XbarD S ∧ ((c : S.Qt) = 0 → t = 1) ∧
      ((c : S.Qt) ≠ 0 → t ∈ Abar S (S.clPre W) (spRep hWs c)) ∧
      ∀ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + spFun hWs c w • (c : S.Qt) := by
    intro c
    by_cases hc0 : (c : S.Qt) = 0
    · refine ⟨1, one_mem _, fun _ => rfl, fun h => absurd hc0 h, fun w _ => ?_⟩
      rw [hc0, spFun_zero_left, zero_smul, add_zero, hone]
    · obtain ⟨h1, h2, -⟩ := spRep_spec hWs c.2 hc0
      obtain ⟨t, ht, ht'⟩ := exists_spTrans hWs hSp hlt c.2 hc0
      exact ⟨t, Abar_le_XbarD h1 h2 ht, fun h => absurd h hc0, fun _ => ht, ht'⟩
  choose T hTX hT1 hTA hTW using hex
  set β := spForm hWs hSp with hβdef
  have hβa : β.IsAlt := spForm_isAlt hWs hSp
  have hnd : β.Nondegenerate := spForm_nondegenerate hWs hSp hlt
  have hnd' : ∀ a : W, a ≠ 0 → ∃ b, β a b = 1 := by
    intro a ha
    by_contra hcon
    push Not at hcon
    exact ha (hnd.1 a fun b => (zmod2_cases _).resolve_right (hcon b))
  let ε : S.Qt → W → ZMod 2 := fun v c => if (T c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v then 0 else 1
  have hTv : ∀ v ∈ perp S W, ∀ c : W,
      (T c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + ε v c • (c : S.Qt) := by
    intro v hv c
    by_cases hc0 : (c : S.Qt) = 0
    · rw [hT1 c hc0, hc0, smul_zero, add_zero, hone]
    obtain ⟨h1, h2, h3⟩ := spRep_spec hWs c.2 hc0
    have hmem := Abar_sub_mem_span_of_perp hWs h1 h2 (hTA c hc0) hv
    rw [h3] at hmem
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
    by_cases hfix : (T c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    · simp only [ε, hfix, ↓reduceIte, zero_smul, add_zero]
    · simp only [ε, hfix, ↓reduceIte, one_smul]
      rcases zmod2_cases μ with rfl | rfl
      · rw [zero_smul, eq_comm, sub_eq_zero] at hμ
        exact absurd hμ hfix
      · rw [one_smul, eq_comm, sub_eq_iff_eq_add, add_comm] at hμ
        exact hμ
  have hεz : ∀ v, ε v 0 = 0 := fun v => by simp only [ε, hT1 0 rfl, hone, ↓reduceIte]
  have hE : ∀ c c' : W, β c c' = 1 →
      (T c : S.Qt ≃ₗ[ZMod 2] S.Qt) c' = c' + c ∧ (T c' : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c + c' ∧
        (T c' : S.Qt ≃ₗ[ZMod 2] S.Qt) c' = c' := by
    intro c c' hcc'
    have h1 : spFun hWs (c : S.Qt) c' = 1 := hcc'
    have h2 : spFun hWs (c' : S.Qt) c = 1 := by rw [spFun_comm hWs c'.2 c.2]; exact h1
    refine ⟨?_, ?_, ?_⟩
    · rw [hTW c _ c'.2, h1, one_smul]
    · rw [hTW c' _ c.2, h2, one_smul]
    · rw [hTW c' _ c'.2, spFun_self hWs c'.2, zero_smul, add_zero]
  have hrel : ∀ c c' : W, β c c' = 1 → T c' * T c * T c' = T (c + c') := by
    intro c c' hcc'
    obtain ⟨e1, e2, e3⟩ := hE c c' hcc'
    refine eq_of_forall_spanD hWs
      ((XbarD S).mul_mem ((XbarD S).mul_mem (hTX c') (hTX c)) (hTX c')) (hTX _) fun w hw => ?_
    have := conj_apply_eq (T c' : S.Qt ≃ₗ[ZMod 2] S.Qt) (T c) (hTW c' w hw) (hTW c w hw) e1 e2 e3
    change (T c' : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T c : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((T c' : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) = _
    rw [this, hTW (c + c') w hw, Submodule.coe_add, spFun_add_left hWs hSp c.2 c'.2 hw]
  have hR : ∀ v ∈ perp S W, ∀ c c' : W, β c c' = 1 → ε v (c + c') = ε v c + ε v c' := by
    intro v hv c c' hcc'
    obtain ⟨e1, e2, e3⟩ := hE c c' hcc'
    have hne : (c : S.Qt) + c' ≠ 0 := by
      intro h0
      have h0' : c + c' = 0 := Subtype.ext h0
      have : β (c + c') c' = β 0 c' := by rw [h0']
      rw [map_add, LinearMap.add_apply, hcc', hβa c', map_zero, LinearMap.zero_apply] at this
      exact one_ne_zero this
    have h1 := conj_apply_eq (T c' : S.Qt ≃ₗ[ZMod 2] S.Qt) (T c) (hTv v hv c') (hTv v hv c)
      e1 e2 e3
    have h2 := congrArg (fun t : S.O => (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) (hrel c c' hcc')
    change (T c' : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T c : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((T c' : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = _ at h2
    rw [h1, hTv v hv (c + c'), Submodule.coe_add] at h2
    exact (smul_left_injective (ZMod 2) hne (add_left_cancel h2)).symm
  have hεadd : ∀ v ∈ perp S W, ∀ v' ∈ perp S W, ∀ c : W, ε (v + v') c = ε v c + ε v' c := by
    intro v hv v' hv' c
    by_cases hc0 : (c : S.Qt) = 0
    · simp only [ε, hT1 c hc0, hone, ↓reduceIte, add_zero]
    have h1 := hTv (v + v') (add_mem hv hv') c
    rw [map_add, hTv v hv c, hTv v' hv' c] at h1
    have h2 : v + v' + (ε v c + ε v' c) • (c : S.Qt) = v + v' + ε (v + v') c • (c : S.Qt) := by
      rw [← h1, add_smul]
      abel
    exact (smul_left_injective (ZMod 2) hc0 (add_left_cancel h2)).symm
  have hfixT : ∀ v ∈ perp S W, (∀ c : W, (c : S.Qt) ≠ 0 → (T c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
      v ∈ fixD S := by
    intro v hv hfix
    refine mem_fixD_of_forall_Abar hv fun k hkQ hkz t ht => ?_
    let c : W := ⟨S.cl (k * S.z * k⁻¹), cl_conj_mem_spanD hkQ⟩
    have hc0 : (c : S.Qt) ≠ 0 := (cl_ne_zero_iff hkQ).mpr hkz
    rcases Abar_eq_one_or hWs hSp hkQ hkz ht with rfl | ht'
    · rfl
    · have : t = T c := eq_of_forall_spanD hWs (Abar_le_XbarD hkQ hkz ht) (hTX c)
        fun w hw => by rw [ht' w hw, hTW c w hw]
      rw [this]
      exact hfix c hc0
  have hgood : ∀ v ∈ perp S W, (∀ c c' : W, IsIsoPair β c c' → defect (ε v) c c' = 0) →
      v ∈ fixD S ⊔ W := by
    intro v hv hD
    obtain ⟨w, hw⟩ := exists_eq_of_defect_eq_zero hnd (hR v hv) (hεz v) hD
    have hvw : v + (w : S.Qt) ∈ fixD S := by
      refine hfixT _ (add_mem hv (hWW w.2)) fun c _ => ?_
      have hβ : β w c = spFun hWs (c : S.Qt) w := by
        rw [spForm_apply, spFun_comm hWs w.2 c.2]
      rw [map_add, hTv v hv c, hTW c w w.2, hw c, hβ, add_add_add_comm, add_self_zmod2,
        add_zero]
    have e : v = (v + w) + w := by rw [add_assoc, add_self_zmod2, add_zero]
    rw [e]
    exact add_mem (Submodule.mem_sup_left hvw) (Submodule.mem_sup_right w.2)
  have hpair : ∀ v ∈ perp S W, v ∉ fixD S ⊔ W → ∀ c c' : W, IsIsoPair β c c' →
      defect (ε v) c c' = 1 := by
    intro v hv hvH c c' hcc'
    by_contra hne
    refine hvH (hgood v hv fun d d' hdd' => ?_)
    rw [defect_eq_of_isIsoPair hβa (hR v hv) hnd' hdd' hcc']
    exact (zmod2_cases _).resolve_right hne
  have hcodim : finrank (ZMod 2) (perp S W) ≤
      finrank (ZMod 2) (fixD S ⊔ W : Submodule (ZMod 2) S.Qt) + 1 := by
    refine finrank_le_add_one_of_add_mem fun v hv v' hv' hvH hv'H => ?_
    refine hgood _ (add_mem hv hv') fun c c' hcc' => ?_
    have hdef : defect (ε (v + v')) c c' = defect (ε v) c c' + defect (ε v') c c' := by
      simp only [defect, hεadd v hv v' hv']
      ring
    rw [hdef, hpair v hv hvH c c' hcc', hpair v' hv' hv'H c c' hcc']
    rfl
  have hTW0 : fixD S ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwT, hwW⟩
    rw [Submodule.mem_bot]
    have h0 : (⟨w, hwW⟩ : W) = 0 := hnd.2 _ fun c => by
      by_cases hc0 : (c : S.Qt) = 0
      · have : c = 0 := Subtype.ext hc0
        rw [this, map_zero, LinearMap.zero_apply]
      have h1 := (mem_fixD.mp hwT).2 (T c) (hTX c)
      rw [hTW c w hwW] at h1
      have h2 : spFun hWs (c : S.Qt) w • (c : S.Qt) = 0 :=
        (add_right_inj w).mp (h1.trans (add_zero w).symm)
      rw [spForm_apply]
      exact (smul_eq_zero.mp h2).resolve_right hc0
    exact congrArg Subtype.val h0
  have hTle : fixD S ≤ perp S W := fun v hv => (mem_fixD.mp hv).1
  exact false_of_sup_ge_of_nondeg hn hP hg₀Q hg₀ hW hWW hW0 hlt isMbarInvariant_fixD hTle hTW0
    hcodim

end SpCase

end CFSG.LargeExtraspecial.DW
