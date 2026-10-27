module

public import CFSG.GH74.GLS.C3.Layer2.L5C5c
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5c
public import CFSG.GH74.GLS.C3.Layer2.L5C5dInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5dInputs
public import Certificates.Certificate5051
public import Certificates.Certificate5065
public import Certificates.Certificate5066
public import Certificates.Certificate5067

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

@[irreducible] def R1Idx : List Nat :=
  (List.range 128).filter fun i => decide (Sh0L.getD i 1 ∈ R1L)

theorem mem_RIdx {i : Nat} (hi : i < 128) :
    i ∈ RIdx ↔ ((dec0 i : ↥Sh0) : Perm (Fin 16)) ∈ RsubP0 := by
  rw [RIdx, List.mem_filter, mem_RsubP0, dec0_val]
  simp [hi]

theorem mem_R1Idx {i : Nat} (hi : i < 128) :
    i ∈ R1Idx ↔ ((dec0 i : ↥Sh0) : Perm (Fin 16)) ∈ R1subP := by
  rw [R1Idx, List.mem_filter, mem_R1subP, dec0_val]
  simp [hi]

theorem lt_of_mem_RIdx {i : Nat} (h : i ∈ RIdx) : i < 128 := by
  rw [RIdx, List.mem_filter, List.mem_range] at h
  exact h.1

theorem lt_of_mem_R1Idx {i : Nat} (h : i ∈ R1Idx) : i < 128 := by
  rw [R1Idx, List.mem_filter, List.mem_range] at h
  exact h.1

theorem mem_invL {i : Nat} : i ∈ invL ↔ i < 128 ∧ mt0.getD (i * 128 + i) 0 = 0 := by
  rw [invL, List.mem_filter, List.mem_range]
  simp

@[expose] def gH (k : Nat) : ↥Sh0 := dec0 (gI.getD k 0)

theorem genChk_true : genChk = true :=
  Certificates.certificate5067.1

theorem gH_sq
    (k : Nat) : gH k * gH k = 1 := by
  by_cases hk : k < 3
  · have h := genChk_true
    simp only [genChk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq] at h
    have h1 := h.1.1 k hk
    unfold gH
    rw [← dec0_mul (gI_lt k) (gI_lt k), h1, dec0_zero]
  · have : gI.getD k 0 = 0 := by
      rw [getD_of_ge (by simp [gI]; omega)]
    unfold gH
    rw [this, dec0_zero, mul_one]

theorem zc_ne : zc ≠ 0 := by
  have h := genChk_true
  simp only [genChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem zc_lt : zc < 128 := by
  have h := genChk_true
  simp only [genChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem classifyChk_true : classifyChk = true :=
  Certificates.certificate5067.2.1

theorem dec0_eq_evH
    {j : Nat} (hj : j < 128) : dec0 j = evH gH (Wd.getD j []) := by
  have h := dec0_evI (x := gI) gI_lt (Wd.getD j [])
  rw [Wd_eval hj] at h
  exact h

theorem map_dec0
    (f : ↥Sh0 →* ↥Sh0) {x : List Nat} (hx : ∀ k, x.getD k 0 < 128)
    (hxf : ∀ k, dec0 (x.getD k 0) = f (gH k)) {j : Nat} (hj : j < 128) :
    f (dec0 j) = dec0 (evI x (Wd.getD j [])) := by
  rw [dec0_eq_evH hj, evH_map f gH, dec0_evI hx]
  congr 1
  funext k
  exact (hxf k).symm

theorem hom_ext_gens
    (f f' : ↥Sh0 →* ↥Sh0) (h : ∀ k, f (gH k) = f' (gH k)) (a : ↥Sh0) :
    f a = f' a := by
  obtain ⟨j, hj, rfl⟩ := dec0_surj a
  rw [dec0_eq_evH hj, evH_map f, evH_map f']
  congr 1
  funext k
  exact h k

theorem gH_ge
    {k : Nat} (hk : 3 ≤ k) : gH k = 1 := by
  have : gI.getD k 0 = 0 := getD_of_ge (by simp [gI]; omega)
  unfold gH
  rw [this, dec0_zero]

theorem exists_imgs
    (γ : ↥Sh0 ≃* ↥Sh0) :
    ∃ x0 x1 x2 : Nat, x0 < 128 ∧ x1 < 128 ∧ x2 < 128 ∧
      (∀ k, dec0 (([x0, x1, x2] : List Nat).getD k 0) = γ (gH k)) := by
  obtain ⟨x0, h0, e0⟩ := dec0_surj (γ (gH 0))
  obtain ⟨x1, h1, e1⟩ := dec0_surj (γ (gH 1))
  obtain ⟨x2, h2, e2⟩ := dec0_surj (γ (gH 2))
  refine ⟨x0, x1, x2, h0, h1, h2, fun k => ?_⟩
  match k with
  | 0 => exact e0
  | 1 => exact e1
  | 2 => exact e2
  | k + 3 =>
    have : ([x0, x1, x2] : List Nat).getD (k + 3) 0 = 0 := getD_of_ge (by simp)
    rw [this, dec0_zero, show gH (k + 3) = 1 from gH_ge (by omega), map_one]

theorem lt_three {x0 x1 x2 : Nat} (h0 : x0 < 128) (h1 : x1 < 128) (h2 : x2 < 128) (k : Nat) :
    ([x0, x1, x2] : List Nat).getD k 0 < 128 := by
  match k with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | k + 3 => rw [getD_of_ge (by simp)]; norm_num

theorem gamGenChk_true : gamGenChk = true :=
  Certificates.certificate5067.2.2

theorem gam_gen
    (m : Fin 4) {k : Nat} (hk : k < 3) :
    gam m (gH k) = dec0 ((xsData.getD m.val []).getD k 0) := by
  have h := gamGenChk_true
  simp only [gamGenChk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  unfold gH
  rw [gam_dec0 m (gI_lt k), h m.val m.2 k hk]

theorem x_facts
    (γ : ↥Sh0 ≃* ↥Sh0)
    (hmv : ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 ∧ (γ r : Perm (Fin 16)) ∉ RsubP0)
    (x : List Nat) (hxlt : ∀ k, x.getD k 0 < 128) (hxg : ∀ k, dec0 (x.getD k 0) = γ (gH k)) :
    evI x (Wd.getD zc []) ≠ 0 ∧ (∀ r ∈ relsL, evI x r.1 = evI x r.2) ∧
      (RIdx.any fun r => !decide (evI x (Wd.getD r []) ∈ RIdx)) = true := by
  have hword : ∀ {j : Nat}, j < 128 → γ (dec0 j) = dec0 (evI x (Wd.getD j [])) := fun hj =>
    map_dec0 γ.toMonoidHom hxlt hxg hj
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have e := hword zc_lt
    rw [h0, dec0_zero] at e
    have : dec0 zc = dec0 0 := by
      apply γ.injective
      rw [e, dec0_zero, map_one]
    exact zc_ne (dec0_inj zc_lt (by norm_num) this)
  · intro r hr
    have e1 := dec0_evI gI_lt r.1
    have e2 := dec0_evI gI_lt r.2
    rw [rels_eval r hr] at e1
    have h2 : evH gH r.1 = evH gH r.2 := e1.symm.trans e2
    have h3 : evH (fun k => dec0 (x.getD k 0)) r.1 = evH (fun k => dec0 (x.getD k 0)) r.2 := by
      have e3 := evH_map γ.toMonoidHom gH r.1
      have e4 := evH_map γ.toMonoidHom gH r.2
      have : (fun k => dec0 (x.getD k 0)) = (fun k => γ.toMonoidHom (gH k)) := funext hxg
      rw [this, ← e3, ← e4, h2]
    rw [← dec0_evI hxlt, ← dec0_evI hxlt] at h3
    exact dec0_inj (evI_lt hxlt _) (evI_lt hxlt _) h3
  · obtain ⟨r, hrR, hrγ⟩ := hmv
    obtain ⟨ri, hri, rfl⟩ := dec0_surj r
    have hriR : ri ∈ RIdx := (mem_RIdx hri).2 hrR
    rw [List.any_eq_true]
    refine ⟨ri, hriR, ?_⟩
    rw [Bool.not_eq_true', decide_eq_false_iff_not]
    intro hmem
    apply hrγ
    rw [hword hri]
    exact (mem_RIdx (evI_lt hxlt _)).1 hmem

theorem pair_of
    (γ : ↥Sh0 ≃* ↥Sh0) (u : ↥Sh0) (hsq : ∀ h, γ (γ h) = u * h * u⁻¹)
    (hfix : γ u = u) (x : List Nat) (hxlt : ∀ k, x.getD k 0 < 128)
    (hxg : ∀ k, dec0 (x.getD k 0) = γ (gH k)) {ui : Nat} (hui : ui < 128) (hu : dec0 ui = u) :
    autPairOK x ui = true := by
  have hword : ∀ {j : Nat}, j < 128 → γ (dec0 j) = dec0 (evI x (Wd.getD j [])) := fun hj =>
    map_dec0 γ.toMonoidHom hxlt hxg hj
  simp only [autPairOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨?_, fun k _ => ?_⟩
  · apply dec0_inj (evI_lt hxlt _) hui
    rw [← hword hui, hu, hfix]
  · apply dec0_inj (evI_lt hxlt _) (conjI_lt hui (gI_lt k))
    rw [← hword (hxlt k), hxg k, hsq, dec0_conjI hui (gI_lt k), hu]
    rfl

theorem classify_core
    (γ : ↥Sh0 ≃* ↥Sh0) (u : ↥Sh0) (x : List Nat)
    (hxlt : ∀ k, x.getD k 0 < 128) (hxg : ∀ k, dec0 (x.getD k 0) = γ (gH k)) {ui : Nat}
    (hui : ui < 128) (hu : dec0 ui = u) (ht : twistOK x ui = true) :
    ∃ (m : Fin 4) (h₀ : ↥Sh0), (∀ h, h₀ * γ h * h₀⁻¹ = gam m h) ∧
      h₀ * γ h₀ * u = dec0 (ssData.getD m.val 0) := by
  have hword : ∀ {j : Nat}, j < 128 → γ (dec0 j) = dec0 (evI x (Wd.getD j [])) := fun hj =>
    map_dec0 γ.toMonoidHom hxlt hxg hj
  simp only [twistOK, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_range] at ht
  obtain ⟨m, hm, hh, hhlt, hk, hmul⟩ := ht
  refine ⟨⟨m, hm⟩, dec0 hh, ?_, ?_⟩
  · intro h
    let F : ↥Sh0 →* ↥Sh0 := (MulAut.conj (dec0 hh)).toMonoidHom.comp γ.toMonoidHom
    let G : ↥Sh0 →* ↥Sh0 := (gam ⟨m, hm⟩).toMonoidHom
    have hFG : ∀ k, F (gH k) = G (gH k) := by
      intro k
      by_cases hk3 : k < 3
      · have e1 : F (gH k) = dec0 hh * dec0 (x.getD k 0) * (dec0 hh)⁻¹ := by
          show dec0 hh * γ (gH k) * (dec0 hh)⁻¹ = _
          rw [hxg k]
        rw [e1, ← dec0_conjI hhlt (hxlt k), hk k hk3]
        exact (gam_gen ⟨m, hm⟩ hk3).symm
      · rw [gH_ge (by omega)]
        simp only [map_one]
    exact hom_ext_gens F G hFG h
  · rw [hword hhlt, ← hmul]
    rw [dec0_mul (mt0_lt hhlt (evI_lt hxlt _)) hui, dec0_mul hhlt (evI_lt hxlt _), hu]

theorem classify_sound
    (γ : ↥Sh0 ≃* ↥Sh0) (u : ↥Sh0)
    (hsq : ∀ h, γ (γ h) = u * h * u⁻¹) (hfix : γ u = u)
    (hmv : ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 ∧ (γ r : Perm (Fin 16)) ∉ RsubP0) :
    ∃ (m : Fin 4) (h₀ : ↥Sh0), (∀ h, h₀ * γ h * h₀⁻¹ = gam m h) ∧
      h₀ * γ h₀ * u = dec0 (ssData.getD m.val 0) := by
  obtain ⟨x0, x1, x2, hx0, hx1, hx2, hxg⟩ := exists_imgs γ
  have hxlt := lt_three hx0 hx1 hx2
  obtain ⟨hz, hrel, hmvB⟩ := x_facts γ hmv _ hxlt hxg
  have hinv : ∀ {y : Nat}, y < 128 → ∀ {k : Nat}, dec0 y = γ (gH k) → y ∈ invL := by
    intro y hy k hk
    rw [mem_invL]
    refine ⟨hy, dec0_inj (mt0_lt hy hy) (by norm_num) ?_⟩
    rw [dec0_mul hy hy, hk, ← map_mul, gH_sq, map_one, dec0_zero]
  obtain ⟨ui, hui, rfl⟩ := dec0_surj u
  have hc := classifyChk_true
  simp only [classifyChk, List.all_eq_true] at hc
  have hc' := hc x0 (hinv hx0 (hxg 0)) x1 (hinv hx1 (hxg 1)) x2 (hinv hx2 (hxg 2))
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at hc'
  rcases hc' with ((hA | hB) | hC) | hD
  · exact absurd (of_decide_eq_true hA) hz
  · rw [Bool.not_eq_true'] at hB
    exact absurd (List.all_eq_true.2 fun r hr => decide_eq_true (hrel r hr)) (by simp [hB])
  · rw [Bool.not_eq_true'] at hC
    rw [hmvB] at hC
    exact absurd hC (by simp)
  · have hD' := List.all_eq_true.1 hD ui (List.mem_range.2 hui)
    rw [pair_of γ _ hsq hfix _ hxlt hxg hui rfl] at hD'
    simp only [Bool.not_true, Bool.false_or] at hD'
    exact classify_core γ _ _ hxlt hxg hui rfl hD'

end CFSG.GH74.GLS.C3.Layer2.L5
