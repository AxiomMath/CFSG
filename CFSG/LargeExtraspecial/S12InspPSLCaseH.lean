module

public import CFSG.LargeExtraspecial.S12Elim
public import CFSG.LargeExtraspecial.S12InspPSLLbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace PSLPair

variable {g : G} {t : S.O} (P : S.PSLPair g t)

@[expose] noncomputable def H : Submodule (ZMod 2) S.Qt :=
  P.W ⊓ LinearMap.ker (S.q.polarBilin P.c')

theorem H_le : P.H ≤ P.W := inf_le_left

theorem c_mem_H : P.c ∈ P.H := ⟨P.hc, by
  change polar S.q P.c' P.c = 0
  rw [polar_comm]
  exact P.polar_c_c'⟩

theorem c'_notMem_W : P.c' ∉ P.W := fun h => P.c'_ne (by
  have : P.c' ∈ P.W ⊓ P.W' := ⟨h, P.hc'⟩
  rwa [P.inf_eq, Submodule.mem_bot] at this)

theorem eq_of_add_eq {u u' : S.Qt} (hu : u ∈ P.W) (hu' : u' ∈ P.W')
    (h : u + u' = P.c + P.c') : u = P.c ∧ u' = P.c' := by
  have hmem : u - P.c ∈ P.W ⊓ P.W' := by
    refine ⟨P.W.sub_mem hu P.hc, ?_⟩
    have : u - P.c = P.c' - u' := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]
    exact P.W'.sub_mem P.hc' hu'
  rw [P.inf_eq, Submodule.mem_bot, sub_eq_zero] at hmem
  refine ⟨hmem, ?_⟩
  rw [hmem] at h
  exact add_left_cancel h

theorem fix_of_fix_add {x : S.O} (hx : x ∈ S.Xbar12 g)
    (hxa : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (P.c + P.c') = P.c + P.c') :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c ∧ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c' := by
  rw [map_add] at hxa
  exact P.eq_of_add_eq (P.apply_mem hx P.hc) (P.apply_mem' hx P.hc') hxa

theorem conj_eq_of_fix (htX : t ∈ S.Xbar12 g) {x : S.O} (hx : x ∈ S.Xbar12 g)
    (hxc : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c)
    (hxc' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c') : x * t * x⁻¹ = t :=
  P.ext ((S.Xbar12 g).mul_mem ((S.Xbar12 g).mul_mem hx htX) ((S.Xbar12 g).inv_mem hx)) htX
    fun w hw => by rw [P.conj_apply hx hw, hxc, hxc', P.tW w hw]

theorem conj_fix_of_mem_Lbar (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c')
    {x : S.O} (hx : x ∈ S.Xbar12 g) (hL : x * t * x⁻¹ ∈ S.Lbar g) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c ∧ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c' := by
  have hA : IsTypeA S.q ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact s12_isTypeA_conj htA x.2
  obtain ⟨hmem, -⟩ := S.timmesfeld_12_6 haQ hne hL hA
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, commSpace_conj] at hmem
  obtain ⟨v, hv, hxv⟩ := hmem
  change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = _ at hxv
  rw [P.commSpace_eq] at hv
  replace hv : v ∈ span (ZMod 2) {P.c, P.c'} := hv
  rw [mem_span_pair_iff] at hv
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  rcases hv with rfl | rfl | rfl | rfl
  · rw [map_zero] at hxv
    exact absurd hxv.symm ha0
  · exfalso
    apply P.c'_notMem_W
    have h1 : P.c + P.c' ∈ P.W := by
      rw [← ha, ← hxv]
      exact P.apply_mem hx P.hc
    have : P.c' = (P.c + P.c') - P.c := by abel
    rw [this]
    exact P.W.sub_mem h1 P.hc
  · exfalso
    apply P.swap.c'_notMem_W
    have h1 : P.c + P.c' ∈ P.W' := by
      rw [← ha, ← hxv]
      exact P.apply_mem' hx P.hc'
    have : P.c = (P.c + P.c') - P.c' := by abel
    change P.c ∈ P.W'
    rw [this]
    exact P.W'.sub_mem h1 P.hc'
  · rw [ha, map_add] at hxv
    exact P.eq_of_add_eq (P.apply_mem hx P.hc) (P.apply_mem' hx P.hc') hxv

variable {P} in
theorem fix_of_mem_Lbar (haQ : g * S.z * g⁻¹ ∈ S.QG) (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c')
    {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g) (hℓX : ℓ ∈ S.Xbar12 g) :
    (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c ∧ (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c' :=
  P.fix_of_fix_add hℓX (ha ▸ S.s12_Lbar_apply_cl_a haQ hℓ)

theorem polar_a_eq (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') {w : S.Qt} (hw : w ∈ P.W) :
    polar S.q (S.cl (g * S.z * g⁻¹)) w = polar S.q P.c' w := by
  rw [ha, polar_add_left, psl_polar_eq_zero_of_sing P.sing P.hc hw, zero_add]

theorem apply_mem_H {x : S.O} (hx : x ∈ S.Xbar12 g)
    (hxc' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c') {h : S.Qt} (hh : h ∈ P.H) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h ∈ P.H := by
  refine ⟨P.apply_mem hx hh.1, ?_⟩
  change polar S.q P.c' ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) h) = 0
  rw [← hxc', psl_polar_apply_apply]
  exact hh.2

theorem comm_H_le (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') {ℓ : S.O}
    (hℓ : ℓ ∈ S.Lbar g) (hℓX : ℓ ∈ S.Xbar12 g) :
    ∀ h ∈ P.H, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) h - h ∈ span (ZMod 2) {P.c} := by
  refine psl_Lbar_comm_le_of_transitive haQ hne (H := P.H) (c := P.c)
    (L₁ := {ℓ | ℓ ∈ S.Lbar g ∧ ℓ ∈ S.Xbar12 g})
    (K := {k | k ∈ S.Xbar12 g ∧ (k : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = P.c ∧
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c'}) ?_ ?_ (fun ℓ hℓ => hℓ.1)
    (fun ℓ hℓ h hh => P.apply_mem_H hℓ.2 (fix_of_mem_Lbar haQ ha hℓ.1 hℓ.2).2 hh)
    (fun ℓ hℓ => (fix_of_mem_Lbar haQ ha hℓ.1 hℓ.2).1)
    (fun k hk h hh => P.apply_mem_H hk.1 hk.2.2 hh) ?_ ?_ ℓ ⟨hℓ, hℓX⟩
  · intro h hh
    rw [P.polar_a_eq ha hh.1]
    exact hh.2
  · intro v hv hva
    rw [mem_span_singleton_iff] at hva
    rcases hva with rfl | h
    · exact zero_mem _
    · exfalso
      apply P.c'_notMem_W
      have : P.c' = (P.c + P.c') - P.c := by abel
      rw [this, ← ha, ← h]
      exact P.W.sub_mem hv.1 P.hc
  · rintro k ⟨hk, hkc, hkc'⟩ ℓ' ⟨hℓ', hℓ'X⟩
    have hkN : k ∈ normalizer (S.Lbar g : Set S.O) := by
      rw [mem_normalizer_Lbar_iff_fix haQ hne hn (Xbar12_le_Mbar hk), ha, map_add, hkc, hkc']
    exact ⟨(mem_normalizer_iff.mp hkN ℓ').mp hℓ',
      (S.Xbar12 g).mul_mem ((S.Xbar12 g).mul_mem hk hℓ'X) ((S.Xbar12 g).inv_mem hk)⟩
  · intro h₁ hh₁ h₂ hh₂ hh₁c hh₂c
    obtain ⟨x, hx, hxc, hxh, hxw⟩ := P.exists_move P.H_le P.c_mem_H hh₁ hh₂ hh₁c hh₂c
    refine ⟨x, ⟨hx, hxc, P.apply_c'_eq hx fun w hw => ?_⟩, hxh⟩
    have h := hxw w hw
    rw [mem_span_singleton_iff] at h
    have hδ : polar S.q (h₂ - h₁) P.c' = 0 := by
      rw [polar_comm]
      exact (P.H.sub_mem hh₂ hh₁).2
    rcases h with h | h
    · rw [sub_eq_zero.mp h]
    · rw [sub_eq_iff_eq_add.mp h, polar_add_left, hδ, zero_add]

theorem eq_one_or_eq_of_fix_H (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g)
    (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g)
    (hℓX : ℓ ∈ S.Xbar12 g) (hfix : ∀ h ∈ P.H, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) h = h) :
    ℓ = 1 ∨ ℓ = t := by
  obtain ⟨e, he, he1⟩ := P.exists_polar_c'
  have hℓc' := (fix_of_mem_Lbar haQ ha hℓ hℓX).2
  set h₀ := (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e with hh₀
  have hh₀H : h₀ ∈ P.H := by
    refine ⟨P.W.sub_mem (P.apply_mem hℓX he) he, ?_⟩
    change polar S.q P.c' h₀ = 0
    rw [hh₀, polar_sub_right, ← hℓc', psl_polar_apply_apply, hℓc', sub_self]
  have hℓw : ∀ w ∈ P.W, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + polar S.q w P.c' • h₀ := by
    intro w hw
    have hmem : w - polar S.q w P.c' • e ∈ P.H := by
      refine ⟨P.W.sub_mem hw (P.W.smul_mem _ he), ?_⟩
      change polar S.q P.c' (w - polar S.q w P.c' • e) = 0
      rw [polar_sub_right, polar_smul_right, polar_comm S.q P.c' e, he1, polar_comm S.q P.c' w,
        smul_eq_mul, mul_one, sub_self]
    have h1 := hfix _ hmem
    rw [map_sub, map_smul] at h1
    rw [hh₀, smul_sub]
    calc (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w
        = ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - polar S.q w P.c' • (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e) +
          polar S.q w P.c' • (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e := by abel
      _ = w + (polar S.q w P.c' • (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e - polar S.q w P.c' • e) := by
          rw [h1]
          abel
  by_cases hspan : h₀ ∈ span (ZMod 2) {P.c}
  · rw [mem_span_singleton_iff] at hspan
    rcases hspan with h0 | h0
    · left
      exact P.eq_one hℓX fun w hw => by rw [hℓw w hw, h0, smul_zero, add_zero]
    · right
      exact P.ext hℓX htX fun w hw => by rw [hℓw w hw, h0, P.tW w hw]
  · exfalso
    have hnot : P.c ∉ span (ZMod 2) {h₀ - P.c} := by
      rw [mem_span_singleton_iff]
      rintro (h | h)
      · exact P.c_ne h
      · apply hspan
        have : h₀ = P.c + P.c := by
          calc h₀ = (h₀ - P.c) + P.c := (sub_add_cancel h₀ P.c).symm
            _ = P.c + P.c := by rw [← h]
        rw [this, self_add_self]
        exact zero_mem _
    obtain ⟨ψ, hψ, hψ1⟩ := exists_functional hnot
    obtain ⟨x, hx, hxw⟩ := P.lift ψ (h₀ - P.c) (P.W.sub_mem hh₀H.1 P.hc)
      (hψ _ (mem_span_singleton_self _))
    have hxc : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c = h₀ := by
      rw [hxw P.c P.hc, hψ1, one_smul, add_sub_cancel]
    have hδ : polar S.q (h₀ - P.c) P.c' = 0 := by
      rw [polar_comm]
      exact (P.H.sub_mem hh₀H P.c_mem_H).2
    have hxc' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c' := P.apply_c'_eq hx fun w hw => by
      rw [hxw w hw, polar_add_left, polar_smul_left, hδ, smul_zero, add_zero]
    have hconj : x * t * x⁻¹ = ℓ := P.ext
      ((S.Xbar12 g).mul_mem ((S.Xbar12 g).mul_mem hx htX) ((S.Xbar12 g).inv_mem hx)) hℓX
      fun w hw => by rw [P.conj_apply hx hw, hxc, hxc', hℓw w hw]
    have := (P.conj_fix_of_mem_Lbar haQ hne htA ha hx (hconj ▸ hℓ)).1
    rw [hxc] at this
    exact hspan (this ▸ mem_span_singleton_self _)

theorem swap_eq_add (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') :
    S.cl (g * S.z * g⁻¹) = P.swap.c + P.swap.c' := by
  rw [ha, add_comm]
  rfl

theorem eq_one_or_eq_of_comm_le (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g)
    (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g)
    (hℓX : ℓ ∈ S.Xbar12 g)
    (hcomm : ∀ w ∈ P.W, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ span (ZMod 2) {P.c}) :
    ℓ = 1 ∨ ℓ = t := by
  refine P.swap.eq_one_or_eq_of_fix_H haQ hne htA htX (P.swap_eq_add ha) hℓ hℓX ?_
  rintro w' ⟨hw', hw'c⟩
  change w' ∈ P.W' at hw'
  change polar S.q P.c w' = 0 at hw'c
  have hmem : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w' - w' ∈ P.W := by
    refine P.mem_of_polar fun w hw => ?_
    have hw1 : ((ℓ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P.W :=
      P.apply_mem ((S.Xbar12 g).inv_mem hℓX) hw
    have h := hcomm _ hw1
    rw [psl_apply_inv_apply, mem_span_singleton_iff] at h
    have h2 := psl_polar_apply_apply ℓ (((ℓ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) w'
    rw [psl_apply_inv_apply] at h2
    rw [polar_sub_right, h2, sub_eq_zero]
    rcases h with h | h
    · rw [← sub_eq_zero.mp h]
    · rw [show ((ℓ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + P.c by
        rw [← h, sub_eq_add', ← add_assoc, self_add_self, zero_add],
        polar_add_left, hw'c, add_zero]
  have h0 : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w' - w' ∈ P.W ⊓ P.W' :=
    ⟨hmem, P.W'.sub_mem (P.apply_mem' hℓX hw') hw'⟩
  rw [P.inf_eq, Submodule.mem_bot, sub_eq_zero] at h0
  exact h0

end PSLPair

end Setting

end CFSG.LargeExtraspecial
