module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Basic

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

section Counting

variable {K : Type} [Group K] [Finite K] {A : Type} [Group A] [Finite A]
  {ρ : K →* MulAut A} {V : Sylow 2 K} {Z : Subgroup A}

omit [Finite K] [Finite A] in
theorem fu_fix (h : Hyp ρ V Z) {v : K} (hv : v ∈ (V : Subgroup K)) {x : A} (hx : x ∈ Z) :
    ρ v x = x := by
  by_cases hv1 : v = 1
  · subst hv1; simp
  · exact (h.fix v hv hv1 x).2 hx

omit [Finite K] in
omit [Finite A] in
theorem fu_comm (h : Hyp ρ V Z) {v : K} (hv : v ∈ (V : Subgroup K)) (x : A) :
    ρ v x * x⁻¹ ∈ Z := by
  by_cases hv1 : v = 1
  · subst hv1; simp
  · exact h.comm_mem hv hv1 x

omit [Finite K] in
omit [Finite A] in
theorem fu_inj (h : Hyp ρ V Z) {c : A} (hc : c ∉ Z) {v₁ v₂ : K} (h1 : v₁ ∈ (V : Subgroup K))
    (h2 : v₂ ∈ (V : Subgroup K)) (he : ρ v₁ c * c⁻¹ = ρ v₂ c * c⁻¹) : v₁ = v₂ := by
  have e1 : ρ v₁ c = (ρ v₁ c * c⁻¹) * c := (inv_mul_cancel_right _ _).symm
  have e2 : ρ v₂ c = (ρ v₂ c * c⁻¹) * c := (inv_mul_cancel_right _ _).symm
  have key : ρ (v₁ * v₂) c = c := by
    calc ρ (v₁ * v₂) c = ρ v₁ (ρ v₂ c) := by rw [map_mul, MulAut.mul_apply]
      _ = ρ v₁ ((ρ v₂ c * c⁻¹) * c) := by rw [← e2]
      _ = ρ v₁ (ρ v₂ c * c⁻¹) * ρ v₁ c := map_mul (ρ v₁) _ _
      _ = (ρ v₂ c * c⁻¹) * ((ρ v₁ c * c⁻¹) * c) := by
          rw [fu_fix h h1 (fu_comm h h2 c), ← e1]
      _ = (ρ v₂ c * c⁻¹) * ((ρ v₂ c * c⁻¹) * c) := by rw [he]
      _ = c := by rw [← mul_assoc, h.sq, one_mul]
  by_contra hne
  have h12 : v₁ * v₂ ≠ 1 := by
    intro h12
    apply hne
    calc v₁ = v₁ * (v₂ * v₂) := by rw [h.sqV v₂ h2, mul_one]
      _ = (v₁ * v₂) * v₂ := (mul_assoc _ _ _).symm
      _ = v₂ := by rw [h12, one_mul]
  exact hc ((h.fix _ ((V : Subgroup K).mul_mem h1 h2) h12 c).1 key)

omit [Finite K] in
theorem fu_exists (h : Hyp ρ V Z) {c : A} (hc : c ∉ Z) {y : A} (hy : y ∈ Z) :
    ∃ v ∈ (V : Subgroup K), ρ v c * c⁻¹ = y := by
  let F : ↥(V : Subgroup K) → ↥Z := fun v => ⟨ρ v c * c⁻¹, fu_comm h v.2 c⟩
  have hF : Function.Injective F := fun v₁ v₂ he =>
    Subtype.ext (fu_inj h hc v₁.2 v₂.2 (congrArg Subtype.val he))
  obtain ⟨v, hv⟩ := (hF.bijective_of_nat_card_le (by rw [h.cardV, h.cardZ])).2 ⟨y, hy⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

theorem fu_mul_mem {Z Z' : Subgroup A} (hZ : Nat.card Z = 4) {a c z : A} (haZ : a ∈ Z)
    (haZ' : a ∈ Z') (ha1 : a ≠ 1) (hcZ : c ∈ Z) (hcZ' : c ∉ Z') (hzZ : z ∈ Z)
    (hzZ' : z ∉ Z') : z * c ∈ Z' := by
  set H : Subgroup Z := Z'.subgroupOf Z
  have hcard : Nat.card H * H.index = 4 := by rw [H.card_mul_index, hZ]
  have hne_top : H ≠ ⊤ := by
    intro htop
    apply hcZ'
    have hc : (⟨c, hcZ⟩ : Z) ∈ H := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hc
  have hne_bot : H ≠ ⊥ := by
    intro hbot
    apply ha1
    have ha : (⟨a, haZ⟩ : Z) ∈ H := Subgroup.mem_subgroupOf.2 haZ'
    rw [hbot, Subgroup.mem_bot] at ha
    exact congrArg Subtype.val ha
  have hi1 : H.index ≠ 1 := fun h1 => hne_top (Subgroup.index_eq_one.1 h1)
  have hc1 : Nat.card H ≠ 1 := fun h1 => hne_bot (Subgroup.card_eq_one.1 h1)
  have hi0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hc0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hi2 : H.index = 2 := by
    have h2c : 2 ≤ Nat.card H := by omega
    have hle := Nat.mul_le_mul_right H.index h2c
    rw [hcard] at hle
    omega
  exact Subgroup.mem_subgroupOf.1 ((Subgroup.mul_mem_iff_of_index_two hi2
    (a := ⟨z, hzZ⟩) (b := ⟨c, hcZ⟩)).2 (iff_of_false
      (fun hz => hzZ' (Subgroup.mem_subgroupOf.1 hz))
      (fun hc => hcZ' (Subgroup.mem_subgroupOf.1 hc))))

omit [Finite K] in
theorem fu_mem_of_normalizer (P : Sylow 2 K) {w : K}
    (hw : w ∈ normalizer ((P : Subgroup K) : Set K)) (hw2 : w * w = 1) :
    w ∈ (P : Subgroup K) := by
  have hp : IsPGroup 2 (zpowers w) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2))
  have hmem : w ∈ zpowers w ⊓ normalizer (P : Set K) := Subgroup.mem_inf.2 ⟨mem_zpowers w, hw⟩
  rw [hp.inf_normalizer_sylow P] at hmem
  exact (Subgroup.mem_inf.1 hmem).2

theorem fu_exists_c (h : Hyp ρ V Z) {k : K} (hk : k ∉ normalizer ((V : Subgroup K) : Set K)) :
    ∃ c ∈ Z, c ∉ Z.map (ρ k).toMonoidHom := by
  by_contra hcon
  have hle : Z ≤ Z.map (ρ k).toMonoidHom := fun c hc => by
    by_contra hc'
    exact hcon ⟨c, hc, hc'⟩
  have heq : Z = Z.map (ρ k).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [(h.conj k).cardZ, h.cardZ])
  apply hk
  refine (h.stab_iff k).1 fun x hx => ?_
  have hx' : ρ k x ∈ Z.map (ρ k).toMonoidHom := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  rwa [← heq] at hx'

theorem Hyp.fixer_unique (h : Hyp ρ V Z) {k : K}
    (hk : k ∉ normalizer ((V : Subgroup K) : Set K)) {a : A} (haZ : a ∈ Z)
    (hak : a ∈ Z.map (ρ k).toMonoidHom) : a = 1 := by
  by_contra ha1
  have h' := h.conj k
  obtain ⟨c, hcZ, hcZ'⟩ := fu_exists_c h hk
  obtain ⟨w, hwW, hwc⟩ := fu_exists h' hcZ' hak
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply ha1
    rw [← hwc]
    simp
  have hwZ : ∀ z ∈ Z, ρ w z ∈ Z := by
    intro z hz
    by_cases hz' : z ∈ Z.map (ρ k).toMonoidHom
    · rw [fu_fix h' hwW hz']
      exact hz
    · have e := fu_fix h' hwW (fu_mul_mem h.cardZ haZ hak ha1 hcZ hcZ' hz hz')
      rw [map_mul] at e
      have e2 : ρ w c = a * c := by rw [← hwc]; group
      rw [e2] at e
      have e3 : ρ w z = z * a⁻¹ := by
        calc ρ w z = ρ w z * (a * c) * (a * c)⁻¹ := by group
          _ = z * c * (a * c)⁻¹ := by rw [e]
          _ = z * a⁻¹ := by group
      rw [e3]
      exact Z.mul_mem hz (Z.inv_mem haZ)
  have hwV := fu_mem_of_normalizer V ((h.stab_iff w).1 hwZ) (h'.sqV w hwW)
  exact hw1 (h.ti hk w hwV hwW)

end Counting

end CFSG.OddStandard.ThmC.O2.A8
