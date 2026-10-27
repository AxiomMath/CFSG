module

public import CFSG.LieType.SeitzGeneration.UnitaryCenters

public section

namespace CFSG.LieType.SeitzGeneration.Centers

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem isCenter_of_eigen (hσ : ∀ c, σ (σ c) = c) {H : Subgroup (SUid σ n)} {y : SUid σ n}
    (hH : ∀ g : SUid σ n, g * y = y * g → g ∈ H) {v : Fin n → K} (hv : herm σ v v = 0) {l : K}
    (hl : σ l * l = 1) (hyv : y • v = l • v) : IsCenter H v := by
  refine ⟨hv, fun c hc => ⟨tv hσ hv hc, hH _ ?_, tv_smul hσ hv hc⟩⟩
  apply ext_smul σ
  intro u
  have h1 : herm σ v (y • u) = l * herm σ v u := by
    have h := herm_smul_smul σ y v u
    rw [hyv, herm_smul_left] at h
    calc herm σ v (y • u) = l * (σ l * herm σ v (y • u)) := by
          linear_combination (-(herm σ v (y • u))) * hl
      _ = l * herm σ v u := by rw [h]
  rw [mul_smul, mul_smul, tv_smul, tv_smul, smul_add, smul_comm y (c * herm σ v u) v, hyv, h1,
    smul_smul]
  congr 2
  ring

theorem allCenters_step (hσ : IsUnitaryInvolution σ) (hq : ∀ c : K, c ≠ 0 → σ c * c = 1)
    (h2 : (1 : K) + 1 = 0) {H : Subgroup (SUid σ n)} {W : Submodule K (Fin n → K)}
    (hON : HasONBasis σ W) (hA : AllCenters H W) {u e : Fin n → K} (hu : u ∈ W)
    (hu1 : herm σ u u = 1) (he1 : herm σ e e = 1) (hWe : ∀ w ∈ W, herm σ w e = 0)
    (hC : IsCenter H (u + e)) : AllCenters H (W ⊔ Submodule.span K {e}) := by
  obtain ⟨m, x, hx, hspan, hm⟩ := hON
  intro v hv hiso
  obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
  have hew : herm σ e w = 0 := herm_eq_zero_comm σ hσ.invol (hWe w hw)
  have hnorm : herm σ (w + c • e) (w + c • e) = herm σ w w + σ c * c := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hWe w hw, hew,
      he1]
    ring
  by_cases hc : c = 0
  · subst hc
    have hw0 : herm σ w w = 0 := by simpa [hnorm] using hiso
    simpa using hA w hw hw0
  · have hcc : σ c * c = 1 := hq c hc
    have hww : herm σ w w = 1 := by
      rw [hnorm, hcc] at hiso
      linear_combination hiso - h2
    have hcuW : c • u ∈ W := W.smul_mem c hu
    obtain ⟨d₁, hd₁⟩ := (mem_span_range_iff x _).1 (hspan ▸ hcuW)
    obtain ⟨d₂, hd₂⟩ := (mem_span_range_iff x _).1 (hspan ▸ hw)
    have hn₁ : herm σ d₁ d₁ = 1 := by
      rw [← herm_orthoEmb hx, hd₁, herm_smul_left, herm_smul_right, hu1]
      linear_combination hcc
    have hn₂ : herm σ d₂ d₂ = 1 := by rw [← herm_orthoEmb hx, hd₂, hww]
    have hH : ∀ c', herm σ c' c' = 0 → IsCenter H (orthoEmb x c') := fun c' hc' =>
      hA _ (hspan ▸ orthoEmb_mem_span x c') (by rw [herm_orthoEmb hx]; exact hc')
    obtain ⟨g, hg, hgd, hgfix⟩ := exists_mem_fix_of_norm hσ hm (herm_orthoEmb hx) hH
      (one_ne_zero : (1 : K) ≠ 0) hn₁ hn₂
    have hge : g • e = e := hgfix e fun u' => hWe _ (hspan ▸ orthoEmb_mem_span x u')
    have hgu : g • (c • u) = w := by rw [← hd₁, hgd, hd₂]
    have hmap := (hC.smul hσ.invol c).map hg
    rw [smul_add, smul_add, hgu, smul_comm g c e, hge] at hmap
    exact hmap

section Frame

variable (K) (n)

@[expose] def frameSpan (j : ℕ) : Submodule K (Fin n → K) :=
  Submodule.span K {v | ∃ i : Fin n, i.val < j ∧ v = Pi.single i 1}

variable {K} {n}

theorem herm_std (σ : K ≃+* K) (i j : Fin n) :
    herm σ (Pi.single i (1 : K)) (Pi.single j 1) = if i = j then 1 else 0 := by
  rw [herm_single_left, map_one, one_mul, Pi.single_apply]

theorem single_mem_frameSpan {i : Fin n} {j : ℕ} (h : i.val < j) :
    (Pi.single i 1 : Fin n → K) ∈ frameSpan K n j := Submodule.subset_span ⟨i, h, rfl⟩

theorem frameSpan_succ {j : ℕ} (hj : j < n) :
    frameSpan K n (j + 1) =
      frameSpan K n j ⊔ Submodule.span K {(Pi.single ⟨j, hj⟩ 1 : Fin n → K)} := by
  rw [frameSpan, frameSpan, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i.val < j
    · exact Or.inl ⟨i, h, rfl⟩
    · right
      have : i = ⟨j, hj⟩ := Fin.ext (by show i.val = j; omega)
      rw [this]
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨⟨j, hj⟩, by simp, rfl⟩

theorem frameSpan_hasON (σ : K ≃+* K) {j : ℕ} (hj : 4 ≤ j) (hjn : j ≤ n) :
    HasONBasis σ (frameSpan K n j) := by
  refine ⟨j, fun i => Pi.single ⟨i.val, by omega⟩ 1, fun a b => ?_, ?_, Or.inl hj⟩
  · rw [herm_std]
    simp [Fin.ext_iff]
  · rw [frameSpan]
    congr 1
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i.val, by omega⟩, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, rfl⟩

theorem herm_frameSpan_single (σ : K ≃+* K) {j : ℕ} {k : Fin n} (hk : j ≤ k.val)
    {w : Fin n → K} (hw : w ∈ frameSpan K n j) : herm σ w (Pi.single k 1) = 0 := by
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    rw [herm_std]
    have hne : i ≠ k := fun h => by
      subst h
      omega
    simp [hne]
  | zero => simp
  | add a b _ _ ha hb => rw [herm_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [herm_smul_left, ha, mul_zero]

theorem frameSpan_self : frameSpan K n n = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (single_mem_frameSpan i.isLt)

theorem eq_top_of_frame (hσ : IsUnitaryInvolution σ) (hq : ∀ c : K, c ≠ 0 → σ c * c = 1)
    (h2 : (1 : K) + 1 = 0) {H : Subgroup (SUid σ n)} (hn : 5 ≤ n)
    (H₁ : AllCenters H (frameSpan K n 4))
    (H₂ : IsCenter H (Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨4, by omega⟩ 1))
    (H₃ : ∀ j : Fin n, 5 ≤ j.val →
      IsCenter H (Pi.single ⟨2, by omega⟩ 1 + Pi.single j 1)) : H = ⊤ := by
  have hall : ∀ j, 4 ≤ j → j ≤ n → AllCenters H (frameSpan K n j) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun _ => H₁
    | succ j hj ih =>
      intro hjn
      have hjlt : j < n := by omega
      rw [frameSpan_succ hjlt]
      have hunit : ∀ i : Fin n, herm σ (Pi.single i (1 : K)) (Pi.single i 1) = 1 := fun i => by
        rw [herm_std]
        simp
      have horth : ∀ w ∈ frameSpan K n j, herm σ w (Pi.single (⟨j, hjlt⟩ : Fin n) 1) = 0 :=
        fun w hw => herm_frameSpan_single σ le_rfl hw
      by_cases hj4 : j = 4
      · subst hj4
        exact allCenters_step hσ hq h2 (frameSpan_hasON σ le_rfl (by omega)) (ih (by omega))
          (single_mem_frameSpan (i := ⟨0, by omega⟩) (by simp)) (hunit _) (hunit _) horth H₂
      · have hj5 : 5 ≤ j := by omega
        exact allCenters_step hσ hq h2 (frameSpan_hasON σ hj (by omega)) (ih (by omega))
          (single_mem_frameSpan (i := ⟨2, by omega⟩) (by simp; omega)) (hunit _) (hunit _) horth
          (H₃ ⟨j, hjlt⟩ hj5)
  refine eq_top_of_forall_isCenter hσ (by omega) (fun h => by omega) fun a ha => ?_
  have hmem : a ∈ frameSpan K n n := by
    rw [frameSpan_self]
    exact Submodule.mem_top
  exact hall n (by omega) le_rfl a hmem ha

end Frame

end CFSG.LieType.SeitzGeneration.Centers
