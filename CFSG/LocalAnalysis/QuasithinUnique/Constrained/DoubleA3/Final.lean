module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Equiv Equiv.Perm

theorem perm_fin6_central_aux :
    ∀ σ : Perm (Fin 6), σ * (swap 0 1 * swap 1 2 : Perm (Fin 6)) = (swap 0 1 * swap 1 2) * σ →
      σ * (swap 0 1 * swap 1 3 : Perm (Fin 6)) = (swap 0 1 * swap 1 3) * σ →
      σ * (swap 0 1 * swap 1 4 : Perm (Fin 6)) = (swap 0 1 * swap 1 4) * σ →
      σ * (swap 0 1 * swap 1 5 : Perm (Fin 6)) = (swap 0 1 * swap 1 5) * σ → σ = 1 := by
  decide +kernel

theorem perm_fin6_central (σ : Perm (Fin 6))
    (h : ∀ a : alternatingGroup (Fin 6), σ * (a : Perm (Fin 6)) = (a : Perm (Fin 6)) * σ) :
    σ = 1 := by
  have m2 : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have m3 : (swap 0 1 * swap 1 3 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have m4 : (swap 0 1 * swap 1 4 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have m5 : (swap 0 1 * swap 1 5 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  exact perm_fin6_central_aux σ (h ⟨_, m2⟩) (h ⟨_, m3⟩) (h ⟨_, m4⟩) (h ⟨_, m5⟩)

@[expose] def alt6X0 : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6D0 : Subgroup (alternatingGroup (Fin 6)) := Subgroup.centralizer {alt6X0}

theorem card_filter_alt6D0 :
    (Finset.univ.filter fun y : alternatingGroup (Fin 6) => y * alt6X0 = alt6X0 * y).card = 8 := by
  decide +kernel

theorem card_alt6D0 : Nat.card alt6D0 = 8 := by
  classical
  have h : Nat.card alt6D0 =
      (Finset.univ.filter fun y : alternatingGroup (Fin 6) => y * alt6X0 = alt6X0 * y).card := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight
      (fun y => by simp [alt6D0, Subgroup.mem_centralizer_iff, eq_comm])
  rw [h]; exact card_filter_alt6D0

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem alt6_exists_conj_of_card_eight (D : Subgroup (alternatingGroup (Fin 6)))
    (hD : Nat.card D = 8) :
    ∃ g : alternatingGroup (Fin 6), ∀ x : alternatingGroup (Fin 6), x ∈ D ↔ g⁻¹ * x * g ∈ alt6D0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ H : Subgroup (alternatingGroup (Fin 6)), Nat.card H = 8 → ¬ 2 ∣ H.index := by
    intro H hH h2
    have := H.card_mul_index
    rw [hH, card_alt6] at this
    omega
  have hp : ∀ H : Subgroup (alternatingGroup (Fin 6)), Nat.card H = 8 → IsPGroup 2 H := fun H hH =>
    IsPGroup.of_card (n := 3) (by rw [hH]; norm_num)
  let P : Sylow 2 (alternatingGroup (Fin 6)) := (hp D hD).toSylow (hidx D hD)
  let P₀ : Sylow 2 (alternatingGroup (Fin 6)) := (hp alt6D0 card_alt6D0).toSylow (hidx alt6D0 card_alt6D0)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) P₀ P
  refine ⟨g, fun x => ?_⟩
  have h1 : (g • P₀ : Sylow 2 (alternatingGroup (Fin 6))) = P := hg
  have h2 : ((g • P₀ : Sylow 2 (alternatingGroup (Fin 6))) : Subgroup (alternatingGroup (Fin 6))) =
      (P : Subgroup (alternatingGroup (Fin 6))) := by rw [h1]
  have h3 : x ∈ (P : Subgroup (alternatingGroup (Fin 6))) ↔
      g⁻¹ * x * g ∈ (P₀ : Subgroup (alternatingGroup (Fin 6))) := by
    rw [← h2, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  exact h3

theorem swap_commute_da : ∀ x y : Fin 6, x ≠ y →
    swap x y * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) =
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) * swap x y →
      swap x y = swap 4 5 := by
  decide +kernel

theorem alt6_exists_three_swaps (D : Subgroup (alternatingGroup (Fin 6))) (hD : Nat.card D = 8)
    (τ : Perm (Fin 6)) (hτ : τ.IsSwap)
    (hc : ∀ d ∈ D, τ * (d : Perm (Fin 6)) = (d : Perm (Fin 6)) * τ) :
    ∃ d₁ ∈ D, ∃ d₂ ∈ D, (τ * (d₁ : Perm (Fin 6))).IsSwap ∧ (τ * (d₂ : Perm (Fin 6))).IsSwap ∧
      τ ≠ τ * (d₁ : Perm (Fin 6)) ∧ τ ≠ τ * (d₂ : Perm (Fin 6)) ∧
      τ * (d₁ : Perm (Fin 6)) ≠ τ * (d₂ : Perm (Fin 6)) := by
  obtain ⟨g, hg⟩ := alt6_exists_conj_of_card_eight D hD
  let da : alternatingGroup (Fin 6) :=
    ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let e1 : alternatingGroup (Fin 6) :=
    ⟨swap 0 2 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let e2 : alternatingGroup (Fin 6) :=
    ⟨swap 1 3 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have hmemD₀ : ∀ y : alternatingGroup (Fin 6),
      (y : Perm (Fin 6)) * (swap 0 2 * swap 1 3 : Perm (Fin 6)) =
        (swap 0 2 * swap 1 3 : Perm (Fin 6)) * (y : Perm (Fin 6)) → y ∈ alt6D0 := by
    intro y hy
    rw [alt6D0, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    simpa [alt6X0] using hy.symm
  have hda : da ∈ alt6D0 := hmemD₀ _ (by decide +kernel)
  have hd1 : e1 ∈ alt6D0 := hmemD₀ _ (by decide +kernel)
  have hd2 : e2 ∈ alt6D0 := hmemD₀ _ (by decide +kernel)
  set γ : Perm (Fin 6) := (g : Perm (Fin 6)) with hγ
  have hconjmem : ∀ d₀ : alternatingGroup (Fin 6), d₀ ∈ alt6D0 → g * d₀ * g⁻¹ ∈ D := by
    intro d₀ hd₀
    rw [hg]
    have : g⁻¹ * (g * d₀ * g⁻¹) * g = d₀ := by group
    rw [this]; exact hd₀
  have hcoe : ∀ d : alternatingGroup (Fin 6),
      ((g * d * g⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        γ * (d : Perm (Fin 6)) * γ⁻¹ := by
    intro d; simp [hγ]
  obtain ⟨a, b, hab, rfl⟩ := hτ
  have hτ'swap : γ⁻¹ * swap a b * γ = swap (γ⁻¹ a) (γ⁻¹ b) := by
    have := Equiv.swap_apply_apply γ⁻¹ a b
    simpa using this.symm
  have hτ'ne : γ⁻¹ a ≠ γ⁻¹ b := fun h => hab (γ⁻¹.injective h)
  have hcomm_da : swap (γ⁻¹ a) (γ⁻¹ b) *
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) =
      (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) * swap (γ⁻¹ a) (γ⁻¹ b) := by
    have h1 := hc _ (hconjmem _ hda)
    rw [hcoe] at h1
    rw [← hτ'swap]
    calc γ⁻¹ * swap a b * γ * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5)
        = γ⁻¹ * (swap a b * (γ * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) * γ⁻¹)) * γ := by
          group
      _ = γ⁻¹ * ((γ * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) * γ⁻¹) * swap a b) * γ := by
          rw [show (da : Perm (Fin 6)) = swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 from rfl] at h1
          rw [h1]
      _ = _ := by group
  have hτ'eq := swap_commute_da _ _ hτ'ne hcomm_da
  have hτ_eq : swap a b = γ * swap 4 5 * γ⁻¹ := by
    have h := hτ'swap
    rw [hτ'eq] at h
    calc swap a b = γ * (γ⁻¹ * swap a b * γ) * γ⁻¹ := by group
      _ = _ := by rw [h]
  have hswap : ∀ x y : Fin 6, x ≠ y → (γ * swap x y * γ⁻¹).IsSwap := by
    intro x y hxy
    refine ⟨γ x, γ y, fun h => hxy (γ.injective h), ?_⟩
    simpa using (Equiv.swap_apply_apply γ x y).symm
  have hk1 : swap a b * ((g * e1 * g⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      γ * swap 0 2 * γ⁻¹ := by
    rw [hcoe, hτ_eq]
    have : (swap 4 5 : Perm (Fin 6)) * (e1 : Perm (Fin 6)) = swap 0 2 := by
      show (swap 4 5 : Perm (Fin 6)) * (swap 0 2 * swap 4 5) = swap 0 2
      decide +kernel
    calc γ * swap 4 5 * γ⁻¹ * (γ * (e1 : Perm (Fin 6)) * γ⁻¹)
        = γ * (swap 4 5 * (e1 : Perm (Fin 6))) * γ⁻¹ := by group
      _ = _ := by rw [this]
  have hk2 : swap a b * ((g * e2 * g⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      γ * swap 1 3 * γ⁻¹ := by
    rw [hcoe, hτ_eq]
    have : (swap 4 5 : Perm (Fin 6)) * (e2 : Perm (Fin 6)) = swap 1 3 := by
      show (swap 4 5 : Perm (Fin 6)) * (swap 1 3 * swap 4 5) = swap 1 3
      decide +kernel
    calc γ * swap 4 5 * γ⁻¹ * (γ * (e2 : Perm (Fin 6)) * γ⁻¹)
        = γ * (swap 4 5 * (e2 : Perm (Fin 6))) * γ⁻¹ := by group
      _ = _ := by rw [this]
  refine ⟨g * e1 * g⁻¹, hconjmem _ hd1, g * e2 * g⁻¹, hconjmem _ hd2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk1]; exact hswap 0 2 (by decide)
  · rw [hk2]; exact hswap 1 3 (by decide)
  · rw [hk1, hτ_eq]
    intro h
    have := mul_left_cancel (mul_right_cancel h)
    exact absurd this (by decide)
  · rw [hk2, hτ_eq]
    intro h
    have := mul_left_cancel (mul_right_cancel h)
    exact absurd this (by decide)
  · rw [hk1, hk2]
    intro h
    have := mul_left_cancel (mul_right_cancel h)
    exact absurd this (by decide)

section API

variable {G : Type*} [Group G] {K : Subgroup G} (e : K ≃* alternatingGroup (Fin 6))

theorem conj_mem_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) {k : G}
    (hk : k ∈ K) : g⁻¹ * k * g ∈ K := by
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg)) k
  simpa using this.mp hk

theorem inducesPerm_mul {g h : G} {σ ρ : Perm (Fin 6)}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hgσ : InducesPerm e g σ) (hhρ : InducesPerm e h ρ) : InducesPerm e (g * h) (σ * ρ) := by
  intro k k' hk'
  let k₁ : K := ⟨g⁻¹ * (k : G) * g, conj_mem_of_mem_normalizer hg k.2⟩
  have h1 := hgσ k k₁ rfl
  have h2 := hhρ k₁ k' (by rw [hk']; simp [k₁, mul_assoc])
  rw [h2, h1]
  simp [mul_assoc]

theorem inducesPerm_inv {g : G} {σ : Perm (Fin 6)}
    (h : InducesPerm e g σ) : InducesPerm e g⁻¹ σ⁻¹ := by
  intro k k' hk'
  have hk : (k : G) = g⁻¹ * (k' : G) * g := by
    rw [hk']; simp [mul_assoc]
  have h1 := h k' k hk
  rw [h1]
  simp [mul_assoc]

theorem inducesPerm_of_mem (r : K) :
    InducesPerm e (r : G) ((e r : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
  intro k k' hk'
  have : k' = r⁻¹ * k * r := Subtype.ext (by simpa using hk')
  rw [this]
  simp

theorem inducesPerm_one_of_centralizer {g : G} (hg : g ∈ Subgroup.centralizer (K : Set G)) :
    InducesPerm e g 1 := by
  intro k k' hk'
  have hc : g * (k : G) = (k : G) * g := ((Subgroup.mem_centralizer_iff.mp hg) k k.2).symm
  have : k' = k := Subtype.ext (by rw [hk', mul_assoc, ← hc]; simp)
  rw [this]; simp

theorem mem_centralizer_of_inducesPerm_one {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (h : InducesPerm e g 1) : g ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let k₀ : K := ⟨k, hk⟩
  let k₁ : K := ⟨g⁻¹ * k * g, conj_mem_of_mem_normalizer hg hk⟩
  have h1 := h k₀ k₁ rfl
  have : k₁ = k₀ := e.injective (Subtype.ext (by simpa using h1))
  have h2 : g⁻¹ * k * g = k := congrArg Subtype.val this
  calc k * g = g * (g⁻¹ * k * g) := by simp [mul_assoc]
    _ = g * k := by rw [h2]

theorem inducesPerm_unique {g : G} {σ ρ : Perm (Fin 6)}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (h1 : InducesPerm e g σ) (h2 : InducesPerm e g ρ) : σ = ρ := by
  have key : ρ * σ⁻¹ = 1 := by
    apply perm_fin6_central
    intro a
    obtain ⟨k, rfl⟩ := e.surjective a
    let k₁ : K := ⟨g⁻¹ * (k : G) * g, conj_mem_of_mem_normalizer hg k.2⟩
    have a1 := h1 k k₁ rfl
    have a2 := h2 k k₁ rfl
    rw [a1] at a2
    calc ρ * σ⁻¹ * ((e k : alternatingGroup (Fin 6)) : Perm (Fin 6))
        = ρ * (σ⁻¹ * (e k : Perm (Fin 6)) * σ) * σ⁻¹ := by group
      _ = ρ * (ρ⁻¹ * (e k : Perm (Fin 6)) * ρ) * σ⁻¹ := by rw [a2]
      _ = (e k : Perm (Fin 6)) * (ρ * σ⁻¹) := by group
  have := mul_inv_eq_one.mp key
  exact this.symm

theorem not_mem_of_inducesPerm_swap {w : G} {c : Perm (Fin 6)}
    (hw : w ∈ Subgroup.normalizer (K : Set G))
    (hc : c.IsSwap) (h : InducesPerm e w c) : w ∉ K := by
  intro hwK
  have h1 := inducesPerm_of_mem e ⟨w, hwK⟩
  have := inducesPerm_unique e hw h h1
  have hmem : c ∈ alternatingGroup (Fin 6) := by
    rw [this]; exact (e ⟨w, hwK⟩).2
  rw [Equiv.Perm.mem_alternatingGroup] at hmem
  obtain ⟨x, y, hxy, rfl⟩ := hc
  rw [Equiv.Perm.sign_swap hxy] at hmem
  exact absurd hmem (by decide)

theorem two_conjugates {R G₂ : Subgroup G} {z₂ u s : G} {τ c : Perm (Fin 6)}
    (hN : G₂ ≤ Subgroup.normalizer (K : Set G)) (hz₂ : z₂ ≠ 1)
    (hz₂K : z₂ ∈ Subgroup.centralizer (K : Set G)) (hz₂G : z₂ ∈ G₂)
    (huG : u ∈ G₂) (hu : u ∈ conjClass z₂) (huz : u * z₂ ∈ conjClass z₂)
    (hτ : τ.IsSwap) (hτu : InducesPerm e u τ) (hc : c.IsSwap)
    (hBR : G₂ ⊓ Subgroup.centralizer (K : Set G) ≤ R)
    (hsurj : ∀ α : MulAut ↥K, ∃ g ∈ G₂, ∀ k : K, ((α k : K) : G) = g⁻¹ * (k : G) * g)
    (h37 : ∀ y ∈ conjClass z₂, y ∈ R → y ∈ R ⊓ K ∨ y ∈ conjR (R ⊓ K) s)
    {y : G} (hyG : y ∈ G₂) (hyR : y ∈ R) (hyc : InducesPerm e y c) :
    ∃ w w' : G, w ≠ w' ∧
      (w ∈ conjClass z₂ ∧ w ∈ conjR (R ⊓ K) s ∧ w ∈ G₂ ∧ InducesPerm e w c) ∧
      (w' ∈ conjClass z₂ ∧ w' ∈ conjR (R ⊓ K) s ∧ w' ∈ G₂ ∧ InducesPerm e w' c) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Perm (Fin 6), σ⁻¹ * τ * σ = c := by
    obtain ⟨a, b, hab, rfl⟩ := hτ
    obtain ⟨x, y, hxy, rfl⟩ := hc
    obtain ⟨σ, hσ⟩ := isConj_iff.mp (isConj_swap hab hxy)
    exact ⟨σ⁻¹, by simpa using hσ⟩
  obtain ⟨g, hgG, hgσ⟩ : ∃ g ∈ G₂, InducesPerm e g σ := by
    obtain ⟨g, hg, hg'⟩ := hsurj ((e.trans (MulAut.conjNormal σ⁻¹)).trans e.symm)
    refine ⟨g, hg, fun k k' hk' => ?_⟩
    have : k' = ((e.trans (MulAut.conjNormal σ⁻¹)).trans e.symm) k :=
      Subtype.ext (by rw [hg' k]; exact hk')
    rw [this]
    simp
  have hgN : g ∈ Subgroup.normalizer (K : Set G) := hN hgG
  have hginvN : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hgN
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := hN hyG
  have build : ∀ v : G, v ∈ G₂ → v ∈ conjClass z₂ → InducesPerm e v τ →
      (g⁻¹ * v * g ∈ conjClass z₂ ∧ g⁻¹ * v * g ∈ conjR (R ⊓ K) s ∧ g⁻¹ * v * g ∈ G₂ ∧
        InducesPerm e (g⁻¹ * v * g) c) := by
    intro v hvG hvc hvτ
    have hvN : v ∈ Subgroup.normalizer (K : Set G) := hN hvG
    have hwG : g⁻¹ * v * g ∈ G₂ := G₂.mul_mem (G₂.mul_mem (G₂.inv_mem hgG) hvG) hgG
    have hwc : InducesPerm e (g⁻¹ * v * g) c := by
      have h1 := inducesPerm_mul e hginvN (inducesPerm_inv e hgσ) hvτ
      have h2 := inducesPerm_mul e (mul_mem hginvN hvN) h1 hgσ
      rw [← hσ]
      simpa [mul_assoc] using h2
    have hwN : g⁻¹ * v * g ∈ Subgroup.normalizer (K : Set G) := hN hwG
    have hq : (g⁻¹ * v * g) * y⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      apply mem_centralizer_of_inducesPerm_one e (mul_mem hwN (inv_mem hyN))
      have := inducesPerm_mul e hwN hwc (inducesPerm_inv e hyc)
      simpa using this
    have hwR : g⁻¹ * v * g ∈ R := by
      have hq' : (g⁻¹ * v * g) * y⁻¹ ∈ R := hBR ⟨G₂.mul_mem hwG (G₂.inv_mem hyG), hq⟩
      have := R.mul_mem hq' hyR
      simpa using this
    have hwcl : g⁻¹ * v * g ∈ conjClass z₂ := conj_mem_conjClass hvc g
    refine ⟨hwcl, ?_, hwG, hwc⟩
    rcases h37 _ hwcl hwR with h | h
    · exact absurd h.2 (not_mem_of_inducesPerm_swap e hwN hc hwc)
    · exact h
  obtain ⟨a1, a2, a3, a4⟩ := build u huG hu hτu
  have huzG : u * z₂ ∈ G₂ := G₂.mul_mem huG hz₂G
  have huzτ : InducesPerm e (u * z₂) τ := by
    have := inducesPerm_mul e (hN huG) hτu (inducesPerm_one_of_centralizer e hz₂K)
    simpa using this
  obtain ⟨b1, b2, b3, b4⟩ := build (u * z₂) huzG huz huzτ
  refine ⟨g⁻¹ * u * g, g⁻¹ * (u * z₂) * g, ?_, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
  intro h
  have : u = u * z₂ := by
    have := mul_left_cancel (mul_right_cancel
      (by simpa [mul_assoc] using h : g⁻¹ * u * g = g⁻¹ * (u * z₂) * g))
    exact this
  exact hz₂ (by simpa using this.symm)

end API

theorem final_contradiction {G : Type*} [Group G] [Finite G] {K R G₂ : Subgroup G}
    (e : K ≃* alternatingGroup (Fin 6))
    {z₂ u s : G} {τ : Perm (Fin 6)}
    (hKG₂ : K ≤ G₂) (hN : G₂ ≤ Subgroup.normalizer (K : Set G)) (hz₂ : z₂ ≠ 1)
    (hz₂K : z₂ ∈ Subgroup.centralizer (K : Set G)) (hz₂G : z₂ ∈ G₂)
    (huG : u ∈ G₂) (huR : u ∈ R) (hu : u ∈ conjClass z₂) (huz : u * z₂ ∈ conjClass z₂)
    (hτ : τ.IsSwap) (hτu : InducesPerm e u τ)
    (huRK : ∀ r ∈ R ⊓ K, u * r = r * u) (hRK : Nat.card ↥(R ⊓ K) = 8)
    (hBR : G₂ ⊓ Subgroup.centralizer (K : Set G) ≤ R)
    (hsurj : ∀ α : MulAut ↥K, ∃ g ∈ G₂, ∀ k : K, ((α k : K) : G) = g⁻¹ * (k : G) * g)
    (h37 : ∀ y ∈ conjClass z₂, y ∈ R → y ∈ R ⊓ K ∨ y ∈ conjR (R ⊓ K) s)
    (h5 : {y | y ∈ conjClass z₂ ∧ y ∈ R ⊓ K}.ncard = 5) : False := by
  classical
  have huN : u ∈ Subgroup.normalizer (K : Set G) := hN huG
  let D : Subgroup (alternatingGroup (Fin 6)) := ((R ⊓ K).subgroupOf K).map e.toMonoidHom
  have hDcard : Nat.card D = 8 := by
    rw [Subgroup.card_map_of_injective e.injective, ← hRK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hDmem : ∀ d ∈ D, ∃ r : K, (r : G) ∈ R ⊓ K ∧ e r = d := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hd
    exact ⟨r, hr, rfl⟩
  have hcomm : ∀ d ∈ D, τ * (d : Perm (Fin 6)) = (d : Perm (Fin 6)) * τ := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := hDmem d hd
    have h1 := hτu r r (by rw [mul_assoc, ← huRK _ hr, inv_mul_cancel_left])
    calc τ * ((e r : alternatingGroup (Fin 6)) : Perm (Fin 6))
        = τ * (τ⁻¹ * ((e r : alternatingGroup (Fin 6)) : Perm (Fin 6)) * τ) := by rw [← h1]
      _ = _ := by group
  obtain ⟨d₁, hd₁, d₂, hd₂, hs₁, hs₂, h01, h02, h12⟩ :=
    alt6_exists_three_swaps D hDcard τ hτ hcomm
  have hy : ∀ d ∈ D, ∃ y ∈ G₂, y ∈ R ∧ InducesPerm e y (τ * (d : Perm (Fin 6))) := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := hDmem d hd
    refine ⟨u * r, G₂.mul_mem huG (hKG₂ r.2), R.mul_mem huR hr.1, ?_⟩
    exact inducesPerm_mul e huN hτu (inducesPerm_of_mem e r)
  let Ss : Set G := {y | y ∈ conjClass z₂ ∧ y ∈ conjR (R ⊓ K) s}
  have hSs : Ss.ncard = 5 := by
    have h := Set.ncard_image_of_injective {y | y ∈ conjClass z₂ ∧ y ∈ R ⊓ K}
      (f := fun y : G => s⁻¹ * y * s) (fun a b hab => by simpa using hab)
    rw [image_conj_eq] at h
    rw [h5] at h
    exact h
  let P : Perm (Fin 6) → Set G := fun c =>
    {w | w ∈ conjClass z₂ ∧ w ∈ conjR (R ⊓ K) s ∧ w ∈ G₂ ∧ InducesPerm e w c}
  have hPsub : ∀ c, P c ⊆ Ss := fun c w hw => ⟨hw.1, hw.2.1⟩
  have hP2 : ∀ c : Perm (Fin 6), c.IsSwap → (∃ y ∈ G₂, y ∈ R ∧ InducesPerm e y c) →
      2 ≤ (P c).ncard := by
    intro c hc ⟨y, hyG, hyR, hyc⟩
    obtain ⟨w, w', hne, hw, hw'⟩ :=
      two_conjugates e hN hz₂ hz₂K hz₂G huG hu huz hτ hτu hc hBR hsurj h37 hyG hyR hyc
    have hsub : ({w, w'} : Set G) ⊆ P c := by
      intro x hx
      rcases hx with rfl | rfl
      · exact hw
      · exact hw'
    calc 2 = ({w, w'} : Set G).ncard := (Set.ncard_pair hne).symm
      _ ≤ (P c).ncard := Set.ncard_le_ncard hsub
  have hdisj : ∀ c c' : Perm (Fin 6), c ≠ c' → Disjoint (P c) (P c') := by
    intro c c' hcc'
    rw [Set.disjoint_left]
    intro w hw hw'
    exact hcc' (inducesPerm_unique e (hN hw.2.2.1) hw.2.2.2 hw'.2.2.2)
  have hτ0 : (∃ y ∈ G₂, y ∈ R ∧ InducesPerm e y τ) := ⟨u, huG, huR, hτu⟩
  have p0 := hP2 τ hτ hτ0
  have p1 := hP2 _ hs₁ (hy d₁ hd₁)
  have p2 := hP2 _ hs₂ (hy d₂ hd₂)
  have hU : (P τ ∪ P (τ * (d₁ : Perm (Fin 6))) ∪ P (τ * (d₂ : Perm (Fin 6)))).ncard =
      (P τ).ncard + (P (τ * (d₁ : Perm (Fin 6)))).ncard + (P (τ * (d₂ : Perm (Fin 6)))).ncard := by
    rw [Set.ncard_union_eq, Set.ncard_union_eq (hdisj _ _ h01)]
    rw [Set.disjoint_union_left]
    exact ⟨hdisj _ _ h02, hdisj _ _ h12⟩
  have hsubU : P τ ∪ P (τ * (d₁ : Perm (Fin 6))) ∪ P (τ * (d₂ : Perm (Fin 6))) ⊆ Ss := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact hPsub _ hx
    · exact hPsub _ hx
    · exact hPsub _ hx
  have := Set.ncard_le_ncard hsubU
  omega

end CFSG.QuasithinUnique.DoubleA3
