module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Targets

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def AEChar (n : ℕ) : Prop :=
  ∀ (α : Finset (Fin n)) (hα : α.card = 4) (g : AEQ n), g * zBar α hα * g⁻¹ = zBar α hα →
    ∃ k₁ ∈ memBar α hα true, ∃ k₂ ∈ memBar α hα false, ∃ j : ℕ,
      g * yBar α hα * g⁻¹ = k₁ * k₂ * yBar α hα ^ j

@[expose] def AEThreeC (n : ℕ) : Prop :=
  ∀ (α : Finset (Fin n)) (hα : α.card = 4) (H : Subgroup (AEQ n)), H = Hn n → ∀ σ : ↥H →* ↥H,
    (∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r) → PermMembers H σ →
    (∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), (Disjoint α β ∨ β = α) →
      ∀ x : ↥H, (x : AEQ n) ∈ memBar β hβ c → σ x = x) →
    (∀ x : ↥H, (x : AEQ n) * zBar α hα = zBar α hα * (x : AEQ n) → σ x = x) →
    ∀ r, σ r = r

theorem aeThreeC_of_aeThree {n : ℕ} (hT : AEThree n) (hn7 : n ≠ 7) : AEThreeC n := by
  intro α hα H hH σ hit hperm hcent _
  rcases hT α hα H hH σ hit hperm hcent with h | h
  · exact absurd h hn7
  · exact h

theorem yBar_not_inner {n : ℕ} (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4)
    (k : AEQ n) (hk : k ∈ memBar α h true) :
    ∃ m ∈ memBar α h true, yBar α h * m * (yBar α h)⁻¹ ≠ k * m * k⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := hk
  obtain ⟨a0, ha0, rfl⟩ : a ∈ memK (emb α h) := ha
  obtain ⟨m0, hm0, hne⟩ := (by decide +kernel :
    ∀ a ∈ kList, ∃ m ∈ kList, yQ * m * yQ⁻¹ ≠ a * m * a⁻¹) a0 ha0
  refine ⟨mkQ n (embed (emb α h) m0), ⟨_, ⟨m0, hm0, rfl⟩, rfl⟩, fun he => hne ?_⟩
  have h1 : mkQ n (yOf (emb α h) * embed (emb α h) m0 * (yOf (emb α h))⁻¹) =
      mkQ n (embed (emb α h) a0 * embed (emb α h) m0 * (embed (emb α h) a0)⁻¹) := by
    simpa only [yBar, map_mul, map_inv] using he
  have hy := yOf_supportedOn (emb α h)
  have hm := embed_supportedOn (emb α h) m0
  have hk := embed_supportedOn (emb α h) a0
  have h2 := mkQ_inj_of_supportedOn hn ((hy.mul hm).mul hy.inv) ((hk.mul hm).mul hk.inv) h1
  apply embed_injective (emb α h)
  simpa [yOf, map_mul, map_inv] using h2

theorem comm_memBar_twin' {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) :
    ∀ x ∈ memBar α h true, ∀ y ∈ memBar α h false, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact comm_memK_memKStar (emb α h) a ha b hb

theorem yBar_mul_self {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) :
    yBar α h * yBar α h = (yBar α h)⁻¹ := by
  have h3 := yBar_pow_three α h
  rw [pow_three'] at h3
  exact eq_inv_of_mul_eq_one_left h3

theorem yBar_inv_mul_inv {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) :
    (yBar α h)⁻¹ * (yBar α h)⁻¹ = yBar α h := by
  calc (yBar α h)⁻¹ * (yBar α h)⁻¹ = (yBar α h * yBar α h)⁻¹ := (mul_inv_rev _ _).symm
    _ = yBar α h := by rw [yBar_mul_self, inv_inv]

theorem yBar_conj_inv_mem {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) {m : AEQ n}
    (hm : m ∈ memBar α h true) : (yBar α h)⁻¹ * m * yBar α h ∈ memBar α h true := by
  have h1 := yBar_conj_mem_memBar α h true _ (yBar_conj_mem_memBar α h true m hm)
  have e : (yBar α h)⁻¹ * m * yBar α h =
      yBar α h * (yBar α h * m * (yBar α h)⁻¹) * (yBar α h)⁻¹ := by
    calc (yBar α h)⁻¹ * m * yBar α h
        = (yBar α h * yBar α h) * m * ((yBar α h)⁻¹ * (yBar α h)⁻¹) := by
          rw [yBar_mul_self, yBar_inv_mul_inv]
      _ = _ := by group
  rw [e]; exact h1

theorem yBar_pow_conj_mem {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) (r : ℕ) (hr : r < 3)
    {m : AEQ n} (hm : m ∈ memBar α h true) :
    yBar α h ^ r * m * (yBar α h ^ r)⁻¹ ∈ memBar α h true := by
  interval_cases r
  · simpa using hm
  · simpa using yBar_conj_mem_memBar α h true m hm
  · have := yBar_conj_mem_memBar α h true _ (yBar_conj_mem_memBar α h true m hm)
    simpa [pow_two, mul_assoc] using this

theorem exists_conj_yBar {n : ℕ} (hn : 5 ≤ n) (hC : AEChar n) (α : Finset (Fin n))
    (h : α.card = 4) (g : AEQ n) (hz : g * zBar α h * g⁻¹ = zBar α h)
    (hK : ∀ m ∈ memBar α h true, g * m * g⁻¹ = m) :
    ∃ k₁ ∈ memBar α h true, ∃ k₂ ∈ memBar α h false,
      g * yBar α h * g⁻¹ = k₁ * k₂ * yBar α h := by
  obtain ⟨k₁, hk₁, k₂, hk₂, j, hj⟩ := hC α h g hz
  have h3 := yBar_pow_three α h
  have hr : yBar α h ^ j = yBar α h ^ (j % 3) := pow_eq_pow_mod _ h3
  rw [hr] at hj
  have hE : ∀ m ∈ memBar α h true, yBar α h * m * (yBar α h)⁻¹ =
      k₁ * (yBar α h ^ (j % 3) * m * (yBar α h ^ (j % 3))⁻¹) * k₁⁻¹ := by
    intro m hm
    have hym := yBar_conj_mem_memBar α h true m hm
    have h1 := hK _ hym
    have h2 : g * (yBar α h * m * (yBar α h)⁻¹) * g⁻¹ =
        (g * yBar α h * g⁻¹) * (g * m * g⁻¹) * (g * yBar α h * g⁻¹)⁻¹ := by group
    rw [hK m hm, hj, h1] at h2
    have hu := yBar_pow_conj_mem α h (j % 3) (Nat.mod_lt _ (by norm_num)) hm
    have hc := comm_memBar_twin' α h _ hu k₂ hk₂
    rw [h2]
    calc k₁ * k₂ * yBar α h ^ (j % 3) * m * (k₁ * k₂ * yBar α h ^ (j % 3))⁻¹
        = k₁ * (k₂ * (yBar α h ^ (j % 3) * m * (yBar α h ^ (j % 3))⁻¹) * k₂⁻¹) * k₁⁻¹ := by group
      _ = _ := by rw [← hc]; group
  have hk₁' : k₁⁻¹ ∈ memBar α h true := inv_mem hk₁
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with e | e | e
  · exfalso
    obtain ⟨m, hm, hne⟩ := yBar_not_inner hn α h k₁ hk₁
    apply hne
    rw [hE m hm, e]
    simp
  · exact ⟨k₁, hk₁, k₂, hk₂, by rw [hj, e, pow_one]⟩
  · exfalso
    obtain ⟨u, hu, hne⟩ := yBar_not_inner hn α h k₁⁻¹ hk₁'
    apply hne
    have hv : ∀ v ∈ memBar α h true, (yBar α h)⁻¹ * v * yBar α h = k₁ * v * k₁⁻¹ := by
      intro v hv
      have hm := yBar_conj_mem_memBar α h true v hv
      have := hE _ hm
      rw [e] at this
      have e2 : yBar α h * (yBar α h * v * (yBar α h)⁻¹) * (yBar α h)⁻¹ =
          (yBar α h)⁻¹ * v * yBar α h := by
        calc _ = (yBar α h * yBar α h) * v * ((yBar α h)⁻¹ * (yBar α h)⁻¹) := by group
          _ = _ := by rw [yBar_mul_self, yBar_inv_mul_inv]
      have e3 : (yBar α h ^ 2 * (yBar α h * v * (yBar α h)⁻¹) * (yBar α h ^ 2)⁻¹) = v := by
        calc _ = yBar α h ^ 3 * v * (yBar α h ^ 3)⁻¹ := by group
          _ = v := by rw [h3]; simp
      rw [e3] at this
      rw [← e2, this]
    have := hv (yBar α h * u * (yBar α h)⁻¹) (yBar_conj_mem_memBar α h true u hu)
    have e4 : (yBar α h)⁻¹ * (yBar α h * u * (yBar α h)⁻¹) * yBar α h = u := by group
    rw [e4] at this
    calc yBar α h * u * (yBar α h)⁻¹ = k₁⁻¹ * (k₁ * (yBar α h * u * (yBar α h)⁻¹) * k₁⁻¹) * k₁ := by
          group
      _ = k₁⁻¹ * u * k₁⁻¹⁻¹ := by rw [← this]; group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8
