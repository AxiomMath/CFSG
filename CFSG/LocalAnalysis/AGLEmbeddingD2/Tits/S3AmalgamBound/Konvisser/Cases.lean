module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Config
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Counting
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_lt_of_le_card {A C B : Subgroup G} {i : ℕ} (hAC : A < C) (hCB : C ≤ B)
    (hA : Nat.card A = 3 ^ i) (hB : Nat.card B = 3 ^ (i + 1)) : C = B := by
  have hd : Nat.card C ∣ 3 ^ (i + 1) := hB ▸ Subgroup.card_dvd_of_le hCB
  obtain ⟨t, ht, hCt⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hlt : Nat.card A < Nat.card C :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hAC.le)
      (fun h => hAC.ne (Subgroup.eq_of_le_of_card_ge hAC.le h.ge))
  rw [hA, hCt] at hlt
  have : i < t := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have : t = i + 1 := by omega
  apply Subgroup.eq_of_le_of_card_ge hCB
  rw [hB, hCt, this]

namespace Cfg

variable {j : ℕ} (c : Cfg G j)

abbrev J : Subgroup G := c.S ⊓ c.N

theorem comm_mem {s n : G} (hs : s ∈ c.S) (hn : n ∈ c.N) : s * n * s⁻¹ * n⁻¹ ∈ c.J := by
  have hMn := c.hMn
  have hNn := c.hNn
  refine ⟨?_, ?_⟩
  · have : s * n * s⁻¹ * n⁻¹ = s * (n * s⁻¹ * n⁻¹) := by group
    rw [this]
    exact c.S.mul_mem hs (c.hSn n (c.hNM hn) s⁻¹ (c.S.inv_mem hs) |> fun h => by
      simpa [mul_assoc] using h)
  · exact c.N.mul_mem (Subgroup.Normal.conj_mem hNn n hn s) (c.N.inv_mem hn)

theorem J_le_N : c.J ≤ c.N := inf_le_right

theorem J_le_S : c.J ≤ c.S := inf_le_left

theorem not_S_le_N : ¬ c.S ≤ c.N := by
  intro h
  have := Subgroup.card_le_of_le h
  rw [c.hSc, c.hNc] at this
  have := Nat.pow_le_pow_iff_right (show 1 < 3 by norm_num) |>.mp this
  omega

theorem J_ne_bot : c.J ≠ ⊥ := by
  intro h
  apply c.not_S_le_N
  intro s hs
  refine c.centralizer_le hs fun n hn => ?_
  have := c.comm_mem hs hn
  rw [h, Subgroup.mem_bot] at this
  calc s * n = s * n * s⁻¹ * n⁻¹ * n * s := by group
    _ = n * s := by rw [this]; group

theorem J_ne_N : c.J ≠ c.N := by
  intro h
  apply c.not_S_le_N
  have hNS : c.N ≤ c.S := by rw [← h]; exact inf_le_left
  intro s hs
  exact c.centralizer_le hs fun n hn => c.hS.1 s hs n (hNS hn)

theorem mem_J_of_gen {s n₁ n₂ : G} (hs : s ∈ c.S)
    (hgen : c.N ≤ c.J ⊔ Subgroup.zpowers n₁ ⊔ Subgroup.zpowers n₂)
    (h1 : s * n₁ = n₁ * s) (h2 : s * n₂ = n₂ * s) : s ∈ c.J := by
  have hle : c.J ⊔ Subgroup.zpowers n₁ ⊔ Subgroup.zpowers n₂ ≤ Subgroup.centralizer {s} := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact c.hS.1 _ hs x (c.J_le_S hx)
    · refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact h1
    · refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact h2
  have hsN : s ∈ c.N := c.centralizer_le hs fun n hn => by
    have := hle (hgen hn)
    rw [Subgroup.mem_centralizer_iff] at this
    exact this s rfl
  exact ⟨hs, hsN⟩

theorem card_J_dvd : Nat.card c.J ∣ 3 ^ j := c.hNc ▸ Subgroup.card_dvd_of_le c.J_le_N

theorem card_J_ne_one : Nat.card c.J ≠ 1 := fun h => c.J_ne_bot (Subgroup.eq_bot_of_card_eq _ h)

theorem card_J_ne_N : Nat.card c.J ≠ 3 ^ j := fun h =>
  c.J_ne_N (Subgroup.eq_of_le_of_card_ge c.J_le_N (by rw [h, c.hNc]))

theorem J_lt_N : c.J < c.N := lt_of_le_of_ne c.J_le_N c.J_ne_N

theorem relIndex_le {n : G} (hn : n ∈ c.N) :
    (c.S ⊓ Subgroup.centralizer {n}).relIndex c.S ≤ Nat.card c.J := by
  have h1 := card_le_card_inf_centralizer_mul c.S c.J
    (fun a ha x hx => c.hS.1 a ha x (c.J_le_S hx)) c.J_le_S n
    (fun s hs => c.comm_mem hs hn)
  have h2 := Subgroup.relIndex_mul_card (H := c.S ⊓ Subgroup.centralizer {n}) (K := c.S)
  have h3 : c.S ⊓ Subgroup.centralizer {n} ⊓ c.S = c.S ⊓ Subgroup.centralizer {n} := by
    exact inf_of_le_left inf_le_left
  rw [h3] at h2
  have hpos : 0 < Nat.card (c.S ⊓ Subgroup.centralizer {n} : Subgroup G) := Nat.card_pos
  by_contra hlt
  have hlt := not_le.mp hlt
  have : Nat.card c.S < Nat.card c.S := by
    calc Nat.card c.S ≤ Nat.card (c.S ⊓ Subgroup.centralizer {n} : Subgroup G) * Nat.card c.J := h1
      _ < Nat.card (c.S ⊓ Subgroup.centralizer {n} : Subgroup G) *
          (c.S ⊓ Subgroup.centralizer {n}).relIndex c.S := by
        exact Nat.mul_lt_mul_of_pos_left hlt hpos
      _ = Nat.card c.S := by rw [mul_comm]; exact h2
  exact lt_irrefl _ this


theorem card_cs_le {n₀ : G} (hgen : c.N ≤ c.J ⊔ Subgroup.zpowers n₀) :
    Nat.card (c.S ⊓ Subgroup.centralizer {n₀} : Subgroup G) ≤ Nat.card c.J := by
  apply Subgroup.card_le_of_le
  intro s hs
  obtain ⟨hsS, hsc⟩ := Subgroup.mem_inf.mp hs
  have hsc' := Subgroup.mem_centralizer_iff.mp hsc n₀ rfl
  exact c.mem_J_of_gen (n₁ := n₀) (n₂ := 1) hsS (hgen.trans le_sup_left) hsc'.symm (by simp)

theorem N_eq_sup {i : ℕ} (hJi : Nat.card c.J = 3 ^ i) (hN : Nat.card c.N = 3 ^ (i + 1))
    {n₀ : G} (hn₀ : n₀ ∈ c.N) (hn₀J : n₀ ∉ c.J) : c.N = c.J ⊔ Subgroup.zpowers n₀ := by
  symm
  refine eq_of_lt_of_le_card (A := c.J) (i := i) ?_ (sup_le c.J_le_N
    (Subgroup.zpowers_le.mpr hn₀)) hJi hN
  refine lt_of_le_of_ne le_sup_left (fun h => hn₀J ?_)
  rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n₀)

theorem main_case (hj1 : 1 ≤ j) (hj3 : j ≤ 3) :
    j = 3 ∧ Nat.card c.J = 9 ∧ ∃ n₀ ∈ c.N, n₀ ∉ c.J ∧ c.N = c.J ⊔ Subgroup.zpowers n₀ ∧
      (∀ x ∈ c.J, ∃ s ∈ c.S, s * n₀ * s⁻¹ * n₀⁻¹ = x) ∧
      (∀ s ∈ c.S, s * n₀ = n₀ * s → s ∈ c.J) := by
  obtain ⟨i, hij, hJi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp c.card_J_dvd
  have hi0 : i ≠ 0 := by
    intro h; apply c.card_J_ne_one; rw [hJi, h]; simp
  have hij' : i ≠ j := by
    intro h; apply c.card_J_ne_N; rw [hJi, h]
  obtain ⟨n₁, hn₁N, hn₁J⟩ := IsConcreteLE.exists_of_lt c.J_lt_N
  have hmemJ : ∀ {s n : G}, s ∈ c.S → n ∈ c.N → s * n * s⁻¹ * n⁻¹ ∈ c.J := fun hs hn => c.comm_mem hs hn
  have hJc : ∀ a ∈ c.S, ∀ x ∈ c.J, a * x = x * a := fun a ha x hx => c.hS.1 a ha x (c.J_le_S hx)
  have hcases : (j = 2 ∧ i = 1) ∨ (j = 3 ∧ i = 1) ∨ (j = 3 ∧ i = 2) := by omega
  rcases hcases with ⟨hj, hi⟩ | ⟨hj, hi⟩ | ⟨hj, hi⟩
  ·
    exfalso
    have hJ3 : Nat.card c.J = 3 ^ 1 := by rw [hJi, hi]
    have hN9 : Nat.card c.N = 3 ^ (1 + 1) := by rw [c.hNc, hj]
    have hgen := c.N_eq_sup hJ3 hN9 hn₁N hn₁J
    have h1 := card_le_card_inf_centralizer_mul c.S c.J hJc c.J_le_S n₁
      (fun s hs => hmemJ hs hn₁N)
    have h2 := c.card_cs_le hgen.le
    have h3 : Nat.card c.S = 27 := by rw [c.hSc, hj]; norm_num
    have h4 : Nat.card c.J = 3 := by rw [hJ3]; norm_num
    rw [h3, h4] at h1
    rw [h4] at h2
    omega
  ·
    exfalso
    have hJ3 : Nat.card c.J = 3 ^ 1 := by rw [hJi, hi]
    have h4 : Nat.card c.J = 3 := by rw [hJ3]; norm_num
    have hN27 : Nat.card c.N = 27 := by rw [c.hNc, hj]; norm_num
    have hS81 : Nat.card c.S = 81 := by rw [c.hSc, hj]; norm_num
    set N₁ : Subgroup G := c.J ⊔ Subgroup.zpowers n₁ with hN₁
    have hJN₁ : c.J < N₁ := by
      refine lt_of_le_of_ne le_sup_left (fun h => hn₁J ?_)
      rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n₁)
    have hN₁N : N₁ ≤ c.N := sup_le c.J_le_N (Subgroup.zpowers_le.mpr hn₁N)
    by_cases hN₁eq : N₁ = c.N
    · have h1 := card_le_card_inf_centralizer_mul c.S c.J hJc c.J_le_S n₁
        (fun s hs => hmemJ hs hn₁N)
      have h2 := c.card_cs_le (n₀ := n₁) hN₁eq.ge
      rw [hS81, h4] at h1
      rw [h4] at h2
      omega
    · have hN₁lt : N₁ < c.N := lt_of_le_of_ne hN₁N hN₁eq
      obtain ⟨n₂, hn₂N, hn₂N₁⟩ := IsConcreteLE.exists_of_lt hN₁lt
      set N₂ : Subgroup G := N₁ ⊔ Subgroup.zpowers n₂ with hN₂
      have hN₁N₂ : N₁ < N₂ := by
        refine lt_of_le_of_ne le_sup_left (fun h => hn₂N₁ ?_)
        rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n₂)
      have hN₂N : N₂ ≤ c.N := sup_le hN₁N (Subgroup.zpowers_le.mpr hn₂N)
      have hcard9 : Nat.card N₁ = 3 ^ 2 := by
        have hd : Nat.card N₁ ∣ 3 ^ 3 := by
          have := Subgroup.card_dvd_of_le hN₁N
          rwa [hN27] at this
        obtain ⟨u, hu, hu'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
        have hlt1 : Nat.card c.J < Nat.card N₁ :=
          lt_of_le_of_ne (Subgroup.card_le_of_le hJN₁.le)
            (fun h => hJN₁.ne (Subgroup.eq_of_le_of_card_ge hJN₁.le h.ge))
        have hlt2 : Nat.card N₁ < Nat.card c.N :=
          lt_of_le_of_ne (Subgroup.card_le_of_le hN₁N)
            (fun h => hN₁lt.ne (Subgroup.eq_of_le_of_card_ge hN₁N h.ge))
        rw [hu', h4] at hlt1
        rw [hu', hN27] at hlt2
        interval_cases u <;> simp_all
      have hN₂eq : N₂ = c.N :=
        eq_of_lt_of_le_card (A := N₁) (i := 2) hN₁N₂ hN₂N hcard9 (by rw [hN27]; norm_num)
      have hgen : c.N ≤ c.J ⊔ Subgroup.zpowers n₁ ⊔ Subgroup.zpowers n₂ := hN₂eq.ge
      set C₁ : Subgroup G := c.S ⊓ Subgroup.centralizer {n₁} with hC₁
      set C₂ : Subgroup G := c.S ⊓ Subgroup.centralizer {n₂} with hC₂
      have hr1 := c.relIndex_le hn₁N
      have hr2 := c.relIndex_le hn₂N
      have hr12 : (C₁ ⊓ C₂).relIndex c.S ≤ C₁.relIndex c.S * C₂.relIndex c.S :=
        Subgroup.relIndex_inf_le
      have hC12 : C₁ ⊓ C₂ ≤ c.J := by
        intro s hs
        obtain ⟨⟨hsS, hs1⟩, ⟨-, hs2⟩⟩ := hs
        exact c.mem_J_of_gen hsS hgen (Subgroup.mem_centralizer_iff.mp hs1 n₁ rfl).symm
          (Subgroup.mem_centralizer_iff.mp hs2 n₂ rfl).symm
      have hC12S : C₁ ⊓ C₂ ≤ c.S := inf_le_left.trans inf_le_left
      have h5 := Subgroup.relIndex_mul_card (H := C₁ ⊓ C₂) (K := c.S)
      rw [inf_of_le_left hC12S, hS81] at h5
      have h6 : Nat.card (C₁ ⊓ C₂ : Subgroup G) ≤ 3 := h4 ▸ Subgroup.card_le_of_le hC12
      rw [h4] at hr1 hr2
      have h7 : (C₁ ⊓ C₂).relIndex c.S ≤ 9 := hr12.trans (Nat.mul_le_mul hr1 hr2)
      have h8 : (C₁ ⊓ C₂).relIndex c.S * Nat.card (C₁ ⊓ C₂ : Subgroup G) ≤ 9 * 3 :=
        Nat.mul_le_mul h7 h6
      omega
  ·
    have hJ9 : Nat.card c.J = 3 ^ 2 := by rw [hJi, hi]
    have h9 : Nat.card c.J = 9 := by rw [hJ9]; norm_num
    have hN27 : Nat.card c.N = 3 ^ (2 + 1) := by rw [c.hNc, hj]
    have hS81 : Nat.card c.S = 81 := by rw [c.hSc, hj]; norm_num
    have hgen := c.N_eq_sup hJ9 hN27 hn₁N hn₁J
    have h1 := card_le_card_inf_centralizer_mul c.S c.J hJc c.J_le_S n₁
      (fun s hs => hmemJ hs hn₁N)
    have h2 := c.card_cs_le hgen.le
    rw [hS81, h9] at h1
    rw [h9] at h2
    have heq : Nat.card c.S =
        Nat.card (c.S ⊓ Subgroup.centralizer {n₁} : Subgroup G) * Nat.card c.J := by
      rw [hS81, h9]; omega
    refine ⟨hj, h9, n₁, hn₁N, hn₁J, hgen, ?_, ?_⟩
    · exact exists_commutator_eq c.S c.J hJc c.J_le_S n₁ (fun s hs => hmemJ hs hn₁N) heq
    · intro s hs hsc
      exact c.mem_J_of_gen (n₁ := n₁) (n₂ := 1) hs (hgen.le.trans le_sup_left) hsc (by simp)

end Cfg

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser
