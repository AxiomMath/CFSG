module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Extend

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

structure Cfg (G : Type*) [Group G] [Finite G] (j : ℕ) where
  hG : IsPGroup 3 G
  M : Subgroup G
  N : Subgroup G
  S : Subgroup G
  hMn : M.Normal
  hNn : N.Normal
  hNM : N ≤ M
  hSM : S ≤ M
  hN : IsEA3 N
  hS : IsEA3 S
  hSn : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S
  hNc : Nat.card N = 3 ^ j
  hSc : Nat.card S = 3 ^ (j + 1)
  hno : ∀ Y : Subgroup G, Y ≤ M → Y.Normal → IsEA3 Y → Nat.card Y ≠ 3 ^ (j + 1)
  hmin : ∀ T : Subgroup G, T ≤ M → T.Normal → S ≤ T → T = M

namespace Cfg

variable {G : Type*} [Group G] [Finite G] {j : ℕ} (c : Cfg G j)

theorem pM : IsPGroup 3 c.M := c.hG.to_subgroup c.M

theorem ext_mem {x : G} (hxM : x ∈ c.M) (hxc : ∀ n ∈ c.N, x * n = n * x)
    (hxm : ∀ m ∈ c.M, m * x * m⁻¹ * x⁻¹ ∈ c.N) (hx3 : x ^ 3 = 1) : x ∈ c.N := by
  by_contra hxN
  have := c.hMn
  have := c.hNn
  obtain ⟨Y, hYM, hYn, hYe, hYc⟩ :=
    exists_normal_ea_extend c.hG c.hNM c.hN hxM hxN hxc hxm hx3
  apply c.hno Y hYM hYn hYe
  rw [hYc, c.hNc, pow_succ]
  ring

theorem centralizer_le {s : G} (hs : s ∈ c.S) (hsc : ∀ n ∈ c.N, s * n = n * s) : s ∈ c.N := by
  classical
  have := c.hMn
  have := c.hNn
  by_contra hsN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite c.M := inferInstance
  set Q : Subgroup G := c.S ⊓ Subgroup.centralizer (c.N : Set G) with hQ
  have hQmem : ∀ q, q ∈ Q ↔ q ∈ c.S ∧ ∀ n ∈ c.N, n * q = q * n := by
    intro q
    simp only [hQ, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hQn : ∀ m ∈ c.M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := by
    intro m hm q hq
    obtain ⟨hqS, hqc⟩ := (hQmem q).mp hq
    refine (hQmem _).mpr ⟨c.hSn m hm q hqS, fun n hn => ?_⟩
    have hn' : m⁻¹ * n * m ∈ c.N := by
      simpa using Subgroup.Normal.conj_mem c.hNn n hn m⁻¹
    have := hqc _ hn'
    calc n * (m * q * m⁻¹) = m * ((m⁻¹ * n * m) * q) * m⁻¹ := by group
      _ = m * (q * (m⁻¹ * n * m)) * m⁻¹ := by rw [this]
      _ = (m * q * m⁻¹) * n := by group
  have hQN : ∀ m ∈ c.M, ∀ q ∈ Q ⊓ c.N, m * q * m⁻¹ ∈ Q ⊓ c.N := fun m hm q hq =>
    ⟨hQn m hm q hq.1, Subgroup.Normal.conj_mem c.hNn q hq.2 m⟩
  have hsQ : s ∈ Q := (hQmem s).mpr ⟨hs, fun n hn => (hsc n hn).symm⟩
  have hlt : Q ⊓ c.N < Q := lt_of_le_of_ne inf_le_left (fun h => hsN (by
    have : s ∈ Q ⊓ c.N := by rw [h]; exact hsQ
    exact this.2))
  have hQS : Q ≤ c.S := inf_le_left
  obtain ⟨x, hxQ, hxA, hxm⟩ := exists_mem_central_mod_of_normalizes (p := 3) c.pM
    (hQS.trans c.hSM) hQN hQn hlt
  obtain ⟨hxS, hxc⟩ := (hQmem x).mp hxQ
  apply hxA
  refine ⟨hxQ, c.ext_mem (c.hSM hxS) (fun n hn => (hxc n hn).symm)
    (fun m hm => (hxm m hm).2) (c.hS.2 x hxS)⟩

end Cfg

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser
