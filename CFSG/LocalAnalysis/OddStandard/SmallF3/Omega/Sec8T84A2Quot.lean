module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A2Vec
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec8t84a2_quot_split {K V X : Type*} [Group K] [Group V] [Finite V] {Bs : Subgroup K}
    (hBs : ∀ b ∈ Bs, ∀ k : K, b * k = k * b)
    (hKc : ∀ x y : K, x * y * x⁻¹ * y⁻¹ ∈ Bs) (hK2 : ∀ x : K, x * x ∈ Bs)
    (hVc : ∀ u v : V, u * v = v * u) (hV2 : ∀ v : V, v * v = 1) (hV16 : Nat.card V = 16)
    (t : K) (ht : t ∉ Bs) (τ : K →* V) (hτ : Function.Surjective τ)
    (hτBs : ∀ b ∈ Bs, τ b = 1) (hτker : ∀ k, τ k = 1 → k ∈ Bs ∨ ∃ b ∈ Bs, k = t * b)
    (βK : K → K → V) (hβl : ∀ x x' y, βK (x * x') y = βK x y * βK x' y)
    (hβr : ∀ x y y', βK x (y * y') = βK x y * βK x y')
    (hβBl : ∀ b ∈ Bs, ∀ y, βK b y = 1) (hβBr : ∀ b ∈ Bs, ∀ x, βK x b = 1)
    (halt : ∀ x, βK x x = 1) (hβt : ∀ x, βK x t = τ x)
    (σ : X → K ≃* K) (ρ : X → V ≃* V) (hσBs : ∀ x k, σ x k ∈ Bs ↔ k ∈ Bs)
    (hσt : ∀ x, σ x t = t) (hτσ : ∀ x k, τ (σ x k) = ρ x (τ k))
    (hβσ : ∀ x k k', βK (σ x k) (σ x k') = ρ x (βK k k')) :
    ∃ L1 : Subgroup K, Bs ≤ L1 ∧ t ∉ L1 ∧ (∀ k, k ∈ L1 ∨ k * t ∈ L1) ∧
      ∀ x, ∀ k ∈ L1, σ x k ∈ L1 := by
  haveI hBsn : Bs.Normal :=
    ⟨fun n hn g => by rw [← hBs n hn g, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  have hQc : ∀ x y : K ⧸ Bs, x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on y ?_
    intro b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    simpa [mul_inv_rev, inv_inv, mul_assoc] using hKc b⁻¹ a⁻¹
  have hQ2 : ∀ x : K ⧸ Bs, x * x = 1 := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro a
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hK2 a
  let π : (K ⧸ Bs) →* V :=
    QuotientGroup.lift Bs τ (fun b hb => (MonoidHom.mem_ker).mpr (hτBs b hb))
  have hπ : Function.Surjective π := by
    intro v
    obtain ⟨k, hk⟩ := hτ v
    exact ⟨QuotientGroup.mk k, by show τ k = v; exact hk⟩
  have hker_Q : ∀ q : K ⧸ Bs, π q = 1 → q = 1 ∨ q = QuotientGroup.mk t := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro k hk
    have hτk : τ k = 1 := by simpa [π] using hk
    rcases hτker k hτk with hkBs | ⟨b, hb, hkb⟩
    · left
      exact (QuotientGroup.eq_one_iff k).mpr hkBs
    · right
      rw [hkb, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).mpr hb, mul_one]
  have ht' : (QuotientGroup.mk t : K ⧸ Bs) ≠ 1 := by
    intro h
    exact ht ((QuotientGroup.eq_one_iff t).mp h)
  have hmap : ∀ x, Bs.map (σ x : K →* K) = Bs := by
    intro x
    ext k
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hσBs x b).mpr hb
    · intro hk
      exact ⟨(σ x).symm k, (hσBs x ((σ x).symm k)).mp (by simpa using hk), by simp⟩
  let σQ : X → (K ⧸ Bs) ≃* (K ⧸ Bs) :=
    fun x => QuotientGroup.congr Bs Bs (σ x) (hmap x)
  have hwl : ∀ a a' b : K, QuotientGroup.leftRel Bs a a' → βK a b = βK a' b := by
    intro a a' b haa'
    have hd : a⁻¹ * a' ∈ Bs := QuotientGroup.leftRel_apply.mp haa'
    calc βK a b = βK a b * 1 := (mul_one _).symm
      _ = βK a b * βK (a⁻¹ * a') b := by rw [hβBl (a⁻¹ * a') hd b]
      _ = βK (a * (a⁻¹ * a')) b := (hβl a (a⁻¹ * a') b).symm
      _ = βK a' b := by rw [mul_inv_cancel_left]
  have hwr : ∀ a b b' : K, QuotientGroup.leftRel Bs b b' → βK a b = βK a b' := by
    intro a b b' hbb'
    have hd : b⁻¹ * b' ∈ Bs := QuotientGroup.leftRel_apply.mp hbb'
    calc βK a b = βK a b * 1 := (mul_one _).symm
      _ = βK a b * βK a (b⁻¹ * b') := by rw [hβBr (b⁻¹ * b') hd a]
      _ = βK a (b * (b⁻¹ * b')) := (hβr a b (b⁻¹ * b')).symm
      _ = βK a b' := by rw [mul_inv_cancel_left]
  have hβQ_wd : ∀ a₁ a₂ b₁ b₂ : K, QuotientGroup.leftRel Bs a₁ b₁ →
      QuotientGroup.leftRel Bs a₂ b₂ → βK a₁ a₂ = βK b₁ b₂ :=
    fun a₁ a₂ b₁ b₂ h1 h2 => (hwl a₁ b₁ a₂ h1).trans (hwr b₁ a₂ b₂ h2)
  let βQ : (K ⧸ Bs) → (K ⧸ Bs) → V :=
    fun q q' => Quotient.liftOn₂' q q' βK hβQ_wd
  have hβQ_mk : ∀ a b : K, βQ (QuotientGroup.mk a) (QuotientGroup.mk b) = βK a b :=
    fun a b => rfl
  have hβl' : ∀ x x' y : K ⧸ Bs, βQ (x * x') y = βQ x y * βQ x' y := by
    intro x x' y
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on x' ?_
    intro a'
    refine QuotientGroup.induction_on y ?_
    intro b
    rw [← QuotientGroup.mk_mul, hβQ_mk (a * a') b, hβQ_mk a b, hβQ_mk a' b, hβl]
  have hβr' : ∀ x y y' : K ⧸ Bs, βQ x (y * y') = βQ x y * βQ x y' := by
    intro x y y'
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on y ?_
    intro b
    refine QuotientGroup.induction_on y' ?_
    intro b'
    rw [← QuotientGroup.mk_mul, hβQ_mk a (b * b'), hβQ_mk a b, hβQ_mk a b', hβr]
  have halt' : ∀ x : K ⧸ Bs, βQ x x = 1 := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro a
    rw [hβQ_mk a a, halt]
  have hβt' : ∀ x : K ⧸ Bs, βQ x (QuotientGroup.mk t) = π x := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro a
    rw [hβQ_mk a t, hβt a]
    rfl
  have hσt' : ∀ x, σQ x (QuotientGroup.mk t) = QuotientGroup.mk t := by
    intro x
    rw [QuotientGroup.congr_mk, hσt]
  have hπσ' : ∀ x q, π (σQ x q) = ρ x (π q) := by
    intro x q
    refine QuotientGroup.induction_on q ?_
    intro a
    rw [QuotientGroup.congr_mk]
    simpa [π] using hτσ x a
  have hβσ' : ∀ (x : X) (q q' : K ⧸ Bs), βQ (σQ x q) (σQ x q') = ρ x (βQ q q') := by
    intro x q q'
    refine QuotientGroup.induction_on q ?_
    intro a
    refine QuotientGroup.induction_on q' ?_
    intro a'
    rw [QuotientGroup.congr_mk, QuotientGroup.congr_mk, hβQ_mk (σ x a) (σ x a'),
      hβQ_mk a a', hβσ]
  obtain ⟨L, htL, hcover, hinv⟩ :=
    sec8t84a2_trace_split_grp (Q := K ⧸ Bs) (V := V) (X := X) hQc hQ2 hVc hV2 hV16
      σQ ρ (QuotientGroup.mk t) ht' π hπ hker_Q βQ hβl' hβr' halt' hβt' hσt' hπσ' hβσ'
  refine ⟨L.comap (QuotientGroup.mk' Bs), ?_, ?_, ?_, ?_⟩
  · intro b hb
    change (b : K ⧸ Bs) ∈ L
    rw [(QuotientGroup.eq_one_iff b).mpr hb]
    exact L.one_mem
  · intro h
    exact htL h
  · intro k
    rcases hcover (k : K ⧸ Bs) with h | h
    · left
      exact h
    · right
      simpa using h
  · intro x k hk
    have h := hinv x (k : K ⧸ Bs) hk
    rwa [QuotientGroup.congr_mk] at h

end CFSG.OddStandard.SmallF3.Omega
