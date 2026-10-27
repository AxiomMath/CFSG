module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127A5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Base

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec127_betaOf_ne_one [Finite G] {V B : Subgroup G} {t : G}
    (htN : t ∈ normalizer (V : Set G)) (hVB : V ⊓ centralizer ({t} : Set G) = B)
    (hB : Nat.card ↥B = 16) (hV : Nat.card ↥V = 256) : betaOf V t ≠ 1 := by
  intro h
  have htC : t ∈ centralizer (V : Set G) := (sec127_betaOf_eq_one_iff htN).mp h
  have hle : V ≤ centralizer ({t} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp htC) v hv
  have hVB' : V ⊓ centralizer ({t} : Set G) = V := inf_eq_left.mpr hle
  rw [hVB'] at hVB
  rw [hVB] at hV
  omega

theorem sec127_card_autIn {V X : Subgroup G} (hXN : X ≤ normalizer (V : Set G))
    (hbot : X ⊓ centralizer (V : Set G) = ⊥) : Nat.card ↥(autIn X V) = Nat.card ↥X := by
  let f : ↥X →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hXN)
  have hf : ∀ x : ↥X, f x = betaOf V x.1 := fun x => (sec127_betaOf_of_mem (hXN x.2)).symm
  have hrange : autIn X V = f.range := by
    ext b
    rw [sec127_mem_autIn_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨n, hnX, hnN, rfl⟩
      exact ⟨⟨n, hnX⟩, hf ⟨n, hnX⟩⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, hXN x.2, hf x⟩
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hf] at hx
    have h2 := (sec127_betaOf_eq_one_iff (hXN x.2)).mp hx
    have h3 : x.1 ∈ X ⊓ centralizer (V : Set G) := Subgroup.mem_inf.mpr ⟨x.2, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h3)
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem sec127_betaOf_not_mem [Finite G] {V X : Subgroup G} {t : G}
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    (hXN : X ≤ normalizer (V : Set G)) (hbot : X ⊓ centralizer (V : Set G) = ⊥)
    (hXt : X ≤ centralizer ({t} : Set G)) (htN : t ∈ normalizer (V : Set G))
    (ht1 : betaOf V t ≠ 1) : betaOf V t ∉ autIn X V := by
  intro hmem
  obtain ⟨n, hnX, hnN, hn⟩ := sec127_mem_autIn_iff.mp hmem
  apply ht1
  have hcen : ∀ x ∈ X, n * x = x * n := by
    intro x hx
    have hxN := hXN hx
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hXt hx)
    have h1 : betaOf V x * betaOf V t = betaOf V t * betaOf V x := by
      rw [← sec127_betaOf_mul hxN htN, ← sec127_betaOf_mul htN hxN, hxt]
    rw [hn, ← sec127_betaOf_mul hxN hnN, ← sec127_betaOf_mul hnN hxN] at h1
    have h2 := (sec127_betaOf_eq_iff ((normalizer (V : Set G)).mul_mem hxN hnN)
      ((normalizer (V : Set G)).mul_mem hnN hxN)).mp h1
    have h3 : (x * n)⁻¹ * (n * x) ∈ X ⊓ centralizer (V : Set G) :=
      Subgroup.mem_inf.mpr ⟨X.mul_mem (X.inv_mem (X.mul_mem hx hnX)) (X.mul_mem hnX hx), h2⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact h3.symm
  have hn1 : n = 1 := sec127_center_alt5 hA5 hnX hcen
  rw [hn, hn1]
  exact (sec127_betaOf_eq_one_iff (normalizer (V : Set G)).one_mem).mpr (Subgroup.one_mem _)

theorem sec127_index_two {Γ : Type} [Group Γ] [Finite Γ] {K H : Subgroup Γ} {g : Γ}
    (hHK : H ≤ K) (hcard : Nat.card ↥K = 2 * Nat.card ↥H) (hgK : g ∈ K) (hgH : g ∉ H)
    (hcomm : ∀ y ∈ K, g * y = y * g) {y : Γ} (hy : y ∈ K) : y ∈ H ∨ ∃ h ∈ H, y = g * h := by
  have hH0 : 0 < Nat.card ↥H := Nat.card_pos
  have hH' : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hidx : (H.subgroupOf K).index = 2 := by
    have h := Subgroup.card_mul_index (H.subgroupOf K)
    rw [hH', hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hH0 (by rw [h, mul_comm])
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  by_cases hyH : y ∈ H
  · exact Or.inl hyH
  · right
    have hg' : (⟨g, hgK⟩ : ↥K) * a ∈ H.subgroupOf K := by
      rcases ha ⟨g, hgK⟩ with h | h
      · exact h.1
      · exact absurd (Subgroup.mem_subgroupOf.mp h.1) hgH
    have hy' : (⟨y, hy⟩ : ↥K) * a ∈ H.subgroupOf K := by
      rcases ha ⟨y, hy⟩ with h | h
      · exact h.1
      · exact absurd (Subgroup.mem_subgroupOf.mp h.1) hyH
    have hmem := (H.subgroupOf K).mul_mem hy' ((H.subgroupOf K).inv_mem hg')
    rw [Subgroup.mem_subgroupOf] at hmem
    have h1 : y * g⁻¹ ∈ H := by
      have h2 : (((⟨y, hy⟩ : ↥K) * a * ((⟨g, hgK⟩ : ↥K) * a)⁻¹ : ↥K) : Γ) = y * g⁻¹ := by
        simp [mul_assoc]
      rwa [h2] at hmem
    refine ⟨y * g⁻¹, h1, ?_⟩
    have h3 := hcomm y hy
    calc y = (y * g) * g⁻¹ := by group
      _ = (g * y) * g⁻¹ := by rw [h3]
      _ = g * (y * g⁻¹) := by group

theorem sec127_cases_K [Finite G] {V X : Subgroup G} {t : G} {K : Subgroup (MulAut ↥V)}
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    (hXN : X ≤ normalizer (V : Set G)) (hbot : X ⊓ centralizer (V : Set G) = ⊥)
    (hXt : X ≤ centralizer ({t} : Set G)) (htN : t ∈ normalizer (V : Set G))
    (ht1 : betaOf V t ≠ 1) (hKX : autIn X V ≤ K) (hKcard : Nat.card ↥K = 120)
    (hKt : betaOf V t ∈ K) (hKcomm : ∀ y ∈ K, betaOf V t * y = y * betaOf V t)
    {y : MulAut ↥V} (hy : y ∈ K) :
    y ∈ autIn X V ∨ ∃ x ∈ autIn X V, y = betaOf V t * x := by
  have hX60 : Nat.card ↥(autIn X V) = 60 := by
    rw [sec127_card_autIn hXN hbot, sec127_card_alt5 hA5]
  exact sec127_index_two hKX (by rw [hKcard, hX60]) hKt
    (sec127_betaOf_not_mem hA5 hXN hbot hXt htN ht1) hKcomm hy

end CFSG.OddStandard.SmallF3.Omega
