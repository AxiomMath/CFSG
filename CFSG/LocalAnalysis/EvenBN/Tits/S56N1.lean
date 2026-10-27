module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N0
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec5Eleven
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.CommFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem s56_P0_le_N (d : Data G) : d.s56P0 ≤ d.N := by
  rw [s56P0_def]
  exact map_subtype_le _

theorem s56_mem_P0_of_mem_pCore (d : Data G) {p : ↥d.N} (hp : p ∈ CFSG.pCore 2 ↥d.N) :
    (p : G) ∈ d.s56P0 := by
  rw [s56P0_def]
  exact ⟨p, hp, rfl⟩

theorem s56_card_P0_eq (d : Data G) : Nat.card d.s56P0 = Nat.card (CFSG.pCore 2 ↥d.N) := by
  rw [s56P0_def]
  exact Subgroup.card_map_of_injective d.N.subtype_injective

theorem s56_P0_isPGroup (d : Data G) : IsPGroup 2 d.s56P0 := by
  rw [s56P0_def]
  exact (CFSG.pCore_isPGroup).map _

theorem s56_N_conj_P0 (d : Data G) {n p : G} (hn : n ∈ d.N) (hp : p ∈ d.s56P0) :
    n * p * n⁻¹ ∈ d.s56P0 := by
  rw [s56P0_def] at hp ⊢
  obtain ⟨p', hp', rfl⟩ := hp
  exact ⟨⟨n, hn⟩ * p' * ⟨n, hn⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥d.N)).conj_mem p' hp' ⟨n, hn⟩, rfl⟩

theorem s56_le_P0_of_normal (d : Data G) {S : Subgroup G} (hSN : S ≤ d.N) (hS2 : IsPGroup 2 S)
    (hSn : ∀ n ∈ d.N, ∀ s ∈ S, n * s * n⁻¹ ∈ S) : S ≤ d.s56P0 := by
  rw [s56P0_def]
  have hS' : (S.subgroupOf d.N).Normal := ⟨fun s hs g => by
    rw [mem_subgroupOf] at hs ⊢
    simpa using hSn g g.2 s hs⟩
  have hp : IsPGroup 2 (S.subgroupOf d.N) := hS2.of_equiv (subgroupOfEquivOfLe hSN).symm
  have hle : S.subgroupOf d.N ≤ CFSG.pCore 2 ↥d.N := le_sSup ⟨hS', hp⟩
  intro s hs
  exact ⟨⟨s, hSN hs⟩, hle (mem_subgroupOf.2 hs), rfl⟩

theorem Hyp.s56_N_decomp (h49 : d.Thm49Statement) (hd : d.Hyp) {n : G} (hn : n ∈ d.N) :
    ∃ p ∈ d.s56P0, ∃ c ∈ d.N ⊓ centralizer ({d.t} : Set G), n = p * c := by
  have h := (hd.thm511 h49).1
  have hn' : n ∈ (d.N : Set G) := hn
  rw [← h] at hn'
  obtain ⟨p, hp, c, hc, rfl⟩ := hn'
  refine ⟨p, ?_, c, hc, rfl⟩
  rw [s56P0_def]
  exact hp

theorem Hyp.s56_le_P0_of_normal_CNt (h49 : d.Thm49Statement) (hd : d.Hyp) {R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hRC : R ≤ d.N ⊓ centralizer ({d.t} : Set G))
    (hRn : ∀ c ∈ d.N ⊓ centralizer ({d.t} : Set G), ∀ r ∈ R, c * r * c⁻¹ ∈ R) :
    R ≤ d.s56P0 := by
  have hRN : R ≤ d.N := fun r hr => (mem_inf.1 (hRC hr)).1
  have hP0n : ∀ r ∈ R, ∀ p ∈ d.s56P0, r * p * r⁻¹ ∈ d.s56P0 := fun r hr p hp =>
    s56_N_conj_P0 d (hRN hr) hp
  let S : Subgroup G :=
    { carrier := {x | ∃ p ∈ d.s56P0, ∃ r ∈ R, x = p * r}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, r, hr, rfl⟩ ⟨p', hp', r', hr', rfl⟩
        refine ⟨p * (r * p' * r⁻¹), mul_mem hp (hP0n r hr p' hp'), r * r', mul_mem hr hr', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨p, hp, r, hr, rfl⟩
        refine ⟨r⁻¹ * p⁻¹ * r⁻¹⁻¹, ?_, r⁻¹, inv_mem hr, ?_⟩
        · exact hP0n r⁻¹ (inv_mem hr) p⁻¹ (inv_mem hp)
        · group }
  have hPS : d.s56P0 ≤ S := fun p hp => ⟨p, hp, 1, one_mem _, by simp⟩
  have hRS : R ≤ S := fun r hr => ⟨1, one_mem _, r, hr, by simp⟩
  have hSN : S ≤ d.N := by
    rintro _ ⟨p, hp, r, hr, rfl⟩
    exact mul_mem (s56_P0_le_N d hp) (hRN hr)
  have hSsup : S ≤ d.s56P0 ⊔ R := by
    rintro _ ⟨p, hp, r, hr, rfl⟩
    exact mul_mem (mem_sup_left hp) (mem_sup_right hr)
  have hRnorm : R ≤ normalizer (d.s56P0 : Set G) := fun r hr =>
    mem_normalizer_of_conj_mem (hP0n r hr)
  have hS2 : IsPGroup 2 S :=
    IsPGroup.to_le ((s56_P0_isPGroup d).to_sup_of_normal_left' hR2 hRnorm) hSsup
  have hSn : ∀ n ∈ d.N, ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
    rintro n hn _ ⟨p, hp, r, hr, rfl⟩
    obtain ⟨p₀, hp₀, c, hc, rfl⟩ := hd.s56_N_decomp h49 hn
    have hcN : c ∈ d.N := (mem_inf.1 hc).1
    set r' := c * r * c⁻¹ with hr'
    have hr'R : r' ∈ R := hRn c hc r hr
    have hr'N : r' ∈ d.N := hRN hr'R
    have hcp : c * p * c⁻¹ ∈ d.s56P0 := s56_N_conj_P0 d hcN hp
    have e : p₀ * c * (p * r) * (p₀ * c)⁻¹ =
        (p₀ * (c * p * c⁻¹) * p₀⁻¹) * ((p₀ * (r' * p₀⁻¹ * r'⁻¹)) * r') := by
      rw [hr']; group
    have h1 : p₀ * (c * p * c⁻¹) * p₀⁻¹ ∈ d.s56P0 :=
      s56_N_conj_P0 d (s56_P0_le_N d hp₀) hcp
    have h2 : p₀ * (r' * p₀⁻¹ * r'⁻¹) ∈ d.s56P0 :=
      mul_mem hp₀ (s56_N_conj_P0 d hr'N (inv_mem hp₀))
    rw [e]
    exact ⟨_, mul_mem h1 h2, r', hr'R, by group⟩
  exact hRS.trans (s56_le_P0_of_normal d hSN hS2 hSn)

theorem s56_B_le_N (d : Data G) : d.B ≤ d.N := fun b hb =>
  mem_normalizer_iff.2 fun h => ⟨fun hh => mul_mem (mul_mem hb hh) (inv_mem hb), fun hh => by
    have := mul_mem (mul_mem (inv_mem hb) hh) hb
    simpa [mul_assoc] using this⟩

theorem Hyp.s56_B_isPGroup (hd : d.Hyp) : IsPGroup 2 d.B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 6) hd.B_facts.2.2.2.1

theorem Hyp.s56_B_le_P0 (hd : d.Hyp) : d.B ≤ d.s56P0 :=
  s56_le_P0_of_normal d (s56_B_le_N d) hd.s56_B_isPGroup fun n hn b hb =>
    (mem_normalizer_iff.1 hn b).1 hb

theorem s56_F_le_B (d : Data G) : d.F ≤ d.B := le_sup_left

theorem s56_t_mem_B (d : Data G) : d.t ∈ d.B := mem_sup_right (mem_zpowers _)

theorem Hyp.s56_F_le_P0 (hd : d.Hyp) : d.F ≤ d.s56P0 := (s56_F_le_B d).trans hd.s56_B_le_P0

theorem Hyp.s56_t_mem_CNt (hd : d.Hyp) : d.t ∈ d.N ⊓ centralizer ({d.t} : Set G) :=
  mem_inf.2 ⟨s56_B_le_N d (s56_t_mem_B d), t_mem_centralizer d⟩

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
