module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem actsAs_pow {g : G} {α : MulAut (L ⧸ center L)} (h : ActsAs L g α) (n : ℕ) :
    ActsAs L (g ^ n) (α ^ n) := by
  induction n with
  | zero => simpa using actsAs_one L
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact actsAs_mul L ih h

private theorem actsAs_zpow {g : G} {α : MulAut (L ⧸ center L)} (h : ActsAs L g α) (k : ℤ) :
    ActsAs L (g ^ k) (α ^ k) := by
  rcases lt_or_ge k 0 with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hk
    simpa [zpow_negSucc] using actsAs_inv L (actsAs_pow h (n + 1))
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simpa [zpow_natCast] using actsAs_pow h n

private theorem A_le_S (s : Setting3 G L) : s.fr.A ≤ s.fr.S :=
  Subgroup.closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)

theorem isPerfect_of_hrSetting (hS : HRSetting G L) : Group.IsPerfect ↥L := by
  exact ⟨hS.std.standard.1.1⟩

theorem s3_actsAs_gens :
    ActsAs L s.fr.a₁ s.fr'.a₁ ∧ ActsAs L s.fr.b₁ s.fr'.b₁ ∧ ActsAs L s.fr.a₂ s.fr'.a₂ ∧
      ActsAs L s.fr.b₂ s.fr'.b₂ ∧ ActsAs L s.fr.h₀ s.fr'.h₀ ∧ ActsAs L s.fr.z s.fr'.z := by
  obtain ⟨⟨-, hu₁⟩, ⟨-, hb₁⟩, ⟨-, hu₂⟩, ⟨-, hb₂⟩, ⟨-, hh₀⟩⟩ := s.lift
  refine ⟨?_, hb₁, ?_, hb₂, hh₀, ?_⟩
  · show ActsAs L (s.fr.u₁ * s.fr.b₁ ^ 3 * s.fr.u₁⁻¹)
      (s.fr'.u₁ * s.fr'.b₁ ^ 3 * s.fr'.u₁⁻¹)
    exact actsAs_mul L (actsAs_mul L hu₁ (actsAs_pow hb₁ 3)) (actsAs_inv L hu₁)
  · show ActsAs L (s.fr.u₂ * s.fr.b₂ ^ 3 * s.fr.u₂⁻¹)
      (s.fr'.u₂ * s.fr'.b₂ ^ 3 * s.fr'.u₂⁻¹)
    exact actsAs_mul L (actsAs_mul L hu₂ (actsAs_pow hb₂ 3)) (actsAs_inv L hu₂)
  · show ActsAs L (s.fr.b₁ ^ 2) (s.fr'.b₁ ^ 2)
    exact actsAs_pow hb₁ 2

theorem s3_S_le_N : s.fr.S ≤ normalizer (L : Set G) :=
  s.sylow_S.1.trans Subgroup.le_normalizer

theorem s3_A_le_N : s.fr.A ≤ normalizer (L : Set G) :=
  (A_le_S s).trans (s3_S_le_N s)

theorem s3_jSub_S : jSub L s.fr.S = s.fr'.S := by
  obtain ⟨ha₁, hb₁, ha₂, hb₂, hh₀, _⟩ := s3_actsAs_gens s
  refine le_antisymm ?_ ?_
  · intro α hα
    rw [mem_jSub L] at hα
    obtain ⟨g, hgS, hag⟩ := hα
    have key : ∀ g ∈ s.fr.S, ∃ β ∈ s.fr'.S, ActsAs L g β := by
      intro g hg
      have hg' : g ∈ Subgroup.closure
          ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀} : Set G) := hg
      refine Subgroup.closure_induction
        (p := fun g _ => ∃ β ∈ s.fr'.S, ActsAs L g β) ?_ ?_ ?_ ?_ hg'
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact ⟨s.fr'.a₁, Subgroup.subset_closure (by simp), ha₁⟩
        · exact ⟨s.fr'.b₁, Subgroup.subset_closure (by simp), hb₁⟩
        · exact ⟨s.fr'.a₂, Subgroup.subset_closure (by simp), ha₂⟩
        · exact ⟨s.fr'.b₂, Subgroup.subset_closure (by simp), hb₂⟩
        · exact ⟨s.fr'.h₀, Subgroup.subset_closure (by simp), hh₀⟩
      · exact ⟨1, one_mem _, actsAs_one L⟩
      · intro x y _ _ ihx ihy
        obtain ⟨β, hβ, haβ⟩ := ihx
        obtain ⟨γ, hγ, haγ⟩ := ihy
        exact ⟨β * γ, mul_mem hβ hγ, actsAs_mul L haβ haγ⟩
      · intro x _ ihx
        obtain ⟨β, hβ, haβ⟩ := ihx
        exact ⟨β⁻¹, inv_mem hβ, actsAs_inv L haβ⟩
    obtain ⟨β, hβ, haβ⟩ := key g hgS
    rw [actsAs_unique L hag haβ]
    exact hβ
  · show Subgroup.closure
        ({s.fr'.a₁, s.fr'.b₁, s.fr'.a₂, s.fr'.b₂, s.fr'.h₀} : Set (MulAut (L ⧸ center L))) ≤
      jSub L s.fr.S
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact (mem_jSub L).mpr ⟨s.fr.a₁, Subgroup.subset_closure (by simp), ha₁⟩
    · exact (mem_jSub L).mpr ⟨s.fr.b₁, Subgroup.subset_closure (by simp), hb₁⟩
    · exact (mem_jSub L).mpr ⟨s.fr.a₂, Subgroup.subset_closure (by simp), ha₂⟩
    · exact (mem_jSub L).mpr ⟨s.fr.b₂, Subgroup.subset_closure (by simp), hb₂⟩
    · exact (mem_jSub L).mpr ⟨s.fr.h₀, Subgroup.subset_closure (by simp), hh₀⟩

theorem s3_jSub_A : jSub L s.fr.A = s.fr'.A := by
  obtain ⟨ha₁, hb₁, ha₂, hb₂, _, _⟩ := s3_actsAs_gens s
  refine le_antisymm ?_ ?_
  · intro α hα
    rw [mem_jSub L] at hα
    obtain ⟨g, hgA, hag⟩ := hα
    have key : ∀ g ∈ s.fr.A, ∃ β ∈ s.fr'.A, ActsAs L g β := by
      intro g hg
      have hg' : g ∈ Subgroup.closure
          ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂} : Set G) := hg
      refine Subgroup.closure_induction
        (p := fun g _ => ∃ β ∈ s.fr'.A, ActsAs L g β) ?_ ?_ ?_ ?_ hg'
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨s.fr'.a₁, Subgroup.subset_closure (by simp), ha₁⟩
        · exact ⟨s.fr'.b₁, Subgroup.subset_closure (by simp), hb₁⟩
        · exact ⟨s.fr'.a₂, Subgroup.subset_closure (by simp), ha₂⟩
        · exact ⟨s.fr'.b₂, Subgroup.subset_closure (by simp), hb₂⟩
      · exact ⟨1, one_mem _, actsAs_one L⟩
      · intro x y _ _ ihx ihy
        obtain ⟨β, hβ, haβ⟩ := ihx
        obtain ⟨γ, hγ, haγ⟩ := ihy
        exact ⟨β * γ, mul_mem hβ hγ, actsAs_mul L haβ haγ⟩
      · intro x _ ihx
        obtain ⟨β, hβ, haβ⟩ := ihx
        exact ⟨β⁻¹, inv_mem hβ, actsAs_inv L haβ⟩
    obtain ⟨β, hβ, haβ⟩ := key g hgA
    rw [actsAs_unique L hag haβ]
    exact hβ
  · show Subgroup.closure
        ({s.fr'.a₁, s.fr'.b₁, s.fr'.a₂, s.fr'.b₂} : Set (MulAut (L ⧸ center L))) ≤
      jSub L s.fr.A
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (mem_jSub L).mpr ⟨s.fr.a₁, Subgroup.subset_closure (by simp), ha₁⟩
    · exact (mem_jSub L).mpr ⟨s.fr.b₁, Subgroup.subset_closure (by simp), hb₁⟩
    · exact (mem_jSub L).mpr ⟨s.fr.a₂, Subgroup.subset_closure (by simp), ha₂⟩
    · exact (mem_jSub L).mpr ⟨s.fr.b₂, Subgroup.subset_closure (by simp), hb₂⟩

theorem s3_jSub_Z : jSub L s.fr.Z = s.fr'.Z := by
  obtain ⟨_, _, _, _, _, hz⟩ := s3_actsAs_gens s
  show jSub L (zpowers s.fr.z) = zpowers s.fr'.z
  refine le_antisymm ?_ ?_
  · intro α hα
    rw [mem_jSub L] at hα
    obtain ⟨g, hg, hag⟩ := hα
    rw [Subgroup.mem_zpowers_iff] at hg
    obtain ⟨k, hk⟩ := hg
    have hact : ActsAs L (s.fr.z ^ k) (s.fr'.z ^ k) := actsAs_zpow hz k
    have h1 : ActsAs L (s.fr.z ^ k) α := by rw [hk]; exact hag
    have hαeq : α = s.fr'.z ^ k := (actsAs_unique L hact h1).symm
    rw [hαeq]
    exact Subgroup.zpow_mem_zpowers s.fr'.z k
  · rw [Subgroup.zpowers_le]
    exact (mem_jSub L).mpr ⟨s.fr.z, Subgroup.mem_zpowers s.fr.z, hz⟩

theorem s3_inj_on_S (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) {x y : G}
    {α : MulAut (L ⧸ center L)} (hx : x ∈ s.fr.S) (hy : y ∈ s.fr.S) (hax : ActsAs L x α)
    (hay : ActsAs L y α) : x = y := by
  let d : G := x⁻¹ * y
  have hdS : d ∈ s.fr.S := mul_mem (inv_mem hx) hy
  have hdL : d ∈ L := s.sylow_S.1 hdS
  have hact : ActsAs L d (1 : MulAut (L ⧸ center L)) := by
    have h := actsAs_mul L (actsAs_inv L hax) hay
    simpa [d] using h
  have hdC : d ∈ centralizer (L : Set G) := by
    haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
    exact (actsAs_one_iff L).mp hact
  have hz : (⟨d, hdL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hdC g g.2)
  have hdvd : orderOf (⟨d, hdL⟩ : ↥L) ∣ Nat.card ↥(center ↥L) :=
    (center ↥L).orderOf_dvd_natCard hz
  have hdvd' : orderOf d ∣ Nat.card ↥(center ↥L) := by
    rwa [Subgroup.orderOf_mk d hdL] at hdvd
  have hodd : Odd (orderOf d) := Odd.of_dvd_nat hZ hdvd'
  obtain ⟨k, hk⟩ := (s.sylow_S.2.1).exists_pow_pow_eq_one (⟨d, hdS⟩ : ↥s.fr.S)
  have hkG : d ^ 2 ^ k = 1 := by
    simpa using congrArg (Subtype.val) hk
  have hdvd2 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hkG
  have hd_eq_one : d = 1 := by
    rw [← orderOf_eq_one_iff]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    cases j with
    | zero => simpa using hj
    | succ j =>
        exfalso
        exact (Nat.not_even_iff_odd.mpr hodd)
          (by rw [hj]; exact Even.pow_of_ne_zero even_two (Nat.succ_ne_zero j))
  have : x⁻¹ * y = 1 := by simpa [d] using hd_eq_one
  exact eq_of_inv_mul_eq_one this

theorem s3_jOn_S_injective (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) :
    Function.Injective (jOn L (s3_S_le_N s)) := by
  intro x y hxy
  apply Subtype.ext
  exact s3_inj_on_S s hS hZ x.2 y.2 (jOn_actsAs L (s3_S_le_N s) x) (by
    rw [hxy]
    exact jOn_actsAs L (s3_S_le_N s) y)

end CFSG.OddStandard.HigherRank.YamadaG23
