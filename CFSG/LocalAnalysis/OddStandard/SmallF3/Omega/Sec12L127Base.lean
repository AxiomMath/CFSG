module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec127_betaOf_of_mem {V : Subgroup G} {n : G} (hn : n ∈ normalizer (V : Set G)) :
    betaOf V n = V.normalizerMonoidHom ⟨n, hn⟩ := by
  unfold betaOf
  rw [dif_pos hn]

theorem sec127_betaOf_apply {V : Subgroup G} {n : G} (hn : n ∈ normalizer (V : Set G))
    (v : ↥V) : ((betaOf V n v : ↥V) : G) = n * v * n⁻¹ := by
  rw [sec127_betaOf_of_mem hn]
  rfl

theorem sec127_betaOf_mul {V : Subgroup G} {m n : G} (hm : m ∈ normalizer (V : Set G))
    (hn : n ∈ normalizer (V : Set G)) : betaOf V (m * n) = betaOf V m * betaOf V n := by
  have hmn : m * n ∈ normalizer (V : Set G) := (normalizer (V : Set G)).mul_mem hm hn
  rw [sec127_betaOf_of_mem hmn, sec127_betaOf_of_mem hm, sec127_betaOf_of_mem hn]
  exact map_mul V.normalizerMonoidHom ⟨m, hm⟩ ⟨n, hn⟩

theorem sec127_betaOf_inv {V : Subgroup G} {n : G} (hn : n ∈ normalizer (V : Set G)) :
    betaOf V n⁻¹ = (betaOf V n)⁻¹ := by
  have hi : n⁻¹ ∈ normalizer (V : Set G) := (normalizer (V : Set G)).inv_mem hn
  rw [sec127_betaOf_of_mem hi, sec127_betaOf_of_mem hn]
  exact map_inv V.normalizerMonoidHom ⟨n, hn⟩

theorem sec127_betaOf_eq_one_iff {V : Subgroup G} {n : G} (hn : n ∈ normalizer (V : Set G)) :
    betaOf V n = 1 ↔ n ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h
    have h2 : n * v * n⁻¹ = v := by
      simpa [sec127_betaOf_apply hn] using h1
    calc v * n = (n * v * n⁻¹) * n := by rw [h2]
      _ = n * v := by group
  · intro h
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [sec127_betaOf_apply hn]
    have h1 : (v : G) * n = n * v := h v v.2
    calc n * (v : G) * n⁻¹ = (v : G) * n * n⁻¹ := by rw [h1]
      _ = v := by group

theorem sec127_betaOf_one {V : Subgroup G} : betaOf V 1 = 1 :=
  (sec127_betaOf_eq_one_iff (normalizer (V : Set G)).one_mem).mpr (Subgroup.one_mem _)

theorem sec127_betaOf_conj {V : Subgroup G} {n t : G} (hn : n ∈ normalizer (V : Set G))
    (ht : t ∈ normalizer (V : Set G)) :
    betaOf V (n * t * n⁻¹) = betaOf V n * betaOf V t * (betaOf V n)⁻¹ := by
  have hnt : n * t ∈ normalizer (V : Set G) := (normalizer (V : Set G)).mul_mem hn ht
  rw [sec127_betaOf_mul hnt ((normalizer (V : Set G)).inv_mem hn), sec127_betaOf_mul hn ht,
    sec127_betaOf_inv hn]

theorem sec127_betaOf_eq_iff {V : Subgroup G} {m n : G} (hm : m ∈ normalizer (V : Set G))
    (hn : n ∈ normalizer (V : Set G)) :
    betaOf V m = betaOf V n ↔ m⁻¹ * n ∈ centralizer (V : Set G) := by
  have hmi : m⁻¹ ∈ normalizer (V : Set G) := (normalizer (V : Set G)).inv_mem hm
  rw [← sec127_betaOf_eq_one_iff ((normalizer (V : Set G)).mul_mem hmi hn),
    sec127_betaOf_mul hmi hn, sec127_betaOf_inv hm]
  exact inv_mul_eq_one.symm

theorem sec127_mem_secNb_iff {V : Subgroup G} {b : MulAut ↥V} :
    b ∈ secNb V ↔ ∃ n ∈ normalizer (V : Set G), b = betaOf V n := by
  unfold secNb autIn secN
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨n, hn⟩, -, rfl⟩
    exact ⟨n, hn, (sec127_betaOf_of_mem hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, Subgroup.mem_subgroupOf.mpr hn, (sec127_betaOf_of_mem hn).symm⟩

theorem sec127_mem_autIn_iff {V X : Subgroup G} {b : MulAut ↥V} :
    b ∈ autIn X V ↔ ∃ n ∈ X, n ∈ normalizer (V : Set G) ∧ b = betaOf V n := by
  unfold autIn
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨n, hn⟩, hnX, rfl⟩
    exact ⟨n, Subgroup.mem_subgroupOf.mp hnX, hn, (sec127_betaOf_of_mem hn).symm⟩
  · rintro ⟨n, hnX, hn, rfl⟩
    exact ⟨⟨n, hn⟩, Subgroup.mem_subgroupOf.mpr hnX, (sec127_betaOf_of_mem hn).symm⟩

theorem sec127_autIn_mono {V X Y : Subgroup G} (h : X ≤ Y) : autIn X V ≤ autIn Y V := by
  intro b hb
  obtain ⟨n, hnX, hnN, rfl⟩ := sec127_mem_autIn_iff.mp hb
  exact sec127_mem_autIn_iff.mpr ⟨n, h hnX, hnN, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
