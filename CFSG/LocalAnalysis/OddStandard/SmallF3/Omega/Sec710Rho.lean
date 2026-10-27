module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Cfg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec710_exists_rho_cfg [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P)
    (hF : Asc82AutFacts) (hP7 : Asc82Tab7P) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    ∃ ρ : ↥(MSub S B) →* Equiv.Perm (Fin 5),
      (∀ m : ↥(MSub S B), ρ m = 1 ↔ (m : G) ∈ centralizer (B : Set G)) ∧
        ∀ σ : Equiv.Perm (Fin 5), ∃ n : ↥(MSub S B), (n : G) ∈ L ∧ ρ n = σ := by
  have hL : IsOm6P L := hc.ctx.isOm6P
  obtain ⟨φ, hφ⟩ :=
    (hP.aut_B G L hL (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16).2.2
  have hM := sec710_M_perm h36 hP hF hP7 h78 h710b h710c hc hφ
  obtain ⟨ρ, hρ⟩ := sec710_exists_rho (φ := φ) (B := B)
    (N := L ⊓ normalizer (B : Set G)) (M := MSub S B) hφ hM
  refine ⟨ρ, ?_, ?_⟩
  · intro m
    constructor
    · intro h1
      exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
        ((sec710_rho_eq_one_iff hφ hρ m).mp h1 b hb).symm
    · intro h1
      exact (sec710_rho_eq_one_iff hφ hρ m).mpr fun b hb =>
        (Subgroup.mem_centralizer_iff.mp h1 b hb).symm
  · intro σ
    have hNM : L ⊓ normalizer (B : Set G) ≤ MSub S B := by
      rw [← sec710_inf_M_eq h78 h710c hc]
      exact inf_le_right
    obtain ⟨n, hnN, hnρ⟩ := sec710_rho_surj hφ hρ hNM σ
    exact ⟨n, hnN.1, hnρ⟩

theorem sec710_M_eq_K_sup_N [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P)
    (hF : Asc82AutFacts) (hP7 : Asc82Tab7P) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    MSub S B = (MSub S B ⊓ centralizer (B : Set G)) ⊔ (L ⊓ MSub S B) := by
  obtain ⟨ρ, hker, hsurj⟩ :=
    sec710_exists_rho_cfg h36 hP hF hP7 h78 h710b h710c hc
  apply le_antisymm
  · intro m hm
    let σ : Equiv.Perm (Fin 5) := ρ ⟨m, hm⟩
    obtain ⟨n, hnL, hnρ⟩ := hsurj σ
    let k : G := m * (n : G)⁻¹
    have hkM : k ∈ MSub S B := Subgroup.mul_mem _ hm (Subgroup.inv_mem _ n.2)
    have hρk : ρ ⟨k, hkM⟩ = 1 := by
      have hsub : (⟨k, hkM⟩ : ↥(MSub S B)) = (⟨m, hm⟩ : ↥(MSub S B)) * n⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hsub, map_mul, map_inv, hnρ]
      exact mul_inv_cancel _
    have hkK : k ∈ MSub S B ⊓ centralizer (B : Set G) :=
      ⟨hkM, (hker ⟨k, hkM⟩).mp hρk⟩
    have hmn : m = k * (n : G) := by simp only [k]; group
    rw [hmn]
    exact Subgroup.mul_mem_sup hkK ⟨hnL, n.2⟩
  · exact sup_le inf_le_left inf_le_right

theorem sec710_normal_two [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P)
    (hF : Asc82AutFacts) (hP7 : Asc82Tab7P) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {N₀ : Subgroup G} (hN₀M : N₀ ≤ MSub S B)
    (hN₀ : (N₀.subgroupOf (MSub S B)).Normal) (hC : centralizer (ASub S B : Set G) ≤ N₀)
    (hk : ∃ k : ℕ, (centralizer (ASub S B : Set G)).relIndex N₀ = 2 ^ k) :
    N₀ ≤ centralizer (B : Set G) := by
  obtain ⟨ρ, hker, hsurj⟩ :=
    sec710_exists_rho_cfg h36 hP hF hP7 h78 h710b h710c hc
  let C : Subgroup G := centralizer (ASub S B : Set G)
  let f : ↥N₀ →* Equiv.Perm (Fin 5) := ρ.comp (Subgroup.inclusion hN₀M)
  let Q : Subgroup (Equiv.Perm (Fin 5)) := f.range
  have hCM : C ≤ MSub S B := by
    show centralizer (ASub S B : Set G) ≤ normalizer (ASub S B : Set G)
    exact centralizer_le_normalizer _
  have hCB : C ≤ centralizer (B : Set G) := by
    show centralizer (ASub S B : Set G) ≤ centralizer (B : Set G)
    exact centralizer_le (fun b hb => sec79_B_le_A hc hb)
  have hkerC : ∀ c : ↥C, ρ ⟨(c : G), hCM c.2⟩ = 1 := by
    intro c
    exact (hker ⟨(c : G), hCM c.2⟩).mpr (hCB c.2)
  have hf_apply : ∀ y : ↥N₀, f y = ρ ⟨(y : G), hN₀M y.2⟩ := fun _ => rfl
  have hkerN : C.subgroupOf N₀ ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, hf_apply]
    exact hkerC ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
  obtain ⟨k, hk⟩ := hk
  have hdvd : f.ker.index ∣ 2 ^ k := by
    have h1 := Subgroup.index_dvd_of_le hkerN
    have h2 : (C.subgroupOf N₀).index = 2 ^ k := hk
    rwa [h2] at h1
  have hcarddvd : Nat.card Q ∣ 2 ^ k := by
    have h := hdvd
    rwa [Subgroup.index_ker f] at h
  obtain ⟨j, -, hQcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcarddvd
  have hQp : IsPGroup 2 Q := IsPGroup.of_card hQcard
  have hQnorm : Q.Normal := ⟨by
    intro q hq g
    obtain ⟨y, rfl⟩ := hq
    obtain ⟨m, hm⟩ := hsurj g
    have hyM : (y : G) ∈ MSub S B := hN₀M y.2
    have hy' : (⟨(y : G), hyM⟩ : ↥(MSub S B)) ∈ N₀.subgroupOf (MSub S B) := by
      rw [Subgroup.mem_subgroupOf]
      exact y.2
    have hconjN : (m : G) * (y : G) * (m : G)⁻¹ ∈ N₀ := by
      have h := hN₀.conj_mem ⟨(y : G), hyM⟩ hy' m
      exact Subgroup.mem_subgroupOf.mp h
    refine ⟨⟨(m : G) * (y : G) * (m : G)⁻¹, hconjN⟩, ?_⟩
    show f ⟨(m : G) * (y : G) * (m : G)⁻¹, hconjN⟩ = g * f y * g⁻¹
    rw [hf_apply, hf_apply]
    have hsub : (⟨(m : G) * (y : G) * (m : G)⁻¹, hN₀M hconjN⟩ : ↥(MSub S B)) =
        m * ⟨(y : G), hyM⟩ * m⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hsub, map_mul, map_mul, map_inv, hm.2]
  ⟩
  haveI : Q.Normal := hQnorm
  have hQbot : Q = ⊥ := sec710_perm5_normal_two_eq_bot Q hQp
  intro x hxN
  have hfx1 : f ⟨x, hxN⟩ = 1 := by
    have hmem : f ⟨x, hxN⟩ ∈ Q := ⟨⟨x, hxN⟩, rfl⟩
    rw [hQbot] at hmem
    simpa using hmem
  have hρ1 : ρ (Subgroup.inclusion hN₀M ⟨x, hxN⟩) = 1 := hfx1
  have hmem := (hker (Subgroup.inclusion hN₀M ⟨x, hxN⟩)).mp hρ1
  simpa using hmem

end CFSG.OddStandard.SmallF3.Omega
