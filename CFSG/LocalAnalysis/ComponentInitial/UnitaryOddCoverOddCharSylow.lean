module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverSylow
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverTrivialPrime
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddChar

open Matrix CFSG.ClassicalGroups.UnitaryFlag UnitaryOddCover
open scoped commutatorElement Pointwise

section LinearCover

theorem mem_center_of_map_mem_center {Y G : Type*} [Group Y] [Group G] [Group.IsPerfect Y]
    (ρ : Y →* G) (hcen : ρ.ker ≤ Subgroup.center Y) {x : Y} (hx : ρ x ∈ Subgroup.center G) :
    x ∈ Subgroup.center Y := by
  set A := Subgroup.zpowers x with hA
  have hAc : ⁅A, (⊤ : Subgroup Y)⁆ ≤ Subgroup.center Y := by
    rw [Subgroup.commutator_le]
    intro a ha y _
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    apply hcen
    rw [MonoidHom.mem_ker, map_commutatorElement, map_zpow, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hx n) (ρ y)).symm
  have h1 : ⁅⁅A, (⊤ : Subgroup Y)⁆, (⊤ : Subgroup Y)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hAc.trans (Subgroup.center_le_centralizer _))
  have h2 : ⁅⁅(⊤ : Subgroup Y), A⁆, (⊤ : Subgroup Y)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (⊤ : Subgroup Y) A]
    exact h1
  have h3 : ⁅⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆, A⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  have htop : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
    have := Group.IsPerfect.commutator_eq_top (G := Y)
    rwa [_root_.commutator_def] at this
  rw [htop] at h3
  rw [Subgroup.mem_center_iff]
  intro y
  have hc : ⁅y, x⁆ ∈ ⁅(⊤ : Subgroup Y), A⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_zpowers x)
  rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

theorem ker_eq_bot_of_sl_cover_of_three_le {k : Type} [Field k] [Finite k] (hk : 5 ≤ Nat.card k)
    {n : ℕ} (hn : 3 ≤ n) {Y : Type*} [Group Y] [Group.IsPerfect Y]
    (ρ : Y →* SpecialLinearGroup (Fin n) k) (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center Y) : ρ.ker = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
    (by omega) hk hρ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section ρ hcen σ hσ

theorem ker_eq_bot_of_sl_two_cover {k : Type} [Field k] [Finite k] {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : Nat.card k = p ^ m) (h9 : p ^ m ≠ 9) {Y : Type*} [Group Y] [Finite Y]
    [Group.IsPerfect Y] (ρ : Y →* SpecialLinearGroup (Fin 2) k) (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center Y) (hp : IsPGroup p ρ.ker) : ρ.ker = ⊥ := by
  set π : Y →* ProjectiveSpecialLinearGroup (Fin 2) k :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) k))).comp ρ with hπ
  have hπs : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp hρ
  have hπc : π.ker ≤ Subgroup.center Y := fun y hy => by
    refine mem_center_of_map_mem_center ρ hcen ?_
    rwa [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
  have hle : ρ.ker ≤ π.ker := fun y hy => by
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hy, map_one]
  have hP : IsPGroup p (ρ.ker.subgroupOf π.ker) :=
    hp.comap_of_injective _ π.ker.subtype_injective
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have hQ1 := CFSG.SectionRank.OddCover.psl_two_sylow_kernel_eq_bot hp2 hk h9 π hπs hπc Q
  rw [eq_bot_iff]
  intro y hy
  have hmem : (⟨y, hle hy⟩ : π.ker) ∈ ρ.ker.subgroupOf π.ker := hy
  have h1 := hQ hmem
  rw [hQ1, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

end LinearCover

variable {p f : ℕ} {K : Type} [Field K] {r : ℕ} {E : Type*} [Group E]

theorem ker_eq_bot_of_lifts [Fact p.Prime] {h : UnitaryFieldData p f K} {θ : E →* hypPSU h r 1}
    [Finite E] [Group.IsPerfect E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (hp : IsPGroup p θ.ker) (hr : 1 ≤ r) (M₀ : Subgroup E)
    (hM₀N : M₀ ≤ preN θ) (hM₀inj : ∀ y ∈ M₀, θ y = 1 → y = 1)
    (hM₀surj : ∀ {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hx : IsRad h x C),
      ∃ y ∈ M₀, θ y = hypProj h r 1 (nElt hx))
    (hM₀norm : ∀ (A : SpecialLinearGroup (Fin r) K) (u : E),
      θ u = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) →
        ∀ y, y ∈ M₀ ↔ u * y * u⁻¹ ∈ M₀)
    (Y : Subgroup E) (hYinj : ∀ y ∈ Y, θ y = 1 → y = 1)
    (hYsurj : ∀ A ∈ LinearFlag.unitriangular r K,
      ∃ y ∈ Y, θ y = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A))) :
    θ.ker = ⊥ := by
  set ρ : SpecialLinearGroup (Fin r) K →* hypPSU h r 1 :=
    (hypProj h r 1).comp ((lHom h r).comp SpecialLinearGroup.toGL) with hρ
  set Ut := Y ⊓ ((LinearFlag.unitriangular r K).map ρ).comap θ with hUt
  have hUtN : Ut ≤ Subgroup.normalizer (M₀ : Set E) := by
    intro u hu
    obtain ⟨A, -, hAu⟩ := (Subgroup.mem_inf.mp hu).2
    rw [Subgroup.mem_normalizer_iff]
    exact hM₀norm A u hAu.symm
  set P₀ := M₀ ⊔ Ut with hP₀
  have hP₀mul : (P₀ : Set E) = (M₀ : Set E) * (Ut : Set E) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M₀ Ut hUtN
  have hinj : ∀ z ∈ P₀, θ z = 1 → z = 1 := by
    intro z hz hθz
    rw [← SetLike.mem_coe, hP₀mul, Set.mem_mul] at hz
    obtain ⟨m, hm, u, hu, rfl⟩ := hz
    obtain ⟨_, ⟨x, C, hx, rfl⟩, hxm⟩ := hM₀N hm
    obtain ⟨A, hA, hAu⟩ := (Subgroup.mem_inf.mp hu).2
    have hAU : IsUnitriangular ((SpecialLinearGroup.toGL A : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K) := ⟨fun i j hij => hA.1 i j hij, hA.2⟩
    have h1 : hypProj h r 1 (nElt hx) * hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) =
        1 := by
      rw [hxm]
      change θ m * ρ A = 1
      rw [hAu, ← map_mul, hθz]
    have hA1 := eq_one_of_hypProj_nElt_mul_lHom hr hx hAU h1
    have hθu : θ u = 1 := by
      rw [← hAu]
      change hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) = 1
      rw [hA1, map_one, map_one]
    have hθm : θ m = 1 := by rwa [map_mul, hθu, mul_one] at hθz
    rw [hM₀inj m hm hθm, hYinj u (Subgroup.mem_inf.mp hu).1 hθu, one_mul]
  obtain ⟨-, -, -, -, ⟨S, hS⟩, -, -⟩ := unitary_order_and_Sylow h hr (le_refl 1)
  have hSle : (S : Subgroup (hypPSU h r 1)) ≤ P₀.map θ := by
    intro s hs
    rw [hS] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    obtain ⟨A, hA, x, C, hx, rfl⟩ := exists_lHom_mul_nElt_of_mem hg
    set A' : SpecialLinearGroup (Fin r) K := ⟨A, hA.det_eq_one⟩ with hA'
    have hA'U : A' ∈ LinearFlag.unitriangular r K :=
      ⟨fun i j hij => hA.1 hij, hA.2⟩
    have hA'GL : SpecialLinearGroup.toGL A' = A := Units.ext rfl
    obtain ⟨y, hy, hyA⟩ := hYsurj A' hA'U
    obtain ⟨m, hm, hmx⟩ := hM₀surj hx
    have hyU : y ∈ Ut := ⟨hy, ⟨A', hA'U, hyA.symm⟩⟩
    refine ⟨y * m, mul_mem (Subgroup.mem_sup_right hyU) (Subgroup.mem_sup_left hm), ?_⟩
    rw [map_mul, hyA, hmx, hA'GL, map_mul]
  have hle := ker_le_of_sylow_le_map_prime θ hθ hC hp S P₀ hSle
  rw [eq_bot_iff]
  intro z hz
  exact Subgroup.mem_bot.mpr (hinj z (hle hz) hz)

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddChar
