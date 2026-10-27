module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCoreNorm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralBlockCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralSwitch
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Groups

variable {G : Type*} [Group G]

theorem exists_plane_le_of_card {E₀ : Subgroup G} (hc : Nat.card E₀ = 3 ^ 3) :
    ∃ P : Subgroup G, P ≤ E₀ ∧ Nat.card P = 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) 3 (n := 2)
    (by rw [hc]; exact pow_dvd_pow 3 (by norm_num))
  refine ⟨Q.map E₀.subtype, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective]
    exact hQ

theorem exists_plane_mem_of_card {E₀ : Subgroup G} (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hc : Nat.card E₀ = 3 ^ 3) {x : G} (hx : x ∈ E₀) (hx1 : x ≠ 1) :
    ∃ P : Subgroup G, P ≤ E₀ ∧ Nat.card P = 3 ^ 2 ∧ x ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  set x' : E₀ := ⟨x, hx⟩ with hx'
  have hord : orderOf x' = 3 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hx1 (congrArg Subtype.val h)
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hexp x hx
  have hcz : Nat.card (Subgroup.zpowers x') = 3 ^ 1 := by rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨Q, hQc, hQ⟩ := Sylow.exists_subgroup_card_pow_succ (G := E₀) (p := 3) (n := 1)
    (by rw [hc]; exact pow_dvd_pow 3 (by norm_num)) hcz
  refine ⟨Q.map E₀.subtype, ?_, ?_, ⟨x', hQ (Subgroup.mem_zpowers x'), rfl⟩⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective]
    exact hQc

theorem exists_mem_not_mem_of_card {E₀ P : Subgroup G} (hc : Nat.card E₀ = 3 ^ 3)
    (hPc : Nat.card P = 3 ^ 2) : ∃ z ∈ E₀, z ∉ P := by
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hPc]; norm_num)
  by_contra h
  push Not at h
  have hle := Subgroup.card_le_of_le (show E₀ ≤ P from fun x hx => h x hx)
  rw [hc, hPc] at hle
  omega

theorem le_sup_zpowers_of_card {E₀ P : Subgroup G} (hc : Nat.card E₀ = 3 ^ 3) (hPE : P ≤ E₀)
    (hPc : Nat.card P = 3 ^ 2) {z : G} (hz : z ∈ E₀) (hzP : z ∉ P) :
    E₀ ≤ P ⊔ Subgroup.zpowers z := by
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  set C := P ⊔ Subgroup.zpowers z with hCdef
  have hCE : C ≤ E₀ := sup_le hPE ((Subgroup.zpowers_le).2 hz)
  have hzC : z ∈ C := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hlt : P < C := lt_of_le_of_ne le_sup_left fun h => hzP (h ▸ hzC)
  haveI : Finite C := Finite.of_injective (Subgroup.inclusion hCE) (Subgroup.inclusion_injective _)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 : Nat.card C ∣ 3 ^ 3 := hc ▸ Subgroup.card_dvd_of_le hCE
  obtain ⟨k, hk3, hkC⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  rw [hPc, hkC] at h1
  have hk : k = 3 := by
    have : 2 < k := (Nat.pow_lt_pow_iff_right Nat.prime_three.one_lt).1 h1
    omega
  exact (Subgroup.eq_of_le_of_card_ge hCE (by rw [hc, hkC, hk])).symm.le

end Groups

section Diagonal


variable {τ : Tag} {L : Type} [Field L]

theorem exists_pow_of_mem_closure_rootDiag {a : Fin 2 → Fin τ.rank → Lˣ}
    (ha3 : ∀ s i, a s i ^ 3 = 1) {y : ModGL τ L}
    (hy : y ∈ Subgroup.closure (Set.range fun s => rootDiagUnit τ (a s))) :
    ∃ n₀ n₁ : ℕ, y = rootDiagUnit τ (fun i => a 0 i ^ n₀ * a 1 i ^ n₁) := by
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    fin_cases s
    · refine ⟨1, 0, congrArg _ (funext fun i => ?_)⟩
      simp
    · refine ⟨0, 1, congrArg _ (funext fun i => ?_)⟩
      simp
  | one =>
    refine ⟨0, 0, ?_⟩
    rw [← rootDiagUnit_one]
    exact congrArg _ (funext fun i => by simp)
  | mul y y' _ _ hy hy' =>
    obtain ⟨n₀, n₁, rfl⟩ := hy
    obtain ⟨m₀, m₁, rfl⟩ := hy'
    refine ⟨n₀ + m₀, n₁ + m₁, ?_⟩
    rw [← rootDiagUnit_mul]
    refine congrArg _ (funext fun i => ?_)
    rw [Pi.mul_apply, pow_add, pow_add, mul_mul_mul_comm]
  | inv y _ hy =>
    obtain ⟨n₀, n₁, rfl⟩ := hy
    refine ⟨2 * n₀, 2 * n₁, inv_eq_of_mul_eq_one_right ?_⟩
    rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
    refine congrArg _ (funext fun i => ?_)
    rw [Pi.mul_apply, Pi.one_apply, mul_mul_mul_comm, ← pow_add, ← pow_add,
      show n₀ + 2 * n₀ = 3 * n₀ by ring, show n₁ + 2 * n₁ = 3 * n₁ by ring, pow_mul, pow_mul,
      ha3, ha3, one_pow, one_pow, mul_one]

theorem pow_eq_pow_mod_three {M : Type*} [Monoid M] {x : M} (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem kills_of_mem_closure_rootDiag {a : Fin 2 → Fin Tag.E8.rank → Lˣ}
    (ha3 : ∀ s i, a s i ^ 3 = 1) (h78 : E8KillsSeventyEight a) {y : ModGL Tag.E8 L}
    (hy : y ∈ Subgroup.closure (Set.range fun s => rootDiagUnit Tag.E8 (a s))) (hy1 : y ≠ 1) :
    ∃ b : Fin Tag.E8.rank → Lˣ, y = rootDiagUnit Tag.E8 b ∧ (∀ i, b i ^ 3 = 1) ∧
      {α : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 α ∧ rootChar b α = 1}.ncard = 78 := by
  obtain ⟨n₀, n₁, rfl⟩ := exists_pow_of_mem_closure_rootDiag ha3 hy
  set c : Fin 2 → ZMod 3 := ![(n₀ : ZMod 3), (n₁ : ZMod 3)] with hcdef
  have hc0 : (c 0).val = n₀ % 3 := ZMod.val_natCast 3 n₀
  have hc1 : (c 1).val = n₁ % 3 := ZMod.val_natCast 3 n₁
  have hb : (fun i => a 0 i ^ n₀ * a 1 i ^ n₁) =
      fun i => a 0 i ^ (c 0).val * a 1 i ^ (c 1).val := by
    funext i
    rw [hc0, hc1, ← pow_eq_pow_mod_three (ha3 0 i), ← pow_eq_pow_mod_three (ha3 1 i)]
  refine ⟨_, rfl, fun i => ?_, ?_⟩
  · rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n₀, mul_comm n₁, pow_mul, pow_mul, ha3, ha3,
      one_pow, one_pow, mul_one]
  · have hcne : c ≠ 0 := by
      intro h
      apply hy1
      have h0 : (c 0).val = 0 := by rw [h]; rfl
      have h1 : (c 1).val = 0 := by rw [h]; rfl
      rw [hb, ← rootDiagUnit_one]
      refine congrArg _ (funext fun i => ?_)
      rw [h0, h1, pow_zero, pow_zero, mul_one, Pi.one_apply]
    rw [hb]
    exact h78 c hcne

end Diagonal

section Frame


variable {K : Type} [Field K] [Finite K]

theorem trace_eq_neg_four_of_triangles {P : Subgroup (adjointGroup .E8 K)}
    {D : LangPlaneData .E8 K P} {z : adjointGroup .E8 K} (F : CubeFrame D z)
    (hT : E8D4Triangles F.ω) :
    LinearMap.trace (AlgebraicClosure K) (RootModule .E8 (AlgebraicClosure K))
        ((baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL .E8 K) :
          ModGL .E8 (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule .E8 (AlgebraicClosure K))) =
      ((-4 : ℤ) : AlgebraicClosure K) := by
  rw [← F.conj_z, trace_conj, monomialElt,
    trace_rootDiagUnit_mul_canonicalRep_E8 F.b F.ω hT.1, hT.2]

theorem trace_eq_five_of_mem_plane {P : Subgroup (adjointGroup .E8 K)}
    {D : LangPlaneData .E8 K P} {y : adjointGroup .E8 K} (F : CubeFrame D y)
    (h78 : E8KillsSeventyEight F.a) {x : adjointGroup .E8 K} (hx : x ∈ P) (hx1 : x ≠ 1) :
    LinearMap.trace (AlgebraicClosure K) (RootModule .E8 (AlgebraicClosure K))
        ((baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) :
          ModGL .E8 (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule .E8 (AlgebraicClosure K))) = 5 := by
  have hne : F.g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * F.g ≠
      1 := by
    intro h
    apply hx1
    have h1 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) = 1 := by
      calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K)
          = F.g * (F.g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
              F.g) * F.g⁻¹ := by group
        _ = 1 := by rw [h]; group
    apply Subtype.ext
    apply baseChangeGL_injective (τ := Tag.E8) (algebraMap K (AlgebraicClosure K))
    rw [h1, Subgroup.coe_one, map_one]
  obtain ⟨b, hb, hb3, hk⟩ := kills_of_mem_closure_rootDiag F.exp3 h78 (F.plane x hx) hne
  have e : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) =
      F.g * rootDiagUnit .E8 b * F.g⁻¹ := by
    rw [← hb]
    group
  rw [e, trace_conj, trace_rootDiagUnit_E8_of_kills b hb3 hk]


theorem nonempty_langPlaneData_of_weyl_mem_kernel (hK3 : ¬ 3 ∣ Nat.card K)
    {E₀ P : Subgroup (adjointGroup .E8 K)} (hE₀ : IsElemAbelian 3 E₀)
    {D : LangPlaneData .E8 K P} {z : adjointGroup .E8 K} (hz : z ∈ E₀)
    (hEgen : E₀ ≤ P ⊔ Subgroup.zpowers z) (F : CubeFrame D z)
    (hW : F.ω ∈ kernelWeylGroup (familyChar F.a)) : Nonempty (LangPlaneData .E8 K E₀) := by
  obtain ⟨h, hhG, hh⟩ := F.exists_torus (monomialToralAt_three_of_block a2BlockToral_E8) hK3
    hEgen (hE₀.2 z hz) hW
  exact SeitzExcOpenRest8bAux.langPlaneData_of_toral Nat.prime_three hK3 hE₀.2 hhG hh

theorem normalizesRGroup_of_blocks {E₀ P : Subgroup (adjointGroup .E8 K)}
    (hE₀ : IsElemAbelian 3 E₀) (hPE : P ≤ E₀) {D : LangPlaneData .E8 K P}
    {z : adjointGroup .E8 K} (hz : z ∈ E₀) (hEgen : E₀ ≤ P ⊔ Subgroup.zpowers z)
    (F : CubeFrame D z) (B : KernelBlocks Tag.E8 (familyKernel F.a))
    (hB : ∀ j : Fin 3, (fun α => F.ω • α) '' B.blk j = B.blk (j + 1)) :
    NormalizesRGroup (ringChar K) E₀ := by
  obtain ⟨u₁, k, hu₁G, hu₁M, hu₁r, hF, h12, hnt⟩ := nonToralBlockCore_holds Tag.E8 (Or.inr rfl)
    K D.Fr D.hFr F.a B F.b F.ω hB F.m F.x F.m_mem F.x_stab
  have hPz : ∀ p ∈ P, Commute z p := fun p hp =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨z, hz⟩ ⟨p, hPE hp⟩)
  obtain ⟨u, hu1, hur, hcomm⟩ := exists_rational_centralizing_of_frame_orbit (Or.inr rfl) D.Fr
    D.hFr F.g F.g_mem E₀ P z (hE₀.2 z hz) hEgen hPz _ _ F.conj_z F.frame u₁ k hu₁G hu₁r hF h12
    hnt (F.commute_plane hu₁M)
  exact normalizesRGroup_of_commute hu1 hur hcomm

theorem normalizes_or_killsSeventyEight (hS1 : E8ThreeKilledPlaneBlocks)
    (hK3 : ¬ 3 ∣ Nat.card K) {E₀ : Subgroup (adjointGroup .E8 K)} (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) (hLang : IsEmpty (LangPlaneData .E8 K E₀))
    {P : Subgroup (adjointGroup .E8 K)} (hPE : P ≤ E₀) (hPc : Nat.card P = 3 ^ 2)
    (D : LangPlaneData .E8 K P) {z : adjointGroup .E8 K} (hz : z ∈ E₀) (hzP : z ∉ P)
    (F : CubeFrame D z) :
    NormalizesRGroup (ringChar K) E₀ ∨
      (E8KillsSeventyEight F.a ∧ (E8D4OrthOrbit F.a F.ω ∨ E8D4Triangles F.ω)) := by
  have hEgen := le_sup_zpowers_of_card hc hPE hPc hz hzP
  obtain ⟨α, hα, hk⟩ := langPlaneKilled_E8 K hK3 P (fun x hx => hE₀.2 x (hPE hx)) hPc D
  have hker : (familyKernel F.a).Nonempty := ⟨α, F.kills α hα hk⟩
  rcases hS1 _ F.a F.exp3 hker F.ω F.ω_pow F.ω_stab with hW | ⟨B, hB⟩ | h
  · exact (hLang.false (nonempty_langPlaneData_of_weyl_mem_kernel hK3 hE₀ hz hEgen F hW).some).elim
  · exact Or.inl (normalizesRGroup_of_blocks hE₀ hPE hz hEgen F B hB)
  · exact Or.inr h


theorem e8NonToralNormalizes_of_core (hS1 : E8ThreeKilledPlaneBlocks)
    (hD4 : E8NonToralD4Core) : E8NonToralNormalizes := by
  intro K _ _ hK3 _ E₀ hE₀ hc hLang
  classical
  have hdatum : ∀ P : Subgroup (adjointGroup .E8 K), P ≤ E₀ → Nat.card P = 3 ^ 2 →
      Nonempty (LangPlaneData .E8 K P) := by
    intro P hPE hPc
    obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩ :=
      langToralPlane_E8_three K hK3 P (fun x hx => hE₀.2 x (hPE hx)) hPc
    exact ⟨⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩⟩
  by_cases h4 : ∃ x ∈ E₀, x ≠ 1 ∧
      LinearMap.trace (AlgebraicClosure K) (RootModule .E8 (AlgebraicClosure K))
        ((baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) :
          ModGL .E8 (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule .E8 (AlgebraicClosure K))) =
        ((-4 : ℤ) : AlgebraicClosure K)
  ·
    obtain ⟨x, hxE, hx1, htr⟩ := h4
    obtain ⟨P', hP'E, hP'c, hxP'⟩ := exists_plane_mem_of_card hE₀.2 hc hxE hx1
    obtain ⟨y, hyE, hyP'⟩ := exists_mem_not_mem_of_card hc hP'c
    obtain ⟨D'⟩ := hdatum P' hP'E hP'c
    obtain ⟨F'⟩ := nonempty_cubeFrame hK3 hE₀ hc hP'E hP'c D' hyE
    rcases normalizes_or_killsSeventyEight hS1 hK3 hE₀ hc hLang hP'E hP'c D' hyE hyP' F' with
      hN | ⟨h78, -⟩
    · exact hN
    · exact (five_ne_neg_four (ringChar_algebraicClosure_ne_three hK3)
        ((trace_eq_five_of_mem_plane F' h78 hxP' hx1).symm.trans htr)).elim
  · push Not at h4
    obtain ⟨P, hPE, hPc⟩ := exists_plane_le_of_card hc
    obtain ⟨z, hzE, hzP⟩ := exists_mem_not_mem_of_card hc hPc
    have hz1 : z ≠ 1 := fun h => hzP (h ▸ P.one_mem)
    obtain ⟨D⟩ := hdatum P hPE hPc
    obtain ⟨F⟩ := nonempty_cubeFrame hK3 hE₀ hc hPE hPc D hzE
    rcases normalizes_or_killsSeventyEight hS1 hK3 hE₀ hc hLang hPE hPc D hzE hzP F with
      hN | ⟨h78, hT1 | hT3⟩
    · exact hN
    · exact hD4 K hK3 E₀ hE₀ hc hLang h4 P hPE hPc D z hzE hzP F h78 hT1
    · exact (h4 z hzE hz1 (trace_eq_neg_four_of_triangles F hT3)).elim

end Frame

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral
