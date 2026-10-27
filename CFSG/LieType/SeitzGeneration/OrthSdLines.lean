module

public import CFSG.LieType.SeitzGeneration.OrthSdMixing
public import CFSG.LieType.SeitzGeneration.OrthCommutator

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section Helpers

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

omit [Finite K] [FiniteDimensional K V] in
theorem polarNondegOn_of_nondegenerate {U : Submodule K V}
    (hU : (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate) : PolarNondegOn Q U :=
  fun u hu hperp => congrArg Subtype.val (hU.1 ⟨u, hu⟩ fun t => by
    simpa [polarBilin_apply_apply] using hperp t t.2)

omit [Finite K] [FiniteDimensional K V] in
theorem stable_symm_of_pow {x : V ≃ₗ[K] V} (hxp : x ^ p = 1) (hp : 0 < p) {S : Submodule K V}
    (hst : ∀ s ∈ S, x s ∈ S) : ∀ s ∈ S, x.symm s ∈ S := by
  intro s hs
  have h1 : x * x ^ (p - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hp, hxp]
  have : x⁻¹ = x ^ (p - 1) := inv_eq_of_mul_eq_one_right h1
  show x⁻¹ s ∈ S
  rw [this]
  exact pow_apply_mem hst _ s hs

omit [Finite K] in
theorem exists_block_of_fpf (hp : p.Prime) {S : Submodule K V} {x : V ≃ₗ[K] V}
    (hS : PolarNondegOn Q S) (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxp : x ^ p = 1)
    (hst : ∀ s ∈ S, x s ∈ S) (hS0 : S ≠ ⊥) (hfpf : ∀ s ∈ S, x s = s → s = 0) :
    ∃ g, IsBlock Q p S g := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have hmove : ∃ s ∈ S, x s ≠ s := ⟨s, hs, fun h => hs0 (hfpf s hs h)⟩
  exact ⟨extendId hS x hst (stable_symm_of_pow hxp hp.pos hst),
    extendId_isBlock hS hxO hxp hst (stable_symm_of_pow hxp hp.pos hst) hmove⟩

end Helpers

section Lines

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] in
theorem fpf_of_not_mem (hK : KernelLineData Q p E) (hp : p.Prime) {M : Subgroup E}
    (hM : Nat.card M = p) {a : E} (haM : a ∉ M) {v : V} (hv : v ∈ lineSpace M)
    (hfix : ((a : orthDerived Q) : V ≃ₗ[K] V) v = v) : v = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have ha1 : a ≠ 1 := fun h => haM (h ▸ M.one_mem)
  have hord : orderOf a = p := orderOf_eq_prime (hK.exp a) ha1
  have hcard : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
  have hne : M ≠ Subgroup.zpowers a := fun h => haM (h ▸ Subgroup.mem_zpowers a)
  exact eq_zero_of_fixed_lineSpace hK hp hM hcard hne
    (t := ⟨a, Subgroup.mem_zpowers a⟩) (fun h => ha1 (congrArg Subtype.val h)) hv hfix

omit [Finite K] [FiniteDimensional K V] in
theorem exists_notMem_line (hK : KernelLineData Q p E) (hp : p.Prime) {M : Subgroup E}
    (hM : Nat.card M = p) : ∃ a : E, a ∉ M := by
  by_contra h
  push Not at h
  have : M = ⊤ := eq_top_iff.mpr fun a _ => h a
  rw [this, Subgroup.card_top, hK.card] at hM
  have h1 := hp.one_lt
  have : p ^ 2 = p * p := sq p
  nlinarith

omit [Finite K] [FiniteDimensional K V] in
theorem coe_pow_eq_one (hK : KernelLineData Q p E) (a : E) :
    (((a : E) : orthDerived Q) : V ≃ₗ[K] V) ^ p = 1 := by
  have := congrArg (fun z : E => ((z : orthDerived Q) : V ≃ₗ[K] V)) (hK.exp a)
  simpa using this

omit [Finite K] in
theorem exists_block_lineSpace (hK : KernelLineData Q p E) (hp : p.Prime) {M : Subgroup E}
    (hM : Nat.card M = p) (hVM : lineSpace M ≠ ⊥) : ∃ g, IsBlock Q p (lineSpace M) g := by
  obtain ⟨a, haM⟩ := exists_notMem_line hK hp hM
  exact exists_block_of_fpf hp (polarNondegOn_of_nondegenerate (hK.regular (some ⟨M, hM⟩)))
    orthDerived_mem_orthogonalGroup (coe_pow_eq_one hK a)
    (fun s hs => lineSpace_stable hK.comm M a hs) hVM
    (fun s hs hfix => fpf_of_not_mem hK hp hM haM hs hfix)

omit [Finite K] [FiniteDimensional K V] in
theorem orthSep_lineSpace (hK : KernelLineData Q p E) {M N : Subgroup E} (hM : Nat.card M = p)
    (hN : Nat.card N = p) (hMN : M ≠ N) : OrthSep Q (lineSpace M) (lineSpace N) := by
  intro u hu w hw
  have hne : (some ⟨M, hM⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h' => hMN (congrArg Subtype.val (Option.some.inj h'))
  have := hK.orth _ _ hne u hu w hw
  rwa [polarBilin_apply_apply] at this

theorem eq_or_eq_of_active (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hrank : RankLE2 p (orthDerived Q)) (hK : KernelLineData Q p E)
    {L N : Subgroup E} (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hVL : lineSpace L ≠ ⊥) (hVN : lineSpace N ≠ ⊥) {M : Subgroup E} (hM : Nat.card M = p)
    (hVM : lineSpace M ≠ ⊥) : M = L ∨ M = N := by
  by_contra hcon
  push Not at hcon
  obtain ⟨gL, bL⟩ := exists_block_lineSpace hK hp hL hVL
  obtain ⟨gN, bN⟩ := exists_block_lineSpace hK hp hN hVN
  obtain ⟨gM, bM⟩ := exists_block_lineSpace hK hp hM hVM
  exact false_of_three_blocks hQ hT hp hp2 hrank
    (polarNondegOn_of_nondegenerate (hK.regular (some ⟨L, hL⟩)))
    (polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))) bL bN bM
    (orthSep_lineSpace hK hL hN hLN) (orthSep_lineSpace hK hL hM (Ne.symm hcon.1))
    (orthSep_lineSpace hK hN hM (Ne.symm hcon.2))

theorem lineSpace_eq_range_eline (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hrank : RankLE2 p (orthDerived Q)) (hK : KernelLineData Q p E)
    {L N : Subgroup E} (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hVN : lineSpace N ≠ ⊥) {a : E} (haL : a ∉ L) {x : V ≃ₗ[K] V}
    (hxa : x = (((a : E) : orthDerived Q) : V ≃ₗ[K] V)) {r : K[X]}
    (u : primaryComponent x.toLinearMap r) (hu : (u : V) ∈ lineSpace L) (hu0 : u ≠ 0)
    (hureg : PolarNondegOn Q (LinearMap.range (eline x r u))) :
    lineSpace L = LinearMap.range (eline x r u) := by
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hxa]; exact orthDerived_mem_orthogonalGroup
  have hxp : x ^ p = 1 := by rw [hxa]; exact coe_pow_eq_one hK a
  have hVLreg : PolarNondegOn Q (lineSpace L) :=
    polarNondegOn_of_nondegenerate (hK.regular (some ⟨L, hL⟩))
  have hVL : ∀ s ∈ lineSpace L, x s ∈ lineSpace L := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm L a hs
  have hA'L : LinearMap.range (eline x r u) ≤ lineSpace L := by
    rintro _ ⟨z, rfl⟩
    exact smul_mem_of_stable hVL z u hu
  have hstA : ∀ s ∈ LinearMap.range (eline x r u), x s ∈ LinearMap.range (eline x r u) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨AdjoinRoot.root r * z, ?_⟩
    rw [eline_apply, eline_apply, mul_smul]
    exact (coe_root_smul_primaryComponent x.toLinearMap r (z • u))
  have hsymA := stable_symm_of_pow hxp hp.pos hstA
  have hRreg := polarNondegOn_inf_perp hVLreg hureg hA'L
  have hstR : ∀ s ∈ lineSpace L ⊓ perp Q (LinearMap.range (eline x r u)),
      x s ∈ lineSpace L ⊓ perp Q (LinearMap.range (eline x r u)) := by
    intro s hs
    refine ⟨hVL s hs.1, mem_perp.mpr fun t ht => ?_⟩
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxO (x.symm t) s
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this]
    exact mem_perp.mp hs.2 _ (hsymA t ht)
  have hRbot : lineSpace L ⊓ perp Q (LinearMap.range (eline x r u)) = ⊥ := by
    by_contra hRne
    have hfpf : ∀ S : Submodule K V, S ≤ lineSpace L → ∀ s ∈ S, x s = s → s = 0 :=
      fun S hS s hs hfix => fpf_of_not_mem hK hp hL haL (hS hs) (by rw [← hxa]; exact hfix)
    have hA'ne : LinearMap.range (eline x r u) ≠ ⊥ := by
      intro h0
      have : eline x r u 1 ∈ LinearMap.range (eline x r u) := ⟨1, rfl⟩
      rw [h0, Submodule.mem_bot, eline_apply, one_smul] at this
      exact hu0 (Subtype.ext this)
    obtain ⟨gA, bA⟩ := exists_block_of_fpf hp hureg hxO hxp hstA hA'ne (hfpf _ hA'L)
    obtain ⟨gR, bR⟩ := exists_block_of_fpf hp hRreg hxO hxp hstR hRne (hfpf _ inf_le_left)
    obtain ⟨gN, bN⟩ := exists_block_lineSpace hK hp hN hVN
    exact false_of_three_blocks hQ hT hp hp2 hrank hureg hRreg bA bR bN
      (fun s hs t ht => mem_perp.mp ht.2 s hs)
      (fun s hs t ht => orthSep_lineSpace hK hL hN hLN s (hA'L hs) t ht)
      (fun s hs t ht => orthSep_lineSpace hK hL hN hLN s hs.1 t ht)
  refine le_antisymm (fun s hs => ?_) hA'L
  obtain ⟨a', ha', r', hr', rfl⟩ := exists_add_inf_perp hureg hA'L hs
  rw [hRbot, Submodule.mem_bot] at hr'
  rw [hr', add_zero]
  exact ha'

end Lines

end CFSG.LieType.SeitzGeneration.OrthBlk
