module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141e
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Generic

variable {G : Type*} [Group G]

theorem mem_of_pow_mem_of_coprime_charQ {H : Subgroup G} {y : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : y ^ a ∈ H) (hb : y ^ b ∈ H) : y ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hy : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast y a, ← zpow_natCast y b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [hy]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem mem_of_charPow_of_coprime_pow_mem {H : Subgroup G} {g : G} {ℓ e N : ℕ} (hg : g ^ ℓ ^ e = 1)
    (hN : Nat.Coprime N ℓ) (hgN : g ^ N ∈ H) : g ∈ H := by
  have h1 : g ^ ℓ ^ e ∈ H := by rw [hg]; exact one_mem _
  exact mem_of_pow_mem_of_coprime_charQ (Nat.Coprime.pow_left e hN.symm) h1 hgN

theorem eq_one_of_charPow_of_coprime {g : G} {ℓ e N : ℕ} (hg : g ^ ℓ ^ e = 1) (hN : Nat.Coprime N ℓ)
    (hgN : g ^ N = 1) : g = 1 := by
  have h := mem_of_charPow_of_coprime_pow_mem (H := ⊥) hg hN (by rw [hgN]; exact one_mem _)
  simpa using h

theorem mul_pow_mem_of_mem_normalizer_charQ {N : Subgroup G} {t n : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hn : n ∈ N) (m : ℕ) :
    (t ^ m)⁻¹ * (t * n) ^ m ∈ N := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (t ^ (m + 1))⁻¹ * (t * n) ^ (m + 1) =
        ((t⁻¹ * ((t ^ m)⁻¹ * (t * n) ^ m) * t) * n) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    refine mul_mem ?_ hn
    have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem ht) _).1 ih
    simpa using h1

theorem mem_of_charElem_of_mul {N : Subgroup G} {t n : G} (ht : t ∈ Subgroup.normalizer (N : Set G))
    {ℓ M : ℕ} (htM : t ^ M = 1) (hM : Nat.Coprime M ℓ) (hn : n ∈ N) {e : ℕ} (he : (t * n) ^ ℓ ^ e = 1) :
    t * n ∈ N := by
  have h1 : (t * n) ^ M ∈ N := by
    have := mul_pow_mem_of_mem_normalizer_charQ ht hn M
    rwa [htM, inv_one, one_mul] at this
  exact mem_of_charPow_of_coprime_pow_mem he hM h1

theorem commutator_subgroupOf_eq_of_perfect {H K : Subgroup G} (hHK : H ≤ K) (hH : ⁅H, H⁆ = H) :
    ⁅H.subgroupOf K, H.subgroupOf K⁆ = H.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  have hmap : (H.subgroupOf K).map K.subtype = H := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHK]
  rw [Subgroup.map_commutator, hmap, hH]

theorem commutator_iSup_eq_charQ {ι : Type*} (F : ι → Subgroup G) (hF : ∀ i, ⁅F i, F i⁆ = F i) :
    ⁅⨆ i, F i, ⨆ i, F i⁆ = ⨆ i, F i :=
  le_antisymm (Subgroup.commutator_le_self _) (iSup_le fun i =>
    (hF i).symm.le.trans (Subgroup.commutator_mono (le_iSup F i) (le_iSup F i)))

end Generic

section Cyc

open CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s] (P : CycFamily F s)

theorem exists_coprime_pow_mem_normImage {ℓ : ℕ}
    (hZ : ∀ z ∈ P.A, z ∈ P.Z → ∃ N : ℕ, Nat.Coprime N ℓ ∧ z ^ N = 1)
    {H : Subgroup G} (hH : ∀ y ∈ P.S 0, iterHom F s y = y → (∃ n : ℕ, y ^ ℓ ^ n = 1) → y ∈ H)
    {g : G} (hgA : g ∈ P.A) (hgF : F g = g) {e : ℕ} (hge : g ^ ℓ ^ e = 1) :
    ∃ M : ℕ, Nat.Coprime M ℓ ∧ g ^ M ∈ P.normImage H := by
  obtain ⟨y, hyY, ζ, hζZ, hζA, rfl⟩ := P.exists_eq_zeta_norm hgA hgF
  obtain ⟨m, hm, hζm⟩ := hZ ζ hζA hζZ
  have hcomm : Commute ζ (P.norm y) := ((P.mem_Z.1 hζZ) _ (P.norm_mem_A y)).symm
  have hgm : (ζ * P.norm y) ^ m = P.norm (y ^ m) := by
    rw [hcomm.mul_pow, hζm, one_mul, map_pow]
  have hy₁Y : ((y ^ m : P.S 0) : G) ∈ P.Y := by
    rw [SubgroupClass.coe_pow]
    exact P.Y.pow_mem hyY m
  have hNe : P.norm ((y ^ m) ^ ℓ ^ e) = 1 := by
    rw [map_pow, ← hgm, ← pow_mul, mul_comm, pow_mul, hge, one_pow]
  have hy₁Z : (((y ^ m) ^ ℓ ^ e : P.S 0) : G) ∈ P.Z := P.mem_Z_of_norm_eq_one hNe
  obtain ⟨m', hm', hm'e⟩ := hZ _ (P.S_le_A 0 ((y ^ m) ^ ℓ ^ e).2) hy₁Z
  set y₂ : P.S 0 := (y ^ m) ^ m' with hy₂def
  have hy₂Y : (y₂ : G) ∈ P.Y := by
    rw [hy₂def, SubgroupClass.coe_pow]
    exact P.Y.pow_mem hy₁Y m'
  have hy₂e : (y₂ : G) ^ ℓ ^ e = 1 := by
    have h1 : (((y ^ m) ^ ℓ ^ e : P.S 0) : G) ^ m' = 1 := hm'e
    rw [hy₂def, SubgroupClass.coe_pow, ← pow_mul, mul_comm, pow_mul]
    rw [SubgroupClass.coe_pow] at h1
    exact h1
  have hc : iterHom F s (y₂ : G) * (y₂ : G)⁻¹ ∈ P.Z := hy₂Y.2
  have hcA : iterHom F s (y₂ : G) * (y₂ : G)⁻¹ ∈ P.A :=
    mul_mem (P.S_le_A 0 (P.iterHom_s_mem y₂.2)) (inv_mem (P.S_le_A 0 y₂.2))
  obtain ⟨m'', hm'', hcm''⟩ := hZ _ hcA hc
  have hcomm2 : Commute (iterHom F s (y₂ : G) * (y₂ : G)⁻¹) (y₂ : G) :=
    ((P.mem_Z.1 hc) _ (P.S_le_A 0 y₂.2)).symm
  have hce : (iterHom F s (y₂ : G) * (y₂ : G)⁻¹) ^ ℓ ^ e = 1 := by
    have e1 : iterHom F s (y₂ : G) = (iterHom F s (y₂ : G) * (y₂ : G)⁻¹) * (y₂ : G) := by group
    have h2 : (iterHom F s (y₂ : G)) ^ ℓ ^ e = 1 := by rw [← map_pow, hy₂e, map_one]
    rw [e1, hcomm2.mul_pow, hy₂e, mul_one] at h2
    exact h2
  have hc1 := eq_one_of_charPow_of_coprime hce hm'' hcm''
  have hfix : iterHom F s (y₂ : G) = y₂ := mul_inv_eq_one.1 hc1
  have hy₂H : (y₂ : G) ∈ H := hH _ y₂.2 hfix ⟨e, hy₂e⟩
  refine ⟨m * m', Nat.Coprime.mul_left hm hm', ?_⟩
  rw [CycFamily.mem_normImage]
  refine ⟨y₂, hy₂H, ?_⟩
  rw [hy₂def, map_pow, ← hgm, ← pow_mul]

theorem commutator_normImage_eq {H : Subgroup G} (hH0 : H ≤ P.S 0) (hH : ⁅H, H⁆ = H) :
    ⁅P.normImage H, P.normImage H⁆ = P.normImage H := by
  unfold CycFamily.normImage
  rw [← Subgroup.map_commutator, commutator_subgroupOf_eq_of_perfect hH0 hH]

end Cyc

theorem exists_coprime_pow_eq_one_algClosure {K : Type} [Field K] [Finite K] {ℓ : ℕ} (hℓp : ℓ.Prime)
    (hK : ringChar K = ℓ) {ι : Type} [Finite ι] (b : ι → (AlgebraicClosure K)ˣ) :
    ∃ N : ℕ, Nat.Coprime N ℓ ∧ ∀ i, b i ^ N = 1 := by
  classical
  haveI : CharP K ℓ := hK ▸ ringChar.charP K
  set F : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K (Set.range fun i => ((b i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))
  haveI : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Finite F := Module.finite_of_finite K
  haveI : CharP F ℓ := charP_of_injective_algebraMap (algebraMap K F).injective ℓ
  refine ⟨Nat.card F - 1, ?_, fun i => Units.ext ?_⟩
  · rw [← Nat.card_units]
    exact Inputs256e.coprime_card_units hℓp (ringChar.eq F ℓ)
  have hmem : ((b i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ∈ F :=
    IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  set y : F := ⟨_, hmem⟩
  have hy0 : y ≠ 0 := fun h => (b i).ne_zero (congrArg Subtype.val h)
  haveI : Fintype F := Fintype.ofFinite F
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy0
  rw [← Nat.card_eq_fintype_card] at h1
  have h2 := congrArg Subtype.val h1
  simpa using h2

section Lang

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped Pointwise

set_option linter.unusedSectionVars false

@[expose] def CompCharElem {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) (ℓ : ℕ) (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) : Prop :=
  ∃ H : Subgroup (ModGL τ L), H ≤ rootSpan τ L (componentRoots (rootCharHom a) i) ∧
    (∀ y ∈ H, iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) y = y) ∧
    ⁅H, H⁆ = H ∧
    ∀ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) y = y →
      (∃ n : ℕ, y ^ ℓ ^ n = 1) → y ∈ H

@[expose] def OrbitCharElemPerfect {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) (ℓ : ℕ) (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) : Prop :=
  ∃ P : Subgroup (ModGL τ L),
    P ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.D.model ∧ ⁅P, P⁆ = P ∧
    ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P

@[expose] def LangOuterCharElem : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K], 5 ≤ ringChar K →
    ∀ (p₀ : ℕ) (S : LangSetup τ (AlgebraicClosure K) p₀) (p : ℕ), p.Prime →
    ∀ (a : Fin τ.rank → (AlgebraicClosure K)ˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
      rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        (twistKind S.ρ (rootCharHom a) i = .twoD ∨ twistKind S.ρ (rootCharHom a) i = .exc) →
          OrbitCharElemPerfect S (ringChar K) a i


variable {τ : Tag} {K : Type} [Field K] [Finite K] {ℓ : ℕ}

theorem mem_rootSpan_of_charElem (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hap : ∀ i, a i ^ p = 1) {k : ModGL τ (AlgebraicClosure K)}
    (hk : k ∈ toralCentralizer τ (AlgebraicClosure K) a) {m : ℕ} (hkm : k ^ ℓ ^ m = 1) :
    k ∈ rootSpan τ (AlgebraicClosure K) (rootCharKernel a) := by
  classical
  obtain ⟨-, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ (AlgebraicClosure K) a
  have h3 : IsPGroup p (↥(toralCentralizer τ (AlgebraicClosure K) a) ⧸
      (toralRootGroup τ (AlgebraicClosure K) a).subgroupOf (toralCentralizer τ (AlgebraicClosure K) a)) :=
    (isPGroup_quotient hp hap).of_surjective φ hφ
  have hkM : k ∈ toralRootGroup τ (AlgebraicClosure K) a := by
    set x : ↥(toralCentralizer τ (AlgebraicClosure K) a) := ⟨k, hk⟩ with hxdef
    obtain ⟨n, hn⟩ := h3 (QuotientGroup.mk x)
    have hx2 : x ^ (ℓ ^ m) = 1 := Subtype.ext (by simpa using hkm)
    have hA : (QuotientGroup.mk x : ↥(toralCentralizer τ (AlgebraicClosure K) a) ⧸
        (toralRootGroup τ (AlgebraicClosure K) a).subgroupOf (toralCentralizer τ (AlgebraicClosure K) a)) ^
          (ℓ ^ m) = 1 := by
      rw [← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (ℓ ^ m) (p ^ n) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hℓp hp).2 (Ne.symm hpℓ))
    have h1 := (pow_gcd_eq_one (a := (QuotientGroup.mk x : ↥(toralCentralizer τ (AlgebraicClosure K) a) ⧸
        (toralRootGroup τ (AlgebraicClosure K) a).subgroupOf (toralCentralizer τ (AlgebraicClosure K) a)))).2
      ⟨hA, hn⟩
    rw [hcop.gcd_eq_one, pow_one, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hTU : torusGroup τ (AlgebraicClosure K) ≤ Subgroup.normalizer
      (rootSpan τ (AlgebraicClosure K) (rootCharKernel a) : Set (ModGL τ (AlgebraicClosure K))) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hmul : k ∈ (torusGroup τ (AlgebraicClosure K) : Set (ModGL τ (AlgebraicClosure K))) *
      (rootSpan τ (AlgebraicClosure K) (rootCharKernel a) : Set (ModGL τ (AlgebraicClosure K))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTU]
    exact hkM
  obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.1 hmul
  have htN := hTU ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨N, hN, hbN⟩ := exists_coprime_pow_eq_one_algClosure hℓp hK b
  exact mem_of_charElem_of_mul htN (rootDiagUnit_pow_eq_one_of_forall hbN) hN hu hkm

variable {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

theorem unionRootSpan_singleton_charQ {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (i : KernelComponent (rootCharHom a)) :
    unionRootSpan (AlgebraicClosure K) (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))) =
      rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
  unfold unionRootSpan
  rw [unionRoots_singleton]

theorem exists_coprime_pow_of_mem_center_orbitQ (hK : ringChar K = ℓ) (hℓp : ℓ.Prime)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {z : ModGL τ (AlgebraicClosure K)}
    (hzA : z ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i))
    (hzC : z ∈ Subgroup.centralizer
      (rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :
        Set (ModGL τ (AlgebraicClosure K)))) :
    ∃ N : ℕ, Nat.Coprime N ℓ ∧ z ^ N = 1 := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hPA : P.A = rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :=
    outerOrbitFamily_A S hT i hs hmin
  have hzP : z ∈ P.A := hPA ▸ hzA
  have hzZ : z ∈ P.Z := by
    show z ∈ Subgroup.centralizer (P.A : Set (ModGL τ (AlgebraicClosure K)))
    rw [hPA]
    exact hzC
  obtain ⟨f, rfl⟩ := P.mem_A_iff.1 hzP
  have hfZ : ∀ k, ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) ∈ P.Z :=
    fun k => CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e.mem_Z_of_mu_mem_Z P f hzZ k
  have hsL := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e.exists_unit_sq_ne_one_of_isAlgClosed
    (L := AlgebraicClosure K)
  have htor : ∀ k, ∃ b : Fin τ.rank → (AlgebraicClosure K)ˣ,
      ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ b := by
    intro k
    obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
    have hSk : P.S k = rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) := by
      rw [hP, outerOrbitFamily_S, hj]
    have hUS := unionRootSpan_singleton_charQ (K := K) j
    have hmem : ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) ∈
        unionRootSpan (AlgebraicClosure K) (rootCharHom a) ({j} : Set (KernelComponent (rootCharHom a))) := by
      rw [hUS, ← hSk]
      exact (f k).2
    have hcomm : ∀ x ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
        ({j} : Set (KernelComponent (rootCharHom a))),
        x * ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) = ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) * x := by
      intro x hx
      rw [hUS, ← hSk] at hx
      exact (P.mem_Z.1 (hfZ k)) x (P.S_le_A k hx)
    have htT := central_mem_unionTorus hsL hmem hcomm
    exact exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup htT)
  choose b hb using htor
  obtain ⟨N, hN, hbN⟩ :=
    exists_coprime_pow_eq_one_algClosure hℓp hK (fun ki : ZMod s × Fin τ.rank => b ki.1 ki.2)
  refine ⟨N, hN, ?_⟩
  have hfN : f ^ N = 1 := by
    funext k
    apply Subtype.ext
    simp only [Pi.pow_apply, SubgroupClass.coe_pow, Pi.one_apply, OneMemClass.coe_one]
    rw [hb k]
    exact rootDiagUnit_pow_eq_one_of_forall fun i => hbN (k, i)
  rw [← map_pow, hfN, map_one]

theorem exists_perfect_orbit_of_comp (hK : ringChar K = ℓ) (hℓp : ℓ.Prime)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hcomp : CompCharElem S ℓ a i) :
    ∃ P : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P, P⁆ = P ∧
      P ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      ∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
        (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hPA : P.A = rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :=
    outerOrbitFamily_A S hT i hs hmin
  have hP0 : P.S 0 = rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  obtain ⟨H, hH0, hHfix, hHperf, hHy⟩ := hcomp
  have hH0' : H ≤ P.S 0 := hP0 ▸ hH0
  have hZ : ∀ z ∈ P.A, z ∈ P.Z → ∃ N : ℕ, Nat.Coprime N ℓ ∧ z ^ N = 1 := by
    intro z hzA hzZ
    have hzZ' : z ∈ Subgroup.centralizer (P.A : Set (ModGL τ (AlgebraicClosure K))) := hzZ
    rw [hPA] at hzA hzZ'
    exact exists_coprime_pow_of_mem_center_orbitQ S hK hℓp hT i hzA hzZ'
  have hNperf := commutator_normImage_eq P hH0' hHperf
  have hNle : P.normImage H ≤ P.Afix := P.normImage_le_Afix fun y hy _ => hHfix y hy
  have hAadj : P.A ≤ adjointGroup τ (AlgebraicClosure K) := by
    rw [hPA]
    exact rootSpan_le_adjointGroup _ _
  have hNmodel : P.normImage H ≤ S.D.model := fun x hx => ⟨hAadj (hNle hx).1, (hNle hx).2⟩
  have hNΓ : P.normImage H ≤ ⁅S.D.model, S.D.model⁆ :=
    hNperf.symm.le.trans (Subgroup.commutator_mono hNmodel hNmodel)
  have hNspan : P.normImage H ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := fun x hx =>
    Subgroup.mem_inf.2 ⟨hPA ▸ (hNle hx).1, hNΓ hx⟩
  refine ⟨P.normImage H, hNperf, hNperf.symm.le.trans (Subgroup.commutator_mono hNspan hNspan), ?_⟩
  intro g hgA hgM ⟨e, he⟩
  obtain ⟨M, hM, hgM'⟩ := exists_coprime_pow_mem_normImage P hZ
    (fun y hy hyF hyn => hHy y (hP0 ▸ hy) hyF hyn) (hPA ▸ hgA) hgM.2 he
  exact mem_of_charPow_of_coprime_pow_mem he hM hgM'

omit [Field K] [Finite K] S
    in
theorem le_rationalComponent_of_perfect {L : Type} [Field L] [IsAlgClosed L]
    {p₁ : ℕ} (SL : LangSetup τ L p₁) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {P : Subgroup (ModGL τ L)}
    (hPA : P ≤ rootSpan τ L (rationalRoots SL.ρ (rootCharHom a) i) ⊓ SL.D.model)
    (hperf : ⁅P, P⁆ = P) : P ≤ rationalComponent SL.ρ SL.Γ (rootCharHom a) i := by
  have hPΓ : P ≤ ⁅SL.D.model, SL.D.model⁆ :=
    hperf.symm.le.trans (Subgroup.commutator_mono (hPA.trans inf_le_right) (hPA.trans inf_le_right))
  have hPspan : P ≤ rationalSpan SL.ρ SL.Γ (rootCharHom a) i := fun x hx =>
    Subgroup.mem_inf.2 ⟨(hPA hx).1, hPΓ hx⟩
  exact hperf.symm.le.trans (Subgroup.commutator_mono hPspan hPspan)

theorem compCharElem_inner (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (h4 : 4 ≤ S.D.q)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .inner) :
    CompCharElem S ℓ a i := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hqe⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hqe, ← pow_mul]
  have hes : 0 < e * s := Nat.mul_pos he hs0
  have hQ : 4 ≤ r ^ (e * s) := by
    calc 4 ≤ S.D.q := h4
      _ = r ^ e := hqe
      _ ≤ r ^ (e * s) := Nat.pow_le_pow_right hr.pos (Nat.le_mul_of_pos_right e hs0)
  obtain ⟨t₀, ht₀⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_unit_sq_ne_one
    (L := AlgebraicClosure K) σ hσ' hes hQ
  have hperfC := CFSG.HardMathSupport.Timmesfeld.CrossChar.isPerfect_componentRootSpan_of_sq_ne_one
    (K := fixSubfield σ) (χ := rootCharHom a) ht₀ i
  have hperfCQ : ⁅CQ σ i, CQ σ i⁆ = CQ σ i := by
    rw [CQ_eq_map, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperfC]
  refine ⟨(CQ σ i).map (MulAut.conj z).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hnorm i x).1 (CQ_le_rootSpan σ i hx)
  · rintro _ ⟨x, hx, rfl⟩
    show iterHom S.D.step s (z * x * z⁻¹) = z * x * z⁻¹
    rw [hz x (CQ_le_rootSpan σ i hx), frobGL_eq_self_of_mem_CQ σ i hx]
  · rw [← Subgroup.map_commutator, hperfCQ]
  · intro y hy hyF ⟨n, hn⟩
    set v := z⁻¹ * y * z with hv
    have hzv : z * v * z⁻¹ = y := by rw [hv]; group
    have hvS : v ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
      (hnorm i v).2 (by rw [hzv]; exact hy)
    have hvF : frobGL σ v = v := by
      have h1 := hz v hvS
      rw [hzv, hyF] at h1
      have h2 : frobGL σ v = z⁻¹ * y * z := by rw [h1]; group
      rw [h2]
    have hvn : v ^ ℓ ^ n = 1 := by
      have h1 : v ^ ℓ ^ n = (MulAut.conj z⁻¹) (y ^ ℓ ^ n) := by
        rw [map_pow]
        congr 1
      rw [h1, hn, map_one]
    have hvU : v ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
        ({i} : Set (KernelComponent (rootCharHom a))) := by
      rw [unionRootSpan_singleton_charQ]
      exact hvS
    obtain ⟨t, ht, x, hx, hvtx, htF⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_decomp (σ := σ) hvU
      (one_mem _) (by rw [one_mul]; exact hvF)
    have hcen1 : ∀ w ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
        ({i} : Set (KernelComponent (rootCharHom a))), w * 1 = 1 * w := fun _ _ => by
      rw [mul_one, one_mul]
    have hn' := torus_normalizes_CQ (σ := σ) ht hcen1 htF
    have htN' : t ∈ Subgroup.normalizer (CQ σ i : Set (ModGL τ (AlgebraicClosure K))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨fun hw => hn'.1 w hw, fun hw => ?_⟩
      have h1 := hn'.2 _ hw
      have e1 : t⁻¹ * (t * w * t⁻¹) * t = w := by group
      rwa [e1] at h1
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
    obtain ⟨Nt, hNt, hlN⟩ := exists_coprime_pow_eq_one_algClosure hℓp hK l
    have htN : t ^ Nt = 1 := by
      rw [hl]
      exact rootDiagUnit_pow_eq_one_of_forall hlN
    have hvC : v ∈ CQ σ i := by
      rw [hvtx]
      exact mem_of_charElem_of_mul htN' htN hNt hx (by rw [← hvtx]; exact hvn)
    exact ⟨v, hvC, hzv⟩

section SuN

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups commutatorElement

theorem eq_one_of_mem_center_SL_charPow {L : Type} [Field L] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP L ℓ] {ν : ℕ}
    (hν : 0 < ν) {c : SL(ν, L)} (hc : c ∈ Subgroup.center SL(ν, L)) {n : ℕ} (hcn : c ^ ℓ ^ n = 1) : c = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have h1 : Matrix.scalar (Fin ν) (r ^ ℓ ^ n) = (1 : Matrix (Fin ν) (Fin ν) L) := by
    have h := congrArg (fun X : SL(ν, L) => (X : Matrix (Fin ν) (Fin ν) L)) hcn
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
    rw [← hr, ← map_pow] at h
    exact h
  have h2 : r ^ ℓ ^ n = 1 := by
    have h := congrFun (congrFun h1 ⟨0, hν⟩) ⟨0, hν⟩
    simpa using h
  have h3 : r = 1 := by
    have h4 : (r - 1) ^ ℓ ^ n = 0 := by rw [sub_pow_char_pow, one_pow, h2, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hℓ.out.ne_zero)).1 h4)
  apply Subtype.ext
  rw [← hr, h3, map_one]
  rfl

theorem exists_coprime_pow_of_mem_center_SL {K : Type} [Field K] [Finite K] {ℓ : ℕ} (hℓp : ℓ.Prime)
    (hK : ringChar K = ℓ) {ν : ℕ} (hν : 0 < ν) {c : SL(ν, AlgebraicClosure K)}
    (hc : c ∈ Subgroup.center SL(ν, AlgebraicClosure K)) : ∃ N : ℕ, Nat.Coprime N ℓ ∧ c ^ N = 1 := by
  obtain ⟨r, hrν, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by simp; omega)] at hrν
    exact zero_ne_one hrν
  obtain ⟨N, hN, hrN⟩ := exists_coprime_pow_eq_one_algClosure hℓp hK (fun _ : Unit => Units.mk0 r hr0)
  refine ⟨N, hN, ?_⟩
  have hrN' : r ^ N = 1 := by
    have := congrArg Units.val (hrN ())
    simpa using this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, ← map_pow, hrN', map_one]
  rfl

theorem compCharElem_of_unitary_frame (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (h5 : 5 ≤ ℓ)
    {ta : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K)} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a)) :
    CompCharElem S ℓ ta i := by
  classical
  set L := AlgebraicClosure K with hLdef
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hrℓ : r = ℓ := by
    have hLℓ : ringChar L = ℓ := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hK]
    rw [← hLℓ]
    exact (ringChar.eq L r).symm
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ a b) c) = pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
    ring
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(ν, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      have e1 : (d b : L) * (-((d a : L) * (d b : L)⁻¹) * σQ t) * (d a : L)⁻¹ =
          -(σQ t) * ((d b : L) * (d b : L)⁻¹) * ((d a : L) * (d a : L)⁻¹) := by ring
      rw [e1, mul_inv_cancel₀ h0', mul_inv_cancel₀ h0, mul_one, mul_one]
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hz, hnorm⟩ := exists_lang_mul_T S hT hs0 hy₁
  have hconj : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
    intro X
    rw [← hstd X, map_mul, map_mul, map_inv, hz]
    group
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε _ _ h01, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hkerc : ∀ X : SL(ν, L), ψ X = 1 → X ∈ Subgroup.center SL(ν, L) := fun X hX =>
    mem_center_SL_of_commute hν ψ hker fun Y => by rw [hX, one_mul, mul_one]
  set C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  obtain ⟨-, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr (Nat.mul_pos he hs0) σQ hσc hν
  have hne : (ν, r ^ (e * s)) ≠ (3, 2) := by
    intro h
    have h2 : r ^ (e * s) = 2 := congrArg Prod.snd h
    have h3 : r ≤ r ^ (e * s) := Nat.le_self_pow (Nat.mul_pos he hs0).ne' r
    omega
  have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 (hqsC hne).1
  set θ : SL(ν, L) →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp ψ with hθdef
  have hθ : ∀ X, θ X = z * ψ X * z⁻¹ := fun X => rfl
  refine ⟨C.map θ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, -, rfl⟩
    rw [hθ]
    exact (hnorm i _).1 (hψS X)
  · rintro _ ⟨X, hX, rfl⟩
    show Fs (θ X) = θ X
    rw [hθ, hconj, (hCmem X).1 hX]
  · rw [← Subgroup.map_commutator, hCperf]
  · intro y hy hyF ⟨n, hn⟩
    have hy' : z⁻¹ * y * z ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [e]
      exact hy)
    rw [hΨ, ← hψ.range] at hy'
    obtain ⟨X, hX⟩ := hy'
    have hyX : y = θ X := by rw [hθ, hX]; group
    have hrℓ' : ℓ = r := hrℓ.symm
    have hcX : X ^ ℓ ^ n ∈ Subgroup.center SL(ν, L) := by
      refine hkerc _ ?_
      have h1 : θ (X ^ ℓ ^ n) = 1 := by rw [map_pow, ← hyX, hn]
      rw [hθ] at h1
      have h2 : ψ (X ^ ℓ ^ n) = z⁻¹ * (z * ψ (X ^ ℓ ^ n) * z⁻¹) * z := by group
      rw [h2, h1]
      group
    obtain ⟨N, hN, hcN⟩ := exists_coprime_pow_of_mem_center_SL hℓp hK (by omega) hcX
    have hcopy : Nat.Coprime N (orderOf y) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hn) (Nat.Coprime.pow_right n hN)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopy
    set X₁ := (X ^ N) ^ m with hX₁
    have hyX₁ : y = θ X₁ := by
      rw [hX₁, map_pow, map_pow, ← hyX, hm]
    have hX₁n : X₁ ^ ℓ ^ n = 1 := by
      rw [hX₁, ← pow_mul, ← pow_mul, show N * (m * ℓ ^ n) = ℓ ^ n * N * m by ring, pow_mul, pow_mul, hcN,
        one_pow]
    set c₁ := stdUnitary σQ.toRingHom X₁ * X₁⁻¹ with hc₁
    have hc₁c : c₁ ∈ Subgroup.center SL(ν, L) := by
      refine hkerc _ ?_
      have h1 : Fs (θ X₁) = θ X₁ := by rw [← hyX₁]; exact hyF
      rw [hθ, hconj] at h1
      have h2 : ψ (stdUnitary σQ.toRingHom X₁) = ψ X₁ := by
        have := congrArg (fun g => z⁻¹ * g * z) h1
        simpa [mul_assoc] using this
      rw [hc₁, map_mul, map_inv, h2, mul_inv_cancel]
    have hc₁n : c₁ ^ ℓ ^ n = 1 := by
      have hcomm : Commute c₁ X₁ := (Subgroup.mem_center_iff.1 hc₁c X₁).symm
      have e1 : stdUnitary σQ.toRingHom X₁ = c₁ * X₁ := by rw [hc₁, inv_mul_cancel_right]
      have h1 : (stdUnitary σQ.toRingHom X₁) ^ ℓ ^ n = 1 := by rw [← map_pow, hX₁n, map_one]
      rw [e1, hcomm.mul_pow, hX₁n, mul_one] at h1
      exact h1
    haveI : Fact ℓ.Prime := ⟨hℓp⟩
    haveI : CharP L ℓ := hrℓ ▸ hchar
    have hc₁1 : c₁ = 1 := eq_one_of_mem_center_SL_charPow (by omega) hc₁c hc₁n
    have hX₁C : X₁ ∈ C := by
      rw [hCmem]
      exact mul_inv_eq_one.1 hc₁1
    exact ⟨X₁, hX₁C, hyX₁.symm⟩

theorem compCharElem_suN (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (h5 : 5 ≤ ℓ) {p : ℕ} (hp : p.Prime)
    {ta : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus) (hap : ∀ i, ta i ^ p = 1)
    (h1 : rootDiagUnit τ ta ≠ 1) (i : KernelComponent (rootCharHom ta))
    (hkind : twistKind S.ρ (rootCharHom ta) i = .suN) :
    CompCharElem S ℓ ta i := by
  classical
  have hℓL : ringChar (AlgebraicClosure K) ≠ p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓL
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨h2, hn⟩ := suN_rank_ncard hkind
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hout : ¬ twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKind at hkind
    rw [ite_eq_left_iff.2 (fun h' => absurd h h')] at hkind
    exact absurd hkind (by decide)
  have hmaps : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈ frameRoots σ := by
    intro a b hab
    have h1 : σ a b ∈ componentRoots (rootCharHom ta) i := by
      rw [hΨ]
      exact ⟨a, b, hab, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom ta) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨a, b, hab, rfl⟩ := hγ
      rw [hπ a b hab, hwσ]
  · exact compCharElem_of_unitary_frame S hK hℓp h5 hT i hν hψ hΨ π hπ

end SuN

theorem mem_iSup_of_charElem_family (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (Nf : Set.range (rationalRoots S.ρ (rootCharHom a)) → Subgroup (ModGL τ (AlgebraicClosure K)))
    (hNf : ∀ O, ∀ g ∈ rootSpan τ (AlgebraicClosure K) O.1, g ∈ S.D.model → (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ Nf O)
    {k : ModGL τ (AlgebraicClosure K)} (hk : k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    {m : ℕ} (hkm : k ^ ℓ ^ m = 1) :
    k ∈ ⨆ O, Nf O := by
  classical
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  have hΓ : S.Γ ≤ adjointGroup τ (AlgebraicClosure K) :=
    (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  have hΓfix : ∀ x ∈ S.Γ, S.D.step x = x := fun x hx =>
    ((Subgroup.commutator_le_self S.D.model) hx).2
  have hkX : k ∈ toralCentralizer τ (AlgebraicClosure K) a :=
    Subgroup.mem_inf.2 ⟨hΓ (Subgroup.mem_inf.1 hk).1, (Subgroup.mem_inf.1 hk).2⟩
  have hkU := mem_rootSpan_of_charElem hK hℓp hp hpℓ hap hkX hkm
  have hkF : S.D.step k = k := hΓfix k (Subgroup.mem_inf.1 hk).1
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K) (rootCharHom a)).2.1
  haveI : Finite (Set.range (rationalRoots S.ρ (rootCharHom a))) := (Set.finite_range _).to_subtype
  haveI : Fintype (Set.range (rationalRoots S.ρ (rootCharHom a))) := Fintype.ofFinite _
  let A : Set.range (rationalRoots S.ρ (rootCharHom a)) → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun O => rootSpan τ (AlgebraicClosure K) O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact commute_rootSpan_rationalRoots hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, S.D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact step_mem_rootSpan S (fun γ hγ => (rationalRoots_subset_kernelRoots hker i hγ).1)
      (rationalRoots_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan τ (AlgebraicClosure K) (rootCharKernel a) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (rationalRoots_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan (AlgebraicClosure K) (χ := rootCharHom a)).ge
        (iSup_le fun i => ?_)
      have h : componentRootSpan (AlgebraicClosure K) (rootCharHom a) i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup τ (AlgebraicClosure K) := fun O => rootSpan_le_adjointGroup _ O.1
  have hcomm : Pairwise fun O O' : Set.range (rationalRoots S.ρ (rootCharHom a)) =>
      ∀ x y : ModGL τ (AlgebraicClosure K), x ∈ A O → y ∈ A O' → Commute x y :=
    fun O O' hne x y hx hy => hc O O' hne x hx y hy
  set ν := Subgroup.noncommPiCoprod hcomm with hν
  have hrange : ν.range = ⨆ O, A O := Subgroup.noncommPiCoprod_range
  obtain ⟨f, hf⟩ : k ∈ ν.range := by rw [hrange, hU]; exact hkU
  have hcen : ∀ O, ∀ z ∈ A O, z ∈ Subgroup.centralizer (A O : Set (ModGL τ (AlgebraicClosure K))) →
      ∃ N : ℕ, Nat.Coprime N ℓ ∧ z ^ N = 1 := by
    rintro ⟨_, i, rfl⟩ z hz hzC
    exact exists_coprime_pow_of_mem_center_orbitQ S hK hℓp hT i hz hzC
  have hfm : ∀ O, ((f O : A O) : ModGL τ (AlgebraicClosure K)) ^ (ℓ ^ m) ∈
      Subgroup.centralizer (A O : Set (ModGL τ (AlgebraicClosure K))) := by
    intro O
    have h1 : ν (f ^ (ℓ ^ m)) = 1 := by rw [map_pow, hf, hkm]
    have h2 := mem_centralizer_of_noncommPiCoprod_eq_one A hcomm (f ^ (ℓ ^ m)) h1 O
    simpa using h2
  have hodd : ∀ O, ∃ N : ℕ, Nat.Coprime N ℓ ∧
      (((f O : A O) : ModGL τ (AlgebraicClosure K)) ^ (ℓ ^ m)) ^ N = 1 :=
    fun O => hcen O _ (pow_mem (f O).2 _) (hfm O)
  choose N hN hfN using hodd
  set N₀ : ℕ := ∏ O, N O with hN₀def
  have hN₀ : Nat.Coprime N₀ ℓ := Nat.Coprime.prod_left fun O _ => hN O
  have hfN₀ : ∀ O, (((f O : A O) : ModGL τ (AlgebraicClosure K)) ^ (ℓ ^ m)) ^ N₀ = 1 := by
    intro O
    obtain ⟨c, hc'⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ O)
    rw [← hN₀def] at hc'
    rw [hc', pow_mul, hfN O, one_pow]
  have hgcd : Nat.gcd N₀ (ℓ ^ m) = 1 := Nat.Coprime.pow_right m hN₀
  set x : ℤ := Nat.gcdA N₀ (ℓ ^ m) with hx
  set y : ℤ := Nat.gcdB N₀ (ℓ ^ m) with hy
  have hxy : (N₀ : ℤ) * x + ((ℓ ^ m : ℕ) : ℤ) * y = 1 := by
    have h := Nat.gcd_eq_gcd_ab N₀ (ℓ ^ m)
    rw [hgcd, Nat.cast_one] at h
    exact h.symm
  let f₂ : ∀ O, A O := fun O => (f O) ^ ((N₀ : ℤ) * x)
  let b : ∀ O, A O := fun O => (f O) ^ (((ℓ ^ m : ℕ) : ℤ) * y)
  have hfb : f = f₂ * b := by
    funext O
    show f O = (f O) ^ ((N₀ : ℤ) * x) * (f O) ^ (((ℓ ^ m : ℕ) : ℤ) * y)
    rw [← zpow_add, hxy, zpow_one]
  have hf₂2 : f₂ ^ (ℓ ^ m) = 1 := by
    funext O
    apply Subtype.ext
    show (((f O) ^ ((N₀ : ℤ) * x)) ^ (ℓ ^ m) : A O).1 = 1
    rw [← zpow_natCast, ← zpow_mul, show (N₀ : ℤ) * x * ((ℓ ^ m : ℕ) : ℤ) = ((ℓ ^ m * N₀ : ℕ) : ℤ) * x by
      push_cast; ring, zpow_mul, zpow_natCast, pow_mul]
    have h1 : (((f O : A O)) ^ (ℓ ^ m)) ^ N₀ = 1 := Subtype.ext (by simpa using hfN₀ O)
    rw [h1, one_zpow]
    rfl
  have hbC : ∀ O, ((b O : A O) : ModGL τ (AlgebraicClosure K)) ∈
      Subgroup.centralizer (A O : Set (ModGL τ (AlgebraicClosure K))) := by
    intro O
    show (((f O) ^ (((ℓ ^ m : ℕ) : ℤ) * y) : A O) : ModGL τ (AlgebraicClosure K)) ∈ _
    rw [zpow_mul, zpow_natCast, Subgroup.coe_zpow, Subgroup.coe_pow]
    exact zpow_mem (hfm O) y
  have hbN : b ^ N₀ = 1 := by
    funext O
    apply Subtype.ext
    show (((f O) ^ (((ℓ ^ m : ℕ) : ℤ) * y)) ^ N₀ : A O).1 = 1
    rw [← zpow_natCast, ← zpow_mul, show ((ℓ ^ m : ℕ) : ℤ) * y * (N₀ : ℤ) = ((ℓ ^ m * N₀ : ℕ) : ℤ) * y by
      push_cast; ring, zpow_mul, zpow_natCast, pow_mul]
    have h1 : (((f O : A O)) ^ (ℓ ^ m)) ^ N₀ = 1 := Subtype.ext (by simpa using hfN₀ O)
    rw [h1, one_zpow]
    rfl
  have hbf : b * f₂ = f₂ * b := by
    funext O
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (hbC O) _ (f₂ O).2).symm
  have hk₂ : k = ν f₂ := by
    have e1 : k = ν f₂ * ν b := by rw [← hf, hfb, map_mul]
    have hνc : Commute (ν f₂) (ν b) := by
      show ν f₂ * ν b = ν b * ν f₂
      rw [← map_mul, ← map_mul, hbf]
    have hb2 : (ν b) ^ (ℓ ^ m) = 1 := by
      have h1 : k ^ (ℓ ^ m) = (ν f₂) ^ (ℓ ^ m) * (ν b) ^ (ℓ ^ m) := by rw [e1, hνc.mul_pow]
      rw [hkm, ← map_pow, hf₂2, map_one, one_mul] at h1
      exact h1.symm
    have hbN' : (ν b) ^ N₀ = 1 := by rw [← map_pow, hbN, map_one]
    rw [e1, eq_one_of_charPow_of_coprime hb2 hN₀ hbN', mul_one]
  have hkey : ∀ O, S.D.step ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) *
      ((f₂ O : A O) : ModGL τ (AlgebraicClosure K))⁻¹ ∈
      Subgroup.centralizer (A O : Set (ModGL τ (AlgebraicClosure K))) := by
    intro O
    let Ff : ∀ O, A O := fun O => ⟨S.D.step (f₂ O), hF O _ (f₂ O).2⟩
    have hFν : ν Ff = S.D.step (ν f₂) := by
      rw [hν, Subgroup.noncommPiCoprod_apply, Subgroup.noncommPiCoprod_apply]
      exact (Finset.map_noncommProd Finset.univ (fun O => ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)))
        _ S.D.step).symm
    have h1 : ν (Ff * f₂⁻¹) = 1 := by rw [map_mul, map_inv, hFν, ← hk₂, hkF, mul_inv_cancel]
    exact mem_centralizer_of_noncommPiCoprod_eq_one A hcomm (Ff * f₂⁻¹) h1 O
  have hg2 : ∀ O, ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) ^ (ℓ ^ m) = 1 := by
    intro O
    have h1 := congrArg (fun φ : ∀ O, A O => ((φ O : A O) : ModGL τ (AlgebraicClosure K))) hf₂2
    simpa using h1
  have hfix : ∀ O, S.D.step ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) =
      ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) := by
    intro O
    set g : ModGL τ (AlgebraicClosure K) := ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) with hg
    set w := S.D.step g * g⁻¹ with hw
    have hwA : w ∈ A O := mul_mem (hF O _ (f₂ O).2) (inv_mem (f₂ O).2)
    obtain ⟨N', hN', hwN⟩ := hcen O w hwA (hkey O)
    have hwg : Commute w g := (Subgroup.mem_centralizer_iff.1 (hkey O) g (f₂ O).2).symm
    have hFg : S.D.step g = w * g := by rw [hw]; group
    have hFgc : Commute (S.D.step g) g := by rw [hFg]; exact hwg.mul_left (Commute.refl g)
    have hw2 : w ^ (ℓ ^ m) = 1 := by
      rw [hw, (hFgc.inv_right).mul_pow, ← map_pow, hg2 O, map_one, inv_pow, hg2 O, inv_one, one_mul]
    have hw1 := eq_one_of_charPow_of_coprime hw2 hN' hwN
    rw [hw] at hw1
    exact mul_inv_eq_one.1 hw1
  rw [hk₂, hν, Subgroup.noncommPiCoprod_apply]
  exact Subgroup.noncommProd_mem _ _ fun O _ => Subgroup.mem_iSup_of_mem O
    (hNf O _ (f₂ O).2 ⟨hAadj O (f₂ O).2, hfix O⟩ ⟨m, hg2 O⟩)

theorem exists_perfect_of_charElem (hout : LangOuterCharElem) (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (h5 : 5 ≤ ℓ)
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    {k : ModGL τ (AlgebraicClosure K)} (hk : k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    {m : ℕ} (hkm : k ^ ℓ ^ m = 1) :
    ∃ P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}, ⁅P, P⁆ = P ∧ k ∈ P := by
  classical
  have hq4 : 4 ≤ S.D.q := by
    obtain ⟨r, e, hr, hchar, he, hqe⟩ := exists_char_pow S
    have hLℓ : ringChar (AlgebraicClosure K) = ℓ := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hK]
    have hrℓ : r = ℓ := by
      haveI := hchar
      rw [← hLℓ]
      exact (ringChar.eq (AlgebraicClosure K) r).symm
    rw [hqe, hrℓ]
    calc 4 ≤ ℓ := by omega
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ e := Nat.pow_le_pow_right hℓp.pos he
  have hgood : ∀ O : Set.range (rationalRoots S.ρ (rootCharHom a)),
      ∃ P' : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P', P'⁆ = P' ∧
        P' ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) O.1, g ∈ S.D.model → (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P' := by
    rintro ⟨_, i, rfl⟩
    have horb : ∃ P' : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P', P'⁆ = P' ∧
        P' ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
          (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P' := by
      cases hkind : twistKind S.ρ (rootCharHom a) i with
      | inner => exact exists_perfect_orbit_of_comp S hK hℓp hT i (compCharElem_inner S hK hℓp hq4 hT i hkind)
      | suN => exact exists_perfect_orbit_of_comp S hK hℓp hT i (compCharElem_suN S hK hℓp h5 hp hT hap h1 i hkind)
      | twoD =>
        obtain ⟨P', hP'A, hP'perf, hP'⟩ := hout τ K (by rw [hK]; exact h5) p₀ S p hp a hT hap h1 i (Or.inl hkind)
        rw [hK] at hP'
        exact ⟨P', hP'perf, le_rationalComponent_of_perfect S i hP'A hP'perf, hP'⟩
      | exc =>
        obtain ⟨P', hP'A, hP'perf, hP'⟩ := hout τ K (by rw [hK]; exact h5) p₀ S p hp a hT hap h1 i (Or.inr hkind)
        rw [hK] at hP'
        exact ⟨P', hP'perf, le_rationalComponent_of_perfect S i hP'A hP'perf, hP'⟩
    obtain ⟨P', hP'perf, hP'R, hP'⟩ := horb
    exact ⟨P', hP'perf, hP'R.trans (langSubnormal_of_mem_torus S hT i).1, hP'⟩
  choose Pf hPfperf hPfle hPfmem using hgood
  exact ⟨⨆ O, Pf O, iSup_le hPfle, commutator_iSup_eq_charQ Pf hPfperf,
    mem_iSup_of_charElem_family S hK hℓp hp hpℓ hT hap Pf hPfmem hk hkm⟩

theorem qGen_of_langSetup_charElem (hout : LangOuterCharElem) {p : ℕ} (hp : p.Prime)
    (hres : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcRationalLieTypesP p)
    (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (h5 : 5 ≤ ℓ) (hpℓ : p ≠ ℓ)
    {C : Type} [Group C] (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    Inputs256e.QGen ℓ β := by
  classical
  intro s hs ⟨n, hn⟩
  set d : ModGL τ (AlgebraicClosure K) := rootDiagUnit τ a with hd
  set R : KernelComponent (rootCharHom a) → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β d hβ, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {d}).comap ι = fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hι _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {d} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  have hιs : ι s ∈ S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [← hfix]
    exact ⟨s, mem_fixSubgroup.2 hs, rfl⟩
  have hιn : ι s ^ ℓ ^ n = 1 := by rw [← map_pow, hn, map_one]
  obtain ⟨P, hPle, hPperf, hsP⟩ := exists_perfect_of_charElem S hout hK hℓp h5 hp hpℓ hT hap h1 hιs hιn
  have hPR := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.perfect_le_iSup_rationalComponent_of_prime
    S hp hT hap h1 hTame P hPle hPperf
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K) (rootCharHom a)).2.1
  let Q := {i : KernelComponent (rootCharHom a) // CFSG.IsQuasisimple (R i)}
  have hcompR : ∀ i : Q, IsComponentOf (R i.1) (S.Γ ⊓ Subgroup.centralizer {d}) := by
    intro i
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i.1
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple i.2⟩
  have hRrange : ∀ i : Q, R i.1 ≤ ι.range := fun i => (hcompR i).1.trans hCdrange
  let Fq : Q → Subgroup C := fun i => (R i.1).comap ι
  have hmapF : (⨆ i, Fq i).map ι = ⨆ i : Q, R i.1 := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => Subgroup.map_comap_eq_self (hRrange i)
  have hsF : s ∈ ⨆ i, Fq i := by
    have h' : ι s ∈ (⨆ i, Fq i).map ι := by
      rw [hmapF]
      exact hPR hsP
    obtain ⟨s', hs', hs'eq⟩ := h'
    rwa [hι hs'eq] at hs'
  have hLℓ : ringChar (AlgebraicClosure K) = ℓ := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hK]
  have hFchev : ∀ i : Q, Inputs256e.IsChevSub ℓ β (Fq i) := by
    intro i
    have hc := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isComponentOf_comap_of_injective ι hι
      (hRrange i) hCdrange (hcompR i)
    rw [hcomapfix] at hc
    obtain ⟨-, hsub, hq⟩ := hc
    let e : ↥(Fq i) ≃* ↥(R i.1) := (Subgroup.equivMapOfInjective (Fq i) ι hι).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (hRrange i)))
    have hdata := hres τ (AlgebraicClosure K) p₀ S a hT hap h1 i.1 i.2
    rw [hLℓ] at hdata
    exact ⟨hsub, hq, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hdata.chev⟩
  exact (iSup_le fun i => le_iSup₂_of_le (f := fun (J : Subgroup C) (_ : Inputs256e.IsChevSub ℓ β J) => J)
    (Fq i) (hFchev i) le_rfl) hsF

end Lang

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

end
