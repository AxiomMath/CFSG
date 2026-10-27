module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux.Kernel
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerDecomp
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4PlaneCentralizer

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Malle.LocalAction

section Twisted

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem exists_hom_twisted_explicit (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) {m : ℕ}
    (hm : Odd m) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ) (i j : Fin 4)
    (hW : ∀ k l : Fin 4, (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (m : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin 4),
      (∑ l, U s l * Wm l k) ≡
        U s ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
          (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
            ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) [ZMOD m]) :
    ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U) := by
  refine exists_hom_twisted_aux_explicit hF w hm Wm U i j hW hdet (fun s k => ?_)
  have h := hfix s k
  have e : (ReeTag.F4.perm k : Fin 4) = (![3, 2, 1, 0] : Fin 4 → Fin 4) k := perm_vec k
  have h1 := congrArg (fun j : Fin 4 => U s j *
    (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) j) e
  have h2 : U s ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
      (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) ((![3, 2, 1, 0] : Fin 4 → Fin 4) k)
        = U s (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) := by
    rw [relExp_vec a (ReeTag.F4.perm k)]
    exact h1.symm
  rw [← h2]
  exact h

theorem exists_hom_five_m (hF : IsReeFrob a F)
    (hmM : ((5 : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) :
    ∃ Φ : (rootsOfUnity 5 L) × (rootsOfUnity 5 L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4m) ∧
      ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag
        (expTuple (z.1 : Lˣ) (z.2 : Lˣ) (Um (2 ^ a))) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted_explicit hF wPhi4m (m := 5) (by decide)
    (toMat 4 [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]])
    (Um (2 ^ a)) 0 1 (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num [Um]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, Um] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

theorem exists_hom_five_p (hF : IsReeFrob a F)
    (hmM : ((5 : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) :
    ∃ Φ : (rootsOfUnity 5 L) × (rootsOfUnity 5 L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4p) ∧
      ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag
        (expTuple (z.1 : Lˣ) (z.2 : Lˣ) (Up (2 ^ a))) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted_explicit hF wPhi4p (m := 5) (by decide)
    (toMat 4 [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]])
    (Up (2 ^ a)) 0 1 (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num [Up]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, Up] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

end Twisted

section Arith

theorem five_dvd_phi4 (a : ℕ) : 5 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  have h : (2 ^ (2 * a + 1)) ^ 2 + 1 = 4 * 16 ^ a + 1 := by
    have : (2 ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
      rw [← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
      norm_num
    rw [this]
  rw [h, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_primitive_five (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] :
    ∃ ξ : Lˣ, IsPrimitiveRoot ξ 5 := by
  have hp : (5 : L) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff L 2 5).1 (by exact_mod_cast h)
    omega
  have : NeZero (5 : ℕ) := ⟨by norm_num⟩
  have : NeZero ((5 : ℕ) : L) := ⟨by exact_mod_cast hp⟩
  obtain ⟨ξ₀, hξ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  lift ξ₀ to Lˣ using hξ₀.isUnit (by norm_num)
  rw [IsPrimitiveRoot.coe_units_iff] at hξ₀
  exact ⟨ξ₀, hξ₀⟩

theorem zpow_pow_five_aux {L : Type} [Field L] {x : Lˣ} (hx : x ^ 5 = 1) (n : ℤ) :
    (x ^ n) ^ 5 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

end Arith

section Frame

variable (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ)

structure Plane5 where
  D : ReeFrameData K (AlgebraicClosure K) a
  w : WeylGroup ReeTag.F4.tag
  U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ
  g₀ : ModGL ReeTag.F4.tag (AlgebraicClosure K)
  hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag (AlgebraicClosure K)
  hFg₀ : Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) (AlgebraicClosure K) w
  Ψ : (rootsOfUnity 5 (AlgebraicClosure K)) × (rootsOfUnity 5 (AlgebraicClosure K)) →*
    ReeTag.F4.reeGamma K a
  Ψinj : Function.Injective Ψ
  hΨ : ∀ z, reeConj g₀ (Ψ z) = rootDiagUnit ReeTag.F4.tag
    (expTuple ((z.1 : (AlgebraicClosure K)ˣ)) (z.2 : (AlgebraicClosure K)ˣ) U)
  hker : KerOKZ (fun s i => ((U s i : ℤ) : ZMod 5))
  hcov : CoverZ (fun s i => ((U s i : ℤ) : ZMod 5))

variable {K a}

theorem exists_plane5 (hK : Nat.card K = 2 ^ (2 * a + 1)) : Nonempty (Plane5 K a) := by
  classical
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h5 : 5 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := five_dvd_phi4 a
  have hcast : ∀ w : ZMod 5, (w = (2 : ZMod 5) ^ a) →
      (2 * w ^ 2 + 2 * w + 1 = 0 ↔ (2 : ZMod 5) ^ (2 * a + 1) + 2 ^ (a + 1) + 1 = 0) ∧
      (2 * w ^ 2 - 2 * w + 1 = 0 ↔ (2 : ZMod 5) ^ (2 * a + 1) - 2 ^ (a + 1) + 1 = 0) := by
    intro w hw
    subst hw
    constructor <;> (constructor <;> intro h <;> [skip; skip] <;> ring_nf at h ⊢ <;> linear_combination h)
  rcases dvd_phi4_cases Nat.prime_five (by norm_num) h5 with ⟨h1, -⟩ | ⟨h1, -⟩
  · have hmM : ((5 : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by exact_mod_cast h1
    obtain ⟨Φ, hΦinj, hΦF, hΦ⟩ := exists_hom_five_p D.isFrob hmM
    obtain ⟨g₀, hg₀, hFg₀, Ψ, hΨinj, hΨ⟩ := exists_hom_reeGamma_explicit D wPhi4p Φ hΦinj hΦF
    have hz : (2 : ZMod 5) ^ (2 * a + 1) + 2 ^ (a + 1) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hmM
      simpa using this
    have hv : 2 * ((2 : ZMod 5) ^ a) ^ 2 + 2 * (2 : ZMod 5) ^ a + 1 = 0 :=
      ((hcast _ rfl).1.2 hz)
    have hW : (fun s i => (((Up (2 ^ a)) s i : ℤ) : ZMod 5)) = Wp ((2 : ZMod 5) ^ a) := by
      have h : ∀ (s : Fin 2) (i : Fin 4), (((Up (2 ^ a)) s i : ℤ) : ZMod 5) =
          Wp ((2 : ZMod 5) ^ a) s i := by
        intro s i
        fin_cases s <;> fin_cases i <;> simp [Up, Wp]
      funext s i
      exact h s i
    refine ⟨⟨D, wPhi4p, Up (2 ^ a), g₀, hg₀, hFg₀, Ψ, hΨinj, fun z => ?_, ?_, ?_⟩⟩
    · rw [reeConj_apply, hΨ z, ← hΦ z]
      group
    · rw [hW]; exact kerOKZ_Wp _ hv
    · rw [hW]; exact coverZ_Wp _ hv
  · have hmM : ((5 : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
      have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Int.natCast_dvd_natCast.2 h1
      push_cast [Nat.cast_sub hle] at this
      exact_mod_cast this
    obtain ⟨Φ, hΦinj, hΦF, hΦ⟩ := exists_hom_five_m D.isFrob hmM
    obtain ⟨g₀, hg₀, hFg₀, Ψ, hΨinj, hΨ⟩ := exists_hom_reeGamma_explicit D wPhi4m Φ hΦinj hΦF
    have hz : (2 : ZMod 5) ^ (2 * a + 1) - 2 ^ (a + 1) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hmM
      simpa using this
    have hv : 2 * ((2 : ZMod 5) ^ a) ^ 2 - 2 * (2 : ZMod 5) ^ a + 1 = 0 :=
      ((hcast _ rfl).2.2 hz)
    have hW : (fun s i => (((Um (2 ^ a)) s i : ℤ) : ZMod 5)) = Wm ((2 : ZMod 5) ^ a) := by
      have h : ∀ (s : Fin 2) (i : Fin 4), (((Um (2 ^ a)) s i : ℤ) : ZMod 5) =
          Wm ((2 : ZMod 5) ^ a) s i := by
        intro s i
        fin_cases s <;> fin_cases i <;> simp [Um, Wm]
      funext s i
      exact h s i
    refine ⟨⟨D, wPhi4m, Um (2 ^ a), g₀, hg₀, hFg₀, Ψ, hΨinj, fun z => ?_, ?_, ?_⟩⟩
    · rw [reeConj_apply, hΨ z, ← hΦ z]
      group
    · rw [hW]; exact kerOKZ_Wm _ hv
    · rw [hW]; exact coverZ_Wm _ hv

end Frame

section Bridge

variable {L : Type} [Field L]

omit [Field L] in
theorem uPZ_cast (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (s : Fin 2)
    (α : Fin ReeTag.F4.tag.rank → ℤ) :
    ((∑ i, U s i * α i : ℤ) : ZMod 5) = uPZ (fun s i => ((U s i : ℤ) : ZMod 5)) s α := by
  simp [uPZ]

theorem rootChar_expTuple_pow_five_iff {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 5)
    (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (a b : ℕ) (α : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (expTuple (ξ ^ a) (ξ ^ b) U) α = 1 ↔
      (a : ZMod 5) * uPZ (fun s i => ((U s i : ℤ) : ZMod 5)) 0 α +
        (b : ZMod 5) * uPZ (fun s i => ((U s i : ℤ) : ZMod 5)) 1 α = 0 := by
  rw [rootChar_expTuple, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
    hξ.zpow_eq_one_iff_dvd, ← uPZ_cast, ← uPZ_cast, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

theorem rootCharKernel_expTuple_pow_five {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 5)
    (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (a b : ℕ) :
    rootCharKernel (expTuple (ξ ^ a) (ξ ^ b) U) =
      ↑(kerZ (fun s i => ((U s i : ℤ) : ZMod 5)) (a : ZMod 5) (b : ZMod 5)) := by
  ext α
  simp only [rootCharKernel, kerZ, Set.mem_ofPred_eq, Finset.coe_filter]
  rw [rootChar_expTuple_pow_five_iff hξ]
  exact and_congr_left (fun _ => mem_rootFinset.symm)

theorem ncard_kernel_inter_long {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 5)
    (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (a b : ℕ) :
    (rootCharKernel (expTuple (ξ ^ a) (ξ ^ b) U) ∩ ReeTag.F4.longRoots).ncard =
      ((kerZ (fun s i => ((U s i : ℤ) : ZMod 5)) (a : ZMod 5) (b : ZMod 5)).filter
        fun α => ReeTag.F4.quadForm α = 4).card := by
  rw [← Set.ncard_coe_finset, rootCharKernel_expTuple_pow_five hξ, ReeTag.longRoots_eq]
  congr 1
  ext α
  simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter]
  have h4 : (2 * (ReeTag.F4.prime : ℤ)) = 4 := by simp [ReeTag.prime]
  rw [h4]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Finset.mem_filter.1 h1).1, h2⟩

theorem ncard_kernel_inter_short {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 5)
    (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (a b : ℕ) :
    (rootCharKernel (expTuple (ξ ^ a) (ξ ^ b) U) ∩ ReeTag.F4.shortRoots).ncard =
      ((kerZ (fun s i => ((U s i : ℤ) : ZMod 5)) (a : ZMod 5) (b : ZMod 5)).filter
        fun α => ReeTag.F4.quadForm α = 2).card := by
  rw [← Set.ncard_coe_finset, rootCharKernel_expTuple_pow_five hξ, ReeTag.shortRoots_eq]
  congr 1
  ext α
  simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Finset.mem_filter.1 h1).1, h2⟩

end Bridge

section Decomp

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

@[expose] def IsDecomp (P : Plane5 K a)
    (z : (rootsOfUnity 5 (AlgebraicClosure K)) × (rootsOfUnity 5 (AlgebraicClosure K)))
    (A Sg : Subgroup (ReeTag.F4.reeGamma K a)) : Prop :=
  (∀ γ, γ ∈ A ↔ reeConj P.g₀ γ ∈ ZGrp (L := AlgebraicClosure K)
    (rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ) P.U))) ∧
  (∀ α ∈ A, ∀ s ∈ Sg, α * s = s * α) ∧ A ⊓ Sg = ⊥ ∧
  A ⊔ Sg = Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) ∧ P.Ψ z ∈ A ∧
  Nonempty (Sg ≃* suzukiGroup a K)

theorem plane5_decomp (hK : Nat.card K = 2 ^ (2 * a + 1)) (P : Plane5 K a)
    (z : (rootsOfUnity 5 (AlgebraicClosure K)) × (rootsOfUnity 5 (AlgebraicClosure K)))
    (hz1 : z ≠ 1) : ∃ A Sg : Subgroup (ReeTag.F4.reeGamma K a), IsDecomp P z A Sg := by
  classical
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ξ, hξ⟩ := exists_primitive_five (AlgebraicClosure K)
  have hexp : ∀ w : rootsOfUnity 5 (AlgebraicClosure K),
      ∃ s < 5, (w : (AlgebraicClosure K)ˣ) = ξ ^ s := fun w => by
    obtain ⟨i, hi, h⟩ := hξ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 5 _).1 w.2)
    exact ⟨i, hi, h.symm⟩
  obtain ⟨s, hs, hs'⟩ := hexp z.1
  obtain ⟨t, ht, ht'⟩ := hexp z.2
  have hst : (s : ZMod 5) ≠ 0 ∨ (t : ZMod 5) ≠ 0 := by
    by_contra h
    push Not at h
    have hs0 : s = 0 := by
      have := (ZMod.natCast_eq_zero_iff s 5).1 h.1
      omega
    have ht0 : t = 0 := by
      have := (ZMod.natCast_eq_zero_iff t 5).1 h.2
      omega
    apply hz1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [hs', hs0, pow_zero]; rfl
    · rw [ht', ht0, pow_zero]; rfl
  have hz5 : (z.1 : (AlgebraicClosure K)ˣ) ^ 5 = 1 ∧ (z.2 : (AlgebraicClosure K)ˣ) ^ 5 = 1 :=
    ⟨(mem_rootsOfUnity 5 _).1 z.1.2, (mem_rootsOfUnity 5 _).1 z.2.2⟩
  set b₀ : Fin ReeTag.F4.tag.rank → (AlgebraicClosure K)ˣ :=
    expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ) P.U with hb₀
  have hb₀' : b₀ = expTuple (ξ ^ s) (ξ ^ t) P.U := by rw [hb₀, hs', ht']
  have hxb : reeConj P.g₀ (P.Ψ z) = rootDiagUnit ReeTag.F4.tag b₀ := P.hΨ z
  have hbF : rootDiagUnit ReeTag.F4.tag b₀ ∈ twistedFixed P.D.F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) (AlgebraicClosure K) P.w) := by
    rw [← hxb]
    exact reeConj_mem_twistedFixed P.D P.hg₀ P.hFg₀ _
  have hbp : ∀ i, b₀ i ^ 5 = 1 := by
    intro i
    show ((z.1 : (AlgebraicClosure K)ˣ) ^ P.U 0 i * (z.2 : (AlgebraicClosure K)ˣ) ^ P.U 1 i) ^ 5 = 1
    rw [mul_pow, zpow_pow_five_aux hz5.1, zpow_pow_five_aux hz5.2, mul_one]
  have hb1 : b₀ ≠ 1 := by
    intro h
    apply hz1
    apply P.Ψinj
    apply reeConj_injective P.g₀
    rw [hxb, h, rootDiagUnit_one, map_one, map_one]
  have hlong : (rootCharKernel b₀ ∩ ReeTag.F4.longRoots).ncard = 4 := by
    rw [hb₀', ncard_kernel_inter_long hξ]
    exact (P.hker _ _ hst).1
  have hshort : (rootCharKernel b₀ ∩ ReeTag.F4.shortRoots).ncard = 4 := by
    rw [hb₀', ncard_kernel_inter_short hξ]
    exact (P.hker _ _ hst).2
  obtain ⟨A, Sg, hAmem, -, hcomm, hinf, hsup, hxA, hSz⟩ :=
    exists_decomp_of_kernel P.D hK P.w P.hg₀ P.hFg₀ hbF hbp hb1 hlong hshort (P.Ψ z) hxb
  exact ⟨A, Sg, hAmem, hcomm, hinf, hsup, hxA, hSz⟩


theorem card_range_plane5 (P : Plane5 K a) : Nat.card P.Ψ.range = 5 ^ 2 := by
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : (5 : AlgebraicClosure K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 5).1 (by exact_mod_cast h)
    omega
  rw [← Nat.card_congr (MonoidHom.ofInjective P.Ψinj).toEquiv, Nat.card_prod]
  have := card_rootsOfUnity_pow (p := 5) (e := 1) (L := AlgebraicClosure K) hpL
  rw [pow_one] at this
  rw [this]
  norm_num

theorem pow_five_range_plane5 (P : Plane5 K a) : ∀ x ∈ P.Ψ.range, x ^ 5 = 1 := by
  rintro _ ⟨z, rfl⟩
  rw [← map_pow]
  have : z ^ 5 = 1 := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact (mem_rootsOfUnity 5 _).1 z.1.2
    · exact (mem_rootsOfUnity 5 _).1 z.2.2
  rw [this, map_one]

end Decomp

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux
