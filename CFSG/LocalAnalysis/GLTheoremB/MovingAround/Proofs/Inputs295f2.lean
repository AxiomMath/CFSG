module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295f
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295e2
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompStd
public import CFSG.RankThree.PartOne.KE.E7FourStabFive

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295f

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

set_option linter.unusedSectionVars false

theorem kys_e6KerCount_inner : ∀ y0 y1 y2 y3 y4 : ZMod 3,
    subLin (τ := .E6) e6InnerVec ![y0, y1, y2, y3, y4] ≠ 0 →
      e6KerCount (subLin (τ := .E6) e6InnerVec ![y0, y1, y2, y3, y4]) ∈
        ({18, 24, 30} : Finset ℕ) := by
  decide +kernel

section Bridge


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem kys_eq_one_of_mem_model_of_commute (hK : Nat.card K = 4) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2) {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {u : ModGL TwistTag.E6.tag (AlgebraicClosure K)} (huM : u ∈ twE6TwoModel (AlgebraicClosure K))
    (hu : ∀ c : twistedE6RootGroup K σ,
      u * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c : ModGL TwistTag.E6.tag K) * g0) =
      (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c : ModGL TwistTag.E6.tag K) * g0) * u) :
    u = 1 := by
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ.toRingHom c = c ^ (2 ^ 1) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]; norm_num
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) 2 1 c = c ^ (2 ^ 1) :=
    fun c => by rw [iterateFrobenius_two_one]; norm_num
  set D := LangDatum.ofTwist TwistTag.E6 (iterateFrobenius (AlgebraicClosure K) 2 1) 2
    iterateFrobenius_two_one twE6W0 hg0C hg0 with hD
  have huD : u ∈ D.model := huM
  rw [model_eq_map_twistedFixedGroup D (Fr := iterateFrobenius (AlgebraicClosure K) 2 1) rfl]
    at huD
  obtain ⟨r, hrR, hru⟩ := huD
  have hru' : g0⁻¹ * r * g0 = u := by
    rw [← hru]
    change g0⁻¹ * r * g0 = g0⁻¹ * r * g0⁻¹⁻¹
    rw [inv_inv]
  obtain ⟨-, -, hcent, -⟩ :=
    CFSG.LieType.AlgebraicGroups.E6_rational_twisted_fixed_group_faithful_action Nat.prime_two
      le_rfl K hK2 σ.toRingHom hσ2 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) hFr
  have hrC : r ∈ Subgroup.centralizer
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
        (baseChangeGL (algebraMap K (AlgebraicClosure K))) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    have h1 := hu ⟨c, hc⟩
    rw [← hru'] at h1
    have h2 : g0⁻¹ * (r * baseChangeGL (algebraMap K (AlgebraicClosure K)) c) * g0 =
        g0⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K)) c * r) * g0 := by
      calc g0⁻¹ * (r * baseChangeGL (algebraMap K (AlgebraicClosure K)) c) * g0 =
          g0⁻¹ * r * g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) c * g0) := by
            group
        _ = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) c * g0 * (g0⁻¹ * r * g0) :=
            h1
        _ = _ := by group
    have h3 := mul_left_cancel (mul_right_cancel h2)
    exact h3.symm
  have hr1 : r = 1 := by
    have hmem := Subgroup.mem_inf.2 ⟨hrR, hrC⟩
    rw [hcent] at hmem
    exact (Subgroup.mem_bot).1 hmem
  rw [← hru', hr1]
  group

theorem kys_exists_inndiag_of_model (hK : Nat.card K = 4) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2) {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {m : ModGL Tag.E6 (AlgebraicClosure K)} (hmM : m ∈ twE6TwoModel (AlgebraicClosure K))
    (hmΓ : m ∉ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
      Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) (hm3 : m ^ 3 = 1) :
    ∃ (ĝ : ModGL TwistTag.E6.tag K) (hĝ : ĝ ∈ twistedE6InndiagGL K σ),
      ĝ ∉ twistedE6RootGroup K σ ∧ ĝ ^ 3 = 1 ∧
      twistedE6InndiagConj K σ ⟨ĝ, hĝ⟩ ∉ twistedE6Inn K σ ∧
      m = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ * g0 := by
  classical
  set L := AlgebraicClosure K with hL
  set ι := algebraMap K L with hι
  set Γ : Subgroup (ModGL Tag.E6 L) := ⁅twE6TwoModel L, twE6TwoModel L⁆ with hΓ
  set e := twE6TwoEquiv hK σ hσ hg0C hg0 with he
  have hcoe : ∀ c : twistedE6RootGroup K σ,
      ((e c : Γ) : ModGL Tag.E6 L) = g0⁻¹ * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * g0 :=
    fun c => coe_twE6TwoEquiv hK σ hσ hg0C hg0 c
  have hΓM : Γ ≤ twE6TwoModel L := twE6Two_commutator_le_model
  let cm : Γ ≃* Γ :=
    { toFun := fun x => ⟨m * x * m⁻¹, twE6Two_conj_mem_commutator hmM x.2⟩
      invFun := fun x => ⟨m⁻¹ * x * m, by
        have := twE6Two_conj_mem_commutator ((twE6TwoModel L).inv_mem hmM) x.2
        rwa [inv_inv] at this⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcm : ∀ x : Γ, ((cm x : Γ) : ModGL Tag.E6 L) = m * x * m⁻¹ := fun x => rfl
  set δ : MulAut (twistedE6RootGroup K σ) := (e.trans cm).trans e.symm with hδdef
  have hδ : ∀ c, ((e (δ c) : Γ) : ModGL Tag.E6 L) = m * (e c : ModGL Tag.E6 L) * m⁻¹ := by
    intro c
    have : e (δ c) = cm (e c) := e.apply_symm_apply (cm (e c))
    rw [this, hcm]
  have hδ3 : δ ^ 3 = 1 := by
    refine MulEquiv.ext fun c => e.injective (Subtype.ext ?_)
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply,
      hδ, hδ, hδ]
    have hm3' : m * m * m = 1 := by rw [← pow_three']; exact hm3
    have : m * (m * (m * (e c : ModGL Tag.E6 L) * m⁻¹) * m⁻¹) * m⁻¹ =
        (m * m * m) * (e c : ModGL Tag.E6 L) * (m * m * m)⁻¹ := by group
    rw [this, hm3', one_mul, inv_one, mul_one]
  have hδout : δ ∉ twistedE6Inn K σ := by
    rintro ⟨c₀, hc₀⟩
    apply hmΓ
    set u : ModGL Tag.E6 L := (e c₀ : ModGL Tag.E6 L)⁻¹ * m with hu
    have huM : u ∈ twE6TwoModel L := mul_mem (inv_mem (hΓM (e c₀).2)) hmM
    have hcomm : ∀ c : twistedE6RootGroup K σ, u * (e c : ModGL Tag.E6 L) =
        (e c : ModGL Tag.E6 L) * u := by
      intro c
      have h1 : δ c = c₀ * c * c₀⁻¹ := by
        rw [← hc₀]
        rfl
      have h2 : m * (e c : ModGL Tag.E6 L) * m⁻¹ =
          (e c₀ : ModGL Tag.E6 L) * (e c : ModGL Tag.E6 L) * (e c₀ : ModGL Tag.E6 L)⁻¹ := by
        rw [← hδ, h1, map_mul, map_mul, map_inv]
        rfl
      calc u * (e c : ModGL Tag.E6 L) =
          (e c₀ : ModGL Tag.E6 L)⁻¹ * (m * (e c : ModGL Tag.E6 L) * m⁻¹) * m := by
            rw [hu]; group
        _ = (e c : ModGL Tag.E6 L) * u := by rw [h2, hu]; group
    have hu1 : u = 1 := kys_eq_one_of_mem_model_of_commute hK σ hσ hg0C hg0 huM fun c => by
      rw [← hcoe]
      exact hcomm c
    have hm : m = (e c₀ : ModGL Tag.E6 L) := by
      rw [hu] at hu1
      exact (inv_mul_eq_one.1 hu1).symm
    rw [hm]
    exact (e c₀).2
  obtain ⟨ĝ, hĝ, hĝC, hĝ3, hĝδ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux.exists_ghat hK σ hσ hδ3
      hδout
  set m₁ : ModGL Tag.E6 L := g0⁻¹ * baseChangeGL ι ĝ * g0 with hm₁
  have hm'M : m₁ ∈ twE6TwoModel L :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux.conj_ghat_mem_model hK σ hσ
      hg0C hg0 hĝ
  have hm₁c : ∀ c : twistedE6RootGroup K σ,
      m₁ * (e c : ModGL Tag.E6 L) * m₁⁻¹ = m * (e c : ModGL Tag.E6 L) * m⁻¹ := by
    intro c
    rw [← hδ, hcoe, hcoe]
    change (g0⁻¹ * baseChangeGL ι ĝ * g0) *
        (g0⁻¹ * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * g0) *
          (g0⁻¹ * baseChangeGL ι ĝ * g0)⁻¹ =
        g0⁻¹ * baseChangeGL ι ((δ c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0
    rw [hĝδ c]
    simp only [map_mul, map_inv]
    group
  have hmm' : m = m₁ := by
    set u : ModGL Tag.E6 L := m⁻¹ * m₁ with hu
    have huM : u ∈ twE6TwoModel L := mul_mem (inv_mem hmM) hm'M
    have hcomm : ∀ c : twistedE6RootGroup K σ, u * (e c : ModGL Tag.E6 L) =
        (e c : ModGL Tag.E6 L) * u := by
      intro c
      calc u * (e c : ModGL Tag.E6 L) =
          m⁻¹ * (m₁ * (e c : ModGL Tag.E6 L) * m₁⁻¹) * m₁ := by rw [hu]; group
        _ = (e c : ModGL Tag.E6 L) * u := by rw [hm₁c, hu]; group
    have hu1 : u = 1 := kys_eq_one_of_mem_model_of_commute hK σ hσ hg0C hg0 huM fun c => by
      rw [← hcoe]
      exact hcomm c
    rw [hu] at hu1
    exact (inv_mul_eq_one.1 hu1)
  refine ⟨ĝ, hĝ, hĝC, hĝ3, ?_, hmm'⟩
  have hfδ : twistedE6InndiagConj K σ ⟨ĝ, hĝ⟩ = δ :=
    MulEquiv.ext fun c => Subtype.ext ((twistedE6InndiagConj_apply ⟨ĝ, hĝ⟩ c).trans (hĝδ c).symm)
  rw [hfδ]
  exact hδout

end Bridge

section ExoticType


theorem kys_cocycle_mem_toralRootGroup {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
    {s y : ModGL Tag.E6 L} (hsM : s ∈ twE6TwoModel L) (hy : y ∈ adjointGroup Tag.E6 L)
    {a : Fin Tag.E6.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1)
    (hsy : s = y * rootDiagUnit Tag.E6 a * y⁻¹)
    (hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a := by
  set d : ModGL Tag.E6 L := rootDiagUnit Tag.E6 a with hd
  have hd3 : d ^ 3 = 1 := by
    rw [hd, rootDiagUnit_pow]
    have : a ^ 3 = 1 := funext fun j => by simpa using ha3 j
    rw [this, rootDiagUnit_one]
  have hFd : twE6TwoF L d = d := by
    rw [hd, twE6TwoF_rootDiagUnit, ← hd, inv_pow]
    exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hd3)
  have hFs : twE6TwoF L (y * d * y⁻¹) = y * d * y⁻¹ := by
    rw [← hsy]
    exact hsM.2
  rw [map_mul, map_mul, map_inv, hFd] at hFs
  set c : ModGL Tag.E6 L := y⁻¹ * twE6TwoF L y with hc
  have hcd : c * d * c⁻¹ = d := by
    calc c * d * c⁻¹ = y⁻¹ * (twE6TwoF L y * d * (twE6TwoF L y)⁻¹) * y := by rw [hc]; group
      _ = y⁻¹ * (y * d * y⁻¹) * y := by rw [hFs]
      _ = d := by group
  have hFy : twE6TwoF L y ∈ adjointGroup Tag.E6 L := by
    have hy' : (y : ModGL TwistTag.E6.tag L) ∈ adjointGroup TwistTag.E6.tag L := hy
    have h3 := mul_mem (mul_mem
      (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) L twE6W0)
      (twistHom_mem_adjointGroup TwistTag.E6 L (iterateFrobenius L 2 1) hy'))
      (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) L twE6W0))
    exact h3
  have hcG : c ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem hy) hFy
  have hcC : c ∈ toralCentralizer Tag.E6 L a := by
    refine mem_toralCentralizer.2 ⟨hcG, ?_⟩
    rw [← hd]
    have h1 : c * d = d * c := mul_inv_eq_iff_eq_mul.1 hcd
    calc d * c * d⁻¹ = c * d * d⁻¹ := by rw [← h1]
      _ = c := by group
  rw [← toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 L a hW]
  exact hcC

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem kys_ncard_kernelRoots_of_outer (hK : Nat.card K = 4) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2) {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {m : ModGL Tag.E6 (AlgebraicClosure K)} (hmM : m ∈ twE6TwoModel (AlgebraicClosure K))
    (hmΓ : m ∉ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
      Subgroup (ModGL Tag.E6 (AlgebraicClosure K))))
    {y : ModGL Tag.E6 (AlgebraicClosure K)} (hyG : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ} (ha3 : ∀ i, a i ^ 3 = 1)
    (hinner : rootChar a e6Omega3 = 1) (hmy : m = y * rootDiagUnit Tag.E6 a * y⁻¹) :
    (kernelRoots (rootCharHom a)).ncard = 18 ∨ (kernelRoots (rootCharHom a)).ncard = 24 := by
  classical
  set L := AlgebraicClosure K with hL
  haveI hcL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨ω, hω⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.exists_orderOf_three (L := L)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω
    norm_num at hω
  have hprim : IsPrimitiveRoot (ω : L) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)
  have hapow : ∀ i, ∃ n : ℕ, a i = ω ^ n := fun i => by
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (a i : L))
      (by have := congrArg Units.val (ha3 i); simpa using this)
    exact ⟨n, Units.ext (by simpa using hn.symm)⟩
  choose mm hmm using hapow
  set x : Fin Tag.E6.rank → ZMod 3 := fun i => (mm i : ZMod 3) with hxdef
  have hax : a = torV ω x := by
    funext i
    rw [torV, hxdef, ZMod.val_natCast, hmm i]
    have := pow_mod_orderOf ω (mm i)
    rw [hω] at this
    exact this.symm
  obtain ⟨y₀, hy₀⟩ := exists_subLin_eq_of_rootChar hω (x := x) (by rw [← hax]; exact hinner)
  have hcount : (kernelRoots (rootCharHom a)).ncard = e6KerCount x := by
    rw [← card_filter_rootChar_torV hω3 hω1 x, ← hax, kernelRoots_rootCharHom,
      ← Set.ncard_coe_finset]
    congr 1
    ext α
    simp only [Set.mem_setOf_eq, Finset.coe_filter, mem_rootFinset]
  have hx0 : x ≠ 0 := by
    intro hx
    apply hmΓ
    have ha1 : a = 1 := by rw [hax, hx, torV_zero]
    rw [hmy, ha1, rootDiagUnit_one, mul_one, mul_inv_cancel]
    exact one_mem _
  have hmem : e6KerCount x ∈ ({18, 24, 30} : Finset ℕ) := by
    have h := kys_e6KerCount_inner (y₀ 0) (y₀ 1) (y₀ 2) (y₀ 3) (y₀ 4)
    have hy : (![y₀ 0, y₀ 1, y₀ 2, y₀ 3, y₀ 4] : Fin 5 → ZMod 3) = y₀ := by
      funext i
      fin_cases i <;> rfl
    rw [hy, hy₀] at h
    exact h hx0
  rw [hcount]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h18 | h24 | h30
  · exact Or.inl h18
  · exact Or.inr h24
  ·
    exfalso
    apply hmΓ
    have hW := kys_kernelReflectionGroup_of_ker30 hω3 hω1 x h30
    rw [← hax] at hW
    have hcoc := kys_cocycle_mem_toralRootGroup hmM hyG ha3 hmy hW
    obtain ⟨m', hm'M, hm'⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux.exists_model_conj_dV hyG
        hmy hcoc hax
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    haveI : Finite ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) :=
      Finite.of_equiv _ (twE6TwoEquiv hK σ hσ hg0C hg0).toEquiv
    have hdx : dV ω x ∈ (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) := by
      rw [← hy₀]
      exact dV_subLin_mem hω3 (twE6Two_dV_e6InnerVec_mem_commutator hω3) y₀
    have hmx : m = m'⁻¹ * dV ω x * m' := by rw [← hm']; group
    rw [hmx]
    have h1 := twE6Two_conj_mem_commutator ((twE6TwoModel L).inv_mem hm'M) hdx
    rwa [inv_inv] at h1

end ExoticType

section Main

open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal (isPSolvable_of_mulEquiv)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_map)


theorem input29_5'LieRest4_holds : Inputs295e.Input29_5'LieRest4 := by
  intro K _ _ _ hK σ hσ g0 hg0C hg0 m hmM hmΓ hm3 y hyG a ha3 hinner hmy
  classical
  set L := AlgebraicClosure K with hL
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ĝ, hĝ, hĝC, hĝ3, hfout, hm⟩ := kys_exists_inndiag_of_model hK σ hσ hg0C hg0 hmM hmΓ hm3
  set h : twistedE6InndiagGL K σ := ⟨ĝ, hĝ⟩ with hhdef
  have hh1 : h ≠ 1 := fun h1 => hĝC (by
    have h2 : ĝ = 1 := congrArg Subtype.val h1
    rw [h2]
    exact one_mem _)
  have hh3 : h ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hĝ3)
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ (by rw [hK]; norm_num) le_rfl h hh1 hh3
  have hdimA : twE6MatFixDim K σ h = 6 + (kernelRoots (rootCharHom a)).ncard := by
    let g0' : ModGL Tag.E6 L := g0
    refine twE6MatFixDim_eq_of_conj σ h (g0' * y) a ?_
    have hb : baseChangeGL (algebraMap K L) ĝ = g0' * m * g0'⁻¹ := by
      rw [hm]
      change baseChangeGL (algebraMap K L) ĝ =
        g0 * (g0⁻¹ * baseChangeGL (algebraMap K L) ĝ * g0) * g0⁻¹
      group
    change g0' * y * rootDiagUnit Tag.E6 a * (g0' * y)⁻¹ = baseChangeGL (algebraMap K L) ĝ
    rw [hb, hmy]
    group
  have htype := kys_ncard_kernelRoots_of_outer hK σ hσ hg0C hg0 hmM hmΓ hyG ha3 hinner hmy
  have hfix : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup (twistedE6InndiagConj K σ h)) := by
    intro hs
    rw [fixSubgroup_eq_fixedPoints] at hs
    have himg := isPSolvable_map D.ι hs
    rw [D.map_fixedPoints] at himg
    haveI : Finite ↥(D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a}) :=
      kys_finite_of_le_Gamma D.S inf_le_left
    rcases htype with h18 | h24
    · have hdim : twE6MatFixDim K σ h = 24 := by rw [hdimA, h18]
      obtain ⟨i⟩ := D.nonempty_kernelComponent_a2out hdim
      exact kys_not_isPSolvable_rationalComponent_a2out D hdim rfl hfout i
        (kys_isPSolvable_of_le himg (langSubnormal_of_mem_torus D.S D.hT i).1)
    · have hdim : twE6MatFixDim K σ h = 30 := by rw [hdimA, h24]
      have hall : (kernelRoots (rootCharHom D.a)).ncard = 24 := by
        have := D.hker
        omega
      obtain ⟨α₀, hα₀⟩ : (kernelRoots (rootCharHom D.a)).Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by rw [hall]; omega)
      exact kys_not_isPSolvable_rationalComponent_d4 D hdim rfl (⟦⟨α₀, hα₀⟩⟧)
        (kys_isPSolvable_of_le himg (langSubnormal_of_mem_torus D.S D.hT _).1)
  intro hs
  apply hfix
  set e := twE6TwoEquiv hK σ hσ hg0C hg0 with he
  have hmap : (fixSubgroup (twistedE6InndiagConj K σ h)).map e.toMonoidHom =
      (Subgroup.centralizer ({m} : Set (ModGL Tag.E6 L))).subgroupOf
        (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) := by
    ext z
    obtain ⟨c, rfl⟩ := e.surjective z
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact Inputs295e.mem_fixSubgroup_iff_twE6Two hK σ hσ hg0C hg0
      (fun c => twistedE6InndiagConj_apply h c) hm c
  rw [← hmap] at hs
  exact isPSolvable_of_mulEquiv
    ((fixSubgroup (twistedE6InndiagConj K σ h)).equivMapOfInjective _ e.injective).symm hs

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295f
