module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremB

namespace TwE6UniqAbs

section Generic


set_option linter.unusedSectionVars false

theorem glaPComponent_unique_of_langSetup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hU : ∀ i j : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) j) →
        rationalComponent S.ρ S.Γ (rootCharHom a) i = rationalComponent S.ρ S.Γ (rootCharHom a) j)
    {J J' : Subgroup C} (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJ' : GLAPComponent 3 (fixSubgroup β) J') : J = J' := by
  classical
  set d : ModGL τ L := rootDiagUnit τ a with hd
  set R : KernelComponent (rootCharHom a) → Subgroup (ModGL τ L) :=
    fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [map_fixSubgroup_eq_of_conj ι hι β d hβ, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {d}).comap ι = fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hι _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {d} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ L (rootCharHom a)).2.1
  have hcompR : ∀ i : KernelComponent (rootCharHom a), CFSG.IsQuasisimple (R i) →
      IsComponentOf (R i) (S.Γ ⊓ Subgroup.centralizer {d}) := by
    intro i hi
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hi⟩
  have key : ∀ {J₀ : Subgroup C}, GLAPComponent 3 (fixSubgroup β) J₀ →
      ∃ i, CFSG.IsQuasisimple (R i) ∧ J₀ = (R i).comap ι := by
    intro J₀ hJ₀
    have hperf : ⁅J₀, J₀⁆ = J₀ := glaPComponent_perfect hJ₀
    have hne : J₀ ≠ ⊥ := glaPComponent_ne_bot hJ₀
    have hJ₀C : J₀ ≤ fixSubgroup β := hJ₀.1
    have hPmap : J₀.map ι ≤ S.Γ ⊓ Subgroup.centralizer {d} := by
      rw [← hfix]
      exact Subgroup.map_mono hJ₀C
    have hperfmap : ⁅J₀.map ι, J₀.map ι⁆ = J₀.map ι := by
      rw [← Subgroup.map_commutator, hperf]
    have h2 := perfect_le_iSup_rationalComponent_of_prime S hp hT hap h1 hTame (J₀.map ι) hPmap
      hperfmap
    obtain ⟨i₀, hi₀⟩ : ∃ i, CFSG.IsQuasisimple (R i) := by
      by_contra hcon
      push Not at hcon
      haveI : IsEmpty {i : KernelComponent (rootCharHom a) // CFSG.IsQuasisimple (R i)} :=
        ⟨fun ⟨i, hi⟩ => hcon i hi⟩
      rw [iSup_of_empty] at h2
      exact hne ((Subgroup.map_eq_bot_iff_of_injective _ hι).1 (le_bot_iff.1 h2))
    have hle : J₀.map ι ≤ R i₀ :=
      h2.trans (iSup_le fun i => (hU i.1 i₀ i.2 hi₀).le)
    have hJR : J₀ ≤ (R i₀).comap ι := (Subgroup.map_le_iff_le_comap).1 hle
    have hRrange : R i₀ ≤ ι.range := (hcompR i₀ hi₀).1.trans hCdrange
    have hcomp := isComponentOf_comap_of_injective ι hι hRrange hCdrange (hcompR i₀ hi₀)
    rw [hcomapfix] at hcomp
    refine ⟨i₀, hi₀, ?_⟩
    have hsub : IsSubnormal J₀ ((R i₀).comap ι) :=
      isSubnormal_of_le_of_le hJ₀.2.1 hJR hcomp.1
    rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center hsub hcomp.2.2 with
      h | h
    · exact h
    · exfalso
      have hcomm : ⁅J₀, J₀⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨x', hx', rfl⟩ := h hx
        obtain ⟨y', hy', rfl⟩ := h hy
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hx' y')
      exact hne (hperf ▸ hcomm)
  obtain ⟨i, hi, rfl⟩ := key hJ
  obtain ⟨j, hj, rfl⟩ := key hJ'
  exact congrArg (Subgroup.comap ι) (hU i j hi hj)

end Generic

section Model


set_option linter.unusedSectionVars false

theorem twE6UniqModel_of_ratQuasiEq (hR : RatQuasiEq) : TwE6UniqModel := by
  classical
  intro K _ _ hK σ hσ β hβ3 hβ1 J J' hJ hJ'
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hmem := Bal209TwoOuterInAux.mem_inn_sup_diag_of_pow_three hK σ hσ hβ3
  rw [← range_twistedE6InndiagConj] at hmem
  obtain ⟨h, rfl⟩ := hmem
  have hp1 : h ^ 3 = 1 :=
    twistedE6InndiagConj_injective Nat.prime_two le_rfl hK2 σ hσ2
      (by rw [map_pow, hβ3, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
  obtain ⟨S, a, ι, hq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two le_rfl hK2 σ hσ2 Nat.prime_three
      (by decide) Nat.prime_five (by decide) (Or.inl le_rfl) monomialToralAt_E6_three
      (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne Nat.prime_two Nat.prime_three hK2 (by decide)
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL (fun h => absurd h (by decide)) hT
    hap h1
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) :=
    Finite.of_injective (fun x => (x : ModGL TwistTag.E6.tag K)) Subtype.val_injective
  exact glaPComponent_unique_of_langSetup S Nat.prime_three ι hinj hrange _ hconj hT hap h1 hTame
    (hR (AlgebraicClosure K) 5 S a (by rw [hq]; norm_num) hT hap h1) hJ hJ'

end Model

end TwE6UniqAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
