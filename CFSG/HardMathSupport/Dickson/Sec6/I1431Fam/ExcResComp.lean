module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Reduce

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.HardMathSupport.Dickson.Sec6
open scoped commutatorElement

section Generic

theorem excres_isTypeL2_of_central_surjection {C R : Type*} [Group C] [Group R]
    (hC : Group.IsPerfect C) (f : C →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center C) {q : ℕ} :
    IsTypeL2 q R ↔ IsTypeL2 q C := by
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hC f hf hker
  constructor
  · rintro ⟨F, hF, hFin, hFcard, ⟨g⟩⟩
    exact ⟨F, hF, hFin, hFcard, ⟨e.trans g⟩⟩
  · rintro ⟨F, hF, hFin, hFcard, ⟨g⟩⟩
    exact ⟨F, hF, hFin, hFcard, ⟨e.symm.trans g⟩⟩

theorem excres_isTypeL2_of_glaPComponent {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hβ : PerfectInLayer β) {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup β) J) {q : ℕ}
    (hq : IsTypeL2 q (barOf 3 J)) : IsComponentOf J (fixSubgroup β) ∧ IsTypeL2 q ↥J := by
  have hle : J ≤ GLALayer (fixSubgroup β) := hβ J hJ.1 (glaPComponent_perfect hJ)
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hJ hle
  refine ⟨hcomp, ?_⟩
  have hqs : CFSG.IsQuasisimple ↥J := isQuasisimple_of_open_up34 hcomp.2.2
  have hQ := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hJ
  obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.exists_not_comm_of_quasisimple hQ
  set N : Subgroup ↥J := GLAPPrimeCore 3 ↥J with hN
  have hNn : N.Normal := GLAPPrimeCore.normal 3 ↥J
  have hNZ : N ≤ Subgroup.center ↥J := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hNn with h | h
    · exfalso
      have hsub : Subsingleton (barOf 3 J) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            change a⁻¹ * b ∈ GLAPPrimeCore 3 ↥J
            rw [← hN, h]
            exact Subgroup.mem_top _
      exact hab (Subsingleton.elim _ _)
    · exact h
  have hperf : Group.IsPerfect ↥J := ⟨hqs.1.1⟩
  exact (excres_isTypeL2_of_central_surjection hperf (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hNZ)).1 hq

end Generic

section Rational


theorem excres_component_eq_rational {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ)
    (β : MulAut C) {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {K : Subgroup C} (hK : IsComponentOf K (fixSubgroup β)) :
    ∃ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        K.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hfix : (fixSubgroup β).map ι =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [up34_map_fixSubgroup_eq ι hι β _ hβ, hrange]
  have hRC : ∀ i, rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ ι.range := fun i =>
    hrange ▸ ((langSubnormal_of_mem_torus S hT i).1.trans inf_le_left)
  have hcomp : ∀ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      IsComponentOf ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι)
        (fixSubgroup β) := fun i hi => by
    apply up34_isComponentOf_comap ι hι
    rw [hfix]
    exact isComponentOf_rationalComponent S hT i hi
  have hKd : K.map ι ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact Subgroup.map_mono hK.1
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hperf' : ⁅K.map ι, K.map ι⁆ = K.map ι := by rw [← Subgroup.map_commutator, hKperf]
  have hbig := perfect_le_iSup_rationalComponent S hp hT hap hTame (K.map ι) hKd hperf'
  have hKle : K ≤ ⨆ i : KernelComponent (rootCharHom a),
      ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
        (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι := by
    intro x hx
    have hx' : ι x ∈ ⨆ i : KernelComponent (rootCharHom a),
        ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          rationalComponent S.ρ S.Γ (rootCharHom a) i := hbig ⟨x, hx, rfl⟩
    have e : (⨆ i : KernelComponent (rootCharHom a),
        ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι).map ι =
        ⨆ i : KernelComponent (rootCharHom a),
          ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
            rationalComponent S.ρ S.Γ (rootCharHom a) i := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun i => ?_
      rw [Subgroup.map_iSup]
      exact iSup_congr fun hi => Subgroup.map_comap_eq_self (hRC i)
    rw [← e] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← hι hyx]
  have hex : ∃ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι ≤ K := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ⁅(rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι, K⁆ = ⊥ := fun i hi =>
      (b3Lie_comp_le_or_comm (hcomp i hi) hK.1 hK.2.1).resolve_left (hcon i hi)
    have hM : (⨆ i : KernelComponent (rootCharHom a),
        ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) ≤
        Subgroup.centralizer (K : Set C) :=
      iSup_le fun i => iSup_le fun hi =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i hi)
    have hKc : K ≤ Subgroup.centralizer (K : Set C) := hKle.trans hM
    have hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.1 (hKc hb)) a ha
    obtain ⟨-, -, a, b, hab'⟩ := isQuasisimple_of_open_up34 hK.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab' ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hab a a.2 b b.2)
  obtain ⟨i, hQi, hiK⟩ := hex
  have hGsn : IsSubnormal ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) K :=
    isSubnormal_of_le_of_le (hcomp i hQi).2.1 hiK hK.1
  have hGq : CFSG.Open.IsQuasisimple ↥((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) :=
    (hcomp i hQi).2.2
  have hGp : ⁅(rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι,
      (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι⁆ =
        (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι :=
    Subgroup.isPerfect_iff.1 ⟨hGq.1⟩
  have hGne : (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι ≠ ⊥ := by
    haveI := CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_of_open_up34 hGq)
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hGeq : (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι = K :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hK.2.2 hGsn hGp hGne
  refine ⟨i, hQi, ?_⟩
  rw [← hGeq]
  exact Subgroup.map_comap_eq_self (hRC i)

end Rational

end CFSG.HardMathSupport.Dickson.Sec6.I1431
