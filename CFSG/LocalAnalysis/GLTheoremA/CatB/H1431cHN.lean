module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS2
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownAux
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Simple
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cClause

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.I271 (ShapeRkAt)

@[expose] def NoCardComp {Q : Type} [Group Q] (n : ℕ) (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({k} : Set Q)) I →
    Nat.card (PSimple 3 I) ≠ n

theorem noCardComp_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] [Finite Q'] {n : ℕ}
    (σ : Q ≃* Q') {k : Q} (h : NoCardComp n k) : NoCardComp n (σ k) := by
  intro I hI hc
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  have e := CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)
  exact h _ hI' ((Nat.card_congr e.toEquiv).symm.trans hc)

theorem noCardComp_of_mulEquiv_apply {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] {n : ℕ}
    (σ : Q ≃* Q') {k : Q} (h : NoCardComp n (σ k)) : NoCardComp n k := by
  have h' := noCardComp_of_mulEquiv σ.symm h
  rwa [MulEquiv.symm_apply_apply] at h'

theorem noCardComp_of_model {S Q T : Type} [Group S] [Group Q] [Group T] [Finite S] {n : ℕ}
    (e : S ≃* T) (b : Q ≃* T) (hQ : ∀ k : Q, k ^ 3 = 1 → NoCardComp n k) (x : S)
    (hx : x ^ 3 = 1) : NoCardComp n x := by
  let φ : S ≃* Q := e.trans b.symm
  have hxφ : (φ x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  exact noCardComp_of_mulEquiv_apply φ (hQ (φ x) hxφ)

theorem noCardComp_of_shapeRkAt {Q : Type} [Group Q] [Finite Q] {k : Q} {n : ℕ}
    {Rk : ∀ (T : Type) [Group T], Prop}
    (h : ShapeRkAt 3 (fun T _ => Nat.card T ≠ n) Rk k) : NoCardComp n k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three hc hI).elim
  · rw [huniq I hI]
    exact hg

theorem noCardComp_of_pConstrained {Q : Type} [Group Q] [Finite Q] {k : Q} {n : ℕ}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
      (Subgroup.centralizer ({k} : Set Q))) : NoCardComp n k :=
  fun _ hI => (KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three h hI).elim

theorem noCardComp_conj {Q : Type} [Group Q] [Finite Q] {n : ℕ} {c : Q} (h : NoCardComp n c)
    (g : Q) : NoCardComp n (g * c * g⁻¹) :=
  noCardComp_of_mulEquiv (MulAut.conj g) h

theorem noCardComp_one {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q] {n : ℕ}
    (hnc : ∃ a b : Q, a * b ≠ b * a) (hn : Nat.card Q ≠ n) : NoCardComp n (1 : Q) := by
  intro I hI hc
  have hI' : GLAPComponent 3 (⊤ : Subgroup Q) I := by
    have h1 : Subgroup.centralizer ({(1 : Q)} : Set Q) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [h1] at hI
    exact hI
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.rtd_nonempty_pSimple_equiv_top Nat.prime_three hnc hI'
  exact hn ((Nat.card_congr e.toEquiv).symm.trans hc)


theorem card_isA6_S8 {S : Type} [Group S] [Finite S] (h : catalogIs S S8.isA6) :
    Nat.card S = 360 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | alternating n hn =>
    simp only [S8.isA6] at hi
    rcases hi with hi | hi
    · subst hi
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card, Nat.factorial]
    · exact hi.elim
  | cyclic _ _ =>
    simp only [S8.isA6, onLie] at hi
    rcases hi with hi | hi <;> exact hi.elim
  | sporadic _ =>
    simp only [S8.isA6, onLie] at hi
    rcases hi with hi | hi <;> exact hi.elim
  | lie d =>
    simp only [S8.isA6, onLie] at hi
    rcases hi with hi | hi
    · exact hi.elim
    · obtain ⟨d, hv⟩ := d
      cases d with
      | A r q =>
        rcases r with _ | _ | r
        · exact hi.elim
        · have hc : Nat.card S =
              CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula
                (TauCeti.LieTypeIndex.A 1 q) :=
            CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 1 q, hv⟩ S ⟨e⟩
          rw [hc]
          show CFSG.Open.orderA 1 q.card = 360
          rw [show q.card = 9 from hi]
          decide
        · exact hi.elim
      | _ => exact hi.elim

section HN

open CFSG.Sporadic.HNSchreier CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement


set_option maxRecDepth 4000 in
theorem noCardComp_s1 : NoCardComp 360 (sJ 0) := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  obtain ⟨-, -, hcomm⟩ := CJ_s1_structure
  have hder := commutator_CJ_s1
  haveI hsimple : IsSimpleGroup ↥L1J := by
    have := alt3_simple
    exact MulEquiv.isSimpleGroup (alt3.equivMapOfInjective iotaA iotaA_injective).symm
  have hcard : Nat.card ↥L1J = 181440 := by
    rw [show (L1J : Subgroup JH) = alt3.map iotaA from rfl,
      Subgroup.card_map_of_injective iotaA_injective, card_alt3]
  have hLC : L1J ≤ Subgroup.centralizer ({sJ 0} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx)
  have hnp : ¬ (Nat.card ↥L1J).Prime := by
    rw [hcard]
    norm_num
  have hnab : ∃ a b : ↥L1J, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥L1J) hnp
  have h3 : 3 ∣ Nat.card ↥L1J := by
    rw [hcard]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({sJ 0} : Set ↥JH)) = Nat.card ↥L1J * 3 ^ 1 := by
    rw [show Subgroup.centralizer ({sJ 0} : Set ↥JH) = CJ (sJ 0) from rfl, card_CJ_s1, hcard]
    norm_num
  refine noCardComp_of_shapeRkAt (Rk := fun _ _ => True) ?_
  refine shapeRkAt_of_data (Good := fun T _ => Nat.card T ≠ 360) (Rk := fun _ _ => True)
    Nat.prime_three (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
    (fun _ _ _ _ _ h => h) (sJ 0) L1J hLC ?_ hsimple hnab h3 hk (by rw [hcard]; norm_num) trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈ ⁅CJ (sJ 0), CJ (sJ 0)⁆ := Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact L1J.mul_mem h1 hl

theorem noCardComp_JH (k : ↥JH) (hk : k ^ 3 = 1) : NoCardComp 360 k := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  by_cases h1 : k = 1
  · subst h1
    haveI hHN : IsSimpleGroup NativeSporadic.HN := CFSG.Sporadic.HN.isSimpleGroup_HN
    haveI : IsSimpleGroup ↥JH := @MulEquiv.isSimpleGroup _ _ _ _ hHN hnEquivJ.symm
    have hp : ¬ (Nat.card ↥JH).Prime := by rw [card_JH]; norm_num
    exact noCardComp_one
      (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := ↥JH) hp)
      (by rw [card_JH]; norm_num)
  have ho : orderOf k = 3 := orderOf_eq_prime hk h1
  rcases (order_three_classes k).1 ho with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    rw [← hg]
    exact noCardComp_conj noCardComp_s1 g
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    rw [← hg]
    exact noCardComp_conj
      (noCardComp_of_pConstrained (pConstrainedShape_of_hn3bRChecks hn3bR_checks)) g

set_option maxRecDepth 100000 in
theorem noCardComp_HN {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.sporadic .HN).Group) (x : S) (hx : x ^ 3 = 1) :
    NoCardComp 360 x := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have hb : ↥JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group := hnEquivJ.symm.trans b
  refine noCardComp_of_model (Q := ↥JH) e ?_ ?_ x hx
  · exact hb
  · exact noCardComp_JH

theorem exists_simple_card_360 {Y : Type} [Group Y] [Finite Y] {τ : MulAut Y} (hτ : τ ^ 3 = 1)
    {A : Subgroup Y}
    (hA : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup τ) A)
    (hT : S8.IsTypeWithCenter 3 A S8.isA6 1) :
    ∃ (β : MulAut (Y ⧸ Subgroup.center Y)) (J' : Subgroup (Y ⧸ Subgroup.center Y)), β ^ 3 = 1 ∧
      GLAPComponent 3 (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub β) J' ∧
      Nat.card (PSimple 3 J') = 360 := by
  obtain ⟨hTc, hZ⟩ := hT
  obtain ⟨β, J', hβ, hJ', ψ, hψs, hψk⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.component_to_simple hτ hA
  have hZbot : Subgroup.center (PQuot 3 A) = ⊥ := (Subgroup.eq_bot_iff_card _).2 hZ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hψk.trans hZbot.le
  let eψ : PQuot 3 A ≃* PQuot 3 J' := MulEquiv.ofBijective ψ ⟨hinj, hψs⟩
  have eS : PSimple 3 A ≃* PSimple 3 J' :=
    QuotientGroup.congr _ _ eψ (Subgroup.map_center_eq eψ)
  refine ⟨β, J', hβ, hJ', ?_⟩
  rw [← Nat.card_congr eS.toEquiv]
  exact card_isA6_S8 hTc

theorem i1431InspHN_holds : I1431InspHN := by
  intro Y _ _ hY _ hcat τ hτ A hA hT
  obtain ⟨β, J', hβ, hJ', hc360⟩ := exists_simple_card_360 hτ hA hT
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hncS : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  have hcen : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Y ⧸ Subgroup.center Y))
      with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds _ inferInstance
    hncS .HN ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three (by norm_num)
      hcen hout β hβ
  have hJx : GLAPComponent 3 (Subgroup.centralizer ({x} : Set (Y ⧸ Subgroup.center Y))) J' := by
    have h := hJ'
    rw [show CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub (MulAut.conj x) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) from rfl,
      KDSpor.fixSubgroup_conj_eq] at h
    exact h
  exact noCardComp_HN e x hxp J' hJx hc360

end HN

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
