module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldLiftTwist
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Descent


theorem exists_baseChangeGL_eq_of_entries {k L : Type} [Field k] [Field L] (f : k →+* L) {τ : Tag}
    (y : ModGL τ L)
    (hy : ∀ a b, (y : Module.End L (RootModule τ L)) (Finsupp.single b 1) a ∈ Set.range f)
    (hy' : ∀ a b, ((y⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b 1) a ∈
      Set.range f) :
    ∃ y₀ : ModGL τ k, baseChangeGL f y₀ = y := by
  classical
  set p : L → k := Function.invFun f
  have hp : ∀ c ∈ Set.range f, f (p c) = c := fun c hc => Function.invFun_eq hc
  have hp0 : p 0 = 0 := f.injective (by rw [hp 0 ⟨0, map_zero f⟩, map_zero])
  have key : ∀ A : Module.End L (RootModule τ L),
      (∀ a b, A (Finsupp.single b 1) a ∈ Set.range f) → ∃ A₀, baseChangeEnd f A₀ = A := by
    intro A hA
    refine ⟨Finsupp.linearCombination k
      (fun b => Finsupp.mapRange p hp0 (A (Finsupp.single b 1))), ?_⟩
    refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [baseChangeEnd_single, Finsupp.linearCombination_single, one_smul]
    ext a
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply]
    exact hp _ (hA a b)
  obtain ⟨A₀, hA₀⟩ := key _ hy
  obtain ⟨B₀, hB₀⟩ := key _ hy'
  have hinj : ∀ C D : Module.End k (RootModule τ k), baseChangeEnd f C = baseChangeEnd f D →
      C = D := fun C D h =>
    (baseChange_baseChangeEnd f C).eq_of_injective f.injective (h ▸ baseChange_baseChangeEnd f D)
  have hmul : ∀ C D : Module.End k (RootModule τ k),
      baseChangeEnd f (C * D) = baseChangeEnd f C * baseChangeEnd f D :=
    fun C D => map_mul (baseChangeEndHom (τ := τ) f) C D
  have hone : baseChangeEnd f (1 : Module.End k (RootModule τ k)) = 1 :=
    map_one (baseChangeEndHom (τ := τ) f)
  have h1 : A₀ * B₀ = 1 := hinj _ _ (by rw [hmul, hA₀, hB₀, Units.mul_inv, hone])
  have h2 : B₀ * A₀ = 1 := hinj _ _ (by rw [hmul, hA₀, hB₀, Units.inv_mul, hone])
  exact ⟨⟨A₀, B₀, h1, h2⟩, Units.ext (by rw [coe_baseChangeGL]; exact hA₀)⟩

theorem baseChangeGL_pow_eq_conj {L : Type} [Field L] [CharP L 2] {τ : Tag} (f : L →+* L)
    (v : WeylGroup τ) {y : ModGL τ L}
    (h : baseChangeGL f y =
      (canonicalRep (coxeterSystem τ) L v)⁻¹ * y * canonicalRep (coxeterSystem τ) L v) :
    ∀ k : ℕ, baseChangeGL (f ^ k) y =
      (canonicalRep (coxeterSystem τ) L (v ^ k))⁻¹ * y * canonicalRep (coxeterSystem τ) L (v ^ k)
  | 0 => by
    rw [pow_zero, pow_zero, canonicalRep_one, inv_one, one_mul, mul_one]
    exact baseChangeGL_id L y
  | k + 1 => by
    have e : f ^ (k + 1) = (f ^ k).comp f := pow_succ f k
    rw [e, ← baseChangeGL_baseChangeGL, h, map_mul, map_mul, map_inv, baseChangeGL_canonicalRep,
      baseChangeGL_pow_eq_conj f v h k, pow_succ,
      CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo]
    group

end Descent

section Adjoint


theorem mem_adjointGroup_of_baseChangeGL_mem (k L : Type) [Field k] [IsAlgClosed k] [Field L]
    [IsAlgClosed L] [Algebra k L] {τ : Tag} {y₀ : ModGL τ k}
    (h : baseChangeGL (algebraMap k L) y₀ ∈ adjointGroup τ L) : y₀ ∈ adjointGroup τ k := by
  have hL := (exceptional_Lang_exact_root_group_base_change k L τ).2.2.1
  have hk := (exceptional_Lang_exact_root_group_base_change k k τ).2.2.1
  refine (hk y₀).2 fun g hg => ?_
  have h1 := (hL _).1 h g hg
  have h2 : (Algebra.ofId k L).comp (unitCo k (D := k) y₀) =
      unitCo k (D := L) (baseChangeGL (algebraMap k L) y₀) :=
    comp_unitCo_of_baseChange' (Algebra.ofId k L) y₀ _ (baseChange_baseChangeEnd _ _)
  have h3 : algebraMap k L (unitCo k (D := k) y₀ g) = 0 := by
    have := congrArg (fun φ : GLCoord k (Label τ) →ₐ[k] L => φ g) h2
    simp only [AlgHom.comp_apply, Algebra.ofId_apply] at this
    rw [this]
    exact h1
  exact (algebraMap k L).injective (h3.trans (map_zero _).symm)

end Adjoint

section Model


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem exists_frob_conj_of_shape (S : LangSetup Tag.E6 L p₀) (hS : E6ShapeSetup S) :
    ∃ (f : L →+* L) (Q : ℕ) (v : WeylGroup Tag.E6), 1 < Q ∧ (∀ c, f c = c ^ Q) ∧
      ∀ y ∈ S.D.model, baseChangeGL f y =
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ * y * canonicalRep (coxeterSystem Tag.E6) L v := by
  obtain ⟨Fr, hFr, hcase⟩ := hS
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
  rcases hcase with ⟨hΦ, -⟩ | ⟨hΦ, -⟩
  · refine ⟨Fr, S.D.q, w, hq1, hFr, fun y hy => ?_⟩
    have h := ((S.D.mem_model).1 hy).2
    rw [hΦ, hn, CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self] at h
    have e : baseChangeGL Fr y = (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
        (canonicalRep (coxeterSystem Tag.E6) L w * baseChangeGL Fr y *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) * canonicalRep (coxeterSystem Tag.E6) L w := by
      group
    rw [e, h]
  · obtain ⟨δ, hδ⟩ : ∃ δ : WeylGroup Tag.E6, δ = weylTwist TwistTag.E6 w := ⟨_, rfl⟩
    refine ⟨Fr.comp Fr, S.D.q * S.D.q, w * δ, Nat.one_lt_mul_iff.2
      ⟨by omega, by omega, Or.inl hq1⟩, fun c => by rw [RingHom.comp_apply, hFr, hFr, ← pow_mul],
      fun y hy => ?_⟩
    have h := ((S.D.mem_model).1 hy).2
    rw [hn] at h
    have h1 : S.D.Φ y = (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * y *
        canonicalRep (coxeterSystem Tag.E6) L w := by
      have e : S.D.Φ y = (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          (canonicalRep (coxeterSystem Tag.E6) L w * S.D.Φ y *
            (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) * canonicalRep (coxeterSystem Tag.E6) L w := by
        group
      rw [e, h]
    have hΦn : S.D.Φ (canonicalRep (coxeterSystem Tag.E6) L w) =
        canonicalRep (coxeterSystem Tag.E6) L δ := by
      rw [hΦ, hδ]
      exact twistHom_canonicalRep TwistTag.E6 L Fr w
    have hΦΦ : S.D.Φ (S.D.Φ y) = baseChangeGL (Fr.comp Fr) y := by
      rw [hΦ]
      exact (CFSG.StandardType.TwE6FieldCore.twistHom_twistHom_eq_entrywise Fr Fr y).trans
        (CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self (Fr.comp Fr) y)
    have h4 : canonicalRep (coxeterSystem Tag.E6) L (w * δ) =
        canonicalRep (coxeterSystem Tag.E6) L w * canonicalRep (coxeterSystem Tag.E6) L δ :=
      CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo _ _
    rw [← hΦΦ, h1, map_mul, map_mul, map_inv, hΦn, h1, h4]
    group

theorem exists_finite_model_descent (S : LangSetup Tag.E6 L p₀) (hS : E6ShapeSetup S)
    (E : Finset L) (hE : ∀ c ∈ E, c ^ 3 = 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (ι : K →+* L),
      (∀ y ∈ S.D.model, ∃ y₃ ∈ adjointGroup Tag.E6 K, baseChangeGL ι y₃ = y) ∧
        ∀ c ∈ E, c ∈ Set.range ι := by
  classical
  obtain ⟨f, Q, v, hQ, hf, hconj⟩ := exists_frob_conj_of_shape S hS
  letI : Algebra (ZMod 2) L := ZMod.algebra L 2
  set L₀ := algebraicClosure (ZMod 2) L
  haveI : IsAlgClosed L₀ := IsAlgClosure.isAlgClosed (ZMod 2)
  haveI : Algebra.IsAlgebraic (ZMod 2) L₀ := algebraicClosure.isAlgebraic (ZMod 2) L
  have halg : ∀ {c : L} {N : ℕ}, 1 < N → c ^ N = c → c ∈ L₀ := fun {c N} hN hc =>
    mem_algebraicClosure_iff.2 ⟨Polynomial.X ^ N - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod 2) hN, by simp [hc]⟩
  have hm : 0 < orderOf v := orderOf_pos v
  have hentry : ∀ y ∈ S.D.model, ∀ a b,
      (y : Module.End L (RootModule Tag.E6 L)) (Finsupp.single b 1) a ∈ L₀ := by
    intro y hy a b
    have h1 := baseChangeGL_pow_eq_conj f v (hconj y hy) (orderOf v)
    rw [pow_orderOf_eq_one, canonicalRep_one, inv_one, one_mul, mul_one] at h1
    have h2 := congrArg
      (fun g : ModGL Tag.E6 L => (g : Module.End L (RootModule Tag.E6 L)) (Finsupp.single b 1) a) h1
    simp only [baseChangeGL_apply_single, Finsupp.mapRange_apply] at h2
    rw [CFSG.StandardType.TwE6FieldCore.ringHom_pow_apply_eq_pow hf] at h2
    exact halg (Nat.one_lt_pow hm.ne' hQ) h2
  have hdesc : ∀ y ∈ S.D.model,
      ∃ y₀ ∈ adjointGroup Tag.E6 L₀, baseChangeGL (algebraMap L₀ L) y₀ = y := by
    intro y hy
    obtain ⟨y₀, hy₀⟩ := exists_baseChangeGL_eq_of_entries (algebraMap L₀ L) y
      (fun a b => ⟨⟨_, hentry y hy a b⟩, rfl⟩) (fun a b => ⟨⟨_, hentry y⁻¹ (inv_mem hy) a b⟩, rfl⟩)
    refine ⟨y₀, mem_adjointGroup_of_baseChangeGL_mem L₀ L ?_, hy₀⟩
    rw [hy₀]
    exact ((S.D.mem_model).1 hy).1
  haveI : Finite S.D.model := S.finite
  letI : Fintype S.D.model := Fintype.ofFinite _
  have hpar : ∀ y : S.D.model, ∃ Ey : Finset L₀, ∀ K : Subfield L₀, (Ey : Set L₀) ⊆ K →
      ∃ y₃ ∈ adjointGroup Tag.E6 K,
        baseChangeGL ((algebraMap L₀ L).comp K.subtype) y₃ = (y : ModGL Tag.E6 L) := by
    intro y
    obtain ⟨y₀, hy₀C, hy₀⟩ := hdesc y y.2
    obtain ⟨Ey, hEy⟩ := exists_finset_descent hy₀C
    refine ⟨Ey, fun K hK => ?_⟩
    obtain ⟨y₃, h₃, e₃⟩ := hEy K hK
    exact ⟨y₃, h₃, by rw [← baseChangeGL_baseChangeGL, e₃, hy₀]⟩
  choose Ey hEy using hpar
  have hE₀ : ∀ c ∈ E, c ∈ L₀ := fun c hc => halg (N := 4) (by norm_num) (by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hE c hc, one_mul])
  let E₀ : Finset L₀ := E.attach.image fun c => ⟨c.1, hE₀ c.1 c.2⟩
  obtain ⟨K, hKfin, hKE, -⟩ :=
    exists_finite_subfield_of_finset (K := ZMod 2) (L := L₀) (Finset.univ.biUnion Ey ∪ E₀)
  refine ⟨K, inferInstance, hKfin, (algebraMap L₀ L).comp K.subtype, fun y hy => ?_, fun c hc => ?_⟩
  · exact hEy ⟨y, hy⟩ K fun x hx => hKE (Finset.mem_coe.2 (Finset.mem_union_left _
      (Finset.mem_biUnion.2 ⟨⟨y, hy⟩, Finset.mem_univ _, hx⟩)))
  · have hcK : (⟨c, hE₀ c hc⟩ : L₀) ∈ K := hKE (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨⟨c, hc⟩, Finset.mem_attach _ _, rfl⟩)))
    exact ⟨⟨_, hcK⟩, rfl⟩

end Model

end CFSG.LocalAnalysis.GLTheoremA.T158

end
