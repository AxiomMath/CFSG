module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.ONAutFact
public import CFSG.ClassicalInvolution.AschTight.E3ModAut
public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON

open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Blueprint.NativeSporadic

@[expose] def autQuot {K : Type*} [Group K] (N : Subgroup K) [N.Characteristic] :
    MulAut K →* MulAut (K ⧸ N) where
  toFun α := QuotientGroup.congr N N α (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem autQuot_mk {K : Type*} [Group K] (N : Subgroup K) [N.Characteristic] (α : MulAut K)
    (x : K) : autQuot N α (QuotientGroup.mk x) = QuotientGroup.mk (α x) := rfl

theorem le_ker_of_solvable {X S : Type*} [Group X] [Group S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (f : X →* S) (hf : Function.Surjective f) (N : Subgroup X)
    [N.Normal] (hN : Group.IsSolvable N) : N ≤ f.ker := by
  have hn : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
  · intro w hw
    have : f w ∈ N.map f := ⟨w, hw, rfl⟩
    rw [h] at this
    exact this
  · exfalso
    apply hS
    have h1 : Group.IsSolvable (N.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective N)
    rw [h] at h1
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := S)).symm.toMonoidHom) (Subgroup.topEquiv (G := S)).symm.injective

theorem not_solvable_of_not_prime {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : ¬ Group.IsSolvable S := by
  intro hs
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := S)).2 hs
  exact h (@IsSimpleGroup.prime_card _ ⟨fun a b => hc a b⟩ _)

theorem card_alt7' : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp
  decide

theorem exists_of_solvable_ker {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hker : Group.IsSolvable π.ker)
    (hS : (∃ (_ : Fact (Nat.Prime 7))
        (f : X →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : X →* alternatingGroup (Fin 7), Function.Surjective f) :
    ((∃ (_ : Fact (Nat.Prime 7))
        (f : ↥π.range →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : ↥π.range →* alternatingGroup (Fin 7), Function.Surjective f) := by
  rcases hS with ⟨hp7, f, hf⟩ | ⟨f, hf⟩
  · have hcardS : Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) = 1876896 :=
      CFSG.RankThree.PartTwo.Sec15.Proof1515.card_projSL_three_seven
    have hsS : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
      CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
    have hns := not_solvable_of_not_prime (S := CFSG.Assembly.RankThreeEven.projSL 3
      (GaloisField 7 1)) (by rw [hcardS]; norm_num)
    have hle := le_ker_of_solvable hns f hf π.ker hker
    obtain ⟨g, hg⟩ := exists_surj_of_ker_le π f hle hf
    exact Or.inl ⟨hp7, g, hg⟩
  · have hsS : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have hns := not_solvable_of_not_prime (S := alternatingGroup (Fin 7))
      (by rw [card_alt7']; norm_num)
    have hle := le_ker_of_solvable hns f hf π.ker hker
    obtain ⟨g, hg⟩ := exists_surj_of_ker_le π f hle hf
    exact Or.inr ⟨g, hg⟩

section Core

variable {H : Type} [Group H] (K : Subgroup H)

@[expose] noncomputable def lam (G : Type) [Group G]
    (e : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃* G) :
    Subgroup.normalizer (K : Set H) →* MulAut G :=
  ((MulAut.congr e).toMonoidHom.comp (centerQuotientAut (↥K ⧸ CFSG.pCore 2 ↥K))).comp
    ((autQuot (CFSG.pCore 2 ↥K)).comp (normalizerConj K))

@[expose] noncomputable def projK (G : Type) [Group G]
    (e : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃* G) : ↥K →* G :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))

theorem projK_surjective (G : Type) [Group G]
    (e : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃* G) :
    Function.Surjective (projK K G e) := by
  intro g
  obtain ⟨q, rfl⟩ := e.surjective g
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨k, rfl⟩

theorem lam_projK (G : Type) [Group G]
    (e : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃* G)
    (n : Subgroup.normalizer (K : Set H)) (k : ↥K) :
    lam K G e n (projK K G e k) = projK K G e (normalizerConj K n k) := by
  simp [lam, projK, MulAut.congr_apply, centerQuotientAut_mk, autQuot_mk]

theorem lam_of_mem (G : Type) [Group G]
    (e : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃* G)
    (k : ↥K) :
    lam K G e ⟨(k : H), Subgroup.le_normalizer k.2⟩ = MulAut.conj (projK K G e k) := by
  ext g
  obtain ⟨k', rfl⟩ := projK_surjective K G e g
  rw [lam_projK, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem comm_mem_pCoreOf_of_lam_eq_one (G : Type) [Group G]
    (e : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃* G)
    (hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K))
    (n : Subgroup.normalizer (K : Set H)) (hn : lam K G e n = 1) (k : ↥K) :
    (n : H) * k * (n : H)⁻¹ * (k : H)⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have h1 : centerQuotientAut (↥K ⧸ CFSG.pCore 2 ↥K) (autQuot (CFSG.pCore 2 ↥K) (normalizerConj K n))
      = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hn
  have h2 := eq_one_of_centerQuotientAut_eq_one h1
  have h3 := congrArg (fun γ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => γ (QuotientGroup.mk k)) h2
  simp only [autQuot_mk, MulAut.one_apply] at h3
  have h4 := (QuotientGroup.eq_iff_div_mem).1 h3
  refine ⟨normalizerConj K n k / k, h4, ?_⟩
  simp [normalizerConj_apply_coe, div_eq_mul_inv]

end Core

theorem reduction_core {H : Type} [Group H] [Finite H] {G : Type} [Group G]
    (hA : ∀ (R : Subgroup (MulAut G)) (X : Subgroup G), IsPGroup 2 R →
      ((∃ (_ : Fact (Nat.Prime 7))
          (f : ↥X →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
          Function.Surjective f) ∨
        ∃ f : ↥X →* alternatingGroup (Fin 7), Function.Surjective f) →
      (∀ x ∈ X, MulAut.conj x ∈ Subgroup.normalizer (R : Set (MulAut G))) → R = ⊥)
    (K X R : Subgroup H) (hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K))
    (e : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃* G)
    (hXK : X ≤ K)
    (hS : (∃ (_ : Fact (Nat.Prime 7))
        (f : ↥X →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : ↥X →* alternatingGroup (Fin 7), Function.Surjective f)
    (hR : IsPGroup 2 R) (hRN : R ≤ Subgroup.normalizer (K : Set H))
    (hXN : X ≤ Subgroup.normalizer (R : Set H)) :
    ⁅R, K⁆ ≤ CFSG.Open.pCoreOf 2 K := by
  classical
  set P : Subgroup ↥K := CFSG.pCore 2 ↥K with hP
  let lamR : ↥R →* MulAut G := (lam K G e).comp (Subgroup.inclusion hRN)
  have hR'p : IsPGroup 2 lamR.range :=
    hR.of_surjective lamR.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  let X₀ : ↥X →* G := (projK K G e).comp (Subgroup.inclusion hXK)
  have hker : Group.IsSolvable X₀.ker := by
    have hmem : ∀ n : X₀.ker, (QuotientGroup.mk (Subgroup.inclusion hXK n.1) : ↥K ⧸ P) ∈
        Subgroup.center (↥K ⧸ P) := by
      intro n
      have h1 : projK K G e (Subgroup.inclusion hXK n.1) = 1 := n.2
      have h2 : e.toMonoidHom (QuotientGroup.mk' (Subgroup.center (↥K ⧸ P))
          (QuotientGroup.mk (Subgroup.inclusion hXK n.1))) = 1 := h1
      have h3 := e.injective (h2.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff _).1 h3
    let ν : X₀.ker →* Subgroup.center (↥K ⧸ P) :=
      ((QuotientGroup.mk' P).comp ((Subgroup.inclusion hXK).comp X₀.ker.subtype)).codRestrict _ hmem
    have hmemP : ∀ n : ν.ker, (Subgroup.inclusion hXK n.1.1 : ↥K) ∈ P := by
      intro n
      have h1 : ν n.1 = 1 := n.2
      have h2 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).1 h2
    let κ : ν.ker →* ↥P :=
      ((Subgroup.inclusion hXK).comp (X₀.ker.subtype.comp ν.ker.subtype)).codRestrict P hmemP
    have hκ : Function.Injective κ := by
      intro a b hab
      have h := congrArg (fun z : ↥P => ((z : ↥K) : H)) hab
      apply Subtype.ext
      apply Subtype.ext
      exact Subtype.ext h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ν.ker := IsPGroup.of_injective (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) κ hκ
    have : Group.IsNilpotent ν.ker := hp.isNilpotent
    have : Group.IsSolvable ν.ker := inferInstance
    have : Group.IsSolvable (Subgroup.center (↥K ⧸ P)) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a)
    exact Group.isSolvable_of_ker_le_range ν.ker.subtype ν (by simp)
  have hS' := exists_of_solvable_ker X₀ hker hS
  have hnorm : ∀ y ∈ X₀.range, MulAut.conj y ∈ Subgroup.normalizer (lamR.range : Set (MulAut G)) := by
    rintro _ ⟨x, rfl⟩
    have hxK : (x : H) ∈ K := hXK x.2
    have hxN : (x : H) ∈ Subgroup.normalizer (K : Set H) := Subgroup.le_normalizer hxK
    have hconj : MulAut.conj (X₀ x) = lam K G e ⟨(x : H), hxN⟩ :=
      (lam_of_mem K G e ⟨(x : H), hxK⟩).symm
    have key : ∀ (x' : H) (hx' : x' ∈ X) (hxN' : x' ∈ Subgroup.normalizer (K : Set H)),
        ∀ z ∈ lamR.range, lam K G e ⟨x', hxN'⟩ * z * (lam K G e ⟨x', hxN'⟩)⁻¹ ∈ lamR.range := by
      rintro x' hx' hxN' _ ⟨r, rfl⟩
      have hr' : x' * (r : H) * x'⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (hXN hx') r).1 r.2
      refine ⟨⟨x' * (r : H) * x'⁻¹, hr'⟩, ?_⟩
      change lam K G e (Subgroup.inclusion hRN ⟨x' * (r : H) * x'⁻¹, hr'⟩) =
        lam K G e ⟨x', hxN'⟩ * lam K G e (Subgroup.inclusion hRN r) * (lam K G e ⟨x', hxN'⟩)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [hconj, Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => key _ x.2 hxN z hz, fun hz => ?_⟩
    have hxinvN : (x : H)⁻¹ ∈ Subgroup.normalizer (K : Set H) := Subgroup.inv_mem _ hxN
    have := key ((x : H)⁻¹) (Subgroup.inv_mem _ x.2) hxinvN _ hz
    have e1 : (lam K G e ⟨(x : H)⁻¹, hxinvN⟩) = (lam K G e ⟨(x : H), hxN⟩)⁻¹ := by
      rw [← map_inv]; congr 1
    rw [e1] at this
    simpa [mul_assoc] using this
  have hbot := hA lamR.range X₀.range hR'p hS' hnorm
  rw [Subgroup.commutator_le]
  intro r hr k hk
  have hlam : lam K G e (Subgroup.inclusion hRN ⟨r, hr⟩) = 1 := by
    have : lamR ⟨r, hr⟩ ∈ lamR.range := ⟨_, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have := comm_mem_pCoreOf_of_lam_eq_one K G e hperf (Subgroup.inclusion hRN ⟨r, hr⟩) hlam ⟨k, hk⟩
  simpa [commutatorElement_def] using this

theorem ks1523ONCent_of_onAutFact
    (hA : CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut.ONAutFact) :
    CFSG.RankThree.PartTwo.Sec15.KS1523ONCent := by
  intro H _ _ K X R hq hT hXK hS hR hRN hXN
  obtain ⟨-, ⟨e⟩⟩ := hT
  have hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
  exact reduction_core (G := ON) (by
      unfold CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut.ONAutFact at hA
      with_reducible_and_instances exact hA) K X R hperf
    (by with_reducible_and_instances exact e) hXK hS hR hRN hXN

theorem ks1523ONCent_of_inputs
    (hI1 : ∀ E : Subgroup ON, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8)
    (hI3 : ∀ τ : MulAut ON, τ ^ 2 = 1 → (¬ ∃ g : ON, τ = MulAut.conj g) →
      ∀ E : Subgroup ON, Nat.card E = 9 → (∀ g ∈ E, τ g = g) → False) :
    CFSG.RankThree.PartTwo.Sec15.KS1523ONCent :=
  ks1523ONCent_of_onAutFact (onAutFact_of_inputs hI1 hI3)

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON
