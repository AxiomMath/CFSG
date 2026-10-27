module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CanonicalBFixedHyperplane
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CyclicActor

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

private theorem pRank_le_one_of_cyclic {p : ℕ} (hp : p.Prime) (P : Subgroup G)
    (hP : IsCyclic P) : CFSG.Open.pRank p P ≤ 1 := by
  classical
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨E, hEP, ⟨-, hexp⟩, hcard⟩
  have hEc : IsCyclic (E.subgroupOf P) := Subgroup.isCyclic _
  have hcardE : Nat.card (E.subgroupOf P) = p ^ k := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
  haveI : Fintype (E.subgroupOf P) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := E.subgroupOf P) (n := p) hp.pos
  have hall : (Finset.univ.filter fun x : E.subgroupOf P => x ^ p = 1) = Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    apply Subtype.ext
    apply Subtype.ext
    simpa using hexp (x : G) (Subgroup.mem_subgroupOf.1 x.2)
  rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, hcardE] at hle
  by_contra hk
  have h2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
  have h3 : p ^ 2 ≤ p := le_trans h2 hle
  have := hp.two_le
  nlinarith

theorem exists_rep {B Q : Type*} [Group B] [CommGroup Q] (p : ℕ) [Fact p.Prime]
    [Module (ZMod p) (Additive Q)] (f : B →* Monoid.End Q) :
    ∃ σ : Representation (ZMod p) B (Additive Q), ∀ b x, σ b (Additive.ofMul x) =
      Additive.ofMul (f b x) := by
  refine ⟨{ toFun := fun b => AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive (f b))
            map_one' := ?_
            map_mul' := ?_ }, fun b x => rfl⟩
  · refine LinearMap.ext fun x => ?_
    induction x using Additive.rec with | _ x => ?_
    simp
    rfl
  · intro b c
    refine LinearMap.ext fun x => ?_
    induction x using Additive.rec with | _ x => ?_
    simp
    rfl

theorem cyclic {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) : IsCyclic B := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  have hel := isElemAbelian_of_binary_rank_counterexample hc
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : P)
    rw [hS.exponent] at this
    exact congrArg Subtype.val this
  have hcop : (Nat.card B).Coprime p := by
    have h19 := (three_lt_pRank_and_prime_not_dvd_card_actor hc).2
    by_contra h
    apply h19
    refine ⟨hS.prime, ?_⟩
    by_contra hd
    exact h ((Nat.Prime.coprime_iff_not_dvd hS.prime).2 hd).symm
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := hS.normB
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative B := hS.abelian
  obtain ⟨-, ⟨-, huni⟩, -⟩ := CanonicalBFixedHyperplane.canonical hc
  by_cases hB1 : B = ⊥
  · subst hB1; infer_instance
  obtain ⟨b0, hb0, hb01⟩ : ∃ b ∈ B, b ≠ 1 := by
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    exact ⟨b, b.2, fun h => hb (Subtype.ext h)⟩
  set N : Subgroup G := P ⊓ Subgroup.centralizer (B : Set G) with hN
  have hNP : N ≤ P := inf_le_left
  have hNc : ∀ x ∈ N, ∀ b ∈ B, b * x = x * b := fun x hx b hb =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 b hb
  set N' : Subgroup P := N.subgroupOf P with hN'
  haveI hNn : N'.Normal := ⟨fun n hn g => by
    have : (g : P) * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm g g.2 n n.2]; group
    rw [this]; exact hn⟩
  letI : CommGroup (P ⧸ N') :=
    { (inferInstance : Group (P ⧸ N')) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | _ x => ?_
        induction b using QuotientGroup.induction_on with | _ y => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subtype.ext (hcomm x x.2 y y.2)) }
  letI hMod : Module (ZMod p) (Additive (P ⧸ N')) :=
    AddCommGroup.zmodModule (n := p) fun x => by
      induction x using Additive.rec with | _ x => ?_
      induction x using QuotientGroup.induction_on with | _ g => ?_
      show Additive.ofMul ((QuotientGroup.mk g) ^ p) = 0
      rw [← QuotientGroup.mk_pow]
      have : g ^ p = 1 := Subtype.ext (hexp g g.2)
      rw [this]; rfl
  have hN'conj : ∀ b : B, ∀ x : P, x ∈ N' →
      Quotient.conjAut hBP b x ∈ N' := by
    intro b x hx
    have hx' : (x : G) ∈ N := hx
    show ((Quotient.conjAut hBP b x : P) : G) ∈ N
    rw [Quotient.conjAut_apply, hNc x hx' b b.2]
    simpa using hx'
  let fm : B → (P ⧸ N') →* (P ⧸ N') := fun b =>
    QuotientGroup.map N' N' (Quotient.conjAut hBP b).toMonoidHom (fun x hx => hN'conj b x hx)
  have fm_mk : ∀ b x, fm b (QuotientGroup.mk x) = QuotientGroup.mk (Quotient.conjAut hBP b x) :=
    fun b x => rfl
  let fE : B →* Monoid.End (P ⧸ N') :=
    { toFun := fm
      map_one' := by
        refine MonoidHom.ext fun x => ?_
        induction x using QuotientGroup.induction_on with | _ x => ?_
        refine (fm_mk 1 x).trans ?_
        refine congrArg (QuotientGroup.mk (s := N')) ?_
        apply Subtype.ext
        simp [Quotient.conjAut_apply]
      map_mul' := by
        intro b c
        refine MonoidHom.ext fun x => ?_
        induction x using QuotientGroup.induction_on with | _ x => ?_
        refine (fm_mk (b * c) x).trans ?_
        refine Eq.trans ?_ (congrArg (fm b) (fm_mk c x)).symm
        refine Eq.trans ?_ (fm_mk b _).symm
        refine congrArg (QuotientGroup.mk (s := N')) ?_
        apply Subtype.ext
        simp [Quotient.conjAut_apply, mul_assoc] }
  obtain ⟨σ, hσ'⟩ := exists_rep p fE
  haveI hNT : Nontrivial (Additive (P ⧸ N')) := by
    haveI : Nontrivial (P ⧸ N') := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      have hPN : P ≤ N := by
        intro x hx
        have h1 : (QuotientGroup.mk (⟨x, hx⟩ : P) : P ⧸ N') = 1 := Subsingleton.elim _ _
        exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : P)).1 h1
      have hPeq : P = P ⊓ Subgroup.centralizer ({b0} : Set G) := by
        rw [huni b0 hb0 hb01]; exact le_antisymm hPN hNP
      have hcyc : IsCyclic P := by
        have := hc.oddPrimeClassTwoAction.cyclic_centralizer b0 hb0 hb01
        rw [← hPeq] at this
        exact this
      have := pRank_le_one_of_cyclic hp P hcyc
      have := hc.faithfulBinaryIrreducibleAction.rank_gt
      omega
    obtain ⟨a, a', haa⟩ := exists_pair_ne (P ⧸ N')
    exact ⟨⟨Additive.ofMul a, Additive.ofMul a', fun h => haa (Additive.ofMul.injective h)⟩⟩
  haveI : Finite (Additive (P ⧸ N')) := inferInstanceAs (Finite (P ⧸ N'))
  haveI hFD : FiniteDimensional (ZMod p) (Additive (P ⧸ N')) := Module.Finite.of_finite
  refine @CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic.isCyclic_of_fixedFree (ZMod p) _ B _ _ _ (Additive (P ⧸ N')) _ hMod hFD hNT σ ?_
  intro b hb1 v hv
  have hbB : (b : G) ∈ B := b.2
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hcop' : Nat.Coprime (orderOf (b : G)) p := by
    refine Nat.Coprime.coprime_dvd_left ?_ hcop
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard _
  induction v using Additive.rec with | _ v => ?_
  induction v using QuotientGroup.induction_on with | _ x => ?_
  obtain ⟨g, hg⟩ := x
  have hv' : fE b (QuotientGroup.mk ⟨g, hg⟩) = QuotientGroup.mk ⟨g, hg⟩ :=
    Additive.ofMul.injective ((hσ' b _).symm.trans hv)
  rw [show fE b (QuotientGroup.mk ⟨g, hg⟩) = QuotientGroup.mk (Quotient.conjAut hBP b ⟨g, hg⟩)
    from fm_mk b _, QuotientGroup.eq_iff_div_mem] at hv'
  have hcN : (b : G) * g * (b : G)⁻¹ * g⁻¹ ∈ N := by
    have : (Quotient.conjAut hBP b ⟨g, hg⟩ / ⟨g, hg⟩ : P) =
        ⟨(b : G) * g * (b : G)⁻¹ * g⁻¹, by
          exact P.mul_mem (((Subgroup.mem_normalizer_iff.mp (hBP b.2)) g).mp hg) (P.inv_mem hg)⟩ :=
      Subtype.ext (by simp [Quotient.conjAut_apply, div_eq_mul_inv])
    rw [this] at hv'
    exact hv'
  have h1 := ProofSupport.CoprimeFixedCentralCoset.commutator_eq_one hp N
    (fun x hx => hexp x (hNP hx)) b g (fun x hx => hNc x hx b hbB) hcN hcop'
  have hgN : g ∈ N := by
    have hgc : g ∈ P ⊓ Subgroup.centralizer ({(b : G)} : Set G) := by
      refine ⟨hg, ?_⟩
      show g ∈ Subgroup.centralizer ({(b : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc _ = ((b : G) * g * (b : G)⁻¹ * g⁻¹) * g * b := by group
        _ = g * b := by rw [h1]; group
    rw [huni (b : G) hbB hb1'] at hgc
    exact hgc
  have : (QuotientGroup.mk (⟨g, hg⟩ : P) : P ⧸ N') = 1 :=
    (QuotientGroup.eq_one_iff _).2 hgN
  rw [this]
  rfl

end CFSG.LocalAnalysis.RankThreeUC.Section5.CyclicActor
