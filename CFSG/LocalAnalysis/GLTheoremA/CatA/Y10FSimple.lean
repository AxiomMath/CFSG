module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FU64
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F1441
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FNeg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  glaPComponent_map_fixSubgroup)

theorem center_centerQuot_eq_bot {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := by
  obtain ⟨hperf, hsimple⟩ := hK
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hsimple
  haveI : Group.IsPerfect K := ⟨hperf⟩
  haveI : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (K ⧸ Subgroup.center K))
    with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : K ⧸ Subgroup.center K, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
    have hbot : commutator (K ⧸ Subgroup.center K) = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_def]
      have := hcomm a b
      calc a * b * a⁻¹ * b⁻¹ = b * a * a⁻¹ * b⁻¹ := by rw [this]
        _ = 1 := by group
    have htop : commutator (K ⧸ Subgroup.center K) = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [hbot] at htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ Subgroup.center K)
    apply hab
    have h1 : a ∈ (⊥ : Subgroup (K ⧸ Subgroup.center K)) := htop ▸ Subgroup.mem_top a
    have h2 : b ∈ (⊥ : Subgroup (K ⧸ Subgroup.center K)) := htop ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot.1 h1, Subgroup.mem_bot.1 h2]

theorem hasLabel_centerQuot {K : Type} [Group K] {S : GLALabel → Prop} (h : HasLabel K S) :
    HasLabel (K ⧸ Subgroup.center K) S := by
  have hq := hasLabel_isQuasisimple h
  have hbot := center_centerQuot_eq_bot hq
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  haveI : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)
  refine hasLabel_of_equiv_centerQuot (X := K) Group.IsPerfect.commutator_eq_top ?_ h
  exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm

@[expose] noncomputable def centerQuotAut (K : Type) [Group K] : MulAut K →* MulAut (K ⧸ Subgroup.center K) :=
  CFSG.LocalAnalysis.GLTheoremB.quotAutHom (Subgroup.center K) (MonoidHom.id (MulAut K))
    (fun σ => Subgroup.map_center_eq σ)

theorem centerQuotAut_mk (K : Type) [Group K] (σ : MulAut K) (k : K) :
    centerQuotAut K σ (QuotientGroup.mk k) = QuotientGroup.mk (σ k) :=
  CFSG.LocalAnalysis.GLTheoremB.quotAutHom_mk _ _ _ σ k

theorem simple_transfer {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (α : MulAut K)
    {J : Subgroup K} {S T : GLALabel → Prop} (hα : α ^ p = 1) (hK : HasLabel K S)
    (hJ : GLAPComponent p (fixSubgroup α) J) (hJl : HasLabel ↥J T) :
    ∃ (β : MulAut (K ⧸ Subgroup.center K)) (Jb : Subgroup (K ⧸ Subgroup.center K)),
      β ^ p = 1 ∧ GLAPComponent p (fixSubgroup β) Jb ∧ HasLabel ↥Jb T := by
  have hq := hasLabel_isQuasisimple hK
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  refine ⟨centerQuotAut K α, J.map π, by rw [← map_pow, hα, map_one], ?_, ?_⟩
  · refine glaPComponent_map_fixSubgroup π (by rw [QuotientGroup.ker_mk']) α (centerQuotAut K α)
      (fun k => (centerQuotAut_mk K α k).symm) (QuotientGroup.mk'_surjective _) hp hJ
  · have hqJ : CFSG.Open.IsQuasisimple ↥J := hasLabel_isQuasisimple hJl
    let φ : ↥J →* ↥(J.map π) :=
      (π.comp J.subtype).codRestrict _ (fun j => Subgroup.mem_map_of_mem π j.2)
    have hφsurj : Function.Surjective φ := by
      rintro ⟨_, ⟨j, hj, rfl⟩⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    haveI hperf : Group.IsPerfect ↥J := ⟨hqJ.1⟩
    have hker : φ.ker ≤ Subgroup.center ↥J := by
      intro j hj
      have hj1 : π (j : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hj)
      have hjZ : (j : K) ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).1 hj1
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hjZ (g : K)
    obtain ⟨e⟩ := quotEquiv_of_perfect_central φ hφsurj hperf hker
    exact hasLabel_of_equiv_centerQuot
      ((Group.IsPerfect.ofSurjective (f := φ) hφsurj).commutator_eq_top) e hJl

@[expose] def I14NegFactS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
    HasLabel ↥J (fun l : GLALabel => l = labJ) → α ^ p = 1 →
    GLAPComponent p (fixSubgroup α) J → I14Neg p labK labJ

@[expose] def I1441FactS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
    HasLabel ↥J (fun l : GLALabel => l = labJ) → α ^ p = 1 →
    GLAPComponent p (fixSubgroup α) J → FieldRel p (canonLabel labK) (canonLabel labJ)

theorem i14NegFact_of_simple (h : I14NegFactS) : I14NegFact := by
  intro K _ _ p α J labK labJ hp hp2 hlK hlJ hα hJ
  obtain ⟨β, Jb, hβ, hJb, hlb⟩ := simple_transfer hp α hα hlK hJ hlJ
  exact h (K ⧸ Subgroup.center K) p β Jb labK labJ hp hp2
    (center_centerQuot_eq_bot (hasLabel_isQuasisimple hlK)) (hasLabel_centerQuot hlK) hlb hβ hJb

theorem i1441Fact_of_simple (h : I1441FactS) : I1441Fact := by
  intro K _ _ p α J labK labJ hp hp2 hlK hlJ hα hJ
  obtain ⟨β, Jb, hβ, hJb, hlb⟩ := simple_transfer hp α hα hlK hJ hlJ
  exact h (K ⧸ Subgroup.center K) p β Jb labK labJ hp hp2
    (center_centerQuot_eq_bot (hasLabel_isQuasisimple hlK)) (hasLabel_centerQuot hlK) hlb hβ hJb


@[expose] def U64FactS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (lab : GLALabel), Subgroup.center S = ⊥ →
    HasLabel S (fun l : GLALabel => l = lab) →
    ((lab.tag = .A ∧ 4 ∣ lab.n ∧ 5 ∣ lab.rank + 1) ∨
      (lab.tag = .twA ∧ lab.n % 4 = 2 ∧ 5 ∣ lab.rank + 1)) →
    ∀ β : MulAut S, β ^ 3 = 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J →
      HasLabel ↥J (fun l : GLALabel => l = ⟨.twA, 4, 2⟩) →
      lab = ⟨.twA, 4, 2⟩ ∨ lab = ⟨.twA, 4, 6⟩ ∨ ∃ r : ℕ, 1 < r ∧ lab = ⟨.twA, 5 * r - 1, 2⟩

theorem u64Fact_of_simple (h : U64FactS) : U64Fact := by
  intro K _ _ lab hl hfam _ β hβ J hJ hJl
  obtain ⟨β', Jb, hβ', hJb, hlb⟩ := simple_transfer Nat.prime_three β hβ hl hJ hJl
  exact h (K ⧸ Subgroup.center K) lab (center_centerQuot_eq_bot (hasLabel_isQuasisimple hl))
    (hasLabel_centerQuot hl) hfam β' hβ' Jb hJb hlb

variable {G : Type} [Group G] [Finite G]

theorem i14NegAt_of_facts (h : I14NegFactS) : I14NegAt G :=
  i14NegAt_of_fact (i14NegFact_of_simple h)

theorem i1441At_of_facts (h : I1441FactS) : I1441At G :=
  i1441At_of_fact (i1441Fact_of_simple h)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
