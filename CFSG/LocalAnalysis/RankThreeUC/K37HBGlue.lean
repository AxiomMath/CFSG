module

public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Split
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Proving

variable {X : Type} [Group X] [Finite X]

private theorem exists_isSCp_above' {p : ℕ} {Y : Subgroup X} (hY : IsElemAbelian p Y) :
    ∃ H : Subgroup X, IsSCp p ⊤ H ∧ Y ≤ H := by
  obtain ⟨H, hH, hmax⟩ := Set.exists_max_image
    {H : Subgroup X | Y ≤ H ∧ IsElemAbelian p H} (fun H => Nat.card H)
    (Set.toFinite _) ⟨Y, le_rfl, hY⟩
  refine ⟨H, ⟨le_top, hH.2, fun E _ hEab hHE => ?_⟩, hH.1⟩
  have hE : E ∈ {H : Subgroup X | Y ≤ H ∧ IsElemAbelian p H} := ⟨hH.1.trans hHE, hEab⟩
  exact (Subgroup.eq_of_le_of_card_ge hHE (hmax E hE)).symm

private theorem le_pRank_of_card' {p k : ℕ} (hp : 1 < p) {H E : Subgroup X} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card X, fun m ⟨F, _, _, hF⟩ => ?_⟩ ⟨E, hEH, hE, hk⟩
  have h1 : p ^ m ≤ Nat.card X := hF ▸ Subgroup.card_le_card_group F
  exact (Nat.lt_pow_self hp).le.trans h1

private theorem le_normalizer_of_abelian {p : ℕ} {B E : Subgroup X} (hB : IsElemAbelian p B)
    (hEB : E ≤ B) : B ≤ Subgroup.normalizer (E : Set X) := by
  intro b hb
  haveI := hB.1
  refine Subgroup.centralizer_le_normalizer (E : Set X)
    (Subgroup.mem_centralizer_iff.2 fun e he => ?_)
  have h : (⟨e, hEB he⟩ : B) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨e, hEB he⟩ := mul_comm' _ _
  exact congrArg Subtype.val h

theorem k37b_exists_scp {K E S : Subgroup X} (h : K37Setting X K E S) :
    ∃ B : Subgroup X, IsSCp 3 ⊤ B ∧ E ≤ B ∧ B ≤ Subgroup.normalizer (S : Set X) := by
  obtain ⟨B, hB, hEB⟩ := exists_isSCp_above' h.elem
  refine ⟨B, hB, hEB, fun b hb => h.le_normalizer ?_⟩
  have hE1 : 1 ≤ CFSG.Open.pRank 3 E :=
    (le_pRank_of_card' (k := 2) (by norm_num) le_rfl h.elem (by rw [h.card]; norm_num)).trans'
      (by norm_num)
  exact normalizer_le_glbCore (k := 1) le_rfl hE1 (le_normalizer_of_abelian hB.2.1 hEB hb)

theorem k37b_inf_centralizer_eq_bot {K E S : Subgroup X} (h : K37Setting X K E S) :
    E ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  rintro f ⟨hfE, hfC⟩
  by_contra hf
  have hf1 : f ≠ 1 := fun h1 => hf (Subgroup.mem_bot.2 h1)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    haveI := h.elem.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  set Q := Subgroup.zpowers f with hQ
  have hQE : Q ≤ E := (Subgroup.zpowers_le).2 hfE
  have hQel : IsElemAbelian 3 Q :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 (hQE a.2) b.1 (hQE b.2))⟩⟩,
      fun x hx => h.elem.2 x (hQE hx)⟩
  have hcard : Nat.card Q = 3 ^ 1 := by
    rw [hQ, Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (h.elem.2 f hfE) hf1
  have hrank : 1 ≤ CFSG.Open.pRank 3 Q := le_pRank_of_card' (by norm_num) le_rfl hQel hcard
  refine h.not_le fun k hk => normalizer_le_glbCore hQE hrank ?_
  refine Subgroup.centralizer_le_normalizer (Q : Set X)
    (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hkf : Commute k f := Subgroup.mem_centralizer_iff.1 hfC k hk
  exact (hkf.symm.zpow_left n).eq

theorem k37b_card_le_autOrderIn {Y : Type} [Group Y] [Finite Y] {B K : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {A : Type} (f : A → Y) (hf : ∀ a, f a ∈ B)
    (hinj : ∀ a b, (f a)⁻¹ * f b ∈ Subgroup.centralizer (K : Set Y) → a = b) :
    Nat.card A ≤ autOrderIn B K := by
  have hB : B ⊓ Subgroup.normalizer (K : Set Y) = B := inf_of_le_left hBN
  have hinj' : Function.Injective fun a : A =>
      (QuotientGroup.mk (⟨f a, hf a⟩ : B) :
        B ⧸ (Subgroup.centralizer (K : Set Y)).subgroupOf B) := by
    intro a b hab
    exact hinj a b (Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hab))
  have h4 := Nat.card_le_card_of_injective _ hinj'
  unfold autOrderIn
  rw [hB]
  exact h4

theorem k37b_coprime_card {K E S : Subgroup X} (h : K37Setting X K E S) :
    Nat.Coprime 3 (Nat.card S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h.two.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem k37b_isKGroup {K E S : Subgroup X} (h : K37Setting X K E S) : CFSG.Open.IsKGroup X :=
  CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.1 h.catalog

theorem k37b_isQuasisimple {K E S : Subgroup X} (h : K37Setting X K E S) :
    CFSG.Open.IsQuasisimple ↥K :=
  ⟨h.quasi.1.commutator_eq_top, h.quasi.2.1⟩

theorem k37b_isComponentOf_top {K E S : Subgroup X} (h : K37Setting X K E S) :
    IsComponentOf K ⊤ :=
  haveI := h.normal
  ⟨le_top, IsSubnormal.step le_top (Subgroup.Normal.subgroupOf h.normal ⊤) (IsSubnormal.refl ⊤),
    k37b_isQuasisimple h⟩

theorem k37b_le_normalizer {K E S : Subgroup X} (h : K37Setting X K E S) (B : Subgroup X) :
    B ≤ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.normalizer_eq_top_iff.2 h.normal]
  exact le_top

theorem k37b_centralizes {K E S : Subgroup X} (h : K37Setting X K E S) {B : Subgroup X}
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (hB : IsStronglyBalancedIn 3 B K) :
    S ≤ Subgroup.centralizer (K : Set X) :=
  hB S (k37b_le_normalizer h S) (k37b_coprime_card h) (inf_le_left.trans hBS)

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
