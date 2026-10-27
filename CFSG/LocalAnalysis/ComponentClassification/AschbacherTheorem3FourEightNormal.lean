module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightCTrick
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightGroup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTorusConj

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped MatrixGroups Pointwise

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

omit [Finite X] in
theorem normalizer_le_normalizer_centralizer (Y : Subgroup X) :
    Subgroup.normalizer (Y : Set X) ≤
      Subgroup.normalizer (Subgroup.centralizer (Y : Set X) : Set X) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have key : ∀ x' ∈ Subgroup.normalizer (Y : Set X), ∀ c', c' ∈ Subgroup.centralizer (Y : Set X) →
      x' * c' * x'⁻¹ ∈ Subgroup.centralizer (Y : Set X) := by
    intro x' hx' c' hc'
    rw [Subgroup.mem_centralizer_iff] at hc' ⊢
    intro w hw
    have hw' : x'⁻¹ * w * x' ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx') w).mp hw
      simpa using this
    have h1 := hc' _ hw'
    calc w * (x' * c' * x'⁻¹) = x' * ((x'⁻¹ * w * x') * c') * x'⁻¹ := by group
      _ = x' * (c' * (x'⁻¹ * w * x')) * x'⁻¹ := by rw [h1]
      _ = x' * c' * x'⁻¹ * w := by group
  constructor
  · exact key x hx c
  · intro hc
    have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hc
    simpa [mul_assoc] using this

namespace ElemCtx

theorem mem_M_of_comm (c : ElemCtx G T S Q H g y) {s t : X} (hs : s ∈ S) (ht : t ∈ T)
    (ht1 : t ≠ 1) (hst : s * t = t * s) : s ∈ T ⊔ rightConjugate T g := by
  have e := c.elem
  obtain ⟨t', ht', k, hk, rfl⟩ := c.frame.mem_sup_iff.mp (c.sylowFrame.sylow.le hs)
  have hkS : k ∈ S := by simpa using S.mul_mem (S.inv_mem (c.sylowFrame.le ht')) hs
  have hcomm : k * t = t * k := by
    have htt' : t' * t = t * t' := M_comm' e (Subgroup.mem_sup_left ht') (Subgroup.mem_sup_left ht)
    have h1 : t' * (k * t) = t' * (t * k) := by
      calc t' * (k * t) = t' * k * t := by group
        _ = t * (t' * k) := hst
        _ = t' * (t * k) := by rw [← mul_assoc, ← htt', mul_assoc]
    exact mul_left_cancel h1
  have hkZ : k ∈ (T ⊔ rightConjugate T g) ⊓ G := by
    rw [← inf_centralizer_eq_Z e ht ht1]
    exact ⟨⟨hkS, hk⟩, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht') hkZ.1

theorem inv_mul_mem_Z_of_conj_eq (c : ElemCtx G T S Q H g y) {r r' : X}
    (hr : r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G)
    (hr' : r' ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G)
    (heq : rightConjugate T r = rightConjugate T r') :
    r⁻¹ * r' ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have e := c.elem
  have hWS : rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ≤ S := e.A_le_S
  have hN : r' * r⁻¹ ∈ Subgroup.normalizer (T : Set X) := by
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← heq, rightConjugate_mul,
      mul_inv_cancel, rightConjugate_one]
  have hmem : r' * r⁻¹ ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G :=
    Subgroup.mul_mem _ hr' (Subgroup.inv_mem _ hr)
  have hM : r' * r⁻¹ ∈ T ⊔ rightConjugate T g := by
    rw [← e.inf_eq, e.hyp45.inf_eq_normalizer]
    exact ⟨hWS hmem.1, hN⟩
  have hZ : r' * r⁻¹ ∈ (T ⊔ rightConjugate T g) ⊓ G := ⟨hM, hmem.2⟩
  have hcomm := e.Z_comm hZ hr.1
  have h1 : r⁻¹ * r' = r' * r⁻¹ := by
    calc r⁻¹ * r' = r⁻¹ * ((r' * r⁻¹) * r) := by group
      _ = r⁻¹ * (r * (r' * r⁻¹)) := by rw [hcomm]
      _ = r' * r⁻¹ := by group
  rw [h1]
  exact hZ

theorem card_quotient_R (c : ElemCtx G T S Q H g y) :
    Nat.card (↥((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) ⧸
      ((T ⊔ rightConjugate T g) ⊓ G).subgroupOf
        ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G)) = Nat.card T := by
  have e := c.elem
  rw [← Subgroup.index_eq_card]
  have h1 := Subgroup.relIndex_mul_card ((T ⊔ rightConjugate T g) ⊓ G)
    ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G)
  rw [inf_eq_left.mpr (inf_le_inf_right G le_sup_right), card_R e, e.card_Z] at h1
  have hpos : 0 < Nat.card T := Nat.card_pos
  rw [Subgroup.relIndex] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem not_psl_of_normal (c : ElemCtx G T S Q H g y) {G₁ : Subgroup X} (hG₁ : G₁ ≤ G)
    (hn : G ⊔ T ≤ Subgroup.normalizer (G₁ : Set X))
    (hpsl : ∃ n : ℕ, 2 ≤ n ∧ oTwoPrime (G₁ ⊔ T) = pCoreOf 2 (G₁ ⊔ T) ⊔ ⁅T, G₁⁆ ∧
      pCoreOf 2 (G₁ ⊔ T) ⊓ ⁅T, G₁⁆ = ⊥ ∧ ⁅pCoreOf 2 (G₁ ⊔ T), ⁅T, G₁⁆⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (G₁ ⊔ T)) ∧ Nat.card (pCoreOf 2 (G₁ ⊔ T)) = 2 ^ n ∧
      Nonempty ((⁅T, G₁⁆ : Subgroup X) ≃* PSL(2, GaloisField 2 n))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have h := c.sylowFrame
  have hF := h.toFrame
  have h₁ := h.restrict hG₁ hn
  have hab : IsMulCommutative (S ⊓ (G₁ ⊔ T) : Subgroup X) :=
    isMulCommutative_of_psl_case h₁.toFrame h₁.sylow hpsl
  obtain ⟨n, hn2, h2, hinf, hcomm, -, hcard, ⟨φ⟩⟩ := hpsl
  set S₁ := S ⊓ (G₁ ⊔ T) with hS₁
  set E := pCoreOf 2 (G₁ ⊔ T) with hE
  set L := ⁅T, G₁⁆ with hL
  have hLG₁ : L ≤ G₁ := by rw [hL, Subgroup.commutator_comm]; exact h₁.toFrame.commutator_le
  have hLG : L ≤ G := hLG₁.trans hG₁
  have hLN : G₁ ⊔ T ≤ Subgroup.normalizer (L : Set X) := sup_le_normalizer_commutator h₁.toFrame
  have hES₁ : E ≤ S₁ := pCoreOf_le_of_isSylowOf h₁.sylow
  have hEGT : E ≤ G₁ ⊔ T := LieType.BorelTits.pCoreOf_le 2 _
  have hEN : G₁ ⊔ T ≤ Subgroup.normalizer (E : Set X) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hP₁ : IsSylowOf 2 (S₁ ⊓ L) L :=
    h₁.sylow.inf_of_le_normalizer (hLG₁.trans le_sup_left) hLN
  set P₁ := S₁ ⊓ L with hP₁def
  obtain ⟨-, hP₁card, D, hDL, hDN, hDcard, hfree⟩ := exists_torus hn2 φ hP₁
  have hPL : P₁ ≤ L := inf_le_right
  have hECL : E ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hEC : E ≤ Subgroup.centralizer (P₁ : Set X) :=
    hECL.trans (Subgroup.centralizer_le hPL)
  have hDE : D ≤ Subgroup.centralizer (E : Set X) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hECL hx) d (hDL hd)).symm
  have hEP : E ⊓ P₁ = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_left E hPL
  have hEPS : E ⊔ P₁ ≤ S := sup_le (hES₁.trans inf_le_left) (inf_le_left.trans inf_le_left)
  have hTM' : T ≤ E ⊔ P₁ := by
    intro t ht
    have htO : t ∈ oTwoPrime (G₁ ⊔ T) := by
      apply Subgroup.subset_closure
      exact ⟨Subgroup.mem_sup_right ht, 1, by simpa using e.sq_T t ht⟩
    rw [h2] at htO
    have hm : t ∈ (E : Set X) * (L : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right E L (hEGT.trans hLN)]
      exact htO
    obtain ⟨a, ha, l, hl, rfl⟩ := Set.mem_mul.mp hm
    have hlS₁ : l ∈ S₁ := by
      have := S₁.mul_mem (S₁.inv_mem (hES₁ ha)) (le_inf h.le le_sup_right ht)
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hlS₁, hl⟩)
  have hTL : T ⊓ L = ⊥ := by
    rw [eq_bot_iff, ← hF.inf_eq_bot]
    exact inf_le_inf_left T hLG
  have hpow : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hD : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    omega
  have hTE : ¬ T ≤ E := by
    intro hTE
    have hLE : L ≤ E := by
      rw [hL, Subgroup.commutator_le]
      intro t ht x hx
      have h1 : x * t⁻¹ * x⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp (hEN (Subgroup.mem_sup_left hx)) _).mp
          (E.inv_mem (hTE ht))
      have h2 : t * (x * t⁻¹ * x⁻¹) ∈ E := E.mul_mem (hTE ht) h1
      simpa [commutatorElement_def, mul_assoc] using h2
    have hbot : P₁ = ⊥ := by
      rw [eq_bot_iff, ← hEP]
      exact le_inf (hPL.trans hLE) le_rfl
    rw [hbot, Subgroup.card_bot] at hP₁card
    omega
  have hTab : IsMulCommutative T := e.elem.1
  have hTE' : T ⊓ E = ⊥ := inf_eq_bot_of_torus h c.hyp43 hTab hEPS hTM' hEC hPL hLG hTL hDL hDE
    hDN hD hfree hTE
  have hcardEP : Nat.card (E ⊔ P₁ : Subgroup X) = 2 ^ n * 2 ^ n := by
    rw [card_sup_of_le_normalizer (hPL.trans (hLG₁.trans (le_sup_left.trans hEN))) hEP, hcard,
      hP₁card]
  have hcardET : Nat.card (E ⊔ T : Subgroup X) = 2 ^ n * Nat.card T := by
    rw [card_sup_of_le_normalizer (le_sup_right.trans hEN) (by rw [inf_comm]; exact hTE'), hcard]
  have hTle : Nat.card T ≤ 2 ^ n := by
    have h1 := Subgroup.card_le_of_le (sup_le (le_sup_left : E ≤ E ⊔ P₁) hTM')
    rw [hcardET, hcardEP] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  obtain ⟨t₀, ht₀, ht₀1⟩ := c.exists_ne_one
  have hS₁M : S₁ ≤ T ⊔ rightConjugate T g := by
    intro s hs
    have := hab.is_comm.comm ⟨s, hs⟩ ⟨t₀, le_inf h.le le_sup_right ht₀⟩
    exact c.mem_M_of_comm hs.1 ht₀ ht₀1 (congrArg Subtype.val this)
  have hEPM : E ⊔ P₁ ≤ T ⊔ rightConjugate T g :=
    (sup_le hES₁ inf_le_left).trans hS₁M
  have hcardM : Nat.card (T ⊔ rightConjugate T g : Subgroup X) = Nat.card T * Nat.card T :=
    e.hyp45.card_W
  have hge : 2 ^ n ≤ Nat.card T := by
    have h1 := Subgroup.card_le_of_le hEPM
    rw [hcardEP, hcardM] at h1
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul'' hlt hlt
    omega
  have hqn : Nat.card T = 2 ^ n := le_antisymm hTle hge
  have hEPM' : E ⊔ P₁ = T ⊔ rightConjugate T g :=
    Subgroup.eq_of_le_of_card_ge hEPM (by rw [hcardM, hcardEP, hqn])
  have hcardTE : Nat.card E ≤ Nat.card T := by rw [hcard, hqn]
  have hcardD : Nat.card P₁ - 1 ≤ Nat.card D := by rw [hP₁card, hDcard]
  have hTne : T ≠ ⊥ := by
    intro hbot
    rw [hbot] at ht₀
    exact ht₀1 ((Subgroup.mem_bot).mp ht₀)
  set R := (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G with hRdef
  have hex : ∀ r : R, ∃ d : D, rightConjugate T r = rightConjugate T d := by
    intro r
    have hrW : (r : X) ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := r.2.1
    have hrG : (r : X) ∈ G := r.2.2
    have hrM : rightConjugate T r ≤ E ⊔ P₁ := by
      rw [hEPM']
      have h1 := rightConjugate_le_rightConjugate (le_sup_left : T ≤ T ⊔ rightConjugate T g) r
      rwa [(rightConjugate_eq_self_iff _ _).mpr (W_le_normalizer_M e hrW)] at h1
    have hrN : (r : X) ∈ Subgroup.normalizer ((G₁ ⊔ T : Subgroup X) : Set X) := by
      rw [← rightConjugate_eq_self_iff]
      apply Subgroup.eq_of_le_of_card_ge _ (rightConjugate_card _ _).ge
      have hG₁r : rightConjugate G₁ r = G₁ :=
        (rightConjugate_eq_self_iff _ _).mpr (hn (Subgroup.mem_sup_left hrG))
      have hTr : rightConjugate T r ≤ G₁ ⊔ T := hrM.trans (sup_le hEGT
        ((hPL.trans hLG₁).trans le_sup_left))
      have hsup : rightConjugate (G₁ ⊔ T) r = rightConjugate G₁ r ⊔ rightConjugate T r :=
        Subgroup.map_sup _ _ _
      rw [hsup, hG₁r]
      exact sup_le le_sup_left hTr
    have hrE : rightConjugate E r = E :=
      (rightConjugate_eq_self_iff _ _).mpr
        (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hrN)
    have hrTE : rightConjugate T r ⊓ E = ⊥ := by
      rw [← hrE, ← rightConjugate_inf, hTE', rightConjugate_bot]
    obtain ⟨d, hd, hdeq⟩ := exists_eq_torus h c.hyp43 hTab hEPS hTM' hEP hEC hPL hLG hTE'
      hcardTE hDL hDE hDN hcardD hfree hTne hrG hrM hrTE
    exact ⟨⟨d, hd⟩, hdeq⟩
  choose f hf using hex
  set Z' := ((T ⊔ rightConjugate T g) ⊓ G).subgroupOf R with hZ'
  let F : R ⧸ Z' → D := fun q => f q.out
  have hF : Function.Injective F := by
    intro a b hab
    have h1 : rightConjugate T (a.out : X) = rightConjugate T (b.out : X) := by
      rw [hf, hf]
      simp only [F] at hab
      rw [hab]
    have h2 := c.inv_mul_mem_Z_of_conj_eq a.out.2 b.out.2 h1
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    exact Subgroup.mem_subgroupOf.mpr (by simpa using h2)
  have h1 := Nat.card_le_card_of_injective F hF
  rw [c.card_quotient_R, hDcard, hqn] at h1
  have : 0 < 2 ^ n := by positivity
  omega

theorem le_normalizer_of_normal (c : ElemCtx G T S Q H g y) {G₁ : Subgroup X} (hG₁ : G₁ ≤ G)
    (hn : G ⊔ T ≤ Subgroup.normalizer (G₁ : Set X)) (hne : G₁ ≠ G) :
    G₁ ≤ Subgroup.normalizer (relativeWeakClosure G₁ T (S ⊓ (G₁ ⊔ T)) : Set X) := by
  rcases conclusion_of_normal c.ih c.sylowFrame c.hyp43 c.index_le c.oddCore_eq_bot c.pRank_lt
      hG₁ hn hne with hN | hpsl
  · exact hN
  · exact (c.not_psl_of_normal hG₁ hn hpsl).elim

theorem le_centralizer_of_normal (c : ElemCtx G T S Q H g y) {Y : Subgroup X}
    (hYN : G ⊔ T ≤ Subgroup.normalizer (Y : Set X))
    (hTY : T ≤ Subgroup.centralizer (Y : Set X)) :
    G ≤ Subgroup.centralizer (Y : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := c.sylowFrame
  have hF := h.toFrame
  set G₁ := G ⊓ Subgroup.centralizer (Y : Set X) with hG₁def
  by_contra hne'
  have hne : G₁ ≠ G := fun h1 => hne' (by rw [← h1]; exact inf_le_right)
  have hG₁ : G₁ ≤ G := inf_le_left
  have hCN : G ⊔ T ≤ Subgroup.normalizer (Subgroup.centralizer (Y : Set X) : Set X) :=
    hYN.trans (normalizer_le_normalizer_centralizer Y)
  have hGN : G ⊔ T ≤ Subgroup.normalizer (G : Set X) :=
    sup_le Subgroup.le_normalizer hF.le_normalizer
  have hn : G ⊔ T ≤ Subgroup.normalizer (G₁ : Set X) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hGN hx, hCN hx⟩
  have hW₁ := c.le_normalizer_of_normal hG₁ hn hne
  set W₁ := relativeWeakClosure G₁ T (S ⊓ (G₁ ⊔ T)) with hW₁def
  have hTW₁ : T ≤ W₁ := subgroup_le_relative_weak_closure _ _ _ (le_inf h.le le_sup_right)
  have hW₁S : W₁ ≤ S ⊓ (G₁ ⊔ T) := relative_weak_closure_le _ _ _
  have hK : G₁ ⊔ T = (G ⊔ T) ⊓ Subgroup.centralizer (Y : Set X) := by
    apply le_antisymm
    · exact sup_le (le_inf (hG₁.trans le_sup_left) inf_le_right) (le_inf le_sup_right hTY)
    · rintro x ⟨hx, hxC⟩
      obtain ⟨t, ht, k, hk, rfl⟩ := hF.mem_sup_iff.mp hx
      have hkC : k ∈ Subgroup.centralizer (Y : Set X) := by
        simpa using (Subgroup.centralizer (Y : Set X)).mul_mem
          ((Subgroup.centralizer (Y : Set X)).inv_mem (hTY ht)) hxC
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left ⟨hk, hkC⟩)
  have hKN : G ⊔ T ≤ Subgroup.normalizer ((G₁ ⊔ T : Subgroup X) : Set X) := by
    rw [hK]
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, hCN hx⟩
  have hW₁N : G₁ ⊔ T ≤ Subgroup.normalizer (W₁ : Set X) :=
    sup_le hW₁ (hTW₁.trans Subgroup.le_normalizer)
  have hle := le_pCoreOf_of_normal (sup_le (hG₁.trans le_sup_left) le_sup_right) hKN
    (hW₁S.trans inf_le_right) hW₁N (h.sylow.isPGroup.to_le (hW₁S.trans inf_le_left))
  exact c.not_le_pCoreOf (hTW₁.trans hle)

theorem isSylowOf_P (c : ElemCtx G T S Q H g y) : IsSylowOf 2 (S ⊓ G) G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact c.sylowFrame.sylow.inf_of_le_normalizer le_sup_left
    (sup_le Subgroup.le_normalizer c.frame.le_normalizer)

theorem relIndex_R_P (c : ElemCtx G T S Q H g y) :
    ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G).relIndex (S ⊓ G) = 2 := by
  have e := c.elem
  have h1 := Subgroup.relIndex_mul_card ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G)
    (S ⊓ G)
  rw [inf_eq_left.mpr (inf_le_inf_right G e.A_le_S), card_R e, card_SG e] at h1
  have hpos : 0 < Nat.card T * Nat.card T := Nat.mul_pos Nat.card_pos Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem false_of_normal_relIndex (c : ElemCtx G T S Q H g y) {N : Subgroup X} (hNG : N ≤ G)
    (hNn : G ≤ Subgroup.normalizer (N : Set X)) (h2 : 2 ∣ N.relIndex G)
    (h4 : ¬ 4 ∣ N.relIndex G) : False :=
  false_of_relIndex_two_mul_odd c.frame.isPGroup c.frame.le_normalizer c.commutator_eq hNG hNn
    h2 h4

theorem not_le_normalizer_R (c : ElemCtx G T S Q H g y) :
    ¬ G ≤ Subgroup.normalizer
      (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hR
  have e := c.elem
  have hRP : (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G ≤ S ⊓ G :=
    inf_le_inf_right G e.A_le_S
  have hidx := Subgroup.relIndex_mul_relIndex _ _ _ hRP (inf_le_right : S ⊓ G ≤ G)
  rw [c.relIndex_R_P] at hidx
  obtain ⟨-, -, hodd⟩ := isSylowOf_iff.mp c.isSylowOf_P
  refine c.false_of_normal_relIndex inf_le_right hR ?_ ?_
  · rw [← hidx]; exact dvd_mul_right 2 _
  · rw [← hidx]
    rintro ⟨k, hk⟩
    apply hodd
    exact ⟨k, by omega⟩

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
