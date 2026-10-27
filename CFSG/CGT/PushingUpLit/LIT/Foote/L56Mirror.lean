module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56PartC

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3
  (Theorem3Statement Frame SylowFrame exists_isSylowOf_le)

variable {G : Type} [Group G] [Finite G]

theorem exists_sylowFrame_of_le {A T R : Subgroup G} (hF : Frame A T) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ (A ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) :
    ∃ S : Subgroup G, SylowFrame A T S ∧ R ≤ S ⊓ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hRP⟩ := exists_isSylowOf_le hR2 hRN
  obtain ⟨S, hS, hPS⟩ := exists_isSylowOf_le hP.isPGroup (hP.le.trans inf_le_left)
  have hPle : P ≤ S ⊓ Subgroup.normalizer (T : Set G) :=
    le_inf hPS (hP.le.trans inf_le_right)
  have heq := hP.eq_of_le hPle (inf_le_inf_right _ hS.le) hS.isPGroup.to_inf_left
  refine ⟨S, { toFrame := hF, sylow := hS, sylow_normalizer := ?_ }, hRP.trans hPle⟩
  rw [heq]
  exact hP

omit [Finite G] in
theorem rightConjugate_eSub (J : Subgroup G) (g h : G) :
    rightConjugate (eSub (rightConjugate J g) h) g⁻¹ = eSub J (g * h * g⁻¹) := by
  unfold eSub
  rw [CFSG.ComponentClassification.AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul,
    rightConjugate_mul, ← CFSG.ComponentClassification.AschbacherTheorem3.rightConjugate_normalizer,
    rightConjugate_mul, mul_inv_cancel, rightConjugate_one, mul_assoc]

theorem blockU_le_of_sylowFrame {J T S : Subgroup G} (hJ : QBlock J) (hS : SylowFrame J T S) :
    blockU J ≤ S := by
  have hTV : T ≤ Subgroup.normalizer (blockU J : Set G) := fun t ht =>
    mem_normalizer_blockU (hS.le_normalizer ht)
  exact QBlock.le_of_isPGroup_normal' hS.sylow ((blockU_le J).trans le_sup_left)
    (sup_le (le_normalizer_blockU J) hTV) hJ.isPGroup_blockU

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem le_blockU_conj (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G} {T S : Subgroup G}
    (hgood : Good56 M J g) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    (hS : SylowFrame J T S) (hncent : ¬ ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t) :
    T ≤ blockU (rightConjugate J g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := c.block
  have hg : g ∉ M := hgood.1
  obtain ⟨-, -, hQV, hQT⟩ := c.partC hA hz hgood hT hmax hS hncent
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup G, Q = S ⊓ Subgroup.normalizer (T : Set G) ⊓ J := ⟨_, rfl⟩
  rw [← hQdef] at hQV hQT
  have hT1 : T ≠ ⊥ := sylow_ne_bot56 hgood hT
  have hTJg : T ≤ rightConjugate J g := hT.le.trans inf_le_left
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hnc := c.exists_noncentral hA hz hg hT hT1
  have hQc : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q := by
    rw [hQdef]
    exact inf_comm_T hS
  have hQJ : Q ≤ J := by
    rw [hQdef]
    exact inf_le_right
  have hQnT : Q ≤ Subgroup.normalizer (T : Set G) := by
    rw [hQdef]
    exact inf_le_left.trans inf_le_right
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [hQdef]
    exact hS.sylow.isPGroup.to_le (inf_le_left.trans inf_le_left)
  have hQN : Q ≤ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := fun q hq =>
    c.mem_normalizer_conj_of_centralizes hTJg hT2 hT1 hnc (hQc q hq)
  have hc₁ := c.transport g
  have hz₁ := hz.transport g
  have e : rightConjugate (rightConjugate J g) g⁻¹ = J := by
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hg1 : g⁻¹ ∉ rightConjugate M g := by
    intro h
    apply hg
    rw [mem_rightConjugate_iff] at h
    have h' : g⁻¹ ∈ M := by simpa using h
    simpa using M.inv_mem h'
  have hQE : Q ≤ eSub (rightConjugate J g) g⁻¹ := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨?_, hQN hx⟩
    rw [e]
    exact hQJ hx
  have h4T : 4 ≤ Nat.card T := by
    obtain ⟨W, hWle, hW2, hW4⟩ := hgood.2
    have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW4]; norm_num)
    have := card_le_of_isSylowOf hT hWle hWp
    omega
  have hQ4 : 4 ≤ Nat.card Q := by rw [hQT]; exact h4T
  have hQbot : Q ≠ ⊥ := by
    have := (Subgroup.one_lt_card_iff_ne_bot Q).1 (by omega)
    exact this
  obtain ⟨⟨a, ha⟩, ha1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hQbot
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  obtain ⟨W₁, hW₁Q, -, hW₁2, hW₁4⟩ := exists_fourGroup_of_card
    (fun x hx y hy => hJ.blockU_comm x (hQV hx) y (hQV hy))
    (fun x hx => hJ.blockU_sq_eq_one x (hQV hx)) hQ4 ha ha1
  have hgood₁ : Good56 (rightConjugate M g) (rightConjugate J g) g⁻¹ :=
    ⟨hg1, W₁, hW₁Q.trans hQE, hW₁2, hW₁4⟩
  have hcardle : ∀ R : Subgroup G, R ≤ eSub (rightConjugate J g) g⁻¹ → IsPGroup 2 ↥R →
      Nat.card R ≤ Nat.card T := by
    intro R hR hR2
    have hRJ : R ≤ J := fun x hx => by
      have := (Subgroup.mem_inf.1 (hR hx)).1
      rwa [e] at this
    exact c.card_le_of_le_normalizer hA hz hgood hT hmax hRJ
      (fun x hx => (Subgroup.mem_inf.1 (hR hx)).2) hR2
  have hT₁ : ABGLocalTools.IsSylowOf 2 Q (eSub (rightConjugate J g) g⁻¹) := by
    obtain ⟨Q₂, hQ₂, hQQ₂⟩ := exists_isSylowOf_le hQ2 hQE
    have hle := hcardle Q₂ hQ₂.le hQ₂.isPGroup
    have heq : Q = Q₂ := Subgroup.eq_of_le_of_card_ge hQQ₂ (by rw [hQT]; exact hle)
    rw [heq]
    exact hQ₂
  have hmax₁ : ∀ h, Good56 (rightConjugate M g) (rightConjugate J g) h →
      (Nat.card ↥(eSub (rightConjugate J g) h)).factorization 2 ≤
        (Nat.card ↥(eSub (rightConjugate J g) g⁻¹)).factorization 2 := by
    intro h hh
    obtain ⟨hhM, W₂, hW₂le, hW₂2, hW₂4⟩ := hh
    have hgood' : Good56 M J (g * h * g⁻¹) := by
      refine ⟨fun hm => hhM ((mem_rightConjugate_iff M g h).2 hm), rightConjugate W₂ g⁻¹, ?_,
        isElemAbelian_rightConjugate hW₂2 g⁻¹, ?_⟩
      · rw [← rightConjugate_eSub J g h]
        exact CFSG.ComponentClassification.AschbacherTheorem3.rightConjugate_le_rightConjugate
          hW₂le g⁻¹
      · rw [rightConjugate_card, hW₂4]
    have h1 := hmax _ hgood'
    have h2 : Nat.card ↥(eSub (rightConjugate J g) h) = Nat.card ↥(eSub J (g * h * g⁻¹)) := by
      rw [← rightConjugate_eSub J g h, rightConjugate_card]
    have h3 : (Nat.card ↥(eSub J g)).factorization 2 ≤
        (Nat.card ↥(eSub (rightConjugate J g) g⁻¹)).factorization 2 := by
      have hdvd : Nat.card Q ∣ Nat.card ↥(eSub (rightConjugate J g) g⁻¹) :=
        Subgroup.card_dvd_of_le hQE
      rw [hQT, hT.card_eq] at hdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
    rw [h2]
    exact h1.trans h3
  have hnc₁ := hc₁.not_centralizes_blockU hA hz₁ hgood₁ hT₁ hmax₁
  have hF : Frame (rightConjugate J g) Q :=
    { le_normalizer := hQN
      inf_eq_bot := hc₁.inf_eq_bot_of_le hg1 (by rw [e]; exact hQJ) hQ2
      isPGroup := hQ2 }
  have hTQ2 : IsPGroup 2 ↥(T ⊔ Q) := hT2.to_sup_of_normal_left' hQ2 hQnT
  have hTnQ : T ≤ Subgroup.normalizer (Q : Set G) := fun t ht =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun q hq => hQc q hq t ht)
  have hRN : T ⊔ Q ≤ (rightConjugate J g ⊔ Q) ⊓ Subgroup.normalizer (Q : Set G) :=
    sup_le (le_inf (hTJg.trans le_sup_left) hTnQ)
      (le_inf le_sup_right Subgroup.le_normalizer)
  obtain ⟨S', hS', hRS'⟩ := exists_sylowFrame_of_le hF hTQ2 hRN
  obtain ⟨-, -, hQ'V, -⟩ := hc₁.partC hA hz₁ hgood₁ hT₁ hmax₁ hS' hnc₁
  exact fun t ht => hQ'V ⟨hRS' (Subgroup.mem_sup_left ht), hTJg ht⟩

theorem false_of_blockU_conj_le (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G}
    {T S : Subgroup G} (hgood : Good56 M J g) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    (hS : SylowFrame J T S) (hncent : ¬ ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t)
    (hVM : blockU (rightConjugate J g) ≤ M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := c.block
  have hB := hJ.conj g
  have hg : g ∉ M := hgood.1
  obtain ⟨-, -, hQV, hQT⟩ := c.partC hA hz hgood hT hmax hS hncent
  have hVc := hB.blockU_comm
  have hVs := hB.blockU_sq_eq_one
  have hVN : blockU (rightConjugate J g) ≤ Subgroup.normalizer (J : Set G) := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact Subgroup.one_mem _
    obtain ⟨W, hWV, haW, hW2, hW4⟩ := exists_fourGroup_of_card hVc hVs
      (by have := hB.eight_le_card_blockU; omega) ha ha1
    exact c.normalizes_of_le_conj hA hz hg
      (fun x hx => ⟨blockU_le _ (hWV hx), hVM (hWV hx)⟩) hW2 hW4 haW
  have hVE : blockU (rightConjugate J g) ≤ eSub J g := fun a ha =>
    Subgroup.mem_inf.2 ⟨blockU_le _ ha, hVN ha⟩
  have h1 : Nat.card ↥(blockU (rightConjugate J g)) ≤ Nat.card T :=
    card_le_of_isSylowOf hT hVE hB.isPGroup_blockU
  have h2 : Nat.card ↥(blockU (rightConjugate J g)) = Nat.card ↥(blockU J) := by
    rw [blockU_rightConjugate, rightConjugate_card]
  have hVQ : blockU J ≤ S ⊓ Subgroup.normalizer (T : Set G) ⊓ J :=
    Subgroup.eq_of_le_of_card_ge hQV (by rw [hQT, ← h2]; exact h1) ▸ le_rfl
  apply hncent
  intro t ht v hv
  have := (inf_comm_T hS) v (hVQ hv) t ht
  exact this.symm

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
