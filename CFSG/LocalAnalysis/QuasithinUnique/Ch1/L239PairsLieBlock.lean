module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieSub
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieCoprime
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsBlocks

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.Open
open scoped commutatorElement

section A3

variable {G : Type*} [Group G]

theorem commutator_blockU_le_blockZ [Finite G] {B Q : Subgroup G} (hB : IsShort2 B)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hQB : Q ≤ Subgroup.normalizer (B : Set G))
    (hQ : IsPGroup 2 Q) : ⁅blockU B, Q⁆ ≤ blockZ B := by
  obtain ⟨-, -, ⟨hU1, hU2⟩, -, hZlt, hirr⟩ := hB
  have hBnQB : B ≤ Subgroup.normalizer (blockQ B : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B
  have hQnQB : Q ≤ Subgroup.normalizer (blockQ B : Set G) :=
    hQB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B)
  have hBnB : B ≤ Subgroup.normalizer (B : Set G) := Subgroup.le_normalizer
  have hBnU : B ≤ Subgroup.normalizer (blockU B : Set G) :=
    le_normalizer_commutator_of_le_normalizer B _ _ hBnQB hBnB
  have hQnU : Q ≤ Subgroup.normalizer (blockU B : Set G) :=
    le_normalizer_commutator_of_le_normalizer Q _ _ hQnQB hQB
  have hQBle : blockQ B ≤ B := CFSG.LieType.BorelTits.pCoreOf_le 2 B
  have hUB : blockU B ≤ B := by
    refine Subgroup.commutator_le.2 fun x hx b hb => ?_
    have : ⁅x, b⁆ = x * (b * x⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact B.mul_mem (hQBle hx) (B.mul_mem (B.mul_mem hb (B.inv_mem (hQBle hx))) (B.inv_mem hb))
  have hBnC : B ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) :=
    hBnB.trans (normalizer_le_normalizer_centralizer B)
  have hQnC : Q ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) :=
    hQB.trans (normalizer_le_normalizer_centralizer B)
  have hBnZ : B ≤ Subgroup.normalizer (blockZ B : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hBnU hg, hBnC hg⟩
  have hQnZ : Q ≤ Subgroup.normalizer (blockZ B : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hQnU hg, hQnC hg⟩
  have hZU : blockZ B ≤ blockU B := inf_le_left
  have hV : ⁅blockU B, Q⁆ ≤ blockU B := by
    refine Subgroup.commutator_le.2 fun u hu q hq => ?_
    have h1 : q * u⁻¹ * q⁻¹ ∈ blockU B := (Subgroup.mem_normalizer_iff.1 (hQnU hq) u⁻¹).1
      ((blockU B).inv_mem hu)
    have : ⁅u, q⁆ = u * (q * u⁻¹ * q⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact (blockU B).mul_mem hu h1
  have hBV : B ≤ Subgroup.normalizer ((⁅blockU B, Q⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le_normalizer B _ _ hBnU hBQ
  have hW : B ≤ Subgroup.normalizer ((blockZ B ⊔ ⁅blockU B, Q⁆ : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_sup (hBnZ hg) (hBV hg)
  rcases hirr _ le_sup_left (sup_le hZU hV) hW with h | h
  · exact h ▸ le_sup_right
  · exfalso
    have hUpg : IsPGroup 2 (blockU B) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B).to_le (fun x hx => (hU1 hx).1)
    have hUQ : IsPGroup 2 (blockU B ⊔ Q : Subgroup G) :=
      hUpg.to_sup_of_normal_left' hQ hQnU
    have hZn : (blockU B ⊔ Q : Subgroup G) ≤ Subgroup.normalizer (blockZ B : Set G) :=
      sup_le (hUB.trans hBnZ) hQnZ
    have hle0 : blockU B ≤ blockZ B ⊔ ⁅blockU B, blockU B ⊔ Q⁆ := by
      calc blockU B = blockZ B ⊔ ⁅blockU B, Q⁆ := h.symm
        _ ≤ blockZ B ⊔ ⁅blockU B, blockU B ⊔ Q⁆ :=
          sup_le_sup_left (Subgroup.commutator_mono le_rfl le_sup_right) _
    have hle : blockU B ≤ blockZ B :=
      le_of_le_sup_commutator_of_isPGroup (p := 2) (Y := blockU B ⊔ Q) hUQ le_sup_left
        (hZU.trans le_sup_left) hZn hle0
    exact absurd hZlt (not_lt_of_ge hle)

theorem commutator_self_eq_of_quasisimple [Finite G] {B : Subgroup G}
    (h2 : ∀ (N : Subgroup ↥B) [N.Normal], IsPGroup 2 (↥B ⧸ N) → N = ⊤)
    (hqs : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) : ⁅B, B⁆ = B := by
  have hK : _root_.commutator ↥B = ⊤ := by
    apply h2
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    let π : ↥B →* ↥B ⧸ CFSG.pCore 2 ↥B := QuotientGroup.mk' (CFSG.pCore 2 ↥B)
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hmap : (_root_.commutator ↥B).map π = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπs]
      have := hqs.1.commutator_eq_top
      rwa [_root_.commutator_def] at this
    have hg : π g ∈ (_root_.commutator ↥B).map π := hmap ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hcg⟩ := hg
    have hn : c⁻¹ * g ∈ CFSG.pCore 2 ↥B := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥B), MonoidHom.mem_ker, map_mul, map_inv]
      have : π c = π g := hcg
      rw [this, inv_mul_cancel]
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥B) ⟨c⁻¹ * g, hn⟩
    refine ⟨k, ?_⟩
    have hk' : (c⁻¹ * g) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hmc : (QuotientGroup.mk c : ↥B ⧸ _root_.commutator ↥B) = 1 :=
      (QuotientGroup.eq_one_iff c).2 hc
    have hgc : (QuotientGroup.mk g : ↥B ⧸ _root_.commutator ↥B) =
        QuotientGroup.mk (c⁻¹ * g) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmc, inv_one, one_mul]
    rw [hgc, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  exact Subgroup.isPerfect_iff.1 ⟨hK⟩

end A3

section Facts

variable {G : Type*} [Group G]

@[expose] def LeviFacts (P Q : Subgroup G) : Prop :=
  CFSG.Quasithin.perfectCore P ≤ Q ∨
    (Q ≤ ⁅Q, CFSG.Quasithin.perfectCore P⁆ ∧
      ∃ (T : Type) (_ : Group T) (g : ↥(CFSG.Quasithin.perfectCore P) →* T),
        IsSimpleGroup T ∧ Function.Surjective g ∧ ∀ x, g x = 1 → (x : G) ∈ Q)

structure ParabolicFacts (P Q : Subgroup G) : Prop where
  le : Q ≤ P
  normalizes : P ≤ Subgroup.normalizer (Q : Set G)
  pGroup : IsPGroup 2 Q
  selfCentralizing : P ⊓ Subgroup.centralizer (Q : Set G) ≤ Q
  center_le : Q ⊓ Subgroup.centralizer (Q : Set G) ≤ ⁅Q, Q⁆
  nonabelian : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x
  levi : LeviFacts P Q

variable {P Q : Subgroup G}

theorem ParabolicFacts.charTwo (hF : ParabolicFacts P Q) : CharTwo P := by
  have hQle : Q ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hF.le hF.normalizes hF.pGroup
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hQle) hx.2
  exact hQle (hF.selfCentralizing ⟨hx.1, hxC⟩)

theorem ParabolicFacts.no_a3 [Finite G] (hF : ParabolicFacts P Q) {B : Subgroup G}
    (hB : IsBlock2 P B) (h3 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 3) : False := by
  obtain ⟨hshort, hBP, hsub⟩ := hB
  have hB2 := hshort.1
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hBP.trans hF.normalizes
  have hQB : Q ≤ Subgroup.normalizer (B : Set G) :=
    normalizes_of_subnormal hBP hsub hB2 hF.le hF.normalizes hF.pGroup
  have hQ := hF.pGroup
  have h3dvd : 3 ∣ Nat.card ↥B := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), h3]
    exact Dvd.intro _ rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3dvd
  set t : G := (t' : G) with htdef
  have ht : orderOf t = 3 := by rw [htdef, Subgroup.orderOf_coe]; exact ht'
  have htB : t ∈ B := t'.2
  set A : Subgroup G := Subgroup.zpowers t with hAdef
  have hAB : A ≤ B := by rw [hAdef, Subgroup.zpowers_le]; exact htB
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hAB.trans hBQ
  set W : Subgroup G := ⁅Q, A⁆ with hWdef
  have hWQle : W ≤ Q := by
    refine Subgroup.commutator_le.2 fun q hq a ha => ?_
    have h1 : a * q⁻¹ * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hAQ ha) q⁻¹).1 (Q.inv_mem hq)
    have : ⁅q, a⁆ = q * (a * q⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Q.mul_mem hq h1
  have hWle : W ≤ pCoreOf 2 B :=
    ((Subgroup.commutator_mono (le_refl Q) hAB).trans
      (commutator_le_inf_of_normalizes hBQ hQB)).trans
      (inf_le_pCoreOf hBP hF.normalizes hQ)
  have hidem : ⁅W, A⁆ = W :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three A Q
      (isPGroup_three_zpowers ht) hAQ (coprime_three_card hQ)
  have hWU : W ≤ blockU B := by
    calc W = ⁅W, A⁆ := hidem.symm
      _ ≤ blockU B := Subgroup.commutator_mono hWle hAB
  obtain ⟨hU1, -⟩ := hshort.2.2.1
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have hyC : y ∈ Subgroup.centralizer (blockQ B : Set G) := (hU1 (hWU hy)).2
    exact Subgroup.mem_centralizer_iff.1 hyC x (hWle hx)
  have hQW : Q ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_left Q A
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_right Q A
  have hWQ_Z : ⁅W, Q⁆ ≤ blockZ B :=
    (Subgroup.commutator_mono hWU (le_refl Q)).trans
      (commutator_blockU_le_blockZ hshort hBQ hQB hQ)
  have hWQ_W : ⁅W, Q⁆ ≤ W := by
    refine Subgroup.commutator_le.2 fun w hw q hq => ?_
    have h1 : q * w⁻¹ * q⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hQW hq) w⁻¹).1 (W.inv_mem hw)
    have : ⁅w, q⁆ = w * (q * w⁻¹ * q⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact W.mul_mem hw h1
  have hWQ_C : ⁅W, Q⁆ ≤ Subgroup.centralizer (A : Set G) :=
    hWQ_Z.trans (inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAB)))
  have hWcard : Nat.Coprime (Nat.card A) (Nat.card W) := by
    have : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, ht]
    rw [this]
    exact coprime_three_card (hQ.to_le hWQle)
  have hfit := fitting_commutator_inf_centralizer hWab hAW hWcard
  have hAWeq : ⁅A, W⁆ = W := by rw [Subgroup.commutator_comm]; exact hidem
  rw [hAWeq] at hfit
  have hWQbot : ⁅W, Q⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hfit]
    exact le_inf hWQ_W hWQ_C
  have hWC : W ≤ Subgroup.centralizer (Q : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : ⁅w, q⁆ ∈ ⁅W, Q⁆ := Subgroup.commutator_mem_commutator hw hq
    rw [hWQbot, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hWcomm : W ≤ ⁅Q, Q⁆ := fun w hw => hF.center_le ⟨hWQle hw, hWC hw⟩
  have hcent := zpowers_le_centralizer_of_commutator_le hQ ht (hAQ (Subgroup.mem_zpowers t))
    hWcomm
  have htC : t ∈ Subgroup.centralizer (Q : Set G) := hcent (Subgroup.mem_zpowers t)
  have htQ : t ∈ Q := hF.selfCentralizing ⟨hBP htB, htC⟩
  obtain ⟨k, hk⟩ := hQ ⟨t, htQ⟩
  have hk' : t ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : 3 ∣ 2 ^ k := ht ▸ orderOf_dvd_of_pow_eq_one hk'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem ParabolicFacts.no_quasisimple [Finite G] (hF : ParabolicFacts P Q) {B : Subgroup G}
    (hB : IsBlock2 P B) (hqs : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) : False := by
  obtain ⟨hshort, hBP, hsub⟩ := hB
  have hB2 := hshort.1
  have hQ := hF.pGroup
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hBP.trans hF.normalizes
  have hQB : Q ≤ Subgroup.normalizer (B : Set G) :=
    normalizes_of_subnormal hBP hsub hB2 hF.le hF.normalizes hQ
  have hperf : ⁅B, B⁆ = B := commutator_self_eq_of_quasisimple hB2 hqs
  have hBcore : B ≤ CFSG.Quasithin.perfectCore P :=
    CFSG.Quasithin.le_perfectCore_of_perfect hBP hperf
  have hbadQ : B ≤ Q → False := by
    intro hBQle
    have hB2g : IsPGroup 2 ↥B := hQ.to_le hBQle
    have hcore : CFSG.pCore 2 ↥B = ⊤ := by
      rw [eq_top_iff]
      refine le_pCore_of_normal (N := (⊤ : Subgroup ↥B)) fun x => ?_
      obtain ⟨k, hk⟩ := hB2g (x : ↥B)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hsubs : Subsingleton (↥B ⧸ CFSG.pCore 2 ↥B) := by
      rw [hcore]; exact QuotientGroup.subsingleton_quotient_top
    have hns : Nontrivial ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B)) :=
      hqs.2.1.toNontrivial
    have : Nontrivial (↥B ⧸ CFSG.pCore 2 ↥B) :=
      Function.Surjective.nontrivial (f := (QuotientGroup.mk :
        (↥B ⧸ CFSG.pCore 2 ↥B) → (↥B ⧸ CFSG.pCore 2 ↥B) ⧸
          Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B))) QuotientGroup.mk_surjective
    exact not_subsingleton _ hsubs
  rcases hF.levi with hPQ | ⟨hgen, T, instT, g, hT, hg, hker⟩
  · exact hbadQ (hBcore.trans hPQ)
  have hsub' : (B.subgroupOf (CFSG.Quasithin.perfectCore P)).IsSubnormal :=
    isSubnormal_subgroupOf_of_le (CFSG.Quasithin.perfectCore_le P) hsub
  have himg : ((B.subgroupOf (CFSG.Quasithin.perfectCore P)).map g).IsSubnormal :=
    isSubnormal_map_of_surjective g hg hsub'
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hT himg with hbot | htop
  ·
    have hBQle : B ≤ Q := by
      intro b hb
      have hbc : b ∈ CFSG.Quasithin.perfectCore P := hBcore hb
      let b' : ↥(CFSG.Quasithin.perfectCore P) := ⟨b, hbc⟩
      have hmem : g b' ∈ (B.subgroupOf (CFSG.Quasithin.perfectCore P)).map g := ⟨b', hb, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hker b' hmem
    exact hbadQ hBQle
  ·
    have hPinf : ∀ x ∈ CFSG.Quasithin.perfectCore P, ∃ b ∈ B, ∃ q ∈ Q, x = b * q := by
      intro x hx
      let x' : ↥(CFSG.Quasithin.perfectCore P) := ⟨x, hx⟩
      have hmem : g x' ∈ (B.subgroupOf (CFSG.Quasithin.perfectCore P)).map g :=
        htop ▸ Subgroup.mem_top _
      obtain ⟨b', hb', hbx⟩ := hmem
      refine ⟨(b' : G), hb', ((b'⁻¹ * x' : ↥(CFSG.Quasithin.perfectCore P)) : G), hker _ ?_, ?_⟩
      · rw [map_mul, map_inv, hbx, inv_mul_cancel]
      · simp [x']
    have hQ1 : ⁅Q, CFSG.Quasithin.perfectCore P⁆ ≤ ⁅Q, B⁆ ⊔ ⁅Q, Q⁆ := by
      refine Subgroup.commutator_le.2 fun q hq x hx => ?_
      obtain ⟨b, hb, q', hq', rfl⟩ := hPinf x hx
      have hid : ⁅q, b * q'⁆ = ⁅q, b⁆ * (b * ⁅q, q'⁆ * b⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [hid]
      refine mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq hb)) ?_
      have hn : b ∈ Subgroup.normalizer ((⁅Q, Q⁆ : Subgroup G) : Set G) :=
        le_normalizer_commutator_of_le_normalizer B Q Q hBQ hBQ hb
      have := (Subgroup.mem_normalizer_iff.1 hn _).1 (Subgroup.commutator_mem_commutator hq hq')
      exact Subgroup.mem_sup_right this
    have hQBle : ⁅Q, B⁆ ≤ Q := (commutator_le_inf_of_normalizes hBQ hQB).trans inf_le_right
    have hsupQ : ⁅Q, B⁆ ⊔ ⁅Q, Q⁆ = Q :=
      le_antisymm (sup_le hQBle (commutator_self_le Q)) (hgen.trans hQ1)
    have hQfin : Finite Q := Finite.of_injective _ Q.subtype_injective
    have hQBeq : ⁅Q, B⁆ = Q := eq_of_sup_commutator_eq (p := 2) hQ hQBle hsupQ
    have hQleB : Q ≤ B ⊓ Q := by
      have h := commutator_le_inf_of_normalizes hBQ hQB
      rwa [hQBeq] at h
    have hQle : Q ≤ pCoreOf 2 B := hQleB.trans (inf_le_pCoreOf hBP hF.normalizes hQ)
    have hQU : Q ≤ blockU B := by
      calc Q = ⁅Q, B⁆ := hQBeq.symm
        _ ≤ ⁅pCoreOf 2 B, B⁆ := Subgroup.commutator_mono hQle le_rfl
    obtain ⟨hU1, -⟩ := hshort.2.2.1
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    have hyC : y ∈ Subgroup.centralizer (blockQ B : Set G) := (hU1 (hQU hy)).2
    exact hxy (Subgroup.mem_centralizer_iff.1 hyC x (hQle hx))

theorem ParabolicFacts.no_block [Finite G] (hF : ParabolicFacts P Q) {B : Subgroup G}
    (hB : IsBlock2 P B) : False := by
  rcases hB.1.2.2.2.1 with hqs | h3
  · exact hF.no_quasisimple hB hqs
  · exact hF.no_a3 hB h3

theorem ParabolicFacts.not_hasChi0Block [Finite G] (hF : ParabolicFacts P Q) :
    ¬ HasChi0Block P := by
  rintro ⟨B, hB, -⟩
  exact hF.no_block hB

end Facts


end CFSG.QuasithinUnique.Vol2Native.L239.Lie
