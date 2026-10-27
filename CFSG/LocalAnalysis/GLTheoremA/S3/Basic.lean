module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma31
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

structure S3Ctx (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Open.IsKProper G
  charTwo : IsCharTwoType G
  rank_ge : 4 ≤ GLATwoLocalRank p G
  deltaZero : GLADeltaZero G p
  noGF2 : p = 3 → ¬ GLAGF2Type G
  lemma31 : ∀ B D N : Subgroup G, GLAIsBmax p B → D ≤ B → ¬ IsCyclic D → GLAIsMaxTwoLocal N →
    B ≤ N → ∃ D₀ : Subgroup G, D₀ ≤ D ∧ Nat.card D₀ * p = Nat.card D ∧
      (∀ d ∈ D₀, d ≠ 1 → IsEssential p B d) ∧
      (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G) ≠ ⊥

variable {G : Type} [Group G] [Finite G]

theorem S3Ctx.of_ctx {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) : S3Ctx G p where
  prime := hp.1.1
  odd := hp.1.2.1
  simple := hctx.1.simple
  nonabelian := hctx.1.nonabelian
  kProper := hctx.1.kProper
  charTwo := hctx.1.charTwo
  rank_ge := hp.2.1 ▸ hctx.1.four_le
  deltaZero := hp.2.2
  noGF2 := fun h3 hGF => hctx.2 ⟨h3 ▸ hp, hGF⟩
  lemma31 := fun _ _ _ hB hDB hDnc hN hBN =>
    CFSG.LocalAnalysis.GLTheoremA.lemma31 hctx hp hB hDB hDnc hN hBN

@[expose] def NotPConstr (p : ℕ) (E : Subgroup G) : Prop :=
  GLAPLayer p (Subgroup.centralizer (E : Set G)) ≠ ⊥

structure Star3 (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) : Prop where
  bmax : GLAIsBmax p B
  notSC : ¬ IsSC p B
  chev : ∀ (x : G) (L : Subgroup G), IsEssential p B x →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L → IsChevSimple p (PSimple p L)

namespace S3

theorem glaPLayer_ne_bot_iff {p : ℕ} (hp : p.Prime) {X : Subgroup G} :
    GLAPLayer p X ≠ ⊥ ↔ ∃ L : Subgroup G, GLAPComponent p X L := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply h
    have : {L : Subgroup G | GLAPComponent p X L} = ∅ := by
      ext L; simp [hne L]
    unfold GLAPLayer
    rw [this, sSup_empty]
  · rintro ⟨L, hL⟩ h
    exact glaPComponent_ne_bot' hL (le_bot_iff.1 (h ▸ le_sSup hL))

theorem isKGroup_cen (hsimple : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Open.IsKProper G) {E : Subgroup G} (hE : E ≠ ⊥) :
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer (E : Set G)) := by
  apply isKGroup_of_isKProper hKP
  intro htop
  have hEZ : E ≤ Subgroup.center G := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (E : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.1 hg e he).symm
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · apply hE
    rw [eq_bot_iff]
    exact h ▸ hEZ
  · obtain ⟨a, b, hab⟩ := hna
    apply hab
    have : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem centralizer_zpowers (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem not_isCyclic_of_card {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hcard : p ^ 2 ≤ Nat.card E) : ¬ IsCyclic E := by
  intro hc
  have hexp : Monoid.exponent ↥E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one
      (fun x => Subtype.ext (by simpa using hE.2 (x : G) x.2))
  rw [IsCyclic.exponent_eq_card] at hexp
  have h1 : Nat.card E ≤ p := Nat.le_of_dvd hp.pos hexp
  have h2 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem card_ge_of_not_isCyclic {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hnc : ¬ IsCyclic E) : p ^ 2 ≤ Nat.card E := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  by_contra hlt
  push_neg at hlt
  apply hnc
  have hk1 : k ≤ 1 := by
    by_contra h
    have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  interval_cases k
  · rw [pow_zero] at hk
    haveI : Subsingleton E := (Nat.card_eq_one_iff_unique.1 hk).1
    infer_instance
  · rw [pow_one] at hk
    haveI : Fact p.Prime := ⟨hp⟩
    exact isCyclic_of_prime_card hk

theorem exists_card_pow_le {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    {r : ℕ} (hr : p ^ r ∣ Nat.card E) :
    ∃ F : Subgroup G, F ≤ E ∧ Nat.card F = p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime p hr
  refine ⟨F'.map E.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective]
  exact hF'

theorem exists_invariant_sylow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {A Q : Subgroup G}
    (hA : IsPGroup p A)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hcop : Nat.Coprime p (Nat.card Q))
    (hqQ : q ∣ Nat.card Q) :
    ∃ S : Subgroup G, S ≤ Q ∧ IsPGroup q S ∧ S ≠ ⊥ ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      Nat.card S = q ^ (Nat.card Q).factorization q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  letI : MulDistribMulAction A Q :=
    MulDistribMulAction.compHom Q (Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ))
  obtain ⟨P₀⟩ := Sylow.nonempty (p := q) (G := Q)
  have hnd : ¬ p ∣ Nat.card (Sylow q Q) := by
    intro hdiv
    have h1 : p ∣ Nat.card Q :=
      hdiv.trans (P₀.card_dvd_index.trans (P₀ : Subgroup Q).index_dvd_card)
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hcop h1)
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q Q) hnd
  have hfix : ∀ a : A, a • P = P := fun a => MulAction.mem_fixedPoints.mp hP a
  have key : ∀ b ∈ A, ∀ h ∈ (P : Subgroup Q).map Q.subtype,
      b * h * b⁻¹ ∈ (P : Subgroup Q).map Q.subtype := by
    intro b hb h hh
    obtain ⟨x, hxP, rfl⟩ := hh
    have hmem : (⟨b, hb⟩ : A) • x ∈ (((⟨b, hb⟩ : A) • P : Sylow q Q) : Subgroup Q) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul x _ _ hxP
    rw [hfix] at hmem
    exact ⟨_, hmem, rfl⟩
  refine ⟨(P : Subgroup Q).map Q.subtype, Subgroup.map_subtype_le _,
    P.isPGroup'.map Q.subtype, ?_, ?_, ?_⟩
  · intro h
    exact P.ne_bot_of_dvd_card hqQ
      ((Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective).1 h)
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key a ha h, fun hconj => ?_⟩
    have := key a⁻¹ (A.inv_mem ha) _ hconj
    simpa [mul_assoc] using this
  · rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact P.card_eq_multiplicity

theorem normalizes_of_comm {A T K : Subgroup G}
    (hA : ∀ t ∈ T, A ≤ Subgroup.normalizer ((GLBConj t K : Subgroup G) : Set G))
    (hT : T ≤ (⁅T, A⁆ : Subgroup G)) : T ≤ Subgroup.normalizer (K : Set G) := by
  have hcomm : (⁅T, A⁆ : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.commutator_le]
    intro t ht a ha
    have haK : a ∈ Subgroup.normalizer (K : Set G) := by
      have := hA 1 T.one_mem ha
      rwa [gLBConj_one] at this
    rw [mem_normalizer_iff_gLBConj_eq]
    have e1 : GLBConj (t * a * t⁻¹ * a⁻¹) K =
        GLBConj a⁻¹ (GLBConj t⁻¹ (GLBConj a (GLBConj t K))) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, gLBConj_gLBConj]
      simp only [mul_assoc]
    rw [commutatorElement_def, e1, gLBConj_eq_of_mem_normalizer (hA t ht ha),
      gLBConj_inv_gLBConj, gLBConj_eq_of_mem_normalizer (Subgroup.inv_mem _ haK)]
  exact fun t ht => hcomm (hT ht)

theorem conj_mem_centModSubgroup {p : ℕ} {L : Subgroup G} {t a : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (ha : a ∈ centModSubgroup p L) :
    t * a * t⁻¹ ∈ centModSubgroup p L := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ht ha.1) (Subgroup.inv_mem _ ht), fun l hl => ?_⟩
  have htL : t⁻¹ * l * t ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ht) l).1 hl
    simpa using this
  have h1 := ha.2 _ htL
  have htO := normalizer_le_normalizer_glaPPrimeCoreOf p L ht
  have h2 := (Subgroup.mem_normalizer_iff.1 htO _).1 h1
  convert h2 using 1
  simp only [commutatorElement_def]
  group

theorem le_centModSubgroup_of_comm {p : ℕ} {A T L : Subgroup G} (hA : A ≤ centModSubgroup p L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT : T ≤ (⁅T, A⁆ : Subgroup G)) :
    T ≤ centModSubgroup p L := by
  have hcomm : (⁅T, A⁆ : Subgroup G) ≤ centModSubgroup p L := by
    rw [Subgroup.commutator_le]
    intro t ht a ha
    have h1 := conj_mem_centModSubgroup (hTL ht) (hA ha)
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hA ha))
  exact fun t ht => hcomm (hT ht)

private theorem primeCore_le (p : ℕ) (L : Subgroup G) : GLAPPrimeCoreOf p L ≤ L :=
  Subgroup.map_subtype_le _

theorem mem_normalizer_of_inducesInnerMod {p : ℕ} {L : Subgroup G} {g : G}
    (h : InducesInnerMod p L g) : g ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨l, hl, hy⟩ := h
  have hle : L ≤ GLBConj g⁻¹ L := by
    intro y hy'
    rw [mem_gLBConj, inv_inv]
    have h1 := hy y hy'
    have h2 : g⁻¹ * y * g = (l⁻¹ * y * l) * ((l⁻¹ * y * l)⁻¹ * (g⁻¹ * y * g)) :=
      (mul_inv_cancel_left _ _).symm
    rw [h2]
    exact L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hl) hy') hl) (primeCore_le p L h1)
  have hcard : Nat.card (GLBConj g⁻¹ L) ≤ Nat.card L := by
    have : Nat.card (GLBConj g⁻¹ L) = Nat.card L := by
      unfold GLBConj
      exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹⁻¹).injective
    exact this.le
  have heq : L = GLBConj g⁻¹ L := Subgroup.eq_of_le_of_card_ge hle hcard
  have : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 heq.symm
  simpa using Subgroup.inv_mem _ this

theorem inducesInnerMod_one (p : ℕ) (L : Subgroup G) : InducesInnerMod p L 1 := by
  refine ⟨1, L.one_mem, fun y _ => ?_⟩
  simp

theorem inducesInnerMod_of_centMod {p : ℕ} {L : Subgroup G} {g : G} (hg : CentMod p L g) :
    InducesInnerMod p L g := by
  refine ⟨1, L.one_mem, fun y hy => ?_⟩
  have h : ⁅y⁻¹, g⁻¹⁆ ∈ GLAPPrimeCoreOf p L :=
    hg.2 (Subgroup.commutator_mem_commutator (L.inv_mem hy)
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)))
  convert h using 1
  simp [commutatorElement_def, mul_assoc]

theorem inducesInnerMod_mul {p : ℕ} {L : Subgroup G} {a b : G} (ha : InducesInnerMod p L a)
    (hb : InducesInnerMod p L b) : InducesInnerMod p L (a * b) := by
  have hbN := mem_normalizer_of_inducesInnerMod hb
  obtain ⟨l₁, hl₁, h₁⟩ := ha
  obtain ⟨l₂, hl₂, h₂⟩ := hb
  refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, fun y hy => ?_⟩
  have hy' : l₁⁻¹ * y * l₁ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl₁) hy) hl₁
  have ho₁mem := h₁ y hy
  have ho₂mem := h₂ _ hy'
  have hconj : b⁻¹ * ((l₁⁻¹ * y * l₁)⁻¹ * (a⁻¹ * y * a)) * b ∈ GLAPPrimeCoreOf p L := by
    have hbinvN := normalizer_le_normalizer_glaPPrimeCoreOf p L (Subgroup.inv_mem _ hbN)
    have := (Subgroup.mem_normalizer_iff.1 hbinvN _).1 ho₁mem
    simpa using this
  have key : ((l₁ * l₂)⁻¹ * y * (l₁ * l₂))⁻¹ * ((a * b)⁻¹ * y * (a * b)) =
      ((l₂⁻¹ * (l₁⁻¹ * y * l₁) * l₂)⁻¹ * (b⁻¹ * (l₁⁻¹ * y * l₁) * b)) *
        (b⁻¹ * ((l₁⁻¹ * y * l₁)⁻¹ * (a⁻¹ * y * a)) * b) := by group
  rw [key]
  exact (GLAPPrimeCoreOf p L).mul_mem ho₂mem hconj

theorem inducesInnerMod_inv {p : ℕ} {L : Subgroup G} {a : G} (ha : InducesInnerMod p L a) :
    InducesInnerMod p L a⁻¹ := by
  have haN := mem_normalizer_of_inducesInnerMod ha
  obtain ⟨l, hl, h⟩ := ha
  refine ⟨l⁻¹, L.inv_mem hl, fun y hy => ?_⟩
  have hz : l * y * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hy) (L.inv_mem hl)
  have h1 := h _ hz
  have haO : a ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L haN
  have h2 := (Subgroup.mem_normalizer_iff.1 haO _).1 h1
  have h3 := Subgroup.inv_mem _ h2
  convert h3 using 1
  group

theorem inducesInnerMod_zpow {p : ℕ} {L : Subgroup G} {a : G} (ha : InducesInnerMod p L a)
    (n : ℤ) : InducesInnerMod p L (a ^ n) := by
  refine Int.induction_on n ?_ ?_ ?_
  · simpa using inducesInnerMod_one p L
  · intro k ih
    rw [zpow_add_one]
    exact inducesInnerMod_mul ih ha
  · intro k ih
    rw [zpow_sub_one]
    exact inducesInnerMod_mul ih (inducesInnerMod_inv ha)

private def innSubgroup (p : ℕ) (L : Subgroup G) : Subgroup G where
  carrier := {g | InducesInnerMod p L g}
  one_mem' := inducesInnerMod_one p L
  mul_mem' := fun ha hb => inducesInnerMod_mul ha hb
  inv_mem' := fun ha => inducesInnerMod_inv ha

theorem not_inducesInnerMod_of_index_p {p : ℕ} (hp : p.Prime) {D D' L : Subgroup G}
    (hDD' : D' ≤ D) (hidx : Nat.card D' * p = Nat.card D) (hD' : D' ≤ centModSubgroup p L)
    (hDL : D ≤ Subgroup.normalizer (L : Set G)) (hexp : ∀ d ∈ D, d ^ p = 1) {d₀ : G}
    (hd₀ : d₀ ∈ D) (hout : ¬ InducesInnerMod p L d₀) :
    ∀ d ∈ D, d ∉ D' → ¬ InducesInnerMod p L d := by
  intro d hd hdD' hin
  apply hout
  have hSD : Subgroup.zpowers d ⊔ D' ≤ D := sup_le ((Subgroup.zpowers_le).2 hd) hDD'
  have hD'S : D' ≤ Subgroup.zpowers d ⊔ D' := le_sup_right
  have hdS : d ∈ Subgroup.zpowers d ⊔ D' :=
    (le_sup_left : Subgroup.zpowers d ≤ Subgroup.zpowers d ⊔ D') (Subgroup.mem_zpowers d)
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hD'S
  have hc2 : Nat.card (Subgroup.zpowers d ⊔ D' : Subgroup G) ∣ Nat.card D :=
    Subgroup.card_dvd_of_le hSD
  have hDpos : 0 < Nat.card D' := Nat.card_pos
  have hcdvd : c ∣ p := by
    have : Nat.card D' * c ∣ Nat.card D' * p := by rw [← hc, hidx]; exact hc2
    exact Nat.dvd_of_mul_dvd_mul_left hDpos this
  have hSeq : Subgroup.zpowers d ⊔ D' = D := by
    rcases (Nat.dvd_prime hp).1 hcdvd with h1 | h1
    · exfalso
      have hEq : D' = Subgroup.zpowers d ⊔ D' :=
        Subgroup.eq_of_le_of_card_ge hD'S (by rw [hc, h1, mul_one])
      exact hdD' (hEq ▸ hdS)
    · exact Subgroup.eq_of_le_of_card_ge hSD (by rw [← hidx, hc, h1])
  have hle : Subgroup.zpowers d ⊔ D' ≤ innSubgroup p L :=
    sup_le ((Subgroup.zpowers_le).2 hin)
      (fun x hx => inducesInnerMod_of_centMod (centMod_iff.2 (hD' hx)))
  exact hle (hSeq ▸ hd₀)

theorem eq_inf_centralizer_sup_of_pgroup {p : ℕ} (hp : p.Prime) {Y Q D : Subgroup G}
    (hD : IsPGroup p D) (hQY : Q ≤ Y) (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime p (Nat.card Q)) (hc : ∀ y ∈ Y, ∀ d ∈ D, ⁅y, d⁆ ∈ Q) :
    (Y ⊓ Subgroup.centralizer (D : Set G)) ⊔ Q = Y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm (sup_le inf_le_left hQY)
  intro l hl
  have hmem : ∀ g ∈ D, ∀ o ∈ Q, l⁻¹ * (g * (l * o) * g⁻¹) ∈ Q := by
    intro g hg o ho
    have h1 : ⁅l⁻¹, g⁆ ∈ Q := hc _ (Y.inv_mem hl) g hg
    have h2 : g * o * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hDQ hg) o).1 ho
    have h3 : l⁻¹ * (g * (l * o) * g⁻¹) = ⁅l⁻¹, g⁆ * (g * o * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact Q.mul_mem h1 h2
  letI act : MulAction D Q :=
    { smul := fun g o => ⟨l⁻¹ * ((g : G) * (l * (o : G)) * (g : G)⁻¹), hmem g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (show l⁻¹ * (((1 : D) : G) * (l * (o : G)) *
          ((1 : D) : G)⁻¹) = (o : G) by simp)
      mul_smul := fun g h o => Subtype.ext (show l⁻¹ * (((g * h : D) : G) * (l * (o : G)) *
          ((g * h : D) : G)⁻¹) = l⁻¹ * ((g : G) * (l * (l⁻¹ * ((h : G) * (l * (o : G)) *
          (h : G)⁻¹))) * (g : G)⁻¹) by simp only [Subgroup.coe_mul]; group) }
  have hOp : ¬ p ∣ Nat.card Q := (hp.coprime_iff_not_dvd).1 hcop
  obtain ⟨o, ho⟩ := hD.nonempty_fixed_point_of_prime_not_dvd_card Q hOp
  have hfix : ∀ g ∈ D, g * (l * (o : G)) * g⁻¹ = l * o := by
    intro g hg
    have hfa : l⁻¹ * (g * (l * (o : G)) * g⁻¹) = o := congrArg Subtype.val (ho ⟨g, hg⟩)
    calc g * (l * (o : G)) * g⁻¹ = l * (l⁻¹ * (g * (l * (o : G)) * g⁻¹)) := by group
      _ = l * o := by rw [hfa]
  have hyL : l * (o : G) ∈ Y := Y.mul_mem hl (hQY o.2)
  have hyC : l * (o : G) ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    calc g * (l * (o : G)) = (g * (l * (o : G)) * g⁻¹) * g := by group
      _ = (l * (o : G)) * g := by rw [hfix g hg]
  have hl' : l = (l * (o : G)) * (o : G)⁻¹ := by group
  rw [hl']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hyL, hyC⟩)
    (Subgroup.mem_sup_right (Q.inv_mem o.2))

private theorem inf_centralizer_sup_eq_of_pgroup {p : ℕ} (hp : p.Prime) {L D : Subgroup G}
    (hD : IsPGroup p D) (hDL : D ≤ centModSubgroup p L) :
    (L ⊓ Subgroup.centralizer (D : Set G)) ⊔ GLAPPrimeCoreOf p L = L :=
  eq_inf_centralizer_sup_of_pgroup hp hD (Subgroup.map_subtype_le _)
    (fun _ hg => normalizer_le_normalizer_glaPPrimeCoreOf p L (hDL hg).1)
    ((hp.coprime_iff_not_dvd).2 (not_dvd_card_glaPPrimeCoreOf hp L))
    (fun _ hy _ hd => (hDL hd).2 _ hy)

theorem cover_of_centMod {p : ℕ} (hp : p.Prime) {X D Jc J : Subgroup G}
    (hJc : GLAPComponent p X Jc) (hD : IsPGroup p D) (hDJc : D ≤ centModSubgroup p Jc)
    (hJ : GLAPComponent p (Jc ⊓ Subgroup.centralizer (D : Set G)) J) :
    J ⊔ GLAPPrimeCoreOf p Jc = Jc := by
  set Y := Jc ⊓ Subgroup.centralizer (D : Set G) with hY
  have hcov : Y ⊔ GLAPPrimeCoreOf p Jc = Jc := inf_centralizer_sup_eq_of_pgroup hp hD hDJc
  obtain ⟨hOY, ⟨e⟩⟩ := cover_facts hp (inf_le_left : Y ≤ Jc) hcov
  have hYq : CFSG.Open.IsQuasisimple (PQuot p Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
      (isQuasisimple_pQuot_of_glaPComponent hp hJc)
  obtain ⟨-, huniq, hbar⟩ := glaPLayer_of_isQuasisimple hYq
  have hJeq : J = GLAPLayer p Y := huniq J hJ
  have hJY : J ≤ Y := hJ.1
  have hbarJ : barX p Y J = ⊤ := hJeq ▸ hbar
  have hsupJ : J ⊔ GLAPPrimeCoreOf p Y = Y := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hJY hbarJ
  apply le_antisymm
  · exact sup_le (hJY.trans inf_le_left) (Subgroup.map_subtype_le _)
  · calc Jc = Y ⊔ GLAPPrimeCoreOf p Jc := hcov.symm
      _ = (J ⊔ GLAPPrimeCoreOf p Y) ⊔ GLAPPrimeCoreOf p Jc := by rw [hsupJ]
      _ ≤ J ⊔ GLAPPrimeCoreOf p Jc := by
        refine sup_le (sup_le le_sup_left ?_) le_sup_right
        rw [hOY]; exact inf_le_right.trans le_sup_right

private theorem commutator_le_of_cover {K J O : Subgroup G}
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hO : O ≤ K) (hcov : J ⊔ O = K) {C : Set G}
    (hC : ∀ c ∈ C, c ∈ Subgroup.normalizer (O : Set G))
    (hJ : ∀ j ∈ J, ∀ c ∈ C, ⁅j, c⁆ ∈ O) : ∀ l ∈ K, ∀ c ∈ C, ⁅l, c⁆ ∈ O := by
  let S : Subgroup G :=
    { carrier := {l | l ∈ K ∧ ∀ c ∈ C, ⁅l, c⁆ ∈ O}
      one_mem' := ⟨K.one_mem, fun c _ => by
        rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, hLa⟩ ⟨hb, hLb⟩
        refine ⟨K.mul_mem ha hb, fun c hc => ?_⟩
        have e : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        refine Subgroup.mul_mem _ ?_ (hLa c hc)
        simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.1 (hKO ha) _).1 (hLb c hc)
      inv_mem' := by
        rintro a ⟨ha, hLa⟩
        refine ⟨K.inv_mem ha, fun c hc => ?_⟩
        have e : ⁅a⁻¹, c⁆ = a⁻¹ * (⁅a, c⁆)⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        simpa [mul_assoc] using
          (Subgroup.mem_normalizer_iff.1 (hKO (K.inv_mem ha)) _).1 (O.inv_mem (hLa c hc)) }
  have hJS : J ≤ S := fun j hj => ⟨(le_sup_left.trans hcov.le : J ≤ K) hj, hJ j hj⟩
  have hOS : O ≤ S := fun o ho => ⟨hO ho, fun c hc => by
    have h1 : c * o⁻¹ * c⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hC c hc) _).1 (O.inv_mem ho)
    have : ⁅o, c⁆ = o * (c * o⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]; exact Subgroup.mul_mem _ ho h1⟩
  have hKS : K ≤ S := by rw [← hcov]; exact sup_le hJS hOS
  exact fun l hl c hc => (hKS hl).2 c hc

theorem le_centModSubgroup_of_cover {p : ℕ} {D Jc J : Subgroup G}
    (hJc : J ≤ Jc) (hD : D ≤ Subgroup.normalizer (Jc : Set G))
    (hJD : J ≤ Subgroup.centralizer (D : Set G)) (hcov : J ⊔ GLAPPrimeCoreOf p Jc = Jc) :
    D ≤ centModSubgroup p Jc := by
  intro d hd
  refine ⟨hD hd, fun l hl => ?_⟩
  refine commutator_le_of_cover (K := Jc) (J := J) (O := GLAPPrimeCoreOf p Jc) (C := (D : Set G))
    (le_normalizer_glaPPrimeCoreOf p Jc) (Subgroup.map_subtype_le _) hcov
    (fun c hc => normalizer_le_normalizer_glaPPrimeCoreOf p Jc (hD hc))
    (fun j hj c hc => ?_) l hl d hd
  have : ⁅j, c⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 (hJD hj) c hc).symm
  rw [this]; exact Subgroup.one_mem _


private theorem le_glaPPrimeCoreOf_of_normal {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p K := by
  haveI hn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hle : N.subgroupOf K ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hn, hcard ▸ hcop⟩
  intro n hn'
  exact ⟨⟨n, hNK hn'⟩, hle hn', rfl⟩

theorem centMod_of_le_cen {p : ℕ} (hp : p.Prime) {J J' : Subgroup G} (hJJ' : J ≤ J') {e : G}
    (he : e ∈ Subgroup.normalizer (J : Set G)) (hc : CentMod p J' e) : CentMod p J e := by
  rw [centMod_iff] at hc ⊢
  refine ⟨he, fun l hl => ?_⟩
  have h1 : ⁅l, e⁆ ∈ GLAPPrimeCoreOf p J' := hc.2 l (hJJ' hl)
  have h2 : ⁅l, e⁆ ∈ J := by
    have : ⁅l, e⁆ = l * (e * l⁻¹ * e⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    refine J.mul_mem hl ?_
    exact (Subgroup.mem_normalizer_iff.1 he _).1 (J.inv_mem hl)
  have hN : (J ⊓ GLAPPrimeCoreOf p J') ≤ GLAPPrimeCoreOf p J := by
    refine le_glaPPrimeCoreOf_of_normal inf_le_left ?_ ?_
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hgJ' : g ∈ Subgroup.normalizer (GLAPPrimeCoreOf p J' : Set G) :=
        normalizer_le_normalizer_glaPPrimeCoreOf p J' (Subgroup.le_normalizer (hJJ' hg))
      have hgJ : g ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hg
      simp only [Subgroup.mem_inf]
      exact and_congr ((Subgroup.mem_normalizer_iff.1 hgJ) x) ((Subgroup.mem_normalizer_iff.1 hgJ') x)
    · haveI : Fact p.Prime := ⟨hp⟩
      have hcopO : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p J')) := by
        unfold GLAPPrimeCoreOf
        rw [Subgroup.card_map_of_injective J'.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hcopO
  exact hN ⟨h2, h1⟩

theorem glaPPrimeCoreOf_eq_inf_of_cover {p : ℕ} (hp : p.Prime) {X K J : Subgroup G}
    (hK : GLAPComponent p X K) (hJK : J ≤ K) (hcov : J ⊔ GLAPPrimeCoreOf p K = K) :
    GLAPPrimeCoreOf p J = J ⊓ GLAPPrimeCoreOf p K := by
  exact (cover_facts hp hJK hcov).1

theorem nonempty_pQuot_of_cover {p : ℕ} (hp : p.Prime) {X K J : Subgroup G}
    (hK : GLAPComponent p X K) (hJK : J ≤ K) (hcov : J ⊔ GLAPPrimeCoreOf p K = K) :
    Nonempty (PQuot p J ≃* PQuot p K) := by
  exact (cover_facts hp hJK hcov).2

theorem centMod_of_cover_le {p : ℕ} (hp : p.Prime) {X K J : Subgroup G} (hK : GLAPComponent p X K)
    (hJK : J ≤ K) (hcov : J ⊔ GLAPPrimeCoreOf p K = K) {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgJ : g ∈ Subgroup.normalizer (J : Set G))
    (hg : CentMod p J g) : CentMod p K g := by
  rw [centMod_iff] at hg ⊢
  refine ⟨hgK, fun l hl => ?_⟩
  have hOJ : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p K := by
    rw [(cover_facts hp hJK hcov).1]; exact inf_le_right
  exact commutator_le_of_cover (K := K) (J := J) (O := GLAPPrimeCoreOf p K) (C := ({g} : Set G))
    (le_normalizer_glaPPrimeCoreOf p K) (Subgroup.map_subtype_le _) hcov
    (fun c hc => by
      rw [Set.mem_singleton_iff] at hc
      exact hc ▸ normalizer_le_normalizer_glaPPrimeCoreOf p K hgK)
    (fun j hj c hc => by
      rw [Set.mem_singleton_iff] at hc
      exact hc ▸ hOJ (hg.2 j hj)) l hl g rfl

end S3

end CFSG.LocalAnalysis.GLTheoremA
