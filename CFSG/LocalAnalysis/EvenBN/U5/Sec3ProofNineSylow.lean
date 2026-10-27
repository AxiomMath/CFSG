module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Four
public import CFSG.LocalAnalysis.EvenBN.U5.ModelThree
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

def S39a1TI (J : Type*) [Group J] : Prop :=
  ∀ P Q : Subgroup J, IsSylowOf 2 P ⊤ → IsSylowOf 2 Q ⊤ → P ≠ Q → P ⊓ Q = ⊥

theorem s39a1_card_inf_ker_mul {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B)
    (W : Subgroup A) :
    Nat.card W = Nat.card (W ⊓ φ.ker : Subgroup A) * Nat.card (W.map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.domRestrict W)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h
  rw [← h]
  congr 1
  have h2 := Subgroup.card_subtype W (φ.ker.subgroupOf W)
  rw [Subgroup.subgroupOf_map_subtype, inf_comm] at h2
  exact h2.symm

theorem s39a1_le_of_normal_isSylowOf [Finite G] {K E S : Subgroup G} (hE : IsPGroup 2 E)
    (hEK : E ≤ K) (hN : K ≤ normalizer (E : Set G)) (hS : IsSylowOf 2 S K) : E ≤ S := by
  obtain ⟨Q, rfl⟩ := hS
  haveI : (E.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mpr hN
  have hEp : IsPGroup 2 (E.subgroupOf K) := hE.comap_subtype
  have h := hEp.le_sylow_of_normal Q
  intro x hx
  have hxK : x ∈ K := hEK hx
  have hx' : (⟨x, hxK⟩ : K) ∈ E.subgroupOf K := hx
  exact ⟨⟨x, hxK⟩, h hx', rfl⟩

theorem s39a1_isSylowOf_inf_of_complement [Finite G] {L E M S : Subgroup G} (hE : IsPGroup 2 E)
    (hL : L = E ⊔ M) (hN : L ≤ normalizer (E : Set G)) (hEM : E ⊓ M = ⊥)
    (hS : IsSylowOf 2 S L) : IsSylowOf 2 (S ⊓ M) M := by
  have hEL : E ≤ L := hL ▸ le_sup_left
  have hML : M ≤ normalizer (E : Set G) := (hL ▸ le_sup_right : M ≤ L).trans hN
  have hES : E ≤ S := s39a1_le_of_normal_isSylowOf hE hEL hN hS
  have hSL : S ≤ L := hS.le
  have hSE : S = E ⊔ (S ⊓ M) := by
    apply le_antisymm
    · intro s hs
      have hsL : s ∈ E ⊔ M := hL ▸ hSL hs
      obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hML hsL
      have hmS : m ∈ S := by
        have h1 : m = e⁻¹ * (e * m) := by group
        rw [h1]
        exact S.mul_mem (S.inv_mem (hES he)) hs
      exact Subgroup.mul_mem_sup he ⟨hmS, hm⟩
    · exact sup_le hES inf_le_left
  have hcardL : Nat.card L = Nat.card E * Nat.card M := by
    have h1 := Common.card_sup_mul_card_inf_eq hML
    rw [hEM, ← hL, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hcardS : Nat.card S = Nat.card E * Nat.card (S ⊓ M : Subgroup G) := by
    have hML' : S ⊓ M ≤ normalizer (E : Set G) := inf_le_right.trans hML
    have h1 := Common.card_sup_mul_card_inf_eq hML'
    have hbot : E ⊓ (S ⊓ M) = ⊥ := by
      apply le_bot_iff.mp
      calc E ⊓ (S ⊓ M) ≤ E ⊓ M := inf_le_inf_left _ inf_le_right
        _ = ⊥ := hEM
    rw [hbot, Subgroup.card_bot, mul_one, ← hSE] at h1
    exact h1
  obtain ⟨a, ha⟩ := hE.exists_card_eq
  have hM0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card L).factorization 2 = a + (Nat.card M).factorization 2 := by
    rw [hcardL, ha, Nat.factorization_mul (by positivity) hM0]
    simp [Nat.Prime.factorization_pow Nat.prime_two]
  have hSM : Nat.card (S ⊓ M : Subgroup G) = 2 ^ (Nat.card M).factorization 2 := by
    have h1 := hS.card_eq
    rw [hcardS, hfac, ha, pow_add] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ a) h1
  exact CFSG.ABGLocalTools.isSylowOf_of_card inf_le_right hSM

theorem s39a1_lift [Finite G] {M N S : Subgroup G} (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G))
    (hSM : S ≤ normalizer (M : Set G)) (hSN : S ≤ normalizer (N : Set G)) (hM : IsPGroup 2 M)
    (hS : Odd (Nat.card S)) {m : G} (hm : m ∈ M) (hfix : ∀ s ∈ S, m⁻¹ * (s * m * s⁻¹) ∈ N) :
    ∃ c ∈ M ⊓ centralizer (S : Set G), ∃ n ∈ N, m = c * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable M := by
    have := hM.isNilpotent
    infer_instance
  have hcop : (Nat.card S).Coprime (Nat.card M) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hM
    rw [hk]
    exact Nat.Coprime.pow_right _ (Odd.coprime_two_right hS)
  exact Common.exists_mem_inf_centralizer_mul_of_coprime hNM hMN hSM hSN hsolv hcop hm hfix

theorem s39a1_ebn_eq_one {X : Type*} [Group X] [Finite X] {D D₀ Y : Subgroup X}
    (hD₀ : D₀ ≤ D) (hs : IsSimpleGroup D₀) (hna : ∃ x y : D₀, x * y ≠ y * x)
    (hY : IsPGroup 2 Y) (hDY : D ≤ normalizer (Y : Set X)) {c : X} (hcY : c ∈ Y)
    (hcD : c ∈ D₀) : c = 1 := by
  haveI := hs
  have hN : (Y.subgroupOf D₀).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : X) ∈ normalizer (Y : Set X) := hDY (hD₀ g.2)
    simpa using (mem_set_normalizer_iff.mp hg n).mp hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.subgroupOf D₀) with h | h
  · exact Subgroup.disjoint_def.mp (Subgroup.subgroupOf_eq_bot.mp h) hcY hcD
  · exfalso
    have hp : IsPGroup 2 D₀ := hY.to_le (Subgroup.subgroupOf_eq_top.mp h)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent D₀ := hp.isNilpotent
    have htop : center D₀ = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D₀)).resolve_left
        (Group.IsNilpotent.center_ne_bot D₀)
    obtain ⟨x, y, hxy⟩ := hna
    have hy : y ∈ center D₀ := htop ▸ mem_top y
    exact hxy (Subgroup.mem_center_iff.mp hy x)

theorem s39a1_eq_bot_of_normalizes {X : Type*} [Group X] [Finite X] {D D₁ D₂ : Subgroup X}
    [D.Normal] (hD : D₁ ⊔ D₂ = D) (h12 : ⁅D₁, D₂⁆ = ⊥) (hs₁ : IsSimpleGroup D₁)
    (hna₁ : ∃ x y : D₁, x * y ≠ y * x) (hs₂ : IsSimpleGroup D₂)
    (hna₂ : ∃ x y : D₂, x * y ≠ y * x) (hC : centralizer (D : Set X) = ⊥) {Y : Subgroup X}
    (hY : IsPGroup 2 Y) (hDY : D ≤ normalizer (Y : Set X)) : Y = ⊥ := by
  have hDle₁ : D₁ ≤ D := hD ▸ le_sup_left
  have hDle₂ : D₂ ≤ D := hD ▸ le_sup_right
  have hc12 : D₁ ≤ centralizer (D₂ : Set X) := commutator_eq_bot_iff_le_centralizer.mp h12
  have hc21 : D₂ ≤ centralizer (D₁ : Set X) := le_centralizer_iff.mp hc12
  have hN₁ : D ≤ normalizer (D₁ : Set X) := by
    rw [← hD]; exact sup_le le_normalizer (hc21.trans (centralizer_le_normalizer _))
  have hN₂ : D ≤ normalizer (D₂ : Set X) := by
    rw [← hD]; exact sup_le (hc12.trans (centralizer_le_normalizer _)) le_normalizer
  have hcY : ∀ y ∈ Y, ∀ d ∈ D, y * d * y⁻¹ * d⁻¹ ∈ Y := by
    intro y hy d hd
    have h1 : d * y⁻¹ * d⁻¹ ∈ Y :=
      (mem_set_normalizer_iff.mp (hDY hd) y⁻¹).mp (inv_mem hy)
    have h2 : y * d * y⁻¹ * d⁻¹ = y * (d * y⁻¹ * d⁻¹) := by group
    rw [h2]
    exact mul_mem hy h1
  have hW : ∀ w ∈ Y, w ∈ D → w = 1 := by
    intro w hwY hwD
    have hcomm : ∀ D₀ : Subgroup X, D₀ ≤ D → D ≤ normalizer (D₀ : Set X) →
        IsSimpleGroup D₀ → (∃ x y : D₀, x * y ≠ y * x) → D₀ ≤ centralizer ({w} : Set X) := by
      intro D₀ hD₀ hN hs hna d hd
      rw [mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      have hcD : w * d * w⁻¹ * d⁻¹ ∈ D₀ :=
        mul_mem ((mem_set_normalizer_iff.mp (hN hwD) d).mp hd) (inv_mem hd)
      have h1 := s39a1_ebn_eq_one hD₀ hs hna hY hDY (hcY w hwY d (hD₀ hd)) hcD
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hle : D ≤ centralizer ({w} : Set X) := by
      rw [← hD]
      exact sup_le (hcomm D₁ hDle₁ hN₁ hs₁ hna₁) (hcomm D₂ hDle₂ hN₂ hs₂ hna₂)
    have hwC : w ∈ centralizer (D : Set X) := by
      rw [mem_centralizer_iff]
      intro d hd
      exact ((mem_centralizer_iff.mp (hle hd)) w (Set.mem_singleton w)).symm
    rw [hC] at hwC
    exact hwC
  rw [eq_bot_iff]
  intro y hy
  have hyC : y ∈ centralizer (D : Set X) := by
    rw [mem_centralizer_iff]
    intro d hd
    have hcD : y * d * y⁻¹ * d⁻¹ ∈ D := mul_mem (Subgroup.Normal.conj_mem inferInstance d hd y)
      (inv_mem hd)
    have h1 := hW _ (hcY y hy d hd) hcD
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [hC] at hyC
  exact hyC

theorem s39a1_lop_isSylowOf_top_iff {G : Type*} [Group G] [Finite G] {P : Subgroup G} :
    IsSylowOf 2 P ⊤ ↔ IsPGroup 2 P ∧ ¬ 2 ∣ P.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
  exact ⟨fun h => h.2, fun h => ⟨le_top, h⟩⟩

theorem s39a1_lop_map_isSylowOf {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) {P : Subgroup G} (hP : IsSylowOf 2 P ⊤) :
    IsSylowOf 2 (P.map f) ⊤ := by
  rw [s39a1_lop_isSylowOf_top_iff] at hP ⊢
  exact ⟨hP.1.map f, fun h => hP.2 (h.trans (P.index_map_dvd hf))⟩

theorem s39a1_le_of_prod {J : Type*} [Group J] [Finite J] (hTI : S39a1TI J)
    {R Q : Subgroup (J × J)} (hR : IsSylowOf 2 R ⊤) (hQ : IsPGroup 2 Q) {j : J} (hj : j ≠ 1)
    (hjQ : (j, j) ∈ Q) (hjR : (j, j) ∈ R) : Q ≤ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ f : J × J →* J, Function.Surjective f → f (j, j) = j → Q.map f ≤ R.map f := by
    intro f hf hfj
    have hRf : IsSylowOf 2 (R.map f) ⊤ := s39a1_lop_map_isSylowOf f hf hR
    obtain ⟨P, hP⟩ := (hQ.map f).exists_le_sylow
    have hPs : IsSylowOf 2 (P : Subgroup J) ⊤ :=
      s39a1_lop_isSylowOf_top_iff.mpr ⟨P.isPGroup', P.not_dvd_index⟩
    by_contra hne
    have hPR : (P : Subgroup J) ≠ R.map f := fun h => hne (h ▸ hP)
    have hbot := hTI _ _ hPs hRf hPR
    have hjPR : j ∈ (P : Subgroup J) ⊓ R.map f := ⟨hP ⟨(j, j), hjQ, hfj⟩, ⟨(j, j), hjR, hfj⟩⟩
    rw [hbot, Subgroup.mem_bot] at hjPR
    exact hj hjPR
  have h1 := key (MonoidHom.fst J J) Prod.fst_surjective rfl
  have h2 := key (MonoidHom.snd J J) Prod.snd_surjective rfl
  set R' : Subgroup (J × J) := (R.map (MonoidHom.fst J J)).prod (R.map (MonoidHom.snd J J))
    with hR'
  have hRR' : R ≤ R' := fun x hx => Subgroup.mem_prod.mpr ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hQR' : Q ≤ R' := fun x hx => Subgroup.mem_prod.mpr ⟨h1 ⟨x, hx, rfl⟩, h2 ⟨x, hx, rfl⟩⟩
  have hR'p : IsPGroup 2 R' := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hR.isPGroup.map (MonoidHom.fst J J))
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hR.isPGroup.map (MonoidHom.snd J J))
    refine IsPGroup.of_card (n := a + b) ?_
    rw [hR', Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, ha, hb, pow_add]
  have hR'R := hR.eq_of_le hRR' le_top hR'p
  exact hR'R ▸ hQR'

theorem s39a1_tq_isSylowOf_top_iff {G : Type*} [Group G] [Finite G] {P : Subgroup G} :
    IsSylowOf 2 P ⊤ ↔ IsPGroup 2 P ∧ ¬ 2 ∣ P.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
  exact ⟨fun h => h.2, fun h => ⟨le_top, h⟩⟩

theorem s39a1_tq_eq_one {G : Type*} [Group G] {a b c : G} (hbc : Commute b c)
    (habc : a = b * c) {m n : ℕ} (ha : a ^ 2 ^ m = 1) (hb : b ^ 2 ^ n = 1)
    (hc : Odd (orderOf c)) : c = 1 := by
  have ha' : a ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
  have hb' : b ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul', hb, one_pow]
  have h1 : c ^ 2 ^ (m + n) = 1 := by
    have e : a ^ 2 ^ (m + n) = b ^ 2 ^ (m + n) * c ^ 2 ^ (m + n) := by rw [habc, hbc.mul_pow]
    rw [ha', hb', one_mul] at e
    exact e.symm
  have hdvd : orderOf c ∣ 2 ^ (m + n) := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (orderOf c) (2 ^ (m + n)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hc)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem s39a1_ti_quot {X J : Type*} [Group X] [Finite X] [Group J] [Finite J] (hTI : S39a1TI X)
    (π : X →* J) (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, ∀ x : X, z * x = x * z)
    (hodd : Odd (Nat.card π.ker)) : S39a1TI J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P' Q' hP' hQ' hne
  rw [s39a1_tq_isSylowOf_top_iff] at hP' hQ'
  obtain ⟨P₀, hP₀⟩ := Sylow.mapSurjective_surjective hπ 2 (hP'.1.toSylow hP'.2)
  obtain ⟨Q₀, hQ₀⟩ := Sylow.mapSurjective_surjective hπ 2 (hQ'.1.toSylow hQ'.2)
  have hP₀' : (P₀ : Subgroup X).map π = P' := by
    have := congrArg (fun S : Sylow 2 J => (S : Subgroup J)) hP₀
    simpa using this
  have hQ₀' : (Q₀ : Subgroup X).map π = Q' := by
    have := congrArg (fun S : Sylow 2 J => (S : Subgroup J)) hQ₀
    simpa using this
  have hPQ : (P₀ : Subgroup X) ≠ Q₀ := fun h => hne (by rw [← hP₀', ← hQ₀', h])
  have hbot := hTI _ _ (s39a1_tq_isSylowOf_top_iff.mpr ⟨P₀.isPGroup', P₀.not_dvd_index⟩)
    (s39a1_tq_isSylowOf_top_iff.mpr ⟨Q₀.isPGroup', Q₀.not_dvd_index⟩) hPQ
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxQ⟩
  rw [← hP₀'] at hxP
  rw [← hQ₀'] at hxQ
  obtain ⟨p, hp, rfl⟩ := hxP
  obtain ⟨q, hq, hqp⟩ := hxQ
  have hz : q⁻¹ * p ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqp, inv_mul_cancel]
  have hzodd : Odd (orderOf (q⁻¹ * p)) := Odd.of_dvd_nat hodd (π.ker.orderOf_dvd_natCard hz)
  obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨p, hp⟩
  obtain ⟨n, hn⟩ := Q₀.isPGroup' ⟨q, hq⟩
  have hm' : p ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hn' : q ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hz1 : q⁻¹ * p = 1 :=
    s39a1_tq_eq_one (hker _ hz q).symm (mul_inv_cancel_left q p).symm hm' hn' hzodd
  rw [inv_mul_eq_one] at hz1
  have hpPQ : p ∈ (P₀ : Subgroup X) ⊓ Q₀ := ⟨hp, hz1 ▸ hq⟩
  rw [hbot, Subgroup.mem_bot] at hpPQ
  rw [hpPQ, map_one]
  exact one_mem _

theorem s39a1_tla_isSylowOf_top_iff {G : Type*} [Group G] [Finite G] {P : Subgroup G} :
    IsSylowOf 2 P ⊤ ↔ IsPGroup 2 P ∧ ¬ 2 ∣ P.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
  exact ⟨fun h => h.2, fun h => ⟨le_top, h⟩⟩

theorem s39a1_tla_eq_one {G : Type*} [Group G] {a b c : G} (hbc : Commute b c)
    (habc : a = b * c) {m n : ℕ} (ha : a ^ 2 ^ m = 1) (hb : b ^ 2 ^ n = 1)
    (hc : Odd (orderOf c)) : c = 1 := by
  have ha' : a ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
  have hb' : b ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul', hb, one_pow]
  have h1 : c ^ 2 ^ (m + n) = 1 := by
    have e : a ^ 2 ^ (m + n) = b ^ 2 ^ (m + n) * c ^ 2 ^ (m + n) := by rw [habc, hbc.mul_pow]
    rw [ha', hb', one_mul] at e
    exact e.symm
  have hdvd : orderOf c ∣ 2 ^ (m + n) := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (orderOf c) (2 ^ (m + n)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hc)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem s39a1_ti_lift_abs {M J : Type*} [Group M] [Finite M] [Group J] [Finite J]
    (hTI : S39a1TI J) (φ : M →* J × J) (hφ : Function.Surjective φ)
    (hker : ∀ z ∈ φ.ker, (∀ x : M, z * x = x * z) ∧ Odd (orderOf z)) {R Q : Subgroup M}
    (hR : IsSylowOf 2 R ⊤) (hQ : IsPGroup 2 Q) {z : M} (hzQ : z ∈ Q) (hzR : z ∈ R) {j : J}
    (hj : j ≠ 1) (hzj : φ z = (j, j)) : Q ≤ R := by
  have hRφ : IsSylowOf 2 (R.map φ) ⊤ := by
    have hR' := s39a1_tla_isSylowOf_top_iff.mp hR
    exact s39a1_tla_isSylowOf_top_iff.mpr
      ⟨hR'.1.map φ, fun h => hR'.2 (h.trans (R.index_map_dvd hφ))⟩
  have hle : Q.map φ ≤ R.map φ :=
    s39a1_le_of_prod hTI hRφ (hQ.map φ) hj ⟨z, hzQ, hzj⟩ ⟨z, hzR, hzj⟩
  intro x hx
  obtain ⟨r, hr, hrx⟩ := hle ⟨x, hx, rfl⟩
  have hy : r⁻¹ * x ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrx, inv_mul_cancel]
  obtain ⟨hyc, hyo⟩ := hker _ hy
  obtain ⟨m, hm⟩ := hQ ⟨x, hx⟩
  obtain ⟨n, hn⟩ := hR.isPGroup ⟨r, hr⟩
  have hm' : x ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hn' : r ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hy1 : r⁻¹ * x = 1 :=
    s39a1_tla_eq_one (hyc r).symm (mul_inv_cancel_left r x).symm hm' hn' hyo
  rw [inv_mul_eq_one] at hy1
  exact hy1 ▸ hr

theorem s39a1_closure_facts {H N : Subgroup G} (hNH : N ≤ H) :
    N ≤ (normalClosure ((N.subgroupOf H : Subgroup H) : Set H)).map H.subtype ∧
    (normalClosure ((N.subgroupOf H : Subgroup H) : Set H)).map H.subtype ≤ H ∧
    H ≤ normalizer (((normalClosure ((N.subgroupOf H : Subgroup H) : Set H)).map
      H.subtype : Subgroup G) : Set G) := by
  have hTn : (normalClosure ((N.subgroupOf H : Subgroup H) : Set H)).Normal :=
    Subgroup.normalClosure_normal
  refine ⟨?_, Subgroup.map_subtype_le _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hNH hx⟩, Subgroup.subset_normalClosure hx, rfl⟩
  · rw [Subgroup.le_normalizer_iff]
    rintro h hh _ ⟨y, hy, rfl⟩
    exact ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hTn.conj_mem y hy ⟨h, hh⟩, by simp⟩

theorem s39a1_map_closure {H N : Subgroup G} (g : G) :
    ((normalClosure ((N.subgroupOf H : Subgroup H) : Set H)).map H.subtype).map
        (MulAut.conj g).toMonoidHom =
      (normalClosure (((N.map (MulAut.conj g).toMonoidHom).subgroupOf
        (H.map (MulAut.conj g).toMonoidHom) : Subgroup _) : Set _)).map
        (H.map (MulAut.conj g).toMonoidHom).subtype := by
  set c : G →* G := (MulAut.conj g).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hφs : Function.Surjective (c.subgroupMap H) := c.subgroupMap_surjective H
  have himg : (c.subgroupMap H) '' ((N.subgroupOf H : Subgroup H) : Set H) =
      (((N.map c).subgroupOf (H.map c) : Subgroup _) : Set _) := by
    ext y
    obtain ⟨x, rfl⟩ := hφs y
    constructor
    · rintro ⟨x', hx', hx'eq⟩
      have hxx : x' = x := c.subgroupMap_injective H hcinj hx'eq
      subst hxx
      exact ⟨x', hx', rfl⟩
    · intro hy
      refine ⟨x, ?_, rfl⟩
      obtain ⟨n, hn, hne⟩ := hy
      have hnx : n = (x : G) := hcinj hne
      show (x : G) ∈ N
      rw [← hnx]
      exact hn
  have hNC := Subgroup.map_normalClosure ((N.subgroupOf H : Subgroup H) : Set H)
    (c.subgroupMap H) hφs
  rw [himg] at hNC
  rw [← hNC, Subgroup.map_map, Subgroup.map_map]
  rfl

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

abbrev s39a1H (d : Data G h) : Subgroup G := centralizer (d.I₂ : Set G)

abbrev s39a1O (d : Data G h) : Subgroup (s39a1H d) := standardComponentOddCore (s39a1H d)

abbrev s39a1θ (d : Data G h) : s39a1H d →* s39a1H d ⧸ s39a1O d :=
  QuotientGroup.mk' (s39a1O d)

abbrev s39a1Λ (d : Data G h) : Subgroup (s39a1H d ⧸ s39a1O d) :=
  (d.M₂.subgroupOf (s39a1H d)).map (s39a1θ d)

abbrev s39a1J (d : Data G h) : Subgroup (s39a1H d ⧸ s39a1O d) :=
  (d.N₂.subgroupOf (s39a1H d)).map (s39a1θ d)

theorem s39a1_N₂_le_M₂ (d : Data G h) : d.N₂ ≤ d.M₂ :=
  (s39a1_closure_facts d.N₂_le_centralizer_I₂).1

theorem s39a1_M₂_le_centralizer (d : Data G h) : d.M₂ ≤ centralizer (d.I₂ : Set G) :=
  (s39a1_closure_facts d.N₂_le_centralizer_I₂).2.1

theorem s39a1_centralizer_le_normalizer_M₂ (d : Data G h) :
    centralizer (d.I₂ : Set G) ≤ normalizer (d.M₂ : Set G) :=
  (s39a1_closure_facts d.N₂_le_centralizer_I₂).2.2

theorem s39a1_I₅_eq (d : Data G h) : d.I₅ = d.I₂.map (MulAut.conj d.r).toMonoidHom := by
  show d.pull (I₅sub h) = _
  rw [I₅sub_eq_conj]
  exact d.pull_conj _ _

theorem s39a1_N₅_le_centralizer_I₅ (d : Data G h) : d.N₅ ≤ centralizer (d.I₅ : Set G) := by
  rw [d.N₅_eq, s39a1_I₅_eq]
  rintro _ ⟨n, hn, rfl⟩
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨i, hi, rfl⟩
  have hcomm := mem_centralizer_iff.1 (d.N₂_le_centralizer_I₂ hn) i hi
  rw [← map_mul, ← map_mul, hcomm]

theorem s39a1_N₅_le_M₅ (d : Data G h) : d.N₅ ≤ d.M₅ :=
  (s39a1_closure_facts (s39a1_N₅_le_centralizer_I₅ d)).1

theorem s39a1_M₅_le_centralizer (d : Data G h) : d.M₅ ≤ centralizer (d.I₅ : Set G) :=
  (s39a1_closure_facts (s39a1_N₅_le_centralizer_I₅ d)).2.1

theorem s39a1_centralizer_le_normalizer_M₅ (d : Data G h) :
    centralizer (d.I₅ : Set G) ≤ normalizer (d.M₅ : Set G) :=
  (s39a1_closure_facts (s39a1_N₅_le_centralizer_I₅ d)).2.2

theorem Hyp.s39a1_isPGroup_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    IsPGroup 2 d.E := by
  have hc := hd.card_E hGMS
  rw [← pow_mul] at hc
  exact IsPGroup.of_card hc

theorem Hyp.s39a1_I_le_normalizer_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.I ≤ normalizer (d.E : Set G) := by
  exact hd.I_le_normalizer_B₄.trans (hd.normalizer_B₄_le_normalizer_E hGMS)

theorem Hyp.s39a1_I_le_normalizer_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : d.I ≤ normalizer (d.B₆ : Set G) ∧ d.I ≤ normalizer (d.D : Set G) := by
  have hB₆ : d.I ≤ normalizer (d.B₆ : Set G) := fun i hi => by
    have h1 := hd.I_le_normalizer_B₁ hi
    have hB₃ : i ∈ normalizer (d.B₃ : Set G) :=
      Common.mem_normalizer_sup (mem_normalizer_zpowers_t h1.2)
        (hd.normalizer_B₁_inf_le_normalizer_A₃ h1)
    exact d.normalizer_le_normalizer_B₆
      (Common.mem_normalizer_sup (hd.I_le_normalizer_F hGMS hi) hB₃)
  exact ⟨hB₆, fun i hi => mem_normalizer_D (hB₆ hi)
    (mem_normalizer_of_mem_centralizer' (d.I_le_centralizer_I₁ hi))⟩

omit [Finite G] in
theorem s39a1_conj_r_centralizer_map (g : G) (X : Subgroup G) :
    centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, mem_centralizer_iff.2 fun x hx => ?_, ?_⟩
    · have h1 : g * x * g⁻¹ * y = y * (g * x * g⁻¹) :=
        mem_centralizer_iff.1 hy _ ⟨x, hx, rfl⟩
      calc x * (g⁻¹ * y * g) = g⁻¹ * (g * x * g⁻¹ * y) * g := by group
        _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * y * g * x := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨z, hz, rfl⟩
    refine mem_centralizer_iff.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x * z = z * x := mem_centralizer_iff.1 hz x hx
    rw [← map_mul, ← map_mul, h1]

theorem Hyp.s39a1_conj_r (hd : d.Hyp) :
    d.M₅ = d.M₂.map (MulAut.conj d.r).toMonoidHom ∧
    centralizer (d.I₅ : Set G) = (centralizer (d.I₂ : Set G)).map (MulAut.conj d.r).toMonoidHom ∧
    d.N₅ = d.N₂.map (MulAut.conj d.r).toMonoidHom := by
  have hC : centralizer (d.I₅ : Set G) =
      (centralizer (d.I₂ : Set G)).map (MulAut.conj d.r).toMonoidHom := by
    rw [s39a1_I₅_eq d]
    exact s39a1_conj_r_centralizer_map d.r d.I₂
  refine ⟨?_, hC, d.N₅_eq⟩
  rw [Data.M₂, s39a1_map_closure, Data.M₅, ← hC, ← d.N₅_eq]

theorem Hyp.s39a1_map_conj_r_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.D.map (MulAut.conj d.r).toMonoidHom = d.D :=
  map_conj_eq_of_mem_normalizer (hd.N₁_le_normalizer_D d.r_mem_N₁)

theorem s39a1_J_le_Λ (d : Data G h) : s39a1J d ≤ s39a1Λ d :=
  map_mono (subgroupOf_mono _ (s39a1_N₂_le_M₂ d))

theorem ProductCaseHyp.s39a1_Λ_normal (hp : d.ProductCaseHyp) : (s39a1Λ d).Normal := by
  have hΛ : s39a1Λ d = CFSG.layer (s39a1H d ⧸ s39a1O d) := (hp.hyp.sec3_3_two hp.gms).2
  have hc : (CFSG.layer (s39a1H d ⧸ s39a1O d)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  rw [hΛ]
  infer_instance

theorem ProductCaseHyp.s39a1_layer_data (hp : d.ProductCaseHyp) :
    centralizer ((s39a1Λ d : Subgroup (s39a1H d ⧸ s39a1O d)) : Set (s39a1H d ⧸ s39a1O d)) = ⊥ ∧
    (∃ D₁ D₂ : Subgroup (s39a1H d ⧸ s39a1O d), D₁ ⊔ D₂ = s39a1Λ d ∧ ⁅D₁, D₂⁆ = ⊥ ∧
      IsSimpleGroup D₁ ∧ (∃ x y : D₁, x * y ≠ y * x) ∧
      IsSimpleGroup D₂ ∧ (∃ x y : D₂, x * y ≠ y * x)) ∧
    (∃ ψ : s39a1Λ d ≃* s39a1J d × s39a1J d,
      ∀ (j : s39a1H d ⧸ s39a1O d) (hjJ : j ∈ s39a1J d) (hjΛ : j ∈ s39a1Λ d),
        ψ ⟨j, hjΛ⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩)) := by
  obtain ⟨hout, hΛ⟩ := hp.hyp.sec3_3_two hp.gms
  obtain ⟨-, -, -, hDE, hC, halt, -⟩ := hout.1
  have hDΛ : normalClosure ((s39a1J d : Subgroup (s39a1H d ⧸ s39a1O d)) :
      Set (s39a1H d ⧸ s39a1O d)) = s39a1Λ d := hDE.trans hΛ.symm
  rcases halt with ⟨⟨hDs, -⟩, -⟩ | ⟨⟨D₁, D₂, -, -, -, hs₁, hna₁, hs₂, hna₂, hsup, -, h12, -, -, ψ,
    hψ, -⟩, -⟩
  · exact absurd (show IsSimpleGroup (CFSG.layer (s39a1H d ⧸ s39a1O d)) from hDE ▸ hDs) hp.caseB
  · refine ⟨hDΛ ▸ hC, ⟨D₁, D₂, hsup.trans hDΛ, h12, hs₁, hna₁, hs₂, hna₂⟩,
      (MulEquiv.subgroupCongr hDΛ.symm).trans ψ, fun j hjJ hjΛ => ?_⟩
    exact hψ j hjJ (hDΛ.symm ▸ hjΛ)

theorem ProductCaseHyp.s39a1_eq_bot (hp : d.ProductCaseHyp) {Y : Subgroup (s39a1H d ⧸ s39a1O d)}
    (hY : IsPGroup 2 Y) (hΛY : s39a1Λ d ≤ normalizer (Y : Set (s39a1H d ⧸ s39a1O d))) :
    Y = ⊥ := by
  haveI := hp.s39a1_Λ_normal
  obtain ⟨hC, ⟨D₁, D₂, hsup, h12, hs₁, hna₁, hs₂, hna₂⟩, -⟩ := hp.s39a1_layer_data
  exact s39a1_eq_bot_of_normalizes hsup h12 hs₁ hna₁ hs₂ hna₂ hC hY hΛY

theorem ProductCaseHyp.s39a1_E_inf_H_eq_bot (hp : d.ProductCaseHyp) (hL₂ : d.L₂ = d.E ⊔ d.M₂) :
    d.E ⊓ centralizer (d.I₂ : Set G) = ⊥ := by
  have hE2 : IsPGroup 2 d.E := Hyp.s39a1_isPGroup_E hp.gms hp.hyp
  have hOodd : Odd (Nat.card (s39a1O d)) := GMSK.odd_card_standardComponentOddCore _
  have hMN : d.M₂ ≤ normalizer (d.E : Set G) :=
    (le_sup_right.trans hL₂.symm.le).trans d.L₂_le_normalizer_E
  set Y' : Subgroup (s39a1H d) := d.E.subgroupOf (s39a1H d) with hY'
  have hY'2 : IsPGroup 2 Y' := hE2.comap_subtype
  have hMY : d.M₂.subgroupOf (s39a1H d) ≤ normalizer (Y' : Set (s39a1H d)) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro y
    rw [hY', mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact (mem_normalizer_iff.1 (hMN (mem_subgroupOf.1 hm))) y
  have hYb : Y'.map (s39a1θ d) = ⊥ :=
    hp.s39a1_eq_bot (hY'2.map _) ((map_mono hMY).trans (le_normalizer_map _))
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxH⟩
  rw [mem_bot]
  have hxY : (⟨x, hxH⟩ : s39a1H d) ∈ Y' := mem_subgroupOf.2 hxE
  have h1 : s39a1θ d ⟨x, hxH⟩ = 1 := by
    have : s39a1θ d ⟨x, hxH⟩ ∈ Y'.map (s39a1θ d) := mem_map_of_mem _ hxY
    rwa [hYb, mem_bot] at this
  have hxO : (⟨x, hxH⟩ : s39a1H d) ∈ s39a1O d := (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨k, hk⟩ := hE2 ⟨x, hxE⟩
  have hk' : (⟨x, hxH⟩ : s39a1H d) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  simpa using congrArg Subtype.val (eq_one_of_mem_of_pow_two_pow hOodd hxO hk')

theorem ProductCaseHyp.s39a1_sylow₂ (hp : d.ProductCaseHyp) (hL₂ : d.L₂ = d.E ⊔ d.M₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) :
    S ⊓ centralizer (d.I₂ : Set G) = S ⊓ d.M₂ ∧ IsSylowOf 2 (S ⊓ d.M₂) d.M₂ := by
  have hE2 : IsPGroup 2 d.E := Hyp.s39a1_isPGroup_E hp.gms hp.hyp
  have hEH := hp.s39a1_E_inf_H_eq_bot hL₂
  have hMH : d.M₂ ≤ centralizer (d.I₂ : Set G) := s39a1_M₂_le_centralizer d
  have hEM : d.E ⊓ d.M₂ = ⊥ := eq_bot_iff.2 ((inf_le_inf_left _ hMH).trans hEH.le)
  have hMN : d.M₂ ≤ normalizer (d.E : Set G) :=
    (le_sup_right.trans hL₂.symm.le).trans d.L₂_le_normalizer_E
  refine ⟨le_antisymm ?_ (inf_le_inf_left _ hMH),
    s39a1_isSylowOf_inf_of_complement hE2 hL₂ d.L₂_le_normalizer_E hEM hS⟩
  rintro s ⟨hsS, hsH⟩
  refine ⟨hsS, ?_⟩
  have hsL : s ∈ d.E ⊔ d.M₂ := hL₂ ▸ hS.le hsS
  obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hMN hsL
  have heH : e ∈ centralizer (d.I₂ : Set G) := by
    have e' : e = e * m * m⁻¹ := by group
    rw [e']
    exact mul_mem hsH (inv_mem (hMH hm))
  have he1 : e = 1 := by
    have : e ∈ d.E ⊓ centralizer (d.I₂ : Set G) := ⟨he, heH⟩
    rwa [hEH, mem_bot] at this
  rw [he1, one_mul]
  exact hm

open scoped commutatorElement in
theorem s39a1_odd_normal_le_center_or_eq_top {X : Type*} [Group X]
    (hX : CFSG.Open.IsQuasisimple X) (Y : Subgroup X) [hYn : Y.Normal] :
    Y ≤ center X ∨ Y = ⊤ := by
  haveI : IsSimpleGroup (X ⧸ center X) := hX.2
  haveI : (Y.map (QuotientGroup.mk' (center X))).Normal :=
    hYn.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.map (QuotientGroup.mk' (center X))) with
    hb | ht
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
  · right
    have hdec : ∀ x : X, ∃ z ∈ center X, QuotientGroup.mk' Y x = QuotientGroup.mk' Y z := by
      intro x
      have hx : QuotientGroup.mk' (center X) x ∈ Y.map (QuotientGroup.mk' (center X)) := by
        rw [ht]; exact mem_top _
      obtain ⟨y, hy, hyx⟩ := hx
      have hz : y⁻¹ * x ∈ center X := by
        rw [← QuotientGroup.ker_mk' (center X), MonoidHom.mem_ker, map_mul, map_inv, hyx,
          inv_mul_cancel]
      refine ⟨y⁻¹ * x, hz, ?_⟩
      have hy1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff y).2 hy
      rw [map_mul, map_inv, hy1, inv_one, one_mul]
    have hcomm : commutator X ≤ Y := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun g1 _ g2 _ => ?_
      obtain ⟨z1, -, e1⟩ := hdec g1
      obtain ⟨z2, hz2, e2⟩ := hdec g2
      have hz12 : ⁅z1, z2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 hz2 z1)
      have h1 : QuotientGroup.mk' Y ⁅g1, g2⁆ = 1 := by
        rw [map_commutatorElement, e1, e2, ← map_commutatorElement, hz12, map_one]
      exact (QuotientGroup.eq_one_iff _).1 h1
    exact top_le_iff.1 (hX.1 ▸ hcomm)

open scoped commutatorElement in
theorem s39a1_odd_commutator_central_left {X : Type*} [Group X] {z : X} (hz : z ∈ center X)
    (x w : X) : ⁅z * x, w⁆ = ⁅x, w⁆ := by
  have h := Subgroup.mem_center_iff.1 hz (x * w * x⁻¹)
  calc ⁅z * x, w⁆ = z * (x * w * x⁻¹) * z⁻¹ * w⁻¹ := by group
    _ = x * w * x⁻¹ * w⁻¹ := by rw [← h, mul_inv_cancel_right]
    _ = ⁅x, w⁆ := (commutatorElement_def x w).symm

open scoped commutatorElement in
theorem s39a1_odd_commutator_central_right {X : Type*} [Group X] {z : X} (hz : z ∈ center X)
    (x w : X) : ⁅x, z * w⁆ = ⁅x, w⁆ := by
  rw [← commutatorElement_inv, s39a1_odd_commutator_central_left hz, commutatorElement_inv]

open scoped commutatorElement in
theorem s39a1_odd_eq_of_perfect {X : Type*} [Group X] (hX : commutator X = ⊤) (ψ : X →* X)
    (hψ : ∀ x, ψ x * x⁻¹ ∈ center X) (x : X) : ψ x = x := by
  have key : ∀ a b : X, ψ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    have ha : ψ a = ψ a * a⁻¹ * a := by rw [inv_mul_cancel_right]
    have hb : ψ b = ψ b * b⁻¹ * b := by rw [inv_mul_cancel_right]
    rw [map_commutatorElement, ha, hb, s39a1_odd_commutator_central_left (hψ a),
      s39a1_odd_commutator_central_right (hψ b)]
  have hle : commutator X ≤ MonoidHom.eqLocus ψ (MonoidHom.id X) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact key a b
  exact hle (hX ▸ mem_top x)

theorem s39a1_odd_A_facts (d : Data G h) :
    Odd (Nat.card ((s39a1O d).map (s39a1H d).subtype)) ∧
    (s39a1O d).map (s39a1H d).subtype ≤ s39a1H d ∧
    ∀ g ∈ s39a1H d, ∀ x ∈ (s39a1O d).map (s39a1H d).subtype,
      g * x * g⁻¹ ∈ (s39a1O d).map (s39a1H d).subtype := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (s39a1H d).subtype_injective]
    exact GMSK.odd_card_standardComponentOddCore _
  · rintro _ ⟨o, -, rfl⟩
    exact o.2
  · rintro g hg _ ⟨o, ho, rfl⟩
    exact ⟨⟨g, hg⟩ * o * ⟨g, hg⟩⁻¹,
      (GMSK.standardComponentOddCore_normal (s39a1H d)).conj_mem o ho ⟨g, hg⟩, rfl⟩

theorem s39a1_odd_dihedral (hp : d.CaseHyp) :
    ∃ b ∈ d.N₂, ∃ u ∈ centralizer (d.I₂ : Set G), b ≠ 1 ∧ b * b = 1 ∧ u * b = b * u ∧
      u⁻¹ * d.t * u = b * d.t := by
  have hd := hp.hyp
  have hGMS := hp.gms
  obtain ⟨v, hvV, hvt⟩ := hd.exists_V_not_comm_t
  obtain ⟨κ, hκ⟩ : ∃ κ : G, κ = v⁻¹ * d.t * v * d.t := ⟨_, rfl⟩
  have hκZ : κ ∈ d.Zp := by rw [hκ]; exact hd.cr_mem (hd.V_le_B₄ hvV)
  have hκV : κ ∈ d.V := hd.Zp_le_V hκZ
  have hκκ : κ * κ = 1 := hd.mul_self_eq_one_of_mem_V hGMS hκV
  have hvκ : v * κ = κ * v := hd.comm_of_mem_V hGMS hvV hκV
  have hκN₅ : κ ∈ d.N₅ := by
    have h5 := hd.Zp_le_C₅ hκZ
    rw [hd.P_inf_centralizer_I₅] at h5
    exact d.C₅_le_N₅ h5
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  have hκ1 : κ ≠ 1 := by
    intro e
    apply hvt
    calc d.t * v = v * (v⁻¹ * d.t * v * d.t) * d.t⁻¹ := by group
      _ = v * d.t := by rw [← hκ, e, mul_one, htinv]
  have hrL : d.r ∈ d.L := d.pull_le_L _ d.r_mem_N₁
  have hrt : d.r * d.t = d.t * d.r := hd.comm_t hrL
  have h1 : d.r⁻¹ * d.t * d.r = d.t := by
    calc d.r⁻¹ * d.t * d.r = d.r⁻¹ * (d.t * d.r) := by group
      _ = d.r⁻¹ * (d.r * d.t) := by rw [hrt]
      _ = d.t := by group
  have h2 : d.t * d.r⁻¹ * d.t = d.r⁻¹ := by
    calc d.t * d.r⁻¹ * d.t = d.r⁻¹ * (d.r * d.t) * d.r⁻¹ * d.t := by group
      _ = d.r⁻¹ * (d.t * d.r) * d.r⁻¹ * d.t := by rw [hrt]
      _ = d.r⁻¹ * (d.t * d.t) := by group
      _ = d.r⁻¹ := by rw [hd.t_mul_t, mul_one]
  refine ⟨d.r * κ * d.r⁻¹, d.conj_r_mem_N₂ hκN₅, d.r * v * d.r⁻¹,
    d.conj_r_mem_centralizer_I₂ (hd.V_le_centralizer_I₅ hvV), ?_, ?_, ?_, ?_⟩
  · intro hb
    apply hκ1
    calc κ = d.r⁻¹ * (d.r * κ * d.r⁻¹) * d.r := by group
      _ = 1 := by rw [hb]; group
  · calc d.r * κ * d.r⁻¹ * (d.r * κ * d.r⁻¹) = d.r * (κ * κ) * d.r⁻¹ := by group
      _ = 1 := by rw [hκκ]; group
  · calc d.r * v * d.r⁻¹ * (d.r * κ * d.r⁻¹) = d.r * (v * κ) * d.r⁻¹ := by group
      _ = d.r * (κ * v) * d.r⁻¹ := by rw [hvκ]
      _ = d.r * κ * d.r⁻¹ * (d.r * v * d.r⁻¹) := by group
  · calc (d.r * v * d.r⁻¹)⁻¹ * d.t * (d.r * v * d.r⁻¹)
        = d.r * v⁻¹ * (d.r⁻¹ * d.t * d.r) * v * d.r⁻¹ := by group
      _ = d.r * (v⁻¹ * d.t * v) * (d.t * d.r⁻¹ * d.t) := by rw [h1, h2]; group
      _ = d.r * κ * d.r⁻¹ * d.t := by rw [hκ]; group

theorem s39a1_odd_comm_N₂ (hp : d.CaseHyp) {c : G}
    (hcA : c ∈ (s39a1O d).map (s39a1H d).subtype) (hct : c * d.t = d.t * c) :
    ∀ n ∈ d.N₂, c * n = n * c := by
  have hd := hp.hyp
  obtain ⟨hAodd, hAH', hAH⟩ := s39a1_odd_A_facts d
  have hcH : c ∈ centralizer (d.I₂ : Set G) := hAH' hcA
  have hN₂H : d.N₂ ≤ centralizer (d.I₂ : Set G) := d.N₂_le_centralizer_I₂
  have hcN : ∀ n ∈ d.N₂, c * n * c⁻¹ ∈ d.N₂ := fun n hn =>
    hd.conj_mem_N₂ hcH (mem_centralizer_singleton_iff.2 hct) hn
  have hq : CFSG.Open.IsQuasisimple ↥d.N₂ :=
    (hd.quasisimple_lieModel_N₂ (X := ↥d.N₂) ⟨MulEquiv.refl _⟩).1
  set A := (s39a1O d).map (s39a1H d).subtype
  set Y : Subgroup ↥d.N₂ := A.subgroupOf d.N₂ with hY
  haveI hYn : Y.Normal := ⟨fun y hy n => by
    rw [hY, mem_subgroupOf] at hy ⊢
    exact hAH n (hN₂H n.2) y hy⟩
  have hYc : Y ≤ center ↥d.N₂ := by
    rcases s39a1_odd_normal_le_center_or_eq_top hq Y with hle | htop
    · exact hle
    · exfalso
      have hs : (⟨d.s, d.s_mem_N₂⟩ : ↥d.N₂) ∈ Y := by rw [htop]; exact mem_top _
      rw [hY, mem_subgroupOf] at hs
      have hs' : d.s ∈ A := hs
      have h2 : 2 ∣ Nat.card A := d.orderOf_s ▸ Subgroup.orderOf_dvd_natCard A hs'
      exact (Nat.not_even_iff_odd.2 hAodd) (even_iff_two_dvd.2 h2)
  let ψ : ↥d.N₂ →* ↥d.N₂ :=
    { toFun := fun n => ⟨c * n * c⁻¹, hcN n n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show c * ((x : G) * (y : G)) * c⁻¹ = c * (x : G) * c⁻¹ * (c * (y : G) * c⁻¹)
        group) }
  have hψ : ∀ x, ψ x * x⁻¹ ∈ center ↥d.N₂ := fun x => hYc (by
    rw [hY, mem_subgroupOf]
    show c * (x : G) * c⁻¹ * (x : G)⁻¹ ∈ A
    have hx : (x : G) * c⁻¹ * (x : G)⁻¹ ∈ A := hAH x (hN₂H x.2) c⁻¹ (A.inv_mem hcA)
    have e : c * (x : G) * c⁻¹ * (x : G)⁻¹ = c * ((x : G) * c⁻¹ * (x : G)⁻¹) := by group
    rw [e]
    exact A.mul_mem hcA hx)
  intro n hn
  have e := congrArg Subtype.val (s39a1_odd_eq_of_perfect hq.1 ψ hψ ⟨n, hn⟩)
  change c * n * c⁻¹ = n at e
  calc c * n = c * n * c⁻¹ * c := by group
    _ = n * c := by rw [e]

theorem CaseHyp.s39a1_odd (hp : d.CaseHyp) :
    ∀ a ∈ (s39a1O d).map (s39a1H d).subtype, ∀ m ∈ d.M₂, a * m = m * a := by
  have hd := hp.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAodd, -, hAH⟩ := s39a1_odd_A_facts d
  obtain ⟨b, hbN, u, huH, hb1, hbb, hub, hut⟩ := s39a1_odd_dihedral hp
  have hN₂H : d.N₂ ≤ centralizer (d.I₂ : Set G) := d.N₂_le_centralizer_I₂
  have hbL : b ∈ d.L := d.pull_le_L _ hbN
  have htb : d.t * b = b * d.t := (hd.comm_t hbL).symm
  have htH : d.t ∈ centralizer (d.I₂ : Set G) := hd.t_mem_centralizer_I₂
  set A := (s39a1O d).map (s39a1H d).subtype
  have hnorm : ∀ g ∈ centralizer (d.I₂ : Set G), g ∈ normalizer (A : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hAH g hg x hx, fun hx => ?_⟩
    have e : x = g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := by group
    rw [e]
    exact hAH g⁻¹ (inv_mem hg) _ hx
  have hbA : ∀ x ∈ A, b * x = x * b := by
    refine OddNormalCore.commute_of_four_group_centralizers (z := b) hAodd hd.t_mul_t hbb htb
      hd.t_ne_one hb1 (fun e => hd.t_not_mem_L (by rw [e]; exact hbL)) (hnorm _ htH)
      (hnorm _ (hN₂H hbN)) (fun x hx hxt => (s39a1_odd_comm_N₂ hp hx hxt b hbN).symm)
      (fun x _ hxb => hxb.symm) (fun x hx hxtb => ?_)
    have e1 : u⁻¹ * d.t * u = d.t * b := hut.trans htb.symm
    have hy : u * x * u⁻¹ * d.t = d.t * (u * x * u⁻¹) := by
      calc u * x * u⁻¹ * d.t = u * (x * (u⁻¹ * d.t * u)) * u⁻¹ := by group
        _ = u * (x * (d.t * b)) * u⁻¹ := by rw [e1]
        _ = u * (d.t * b * x) * u⁻¹ := by rw [hxtb]
        _ = u * ((u⁻¹ * d.t * u) * x) * u⁻¹ := by rw [e1]
        _ = d.t * (u * x * u⁻¹) := by group
    have hyb := s39a1_odd_comm_N₂ hp (hAH u huH x hx) hy b hbN
    have hub' : u⁻¹ * b = b * u⁻¹ := by
      calc u⁻¹ * b = u⁻¹ * (b * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * b) * u⁻¹ := by rw [hub]
        _ = b * u⁻¹ := by group
    calc b * x = b * u⁻¹ * (u * x * u⁻¹) * u := by group
      _ = u⁻¹ * (b * (u * x * u⁻¹)) * u := by rw [← hub']; group
      _ = u⁻¹ * (u * x * u⁻¹ * b) * u := by rw [hyb]
      _ = u⁻¹ * (u * x * u⁻¹) * (b * u) := by group
      _ = u⁻¹ * (u * x * u⁻¹) * (u * b) := by rw [hub]
      _ = x * b := by group
  set K := centralizer (A : Set G) with hK
  have hKH : ∀ g ∈ centralizer (d.I₂ : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    rw [hK, mem_centralizer_iff] at hk ⊢
    intro a ha
    have h1 := hk _ (hAH g⁻¹ (inv_mem hg) a ha)
    calc a * (g * k * g⁻¹) = g * ((g⁻¹ * a * g⁻¹⁻¹) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * a * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * k * g⁻¹ * a := by group
  have hq : CFSG.Open.IsQuasisimple ↥d.N₂ :=
    (hd.quasisimple_lieModel_N₂ (X := ↥d.N₂) ⟨MulEquiv.refl _⟩).1
  set Y : Subgroup ↥d.N₂ := K.subgroupOf d.N₂ with hY
  haveI hYn : Y.Normal := ⟨fun y hy n => by
    rw [hY, mem_subgroupOf] at hy ⊢
    exact hKH n (hN₂H n.2) y hy⟩
  have hbK : b ∈ K := by
    rw [hK, mem_centralizer_iff]
    intro x hx
    exact (hbA x hx).symm
  have hN₂K : d.N₂ ≤ K := by
    rcases s39a1_odd_normal_le_center_or_eq_top hq Y with hle | htop
    · exfalso
      have hbY : (⟨b, hbN⟩ : ↥d.N₂) ∈ Y := by rw [hY, mem_subgroupOf]; exact hbK
      have hbZ := hle hbY
      have hbI₂ : b ∈ d.I₂ := d.mem_I₂_of_comm_N₂ hbN fun n hn =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hbZ ⟨n, hn⟩).symm
      have hbI : b ∈ d.I := d.I₂_le_I hbI₂
      have hob : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hbb) hb1
      have h2 : 2 ∣ Nat.card d.I := hob ▸ Subgroup.orderOf_dvd_natCard d.I hbI
      exact (Nat.not_even_iff_odd.2 d.odd_card_I) (even_iff_two_dvd.2 h2)
    · intro n hn
      have hnY : (⟨n, hn⟩ : ↥d.N₂) ∈ Y := by rw [htop]; exact mem_top _
      rw [hY, mem_subgroupOf] at hnY
      exact hnY
  have hM₂K : d.M₂ ≤ K := by
    haveI hK'n : (K.subgroupOf (s39a1H d)).Normal := ⟨fun y hy g => by
      rw [mem_subgroupOf] at hy ⊢
      exact hKH g g.2 y hy⟩
    have hcl : normalClosure ((d.N₂.subgroupOf (s39a1H d) : Subgroup (s39a1H d)) :
        Set (s39a1H d)) ≤ K.subgroupOf (s39a1H d) :=
      normalClosure_le_normal fun x hx => by
        rw [SetLike.mem_coe, mem_subgroupOf] at hx ⊢
        exact hN₂K hx
    rintro _ ⟨x, hx, rfl⟩
    have hxK := hcl hx
    rw [mem_subgroupOf] at hxK
    exact hxK
  intro a ha m hm
  exact mem_centralizer_iff.1 (hM₂K hm) a ha

theorem s39a1_card_le_prod (d : Data G h) {W : Subgroup (s39a1J d × s39a1J d)}
    (hW : IsPGroup 2 W) : Nat.card W ≤ (2 ^ f) ^ 6 := by
  have hbound : ∀ A : Subgroup (s39a1J d), IsPGroup 2 A → Nat.card A ≤ (2 ^ f) ^ 3 := by
    intro A hA
    rw [← Subgroup.card_map_of_injective (s39a1J d).subtype_injective]
    exact card_le_of_le_image_N₂ (Subgroup.map_subtype_le A) (hA.map _)
  have hWle : W ≤ (W.map (MonoidHom.fst _ _)).prod (W.map (MonoidHom.snd _ _)) :=
    Subgroup.le_prod_iff.2 ⟨le_rfl, le_rfl⟩
  calc Nat.card W ≤ Nat.card ((W.map (MonoidHom.fst _ _)).prod (W.map (MonoidHom.snd _ _))) :=
        Subgroup.card_le_of_le hWle
    _ = Nat.card (W.map (MonoidHom.fst _ _)) * Nat.card (W.map (MonoidHom.snd _ _)) := by
        rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    _ ≤ (2 ^ f) ^ 3 * (2 ^ f) ^ 3 :=
        Nat.mul_le_mul (hbound _ (hW.map _)) (hbound _ (hW.map _))
    _ = (2 ^ f) ^ 6 := by ring

theorem ProductCaseHyp.s39a1_card_le (hp : d.ProductCaseHyp) {X : Subgroup G} (hX : X ≤ d.M₂)
    (hX2 : IsPGroup 2 X) : Nat.card X ≤ (2 ^ f) ^ 6 := by
  obtain ⟨-, -, ψ, -⟩ := hp.s39a1_layer_data
  have hOodd : Odd (Nat.card (s39a1O d)) := GMSK.odd_card_standardComponentOddCore _
  have hXH : X ≤ s39a1H d := hX.trans (s39a1_M₂_le_centralizer d)
  have hX'2 : IsPGroup 2 (X.subgroupOf (s39a1H d)) := hX2.comap_subtype
  have hinj := injOn_mk'_of_isPGroup hOodd hX'2
  have hinjX : Function.Injective ((s39a1θ d).subgroupMap (X.subgroupOf (s39a1H d))) :=
    fun a b hab => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
  have hXΛ : (X.subgroupOf (s39a1H d)).map (s39a1θ d) ≤ s39a1Λ d :=
    Subgroup.map_mono (fun x hx => hX hx)
  have hcard : Nat.card X = Nat.card ((((X.subgroupOf (s39a1H d)).map (s39a1θ d)).subgroupOf
      (s39a1Λ d)).map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXΛ).toEquiv,
      ← Nat.card_congr (Equiv.ofBijective _ ⟨hinjX, (s39a1θ d).subgroupMap_surjective _⟩),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
  rw [hcard]
  exact s39a1_card_le_prod d ((hX'2.map _).comap_subtype.map _)

theorem s39a1_ti_lift_TIJ (hTI : CaseBParts.SU3SylowTIStatement) (hp : d.ProductCaseHyp) :
    S39a1TI (s39a1J d) := by
  have hOodd : Odd (Nat.card (s39a1O d)) := GMSK.odd_card_standardComponentOddCore _
  have hNM : d.N₂ ≤ d.M₂ := s39a1_N₂_le_M₂ d
  have hNH : d.N₂ ≤ s39a1H d := hNM.trans (s39a1_M₂_le_centralizer d)
  have hcomm := hp.s39a1_odd
  have : Finite (hypSU h 1 1) := Finite.of_equiv _ d.N₂equiv.symm.toEquiv
  have hTIX : S39a1TI (hypSU h 1 1) := fun P Q hP hQ hPQ =>
    hTI f K h (by have := hp.hyp.two_le; omega) P Q hP hQ hPQ
  let ι : hypSU h 1 1 →* s39a1H d := (Subgroup.inclusion hNH).comp d.N₂equiv.toMonoidHom
  have hιinj : Function.Injective ι :=
    (Subgroup.inclusion_injective hNH).comp d.N₂equiv.injective
  have hιJ : ∀ x, s39a1θ d (ι x) ∈ s39a1J d := fun x =>
    ⟨ι x, Subgroup.mem_subgroupOf.2 (d.N₂equiv x).2, rfl⟩
  let π : hypSU h 1 1 →* s39a1J d := ((s39a1θ d).comp ι).codRestrict (s39a1J d) hιJ
  have hsurj : Function.Surjective π := by
    rintro ⟨_, a, ha, rfl⟩
    refine ⟨d.N₂equiv.symm ⟨a, Subgroup.mem_subgroupOf.1 ha⟩, Subtype.ext ?_⟩
    have e1 : ι (d.N₂equiv.symm ⟨a, Subgroup.mem_subgroupOf.1 ha⟩) = a := by
      apply Subtype.ext
      show ((d.N₂equiv (d.N₂equiv.symm ⟨a, Subgroup.mem_subgroupOf.1 ha⟩) : d.N₂) : G) = a
      rw [MulEquiv.apply_symm_apply]
    exact congrArg (s39a1θ d) e1
  have hkerO : ∀ x ∈ π.ker, ι x ∈ s39a1O d := by
    intro x hx
    have e : s39a1θ d (ι x) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact (QuotientGroup.eq_one_iff _).1 e
  refine s39a1_ti_quot hTIX π hsurj (fun z hz x => ?_) ?_
  · apply hιinj
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact hcomm _ ⟨_, hkerO z hz, rfl⟩ _ (hNM (d.N₂equiv x).2)
  · rw [← Subgroup.card_map_of_injective hιinj]
    refine Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hkerO x hx

theorem ProductCaseHyp.s39a1_ti_lift (hTI : CaseBParts.SU3SylowTIStatement) (hp : d.ProductCaseHyp)
    {R Q : Subgroup G} (hR : IsSylowOf 2 R d.M₂) (hQM : Q ≤ d.M₂) (hQ : IsPGroup 2 Q) {z : G}
    (hzQ : z ∈ Q) (hzR : z ∈ R) (hzN : z ∈ d.N₂) (hz : z ≠ 1) : Q ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ψ, hψ⟩ := hp.s39a1_layer_data
  have hOodd : Odd (Nat.card (s39a1O d)) := GMSK.odd_card_standardComponentOddCore _
  have hMH : d.M₂ ≤ s39a1H d := s39a1_M₂_le_centralizer d
  have hNM : d.N₂ ≤ d.M₂ := s39a1_N₂_le_M₂ d
  have hcomm := hp.s39a1_odd
  have hΛ : ∀ m : d.M₂, s39a1θ d (Subgroup.inclusion hMH m) ∈ s39a1Λ d := fun m =>
    ⟨Subgroup.inclusion hMH m, Subgroup.mem_subgroupOf.2 m.2, rfl⟩
  let φ₀ : d.M₂ →* s39a1Λ d := ((s39a1θ d).comp (Subgroup.inclusion hMH)).codRestrict _ hΛ
  let φ : d.M₂ →* s39a1J d × s39a1J d := ψ.toMonoidHom.comp φ₀
  have hsurj₀ : Function.Surjective φ₀ := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hsurj : Function.Surjective φ := ψ.surjective.comp hsurj₀
  have hker : ∀ m ∈ φ.ker, (∀ x : d.M₂, m * x = x * m) ∧ Odd (orderOf m) := by
    intro m hm
    have h0 : ψ (φ₀ m) = 1 := MonoidHom.mem_ker.1 hm
    have h1 : φ₀ m = 1 := (map_eq_one_iff ψ ψ.injective).1 h0
    have h2 : Subgroup.inclusion hMH m ∈ s39a1O d := by
      have e : s39a1θ d (Subgroup.inclusion hMH m) = 1 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).1 e
    refine ⟨fun x => Subtype.ext (hcomm _ ⟨_, h2, rfl⟩ _ x.2), ?_⟩
    have h3 := orderOf_dvd_natCard (⟨_, h2⟩ : s39a1O d)
    rw [Subgroup.orderOf_mk, orderOf_injective _ (Subgroup.inclusion_injective hMH)] at h3
    exact Odd.of_dvd_nat hOodd h3
  have hR' : IsSylowOf 2 (R.subgroupOf d.M₂) ⊤ := by
    obtain ⟨-, hR2, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hR
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, hR2.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hidx
  have hzM : z ∈ d.M₂ := hNM hzN
  have hzH : z ∈ s39a1H d := hMH hzM
  have hjJ : s39a1θ d ⟨z, hzH⟩ ∈ s39a1J d := ⟨⟨z, hzH⟩, Subgroup.mem_subgroupOf.2 hzN, rfl⟩
  have hzj : φ ⟨z, hzM⟩ = (⟨_, hjJ⟩, ⟨_, hjJ⟩) := hψ _ hjJ (s39a1_J_le_Λ d hjJ)
  have hj : (⟨_, hjJ⟩ : s39a1J d) ≠ 1 := by
    intro h1
    have e : s39a1θ d ⟨z, hzH⟩ = 1 := congrArg Subtype.val h1
    have hO : (⟨z, hzH⟩ : s39a1H d) ∈ s39a1O d := (QuotientGroup.eq_one_iff _).1 e
    obtain ⟨k, hk⟩ := hR.isPGroup ⟨z, hzR⟩
    have hzk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hzk : (⟨z, hzH⟩ : s39a1H d) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hzk')
    exact hz (congrArg Subtype.val (eq_one_of_mem_of_pow_two_pow hOodd hO hzk))
  have hle := s39a1_ti_lift_abs (s39a1_ti_lift_TIJ hTI hp) φ hsurj hker hR' hQ.comap_subtype
    (z := ⟨z, hzM⟩) (Subgroup.mem_subgroupOf.2 hzQ) (Subgroup.mem_subgroupOf.2 hzR) hj hzj
  intro x hx
  exact Subgroup.mem_subgroupOf.1
    (hle (Subgroup.mem_subgroupOf.2 hx : (⟨x, hQM hx⟩ : d.M₂) ∈ Q.subgroupOf d.M₂))

theorem s39a1_ti_lift₅_map_conj_inv {X : Type*} [Group X] (g : X) (A : Subgroup X) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  have e : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id X := by
    ext x
    simp [mul_assoc]
  rw [Subgroup.map_map, e, Subgroup.map_id]

theorem ProductCaseHyp.s39a1_ti_lift₅ (hTI : CaseBParts.SU3SylowTIStatement) (hp : d.ProductCaseHyp)
    {R Q : Subgroup G} (hR : IsSylowOf 2 R d.M₅) (hQM : Q ≤ d.M₅) (hQ : IsPGroup 2 Q) {z : G}
    (hzQ : z ∈ Q) (hzR : z ∈ R) (hzN : z ∈ d.N₅) (hz : z ≠ 1) : Q ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hM₅, -, hN₅⟩ := hp.hyp.s39a1_conj_r
  have hc : Function.Injective (MulAut.conj d.r⁻¹).toMonoidHom := (MulAut.conj d.r⁻¹).injective
  have hM : d.M₅.map (MulAut.conj d.r⁻¹).toMonoidHom = d.M₂ := by
    rw [hM₅, s39a1_ti_lift₅_map_conj_inv]
  have hN : d.N₅.map (MulAut.conj d.r⁻¹).toMonoidHom = d.N₂ := by
    rw [hN₅, s39a1_ti_lift₅_map_conj_inv]
  have hR' : IsSylowOf 2 (R.map (MulAut.conj d.r⁻¹).toMonoidHom) d.M₂ := by
    rw [← hM]
    refine CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono hR.le) ?_
    rw [Subgroup.card_map_of_injective hc, Subgroup.card_map_of_injective hc]
    exact hR.card_eq
  have hQM' : Q.map (MulAut.conj d.r⁻¹).toMonoidHom ≤ d.M₂ := by
    rw [← hM]
    exact Subgroup.map_mono hQM
  have hzN' : (MulAut.conj d.r⁻¹).toMonoidHom z ∈ d.N₂ := by
    rw [← hN]
    exact Subgroup.mem_map_of_mem _ hzN
  have hz' : (MulAut.conj d.r⁻¹).toMonoidHom z ≠ 1 := fun h1 =>
    hz ((map_eq_one_iff _ hc).1 h1)
  have hle := hp.s39a1_ti_lift hTI hR' hQM' (hQ.map _)
    (Subgroup.mem_map_of_mem (MulAut.conj d.r⁻¹).toMonoidHom hzQ)
    (Subgroup.mem_map_of_mem (MulAut.conj d.r⁻¹).toMonoidHom hzR) hzN' hz'
  exact (Subgroup.map_le_map_iff_of_injective hc).1 hle

theorem ProductCaseHyp.s39a1_card_le₅ (hp : d.ProductCaseHyp) {X : Subgroup G} (hX : X ≤ d.M₅)
    (hX2 : IsPGroup 2 X) : Nat.card X ≤ (2 ^ f) ^ 6 := by
  obtain ⟨hM₅, -, -⟩ := hp.hyp.s39a1_conj_r
  have hle : X.map (MulAut.conj d.r⁻¹).toMonoidHom ≤ d.M₂ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hM₅] at hX
    obtain ⟨m, hm, rfl⟩ := hX hy
    simpa [mul_assoc] using hm
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj d.r⁻¹).toMonoidHom)
    (MulAut.conj d.r⁻¹).injective]
  exact hp.s39a1_card_le hle (hX2.map _)

theorem s39a1_cB6_mem_A₁ (hd : d.Hyp) {S : Subgroup G} (hS : S ≤ d.I)
    (hA : d.A₃ ⊓ centralizer (S : Set G) = ⊥) {a : G} (ha : a ∈ d.A₃)
    (hfix : ∀ s ∈ S, a⁻¹ * (s * a * s⁻¹) ∈ d.A₁) : a ∈ d.A₁ := by
  have hIA₃ : d.I ≤ normalizer (d.A₃ : Set G) := fun i hi =>
    hd.normalizer_B₁_inf_le_normalizer_A₃ (hd.I_le_normalizer_B₁ hi)
  have hA₃A₁ : d.A₃ ≤ normalizer (d.A₁ : Set G) := fun b hb =>
    mem_normalizer_of_mem_centralizer'
      (mem_centralizer_iff.2 fun y hy => d.A₁_commute_A₃ y hy b hb)
  obtain ⟨c, hc, n, hn, rfl⟩ := s39a1_lift d.A₁_le_A₃ hA₃A₁ (hS.trans hIA₃)
    (hS.trans d.I_le_normalizer_A₁) (d.isPGroup_P.to_le d.A₃_le_P)
    (Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le hS)) ha hfix
  rw [hA] at hc
  rw [Subgroup.mem_bot.1 hc, one_mul]
  exact hn

theorem s39a1_cB6_eq_one_of_mem_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {S : Subgroup G} (hS : S ≤ d.I) (hA : d.A₃ ⊓ centralizer (S : Set G) = ⊥) {y : G}
    (hyF : y ∈ d.F) (hyS : y ∈ centralizer (S : Set G)) : y = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, φ, -, hφk, hφf, -⟩ := hd.sec3_4 hGMS
  have htS : d.t ∈ centralizer (S : Set G) := mem_centralizer_iff.2 fun s hs =>
    mem_centralizer_singleton_iff.1 (hd.I_le_normalizer_B₁ (hS hs)).2
  have hbot : ∀ z ∈ d.A₁, z ∈ centralizer (S : Set G) → z = 1 := fun z hz hzS => by
    have hz' : z ∈ d.A₃ ⊓ centralizer (S : Set G) := ⟨d.A₁_le_A₃ hz, hzS⟩
    rw [hA] at hz'
    exact Subgroup.mem_bot.1 hz'
  have h1 : ((φ ⟨y, hyF⟩ : d.A₁) : G) = 1 := by
    refine hbot _ (φ ⟨y, hyF⟩).2 ?_
    rw [hφf]
    exact mul_mem (mul_mem (mul_mem (inv_mem hyS) htS) hyS) htS
  have hk : (⟨y, hyF⟩ : d.F) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext h1
  rw [hφk] at hk
  exact hbot y (Subgroup.mem_subgroupOf.1 hk) hyS

theorem Hyp.s39a1_centralizer_B₆_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {S : Subgroup G} (hS : S ≤ d.I) (hA : d.A₃ ⊓ centralizer (S : Set G) = ⊥) :
    d.B₆ ⊓ centralizer (S : Set G) ≤ zpowers d.t := by
  rintro x ⟨hxB, hxS⟩
  obtain ⟨hN13, -, -, hFN, -, -, hFB, -⟩ := hd.sec3_4 hGMS
  obtain ⟨-, -, -, -, ψ, -, hψk, -, hψe⟩ := hd.sec3_7 hGMS
  have hIA₃ : d.I ≤ normalizer (d.A₃ : Set G) := fun i hi =>
    hd.normalizer_B₁_inf_le_normalizer_A₃ (hd.I_le_normalizer_B₁ hi)
  have hst : ∀ s ∈ S, s * d.t = d.t * s := fun s hs =>
    mem_centralizer_singleton_iff.1 (hd.I_le_normalizer_B₁ (hS hs)).2
  have hsN : ∀ s ∈ S, s ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G) :=
    fun s hs => ⟨by rw [← hN13]; exact (hd.I_le_normalizer_B₁ (hS hs)).1,
      (hd.I_le_normalizer_B₁ (hS hs)).2⟩
  have hxc : ∀ s ∈ S, s * x * s⁻¹ = x := fun s hs => by
    rw [mem_centralizer_iff.1 hxS s hs, mul_inv_cancel_right]
  have hxFB : x ∈ d.F ⊔ d.B₃ := by
    obtain ⟨⟨a, haA⟩, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨x, hxB⟩)
    have hfix : ∀ s ∈ S, a⁻¹ * (s * a * s⁻¹) ∈ d.A₁ := fun s hs => by
      have hs1 : s * x * s⁻¹ ∈ d.B₆ := by rw [hxc s hs]; exact hxB
      have hs2 : s * a * s⁻¹ ∈ d.A₃ := (mem_normalizer_iff.1 (hIA₃ (hS hs)) a).1 haA
      have e := hψe s (hsN s hs) ⟨x, hxB⟩ ⟨a, haA⟩ hs1 hs2 ha.symm
      have e' : ψ ⟨x, hxB⟩ = ψ ⟨s * x * s⁻¹, hs1⟩ :=
        congrArg ψ (Subtype.ext (hxc s hs).symm)
      exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (ha.trans (e'.trans e)))
    have haA₁ := s39a1_cB6_mem_A₁ hd hS hA haA hfix
    have h1 : (⟨x, hxB⟩ : d.B₆) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← ha]
      exact (QuotientGroup.eq_one_iff _).2 haA₁
    rw [hψk] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hFN3 : d.F ≤ normalizer (d.B₃ : Set G) := by rw [← hN13]; exact hFN
  have hxBF : x ∈ d.B₃ ⊔ d.F := by rw [sup_comm]; exact hxFB
  obtain ⟨b, hb, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hFN3 hxBF
  have hfixb : ∀ s ∈ S, b⁻¹ * (s * b * s⁻¹) ∈ d.A₁ := fun s hs => by
    have key : b⁻¹ * (s * b * s⁻¹) = y * (s * y * s⁻¹)⁻¹ := by
      have e2 : b⁻¹ * (s * b * s⁻¹) = b⁻¹ * (s * (b * y) * s⁻¹) * (s * y * s⁻¹)⁻¹ := by
        group
      rw [e2, hxc s hs]
      group
    have memF : y * (s * y * s⁻¹)⁻¹ ∈ d.F :=
      mul_mem hy (inv_mem ((mem_normalizer_iff.1 (hd.I_le_normalizer_F hGMS (hS hs)) y).1 hy))
    have memB : b⁻¹ * (s * b * s⁻¹) ∈ d.B₃ :=
      mul_mem (inv_mem hb) ((mem_normalizer_iff.1 (hsN s hs).1 b).1 hb)
    rw [← hFB]
    exact ⟨by rw [key]; exact memF, memB⟩
  obtain ⟨a, haA, hba | hba⟩ := hd.exists_of_mem_B₃ hb
  · have hbA₁ := s39a1_cB6_mem_A₁ hd hS hA (by rw [hba]; exact haA) hfixb
    have h1 := s39a1_cB6_eq_one_of_mem_F hGMS hd hS hA (mul_mem (hd.A₁_le_F hbA₁) hy) hxS
    rw [h1]
    exact one_mem _
  · subst hba
    have hfixa : ∀ s ∈ S, a⁻¹ * (s * a * s⁻¹) ∈ d.A₁ := fun s hs => by
      have e : a⁻¹ * (s * a * s⁻¹) = (d.t * a)⁻¹ * (s * (d.t * a) * s⁻¹) := by
        rw [show s * (d.t * a) * s⁻¹ = d.t * (s * a * s⁻¹) by
          rw [← mul_assoc, hst s hs]; group]
        group
      rw [e]
      exact hfixb s hs
    have haA₁ := s39a1_cB6_mem_A₁ hd hS hA haA hfixa
    have htS : d.t ∈ centralizer (S : Set G) := mem_centralizer_iff.2 fun s hs => hst s hs
    have hyS : a * y ∈ centralizer (S : Set G) := by
      have e : a * y = d.t⁻¹ * (d.t * a * y) := by group
      rw [e]
      exact mul_mem (inv_mem htS) hxS
    have h1 := s39a1_cB6_eq_one_of_mem_F hGMS hd hS hA (mul_mem (hd.A₁_le_F haA₁) hy) hyS
    have e : d.t * a * y = d.t := by rw [mul_assoc, h1, mul_one]
    rw [e]
    exact mem_zpowers _

theorem Hyp.s39a1_D_facts (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.D ≤ d.B₆ ∧ d.B₆ ≤ normalizer (d.D : Set G) ∧ d.A₃ ≤ d.D ∧
    (∀ b ∈ d.B₆, ∃ c ∈ zpowers d.t, ∃ n ∈ d.D, b = c * n) := by
  obtain ⟨hIB, hID⟩ := hd.s39a1_I_le_normalizer_B₆ hGMS
  have hI₁B : d.I₁ ≤ normalizer (d.B₆ : Set G) := d.I₁_le_I.trans hIB
  have hI₁D : d.I₁ ≤ normalizer (d.D : Set G) := d.I₁_le_I.trans hID
  have hDB : d.D ≤ d.B₆ := Subgroup.le_normalizer_iff_commutator_le_left.1 hI₁B
  have hBD : d.B₆ ≤ normalizer (d.D : Set G) :=
    Subgroup.normalizer_commutator_ge_left d.B₆ d.I₁
  have hodd : Odd (Nat.card d.I₁) :=
    Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₁_le_I)
  have hcomm : ∀ b ∈ d.B₆, ∀ s ∈ d.I₁, b⁻¹ * (s * b * s⁻¹) ∈ d.D := fun b hb s hs => by
    have hc := Subgroup.commutator_mem_commutator (inv_mem hb) hs
    rw [commutatorElement_def, inv_inv] at hc
    have e : b⁻¹ * (s * b * s⁻¹) = b⁻¹ * s * b * s⁻¹ := by group
    rw [e]
    exact hc
  have hA₃B : d.A₃ ≤ d.B₆ := d.A₃_le_B₃.trans (le_sup_right.trans hd.F_sup_B₃_le_B₆)
  have hIA₃ : d.I ≤ normalizer (d.A₃ : Set G) := fun i hi =>
    hd.normalizer_B₁_inf_le_normalizer_A₃ (hd.I_le_normalizer_B₁ hi)
  have hA₃C : d.A₃ ⊓ centralizer (d.I₁ : Set G) = ⊥ := by
    have h0 := (d.sec2_1_two hd.two_le).2.2.2.2.2.2.2.2.2.2.2.2
    exact eq_bot_iff.2 fun c hc => h0.le ⟨hc.1, d.A₃_le_P hc.1, hc.2⟩
  have hA₃D : d.A₃ ≤ d.D := by
    intro a ha
    obtain ⟨c, hc, n, hn, rfl⟩ := s39a1_lift (M := d.A₃) (N := d.A₃ ⊓ d.D) (S := d.I₁)
      inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, hBD (hA₃B hg)⟩)
      (d.I₁_le_I.trans hIA₃)
      (fun s hs => Subgroup.inf_normalizer_le_normalizer_inf ⟨hIA₃ (d.I₁_le_I hs), hI₁D hs⟩)
      (d.isPGroup_P.to_le d.A₃_le_P) hodd ha
      (fun s hs => Subgroup.mem_inf.2
        ⟨mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (hIA₃ (d.I₁_le_I hs)) a).1 ha),
          hcomm a (hA₃B ha) s hs⟩)
    rw [hA₃C] at hc
    rw [Subgroup.mem_bot.1 hc, one_mul]
    exact hn.2
  refine ⟨hDB, hBD, hA₃D, fun b hb => ?_⟩
  obtain ⟨c, hc, n, hn, rfl⟩ :=
    s39a1_lift hDB hBD hI₁B hI₁D d.isPGroup_B₆_caseB hodd hb (hcomm b hb)
  exact ⟨c, hd.s39a1_centralizer_B₆_le hGMS d.I₁_le_I hA₃C hc, n, hn, rfl⟩

theorem Hyp.s39a1_CA3_P_inf (hd : d.Hyp) :
    d.P ⊓ centralizer (d.I₂ : Set G) = d.CPI₂ := by
  have e : d.P ⊓ centralizer (d.I₂ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set (hypSU h 2 1))) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  rw [e, U_inf_centralizer_I₂ hd.two_le]
  rfl

theorem Hyp.s39a1_C_A₃_I₂ (hd : d.Hyp) :
    d.A₃ ⊓ centralizer (d.I₂ : Set G) = d.CPI₂ ∧ Nat.card d.CPI₂ = (2 ^ f) ^ 3 := by
  have e := hd.s39a1_CA3_P_inf
  refine ⟨le_antisymm ((inf_le_inf_right _ d.A₃_le_P).trans e.le) ?_, ?_⟩
  · exact le_inf (d.pull_mono patSub_I₂_le_Ssub) (e.symm.le.trans inf_le_right)
  · rw [CPI₂, d.card_pull (patSub_le_U _ _), card_patSub_sI₂]

omit [Finite G] in
theorem s39a1_CA1_I₂_le_I₆ (d : Data G h) : d.I₂ ≤ d.I₆ :=
  d.pull_mono fun t ht => by
    rw [mem_I₂sub] at ht
    rw [mem_I₆sub]
    exact ⟨ht.1, ht.2.1.trans ht.2.2⟩

theorem Hyp.s39a1_CA1_P_inf (hd : d.Hyp) :
    d.P ⊓ centralizer (d.I₆ : Set G) = d.CPI₆ := by
  have e : d.P ⊓ centralizer (d.I₆ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₆sub h : Set (hypSU h 2 1))) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  rw [e, U_inf_centralizer_I₆ hd.two_le]
  rfl

theorem Hyp.s39a1_CA1_eq (hd : d.Hyp) :
    d.A₁ ⊓ centralizer (d.I₂ : Set G) = d.CPI₆ := by
  obtain ⟨-, -, ⟨hA₁, -⟩, -, -, -, ⟨-, hbot⟩, -, hA₂₃, -⟩ := d.sec2_1_two hd.two_le
  have e6 := hd.s39a1_CA1_P_inf
  have hC : centralizer (d.I₆ : Set G) ≤ centralizer (d.I₂ : Set G) :=
    centralizer_le (s39a1_CA1_I₂_le_I₆ d)
  have hZA : d.Z₂p ≤ d.A₁ := by
    rw [hA₁]
    exact le_sup_left
  have hCA : d.P ⊓ centralizer (d.I₆ : Set G) ≤ d.A₁ := by
    rw [hA₁]
    exact le_sup_right
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxA, hxC⟩
    rw [hA₁] at hxA
    obtain ⟨z, hz, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => d.A₁_comm_sq.1 a (hZA ha) b (hCA hb)) hxA
    have hzC : z ∈ centralizer (d.I₂ : Set G) := by
      have hxC' : z * c ∈ centralizer (d.I₂ : Set G) := hxC
      have hcC : c ∈ centralizer (d.I₂ : Set G) := hC hc.2
      have := mul_mem hxC' (inv_mem hcC)
      rwa [mul_inv_cancel_right] at this
    have hz23 : z ∈ d.A₂ ⊓ d.A₃ := by
      rw [hA₂₃]
      exact mem_sup_left hz
    have hz1 : z ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hz23, d.A₃_le_P hz23.2, hzC⟩
    rw [mem_bot.1 hz1, one_mul, ← e6]
    exact hc
  · rw [← e6]
    exact le_inf hCA (inf_le_right.trans hC)

theorem Hyp.s39a1_card_C_A₁_I₂ (hd : d.Hyp) :
    Nat.card (d.A₁ ⊓ centralizer (d.I₂ : Set G) : Subgroup G) = 2 ^ f := by
  rw [hd.s39a1_CA1_eq, d.card_CPI₆]

theorem Hyp.s39a1_card_F_I₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (2 ^ f) ^ 2 ≤ Nat.card (d.F ⊓ centralizer (d.I₂ : Set G) : Subgroup G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, ψ, hψs, hψk, -, hψc⟩ := hd.sec3_4 hGMS
  have hA₁F : d.A₁ ≤ d.F := hd.A₁_le_F
  have hSI : d.I₂ ≤ d.I := d.I₂_le_I
  have hSodd : Odd (Nat.card d.I₂) := Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le hSI)
  have hSN : d.I₂ ≤ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) :=
    hSI.trans hd.I_le_normalizer_B₁
  have hSF : d.I₂ ≤ normalizer (d.F : Set G) := hSI.trans (hd.I_le_normalizer_F hGMS)
  have hSA : d.I₂ ≤ normalizer (d.A₁ : Set G) := hSI.trans d.I_le_normalizer_A₁
  have hFA : d.F ≤ normalizer (d.A₁ : Set G) :=
    hd.F_le_centralizer_A₁.trans (Subgroup.centralizer_le_normalizer _)
  have hK : Nat.card (d.A₁ ⊓ centralizer (d.I₂ : Set G) : Subgroup G) = 2 ^ f :=
    hd.s39a1_card_C_A₁_I₂
  have key := s39a1_card_inf_ker_mul ψ ((d.F ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.F)
  have hWcard : Nat.card ((d.F ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.F) =
      Nat.card (d.F ⊓ centralizer (d.I₂ : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 : 2 ^ f ≤ Nat.card
      ((d.F ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.F ⊓ ψ.ker : Subgroup d.F) := by
    have hle : (d.A₁ ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.F ≤
        (d.F ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.F ⊓ ψ.ker := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      refine ⟨Subgroup.mem_subgroupOf.2 ⟨x.2, hx.2⟩, ?_⟩
      rw [hψk]
      exact Subgroup.mem_subgroupOf.2 hx.1
    exact hK.symm.le.trans ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans hA₁F)).toEquiv).symm.le.trans (Subgroup.card_le_of_le hle))
  have h2 : 2 ^ f ≤ Nat.card (((d.F ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.F).map ψ) := by
    have hle : (d.A₁ ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.A₁ ≤
        ((d.F ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.F).map ψ := by
      intro a ha
      rw [Subgroup.mem_subgroupOf] at ha
      have haC : (a : G) ∈ centralizer (d.I₂ : Set G) := ha.2
      obtain ⟨x, hx⟩ := hψs a
      have hfix : ∀ s ∈ d.I₂, (x : G)⁻¹ * (s * x * s⁻¹) ∈ d.A₁ := by
        intro s hs
        obtain ⟨hsx, hψsx⟩ := hψc s (hSN hs) x
        have hsa : s * (a : G) * s⁻¹ = a := by
          rw [mem_centralizer_iff.1 haC s hs, mul_inv_cancel_right]
        have hker : x⁻¹ * ⟨s * x * s⁻¹, hsx⟩ ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
          apply Subtype.ext
          rw [hψsx, hx, hsa]
        rw [hψk, Subgroup.mem_subgroupOf] at hker
        exact hker
      obtain ⟨c, hc, n, hn, hxcn⟩ := s39a1_lift hA₁F hFA hSF hSA hd.isPGroup_F hSodd x.2 hfix
      have hcF : c ∈ d.F := hc.1
      refine Subgroup.mem_map.2 ⟨⟨c, hcF⟩, Subgroup.mem_subgroupOf.2 hc, ?_⟩
      have hn' : (⟨n, hA₁F hn⟩ : d.F) ∈ ψ.ker := by
        rw [hψk]
        exact Subgroup.mem_subgroupOf.2 hn
      have hxe : x = ⟨c, hcF⟩ * ⟨n, hA₁F hn⟩ := Subtype.ext hxcn
      rw [← hx, hxe, map_mul, MonoidHom.mem_ker.1 hn', mul_one]
    exact hK.symm.le.trans ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : d.A₁ ⊓ centralizer (d.I₂ : Set G) ≤ d.A₁)).toEquiv).symm.le.trans
      (Subgroup.card_le_of_le hle))
  rw [← hWcard, key, sq]
  exact Nat.mul_le_mul h1 h2

theorem Hyp.s39a1_card_FB₃_I₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    2 * (2 ^ f) ^ 4 ≤ Nat.card ((d.F ⊔ d.B₃) ⊓ centralizer (d.I₂ : Set G) : Subgroup G) := by
  obtain ⟨-, -, -, -, -, -, hFB, -⟩ := hd.sec3_4 hGMS
  have hCA₃ := hd.s39a1_C_A₃_I₂
  have hK := hd.s39a1_card_C_A₁_I₂
  have hF₂ := hd.s39a1_card_F_I₂ hGMS
  have htC : d.t ∈ centralizer (d.I₂ : Set G) :=
    mem_centralizer_iff.2 fun s hs => hd.comm_t (d.pull_le_L _ hs)
  have hU₃card : Nat.card (zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G)) : Subgroup G) =
      2 * (2 ^ f) ^ 3 := by
    rw [hd.card_zpowers_sup ((inf_le_left.trans d.A₃_le_P).trans d.P_le_L), hCA₃.1, hCA₃.2]
  have hU₃B₃ : zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G)) ≤ d.B₃ :=
    sup_le_sup_left inf_le_left _
  have hU₃C : zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G)) ≤ centralizer (d.I₂ : Set G) :=
    sup_le (zpowers_le.2 htC) inf_le_right
  have hU₃N : zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G)) ≤
      normalizer ((d.F ⊓ centralizer (d.I₂ : Set G) : Subgroup G) : Set G) := by
    intro u hu
    have h1 := Subgroup.mem_normalizer_iff.1 (hd.B₃_le_normalizer_F (hU₃B₃ hu))
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (hU₃C hu))
    exact Subgroup.mem_normalizer_iff.2 fun x =>
      ⟨fun hx => ⟨(h1 x).1 hx.1, (h2 x).1 hx.2⟩, fun hx => ⟨(h1 x).2 hx.1, (h2 x).2 hx.2⟩⟩
  have hcard := Common.card_sup_mul_card_inf_eq hU₃N
  have hinf : (d.F ⊓ centralizer (d.I₂ : Set G)) ⊓
      (zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G))) ≤
        d.A₁ ⊓ centralizer (d.I₂ : Set G) := by
    intro x hx
    have hxF : x ∈ d.F ⊓ centralizer (d.I₂ : Set G) := hx.1
    have hxU : x ∈ zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G)) := hx.2
    have hxFB : x ∈ d.F ⊓ d.B₃ := ⟨hxF.1, hU₃B₃ hxU⟩
    rw [hFB] at hxFB
    exact ⟨hxFB, hxF.2⟩
  have hinfcard : Nat.card ((d.F ⊓ centralizer (d.I₂ : Set G)) ⊓
      (zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G))) : Subgroup G) ≤ 2 ^ f :=
    (Subgroup.card_le_of_le hinf).trans hK.le
  have hsup : (d.F ⊓ centralizer (d.I₂ : Set G)) ⊔
      (zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G))) ≤
        (d.F ⊔ d.B₃) ⊓ centralizer (d.I₂ : Set G) :=
    sup_le (inf_le_inf_right _ le_sup_left) (le_inf (hU₃B₃.trans le_sup_right) hU₃C)
  have hpos : 0 < 2 ^ f := by positivity
  have hmul : 2 * (2 ^ f) ^ 4 * 2 ^ f ≤ Nat.card ((d.F ⊓ centralizer (d.I₂ : Set G)) ⊔
      (zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G))) : Subgroup G) * 2 ^ f := by
    calc 2 * (2 ^ f) ^ 4 * 2 ^ f = (2 ^ f) ^ 2 * (2 * (2 ^ f) ^ 3) := by ring
      _ ≤ Nat.card (d.F ⊓ centralizer (d.I₂ : Set G) : Subgroup G) *
          Nat.card (zpowers d.t ⊔ (d.A₃ ⊓ centralizer (d.I₂ : Set G)) : Subgroup G) := by
        rw [hU₃card]
        exact Nat.mul_le_mul hF₂ le_rfl
      _ = _ := hcard.symm
      _ ≤ _ := Nat.mul_le_mul le_rfl hinfcard
  exact (Nat.le_of_mul_le_mul_right hmul hpos).trans (Subgroup.card_le_of_le hsup)

theorem Hyp.s39a1_card_centralizer_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    2 * (2 ^ f) ^ 6 ≤ Nat.card (d.B₆ ⊓ centralizer (d.I₂ : Set G) : Subgroup G) := by
  obtain ⟨hFB, -, -, -, ψ, hψs, hψk, -, hψeq⟩ := hd.sec3_7 hGMS
  have hI₂ : ∀ σ ∈ d.I₂, σ ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G) := by
    intro σ hσ
    have h1 := hd.I_le_normalizer_B₁ (d.I₂_le_I hσ)
    have h1t : σ ∈ centralizer ({d.t} : Set G) := (Subgroup.mem_inf.1 h1).2
    exact Subgroup.mem_inf.2 ⟨Common.mem_normalizer_sup (mem_normalizer_zpowers_t h1t)
      (hd.normalizer_B₁_inf_le_normalizer_A₃ h1), h1t⟩
  have hSN : d.I₂ ≤ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := fun σ hσ =>
    Common.mem_normalizer_sup (hd.I_le_normalizer_F hGMS (d.I₂_le_I hσ))
      (Subgroup.mem_inf.1 (hI₂ σ hσ)).1
  have hSM : d.I₂ ≤ normalizer (d.B₆ : Set G) := hSN.trans d.normalizer_le_normalizer_B₆
  have hodd : Odd (Nat.card d.I₂) :=
    d.odd_card_I.of_dvd_nat (Subgroup.card_dvd_of_le d.I₂_le_I)
  have hYle : d.B₆ ⊓ centralizer (d.I₂ : Set G) ≤ d.B₆ := inf_le_left
  obtain ⟨W, hW⟩ : ∃ W : Subgroup d.B₆,
      W = (d.B₆ ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.B₆ := ⟨_, rfl⟩
  have hker : 2 * (2 ^ f) ^ 4 ≤ Nat.card (W ⊓ ψ.ker : Subgroup d.B₆) := by
    have hle0 : (d.F ⊔ d.B₃) ⊓ centralizer (d.I₂ : Set G) ≤ d.B₆ := inf_le_left.trans hFB
    have hle : ((d.F ⊔ d.B₃) ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.B₆ ≤ W ⊓ ψ.ker := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [hW, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_inf.2 ⟨x.2, (Subgroup.mem_inf.1 hx).2⟩
      · rw [hψk, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_inf.1 hx).1
    exact (hd.s39a1_card_FB₃_I₂ hGMS).trans
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle0).toEquiv).symm.trans_le
        (Subgroup.card_le_of_le hle))
  obtain ⟨hCA, hCcard⟩ := hd.s39a1_C_A₃_I₂
  have hCle : d.CPI₂ ≤ d.A₃ := by
    rw [← hCA]
    exact inf_le_left
  obtain ⟨C', hC'⟩ : ∃ C' : Subgroup d.A₃, C' = d.CPI₂.subgroupOf d.A₃ := ⟨_, rfl⟩
  have himg : (2 ^ f) ^ 2 ≤ Nat.card (C'.map (QuotientGroup.mk' (d.A₁.subgroupOf d.A₃))) := by
    have h1 := s39a1_card_inf_ker_mul (QuotientGroup.mk' (d.A₁.subgroupOf d.A₃)) C'
    have h2 : Nat.card C' = (2 ^ f) ^ 3 := by
      rw [hC', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv, hCcard]
    have hA1le : d.A₁ ⊓ centralizer (d.I₂ : Set G) ≤ d.A₃ := inf_le_left.trans d.A₁_le_A₃
    have hle : C' ⊓ (QuotientGroup.mk' (d.A₁.subgroupOf d.A₃)).ker ≤
        (d.A₁ ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.A₃ := by
      intro x hx
      have hx0 : x ∈ C' := (Subgroup.mem_inf.1 hx).1
      rw [hC', Subgroup.mem_subgroupOf, ← hCA] at hx0
      have hx2 : x ∈ d.A₁.subgroupOf d.A₃ := by
        rw [← QuotientGroup.ker_mk' (d.A₁.subgroupOf d.A₃)]
        exact (Subgroup.mem_inf.1 hx).2
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
        ⟨Subgroup.mem_subgroupOf.1 hx2, (Subgroup.mem_inf.1 hx0).2⟩)
    have h3 : Nat.card (C' ⊓ (QuotientGroup.mk' (d.A₁.subgroupOf d.A₃)).ker : Subgroup d.A₃) ≤
        2 ^ f :=
      calc _ ≤ Nat.card ((d.A₁ ⊓ centralizer (d.I₂ : Set G)).subgroupOf d.A₃) :=
            Subgroup.card_le_of_le hle
        _ = Nat.card (d.A₁ ⊓ centralizer (d.I₂ : Set G) : Subgroup G) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA1le).toEquiv
        _ = 2 ^ f := hd.s39a1_card_C_A₁_I₂
    have h4 : 2 ^ f * (2 ^ f) ^ 2 ≤
        2 ^ f * Nat.card (C'.map (QuotientGroup.mk' (d.A₁.subgroupOf d.A₃))) :=
      calc 2 ^ f * (2 ^ f) ^ 2 = Nat.card C' := by rw [h2]; ring
        _ = _ := h1
        _ ≤ _ := Nat.mul_le_mul h3 le_rfl
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)
  have hclaim : C'.map (QuotientGroup.mk' (d.A₁.subgroupOf d.A₃)) ≤ W.map ψ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    rw [hC', Subgroup.mem_subgroupOf, ← hCA] at ha
    have haC : (a : G) ∈ centralizer (d.I₂ : Set G) := (Subgroup.mem_inf.1 ha).2
    show (a : d.A₃ ⧸ d.A₁.subgroupOf d.A₃) ∈ W.map ψ
    obtain ⟨s, hs⟩ := hψs (a : d.A₃ ⧸ d.A₁.subgroupOf d.A₃)
    have hfix : ∀ σ ∈ d.I₂, (s : G)⁻¹ * (σ * s * σ⁻¹) ∈ d.F ⊔ d.B₃ := by
      intro σ hσ
      have hσs : σ * (s : G) * σ⁻¹ ∈ d.B₆ := (Subgroup.mem_normalizer_iff.1 (hSM hσ) s).1 s.2
      have hσa : σ * (a : G) * σ⁻¹ = a := by
        rw [Subgroup.mem_centralizer_iff.1 haC σ hσ, mul_inv_cancel_right]
      have hσa' : σ * (a : G) * σ⁻¹ ∈ d.A₃ := by
        rw [hσa]
        exact a.2
      have e := hψeq σ (hI₂ σ hσ) s a hσs hσa' hs
      have e2 : (⟨σ * (a : G) * σ⁻¹, hσa'⟩ : d.A₃) = a := Subtype.ext hσa
      rw [e2] at e
      have hk : s⁻¹ * (⟨σ * s * σ⁻¹, hσs⟩ : d.B₆) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, e, hs, inv_mul_cancel]
      rw [hψk, Subgroup.mem_subgroupOf] at hk
      exact hk
    obtain ⟨c, hc, n, hn, hsc⟩ :=
      s39a1_lift hFB d.B₆_le_normalizer hSM hSN d.isPGroup_B₆_caseB hodd s.2 hfix
    have hc1 : c ∈ d.B₆ := (Subgroup.mem_inf.1 hc).1
    have hn' : (⟨n, hFB hn⟩ : d.B₆) ∈ ψ.ker := by
      rw [hψk, Subgroup.mem_subgroupOf]
      exact hn
    have hs' : s = (⟨c, hc1⟩ : d.B₆) * (⟨n, hFB hn⟩ : d.B₆) := Subtype.ext hsc
    refine Subgroup.mem_map.2 ⟨⟨c, hc1⟩, ?_, ?_⟩
    · rw [hW, Subgroup.mem_subgroupOf]
      exact hc
    · rw [← hs, hs', map_mul, MonoidHom.mem_ker.1 hn', mul_one]
  have hmain := s39a1_card_inf_ker_mul ψ W
  calc 2 * (2 ^ f) ^ 6 = 2 * (2 ^ f) ^ 4 * (2 ^ f) ^ 2 := by ring
    _ ≤ Nat.card (W ⊓ ψ.ker : Subgroup d.B₆) * Nat.card (W.map ψ) :=
        Nat.mul_le_mul hker (himg.trans (Subgroup.card_le_of_le hclaim))
    _ = Nat.card W := hmain.symm
    _ = Nat.card (d.B₆ ⊓ centralizer (d.I₂ : Set G) : Subgroup G) := by
        rw [hW]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv

theorem Hyp.s39a1_centralizer_E_eq_bot (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {S : Subgroup G} (hS : S ≤ d.I) (hA : d.A₂ ⊓ centralizer (S : Set G) = ⊥) :
    d.E ⊓ centralizer (S : Set G) = ⊥ := by
  obtain ⟨-, -, -, hEB, ⟨ψ, -, hker, -, hequiv⟩, -⟩ := hd.sec3_6 hGMS
  have hSC : ∀ σ ∈ S, σ ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G) :=
    fun σ hσ => ⟨hd.normalizer_ZtP_le_normalizer_B₂ (hd.I_le_H (hS hσ)).1, (hd.I_le_H (hS hσ)).2⟩
  have hSA : ∀ σ ∈ S, ∀ a ∈ d.A₂, σ * a * σ⁻¹ ∈ d.A₂ := fun σ hσ a ha =>
    hd.conj_mem_A₂ (hd.I_le_H (hS hσ)).1 (hd.I_le_H (hS hσ)).2 ha
  have hSnA : S ≤ normalizer (d.A₂ : Set G) := fun σ hσ =>
    Subgroup.mem_normalizer_fintype (fun a ha => hSA σ hσ a ha)
  have hSnZ : S ≤ normalizer (d.Zp : Set G) := hS.trans d.I_le_normalizer_Zp
  have hSodd : Odd (Nat.card S) := Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le hS)
  have hA₂Z : d.A₂ ≤ normalizer (d.Zp : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer d.Zp_le_A₂).mp d.normal_Zp_subgroupOf_A₂
  have hA₂p : IsPGroup 2 d.A₂ := d.isPGroup_P.to_le d.A₂_le_P
  have htC : d.t ∈ centralizer (S : Set G) := Subgroup.mem_centralizer_iff.2 fun σ hσ =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hSC σ hσ).2)
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxC⟩
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨x, hxE⟩)
  have hfix : ∀ σ ∈ S, (a : G)⁻¹ * (σ * a * σ⁻¹) ∈ d.Zp := by
    intro σ hσ
    have hxσ : σ * x * σ⁻¹ = x := by
      rw [Subgroup.mem_centralizer_iff.1 hxC σ hσ, mul_inv_cancel_right]
    have hσE : σ * (⟨x, hxE⟩ : d.E) * σ⁻¹ ∈ d.E := by
      change σ * x * σ⁻¹ ∈ d.E
      rw [hxσ]
      exact hxE
    have h1 := hequiv σ (hSC σ hσ) ⟨x, hxE⟩ a hσE (hSA σ hσ a a.2) ha.symm
    have h2 : (⟨σ * (⟨x, hxE⟩ : d.E) * σ⁻¹, hσE⟩ : d.E) = ⟨x, hxE⟩ := Subtype.ext hxσ
    rw [h2, ← ha, QuotientGroup.eq] at h1
    exact h1
  obtain ⟨c, hc, n, hn, hcn⟩ := s39a1_lift d.Zp_le_A₂ hA₂Z hSnA hSnZ hA₂p hSodd a.2 hfix
  have hc1 : c = 1 := by
    rw [← Subgroup.mem_bot, ← hA]
    exact hc
  have haZ : (a : G) ∈ d.Zp := by
    rw [hcn, hc1, one_mul]
    exact hn
  have hψ : (⟨x, hxE⟩ : d.E) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, ← ha]
    exact (QuotientGroup.eq_one_iff a).2 haZ
  rw [hker] at hψ
  have hxVA : x ∈ d.V ⊔ d.A₂ := hψ
  have hxB₄ : x ∈ d.B₄ := hd.VA_le_B₄ hxVA
  have hκ1 : x⁻¹ * d.t * x * d.t = 1 := by
    have hκC : x⁻¹ * d.t * x * d.t ∈ centralizer (S : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxC) htC)
        hxC) htC
    have hκ : x⁻¹ * d.t * x * d.t ∈ d.A₂ ⊓ centralizer (S : Set G) :=
      ⟨d.Zp_le_A₂ (hd.cr_mem hxB₄), hκC⟩
    rw [hA] at hκ
    exact hκ
  have hxA₂ : x ∈ d.A₂ := by
    rw [← hEB]
    exact ⟨hxE, (hd.cr_eq_one_iff hxB₄).1 hκ1⟩
  have hx : x ∈ d.A₂ ⊓ centralizer (S : Set G) := ⟨hxA₂, hxC⟩
  rw [hA] at hx
  exact hx

theorem Hyp.s39a1_card_centralizer_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    (2 ^ f) ^ 6 ≤ Nat.card (d.E ⊓ centralizer (d.I₅ : Set G) : Subgroup G) := by
  obtain ⟨-, -, -, hEB₂, ⟨ψ, hψs, hψk, -, hψc⟩, -, -, -⟩ := hd.sec3_6 hGMS
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, -⟩ := d.sec2_1_two hd.two_le
  have hSI : d.I₅ ≤ d.I := d.I₅_le_I
  have hSodd : Odd (Nat.card d.I₅) := Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le hSI)
  have hA₂E : d.A₂ ≤ d.E := hd.A₂_le_E hGMS
  have hNE : d.V ⊔ d.A₂ ≤ d.E := sup_le d.V_le_E hA₂E
  have hC₅A₂ : d.P ⊓ centralizer (d.I₅ : Set G) ≤ d.A₂ :=
    le_sup_right.trans (h9.ge.trans inf_le_left)
  have hE2 : IsPGroup 2 d.E := hd.s39a1_isPGroup_E hGMS
  have hSE : d.I₅ ≤ normalizer (d.E : Set G) := hSI.trans (hd.s39a1_I_le_normalizer_E hGMS)
  have hSBt : d.I₅ ≤ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G) := fun i hi =>
    ⟨hd.normalizer_ZtP_le_normalizer_B₂ (hd.I_le_H (hSI hi)).1, (hd.I_le_H (hSI hi)).2⟩
  have hSA₂ : d.I₅ ≤ normalizer (d.A₂ : Set G) := fun i hi => by
    rw [← hEB₂]
    exact inf_normalizer_le_normalizer_inf ⟨hSE hi, (hSBt hi).1⟩
  have hSV : d.I₅ ≤ normalizer (d.V : Set G) := hSI.trans hd.I_le_normalizer_V
  have hSN : d.I₅ ≤ normalizer ((d.V ⊔ d.A₂ : Subgroup G) : Set G) := fun i hi =>
    inf_normalizer_le_normalizer_sup d.V d.A₂ ⟨hSV hi, hSA₂ hi⟩
  have hEN : d.E ≤ normalizer ((d.V ⊔ d.A₂ : Subgroup G) : Set G) := by
    have hn : ((d.V ⊔ d.A₂).subgroupOf d.E).Normal := by
      rw [← hψk]
      infer_instance
    exact (normal_subgroupOf_iff_le_normalizer hNE).1 hn
  have hker : ∀ e : d.E, ψ e = 1 ↔ (e : G) ∈ d.V ⊔ d.A₂ := fun e => by
    rw [← MonoidHom.mem_ker, hψk, mem_subgroupOf]
  have hcard := s39a1_card_inf_ker_mul ψ ((d.E ⊓ centralizer (d.I₅ : Set G)).subgroupOf d.E)
  have hWc : Nat.card ((d.E ⊓ centralizer (d.I₅ : Set G)).subgroupOf d.E) =
      Nat.card (d.E ⊓ centralizer (d.I₅ : Set G) : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 : (2 ^ f) ^ 4 ≤ Nat.card ((d.E ⊓ centralizer (d.I₅ : Set G)).subgroupOf d.E ⊓
      ψ.ker : Subgroup d.E) := by
    have hle : d.V ⊔ (d.P ⊓ centralizer (d.I₅ : Set G)) ≤ d.E :=
      sup_le d.V_le_E (hC₅A₂.trans hA₂E)
    rw [← (hd.card_V_sup_C₅).2, ← Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    refine Subgroup.card_le_of_le fun x hx => ?_
    rw [mem_subgroupOf] at hx
    have hxC : (x : G) ∈ centralizer (d.I₅ : Set G) :=
      (sup_le hd.V_le_centralizer_I₅ inf_le_right) hx
    have hxN : (x : G) ∈ d.V ⊔ d.A₂ := (sup_le le_sup_left (hC₅A₂.trans le_sup_right)) hx
    refine ⟨mem_subgroupOf.2 ⟨x.2, hxC⟩, ?_⟩
    rw [hψk]
    exact mem_subgroupOf.2 hxN
  have hZC : d.Zp ≤ d.P ⊓ centralizer (d.I₅ : Set G) := hd.Zp_le_C₅
  have hZA : d.Zp ≤ d.A₂ := hZC.trans hC₅A₂
  have hXc : Nat.card (((d.P ⊓ centralizer (d.I₅ : Set G)).subgroupOf d.A₂).map
      (QuotientGroup.mk' (d.Zp.subgroupOf d.A₂))) = (2 ^ f) ^ 2 := by
    have e := s39a1_card_inf_ker_mul (QuotientGroup.mk' (d.Zp.subgroupOf d.A₂))
      ((d.P ⊓ centralizer (d.I₅ : Set G)).subgroupOf d.A₂)
    rw [QuotientGroup.ker_mk', inf_eq_right.2 (subgroupOf_mono _ hZC),
      Nat.card_congr (subgroupOfEquivOfLe hC₅A₂).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv, hd.card_C₅, d.card_Zp] at e
    have hq : 0 < 2 ^ f := Nat.pos_of_ne_zero (pow_ne_zero _ two_ne_zero)
    refine (Nat.eq_of_mul_eq_mul_left hq ?_).symm
    rw [← e]
    ring
  have hXW : ((d.P ⊓ centralizer (d.I₅ : Set G)).subgroupOf d.A₂).map
      (QuotientGroup.mk' (d.Zp.subgroupOf d.A₂)) ≤
      ((d.E ⊓ centralizer (d.I₅ : Set G)).subgroupOf d.E).map ψ := by
    rintro _ ⟨a, ha, rfl⟩
    replace ha : (a : G) ∈ d.P ⊓ centralizer (d.I₅ : Set G) := ha
    obtain ⟨e, he⟩ := hψs ((QuotientGroup.mk' (d.Zp.subgroupOf d.A₂)) a)
    have hfix : ∀ s ∈ d.I₅, (e : G)⁻¹ * (s * e * s⁻¹) ∈ d.V ⊔ d.A₂ := by
      intro s hs
      have hseE : s * (e : G) * s⁻¹ ∈ d.E := (mem_normalizer_iff.1 (hSE hs) e).1 e.2
      have hsaA : s * (a : G) * s⁻¹ ∈ d.A₂ := (mem_normalizer_iff.1 (hSA₂ hs) a).1 a.2
      have hsa : s * (a : G) * s⁻¹ = a := by
        rw [mem_centralizer_iff.1 ha.2 s hs, mul_inv_cancel_right]
      have h2 : ψ ⟨s * e * s⁻¹, hseE⟩ = ψ e := by
        rw [hψc s (hSBt hs) e a hseE hsaA he, he]
        exact congrArg _ (Subtype.ext hsa)
      have h3 : ψ (e⁻¹ * ⟨s * e * s⁻¹, hseE⟩) = 1 := by
        rw [map_mul, map_inv, h2, inv_mul_cancel]
      exact (hker _).1 h3
    obtain ⟨c, hc, n, hn, hcn⟩ := s39a1_lift hNE hEN hSE hSN hE2 hSodd e.2 hfix
    refine ⟨⟨c, hc.1⟩, mem_subgroupOf.2 hc, ?_⟩
    have hnE : n ∈ d.E := hNE hn
    have hψn : ψ ⟨n, hnE⟩ = 1 := (hker _).2 hn
    have hce : (⟨c, hc.1⟩ : d.E) = e * (⟨n, hnE⟩ : d.E)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcn, mul_inv_cancel_right]
    rw [hce, map_mul, map_inv, hψn, inv_one, mul_one, he]
  have h2 : (2 ^ f) ^ 2 ≤ Nat.card (((d.E ⊓ centralizer (d.I₅ : Set G)).subgroupOf d.E).map ψ) :=
    hXc ▸ Subgroup.card_le_of_le hXW
  calc (2 ^ f) ^ 6 = (2 ^ f) ^ 4 * (2 ^ f) ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul h1 h2
    _ = _ := hcard.symm
    _ = _ := hWc

omit [Finite G] in
theorem s39a1_cardQ_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  mem_normalizer_iff.2 fun x => by
    simp only [Subgroup.mem_inf]
    exact and_congr (mem_normalizer_iff.1 hA x) (mem_normalizer_iff.1 hB x)

omit [Finite G] in
theorem s39a1_cardQ_mem_centralizer_sup {A B : Subgroup G} {x : G}
    (hA : x ∈ centralizer (A : Set G)) (hB : x ∈ centralizer (B : Set G)) :
    x ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hsub : A ⊔ B ≤ centralizer ({x} : Set G) :=
    sup_le (fun y hy => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hA y hy))
      (fun y hy => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hB y hy))
  exact mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hsub hy)

theorem ProductCaseHyp.s39a1_card_Q (hp : d.ProductCaseHyp) :
    (2 ^ f) ^ 6 ≤ Nat.card (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ : Subgroup G) := by
  have hd : d.Hyp := hp.hyp
  have hGMS := hp.gms
  obtain ⟨hIB, hID⟩ := hd.s39a1_I_le_normalizer_B₆ hGMS
  obtain ⟨hDB, hBD, -, hfac⟩ := hd.s39a1_D_facts hGMS
  set C₂ : Subgroup G := centralizer (d.I₂ : Set G)
  set Y : Subgroup G := d.B₆ ⊓ C₂
  set Q : Subgroup G := d.D ⊓ C₂ ⊓ d.M₂
  set T : Subgroup G := d.I ⊓ d.N₂
  have hIC : d.I ≤ C₂ := fun x hx =>
    mem_centralizer_iff.2 fun y hy => d.I_comm (d.I₂_le_I hy) hx
  have hTI : T ≤ d.I := inf_le_left
  have hTC : T ≤ C₂ := hTI.trans hIC
  have hTM : T ≤ d.M₂ := inf_le_right.trans d.s39a1_N₂_le_M₂
  have hCN : C₂ ≤ normalizer (d.M₂ : Set G) := d.s39a1_centralizer_le_normalizer_M₂
  have hQY : Q ≤ Y := fun x hx => ⟨hDB hx.1.1, hx.1.2⟩
  have hYQ : Y ≤ normalizer (Q : Set G) := fun y hy =>
    s39a1_cardQ_mem_normalizer_inf
      (s39a1_cardQ_mem_normalizer_inf (hBD hy.1) (le_normalizer hy.2)) (hCN hy.2)
  have hTY : T ≤ normalizer (Y : Set G) := fun x hx =>
    s39a1_cardQ_mem_normalizer_inf (hIB (hTI hx)) (le_normalizer (hTC hx))
  have hTQ : T ≤ normalizer (Q : Set G) := fun x hx =>
    s39a1_cardQ_mem_normalizer_inf
      (s39a1_cardQ_mem_normalizer_inf (hID (hTI hx)) (le_normalizer (hTC hx))) (hCN (hTC hx))
  have hY2 : IsPGroup 2 Y := d.isPGroup_B₆_caseB.to_le inf_le_left
  have hTodd : Odd (Nat.card T) := Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le hTI)
  have hfix : ∀ y ∈ Y, ∀ s ∈ T, y⁻¹ * (s * y * s⁻¹) ∈ Q := by
    intro y hy s hs
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨c, hc, n, hn, rfl⟩ := hfac y hy.1
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      have hst : Commute s d.t := hd.comm_t (d.pull_le_L _ (hTI hs))
      have hcs : d.t ^ k * s = s * d.t ^ k := (hst.symm.zpow_left k).eq
      have hcs' : (d.t ^ k)⁻¹ * s * d.t ^ k = s := by
        rw [mul_assoc, ← hcs, inv_mul_cancel_left]
      have e : (d.t ^ k * n)⁻¹ * (s * (d.t ^ k * n) * s⁻¹) =
          n⁻¹ * (((d.t ^ k)⁻¹ * s * d.t ^ k) * n * s⁻¹) := by group
      rw [e, hcs']
      exact d.D.mul_mem (d.D.inv_mem hn) ((mem_normalizer_iff.1 (hID (hTI hs)) n).1 hn)
    · exact C₂.mul_mem (C₂.inv_mem hy.2)
        (C₂.mul_mem (C₂.mul_mem (hTC hs) hy.2) (C₂.inv_mem (hTC hs)))
    · have h1 : y⁻¹ * s * y⁻¹⁻¹ ∈ d.M₂ :=
        (mem_normalizer_iff.1 (hCN (C₂.inv_mem hy.2)) s).1 (hTM hs)
      have e : y⁻¹ * (s * y * s⁻¹) = (y⁻¹ * s * y⁻¹⁻¹) * s⁻¹ := by group
      rw [e]
      exact d.M₂.mul_mem h1 (d.M₂.inv_mem (hTM hs))
  have hYT : Y ⊓ centralizer (T : Set G) ≤ zpowers d.t := by
    have hS : d.I₂ ⊔ T ≤ d.I := sup_le d.I₂_le_I hTI
    have hA : d.A₃ ⊓ centralizer ((d.I₂ ⊔ T : Subgroup G) : Set G) = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      rw [← (d.sec2_1_four hd.two_le).2.1]
      exact ⟨⟨d.A₃_le_P hx.1, centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx.2⟩,
        centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) hx.2⟩
    refine le_trans ?_ (hd.s39a1_centralizer_B₆_le hGMS hS hA)
    exact fun x hx => ⟨hx.1.1, s39a1_cardQ_mem_centralizer_sup hx.1.2 hx.2⟩
  have hlift : ∀ y ∈ Y, ∃ c ∈ Y ⊓ centralizer (T : Set G), ∃ n ∈ Q, y = c * n :=
    fun y hy => s39a1_lift hQY hYQ hTY hTQ hY2 hTodd hy (hfix y hy)
  let φ : (Y ⊓ centralizer (T : Set G) : Subgroup G) × Q → Y := fun p =>
    ⟨p.1 * p.2, Y.mul_mem p.1.2.1 (hQY p.2.2)⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc, n, hn, rfl⟩ := hlift y hy
    exact ⟨(⟨c, hc⟩, ⟨n, hn⟩), rfl⟩
  have h1 : Nat.card Y ≤ Nat.card (Y ⊓ centralizer (T : Set G) : Subgroup G) * Nat.card Q := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective φ hφ
  have h2 : Nat.card (Y ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 := by
    rw [← hd.card_zpowers_t]
    exact Subgroup.card_le_of_le hYT
  have h3 : 2 * (2 ^ f) ^ 6 ≤ 2 * Nat.card Q :=
    (hd.s39a1_card_centralizer_B₆ hGMS).trans (h1.trans (Nat.mul_le_mul h2 le_rfl))
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

theorem ProductCaseHyp.s39a1_sylowE₅ (hp : d.ProductCaseHyp) :
    IsSylowOf 2 (d.E ⊓ centralizer (d.I₅ : Set G)) d.M₅ := by
  have hd : d.Hyp := hp.hyp
  have hGMS := hp.gms
  have hX2 : IsPGroup 2 (d.E ⊓ centralizer (d.I₅ : Set G) : Subgroup G) :=
    (hd.s39a1_isPGroup_E hGMS).to_le inf_le_left
  have hXN : d.E ⊓ centralizer (d.I₅ : Set G) ≤ normalizer (d.M₅ : Set G) :=
    inf_le_right.trans d.s39a1_centralizer_le_normalizer_M₅
  have hTM : d.I ⊓ d.N₅ ≤ d.M₅ := inf_le_right.trans d.s39a1_N₅_le_M₅
  have hTC : d.I ⊓ d.N₅ ≤ centralizer (d.I₅ : Set G) :=
    inf_le_right.trans d.s39a1_N₅_le_centralizer_I₅
  have hTX : d.I ⊓ d.N₅ ≤
      normalizer ((d.E ⊓ centralizer (d.I₅ : Set G) : Subgroup G) : Set G) := fun τ hτ =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hd.s39a1_I_le_normalizer_E hGMS hτ.1, Subgroup.le_normalizer (hTC hτ)⟩
  have hXXM : d.E ⊓ centralizer (d.I₅ : Set G) ≤
      normalizer ((d.E ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hXN hx⟩
  have hTXM : d.I ⊓ d.N₅ ≤
      normalizer ((d.E ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ : Subgroup G) : Set G) :=
    fun τ hτ => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTX hτ, Subgroup.le_normalizer (hTM hτ)⟩
  have hTodd : Odd (Nat.card (d.I ⊓ d.N₅ : Subgroup G)) :=
    Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le inf_le_left)
  have hSI : d.I₅ ⊔ d.I ⊓ d.N₅ ≤ d.I := sup_le d.I₅_le_I inf_le_left
  have hA : d.A₂ ⊓ centralizer ((d.I₅ ⊔ d.I ⊓ d.N₅ : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff, ← (d.sec2_1_four hd.two_le).2.2.2]
    rintro y ⟨hyA, hyC⟩
    exact ⟨⟨d.A₂_le_P hyA, Subgroup.centralizer_le
      (le_sup_left : d.I₅ ≤ d.I₅ ⊔ d.I ⊓ d.N₅) hyC⟩,
      Subgroup.centralizer_le (le_sup_right : d.I ⊓ d.N₅ ≤ d.I₅ ⊔ d.I ⊓ d.N₅) hyC⟩
  have hE := hd.s39a1_centralizer_E_eq_bot hGMS hSI hA
  have hXM : d.E ⊓ centralizer (d.I₅ : Set G) ≤ d.M₅ := by
    intro x hx
    have hfix : ∀ τ ∈ d.I ⊓ d.N₅,
        x⁻¹ * (τ * x * τ⁻¹) ∈ d.E ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ := by
      intro τ hτ
      have h0 : x⁻¹ * (τ * x * τ⁻¹) ∈ d.E ⊓ centralizer (d.I₅ : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hx)
          ((Subgroup.mem_normalizer_iff.1 (hTX hτ) x).1 hx)
      have h1 : x⁻¹ * τ * x ∈ d.M₅ :=
        (Subgroup.mem_normalizer_iff''.1 (hXN hx) τ).1 (hTM hτ)
      have h2 : x⁻¹ * (τ * x * τ⁻¹) = x⁻¹ * τ * x * τ⁻¹ := by group
      have h3 : x⁻¹ * (τ * x * τ⁻¹) ∈ d.M₅ := by
        rw [h2]
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hTM hτ))
      exact ⟨h0, h3⟩
    obtain ⟨c, hc, n, hn, rfl⟩ := s39a1_lift inf_le_left hXXM hTX hTXM hX2 hTodd hx hfix
    have hc1 : c = 1 := by
      have hcS : c ∈ d.E ⊓ centralizer ((d.I₅ ⊔ d.I ⊓ d.N₅ : Subgroup G) : Set G) := by
        refine ⟨hc.1.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        have hle : d.I₅ ⊔ d.I ⊓ d.N₅ ≤ centralizer ({c} : Set G) := sup_le
          (fun i hi => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 hc.1.2 i hi))
          (fun i hi => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 hc.2 i hi))
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
      rw [hE] at hcS
      exact hcS
    rw [hc1, one_mul]
    exact hn.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hX2.comap_subtype (K := d.M₅)).exists_le_sylow
  have hQS : IsSylowOf 2 ((Q : Subgroup d.M₅).map d.M₅.subtype) d.M₅ := ⟨Q, rfl⟩
  have hXQ : d.E ⊓ centralizer (d.I₅ : Set G) ≤ (Q : Subgroup d.M₅).map d.M₅.subtype :=
    fun x hx => ⟨⟨x, hXM hx⟩, hQ hx, rfl⟩
  have heq : d.E ⊓ centralizer (d.I₅ : Set G) = (Q : Subgroup d.M₅).map d.M₅.subtype :=
    Subgroup.eq_of_le_of_card_ge hXQ
      ((hp.s39a1_card_le₅ hQS.le hQS.isPGroup).trans (hd.s39a1_card_centralizer_E hGMS))
  rw [heq]
  exact hQS

theorem Hyp.s39a1_exists_z₂ (hd : d.Hyp) :
    ∃ z : G, z ∈ d.N₂ ∧ z ∈ d.P ∧ z ∈ d.A₃ ∧ z ≠ 1 := by
  have hcard : Nat.card d.CPI₂ = (2 ^ f) ^ 3 :=
    (d.card_pull (patSub_le_U sI₂ isPattern_sI₂)).trans card_patSub_sI₂
  have h4 := hd.four_le
  have h1 : 1 < (2 ^ f) ^ 3 :=
    lt_of_lt_of_le (by omega : 1 < 2 ^ f) (Nat.le_self_pow (by norm_num) _)
  rcases d.CPI₂.bot_or_exists_ne_one with h0 | ⟨z, hz, hz1⟩
  · rw [h0, Subgroup.card_bot] at hcard
    omega
  · exact ⟨z, d.pull_mono patSub_sI₂_le_N₂sub hz, d.pull_mono (patSub_le_U _ _) hz,
      d.pull_mono patSub_I₂_le_Ssub hz, hz1⟩

theorem Hyp.s39a1_exists_z₅ (hd : d.Hyp) :
    ∃ z : G, z ∈ d.N₅ ∧ z ∈ d.A₂ ∧ z ∈ d.A₃ ∧ z ∈ centralizer (d.I₅ : Set G) ∧ z ≠ 1 := by
  have hcard := hd.card_C₅
  have h4 := hd.four_le
  have h1 : 1 < (2 ^ f) ^ 3 :=
    lt_of_lt_of_le (by omega : 1 < 2 ^ f) (Nat.le_self_pow (by norm_num) _)
  rcases (d.P ⊓ centralizer (d.I₅ : Set G) : Subgroup G).bot_or_exists_ne_one with
    h0 | ⟨z, hz, hz1⟩
  · rw [h0, Subgroup.card_bot] at hcard
    omega
  · have hz' : z ∈ d.pull (patSub h sI₅ isPattern_sI₅) := hd.P_inf_centralizer_I₅ ▸ hz
    exact ⟨z, d.C₅_le_N₅ hz', d.pull_mono (patSub_I₅_le_A₂sub_inf_Ssub.trans inf_le_left) hz',
      d.pull_mono (patSub_I₅_le_A₂sub_inf_Ssub.trans inf_le_right) hz', hz.2, hz1⟩

theorem sec39a1_of_hyp (hTI : CaseBParts.SU3SylowTIStatement) (hp : d.ProductCaseHyp)
    (k8 : d.Know8) (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) :
    d.Sec39a1 S := by
  have hd : d.Hyp := hp.hyp
  have hGMS := hp.gms
  have hL₂ : d.L₂ = d.E ⊔ d.M₂ := k8.s8.1
  obtain ⟨hSH, hA⟩ := hp.s39a1_sylow₂ hL₂ hS
  have hDf := hd.s39a1_D_facts hGMS
  have hQ2 : IsPGroup 2 (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ : Subgroup G) :=
    (d.isPGroup_B₆_caseB.to_le hDf.1).to_le (inf_le_left.trans inf_le_left)
  have hRcard : Nat.card (S ⊓ d.M₂ : Subgroup G) ≤ (2 ^ f) ^ 6 :=
    hp.s39a1_card_le inf_le_right (hS.isPGroup.to_le inf_le_left)
  have hB : d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ = S ⊓ centralizer (d.I₂ : Set G) := by
    rw [hSH]
    obtain ⟨z, hzN, hzP, hzA, hz1⟩ := hd.s39a1_exists_z₂
    have hle : d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ ≤ S ⊓ d.M₂ :=
      hp.s39a1_ti_lift hTI hA inf_le_right hQ2
        (z := z) ⟨⟨hDf.2.2.1 hzA, d.N₂_le_centralizer_I₂ hzN⟩, d.s39a1_N₂_le_M₂ hzN⟩
        ⟨hP hzP, d.s39a1_N₂_le_M₂ hzN⟩ hzN hz1
    exact Subgroup.eq_of_le_of_card_ge hle (hRcard.trans hp.s39a1_card_Q)
  have hC := hp.s39a1_sylowE₅
  have hD : d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ = d.E ⊓ centralizer (d.I₅ : Set G) := by
    obtain ⟨z, hzN, hzA₂, hzA₃, hzC, hz1⟩ := hd.s39a1_exists_z₅
    obtain ⟨hM₅, hC₅, -⟩ := hd.s39a1_conj_r
    have hQcard : Nat.card (d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ : Subgroup G) =
        Nat.card (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ : Subgroup G) := by
      have e : (d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂).map (MulAut.conj d.r).toMonoidHom =
          d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d.r).injective,
          Subgroup.map_inf_eq _ _ _ (MulAut.conj d.r).injective, hM₅, hC₅,
          hd.s39a1_map_conj_r_D hGMS]
      rw [← e, Subgroup.card_map_of_injective (MulAut.conj d.r).injective]
    have hQ2' : IsPGroup 2 (d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ : Subgroup G) :=
      (d.isPGroup_B₆_caseB.to_le hDf.1).to_le (inf_le_left.trans inf_le_left)
    have hle : d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ ≤ d.E ⊓ centralizer (d.I₅ : Set G) :=
      hp.s39a1_ti_lift₅ hTI hC inf_le_right hQ2'
        (z := z) ⟨⟨hDf.2.2.1 hzA₃, hzC⟩, d.s39a1_N₅_le_M₅ hzN⟩
        ⟨hd.A₂_le_E hGMS hzA₂, hzC⟩ hzN hz1
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hQcard]
    exact (hp.s39a1_card_le₅ hC.le hC.isPGroup).trans hp.s39a1_card_Q
  exact ⟨hSH ▸ hA, hB, hC, hD⟩

end Data

namespace CaseBParts

theorem sec39a1 : Sec39a1Statement :=
  fun hTI _ _ _ _ _ _ _ _ hp k8 S hS hP => Data.sec39a1_of_hyp hTI hp k8 S hS hP

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
