module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step27
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SCoord
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step25

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec2

section Trichotomy

variable {L Z : Subgroup G}

omit [Finite G] in
theorem conj_inv_mul_mem {q a b : G} (hqZ : q ∈ normalizer (Z : Set G)) (h : a⁻¹ * b ∈ Z) :
    (q * a * q⁻¹)⁻¹ * (q * b * q⁻¹) ∈ Z := by
  have e : (q * a * q⁻¹)⁻¹ * (q * b * q⁻¹) = q * (a⁻¹ * b) * q⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp hqZ _).mp h

omit [Finite G] in
theorem inv_mul_mem_trans {a b c : G} (hab : a⁻¹ * b ∈ Z) (hbc : b⁻¹ * c ∈ Z) : a⁻¹ * c ∈ Z := by
  have e : a⁻¹ * c = (a⁻¹ * b) * (b⁻¹ * c) := by group
  rw [e]
  exact Z.mul_mem hab hbc

omit [Finite G] in
theorem inv_mul_mem_symm {a b : G} (hab : a⁻¹ * b ∈ Z) : b⁻¹ * a ∈ Z := by
  have := Z.inv_mem hab
  simpa using this

theorem trichotomy (h4 : Z.relIndex L = 4) {p q : G} (hpL : p ∈ normalizer (L : Set G))
    (hpZ : p ∈ normalizer (Z : Set G))
    (hp3 : p ^ 3 = 1) (hpfix : ∀ a ∈ L, a⁻¹ * (p * a * p⁻¹) ∈ Z → a ∈ Z)
    (hqL : q ∈ normalizer (L : Set G)) (hqZ : q ∈ normalizer (Z : Set G))
    (hpq : ∀ a ∈ L, (q * (p * a * p⁻¹) * q⁻¹)⁻¹ * (p * (q * a * q⁻¹) * p⁻¹) ∈ Z) :
    ∃ r ∈ ({1, p, p⁻¹} : Set G), ∀ b ∈ L, (r * b * r⁻¹)⁻¹ * (q * b * q⁻¹) ∈ Z := by
  have hp' : p⁻¹ = p * p := by
    rw [inv_eq_iff_mul_eq_one, ← hp3, pow_three]
  have hcL : ∀ {n : G}, n ∈ normalizer (L : Set G) → ∀ a ∈ L, n * a * n⁻¹ ∈ L :=
    fun hn a ha => (mem_normalizer_iff.mp hn a).mp ha
  have hcZ : ∀ {n : G}, n ∈ normalizer (Z : Set G) → ∀ a, a ∈ Z ↔ n * a * n⁻¹ ∈ Z :=
    fun hn a => mem_normalizer_iff.mp hn a
  obtain ⟨a₀, ha₀, ha₀Z⟩ : ∃ a₀ ∈ L, a₀ ∉ Z := by
    by_contra hall
    push Not at hall
    have : Z.relIndex L = 1 := relIndex_eq_one.mpr hall
    omega
  set a₁ := p * a₀ * p⁻¹ with ha₁def
  set a₂ := p⁻¹ * a₀ * p⁻¹⁻¹ with ha₂def
  have ha₁ : a₁ ∈ L := hcL hpL a₀ ha₀
  have ha₂ : a₂ ∈ L := hcL (inv_mem hpL) a₀ ha₀
  have ha₁Z : a₁ ∉ Z := fun h => ha₀Z ((hcZ hpZ a₀).mpr h)
  have ha₂Z : a₂ ∉ Z := fun h => ha₀Z ((hcZ (inv_mem hpZ) a₀).mpr h)
  have h01 : a₀⁻¹ * a₁ ∉ Z := fun h => ha₀Z (hpfix a₀ ha₀ h)
  have h02 : a₀⁻¹ * a₂ ∉ Z := fun h => by
    apply h01
    have h' := Sec2.conj_inv_mul_mem hpZ h
    have e : (p * a₀ * p⁻¹)⁻¹ * (p * a₂ * p⁻¹) = (a₀⁻¹ * a₁)⁻¹ := by
      rw [ha₂def, ha₁def]
      group
    rw [e] at h'
    simpa using Z.inv_mem h'
  have h12 : a₁⁻¹ * a₂ ∉ Z := fun h => by
    apply h02
    have h' := Sec2.conj_inv_mul_mem hpZ h
    have e : (p * a₁ * p⁻¹)⁻¹ * (p * a₂ * p⁻¹) = (a₀⁻¹ * a₂)⁻¹ := by
      rw [ha₂def, ha₁def]
      calc (p * (p * a₀ * p⁻¹) * p⁻¹)⁻¹ * (p * (p⁻¹ * a₀ * p⁻¹⁻¹) * p⁻¹)
          = p ^ 2 * a₀⁻¹ * (p ^ 2)⁻¹ * a₀ := by group
        _ = p⁻¹ * a₀⁻¹ * p * a₀ := by rw [sq, ← hp', inv_inv]
        _ = (a₀⁻¹ * (p⁻¹ * a₀ * p⁻¹⁻¹))⁻¹ := by group
    rw [e] at h'
    simpa using Z.inv_mem h'
  have hcover : ∀ b ∈ L, b ∈ Z ∨ a₀⁻¹ * b ∈ Z ∨ a₁⁻¹ * b ∈ Z ∨ a₂⁻¹ * b ∈ Z := fun b hb =>
    mem_or_of_relIndex_eq_four h4 ha₀ ha₁ ha₂ hb ha₀Z ha₁Z ha₂Z h01 h02 h12
  have hpq' : ∀ a ∈ L, (q * (p⁻¹ * a * p⁻¹⁻¹) * q⁻¹)⁻¹ * (p⁻¹ * (q * a * q⁻¹) * p⁻¹⁻¹) ∈ Z := by
    intro a ha
    have h1 := hpq _ (hcL (inv_mem hpL) a ha)
    have e1 : p * (p⁻¹ * a * p⁻¹⁻¹) * p⁻¹ = a := by group
    rw [e1] at h1
    have h2 := Sec2.conj_inv_mul_mem (inv_mem hpZ) (inv_mul_mem_symm h1)
    have e2 : p⁻¹ * (p * (q * (p⁻¹ * a * p⁻¹⁻¹) * q⁻¹) * p⁻¹) * p⁻¹⁻¹ =
        q * (p⁻¹ * a * p⁻¹⁻¹) * q⁻¹ := by group
    rw [e2] at h2
    exact h2
  have hw : q * a₀ * q⁻¹ ∈ L := hcL hqL a₀ ha₀
  have hwZ : q * a₀ * q⁻¹ ∉ Z := fun h => ha₀Z ((hcZ hqZ a₀).mpr h)
  have key : ∀ r : G, r ∈ ({1, p, p⁻¹} : Set G) → (r * a₀ * r⁻¹)⁻¹ * (q * a₀ * q⁻¹) ∈ Z →
      ∀ b ∈ L, (r * b * r⁻¹)⁻¹ * (q * b * q⁻¹) ∈ Z := by
    intro r hr h0 b hb
    have hrp : r * p = p * r := by
      rcases hr with rfl | rfl | rfl
      · group
      · rfl
      · group
    have hrp' : r * p⁻¹ = p⁻¹ * r := by
      calc r * p⁻¹ = p⁻¹ * (p * r) * p⁻¹ := by group
        _ = p⁻¹ * (r * p) * p⁻¹ := by rw [hrp]
        _ = p⁻¹ * r := by group
    have hrZ : r ∈ normalizer (Z : Set G) := by
      rcases hr with rfl | rfl | rfl
      · exact one_mem _
      · exact hpZ
      · exact inv_mem hpZ
    have h1 : (r * a₁ * r⁻¹)⁻¹ * (q * a₁ * q⁻¹) ∈ Z := by
      have k1 := Sec2.conj_inv_mul_mem hpZ h0
      have e : p * (r * a₀ * r⁻¹) * p⁻¹ = r * a₁ * r⁻¹ := by
        rw [ha₁def]
        calc p * (r * a₀ * r⁻¹) * p⁻¹ = (p * r) * a₀ * (p * r)⁻¹ := by group
          _ = (r * p) * a₀ * (r * p)⁻¹ := by rw [hrp]
          _ = r * (p * a₀ * p⁻¹) * r⁻¹ := by group
      rw [e] at k1
      exact inv_mul_mem_trans k1 (inv_mul_mem_symm (hpq a₀ ha₀))
    have h2 : (r * a₂ * r⁻¹)⁻¹ * (q * a₂ * q⁻¹) ∈ Z := by
      have k1 := Sec2.conj_inv_mul_mem (inv_mem hpZ) h0
      have e : p⁻¹ * (r * a₀ * r⁻¹) * p⁻¹⁻¹ = r * a₂ * r⁻¹ := by
        rw [ha₂def]
        calc p⁻¹ * (r * a₀ * r⁻¹) * p⁻¹⁻¹ = (p⁻¹ * r) * a₀ * (p⁻¹ * r)⁻¹ := by group
          _ = (r * p⁻¹) * a₀ * (r * p⁻¹)⁻¹ := by rw [hrp']
          _ = r * (p⁻¹ * a₀ * p⁻¹⁻¹) * r⁻¹ := by group
      rw [e] at k1
      exact inv_mul_mem_trans k1 (inv_mul_mem_symm (hpq' a₀ ha₀))
    have hext : ∀ c ∈ L, (r * c * r⁻¹)⁻¹ * (q * c * q⁻¹) ∈ Z → c⁻¹ * b ∈ Z →
        (r * b * r⁻¹)⁻¹ * (q * b * q⁻¹) ∈ Z := by
      intro c _ hc hcb
      exact inv_mul_mem_trans (inv_mul_mem_symm (Sec2.conj_inv_mul_mem hrZ hcb))
        (inv_mul_mem_trans hc (Sec2.conj_inv_mul_mem hqZ hcb))
    rcases hcover b hb with hbZ | hb0 | hb1 | hb2
    · have e1 : (r * b * r⁻¹)⁻¹ * (q * b * q⁻¹) = (r * b * r⁻¹)⁻¹ * (q * b * q⁻¹) := rfl
      have k1 := (hcZ hrZ b).mp hbZ
      have k2 := (hcZ hqZ b).mp hbZ
      rw [e1]
      exact Z.mul_mem (Z.inv_mem k1) k2
    · exact hext a₀ ha₀ h0 hb0
    · exact hext a₁ ha₁ h1 hb1
    · exact hext a₂ ha₂ h2 hb2
  rcases hcover _ hw with h | h | h | h
  · exact absurd h hwZ
  · refine ⟨1, Set.mem_insert _ _, key 1 (Set.mem_insert _ _) ?_⟩
    simpa using h
  · exact ⟨p, by simp, key p (by simp) h⟩
  · exact ⟨p⁻¹, by simp, key p⁻¹ (by simp) h⟩

omit [Finite G] in
theorem pow_conj_inv_mul_mem {q r : G} (hrL : r ∈ normalizer (L : Set G))
    (hqZ : q ∈ normalizer (Z : Set G))
    (h : ∀ b ∈ L, (r * b * r⁻¹)⁻¹ * (q * b * q⁻¹) ∈ Z) :
    ∀ m : ℕ, ∀ b ∈ L, (r ^ m * b * (r ^ m)⁻¹)⁻¹ * (q ^ m * b * (q ^ m)⁻¹) ∈ Z := by
  intro m
  induction m with
  | zero => intro b _; simp
  | succ m ih =>
    intro b hb
    have hbr : r ^ m * b * (r ^ m)⁻¹ ∈ L :=
      (mem_normalizer_iff.mp ((normalizer (L : Set G)).pow_mem hrL m) b).mp hb
    have e1 : r ^ (m + 1) * b * (r ^ (m + 1))⁻¹ = r * (r ^ m * b * (r ^ m)⁻¹) * r⁻¹ := by
      rw [pow_succ']
      group
    have e2 : q ^ (m + 1) * b * (q ^ (m + 1))⁻¹ = q * (q ^ m * b * (q ^ m)⁻¹) * q⁻¹ := by
      rw [pow_succ']
      group
    rw [e1, e2]
    exact inv_mul_mem_trans (h _ hbr) (conj_inv_mul_mem hqZ (ih b hb))

end Trichotomy

theorem exists_conj_eq_zpow {Γ : Subgroup G} {g k : G} (hg : g ∈ Γ) (hg3 : orderOf g = 3)
    (h9 : ¬ 9 ∣ Nat.card Γ) (hk : k ∈ Γ) {n : ℕ} (hkn : k ^ 3 ^ n = 1) :
    ∃ c ∈ Γ, ∃ j : ℤ, k = c * g ^ j * c⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set g' : ↥Γ := ⟨g, hg⟩ with hg'
  set k' : ↥Γ := ⟨k, hk⟩ with hk'
  have hg'3 : orderOf g' = 3 := by rw [hg', Subgroup.orderOf_mk, hg3]
  have hcardP : Nat.card (zpowers g') = 3 := by rw [Nat.card_zpowers, hg'3]
  have hΓ0 : Nat.card ↥Γ ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ∣ Nat.card ↥Γ := hg'3 ▸ orderOf_dvd_natCard g'
  have hfac : (Nat.card ↥Γ).factorization 3 = 1 := by
    have h1 := (Nat.prime_three.dvd_iff_one_le_factorization hΓ0).mp h3
    have h2 : ¬ 2 ≤ (Nat.card ↥Γ).factorization 3 := fun h =>
      h9 ((Nat.prime_three.pow_dvd_iff_le_factorization hΓ0).mpr h)
    omega
  let Q₀ : Sylow 3 ↥Γ := Sylow.ofCard (zpowers g') (by rw [hcardP, hfac, pow_one])
  have hk'p : IsPGroup 3 (zpowers k') := by
    have hdvd : orderOf k' ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hkn))
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := hk'p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥Γ Q₀ Q
  have hkQ : k' ∈ (Q : Subgroup ↥Γ) := hQ (mem_zpowers k')
  rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hkQ
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hkQ
  refine ⟨c, c.2, j, ?_⟩
  have hj' := congrArg Subtype.val hj
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    SubgroupClass.coe_zpow, hg', hk'] at hj'
  calc k = (c : G) * ((c : G)⁻¹ * k * c) * (c : G)⁻¹ := by group
    _ = (c : G) * g ^ j * (c : G)⁻¹ := by rw [← hj']

theorem small_cases : ∀ v : Fin 5 → ZMod 2, v ≠ 0 → v ≠ 1 →
    (∃ i, v = Pi.single i 1 ∨ v + 1 = Pi.single i 1) ∨
      ∃ i j, i ≠ j ∧ (v = Sec2V4.pair i j ∨ v + 1 = Sec2V4.pair i j) := by
  decide

theorem eq_of_forall_act_eq {i₀ : Fin 5} {w : Fin 5 → ZMod 2} (hw : Sec2V4.IsEven w) (hw0 : w ≠ 0)
    (hfix : ∀ σ ∈ alternatingGroup (Fin 5), σ i₀ = i₀ → Sec2V4.act σ w = w) :
    w = 1 + Pi.single i₀ 1 := by
  have hconst : ∀ j j', j ≠ i₀ → j' ≠ i₀ → w j = w j' := by
    intro j j' hj hj'
    by_cases hjj : j = j'
    · rw [hjj]
    obtain ⟨σ, hσ, hσ0, hσj⟩ := Sec2V4.exists_apply_eq (i := i₀) (j := j) (a := i₀) (b := j')
      (Ne.symm hj) (Ne.symm hj')
    have h1 := congrFun (hfix σ hσ hσ0) j'
    rw [Sec2V4.act_apply] at h1
    have hinv : σ⁻¹ j' = j := Equiv.Perm.inv_eq_iff_eq.mpr hσj.symm
    rw [hinv] at h1
    exact h1
  have key : ∀ (i₀ : Fin 5) (w : Fin 5 → ZMod 2), Sec2V4.IsEven w → w ≠ 0 →
      w = 1 + Pi.single i₀ (1 : ZMod 2) ∨ ∃ j j' : Fin 5, j ≠ i₀ ∧ j' ≠ i₀ ∧ w j ≠ w j' := by
    decide
  rcases key i₀ w hw hw0 with h | ⟨j, j', hj, hj', hne⟩
  · exact h
  · exact absurd (hconst j j' hj hj') hne

section Abel

open Sec2V4

variable {S Z : Subgroup G}

omit [Finite G] in
theorem mem_commutator_iff_mem (a : ↥S) : a ∈ commutator ↥S ↔ (a : G) ∈ ⁅S, S⁆ := by
  rw [← Subgroup.mem_map_iff_mem S.subtype_injective, commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

@[expose] def conjS (n : G) (hn : n ∈ normalizer (S : Set G)) : ↥S →* ↥S where
  toFun a := ⟨n * a * n⁻¹, (mem_normalizer_iff.mp hn a).mp a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite G] in
theorem coe_conjS {n : G} (hn : n ∈ normalizer (S : Set G)) (a : ↥S) :
    (conjS n hn a : G) = n * a * n⁻¹ :=
  rfl

@[expose] noncomputable def abelConj (n : G) (hn : n ∈ normalizer (S : Set G)) :
    Abelianization ↥S →* Abelianization ↥S :=
  Abelianization.map (conjS n hn)

omit [Finite G] in
theorem abelConj_of {n : G} (hn : n ∈ normalizer (S : Set G)) (a : ↥S) :
    abelConj n hn (Abelianization.of a) = Abelianization.of (conjS n hn a) :=
  Abelianization.map_of _ _

omit [Finite G] in
theorem abelConj_abelConj {a b : G} (ha : a ∈ normalizer (S : Set G))
    (hb : b ∈ normalizer (S : Set G)) (m : Abelianization ↥S) :
    abelConj a ha (abelConj b hb m) = abelConj (a * b) (mul_mem ha hb) m := by
  induction m using QuotientGroup.induction_on with
  | H x =>
    show abelConj a ha (abelConj b hb (Abelianization.of x)) =
      abelConj (a * b) (mul_mem ha hb) (Abelianization.of x)
    rw [abelConj_of, abelConj_of, abelConj_of]
    congr 1
    exact Subtype.ext (by simp only [coe_conjS]; group)

omit [Finite G] in
theorem abelConj_one (m : Abelianization ↥S) : abelConj 1 (one_mem _) m = m := by
  induction m using QuotientGroup.induction_on with
  | H x =>
    show abelConj 1 (one_mem _) (Abelianization.of x) = Abelianization.of x
    rw [abelConj_of]
    congr 1
    exact Subtype.ext (by simp only [coe_conjS]; group)

omit [Finite G] in
theorem abelConj_congr {a b : G} (ha : a ∈ normalizer (S : Set G))
    (hb : b ∈ normalizer (S : Set G)) (hab : a = b) (m : Abelianization ↥S) :
    abelConj a ha m = abelConj b hb m := by
  subst hab
  rfl

omit [Finite G] in
theorem card_sup_mul_card_inf {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have h1 := relIndex_mul_card (A.subgroupOf N) (B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := relIndex_mul_card (A.subgroupOf N) (B.subgroupOf N)
  rw [relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

@[expose] noncomputable def coordProd (q : Fin 5 → Abelianization ↥S) (v : Fin 5 → ZMod 2) :
    Abelianization ↥S :=
  ∏ i, q i ^ (v i).val

omit [Finite G] in
theorem coordProd_comp (q : Fin 5 → Abelianization ↥S) (σ : Equiv.Perm (Fin 5))
    (v : Fin 5 → ZMod 2) : coordProd (q ∘ σ) v = coordProd q (act σ v) := by
  rw [coordProd, coordProd]
  conv_rhs => rw [← Equiv.prod_comp σ]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [act]

omit [Finite G] in
theorem map_coordProd (f : Abelianization ↥S →* Abelianization ↥S)
    (q : Fin 5 → Abelianization ↥S) (v : Fin 5 → ZMod 2) :
    f (coordProd q v) = coordProd (f ∘ q) v := by
  rw [coordProd, coordProd, map_prod]
  simp [map_pow]

variable (hS : Special S Z)
include hS

omit [Finite G] in
theorem abel_of_eq_one_iff {a : ↥S} : Abelianization.of a = 1 ↔ (a : G) ∈ Z := by
  rw [← MonoidHom.mem_ker, Abelianization.ker_of, mem_commutator_iff_mem, hS.comm]

omit [Finite G] in
theorem abel_of_eq_of_iff {a b : ↥S} :
    Abelianization.of a = Abelianization.of b ↔ (a : G)⁻¹ * b ∈ Z := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, abel_of_eq_one_iff hS]
  rfl

omit [Finite G] in
theorem abel_mul_self (q : Abelianization ↥S) : q * q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    show Abelianization.of a * Abelianization.of a = 1
    rw [← map_mul, abel_of_eq_one_iff hS]
    exact hS.sq a a.2

omit [Finite G] in
theorem pow_val_add (q : Abelianization ↥S) (α β : ZMod 2) :
    q ^ (α + β).val = q ^ α.val * q ^ β.val := by
  rcases zmod2_cases α with rfl | rfl <;> rcases zmod2_cases β with rfl | rfl
  · simp
  · simp
  · simp
  · have h2 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h2, ZMod.val_zero, pow_zero, ZMod.val_one, pow_one, abel_mul_self hS]

omit [Finite G] in
theorem coordProd_add (q : Fin 5 → Abelianization ↥S) (v w : Fin 5 → ZMod 2) :
    coordProd q (v + w) = coordProd q v * coordProd q w := by
  rw [coordProd, coordProd, coordProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply, pow_val_add hS]

omit [Finite G] hS in
theorem coordProd_single (q : Fin 5 → Abelianization ↥S) (i : Fin 5) :
    coordProd q (Pi.single i 1) = q i := by
  rw [coordProd, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [Finite G] hS in
theorem coordProd_zero (q : Fin 5 → Abelianization ↥S) : coordProd q 0 = 1 := by
  simp [coordProd]

omit [Finite G] in
theorem coordProd_eq_one_iff {q : Fin 5 → Abelianization ↥S} (hq1 : ∀ i, q i ≠ 1)
    (hq2 : ∀ i j, i ≠ j → q i ≠ q j) (hall : coordProd q 1 = 1) (v : Fin 5 → ZMod 2) :
    coordProd q v = 1 ↔ v = 0 ∨ v = 1 := by
  constructor
  · intro hv
    by_contra hne
    push Not at hne
    have hv1 : coordProd q (v + 1) = 1 := by rw [coordProd_add hS, hv, hall, one_mul]
    have hpair : ∀ i j, i ≠ j → coordProd q (pair i j) ≠ 1 := fun i j hij h => by
      rw [pair, coordProd_add hS, coordProd_single, coordProd_single] at h
      apply hq2 i j hij
      have hj := abel_mul_self hS (q j)
      calc q i = q i * q j * q j := by rw [mul_assoc, hj, mul_one]
        _ = q j := by rw [h, one_mul]
    rcases small_cases v hne.1 hne.2 with ⟨i, hi | hi⟩ | ⟨i, j, hij, hi | hi⟩
    · exact hq1 i (by rw [← coordProd_single q i, ← hi, hv])
    · exact hq1 i (by rw [← coordProd_single q i, ← hi, hv1])
    · exact hpair i j hij (by rw [← hi, hv])
    · exact hpair i j hij (by rw [← hi, hv1])
  · rintro (rfl | rfl)
    · exact coordProd_zero q
    · exact hall

omit [Finite G] in
theorem exists_isEven_coordProd_eq (q : Fin 5 → Abelianization ↥S) (hall : coordProd q 1 = 1)
    (v : Fin 5 → ZMod 2) : ∃ w, IsEven w ∧ coordProd q w = coordProd q v := by
  have hcases : ∀ v : Fin 5 → ZMod 2, IsEven v ∨ IsEven (v + 1) := by decide
  rcases hcases v with h | h
  · exact ⟨v, h, rfl⟩
  · exact ⟨v + 1, h, by rw [coordProd_add hS, hall, mul_one]⟩

open Classical in
@[expose] noncomputable def coordDecode (q : Fin 5 → Abelianization ↥S) (m : Abelianization ↥S) :
    Fin 5 → ZMod 2 :=
  if h : ∃ v, IsEven v ∧ coordProd q v = m then Classical.choose h else 0

omit [Finite G] in
theorem eq_of_coordProd_eq {q : Fin 5 → Abelianization ↥S}
    (hker : ∀ v, coordProd q v = 1 ↔ v = 0 ∨ v = 1) {v w : Fin 5 → ZMod 2} (hv : IsEven v)
    (hw : IsEven w) (h : coordProd q v = coordProd q w) : v = w := by
  have h1 : coordProd q (v + w) = 1 := by
    rw [coordProd_add hS, h, abel_mul_self hS]
  have hvw := isEven_add hv hw
  rcases (hker _).mp h1 with h2 | h2
  · have hab : v = -w := eq_neg_of_add_eq_zero_left h2
    funext k
    rw [hab, Pi.neg_apply, ZMod.neg_eq_self_mod_two]
  · rw [h2] at hvw
    exact absurd hvw (by decide)

omit [Finite G] in
theorem coordDecode_coordProd {q : Fin 5 → Abelianization ↥S}
    (hker : ∀ v, coordProd q v = 1 ↔ v = 0 ∨ v = 1) {v : Fin 5 → ZMod 2} (hv : IsEven v) :
    coordDecode q (coordProd q v) = v := by
  have h : ∃ w, IsEven w ∧ coordProd q w = coordProd q v := ⟨v, hv, rfl⟩
  rw [coordDecode, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hw, hwv⟩ := Classical.choose_spec h
  exact eq_of_coordProd_eq hS hker hw hv hwv

@[expose] def coordRange (q : Fin 5 → Abelianization ↥S) : Subgroup (Abelianization ↥S) where
  carrier := {m | ∃ v, coordProd q v = m}
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, coordProd_add hS q v w⟩
  one_mem' := ⟨0, coordProd_zero q⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨v, (inv_eq_of_mul_eq_one_right (abel_mul_self hS _)).symm⟩

@[expose] def summand (q : Fin 5 → Abelianization ↥S) : Subgroup G :=
  ((coordRange hS q).comap Abelianization.of).map S.subtype

omit [Finite G] in
theorem mem_summand {q : Fin 5 → Abelianization ↥S} {a : G} :
    a ∈ summand hS q ↔ ∃ ha : a ∈ S, ∃ v, coordProd q v = Abelianization.of ⟨a, ha⟩ := by
  constructor
  · rintro ⟨x, ⟨v, hv⟩, rfl⟩
    exact ⟨x.2, v, hv⟩
  · rintro ⟨ha, v, hv⟩
    exact ⟨⟨a, ha⟩, ⟨v, hv⟩, rfl⟩

omit hS in
open Classical in
@[expose] noncomputable def summandCoord (q : Fin 5 → Abelianization ↥S) (a : G) :
    Fin 5 → ZMod 2 :=
  if ha : a ∈ S then coordDecode q (Abelianization.of ⟨a, ha⟩) else 0

section Summand

variable {q : Fin 5 → Abelianization ↥S} (hker : ∀ v, coordProd q v = 1 ↔ v = 0 ∨ v = 1)
  (hall : coordProd q 1 = 1)
include hker

omit [Finite G] in
theorem summandCoord_eq {a : G} (ha : a ∈ S) {v : Fin 5 → ZMod 2} (hv : IsEven v)
    (h : coordProd q v = Abelianization.of ⟨a, ha⟩) : summandCoord q a = v := by
  rw [summandCoord, dite_eq_left_of_eq_true (eq_true ha), ← h, coordDecode_coordProd hS hker hv]

include hall in
omit [Finite G] in
theorem summandCoord_spec {a : G} (h : a ∈ summand hS q) : ∃ ha : a ∈ S,
    IsEven (summandCoord q a) ∧ coordProd q (summandCoord q a) = Abelianization.of ⟨a, ha⟩ := by
  obtain ⟨ha, v, hv⟩ := (mem_summand hS).mp h
  obtain ⟨w, hw, hwv⟩ := exists_isEven_coordProd_eq hS q hall v
  have e : summandCoord q a = w := summandCoord_eq hS hker ha hw (hwv.trans hv)
  exact ⟨ha, e ▸ hw, by rw [e, hwv, hv]⟩

omit hker in
omit [Finite G] in
theorem Z_le_summand : Z ≤ summand hS q := fun z hz =>
  (mem_summand hS).mpr ⟨hS.le hz, 0, by
    rw [coordProd_zero]
    exact ((abel_of_eq_one_iff hS).mpr hz).symm⟩

include hall in
omit [Finite G] in
theorem summandCoord_mul {a b : G} (ha : a ∈ summand hS q) (hb : b ∈ summand hS q) :
    summandCoord q (a * b) = summandCoord q a + summandCoord q b := by
  obtain ⟨haS, hva, hpa⟩ := summandCoord_spec hS hker hall ha
  obtain ⟨hbS, hvb, hpb⟩ := summandCoord_spec hS hker hall hb
  refine summandCoord_eq hS hker (S.mul_mem haS hbS) (isEven_add hva hvb) ?_
  rw [coordProd_add hS, hpa, hpb, ← map_mul]
  rfl

include hall in
omit [Finite G] in
theorem summandCoord_eq_zero_iff {a : G} (ha : a ∈ summand hS q) :
    summandCoord q a = 0 ↔ a ∈ Z := by
  obtain ⟨haS, -, hpa⟩ := summandCoord_spec hS hker hall ha
  constructor
  · intro h0
    rw [h0, coordProd_zero] at hpa
    exact (abel_of_eq_one_iff hS).mp hpa.symm
  · intro hz
    exact summandCoord_eq hS hker haS isEven_zero
      (by rw [coordProd_zero]; exact ((abel_of_eq_one_iff hS).mpr hz).symm)

omit [Finite G] in
theorem exists_summandCoord_eq {v : Fin 5 → ZMod 2} (hv : IsEven v) :
    ∃ a ∈ summand hS q, summandCoord q a = v := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (coordProd q v)
  have hx' : Abelianization.of x = coordProd q v := hx
  refine ⟨x, (mem_summand hS).mpr ⟨x.2, v, hx'.symm⟩, ?_⟩
  exact summandCoord_eq hS hker x.2 hv hx'.symm

include hall in
omit [Finite G] in
theorem summandCoord_conj {n : G} (hn : n ∈ normalizer (S : Set G)) {σ : Equiv.Perm (Fin 5)}
    (hσ : ∀ i, abelConj n hn (q i) = q (σ i)) {a : G} (ha : a ∈ summand hS q) :
    n * a * n⁻¹ ∈ summand hS q ∧ summandCoord q (n * a * n⁻¹) = act σ (summandCoord q a) := by
  obtain ⟨haS, hv, hp⟩ := summandCoord_spec hS hker hall ha
  have hnaS : n * a * n⁻¹ ∈ S := (mem_normalizer_iff.mp hn a).mp haS
  have hof : Abelianization.of (⟨n * a * n⁻¹, hnaS⟩ : ↥S) =
      coordProd q (act σ (summandCoord q a)) := by
    have e1 : (⟨n * a * n⁻¹, hnaS⟩ : ↥S) = conjS n hn ⟨a, haS⟩ := rfl
    rw [e1, ← abelConj_of hn, ← hp, map_coordProd, ← coordProd_comp]
    congr 1
    funext i
    exact hσ i
  exact ⟨(mem_summand hS).mpr ⟨hnaS, _, hof.symm⟩,
    summandCoord_eq hS hker hnaS (isEven_act hv σ) hof.symm⟩

include hall in
omit [Finite G] in
theorem summandCoord_eq_iff {a b : G} (ha : a ∈ summand hS q) (hb : b ∈ summand hS q) :
    summandCoord q a = summandCoord q b ↔ a⁻¹ * b ∈ Z := by
  have hai : a⁻¹ ∈ summand hS q := inv_mem ha
  have h0 := summandCoord_mul hS hker hall ha hai
  rw [mul_inv_cancel, (summandCoord_eq_zero_iff hS hker hall (one_mem _)).mpr (one_mem _)] at h0
  have hinv : summandCoord q a⁻¹ = summandCoord q a := by
    funext k
    have := congrFun h0 k
    simp only [Pi.zero_apply, Pi.add_apply] at this
    rw [eq_neg_of_add_eq_zero_right this.symm, ZMod.neg_eq_self_mod_two]
  rw [← summandCoord_eq_zero_iff hS hker hall (mul_mem hai hb),
    summandCoord_mul hS hker hall hai hb, hinv]
  constructor
  · intro h
    rw [h]
    funext k
    have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
    exact h2 _
  · intro h
    have h3 := eq_neg_of_add_eq_zero_left h
    rw [h3]
    funext k
    rw [Pi.neg_apply, ZMod.neg_eq_self_mod_two]

include hall in
omit [Finite G] in
theorem card_coordRange : Nat.card (coordRange hS q) = 16 := by
  let f : {v : Fin 5 → ZMod 2 // IsEven v} → coordRange hS q := fun v => ⟨coordProd q v, v, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      exact Subtype.ext (eq_of_coordProd_eq hS hker v.2 w.2 (congrArg Subtype.val h))
    · rintro ⟨m, v, rfl⟩
      obtain ⟨w, hw, hwv⟩ := exists_isEven_coordProd_eq hS q hall v
      exact ⟨⟨w, hw⟩, Subtype.ext hwv⟩
  rw [← Nat.card_eq_of_bijective f hf, card_even]

include hall in
theorem card_summand : Nat.card (summand hS q) = 16 * Nat.card Z := by
  rw [summand, Subgroup.card_map_of_injective S.subtype_injective,
    CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.card_comap_of_surjective
      (f := Abelianization.of) (fun x => QuotientGroup.mk_surjective x),
    card_coordRange hS hker hall,
    Abelianization.ker_of]
  congr 1
  rw [← Subgroup.card_map_of_injective (K := commutator ↥S) S.subtype_injective, commutator_def,
    Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hS.comm]

include hall in
omit [Finite G] in
theorem summand_props {H : Subgroup G} (hHS : H ≤ normalizer (S : Set G))
    (φ : ↥H →* alternatingGroup (Fin 5))
    (hqeq : ∀ h : ↥H, ∀ i, abelConj (h : G) (hHS h.2) (q i) =
      q (((φ h : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) i)) :
    Z ≤ summand hS q ∧ summand hS q ≤ S ∧
      (∀ a ∈ summand hS q, ∀ b ∈ summand hS q,
        summandCoord q (a * b) = summandCoord q a + summandCoord q b) ∧
      (∀ a ∈ summand hS q, summandCoord q a = 0 ↔ a ∈ Z) ∧
      (∀ a ∈ summand hS q, ∑ k, summandCoord q a k = 0) ∧
      (∀ v : Fin 5 → ZMod 2, ∑ k, v k = 0 → ∃ a ∈ summand hS q, summandCoord q a = v) ∧
      ∀ h : ↥H, ∀ a ∈ summand hS q, (h : G) * a * (h : G)⁻¹ ∈ summand hS q ∧
        summandCoord q ((h : G) * a * (h : G)⁻¹) =
          fun k => summandCoord q a (((φ h : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ k) :=
  ⟨Z_le_summand hS, map_subtype_le _, fun _ ha _ hb => summandCoord_mul hS hker hall ha hb,
    fun _ ha => summandCoord_eq_zero_iff hS hker hall ha,
    fun _ ha => (summandCoord_spec hS hker hall ha).2.1,
    fun _ hv => exists_summandCoord_eq hS hker hv,
    fun h _ ha => summandCoord_conj hS hker hall (hHS h.2) (hqeq h) ha⟩

end Summand

end Abel

end Sec2

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem special_sec2S : Sec2.Special (sec2S A R E F) (sec2Z A E F) where
  card := hF.card_sec2Z hodd
  center := centerIn_sec2S_eq h11 hE16 hF hL hodd
  comm := commutator_sec2S_eq h11 hE16 hF hL hodd
  sq s hs := (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd hs hs).1
  elem c hc := by
    have hc' : c ∈ E := by rw [hF.sec2Z_eq] at hc; exact hc.1.1
    have := hF.elemE.2 c hc'
    rwa [sq] at this

theorem mem_sec2Z_of_actsAsF4Scalar {ξ : G} (hξ : ActsAsF4Scalar ξ (sec2S A R E F) (sec2Z A E F))
    {s : G} (hs : s ∈ sec2S A R E F) (hfix : s⁻¹ * (ξ * s * ξ⁻¹) ∈ sec2Z A E F) :
    s ∈ sec2Z A E F := by
  have hS := special_sec2S h11 hE16 hF hL hodd
  have hξZ := hξ.2.1
  set z := s⁻¹ * (ξ * s * ξ⁻¹) with hz
  have hz₁ : (ξ⁻¹ * z * ξ)⁻¹ ∈ sec2Z A E F := by
    have := (mem_normalizer_iff.mp (inv_mem hξZ) z).mp hfix
    rw [inv_inv] at this
    exact inv_mem this
  set z₁ := (ξ⁻¹ * z * ξ)⁻¹ with hz₁def
  have hz₂ : ξ⁻¹ * z₁ * ξ ∈ sec2Z A E F := by
    have := (mem_normalizer_iff.mp (inv_mem hξZ) z₁).mp hz₁
    rwa [inv_inv] at this
  have e1 : ξ⁻¹ * s * ξ = s * z₁ := by rw [hz₁def, hz]; group
  have e2 : ξ⁻¹ * ξ⁻¹ * s * ξ * ξ = s * z₁ * (ξ⁻¹ * z₁ * ξ) := by
    calc ξ⁻¹ * ξ⁻¹ * s * ξ * ξ = ξ⁻¹ * (ξ⁻¹ * s * ξ) * ξ := by group
      _ = ξ⁻¹ * (s * z₁) * ξ := by rw [e1]
      _ = (ξ⁻¹ * s * ξ) * (ξ⁻¹ * z₁ * ξ) := by group
      _ = s * z₁ * (ξ⁻¹ * z₁ * ξ) := by rw [e1]
  have hN := hξ.2.2 s hs
  rw [e1, e2] at hN
  have e3 : s * (s * z₁) * (s * z₁ * (ξ⁻¹ * z₁ * ξ)) =
      (s * s * s) * (z₁ * z₁ * (ξ⁻¹ * z₁ * ξ)) := by
    calc s * (s * z₁) * (s * z₁ * (ξ⁻¹ * z₁ * ξ)) = s * s * (z₁ * s) * z₁ * (ξ⁻¹ * z₁ * ξ) := by
          group
      _ = s * s * (s * z₁) * z₁ * (ξ⁻¹ * z₁ * ξ) := by rw [hS.comm_Z hz₁ hs]
      _ = (s * s * s) * (z₁ * z₁ * (ξ⁻¹ * z₁ * ξ)) := by group
  rw [e3] at hN
  have h3 : s * s * s ∈ sec2Z A E F := by
    have := (sec2Z A E F).mul_mem hN
      ((sec2Z A E F).inv_mem ((sec2Z A E F).mul_mem ((sec2Z A E F).mul_mem hz₁ hz₁) hz₂))
    simpa [mul_assoc] using this
  have e4 : s = (s * s * s) * (s * s)⁻¹ := by group
  rw [e4]
  exact (sec2Z A E F).mul_mem h3 ((sec2Z A E F).inv_mem (hS.sq s hs))

omit h11 hE16 hL hodd in
theorem mem_sec2Z_of_commute_inf {a : G} (ha : a ∈ E ⊓ A)
    (hc : ∀ b ∈ F ⊓ A, a * b * a⁻¹ * b⁻¹ = 1) : a ∈ sec2Z A E F := by
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hle : E ⊔ F ≤ centralizer ({a} : Set G) := by
    refine sup_le (fun e he => mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨e, he⟩ ⟨a, ha.1⟩))) ?_
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le]
    refine sup_le (fun b hb => mem_centralizer_singleton_iff.mpr ?_) (fun r hr =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hRA hr) a ha.2).symm)
    have h1 := hc b hb
    calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * a * b := by group
      _ = a * b := by rw [h1, inv_one, one_mul]
  refine ⟨ha.2, mem_sup_left ha.1, mem_centralizer_iff.mpr fun t ht => ?_⟩
  exact (mem_centralizer_singleton_iff.mp (hle ht))

theorem inv_mul_conj_mem_of_xi {u ξ : G} (huA : u ∈ A ⊓ normalizer (sec2S A R E F : Set G))
    (hu3 : orderOf u = 3) (huE : ∃ e ∈ E, u⁻¹ * e * u ≠ e)
    (hξEA : ξ ∈ normalizer ((E ⊓ A : Subgroup G) : Set G))
    (hξFA : ξ ∈ normalizer ((F ⊓ A : Subgroup G) : Set G))
    (hξZ : ξ ∈ normalizer (sec2Z A E F : Set G))
    (hξfix : ∀ s ∈ sec2S A R E F, s⁻¹ * (ξ * s * ξ⁻¹) ∈ sec2Z A E F → s ∈ sec2Z A E F)
    (huξ : u * ξ = ξ * u) (hξu : ∀ w ∈ sec2Z A E F, ξ * w * ξ⁻¹ = u * w * u⁻¹) :
    ∀ a ∈ E ⊓ A, a⁻¹ * ((ξ⁻¹ * u) * a * (ξ⁻¹ * u)⁻¹) ∈ sec2Z A E F := by
  set Z := sec2Z A E F with hZdef
  have hS := special_sec2S h11 hE16 hF hL hodd
  obtain ⟨huEn, huFn, -, hufix⟩ := sec2U_facts h11 hE16 hF hL hodd huA hu3 huE
  obtain ⟨huZ, -, -⟩ := mem_normalizer_sec2S_of_mem hF huA.1 huEn huFn
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have huEA : u ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨huEn, le_normalizer huA.1⟩
  have huFA : u ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨huFn, le_normalizer huA.1⟩
  have hZE : Z ≤ E ⊓ A := by
    rw [hZdef, hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.1, hz.2⟩
  have hZF : Z ≤ F ⊓ A := by
    rw [hZdef, hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.2, hz.2⟩
  have hES : E ⊓ A ≤ sec2S A R E F :=
    inf_le_left.trans (le_sec2S_and_le_sec2S (A := A) (R := R) hF).1
  have hFS : F ⊓ A ≤ sec2S A R E F :=
    inf_le_left.trans (le_sec2S_and_le_sec2S (A := A) (R := R) hF).2
  have hidx : ∀ X : Subgroup G, Z ≤ X → Nat.card X = 16 → Z.relIndex X = 4 := fun X hZX hX => by
    have h := relIndex_mul_card Z X
    rw [inf_eq_left.mpr hZX, hF.card_sec2Z hodd, hX] at h
    omega
  have h4E := hidx _ hZE (card_inf_left hF hodd)
  have h4F := hidx _ hZF (card_inf_left hF.symm hodd)
  have hconv : ∀ a ∈ sec2S A R E F, ∀ n : G, a⁻¹ * (n * a * n⁻¹) ∈ Z →
      n * a * n⁻¹ * a⁻¹ ∈ Z := fun a ha n h => by
    have e : n * a * n⁻¹ * a⁻¹ = a * (a⁻¹ * (n * a * n⁻¹)) * a⁻¹ := by group
    rw [e, hS.conj_Z h ha]
    exact h
  have hufixE : ∀ a ∈ E ⊓ A, a⁻¹ * (u * a * u⁻¹) ∈ Z → a ∈ Z := fun a ha h =>
    mem_sec2Z_of_conj_mul_inv_mem hF hL hodd huA.1 huZ hufix ha (hconv a (hES ha) u h)
  have hufixF : ∀ b ∈ F ⊓ A, b⁻¹ * (u * b * u⁻¹) ∈ Z → b ∈ Z := fun b hb h => by
    have hZ' : sec2Z A F E = Z := sec2Z_comm A E F
    have huZ' : u ∈ normalizer (sec2Z A F E : Set G) := by rw [hZ']; exact huZ
    have hufix' : ∀ w ∈ sec2Z A F E, u * w * u⁻¹ = w → w = 1 := fun w hw =>
      hufix w (by rwa [sec2Z_comm] at hw)
    have h' : u * b * u⁻¹ * b⁻¹ ∈ sec2Z A F E := by rw [hZ']; exact hconv b (hFS hb) u h
    have := mem_sec2Z_of_conj_mul_inv_mem hF.symm hL hodd huA.1 huZ' hufix' hb h'
    rw [hZ'] at this
    exact this
  have hξfixE : ∀ a ∈ E ⊓ A, a⁻¹ * (ξ * a * ξ⁻¹) ∈ Z → a ∈ Z := fun a ha h => hξfix a (hES ha) h
  have hξfixF : ∀ b ∈ F ⊓ A, b⁻¹ * (ξ * b * ξ⁻¹) ∈ Z → b ∈ Z := fun b hb h => hξfix b (hFS hb) h
  have hcommZ : ∀ a ∈ sec2S A R E F, (ξ * (u * a * u⁻¹) * ξ⁻¹)⁻¹ * (u * (ξ * a * ξ⁻¹) * u⁻¹) ∈ Z :=
    fun a _ => by
      have e : ξ * (u * a * u⁻¹) * ξ⁻¹ = u * (ξ * a * ξ⁻¹) * u⁻¹ := by
        calc ξ * (u * a * u⁻¹) * ξ⁻¹ = (ξ * u) * a * (ξ * u)⁻¹ := by group
          _ = (u * ξ) * a * (u * ξ)⁻¹ := by rw [huξ]
          _ = u * (ξ * a * ξ⁻¹) * u⁻¹ := by group
      rw [e, inv_mul_cancel]
      exact one_mem _
  obtain ⟨r₁, hr₁, hξr₁⟩ := Sec2.trichotomy h4E huEA huZ hu3' hufixE hξEA hξZ
    fun a ha => hcommZ a (hES ha)
  obtain ⟨r₂, hr₂, hξr₂⟩ := Sec2.trichotomy h4F huFA huZ hu3' hufixF hξFA hξZ
    fun b hb => hcommZ b (hFS hb)
  obtain ⟨a₀, ha₀, ha₀Z⟩ : ∃ a₀ ∈ E ⊓ A, a₀ ∉ Z := by
    by_contra hall
    push Not at hall
    have : Z.relIndex (E ⊓ A) = 1 := relIndex_eq_one.mpr hall
    omega
  obtain ⟨b₀, hb₀, hb₀Z⟩ : ∃ b₀ ∈ F ⊓ A, b₀ ∉ Z := by
    by_contra hall
    push Not at hall
    have : Z.relIndex (F ⊓ A) = 1 := relIndex_eq_one.mpr hall
    omega
  have huu : u * u = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hu3', pow_three, mul_assoc]
  have hcZl : ∀ {x y z : G}, x ∈ sec2S A R E F → y ∈ sec2S A R E F → z ∈ Z →
      x * z * y * (x * z)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := fun {x y z} _ hy hz => by
    calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
      _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hS.comm_Z hz hy]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  have hr₁N : r₁ ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    rcases hr₁ with rfl | rfl | rfl
    · exact one_mem _
    · exact huEA
    · exact inv_mem huEA
  have hr₂N : r₂ ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) := by
    rcases hr₂ with rfl | rfl | rfl
    · exact one_mem _
    · exact huFA
    · exact inv_mem huFA
  have hpair : ∀ a ∈ E ⊓ A, ∀ b ∈ F ⊓ A,
      (r₁ * a * r₁⁻¹) * (r₂ * b * r₂⁻¹) * (r₁ * a * r₁⁻¹)⁻¹ * (r₂ * b * r₂⁻¹)⁻¹ =
        u * (a * b * a⁻¹ * b⁻¹) * u⁻¹ := by
    intro a ha b hb
    have hx : r₁ * a * r₁⁻¹ ∈ sec2S A R E F := hES ((mem_normalizer_iff.mp hr₁N a).mp ha)
    have hy : r₂ * b * r₂⁻¹ ∈ sec2S A R E F := hFS ((mem_normalizer_iff.mp hr₂N b).mp hb)
    have e1 : ξ * a * ξ⁻¹ = (r₁ * a * r₁⁻¹) * ((r₁ * a * r₁⁻¹)⁻¹ * (ξ * a * ξ⁻¹)) :=
      (mul_inv_cancel_left _ _).symm
    have e2 : ξ * b * ξ⁻¹ = (r₂ * b * r₂⁻¹) * ((r₂ * b * r₂⁻¹)⁻¹ * (ξ * b * ξ⁻¹)) :=
      (mul_inv_cancel_left _ _).symm
    have hz₂ := hξr₂ b hb
    calc (r₁ * a * r₁⁻¹) * (r₂ * b * r₂⁻¹) * (r₁ * a * r₁⁻¹)⁻¹ * (r₂ * b * r₂⁻¹)⁻¹
        = (r₁ * a * r₁⁻¹) * ((r₂ * b * r₂⁻¹) * ((r₂ * b * r₂⁻¹)⁻¹ * (ξ * b * ξ⁻¹))) *
            (r₁ * a * r₁⁻¹)⁻¹ * ((r₂ * b * r₂⁻¹) * ((r₂ * b * r₂⁻¹)⁻¹ * (ξ * b * ξ⁻¹)))⁻¹ := by
          rw [hS.comm_mul_Z hx hy hz₂]
      _ = (r₁ * a * r₁⁻¹) * ((r₁ * a * r₁⁻¹)⁻¹ * (ξ * a * ξ⁻¹)) *
            ((r₂ * b * r₂⁻¹) * ((r₂ * b * r₂⁻¹)⁻¹ * (ξ * b * ξ⁻¹))) *
            ((r₁ * a * r₁⁻¹) * ((r₁ * a * r₁⁻¹)⁻¹ * (ξ * a * ξ⁻¹)))⁻¹ *
            ((r₂ * b * r₂⁻¹) * ((r₂ * b * r₂⁻¹)⁻¹ * (ξ * b * ξ⁻¹)))⁻¹ := by
          rw [hcZl hx ((sec2S A R E F).mul_mem hy (hS.le hz₂)) (hξr₁ a ha)]
      _ = (ξ * a * ξ⁻¹) * (ξ * b * ξ⁻¹) * (ξ * a * ξ⁻¹)⁻¹ * (ξ * b * ξ⁻¹)⁻¹ := by
          rw [← e1, ← e2]
      _ = ξ * (a * b * a⁻¹ * b⁻¹) * ξ⁻¹ := by group
      _ = u * (a * b * a⁻¹ * b⁻¹) * u⁻¹ := hξu _ (hS.comm_mem (hES ha) (hFS hb))
  rcases hr₁ with hr | hr | hr <;> rw [hr] at hξr₁ hpair
  · exfalso
    exact ha₀Z (hξfixE a₀ ha₀ (by simpa using hξr₁ a₀ ha₀))
  · intro a ha
    have h1 := Sec2.conj_inv_mul_mem (inv_mem hξZ) (hξr₁ a ha)
    have e1 : ξ⁻¹ * (u * a * u⁻¹) * ξ⁻¹⁻¹ = (ξ⁻¹ * u) * a * (ξ⁻¹ * u)⁻¹ := by group
    have e2 : ξ⁻¹ * (ξ * a * ξ⁻¹) * ξ⁻¹⁻¹ = a := by group
    rw [e1, e2] at h1
    exact Sec2.inv_mul_mem_symm h1
  · exfalso
    rcases hr₂ with hr' | hr' | hr' <;> rw [hr'] at hξr₂ hpair
    · exact hb₀Z (hξfixF b₀ hb₀ (by simpa using hξr₂ b₀ hb₀))
    ·
      set x₁ := u⁻¹ * a₀ * u⁻¹⁻¹ with hx₁
      set x₂ := u * a₀ * u⁻¹ with hx₂
      have hx₁S : x₁ ∈ sec2S A R E F := hES ((mem_normalizer_iff.mp (inv_mem huEA) a₀).mp ha₀)
      have hx₂S : x₂ ∈ sec2S A R E F := hES ((mem_normalizer_iff.mp huEA a₀).mp ha₀)
      have hd : x₂⁻¹ * x₁ ∈ E ⊓ A := (E ⊓ A).mul_mem
        ((E ⊓ A).inv_mem ((mem_normalizer_iff.mp huEA a₀).mp ha₀))
        ((mem_normalizer_iff.mp (inv_mem huEA) a₀).mp ha₀)
      have hdZ := mem_sec2Z_of_commute_inf hF hd fun b' hb' => by
        have hb : u⁻¹ * b' * u⁻¹⁻¹ ∈ F ⊓ A := (mem_normalizer_iff.mp (inv_mem huFA) b').mp hb'
        have h1 := hpair a₀ ha₀ _ hb
        have e : u * (u⁻¹ * b' * u⁻¹⁻¹) * u⁻¹ = b' := by group
        rw [e] at h1
        have h2 : u * (a₀ * (u⁻¹ * b' * u⁻¹⁻¹) * a₀⁻¹ * (u⁻¹ * b' * u⁻¹⁻¹)⁻¹) * u⁻¹ =
            x₂ * b' * x₂⁻¹ * b'⁻¹ := by rw [hx₂]; group
        rw [h2] at h1
        have hb'S := hFS hb'
        have h3 := hS.comm_mul_left ((sec2S A R E F).inv_mem hx₂S) hx₁S hb'S
        have h4 := hS.comm_mul_left hx₂S ((sec2S A R E F).inv_mem hx₂S) hb'S
        have h4' : (x₂ * b' * x₂⁻¹ * b'⁻¹) * (x₂⁻¹ * b' * x₂⁻¹⁻¹ * b'⁻¹) = 1 := by
          rw [← h4]
          group
        rw [h3, h1, eq_inv_of_mul_eq_one_right h4', inv_mul_cancel]
      apply ha₀Z
      apply hufixE a₀ ha₀
      have k1 := Sec2.conj_inv_mul_mem huZ hdZ
      have e1 : u * x₂ * u⁻¹ = u⁻¹ * a₀ * u⁻¹⁻¹ := by
        rw [hx₂]
        calc u * (u * a₀ * u⁻¹) * u⁻¹ = (u * u) * a₀ * (u * u)⁻¹ := by group
          _ = u⁻¹ * a₀ * u⁻¹⁻¹ := by rw [huu]
      have e2 : u * x₁ * u⁻¹ = a₀ := by rw [hx₁]; group
      rw [e1, e2] at k1
      have k2 := Sec2.conj_inv_mul_mem huZ (Sec2.inv_mul_mem_symm k1)
      have e4 : u * (u⁻¹ * a₀ * u⁻¹⁻¹) * u⁻¹ = a₀ := by group
      rw [e4] at k2
      exact Sec2.inv_mul_mem_symm k2
    ·
      apply ha₀Z
      refine mem_sec2Z_of_commute_inf hF ha₀ fun b hb => ?_
      have h1 := hpair a₀ ha₀ b hb
      have e : u⁻¹ * a₀ * u⁻¹⁻¹ * (u⁻¹ * b * u⁻¹⁻¹) * (u⁻¹ * a₀ * u⁻¹⁻¹)⁻¹ *
          (u⁻¹ * b * u⁻¹⁻¹)⁻¹ = u⁻¹ * (a₀ * b * a₀⁻¹ * b⁻¹) * u⁻¹⁻¹ := by group
      rw [e] at h1
      set c := a₀ * b * a₀⁻¹ * b⁻¹ with hc
      have hcZ : c ∈ Z := hS.comm_mem (hES ha₀) (hFS hb)
      refine hufix c hcZ ?_
      calc u * c * u⁻¹ = u * (u * (u⁻¹ * c * u⁻¹⁻¹) * u⁻¹) * u⁻¹ := by group
        _ = u * (u * (u * c * u⁻¹) * u⁻¹) * u⁻¹ := by rw [h1]
        _ = (u * u * u) * c * (u * u * u)⁻¹ := by group
        _ = c := by rw [huu, inv_mul_cancel, one_mul, inv_one, mul_one]

end Frame

section FrameXH

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G} (hh : h ∈ sec2P E)
  (hhS : h ∉ sec2S A R E F) (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
  (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)))

include h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'

theorem card_sec2H : Nat.card (sec2H E F) = Nat.card (sec2S A R E F) * 60 := by
  obtain ⟨φ, hφs, hφk⟩ :=
    exists_hom_alternatingGroup_ker_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have h1 := Subgroup.card_ker_mul_card_of_surjective (f := φ) hφs
  rw [hφk, Nat.card_congr (subgroupOfEquivOfLe (sec2S_le_sec2H hF)).toEquiv,
    nat_card_alternatingGroup, Nat.card_fin] at h1
  rw [← h1]
  rfl

theorem not_nine_dvd_card_inf :
    ¬ 9 ∣ Nat.card (sec2H E F ⊓ normalizer (E : Set G) : Subgroup G) := by
  intro h9
  have hdvd := Subgroup.card_dvd_of_le (inf_le_left :
    sec2H E F ⊓ normalizer (E : Set G) ≤ sec2H E F)
  rw [card_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'] at hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (isSylowOf_sec2S h11 hE16 hF hL hodd).isPGroup.exists_card_eq
  rw [hn] at hdvd
  have h' := h9.trans hdvd
  have hcop : Nat.Coprime 9 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  rw [mul_comm] at h'
  have := hcop.dvd_of_dvd_mul_right h'
  norm_num at this

theorem exists_sec2Xi : ∃ ξ g₀ : G, ξ ∈ normalizer (sec2S A R E F : Set G) ∧
    ξ ∈ normalizer (sec2Z A E F : Set G) ∧ ξ ^ 3 = 1 ∧
    ActsAsF4Scalar ξ (sec2S A R E F) (sec2Z A E F) ∧
    (∀ q ∈ sec2H E F, ξ⁻¹ * q⁻¹ * ξ * q ∈ sec2S A R E F) ∧
    ξ ∈ normalizer (sec2H E F : Set G) ∧
    ξ ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) ∧
    (∀ V ∈ conjSet E (sec2H E F), ξ ∈ normalizer (V : Set G)) ∧
    g₀ ∈ sec2H E F ∧ g₀ ∈ normalizer (E : Set G) ∧ orderOf g₀ = 3 ∧
    ∀ a ∈ E ⊓ A, a⁻¹ * (g₀ * a * g₀⁻¹) ∈ sec2Z A E F := by
  set H := sec2H E F with hHdef
  obtain ⟨u, y, huy⟩ := exists_sec2UY h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨ξ, hξo, hu, hF4, -, hξH, hξHS, hξE, hξF⟩ :=
    exists_xi_of_sec2UY h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' huy
  obtain ⟨huA, hu3, huE, ⟨⟨hyH, -⟩, hyu⟩, hy3⟩ := huy
  have hξ3 : ξ ^ 3 = 1 := by rw [← hξo]; exact pow_orderOf_eq_one ξ
  have hHC := sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd
  have hyu' : y * u = u * y := mem_centralizer_singleton_iff.mp hyu
  have hg : ξ⁻¹ * u = y ∨ ξ⁻¹ * u = y⁻¹ := by
    rcases hu with h1 | h1
    · left; rw [h1]; group
    · right; rw [h1]; group
  have hgH : ξ⁻¹ * u ∈ H := by
    rcases hg with h1 | h1
    · rw [h1]; exact hyH
    · rw [h1]; exact inv_mem hyH
  have hgo : orderOf (ξ⁻¹ * u) = 3 := by
    rcases hg with h1 | h1
    · rw [h1, hy3]
    · rw [h1, orderOf_inv, hy3]
  have huξ : u * ξ = ξ * u := by
    rcases hu with h1 | h1
    · have e : ξ = u * y⁻¹ := by rw [h1]; group
      rw [e]
      calc u * (u * y⁻¹) = u * (y⁻¹ * u) := by
            rw [show u * y⁻¹ = y⁻¹ * u by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hyu', ← mul_assoc, inv_mul_cancel, one_mul]]
        _ = u * y⁻¹ * u := by group
    · have e : ξ = u * y := by rw [h1]; group
      rw [e]
      calc u * (u * y) = u * (y * u) := by rw [hyu']
        _ = u * y * u := by group
  have hξu : ∀ w ∈ sec2Z A E F, ξ * w * ξ⁻¹ = u * w * u⁻¹ := fun w hw => by
    have h1 : (ξ⁻¹ * u) * w = w * (ξ⁻¹ * u) := (mem_centralizer_iff.mp (hHC hgH) w hw).symm
    calc ξ * w * ξ⁻¹ = ξ * (w * (ξ⁻¹ * u)) * u⁻¹ := by group
      _ = ξ * ((ξ⁻¹ * u) * w) * u⁻¹ := by rw [h1]
      _ = u * w * u⁻¹ := by group
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  have hFmem : F ∈ conjSet F H := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  have hξEA : ξ ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    have hF₀ : sec2F0 A E x ∈ conjSet F H := by
      rw [conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
      exact Set.mem_insert _ _
    have := inf_normalizer_le_normalizer_inf ⟨hξF _ hF₀, hξE E hEmem⟩
    rwa [sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS] at this
  have hξFA : ξ ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) := by
    have hE₀ : sec2F0 A F h ∈ conjSet E H := by
      rw [conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
      exact Set.mem_insert _ _
    have hhS' : h ∉ sec2S A R F E := by rwa [sec2S_comm h11 hE16 hF hL hodd]
    have := inf_normalizer_le_normalizer_inf ⟨hξE _ hE₀, hξF F hFmem⟩
    rwa [sec2F0_inf_eq h11 hE16 hF.symm hL hodd hh hhS'] at this
  have hfix : ∀ s ∈ sec2S A R E F, s⁻¹ * (ξ * s * ξ⁻¹) ∈ sec2Z A E F → s ∈ sec2Z A E F :=
    fun s hs hs' => mem_sec2Z_of_actsAsF4Scalar h11 hE16 hF hL hodd hF4 hs hs'
  obtain ⟨huEn, -, -, -⟩ := sec2U_facts h11 hE16 hF hL hodd huA hu3 huE
  refine ⟨ξ, ξ⁻¹ * u, hF4.1, hF4.2.1, hξ3, hF4, hξHS, hξH, hξEA, hξE, hgH,
    mul_mem (inv_mem (hξE E hEmem)) huEn, hgo, ?_⟩
  exact inv_mul_conj_mem_of_xi h11 hE16 hF hL hodd huA hu3 huE hξEA hξFA hF4.2.1 hfix huξ hξu

theorem mem_normalizer_inf_of_mem_sec2H {w : G} (hw : w ∈ sec2H E F)
    (hwE : w ∈ normalizer (E : Set G)) : w ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
  have hwPS : w ∈ normalizer ((sec2P E ⊔ sec2S A R E F : Subgroup G) : Set G) :=
    mem_normalizer_sup (Sec2.normalizer_le_normalizer_sec2P E hwE)
      (sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd hw)
  rw [← centralizerMod_sec2P_sup_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
  exact Sec2.mem_normalizer_centralizerMod hwPS hwPS
    (centralizer_le_normalizer _ (sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd hw))

theorem inv_mul_conj_mem_of_mem_normalizer {k : G} (hk : k ∈ sec2H E F)
    (hkE : k ∈ normalizer (E : Set G)) :
    ∀ a ∈ E ⊓ A, a⁻¹ * (k * a * k⁻¹) ∈ sec2Z A E F := by
  obtain ⟨ξ, g₀, -, hξZ, hξ3, hF4, hξHS, -, hξEA, -, hgH, hgE, hgo, hgfix⟩ :=
    exists_sec2Xi h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  set Z := sec2Z A E F with hZdef
  have hS := special_sec2S h11 hE16 hF hL hodd
  have hHC := sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd
  have hES : E ⊓ A ≤ sec2S A R E F :=
    inf_le_left.trans (le_sec2S_and_le_sec2S (A := A) (R := R) hF).1
  have hZE : Z ≤ E ⊓ A := by
    rw [hZdef, hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.1, hz.2⟩
  have h4E : Z.relIndex (E ⊓ A) = 4 := by
    have h := relIndex_mul_card Z (E ⊓ A)
    rw [inf_eq_left.mpr hZE, hF.card_sec2Z hodd, card_inf_left hF hodd] at h
    omega
  have hNZ : ∀ w ∈ sec2H E F, w ∈ normalizer (Z : Set G) := fun w hw =>
    centralizer_le_normalizer _ (hHC hw)
  have hN : ∀ w ∈ sec2H E F, w ∈ normalizer (E : Set G) →
      w ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) := fun w hw hwE =>
    mem_normalizer_inf_of_mem_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hw hwE
  have hkEA := hN k hk hkE
  have hkZ := hNZ k hk
  have hfixξ : ∀ a ∈ E ⊓ A, a⁻¹ * (ξ * a * ξ⁻¹) ∈ Z → a ∈ Z := fun a ha h' =>
    mem_sec2Z_of_actsAsF4Scalar h11 hE16 hF hL hodd hF4 (hES ha) h'
  have hpq : ∀ a ∈ E ⊓ A, (k * (ξ * a * ξ⁻¹) * k⁻¹)⁻¹ * (ξ * (k * a * k⁻¹) * ξ⁻¹) ∈ Z := by
    intro a ha
    have hs' : ξ⁻¹ * k * ξ * k⁻¹ ∈ sec2S A R E F := by
      have := hξHS k⁻¹ (inv_mem hk)
      simpa using this
    have hb : k * a * k⁻¹ ∈ sec2S A R E F := hES ((mem_normalizer_iff.mp hkEA a).mp ha)
    have e2 : k * (ξ * a * ξ⁻¹) * k⁻¹ =
        ξ * ((ξ⁻¹ * k * ξ * k⁻¹) * (k * a * k⁻¹) * (ξ⁻¹ * k * ξ * k⁻¹)⁻¹) * ξ⁻¹ := by group
    rw [e2]
    have hc := hS.comm_mem hs' ((sec2S A R E F).inv_mem hb)
    have e3 : (ξ * ((ξ⁻¹ * k * ξ * k⁻¹) * (k * a * k⁻¹) * (ξ⁻¹ * k * ξ * k⁻¹)⁻¹) * ξ⁻¹)⁻¹ *
        (ξ * (k * a * k⁻¹) * ξ⁻¹) = ξ * ((ξ⁻¹ * k * ξ * k⁻¹) * (k * a * k⁻¹)⁻¹ *
          (ξ⁻¹ * k * ξ * k⁻¹)⁻¹ * (k * a * k⁻¹)⁻¹⁻¹) * ξ⁻¹ := by group
    rw [e3]
    exact (mem_normalizer_iff.mp hξZ _).mp hc
  obtain ⟨r, hr, hkr⟩ := Sec2.trichotomy h4E hξEA hξZ hξ3 hfixξ hkEA hkZ hpq
  rcases hr with hr1 | hrξ
  · intro a ha
    have := hkr a ha
    rw [hr1] at this
    simpa using this
  exfalso
  have hrξ' : r = ξ ∨ r = ξ⁻¹ := hrξ
  have hrN : r ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    rcases hrξ' with rfl | rfl
    · exact hξEA
    · exact inv_mem hξEA
  obtain ⟨e, m, hm3, hm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos k).ne' 3 (by norm_num)
  have hk3 : (k ^ m) ^ 3 ^ e = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have hkΓ : k ^ m ∈ sec2H E F ⊓ normalizer (E : Set G) :=
    ⟨pow_mem hk m, pow_mem hkE m⟩
  obtain ⟨c, hc, j, hcj⟩ :=
    Sec2.exists_conj_eq_zpow (Γ := sec2H E F ⊓ normalizer (E : Set G)) ⟨hgH, hgE⟩ hgo
    (not_nine_dvd_card_inf h11 hE16 hF hL hodd hx hxS hh hhS h4 h4') hkΓ hk3
  set C := centralizerMod ⊤ (E ⊓ A) Z with hCdef
  have hgC : g₀⁻¹ ∈ C := by
    refine ⟨mem_top _, inv_mem (hNZ g₀ hgH), fun a ha => ?_⟩
    have := hgfix a ha
    simpa [mul_assoc] using this
  have hgjC : g₀ ^ j ∈ C := by
    have := C.inv_mem hgC
    rw [inv_inv] at this
    exact C.zpow_mem this j
  have hcN : c ∈ normalizer (C : Set G) :=
    Sec2.mem_normalizer_centralizerMod (le_normalizer (mem_top c)) (hN c hc.1 hc.2) (hNZ c hc.1)
  have hk₃C : k ^ m ∈ C := by
    rw [hcj]
    exact (mem_normalizer_iff.mp hcN _).mp hgjC
  have hk₃fix : ∀ a ∈ E ⊓ A, a⁻¹ * (k ^ m * a * (k ^ m)⁻¹) ∈ Z := fun a ha => by
    have := (mem_centralizerMod.mp (C.inv_mem hk₃C)).2.2 a ha
    simpa [mul_assoc] using this
  have hpow := Sec2.pow_conj_inv_mul_mem hrN hkZ hkr m
  have hξm : ξ ^ m = ξ ∨ ξ ^ m = ξ⁻¹ := by
    rw [pow_eq_pow_mod m hξ3]
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h1 | h1
    · left; rw [h1, pow_one]
    · right
      rw [h1, eq_inv_iff_mul_eq_one, ← pow_succ, hξ3]
  have hrm : r ^ m = ξ ∨ r ^ m = ξ⁻¹ := by
    rcases hrξ' with rfl | rfl
    · exact hξm
    · rw [inv_pow]
      rcases hξm with h1 | h1
      · right; rw [h1]
      · left; rw [h1, inv_inv]
  obtain ⟨a₀, ha₀, ha₀Z⟩ : ∃ a₀ ∈ E ⊓ A, a₀ ∉ Z := by
    by_contra hall
    push Not at hall
    have : Z.relIndex (E ⊓ A) = 1 := relIndex_eq_one.mpr hall
    omega
  have h1 : a₀⁻¹ * (r ^ m * a₀ * (r ^ m)⁻¹) ∈ Z :=
    Sec2.inv_mul_mem_trans (hk₃fix a₀ ha₀) (Sec2.inv_mul_mem_symm (hpow a₀ ha₀))
  apply ha₀Z
  rcases hrm with h2 | h2
  · rw [h2] at h1
    exact hfixξ a₀ ha₀ h1
  · rw [h2, inv_inv] at h1
    refine hfixξ a₀ ha₀ ?_
    have h3 := Sec2.conj_inv_mul_mem hξZ h1
    have e1 : ξ * (ξ⁻¹ * a₀ * ξ) * ξ⁻¹ = a₀ := by group
    rw [e1] at h3
    exact Sec2.inv_mul_mem_symm h3

theorem exists_coherent_family : ∃ (e : ↥(conjSet E (sec2H E F)) ≃ Fin 5) (X : Fin 5 → G),
    (∀ i, X i ∈ sec2S A R E F) ∧ (∀ i, X i ∉ sec2Z A E F) ∧
    (∀ i, X i ∈ ((e.symm i : ↥(conjSet E (sec2H E F))) : Subgroup G)) ∧
    (∀ h ∈ sec2H E F, ∀ i j, ((e.symm j : ↥(conjSet E (sec2H E F))) : Subgroup G) =
      rightConjugate ((e.symm i : ↥(conjSet E (sec2H E F))) : Subgroup G) h⁻¹ →
      (h * X i * h⁻¹)⁻¹ * X j ∈ sec2Z A E F) ∧
    ∃ i₀, ((e.symm i₀ : ↥(conjSet E (sec2H E F))) : Subgroup G) = E ∧ X i₀ ∈ E ⊓ A := by
  classical
  set H := sec2H E F with hHdef
  have hIE : InducesA5 H (conjSet E H) :=
    inducesA5_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have : Fintype ↥(conjSet E H) := Fintype.ofFinite _
  let e : ↥(conjSet E H) ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card, hIE.1])
  have hHC := sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd
  have hHS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd
  have hES : E ⊓ A ≤ sec2S A R E F :=
    inf_le_left.trans (le_sec2S_and_le_sec2S (A := A) (R := R) hF).1
  obtain ⟨a₀, ha₀, ha₀Z⟩ : ∃ a₀ ∈ E ⊓ A, a₀ ∉ sec2Z A E F := by
    by_contra hall
    push Not at hall
    have h3 := Subgroup.card_le_of_le (show E ⊓ A ≤ sec2Z A E F from hall)
    rw [card_inf_left hF hodd, hF.card_sec2Z hodd] at h3
    omega
  have ht : ∀ V : ↥(conjSet E H), ∃ t ∈ H, (V : Subgroup G) = rightConjugate E t :=
    fun V => V.2
  choose t htH htV using ht
  have hNZ : ∀ w ∈ H, w ∈ normalizer (sec2Z A E F : Set G) := fun w hw =>
    centralizer_le_normalizer _ (hHC hw)
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  refine ⟨e, fun i => (t (e.symm i))⁻¹ * a₀ * t (e.symm i), fun i => ?_, fun i hi => ?_,
    fun i => ?_, fun w hw i j hij => ?_, e ⟨E, hEmem⟩, by simp, ?_⟩
  · have := (mem_normalizer_iff.mp (inv_mem (hHS (htH (e.symm i)))) a₀).mp (hES ha₀)
    simpa using this
  · apply ha₀Z
    have := (mem_normalizer_iff.mp (hNZ _ (htH (e.symm i))) _).mp hi
    simpa [mul_assoc] using this
  · show (t (e.symm i))⁻¹ * a₀ * t (e.symm i) ∈ ((e.symm i : ↥(conjSet E H)) : Subgroup G)
    rw [htV (e.symm i), mem_rightConjugate_iff]
    have e1 : t (e.symm i) * ((t (e.symm i))⁻¹ * a₀ * t (e.symm i)) * (t (e.symm i))⁻¹ = a₀ := by
      group
    rw [e1]
    exact ha₀.1
  ·
    show (w * ((t (e.symm i))⁻¹ * a₀ * t (e.symm i)) * w⁻¹)⁻¹ *
      ((t (e.symm j))⁻¹ * a₀ * t (e.symm j)) ∈ sec2Z A E F
    set ti := t (e.symm i) with hti
    set tj := t (e.symm j) with htj
    have hc : ti * w⁻¹ ∈ H := H.mul_mem (htH _) (H.inv_mem hw)
    have hk : tj * (ti * w⁻¹)⁻¹ ∈ H := H.mul_mem (htH _) (H.inv_mem hc)
    have hkE : tj * (ti * w⁻¹)⁻¹ ∈ normalizer (E : Set G) := by
      rw [← rightConjugate_eq_self_iff]
      have h1 : rightConjugate E tj = rightConjugate E (ti * w⁻¹) := by
        rw [← htV (e.symm j), hij, htV (e.symm i), rightConjugate_mul]
      rw [← rightConjugate_mul, h1, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have hfix := inv_mul_conj_mem_of_mem_normalizer h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
      (H.inv_mem hk) (inv_mem hkE) a₀ ha₀
    have h3 := (mem_normalizer_iff.mp (hNZ _ (H.inv_mem hc)) _).mp hfix
    have e1 : (w * (ti⁻¹ * a₀ * ti) * w⁻¹)⁻¹ * (tj⁻¹ * a₀ * tj) =
        (ti * w⁻¹)⁻¹ * (a₀⁻¹ * ((tj * (ti * w⁻¹)⁻¹)⁻¹ * a₀ * (tj * (ti * w⁻¹)⁻¹)⁻¹⁻¹)) *
          (ti * w⁻¹)⁻¹⁻¹ := by group
    rw [e1]
    exact h3
  · show (t (e.symm (e ⟨E, hEmem⟩)))⁻¹ * a₀ * t (e.symm (e ⟨E, hEmem⟩)) ∈ E ⊓ A
    rw [Equiv.symm_apply_apply]
    have hE' := htV ⟨E, hEmem⟩
    have htE : t ⟨E, hEmem⟩ ∈ normalizer (E : Set G) :=
      (rightConjugate_eq_self_iff _ _).mp hE'.symm
    have hN := mem_normalizer_inf_of_mem_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
      (htH _) htE
    have := (mem_normalizer_iff.mp (inv_mem hN) a₀).mp ha₀
    simpa using this

theorem mem_sec2Z_of_forall_mem_sec2H {s : G} (hs : s ∈ sec2S A R E F)
    (hfix : ∀ k ∈ sec2H E F, s⁻¹ * (k * s * k⁻¹) ∈ sec2Z A E F) : s ∈ sec2Z A E F := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hZc := sec2Z_comm A E F
  have hSZ : sec2S A R E F ≤ normalizer (sec2Z A E F : Set G) :=
    (le_sup_right : sec2S A R E F ≤ sec2P E ⊔ sec2S A R E F).trans
      (sec2P_sup_sec2S_le_normalizer_sec2Z h11 hE16 hF hL hodd)
  have hmod : ∀ y ∈ sec2H E F, y⁻¹ * s⁻¹ * y * s ∈ sec2Z A E F := fun y hy => by
    have h1 := hfix y⁻¹ (inv_mem hy)
    have e : y⁻¹ * s⁻¹ * y * s = (s⁻¹ * (y⁻¹ * s * y⁻¹⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hPSH : sec2P E ⊔ sec2S A R E F ≤ sec2H E F := sup_le le_sup_left (sec2S_le_sec2H hF)
  have hEA : s ∈ E ⊓ A := by
    rw [← centralizerMod_sec2P_sup_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
    exact ⟨mem_sup_right hs, hSZ hs, fun y hy => hmod y (hPSH hy)⟩
  have hhS' : h ∉ sec2S A R F E := by rwa [hSc]
  have hxS' : x ∉ sec2S A R F E := by rwa [hSc]
  have hFA : s ∈ F ⊓ A := by
    rw [← centralizerMod_sec2P_sup_eq h11 hE16 hF.symm hL hodd hh hhS' hx hxS' h4' h4, hSc,
      hZc]
    have hPSH' : sec2P F ⊔ sec2S A R E F ≤ sec2H E F := sup_le le_sup_right (sec2S_le_sec2H hF)
    have hSZ' : sec2S A R E F ≤ normalizer (sec2Z A E F : Set G) := hSZ
    exact ⟨mem_sup_right hs, hSZ' hs, fun y hy => hmod y (hPSH' hy)⟩
  rw [hF.sec2Z_eq]
  exact ⟨⟨hEA.1, hFA.1⟩, hEA.2⟩

theorem exists_sec2_family : ∃ (φ : ↥(sec2H E F) →* alternatingGroup (Fin 5))
    (q : Fin 5 → Abelianization ↥(sec2S A R E F)) (i₀ : Fin 5) (X₀ : G)
    (hX₀ : X₀ ∈ sec2S A R E F),
    Function.Surjective φ ∧ φ.ker = (sec2S A R E F).subgroupOf (sec2H E F) ∧
    (∀ v, Sec2.coordProd q v = 1 ↔ v = 0 ∨ v = 1) ∧ Sec2.coordProd q 1 = 1 ∧
    (∀ k : ↥(sec2H E F), ∀ i, Sec2.abelConj (k : G)
      (sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd k.2) (q i) =
        q (((φ k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) i)) ∧
    q i₀ = Abelianization.of ⟨X₀, hX₀⟩ ∧ X₀ ∈ E ⊓ A ∧ X₀ ∉ sec2Z A E F ∧
    ∀ k : ↥(sec2H E F), ((φ k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) i₀ = i₀ →
      (k : G) ∈ normalizer (E : Set G) := by
  classical
  set H := sec2H E F with hHdef
  have hS := special_sec2S h11 hE16 hF hL hodd
  have hHS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd
  obtain ⟨e, X, hXS, hXZ, hXV, hXeq, i₀, hi₀, hXi₀⟩ :=
    exists_coherent_family h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨hpl, hEE, -, -⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hHP : H ≤ Sec2.conjSetStab (conjSet E H) := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  set ψ := Sec2.conjPermHom hHP with hψ
  have hIE : InducesA5 H (conjSet E H) :=
    inducesA5_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have : Fintype ↥(conjSet E H) := Fintype.ofFinite _
  have hcard := Sec2.card_range_conjPermHom hHP hIE
  have hperm : Nat.card (Equiv.Perm ↥(conjSet E H)) = 120 := by
    rw [Nat.card_perm, hIE.1]
    decide
  have hidx : ψ.range.index = 2 := by
    have := ψ.range.index_mul_card
    rw [hcard, hperm] at this
    omega
  have hrange : ψ.range = alternatingGroup ↥(conjSet E H) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  have hmem : ∀ k : ↥H, ψ k ∈ alternatingGroup ↥(conjSet E H) := fun k =>
    hrange ▸ (⟨k, rfl⟩ : ψ k ∈ ψ.range)
  set ψ' := ψ.codRestrict (alternatingGroup ↥(conjSet E H)) hmem with hψ'
  set φ := (Equiv.altCongrHom e).toMonoidHom.comp ψ' with hφdef
  have hφ : ∀ k : ↥H, ∀ i, ((φ k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) i =
      e (ψ k (e.symm i)) := fun k i => rfl
  have hsurj : Function.Surjective φ := by
    refine (Equiv.altCongrHom e).surjective.comp ?_
    rintro ⟨τ, hτ⟩
    obtain ⟨k, hk⟩ := (hrange ▸ hτ : τ ∈ ψ.range)
    exact ⟨k, Subtype.ext hk⟩
  have hkerφ : φ.ker = (sec2S A R E F).subgroupOf H := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, mem_subgroupOf]
    have hk1 : ψ' k = 1 ↔ ψ k = 1 := by
      rw [hψ', ← Subtype.coe_inj]
      rfl
    rw [hk1, Sec2.conjPermHom_eq_one_iff]
    constructor
    · exact mem_sec2S_of_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' k.2
    · intro hkS V hV
      exact sec2S_le_normalizer_of_sec2Z_le h11 hE16 hF hL hodd (hpl V (Or.inl hV)).2.2.1
        (hpl V (Or.inl hV)).2.2.2 hkS
  set q : Fin 5 → Abelianization ↥(sec2S A R E F) := fun i =>
    Abelianization.of ⟨X i, hXS i⟩ with hqdef
  have hqeq : ∀ k : ↥H, ∀ i, Sec2.abelConj (k : G) (hHS k.2) (q i) =
      q (((φ k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) i) := by
    intro k i
    rw [hqdef, Sec2.abelConj_of, Sec2.abel_of_eq_of_iff hS]
    refine hXeq k k.2 i _ ?_
    rw [hφ, Equiv.symm_apply_apply]
    exact Sec2.conjPermHom_apply hHP k (e.symm i)
  have hq1 : ∀ i, q i ≠ 1 := fun i h1 => hXZ i ((Sec2.abel_of_eq_one_iff hS).mp h1)
  have hq2 : ∀ i j, i ≠ j → q i ≠ q j := fun i j hij h1 => by
    have h2 := (Sec2.abel_of_eq_of_iff hS).mp h1
    have hVne : ((e.symm i : ↥(conjSet E H)) : Subgroup G) ≠ (e.symm j : Subgroup G) :=
      fun h3 => hij (e.symm.injective (Subtype.ext h3))
    have hZj := (hpl _ (Or.inl (e.symm j).2)).2.2.1
    have hXij : X i ∈ ((e.symm j : ↥(conjSet E H)) : Subgroup G) := by
      have e1 : X i = X j * ((X i)⁻¹ * X j)⁻¹ := by group
      rw [e1]
      exact mul_mem (hXV j) (inv_mem (hZj h2))
    apply hXZ i
    rw [← hEE _ (e.symm i).2 _ (e.symm j).2 hVne]
    exact ⟨hXV i, hXij⟩
  have hall : Sec2.coordProd q 1 = 1 := by
    have hinv : ∀ k : ↥H, Sec2.abelConj (k : G) (hHS k.2) (Sec2.coordProd q 1) =
        Sec2.coordProd q 1 := fun k => by
      rw [Sec2.map_coordProd]
      have h1 : (Sec2.abelConj (k : G) (hHS k.2)) ∘ q =
          q ∘ ((φ k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := funext (hqeq k)
      rw [h1, Sec2.coordProd_comp, Sec2V4.act_one']
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Sec2.coordProd q 1)
    have hy' : Abelianization.of y = Sec2.coordProd q 1 := hy
    have hyZ : (y : G) ∈ sec2Z A E F := by
      refine mem_sec2Z_of_forall_mem_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' y.2
        fun k hk => ?_
      have h1 := hinv ⟨k, hk⟩
      rw [← hy', Sec2.abelConj_of, Sec2.abel_of_eq_of_iff hS] at h1
      exact Sec2.inv_mul_mem_symm h1
    rw [← hy']
    exact (Sec2.abel_of_eq_one_iff hS).mpr hyZ
  refine ⟨φ, q, i₀, X i₀, hXS i₀, hsurj, hkerφ, Sec2.coordProd_eq_one_iff hS hq1 hq2 hall, hall,
    hqeq, rfl, hXi₀, hXZ i₀, fun k hk => ?_⟩
  rw [hφ] at hk
  have h1 : ψ k (e.symm i₀) = e.symm i₀ := by
    have := congrArg e.symm hk
    rwa [Equiv.symm_apply_apply] at this
  have h2 := congrArg Subtype.val h1
  rw [Sec2.conjPermHom_apply, hi₀] at h2
  simpa using inv_mem ((rightConjugate_eq_self_iff _ _).mp h2)

theorem exists_sec2V : ∃ φ : ↥(sec2H E F) →* alternatingGroup (Fin 5),
    Function.Surjective φ ∧ φ.ker = (sec2S A R E F).subgroupOf (sec2H E F) ∧
    ∃ (S₂ S₃ : Subgroup G) (ψ₂ ψ₃ : G → (Fin 5 → ZMod 2)),
      S₂ ⊔ S₃ = sec2S A R E F ∧ S₂ ⊓ S₃ = sec2Z A E F ∧
      ∀ i ∈ ({(S₂, ψ₂), (S₃, ψ₃)} : Set (Subgroup G × (G → (Fin 5 → ZMod 2)))),
        sec2Z A E F ≤ i.1 ∧ i.1 ≤ sec2S A R E F ∧
        (∀ a ∈ i.1, ∀ b ∈ i.1, i.2 (a * b) = i.2 a + i.2 b) ∧
        (∀ a ∈ i.1, i.2 a = 0 ↔ a ∈ sec2Z A E F) ∧
        (∀ a ∈ i.1, ∑ k, i.2 a k = 0) ∧
        (∀ v : Fin 5 → ZMod 2, ∑ k, v k = 0 → ∃ a ∈ i.1, i.2 a = v) ∧
        ∀ h : ↥(sec2H E F), ∀ a ∈ i.1, (h : G) * a * (h : G)⁻¹ ∈ i.1 ∧
          i.2 ((h : G) * a * (h : G)⁻¹) =
            fun k => i.2 a (((φ h : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ k) := by
  classical
  set H := sec2H E F with hHdef
  have hS := special_sec2S h11 hE16 hF hL hodd
  have hHS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd
  obtain ⟨φ, q, i₀, X₀, hX₀, hφs, hφk, hker, hall, hqeq, hqi₀, hX₀EA, hX₀Z, hstab⟩ :=
    exists_sec2_family h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨ξ, -, hξS, -, -, hF4, hξHS, hξH, hξEA, -, -, -, -, -⟩ :=
    exists_sec2Xi h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  set q' : Fin 5 → Abelianization ↥(sec2S A R E F) := fun i => Sec2.abelConj ξ hξS (q i)
    with hq'def
  have hinvξ : ∀ m, Sec2.abelConj ξ⁻¹ (inv_mem hξS) (Sec2.abelConj ξ hξS m) = m := fun m => by
    rw [Sec2.abelConj_abelConj, Sec2.abelConj_congr _ (one_mem _) (inv_mul_cancel ξ),
      Sec2.abelConj_one]
  have hcp' : ∀ v, Sec2.coordProd q' v = Sec2.abelConj ξ hξS (Sec2.coordProd q v) := fun v => by
    rw [Sec2.map_coordProd]
    rfl
  have hker' : ∀ v, Sec2.coordProd q' v = 1 ↔ v = 0 ∨ v = 1 := fun v => by
    rw [hcp', ← hker v]
    constructor
    · intro h1
      have := congrArg (Sec2.abelConj ξ⁻¹ (inv_mem hξS)) h1
      rwa [hinvξ, map_one] at this
    · intro h1
      rw [h1, map_one]
  have hall' : Sec2.coordProd q' 1 = 1 := by rw [hcp', hall, map_one]
  have hqeq' : ∀ k : ↥H, ∀ i, Sec2.abelConj (k : G) (hHS k.2) (q' i) =
      q' (((φ k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) i) := by
    intro k i
    have hk' : ξ⁻¹ * k * ξ ∈ H := by
      have := (mem_normalizer_iff.mp (inv_mem hξH) k).mp k.2
      simpa using this
    have hφk' : φ ⟨ξ⁻¹ * k * ξ, hk'⟩ = φ k := by
      rw [← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, hφk, mem_subgroupOf]
      have h1 := hξHS (k : G)⁻¹ (inv_mem k.2)
      have e : ((⟨ξ⁻¹ * k * ξ, hk'⟩ * k⁻¹ : ↥H) : G) = ξ⁻¹ * (k : G)⁻¹⁻¹ * ξ * (k : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [e]
      exact h1
    rw [hq'def]
    simp only
    rw [Sec2.abelConj_abelConj, Sec2.abelConj_congr _ (mul_mem hξS (hHS hk'))
      (show (k : G) * ξ = ξ * (ξ⁻¹ * k * ξ) by group), ← Sec2.abelConj_abelConj hξS (hHS hk'),
      hqeq ⟨ξ⁻¹ * k * ξ, hk'⟩, hφk']
  set S₂ := Sec2.summand hS q with hS₂
  set S₃ := Sec2.summand hS q' with hS₃
  have hP₂ := Sec2.summand_props hS hker hall hHS φ hqeq
  have hP₃ := Sec2.summand_props hS hker' hall' hHS φ hqeq'
  have hinf : S₂ ⊓ S₃ = sec2Z A E F := by
    refine le_antisymm (fun a ha => ?_) (le_inf hP₂.1 hP₃.1)
    by_contra haZ
    let N : AddSubgroup (Fin 5 → ZMod 2) :=
      { carrier := {v | ∃ b ∈ S₂ ⊓ S₃, Sec2.summandCoord q b = v}
        add_mem' := by
          rintro _ _ ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩
          exact ⟨b₁ * b₂, mul_mem hb₁ hb₂, hP₂.2.2.1 _ hb₁.1 _ hb₂.1⟩
        zero_mem' := ⟨1, one_mem _, (hP₂.2.2.2.1 _ (one_mem _)).mpr (one_mem _)⟩
        neg_mem' := by
          rintro _ ⟨b, hb, rfl⟩
          refine ⟨b, hb, ?_⟩
          funext k
          rw [Pi.neg_apply, ZMod.neg_eq_self_mod_two] }
    have hNinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ N, Sec2V4.act σ v ∈ N := by
      rintro σ hσ _ ⟨b, hb, rfl⟩
      obtain ⟨k, hk⟩ := hφs ⟨σ, hσ⟩
      obtain ⟨hkb₂, hkc₂⟩ := hP₂.2.2.2.2.2.2 k b hb.1
      obtain ⟨hkb₃, -⟩ := hP₃.2.2.2.2.2.2 k b hb.2
      refine ⟨(k : G) * b * (k : G)⁻¹, ⟨hkb₂, hkb₃⟩, ?_⟩
      rw [hkc₂, hk]
      rfl
    have hall_N : ∀ w, Sec2V4.IsEven w → w ∈ N := fun w hw =>
      Sec2V4.mem_of_invariant hNinv ⟨a, ha, rfl⟩ (hP₂.2.2.2.2.1 a ha.1)
        (fun h0 => haZ ((hP₂.2.2.2.1 a ha.1).mp h0)) hw
    have hle : ∀ b ∈ S₂, b ∈ S₃ := fun b hb => by
      obtain ⟨b', hb', hb'v⟩ := hall_N _ (hP₂.2.2.2.2.1 b hb)
      have hinv' : Sec2.summandCoord q b'⁻¹ = Sec2.summandCoord q b' := by
        have h1 := hP₂.2.2.1 _ hb'.1 _ (inv_mem hb'.1)
        rw [mul_inv_cancel, (hP₂.2.2.2.1 _ (one_mem _)).mpr (one_mem _)] at h1
        funext k
        have := congrFun h1 k
        simp only [Pi.zero_apply, Pi.add_apply] at this
        rw [eq_neg_of_add_eq_zero_right this.symm, ZMod.neg_eq_self_mod_two]
      have h1 : Sec2.summandCoord q (b'⁻¹ * b) = 0 := by
        rw [hP₂.2.2.1 _ (inv_mem hb'.1) _ hb, hinv', hb'v]
        funext k
        simp only [Pi.add_apply, Pi.zero_apply]
        have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
        exact h2 _
      have hZ := (hP₂.2.2.2.1 _ (mul_mem (inv_mem hb'.1) hb)).mp h1
      have e : b = b' * (b'⁻¹ * b) := by group
      rw [e]
      exact mul_mem hb'.2 (hP₃.1 hZ)
    have hX₀₂ : X₀ ∈ S₂ := (Sec2.mem_summand hS).mpr ⟨hX₀, Pi.single i₀ 1, by
      rw [Sec2.coordProd_single, hqi₀]⟩
    have hX₀₃ := hle X₀ hX₀₂
    have hξX₀S : ξ * X₀ * ξ⁻¹ ∈ sec2S A R E F := (mem_normalizer_iff.mp hξS X₀).mp hX₀
    have hof : Sec2.coordProd q' (Pi.single i₀ 1) = Abelianization.of ⟨ξ * X₀ * ξ⁻¹, hξX₀S⟩ := by
      rw [Sec2.coordProd_single]
      show Sec2.abelConj ξ hξS (q i₀) = _
      rw [hqi₀, Sec2.abelConj_of]
      rfl
    have hξX₀ : ξ * X₀ * ξ⁻¹ ∈ S₃ :=
      (Sec2.mem_summand hS).mpr ⟨hξX₀S, Pi.single i₀ 1, hof⟩
    have heven' : ∀ j : Fin 5, Sec2V4.IsEven (1 + Pi.single j (1 : ZMod 2)) := by decide
    have heven := heven' i₀
    have hw : Sec2.summandCoord q' (ξ * X₀ * ξ⁻¹) = 1 + Pi.single i₀ 1 :=
      Sec2.summandCoord_eq hS hker' hξX₀S heven (by rw [Sec2.coordProd_add hS, hall', one_mul, hof])
    have hv : Sec2.summandCoord q' X₀ = 1 + Pi.single i₀ 1 := by
      refine Sec2.eq_of_forall_act_eq (hP₃.2.2.2.2.1 X₀ hX₀₃)
        (fun h0 => hX₀Z ((hP₃.2.2.2.1 X₀ hX₀₃).mp h0)) fun σ hσ hσi => ?_
      obtain ⟨k, hk⟩ := hφs ⟨σ, hσ⟩
      have hσ' : ((φ k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = σ := by rw [hk]
      have hkE := hstab k (by rw [hσ']; exact hσi)
      have hkX := inv_mul_conj_mem_of_mem_normalizer h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
        k.2 hkE X₀ hX₀EA
      obtain ⟨hkX₃, hkc⟩ := hP₃.2.2.2.2.2.2 k X₀ hX₀₃
      have h1 := (Sec2.summandCoord_eq_iff hS hker' hall' hX₀₃ hkX₃).mpr hkX
      rw [← hσ']
      exact hkc.symm.trans h1.symm
    have h2 := (Sec2.summandCoord_eq_iff hS hker' hall' hX₀₃ hξX₀).mp (hv.trans hw.symm)
    exact hX₀Z (mem_sec2Z_of_actsAsF4Scalar h11 hE16 hF hL hodd hF4 hX₀ h2)
  have hS₂card := Sec2.card_summand hS hker hall
  have hS₃card := Sec2.card_summand hS hker' hall'
  have hnorm : S₃ ≤ normalizer (S₂ : Set G) := fun b hb =>
    Sec2.mem_normalizer_of_forall_conj_mem fun a ha => by
      have e : b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact mul_mem (hP₂.1 (hS.comm_mem (hP₃.2.1 hb) (hP₂.2.1 ha))) ha
  have hcard := Sec2.card_sup_mul_card_inf hnorm
  rw [hinf, hS₂card, hS₃card, hF.card_sec2Z hodd] at hcard
  have hsup : S₂ ⊔ S₃ = sec2S A R E F := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hP₂.2.1 hP₃.2.1) ?_
    rw [card_sec2S h11 hE16 hF hL hodd]
    omega
  refine ⟨φ, hφs, hφk, S₂, S₃, Sec2.summandCoord q, Sec2.summandCoord q', hsup, hinf, ?_⟩
  rintro i (rfl | rfl)
  · exact hP₂
  · exact hP₃

end FrameXH

end CFSG.ComponentClassification.AS81
