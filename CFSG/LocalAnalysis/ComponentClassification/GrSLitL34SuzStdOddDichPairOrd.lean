module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichSetup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.GS82P10Centre
import CFSG.GroupTheory.CommuteOfSqEqOne
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
private theorem mem_coreActionKernel_of_commutator_mem {L : Subgroup G} {e : G}
    (heN : e ∈ normalizer (L : Set G))
    (he : ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ oddIn L) :
    e ∈ UnbalancedLayer.coreActionKernel L := by
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨heN, fun j hj => ?_⟩
  have hl : e⁻¹ * j * e ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem heN) j).mp hj
    rwa [inv_inv] at h
  have h1 := he (e⁻¹ * j * e) hl
  have h2 : j * e⁻¹ * j⁻¹ * e ∈ oddIn L := by
    convert h1 using 1
    group
  have h3 : e⁻¹ * j⁻¹ * e * j ∈ oddIn L := by
    have h := CFSG.ComponentClassification.GrSLit.GrS4.conj_mem_oddIn (inv_mem hj) h2
    rwa [show j⁻¹ * (j * e⁻¹ * j⁻¹ * e) * j⁻¹⁻¹ = e⁻¹ * j⁻¹ * e * j by group] at h
  change j⁻¹ * e⁻¹ * j * e ∈ oddIn L
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using inv_mem h3

private theorem l34SuzOddPair_E1_isElemAbelian
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} {P E₁ : Subgroup G} {a : G}
    (hP : L34SuzOddPairData t u V P E₁ a) :
    Open.IsElemAbelian 2 E₁ ∧ E₁ ≤ Subgroup.centralizer ({t} : Set G) := by
  have ht2 : t * t = 1 := by rw [← sq, ← hS.orderOf_t, pow_orderOf_eq_one]
  have hVea : Open.IsElemAbelian 2 V := by
    have h := Open.IsElemAbelian.closure_of_commute (p := 2) (s := (V : Set G))
      (fun x hx y hy => CFSG.commute_of_sq_eq_one
        (by rw [pow_two]; exact hD.mul_self x hx)
        (by rw [pow_two]; exact hD.mul_self y hy)
        (by rw [pow_two]; exact hD.mul_self (x * y) (V.mul_mem hx hy)))
      (fun x hx => by rw [pow_two]; exact hD.mul_self x hx)
    simpa [Subgroup.closure_eq] using h
  have htV : t ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.mp hS.t_mem v (hD.le_A hv)
  have hVt_ea : Open.IsElemAbelian 2 (V ⊔ zpowers t) :=
    Open.IsElemAbelian.sup_of_commute hVea
      (Open.isElemAbelian_zpowers (by rw [pow_two]; exact ht2)) fun v hv w hw =>
        Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr htV) hw) v hv
  have hE1_ea : Open.IsElemAbelian 2 E₁ := hVt_ea.mono hP.le_sup
  have hE1t : E₁ ≤ Subgroup.centralizer ({t} : Set G) := by
    refine hP.le_sup.trans (sup_le ?_ ?_)
    · intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hS.t_mem v (hD.le_A hv)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  exact ⟨hE1_ea, hE1t⟩

private theorem l34SuzOddPair_F_elemAbelian
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} {P E₁ : Subgroup G} {a : G}
    (hP : L34SuzOddPairData t u V P E₁ a) :
    Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.zpowers (t * a * t⁻¹)) ∧
    (∀ x ∈ E₁, x * a = a * x) ∧
    (∀ x ∈ E₁, x * (t * a * t⁻¹) = (t * a * t⁻¹) * x) := by
  obtain ⟨hE1_ea, hE1t⟩ := l34SuzOddPair_E1_isElemAbelian hS hD hP
  have ht2 : t * t = 1 := by rw [← sq, ← hS.orderOf_t, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ha2 : a * a = 1 := hP.mul_self
  have ha'2 : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 := by
    simp [ha2]
  have hcomm_E1_a : ∀ x ∈ E₁, x * a = a * x := by
    intro x hx
    exact (hP.commute_of_mem x hx).symm
  have hcomm_E1_a' : ∀ x ∈ E₁, x * (t * a * t⁻¹) = (t * a * t⁻¹) * x := by
    intro x hx
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hE1t hx)
    have hxa : x * a = a * x := hcomm_E1_a x hx
    change x * (t * a * t⁻¹) = (t * a * t⁻¹) * x
    rw [htinv]
    calc x * (t * a * t) = (x * t) * a * t := by group
      _ = (t * x) * a * t := by rw [hxt]
      _ = t * (x * a) * t := by group
      _ = t * (a * x) * t := by rw [hxa]
      _ = t * a * x * t := by group
      _ = t * a * t * x := by rw [mul_assoc, hxt, ← mul_assoc]
      _ = (t * a * t) * x := by group
  have hF_ea : Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.zpowers (t * a * t⁻¹)) := by
    refine Open.IsElemAbelian.sup_of_commute hE1_ea
      (Open.isElemAbelian_zpowers (by rw [pow_two]; exact ha'2)) ?_
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp
      ((Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr
        (fun z hz => hcomm_E1_a' z hz))) hy) x hx
  exact ⟨hF_ea, hcomm_E1_a, hcomm_E1_a'⟩

private theorem l34SuzOddPair_a'_notin
    {u : G} {P E₁ : Subgroup G} {a : G}
    (hP : L34SuzOddPairData t u V P E₁ a) :
    t * a * t⁻¹ ∉ E₁ := by
  have ha2 : a * a = 1 := hP.mul_self
  intro ha'
  have hle : E₁ ⊔ closure ({a, t * a * t⁻¹} : Set G) ≤ E₁ ⊔ zpowers a := by
    refine sup_le le_sup_left ?_
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_sup_left ha'
  have hcent : E₁ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hP.commute_of_mem e he).symm
  have hcent_z : E₁ ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_eq_closure]
    rw [Subgroup.centralizer_closure]
    exact hcent
  have hnorm : E₁ ≤ Subgroup.normalizer ((zpowers a) : Set G) :=
    hcent_z.trans (Subgroup.centralizer_le_normalizer _)
  have hcard_mul : Nat.card ↥(E₁ ⊔ zpowers a) * Nat.card ↥(E₁ ⊓ zpowers a) =
      Nat.card E₁ * Nat.card ↥(zpowers a) :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hnorm
  have hcard_bound : Nat.card ↥(E₁ ⊔ zpowers a) ≤ Nat.card E₁ * Nat.card ↥(zpowers a) := by
    have hpos : 0 < Nat.card ↥(E₁ ⊓ zpowers a) := Nat.card_pos
    nlinarith
  have hcard_le : 16 ≤ Nat.card ↥(E₁ ⊔ zpowers a) := by
    rw [← hP.card_sup]
    exact Subgroup.card_le_of_le hle
  have hzpow_card : Nat.card ↥(zpowers a) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact ha2)
  have hE1card : Nat.card E₁ = 4 := hP.card_eq
  have hbound' : Nat.card ↥(E₁ ⊔ zpowers a) ≤ 8 := by
    calc Nat.card ↥(E₁ ⊔ zpowers a) ≤ Nat.card E₁ * Nat.card ↥(zpowers a) := hcard_bound
      _ = 4 * Nat.card ↥(zpowers a) := by rw [hE1card]
      _ ≤ 4 * 2 := by nlinarith
      _ = 8 := by norm_num
  omega

private theorem l34SuzOddPair_F_card
    {u : G} {P E₁ : Subgroup G} {a a' : G}
    (hP : L34SuzOddPairData t u V P E₁ a) (ha' : a' = t * a * t⁻¹)
    (hcomm_E1_a' : ∀ x ∈ E₁, x * a' = a' * x)
    (ha'_notin : a' ∉ E₁) :
    orderOf a' = 2 ∧ Nat.card ↥(E₁ ⊔ Subgroup.zpowers a') = 8 := by
  have ha2 : a * a = 1 := hP.mul_self
  have ha'2 : a' * a' = 1 := by
    rw [ha']
    simp [ha2]
  have ha'ord : orderOf a' = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨by rw [pow_two]; exact ha'2, by intro h; exact ha'_notin (h ▸ E₁.one_mem)⟩
  have hF_card : Nat.card ↥(E₁ ⊔ Subgroup.zpowers a') = 8 := by
    have hcent' : E₁ ≤ Subgroup.centralizer ({a'} : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm_E1_a' e he
    have hcent_z' : E₁ ≤ Subgroup.centralizer (Subgroup.zpowers a' : Set G) := by
      rw [Subgroup.zpowers_eq_closure]
      rw [Subgroup.centralizer_closure]
      exact hcent'
    have hnorm' : E₁ ≤ Subgroup.normalizer ((zpowers a') : Set G) :=
      hcent_z'.trans (Subgroup.centralizer_le_normalizer _)
    have hcard_eq : Nat.card ↥(E₁ ⊔ zpowers a') * Nat.card ↥(E₁ ⊓ zpowers a') =
        Nat.card E₁ * Nat.card ↥(zpowers a') :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hnorm'
    have hdisj : E₁ ⊓ zpowers a' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hxE : x ∈ E₁ := (Subgroup.mem_inf.mp hx).1
      have hxa' : x ∈ zpowers a' := (Subgroup.mem_inf.mp hx).2
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxa'
      have hxa'_power : a' ^ n = 1 ∨ a' ^ n = a' := by
        have h2 : a' ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha'2
        rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        · left
          rw [hk, show k + k = 2 * k by ring, zpow_mul, h2, one_zpow]
        · right
          rw [hk, show 2 * k + 1 = 2 * k + 1 by rfl, zpow_add, zpow_mul, h2, one_zpow,
            one_mul, zpow_one]
      rcases hxa'_power with h1 | h2
      · exact h1
      · rw [h2] at hxE
        exact absurd hxE ha'_notin
    rw [hdisj, Subgroup.card_bot, mul_one, hP.card_eq, Nat.card_zpowers, ha'ord] at hcard_eq
    omega
  exact ⟨ha'ord, hF_card⟩

private theorem l34SuzOddPair_aa'_notin
    {u : G} {P E₁ : Subgroup G} {a a' : G}
    (hP : L34SuzOddPairData t u V P E₁ a)
    (haa' : a * a' = a' * a)
    (ha' : a' = t * a * t⁻¹) :
    a * a' ∉ E₁ := by
  subst ha'
  have ha2 : a * a = 1 := hP.mul_self
  intro h
  have hle : E₁ ⊔ closure ({a, t * a * t⁻¹} : Set G) ≤ E₁ ⊔ zpowers a := by
    refine sup_le le_sup_left ?_
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have ha'eq : t * a * t⁻¹ = (a * (t * a * t⁻¹)) * a := by
        calc t * a * t⁻¹ = a * (a * (t * a * t⁻¹)) := by rw [← mul_assoc, ha2, one_mul]
          _ = a * ((t * a * t⁻¹) * a) := by rw [haa']
          _ = (a * (t * a * t⁻¹)) * a := by group
      rw [ha'eq]
      exact Subgroup.mul_mem_sup h (Subgroup.mem_zpowers a)
  have hcent : E₁ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hP.commute_of_mem e he).symm
  have hcent_z : E₁ ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_eq_closure]
    rw [Subgroup.centralizer_closure]
    exact hcent
  have hnorm : E₁ ≤ Subgroup.normalizer ((zpowers a) : Set G) :=
    hcent_z.trans (Subgroup.centralizer_le_normalizer _)
  have hcard_mul : Nat.card ↥(E₁ ⊔ zpowers a) * Nat.card ↥(E₁ ⊓ zpowers a) =
      Nat.card E₁ * Nat.card ↥(zpowers a) :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hnorm
  have hcard_bound : Nat.card ↥(E₁ ⊔ zpowers a) ≤ Nat.card E₁ * Nat.card ↥(zpowers a) := by
    have hpos : 0 < Nat.card ↥(E₁ ⊓ zpowers a) := Nat.card_pos
    nlinarith
  have hcard_le : 16 ≤ Nat.card ↥(E₁ ⊔ zpowers a) := by
    rw [← hP.card_sup]
    exact Subgroup.card_le_of_le hle
  have hzpow_card : Nat.card ↥(zpowers a) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact ha2)
  have hE1card : Nat.card E₁ = 4 := hP.card_eq
  have hbound' : Nat.card ↥(E₁ ⊔ zpowers a) ≤ 8 := by
    calc Nat.card ↥(E₁ ⊔ zpowers a) ≤ Nat.card E₁ * Nat.card ↥(zpowers a) := hcard_bound
      _ = 4 * Nat.card ↥(zpowers a) := by rw [hE1card]
      _ ≤ 4 * 2 := by nlinarith
      _ = 8 := by norm_num
  omega

private theorem l34SuzOddPair_J_card
    {u : G} {P E₁ : Subgroup G} {a a' : G}
    (hP : L34SuzOddPairData t u V P E₁ a)
    (_ha' : a' = t * a * t⁻¹)
    (hcomm_E1_aa' : ∀ z ∈ E₁, z * (a * a') = (a * a') * z)
    (haa'_notin : a * a' ∉ E₁)
    (hd2 : (a * a') * (a * a') = 1) :
    Nat.card ↥(E₁ ⊔ Subgroup.zpowers (a * a')) = 8 := by
  have hcent_aa' : E₁ ≤ Subgroup.centralizer ({a * a'} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm_E1_aa' e he
  have hcent_z : E₁ ≤ Subgroup.centralizer (Subgroup.zpowers (a * a') : Set G) := by
    rw [Subgroup.zpowers_eq_closure]
    rw [Subgroup.centralizer_closure]
    exact hcent_aa'
  have hnorm : E₁ ≤ Subgroup.normalizer ((zpowers (a * a')) : Set G) :=
    hcent_z.trans (Subgroup.centralizer_le_normalizer _)
  have hcard_eq : Nat.card ↥(E₁ ⊔ zpowers (a * a')) * Nat.card ↥(E₁ ⊓ zpowers (a * a')) =
      Nat.card E₁ * Nat.card ↥(zpowers (a * a')) :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hnorm
  have hd_ord : orderOf (a * a') = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨by rw [pow_two]; exact hd2, by intro h; exact haa'_notin (h ▸ E₁.one_mem)⟩
  have hdisj : E₁ ⊓ zpowers (a * a') = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxE : x ∈ E₁ := (Subgroup.mem_inf.mp hx).1
    have hxa' : x ∈ zpowers (a * a') := (Subgroup.mem_inf.mp hx).2
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxa'
    have hxa'_power : (a * a') ^ n = 1 ∨ (a * a') ^ n = (a * a') := by
      have h2 : (a * a') ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hd2
      rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · left
        rw [hk, show k + k = 2 * k by ring, zpow_mul, h2, one_zpow]
      · right
        rw [hk, show 2 * k + 1 = 2 * k + 1 by rfl, zpow_add, zpow_mul, h2, one_zpow,
          one_mul, zpow_one]
    rcases hxa'_power with h1 | h2
    · exact h1
    · rw [h2] at hxE
      exact absurd hxE haa'_notin
  rw [hdisj, Subgroup.card_bot, mul_one, hP.card_eq, Nat.card_zpowers, hd_ord] at hcard_eq
  omega

omit [Finite G] in
private theorem l34SuzOddPair_closure_data
    {E₁ : Subgroup G} {a a' : G}
    (_hE1_ea : Open.IsElemAbelian 2 E₁)
    (hcomm_E1_a : ∀ x ∈ E₁, x * a = a * x)
    (hcomm_E1_a' : ∀ x ∈ E₁, x * a' = a' * x)
    (ha2 : a * a = 1)
    (ha'2 : a' * a' = 1)
    (haa' : a * a' = a' * a) :
    Subgroup.closure ({a, a'} : Set G) = zpowers a ⊔ zpowers a' ∧
    Open.IsElemAbelian 2 (Subgroup.closure ({a, a'} : Set G)) ∧
    E₁ ≤ Subgroup.centralizer (Subgroup.closure ({a, a'} : Set G)) := by
  have hpair_eq : Subgroup.closure ({a, a'} : Set G) = zpowers a ⊔ zpowers a' := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_insert_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a')
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
  have hpair_ea : Open.IsElemAbelian 2 (Subgroup.closure ({a, a'} : Set G)) := by
    rw [hpair_eq]
    refine Open.IsElemAbelian.sup_of_commute
      (Open.isElemAbelian_zpowers (by rw [pow_two]; exact ha2))
      (Open.isElemAbelian_zpowers (by rw [pow_two]; exact ha'2)) ?_
    intro x hx y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow haa' m n).eq
  have hE1_cent_closure : E₁ ≤ Subgroup.centralizer (Subgroup.closure ({a, a'} : Set G)) := by
    rw [Subgroup.centralizer_closure]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_insert_iff] at hy
    rcases hy with rfl | hy
    · exact (hcomm_E1_a x hx).symm
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (hcomm_E1_a' x hx).symm
  exact ⟨hpair_eq, hpair_ea, hE1_cent_closure⟩

omit [Finite G] in
private theorem l34SuzOddPair_closure_pair
    {E₁ : Subgroup G} {a a' : G}
    (hE1_ea : Open.IsElemAbelian 2 E₁)
    (hcomm_E1_a : ∀ x ∈ E₁, x * a = a * x)
    (hcomm_E1_a' : ∀ x ∈ E₁, x * a' = a' * x)
    (ha2 : a * a = 1)
    (ha'2 : a' * a' = 1)
    (haa' : a * a' = a' * a) :
    Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.closure ({a, a'} : Set G)) ∧
    E₁ ⊔ Subgroup.zpowers a' ≤ E₁ ⊔ Subgroup.closure ({a, a'} : Set G) ∧
    E₁ ⊔ Subgroup.zpowers (a * a') ≤ E₁ ⊔ Subgroup.closure ({a, a'} : Set G) ∧
    (∀ x ∈ E₁ ⊔ Subgroup.zpowers a',
     ∀ y ∈ E₁ ⊔ Subgroup.zpowers (a * a'), x * y = y * x) := by
  obtain ⟨hpair_eq, hpair_ea, hE1_cent_closure⟩ :=
    l34SuzOddPair_closure_data hE1_ea hcomm_E1_a hcomm_E1_a' ha2 ha'2 haa'
  have hM_ea : Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.closure ({a, a'} : Set G)) :=
    Open.IsElemAbelian.sup_of_commute hE1_ea hpair_ea fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (hE1_cent_closure hx) y hy).symm
  have hF_le_M : E₁ ⊔ Subgroup.zpowers a' ≤ E₁ ⊔ Subgroup.closure ({a, a'} : Set G) := by
    refine sup_le le_sup_left ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hJ_le_M : E₁ ⊔ Subgroup.zpowers (a * a') ≤ E₁ ⊔ Subgroup.closure ({a, a'} : Set G) := by
    refine sup_le le_sup_left ?_
    rw [Subgroup.zpowers_le]
    have haa'_mem : a * a' ∈ Subgroup.closure ({a, a'} : Set G) := by
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    exact Subgroup.mem_sup_right haa'_mem
  have hcomm_FJ : ∀ x ∈ E₁ ⊔ Subgroup.zpowers a',
      ∀ y ∈ E₁ ⊔ Subgroup.zpowers (a * a'), x * y = y * x :=
    fun x hx y hy => Open.IsElemAbelian.comm hM_ea (hF_le_M hx) (hJ_le_M hy)
  exact ⟨hM_ea, hF_le_M, hJ_le_M, hcomm_FJ⟩

private theorem l34SuzOddPair_wGroup_eq_bot
    {E₁ : Subgroup G} {a a' : G}
    (hW : ∀ F : Subgroup G, F ≤ Subgroup.centralizer ({t} : Set G) → Open.IsElemAbelian 2 F →
      8 ≤ Nat.card F → wGroup F = ⊥)
    (hS : L34SuzOddSetting A t)
    (_hE1_ea : Open.IsElemAbelian 2 E₁)
    (hF_ea : Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.zpowers a'))
    (hJ_ea : Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.zpowers (a * a')))
    (hF_card : Nat.card ↥(E₁ ⊔ Subgroup.zpowers a') = 8)
    (hJ_card : Nat.card ↥(E₁ ⊔ Subgroup.zpowers (a * a')) = 8)
    (hJ_le : E₁ ⊔ Subgroup.zpowers (a * a') ≤ Subgroup.centralizer ({t} : Set G))
    (hcomm_FJ : ∀ x ∈ E₁ ⊔ Subgroup.zpowers a',
      ∀ y ∈ E₁ ⊔ Subgroup.zpowers (a * a'), x * y = y * x) :
    wGroup (E₁ ⊔ Subgroup.zpowers (a * a')) = ⊥ ∧
    wGroup (E₁ ⊔ Subgroup.zpowers a') = ⊥ := by
  have hWJ : wGroup (E₁ ⊔ Subgroup.zpowers (a * a')) = ⊥ := by
    apply hW _ hJ_le hJ_ea
    rw [hJ_card]
  have hB : GWTwoBalanced G := by
    have hLB : LocallyTwoBalanced G := by
      have h := hS.base
      exact h.2.2.2.2.2.1
    exact gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hLB
  have hF_rank : IsAbelianTwoOfRank 3 (E₁ ⊔ Subgroup.zpowers a') := by
    have hF_two : IsElemTwo (E₁ ⊔ Subgroup.zpowers a') :=
      ⟨fun x hx y hy => Open.IsElemAbelian.comm hF_ea hx hy,
       fun x hx => Open.IsElemAbelian.mul_self_eq_one hF_ea hx⟩
    exact IsElemTwo.isAbelianTwoOfRank hF_two (by rw [hF_card])
  have hJ_rank : IsAbelianTwoOfRank 3 (E₁ ⊔ Subgroup.zpowers (a * a')) := by
    have hJ_two : IsElemTwo (E₁ ⊔ Subgroup.zpowers (a * a')) :=
      ⟨fun x hx y hy => Open.IsElemAbelian.comm hJ_ea hx hy,
       fun x hx => Open.IsElemAbelian.mul_self_eq_one hJ_ea hx⟩
    exact IsElemTwo.isAbelianTwoOfRank hJ_two (by rw [hJ_card])
  have hWF : wGroup (E₁ ⊔ Subgroup.zpowers a') = ⊥ := by
    rw [wGroup_eq_of_commute hB hF_rank hJ_rank hcomm_FJ]
    exact hWJ
  exact ⟨hWJ, hWF⟩

private theorem l34SuzOddPair_F_action_on_P
    {u : G} {P E₁ : Subgroup G} {a a' : G}
    (hP : L34SuzOddPairData t u V P E₁ a)
    (htX : t ∈ Subgroup.centralizer ({u} : Set G))
    (ha' : a' = t * a * t⁻¹) :
    (E₁ ⊔ Subgroup.zpowers a') ≤ normalizer (P : Set G) ∧
    (∀ e ∈ E₁ ⊔ Subgroup.zpowers a', ∀ l ∈ P,
      e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 P).map P.subtype) := by
  let X : Subgroup G := Subgroup.centralizer ({u} : Set G)
  let F : Subgroup G := E₁ ⊔ Subgroup.zpowers a'
  let P' : Subgroup G := P.map (MulAut.conj t).toMonoidHom
  have hP'_le_X : P' ≤ X := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    exact X.mul_mem (X.mul_mem htX (hP.le_centralizer hp)) (X.inv_mem htX)
  have htN : t ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer htX
  have hP'_comp : IsPComponent 2 (P'.subgroupOf X) :=
    (GS82PumpInputs.P10.isPComponent_cj_subgroupOf (X := X) (K := P) hP.le_centralizer
      hP.isPComponent (g := t) htN).2
  have hne : P ≠ P' := by
    intro h
    exact hP.map_ne h.symm
  have hP'_ker : P' ≤ UnbalancedLayer.coreActionKernel P :=
    CFSG.ComponentClassification.GSThmB.B5a.le_coreActionKernel_of_ne hP.le_centralizer
      hP'_le_X hP.isPComponent hP'_comp hne
  have ha'_mem_P' : a' ∈ P' := by
    rw [ha']
    show (MulAut.conj t) a ∈ P'
    exact Subgroup.mem_map_of_mem _ hP.mem
  have hF_le_N : F ≤ normalizer (P : Set G) := by
    change E₁ ⊔ zpowers a' ≤ normalizer (P : Set G)
    refine sup_le hP.le_normalizer ?_
    rw [Subgroup.zpowers_le]
    exact (UnbalancedLayer.mem_coreActionKernel.mp (hP'_ker ha'_mem_P')).1
  have hE1_ker : E₁ ≤ UnbalancedLayer.coreActionKernel P := by
    intro e he
    exact mem_coreActionKernel_of_commutator_mem (hP.le_normalizer he)
      (fun l hl => hP.commutator_mem e he l hl)
  have hF_le_ker : F ≤ UnbalancedLayer.coreActionKernel P := by
    change E₁ ⊔ zpowers a' ≤ UnbalancedLayer.coreActionKernel P
    exact sup_le hE1_ker (Subgroup.zpowers_le.mpr (hP'_ker ha'_mem_P'))
  have hF_comm : ∀ e ∈ F, ∀ l ∈ P, e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 P).map P.subtype :=
    fun e he l hl => GrS5.conj_mem_oddIn_of_mem_coreActionKernel (hF_le_ker he) l hl
  exact ⟨hF_le_N, hF_comm⟩

private theorem l34SuzOddPair_J_data
    {u : G} {P E₁ : Subgroup G} {a a' : G}
    (hP : L34SuzOddPairData t u V P E₁ a)
    (hE1_ea : Open.IsElemAbelian 2 E₁)
    (hE1t : E₁ ≤ Subgroup.centralizer ({t} : Set G))
    (hcomm_E1_a : ∀ x ∈ E₁, x * a = a * x)
    (hcomm_E1_a' : ∀ x ∈ E₁, x * a' = a' * x)
    (ht2 : t * t = 1) (htinv : t⁻¹ = t)
    (_ha2 : a * a = 1) (_ha'2 : a' * a' = 1)
    (haa' : a * a' = a' * a)
    (hd2 : (a * a') * (a * a') = 1)
    (_ha'_notin : a' ∉ E₁)
    (ha' : a' = t * a * t⁻¹) :
    (∀ z ∈ E₁, z * (a * a') = (a * a') * z) ∧
    a * a' ∉ E₁ ∧
    Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.zpowers (a * a')) ∧
    (E₁ ⊔ Subgroup.zpowers (a * a')) ≤ Subgroup.centralizer ({t} : Set G) := by
  have hcomm_E1_aa' : ∀ z ∈ E₁, z * (a * a') = (a * a') * z := by
    intro z hz
    calc z * (a * a') = (z * a) * a' := by group
      _ = (a * z) * a' := by rw [hcomm_E1_a z hz]
      _ = a * (z * a') := by group
      _ = a * (a' * z) := by rw [hcomm_E1_a' z hz]
      _ = (a * a') * z := by group
  have haa'_notin : a * a' ∉ E₁ := l34SuzOddPair_aa'_notin hP haa' ha'
  have hJ_ea : Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.zpowers (a * a')) := by
    refine Open.IsElemAbelian.sup_of_commute hE1_ea
      (Open.isElemAbelian_zpowers (by rw [pow_two]; exact hd2)) ?_
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp
      ((Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_iff.mpr (fun z hz => hcomm_E1_aa' z hz))) hy) x hx
  have hJ_le : E₁ ⊔ Subgroup.zpowers (a * a') ≤ Subgroup.centralizer ({t} : Set G) := by
    refine sup_le hE1t ?_
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : t * (a * a') * t⁻¹ = a * a' := by
      calc t * (a * a') * t⁻¹ = (t * a * t⁻¹) * (t * a' * t⁻¹) := by group
        _ = a' * a := by
          have h1 : t * a * t⁻¹ = a' := by rw [← ha']
          have h2 : t * a' * t⁻¹ = a := by
            rw [ha']
            rw [htinv]
            calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
              _ = 1 * a * 1 := by rw [ht2]
              _ = a := by rw [one_mul, mul_one]
          rw [h1, h2]
        _ = a * a' := haa'.symm
    rw [htinv] at h
    have hcomm_t : (a * a') * t = t * (a * a') := by
      calc (a * a') * t = (t * (a * a') * t) * t := by rw [h]
        _ = t * (a * a') := by rw [mul_assoc, ht2, mul_one]
    exact hcomm_t
  exact ⟨hcomm_E1_aa', haa'_notin, hJ_ea, hJ_le⟩

private theorem l34SuzOddPair_step0
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) {P E₁ : Subgroup G} {a : G}
    (hP : L34SuzOddPairData t u V P E₁ a) :
    t * t = 1 ∧ a * a = 1 ∧ t⁻¹ = t ∧
    (t * a * t⁻¹) * (t * a * t⁻¹) = 1 ∧
    a * (t * a * t⁻¹) = (t * a * t⁻¹) * a ∧
    (a * (t * a * t⁻¹)) * (a * (t * a * t⁻¹)) = 1 ∧
    t ∈ Subgroup.centralizer ({u} : Set G) ∧
    E₁ ⊔ Subgroup.zpowers (t * a * t⁻¹) ≤ Subgroup.centralizer ({u} : Set G) := by
  have ht2 : t * t = 1 := by rw [← sq, ← hS.orderOf_t, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := hP.mul_self
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ha'2 : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 := by
    simp [ha2]
  have haa' : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a := hP.commute_conj
  have ha'a : (t * a * t⁻¹) * a = a * (t * a * t⁻¹) := haa'.symm
  have hd2 : (a * (t * a * t⁻¹)) * (a * (t * a * t⁻¹)) = 1 := by
    calc (a * (t * a * t⁻¹)) * (a * (t * a * t⁻¹))
        = a * ((t * a * t⁻¹) * a) * (t * a * t⁻¹) := by group
      _ = a * (a * (t * a * t⁻¹)) * (t * a * t⁻¹) := by rw [ha'a]
      _ = (a * a) * ((t * a * t⁻¹) * (t * a * t⁻¹)) := by group
      _ = 1 := by rw [ha2, ha'2, one_mul]
  have hVX : V ≤ Subgroup.centralizer ({u} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.commute_of_sq_eq_one
      (by rw [pow_two]; exact hD.mul_self v hv)
      (by rw [pow_two]; exact hD.mul_self u hu)
      (by rw [pow_two]; exact hD.mul_self (v * u) (V.mul_mem hv hu))
  have htX : t ∈ Subgroup.centralizer ({u} : Set G) := mem_centralizer_of_l34SuzOdd hS hD hu
  have hVtX : V ⊔ zpowers t ≤ Subgroup.centralizer ({u} : Set G) :=
    sup_le hVX (Subgroup.zpowers_le.mpr htX)
  have hE1X : E₁ ≤ Subgroup.centralizer ({u} : Set G) := hP.le_sup.trans hVtX
  have haX : a ∈ Subgroup.centralizer ({u} : Set G) := hP.le_centralizer hP.mem
  have ha'X : t * a * t⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
    exact (Subgroup.centralizer ({u} : Set G)).mul_mem
      ((Subgroup.centralizer ({u} : Set G)).mul_mem htX haX)
      ((Subgroup.centralizer ({u} : Set G)).inv_mem htX)
  have hFX : E₁ ⊔ Subgroup.zpowers (t * a * t⁻¹) ≤ Subgroup.centralizer ({u} : Set G) :=
    sup_le hE1X (Subgroup.zpowers_le.mpr ha'X)
  exact ⟨ht2, ha2, htinv, ha'2, haa', hd2, htX, hFX⟩

omit [Finite G] in
private theorem l34SuzOddPair_core_center_le
    {u : G} {P E₁ : Subgroup G} {a : G}
    (hP : L34SuzOddPairData t u V P E₁ a)
    (hOcenG : ∀ x ∈ (pPrimeCore 2 P).map P.subtype, ∀ l ∈ P, x * l = l * x) :
    pPrimeCore 2 (P.subgroupOf (Subgroup.centralizer ({u} : Set G))) ≤
      Subgroup.center (P.subgroupOf (Subgroup.centralizer ({u} : Set G))) := by
  let X : Subgroup G := Subgroup.centralizer ({u} : Set G)
  have hcore_center : pPrimeCore 2 (P.subgroupOf X) ≤ Subgroup.center (P.subgroupOf X) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    apply Subtype.ext
    have hzG : (((z : ↥(P.subgroupOf X)) : ↥X) : G) ∈ (pPrimeCore 2 P).map P.subtype := by
      have hpc := CFSG.pPrimeCore_map_subgroupOf (p := 2) P X hP.le_centralizer
      have hz1 : ((z : ↥(P.subgroupOf X)) : ↥X) ∈
          (pPrimeCore 2 (P.subgroupOf X)).map (P.subgroupOf X).subtype :=
        Subgroup.mem_map_of_mem _ hz
      rw [← hpc]
      exact Subgroup.mem_map_of_mem X.subtype hz1
    have hwG : (((w : ↥(P.subgroupOf X)) : ↥X) : G) ∈ P :=
      Subgroup.mem_subgroupOf.mp w.2
    exact (hOcenG _ hzG _ hwG).symm
  exact hcore_center

section Certified


private theorem l34SuzOddPair_OP_le_ZP
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput)
    (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    {P E₁ : Subgroup G} {a a' : G}
    (hP : L34SuzOddPairData t u V P E₁ a)
    (hFX : E₁ ⊔ Subgroup.zpowers a' ≤ Subgroup.centralizer ({u} : Set G))
    (hF_ea : Open.IsElemAbelian 2 (E₁ ⊔ Subgroup.zpowers a'))
    (hF_card : Nat.card ↥(E₁ ⊔ Subgroup.zpowers a') = 8)
    (hF_le_N : E₁ ⊔ Subgroup.zpowers a' ≤ normalizer (P : Set G))
    (hF_comm : ∀ e ∈ E₁ ⊔ Subgroup.zpowers a', ∀ l ∈ P,
      e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 P).map P.subtype)
    (hWF : wGroup (E₁ ⊔ Subgroup.zpowers a') = ⊥) :
    ∀ x ∈ (pPrimeCore 2 P).map P.subtype, ∀ l ∈ P, x * l = l * x := by
  have hu2 : orderOf u = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨by rw [pow_two]; exact hD.mul_self u hu, hu1⟩
  have hbal : ∀ e ∈ (E₁ ⊔ Subgroup.zpowers a'), e ≠ 1 →
      ⁅(pPrimeCore 2 P).map P.subtype ⊓ Subgroup.centralizer ({e} : Set G),
        (pLayer ↥(P ⊓ Subgroup.centralizer ({e} : Set G)) 2).map
          (P ⊓ Subgroup.centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (Subgroup.centralizer ({e} : Set G))).map
        (Subgroup.centralizer ({e} : Set G)).subtype := by
    intro e he he1
    obtain ⟨hsimple, hnonab, hKproper, -⟩ := hS.base
    have hnotmem : e ∉ Subgroup.center G :=
      CFSG.ComponentClassification.GrSLit.GrS5.not_mem_center_of_ne_one hnonab he1
    have htop : Subgroup.centralizer ({e} : Set G) ≠ ⊤ :=
      CFSG.ComponentClassification.GrSLit.GrS5.centralizer_ne_top_of_not_mem_center hnotmem
    exact CFSG.ComponentClassification.GrSLit.GrS5.commutator_oddCore_pLayer_le
      hSch hU hheld hKproper hu2 hP.le_centralizer hP.isPComponent
      (Subgroup.mem_centralizer_singleton_iff.mp (hFX he)).symm htop
  exact oddCore_le_center_of_wGroup_eq_bot hP.le_centralizer hP.isPComponent hFX
    (fun x hx y hy => Open.IsElemAbelian.comm hF_ea hx hy)
    (fun x hx => by rw [← pow_two]; exact hF_ea.2 x hx)
    (by rw [hF_card]; norm_num) hF_le_N hF_comm hWF hbal
    (Or.inr (by rw [hF_card]))

theorem isComponent_of_l34SuzOddPairData
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hW : ∀ F : Subgroup G, F ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 F →
      8 ≤ Nat.card F → wGroup F = ⊥)
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    {P E₁ : Subgroup G} {a : G} (hP : L34SuzOddPairData t u V P E₁ a) :
    IsComponent (P.subgroupOf (centralizer ({u} : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := centralizer ({u} : Set G)
  let a' : G := t * a * t⁻¹
  obtain ⟨ht2, ha2, htinv, ha'2, haa', hd2, htX, hFX⟩ := l34SuzOddPair_step0 hS hD hu hP
  obtain ⟨hE1_ea, hE1t⟩ := l34SuzOddPair_E1_isElemAbelian hS hD hP
  obtain ⟨hF_ea, hcomm_E1_a, hcomm_E1_a'⟩ := l34SuzOddPair_F_elemAbelian hS hD hP
  have ha'_notin : a' ∉ E₁ := by
    change t * a * t⁻¹ ∉ E₁
    exact l34SuzOddPair_a'_notin hP
  obtain ⟨_, hF_card⟩ :=
    l34SuzOddPair_F_card (a' := a') hP rfl hcomm_E1_a' ha'_notin
  obtain ⟨hcomm_E1_aa', haa'_notin, hJ_ea, hJ_le⟩ :=
    l34SuzOddPair_J_data hP hE1_ea hE1t hcomm_E1_a hcomm_E1_a' ht2 htinv ha2 ha'2
      haa' hd2 ha'_notin rfl
  have hJ_card : Nat.card ↥(E₁ ⊔ Subgroup.zpowers (a * a')) = 8 :=
    l34SuzOddPair_J_card hP rfl hcomm_E1_aa' haa'_notin hd2
  obtain ⟨_, _, _, hcomm_FJ⟩ :=
    l34SuzOddPair_closure_pair hE1_ea hcomm_E1_a hcomm_E1_a' ha2 ha'2 haa'
  obtain ⟨_, hWF⟩ :=
    l34SuzOddPair_wGroup_eq_bot hW hS hE1_ea hF_ea hJ_ea hF_card hJ_card hJ_le hcomm_FJ
  obtain ⟨hF_le_N, hF_comm⟩ := l34SuzOddPair_F_action_on_P hP htX rfl
  have hOcenG : ∀ x ∈ (pPrimeCore 2 P).map P.subtype, ∀ l ∈ P, x * l = l * x :=
    l34SuzOddPair_OP_le_ZP hSch hU hheld hS hD hu hu1 hP hFX hF_ea hF_card hF_le_N hF_comm hWF
  have hcore_center := l34SuzOddPair_core_center_le hP hOcenG
  exact ⟨(CatalogueBPrimeJoin.quasisimple_iff_core_central 2 (P.subgroupOf X)
    hP.isPComponent).mpr hcore_center, hP.isPComponent.choose_spec.2.1⟩

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S
