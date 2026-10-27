module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Homo
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4CentCard
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIsoS0

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix AltStdCycTwo
open scoped Pointwise

section Perm

open Equiv

theorem perm_pow_eight {m : ℕ} (hm : m ≤ 15) {σ : Perm (Fin m)} {j : ℕ} (hj : σ ^ 2 ^ j = 1) :
    σ ^ 8 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro ℓ hℓ
  have h1 : ℓ ∣ 2 ^ j := (Perm.dvd_of_mem_cycleType hℓ).trans (orderOf_dvd_of_pow_eq_one hj)
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : 2 ^ i ≤ m := (Perm.le_card_support_of_mem_cycleType hℓ).trans
    ((Finset.card_le_univ _).trans (by simp))
  have hi3 : i ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    omega
  exact (pow_dvd_pow 2 hi3).trans (by norm_num)

theorem perm_pow_four_of_sign_of_le {m : ℕ} (hm : m ≤ 9) {σ : Perm (Fin m)}
    (hσ : Perm.sign σ = 1) {j : ℕ} (hj : σ ^ 2 ^ j = 1) : σ ^ 4 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro ℓ hℓ
  have h1 : ℓ ∣ 2 ^ j := (Perm.dvd_of_mem_cycleType hℓ).trans (orderOf_dvd_of_pow_eq_one hj)
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : 2 ^ i ≤ 9 := (Perm.le_card_support_of_mem_cycleType hℓ).trans
    ((Finset.card_le_univ _).trans (by simpa using hm))
  have hi3 : i ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    omega
  rcases Nat.lt_or_ge i 3 with h | h
  · exact (pow_dvd_pow 2 (by omega : i ≤ 2)).trans (by norm_num)
  · exfalso
    obtain rfl : i = 3 := le_antisymm hi3 h
    have hsum : σ.cycleType.sum ≤ 9 := (Perm.sum_cycleType_le σ).trans (by simpa using hm)
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hℓ
    have ht0 : t = 0 := by
      by_contra hne
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
      have ha2 : 2 ≤ a :=
        Perm.two_le_of_mem_cycleType (by rw [ht]; exact Multiset.mem_cons_of_mem ha)
      have h3 : 2 ^ 3 + a ≤ σ.cycleType.sum := by
        rw [ht, Multiset.sum_cons]
        exact Nat.add_le_add_left (Multiset.le_sum_of_mem ha) _
      omega
    have hsign := Perm.sign_of_cycleType σ
    rw [ht, ht0, hσ] at hsign
    revert hsign
    decide

theorem perm_pow_four_of_sign {σ : Perm (Fin 9)} (hσ : Perm.sign σ = 1) {j : ℕ}
    (hj : σ ^ 2 ^ j = 1) : σ ^ 4 = 1 :=
  perm_pow_four_of_sign_of_le le_rfl hσ hj

end Perm

section Lfree

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

@[expose] def Yodd (L : Subgroup G) (z : G) : Subgroup G :=
  AltStdBal.oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G))

theorem Lfree_eq (L : Subgroup G) (z : G) : Lfree L z = L ⊔ Yodd L z := rfl

theorem zpowers_eq (c : Config G L Q n θ z) : zpowers z = Q :=
  Subgroup.eq_of_le_of_card_ge (zpowers_le.2 c.ot.cyc.mem)
    (by rw [c.ot.card, Nat.card_zpowers, c.ot.cyc.order])

theorem z_mul_self (c : Config G L Q n θ z) : z * z = 1 := c.ot.cyc.mul_self

theorem z_inv (c : Config G L Q n θ z) : z⁻¹ = z := inv_eq_of_mul_eq_one_right (z_mul_self c)

theorem z_ne_one (c : Config G L Q n θ z) : z ≠ 1 := fun h => by
  have := c.ot.cyc.order
  rw [h, orderOf_one] at this
  omega

theorem z_mem_centralizer_L (c : Config G L Q n θ z) : z ∈ centralizer (L : Set G) :=
  c.ot.cyc.le c.ot.cyc.mem

theorem L_le_centralizer_z (c : Config G L Q n θ z) : L ≤ centralizer ({z} : Set G) :=
  le_cent_single c.ot.std c.ot.cyc

theorem eq_one_of_mem_L_of_mem_cent (c : Config G L Q n θ z) {x : G} (hxL : x ∈ L)
    (hxK : x ∈ centralizer (L : Set G)) : x = 1 :=
  AltStdBal.eq_one_of_mem_of_mem_centralizer θ (by have := c.hn8; omega) hxL hxK

theorem Yodd_spec (c : Config G L Q n θ z) :
    Yodd L z ≤ centralizer (L : Set G) ⊓ centralizer ({z} : Set G) ∧
      Odd (Nat.card (Yodd L z)) ∧ Yodd L z ⊓ zpowers z = ⊥ ∧
      ∀ m ∈ centralizer (L : Set G) ⊓ centralizer ({z} : Set G),
        ∃ y ∈ Yodd L z, ∃ q ∈ zpowers z, m = y * q := by
  set M := centralizer (L : Set G) ⊓ centralizer ({z} : Set G) with hM
  have hQz := zpowers_eq c
  have hQM : Q ≤ M := by
    rw [← hQz, zpowers_le]
    exact ⟨z_mem_centralizer_L c, mem_centralizer_singleton_iff.2 rfl⟩
  have hMK : M ≤ centralizer (L : Set G) := inf_le_left
  have hi : ¬ 2 ∣ Q.relIndex M := by
    intro h2
    apply c.ot.cyc.odd_index
    exact h2.trans (Dvd.intro _ (relIndex_mul_relIndex Q M (centralizer (L : Set G)) hQM hMK))
  obtain ⟨h1, -, h3, h4, h5⟩ := AltStdBal.oddPart_spec hQM c.ot.cyc.pgroup hi c.ot.cyc.cyclic
  rw [← hQz] at h4 h5
  exact ⟨h1, h3, h4, h5⟩

theorem Yodd_le_cent_L (c : Config G L Q n θ z) : Yodd L z ≤ centralizer (L : Set G) :=
  (Yodd_spec c).1.trans inf_le_left

theorem Yodd_le_cent_z (c : Config G L Q n θ z) : Yodd L z ≤ centralizer ({z} : Set G) :=
  (Yodd_spec c).1.trans inf_le_right

theorem odd_orderOf_of_mem_Yodd (c : Config G L Q n θ z) {y : G} (hy : y ∈ Yodd L z) :
    Odd (orderOf y) := by
  have h1 : orderOf y ∣ Nat.card (Yodd L z) := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : Yodd L z)
    rwa [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat (Yodd_spec c).2.1 h1

theorem Lfree_le_cent_z (c : Config G L Q n θ z) : Lfree L z ≤ centralizer ({z} : Set G) :=
  sup_le (L_le_centralizer_z c) (Yodd_le_cent_z c)

theorem Lfree_le_sup (c : Config G L Q n θ z) : Lfree L z ≤ L ⊔ centralizer (L : Set G) :=
  sup_le le_sup_left ((Yodd_le_cent_L c).trans le_sup_right)

theorem mem_Lfree_iff (c : Config G L Q n θ z) {g : G} :
    g ∈ Lfree L z ↔ ∃ l ∈ L, ∃ y ∈ Yodd L z, g = l * y := by
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left L (Yodd L z)
    ((Yodd_le_cent_L c).trans (Subgroup.centralizer_le_normalizer _))
  constructor
  · intro hg
    have hg' : g ∈ (L : Set G) * (Yodd L z : Set G) := by
      rw [← hm]
      exact hg
    obtain ⟨l, hl, y, hy, rfl⟩ := Set.mem_mul.1 hg'
    exact ⟨l, hl, y, hy, rfl⟩
  · rintro ⟨l, hl, y, hy, rfl⟩
    exact mul_mem (mem_sup_left hl) (mem_sup_right hy)

theorem mem_L_of_two_pow (c : Config G L Q n θ z) {g : G} (hg : g ∈ Lfree L z) {j : ℕ}
    (hj : g ^ 2 ^ j = 1) : g ∈ L := by
  obtain ⟨l, hl, y, hy, rfl⟩ := (mem_Lfree_iff c).1 hg
  have hly : Commute l y := mem_centralizer_iff.1 (Yodd_le_cent_L c hy) l hl
  rw [hly.mul_pow] at hj
  have hy1 : y ^ 2 ^ j = 1 := by
    have h1 : y ^ 2 ^ j = (l ^ 2 ^ j)⁻¹ := eq_inv_of_mul_eq_one_right hj
    refine eq_one_of_mem_L_of_mem_cent c ?_ (pow_mem (Yodd_le_cent_L c hy) _)
    rw [h1]
    exact inv_mem (pow_mem hl _)
  have hy' : y = 1 := by
    have h2 : orderOf y ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hy1
    have h3 := odd_orderOf_of_mem_Yodd c hy
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases i with _ | i
    · rwa [pow_zero, orderOf_eq_one_iff] at hi
    · rw [hi, pow_succ] at h3
      exact absurd h3 (by simp [Nat.not_odd_iff_even])
  rw [hy', mul_one]
  exact hl

theorem z_not_mem_Lfree (c : Config G L Q n θ z) : z ∉ Lfree L z := fun hz =>
  N0.z_not_mem_L c (mem_L_of_two_pow c hz (j := 1) (by rw [pow_one, sq, z_mul_self c]))

theorem mem_Lfree_of_odd_pow (c : Config G L Q n θ z) {g : G}
    (hgC : g ∈ centralizer ({z} : Set G)) (hgL : g ∈ L ⊔ centralizer (L : Set G)) {m : ℕ}
    (hm : Odd m) (hgm : g ^ m ∈ L) : g ∈ Lfree L z := by
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G))
    (Subgroup.centralizer_le_normalizer _)
  have hg' : g ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hmul]
    exact hgL
  obtain ⟨l, hl, w, hw, rfl⟩ := Set.mem_mul.1 hg'
  have hwC : w ∈ centralizer ({z} : Set G) := by
    have : w = l⁻¹ * (l * w) := by group
    rw [this]
    exact mul_mem (inv_mem (L_le_centralizer_z c hl)) hgC
  obtain ⟨y, hy, q, hq, rfl⟩ := (Yodd_spec c).2.2.2 w ⟨hw, hwC⟩
  have hlw : Commute l (y * q) := mem_centralizer_iff.1 hw l hl
  have hyq : Commute y q := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 (Yodd_le_cent_z c hy)) j)
  rw [hlw.mul_pow] at hgm
  have hw1 : (y * q) ^ m = 1 := by
    refine eq_one_of_mem_L_of_mem_cent c ?_ (pow_mem hw _)
    have : (y * q) ^ m = (l ^ m)⁻¹ * (l ^ m * (y * q) ^ m) := by group
    rw [this]
    exact mul_mem (inv_mem (pow_mem hl _)) hgm
  rw [hyq.mul_pow] at hw1
  have hq1 : q ^ m = 1 := by
    have h1 : q ^ m = (y ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hw1
    have h2 : q ^ m ∈ Yodd L z ⊓ zpowers z := by
      refine Subgroup.mem_inf.2 ⟨?_, pow_mem hq _⟩
      rw [h1]
      exact inv_mem (pow_mem hy _)
    rw [(Yodd_spec c).2.2.1] at h2
    exact h2
  have hq' : q = 1 := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    rcases zpow_eq_one_or_eq (z_mul_self c) j with h | h
    · exact h
    · exfalso
      rw [h] at hq1
      obtain ⟨r, rfl⟩ := hm
      rw [pow_succ, pow_mul, sq, z_mul_self c, one_pow, one_mul] at hq1
      exact z_ne_one c hq1
  rw [hq', mul_one]
  exact mul_mem (mem_sup_left hl) (mem_sup_right hy)

theorem mem_Lfree_of_odd (c : Config G L Q n θ z) {g : G}
    (hgC : g ∈ centralizer ({z} : Set G)) (hgL : g ∈ L ⊔ centralizer (L : Set G))
    (hg : Odd (orderOf g)) : g ∈ Lfree L z :=
  mem_Lfree_of_odd_pow c hgC hgL hg (by rw [pow_orderOf_eq_one]; exact one_mem L)

theorem mem_Lfree_of_N0 (c : Config G L Q n θ z) {g : G}
    (hg : g ∈ N0 θ c.hn8 z ⊓ centralizer ({z} : Set G)) {m : ℕ} (hm : Odd m) (hgm : g ^ m ∈ L) :
    g ∈ Lfree L z :=
  mem_Lfree_of_odd_pow c hg.2 (N0_inf_centralizer_le_sup c hg) hm hgm

theorem mem_Lfree_of_N0_of_odd (c : Config G L Q n θ z) {g : G}
    (hg : g ∈ N0 θ c.hn8 z ⊓ centralizer ({z} : Set G)) (ho : Odd (orderOf g)) :
    g ∈ Lfree L z :=
  mem_Lfree_of_odd c hg.2 (N0_inf_centralizer_le_sup c hg) ho

end Lfree

section Kap

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (θ : L ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n)

theorem kap_conj_epsV (M : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    ModIso.kap θ hn M * epsV θ hn v * (ModIso.kap θ hn M)⁻¹ =
      epsV θ hn ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
  rw [epsV, ModIso.kap_conj_eps, epsV]
  congr 1
  apply ModIso.bits.injective
  rw [ModIso.bits_linPerm8, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Kap

section PsiE

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (θ : L ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n)

@[expose] noncomputable def iotaE : E θ hn ≃* Multiplicative (Fin 3 → ZMod (2 ^ 1)) :=
  (epsEquiv θ hn).symm

theorem el_iotaE (v : Fin 3 → ZMod 2) : el (iotaE θ hn) v = epsV θ hn v := by
  simp only [el, iotaE, MulEquiv.symm_symm, coe_epsEquiv, toAdd_ofAdd]

theorem liftE_one (v : Fin 3 → ZMod 2) : liftE 1 v = v := by
  funext i
  simp only [liftE, Nat.sub_self, pow_zero, one_mul]
  exact ZMod.natCast_zmod_val (v i)

theorem ecoords_iotaE : ECoords θ hn 1 (E θ hn) (iotaE θ hn) :=
  ⟨le_rfl, le_rfl, fun v => by rw [liftE_one, el_iotaE]⟩

@[expose] noncomputable def psiE : normalizer (E θ hn : Set G) →* GL (Fin 3) (ZMod 2) :=
  (mat (iotaE θ hn)).toHomUnits

theorem coe_psiE (g : normalizer (E θ hn : Set G)) :
    (psiE θ hn g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = mat (iotaE θ hn) g := rfl

theorem psiE_spec (g : normalizer (E θ hn : Set G)) (v : Fin 3 → ZMod 2) :
    (g : G) * epsV θ hn v * (g : G)⁻¹ =
      epsV θ hn ((psiE θ hn g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
  rw [← el_iotaE, mat_spec, coe_psiE]
  rfl

theorem psiE_eq_one_iff (g : normalizer (E θ hn : Set G)) :
    psiE θ hn g = 1 ↔ (g : G) ∈ centralizer (E θ hn : Set G) := by
  rw [← Units.val_inj, coe_psiE, Units.val_one]
  rw [show (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (1 : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ 1)))
    from rfl, mat_eq_one_iff, mem_centralizer_iff]
  constructor
  · intro h e he
    have := h e he
    calc e * g = g * e * (g : G)⁻¹ * g := by rw [this]
      _ = g * e := by group
  · intro h e he
    rw [← h e he, mul_inv_cancel_right]

theorem card_le_of_pgroup {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPE : P ≤ normalizer (E θ hn : Set G)) :
    Nat.card P ≤ 8 * Nat.card (P ⊓ centralizer (E θ hn : Set G) : Subgroup G) := by
  set f := (psiE θ hn).comp (Subgroup.inclusion hPE) with hf
  have hrange : Nat.card f.range ≤ 8 :=
    ModIso.card_le_eight (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hker : f.ker = (centralizer (E θ hn : Set G)).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, psiE_eq_one_iff]
    rfl
  have hker' : Nat.card f.ker = Nat.card (P ⊓ centralizer (E θ hn : Set G) : Subgroup G) := by
    rw [hker, ← inf_subgroupOf_left, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left :
        P ⊓ centralizer (E θ hn : Set G) ≤ P)).toEquiv]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker'] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_right _ hrange

end PsiE

section Expo

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

@[expose] noncomputable def expo (L : Subgroup G) (n : ℕ) (z : G) : ℕ := by
  classical
  exact if IsASmall L n z then 4 else 8

@[expose] noncomputable def cardN (L : Subgroup G) (n : ℕ) (z : G) : ℕ := by
  classical
  exact if IsASmall L n z then 2 ^ 7 else 2 ^ 8

theorem expo_of_ASmall (h : IsASmall L n z) : expo L n z = 4 := by
  simp only [expo, if_pos h]

theorem expo_of_not_ASmall (h : ¬ IsASmall L n z) : expo L n z = 8 := by
  simp only [expo, if_neg h]

theorem expo_of_A9 (h : n = 9 ∧ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    expo L n z = 4 :=
  expo_of_ASmall ⟨Or.inr h.1, h.2⟩

theorem cardN_of_ASmall (h : IsASmall L n z) : cardN L n z = 2 ^ 7 := by
  simp only [cardN, if_pos h]

theorem cardN_of_not_ASmall (h : ¬ IsASmall L n z) : cardN L n z = 2 ^ 8 := by
  simp only [cardN, if_neg h]

theorem cardN_of_A9 (h : n = 9 ∧ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    cardN L n z = 2 ^ 7 :=
  cardN_of_ASmall ⟨Or.inr h.1, h.2⟩

theorem expo_eq_four_or_eight (L : Subgroup G) (n : ℕ) (z : G) :
    expo L n z = 4 ∨ expo L n z = 8 := by
  by_cases h : IsASmall L n z
  · exact Or.inl (expo_of_ASmall h)
  · exact Or.inr (expo_of_not_ASmall h)

theorem expo_dvd_eight (L : Subgroup G) (n : ℕ) (z : G) : expo L n z ∣ 8 := by
  rcases expo_eq_four_or_eight L n z with h | h <;> rw [h] <;> norm_num

theorem pow_four_of_mem_L_of_le (θ : L ≃* alternatingGroup (Fin n)) (hn : n ≤ 9) {l : G}
    (hl : l ∈ L) {j : ℕ} (hj : l ^ 2 ^ j = 1) : l ^ 4 = 1 := by
  have h1 : (⟨l, hl⟩ : L) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj)
  have h2 : ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ^ 2 ^ j = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
  have h3 := perm_pow_four_of_sign_of_le hn (Equiv.Perm.mem_alternatingGroup.1 (θ ⟨l, hl⟩).2) h2
  have h4 : θ (⟨l, hl⟩ ^ 4) = 1 := by
    rw [map_pow]
    exact Subtype.ext (by rw [Subgroup.coe_pow, h3, Subgroup.coe_one])
  have h5 : (⟨l, hl⟩ : L) ^ 4 = 1 := by
    rw [← map_one θ] at h4
    exact θ.injective h4
  simpa using congrArg Subtype.val h5

theorem pow_four_of_mem_L (θ : L ≃* alternatingGroup (Fin 9)) {l : G} (hl : l ∈ L) {j : ℕ}
    (hj : l ^ 2 ^ j = 1) : l ^ 4 = 1 :=
  pow_four_of_mem_L_of_le θ le_rfl hl hj

theorem pow_eight_of_mem_L (θ : L ≃* alternatingGroup (Fin n)) (hn : n ≤ 15) {l : G} (hl : l ∈ L)
    {j : ℕ} (hj : l ^ 2 ^ j = 1) : l ^ 8 = 1 := by
  have h1 : (⟨l, hl⟩ : L) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj)
  have h2 : ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ^ 2 ^ j = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
  have h3 := perm_pow_eight hn h2
  have h4 : θ (⟨l, hl⟩ ^ 8) = 1 := by
    rw [map_pow]
    exact Subtype.ext (by rw [Subgroup.coe_pow, h3, Subgroup.coe_one])
  have h5 : (⟨l, hl⟩ : L) ^ 8 = 1 := by
    rw [← map_one θ] at h4
    exact θ.injective h4
  simpa using congrArg Subtype.val h5

private theorem exists_two_pow_mul (c : Config G L Q n θ z) {g : G}
    (hgC : g ∈ centralizer ({z} : Set G)) (hgL : g ∈ L ⊔ centralizer (L : Set G)) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) :
    ∃ l ∈ L, ∃ q ∈ zpowers z, g = l * q ∧ Commute l q ∧ l ^ 2 ^ (k + 1) = 1 := by
  obtain ⟨l, hl, hlq'⟩ := exists_eq_of_two_pow c.ot.std θ c.hn8 c.ot.cyc c.ot.card hgC hgL hk
  obtain ⟨q, hq, hlq⟩ : ∃ q ∈ zpowers z, l * q = g := by
    rcases hlq' with h | h
    · exact ⟨1, one_mem _, by rw [mul_one, h]⟩
    · exact ⟨z, mem_zpowers z, h.symm⟩
  have hcomm : Commute l q :=
    mem_centralizer_iff.1 ((zpowers_le.2 (z_mem_centralizer_L c)) hq) l hl
  have hq2 : q ^ 2 = 1 := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    rcases zpow_eq_one_or_eq (z_mul_self c) j with h | h
    · rw [h, one_pow]
    · rw [h, sq, z_mul_self c]
  refine ⟨l, hl, q, hq, hlq.symm, hcomm, ?_⟩
  have h1 : (l * q) ^ 2 ^ (k + 1) = 1 := by
    rw [hlq, pow_succ, pow_mul, hk, one_pow]
  have hq' : q ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, hq2, one_pow]
  rw [hcomm.mul_pow, hq', mul_one] at h1
  exact h1

theorem pow_expo_eq_one (c : Config G L Q n θ z) {g : G} (hg : g ∈ centralizer ({z} : Set G))
    {k : ℕ} (hk : g ^ 2 ^ k = 1) : g ^ expo L n z = 1 := by
  have hq2 : ∀ q ∈ zpowers z, ∀ m : ℕ, q ^ (2 * m) = 1 := by
    intro q hq m
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    rcases zpow_eq_one_or_eq (z_mul_self c) j with h | h
    · rw [h, one_pow]
    · rw [h, pow_mul, sq, z_mul_self c, one_pow]
  by_cases hin : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)
  · obtain ⟨l, hl, q, hq, rfl, hcomm, hl2⟩ := exists_two_pow_mul c hg (hin hg) hk
    by_cases h9 : n ≤ 9
    · rw [expo_of_ASmall ⟨by have := c.hn8; omega, hin⟩, hcomm.mul_pow,
        show (4 : ℕ) = 2 * 2 from rfl, hq2 q hq, mul_one]
      exact pow_four_of_mem_L_of_le θ h9 hl hl2
    · rw [expo_of_not_ASmall (fun h => by have := h.1; omega), hcomm.mul_pow,
        show (8 : ℕ) = 2 * 4 from rfl, hq2 q hq, mul_one]
      exact pow_eight_of_mem_L θ (by have := c.small; omega) hl hl2
  · rw [expo_of_not_ASmall (fun h => hin h.2)]
    have h9 : n ≤ 9 := by
      rcases c.shape with h | ⟨h9, -⟩
      · exact absurd h hin
      · exact h9
    have hCN := cent_le_normalizer c.ot.std c.ot.cyc
    have hg2N : g ^ 2 ∈ normalizer (L : Set G) := pow_mem (hCN hg) 2
    have hg2 : g ^ 2 ∈ L ⊔ centralizer (L : Set G) := by
      refine mem_sup_of_rho_mem θ c.hn8 hg2N (Equiv.Perm.mem_alternatingGroup.2 ?_)
      have : (⟨g ^ 2, hg2N⟩ : normalizer (L : Set G)) = ⟨g, hCN hg⟩ ^ 2 := rfl
      rw [this, map_pow, map_pow, sq, Int.units_mul_self]
    have hk2 : (g ^ 2) ^ 2 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
    obtain ⟨l, hl, q, hq, hlq, hcomm, hl2⟩ := exists_two_pow_mul c (pow_mem hg 2) hg2 hk2
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hlq, hcomm.mul_pow,
      show (4 : ℕ) = 2 * 2 from rfl, hq2 q hq, mul_one]
    exact pow_four_of_mem_L_of_le θ h9 hl hl2

theorem card_sylow_eq_cardN (c : Config G L Q n θ z) (P : Sylow 2 (centralizer ({z} : Set G))) :
    Nat.card P = cardN L n z := by
  obtain ⟨h1, h2⟩ := sec4CentSylowCard_holds G L Q n θ z c P
  by_cases h : IsASmall L n z
  · rw [cardN_of_ASmall h]
    exact h1 h
  · rw [cardN_of_not_ASmall h]
    exact h2 h

end Expo

end CFSG.OddStandard.AltStdSmall4.G2
