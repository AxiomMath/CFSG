module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226Bar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Diag

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.HighestRoot
open scoped commutatorElement MatrixGroups

namespace F3L225

theorem sl23_conj_of_sq_eq_neg_one : ∀ x y : SL23, x ^ 2 = -1 → y ^ 2 = -1 →
    ∃ g : SL23, g * x = y * g := by
  decide +kernel

theorem psl23_sq_eq_one_of_two_pow {x : PSL(2, ZMod 3)} {n : ℕ} (hx : x ^ 2 ^ n = 1) :
    x ^ 2 = 1 := by
  obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_SL23_iff] at hx
  have h8 : X ^ 8 = 1 := by
    have h1 : X ^ 2 ^ (n + 1) = 1 := by
      rcases hx with h | h
      · rw [pow_succ, pow_mul, h, one_pow]
      · rw [pow_succ, pow_mul, h]
        exact neg_one_sq
    have h2 : orderOf X ∣ 2 ^ (n + 1) := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf X ∣ 8 * 3 := by
      have h4 := orderOf_dvd_natCard X
      rw [card_SL23] at h4
      exact h4
    have hcop : Nat.Coprime (orderOf X) 3 :=
      Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left _ (by norm_num))
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h3)
  have h4 := F3L221.sl23_pow_four_of_pow_eight X h8
  rcases T1.sl23_sq_of_pow_four X (Or.inl h4) with h | h
  · rw [← QuotientGroup.mk_pow, h, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, h, QuotientGroup.eq_one_iff, mem_center_SL23_iff]
    exact Or.inr rfl

theorem psl23_conj {x y : PSL(2, ZMod 3)} (hx1 : x ≠ 1) (hx : x ^ 2 = 1) (hy1 : y ≠ 1)
    (hy : y ^ 2 = 1) : ∃ g : PSL(2, ZMod 3), g * x * g⁻¹ = y := by
  obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective y
  have hsq : ∀ {Z : SL23}, (QuotientGroup.mk Z : PSL(2, ZMod 3)) ≠ 1 →
      (QuotientGroup.mk Z : PSL(2, ZMod 3)) ^ 2 = 1 → Z ^ 2 = -1 := by
    intro Z hZ1 hZ
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_SL23_iff] at hZ
    rcases hZ with h | h
    · exfalso
      apply hZ1
      rw [QuotientGroup.eq_one_iff, mem_center_SL23_iff]
      rw [sq] at h
      exact eq_one_or_neg_one_of_mul_self_SL23 Z h
    · exact h
  obtain ⟨g, hg⟩ := sl23_conj_of_sq_eq_neg_one X Y (hsq hx1 hx) (hsq hy1 hy)
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hg,
    mul_inv_cancel_right]

variable {Q : Type} [Group Q] [Finite Q]

theorem commutator_zpowers_le_of_isSubnormal {A M U : Subgroup Q} (hMA : M ≤ A)
    (hMs : (M.subgroupOf A).IsSubnormal) (hUA : U ≤ A) (hAU : A ≤ normalizer (U : Set Q))
    (hU : IsPGroup 2 U) {g : Q} (hgM : g ∈ M) (hg : Odd (orderOf g)) :
    ⁅U, zpowers g⁆ ≤ M ⊓ U := by
  have hgA : g ∈ A := hMA hgM
  have hzA : zpowers g ≤ A := zpowers_le.mpr hgA
  have hzU : zpowers g ≤ normalizer (U : Set Q) := hzA.trans hAU
  have hcop : Nat.Coprime (Nat.card (zpowers g)) (Nat.card U) := by
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    rw [Nat.card_zpowers, hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hg)
  suffices key : ∀ H : Subgroup ↥A, H.IsSubnormal → M.subgroupOf A ≤ H →
      ⁅U, zpowers g⁆ ≤ H.map A.subtype ⊓ U by
    have h1 := key _ hMs le_rfl
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr hMA] at h1
  intro H hH
  induction hH with
  | top =>
    intro _
    rw [← MonoidHom.range_eq_map, range_subtype]
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro u hu h hh
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hUA hu) (hzA hh)) (inv_mem (hUA hu))) (inv_mem (hzA hh))
    · rw [Subgroup.commutator_le]
      intro u hu h hh
      exact ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hu (hzU hh)
  | step H H' hle hH' hN ih =>
    intro hMH
    have hIH := ih (hMH.trans hle)
    refine (ClassicalInvolution.commutator_le_commutator_commutator_of_coprime U (zpowers g)
      hzU hcop).trans ((Subgroup.commutator_mono hIH le_rfl).trans ?_)
    rw [Subgroup.commutator_le]
    intro w hw h hh
    obtain ⟨hwH', hwU⟩ := mem_inf.mp hw
    obtain ⟨w', hw'H', rfl⟩ := hwH'
    have hhM : h ∈ M := (zpowers_le.mpr hgM) hh
    have hhA : h ∈ A := hMA hhM
    have hhH : (⟨h, hhA⟩ : ↥A) ∈ H := hMH hhM
    refine mem_inf.mpr ⟨?_, ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hwU
      (hzU hh)⟩
    have hconj := hN.conj_mem ⟨⟨h, hhA⟩, hle hhH⟩ hhH ⟨w', hw'H'⟩
    refine ⟨w' * ⟨h, hhA⟩ * w'⁻¹ * ⟨h, hhA⟩⁻¹, mul_mem hconj (inv_mem hhH), ?_⟩
    simp [commutatorElement_def]

@[expose] def centralInvolutions (L : Subgroup Q) : Subgroup Q where
  carrier := {x | x ∈ L ∧ (∀ l ∈ L, x * l = l * x) ∧ x * x = 1}
  mul_mem' := by
    rintro a b ⟨haL, hac, haa⟩ ⟨hbL, hbc, hbb⟩
    refine ⟨mul_mem haL hbL, fun l hl => ?_, ?_⟩
    · calc a * b * l = a * (l * b) := by rw [mul_assoc, hbc l hl]
        _ = l * (a * b) := by rw [← mul_assoc, hac l hl, mul_assoc]
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [(hac b hbL).symm]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
  one_mem' := ⟨one_mem _, fun l _ => by rw [one_mul, mul_one], mul_one 1⟩
  inv_mem' := by
    rintro a ⟨haL, hac, haa⟩
    refine ⟨inv_mem haL, fun l hl => ?_, ?_⟩
    · have h1 := hac l hl
      calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * l) * a⁻¹ := by rw [h1]
        _ = l * a⁻¹ := by group
    · rw [← mul_inv_rev, haa, inv_one]

omit [Finite Q] in
theorem isPGroup_centralInvolutions (L : Subgroup Q) : IsPGroup 2 (centralInvolutions L) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_one, sq]
  exact x.2.2.2

omit [Finite Q] in
theorem normalizer_le_normalizer_centralInvolutions (L : Subgroup Q) :
    normalizer (L : Set Q) ≤ normalizer ((centralInvolutions L : Subgroup Q) : Set Q) := by
  have key : ∀ g ∈ normalizer (L : Set Q), ∀ x ∈ centralInvolutions L,
      g * x * g⁻¹ ∈ centralInvolutions L := by
    intro g hg x hx
    obtain ⟨hxL, hxc, hxx⟩ := hx
    refine ⟨(mem_normalizer_iff.mp hg x).mp hxL, fun l hl => ?_, ?_⟩
    · have hl' : g⁻¹ * l * g ∈ L := by
        have h1 := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
        rwa [inv_inv] at h1
      have h2 := hxc _ hl'
      calc g * x * g⁻¹ * l = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by rw [h2]
        _ = l * (g * x * g⁻¹) := by group
    · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hxx, mul_one, mul_inv_cancel]
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have h1 := key g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

theorem eq_one_of_mem_pPrimeCore_of_mul_self {M : Subgroup Q} {x : ↥M}
    (hx : x ∈ pPrimeCore 2 ↥M) (hxx : x * x = 1) : x = 1 := by
  have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥M))
  rw [← Subgroup.orderOf_coe] at h1
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hxx)
  have hodd := odd_card_pPrimeCore_two ↥M
  have h3 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at h1
      exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hodd)
  exact orderOf_eq_one_iff.mp h3

theorem centralizes_centralInvolutions {L M : Subgroup Q} {t : Q} (htL : t ∈ L)
    (hM : IsSolvableTwoComponentIn M (centralizer {t})) (hMN : M ≤ normalizer (L : Set Q))
    (hnot : ¬ ∀ s ∈ M, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ L) :
    ∀ m ∈ M, ∀ u ∈ centralInvolutions L, m * u = u * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := centralInvolutions L with hU
  have hUL : U ≤ L := fun x hx => hx.1
  have hUt : U ≤ centralizer ({t} : Set Q) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hx.2.1 t htL)
  set A := normalizer (L : Set Q) ⊓ centralizer ({t} : Set Q) with hA
  have hMA : M ≤ A := le_inf hMN hM.1
  have hMs : (M.subgroupOf A).IsSubnormal := F3L226.isSubnormal_subgroupOf_mono inf_le_right hM.2.1
  have hUA : U ≤ A := le_inf (hUL.trans le_normalizer) hUt
  have hAU : A ≤ normalizer (U : Set Q) :=
    inf_le_left.trans (normalizer_le_normalizer_centralInvolutions L)
  have hUp : IsPGroup 2 U := isPGroup_centralInvolutions L
  have hMU : ∀ y ∈ M, ∀ a ∈ M ⊓ U, y * a = a * y := by
    rcases hM.2.2.2 with he | he
    ·
      obtain ⟨e⟩ := he
      have htriv : ∀ a ∈ M ⊓ U, a = 1 := by
        intro a ha
        obtain ⟨haM, haU⟩ := mem_inf.mp ha
        by_contra ha1
        apply hnot
        intro s hs ⟨n, hsn⟩
        have hab : QuotientGroup.mk (⟨a, haM⟩ : ↥M) ≠ (1 : ↥M ⧸ pPrimeCore 2 ↥M) := by
          intro h
          rw [QuotientGroup.eq_one_iff] at h
          exact ha1 (congrArg Subtype.val (eq_one_of_mem_pPrimeCore_of_mul_self h
            (Subtype.ext haU.2.2)))
        by_cases hs1 : QuotientGroup.mk (⟨s, hs⟩ : ↥M) = (1 : ↥M ⧸ pPrimeCore 2 ↥M)
        · rw [QuotientGroup.eq_one_iff] at hs1
          have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥(pPrimeCore 2 ↥M)) :=
            Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_card_pPrimeCore_two ↥M))
          have h1 := orderOf_dvd_natCard (⟨⟨s, hs⟩, hs1⟩ : ↥(pPrimeCore 2 ↥M))
          have h2 : orderOf (⟨⟨s, hs⟩, hs1⟩ : ↥(pPrimeCore 2 ↥M)) ∣ 2 ^ n := by
            apply orderOf_dvd_of_pow_eq_one
            apply Subtype.ext
            apply Subtype.ext
            simpa using hsn
          have h3 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
          rw [orderOf_eq_one_iff] at h3
          have h4 : s = 1 := congrArg (fun w : ↥(pPrimeCore 2 ↥M) => ((w : ↥M) : Q)) h3
          rw [h4]
          exact one_mem _
        ·
          have hsq : e (QuotientGroup.mk (⟨s, hs⟩ : ↥M)) ^ 2 = 1 := by
            apply psl23_sq_eq_one_of_two_pow (n := n)
            rw [← map_pow, ← QuotientGroup.mk_pow]
            have h1 : (⟨s, hs⟩ : ↥M) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hsn)
            rw [h1, QuotientGroup.mk_one, map_one]
          have hasq : e (QuotientGroup.mk (⟨a, haM⟩ : ↥M)) ^ 2 = 1 := by
            rw [← map_pow, ← QuotientGroup.mk_pow]
            have h1 : (⟨a, haM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by rw [sq]; exact haU.2.2)
            rw [h1, QuotientGroup.mk_one, map_one]
          obtain ⟨g, hg⟩ := psl23_conj (fun h => hab (e.injective (h.trans (map_one e).symm)))
            hasq (fun h => hs1 (e.injective (h.trans (map_one e).symm))) hsq
          obtain ⟨g', hg'g⟩ := QuotientGroup.mk_surjective (e.symm g)
          have hg' : QuotientGroup.mk (g' * ⟨a, haM⟩ * g'⁻¹) =
              (QuotientGroup.mk (⟨s, hs⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := by
            apply e.injective
            rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul,
              map_mul, map_inv, hg'g, MulEquiv.apply_symm_apply]
            exact hg
          rw [QuotientGroup.eq] at hg'
          have hgaU : (g' : Q) * a * (g' : Q)⁻¹ ∈ U :=
            (mem_normalizer_iff.mp (hAU (hMA g'.2)) a).mp haU
          have hmem : s ∈ L ⊔ (pPrimeCore 2 ↥M).map M.subtype := by
            have h1 : s = ((g' : Q) * a * (g' : Q)⁻¹) *
                (((g' * ⟨a, haM⟩ * g'⁻¹)⁻¹ * ⟨s, hs⟩ : ↥M) : Q) := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
              group
            rw [h1]
            exact mul_mem (mem_sup_left (hUL hgaU)) (mem_sup_right ⟨_, hg', rfl⟩)
          have hON : (pPrimeCore 2 ↥M).map M.subtype ≤ normalizer (L : Set Q) :=
            (map_subtype_le _).trans hMN
          have hOodd : Odd (Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype)) := by
            rw [Subgroup.card_map_of_injective M.subtype_injective]
            exact odd_card_pPrimeCore_two ↥M
          exact F3L221.mem_of_mem_sup_of_odd hON hOodd hmem hsn
      intro y _ a ha
      rw [htriv a ha, mul_one, one_mul]
    ·
      obtain ⟨e⟩ := he
      intro y hy a ha
      obtain ⟨haM, haU⟩ := mem_inf.mp ha
      have hea : e (QuotientGroup.mk (⟨a, haM⟩ : ↥M)) * e (QuotientGroup.mk ⟨a, haM⟩) = 1 := by
        rw [← map_mul, ← QuotientGroup.mk_mul]
        have h1 : (⟨a, haM⟩ : ↥M) * ⟨a, haM⟩ = 1 := Subtype.ext haU.2.2
        rw [h1, QuotientGroup.mk_one, map_one]
      have hc : QuotientGroup.mk (⟨a, haM⟩ : ↥M) ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
        rw [← mem_center_mulEquiv_iff e, mem_center_SL23_iff]
        exact eq_one_or_neg_one_of_mul_self_SL23 _ hea
      have h1 := mem_center_iff.mp hc (QuotientGroup.mk ⟨y, hy⟩)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
      have hyN : y ∈ normalizer ((U : Subgroup Q) : Set Q) := hAU (hMA hy)
      have hcU : a⁻¹ * (y⁻¹ * a * y) ∈ U := by
        refine mul_mem (inv_mem haU) ?_
        have h2 := (mem_normalizer_iff.mp (inv_mem hyN) a).mp haU
        rwa [inv_inv] at h2
      have hcc : ((⟨y, hy⟩ * ⟨a, haM⟩ : ↥M)⁻¹ * (⟨a, haM⟩ * ⟨y, hy⟩)) *
          ((⟨y, hy⟩ * ⟨a, haM⟩ : ↥M)⁻¹ * (⟨a, haM⟩ * ⟨y, hy⟩)) = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        have h3 : ((y * a)⁻¹ * (a * y)) = a⁻¹ * (y⁻¹ * a * y) := by group
        rw [h3]
        exact hcU.2.2
      have h4 := eq_one_of_mem_pPrimeCore_of_mul_self h1 hcc
      have h5 : (y * a)⁻¹ * (a * y) = 1 := by
        have h6 := congrArg Subtype.val h4
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] using h6
      calc y * a = (y * a) * ((y * a)⁻¹ * (a * y)) := by rw [h5, mul_one]
        _ = a * y := by group
  have hle : M ≤ centralizer (U : Set Q) := F3L221.le_of_forall_odd hM fun y hy hodd => by
    have hc := commutator_zpowers_le_of_isSubnormal hMA hMs hUA hAU hUp hy hodd
    have hzU : zpowers y ≤ normalizer (U : Set Q) := zpowers_le.mpr (hAU (hMA hy))
    have hcop : Nat.Coprime (Nat.card (zpowers y)) (Nat.card U) := by
      obtain ⟨k, hk⟩ := hUp.exists_card_eq
      rw [Nat.card_zpowers, hk]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    have h1 := (ClassicalInvolution.commutator_le_commutator_commutator_of_coprime U (zpowers y)
      hzU hcop).trans (Subgroup.commutator_mono hc le_rfl)
    have h2 : ⁅M ⊓ U, zpowers y⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      have h3 : Commute y a := hMU y hy a ha
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (h3.zpow_left k).symm
    rw [h2] at h1
    rw [mem_centralizer_iff]
    intro u hu
    have h3 : ⁅u, y⁆ ∈ ⁅U, zpowers y⁆ := commutator_mem_commutator hu (mem_zpowers y)
    have h4 := h1 h3
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4
  intro m hm u hu
  exact (mem_centralizer_iff.mp (hle hm) u hu).symm

end F3L225

end CFSG.ComponentClassification.HarrisLit.T1
