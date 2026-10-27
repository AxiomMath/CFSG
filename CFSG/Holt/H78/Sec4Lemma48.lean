module

public import CFSG.Holt.H78.Sec4Defs
public import CFSG.Holt.H78.Data
import CFSG.Holt.H78.Sec4Lemma42
import CFSG.Holt.H78.Lemma27Blocks
import CFSG.Holt.H78.Lemma27Real
import CFSG.Holt.H78.Conjugacy
import CFSG.Holt.H78.DataSocle
import CFSG.Holt.H78.Sec4AltSylow
import CFSG.Holt.H78.Prelim
import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open Equiv Equiv.Perm
open scoped Pointwise

section Perm

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem mem_alternatingGroup_iff_four_dvd_card_support {σ : Perm X} (hσ : σ ^ 2 = 1) :
    σ ∈ alternatingGroup X ↔ 4 ∣ σ.support.card := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := cycleType_of_pow_prime_eq_one (p := 2) hσ
  have hsum := sum_cycleType σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [mem_alternatingGroup, sign_of_cycleType, hk, Multiset.sum_replicate,
    Multiset.card_replicate, smul_eq_mul, pow_add, pow_mul', Int.units_sq, one_pow, one_mul,
    ← hsum, neg_one_pow_eq_one_iff_even (by decide), Nat.even_iff]
  omega

theorem card_support_add_card_fixed (σ : Perm X) :
    σ.support.card + (Finset.univ.filter fun x => σ x = x).card = Fintype.card X := by
  rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x => σ x ≠ x)]
  congr 2
  ext x
  simp

theorem IsNaturalSE.eq_alternatingGroup_of_card_eq_five
    {M : Subgroup (Perm X)} (hM : IsNaturalSE M) (h5 : Fintype.card X = 5) :
    M = alternatingGroup X := by
  have hF : IsHoltFactor M := Or.inr hM
  have hP := hF.isPerfect
  refine le_antisymm (fun m hm => ?_) ?_
  · exact Abelianization.commutator_subset_ker (sign.comp M.subtype)
      (Group.IsPerfect.mem_commutator (g := (⟨m, hm⟩ : M)))
  obtain ⟨n, k, e, hA⟩ := hM.exists_isBenderAction
  have hcard := hA.card_eq
  rw [Nat.card_eq_fintype_card, h5] at hcard
  obtain ⟨hk1, -, hn2⟩ := hA.params
  have hnk : n = 2 ∧ k = 1 := by
    have h4 : (2 ^ n) ^ k = 4 := by omega
    rw [← pow_mul] at h4
    have h22 : n * k = 2 := Nat.pow_right_injective (le_refl 2) (h4.trans (by norm_num))
    have hk : k ≤ 1 := by nlinarith
    exact ⟨by nlinarith, by omega⟩
  obtain ⟨rfl, rfl⟩ := hnk
  have : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  have h3 : 3 ∣ Nat.card ↥(stabilizer M a ⊓ stabilizer M b) := by
    rw [hA.card_stabilizer_inf hab]
    exact ⟨e, by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hga : ((g : M) : Perm X) a = a := (Subgroup.mem_inf.mp g.2).1
  have hgb : ((g : M) : Perm X) b = b := (Subgroup.mem_inf.mp g.2).2
  have hord : orderOf ((g : M) : Perm X) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
  have hcyc : ((g : M) : Perm X).IsThreeCycle := by
    rw [← card_support_eq_three_iff]
    have hsub : ((g : M) : Perm X).support ⊆ (Finset.univ.erase a).erase b := by
      intro x hx
      rw [mem_support] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hx (h ▸ hgb), fun h => hx (h ▸ hga)⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hab]), Finset.card_erase_of_mem
      (Finset.mem_univ a), Finset.card_univ, h5] at hle
    have hc := isCycle_of_prime_order (σ := ((g : M) : Perm X))
      (by rw [hord]; exact Nat.prime_three) (by rw [hord]; omega)
    rw [← hc.orderOf, hord]
  have : IsPretransitive M X := hF.isPretransitive
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (IsPreprimitive.of_prime_card (by rw [Nat.card_eq_fintype_card, h5]; norm_num)) hcyc
    (g : M).2

theorem exists_commute_mul_mem_longInv {s : Perm X} {a b c p : X}
    (hs : s ∈ longInvAt (Perm X) X c) (h7 : 7 ≤ Fintype.card X) (hsa : s a = b)
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) :
    ∃ e ∈ alternatingGroup X, s * e = e * s ∧ e a = a ∧ e c = c ∧ e p ≠ p ∧
      s * e ∈ longInv (Perm X) X := by
  have hss : ∀ x, s (s x) = x := fun x => by
    rw [← Perm.mul_apply, mul_self_eq_one_of_mem_longInv hs.1, Perm.one_apply]
  have hsc : s c = c := hs.2
  have hfix : ∀ x, s x = x → x = c := fun x hx => hs.1.2.unique hx hsc
  have hsb : s b = a := by rw [← hsa, hss]
  set q := s p with hq
  obtain ⟨r, hr⟩ : ∃ r, r ∉ ({a, b, c, p, q} : Finset X) := by
    by_contra! h
    have hle := Finset.card_le_card (fun x _ => h x : (Finset.univ : Finset X) ⊆ {a, b, c, p, q})
    have := Finset.card_le_five (a := a) (b := b) (c := c) (d := p) (e := q)
    rw [Finset.card_univ] at hle
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨hra, hrb, hrc, hrp, hrq⟩ := hr
  replace hra : r ≠ a := hra
  replace hrb : r ≠ b := hrb
  replace hrc : r ≠ c := hrc
  replace hrp : r ≠ p := hrp
  replace hrq : r ≠ q := hrq
  set r' := s r with hr'
  have hqp : q ≠ p := fun h => hpc (hfix p h)
  have hqa : q ≠ a := fun h => hpb (by rw [← hss p, ← hq, h, hsa])
  have hqb : q ≠ b := fun h => hpa (by rw [← hss p, ← hq, h, hsb])
  have hqc : q ≠ c := fun h => hpc (by rw [← hss p, ← hq, h, hsc])
  have hr'r : r' ≠ r := fun h => hrc (hfix r h)
  have hr'a : r' ≠ a := fun h => hrb (by rw [← hss r, ← hr', h, hsa])
  have hr'b : r' ≠ b := fun h => hra (by rw [← hss r, ← hr', h, hsb])
  have hr'c : r' ≠ c := fun h => hrc (by rw [← hss r, ← hr', h, hsc])
  have hr'p : r' ≠ p := fun h => hrq (by rw [hq, ← h, hss])
  have hr'q : r' ≠ q := fun h => hrp (by rw [← hss r, ← hr', h, hq, hss])
  set e := swap p r * swap q r' with he
  have hsq : s q = p := hss p
  have hsr' : s r' = r := hss r
  have hcomm₀ : swap q r' * swap p r = swap p r * swap q r' :=
    ((disjoint_swap_swap (by simp [hqp, hrq.symm, hr'p, hr'r, hrp.symm, hr'q.symm])).commute).eq
  have hcomm : s * e = e * s := by
    have h1 : s * swap p r * s⁻¹ = swap q r' := by rw [← swap_apply_apply]
    have h2 : s * swap q r' * s⁻¹ = swap p r := by rw [← swap_apply_apply, hsq, hsr']
    have h3 : s * e * s⁻¹ = e := by
      rw [he, show s * (swap p r * swap q r') * s⁻¹ =
        (s * swap p r * s⁻¹) * (s * swap q r' * s⁻¹) by group, h1, h2, hcomm₀]
    calc s * e = s * e * s⁻¹ * s := by group
      _ = e * s := by rw [h3]
  have hea : e a = a := by
    rw [he, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hqa) (Ne.symm hr'a),
      swap_apply_of_ne_of_ne (Ne.symm hpa) (Ne.symm hra)]
  have hec : e c = c := by
    rw [he, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hqc) (Ne.symm hr'c),
      swap_apply_of_ne_of_ne (Ne.symm hpc) (Ne.symm hrc)]
  have hep : e p = r := by
    rw [he, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hqp) (Ne.symm hr'p), swap_apply_left]
  have heq : e q = r' := by
    rw [he, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hr'p hr'r]
  have her : e r = p := by
    rw [he, Perm.mul_apply, swap_apply_of_ne_of_ne hrq (Ne.symm hr'r), swap_apply_right]
  have her' : e r' = q := by
    rw [he, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hqp hrq.symm]
  refine ⟨e, ?_, hcomm, hea, hec, by rw [hep]; exact hrp, ?_⟩
  · rw [mem_alternatingGroup, he, Perm.sign_mul, sign_swap hrp.symm, sign_swap hr'q.symm]
    rfl
  · have hee : e * e = 1 := by
      have : e * e = swap p r * swap p r * (swap q r' * swap q r') := by
        rw [he, mul_assoc, ← mul_assoc (swap q r'), hcomm₀]
        group
      rw [this, swap_mul_self, swap_mul_self, one_mul]
    have hse2 : (s * e) ^ 2 = 1 := by
      have : s * e * (s * e) = s * s * (e * e) := by
        rw [mul_assoc, ← mul_assoc e, ← hcomm]
        group
      rw [sq, this, mul_self_eq_one_of_mem_longInv hs.1, hee, one_mul]
    have hse1 : s * e ≠ 1 := fun h => hr'p (by
      have := congrArg (· p) h
      simpa [Perm.mul_apply, hep] using this)
    refine ⟨orderOf_eq_prime hse2 hse1, c, ?_, fun x hx => ?_⟩
    · show (s * e) c = c
      rw [Perm.mul_apply, hec, hsc]
    replace hx : s (e x) = x := hx
    by_cases hxp : x = p
    · rw [hxp, hep] at hx; exact absurd hx hr'p
    by_cases hxq : x = q
    · rw [hxq, heq, hsr'] at hx; exact absurd hx hrq
    by_cases hxr : x = r
    · rw [hxr, her] at hx; exact absurd hx hrq.symm
    by_cases hxr' : x = r'
    · rw [hxr', her', hsq] at hx; exact absurd hx hr'p.symm
    rw [he, Perm.mul_apply, swap_apply_of_ne_of_ne hxq hxr', swap_apply_of_ne_of_ne hxp hxr] at hx
    exact hfix x hx

private theorem exists_not_mem_finset (s : Finset X) (h : s.card < Fintype.card X) :
    ∃ x, x ∉ s := by
  by_contra! hx
  have := Finset.card_le_card (fun x _ => hx x : (Finset.univ : Finset X) ⊆ s)
  rw [Finset.card_univ] at this
  omega

end Perm

section BW

variable {X : Type*} [Group X] {Δ : Type*} [MulAction X Δ]

theorem smul_orbit_eq_of_normal {N : Subgroup X} [N.Normal] {γ : Δ} {x : X} (hx : x • γ = γ) :
    x • orbit N γ = orbit N γ := by
  rw [smul_orbit_eq_orbit_smul, hx]

private theorem ncard_setOf_orbit (N : Subgroup X) (γ : Δ) (P : Δ → Prop) :
    {δ : orbit N γ | P δ}.ncard = {δ | δ ∈ orbit N γ ∧ P δ}.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext δ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨δ.2, hδ⟩
  · rintro ⟨hδ, hP⟩
    exact ⟨⟨δ, hδ⟩, hP, rfl⟩

variable [Finite Δ]

theorem ncard_fixed_orbit_mul {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {γ : Δ}
    {x y : X} (hx : x • γ = γ) (hy : y • γ = γ)
    (hx2 : ∀ δ ∈ orbit N γ, x • x • δ = δ) (hy2 : ∀ δ ∈ orbit N γ, y • y • δ = δ)
    (hxy : ∀ δ ∈ orbit N γ, x • y • δ = y • x • δ) :
    {δ | δ ∈ orbit N γ ∧ x • δ = δ}.ncard * {δ | δ ∈ orbit N γ ∧ y • δ = δ}.ncard *
        {δ | δ ∈ orbit N γ ∧ x • y • δ = δ}.ncard =
      (orbit N γ).ncard * {δ | δ ∈ orbit N γ ∧ x • δ = δ ∧ y • δ = δ}.ncard ^ 2 := by
  set b := orbit N γ with hb
  have hxb : ∀ δ ∈ b, x • δ ∈ b := fun δ hδ => by
    rw [hb, ← smul_orbit_eq_of_normal (N := N) hx]
    exact Set.smul_mem_smul_set hδ
  have hyb : ∀ δ ∈ b, y • δ ∈ b := fun δ hδ => by
    rw [hb, ← smul_orbit_eq_of_normal (N := N) hy]
    exact Set.smul_mem_smul_set hδ
  by_cases hx1 : ∀ δ ∈ b, x • δ = δ
  · have e1 : {δ | δ ∈ b ∧ x • δ = δ} = b := Set.ext fun δ => ⟨fun h => h.1, fun h => ⟨h, hx1 δ h⟩⟩
    have e2 : {δ | δ ∈ b ∧ x • y • δ = δ} = {δ | δ ∈ b ∧ y • δ = δ} :=
      Set.ext fun δ => and_congr_right fun h => by rw [hx1 _ (hyb δ h)]
    have e3 : {δ | δ ∈ b ∧ x • δ = δ ∧ y • δ = δ} = {δ | δ ∈ b ∧ y • δ = δ} :=
      Set.ext fun δ => and_congr_right fun h => and_iff_right (hx1 δ h)
    rw [e1, e2, e3]
    ring
  by_cases hy1 : ∀ δ ∈ b, y • δ = δ
  · have e2 : {δ | δ ∈ b ∧ y • δ = δ} = b := Set.ext fun δ => ⟨fun h => h.1, fun h => ⟨h, hy1 δ h⟩⟩
    have e3 : {δ | δ ∈ b ∧ x • y • δ = δ} = {δ | δ ∈ b ∧ x • δ = δ} :=
      Set.ext fun δ => and_congr_right fun h => by rw [hy1 δ h]
    have e4 : {δ | δ ∈ b ∧ x • δ = δ ∧ y • δ = δ} = {δ | δ ∈ b ∧ x • δ = δ} :=
      Set.ext fun δ => and_congr_right fun h => and_iff_left (hy1 δ h)
    rw [e2, e3, e4]
    ring
  by_cases hxy1 : ∀ δ ∈ b, x • δ = y • δ
  · have e2 : {δ | δ ∈ b ∧ y • δ = δ} = {δ | δ ∈ b ∧ x • δ = δ} :=
      Set.ext fun δ => and_congr_right fun h => by rw [hxy1 δ h]
    have e3 : {δ | δ ∈ b ∧ x • y • δ = δ} = b := Set.ext fun δ => ⟨fun h => h.1, fun h =>
      ⟨h, by rw [← hxy1 δ h]; exact hx2 δ h⟩⟩
    have e4 : {δ | δ ∈ b ∧ x • δ = δ ∧ y • δ = δ} = {δ | δ ∈ b ∧ x • δ = δ} :=
      Set.ext fun δ => and_congr_right fun h => ⟨fun h' => h'.1, fun h' => ⟨h', by
        rw [← hxy1 δ h]; exact h'⟩⟩
    rw [e2, e3, e4]
    ring
  push Not at hx1 hy1 hxy1
  set T := stabilizer X b
  have hxT : x ∈ T := mem_stabilizer_iff.mpr (smul_orbit_eq_of_normal hx)
  have hyT : y ∈ T := mem_stabilizer_iff.mpr (smul_orbit_eq_of_normal hy)
  have hNT : N ≤ T := fun n hn => mem_stabilizer_iff.mpr (by
    rw [hb, smul_orbit_eq_orbit_smul]
    exact orbit_eq_iff.mpr ⟨⟨n, hn⟩, rfl⟩)
  set f := toPermHom T b
  have hN' : Nat.Coprime 2 (Nat.card (N.subgroupOf T)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv, Nat.coprime_two_left]
    exact hN
  have htr : IsPretransitive (N.subgroupOf T) b := by
    have hγ : ∀ δ : b, ∃ n : N.subgroupOf T, n • (⟨γ, mem_orbit_self γ⟩ : b) = δ := by
      rintro ⟨δ, n, rfl⟩
      exact ⟨⟨⟨n, hNT n.2⟩, Subgroup.mem_subgroupOf.mpr n.2⟩, rfl⟩
    refine ⟨fun δ₁ δ₂ => ?_⟩
    obtain ⟨n₁, rfl⟩ := hγ δ₁
    obtain ⟨n₂, rfl⟩ := hγ δ₂
    exact ⟨n₂ * n₁⁻¹, by rw [mul_smul, inv_smul_smul]⟩
  have := (Subgroup.Normal.subgroupOf ‹N.Normal› T)
  have htr' := isPretransitive_pPrimeCore_range (X := T) (Δ := b) hN' htr
  set x' : f.range := ⟨f ⟨x, hxT⟩, ⟨_, rfl⟩⟩
  set y' : f.range := ⟨f ⟨y, hyT⟩, ⟨_, rfl⟩⟩
  have hx'δ : ∀ δ : b, ((x' • δ : b) : Δ) = x • (δ : Δ) := fun _ => rfl
  have hy'δ : ∀ δ : b, ((y' • δ : b) : Δ) = y • (δ : Δ) := fun _ => rfl
  have hx'2 : x' ^ 2 = 1 := Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
    rw [sq]; exact hx2 δ δ.2))
  have hy'2 : y' ^ 2 = 1 := Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
    rw [sq]; exact hy2 δ δ.2))
  have hx'1 : x' ≠ 1 := fun h => by
    obtain ⟨δ, hδ, hne⟩ := hx1
    exact hne (congrArg Subtype.val (congrArg (fun z : f.range => z • (⟨δ, hδ⟩ : b)) h))
  have hy'1 : y' ≠ 1 := fun h => by
    obtain ⟨δ, hδ, hne⟩ := hy1
    exact hne (congrArg Subtype.val (congrArg (fun z : f.range => z • (⟨δ, hδ⟩ : b)) h))
  have hne : x' ≠ y' := fun h => by
    obtain ⟨δ, hδ, hne⟩ := hxy1
    exact hne (congrArg Subtype.val (congrArg (fun z : f.range => z • (⟨δ, hδ⟩ : b)) h))
  have hcomm : Commute x' y' := Subtype.ext (Equiv.ext fun δ => Subtype.ext (hxy δ δ.2))
  have hP : IsPretransitive (CFSG.pPrimeCore 2 f.range) b := htr'
  have key := card_fixedBy_mul_card_fixedBy_mul_card_fixedBy (G := f.range) (Ω := b)
    (orderOf_eq_prime hx'2 hx'1) (orderOf_eq_prime hy'2 hy'1) hcomm hne
  have c1 : (fixedBy b x').ncard = {δ | δ ∈ b ∧ x • δ = δ}.ncard := by
    rw [← ncard_setOf_orbit]
    congr 1
    ext δ
    show x' • δ = δ ↔ x • (δ : Δ) = δ
    exact Subtype.ext_iff
  have c2 : (fixedBy b y').ncard = {δ | δ ∈ b ∧ y • δ = δ}.ncard := by
    rw [← ncard_setOf_orbit]
    congr 1
    ext δ
    show y' • δ = δ ↔ y • (δ : Δ) = δ
    exact Subtype.ext_iff
  have c3 : (fixedBy b (x' * y')).ncard = {δ | δ ∈ b ∧ x • y • δ = δ}.ncard := by
    rw [← ncard_setOf_orbit]
    congr 1
    ext δ
    show (x' * y') • δ = δ ↔ x • y • (δ : Δ) = δ
    rw [mul_smul]
    exact Subtype.ext_iff
  have c4 : (fixedBy b x' ∩ fixedBy b y').ncard =
      {δ | δ ∈ b ∧ x • δ = δ ∧ y • δ = δ}.ncard := by
    rw [← ncard_setOf_orbit]
    congr 1
    ext δ
    show x' • δ = δ ∧ y' • δ = δ ↔ x • (δ : Δ) = δ ∧ y • (δ : Δ) = δ
    exact and_congr Subtype.ext_iff Subtype.ext_iff
  rw [c1, c2, c3, c4, Nat.card_coe_set_eq] at key
  exact key

private theorem ncard_setOf_eq_one {Y : Type*} {b : Set Y} {P : Y → Prop} {x₀ : Y} (h0 : x₀ ∈ b)
    (hP0 : P x₀) (hP : ∀ x ∈ b, P x → x = x₀) : {x | x ∈ b ∧ P x}.ncard = 1 :=
  Set.ncard_eq_one.mpr ⟨x₀, Set.ext fun x => ⟨fun h => hP x h.1 h.2, fun h => h ▸ ⟨h0, hP0⟩⟩⟩

private theorem forall_of_ncard_setOf_eq {Y : Type*} [Finite Y] {b : Set Y} {P : Y → Prop}
    (h : {x | x ∈ b ∧ P x}.ncard = b.ncard) : ∀ x ∈ b, P x := by
  have := Set.eq_of_subset_of_ncard_le (fun x hx => hx.1) h.ge
  intro x hx
  rw [← this] at hx
  exact hx.2

end BW

section LiftFix

variable {K : Type*} [Group K] {X : Type*} [MulAction K X] (D : HoltData K X)

theorem HoltData.mem_fixSet_map_iff_of_le_L (hO : jOddCore K X = ⊥) {j : D.ι}
    {Q : Subgroup (jHull K X)} (hQ : Q ≤ (D.L j).subgroupOf (jHull K X)) (δ : X) :
    δ ∈ fixSet X (Q.map (jHull K X).subtype) ↔ D.coord δ j ∈ fixSet (D.Ψc j) (Q.map (D.ρ j)) := by
  constructor
  · rintro hδ _ ⟨q, hq, rfl⟩
    rw [Perm.smul_def, ← D.coord_smul]
    exact congrArg (D.coord · j) (hδ _ ⟨q, hq, rfl⟩)
  · rintro hδ _ ⟨q, hq, rfl⟩
    refine D.coord_injective hO (funext fun l => ?_)
    show D.coord ((q : K) • δ) l = D.coord δ l
    rw [D.coord_smul]
    by_cases hl : l = j
    · subst hl
      exact hδ _ ⟨q, hq, rfl⟩
    · rw [D.rho_eq_one_of_mem_L (Ne.symm hl) (Subgroup.mem_subgroupOf.mp (hQ hq)), Perm.one_apply]

theorem mem_fixSet_iSup_iff {ι : Sort*} (Q : ι → Subgroup K) (δ : X) :
    δ ∈ fixSet X (⨆ i, Q i) ↔ ∀ i, δ ∈ fixSet X (Q i) := by
  simp only [mem_fixSet_iff_le_stabilizer, iSup_le_iff]

theorem HoltData.exists_isPGroup_lift [Finite K] {j : D.ι} {T : Subgroup (Equiv.Perm (D.Ψc j))}
    (hT : IsPGroup 2 T) (hTM : T ≤ D.M j) {E : Subgroup (jHull K X)} (hE : IsPGroup 2 E)
    (hEL : E ≤ (D.L j).subgroupOf (jHull K X)) (hET : E.map (D.ρ j) ≤ T) :
    ∃ Q : Subgroup (jHull K X), E ≤ Q ∧ Q ≤ (D.L j).subgroupOf (jHull K X) ∧ IsPGroup 2 Q ∧
      Q.map (D.ρ j) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Holt.exists_isPGroup_map_eq_of_map_le (D.ρ j) hT hTM hE hEL hET

end LiftFix

section KSide

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

theorem IsTypeL.mem_fixSet_zpowers {α : Ω} {v : G} (hv : IsTypeL G Ω α v) :
    α ∈ fixSet Ω (Subgroup.zpowers v) := by
  rw [fixSet_zpowers, mem_fixedBy]
  exact hv.smul_eq

private theorem ne_of_mem_holtDelta' {α β δ : Ω} (hαβ : α ≠ β) (hδ : δ ∈ holtDelta G Ω α β) :
    δ ≠ α ∧ δ ≠ β := by
  obtain ⟨t, ht, htδ⟩ := hδ
  have htt : t * t = 1 := mul_self_eq_one_of_mem_longInv ht.1
  refine ⟨fun h => hαβ ?_, fun h => hαβ ?_⟩
  · calc α = t • α := by rw [← h]; exact htδ.symm
      _ = β := ht.2
  · calc α = t • β := by rw [← ht.2, ← mul_smul, htt, one_smul]
      _ = β := by rw [← h]; exact htδ

private theorem mem_fixSet_zpowers_iff' {v : G} {ω : Ω} :
    ω ∈ fixSet Ω (Subgroup.zpowers v) ↔ v • ω = ω := by
  rw [fixSet_zpowers, mem_fixedBy]

private theorem mem_centralizer_zpowers_iff_commute' {x g : G} :
    g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) ↔ Commute x g := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · rintro h _ ⟨k, rfl⟩
    exact (h.zpow_left k).eq

variable (G Ω) in
structure L48Config (α : Ω) (v : G) where
  hv : IsTypeL G Ω α v
  D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))
  hO : jOddCore (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) = ⊥
  i : D.ι
  alt : D.M i = alternatingGroup (D.Ψc i)
  seven : 7 ≤ Fintype.card (D.Ψc i)
  b : fixSet Ω (Subgroup.zpowers v)
  coord_b_ne : D.coord b i ≠ D.coord ⟨α, hv.mem_fixSet_zpowers⟩ i
  coord_b_eq : ∀ j, j ≠ i → D.coord b j = D.coord ⟨α, hv.mem_fixSet_zpowers⟩ j

namespace L48Config

variable {α : Ω} {v : G} (C : L48Config G Ω α v)

private abbrev a (C : L48Config G Ω α v) : fixSet Ω (Subgroup.zpowers v) :=
  ⟨α, C.hv.mem_fixSet_zpowers⟩

private theorem coord_injective : Function.Injective C.D.coord := C.D.coord_injective C.hO

private theorem a_ne_b : C.a ≠ C.b := fun h => C.coord_b_ne (by rw [← h])

private theorem ne : α ≠ (C.b : Ω) := fun h => C.a_ne_b (Subtype.ext h)

include C in
private theorem isPGroup : IsPGroup 2 (Subgroup.zpowers v) :=
  isPGroup_zpowers_of_orderOf_eq_two C.hv.orderOf_eq_two

variable [Fintype Ω] [DecidableEq Ω]

include C in
private theorem three_le (hS : Sec4Setting G Ω) : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers v)) :=
  three_le_card_fixSet_of_isTypeL hS.star C.hv

variable [Finite G] [FaithfulSMul G Ω]

private theorem mem_holtDelta_iff (hS : Sec4Setting G Ω) (δ : fixSet Ω (Subgroup.zpowers v)) :
    (δ : Ω) ∈ holtDelta G Ω α C.b ↔ (∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) ∧
      C.D.coord δ C.i ≠ C.D.coord C.a C.i ∧ C.D.coord δ C.i ≠ C.D.coord C.b C.i := by
  change (δ : Ω) ∈ holtDelta G Ω (C.a : Ω) C.b ↔ _
  rw [← hS.mem_holtDelta_centralizerImage_iff C.isPGroup
    (C.three_le hS) C.a_ne_b, ← C.coord_injective.mem_set_image, C.D.coord_holtDelta_eq,
    Set.mem_univ_pi]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have hj' := h j
      rw [C.coord_b_eq j hj, C.D.holtDelta_range_rho_self] at hj'
      exact hj'
    · have hi := h C.i
      rw [C.D.holtDelta_range_rho_eq_compl C.alt (Ne.symm C.coord_b_ne)] at hi
      simpa [not_or] using hi
  · rintro ⟨h1, h2, h3⟩ j
    by_cases hj : j = C.i
    · subst hj
      rw [C.D.holtDelta_range_rho_eq_compl C.alt (Ne.symm C.coord_b_ne)]
      simp [h2, h3]
    · rw [C.coord_b_eq j hj, C.D.holtDelta_range_rho_self]
      exact h1 j hj

private theorem eq_of_coord_eq (hS : Sec4Setting G Ω) {δ δ' : fixSet Ω (Subgroup.zpowers v)}
    (hδ : (δ : Ω) ∈ holtDelta G Ω α C.b) (hδ' : (δ' : Ω) ∈ holtDelta G Ω α C.b)
    (h : C.D.coord δ C.i = C.D.coord δ' C.i) : δ = δ' := by
  refine C.coord_injective (funext fun j => ?_)
  by_cases hj : j = C.i
  · subst hj
    exact h
  · rw [((C.mem_holtDelta_iff hS δ).mp hδ).1 j hj, ((C.mem_holtDelta_iff hS δ').mp hδ').1 j hj]

private theorem exists_mem_holtDelta_coord_eq (hS : Sec4Setting G Ω) {x : C.D.Ψc C.i}
    (hxa : x ≠ C.D.coord C.a C.i) (hxb : x ≠ C.D.coord C.b C.i) :
    ∃ δ : fixSet Ω (Subgroup.zpowers v), (δ : Ω) ∈ holtDelta G Ω α C.b ∧
      C.D.coord δ C.i = x := by
  obtain ⟨δ, hδ⟩ := C.D.exists_coord_eq_update C.a C.i x
  refine ⟨δ, (C.mem_holtDelta_iff hS δ).mpr ⟨fun j hj => ?_, ?_, ?_⟩, ?_⟩
  · rw [hδ, Function.update_of_ne hj]
  · rw [hδ, Function.update_self]
    exact hxa
  · rw [hδ, Function.update_self]
    exact hxb
  · rw [hδ, Function.update_self]

private theorem card_inter (hS : Sec4Setting G Ω) :
    Nat.card ↥(holtDelta G Ω α C.b ∩ fixSet Ω (Subgroup.zpowers v)) =
      Fintype.card (C.D.Ψc C.i) - 2 := by
  let F : ↥(holtDelta G Ω α C.b ∩ fixSet Ω (Subgroup.zpowers v)) →
      {x : C.D.Ψc C.i // x ≠ C.D.coord C.a C.i ∧ x ≠ C.D.coord C.b C.i} := fun δ =>
    ⟨C.D.coord ⟨δ, δ.2.2⟩ C.i, ((C.mem_holtDelta_iff hS ⟨δ, δ.2.2⟩).mp δ.2.1).2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun δ δ' h => ?_, fun x => ?_⟩
    · have := C.eq_of_coord_eq hS δ.2.1 δ'.2.1 (congrArg Subtype.val h)
      exact Subtype.ext (congrArg (fun z : fixSet Ω (Subgroup.zpowers v) => (z : Ω)) this)
    · obtain ⟨δ, hδ, hδx⟩ := C.exists_mem_holtDelta_coord_eq hS x.2.1 x.2.2
      exact ⟨⟨δ, hδ, δ.2⟩, Subtype.ext hδx⟩
  rw [Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hab : C.D.coord C.a C.i ≠ C.D.coord C.b C.i := Ne.symm C.coord_b_ne
  rw [show (Finset.univ.filter fun x : C.D.Ψc C.i =>
      x ≠ C.D.coord C.a C.i ∧ x ≠ C.D.coord C.b C.i) =
      Finset.univ \ {C.D.coord C.a C.i, C.D.coord C.b C.i} by ext x; simp,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair hab, Finset.card_univ]

private theorem exists_w (hS : Sec4Setting G Ω) :
    ∃ w ∈ longInvSwap G Ω α C.b, w ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) ∧
      w * v ∈ longInv G Ω := by
  obtain ⟨t, ht, u, hu, -, hc, htuv, -⟩ := C.hv
  have htC : t ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) :=
    mem_centralizer_zpowers_iff_commute'.mpr (htuv ▸ ((Commute.refl t).mul_left hc.symm))
  have hK := hS.star_typeLSection C.hv
  have hKB := hS.holtTheorem1Below_typeLSection C.hv
  have htK : centralizerImageElt (Ω := Ω) htC ∈
      longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    (hS.mem_longInv_centralizerImage_iff C.isPGroup (C.three_le hS) _).mpr
      ⟨t, ht.1, htC, fun _ => rfl⟩
  obtain ⟨x, hx⟩ := exists_not_mem_finset {C.D.coord C.a C.i, C.D.coord C.b C.i}
    (lt_of_le_of_lt (Finset.card_le_two) (by have := C.seven; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨δ, hδ, -⟩ := C.exists_mem_holtDelta_coord_eq hS hx.1 hx.2
  obtain ⟨s, hs, -⟩ := (hS.mem_holtDelta_centralizerImage_iff C.isPGroup (C.three_le hS)
    C.a_ne_b).mpr hδ
  obtain ⟨⟨_, c, rfl⟩, hk⟩ := exists_conj_eq_of_mem_longInv hK hKB htK hs.1
  have hcv : Commute v (c : G) := mem_centralizer_zpowers_iff_commute'.mp c.2
  refine ⟨(c : G) * t * (c : G)⁻¹, ⟨conj_mem_longInv ht.1 _, ?_⟩,
    mul_mem (mul_mem c.2 htC) (inv_mem c.2), ?_⟩
  · have h := congrArg (fun z : typeLSection G Ω v =>
      ((z : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) C.a : Ω)) hk
    rw [mul_smul, mul_smul]
    exact h.trans (congrArg Subtype.val hs.2)
  · have htv : t * v = u := by
      rw [← htuv, ← mul_assoc, mul_self_eq_one_of_mem_longInv ht.1, one_mul]
    have : (c : G) * t * (c : G)⁻¹ * v = (c : G) * u * (c : G)⁻¹ := by
      rw [mul_assoc _ (c : G)⁻¹, ← hcv.inv_right.eq, ← mul_assoc, mul_assoc (c : G) t, htv]
    rw [this]
    exact conj_mem_longInv hu.1 _

omit [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
private theorem exists_isPGroup_fixSet_K {A B : Set (C.D.Ψc C.i)} (hAB : A ⊆ B)
    (hA : Even (Nat.card ↥Aᶜ)) (hA2 : Nat.card ↥Aᶜ ≠ 2) (hB : Even (Nat.card ↥Bᶜ))
    (hB2 : Nat.card ↥Bᶜ ≠ 2) :
    ∃ P U : Subgroup (typeLSection G Ω v), U ≤ P ∧ IsPGroup 2 P ∧
      (∀ δ, δ ∈ fixSet (fixSet Ω (Subgroup.zpowers v)) P ↔
        (∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) ∧ C.D.coord δ C.i ∈ A) ∧
      (∀ δ, δ ∈ fixSet (fixSet Ω (Subgroup.zpowers v)) U ↔
        (∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) ∧ C.D.coord δ C.i ∈ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨VB, -, hVB⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
    (bot_le : ⊥ ≤ alternatingGroup (C.D.Ψc C.i) ⊓ fixingSubgroup (Perm (C.D.Ψc C.i)) B)
  obtain ⟨VA, hBA, hVA⟩ := exists_fusionIsSylowIn_ge (p := 2) hVB.2.1
    (hVB.1.trans (inf_le_inf_left _ (fixingSubgroup_antitone _ _ hAB)))
  have hFB := fixSet_eq_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup hB hB2 hVB
  have hFA := fixSet_eq_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup hA hA2 hVA
  obtain ⟨LB, -, hLB, hLBp, hLBm⟩ := C.D.exists_isPGroup_lift hVB.2.1
    (C.alt ▸ hVB.1.trans inf_le_left) IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  obtain ⟨LA, hLBA, hLA, hLAp, hLAm⟩ := C.D.exists_isPGroup_lift hVA.2.1
    (C.alt ▸ hVA.1.trans inf_le_left) hLBp hLB (by rw [hLBm]; exact hBA)
  have hZ : ∀ j, ∃ Z : Subgroup (jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))),
      Z ≤ (C.D.L j).subgroupOf _ ∧ IsPGroup 2 Z ∧
        fixSet (C.D.Ψc j) (Z.map (C.D.ρ j)) = {C.D.coord C.a j} := fun j => by
    obtain ⟨T, -, hT⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
      (bot_le : ⊥ ≤ C.D.M j ⊓ stabilizer (Perm (C.D.Ψc j)) (C.D.coord C.a j))
    obtain ⟨Z, -, hZL, hZp, hZm⟩ := C.D.exists_isPGroup_lift hT.2.1 (hT.1.trans inf_le_left)
      IsPGroup.of_bot bot_le (by rw [Subgroup.map_bot]; exact bot_le)
    have hF := (C.D.factor j).fixSet_eq_singleton (C.D.odd_card_Ψc j) hT
    exact ⟨Z, hZL, hZp, by rw [hZm]; exact hF⟩
  choose Z hZL hZp hZF using hZ
  classical
  let Q : Subgroup (jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) →
      C.D.ι → Subgroup (jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) :=
    fun L j => if j = C.i then L else Z j
  have hQL : ∀ L ≤ (C.D.L C.i).subgroupOf _, ∀ j, Q L j ≤ (C.D.L j).subgroupOf _ :=
    fun L hL j => by
      by_cases hj : j = C.i
      · subst hj; simpa [Q] using hL
      · simpa [Q, hj] using hZL j
  have hQp : ∀ L : Subgroup (jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))),
      IsPGroup 2 L → ∀ j, IsPGroup 2 (Q L j) := fun L hL j => by
    by_cases hj : j = C.i
    · rw [show Q L j = L by simp [Q, hj]]; exact hL
    · rw [show Q L j = Z j by simp [Q, hj]]; exact hZp j
  have hfix : ∀ L ≤ (C.D.L C.i).subgroupOf _, ∀ δ : fixSet Ω (Subgroup.zpowers v),
      δ ∈ fixSet (fixSet Ω (Subgroup.zpowers v)) (⨆ j, (Q L j).map (jHull _ _).subtype) ↔
        (∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) ∧
          C.D.coord δ C.i ∈ fixSet (C.D.Ψc C.i) (L.map (C.D.ρ C.i)) := fun L hL δ => by
    rw [mem_fixSet_iSup_iff]
    simp_rw [C.D.mem_fixSet_map_iff_of_le_L C.hO (hQL L hL _)]
    constructor
    · intro h
      refine ⟨fun j hj => ?_, by simpa [Q] using h C.i⟩
      have := h j
      simp only [Q, hj, ite_false, hZF j, Set.mem_singleton_iff] at this
      exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = C.i
      · subst hj; simpa [Q] using h2
      · simp only [Q, hj, ite_false, hZF j, Set.mem_singleton_iff]
        exact h1 j hj
  have hmapL : ∀ L ≤ (C.D.L C.i).subgroupOf _, ∀ j, (Q L j).map (jHull _ _).subtype ≤ C.D.L j :=
    fun L hL j _ ⟨q, hq, hqe⟩ => hqe ▸ Subgroup.mem_subgroupOf.mp (hQL L hL j hq)
  refine ⟨⨆ j, (Q LA j).map (jHull _ _).subtype, ⨆ j, (Q LB j).map (jHull _ _).subtype,
    iSup_mono fun j => Subgroup.map_mono ?_,
    HoltData.isPGroup_iSup_of_le_L (D := C.D) C.hO (hmapL LA hLA)
      (fun j => (hQp LA hLAp j).map _), fun δ => ?_, fun δ => ?_⟩
  · by_cases hj : j = C.i
    · subst hj; simpa [Q] using hLBA
    · simp [Q, hj]
  · rw [hfix LA hLA, hLAm, hFA]
  · rw [hfix LB hLB, hLBm, hFB]

omit [DecidableEq Ω] [FaithfulSMul G Ω] in
private theorem exists_isPGroup_fixSet {A B : Set (C.D.Ψc C.i)} (hAB : A ⊆ B)
    (hA : Even (Nat.card ↥Aᶜ)) (hA2 : Nat.card ↥Aᶜ ≠ 2) (hB : Even (Nat.card ↥Bᶜ))
    (hB2 : Nat.card ↥Bᶜ ≠ 2) :
    ∃ P U : Subgroup G, U ≤ P ∧ IsPGroup 2 P ∧
      P ≤ Subgroup.centralizer (Subgroup.zpowers v : Set G) ∧ v ∈ U ∧
      (∀ ω : Ω, ω ∈ fixSet Ω P ↔ ∃ h : ω ∈ fixSet Ω (Subgroup.zpowers v),
        (∀ j, j ≠ C.i → C.D.coord ⟨ω, h⟩ j = C.D.coord C.a j) ∧ C.D.coord ⟨ω, h⟩ C.i ∈ A) ∧
      (∀ ω : Ω, ω ∈ fixSet Ω U ↔ ∃ h : ω ∈ fixSet Ω (Subgroup.zpowers v),
        (∀ j, j ≠ C.i → C.D.coord ⟨ω, h⟩ j = C.D.coord C.a j) ∧ C.D.coord ⟨ω, h⟩ C.i ∈ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, U, hUP, hPp, hPF, hUF⟩ := C.exists_isPGroup_fixSet_K hAB hA hA2 hB hB2
  set Z := Subgroup.centralizer (Subgroup.zpowers v : Set G)
  set f : Z →* typeLSection G Ω v :=
    (MulAction.toPermHom Z (fixSet Ω (Subgroup.zpowers v))).rangeRestrict
  have hvZ : v ∈ Z := mem_centralizer_zpowers_iff_commute'.mpr (Commute.refl v)
  set E := Subgroup.zpowers (⟨v, hvZ⟩ : Z)
  have hEp : IsPGroup 2 E := isPGroup_zpowers_of_orderOf_eq_two (by
    rw [← Subgroup.orderOf_coe]; exact C.hv.orderOf_eq_two)
  have hf1 : f ⟨v, hvZ⟩ = 1 := Subtype.ext (Equiv.ext fun ω => Subtype.ext
    (mem_fixSet_zpowers_iff'.mp ω.2))
  have hEf : ∀ R : Subgroup (typeLSection G Ω v), E.map f ≤ R := fun R =>
    Subgroup.map_le_iff_le_comap.mpr (Subgroup.zpowers_le.mpr (by
      show f ⟨v, hvZ⟩ ∈ R
      rw [hf1]; exact one_mem R))
  have htop : ∀ R : Subgroup (typeLSection G Ω v), R ≤ (⊤ : Subgroup Z).map f := fun R => by
    rw [Subgroup.map_top_of_surjective f (MonoidHom.rangeRestrict_surjective _)]
    exact le_top
  obtain ⟨U', hEU', -, hU'p, hU'm⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le f
    (hPp.to_le hUP) (htop U) hEp le_top (hEf U)
  obtain ⟨P', hUP', -, hP'p, hP'm⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le f hPp (htop P)
    hU'p le_top (by rw [hU'm]; exact hUP)
  have key : ∀ R : Subgroup Z, E ≤ R → ∀ R' : Subgroup (typeLSection G Ω v), R.map f = R' →
      ∀ ω : Ω, ω ∈ fixSet Ω (R.map Z.subtype) ↔ ∃ h : ω ∈ fixSet Ω (Subgroup.zpowers v),
        (⟨ω, h⟩ : fixSet Ω (Subgroup.zpowers v)) ∈ fixSet (fixSet Ω (Subgroup.zpowers v)) R' := by
    rintro R hER R' rfl ω
    constructor
    · intro hω
      have hvω : v • ω = ω := hω v ⟨⟨v, hvZ⟩, hER (Subgroup.mem_zpowers _), rfl⟩
      refine ⟨mem_fixSet_zpowers_iff'.mpr hvω, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      exact Subtype.ext (hω (r : G) ⟨r, hr, rfl⟩)
    · rintro ⟨h, hω⟩ _ ⟨r, hr, rfl⟩
      exact congrArg Subtype.val (hω (f r) ⟨r, hr, rfl⟩)
  refine ⟨P'.map Z.subtype, U'.map Z.subtype, Subgroup.map_mono hUP', hP'p.map _,
    Subgroup.map_subtype_le _, ⟨⟨v, hvZ⟩, hEU' (Subgroup.mem_zpowers _), rfl⟩,
    fun ω => ?_, fun ω => ?_⟩
  · rw [key P' (hEU'.trans hUP') P hP'm]
    exact exists_congr fun h => hPF _
  · rw [key U' hEU' U hU'm]
    exact exists_congr fun h => hUF _

end L48Config

variable (G Ω) in
structure L48ConfigW (α : Ω) (v : G) extends L48Config G Ω α v where
  w : G
  w_mem : w ∈ longInvSwap G Ω α b
  w_comm : w ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G)
  wv_mem : w * v ∈ longInv G Ω
  γ : Ω
  w_fix : w • γ = γ

namespace L48ConfigW

variable {α : Ω} {v : G} (C : L48ConfigW G Ω α v)

private theorem w_unique {ω : Ω} (h : C.w • ω = ω) : ω = C.γ :=
  C.w_mem.1.2.unique h C.w_fix

private theorem commute_v : Commute v C.w := mem_centralizer_zpowers_iff_commute'.mp C.w_comm

private theorem v_smul_γ : v • C.γ = C.γ :=
  C.w_unique (by rw [← mul_smul, ← C.commute_v.eq, mul_smul, C.w_fix])

private theorem γ_mem_fixSet : C.γ ∈ fixSet Ω (Subgroup.zpowers v) := by
  rw [fixSet_zpowers, mem_fixedBy]
  exact C.v_smul_γ

theorem γ_mem_holtDelta : C.γ ∈ holtDelta G Ω α C.b := ⟨C.w, C.w_mem, C.w_fix⟩

private theorem wv_fix : (C.w * v) • C.γ = C.γ := by rw [mul_smul, C.v_smul_γ, C.w_fix]

private theorem wv_unique {ω : Ω} (h : (C.w * v) • ω = ω) : ω = C.γ :=
  C.wv_mem.2.unique h C.wv_fix

private theorem wv_mem_swap : C.w * v ∈ longInvSwap G Ω α C.b :=
  ⟨C.wv_mem, by rw [mul_smul, C.hv.smul_eq, C.w_mem.2]⟩

private theorem v_mem_closure : v ∈ Subgroup.closure (longInvSwap G Ω α C.b) := by
  have h : C.w * (C.w * v) = v := by
    rw [← mul_assoc, mul_self_eq_one_of_mem_longInv C.w_mem.1, one_mul]
  have h' := mul_mem (Subgroup.subset_closure C.w_mem) (Subgroup.subset_closure C.wv_mem_swap)
  rwa [h] at h'

private abbrev γΦ (C : L48ConfigW G Ω α v) : fixSet Ω (Subgroup.zpowers v) :=
  ⟨C.γ, C.γ_mem_fixSet⟩

private abbrev sK (C : L48ConfigW G Ω α v) : typeLSection G Ω v :=
  centralizerImageElt (Ω := Ω) C.w_comm

variable [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω]

private theorem sK_mem (hS : Sec4Setting G Ω) :
    C.sK ∈ longInvSwap (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) C.a C.b :=
  (hS.mem_longInvSwap_centralizerImage_iff C.isPGroup (C.three_le hS) _).mpr
    ⟨C.w, C.w_mem, C.w_comm, fun _ => rfl⟩

private abbrev sH (C : L48ConfigW G Ω α v) (hS : Sec4Setting G Ω) :
    jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
  ⟨C.sK, mem_jHull_of_mem_longInv (C.sK_mem hS).1⟩

private theorem γ_line (hS : Sec4Setting G Ω) :
    ∀ j, j ≠ C.i → C.D.coord C.γΦ j = C.D.coord C.a j :=
  ((C.mem_holtDelta_iff hS C.γΦ).mp C.γ_mem_holtDelta).1

private theorem rho_sH_coord_a (hS : Sec4Setting G Ω) {j : C.D.ι} (hj : j ≠ C.i) :
    C.D.ρ j (C.sH hS) (C.D.coord C.a j) = C.D.coord C.a j := by
  rw [← C.γ_line hS j hj, ← C.D.coord_smul]
  congr 2
  exact Subtype.ext C.w_fix

private theorem coord_smul_line (hS : Sec4Setting G Ω)
    {u : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))}
    (hu : ∀ j, j ≠ C.i → C.D.ρ j u = C.D.ρ j (C.sH hS)) {δ : fixSet Ω (Subgroup.zpowers v)}
    (hδ : ∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) :
    C.D.coord ((u : typeLSection G Ω v) • δ) =
      Function.update (C.D.coord δ) C.i (C.D.ρ C.i u (C.D.coord δ C.i)) := by
  funext j
  rw [C.D.coord_smul]
  by_cases hj : j = C.i
  · subst hj
    rw [Function.update_self]
  · rw [Function.update_of_ne hj, hu j hj, hδ j hj, C.rho_sH_coord_a hS hj]

private theorem exists_lift (hS : Sec4Setting G Ω) {y : Perm (C.D.Ψc C.i)}
    (hy : y ∈ longInv (Perm (C.D.Ψc C.i)) (C.D.Ψc C.i))
    (hya : y (C.D.coord C.a C.i) = C.D.coord C.b C.i) :
    ∃ g ∈ longInvSwap G Ω α C.b, g ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) ∧
      ∃ u : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)),
        (∀ ω : fixSet Ω (Subgroup.zpowers v), (((u : typeLSection G Ω v) :
          Perm (fixSet Ω (Subgroup.zpowers v))) ω : Ω) = g • (ω : Ω)) ∧
        C.D.ρ C.i u = y ∧ ∀ j, j ≠ C.i → C.D.ρ j u = C.D.ρ j (C.sH hS) := by
  have hsH := C.sK_mem hS
  have hrange : y ∈ (C.D.ρ C.i).range := by
    have hA : alternatingGroup (C.D.Ψc C.i) ≤ (C.D.ρ C.i).range :=
      C.alt ▸ Subgroup.map_le_range _ _
    exact longInv_perm_subset_of_alternatingGroup_le hA ⟨C.sH hS, rfl⟩
      (C.D.rho_mem_longInv hsH.1 C.i) hy
  let z : ∀ j, Perm (C.D.Ψc j) := Function.update (fun j => C.D.ρ j (C.sH hS)) C.i y
  have hz1 : ∀ j, z j ∈ (C.D.ρ j).range := fun j => by
    by_cases hj : j = C.i
    · subst hj; simp only [z, Function.update_self]; exact hrange
    · simp only [z, Function.update_of_ne hj]; exact ⟨_, rfl⟩
  have hz2 : ∀ j, z j ∈ longInv (Perm (C.D.Ψc j)) (C.D.Ψc j) := fun j => by
    by_cases hj : j = C.i
    · subst hj; simp only [z, Function.update_self]; exact hy
    · simp only [z, Function.update_of_ne hj]; exact C.D.rho_mem_longInv hsH.1 j
  have hz3 : ∀ j, z j (C.D.coord C.a j) = C.D.coord C.b j := fun j => by
    by_cases hj : j = C.i
    · subst hj; simp only [z, Function.update_self]; exact hya
    · simp only [z, Function.update_of_ne hj]
      rw [← C.D.coord_smul]
      exact congrArg (C.D.coord · j) hsH.2
  obtain ⟨u, hu, hρu⟩ := C.D.exists_mem_longInvSwap_rho_eq z hz1 hz2 hz3
  obtain ⟨g, hg, hgC, hgu⟩ :=
    (hS.mem_longInvSwap_centralizerImage_iff C.isPGroup (C.three_le hS) _).mp hu
  refine ⟨g, hg, hgC, u, hgu, ?_, fun j hj => ?_⟩
  · rw [hρu C.i]; simp only [z, Function.update_self]
  · rw [hρu j]; simp only [z, Function.update_of_ne hj]

private theorem exists_commuting (hS : Sec4Setting G Ω) {x : fixSet Ω (Subgroup.zpowers v)}
    (hx : (x : Ω) ∈ holtDelta G Ω α C.b) (hxγ : x ≠ C.γΦ) :
    ∃ g ∈ longInvSwap G Ω α C.b, g ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) ∧
      g • C.γ = C.γ ∧ (∀ ω ∈ fixSet Ω (Subgroup.zpowers v), C.w • g • ω = g • C.w • ω) ∧
      C.w • g • (x : Ω) ≠ x := by
  have hsH := C.sK_mem hS
  have hsγ : C.sK ∈ longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) C.γΦ :=
    ⟨hsH.1, Subtype.ext C.w_fix⟩
  have hsi : C.D.ρ C.i (C.sH hS) ∈
      longInvAt (Perm (C.D.Ψc C.i)) (C.D.Ψc C.i) (C.D.coord C.γΦ C.i) :=
    C.D.rho_mem_longInvAt hsγ C.i
  have hsa : C.D.ρ C.i (C.sH hS) (C.D.coord C.a C.i) = C.D.coord C.b C.i := by
    rw [← C.D.coord_smul]
    exact congrArg (C.D.coord · C.i) hsH.2
  obtain ⟨hxl, hxa, hxb⟩ := (C.mem_holtDelta_iff hS x).mp hx
  have hxγ' : C.D.coord x C.i ≠ C.D.coord C.γΦ C.i := fun h =>
    hxγ (C.eq_of_coord_eq hS hx C.γ_mem_holtDelta h)
  obtain ⟨e, -, hcomm, hea, heγ, hep, hse⟩ :=
    exists_commute_mul_mem_longInv hsi C.seven hsa hxa hxb hxγ'
  obtain ⟨g, hg, hgC, u, hgu, hui, huj⟩ := C.exists_lift hS hse (by
    rw [Perm.mul_apply, hea, hsa])
  have huγ : (u : typeLSection G Ω v) • C.γΦ = C.γΦ := by
    refine C.coord_injective ?_
    rw [C.coord_smul_line hS huj (C.γ_line hS), hui, Perm.mul_apply, heγ]
    have h1 := hsi.2
    rw [Perm.smul_def] at h1
    rw [h1, Function.update_eq_self]
  have hsu : C.sH hS * u = u * C.sH hS := by
    have h1 := HoltData.eq_one_of_forall_rho_eq_one (D := C.D) C.hO
      (h := C.sH hS * u * (u * C.sH hS)⁻¹) fun j => by
      rw [map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one]
      by_cases hj : j = C.i
      · subst hj
        rw [hui, mul_assoc _ e, ← hcomm]
      · rw [huj j hj]
    exact mul_inv_eq_one.mp h1
  have hact : ∀ ω : fixSet Ω (Subgroup.zpowers v), C.w • g • (ω : Ω) =
      (((C.sH hS * u : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) :
        typeLSection G Ω v) • ω : fixSet Ω (Subgroup.zpowers v)) := fun ω => by
    rw [← hgu ω]
    rfl
  refine ⟨g, hg, hgC, ?_, fun ω hω => ?_, ?_⟩
  · rw [← hgu C.γΦ]
    exact congrArg Subtype.val huγ
  · rw [hact ⟨ω, hω⟩, hsu]
    show (((u : typeLSection G Ω v) : Perm (fixSet Ω (Subgroup.zpowers v)))
      (C.sK • (⟨ω, hω⟩ : fixSet Ω (Subgroup.zpowers v))) : Ω) = g • C.w • ω
    rw [hgu]
    rfl
  · rw [hact x]
    intro h
    have h2 := congrArg (C.D.coord · C.i) (Subtype.ext h :
      (((C.sH hS * u : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) :
        typeLSection G Ω v) • x : fixSet Ω (Subgroup.zpowers v)) = x)
    rw [C.D.coord_smul, map_mul, Perm.mul_apply, hui, Perm.mul_apply,
      ← Perm.mul_apply (C.D.ρ C.i (C.sH hS)), mul_self_eq_one_of_mem_longInv hsi.1,
      Perm.one_apply] at h2
    exact hep h2

private theorem exists_smul_eq_line (hS : Sec4Setting G Ω) {x y : fixSet Ω (Subgroup.zpowers v)}
    (hx : (x : Ω) ∈ holtDelta G Ω α C.b) (hy : (y : Ω) ∈ holtDelta G Ω α C.b) (hxγ : x ≠ C.γΦ)
    (hyγ : y ≠ C.γΦ) (hxy : x ≠ y) :
    ∃ g ∈ longInvSwap G Ω α C.b, g ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) ∧
      g • C.γ = C.γ ∧ g • (x : Ω) = y := by
  obtain ⟨hxl, hxa, hxb⟩ := (C.mem_holtDelta_iff hS x).mp hx
  obtain ⟨hyl, hya, hyb⟩ := (C.mem_holtDelta_iff hS y).mp hy
  obtain ⟨-, hγa, hγb⟩ := (C.mem_holtDelta_iff hS C.γΦ).mp C.γ_mem_holtDelta
  have hxγ' : C.D.coord x C.i ≠ C.D.coord C.γΦ C.i := fun h =>
    hxγ (C.eq_of_coord_eq hS hx C.γ_mem_holtDelta h)
  have hyγ' : C.D.coord y C.i ≠ C.D.coord C.γΦ C.i := fun h =>
    hyγ (C.eq_of_coord_eq hS hy C.γ_mem_holtDelta h)
  have hxy' : C.D.coord x C.i ≠ C.D.coord y C.i := fun h => hxy (C.eq_of_coord_eq hS hx hy h)
  have hab : C.D.coord C.a C.i ≠ C.D.coord C.b C.i := Ne.symm C.coord_b_ne
  obtain ⟨z, hz, hza, hzx⟩ := exists_mem_longInvAt_perm_apply_eq_apply_eq (C.D.odd_card_Ψc C.i)
    hab (Ne.symm hγa) (Ne.symm hxa) (Ne.symm hya) (Ne.symm hγb) (Ne.symm hxb) (Ne.symm hyb)
    (Ne.symm hxγ') (Ne.symm hyγ') hxy'
  obtain ⟨g, hg, hgC, u, hgu, hui, huj⟩ := C.exists_lift hS hz.1 hza
  refine ⟨g, hg, hgC, ?_, ?_⟩
  · rw [← hgu C.γΦ]
    have h : (u : typeLSection G Ω v) • C.γΦ = C.γΦ := by
      refine C.coord_injective ?_
      rw [C.coord_smul_line hS huj (C.γ_line hS), hui]
      have h1 := hz.2
      rw [Perm.smul_def] at h1
      rw [h1, Function.update_eq_self]
    exact congrArg Subtype.val h
  · rw [← hgu x]
    have h : (u : typeLSection G Ω v) • x = y := by
      refine C.coord_injective ?_
      rw [C.coord_smul_line hS huj hxl, hui, hzx]
      funext j
      by_cases hj : j = C.i
      · subst hj
        rw [Function.update_self]
      · rw [Function.update_of_ne hj, hxl j hj, hyl j hj]
    exact congrArg Subtype.val h

omit [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
private theorem w_mem_stab : C.w ∈ stabilizer G ({α, (C.b : Ω)} : Set Ω) :=
  closure_longInvSwap_le_stabilizer_pair α _ (Subgroup.subset_closure C.w_mem)

omit [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
private theorem v_mem_stab : v ∈ stabilizer G ({α, (C.b : Ω)} : Set Ω) :=
  closure_longInvSwap_le_stabilizer_pair α _ C.v_mem_closure

omit [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
include C in
private theorem v_mul_self : v * v = 1 := by
  rw [← sq, ← C.hv.orderOf_eq_two, pow_orderOf_eq_one]

abbrev γΔ (C : L48ConfigW G Ω α v) : holtDelta G Ω α C.b := ⟨C.γ, C.γ_mem_holtDelta⟩

private theorem five_le_card_holtDelta (hS : Sec4Setting G Ω) :
    5 ≤ Nat.card (holtDelta G Ω α C.b) := by
  have h1 := C.card_inter hS
  have h2 : Nat.card ↥(holtDelta G Ω α C.b ∩ fixSet Ω (Subgroup.zpowers v)) ≤
      Nat.card (holtDelta G Ω α C.b) := Nat.card_mono (Set.toFinite _) Set.inter_subset_left
  have := C.seven
  omega

private theorem jOddCore_eq_bot (hS : Sec4Setting G Ω) :
    jOddCore (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b) = ⊥ := by
  set N := jOddCore (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b)
  have hN : Odd (Nat.card N) := odd_card_jOddCore
  set wD : twoPointSection G Ω α C.b := twoPointElt C.w_mem_stab
  set vD : twoPointSection G Ω α C.b := twoPointElt C.v_mem_stab
  have hwD : ∀ δ : holtDelta G Ω α C.b, ((wD • δ : holtDelta G Ω α C.b) : Ω) = C.w • (δ : Ω) :=
    fun _ => rfl
  have hvD : ∀ δ : holtDelta G Ω α C.b, ((vD • δ : holtDelta G Ω α C.b) : Ω) = v • (δ : Ω) :=
    fun _ => rfl
  have hw2 : ∀ δ : holtDelta G Ω α C.b, wD • wD • δ = δ := fun δ => Subtype.ext (by
    rw [hwD, hwD, ← mul_smul, mul_self_eq_one_of_mem_longInv C.w_mem.1, one_smul])
  have hF := ncard_fixed_orbit_mul (N := N) hN (γ := C.γΔ) (x := wD) (y := vD)
    (Subtype.ext C.w_fix) (Subtype.ext C.v_smul_γ) (fun δ _ => hw2 δ)
    (fun δ _ => Subtype.ext (by rw [hvD, hvD, ← mul_smul, C.v_mul_self, one_smul]))
    (fun δ _ => Subtype.ext (by rw [hwD, hvD, hvD, hwD, ← mul_smul, ← mul_smul, C.commute_v.eq]))
  have e1 : {δ | δ ∈ orbit N C.γΔ ∧ wD • δ = δ}.ncard = 1 :=
    ncard_setOf_eq_one (mem_orbit_self _) (Subtype.ext C.w_fix) (fun δ _ h =>
      Subtype.ext (C.w_unique (congrArg Subtype.val h)))
  have e3 : {δ | δ ∈ orbit N C.γΔ ∧ wD • vD • δ = δ}.ncard = 1 :=
    ncard_setOf_eq_one (mem_orbit_self _) (Subtype.ext (by
      show C.w • v • C.γ = C.γ
      rw [C.v_smul_γ, C.w_fix])) (fun δ _ h => Subtype.ext (C.wv_unique (by
        rw [mul_smul]; exact congrArg Subtype.val h)))
  have e4 : {δ | δ ∈ orbit N C.γΔ ∧ wD • δ = δ ∧ vD • δ = δ}.ncard = 1 :=
    ncard_setOf_eq_one (mem_orbit_self _) ⟨Subtype.ext C.w_fix, Subtype.ext C.v_smul_γ⟩
      (fun δ _ h => Subtype.ext (C.w_unique (congrArg Subtype.val h.1)))
  rw [e1, e3, e4, one_mul, mul_one, one_pow, mul_one] at hF
  have hbΦ := forall_of_ncard_setOf_eq hF
  have hb1 : ∀ δ ∈ orbit N C.γΔ, δ = C.γΔ := by
    intro δ hδ
    by_contra hne
    have hδΦ : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) :=
      mem_fixSet_zpowers_iff'.mpr (congrArg Subtype.val (hbΦ δ hδ))
    have hxγ : (⟨δ, hδΦ⟩ : fixSet Ω (Subgroup.zpowers v)) ≠ C.γΦ := fun h =>
      hne (Subtype.ext (show (δ : Ω) = C.γ from congrArg Subtype.val h))
    obtain ⟨g, hg, -, hgγ, hcomm, hmove⟩ := C.exists_commuting hS δ.2 hxγ
    set gD : twoPointSection G Ω α C.b :=
      twoPointElt (closure_longInvSwap_le_stabilizer_pair α _ (Subgroup.subset_closure hg))
    have hgD : ∀ δ : holtDelta G Ω α C.b, ((gD • δ : holtDelta G Ω α C.b) : Ω) = g • (δ : Ω) :=
      fun _ => rfl
    have hBW := ncard_fixed_orbit_mul (N := N) hN (γ := C.γΔ) (x := wD) (y := gD)
      (Subtype.ext C.w_fix) (Subtype.ext hgγ) (fun δ _ => hw2 δ)
      (fun δ _ => Subtype.ext (by
        rw [hgD, hgD, ← mul_smul, mul_self_eq_one_of_mem_longInv hg.1, one_smul]))
      (fun δ' hδ' => Subtype.ext (by
        rw [hwD, hgD, hgD, hwD]
        exact hcomm _ (mem_fixSet_zpowers_iff'.mpr (congrArg Subtype.val (hbΦ δ' hδ')))))
    have f2 : {δ | δ ∈ orbit N C.γΔ ∧ gD • δ = δ}.ncard = 1 :=
      ncard_setOf_eq_one (mem_orbit_self _) (Subtype.ext hgγ) (fun δ _ h =>
        Subtype.ext (hg.1.2.unique (congrArg Subtype.val h) hgγ))
    have f4 : {δ | δ ∈ orbit N C.γΔ ∧ wD • δ = δ ∧ gD • δ = δ}.ncard = 1 :=
      ncard_setOf_eq_one (mem_orbit_self _) ⟨Subtype.ext C.w_fix, Subtype.ext hgγ⟩
        (fun δ _ h => Subtype.ext (C.w_unique (congrArg Subtype.val h.1)))
    rw [e1, f2, f4, one_mul, one_mul, one_pow, mul_one] at hBW
    exact hmove (congrArg Subtype.val (forall_of_ncard_setOf_eq hBW δ hδ))
  have hle : N ≤ stabilizer (twoPointSection G Ω α C.b) C.γΔ := fun n hn =>
    mem_stabilizer_iff.mpr (hb1 _ (mem_orbit C.γΔ (⟨n, hn⟩ : N)))
  have hstar := hS.star_twoPoint C.ne (by have := C.five_le_card_holtDelta hS; omega)
  have := hstar.isPretransitive
  exact eq_bot_of_normal_le_stabilizer hle

private abbrev hullElt (C : L48ConfigW G Ω α v) (hS : Sec4Setting G Ω) {c : G}
    (hc : c ∈ Subgroup.closure (longInvSwap G Ω α C.b)) :
    jHull (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b) :=
  ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α _ hc), twoPointElt_mem_jHull hS.star hc⟩

omit [FaithfulSMul G Ω] in
private theorem coord_hullElt_smul (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b)) {c : G}
    (hc : c ∈ Subgroup.closure (longInvSwap G Ω α C.b)) {δ δ' : holtDelta G Ω α C.b}
    (h : c • (δ : Ω) = δ') (j : D'.ι) :
    D'.ρ j (C.hullElt hS hc) (D'.coord δ j) = D'.coord δ' j := by
  rw [← D'.coord_smul]
  congr 2
  exact Subtype.ext h

omit [FaithfulSMul G Ω] in
private theorem mem_fixSet_iff_rho (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b))
    (hO' : jOddCore (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b) = ⊥)
    (δ : holtDelta G Ω α C.b) :
    (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ↔
      ∀ j, D'.ρ j (C.hullElt hS C.v_mem_closure) (D'.coord δ j) = D'.coord δ j := by
  rw [mem_fixSet_zpowers_iff']
  constructor
  · intro h j
    exact C.coord_hullElt_smul hS D' C.v_mem_closure h j
  · intro h
    have h' : D'.coord ((C.hullElt hS C.v_mem_closure : twoPointSection G Ω α C.b) • δ) =
        D'.coord δ := funext fun j => by rw [D'.coord_smul]; exact h j
    exact congrArg Subtype.val (D'.coord_injective hO' h')

private theorem exists_line (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b))
    (hO' : jOddCore (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b) = ⊥) :
    ∃ i₁ : D'.ι, ∀ δ : holtDelta G Ω α C.b, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      ∀ j, j ≠ i₁ → D'.coord δ j = D'.coord C.γΔ j := by
  have hγΦ : (C.γΔ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := C.γ_mem_fixSet
  obtain ⟨-, hγa, hγb⟩ := (C.mem_holtDelta_iff hS C.γΦ).mp C.γ_mem_holtDelta
  obtain ⟨y, hy⟩ := exists_not_mem_finset
    {C.D.coord C.a C.i, C.D.coord C.b C.i, C.D.coord C.γΦ C.i}
    (lt_of_le_of_lt Finset.card_le_three (by have := C.seven; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨x, hx, hxy⟩ := C.exists_mem_holtDelta_coord_eq hS hy.1 hy.2.1
  have hxγ : (⟨x, hx⟩ : holtDelta G Ω α C.b) ≠ C.γΔ := fun h => hy.2.2 (by
    have h' : (x : Ω) = C.γ := congrArg Subtype.val h
    rw [← hxy]
    exact congrArg (C.D.coord · C.i) (Subtype.ext h' : x = C.γΦ))
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp fun h => hxγ (D'.coord_injective hO' h)
  refine ⟨i₁, fun δ hδ j hj => ?_⟩
  by_contra hne
  have hbox := C.mem_fixSet_iff_rho hS D' hO'
  obtain ⟨δ₁, hδ₁⟩ := D'.exists_coord_eq_update C.γΔ i₁ (D'.coord ⟨x, hx⟩ i₁)
  obtain ⟨δ₂, hδ₂⟩ := D'.exists_coord_eq_update C.γΔ j (D'.coord δ j)
  have hupd : ∀ (k : D'.ι) (δ' : holtDelta G Ω α C.b), (δ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      ∀ ε : holtDelta G Ω α C.b, D'.coord ε = Function.update (D'.coord C.γΔ) k (D'.coord δ' k) →
        (ε : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := fun k δ' hδ' ε hε => by
    refine (hbox ε).mpr fun l => ?_
    rw [hε]
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self]
      exact (hbox δ').mp hδ' l
    · rw [Function.update_of_ne hl]
      exact (hbox C.γΔ).mp hγΦ l
  have hδ₁Φ := hupd i₁ ⟨x, hx⟩ x.2 δ₁ hδ₁
  have hδ₂Φ := hupd j δ hδ δ₂ hδ₂
  have h1γ : δ₁ ≠ C.γΔ := fun h => hi₁ (by
    have := congrFun hδ₁ i₁
    rw [Function.update_self, h] at this
    exact this.symm)
  have h2γ : δ₂ ≠ C.γΔ := fun h => hne (by
    have := congrFun hδ₂ j
    rw [Function.update_self, h] at this
    exact this.symm)
  have h12 : δ₁ ≠ δ₂ := fun h => hne (by
    have e1 := congrFun hδ₁ j
    have e2 := congrFun hδ₂ j
    rw [Function.update_of_ne hj] at e1
    rw [Function.update_self, ← h, e1] at e2
    exact e2.symm)
  obtain ⟨g, hg, -, hgγ, hg12⟩ := C.exists_smul_eq_line hS (x := ⟨δ₁, hδ₁Φ⟩) (y := ⟨δ₂, hδ₂Φ⟩)
    δ₁.2 δ₂.2 (fun h => h1γ (Subtype.ext (show (δ₁ : Ω) = C.γ from congrArg Subtype.val h)))
    (fun h => h2γ (Subtype.ext (show (δ₂ : Ω) = C.γ from congrArg Subtype.val h)))
    (fun h => h12 (Subtype.ext
      (congrArg (fun z : fixSet Ω (Subgroup.zpowers v) => (z : Ω)) h)))
  have hgc := Subgroup.subset_closure hg
  have e1 := C.coord_hullElt_smul hS D' hgc (δ := δ₁) (δ' := δ₂) hg12 i₁
  have e2 := C.coord_hullElt_smul hS D' hgc (δ := C.γΔ) (δ' := C.γΔ) hgγ i₁
  rw [hδ₁, hδ₂, Function.update_self, Function.update_of_ne (Ne.symm hj)] at e1
  exact hi₁ ((D'.ρ i₁ (C.hullElt hS hgc)).injective (e1.trans e2.symm))

section Line

variable (hS : Sec4Setting G Ω) (D' : HoltData (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b))
  (hO' : jOddCore (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b) = ⊥) (i₁ : D'.ι)
  (hline : ∀ δ : holtDelta G Ω α C.b, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
    ∀ j, j ≠ i₁ → D'.coord δ j = D'.coord C.γΔ j)

include hO' hline in
omit [FaithfulSMul G Ω] in
private theorem fixed_eq_of_ne {j : D'.ι} (hj : j ≠ i₁) {p : D'.Ψc j}
    (hp : D'.ρ j (C.hullElt hS C.v_mem_closure) p = p) : p = D'.coord C.γΔ j := by
  obtain ⟨δ, hδ⟩ := D'.exists_coord_eq_update C.γΔ j p
  have hδΦ : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := (C.mem_fixSet_iff_rho hS D' hO' δ).mpr
    fun k => by
      rw [hδ]
      by_cases hk : k = j
      · subst hk; rw [Function.update_self]; exact hp
      · rw [Function.update_of_ne hk]
        exact (C.mem_fixSet_iff_rho hS D' hO' C.γΔ).mp C.γ_mem_fixSet k
  have := hline δ hδΦ j hj
  rwa [hδ, Function.update_self] at this

include hO' hline in
omit [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
private theorem eq_of_coord_i₁ {δ δ' : holtDelta G Ω α C.b}
    (hδ : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)) (hδ' : (δ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v))
    (h : D'.coord δ i₁ = D'.coord δ' i₁) : δ = δ' :=
  D'.coord_injective hO' (funext fun j => by
    by_cases hj : j = i₁
    · subst hj; exact h
    · rw [hline δ hδ j hj, hline δ' hδ' j hj])

include hO' hline in
private theorem card_fixed_i₁ :
    Fintype.card {p : D'.Ψc i₁ // D'.ρ i₁ (C.hullElt hS C.v_mem_closure) p = p} =
      Fintype.card (C.D.Ψc C.i) - 2 := by
  rw [← C.card_inter hS, ← Nat.card_eq_fintype_card]
  let F : {δ : holtDelta G Ω α C.b // (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)} →
      {p : D'.Ψc i₁ // D'.ρ i₁ (C.hullElt hS C.v_mem_closure) p = p} := fun δ =>
    ⟨D'.coord δ i₁, (C.mem_fixSet_iff_rho hS D' hO' δ).mp δ.2 i₁⟩
  have hF : Function.Bijective F := by
    refine ⟨fun δ δ' h => Subtype.ext (C.eq_of_coord_i₁ D' hO' i₁ hline δ.2 δ'.2
      (congrArg Subtype.val h)), fun p => ?_⟩
    obtain ⟨δ, hδ⟩ := D'.exists_coord_eq_update C.γΔ i₁ p
    refine ⟨⟨δ, (C.mem_fixSet_iff_rho hS D' hO' δ).mpr fun k => ?_⟩, Subtype.ext ?_⟩
    · rw [hδ]
      by_cases hk : k = i₁
      · subst hk; rw [Function.update_self]; exact p.2
      · rw [Function.update_of_ne hk]
        exact (C.mem_fixSet_iff_rho hS D' hO' C.γΔ).mp C.γ_mem_fixSet k
    · show D'.coord δ i₁ = p
      rw [hδ, Function.update_self]
  rw [← Nat.card_eq_of_bijective F hF]
  exact Nat.card_congr
    { toFun := fun δ => ⟨δ.1, δ.1.2, δ.2⟩
      invFun := fun ω => ⟨⟨ω, ω.2.1⟩, ω.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
private theorem jHull_ext {x y : jHull (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b)}
    (h : ∀ δ : holtDelta G Ω α C.b, (((x : twoPointSection G Ω α C.b) • δ :
      holtDelta G Ω α C.b) : Ω) = (((y : twoPointSection G Ω α C.b) • δ :
        holtDelta G Ω α C.b) : Ω)) : x = y :=
  Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (h δ)))

omit [FaithfulSMul G Ω] in
private theorem vH_eq :
    C.hullElt hS C.v_mem_closure = C.hullElt hS (Subgroup.subset_closure C.w_mem) *
      C.hullElt hS (Subgroup.subset_closure C.wv_mem_swap) :=
  C.jHull_ext fun δ => by
    show v • (δ : Ω) = C.w • (C.w * v) • (δ : Ω)
    rw [← mul_smul, ← mul_assoc, mul_self_eq_one_of_mem_longInv C.w_mem.1, one_mul]

omit [FaithfulSMul G Ω] in
private theorem vH_mul_self :
    C.hullElt hS C.v_mem_closure * C.hullElt hS C.v_mem_closure = 1 :=
  C.jHull_ext fun δ => by
    show v • v • (δ : Ω) = (δ : Ω)
    rw [← mul_smul, C.v_mul_self, one_smul]

private theorem rho_mem_longInv_of_mem {c : G} (hc : c ∈ longInvSwap G Ω α C.b) (j : D'.ι) :
    D'.ρ j (C.hullElt hS (Subgroup.subset_closure hc)) ∈ longInv (Perm (D'.Ψc j)) (D'.Ψc j) := by
  have h3 : 3 ≤ Nat.card (holtDelta G Ω α C.b) := by have := C.five_le_card_holtDelta hS; omega
  exact D'.rho_mem_longInv ((hS.mem_longInv_twoPointSection_iff C.ne h3 _).mpr
    ⟨c, hc, fun _ => rfl⟩) j

private theorem sign_rho_v (j : D'.ι) : sign (D'.ρ j (C.hullElt hS C.v_mem_closure)) = 1 := by
  rw [C.vH_eq hS, map_mul, Perm.sign_mul, sign_eq_of_mem_longInv_perm
    (C.rho_mem_longInv_of_mem hS D' C.w_mem j) (C.rho_mem_longInv_of_mem hS D' C.wv_mem_swap j),
    Int.units_mul_self]

include hS in
private theorem exists_ne_γΔ : ∃ x : holtDelta G Ω α C.b,
    (x : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧ x ≠ C.γΔ := by
  obtain ⟨-, hγa, hγb⟩ := (C.mem_holtDelta_iff hS C.γΦ).mp C.γ_mem_holtDelta
  obtain ⟨y, hy⟩ := exists_not_mem_finset
    {C.D.coord C.a C.i, C.D.coord C.b C.i, C.D.coord C.γΦ C.i}
    (lt_of_le_of_lt Finset.card_le_three (by have := C.seven; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨x, hx, hxy⟩ := C.exists_mem_holtDelta_coord_eq hS hy.1 hy.2.1
  refine ⟨⟨x, hx⟩, x.2, fun h => hy.2.2 ?_⟩
  have h' : (x : Ω) = C.γ := congrArg Subtype.val h
  rw [← hxy]
  exact congrArg (C.D.coord · C.i) (Subtype.ext h' : x = C.γΦ)

include hS hO' hline in
private theorem card_mod_four {j : D'.ι} (hj : j ≠ i₁) : Fintype.card (D'.Ψc j) % 4 = 1 := by
  set vj := D'.ρ j (C.hullElt hS C.v_mem_closure)
  have hfix : vj (D'.coord C.γΔ j) = D'.coord C.γΔ j :=
    (C.mem_fixSet_iff_rho hS D' hO' C.γΔ).mp C.γ_mem_fixSet j
  have hvj : vj ∈ longInv (Perm (D'.Ψc j)) (D'.Ψc j) := by
    refine ⟨orderOf_eq_prime ?_ fun h1 => ?_, D'.coord C.γΔ j, hfix,
      fun p hp => C.fixed_eq_of_ne hS D' hO' i₁ hline hj hp⟩
    · rw [sq, ← map_mul, C.vH_mul_self, map_one]
    · obtain ⟨p, hp⟩ := exists_not_mem_finset {D'.coord C.γΔ j}
        (by have := D'.five_le_card j; rw [Finset.card_singleton]; omega)
      exact hp (Finset.mem_singleton.mpr (C.fixed_eq_of_ne hS D' hO' i₁ hline hj
        (Equiv.ext_iff.mp h1 p)))
  rw [← mem_alternatingGroup_iff_of_mem_longInv_perm hvj, mem_alternatingGroup]
  exact C.sign_rho_v hS D' j

include hS hO' hline in
private theorem card_i₁_mod_four :
    Fintype.card (D'.Ψc i₁) % 4 = (Fintype.card (C.D.Ψc C.i) - 2) % 4 := by
  have hfix := C.card_fixed_i₁ hS D' hO' i₁ hline
  rw [Fintype.card_subtype] at hfix
  have h2 : (D'.ρ i₁ (C.hullElt hS C.v_mem_closure)) ^ 2 = 1 := by
    rw [sq, ← map_mul, C.vH_mul_self, map_one]
  have h4 := (mem_alternatingGroup_iff_four_dvd_card_support h2).mp (C.sign_rho_v hS D' i₁)
  have hsum := card_support_add_card_fixed (D'.ρ i₁ (C.hullElt hS C.v_mem_closure))
  omega

include hO' in
omit [FaithfulSMul G Ω] in
private theorem rho_v_ne_one (hr : Fintype.card D'.ι = 1)
    (hodd : Odd (Nat.card (twoPointKernel G Ω α C.b))) :
    D'.ρ i₁ (C.hullElt hS C.v_mem_closure) ≠ 1 := by
  intro h1
  have hall : ∀ k, D'.ρ k (C.hullElt hS C.v_mem_closure) = 1 := fun k => by
    rwa [Fintype.card_le_one_iff.mp hr.le k i₁]
  have hv1 := D'.eq_one_of_forall_rho_eq_one hO' hall
  have hvK : v ∈ twoPointKernel G Ω α C.b := by
    refine mem_twoPointKernel.mpr ⟨C.hv.smul_eq, mem_fixSet_zpowers_iff'.mp C.b.2,
      fun δ hδ => ?_⟩
    exact congrArg (fun x : jHull (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b) =>
      (((x : twoPointSection G Ω α C.b) • (⟨δ, hδ⟩ : holtDelta G Ω α C.b) :
        holtDelta G Ω α C.b) : Ω)) hv1
  have h2 : orderOf v ∣ Nat.card (twoPointKernel G Ω α C.b) := by
    have := orderOf_dvd_natCard (⟨v, hvK⟩ : twoPointKernel G Ω α C.b)
    rwa [← Subgroup.orderOf_coe] at this
  rw [C.hv.orderOf_eq_two] at h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

include hS hO' hline in
private theorem factor_eq_alt
    (hL42 : ∀ j, IsNaturalSE (D'.M j) → Fintype.card (D'.Ψc j) ≠ 5 →
      Odd (Nat.card (twoPointKernel G Ω α C.b)) ∧
        (jOddCore (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b) = ⊥ →
          Fintype.card D'.ι = 1))
    (j : D'.ι) : D'.M j = alternatingGroup (D'.Ψc j) := by
  rcases D'.factor j with ⟨hA, -⟩ | hSE
  · exact hA
  by_cases h5 : Fintype.card (D'.Ψc j) = 5
  · exact hSE.eq_alternatingGroup_of_card_eq_five h5
  obtain ⟨hodd, hr⟩ := hL42 j hSE h5
  have hr1 := hr hO'
  have hji : j = i₁ := Fintype.card_le_one_iff.mp hr1.le j i₁
  subst hji
  exfalso
  have hv1 := C.rho_v_ne_one hS D' hO' j hr1 hodd
  have hvM : D'.ρ j (C.hullElt hS C.v_mem_closure) ∈ D'.M j :=
    HoltData.rho_mem_M_of_isNaturalSE D' hSE _
  have hord : orderOf (⟨_, hvM⟩ : D'.M j) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, ← map_mul, C.vH_mul_self, map_one]) hv1
  obtain ⟨p, -, huniq⟩ := hSE.existsUnique_fixed hord
  obtain ⟨x, hxΦ, hxγ⟩ := C.exists_ne_γΔ hS
  have e1 := huniq _ ((C.mem_fixSet_iff_rho hS D' hO' C.γΔ).mp C.γ_mem_fixSet j)
  have e2 := huniq _ ((C.mem_fixSet_iff_rho hS D' hO' x).mp hxΦ j)
  exact hxγ (C.eq_of_coord_i₁ D' hO' j hline hxΦ C.γ_mem_fixSet (e2.trans e1.symm))

include hS hO' hline in
private theorem not_odd_of_five (hr : Fintype.card D'.ι = 1)
    (h5 : Fintype.card (D'.Ψc i₁) = 5) : ¬ Odd (Nat.card (twoPointKernel G Ω α C.b)) := by
  intro hodd
  apply C.rho_v_ne_one hS D' hO' i₁ hr hodd
  have hfix := C.card_fixed_i₁ hS D' hO' i₁ hline
  have h7 := C.seven
  ext p
  rw [Perm.one_apply]
  by_contra hne
  have := Fintype.card_subtype_lt
    (p := fun p => D'.ρ i₁ (C.hullElt hS C.v_mem_closure) p = p) (x := p) hne
  omega

include hS hO' hline in
private theorem mem_twoPointNormalizer_of_mem {g : G}
    (hgv : g ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G)) (hgα : g • α = α)
    (hgβ : g • (C.b : Ω) = C.b) : g ∈ twoPointNormalizer G Ω α C.b (D'.L i₁) := by
  have hg : g ∈ stabilizer G ({α, (C.b : Ω)} : Set Ω) :=
    stabilizer_inf_le_stabilizer_pair α _ (Subgroup.mem_inf.mpr
      ⟨mem_stabilizer_iff.mpr hgα, mem_stabilizer_iff.mpr hgβ⟩)
  set gD : twoPointSection G Ω α C.b := twoPointElt hg
  have hgΦ : ∀ δ : holtDelta G Ω α C.b, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      ((gD • δ : holtDelta G Ω α C.b) : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := fun δ hδ => by
    rw [mem_fixSet_zpowers_iff'] at hδ ⊢
    show v • g • (δ : Ω) = g • (δ : Ω)
    rw [← mul_smul, (mem_centralizer_zpowers_iff_commute'.mp hgv).eq, mul_smul, hδ]
  obtain ⟨σ, hσ⟩ := HoltData.conj_L D' gD
  obtain ⟨x, hxΦ, hxγ⟩ := C.exists_ne_γΔ hS
  have := (D'.factor i₁).isPretransitive
  obtain ⟨m, hm⟩ := exists_smul_eq (D'.M i₁) (D'.coord C.γΔ i₁) (D'.coord x i₁)
  obtain ⟨h, hhL, hhm⟩ := D'.mem_M.mp m.2
  have hhx : (h : twoPointSection G Ω α C.b) • C.γΔ = x := by
    refine D'.coord_injective hO' (funext fun k => ?_)
    rw [D'.coord_smul]
    by_cases hk : k = i₁
    · subst hk
      rw [hhm]
      exact hm
    · rw [D'.rho_eq_one_of_mem_L (Ne.symm hk) hhL, Perm.one_apply, hline x hxΦ k hk]
  have hσi : σ i₁ = i₁ := by
    by_contra hne
    have hconj : gD * (h : twoPointSection G Ω α C.b) * gD⁻¹ ∈ D'.L (σ i₁) := by
      rw [hσ i₁]
      exact ⟨_, hhL, rfl⟩
    have h1 := D'.rho_eq_one_of_mem_L (h := ⟨_, D'.L_le _ hconj⟩) hne hconj
    have h2 : D'.coord (gD • x) i₁ = D'.coord (gD • C.γΔ) i₁ := by
      rw [← hhx, ← mul_smul, show gD * (h : twoPointSection G Ω α C.b) =
        (gD * (h : twoPointSection G Ω α C.b) * gD⁻¹) * gD by group, mul_smul]
      exact (D'.coord_smul ⟨_, D'.L_le _ hconj⟩ (gD • C.γΔ) i₁).trans (by rw [h1, Perm.one_apply])
    exact hxγ (smul_left_cancel _ (C.eq_of_coord_i₁ D' hO' i₁ hline (hgΦ x hxΦ)
      (hgΦ C.γΔ C.γ_mem_fixSet) h2))
  have hL := hσ i₁
  rw [hσi] at hL
  refine mem_twoPointNormalizer.mpr ⟨hg, Subgroup.mem_normalizer_iff.mpr fun l => ?_⟩
  change l ∈ D'.L i₁ ↔ gD * l * gD⁻¹ ∈ D'.L i₁
  constructor
  · intro hl
    rw [hL]
    exact ⟨l, hl, rfl⟩
  · intro hl
    rw [hL] at hl
    obtain ⟨l', hl', hll'⟩ := hl
    have : l' = l := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj]
        using hll'
    exact this ▸ hl'

omit [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
private theorem eq_of_line {δ ε : fixSet Ω (Subgroup.zpowers v)}
    (hδ : ∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j)
    (hε : ∀ j, j ≠ C.i → C.D.coord ε j = C.D.coord C.a j)
    (h : C.D.coord δ C.i = C.D.coord ε C.i) : δ = ε :=
  C.coord_injective (funext fun j => by
    by_cases hj : j = C.i
    · subst hj; exact h
    · rw [hδ j hj, hε j hj])

omit [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
private theorem b_line : ∀ j, j ≠ C.i → C.D.coord C.b j = C.D.coord C.a j := C.coord_b_eq

include hS hO' hline in
private theorem exists_sylow {B : Finset (C.D.Ψc C.i)}
    (hAB : ({C.D.coord C.a C.i, C.D.coord C.b C.i, C.D.coord C.γΦ C.i} : Finset _) ⊆ B)
    (hB : Even (Nat.card ↥((B : Set (C.D.Ψc C.i))ᶜ)))
    (hB2 : Nat.card ↥((B : Set (C.D.Ψc C.i))ᶜ) ≠ 2) :
    ∃ S : Subgroup G, fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G (C.b : Ω) ⊓
        stabilizer G C.γ) ∧
      Nat.card (fixSet Ω (S ⊓ twoPointNormalizer G Ω α C.b (D'.L i₁))) = 3 ∧
      ∃ U : Subgroup G, U ≤ S ⊓ twoPointNormalizer G Ω α C.b (D'.L i₁) ∧
        ∀ ω : Ω, ω ∈ fixSet Ω U ↔ ∃ h : ω ∈ fixSet Ω (Subgroup.zpowers v),
          (∀ j, j ≠ C.i → C.D.coord ⟨ω, h⟩ j = C.D.coord C.a j) ∧ C.D.coord ⟨ω, h⟩ C.i ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Finset (C.D.Ψc C.i) := {C.D.coord C.a C.i, C.D.coord C.b C.i, C.D.coord C.γΦ C.i}
  obtain ⟨hγl, hγa, hγb⟩ := (C.mem_holtDelta_iff hS C.γΦ).mp C.γ_mem_holtDelta
  have hab : C.D.coord C.a C.i ≠ C.D.coord C.b C.i := Ne.symm C.coord_b_ne
  have hAc : Nat.card ↥((A : Set (C.D.Ψc C.i))ᶜ) = Fintype.card (C.D.Ψc C.i) - 3 := by
    rw [← Finset.coe_compl, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_compl,
      Finset.card_eq_three.mpr ⟨_, _, _, hab, Ne.symm hγa, Ne.symm hγb, rfl⟩]
  have hodd := C.D.odd_card_Ψc C.i
  have h7 := C.seven
  obtain ⟨P, U, hUP, hPp, hPC, -, hPF, hUF⟩ := C.exists_isPGroup_fixSet (A := (A : Set _))
    (B := (B : Set _)) (by exact_mod_cast hAB)
    (by rw [hAc]; exact Nat.Odd.sub_odd hodd (by decide)) (by rw [hAc]; omega) hB hB2
  have hFP : fixSet Ω P = {α, (C.b : Ω), C.γ} := by
    ext ω
    rw [hPF]
    constructor
    · rintro ⟨h, hl, hA⟩
      simp only [A, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hA ⊢
      rcases hA with hA | hA | hA
      · exact Or.inl (congrArg Subtype.val (C.eq_of_line hl (fun _ _ => rfl) hA))
      · exact Or.inr (Or.inl (congrArg Subtype.val (C.eq_of_line hl C.b_line hA)))
      · exact Or.inr (Or.inr (congrArg Subtype.val (C.eq_of_line hl hγl hA)))
    · rintro (rfl | rfl | rfl)
      · exact ⟨C.a.2, fun _ _ => rfl, by simp [A]⟩
      · exact ⟨C.b.2, C.b_line, by simp [A]⟩
      · exact ⟨C.γ_mem_fixSet, hγl, by simp [A]⟩
  have hαP : α ∈ fixSet Ω P := hFP ▸ Set.mem_insert _ _
  have hβP : (C.b : Ω) ∈ fixSet Ω P := hFP ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hγP : C.γ ∈ fixSet Ω P := hFP ▸ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have hPN : P ≤ twoPointNormalizer G Ω α C.b (D'.L i₁) := fun g hg =>
    C.mem_twoPointNormalizer_of_mem hS D' hO' i₁ hline (hPC hg) (hαP g hg) (hβP g hg)
  have hPstab : P ≤ stabilizer G α ⊓ stabilizer G (C.b : Ω) ⊓ stabilizer G C.γ := fun g hg =>
    ⟨⟨hαP g hg, hβP g hg⟩, hγP g hg⟩
  obtain ⟨S, hPS, hS2⟩ := exists_fusionIsSylowIn_ge hPp hPstab
  refine ⟨S, hS2, ?_, U, fun g hg => ⟨hPS (hUP hg), hPN (hUP hg)⟩, hUF⟩
  have hfix : fixSet Ω (S ⊓ twoPointNormalizer G Ω α C.b (D'.L i₁)) = {α, (C.b : Ω), C.γ} := by
    refine le_antisymm (fun ω hω => hFP ▸ fun g hg => hω g ⟨hPS hg, hPN hg⟩) ?_
    rintro ω (rfl | rfl | rfl) g hg
    · exact (hS2.1 hg.1).1.1
    · exact (hS2.1 hg.1).1.2
    · exact (hS2.1 hg.1).2
  obtain ⟨hγα, hγβ⟩ := ne_of_mem_holtDelta' C.ne C.γ_mem_holtDelta
  rw [hfix, Nat.card_coe_set_eq]
  exact Set.ncard_eq_three.mpr ⟨_, _, _, C.ne, Ne.symm hγα, Ne.symm hγβ, rfl⟩

end Line

omit [Fintype Ω] [DecidableEq Ω] [Finite G] [FaithfulSMul G Ω] in
private theorem card_compl_coe (B : Finset (C.D.Ψc C.i)) :
    Nat.card ↥((B : Set (C.D.Ψc C.i))ᶜ) = Fintype.card (C.D.Ψc C.i) - B.card := by
  rw [← Finset.coe_compl, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_compl]

private theorem nonempty_altConfig (hS : Sec4Setting G Ω)
    (hL42 : ∀ (D' : HoltData (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b)) (j : D'.ι),
      IsNaturalSE (factorImage _ _ (D'.L j) (D'.ρ j)) → Fintype.card (D'.Ψc j) ≠ 5 →
        Odd (Nat.card (twoPointKernel G Ω α C.b)) ∧
          (jOddCore (twoPointSection G Ω α C.b) (holtDelta G Ω α C.b) = ⊥ →
            Fintype.card D'.ι = 1)) :
    Nonempty (AltConfig G Ω α C.b) := by
  have hO' := C.jOddCore_eq_bot hS
  have h3 : 3 ≤ Nat.card (holtDelta G Ω α C.b) := by
    have := C.five_le_card_holtDelta hS; omega
  obtain ⟨D'⟩ := hS.holtData_twoPoint h3
  obtain ⟨i₁, hline⟩ := C.exists_line hS D' hO'
  obtain ⟨hγl, hγa, hγb⟩ := (C.mem_holtDelta_iff hS C.γΦ).mp C.γ_mem_holtDelta
  have hab : C.D.coord C.a C.i ≠ C.D.coord C.b C.i := Ne.symm C.coord_b_ne
  have hodd := C.D.odd_card_Ψc C.i
  have h7 := C.seven
  set A : Finset (C.D.Ψc C.i) := {C.D.coord C.a C.i, C.D.coord C.b C.i, C.D.coord C.γΦ C.i}
  have hA3 : A.card = 3 := Finset.card_eq_three.mpr ⟨_, _, _, hab, Ne.symm hγa, Ne.symm hγb, rfl⟩
  obtain ⟨B, hAB, hB, hB2, hB5⟩ : ∃ B : Finset (C.D.Ψc C.i), A ⊆ B ∧
      Even (Nat.card ↥((B : Set (C.D.Ψc C.i))ᶜ)) ∧ Nat.card ↥((B : Set (C.D.Ψc C.i))ᶜ) ≠ 2 ∧
      (Fintype.card (D'.Ψc i₁) % 4 = 3 → ∃ x y : fixSet Ω (Subgroup.zpowers v),
        (x : Ω) ∈ holtDelta G Ω α C.b ∧ (y : Ω) ∈ holtDelta G Ω α C.b ∧ x ≠ C.γΦ ∧
          y ≠ C.γΦ ∧ x ≠ y ∧ B = insert (C.D.coord x C.i) (insert (C.D.coord y C.i) A)) := by
    by_cases h3mod : Fintype.card (D'.Ψc i₁) % 4 = 3
    · have hd := C.card_i₁_mod_four hS D' hO' i₁ hline
      obtain ⟨xi, hxi⟩ := exists_not_mem_finset A (by omega)
      obtain ⟨yi, hyi⟩ := exists_not_mem_finset (insert xi A) (by
        rw [Finset.card_insert_of_notMem hxi]
        have : Fintype.card (C.D.Ψc C.i) % 4 = 1 := by omega
        omega)
      rw [Finset.mem_insert, not_or] at hyi
      simp only [A, Finset.mem_insert, Finset.mem_singleton, not_or] at hxi hyi
      obtain ⟨x, hx, hxc⟩ := C.exists_mem_holtDelta_coord_eq hS hxi.1 hxi.2.1
      obtain ⟨y, hy, hyc⟩ := C.exists_mem_holtDelta_coord_eq hS hyi.2.1 hyi.2.2.1
      have hB5c : (insert xi (insert yi A)).card = 5 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, hA3]
        · simp only [A, Finset.mem_insert, Finset.mem_singleton, not_or]; exact hyi.2
        · simp only [A, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hyi.1, hxi⟩
      refine ⟨insert xi (insert yi A), fun z hz => Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem hz), ?_, ?_,
        fun _ => ⟨x, y, hx, hy, ?_, ?_, ?_, by rw [hxc, hyc]⟩⟩
      · rw [C.card_compl_coe, hB5c]
        exact Nat.Odd.sub_odd hodd (by decide)
      · rw [C.card_compl_coe, hB5c]
        have : Fintype.card (C.D.Ψc C.i) % 4 = 1 := by omega
        omega
      · exact fun h => hxi.2.2 (by rw [← hxc, h])
      · exact fun h => hyi.2.2.2 (by rw [← hyc, h])
      · exact fun h => hyi.1 (by rw [← hxc, ← hyc, h])
    · refine ⟨A, subset_rfl, ?_, ?_, fun h => absurd h h3mod⟩
      · rw [C.card_compl_coe, hA3]
        exact Nat.Odd.sub_odd hodd (by decide)
      · rw [C.card_compl_coe, hA3]
        omega
  obtain ⟨S, hSyl, hfix3, U, hUSN, hUF⟩ := C.exists_sylow hS D' hO' i₁ hline hAB hB hB2
  obtain ⟨-, w', hw', hw'γ, hw'S⟩ := hS.sylow_twoPoint C.ne C.γ_mem_holtDelta hSyl
  refine ⟨⟨D', hO', i₁, C.factor_eq_alt hS D' hO' i₁ hline (hL42 D'),
    fun j hj => C.card_mod_four hS D' hO' i₁ hline hj, C.γΔ, S, hSyl, w', hw', hw'γ, hw'S,
    hfix3, fun h3mod => ?_, fun hr h5 => C.not_odd_of_five hS D' hO' i₁ hline hr h5⟩⟩
  obtain ⟨x, y, hx, hy, hxγ, hyγ, hxy, rfl⟩ := hB5 h3mod
  obtain ⟨hxl, -, -⟩ := (C.mem_holtDelta_iff hS x).mp hx
  obtain ⟨hyl, -, -⟩ := (C.mem_holtDelta_iff hS y).mp hy
  have hFU : fixSet Ω U = {α, (C.b : Ω), C.γ, (x : Ω), (y : Ω)} := by
    ext ω
    rw [hUF]
    constructor
    · rintro ⟨h, hl, hB⟩
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hB
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hB with hB | hB | hB | hB | hB
      · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val (C.eq_of_line hl hxl hB)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (congrArg Subtype.val (C.eq_of_line hl hyl hB)))))
      · exact Or.inl (congrArg Subtype.val (C.eq_of_line hl (fun _ _ => rfl) hB))
      · exact Or.inr (Or.inl (congrArg Subtype.val (C.eq_of_line hl C.b_line hB)))
      · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val (C.eq_of_line hl hγl hB))))
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨C.a.2, fun _ _ => rfl, by simp [A]⟩
      · exact ⟨C.b.2, C.b_line, by simp [A]⟩
      · exact ⟨C.γ_mem_fixSet, hγl, by simp [A]⟩
      · exact ⟨x.2, hxl, by simp⟩
      · exact ⟨y.2, hyl, by simp⟩
  refine ⟨U, hUSN, ?_, ?_⟩
  · obtain ⟨hγα, hγβ⟩ := ne_of_mem_holtDelta' C.ne C.γ_mem_holtDelta
    obtain ⟨hxα, hxβ⟩ := ne_of_mem_holtDelta' C.ne hx
    obtain ⟨hyα, hyβ⟩ := ne_of_mem_holtDelta' C.ne hy
    have hxγ' : (x : Ω) ≠ C.γ := fun h => hxγ (Subtype.ext h)
    have hyγ' : (y : Ω) ≠ C.γ := fun h => hyγ (Subtype.ext h)
    have hxy' : (x : Ω) ≠ y := fun h => hxy (Subtype.ext h)
    have h1 : α ∉ ({(C.b : Ω), C.γ, (x : Ω), (y : Ω)} : Finset Ω) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨C.ne, Ne.symm hγα, Ne.symm hxα, Ne.symm hyα⟩
    have h2 : (C.b : Ω) ∉ ({C.γ, (x : Ω), (y : Ω)} : Finset Ω) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hγβ, Ne.symm hxβ, Ne.symm hyβ⟩
    have h3' : C.γ ∉ ({(x : Ω), (y : Ω)} : Finset Ω) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hxγ', Ne.symm hyγ'⟩
    rw [hFU, Nat.card_coe_set_eq, show ({α, (C.b : Ω), C.γ, (x : Ω), (y : Ω)} : Set Ω) =
      ↑({α, (C.b : Ω), C.γ, (x : Ω), (y : Ω)} : Finset Ω) by simp, Set.ncard_coe_finset,
      Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3', Finset.card_pair hxy']
  · rw [hFU]
    rintro ω (rfl | rfl | rfl | rfl | rfl)
    · exact Or.inl (Set.mem_insert _ _)
    · exact Or.inl (Set.mem_insert_of_mem _ rfl)
    · exact Or.inr ⟨C.γΔ, fun _ _ => rfl, rfl⟩
    · exact Or.inr ⟨⟨x, hx⟩, hline ⟨x, hx⟩ x.2, rfl⟩
    · exact Or.inr ⟨⟨y, hy⟩, hline ⟨y, hy⟩ y.2, rfl⟩

end L48ConfigW

private theorem L48Config.exists_configW [Fintype Ω] [DecidableEq Ω] [Finite G]
    [FaithfulSMul G Ω] {α : Ω} {v : G} (hS : Sec4Setting G Ω) (C : L48Config G Ω α v) :
    ∃ C' : L48ConfigW G Ω α v, C'.toL48Config = C := by
  obtain ⟨w, hw, hwC, hwv⟩ := C.exists_w hS
  obtain ⟨γ, hγ, -⟩ := hw.1.2
  exact ⟨{ C with w := w, w_mem := hw, w_comm := hwC, wv_mem := hwv, γ := γ, w_fix := hγ }, rfl⟩

end KSide

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.isNaturalSE_factor_typeLSection_of (hS : Sec4Setting G Ω)
    (hP43 : ∀ {α β : Ω}, α ≠ β → IsEmpty (AltConfig G Ω α β))
    {α : Ω} {v : G} (hv : IsTypeL G Ω α v)
    (hO : CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥)
    (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι) :
    IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)) := by
  by_contra hSE
  obtain ⟨hA, h7⟩ := (D.factor i).resolve_right hSE
  have hOK : jOddCore (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) = ⊥ :=
    le_bot_iff.mp (hO ▸ jOddCore_le_pPrimeCore)
  obtain ⟨x, hx⟩ := exists_not_mem_finset {D.coord ⟨α, hv.mem_fixSet_zpowers⟩ i}
    (by rw [Finset.card_singleton]; omega)
  rw [Finset.mem_singleton] at hx
  obtain ⟨b, hb⟩ := D.exists_coord_eq_update ⟨α, hv.mem_fixSet_zpowers⟩ i x
  let C : L48Config G Ω α v :=
    { hv := hv, D := D, hO := hOK, i := i, alt := hA, seven := h7, b := b,
      coord_b_ne := by rw [hb, Function.update_self]; exact hx
      coord_b_eq := fun j hj => by rw [hb, Function.update_of_ne hj] }
  obtain ⟨C', -⟩ := C.exists_configW hS
  obtain ⟨A⟩ := C'.nonempty_altConfig hS (fun D' j => hS.lemma_4_2 C'.ne D' j)
  exact (hP43 C'.ne).false A

end Main

end CFSG.Holt.H78
