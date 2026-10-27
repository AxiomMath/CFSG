module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitAction
public import CFSG.GroupTheory.PCore.CommutingBalance
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint
open scoped commutatorElement Pointwise

theorem mulAut_eq_one_of_forall_mem_center {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (σ : MulAut Q) (h : ∀ q : Q, q⁻¹ * σ q ∈ center Q) : σ = 1 := by
  let f : Q →* center Q :=
    { toFun := fun q => ⟨q⁻¹ * σ q, h q⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q r => Subtype.ext (by
        have hc := mem_center_iff.mp (h q) r⁻¹
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        calc r⁻¹ * q⁻¹ * (σ q * σ r) = r⁻¹ * (q⁻¹ * σ q) * σ r := by group
          _ = q⁻¹ * σ q * r⁻¹ * σ r := by rw [hc]
          _ = q⁻¹ * σ q * (r⁻¹ * σ r) := by group) }
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := Q)]
    exact Abelianization.commutator_subset_ker f
  refine MulEquiv.ext fun q => ?_
  have hq : f q = 1 := MonoidHom.mem_ker.mp (hker ▸ mem_top q)
  have h1 : q⁻¹ * σ q = 1 := congrArg Subtype.val hq
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp h1).symm

variable {X : Type*} [Group X]

abbrev zStarIn (K : Subgroup X) : Subgroup X :=
  (UnbalancingLocal.centralPreimage (pPrimeCore 2 K)).map K.subtype

theorem oddCoreIn_le (K : Subgroup X) : oddCoreIn K ≤ K := map_subtype_le _

theorem zStarIn_le (K : Subgroup X) : zStarIn K ≤ K := map_subtype_le _

theorem oddCoreIn_le_zStarIn (K : Subgroup X) : oddCoreIn K ≤ zStarIn K :=
  map_mono (UnbalancingLocal.le_centralPreimage _)

theorem odd_card_oddCoreIn [Finite X] (K : Subgroup X) : Odd (Nat.card (oddCoreIn K)) := by
  rw [card_map_of_injective K.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem not_mem_oddCoreIn_of_orderOf_two [Finite X] (K : Subgroup X) {g : X}
    (hg : orderOf g = 2) : g ∉ oddCoreIn K :=
  not_mem_of_orderOf_two_of_odd (odd_card_oddCoreIn K) hg

theorem forall_mem_oddCoreIn_of_forall_mem_zStarIn {K : Subgroup X}
    (hK : IsQuasisimple (K ⧸ pPrimeCore 2 K)) {g : X} (hg : g ∈ normalizer (K : Set X))
    (h : ∀ k ∈ K, ⁅k, g⁆ ∈ zStarIn K) : ∀ k ∈ K, ⁅k, g⁆ ∈ oddCoreIn K := by
  have : Group.IsPerfect (K ⧸ pPrimeCore 2 K) := hK.1
  apply (oddQuotAction_eq_one_iff (⟨g, hg⟩ : normalizer (K : Set X))).mp
  apply mulAut_eq_one_of_forall_mem_center
  intro q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [oddQuotAction_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    obtain ⟨z, hz, hzk⟩ := h _ (inv_mem k.2)
    have hzval : z = k⁻¹ * ⟨g * k * g⁻¹, (mem_normalizer_iff.mp hg k).mp k.2⟩ := by
      apply Subtype.ext
      have hzk' : (z : X) = ⁅(k : X)⁻¹, g⁆ := hzk
      rw [hzk', Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [← hzval]
    exact hz

theorem commutator_le_of_le_normalizer {K H : Subgroup X} (hH : H ≤ normalizer (K : Set X)) :
    ⁅K, H⁆ ≤ K := by
  rw [commutator_le]
  intro k hk h hh
  have h2 : h * k⁻¹ * h⁻¹ ∈ K := (mem_normalizer_iff.mp (hH hh) k⁻¹).mp (inv_mem hk)
  have h4 : ⁅k, h⁆ = k * (h * k⁻¹ * h⁻¹) := by rw [commutatorElement_def]; group
  rw [h4]
  exact mul_mem hk h2

theorem le_normalizer_commutator (K H : Subgroup X) :
    K ≤ normalizer ((⁅K, H⁆ : Subgroup X) : Set X) := by
  have key : ∀ k' ∈ K, ⁅K, H⁆ ≤ ⁅K, H⁆.comap (MulAut.conj k').toMonoidHom := by
    intro k' hk'
    rw [Subgroup.commutator_def, closure_le]
    rintro _ ⟨k, hk, h, hh, rfl⟩
    change k' * ⁅k, h⁆ * k'⁻¹ ∈ ⁅K, H⁆
    have heq : k' * ⁅k, h⁆ * k'⁻¹ = ⁅k' * k, h⁆ * ⁅k', h⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem (commutator_mem_commutator (mul_mem hk' hk) hh)
      (inv_mem (commutator_mem_commutator hk' hh))
  intro k' hk'
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact key k' hk' hn
  · intro hn
    have h1 := key k'⁻¹ (inv_mem hk') hn
    change k'⁻¹ * (k' * n * k'⁻¹) * k'⁻¹⁻¹ ∈ ⁅K, H⁆ at h1
    rwa [show k'⁻¹ * (k' * n * k'⁻¹) * k'⁻¹⁻¹ = n by group] at h1

theorem commutator_eq_self_of_exists [Finite X] {K H : Subgroup X}
    (hgen : CatalogueBPrimeJoin.primeResidual 2 K = ⊤) (hK : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    (hH : H ≤ normalizer (K : Set X)) (hnt : ∃ h ∈ H, ∃ k ∈ K, ⁅k, h⁆ ∉ oddCoreIn K) :
    ⁅K, H⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := ⁅K, H⁆ with hNdef
  have hNK : N ≤ K := commutator_le_of_le_normalizer hH
  set N' := N.subgroupOf K with hN'
  have hN'n : N'.Normal := by
    rw [hN', normal_subgroupOf_iff hNK]
    intro n k hn hk
    exact (mem_normalizer_iff.mp (le_normalizer_commutator K H hk) n).mp hn
  set q := QuotientGroup.mk' (pPrimeCore 2 K) with hq
  have hNbar : (N'.map q).Normal := hN'n.map q (QuotientGroup.mk'_surjective _)
  rcases Quasisimple.normal_le_center_or_eq_top
      (CatalogueBAlternating.quasisimple_iff_native.mp hK) (N'.map q) with hc | htop
  ·
    exfalso
    obtain ⟨h, hh, k, hk, hnt⟩ := hnt
    apply hnt
    refine forall_mem_oddCoreIn_of_forall_mem_zStarIn hK (hH hh) (fun k hk => ?_) k hk
    have hcK : ⁅k, h⁆ ∈ K := hNK (commutator_mem_commutator hk hh)
    refine ⟨⟨⁅k, h⁆, hcK⟩, ?_, rfl⟩
    change q ⟨⁅k, h⁆, hcK⟩ ∈ center (K ⧸ pPrimeCore 2 K)
    exact hc ⟨_, show (⟨⁅k, h⁆, hcK⟩ : K) ∈ N' from commutator_mem_commutator hk hh, rfl⟩
  ·
    apply le_antisymm hNK
    have h2 : ∀ x : K, (∃ j : ℕ, orderOf x = 2 ^ j) → x ∈ N' := by
      rintro x ⟨j, hj⟩
      obtain ⟨n, hn, hnx⟩ : q x ∈ N'.map q := htop ▸ mem_top _
      have ho : n⁻¹ * x ∈ pPrimeCore 2 K := by
        rw [← QuotientGroup.ker_mk' (pPrimeCore 2 K), MonoidHom.mem_ker, map_mul, map_inv,
          hnx, inv_mul_cancel]
      set r := QuotientGroup.mk' N' with hr
      have hrn : r n = 1 := by
        rw [hr, QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff n).mpr hn
      have hrx : r x = r (n⁻¹ * x) := by
        rw [map_mul, map_inv, hrn, inv_one, one_mul]
      have hd1 : orderOf (r x) ∣ 2 ^ j := hj ▸ orderOf_map_dvd r x
      have hd2 : orderOf (r x) ∣ Nat.card (pPrimeCore 2 K) := by
        rw [hrx]
        refine (orderOf_map_dvd r _).trans ?_
        rw [← Subgroup.orderOf_mk (n⁻¹ * x) ho]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (2 ^ j) (Nat.card (pPrimeCore 2 K)) :=
        Nat.Coprime.pow_left j pPrimeCore_coprime_card
      have h1 : orderOf (r x) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
      rw [orderOf_eq_one_iff, hr, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have htopK : N' = ⊤ := by
      rw [eq_top_iff, ← hgen, CatalogueBPrimeJoin.primeResidual_eq_closure, closure_le]
      intro x hx
      exact h2 x hx
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ N' := htopK ▸ mem_top _
    exact this

theorem inf_le_oddCoreIn [Finite X] {S A : Subgroup X} (hA : Odd (Nat.card A))
    (hSA : S ≤ normalizer (A : Set X)) : S ⊓ A ≤ oddCoreIn S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := (S ⊓ A).subgroupOf S with hB
  have hBn : B.Normal := by
    rw [hB, normal_subgroupOf_iff inf_le_left]
    intro x s hx hs
    exact mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hx).1) (inv_mem hs),
      (mem_normalizer_iff.mp (hSA hs) x).mp (mem_inf.mp hx).2⟩
  have hBodd : Nat.Coprime 2 (Nat.card B) := by
    have h1 : Nat.card B ∣ Nat.card A := by
      rw [hB, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : S ⊓ A ≤ S)).toEquiv]
      exact card_dvd_of_le inf_le_right
    exact Nat.coprime_two_left.mpr (Odd.of_dvd_nat hA h1)
  have hle : B ≤ pPrimeCore 2 S := le_sSup ⟨hBn, hBodd⟩
  intro x hx
  exact ⟨⟨x, (mem_inf.mp hx).1⟩, hle hx, rfl⟩

theorem forall_mem_oddCoreIn_of_le [Finite X] {S M : Subgroup X} (hSM : S ≤ M) {g : X}
    (hgS : g ∈ normalizer (S : Set X)) (h : ∀ m ∈ M, ⁅m, g⁆ ∈ oddCoreIn M) :
    ∀ s ∈ S, ⁅s, g⁆ ∈ oddCoreIn S := by
  intro s hs
  have hSn : S ≤ normalizer ((oddCoreIn M : Subgroup X) : Set X) :=
    hSM.trans (le_normalizer.trans (normalizer_le_normalizer_oddCoreIn M))
  refine inf_le_oddCoreIn (odd_card_oddCoreIn M) hSn (mem_inf.mpr ⟨?_, h s (hSM hs)⟩)
  exact commutator_le_of_le_normalizer (zpowers_le.mpr hgS)
    (commutator_mem_commutator hs (mem_zpowers g))

theorem forall_commutator_mem_iff {J O : Subgroup X} {t : X} (ht : t ∈ normalizer (J : Set X)) :
    (∀ j ∈ J, ⁅j, t⁆ ∈ O) ↔ ∀ j ∈ J, j⁻¹ * t⁻¹ * j * t ∈ O := by
  constructor
  · intro h j hj
    have hj' : t⁻¹ * j⁻¹ * t ∈ J := by
      have h1 := (mem_normalizer_iff.mp (inv_mem ht) j⁻¹).mp (inv_mem hj)
      rwa [inv_inv] at h1
    have h2 := inv_mem (h _ hj')
    rwa [show (⁅t⁻¹ * j⁻¹ * t, t⁆)⁻¹ = j⁻¹ * t⁻¹ * j * t by
      rw [commutatorElement_def]; group] at h2
  · intro h j hj
    have hj' : t * j⁻¹ * t⁻¹ ∈ J := (mem_normalizer_iff.mp ht j⁻¹).mp (inv_mem hj)
    have h2 := inv_mem (h _ hj')
    rwa [show ((t * j⁻¹ * t⁻¹)⁻¹ * t⁻¹ * (t * j⁻¹ * t⁻¹) * t)⁻¹ = ⁅j, t⁆ by
      rw [commutatorElement_def]; group] at h2

theorem eq_of_isPComponent_of_perfect_le [Finite X] {C A B S : Subgroup X} (hAC : A ≤ C)
    (hBC : B ≤ C) (hA : IsPComponent 2 (A.subgroupOf C)) (hB : IsPComponent 2 (B.subgroupOf C))
    (hSA : S ≤ A) (hSB : S ≤ B) (hS : ⁅S, S⁆ = S) {s : X} (hs : s ∈ S) (hs2 : orderOf s = 2) :
    A = B := by
  by_contra hne
  have hne' : A.subgroupOf C ≠ B.subgroupOf C := by
    intro h
    apply hne
    rw [subgroupOf_inj, inf_eq_left.mpr hAC, inf_eq_left.mpr hBC] at h
    exact h
  obtain ⟨-, -, hcomm, -⟩ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ hA hB).2 hne'
  have hAB : ⁅A, B⁆ ≤ oddCoreIn A := by
    have h1 := map_mono (f := C.subtype) (hcomm.trans inf_le_left)
    rwa [map_commutator, map_subgroupOf_eq_of_le hAC, map_subgroupOf_eq_of_le hBC,
      pPrimeCore_map_subgroupOf 2 A C hAC] at h1
  have hsAB : s ∈ ⁅A, B⁆ := commutator_mono hSA hSB (by rw [hS]; exact hs)
  exact not_mem_oddCoreIn_of_orderOf_two A hs2 (hAB hsAB)

theorem mem_of_eq_mul_of_odd {S : Subgroup X} {w s o : X} (hw : w ^ 2 = 1) (hs : s ∈ S)
    (hwo : w = s * o) (hodd : Odd (orderOf o)) (hcomm : w * o = o * w) : w ∈ S := by
  have hsw : s = w * o⁻¹ := by rw [hwo]; group
  have hc : Commute w o⁻¹ := Commute.inv_right hcomm
  obtain ⟨m, hm⟩ := hodd
  have h1 : s ^ orderOf o = w := by
    rw [hsw, hc.mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one, hm, pow_succ, pow_mul,
      hw, one_pow, one_mul]
  rw [← h1]
  exact pow_mem hs _

theorem eq_one_or_eq_of_mem_zpowers {a g : X} (ha : a ^ 2 = 1) (hg : g ∈ zpowers a) :
    g = 1 ∨ g = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ← pow_two, ha, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ← pow_two, ha, one_zpow, one_mul, zpow_one]

theorem isPGroup_zpowers_of_sq_eq_one {a : X} (ha : a ^ 2 = 1) : IsPGroup 2 (zpowers a) :=
  fun g => ⟨1, by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one]
    rcases eq_one_or_eq_of_mem_zpowers ha g.2 with h | h
    · rw [h, one_pow]
    · rw [h, ha]⟩

theorem exists_involution_lift [Finite X] {A N : Subgroup X} (hNA : N ≤ A)
    (hN : (N.subgroupOf A).Normal) (hNodd : Odd (Nat.card N)) {a : X} (ha : a ^ 2 = 1)
    (haN : a ∈ normalizer (N : Set X)) {z : X} (hzA : z ∈ A) (hz2 : z ^ 2 ∈ N) (hzN : z ∉ N)
    (hza : z⁻¹ * (a * z * a⁻¹) ∈ N) :
    ∃ γ ∈ A, orderOf γ = 2 ∧ γ * a = a * γ ∧ γ⁻¹ * z ∈ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α : zpowers a →* MulAut X := MulAut.conj.comp (zpowers a).subtype
  have hα : ∀ (g : zpowers a) (x : X), α g x = (g : X) * x * (g : X)⁻¹ := fun _ _ => rfl
  have hcop : ¬ 2 ∣ Nat.card N := fun h =>
    (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h)
  have hinv : ∀ (g : zpowers a), ∀ x : X, z⁻¹ * x ∈ N → z⁻¹ * α g x ∈ N := by
    intro g x hx
    rw [hα]
    rcases eq_one_or_eq_of_mem_zpowers ha g.2 with h | h
    · rw [h, one_mul, inv_one, mul_one]
      exact hx
    · rw [h]
      have h1 := (mem_normalizer_iff.mp haN _).mp hx
      have heq : z⁻¹ * (a * x * a⁻¹) = z⁻¹ * (a * z * a⁻¹) * (a * (z⁻¹ * x) * a⁻¹) := by group
      rw [heq]
      exact mul_mem hza h1
  obtain ⟨c, hc, hfix⟩ := (Semidihedral.Principal.coprime_invariant_coset_fixed 2
    (isPGroup_zpowers_of_sq_eq_one ha) α N hcop z).2 hinv
  have hca : c * a = a * c := by
    have h1 := hfix ⟨a, mem_zpowers a⟩
    rw [hα] at h1
    calc c * a = a * c * a⁻¹ * a := by rw [h1]
      _ = a * c := by group
  have hcA : c ∈ A := by
    have h1 := mul_mem hzA (hNA hc)
    rwa [mul_inv_cancel_left] at h1
  obtain ⟨k, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  set N' := N.subgroupOf A with hN'
  set q := QuotientGroup.mk' N' with hq'
  have hq : q ⟨c, hcA⟩ = q ⟨z, hzA⟩ := by
    rw [hq', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change c⁻¹ * z ∈ N
    have h1 := inv_mem hc
    rwa [mul_inv_rev, inv_inv] at h1
  have hz2' : q ⟨z, hzA⟩ ^ 2 = 1 := by
    rw [← map_pow, hq', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz2
  have hcm' : q ⟨c ^ m, pow_mem hcA m⟩ = q ⟨z, hzA⟩ := by
    have : (⟨c ^ m, pow_mem hcA m⟩ : A) = ⟨c, hcA⟩ ^ m := rfl
    rw [this, map_pow, hq]
    obtain ⟨l, rfl⟩ := hm
    rw [pow_succ, pow_mul, hz2', one_pow, one_mul]
  have hmem : (c ^ m)⁻¹ * z ∈ N := by
    rw [hq', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcm'
    exact hcm'
  have hsq : (c ^ m) ^ 2 ∈ N := by
    have h1 : q ⟨(c ^ m) ^ 2, pow_mem (pow_mem hcA m) 2⟩ = 1 := by
      have : (⟨(c ^ m) ^ 2, pow_mem (pow_mem hcA m) 2⟩ : A) = ⟨c ^ m, pow_mem hcA m⟩ ^ 2 := rfl
      rw [this, map_pow, hcm', hz2']
    rw [hq', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hc2k : (c ^ m) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hcm, pow_orderOf_eq_one]
  have hsq1 : (c ^ m) ^ 2 = 1 := by
    have hd1 : orderOf ((c ^ m) ^ 2) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hc2k, one_pow]
    have hd2 : orderOf ((c ^ m) ^ 2) ∣ Nat.card N := by
      rw [← Subgroup.orderOf_mk _ hsq]
      exact orderOf_dvd_natCard _
    have hcop' : Nat.Coprime (2 ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hNodd)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop') hd2)
  have hne : c ^ m ≠ 1 := by
    intro h1
    apply hzN
    rw [h1, inv_one, one_mul] at hmem
    exact hmem
  exact ⟨c ^ m, pow_mem hcA m, orderOf_eq_prime hsq1 hne, Commute.pow_left hca m, hmem⟩

end CFSG.ComponentClassification.TBLit
