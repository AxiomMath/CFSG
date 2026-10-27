module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ElemAbelianComplement

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open
open scoped commutatorElement

theorem commutatorElement_mul_right_of_central {P : Type*} [Group P] {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) (x : P) (hc : ∀ y : P, ⁅x, y⁆ ∈ Z) (y y' : P) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have h1 : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  have h2 : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := by
    have := Subgroup.mem_center_iff.mp (hZ (hc y')) y
    rw [this]; group
  rw [h1, h2]

theorem inf_zpowers_eq_bot {P : Type*} [Group P] {p : ℕ} (hp : p.Prime) {x : P} (hxp : x ^ p = 1)
    {Z : Subgroup P} (hxZ : x ∉ Z) : Z ⊓ Subgroup.zpowers x = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyZ, hyx⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyx
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hj : x ^ j = x ^ (j % (p : ℤ)).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j hp0)]
    conv_lhs => rw [← Int.emod_add_mul_ediv j p]
    rw [zpow_add, zpow_mul, zpow_natCast x p, hxp, one_zpow, mul_one]
  rw [hj] at hyZ ⊢
  rw [Subgroup.mem_bot]
  by_contra hne
  have hi0 : 0 < (j % (p : ℤ)).toNat := by
    rcases Nat.eq_zero_or_pos (j % (p : ℤ)).toNat with h | h
    · rw [h, pow_zero] at hne; exact absurd rfl hne
    · exact h
  have hip : (j % (p : ℤ)).toNat < p := by
    have h1 : j % (p : ℤ) < p := Int.emod_lt_of_pos j (by exact_mod_cast hp.pos)
    omega
  exact hxZ (mem_of_pow_mem_of_lt hp hxp hi0 hip hyZ)

theorem mul_pow_of_central {G : Type*} [Group G] {u v z : G} (hz : ∀ w : G, z * w = w * z)
    (huv : v * u = z * (u * v)) (n : ℕ) : (u * v) ^ n = z ^ n.choose 2 * (u ^ n * v ^ n) := by
  have hk : ∀ k : ℕ, v ^ k * u = z ^ k * (u * v ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc v ^ (k + 1) * u = v ^ k * (v * u) := by rw [pow_succ, mul_assoc]
        _ = z * (v ^ k * u * v) := by
          rw [huv, ← mul_assoc (v ^ k) z, ← hz (v ^ k)]; simp only [mul_assoc]
        _ = z * (z ^ k * (u * v ^ k) * v) := by rw [ih]
        _ = z ^ (k + 1) * (u * v ^ (k + 1)) := by
          rw [pow_succ' z k, pow_succ v k]; simp only [mul_assoc]
  have hzk : ∀ (m : ℕ) (w : G), z ^ m * w = w * z ^ m := fun m w =>
    (Commute.pow_left (show Commute z w from hz w) m).eq
  induction n with
  | zero => simp
  | succ n ih =>
    calc (u * v) ^ (n + 1) = z ^ n.choose 2 * (u ^ n * (v ^ n * u) * v) := by
          rw [pow_succ, ih]; simp only [mul_assoc]
      _ = z ^ n.choose 2 * (z ^ n * (u ^ n * (u * v ^ n)) * v) := by
          rw [hk n, ← mul_assoc (u ^ n) (z ^ n), ← hzk n (u ^ n)]; simp only [mul_assoc]
      _ = z ^ (n + 1).choose 2 * (u ^ (n + 1) * v ^ (n + 1)) := by
          rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm n (n.choose 2),
            pow_add z (n.choose 2) n, pow_succ u n, pow_succ v n]
          simp only [mul_assoc]

theorem mul_pow_prime_of_central {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u v : G} (hz : ⁅v, u⁆ ∈ Subgroup.center G) (hzp : ⁅v, u⁆ ^ p = 1) :
    (u * v) ^ p = u ^ p * v ^ p := by
  have huv : v * u = ⁅v, u⁆ * (u * v) := by rw [commutatorElement_def]; group
  rw [mul_pow_of_central (fun w => (Subgroup.mem_center_iff.mp hz w).symm) huv p]
  have hodd : 2 ∣ p - 1 := by
    have := hp.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with ⟨m, hm⟩ | ⟨m, hm⟩
    · have h2 : 2 ∣ p := ⟨m, by omega⟩
      rcases this h2 with h | h
      · omega
      · exact absurd h.symm hp2
    · exact ⟨m, by omega⟩
  rw [Nat.choose_two_right, Nat.mul_div_assoc p hodd, pow_mul, hzp, one_pow, one_mul]

universe u

theorem exists_elemAbelian_of_exponent_central {p : ℕ} (hp : p.Prime) :
    ∀ (s : ℕ) (P : Type u) [Group P] [Finite P], (∀ x : P, x ^ p = 1) → ∀ Z : Subgroup P,
      Z ≤ Subgroup.center P → Nat.card Z = p → commutator P ≤ Z → Nat.card P = p ^ (s + 1) →
      ∃ A : Subgroup P, IsElemAbelian p A ∧ ∃ k, (s + 1) / 2 + 1 ≤ k ∧ Nat.card A = p ^ k := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro P _ _ hexp Z hZ hZp hcomm hcard
  have hZab : IsElemAbelian p Z :=
    ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hZ b.2) (a : P))⟩⟩, fun x _ => hexp x⟩
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    exact ⟨Z, hZab, 1, le_rfl, by rw [hZp, pow_one]⟩
  have hZlt : Nat.card Z < Nat.card P := by
    rw [hZp, hcard]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ (s + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  obtain ⟨x, hxZ⟩ : ∃ x : P, x ∉ Z := by
    by_contra h
    push Not at h
    have hZtop : Z = ⊤ := eq_top_iff.mpr fun y _ => h y
    rw [hZtop, Subgroup.card_top] at hZlt
    exact lt_irrefl _ hZlt
  have hcx : ∀ y : P, ⁅x, y⁆ ∈ Z := fun y =>
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  let φ : P →* Z :=
    { toFun := fun y => ⟨⁅x, y⁆, hcx y⟩
      map_one' := by ext; simp [commutatorElement_def]
      map_mul' := fun y y' => Subtype.ext (commutatorElement_mul_right_of_central hZ x hcx y y') }
  set C := Subgroup.centralizer ({x} : Set P) with hCdef
  have hker : φ.ker = C := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : ⁅x, y⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    · intro h
      apply Subtype.ext
      show ⁅x, y⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h.symm
  have hCcard : Nat.card P ≤ p * Nat.card C := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker] at h1
    have h2 : Nat.card φ.range ≤ p := by
      rw [← hZp]
      exact Subgroup.card_le_card_group φ.range
    calc Nat.card P = Nat.card C * Nat.card φ.range := h1.symm
      _ ≤ Nat.card C * p := Nat.mul_le_mul_left _ h2
      _ = p * Nat.card C := mul_comm _ _
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hZC : Z ≤ C := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp (hZ hz) x).symm
  set xC : C := ⟨x, hxC⟩ with hxCdef
  set N : Subgroup C := Subgroup.zpowers xC with hNdef
  have hNcen : N ≤ Subgroup.center C := by
    rw [hNdef, Subgroup.zpowers_le]
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have : N.Normal := Subgroup.normal_of_le_center hNcen
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ Z.one_mem)
  have hxord : orderOf x = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime (hexp x) hx1
  have hNcard : Nat.card N = p := by
    rw [hNdef, Nat.card_zpowers, Subgroup.orderOf_mk, hxord]
  have hZN : Z ⊓ Subgroup.zpowers x = ⊥ := inf_zpowers_eq_bot hp (hexp x) hxZ
  set Q := C ⧸ N with hQdef
  let π : C →* Q := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  set ZQ : Subgroup Q := (Z.subgroupOf C).map π with hZQdef
  have hπZ : Function.Injective (fun z : Z.subgroupOf C => π z) := by
    intro a b hab
    have h1 : (a : C)⁻¹ * b ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      show π ((a : C)⁻¹ * b) = 1
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.mpr hab
    have h2 : ((a : C) : P)⁻¹ * (b : C) ∈ Z ⊓ Subgroup.zpowers x := by
      refine ⟨Z.mul_mem (Z.inv_mem (Subgroup.mem_subgroupOf.mp a.2))
        (Subgroup.mem_subgroupOf.mp b.2), ?_⟩
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by
        have := congrArg Subtype.val hj
        simpa using this⟩
    rw [hZN, Subgroup.mem_bot] at h2
    apply Subtype.ext
    apply Subtype.ext
    exact (inv_mul_eq_one.mp h2)
  have hZQcard : Nat.card ZQ = p := by
    rw [hZQdef, ← hZp]
    have h1 : Nat.card ((Z.subgroupOf C).map π) = Nat.card (Z.subgroupOf C) := by
      refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨π z, z, z.2, rfl⟩) ⟨?_, ?_⟩).symm
      · intro a b hab
        exact hπZ (congrArg Subtype.val hab)
      · rintro ⟨q, z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv
  have hQexp : ∀ q : Q, q ^ p = 1 := by
    intro q
    obtain ⟨c, rfl⟩ := hπ q
    rw [← map_pow]
    have : c ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hexp c)
    rw [this, map_one]
  have hZQc : ZQ ≤ Subgroup.center Q := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨c, rfl⟩ := hπ q
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hz)) (c : P)
  have hQcomm : commutator Q ≤ ZQ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨c, rfl⟩ := hπ a
    obtain ⟨c', rfl⟩ := hπ b
    rw [← map_commutatorElement]
    refine ⟨⁅c, c'⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have h1 : ((⁅c, c'⁆ : C) : P) = ⁅(c : P), (c' : P)⁆ := by
      simp [commutatorElement_def]
    rw [h1]
    exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hCdvd : Nat.card C ∣ p ^ (s + 1) := hcard ▸ Subgroup.card_subgroup_dvd_card C
  obtain ⟨t, ht, hCt⟩ := (Nat.dvd_prime_pow hp).mp hCdvd
  have hCQ : Nat.card C = Nat.card Q * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hQt : Nat.card Q * p = p ^ t := by rw [← hCt, hCQ, hNcard]
  have hts : s ≤ t := by
    have h1 : p ^ (s + 1) ≤ p ^ (t + 1) := by
      rw [← hcard, pow_succ]
      calc Nat.card P ≤ p * Nat.card C := hCcard
        _ = p ^ t * p := by rw [hCt, mul_comm]
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  have ht2 : 2 ≤ t := by
    have h1 : p ≤ Nat.card Q := by
      rw [← hZQcard]
      exact Subgroup.card_le_card_group ZQ
    have h2 : p * p ≤ p ^ t := by rw [← hQt]; exact Nat.mul_le_mul_right p h1
    by_contra hlt
    push Not at hlt
    interval_cases t
    · simp at h2; nlinarith [hp.two_le]
    · simp at h2; nlinarith [hp.two_le]
  have hQcard : Nat.card Q = p ^ ((t - 2) + 1) := by
    have h1 : p ^ t = p ^ ((t - 2) + 1) * p := by rw [← pow_succ]; congr 1; omega
    rw [h1] at hQt
    exact Nat.eq_of_mul_eq_mul_right hp.pos hQt
  obtain ⟨AQ, hAQ, k', hk', hAQc⟩ := ih (t - 2) (by omega) Q hQexp ZQ hZQc hZQcard hQcomm hQcard
  refine ⟨(AQ.comap π).map C.subtype, ?_, k' + 1, by omega, ?_⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨c, hc, rfl⟩⟩ := a
      obtain ⟨_, ⟨c', hc', rfl⟩⟩ := b
      apply Subtype.ext
      show (c : P) * c' = c' * c
      have hcc : π ⁅c, c'⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact congrArg Subtype.val (hAQ.1.is_comm.comm ⟨π c, hc⟩ ⟨π c', hc'⟩)
      have hN : ⁅c, c'⁆ ∈ N := by
        rw [← QuotientGroup.ker_mk' N]
        exact hcc
      have hZx : ⁅(c : P), (c' : P)⁆ ∈ Z ⊓ Subgroup.zpowers x := by
        refine ⟨hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
          (Subgroup.mem_top _)), ?_⟩
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hN
        refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
        have := congrArg Subtype.val hj
        simpa [commutatorElement_def] using this
      rw [hZN, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hZx
      exact hZx
    · rintro _ ⟨c, -, rfl⟩
      exact hexp c
  · rw [Subgroup.card_map_of_injective C.subtype_injective, pow_succ, ← hAQc, ← hNcard,
      mul_comm]
    exact QuotientGroup.card_preimage_mk N (AQ : Set Q)

theorem le_pRank_of_central_ext {L : Type u} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Z : Subgroup L) [Z.Normal] (hZ : Z ≤ Subgroup.center L) (hZp : Nat.card Z = p)
    {E : Subgroup (L ⧸ Z)} (hE : IsElemAbelian p E) {r : ℕ} (hEc : Nat.card E = p ^ r) :
    r / 2 + 1 ≤ pRank p (⊤ : Subgroup L) := by
  classical
  set Ê : Subgroup L := E.comap (QuotientGroup.mk' Z) with hÊ
  have hmk1 : ∀ z ∈ Z, QuotientGroup.mk' Z z = 1 := fun z hz => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hz
  have hZexp : ∀ z ∈ Z, z ^ p = 1 := by
    intro z hz
    have h : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hZp] at h
    exact congrArg Subtype.val h
  have hcomm : ∀ a ∈ Ê, ∀ b ∈ Ê, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    have h1 : QuotientGroup.mk' Z ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
  have hpowZ : ∀ y ∈ Ê, y ^ p ∈ Z := by
    intro y hy
    have h1 : QuotientGroup.mk' Z (y ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hy
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
  let φ : Ê →* Z :=
    { toFun := fun y => ⟨(y : L) ^ p, hpowZ y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact mul_pow_prime_of_central hp hp2 (hZ (hcomm _ b.2 _ a.2))
          (hZexp _ (hcomm _ b.2 _ a.2))) }
  set P : Subgroup L := φ.ker.map Ê.subtype with hPdef
  have hPÊ : P ≤ Ê := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hPpow : ∀ y ∈ P, y ^ p = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hw)
  have hZÊ : Z ≤ Ê := fun z hz => by
    show QuotientGroup.mk' Z z ∈ E
    rw [hmk1 z hz]
    exact E.one_mem
  have hZP : Z ≤ P := fun z hz =>
    ⟨⟨z, hZÊ hz⟩, MonoidHom.mem_ker.mpr (Subtype.ext (hZexp z hz)), rfl⟩
  have hÊc : Nat.card Ê = p ^ (r + 1) := by
    have h := QuotientGroup.card_preimage_mk Z (E : Set (L ⧸ Z))
    rw [pow_succ, ← hEc, ← hZp, mul_comm]
    exact h
  have hPc : Nat.card P = Nat.card φ.ker :=
    Subgroup.card_map_of_injective Ê.subtype_injective
  have hker := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ p := by
    rw [← hZp]; exact Subgroup.card_le_card_group φ.range
  have hPdvd : Nat.card P ∣ p ^ (r + 1) := by
    rw [hPc, ← hÊc]; exact Subgroup.card_subgroup_dvd_card φ.ker
  obtain ⟨t, -, hPt⟩ := (Nat.dvd_prime_pow hp).mp hPdvd
  have hrt : r ≤ t := by
    have h1 : p ^ (r + 1) ≤ p ^ (t + 1) := by
      rw [← hÊc, ← hker, pow_succ, ← hPt, hPc]
      exact Nat.mul_le_mul_left _ hrange
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  have ht1 : 1 ≤ t := by
    by_contra h0
    push Not at h0
    have h1 : Nat.card Z ≤ Nat.card P := Subgroup.card_le_of_le hZP
    rw [hZp, hPt, Nat.lt_one_iff.mp h0, pow_zero] at h1
    exact absurd h1 (by have := hp.two_le; omega)
  have hexpP : ∀ x : P, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hPpow x x.2)
  have hZc' : Z.subgroupOf P ≤ Subgroup.center P := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hz)) (g : L)
  have hZcard' : Nat.card (Z.subgroupOf P) = p := by
    rw [← hZp]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hcomm' : commutator P ≤ Z.subgroupOf P := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((⁅a, b⁆ : P) : L) = ⁅(a : L), (b : L)⁆ := by simp [commutatorElement_def]
    rw [h1]
    exact hcomm _ (hPÊ a.2) _ (hPÊ b.2)
  have hPcard' : Nat.card P = p ^ (t - 1 + 1) := by rw [Nat.sub_add_cancel ht1]; exact hPt
  obtain ⟨A, hA, k, hk, hAc⟩ :=
    exists_elemAbelian_of_exponent_central hp (t - 1) P hexpP (Z.subgroupOf P) hZc' hZcard'
      hcomm' hPcard'
  have hAc' : Nat.card (A.map P.subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hAc]
  have h1 := CFSG.SectionRank.le_pRank hp.one_lt le_top
    (CFSG.SectionRank.isElemAbelian_map hA P.subtype) hAc'
  have h2 : r / 2 ≤ (t - 1 + 1) / 2 := Nat.div_le_div_right (by omega)
  omega

theorem pRank_quotient_le_of_central {L : Type u} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Z : Subgroup L) [Z.Normal] (hZ : Z ≤ Subgroup.center L)
    (hZp : Nat.card Z = p) :
    pRank p (⊤ : Subgroup (L ⧸ Z)) / 2 + 1 ≤ pRank p (⊤ : Subgroup L) := by
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (L ⧸ Z))
  exact le_pRank_of_central_ext hp hp2 Z hZ hZp hE hEc

end CFSG.HardMathSupport.Timmesfeld.Coordinator
