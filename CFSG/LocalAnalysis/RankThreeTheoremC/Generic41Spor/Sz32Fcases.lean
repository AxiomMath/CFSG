module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup
open scoped commutatorElement

section Abstract

variable {X : Type*} [Group X]

section Facts

variable {Q : Subgroup X} {a c y x : X}

theorem szk_finite_Q (hQ : Sz32QFacts Q a c y x) : Finite Q :=
  Nat.finite_of_card_ne_zero (by rw [hQ.card]; norm_num)

theorem szk_finite_of_le (hQ : Sz32QFacts Q a c y x) {H : Subgroup X} (h : H ≤ Q) : Finite H := by
  haveI := szk_finite_Q hQ
  exact Finite.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

theorem szk_card_zpowers_x (hQ : Sz32QFacts Q a c y x) : Nat.card (Subgroup.zpowers x) = 5 := by
  rw [hQ.x_eq, Nat.card_zpowers,
    orderOf_pow_of_dvd (by norm_num) (by rw [hQ.ord_c]; norm_num), hQ.ord_c]

theorem szk_x_mem_Z (hQ : Sz32QFacts Q a c y x) : x ∈ sz32Z a c := by
  have h : x ∈ Subgroup.zpowers (c ^ 5) := hQ.x_eq ▸ Subgroup.mem_zpowers x
  exact (le_sup_right : Subgroup.zpowers (c ^ 5) ≤ sz32Z a c) h

theorem szk_Z_le_Q (hQ : Sz32QFacts Q a c y x) : sz32Z a c ≤ Q :=
  (le_sup_left : sz32Z a c ≤ sz32Om a c y).trans hQ.Om_le

theorem szk_omega_eq (hQ : Sz32QFacts Q a c y x) {U F : Subgroup X}
    (hU : Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U) (hUF : U ≤ F) (hFQ : F ≤ Q)
    (hrank : ∀ E : Subgroup X, E ≤ F → IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 2) :
    ∀ f ∈ F, f ^ 5 = 1 → f ∈ U := by
  intro f hf hf5
  haveI hOmc : IsMulCommutative (sz32Om a c y) := hQ.Om_elem.1
  have hfOm : f ∈ sz32Om a c y := hQ.Om_all f (hFQ hf) hf5
  have hEOm : U ⊔ Subgroup.zpowers f ≤ sz32Om a c y :=
    sup_le hU.le_Om (Subgroup.zpowers_le.2 hfOm)
  have hEF : U ⊔ Subgroup.zpowers f ≤ F := sup_le hUF (Subgroup.zpowers_le.2 hf)
  have hEel : IsElemAbelian 5 (U ⊔ Subgroup.zpowers f : Subgroup X) :=
    ⟨isMulCommutative_anti hEOm, fun e he => hQ.Om_elem.2 e (hEOm he)⟩
  have hcard := hrank _ hEF hEel
  haveI : Finite (U ⊔ Subgroup.zpowers f : Subgroup X) := szk_finite_of_le hQ (hEF.trans hFQ)
  have hUE : U = U ⊔ Subgroup.zpowers f :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hU.card]; exact hcard)
  have hfE : f ∈ U ⊔ Subgroup.zpowers f := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  rwa [← hUE] at hfE

theorem szk_inf_Z_eq (hQ : Sz32QFacts Q a c y x) {U F : Subgroup X}
    (hU : Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U) (hUF : U ≤ F)
    (hΩ : ∀ f ∈ F, f ^ 5 = 1 → f ∈ U) : F ⊓ sz32Z a c = Subgroup.zpowers x := by
  apply le_antisymm
  · intro z hz
    have hzU : z ∈ U := hΩ z hz.1 (hQ.Z_elem.2 z hz.2)
    have h : z ∈ U ⊓ sz32Z a c := ⟨hzU, hz.2⟩
    rwa [hU.inf_Z] at h
  · exact le_inf ((Subgroup.zpowers_le.2 hU.mem).trans hUF)
      (Subgroup.zpowers_le.2 (szk_x_mem_Z hQ))

theorem szk_not_zpowers_a5 (hQ : Sz32QFacts Q a c y x) {U F : Subgroup X}
    (hU : Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U) (hUF : U ≤ F)
    (hΩ : ∀ f ∈ F, f ^ 5 = 1 → f ∈ U) : ¬ Subgroup.zpowers (a ^ 5) ≤ F := by
  intro h
  have ha5F : a ^ 5 ∈ F := h (Subgroup.mem_zpowers _)
  have ha5Z : a ^ 5 ∈ sz32Z a c :=
    (le_sup_left : Subgroup.zpowers (a ^ 5) ≤ sz32Z a c) (Subgroup.mem_zpowers _)
  have hmem : a ^ 5 ∈ Subgroup.zpowers x := by
    rw [← szk_inf_Z_eq hQ hU hUF hΩ]
    exact ⟨ha5F, ha5Z⟩
  rw [hQ.x_eq] at hmem
  have hle : sz32Z a c ≤ Subgroup.zpowers (c ^ 5) := sup_le (Subgroup.zpowers_le.2 hmem) le_rfl
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hQ.Z_card, Nat.card_zpowers,
    orderOf_pow_of_dvd (by norm_num) (by rw [hQ.ord_c]; norm_num), hQ.ord_c] at hdvd
  omega

theorem szk_pow_comm_aux {G : Type*} [Group G] {f g t : G} (htg : Commute t g)
    (h : g * f = t * (f * g)) (n : ℕ) : g ^ n * f = t ^ n * (f * g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc g ^ (n + 1) * f = g * (g ^ n * f) := by rw [pow_succ', mul_assoc]
      _ = g * (t ^ n * (f * g ^ n)) := by rw [ih]
      _ = (g * t ^ n) * (f * g ^ n) := by rw [mul_assoc]
      _ = (t ^ n * g) * (f * g ^ n) := by rw [(htg.symm.pow_right n).eq]
      _ = t ^ n * ((g * f) * g ^ n) := by simp only [mul_assoc]
      _ = t ^ n * ((t * (f * g)) * g ^ n) := by rw [h]
      _ = t ^ (n + 1) * (f * g ^ (n + 1)) := by
          rw [pow_succ t n, pow_succ' g n]
          simp only [mul_assoc]

theorem szk_mul_pow_aux {G : Type*} [Group G] {f g t : G} (htf : Commute t f) (htg : Commute t g)
    (h : g * f = t * (f * g)) (n : ℕ) : (f * g) ^ n = t ^ (n.choose 2) * (f ^ n * g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 := szk_pow_comm_aux htg h n
    have hfn : f ^ n * t ^ n = t ^ n * f ^ n := ((htf.pow_pow n n).eq).symm
    have hc : (n + 1).choose 2 = n.choose 2 + n := by
      rw [show (2:ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    calc (f * g) ^ (n + 1) = (f * g) ^ n * (f * g) := pow_succ _ _
      _ = (t ^ n.choose 2 * (f ^ n * g ^ n)) * (f * g) := by rw [ih]
      _ = t ^ n.choose 2 * (f ^ n * (g ^ n * f) * g) := by simp only [mul_assoc]
      _ = t ^ n.choose 2 * (f ^ n * (t ^ n * (f * g ^ n)) * g) := by rw [h2]
      _ = t ^ n.choose 2 * (t ^ n * (f ^ n * (f * g ^ n)) * g) := by
          rw [← mul_assoc (f ^ n) (t ^ n), hfn, mul_assoc (t ^ n)]
      _ = t ^ (n + 1).choose 2 * (f ^ (n + 1) * g ^ (n + 1)) := by
          rw [hc, pow_add, pow_succ f n, pow_succ g n]
          simp only [mul_assoc]

theorem szk_pow5_mul (hQ : Sz32QFacts Q a c y x) {f g : X} (hf : f ∈ Q) (hg : g ∈ Q) :
    (f * g) ^ 5 = f ^ 5 * g ^ 5 := by
  have htmem : ⁅g, f⁆ ∈ sz32Z a c := hQ.comm_eq ▸ Subgroup.commutator_mem_commutator hg hf
  have htQ : ⁅g, f⁆ ∈ Q := szk_Z_le_Q hQ htmem
  have hcen : ∀ q ∈ Q, q * ⁅g, f⁆ = ⁅g, f⁆ * q := fun q hq => (hQ.center _ htQ).2 htmem q hq
  have htf : Commute ⁅g, f⁆ f := (hcen f hf).symm
  have htg : Commute ⁅g, f⁆ g := (hcen g hg).symm
  have h : g * f = ⁅g, f⁆ * (f * g) := by simp [commutatorElement_def, mul_assoc]
  have ht5 : ⁅g, f⁆ ^ 5 = 1 := hQ.Z_elem.2 _ htmem
  rw [szk_mul_pow_aux htf htg h 5, show Nat.choose 5 2 = 5 * 2 from by decide, pow_mul, ht5]
  simp

theorem szk_card_F (hQ : Sz32QFacts Q a c y x) {U F : Subgroup X}
    (hU : Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U) (hUF : U ≤ F) (hFQ : F ≤ Q)
    (hΩ : ∀ f ∈ F, f ^ 5 = 1 → f ∈ U) : F = U ∨ Nat.card F = 5 ^ 3 := by
  haveI : Finite F := szk_finite_of_le hQ hFQ
  let ψ : F →* X := MonoidHom.mk' (fun f : F => (f : X) ^ 5)
    (fun f g => szk_pow5_mul hQ (hFQ f.2) (hFQ g.2))
  have hker : ψ.ker = U.subgroupOf F := by
    ext f
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hΩ f f.2 h
    · intro h
      exact hU.elem.2 f h
  have hrange : ψ.range ≤ Subgroup.zpowers x := by
    rintro _ ⟨f, rfl⟩
    have h1 : (f : X) ^ 5 ∈ F := F.pow_mem f.2 5
    have h2 : (f : X) ^ 5 ∈ sz32Z a c := hQ.pow5 f (hFQ f.2)
    rw [← szk_inf_Z_eq hQ hU hUF hΩ]
    exact ⟨h1, h2⟩
  have hcardker : Nat.card ψ.ker = 5 ^ 2 := by
    rw [hker, ← hU.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUF).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range ψ
  have hdvd : Nat.card ψ.range ∣ 5 := (szk_card_zpowers_x hQ) ▸ Subgroup.card_dvd_of_le hrange
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h1 | h5
  · left
    rw [hcardker, h1] at hmul
    exact (Subgroup.eq_of_le_of_card_ge hUF (by rw [← hmul, hU.card]; norm_num)).symm
  · right
    rw [hcardker, h5] at hmul
    rw [← hmul]
    norm_num

theorem szk_abelian_eq (hQ : Sz32QFacts Q a c y x) {U F : Subgroup X}
    (hU : Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U) (hUF : U ≤ F) (hFQ : F ≤ Q)
    (hrank : ∀ E : Subgroup X, E ≤ F → IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 2)
    (hF : IsMulCommutative F) : F = U := by
  haveI : Finite F := szk_finite_of_le hQ hFQ
  have hUZ : ¬ U ≤ sz32Z a c := by
    intro h
    have h1 : U ⊓ sz32Z a c = U := inf_eq_left.2 h
    rw [hU.inf_Z] at h1
    have h2 := hU.card
    rw [← h1, szk_card_zpowers_x hQ] at h2
    norm_num at h2
  obtain ⟨u, huU, huZ⟩ : ∃ u ∈ U, u ∉ sz32Z a c := by
    by_contra hcon
    push_neg at hcon
    exact hUZ hcon
  have hFOm : F ≤ sz32Om a c y := by
    intro f hf
    refine hQ.cent_le u (hU.le_Om huU) huZ f (hFQ hf) ?_
    exact setLike_mul_comm hf (hUF huU)
  have hel : IsElemAbelian 5 F := ⟨hF, fun f hf => hQ.Om_elem.2 f (hFOm hf)⟩
  have hc := hrank F le_rfl hel
  exact (Subgroup.eq_of_le_of_card_ge hUF (by rw [hU.card]; exact hc)).symm

theorem szk_center (hQ : Sz32QFacts Q a c y x) {U F : Subgroup X}
    (hU : Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U) (hUF : U ≤ F) (hFQ : F ≤ Q)
    (hcard : Nat.card F = 5 ^ 3) (hnc : ¬ IsMulCommutative F) :
    ∀ z ∈ F, (∀ f ∈ F, f * z = z * f) ↔ z ∈ Subgroup.zpowers x := by
  have hxF : x ∈ F := hUF hU.mem
  have hxZ : x ∈ sz32Z a c := szk_x_mem_Z hQ
  have hxc : ∀ f ∈ F, f * x = x * f := fun f hf => (hQ.center x (hFQ hxF)).2 hxZ f (hFQ hf)
  intro z hz
  constructor
  · intro hzc
    haveI hFfin : Finite F := szk_finite_of_le hQ hFQ
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    set x' : F := ⟨x, hxF⟩ with hx'
    have hx'C : x' ∈ Subgroup.center F := Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hxc g g.2))
    have hzxC : Subgroup.zpowers x' ≤ Subgroup.center F := Subgroup.zpowers_le.2 hx'C
    have hx'card : Nat.card (Subgroup.zpowers x') = 5 := by
      rw [Nat.card_zpowers, hx', Subgroup.orderOf_mk, ← Nat.card_zpowers, szk_card_zpowers_x hQ]
    have hdvd5 : 5 ∣ Nat.card (Subgroup.center F) := hx'card ▸ Subgroup.card_dvd_of_le hzxC
    obtain ⟨k, hk⟩ := hdvd5
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center F)
    rw [hcard, hk] at hmul
    have hqk : Nat.card (F ⧸ Subgroup.center F) * k = 25 := by
      have h : 5 * (Nat.card (F ⧸ Subgroup.center F) * k) = 5 * 25 := by
        calc 5 * (Nat.card (F ⧸ Subgroup.center F) * k)
            = Nat.card (F ⧸ Subgroup.center F) * (5 * k) := by ring
          _ = 5 ^ 3 := hmul.symm
          _ = 5 * 25 := by norm_num
      omega
    have hk1 : k = 1 := by
      by_contra hk1
      apply hnc
      have hkd : k ∣ 5 ^ 2 := by
        have : k ∣ 25 := Dvd.intro_left _ hqk
        simpa using this
      have hqd : Nat.card (F ⧸ Subgroup.center F) ∣ 5 := by
        obtain ⟨i, hi, hki⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hkd
        interval_cases i
        · exact absurd (by simpa using hki) hk1
        · have hk5 : k = 5 := by simpa using hki
          rw [hk5] at hqk
          exact ⟨1, by omega⟩
        · have hk25 : k = 25 := by simpa using hki
          rw [hk25] at hqk
          exact ⟨5, by omega⟩
      haveI : IsCyclic (F ⧸ Subgroup.center F) := isCyclic_of_card_dvd_prime hqd
      exact (QuotientGroup.mk' (Subgroup.center F)).isMulCommutative_of_isCyclic_of_ker_le_center
        (by rw [QuotientGroup.ker_mk'])
    have hCcard : Nat.card (Subgroup.center F) = 5 := by rw [hk, hk1]
    have hC : Subgroup.zpowers x' = Subgroup.center F :=
      Subgroup.eq_of_le_of_card_ge hzxC (by rw [hCcard, hx'card])
    have hzC : (⟨z, hz⟩ : F) ∈ Subgroup.center F :=
      Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hzc g g.2))
    rw [← hC] at hzC
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hzC
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    rw [Subgroup.coe_zpow] at this
    exact this
  · intro hzx f hf
    have hzZ : z ∈ sz32Z a c := (Subgroup.zpowers_le.2 hxZ) hzx
    exact (hQ.center z (hFQ hz)).2 hzZ f (hFQ hf)

end Facts

theorem sz32_Fcases {Q : Subgroup X} {a c y x : X} (hQ : Sz32QFacts Q a c y x) {U F : Subgroup X}
    (hU : Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U) (hUF : U ≤ F) (hFQ : F ≤ Q)
    (hrank : ∀ E : Subgroup X, E ≤ F → IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 2) :
    ¬ Subgroup.zpowers (a ^ 5) ≤ F ∧
      (F = U ∨ (Nat.card F = 5 ^ 3 ∧ ¬ IsMulCommutative F ∧ (∀ f ∈ F, f ^ 25 = 1) ∧
        (∀ z ∈ F, (∀ f ∈ F, f * z = z * f) ↔ z ∈ Subgroup.zpowers x) ∧
        (∀ f ∈ F, f ^ 5 = 1 → f ∈ U))) := by
  have hΩ := szk_omega_eq hQ hU hUF hFQ hrank
  refine ⟨szk_not_zpowers_a5 hQ hU hUF hΩ, ?_⟩
  by_cases hFU : F = U
  · exact Or.inl hFU
  · right
    have hcard : Nat.card F = 5 ^ 3 := (szk_card_F hQ hU hUF hFQ hΩ).resolve_left hFU
    have hnc : ¬ IsMulCommutative F := fun hF => hFU (szk_abelian_eq hQ hU hUF hFQ hrank hF)
    exact ⟨hcard, hnc, fun f hf => hQ.exp f (hFQ hf), szk_center hQ hU hUF hFQ hcard hnc, hΩ⟩

end Abstract

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
