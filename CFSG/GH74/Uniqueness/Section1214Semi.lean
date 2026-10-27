module

public import CFSG.GH74.Uniqueness.Section12Stmts
public import CFSG.GH74.Uniqueness.Section12Aux
public import CFSG.GH74.Uniqueness.Bender.SuzukiOdd
public import CFSG.GH74.Uniqueness.Section7Cor713Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem mul_comm_of_mem_cenHull {u x : X} (hx : x ∈ cenHull Z u) : u * x = x * u := by
  have h : x ∈ centralizer ({u} : Set X) := Cor713.zHull_le (Z := Z) (centralizer ({u} : Set X)) hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

omit [Finite X] in
theorem conjugate_fixed_iff {β : Subgroup X} {l u : X} (h : u * l = l * u) :
    conjugate (conjugate β l) u = conjugate β l ↔ conjugate β u = β := by
  rw [conjugate_conjugate, ← h, ← conjugate_conjugate]
  constructor
  · intro h'
    exact conjugate_injective l h'
  · intro h'
    rw [h']

theorem ZDSetup.semiregular_two (S : ZDSetup X Z M) {u x : X} (hux : u * x = x * u)
    (hxZ : x ∈ Z) {β : Subgroup X} (hβ : β ∈ omega M) (hβu : conjugate β u ≠ β)
    (hx : conjugate β x = β) : False := by
  obtain ⟨γ, -, huniq⟩ := S.prodDisc.existsUnique_fixed_point S.invariant hxZ
  have h1 := huniq β ⟨hβ, hx⟩
  have h2 := huniq (conjugate β u) ⟨conjugate_mem_omega hβ u, by
    rw [conjugate_conjugate, hux, ← conjugate_conjugate, hx]⟩
  exact hβu (h2.trans h1.symm)

omit [Finite X] in
theorem eq_one_of_mul_self_of_odd_orderOf {x : X} (hx : x * x = 1) (hodd : Odd (orderOf x)) :
    x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

section Odd

variable {c : Ctx12 Z M} {n i : ℕ}

omit [Finite X] in
theorem not_dvd_card_factor {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ n - 1) (i : ℕ) :
    ¬ p ∣ ((2 ^ n) ^ i + 1) * (2 ^ n) ^ i := by
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hmod : 1 ≡ 2 ^ n [MOD p] := (Nat.modEq_iff_dvd' hq1).mpr hpd
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · have h2 : (2 ^ n) ^ i + 1 ≡ 1 ^ i + 1 [MOD p] := (hmod.symm.pow i).add_right 1
    have h3 : 1 ^ i + 1 ≡ 0 [MOD p] := h2.symm.trans (Nat.modEq_zero_iff_dvd.mpr h1)
    have h4 : p ∣ 2 := by
      have := Nat.modEq_zero_iff_dvd.mp h3
      simpa using this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
  · have h2 := hp.dvd_of_dvd_pow h1
    have h3 := hp.dvd_of_dvd_pow h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

omit [Finite X] in
theorem factorization_card_L
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ n - 1)
    {L : Type*} [Group L] [Finite L] (hB : Bender.BenderType L n i 1) :
    (Nat.card L).factorization p = (2 ^ n - 1).factorization p := by
  have hcard := hB.card_eq
  have hq0 : 0 < 2 ^ n := by positivity
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hpos : 0 < 2 ^ n - 1 := by
    have : 2 ≤ 2 ^ n := by
      have := hB.two_le
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hne1 : ((2 ^ n) ^ i + 1) ≠ 0 := Nat.succ_ne_zero _
  have hne2 : ((2 ^ n) ^ i) ≠ 0 := by positivity
  have h0 := not_dvd_card_factor (n := n) hp hp2 hpd i
  have hnd1 : ¬ p ∣ ((2 ^ n) ^ i + 1) := fun h => h0 (Dvd.dvd.mul_right h _)
  have hnd2 : ¬ p ∣ ((2 ^ n) ^ i) := fun h => h0 (Dvd.dvd.mul_left h _)
  rw [hcard, mul_one, Nat.factorization_mul hne1 (mul_ne_zero hne2 hpos.ne'),
    Nat.factorization_mul hne2 hpos.ne']
  have h1 := Nat.factorization_eq_zero_of_not_dvd hnd1
  have h2 := Nat.factorization_eq_zero_of_not_dvd hnd2
  simp only [Finsupp.add_apply]
  rw [h1, h2]
  simp

theorem LData.exists_conj_mem_K
    (hL : LData c n i) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ 2 ^ n - 1) {x : X} (hxL : x ∈ c.L) (hxp : orderOf x = p) :
    ∃ l ∈ c.L, l * x * l⁻¹ ∈ kGrp M c.t := by
  have : Fact p.Prime := ⟨hp⟩
  set K' : Subgroup ↥c.L := (c.D ⊓ c.L).subgroupOf c.L with hK'
  have hK'card : Nat.card K' = 2 ^ n - 1 := by
    have h1 : Nat.card K' = Nat.card ↥(c.D ⊓ c.L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1]
    exact hL.k_card
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥K'))
  set R : Subgroup ↥c.L := (P : Subgroup ↥K').map K'.subtype with hR
  have hRcard : Nat.card R = p ^ (Nat.card ↥c.L).factorization p := by
    have h1 : Nat.card R = Nat.card (P : Subgroup ↥K') :=
      Subgroup.card_map_of_injective K'.subtype_injective
    rw [h1, P.card_eq_multiplicity, hK'card, factorization_card_L hp hp2 hpd hL.bender]
  have hx : IsPGroup p (zpowers (⟨x, hxL⟩ : ↥c.L)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hxp, pow_one]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card_eq hRcard hx
  refine ⟨(g : X), g.2, ?_⟩
  have hgK : g * ⟨x, hxL⟩ * g⁻¹ ∈ K' := by
    obtain ⟨r, hr, hrg⟩ := hg
    rw [← hrg]
    exact r.2
  rw [hL.k_eq']
  exact Subgroup.mem_subgroupOf.mp hgK

theorem LData.ncard_inter_point (S : ZDSetup X Z M) (hL : LData c n i) {β : Subgroup X}
    (hβ : β ∈ omega M) : (Z ∩ (β : Set X)).ncard = 2 ^ n - 1 := by
  obtain ⟨g, rfl⟩ := hβ
  have h1 : zNum Z (conjugate M g) = zNum Z M := zNum_conjugate S.invariant M g
  have h2 : zNum Z M = 2 ^ n - 1 := by
    have h3 : Z ∩ (M : Set X) = (zHull Z M : Set X) \ {1} := hL.zM_eq
    unfold zNum
    rw [h3, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _),
      ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) hL.m_card
  have h4 : zNum Z (conjugate M g) = (Z ∩ ((conjugate M g : Subgroup X) : Set X)).ncard :=
    Nat.card_coe_set_eq _
  rw [← h4, h1, h2]

theorem LData.exists_commuting_mem_inter (S : ZDSetup X Z M) (hL : LData c n i) {p : ℕ}
    (hp : p.Prime) (hpd : ¬ p ∣ 2 ^ n - 1) {x : X} (hxp : orderOf x = p) {β : Subgroup X}
    (hβ : β ∈ omega M) (hxβ : x ∈ β) : ∃ s ∈ Z, s ∈ β ∧ x * s = s * x := by
  have hinv : ∀ a ∈ Z ∩ (β : Set X), x⁻¹ * a * x ∈ Z ∩ (β : Set X) := fun a ha =>
    ⟨S.invariant.2 a ha.1 x, β.mul_mem (β.mul_mem (β.inv_mem hxβ) ha.2) hxβ⟩
  obtain ⟨s, ⟨hsZ, hsβ⟩, hxs⟩ := exists_commute_of_not_dvd_ncard (Set.toFinite _) hp hxp hinv
    (by rw [hL.ncard_inter_point S hβ]; exact hpd)
  exact ⟨s, hsZ, hsβ, hxs⟩

omit [Finite X] in
theorem mem_normalizer_zpowers_of_inv {x y : X} (hy : y * y = 1) (hyx : y * x * y⁻¹ = x⁻¹) :
    y ∈ normalizer ((zpowers x : Subgroup X) : Set X) := by
  have hconj : ∀ h ∈ zpowers x, y * h * y⁻¹ ∈ zpowers x := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have h1 : y * x ^ k * y⁻¹ = (y * x * y⁻¹) ^ k := by
      simp
    rw [h1, hyx, inv_zpow']
    exact Subgroup.mem_zpowers_iff.mpr ⟨-k, rfl⟩
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj h, fun hh => ?_⟩
  have := hconj _ hh
  have e : y * (y * h * y⁻¹) * y⁻¹ = h := by
    rw [hyi]
    calc y * (y * h * y) * y = (y * y) * h * (y * y) := by group
      _ = h := by rw [hy]; simp
  rwa [e] at this

theorem ZDSetup.semiregular_odd_ndvd
    (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M)
    (hL : LData c n i) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ 2 ^ n - 1) {x : X}
    (hxL : x ∈ c.L) (hxp : orderOf x = p) {β : Subgroup X} (hβ : β ∈ omega M)
    (hx : conjugate β x = β) : False := by
  have hxβ : x ∈ β := (S.prodDisc.conjugate_eq_iff_mem hβ).mp hx
  obtain ⟨s, hsZ, -, hxs⟩ := hL.exists_commuting_mem_inter S hp hpd hxp hβ hxβ
  have hodd : Odd (orderOf x) := by rw [hxp]; exact hp.odd_of_ne_two hp2
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne' hxp.symm
  obtain ⟨y, hy2, hy1, hyx⟩ : ∃ y : ↥c.L, y * y = 1 ∧ y ≠ 1 ∧
      y * (⟨x, hxL⟩ : ↥c.L) * y⁻¹ = (⟨x, hxL⟩ : ↥c.L)⁻¹ := by
    have hne : (⟨x, hxL⟩ : ↥c.L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hodd' : Odd (orderOf (⟨x, hxL⟩ : ↥c.L)) := by rwa [Subgroup.orderOf_mk]
    have hcen : (⟨x, hxL⟩ : ↥c.L) ∈ centralizer ({(⟨x, hxL⟩ : ↥c.L)} : Set ↥c.L) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    rcases hL.hi with h1 | h2
    · have hB : Bender.BenderType ↥c.L n 1 1 := h1 ▸ hL.bender
      obtain ⟨-, -, -, w, hw2, hwinv, -⟩ := hB.linear_odd_element hne hodd'
      refine ⟨w, hw2, ?_, hwinv _ hcen⟩
      intro hw
      have := hwinv _ hcen
      rw [hw] at this
      simp only [one_mul, inv_one, mul_one] at this
      exact hne (eq_one_of_mul_self_of_odd_orderOf (mul_eq_one_iff_eq_inv.mpr this) hodd')
    · have hB : Bender.BenderType ↥c.L n 2 1 := h2 ▸ hL.bender
      obtain ⟨⟨y, hyN, hy2, hy1⟩, hinv⟩ := hB.suzuki_odd_involution hne hodd'
      exact ⟨y, hy2, hy1, hinv y hyN hy2 hy1 _ hcen⟩
  have hy2X : (y : X) * y = 1 := congrArg Subtype.val hy2
  have hy1X : (y : X) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyX : (y : X) * x * (y : X)⁻¹ = x⁻¹ := congrArg Subtype.val hyx
  have hyorder : orderOf (y : X) = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1X
  have hyZ : (y : X) ∈ Z := hL.invol y y.2 hyorder
  have hne : (y : X) * x ≠ x * (y : X) := by
    intro h
    have : x * (y : X) * (y : X)⁻¹ = x⁻¹ := by rw [← h]; exact hyX
    rw [mul_inv_cancel_right] at this
    exact hx1 (eq_one_of_mul_self_of_odd_orderOf (mul_eq_one_iff_eq_inv.mpr this) hodd)
  have hYodd : Odd (Nat.card (zpowers x)) := by rw [Nat.card_zpowers, hxp]; exact hp.odd_of_ne_two hp2
  have hbot := (h1212 c n i hL (zpowers x) hYodd
    ⟨(y : X), hyZ, mem_normalizer_zpowers_of_inv hy2X hyX, x, Subgroup.mem_zpowers x, hne⟩).2
  have hsC : s ∈ centralizer ((zpowers x : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute x s from hxs) k).eq)
  have hs1 : s ∈ zHull Z (centralizer ((zpowers x : Subgroup X) : Set X)) :=
    Subgroup.subset_closure ⟨hsZ, hsC⟩
  rw [hbot, Subgroup.mem_bot] at hs1
  have hs2 := S.invariant.1 s hsZ
  rw [hs1, orderOf_one] at hs2
  exact absurd hs2 (by norm_num)

theorem ZDSetup.semiregular_prime
    (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M)
    (h1213 : Prop1213Stmt Z M) (hL : LData c n i) {u : X} (hu : u ∈ c.D)
    (hLu : cenHull Z u = c.L) {p : ℕ} (hp : p.Prime) {x : X} (hxL : x ∈ c.L)
    (hxp : orderOf x = p) {β : Subgroup X} (hβ : β ∈ omega M) (hβu : conjugate β u ≠ β)
    (hx : conjugate β x = β) : False := by
  by_cases hp2 : p = 2
  · subst hp2
    exact S.semiregular_two (mul_comm_of_mem_cenHull (hLu ▸ hxL)) (hL.invol x hxL hxp) hβ hβu hx
  by_cases hpd : p ∣ 2 ^ n - 1
  · obtain ⟨l, hl, hlx⟩ := hL.exists_conj_mem_K hp hp2 hpd hxL hxp
    have hx1' : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxp
      exact hp.one_lt.ne' hxp.symm
    have hx1 : l * x * l⁻¹ ≠ 1 := by
      intro h
      rw [mul_inv_eq_one] at h
      exact hx1' (mul_left_cancel (h.trans (mul_one l).symm))
    have h13 := h1213 c n i hL _ hlx hx1
    have hβ' : conjugate β l⁻¹ ∈ omega M := conjugate_mem_omega hβ _
    have hfix : conjugate (conjugate β l⁻¹) (l * x * l⁻¹) = conjugate β l⁻¹ := by
      calc conjugate (conjugate β l⁻¹) (l * x * l⁻¹) = conjugate β (l⁻¹ * (l * x * l⁻¹)) :=
            conjugate_conjugate _ _ _
        _ = conjugate β (x * l⁻¹) := by group
        _ = conjugate (conjugate β x) l⁻¹ := (conjugate_conjugate _ _ _).symm
        _ = conjugate β l⁻¹ := by rw [hx]
    have hmem : conjugate β l⁻¹ ∈ omegaFix M {l * x * l⁻¹} :=
      ⟨hβ', fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact hfix⟩
    rw [h13] at hmem
    have hu_fix : conjugate (conjugate β l⁻¹) u = conjugate β l⁻¹ := by
      rcases hmem with h | h
      · rw [h]
        exact (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (Subgroup.mem_inf.mp hu).1
      · rw [Set.mem_singleton_iff.mp h]
        exact (S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mpr (Subgroup.mem_inf.mp hu).2
    have hl' : u * l⁻¹ = l⁻¹ * u := mul_comm_of_mem_cenHull (hLu ▸ c.L.inv_mem hl)
    exact hβu ((conjugate_fixed_iff hl').mp hu_fix)
  · exact S.semiregular_odd_ndvd h1212 hL hp hp2 hpd hxL hxp hβ hx

theorem ZDSetup.semiregular
    (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M)
    (h1213 : Prop1213Stmt Z M) (hL : LData c n i) {u : X} (hu : u ∈ c.D)
    (hLu : cenHull Z u = c.L) {x : X} (hxL : x ∈ c.L) (hx1 : x ≠ 1) {β : Subgroup X}
    (hβ : β ∈ omega M) (hβu : conjugate β u ≠ β) (hx : conjugate β x = β) : False := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h) : orderOf x ≠ 1)
  have hord : orderOf (x ^ (orderOf x / p)) = p :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' hpd
  have hxβ : x ∈ β := (S.prodDisc.conjugate_eq_iff_mem hβ).mp hx
  exact S.semiregular_prime h1212 h1213 hL hu hLu hp (Subgroup.pow_mem _ hxL _) hord hβ hβu
    ((S.prodDisc.conjugate_eq_iff_mem hβ).mpr (Subgroup.pow_mem _ hxβ _))

end Odd

end CFSG.GH74.Uniqueness
