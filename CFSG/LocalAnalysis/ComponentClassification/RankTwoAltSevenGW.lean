module

public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenQuot

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.GorensteinWalter

theorem le_of_isPGroup_two {Q : Type*} [Group Q] [Finite Q] {L : Subgroup Q} [L.Normal]
    (hL : Odd L.index) {P : Subgroup Q} (hP : IsPGroup 2 P) : P ≤ L := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (x : Q ⧸ L) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one])
  have h2 : orderOf (x : Q ⧸ L) ∣ L.index := by
    rw [index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) L.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      hL.not_two_dvd_nat)
  have h3 := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem isKleinFour_of_card {V : Type*} [Group V] (h4 : Nat.card V = 4) (hsq : ∀ y : V, y ^ 2 = 1) :
    IsKleinFour V := by
  refine ⟨h4, ?_⟩
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with h | h
  · have : Subsingleton V := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : V)
    omega
  · exact h

theorem mem_of_sq_eq_one {Q : Type*} [Group Q] [Finite Q] {L : Subgroup Q} [L.Normal]
    (hL : Odd L.index) {x : Q} (hx : x ^ 2 = 1) : x ∈ L := by
  have hP : IsPGroup 2 (zpowers x) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hx) : orderOf x ∣ 2 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  exact le_of_isPGroup_two hL hP (mem_zpowers x)

theorem card_sq_eq_one_alt4 : Nat.card {g : alternatingGroup (Fin 4) // g ^ 2 = 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem nonempty_equiv_of_card_five {Q : Type} [Group Q] [Finite Q]
    (hQ : pPrimeCore 2 Q = ⊥) {L : Subgroup Q} [L.Normal] (hLi : Odd L.index)
    {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) (hK5 : Nat.card K = 5)
    (e : L ≃* PSL2 K) : Nonempty (Q ≃* alternatingGroup (Fin 5)) := by
  have hcard : Nat.card (PSL2 K) = 60 := by rw [psl2_card_formula K hK, hK5]; norm_num
  have : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  obtain ⟨θ₀⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard
  set θ : L ≃* alternatingGroup (Fin 5) := e.trans θ₀
  have hCL : centralizer (L : Set Q) ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxL⟩
    have hz : θ ⟨x, hxL⟩ ∈ center (alternatingGroup (Fin 5)) := mem_center_iff.mpr fun g => by
      obtain ⟨b, rfl⟩ := θ.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((mem_centralizer_iff.mp hxC) b b.2)
    rw [alternatingGroup.center_eq_bot (by simp)] at hz
    have h1 : (⟨x, hxL⟩ : L) = 1 := θ.injective (by rw [mem_bot.mp hz, map_one])
    exact mem_bot.mpr (congrArg Subtype.val h1)
  have hinj :
      Function.Injective ((QuotientGroup.mk' L).comp (centralizer (L : Set Q)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcL : (c : Q) ∈ L := (QuotientGroup.eq_one_iff _).mp hc
    have := mem_bot.mp (hCL ▸ (mem_inf.mpr ⟨c.2, hcL⟩ : (c : Q) ∈ centralizer (L : Set Q) ⊓ L))
    exact Subtype.ext this
  have hCodd : Nat.Coprime 2 (Nat.card (centralizer (L : Set Q))) := by
    have hd := Subgroup.card_dvd_of_injective _ hinj
    rw [← index_eq_card] at hd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      fun h2 => hLi.not_two_dvd_nat (h2.trans hd)
  have hC : centralizer (L : Set Q) = ⊥ :=
    (pPrimeCore_eq_bot_iff.mp hQ) _ inferInstance hCodd
  have hφ : Function.Injective (MulAut.conjNormal (H := L) : Q →* MulAut L) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : g ∈ centralizer (L : Set Q) := by
      rw [mem_centralizer_iff]
      intro h hh
      have := congrArg (fun φ : MulAut L => ((φ ⟨h, hh⟩ : L) : Q)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc h * g = g * h * g⁻¹ * g := by rw [this]
        _ = g * h := by group
    rw [hC] at this
    exact mem_bot.mp this
  have hAut : Nat.card (MulAut L) = 120 := by
    rw [Nat.card_congr (MulAut.congr θ).toEquiv,
      ← Nat.card_congr (conjPermEquiv (n := 5) (Or.inl rfl)).toEquiv, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hle : Nat.card Q ≤ 120 := hAut ▸ Nat.card_le_card_of_injective _ hφ
  have hLcard : Nat.card L = 60 := by rw [Nat.card_congr e.toEquiv, hcard]
  have hidx := L.card_mul_index
  rw [hLcard] at hidx
  have hi1 : L.index = 1 := by
    obtain ⟨k, hk⟩ := hLi
    omega
  have hLtop : L = ⊤ := index_eq_one.mp hi1
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)).trans θ⟩

namespace Seven

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 7)} {ψB : B ≃* alternatingGroup (Fin 7)}

theorem odd_card_core [Finite G] : Odd (Nat.card (pPrimeCore 2 (H7 ψA ψB))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
    (pPrimeCore_coprime_card (p := 2) (G := H7 ψA ψB))
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)

theorem not_eight_dvd [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G)) :
    ¬ 8 ∣ Nat.card (H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) := by
  intro h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : 2 ^ 3 ∣ Nat.card (H7 ψA ψB) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 (H7 ψA ψB))]
    exact Dvd.dvd.mul_right h8 _
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 hH
  have hPp : IsPGroup 2 (P.map (H7 ψA ψB).subtype) := IsPGroup.of_card (n := 3) (by
    rw [card_map_of_injective (H7 ψA ψB).subtype_injective, hP])
  have := card_le_card_of_isSylowOf (isSylowOf_VF hco ht1B) (map_subtype_le P) hPp
  rw [card_map_of_injective (H7 ψA ψB).subtype_injective, hP, card_VF] at this
  norm_num at this

theorem eq_one_of_mem_core_of_mul_self [Finite G] {h : H7 ψA ψB} (h2 : h * h = 1)
    (hO : h ∈ pPrimeCore 2 (H7 ψA ψB)) : h = 1 := by
  have hd2 : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  have hodd : Odd (orderOf h) := Odd.of_dvd_nat odd_card_core (Subgroup.orderOf_dvd_natCard _ hO)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

@[expose] noncomputable def Vbar (ψA : A ≃* alternatingGroup (Fin 7))
    (ψB : B ≃* alternatingGroup (Fin 7)) : Subgroup (H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) :=
  ((QuotientGroup.mk' (pPrimeCore 2 (H7 ψA ψB))).comp
    ((VF ψA).subgroupOf (H7 ψA ψB)).subtype).range

theorem mem_Vbar_iff {q : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)} :
    q ∈ Vbar ψA ψB ↔ ∃ s : H7 ψA ψB, (s : G) ∈ VF ψA ∧ (s : H7 ψA ψB ⧸ pPrimeCore 2 _) = q := by
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact ⟨s, mem_subgroupOf.mp hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, mem_subgroupOf.mpr hs⟩, rfl⟩

theorem card_Vbar [Finite G] (hco : AltCoords 7 A B ψA ψB) : Nat.card (Vbar ψA ψB) = 4 := by
  set S := (VF ψA).subgroupOf (H7 ψA ψB)
  have hinj : Function.Injective
      ((QuotientGroup.mk' (pPrimeCore 2 (H7 ψA ψB))).comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : (s : H7 ψA ψB) ∈ pPrimeCore 2 (H7 ψA ψB) := (QuotientGroup.eq_one_iff _).mp hs
    have hs2 : (s : H7 ψA ψB) * s = 1 :=
      Subtype.ext (mul_self_of_mem_VF (mem_subgroupOf.mp s.2))
    exact Subtype.ext (eq_one_of_mem_core_of_mul_self hs2 h1)
  rw [Vbar, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (VF_le_H7 hco (ψB := ψB))).toEquiv, card_VF]

theorem isKleinFour_Vbar [Finite G] (hco : AltCoords 7 A B ψA ψB) : IsKleinFour (Vbar ψA ψB) := by
  refine isKleinFour_of_card (card_Vbar hco) fun y => ?_
  obtain ⟨s, hs, hsy⟩ := mem_Vbar_iff.mp y.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hsy, ← QuotientGroup.mk_pow, Subgroup.coe_one]
  have : s ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, sq]
    exact mul_self_of_mem_VF hs)
  rw [this, QuotientGroup.mk_one]

theorem isPGroup_Vbar [Finite G] (hco : AltCoords 7 A B ψA ψB) : IsPGroup 2 (Vbar ψA ψB) :=
  IsPGroup.of_card (n := 2) (by rw [card_Vbar hco]; norm_num)

theorem VF_le_A : VF ψA ≤ A := by
  rintro _ ⟨t, ht, rfl⟩
  exact mul_mem (mul_mem (inv_mem (x_mem ψA)) (T_le ψA ht)) (inv_mem (inv_mem (x_mem ψA)))

theorem commute_VF_of_inOmega (hco : AltCoords 7 A B ψA ψB) {g : G} (hO : InOmega ψA ψB g)
    {s : G} (hs : s ∈ VF ψA) : g * s = s * g := by
  obtain ⟨k, hk, i, j, rfl⟩ := hO
  have hsH := VF_le_H7 hco (ψB := ψB) hs
  have h1 : Commute s k := (mem_centralizer_iff.mp (mem_inf.mp hk).1) s (VF_le_A hs)
  have h2 : Commute s (w ψA) := mem_centralizer_singleton_iff.mp (mem_inf.mp hsH).1
  have h3 : Commute s (v ψB) := mem_centralizer_singleton_iff.mp (mem_inf.mp hsH).2
  exact ((h1.mul_right (h2.zpow_right i)).mul_right (h3.zpow_right j)).eq.symm

theorem eq_one_of_commute_of_odd
    [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    {L : Subgroup (H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB))} {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hL : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K))
    (hVL : Vbar ψA ψB ≤ L) {s : H7 ψA ψB} (hs : (s : G) ∈ VF ψA) (hs1 : (s : G) ≠ 1)
    {q : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)} (hqL : q ∈ L)
    (hq : (s : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) * q = q * s) (hodd : Odd (orderOf q)) :
    q = 1 := by
  have hs2 : s * s = 1 := Subtype.ext (mul_self_of_mem_VF hs)
  obtain ⟨y, rfl, hys⟩ := exists_lift_commute odd_card_core hs2 q hq
  have hyodd : Odd (orderOf (y : G)) := by
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_odd_mk odd_card_core hodd
  have hO := inOmega_of_mem hco hN ht1B hs hs1 y.2
    (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hys).symm) hyodd
  have hC : (y : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ∈ centralizer (Vbar ψA ψB : Set _) := by
    rw [mem_centralizer_iff]
    intro r hr
    obtain ⟨s', hs', rfl⟩ := mem_Vbar_iff.mp hr
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (commute_VF_of_inOmega hco hO hs').symm
  have hV : (y : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ∈ Vbar ψA ψB := by
    rw [← inf_centralizer_eq_of_linear hK hL hVL (isKleinFour_Vbar hco)]
    exact ⟨hqL, hC⟩
  have hsq := (isKleinFour_Vbar hco).exponent_two
  have h2 : (y : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ^ 2 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨_, hV⟩ : Vbar ψA ψB)
    rw [hsq] at this
    simpa using congrArg Subtype.val this
  have hd := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem exists_involution_Vbar [Finite G] (hco : AltCoords 7 A B ψA ψB) :
    ∃ s : H7 ψA ψB, (s : G) ∈ VF ψA ∧ (s : G) ≠ 1 ∧
      (s : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ∈ Vbar ψA ψB ∧
        (s : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ≠ 1 ∧
          (s : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ^ 2 = 1 := by
  have : Nontrivial (Vbar ψA ψB) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [card_Vbar hco]; norm_num)
  obtain ⟨tb, htb1⟩ := exists_ne (1 : Vbar ψA ψB)
  obtain ⟨s, hs, hst⟩ := mem_Vbar_iff.mp tb.2
  have hs2 : s * s = 1 := Subtype.ext (mul_self_of_mem_VF hs)
  have hne : (s : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ≠ 1 := by
    rw [hst]
    exact fun h => htb1 (Subtype.ext h)
  refine ⟨s, hs, fun h => hne ?_, hst ▸ tb.2, hne, ?_⟩
  · rw [show s = 1 from Subtype.ext h, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, sq, hs2, QuotientGroup.mk_one]

theorem card_eq_three_or_five
    [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    {L : Subgroup (H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB))} [L.Normal] (hLi : Odd L.index)
    {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) (e : L ≃* PSL2 K) :
    Nat.card K = 3 ∨ Nat.card K = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL : Vbar ψA ψB ≤ L := le_of_isPGroup_two hLi (isPGroup_Vbar hco)
  obtain ⟨s, hs, hs1, hsV, hsb1, hsb2⟩ := exists_involution_Vbar hco
  set sb := (s : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) with hsb
  have hsbL : sb ∈ L := hVL hsV
  set t := e ⟨sb, hsbL⟩ with ht_def
  have ht : orderOf t = 2 := by
    rw [ht_def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hsb2 hsb1
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
  have hq3 : 3 ≤ Nat.card K := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases (by omega : p = 2 ∨ 3 ≤ p) with h | h
      · rw [h] at hpodd; exact absurd hpodd (by decide)
      · exact h
    rw [hq]
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have hqodd : Odd (Nat.card K) := by rw [hq]; exact hpodd.pow
  have key : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (Nat.card K : ℤ) ≡ ε [ZMOD 4] →
      (Nat.card K : ℤ) - ε = 4 := by
    intro ε hε1 hε
    obtain ⟨m, hm, ⟨d⟩⟩ :=
      CFSG.ABGDGroups.psl2_centralizer_involution_dihedral ⟨p, n, hp, hpodd, hn, hq⟩ hε hε1 ht
    have hcardC : Nat.card (centralizer ({t} : Set (PSL2 K))) = 2 * m := by
      rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
    have hdvd : 2 * m ∣ Nat.card (H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) := by
      have h1 := Subgroup.card_subgroup_dvd_card (centralizer ({t} : Set (PSL2 K)))
      rw [hcardC, ← Nat.card_congr e.toEquiv] at h1
      exact h1.trans (Subgroup.card_subgroup_dvd_card L)
    have h4 : ¬ 4 ∣ m := fun h =>
      not_eight_dvd hco ht1B ((Nat.mul_dvd_mul_left 2 h).trans hdvd)
    have hmε : (4 : ℤ) ∣ (Nat.card K : ℤ) - ε := hε.symm.dvd
    have hm2 : m % 2 = 0 := by omega
    by_contra hne
    have hm_ne : m ≠ 2 := fun h => hne (by rw [← hm, h]; norm_num)
    set z : centralizer ({t} : Set (PSL2 K)) := d.symm (DihedralGroup.r 1 ^ 2) with hz_def
    have hz : orderOf z = m / 2 := by
      rw [hz_def, MulEquiv.orderOf_eq, orderOf_pow' _ two_ne_zero, DihedralGroup.orderOf_r_one,
        Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hm2)]
    set yL : L := e.symm (z : PSL2 K) with hyL
    have hyc : sb * (yL : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) = (yL : _) * sb := by
      have hzt : (z : PSL2 K) * t = t * z := mem_centralizer_singleton_iff.mp z.2
      have hte : e.symm t = ⟨sb, hsbL⟩ := by rw [ht_def, MulEquiv.symm_apply_apply]
      have := congrArg e.symm hzt
      rw [map_mul, map_mul, hte] at this
      have := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at this
      exact this.symm
    have hyord : orderOf (yL : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) = m / 2 := by
      rw [Subgroup.orderOf_coe, hyL, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hz]
    have hyodd : Odd (orderOf (yL : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB))) := by
      rw [hyord]
      exact Nat.odd_iff.mpr (by omega)
    have h1 := eq_one_of_commute_of_odd hco hN ht1B ⟨p, n, hp, hpodd, hn, hq⟩ (Or.inl ⟨e⟩) hVL
      hs hs1 yL.2 hyc hyodd
    rw [h1, orderOf_one] at hyord
    omega
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqodd) with h | h
  · have := key 1 (Or.inl rfl) (by show (Nat.card K : ℤ) % 4 = 1 % 4; omega)
    right; omega
  · have := key (-1) (Or.inr rfl) (by show (Nat.card K : ℤ) % 4 = (-1) % 4; omega)
    left; omega

theorem not_card_eq_three [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    {L : Subgroup (H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB))} [L.Normal] (hLi : Odd L.index)
    {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3) (e : L ≃* PSL2 K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by simpa [Nat.card_eq_fintype_card] using hK3
  let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let e4 : L ≃* alternatingGroup (Fin 4) :=
    e.trans ((psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup)
  have hVL : Vbar ψA ψB ≤ L := le_of_isPGroup_two hLi (isPGroup_Vbar hco)
  have hsq : ∀ y : Vbar ψA ψB, (y : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ^ 2 = 1 := by
    intro y
    have := Monoid.pow_exponent_eq_one y
    rw [(isKleinFour_Vbar hco).exponent_two] at this
    simpa using congrArg Subtype.val this
  let f : Vbar ψA ψB → {g : alternatingGroup (Fin 4) // g ^ 2 = 1} := fun y =>
    ⟨e4 ⟨y, hVL y.2⟩, by rw [← map_pow]; rw [show (⟨y, hVL y.2⟩ : L) ^ 2 = 1 from
      Subtype.ext (by simpa using hsq y), map_one]⟩
  have hf : Function.Injective f := by
    intro y y' h
    have := e4.injective (congrArg Subtype.val h)
    exact Subtype.ext (congrArg Subtype.val this :)
  have hbij := hf.bijective_of_nat_card_le (by rw [card_sq_eq_one_alt4, card_Vbar hco])
  set sb := ((⟨sB ψB, sB_mem_H7 hco⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB))
  have hsB2 : (⟨sB ψB, sB_mem_H7 hco⟩ : H7 ψA ψB) ^ 2 = 1 := Subtype.ext (by
    have h : a0456 ^ 2 = 1 := Subtype.ext (by decide)
    show ((ψB.symm a0456 : B) : G) ^ 2 = 1
    rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one])
  have hsb2 : sb ^ 2 = 1 := by rw [← QuotientGroup.mk_pow, hsB2, QuotientGroup.mk_one]
  have hsbL : sb ∈ L := mem_of_sq_eq_one hLi hsb2
  obtain ⟨y, hy⟩ := hbij.2 ⟨e4 ⟨sb, hsbL⟩, by rw [← map_pow, show (⟨sb, hsbL⟩ : L) ^ 2 = 1 from
    Subtype.ext (by simpa using hsb2), map_one]⟩
  have hysb : (y : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) = sb := by
    have := e4.injective (congrArg Subtype.val hy)
    exact congrArg Subtype.val this
  obtain ⟨s, hs, hss⟩ := mem_Vbar_iff.mp y.2
  rw [hysb, QuotientGroup.eq] at hss
  exact (not_inOmega_B hco (VF_le_A hs)).2 (inOmega_of_mem_core hco hN ht1B _ hss)

theorem u_bar [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G)) :
    ((⟨u ψA, u_mem_H7 hco⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ≠ 1 ∧
      ((⟨u ψA, u_mem_H7 hco⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ^ 3 = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [QuotientGroup.eq_one_iff] at h
    exact (not_inOmega_A hco).1 (inOmega_of_mem_core hco hN ht1B _ h)
  · rw [← QuotientGroup.mk_pow, show (⟨u ψA, u_mem_H7 hco⟩ : H7 ψA ψB) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact u_pow_three), QuotientGroup.mk_one]

theorem eight_dvd_of_odd {q : ℕ} (hq : Odd q) : 8 ∣ q * (q ^ 2 - 1) := by
  apply Dvd.dvd.mul_left
  have h1 : q ^ 2 % 8 = 1 := by
    rw [Nat.pow_mod]
    rcases (by have := Nat.odd_iff.mp hq; omega :
      q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7) with h | h | h | h <;> rw [h]
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by rcases hq with ⟨k, rfl⟩; omega)
  omega

theorem nonempty_quot_equiv_alt5
    [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G)) :
    Nonempty ((H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) ≃* alternatingGroup (Fin 5)) := by
  have h8 := not_eight_dvd hco ht1B
  rcases gw_cases (hasDihedralSylowTwo_H7 hco ht1B) with h2 | hA | ⟨K, _, _, hK, L, hLn, hLi, hLm⟩
  · exfalso
    obtain ⟨hu1, hu3⟩ := u_bar hco hN ht1B
    obtain ⟨k, hk⟩ := h2 ((⟨u ψA, u_mem_H7 hco⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 _)
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu3) (orderOf_dvd_of_pow_eq_one hk)
    rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at hd
    exact hu1 hd
  · exfalso
    obtain ⟨eA⟩ := hA
    apply h8
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · rcases hLm with hL | hL
    · obtain ⟨e⟩ := hL
      rcases card_eq_three_or_five hco hN ht1B hLi hK e with h3 | h5
      · exact absurd (not_card_eq_three hco hN ht1B hLi h3 e) id
      · exact nonempty_equiv_of_card_five (pPrimeCore_quotient_eq_bot Nat.prime_two) hLi hK h5 e
    · exfalso
      obtain ⟨e⟩ := hL
      apply h8
      have hodd : Odd (Nat.card K) := by
        obtain ⟨p, n, -, hpodd, -, hq⟩ := hK
        rw [hq]
        exact hpodd.pow
      have h1 : 8 ∣ Nat.card L := by
        rw [Nat.card_congr e.toEquiv, pgl2_card_formula]
        exact eight_dvd_of_odd hodd
      exact h1.trans (Subgroup.card_subgroup_dvd_card L)

end Seven

end CFSG.ComponentClassification.RankTwoAlt
