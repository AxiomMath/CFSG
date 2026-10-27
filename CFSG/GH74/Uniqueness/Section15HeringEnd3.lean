module

public import CFSG.GH74.Uniqueness.Section15HeringEnd1
public import CFSG.Quasithin.Background.A1cTransfer
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction

section Group

variable {G : Type*} [Group G]

theorem eq_of_two_pow_mul_odd {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b := by
  have h1 : 2 ^ a ∣ 2 ^ b := by
    have : 2 ^ a ∣ 2 ^ b * v := ⟨u, h.symm⟩
    exact (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hv)).dvd_of_dvd_mul_right this
  have h2 : 2 ^ b ∣ 2 ^ a := by
    have : 2 ^ b ∣ 2 ^ a * u := ⟨v, h⟩
    exact (Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hu)).dvd_of_dvd_mul_right this
  exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1)
    ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2)

theorem orderOf_pow_orderOf_div_two {s : G} (hs : s ≠ 1) {n : ℕ} (hn : s ^ 2 ^ n = 1) :
    orderOf (s ^ (orderOf s / 2)) = 2 := by
  have hfin : IsOfFinOrder s := isOfFinOrder_iff_pow_eq_one.mpr ⟨2 ^ n, by positivity, hn⟩
  have h1 : orderOf s ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hs hj
  apply orderOf_pow_orderOf_div hfin.orderOf_pos.ne'
  rw [hj]
  exact dvd_pow_self 2 hj0

theorem exists_ne_one_commute_of_normalizes [Finite G] {q : ℕ} [hq : Fact q.Prime]
    (S : Subgroup G) {y : G} (hy : y ∈ normalizer (S : Set G)) (hyq : orderOf y = q)
    (hS : ¬ (Nat.card S ≡ 1 [MOD q])) : ∃ s ∈ S, s ≠ 1 ∧ y * s = s * y := by
  classical
  set A := zpowers y with hAdef
  have hA : A ≤ normalizer (S : Set G) := (zpowers_le (H := normalizer _)).mpr hy
  let act : MulAction A S :=
    { smul := fun a s => ⟨(a : G) * s * (a : G)⁻¹, (mem_normalizer_iff.mp (hA a.2) s).mp s.2⟩
      one_smul := fun s => Subtype.ext (show ((1 : A) : G) * s * ((1 : A) : G)⁻¹ = s by simp)
      mul_smul := fun a b s => Subtype.ext (show ((a * b : A) : G) * s * ((a * b : A) : G)⁻¹ =
        (a : G) * ((b : G) * s * (b : G)⁻¹) * (a : G)⁻¹ by simp only [Subgroup.coe_mul]; group) }
  have hAp : IsPGroup q A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyq, pow_one])
  have hmod := hAp.card_modEq_card_fixedPoints (α := S)
  have hfix : ∃ s : S, s ∈ fixedPoints A S ∧ s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : fixedPoints A S = {1} := by
      ext s
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hs
        exact hcon s hs
      · rintro rfl a
        apply Subtype.ext
        change (a : G) * 1 * (a : G)⁻¹ = 1
        group
    rw [hsub, show Nat.card ({1} : Set S) = 1 from Nat.card_unique] at hmod
    exact hS hmod
  obtain ⟨s, hs, hs1⟩ := hfix
  refine ⟨s, s.2, fun h => hs1 (Subtype.ext h), ?_⟩
  have := congrArg Subtype.val (hs ⟨y, mem_zpowers y⟩)
  change y * s * y⁻¹ = s at this
  calc y * s = y * s * y⁻¹ * y := by group
    _ = s * y := by rw [this]

@[expose] def centralInvolutions (S : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ S ∧ (∀ s ∈ S, z * s = s * z) ∧ z ^ 2 = 1}
  mul_mem' := by
    rintro a b ⟨ha, hac, ha2⟩ ⟨hb, hbc, hb2⟩
    refine ⟨S.mul_mem ha hb, fun s hs => ?_, ?_⟩
    · rw [mul_assoc, hbc s hs, ← mul_assoc, hac s hs, mul_assoc]
    · rw [(Commute.mul_pow (hac b hb) 2), ha2, hb2, one_mul]
  one_mem' := ⟨S.one_mem, fun s _ => by simp, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hac, ha2⟩
    refine ⟨S.inv_mem ha, fun s hs => ?_, by rw [inv_pow, ha2, inv_one]⟩
    have := hac s hs
    calc a⁻¹ * s = a⁻¹ * (s * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * s) * a⁻¹ := by rw [this]
      _ = s * a⁻¹ := by group

theorem mem_centralInvolutions {S : Subgroup G} {z : G} :
    z ∈ centralInvolutions S ↔ z ∈ S ∧ (∀ s ∈ S, z * s = s * z) ∧ z ^ 2 = 1 := Iff.rfl

theorem conj_mem_centralInvolutions {S : Subgroup G} {n z : G}
    (hn : n ∈ normalizer (S : Set G)) (hz : z ∈ centralInvolutions S) :
    n * z * n⁻¹ ∈ centralInvolutions S := by
  obtain ⟨hzS, hzc, hz2⟩ := hz
  refine ⟨(mem_normalizer_iff.mp hn z).mp hzS, fun s hs => ?_, by rw [conj_pow, hz2]; group⟩
  have hs' : n⁻¹ * s * n ∈ S := by
    have := (mem_normalizer_iff.mp ((normalizer (S : Set G)).inv_mem hn) s).mp hs
    simpa using this
  have := hzc _ hs'
  calc n * z * n⁻¹ * s = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by rw [this]
    _ = s * (n * z * n⁻¹) := by group

end Group

variable {G Ω : Type*} [Group G] [MulAction G Ω] {p : ℕ} {ω : Ω} {K P : Subgroup G}

theorem EndHyp.card_sylow [Finite G] (h : EndHyp G Ω p ω K P) (S : Sylow 2 G) :
    Nat.card S = 2 ^ p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  have hidx : Odd (S : Subgroup G).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.not_dvd_index)
  have hG := (S : Subgroup G).card_mul_index
  rw [ha, h.card_group] at hG
  rw [ha, eq_of_two_pow_mul_odd hidx h.odd_card_stab hG]

theorem EndHyp.not_dvd_card_normalizer [Finite G] (h : EndHyp G Ω p ω K P) (S : Sylow 2 G) :
    ¬ p ∣ Nat.card (normalizer ((S : Subgroup G) : Set G)) := by
  intro hdvd
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := normalizer ((S : Subgroup G) : Set G)) p hdvd
  have hyG : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe, hy]
  have hS : ¬ (Nat.card S ≡ 1 [MOD p]) := by
    rw [h.card_sylow S]
    intro hmod
    exact not_dvd_two_pow_sub_one h.prime ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm)
  obtain ⟨s, hsS, hs1, hys⟩ := exists_ne_one_commute_of_normalizes (S : Subgroup G) y.2 hyG hS
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨s, hsS⟩
  have hn' : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have ht := orderOf_pow_orderOf_div_two hs1 hn'
  apply h.mul_ne_of_orderOf_eq_two ht h.prime (by have := h.three_le; omega) hyG
  exact ((Commute.pow_right (hys : Commute (y : G) s) _).symm).eq

theorem EndHyp.exists_normalizer_conj [Finite G] (h : EndHyp G Ω p ω K P) (S : Sylow 2 G)
    {z z' : G} (hz : z ∈ centralInvolutions (S : Subgroup G))
    (hz' : z' ∈ centralInvolutions (S : Subgroup G)) (h2 : orderOf z = 2) (h2' : orderOf z' = 2) :
    ∃ n ∈ normalizer ((S : Subgroup G) : Set G), n * z * n⁻¹ = z' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.isConj_of_orderOf_eq_two h2 h2')
  have hwc : Quasithin.IsWeaklyClosedIn (S : Subgroup G) (S : Subgroup G) := by
    intro g hg
    apply Subgroup.eq_of_le_of_card_ge hg
    unfold Quasithin.conjSubgroup
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hcen : ∀ x ∈ centralInvolutions (S : Subgroup G),
      x ∈ centralizer ((S : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro s hs
    exact (hx.2.1 s hs).symm
  obtain ⟨n, hn, hnz⟩ := Quasithin.burnside_fusion_lemma_centralizer S le_rfl hwc (hcen z hz)
    (hcen z' hz') (g := c⁻¹) (by rw [inv_inv]; exact hc)
  exact ⟨n⁻¹, (normalizer _).inv_mem hn, by rw [inv_inv]; exact hnz⟩

theorem EndHyp.card_centralInvolutions_sub_one_dvd [Finite G] (h : EndHyp G Ω p ω K P)
    (S : Sylow 2 G) {z₁ : G} (hz₁ : z₁ ∈ centralInvolutions (S : Subgroup G)) (h1 : z₁ ≠ 1) :
    Nat.card (centralInvolutions (S : Subgroup G)) - 1 ∣
      Nat.card (normalizer ((S : Subgroup G) : Set G)) := by
  classical
  set Z := centralInvolutions (S : Subgroup G) with hZ
  set N := normalizer ((S : Subgroup G) : Set G) with hN
  set N' : Subgroup (ConjAct G) := N.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
    with hN'
  have hord : ∀ z ∈ Z, z ≠ 1 → orderOf z = 2 := by
    intro z hz hz1
    exact orderOf_eq_prime hz.2.2 hz1
  have horbit : orbit N' z₁ = (Z : Set G) \ {1} := by
    ext x
    constructor
    · rintro ⟨⟨c, m, hm, rfl⟩, rfl⟩
      change ConjAct.toConjAct m • z₁ ∈ (Z : Set G) \ {1}
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
      refine ⟨conj_mem_centralInvolutions hm hz₁, ?_⟩
      rw [Set.mem_singleton_iff, conj_eq_one_iff]
      exact h1
    · rintro ⟨hx, hx1⟩
      rw [Set.mem_singleton_iff] at hx1
      obtain ⟨n, hn, hnz⟩ := h.exists_normalizer_conj S hz₁ hx (hord _ hz₁ h1) (hord _ hx hx1)
      refine ⟨⟨ConjAct.toConjAct n, n, hn, rfl⟩, ?_⟩
      change ConjAct.toConjAct n • z₁ = x
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hnz]
  have hdvd : (orbit N' z₁).ncard ∣ Nat.card N' := by
    rw [← index_stabilizer]
    exact (stabilizer N' z₁).index_dvd_card
  have hcardN' : Nat.card N' = Nat.card N :=
    Subgroup.card_map_of_injective (ConjAct.toConjAct : G ≃* ConjAct G).injective
  rw [horbit, hcardN', Set.ncard_sdiff_singleton_of_mem (one_mem Z), ← Nat.card_coe_set_eq]
    at hdvd
  exact hdvd

theorem EndHyp.false_of_central_involutions [Finite G] (h : EndHyp G Ω p ω K P) (S : Sylow 2 G)
    (hZ : ∃ z₁ ∈ (S : Subgroup G), ∃ z₂ ∈ (S : Subgroup G), z₁ ≠ z₂ ∧ orderOf z₁ = 2 ∧
      orderOf z₂ = 2 ∧ ∀ s ∈ (S : Subgroup G), z₁ * s = s * z₁ ∧ z₂ * s = s * z₂) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := h.prime
  have h3 := h.three_le
  obtain ⟨z₁, hz₁S, z₂, hz₂S, h12, ho₁, ho₂, hc⟩ := hZ
  set Z := centralInvolutions (S : Subgroup G) with hZdef
  set N := normalizer ((S : Subgroup G) : Set G) with hNdef
  have hsq : ∀ z : G, orderOf z = 2 → z ^ 2 = 1 := fun z hz => by
    rw [← hz, pow_orderOf_eq_one]
  have hne1 : ∀ z : G, orderOf z = 2 → z ≠ 1 := fun z hz h1 => by
    rw [h1, orderOf_one] at hz
    omega
  have hz₁ : z₁ ∈ Z := ⟨hz₁S, fun s hs => (hc s hs).1, hsq z₁ ho₁⟩
  have hz₂ : z₂ ∈ Z := ⟨hz₂S, fun s hs => (hc s hs).2, hsq z₂ ho₂⟩
  have hZS : Z ≤ S := fun z hz => hz.1
  obtain ⟨r, hrp, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    ((h.card_sylow S) ▸ Subgroup.card_dvd_of_le hZS)
  have hZ3 : 3 ≤ Nat.card Z := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    have hsub : ({1, z₁, z₂} : Set G) ⊆ (Z : Set G) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact one_mem Z
      · exact hz₁
      · exact hz₂
    have h3' : ({1, z₁, z₂} : Set G).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨1, z₁, z₂, (hne1 z₁ ho₁).symm, (hne1 z₂ ho₂).symm, h12, rfl⟩
    rw [← h3']
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hr2 : 2 ≤ r := by
    by_contra hlt
    interval_cases r <;> simp_all
  have hdvdN := h.card_centralInvolutions_sub_one_dvd S hz₁ (hne1 z₁ ho₁)
  rw [hr] at hdvdN
  have hpN := h.not_dvd_card_normalizer S
  have hNG : Nat.card N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
  rw [h.card_group] at hNG
  have hodd : Odd (2 ^ r - 1) := by
    have : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2
    have he : Even (2 ^ r) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    rcases he with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  rcases Nat.lt_or_ge r p with hlt | hge
  ·
    have hcop1 : Nat.Coprime (2 ^ r - 1) (2 ^ p) :=
      Nat.Coprime.pow_right p (Nat.coprime_two_right.mpr hodd)
    have hgcd : Nat.gcd r p = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) hlt))
    have hcop2 : Nat.Coprime (2 ^ r - 1) (2 ^ p - 1) := by
      rw [Nat.Coprime, Nat.pow_sub_one_gcd_pow_sub_one, hgcd, pow_one]
    have h1 : 2 ^ r - 1 ∣ p :=
      hcop2.dvd_of_dvd_mul_left (hcop1.dvd_of_dvd_mul_left (hdvdN.trans hNG))
    rcases (Nat.dvd_prime hp).mp h1 with h1 | h1
    · have : 4 ≤ 2 ^ r := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
      omega
    · exact hpN (h1 ▸ hdvdN)
  ·
    have hrp' : r = p := le_antisymm hrp hge
    subst hrp'
    have h2S : 2 ^ r ∣ Nat.card N := by
      rw [← h.card_sylow S]
      exact Subgroup.card_dvd_of_le (Subgroup.le_normalizer)
    have hcop : Nat.Coprime (2 ^ r) (2 ^ r - 1) :=
      Nat.Coprime.symm (Nat.Coprime.pow_right r (Nat.coprime_two_right.mpr hodd))
    obtain ⟨e, he⟩ := hcop.mul_dvd_of_dvd_of_dvd h2S hdvdN
    have hpos : 0 < 2 ^ r * (2 ^ r - 1) := by
      have : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2
      exact Nat.mul_pos (by positivity) (by omega)
    have he1 : e ∣ r := by
      rw [he, ← mul_assoc] at hNG
      exact (Nat.mul_dvd_mul_iff_left hpos).mp hNG
    have hN : Nat.card N = 2 ^ r * (2 ^ r - 1) := by
      rcases (Nat.dvd_prime hp).mp he1 with he1 | he1
      · rw [he, he1, mul_one]
      · exfalso
        apply hpN
        rw [he, he1]
        exact dvd_mul_left _ _
    set H := stabilizer G ω with hH
    have hcardG := h.card_group
    have hNidx : N.index = r := by
      have := N.card_mul_index
      rw [hN, hcardG] at this
      have : 2 ^ r * (2 ^ r - 1) * N.index = 2 ^ r * (2 ^ r - 1) * r := by rw [this]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have hHidx : H.index = 2 ^ r := by
      have := H.card_mul_index
      rw [h.card_stab, hcardG] at this
      have hpos' : 0 < (2 ^ r - 1) * r := by
        have : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2
        exact Nat.mul_pos (by omega) hp.pos
      have : (2 ^ r - 1) * r * H.index = (2 ^ r - 1) * r * 2 ^ r := by rw [this]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos' this
    have hKn : (K.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff h.K_le]
      intro k x hk hx
      exact h.K_normal x hx k hk
    have hKidx : (K.subgroupOf H).index = r := by
      have h1 := (K.subgroupOf H).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe h.K_le).toEquiv, h.card_K, h.card_stab] at h1
      have hpos' : 0 < 2 ^ r - 1 := by
        have : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2
        omega
      exact Nat.eq_of_mul_eq_mul_left hpos' h1
    have hpow : ∀ x ∈ H, x ^ r ∈ K := by
      intro x hx
      have := Subgroup.pow_index_mem (K.subgroupOf H) ⟨x, hx⟩
      rw [hKidx] at this
      simpa using (mem_subgroupOf.mp this)
    have hHNK : H ⊓ N ≤ K := by
      intro x hx
      have hcop' : Nat.Coprime r (Nat.card (H ⊓ N : Subgroup G)) := by
        apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
        intro hd
        exact hpN (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
      have hx1 : x ^ Nat.card (H ⊓ N : Subgroup G) = 1 := by
        have := pow_card_eq_one' (G := (H ⊓ N : Subgroup G)) (x := ⟨x, hx⟩)
        simpa using congrArg Subtype.val this
      exact mem_of_pow_mem_of_coprime (hpow x hx.1) (by rw [hx1]; exact one_mem K) hcop'
    have hHNcard : 2 ^ r - 1 ≤ Nat.card (H ⊓ N : Subgroup G) := by
      have h1 := (H ⊓ N).card_mul_index
      have h2 : (H ⊓ N).index ≤ 2 ^ r * r := by
        rw [← hHidx, ← hNidx]
        exact Subgroup.index_inf_le
      rw [hcardG] at h1
      by_contra hlt
      push Not at hlt
      have : Nat.card (H ⊓ N : Subgroup G) * (H ⊓ N).index < (2 ^ r - 1) * (2 ^ r * r) := by
        calc Nat.card (H ⊓ N : Subgroup G) * (H ⊓ N).index
            ≤ Nat.card (H ⊓ N : Subgroup G) * (2 ^ r * r) := Nat.mul_le_mul_left _ h2
          _ < (2 ^ r - 1) * (2 ^ r * r) :=
            Nat.mul_lt_mul_of_pos_right hlt (by have := hp.pos; positivity)
      rw [h1] at this
      have : 2 ^ r * ((2 ^ r - 1) * r) = (2 ^ r - 1) * (2 ^ r * r) := by ring
      omega
    have hKeq : H ⊓ N = K :=
      Subgroup.eq_of_le_of_card_ge hHNK (by rw [h.card_K]; exact hHNcard)
    have hKN : K ≤ N := hKeq ▸ inf_le_right
    have hpos' : 0 < 2 ^ r - 1 := by
      have : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2
      omega
    have hfac : ∀ g : G, ∃ n ∈ N, ∃ x ∈ H, g = n * x := by
      have hstab : stabilizer H ((1 : G) : G ⧸ N) = N.subgroupOf H := by
        rw [← stabilizer_subgroupOf, stabilizer_quotient]
      have hcardstab : Nat.card (stabilizer H ((1 : G) : G ⧸ N)) = 2 ^ r - 1 := by
        rw [hstab, ← inf_subgroupOf_left,
          Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : H ⊓ N ≤ H)).toEquiv, hKeq, h.card_K]
      have horb : (orbit H ((1 : G) : G ⧸ N)).ncard = r := by
        have := (stabilizer H ((1 : G) : G ⧸ N)).card_mul_index
        rw [hcardstab, index_stabilizer, h.card_stab] at this
        exact Nat.eq_of_mul_eq_mul_left hpos' this
      have huniv : orbit H ((1 : G) : G ⧸ N) = Set.univ := by
        apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
        rw [Set.ncard_univ, horb, ← hNidx, Subgroup.index_eq_card]
      intro g
      have hmem : ((g⁻¹ : G) : G ⧸ N) ∈ orbit H ((1 : G) : G ⧸ N) := huniv ▸ Set.mem_univ _
      obtain ⟨x, hx⟩ := hmem
      have hx' : x • ((1 : G) : G ⧸ N) = ((g⁻¹ : G) : G ⧸ N) := hx
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at hx'
      rw [QuotientGroup.eq] at hx'
      exact ⟨((x : G)⁻¹ * g⁻¹)⁻¹, N.inv_mem hx', (x : G)⁻¹, H.inv_mem x.2, by group⟩
    have hcl : normalClosure (K : Set G) ≤ N := by
      rw [normalClosure, closure_le]
      intro x hx
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hax
      obtain ⟨n, hn, y, hy, rfl⟩ := hfac c
      have : n * y * a * (n * y)⁻¹ = n * (y * a * y⁻¹) * n⁻¹ := by group
      rw [SetLike.mem_coe, this]
      exact N.mul_mem (N.mul_mem hn (hKN (h.K_normal y hy a ha))) (N.inv_mem hn)
    have htop : N = ⊤ := top_le_iff.mp (h.closure ▸ hcl)
    have hSn : (S : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hSsol : Group.IsSolvable (S : Subgroup G) := by
      have := S.isPGroup'.isNilpotent
      infer_instance
    have hbot := h.solvable _ hSn hSsol
    have hc1 : Nat.card (S : Subgroup G) = 1 := by rw [hbot, Subgroup.card_bot]
    rw [h.card_sylow S] at hc1
    have : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2
    omega

end CFSG.GH74.Uniqueness.Hering
