module

public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG.ClassicalInvolution

private theorem fec_exists_pow_two_pow_odd {Y : Type} [Group Y] [Finite Y] (c : Y) :
    ∃ j : ℕ, Odd (orderOf (c ^ (2 ^ j))) := by
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hpos : 0 < 2 ^ k := by positivity
  have hdvd : 2 ^ k ∣ orderOf c := ⟨m, hk⟩
  refine ⟨k, ?_⟩
  rw [orderOf_pow_of_dvd hpos.ne' hdvd, hk, Nat.mul_div_cancel_left m hpos]
  exact hm

private theorem fec_exists_pow_mem {Y : Type} [Group Y] [Finite Y] (C K : Subgroup Y)
    (hK : ∀ x ∈ C, Odd (orderOf x) → x ∈ K) {c : Y} (hc : c ∈ C) :
    ∃ j : ℕ, c ^ (2 ^ j) ∈ K := by
  obtain ⟨j, hj⟩ := fec_exists_pow_two_pow_odd c
  exact ⟨j, hK _ (pow_mem hc _) hj⟩

private theorem fec_index_eq_two_pow {G : Type} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (h : ∀ c : G, ∃ j : ℕ, c ^ (2 ^ j) ∈ K) : ∃ b : ℕ, K.index = 2 ^ b := by
  have hP : IsPGroup 2 (G ⧸ K) := by
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨j, hj⟩ := h c
    refine ⟨j, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hj
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hP
  exact ⟨b, by rw [Subgroup.index_eq_card]; exact hb⟩

private theorem fec_mem_of_odd_orderOf {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (h2 : N.index = 2) {x : G} (hx : Odd (orderOf x)) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ orderOf x := orderOf_map_dvd _ _
  have h2' : orderOf (QuotientGroup.mk' N x) ∣ 2 := by
    have h := orderOf_dvd_natCard (QuotientGroup.mk' N x)
    rwa [← Subgroup.index_eq_card, h2] at h
  have hodd : Odd (orderOf (QuotientGroup.mk' N x)) := Odd.of_dvd_nat hx h1
  have h3 : orderOf (QuotientGroup.mk' N x) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

private theorem fec_orderOf_conj {Y : Type} [Group Y] (c n : Y) :
    orderOf (c * n * c⁻¹) = orderOf n := by
  have h := MulEquiv.orderOf_eq (MulAut.conj c) n
  rwa [MulAut.conj_apply] at h

private theorem fec_odd_index_subgroupOf {Y : Type} [Group Y] [Finite Y] (S₁ : Sylow 2 Y)
    {C : Subgroup Y} (hSC : (S₁ : Subgroup Y) ≤ C) :
    Odd ((S₁ : Subgroup Y).subgroupOf C).index := by
  have hnd : ¬ 2 ∣ (S₁ : Subgroup Y).index := Sylow.not_dvd_index S₁
  have h := Subgroup.relIndex_mul_index hSC
  have h' : Odd ((S₁ : Subgroup Y).relIndex C * C.index) := by
    rw [h]
    exact Nat.odd_iff.mpr (by omega)
  exact (Nat.odd_mul.mp h').1

private theorem fec_not_four_dvd {n s j b : ℕ} (hs : 0 < s) (hj : Odd j)
    (hC : n * 2 ^ b = s * j) (hle : s ≤ 2 * 2 ^ b) (h4 : 4 ∣ n) : False := by
  obtain ⟨k, rfl⟩ := h4
  have hdvd : 2 ^ (b + 2) ∣ s * j := ⟨k, by rw [← hC]; ring⟩
  have hcop : Nat.Coprime (2 ^ (b + 2)) j :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      fun h => (Nat.not_even_iff_odd.mpr hj) (even_iff_two_dvd.mpr h))
  have h2 : 2 ^ (b + 2) ∣ s := hcop.dvd_of_dvd_mul_right hdvd
  have h3 : 2 ^ (b + 2) ≤ s := Nat.le_of_dvd hs h2
  have h4' : 2 ^ (b + 2) = 4 * 2 ^ b := by ring
  have h5 : 0 < 2 ^ b := by positivity
  have h6 : 2 ^ (b + 2) ≤ 2 * 2 ^ b := le_trans h3 hle
  rw [h4'] at h6
  linarith

private theorem fec_exists_normal_index_two {G : Type} [Group G] [Finite G] (h2 : 2 ∣ Nat.card G)
    (h4 : ¬ 4 ∣ Nat.card G) : ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have P : Sylow 2 G := Classical.arbitrary _
  have hidx := Subgroup.card_mul_index (H := (P : Subgroup G))
  have hnd : ¬ 2 ∣ (P : Subgroup G).index := Sylow.not_dvd_index P
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp P.isPGroup'
  rw [he] at hidx
  have hdvd : 2 ^ e ∣ Nat.card G := Dvd.intro _ hidx
  have he1 : e = 1 := by
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · interval_cases e
      · exfalso
        rw [pow_zero, one_mul] at hidx
        omega
      · rfl
    · exfalso
      have h4e : 4 ∣ 2 ^ e := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.pow_dvd_pow 2 hge
      exact h4 (h4e.trans hdvd)
  have hPcard : Nat.card (P : Subgroup G) = 2 := by
    rw [he, he1, pow_one]
  have hp : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hcyc : IsCyclic P := isCyclic_of_prime_card hPcard
  obtain ⟨N, hNc, hNn⟩ : ∃ N : Subgroup G, N.IsComplement' (P : Subgroup G) ∧ N.Normal :=
    ⟨_, IsCyclic.isComplement' hp hcyc, inferInstance⟩
  exact ⟨N, hNn, hNc.symm.index_eq_card.trans hPcard⟩

theorem odd_mem_oddCoreIn_of_normal {Y : Type} [Group Y] [Finite Y] (S₁ : Sylow 2 Y)
    (C D : Subgroup Y) (hSC : (S₁ : Subgroup Y) ≤ C) (hDC : D ≤ C)
    (hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hodd : ∀ x ∈ C, Odd (orderOf x) → x ∈ D) {t : Y} (ht2 : orderOf t = 2) (htD : t ∈ D)
    (hSD : (S₁ : Subgroup Y) ⊓ D = Subgroup.zpowers t) :
    ∀ x ∈ C, Odd (orderOf x) → x ∈ Balance.oddCoreIn C := by
  haveI hDCn : (D.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hDn (g : Y) g.2 (n : Y) hn⟩
  obtain ⟨b, hb⟩ := fec_index_eq_two_pow (D.subgroupOf C) (fun c => by
    obtain ⟨j, hj⟩ := fec_exists_pow_mem C D hodd c.2
    exact ⟨j, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hj⟩)
  have hiso : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
  have hCD : Nat.card C = Nat.card D * 2 ^ b := by
    rw [← hb, ← hiso]
    exact (Subgroup.card_mul_index (H := D.subgroupOf C)).symm
  have hiso1 : Nat.card ((S₁ : Subgroup Y).subgroupOf C) = Nat.card (S₁ : Subgroup Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
  have hCS : Nat.card C = Nat.card (S₁ : Subgroup Y) * ((S₁ : Subgroup Y).subgroupOf C).index := by
    rw [← hiso1]
    exact (Subgroup.card_mul_index (H := (S₁ : Subgroup Y).subgroupOf C)).symm
  have hSc := fec_odd_index_subgroupOf S₁ hSC
  have hbound : Nat.card ((S₁ : Subgroup Y).subgroupOf C) ≤ 2 * (D.subgroupOf C).index := by
    obtain ⟨f, hf⟩ : ∃ f : ((S₁ : Subgroup Y).subgroupOf C) →* (C ⧸ D.subgroupOf C),
        ∀ x, f x = QuotientGroup.mk (x : C) :=
      ⟨(QuotientGroup.mk' (D.subgroupOf C)).comp ((S₁ : Subgroup Y).subgroupOf C).subtype,
        fun x => rfl⟩
    have hmem : ∀ x : f.ker, x.1.1.1 ∈ Subgroup.zpowers t := by
      rintro ⟨x, hx⟩
      rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
      rw [← hSD]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp x.2, hx⟩
    have hinj : Function.Injective (fun x : f.ker => (⟨x.1.1.1, hmem x⟩ : Subgroup.zpowers t)) := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    have hfker : Nat.card f.ker ≤ 2 := by
      calc Nat.card f.ker ≤ Nat.card (Subgroup.zpowers t) := Nat.card_le_card_of_injective _ hinj
        _ = 2 := by rw [Nat.card_zpowers, ht2]
    have hrange : f.ker.index ≤ (D.subgroupOf C).index := by
      rw [Subgroup.index_ker, Subgroup.index_eq_card]
      apply Subgroup.card_le_card_group
    calc Nat.card ((S₁ : Subgroup Y).subgroupOf C) = Nat.card f.ker * f.ker.index :=
          (Subgroup.card_mul_index (H := f.ker)).symm
      _ ≤ 2 * (D.subgroupOf C).index := Nat.mul_le_mul hfker hrange
  have hS1le : Nat.card (S₁ : Subgroup Y) ≤ 2 * 2 ^ b := by
    rw [← hb, ← hiso1]
    exact hbound
  have h2D : 2 ∣ Nat.card D := by
    have h := orderOf_dvd_natCard (⟨t, htD⟩ : ↥D)
    rwa [Subgroup.orderOf_mk, ht2] at h
  have hS1pos : 0 < Nat.card (S₁ : Subgroup Y) := Nat.card_pos
  have h4 : ¬ 4 ∣ Nat.card D := fun h =>
    fec_not_four_dvd hS1pos hSc (hCD.symm.trans hCS) hS1le h
  obtain ⟨N, hNn, hNidx⟩ := fec_exists_normal_index_two h2D h4
  have hNcard : Nat.card N * 2 = Nat.card D := by
    have h := Subgroup.card_mul_index (H := N)
    rwa [hNidx] at h
  have hNodd : Odd (Nat.card N) := Nat.odd_iff.mpr (by omega)
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup Y, S = N.map D.subtype := ⟨_, rfl⟩
  have hSodd : Odd (Nat.card S) := by
    rw [hSdef, Subgroup.card_map_of_injective D.subtype_injective]
    exact hNodd
  have hSmem : ∀ y : Y, y ∈ S ↔ y ∈ D ∧ Odd (orderOf y) := by
    intro y
    constructor
    · intro hy
      have hyD : y ∈ D := by
        rw [hSdef] at hy
        obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp hy
        exact x.2
      refine ⟨hyD, ?_⟩
      have h1 := orderOf_dvd_natCard (⟨y, hy⟩ : ↥S)
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hSodd h1
    · rintro ⟨hyD, hyodd⟩
      have hxN : (⟨y, hyD⟩ : ↥D) ∈ N :=
        fec_mem_of_odd_orderOf N hNidx (by rw [Subgroup.orderOf_mk]; exact hyodd)
      rw [hSdef]
      exact Subgroup.mem_map_of_mem D.subtype hxN
  have hkey : ∀ c ∈ C, ∀ n ∈ S, c * n * c⁻¹ ∈ S := by
    intro c hc n hn
    obtain ⟨hnD, hnodd⟩ := (hSmem n).mp hn
    exact (hSmem _).mpr ⟨hDn c hc n hnD, by rw [fec_orderOf_conj]; exact hnodd⟩
  have hnorm : C ≤ Subgroup.normalizer (S : Set Y) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hkey c hc n hn
    · intro hn
      have hn' : c * n * c⁻¹ ∈ S := hn
      have h := hkey c⁻¹ (inv_mem hc) _ hn'
      have e : c⁻¹ * (c * n * c⁻¹) * c⁻¹⁻¹ = n := by group
      rw [e] at h
      exact h
  have hSC' : S ≤ C := fun y hy => hDC ((hSmem y).mp hy).1
  have hle : S ≤ Balance.oddCoreIn C := Balance.le_oddCoreIn_of_normalizes hSC' hnorm hSodd
  intro x hx hxodd
  exact hle ((hSmem x).mpr ⟨hodd x hx hxodd, hxodd⟩)

theorem exists_oddCore_mul_of_normal {Y : Type} [Group Y] [Finite Y] (S₁ : Sylow 2 Y)
    (C D : Subgroup Y) (hSC : (S₁ : Subgroup Y) ≤ C) (hDC : D ≤ C)
    (hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hodd : ∀ x ∈ C, Odd (orderOf x) → x ∈ D) {t : Y} (ht2 : orderOf t = 2) (htD : t ∈ D)
    (hSD : (S₁ : Subgroup Y) ⊓ D = Subgroup.zpowers t) :
    ∀ k ∈ C, ∃ o ∈ Balance.oddCoreIn C, ∃ s ∈ (S₁ : Subgroup Y), k = o * s := by
  have hA := odd_mem_oddCoreIn_of_normal S₁ C D hSC hDC hDn hodd ht2 htD hSD
  haveI hOn : ((Balance.oddCoreIn C).subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Balance.conj_mem_oddCoreIn g.2 hn⟩
  obtain ⟨e, he⟩ := fec_index_eq_two_pow ((Balance.oddCoreIn C).subgroupOf C) (fun c => by
    obtain ⟨j, hj⟩ := fec_exists_pow_mem C (Balance.oddCoreIn C) hA c.2
    exact ⟨j, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hj⟩)
  have hSc := fec_odd_index_subgroupOf S₁ hSC
  have hcop : Nat.Coprime (2 ^ e) ((S₁ : Subgroup Y).subgroupOf C).index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      fun h => (Nat.not_even_iff_odd.mpr hSc) (even_iff_two_dvd.mpr h))
  have htop : (Balance.oddCoreIn C).subgroupOf C ⊔ (S₁ : Subgroup Y).subgroupOf C = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have h1 : ((Balance.oddCoreIn C).subgroupOf C ⊔ (S₁ : Subgroup Y).subgroupOf C).index ∣
        ((Balance.oddCoreIn C).subgroupOf C).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h2 : ((Balance.oddCoreIn C).subgroupOf C ⊔ (S₁ : Subgroup Y).subgroupOf C).index ∣
        ((S₁ : Subgroup Y).subgroupOf C).index :=
      Subgroup.index_dvd_of_le le_sup_right
    rw [he] at h1
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  intro k hk
  have hmem : (⟨k, hk⟩ : ↥C) ∈
      (Balance.oddCoreIn C).subgroupOf C ⊔ (S₁ : Subgroup Y).subgroupOf C := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have hyz' : (y : Y) * (z : Y) = k := by
    have := congrArg Subtype.val hyz
    simpa using this
  exact ⟨(y : Y), Subgroup.mem_subgroupOf.mp hy, (z : Y), Subgroup.mem_subgroupOf.mp hz,
    hyz'.symm⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
