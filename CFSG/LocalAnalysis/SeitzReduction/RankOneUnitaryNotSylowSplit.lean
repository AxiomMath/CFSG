module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryNotSylowNcyc

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_cartan_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ D : Subgroup G, D ≤ normalizer (szT₁ L T : Set G) ∧ szT₁ L T ⊓ D = ⊥ ∧
      (∀ y ∈ szT₁ L T, (∀ d ∈ D, y * d = d * y) → y = 1) ∧
      ∀ s ∈ T, ∃ n ∈ szT₁ L T, ∀ d ∈ D, (n⁻¹ * s) * d * (n⁻¹ * s)⁻¹ ∈ D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  obtain ⟨hT₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  set Dl := cartan (Q : Subgroup L) t₀ with hDl
  set Bl := borel (Q : Subgroup L) with hBl
  set D := Dl.map L.subtype with hD
  set B := Bl.map L.subtype with hBdef
  have hT₁ : (Q : Subgroup L).map L.subtype = szT₁ L T :=
    map_subtype_eq_of_mem_iff (szT₁_le_right L T) hmemQ
  have hmemB : ∀ x : G, x ∈ B ↔ x ∈ L ∧ x ∈ normalizer (szT₁ L T : Set G) := by
    intro x
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨l.2, mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
      · have hyL : y ∈ L := szT₁_le_right L T hy
        have := (mem_normalizer_iff.mp hl ⟨y, hyL⟩).mp ((hmemQ _).mpr hy)
        simpa using (hmemQ _).mp this
      · have hyL : y ∈ L := by
          have h1 : (l : G) * y * (l : G)⁻¹ ∈ L := szT₁_le_right L T hy
          have := mul_mem (mul_mem (inv_mem l.2) h1) l.2
          simpa [mul_assoc] using this
        have h1 : l * ⟨y, hyL⟩ * l⁻¹ ∈ (Q : Subgroup L) := (hmemQ _).mpr (by simpa using hy)
        exact (hmemQ _).mp ((mem_normalizer_iff.mp hl _).mpr h1)
    · rintro ⟨hxL, hxN⟩
      refine ⟨⟨x, hxL⟩, mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩, rfl⟩
      · have h1 := (mem_normalizer_iff.mp hxN y).mp ((hmemQ y).mp hy)
        exact (hmemQ _).mpr (by simpa using h1)
      · have h1 : x * (y : G) * x⁻¹ ∈ szT₁ L T := by simpa using (hmemQ _).mp hy
        exact (hmemQ y).mpr ((mem_normalizer_iff.mp hxN y).mpr h1)
  have hBN : B ≤ normalizer (szT₁ L T : Set G) := fun x hx => ((hmemB x).mp hx).2
  have hDB : D ≤ B := map_mono (cartan_le_borel _ _)
  have hT₁B : szT₁ L T ≤ B := fun y hy =>
    (hmemB y).mpr ⟨szT₁_le_right L T hy, Subgroup.le_normalizer hy⟩
  have hinf : szT₁ L T ⊓ D = ⊥ := by
    rw [← hT₁, hD, ← map_inf_eq _ _ _ L.subtype_injective, hc.inf_eq, Subgroup.map_bot]
  have hcardB : Nat.card B = Nat.card (szT₁ L T) * Nat.card D := by
    have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (cartan_le_borel (Q : Subgroup L) t₀)
    rw [inf_comm, hc.inf_eq, card_bot, mul_one, sup_comm, hc.sup_eq] at hprod
    have hBl' : Nat.card Bl = Nat.card (Q : Subgroup L) * Nat.card Dl := by
      rw [hBl, hDl, hprod, mul_comm]
    rw [hBdef, hD, card_map_of_injective L.subtype_injective,
      card_map_of_injective L.subtype_injective, ← hT₁,
      card_map_of_injective L.subtype_injective, hBl']
  have hDodd : Odd (Nat.card D) := by
    rw [hD, card_map_of_injective L.subtype_injective]
    exact hc.odd_card_cartan
  have hcop : Nat.Coprime (Nat.card (szT₁ L T)) (Nat.card D) := by
    rw [hT₁card, ← pow_mul]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hDodd)
  refine ⟨D, hDB.trans hBN, hinf, ?_, ?_⟩
  · intro y hy hyD
    have hyL : y ∈ L := szT₁_le_right L T hy
    set y' : L := ⟨y, hyL⟩ with hy'
    have hy'Q : y' ∈ (Q : Subgroup L) := (hmemQ y').mpr hy
    have hcomm : ∀ d ∈ Dl, d * y' = y' * d := fun d hd => Subtype.ext (by
      have := hyD (d : G) ⟨d, hd, rfl⟩
      simp only [coe_mul]
      exact this.symm)
    have hexists : ∀ z : L, ∃ z' ∈ rootCenter (Q : Subgroup L), z' ∉ ({1, z} : Set L) :=
      fun z => exists_mem_not_mem_of_ncard_lt (Set.toFinite _) (by
        rw [hc.card_center]
        calc ({1, z} : Set L).ncard ≤ ({z} : Set L).ncard + 1 := Set.ncard_insert_le 1 {z}
          _ = 2 := by rw [Set.ncard_singleton]
          _ < 2 ^ f := by omega)
    have hyZ : y' ∈ rootCenter (Q : Subgroup L) := by
      by_contra hyZ
      obtain ⟨z, hz, hz1⟩ := hexists 1
      obtain ⟨z', hz', hz'1⟩ := hexists z
      have hz1' : z ≠ 1 := fun h1 => hz1 (by simp [h1])
      have hz'1' : z' ≠ 1 := fun h1 => hz'1 (by simp [h1])
      have hz'z : z' ≠ z := fun h1 => hz'1 (by simp [h1])
      obtain ⟨d, hd, hdz⟩ := hc.exists_cartan_conj hz hz1' hz' hz'1'
      have hd1 : d ≠ 1 := fun h1 => hz'z (by rw [hdz, h1]; group)
      exact hyZ (hB.fixedPointFree_unitary Q hc.sq_eq_one hc.not_mem hd hd1 hy'Q (by
        rw [hcomm d hd, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _))
    by_contra hy1
    have hy'1 : y' ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
    obtain ⟨z', hz', hz'1⟩ := hexists y'
    have hz'1' : z' ≠ 1 := fun h1 => hz'1 (by simp [h1])
    have hz'y : z' ≠ y' := fun h1 => hz'1 (by simp [h1])
    obtain ⟨d, hd, hdz⟩ := hc.exists_cartan_conj hyZ hy'1 hz' hz'1'
    apply hz'y
    rw [hdz, mul_assoc, ← hcomm d hd, inv_mul_cancel_left]
  · intro s hs
    have hsL : s ∈ normalizer (L : Set G) := h.le_normalizer hs
    have hsT₁ := hTN₁ hs
    have hsB : ∀ x ∈ B, s * x * s⁻¹ ∈ B := by
      intro x hx
      obtain ⟨hxL, hxN⟩ := (hmemB x).mp hx
      exact (hmemB _).mpr ⟨(mem_normalizer_iff.mp hsL x).mp hxL,
        mul_mem (mul_mem hsT₁ hxN) (inv_mem hsT₁)⟩
    set Ds := D.map (MulAut.conj s).toMonoidHom with hDs
    have hDsB : Ds ≤ B := by
      rintro _ ⟨d, hd, rfl⟩
      exact hsB d (hDB hd)
    have hcardDs : Nat.card Ds = Nat.card D := card_map_of_injective (MulAut.conj s).injective
    set N := (szT₁ L T).subgroupOf B with hNdef
    set H := D.subgroupOf B with hHdef
    set K := Ds.subgroupOf B with hKdef
    have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hT₁B).mpr hBN
    have hcN : Nat.card N = Nat.card (szT₁ L T) :=
      Nat.card_congr (subgroupOfEquivOfLe hT₁B).toEquiv
    have hcH : Nat.card H = Nat.card D := Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv
    have hcK : Nat.card K = Nat.card D := by
      rw [← hcardDs]
      exact Nat.card_congr (subgroupOfEquivOfLe hDsB).toEquiv
    have hH : N.IsComplement' H :=
      isComplement'_of_coprime (by rw [hcN, hcH, ← hcardB]) (by rw [hcN, hcH]; exact hcop)
    have hK : N.IsComplement' K :=
      isComplement'_of_coprime (by rw [hcN, hcK, ← hcardB]) (by rw [hcN, hcK]; exact hcop)
    have hidx : N.index = Nat.card D := by
      have h1 := N.card_mul_index
      rw [hcN, hcardB] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    have hcop' : Nat.Coprime (Nat.card N) N.index := by rw [hcN, hidx]; exact hcop
    obtain ⟨n, hn⟩ := CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
      N H K hNn hH hK hcop'
    refine ⟨((n : B) : G), mem_subgroupOf.mp n.2, fun d hd => ?_⟩
    have h1 : (⟨s * d * s⁻¹, hDsB ⟨d, hd, rfl⟩⟩ : B) ∈ K := mem_subgroupOf.mpr ⟨d, hd, rfl⟩
    rw [hn] at h1
    obtain ⟨d', hd', hd'eq⟩ := h1
    have e := congrArg Subtype.val hd'eq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_mul, coe_inv] at e
    rw [show (((n : B) : G))⁻¹ * s * d * ((((n : B) : G))⁻¹ * s)⁻¹ =
      ((n : B) : G)⁻¹ * (s * d * s⁻¹) * ((n : B) : G) by group, ← e]
    simpa [mul_assoc] using mem_subgroupOf.mp hd'

theorem exists_outer_involution_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {s : G} (hs : s ∈ T) (hs2 : s ^ 2 ∈ szT₁ L T) (hsS : s ∉ szT₁ L T ⊔ zpowers t) :
    ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t := by
  obtain ⟨D, hDN, hinf, hcent, hconj⟩ := h.exists_cartan_of_card_sylow hS2
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨n, hn, hnD⟩ := hconj s hs
  set m := n⁻¹ * s with hm
  have hnT : n ∈ T := szT₁_le_left L T hn
  have hmT : m ∈ T := mul_mem (inv_mem hnT) hs
  have hmD : m ∈ normalizer (D : Set G) := by
    have hm' : m⁻¹ ∈ normalizer (D : Set G) :=
      mem_normalizer_of_forall_inv_mul_mul_mem fun d hd => by rw [inv_inv]; exact hnD d hd
    simpa using inv_mem hm'
  have hm2 : m ^ 2 ∈ szT₁ L T := by
    have e : m ^ 2 = n⁻¹ * (s * n⁻¹ * s⁻¹) * s ^ 2 := by rw [hm, sq, sq]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hn) ((mem_normalizer_iff.mp (hTN₁ hs) _).mp (inv_mem hn)))
      hs2
  have hm2D : ∀ d ∈ D, m ^ 2 * d = d * m ^ 2 := by
    intro d hd
    have hm2N : m ^ 2 ∈ normalizer (D : Set G) := pow_mem hmD 2
    have hc : m ^ 2 * d * (m ^ 2)⁻¹ * d⁻¹ ∈ szT₁ L T ⊓ D := by
      refine mem_inf.mpr ⟨?_, mul_mem ((mem_normalizer_iff.mp hm2N d).mp hd) (inv_mem hd)⟩
      have h1 : d * (m ^ 2)⁻¹ * d⁻¹ ∈ szT₁ L T :=
        (mem_normalizer_iff.mp (hDN hd) _).mp (inv_mem hm2)
      rw [show m ^ 2 * d * (m ^ 2)⁻¹ * d⁻¹ = m ^ 2 * (d * (m ^ 2)⁻¹ * d⁻¹) by group]
      exact mul_mem hm2 h1
    rw [hinf, mem_bot] at hc
    calc m ^ 2 * d = (m ^ 2 * d * (m ^ 2)⁻¹ * d⁻¹) * (d * m ^ 2) := by group
      _ = d * m ^ 2 := by rw [hc, one_mul]
  refine ⟨m, hmT, hcent _ hm2 hm2D, fun hmS => hsS ?_⟩
  rw [show s = n * m by rw [hm]; group]
  exact mul_mem (mem_sup_left hn) hmS

end U3Start

theorem u3SplitInput : U3SplitInput := by
  intro G _ _ L f t T h hS2 hncyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, -, -, hTN₁, hdisj, hMn, -⟩ := h.start_of_card_sylow hS2
  have hcycM := h.isCyclic_quotient_of_card_sylow hS2
  obtain ⟨g₀, hg₀⟩ := hcycM.exists_zpow_surjective
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g₀
  have hbgen : ∀ s ∈ T, ∃ k : ℤ, ((b : G) ^ k)⁻¹ * s ∈ szT₁ L T ⊔ zpowers t := by
    intro s hs
    obtain ⟨k, hk⟩ := hg₀ (QuotientGroup.mk ⟨s, hs⟩)
    refine ⟨k, ?_⟩
    simp only at hk
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf] at hk
    simpa using hk
  set N₁ := (szT₁ L T).subgroupOf T with hN₁def
  have hN₁ : N₁.Normal := (normal_subgroupOf_iff_le_normalizer (szT₁_le_left L T)).mpr hTN₁
  have hone : ∀ y : T, (QuotientGroup.mk y : T ⧸ N₁) = 1 ↔ (y : G) ∈ szT₁ L T := fun y => by
    rw [QuotientGroup.eq_one_iff, hN₁def, mem_subgroupOf]
  have hzT : ∀ z ∈ zpowers t, z ∈ T := fun z hz => zpowers_le.mpr htT hz
  have hdecomp : ∀ s : T, ∃ k : ℤ, ∃ z ∈ zpowers t, ∃ hz : z ∈ T,
      (QuotientGroup.mk s : T ⧸ N₁) = (QuotientGroup.mk b) ^ k * QuotientGroup.mk ⟨z, hz⟩ := by
    intro s
    obtain ⟨k, hk⟩ := hbgen s s.2
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hk
    refine ⟨k, z, hz, hzT z hz, ?_⟩
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN₁def,
      mem_subgroupOf]
    have e : ((s⁻¹ * (b ^ k * ⟨z, hzT z hz⟩) : T) : G) =
        (((b : G) ^ k)⁻¹ * s)⁻¹ * z := by
      simp only [coe_mul, coe_inv, coe_zpow]
      group
    rw [e, ← hyz, show (y * z)⁻¹ * z = z⁻¹ * y⁻¹ * z by group]
    exact (mem_normalizer_iff''.mp (hTN₁ (hzT z hz)) _).mp (inv_mem hy)
  have hzQ : ∀ z ∈ zpowers t, ∀ hz : z ∈ T,
      (QuotientGroup.mk ⟨z, hz⟩ : T ⧸ N₁) = 1 ∨
        (QuotientGroup.mk ⟨z, hz⟩ : T ⧸ N₁) = QuotientGroup.mk ⟨t, htT⟩ := by
    intro z hz hzT'
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · left
      rw [hone]
      simp only [hz1]
      exact one_mem _
    · right
      congr 1
      exact Subtype.ext hz1
  by_cases htb : (QuotientGroup.mk ⟨t, htT⟩ : T ⧸ N₁) ∈ zpowers (QuotientGroup.mk b)
  · exfalso
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp htb
    apply hncyc
    refine ⟨b, b.2, fun s hs => ?_⟩
    obtain ⟨k, z, hz, hzT', hk⟩ := hdecomp ⟨s, hs⟩
    rcases hzQ z hz hzT' with hz1 | hz1
    · refine ⟨k, ?_⟩
      have := (hone (((b : T) ^ k)⁻¹ * ⟨s, hs⟩)).mp (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, hk, hz1, mul_one,
          inv_mul_cancel])
      simpa using this
    · refine ⟨k + j, ?_⟩
      have := (hone (((b : T) ^ (k + j))⁻¹ * ⟨s, hs⟩)).mp (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, hk, hz1, ← hj,
          ← zpow_add, inv_mul_cancel])
      simpa using this
  by_cases hb1 : (QuotientGroup.mk b : T ⧸ N₁) = 1
  · exfalso
    apply hncyc
    refine ⟨t, htT, fun s hs => ?_⟩
    obtain ⟨k, z, hz, hzT', hk⟩ := hdecomp ⟨s, hs⟩
    rw [hb1, one_zpow, one_mul] at hk
    rcases hzQ z hz hzT' with hz1 | hz1
    · refine ⟨0, ?_⟩
      have := (hone ⟨s, hs⟩).mp (by rw [hk, hz1])
      simpa using this
    · refine ⟨1, ?_⟩
      have := (hone ((⟨t, htT⟩ : T)⁻¹ * ⟨s, hs⟩)).mp (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk, hz1, inv_mul_cancel])
      simpa using this
  have hp : IsPGroup 2 (T ⧸ N₁) := h.isPGroup.to_quotient N₁
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hp (QuotientGroup.mk b)
  have hm1 : m ≠ 0 := by
    rintro rfl
    exact hb1 (orderOf_eq_one_iff.mp (by rw [hm, pow_zero]))
  set u : T := b ^ (2 ^ (m - 1)) with hu
  have hub : orderOf (QuotientGroup.mk u : T ⧸ N₁) = 2 := by
    rw [hu, QuotientGroup.mk_pow, orderOf_pow_of_dvd (by positivity)
      (by rw [hm]; exact Nat.pow_dvd_pow 2 (Nat.sub_le m 1)), hm]
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm1
    rw [Nat.succ_sub_one, pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have hu2 : ((u : G)) ^ 2 ∈ szT₁ L T := by
    have := (hone (u ^ 2)).mp (by rw [QuotientGroup.mk_pow, ← hub, pow_orderOf_eq_one])
    simpa using this
  have huS : (u : G) ∉ szT₁ L T ⊔ zpowers t := by
    intro huS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ huS
    have hyT : y ∈ T := szT₁_le_left L T hy
    have hmk : (QuotientGroup.mk u : T ⧸ N₁) = QuotientGroup.mk ⟨z, hzT z hz⟩ := by
      rw [QuotientGroup.eq, hN₁def, mem_subgroupOf]
      have e : ((u⁻¹ * ⟨z, hzT z hz⟩ : T) : G) = z⁻¹ * y⁻¹ * z := by
        simp only [coe_mul, coe_inv]
        rw [← hyz]
        group
      rw [e]
      exact (mem_normalizer_iff''.mp (hTN₁ (hzT z hz)) _).mp (inv_mem hy)
    rcases hzQ z hz (hzT z hz) with hz1 | hz1
    · rw [hmk, hz1, orderOf_one] at hub
      exact absurd hub (by norm_num)
    · apply htb
      rw [← hz1, ← hmk, hu, QuotientGroup.mk_pow]
      exact pow_mem (mem_zpowers _) _
  exact h.exists_outer_involution_of_card_sylow hS2 u.2 hu2 huS

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem not_isSylow_S₁_of_closure_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f) (hclos : U3ClosureInput) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ :=
  h.not_isSylow_S₁_of_star_of_card_sylow hS2 hR hstar hclos u3SplitInput

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
