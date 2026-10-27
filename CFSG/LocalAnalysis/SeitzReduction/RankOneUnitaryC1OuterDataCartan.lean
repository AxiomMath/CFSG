module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpConf

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI

theorem exists_unit_pow_eq_one_pow_three_ne {E : Type*} [Field E] [Finite E] {q : ℕ}
    (hq : 4 ≤ q) (hcard : Nat.card E = q ^ 2) : ∃ k : Eˣ, k ^ (q + 1) = 1 ∧ k ^ 3 ≠ 1 := by
  classical
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hq
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hsq : (4 + m) ^ 2 - 1 = (3 + m) * (5 + m) := Nat.sub_eq_of_eq_add (by ring)
  have hcardU : Nat.card Eˣ = (3 + m) * (5 + m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard, hsq]
  have hord : orderOf γ = (3 + m) * (5 + m) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hcardU]
  have hsub : 4 + m - 1 = 3 + m := by omega
  refine ⟨γ ^ (4 + m - 1), ?_, ?_⟩
  · rw [← pow_mul, hsub, show 4 + m + 1 = 5 + m by ring, ← hord, pow_orderOf_eq_one]
  · intro h3
    rw [← pow_mul, hsub] at h3
    have hdvd := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at hdvd
    have h5 : 5 + m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
    have := Nat.le_of_dvd (by norm_num) h5
    omega

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_fpf_mem_cartan (h : U3Start G L f t T) {e : ℕ}
    {Q : Sylow 2 L} (hB : BenderType L f 3 e)
    (hmemQ : ∀ y : L, y ∈ (Q : Subgroup L) ↔ (y : G) ∈ szT₁ L T)
    (hmemZ : ∀ y : L, y ∈ rootCenter (Q : Subgroup L) ↔ (y : G) ∈ szA₁ (szT₁ L T)) {t₀ : L}
    (ht₀ : t₀ * t₀ = 1) (ht₀B : t₀ ∉ borel (Q : Subgroup L)) :
    ∃ x ∈ cartan (Q : Subgroup L) t₀,
      (∀ b ∈ szA₁ (szT₁ L T), (x : G) * b * (x : G)⁻¹ = b) ∧
      ∀ y ∈ szT₁ L T, y⁻¹ * ((x : G) * y * (x : G)⁻¹) ∈ szA₁ (szT₁ L T) →
        y ∈ szA₁ (szT₁ L T) := by
  classical
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, φ, hφQ, hφD⟩ :=
    hB.exists_standard_iso_unitary Q ht₀ ht₀B
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hZ : rootCenter (unitaryCoverRoot J hJ) =
      (rootCenter (Q : Subgroup L)).map φ.toMonoidHom := by
    rw [← hφQ, rootCenter_map]
  have hT₁ : ∀ y : G, y ∈ szT₁ L T ↔ ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ unitaryCoverRoot J hJ := by
    intro y
    refine ⟨fun hy => ?_, ?_⟩
    · have hyL : y ∈ L := szT₁_le_right L T hy
      refine ⟨hyL, ?_⟩
      rw [← hφQ]
      exact ⟨⟨y, hyL⟩, (hmemQ _).mpr hy, rfl⟩
    · rintro ⟨hyL, hyR⟩
      rw [← hφQ] at hyR
      obtain ⟨y', hy'Q, hy'⟩ := hyR
      have : y' = ⟨y, hyL⟩ := φ.injective hy'
      rw [this] at hy'Q
      exact (hmemQ _).mp hy'Q
  have hA₁ : ∀ y : G, y ∈ szA₁ (szT₁ L T) ↔
      ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ rootCenter (unitaryCoverRoot J hJ) := by
    intro y
    refine ⟨fun hy => ?_, ?_⟩
    · have hyL : y ∈ L := szT₁_le_right L T (szA₁_le _ hy)
      refine ⟨hyL, ?_⟩
      rw [hZ]
      exact ⟨⟨y, hyL⟩, (hmemZ _).mpr hy, rfl⟩
    · rintro ⟨hyL, hyR⟩
      rw [hZ] at hyR
      obtain ⟨y', hy'Q, hy'⟩ := hyR
      have : y' = ⟨y, hyL⟩ := φ.injective hy'
      rw [this] at hy'Q
      exact (hmemZ _).mp hy'Q
  have hRC := u3RootCoords_of_mulEquiv J hJ φ (2 ^ f) hcard hfixed hT₁
  have hAu : ∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ (u3Coord J hJ φ y).1.1 = 0) := by
    intro y hy
    obtain ⟨hyL, hyR⟩ := (hT₁ y).mp hy
    have hkey := hermitianUnipotentPSU_u3Coord J hJ φ hyL hyR
    rw [hA₁]
    constructor
    · rintro ⟨hyL', hyZ⟩
      obtain ⟨z, hz0, hz⟩ := (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mp hyZ
      have : z = u3Coord J hJ φ y := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (by rw [hz, hkey])
      rw [← this]
      exact hz0
    · intro hu
      exact ⟨hyL, (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mpr
        ⟨u3Coord J hJ φ y, hu, hkey⟩⟩
  have hq : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  obtain ⟨k, hk1, hk3⟩ := exists_unit_pow_eq_one_pow_three_ne hq hcard
  have htor : hermitianTorusPSU J hJ k ∈ (cartan (Q : Subgroup L) t₀).map φ.toMonoidHom := by
    rw [hφD]
    exact ⟨k, rfl⟩
  obtain ⟨x, hxC, hxφ⟩ := htor
  have hxN : (x : G) ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) x).mp (cartan_le_borel _ _ hxC)
  have hconjk : J.conj (k : E) = (k : E)⁻¹ := by
    rw [huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard hfixed]
    have h1 : (k : E) ^ (2 ^ f) * (k : E) = 1 := by
      rw [← pow_succ, ← Units.val_pow_eq_pow_val, hk1, Units.val_one]
    exact eq_inv_of_mul_eq_one_left h1
  have hk0 : (k : E) ≠ 0 := Units.ne_zero k
  have hk3' : (k : E) ^ 3 ≠ 1 := by
    intro h3
    apply hk3
    ext
    rw [Units.val_pow_eq_pow_val, h3, Units.val_one]
  have hact : ∀ y ∈ szT₁ L T, (x : G) * y * (x : G)⁻¹ ∈ szT₁ L T ∧
      u3Coord J hJ φ ((x : G) * y * (x : G)⁻¹) = hermitianTorusAction J k (u3Coord J hJ φ y) := by
    intro y hy
    obtain ⟨hyL, hyR⟩ := (hT₁ y).mp hy
    have hkey := hermitianUnipotentPSU_u3Coord J hJ φ hyL hyR
    have hxy : (x : G) * y * (x : G)⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hxN y).mp hy
    obtain ⟨hxyL, hxyR⟩ := (hT₁ _).mp hxy
    have hkey2 := hermitianUnipotentPSU_u3Coord J hJ φ hxyL hxyR
    have h3 : φ ⟨(x : G) * y * (x : G)⁻¹, hxyL⟩ =
        hermitianUnipotentPSU J hJ (hermitianTorusAction J k (u3Coord J hJ φ y)) := by
      have e : (⟨(x : G) * y * (x : G)⁻¹, hxyL⟩ : L) = x * ⟨y, hyL⟩ * x⁻¹ := Subtype.ext (by simp)
      have hxφ' : φ x = hermitianTorusPSU J hJ k := hxφ
      rw [e, map_mul, map_mul, map_inv, ← unitaryCoverTorus_conj_root J hJ k, hkey, hxφ']
    exact ⟨hxy, CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (by rw [hkey2, h3])⟩
  refine ⟨x, hxC, fun b hb => ?_, fun y hy hyA => ?_⟩
  · have hbT : b ∈ szT₁ L T := szA₁_le _ hb
    obtain ⟨hxb, hxbc⟩ := hact b hbT
    have hb0 : (u3Coord J hJ φ b).1.1 = 0 := (hAu b hbT).mp hb
    refine hRC.inj _ hxb _ hbT ?_ ?_
    · show (u3Coord J hJ φ ((x : G) * b * (x : G)⁻¹)).1.1 = (u3Coord J hJ φ b).1.1
      rw [hxbc, hermitianTorusAction_fst, hb0, zero_mul, zero_mul]
    · show (u3Coord J hJ φ ((x : G) * b * (x : G)⁻¹)).1.2 = (u3Coord J hJ φ b).1.2
      rw [hxbc, hermitianTorusAction_snd, hconjk, inv_inv, mul_assoc, mul_inv_cancel₀ hk0,
        mul_one]
  · obtain ⟨hxy, hxyc⟩ := hact y hy
    have hz := (hAu _ (mul_mem (inv_mem hy) hxy)).mp hyA
    have e1 : (u3Coord J hJ φ (y⁻¹ * ((x : G) * y * (x : G)⁻¹))).1.1 =
        (u3Coord J hJ φ ((x : G) * y * (x : G)⁻¹)).1.1 - (u3Coord J hJ φ y).1.1 :=
      hRC.u_mul_inv hy hxy
    rw [e1, hxyc, hermitianTorusAction_fst, hconjk, inv_inv] at hz
    have h2 : ((k : E) ^ 3 - 1) * (u3Coord J hJ φ y).1.1 = 0 := by linear_combination hz
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) hk3'
    · exact (hAu y hy).mpr h4

theorem exists_cartan_fpf_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ D : Subgroup G, ∃ d ∈ D, D ≤ L ∧ D ≤ normalizer (szT₁ L T : Set G) ∧
      szT₁ L T ⊓ D = ⊥ ∧ Odd (Nat.card D) ∧
      (∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
        ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b') ∧
      (∀ s ∈ T, ∃ n ∈ szT₁ L T, ∀ x ∈ D, (n⁻¹ * s) * x * (n⁻¹ * s)⁻¹ ∈ D) ∧
      D ≤ zpowers d ∧
      ∃ e ∈ D, (∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b) ∧
        ∀ y ∈ szT₁ L T, y⁻¹ * (e * y * e⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  obtain ⟨hT₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
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
  have : IsCyclic Dl := hc.isCyclic
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Dl)
  have hDz : D ≤ zpowers ((g₀ : L) : G) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg₀ ⟨x, hx⟩)
    refine mem_zpowers_iff.mpr ⟨n, ?_⟩
    have := congrArg (fun z : Dl => ((z : L) : G)) hn
    simpa using this
  have hfpf : ∃ e ∈ D, (∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b) ∧
      ∀ y ∈ szT₁ L T, y⁻¹ * (e * y * e⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T) := by
    obtain ⟨x, hxC, hxA, hxf⟩ := h.exists_fpf_mem_cartan hB hmemQ hmemZ hc.sq_eq_one hc.not_mem
    exact ⟨(x : G), ⟨x, hxC, rfl⟩, hxA, hxf⟩
  refine ⟨D, ((g₀ : L) : G), ⟨g₀, g₀.2, rfl⟩, fun x hx => ((hmemB x).mp (hDB hx)).1,
    hDB.trans hBN, hinf, hDodd, ?_, ?_, hDz, hfpf⟩
  · intro b hb b' hb' hb1 hb1'
    have hbL : b ∈ L := szT₁_le_right L T (szA₁_le _ hb)
    have hb'L : b' ∈ L := szT₁_le_right L T (szA₁_le _ hb')
    obtain ⟨d₁, hd₁, hd₁eq⟩ := hc.exists_cartan_conj ((hmemZ ⟨b, hbL⟩).mpr hb)
      (fun h1 => hb1 (congrArg Subtype.val h1)) ((hmemZ ⟨b', hb'L⟩).mpr hb')
      (fun h1 => hb1' (congrArg Subtype.val h1))
    have hz : (⟨d₁, hd₁⟩ : Dl) ∈ Submonoid.powers g₀ := mem_powers_iff_mem_zpowers.mpr (hg₀ _)
    obtain ⟨n, hn⟩ := hz
    refine ⟨n, ?_⟩
    have e1 := congrArg Subtype.val hd₁eq
    have e2 : ((g₀ : L) : G) ^ n = (d₁ : G) := by
      have := congrArg (fun z : Dl => ((z : L) : G)) hn
      simpa using this
    rw [e2]
    simpa using e1.symm
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

end U3Start

structure U3C1CartanFpf {G : Type} [Group G] (L T D : Subgroup G) (d : G) : Prop
    extends U3C1Cartan L T D d where
  le_zpowers : D ≤ zpowers d
  fpf : ∃ e ∈ D, (∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b) ∧
    ∀ y ∈ szT₁ L T, y⁻¹ * (e * y * e⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T)

theorem U3Start.exists_u3C1CartanFpf {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G} (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (D : Subgroup G) (d : G), U3C1CartanFpf L T D d := by
  obtain ⟨D, d, hdD, hDL, hDN, hinf, hodd, htr, hconj, hDz, hfpf⟩ :=
    h.exists_cartan_fpf_of_card_sylow hS2
  exact ⟨D, d, ⟨⟨hdD, hDL, hDN, hinf, hodd, htr, hconj⟩, hDz, hfpf⟩⟩

end CFSG.SeitzReduction.RankOne
