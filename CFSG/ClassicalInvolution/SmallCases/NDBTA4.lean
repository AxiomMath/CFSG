module

public import CFSG.ClassicalInvolution.SmallCases.NDBTA3

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.ComponentClassification

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace TA

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_fixed_sqrt (hp : p ≠ 2) {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω)
    {L : Subgroup G} (hL : L ∈ Ω) {l : G} (hl : IsUniqueInvolution L l) {a b : G}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G)) :
    ∃ c ∈ L, c * c = l ∧ (a * c = c * a ∨ b * c = c * b ∨ (a * b) * c = c * (a * b)) := by
  classical
  set E : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hE
  have hE2 : IsPGroup 2 E := by
    refine Lift.isPGroup_sup_of_commute (ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2)
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hb2) ?_
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute a b from hab) i j)).eq
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr haN) (Subgroup.zpowers_le.mpr hbN)
  obtain ⟨R, hR, hRinv⟩ := AscL62.exists_sylow_normalized hE2 hEN
  have hquat : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hL hR)
  have hlR : l ∈ R :=
    mem_of_uniqueInvolution_of_pGroup hl hR.1 hR.2.1 (by have := hquat.eight_le; omega)
  have hlR' : IsUniqueInvolution R l := isUniqueInvolution_of_le hl hR.1 hlR
  obtain ⟨C, hCR, hCc, hCcard, hCinv⟩ := exists_invariant_cyclic hquat hlR' hE2 hRinv
  obtain ⟨c, hcC, hcc⟩ := exists_sq_eq_of_index_two hquat hlR' hCR hCc hCcard
  have haE : a ∈ E := (le_sup_left : Subgroup.zpowers a ≤ E) (Subgroup.mem_zpowers a)
  have hbE : b ∈ E := (le_sup_right : Subgroup.zpowers b ≤ E) (Subgroup.mem_zpowers b)
  have hroot : ∀ x ∈ E, x * c * x⁻¹ = c ∨ x * c * x⁻¹ = l * c := by
    intro x hx
    have hxC : x * c * x⁻¹ ∈ C := by
      have := conj_mem_conjSub (n := x) hcC
      rwa [hCinv x hx] at this
    have hxl : x * l * x⁻¹ = l := hlR'.conj_eq (hRinv x hx)
    have hsq : (x * c * x⁻¹) * (x * c * x⁻¹) = l := by
      calc (x * c * x⁻¹) * (x * c * x⁻¹) = x * (c * c) * x⁻¹ := by group
        _ = l := by rw [hcc, hxl]
    set y : G := x * c * x⁻¹ with hy
    have hyc : y * c = c * y := mul_comm_of_isCyclic hCc hxC hcC
    have hu : (y * c⁻¹) * (y * c⁻¹) = 1 := by
      have hyc' : c⁻¹ * y = y * c⁻¹ := by
        calc c⁻¹ * y = c⁻¹ * (y * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * y) * c⁻¹ := by rw [hyc]
          _ = y * c⁻¹ := by group
      calc (y * c⁻¹) * (y * c⁻¹) = y * (c⁻¹ * y) * c⁻¹ := by group
        _ = y * (y * c⁻¹) * c⁻¹ := by rw [hyc']
        _ = (y * y) * (c * c)⁻¹ := by group
        _ = 1 := by rw [hsq, hcc, mul_inv_cancel]
    have huL : y * c⁻¹ ∈ L := hR.1 (hCR (C.mul_mem hxC (C.inv_mem hcC)))
    rcases hl.unique _ huL hu with h | h
    · left
      calc y = y * c⁻¹ * c := by group
        _ = c := by rw [h, one_mul]
    · right
      calc y = y * c⁻¹ * c := by group
        _ = l * c := by rw [h]
  refine ⟨c, hR.1 (hCR hcC), hcc, ?_⟩
  have hfix : ∀ x : G, x * c * x⁻¹ = c → x * c = c * x := fun x h => by
    calc x * c = (x * c * x⁻¹) * x := by group
      _ = c * x := by rw [h]
  rcases hroot a haE with ha | ha
  · exact Or.inl (hfix a ha)
  rcases hroot b hbE with hb | hb
  · exact Or.inr (Or.inl (hfix b hb))
  refine Or.inr (Or.inr (hfix _ ?_))
  have hal : a * l * a⁻¹ = l := hlR'.conj_eq (hRinv a haE)
  calc a * b * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by group
    _ = a * (l * c) * a⁻¹ := by rw [hb]
    _ = (a * l * a⁻¹) * (a * c * a⁻¹) := by group
    _ = l * (l * c) := by rw [hal, ha]
    _ = c := by rw [← mul_assoc, hl.sq, one_mul]

theorem exists_lInvariant_triangle {Ω : Set (Subgroup G)} {z : G} (C : Asc77.XCtx p f Ω z)
    {N N' : Subgroup G} (hN : N ∈ tqMembers Ω z) (hN' : N' ∈ tqMembers Ω z) {n n' : G}
    (hn : IsClassicalMember p f N n) (hn' : IsClassicalMember p f N' n') (hnz : n ≠ z)
    (hprod : ∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
      (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩)
    {l : G} (hlC : l ∈ Subgroup.centralizer ({z} : Set G)) (hl2 : l * l = 1)
    (hA : conjSub (oddQuotMk z ⟨l, hlC⟩) (modOdd z (exactCore z N)) = modOdd z (exactCore z N)) :
    ∃ (N₁ N₂ : Subgroup G) (n₁ : G), N₁ ∈ tqMembers Ω z ∧ N₂ ∈ tqMembers Ω z ∧
      IsClassicalMember p f N₁ n₁ ∧ IsClassicalMember p f N₂ (z * n₁) ∧ n₁ ≠ z ∧
      n₁ * l = l * n₁ ∧ n₁ * z = z * n₁ := by
  classical
  set Cz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCz
  set O : Subgroup G := oddCoreIn Cz with hO
  have hΩ := C.hΩ.conjInvariant
  have hzC : z ∈ Cz := Asc77.XCtx.hzC z
  have hnC : n ∈ Cz := C.involution_mem_centralizer hN hn
  have hn'C : n' ∈ Cz := C.involution_mem_centralizer hN' hn'
  have hn2 : n * n = 1 := hn.isCentralInvolution.sq
  have hn'2 : n' * n' = 1 := hn'.isCentralInvolution.sq
  have un := C.isUniqueInvolution_modOdd hN hn
  have hfix : oddQuotMk z ⟨l, hlC⟩ * oddQuotMk z ⟨n, hnC⟩ =
      oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨l, hlC⟩ := by
    have h1 := un.conj_eq hA
    calc oddQuotMk z ⟨l, hlC⟩ * oddQuotMk z ⟨n, hnC⟩ =
        (oddQuotMk z ⟨l, hlC⟩ * oddQuotMk z ⟨n, hnC⟩ * (oddQuotMk z ⟨l, hlC⟩)⁻¹) *
          oddQuotMk z ⟨l, hlC⟩ := by group
      _ = oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨l, hlC⟩ := by rw [h1]
  have hcomm : ∀ x ∈ Subgroup.zpowers l, (x * n * x⁻¹) * n ∈ O := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hlk : l ^ k ∈ Cz := Cz.zpow_mem hlC k
    have hmem : (l ^ k * n * (l ^ k)⁻¹) * n ∈ Cz :=
      Cz.mul_mem (Cz.mul_mem (Cz.mul_mem hlk hnC) (Cz.inv_mem hlk)) hnC
    have e1 : (⟨(l ^ k * n * (l ^ k)⁻¹) * n, hmem⟩ : ↥Cz) =
        (⟨l, hlC⟩ : ↥Cz) ^ k * ⟨n, hnC⟩ * ((⟨l, hlC⟩ : ↥Cz) ^ k)⁻¹ * ⟨n, hnC⟩ := by
      apply Subtype.ext
      simp
    have hc : Commute (oddQuotMk z ⟨l, hlC⟩) (oddQuotMk z ⟨n, hnC⟩) := hfix
    have hn2' : oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨n, hnC⟩ = 1 := by
      rw [← map_mul]
      have e : (⟨n, hnC⟩ * ⟨n, hnC⟩ : ↥Cz) = 1 := Subtype.ext hn2
      rw [e, map_one]
    have h1 : oddQuotMk z ⟨(l ^ k * n * (l ^ k)⁻¹) * n, hmem⟩ = 1 := by
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_zpow]
      rw [(hc.zpow_left k).eq]
      calc oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨l, hlC⟩ ^ k * (oddQuotMk z ⟨l, hlC⟩ ^ k)⁻¹ *
            oddQuotMk z ⟨n, hnC⟩ = oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨n, hnC⟩ := by group
        _ = 1 := hn2'
    exact ⟨⟨_, hmem⟩, oddQuotMk_eq_one_iff.mp h1, rfl⟩
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn Cz
  have hFN : Subgroup.zpowers l ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.mpr (normalizer_oddCoreIn Cz hlC)
  obtain ⟨o, hoO, hoF⟩ := Asc77.exists_conj_involution_commuting hOodd hFN
    (ExactLayer.isPGroup_zpowers_of_sq_eq_one hl2) hn2 hcomm
  have hoC : o ∈ Cz := oddCoreIn_le Cz hoO
  set n₁ : G := o * n * o⁻¹ with hn₁def
  have hn₁l : n₁ * l = l * n₁ := (hoF l (Subgroup.mem_zpowers l)).symm
  have hoz : o * z * o⁻¹ = z := Bootstrap.conj_eq_of_mem_centralizer_singleton hoC
  have hN₁ : conjSub o N ∈ tqMembers Ω z := conjSub_mem_tqMembers hΩ hoC hN
  have hn₁ : IsClassicalMember p f (conjSub o N) n₁ := hn.conj o
  have hn₁z : n₁ ≠ z := by
    intro h
    apply hnz
    calc n = o⁻¹ * n₁ * o := by rw [hn₁def]; group
      _ = o⁻¹ * (o * z * o⁻¹) * o := by rw [h, hoz]
      _ = z := by group
  have hn₁C : n₁ ∈ Cz := C.involution_mem_centralizer hN₁ hn₁
  have hn₁zc : n₁ * z = z * n₁ := Subgroup.mem_centralizer_singleton_iff.mp hn₁C
  have hob : oddQuotMk z ⟨o, hoC⟩ = 1 := by
    rw [oddQuotMk_eq_one_iff]
    obtain ⟨o', ho', hoo⟩ := hoO
    have : o' = ⟨o, hoC⟩ := Subtype.ext hoo
    rwa [← this]
  have hn₁b : oddQuotMk z ⟨n₁, hn₁C⟩ = oddQuotMk z ⟨n, hnC⟩ := by
    have e : (⟨n₁, hn₁C⟩ : ↥Cz) = ⟨o, hoC⟩ * ⟨n, hnC⟩ * (⟨o, hoC⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, hob]
    group
  obtain ⟨hnC', hn'C', hpr⟩ := hprod
  have hzn : oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨n, hnC⟩ =
      oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨z, hzC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hnC).symm
  have hn2' : oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨n, hnC⟩ = 1 := by
    rw [← map_mul]
    have e : (⟨n, hnC⟩ * ⟨n, hnC⟩ : ↥Cz) = 1 := Subtype.ext hn2
    rw [e, map_one]
  have hpr' : oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨n', hn'C⟩ = oddQuotMk z ⟨z, hzC⟩ := hpr
  have hn'b : oddQuotMk z ⟨n', hn'C⟩ = oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨n, hnC⟩ := by
    calc oddQuotMk z ⟨n', hn'C⟩ =
        (oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨n, hnC⟩) * oddQuotMk z ⟨n', hn'C⟩ := by
          rw [hn2', one_mul]
      _ = oddQuotMk z ⟨n, hnC⟩ * (oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨n', hn'C⟩) := by
          rw [mul_assoc]
      _ = oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨z, hzC⟩ := by rw [hpr']
      _ = oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨n, hnC⟩ := hzn.symm
  have hzn₁C : z * n₁ ∈ Cz := Cz.mul_mem hzC hn₁C
  have heq : oddQuotMk z ⟨z * n₁, hzn₁C⟩ = oddQuotMk z ⟨n', hn'C⟩ := by
    have e : (⟨z * n₁, hzn₁C⟩ : ↥Cz) = ⟨z, hzC⟩ * ⟨n₁, hn₁C⟩ := rfl
    rw [e, map_mul, hn₁b, hn'b]
  have hzL : z ∈ exactLayer Ω z := C.z_mem_exactLayer
  have hn₁L : n₁ ∈ exactLayer Ω z :=
    exactCore_le_exactLayer hN₁ (C.involution_mem_exactCore hN₁ hn₁)
  have hn'L : n' ∈ exactLayer Ω z :=
    exactCore_le_exactLayer hN' (C.involution_mem_exactCore hN' hn')
  have hn₁2 : n₁ * n₁ = 1 := hn₁.isCentralInvolution.sq
  have hs₁ : (z * n₁) * (z * n₁) = 1 := by
    calc (z * n₁) * (z * n₁) = z * (n₁ * z) * n₁ := by group
      _ = z * (z * n₁) * n₁ := by rw [hn₁zc]
      _ = (z * z) * (n₁ * n₁) := by group
      _ = 1 := by rw [C.hz2, hn₁2, one_mul]
  obtain ⟨o₂, ho₂, he⟩ := C.exists_conj_of_oddQuotMk_eq ((exactLayer Ω z).mul_mem hzL hn₁L) hn'L
    hs₁ hn'2 heq
  have ho₂C : o₂ ∈ Cz := exactLayer_le_centralizer Ω z (oddCoreIn_le _ ho₂)
  have hN₂ : conjSub o₂ N' ∈ tqMembers Ω z := conjSub_mem_tqMembers hΩ ho₂C hN'
  have hn₂ : IsClassicalMember p f (conjSub o₂ N') (z * n₁) := by
    rw [he]
    exact hn'.conj o₂
  exact ⟨conjSub o N, conjSub o₂ N', n₁, hN₁, hN₂, hn₁, hn₂, hn₁z, hn₁l, hn₁zc⟩

theorem caseA_false {K : Subgroup G} {z : G} (C : Asc77.XCtx p f (𝒞 K) z)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) (hz : IsClassicalMember p f K z)
    (hT : ¬ HasTwin p f K z) {N N' : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z)
    (hN' : N' ∈ tqMembers (𝒞 K) z) {n n' : G} (hn : IsClassicalMember p f N n)
    (hn' : IsClassicalMember p f N' n') (hnz : n ≠ z)
    (hprod : ∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
      (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩)
    {g : G} (hgz : g * z * g⁻¹ ≠ z) (hl : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G))
    (hLz : conjSub g K ∉ tqMembers (𝒞 K) z)
    (hA : conjSub (oddQuotMk z ⟨g * z * g⁻¹, hl⟩) (modOdd z (exactCore z N)) =
      modOdd z (exactCore z N)) : False := by
  classical
  have hp := C.hp
  have hq := C.hq
  have hΩ : HypOmegaMod p f (𝒞 K) := C.hΩ
  have hKK : K ∈ 𝒞 K := mem_conjClass_self K
  have hLΩ : conjSub g K ∈ 𝒞 K := ⟨g, rfl⟩
  have hLl : IsClassicalMember p f (conjSub g K) (g * z * g⁻¹) := hz.conj g
  have hz2 : z * z = 1 := C.hz2
  have hl2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := hLl.isCentralInvolution.sq
  have hcl : g * z * g⁻¹ * z = z * (g * z * g⁻¹) := Subgroup.mem_centralizer_singleton_iff.mp hl
  have hUL := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hLl
  have hCl := mem_normalizer_of_noTwin hp hq hz hT hLΩ hLl
  obtain ⟨N₁, N₂, n₁, hN₁, hN₂, hn₁, hn₂, hn₁z, hn₁l, hn₁zc⟩ :=
    exists_lInvariant_triangle C hN hN' hn hn' hnz hprod hl hl2 hA
  have hn₁2 : n₁ * n₁ = 1 := hn₁.isCentralInvolution.sq
  have hzn₁z : z * n₁ ≠ z := by
    intro h
    apply hn₁.isCentralInvolution.ne_one
    calc n₁ = z⁻¹ * (z * n₁) := by group
      _ = z⁻¹ * z := by rw [h]
      _ = 1 := inv_mul_cancel z
  have hKn₁ : K ∈ tqMembers (𝒞 K) n₁ := mem_tqMembers_symm hp hq hΩ hKK hN₁.1 hz hn₁ hn₁z hN₁
  have hKzn₁ : K ∈ tqMembers (𝒞 K) (z * n₁) :=
    mem_tqMembers_symm hp hq hΩ hKK hN₂.1 hz hn₂ hzn₁z hN₂
  have hzL : z ∉ trivialOnQuot (conjSub g K) := fun h => hLz ⟨hLΩ, h⟩
  have hn₁L : n₁ ∉ trivialOnQuot (conjSub g K) := fun h =>
    not_mem_tqMembers_of_partner C hall hz hT hLΩ hLl hgz hcl hLz hN₁.1 hn₁ hKn₁ ⟨hLΩ, h⟩
  have hzn₁L : z * n₁ ∉ trivialOnQuot (conjSub g K) := fun h =>
    not_mem_tqMembers_of_partner C hall hz hT hLΩ hLl hgz hcl hLz hN₂.1 hn₂ hKzn₁ ⟨hLΩ, h⟩
  have hln₁ : g * z * g⁻¹ ≠ n₁ := by
    intro h
    rw [h] at hLl
    have e := NDBH2.eq_of_isClassicalMember hp hq hz hT hLΩ hN₁.1 hLl hn₁
    exact hLz (e ▸ hN₁)
  have hlzn₁ : g * z * g⁻¹ ≠ z * n₁ := by
    intro h
    rw [h] at hLl
    have e := NDBH2.eq_of_isClassicalMember hp hq hz hT hLΩ hN₂.1 hLl hn₂
    exact hLz (e ▸ hN₂)
  have hzN : z ∈ Subgroup.normalizer (conjSub g K : Set G) :=
    hCl (Subgroup.mem_centralizer_singleton_iff.mpr hcl.symm)
  have hn₁N : n₁ ∈ Subgroup.normalizer (conjSub g K : Set G) :=
    hCl (Subgroup.mem_centralizer_singleton_iff.mpr hn₁l)
  obtain ⟨c, hcL, hcc, hcomm⟩ :=
    exists_fixed_sqrt hp hΩ hLΩ hUL hz2 hn₁2 hn₁zc.symm hzN hn₁N
  have hc4 : orderOf c = 4 := by
    have h1 : ¬ c ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, hcc]
      exact hUL.ne_one
    have h2 : c ^ 2 ^ (1 + 1) = 1 := by
      calc c ^ 2 ^ (1 + 1) = (c * c) * (c * c) := by
            rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num, pow_succ, pow_succ, pow_succ, pow_one]
            group
        _ = 1 := by rw [hcc, hl2]
    have := orderOf_eq_prime_pow h1 h2
    rw [this]
    norm_num
  have hW2 : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hc4]; norm_num)
  have hW4 : 4 ≤ Nat.card (Subgroup.zpowers c) := by rw [Nat.card_zpowers, hc4]
  have hWL : Subgroup.zpowers c ≤ conjSub g K := Subgroup.zpowers_le.mpr hcL
  have hlW : g * z * g⁻¹ ∈ Subgroup.zpowers c :=
    Subgroup.mem_zpowers_iff.mpr ⟨2, by rw [zpow_two, hcc]⟩
  have hWc : ∀ {e : G}, e * c = c * e →
      Subgroup.zpowers c ≤ Subgroup.centralizer ({e} : Set G) := fun h =>
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h.symm)
  rcases hcomm with h | h | h
  ·
    rcases torus_pin hp hq hΩ hLΩ hKK hUL
        (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz) hgz hcl.symm hn₁l hn₁zc
        hn₁2 hKn₁.2 hCl (mem_normalizer_of_noTwin hp hq hz hT hKK hz) hWL hW2 hlW (hWc h) hW4
      with h1 | h1 | h1
    · exact hzL h1
    · exact hn₁L h1
    · exact hzn₁L h1
  ·
    rcases torus_pin hp hq hΩ hLΩ hN₁.1 hUL
        (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hn₁) hln₁ hn₁l.symm.symm
        hcl.symm hn₁zc.symm hz2 hN₁.2 hCl (mem_normalizer_of_noTwin hp hq hz hT hN₁.1 hn₁) hWL
        hW2 hlW (hWc h) hW4 with h1 | h1 | h1
    · exact hn₁L h1
    · exact hzL h1
    · rw [hn₁zc] at h1
      exact hzn₁L h1
  ·
    have he₀l : z * n₁ * (g * z * g⁻¹) = g * z * g⁻¹ * (z * n₁) := by
      calc z * n₁ * (g * z * g⁻¹) = z * (n₁ * (g * z * g⁻¹)) := by group
        _ = z * ((g * z * g⁻¹) * n₁) := by rw [hn₁l]
        _ = (z * (g * z * g⁻¹)) * n₁ := by group
        _ = ((g * z * g⁻¹) * z) * n₁ := by rw [hcl]
        _ = g * z * g⁻¹ * (z * n₁) := by group
    have he₁e₀ : z * (z * n₁) = z * n₁ * z := by
      calc z * (z * n₁) = z * (n₁ * z) := by rw [hn₁zc]
        _ = z * n₁ * z := by group
    rcases torus_pin hp hq hΩ hLΩ hN₂.1 hUL
        (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hn₂) hlzn₁ he₀l hcl.symm
        he₁e₀ hz2 hN₂.2 hCl (mem_normalizer_of_noTwin hp hq hz hT hN₂.1 hn₂) hWL hW2 hlW
        (hWc h) hW4 with h1 | h1 | h1
    · exact hzn₁L h1
    · exact hzL h1
    · have e : z * n₁ * z = n₁ := by
        calc z * n₁ * z = z * (n₁ * z) := by group
          _ = z * (z * n₁) := by rw [hn₁zc]
          _ = n₁ := by rw [← mul_assoc, hz2, one_mul]
      rw [e] at h1
      exact hn₁L h1

end TA

variable (p f : ℕ) [Fact p.Prime]

theorem triangleA2CaseA_proved : TriangleA2CaseA p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow _ _ D hall N hN n hn hnz hT N' hN' n' hn' _ _ hprod
    _ g hgz hl _ hpart hA _
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have hall' : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2 := hall
  exact TA.caseA_false C hall' hz hT hN hN' hn hn' hnz hprod hgz hl
    (hpart z (Set.mem_insert z _)).1 hA

theorem triangleA2Partner_proved : TriangleA2Partner p f :=
  triangleA2Partner_of_caseA (triangleA2CaseA_proved p f)

end CFSG.ClassicalInvolution.NDB
