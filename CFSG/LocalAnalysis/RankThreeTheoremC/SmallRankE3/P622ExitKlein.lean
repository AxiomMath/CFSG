module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622ExitAbs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619L32

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp
open scoped MatrixGroups

variable {C : Type} [Group C] [Finite C]

private theorem p622Klein_isPGroup {S : Subgroup GL32}
    (h : ∀ g ∈ S, ∃ k : ℕ, g ^ 2 ^ k = 1) : IsPGroup 2 S := by
  intro g
  obtain ⟨k, hk⟩ := h g.1 g.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem p622Klein_mem_map {L S : Subgroup C} (e : ↥L ≃* GL32) {g : GL32} :
    g ∈ (S.subgroupOf L).map e.toMonoidHom ↔ ((e.symm g : ↥L) : C) ∈ S := by
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]

private theorem p622Klein_card_map {L S : Subgroup C} (e : ↥L ≃* GL32) (hSL : S ≤ L) :
    Nat.card ((S.subgroupOf L).map e.toMonoidHom) = Nat.card S := by
  rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv

private theorem p622Klein_props {L S : Subgroup C} (e : ↥L ≃* GL32) (hSL : S ≤ L)
    (hS : ∀ g ∈ S, ∃ k : ℕ, g ^ 2 ^ k = 1) (hSne : S ≠ ⊥) :
    IsPGroup 2 ((S.subgroupOf L).map e.toMonoidHom) ∧
      (S.subgroupOf L).map e.toMonoidHom ≠ ⊥ := by
  have hne' : ∃ u ∈ S, u ≠ 1 := by
    by_contra hcon
    apply hSne
    ext u
    rw [Subgroup.mem_bot]
    exact ⟨fun hu => Classical.byContradiction fun h1 => hcon ⟨u, hu, h1⟩,
      fun h => by rw [h]; exact S.one_mem⟩
  refine ⟨p622Klein_isPGroup ?_, ?_⟩
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨k, hk⟩ := hS (w : C) (Subgroup.mem_subgroupOf.1 hw)
    refine ⟨k, ?_⟩
    have hw1 : w ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [← map_pow, hw1, map_one]
  · intro hbot
    obtain ⟨u, hu, hu1⟩ := hne'
    have hmem : e ⟨u, hSL hu⟩ ∈ (S.subgroupOf L).map e.toMonoidHom :=
      Subgroup.mem_map.2 ⟨⟨u, hSL hu⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hu1
    have h1 : (⟨u, hSL hu⟩ : ↥L) = 1 := e.injective (by rw [hmem, map_one])
    exact congrArg Subtype.val h1

private theorem p622Klein_normalizer {L S : Subgroup C} (e : ↥L ≃* GL32) {z : C}
    (hzL : z ∈ L) (hzS : z ∈ normalizer (S : Set C)) :
    e ⟨z, hzL⟩ ∈ normalizer (((S.subgroupOf L).map e.toMonoidHom : Subgroup GL32) : Set GL32) := by
  refine mem_normalizer_iff.2 fun h => ?_
  have hl : e.symm (e ⟨z, hzL⟩ * h * (e ⟨z, hzL⟩)⁻¹) =
      ((⟨z, hzL⟩ : ↥L) * e.symm h * (⟨z, hzL⟩ : ↥L)⁻¹) := by
    simp
  try simp only [SetLike.mem_coe]
  rw [p622Klein_mem_map e, p622Klein_mem_map e, hl]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.1 hzS _

private theorem p622Klein_orderOf {L : Subgroup C} (e : ↥L ≃* GL32) {z : C} (hzL : z ∈ L)
    (hz3 : orderOf z = 3) : orderOf (e ⟨z, hzL⟩) = 3 := by
  have h : orderOf (e ⟨z, hzL⟩) = orderOf (⟨z, hzL⟩ : ↥L) :=
    orderOf_injective e.toMonoidHom e.injective _
  rw [h, orderOf_mk, hz3]

private theorem p622Klein_card_four {L S : Subgroup C} (e : ↥L ≃* GL32) {z : C}
    (hzL : z ∈ L) (hz3 : orderOf z = 3) (hSL : S ≤ L)
    (hS : ∀ g ∈ S, ∃ k : ℕ, g ^ 2 ^ k = 1) (hSne : S ≠ ⊥) (hzS : z ∈ normalizer (S : Set C)) :
    Nat.card S = 4 := by
  obtain ⟨h1, h2⟩ := p622Klein_props e hSL hS hSne
  have h := card_eq_four_of_normalized_two_subgroup (p622Klein_orderOf e hzL hz3) h1 h2
    (p622Klein_normalizer e hzL hzS)
  rw [← p622Klein_card_map e hSL]
  exact h

private theorem p622Klein_mem_normalizer {U : Subgroup C} {u : C} (hu : u ∈ U) :
    u ∈ normalizer (U : Set C) := by
  refine mem_normalizer_iff.2 fun h => ?_
  refine ⟨fun hh => U.mul_mem (U.mul_mem hu hh) (U.inv_mem hu), fun hh => ?_⟩
  have := U.mul_mem (U.mul_mem (U.inv_mem hu) hh) (U.inv_mem (U.inv_mem hu))
  have key : u⁻¹ * (u * h * u⁻¹) * u⁻¹⁻¹ = h := by group
  rw [key] at this
  exact this

private theorem p622Klein_normalizer_inf {U L : Subgroup C} [L.Normal] {g : C}
    (hgU : g ∈ normalizer (U : Set C)) : g ∈ normalizer ((U ⊓ L : Subgroup C) : Set C) := by
  refine mem_normalizer_iff.2 fun h => ?_
  have hU' := mem_normalizer_iff.1 hgU h
  have hL' : h ∈ L ↔ g * h * g⁻¹ ∈ L := by
    refine ⟨fun hh => Subgroup.Normal.conj_mem ‹L.Normal› h hh g, fun hh => ?_⟩
    have := Subgroup.Normal.conj_mem ‹L.Normal› _ hh g⁻¹
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  simp only [SetLike.mem_coe, Subgroup.mem_inf] at hU' ⊢
  exact and_congr hU' hL'

private theorem p622Klein_mem_of_pow {L : Subgroup C} (e : ↥L ≃* GL32) {x : C}
    (hx : x ∈ Subgroup.center C) (hx3 : orderOf x = 3)
    (hcent : centralizer (L : Set C) = zpowers x) {l u : C} (hl : l ∈ L) {i : ℤ}
    (hu : u = x ^ i * l) {m : ℕ} (hum : u ^ 2 ^ m = 1) : u ∈ L := by
  have hinf := p622Exit_inf_centralizer e
  have hcomm : Commute (x ^ i) l :=
    (Commute.zpow_right (show Commute l x from Subgroup.mem_center_iff.1 hx l) i).symm
  have hpow : (x ^ i) ^ 2 ^ m * l ^ 2 ^ m = 1 := by
    rw [← hcomm.mul_pow, ← hu]
    exact hum
  have hxn : x ^ (i * ((2 ^ m : ℕ) : ℤ)) = (l ^ 2 ^ m)⁻¹ := by
    rw [zpow_mul, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left hpow
  have hmem : x ^ (i * ((2 ^ m : ℕ) : ℤ)) ∈ centralizer (L : Set C) ⊓ L := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hcent]
      exact zpow_mem (mem_zpowers x) _
    · rw [hxn]
      exact L.inv_mem (L.pow_mem hl _)
  rw [hinf, Subgroup.mem_bot] at hmem
  have hdvd : ((orderOf x : ℕ) : ℤ) ∣ i * ((2 ^ m : ℕ) : ℤ) :=
    orderOf_dvd_iff_zpow_eq_one.2 hmem
  rw [hx3] at hdvd
  have h3 : (3 : ℤ) ∣ i * 2 ^ m := by exact_mod_cast hdvd
  have hcop : IsCoprime (3 : ℤ) (2 ^ m) :=
    IsCoprime.pow_right (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num))
  have h3i : (3 : ℤ) ∣ i := hcop.dvd_of_dvd_mul_right h3
  have hx1 : x ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [hx3]; exact_mod_cast h3i)
  rw [hu, hx1, one_mul]
  exact hl

private theorem p622Klein_card_le_two {L : Subgroup C} [L.Normal] (e : ↥L ≃* GL32)
    (hcard : Nat.card C = 504 ∨ Nat.card C = 1008) {U : Subgroup C} (hU : IsPGroup 2 U)
    (hinf : U ⊓ L = ⊥) : Nat.card U ≤ 2 := by
  have hLc : Nat.card L = 168 := by
    rw [Nat.card_congr e.toEquiv, card_GL]
  have hmul := Subgroup.card_mul_index L
  rw [hLc] at hmul
  have hidx : L.index = 3 ∨ L.index = 6 := by
    rcases hcard with h | h <;> rw [h] at hmul <;> omega
  let f : U →* C ⧸ L := (QuotientGroup.mk' L).comp U.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haL : (a : C) ∈ L := (QuotientGroup.eq_one_iff (a : C)).1 ha
    have hbot : (a : C) ∈ U ⊓ L := Subgroup.mem_inf.2 ⟨a.2, haL⟩
    rw [hinf, Subgroup.mem_bot] at hbot
    exact Subtype.ext hbot
  have hdvd : Nat.card U ∣ L.index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_dvd_of_injective f hf
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hU
  rw [hn] at hdvd
  have h6 : 2 ^ n ∣ 6 := by
    rcases hidx with h | h <;> rw [h] at hdvd
    · exact dvd_trans hdvd (by norm_num)
    · exact hdvd
  have hle : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hn2 : n ≤ 2 := by
    by_contra hc
    have hc3 : 3 ≤ n := by omega
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc3
    omega
  rw [hn]
  interval_cases n <;> first | (norm_num at h6; done) | norm_num

private theorem p622Klein_conj_eq {U : Subgroup C} {z : C} (hzU : z ∈ normalizer (U : Set C))
    (hle : Nat.card U ≤ 2) {y : C} (hyU : y ∈ U) (hy1 : y ≠ 1) : z * y * z⁻¹ = y := by
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hord_dvd : orderOf y ∣ Nat.card U := by
    have h := orderOf_dvd_natCard (⟨y, hyU⟩ : U)
    rwa [orderOf_mk] at h
  have hpos' : 0 < orderOf y := Nat.pos_of_dvd_of_pos hord_dvd hpos
  have hle' : orderOf y ≤ Nat.card U := Nat.le_of_dvd hpos hord_dvd
  have hord1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  have hord2 : orderOf y = 2 := by omega
  have hzp : zpowers y = U := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyU) ?_
    rw [Nat.card_zpowers, hord2]
    exact hle
  have hw : z * y * z⁻¹ ∈ zpowers y := by
    rw [hzp]
    exact (mem_normalizer_iff.1 hzU y).1 hyU
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hw
  have hk' : y ^ (k % 2) = z * y * z⁻¹ := by
    have h := zpow_mod_orderOf y k
    rw [hord2] at h
    rw [← hk]
    exact h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk'
    exact absurd (conj_eq_one_iff.1 hk'.symm) hy1
  · rw [h1, zpow_one] at hk'
    exact hk'.symm

private theorem p622Klein_comm_of_orderOf_four {U : Subgroup C} {z : C}
    (hzU : z ∈ normalizer (U : Set C)) (hz3 : orderOf z = 3) (hU4 : Nat.card U = 4)
    {g : C} (hgU : g ∈ U) (hg4 : orderOf g = 4) : ∀ y ∈ U, z * y = y * z := by
  have hzp : zpowers g = U := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hgU) (le_of_eq ?_)
    rw [Nat.card_zpowers, hg4, hU4]
  have hgz : z * g * z⁻¹ ∈ zpowers g := by
    rw [hzp]
    exact (mem_normalizer_iff.1 hzU g).1 hgU
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hgz
  have hσ : ∀ j : ℤ, z * g ^ j * z⁻¹ = g ^ (k * j) := fun j => by
    rw [← conj_zpow, ← hk, ← zpow_mul]
  have hz3' : z * z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz3, pow_three'] at h
    exact h
  have h3 : z * (z * (z * g * z⁻¹) * z⁻¹) * z⁻¹ = g := by
    calc z * (z * (z * g * z⁻¹) * z⁻¹) * z⁻¹ = (z * z * z) * g * (z * z * z)⁻¹ := by group
      _ = g := by rw [hz3']; simp
  have hkey : g ^ (k * (k * k)) = g := by
    rw [← hσ (k * k), ← hσ k, hk]
    exact h3
  have hmod : (k * (k * k) : ℤ) ≡ 1 [ZMOD ((orderOf g : ℕ) : ℤ)] :=
    zpow_eq_zpow_iff_modEq.1 (hkey.trans (zpow_one g).symm)
  rw [hg4] at hmod
  have hZ : (((k * (k * k) : ℤ)) : ZMod 4) = ((1 : ℤ) : ZMod 4) :=
    (ZMod.intCast_eq_intCast_iff _ _ 4).2 hmod
  push_cast at hZ
  have key4 : ∀ a : ZMod 4, a * (a * a) = 1 → a = 1 := by decide
  have hk1 : ((k : ℤ) : ZMod 4) = 1 := key4 _ hZ
  have hk1' : k ≡ 1 [ZMOD ((4 : ℕ) : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ 4).1 (by rw [Int.cast_one]; exact hk1)
  have hmod2 : k ≡ 1 [ZMOD ((orderOf g : ℕ) : ℤ)] := by
    rw [hg4]
    exact hk1'
  have hgk : g ^ k = g ^ (1 : ℤ) := zpow_eq_zpow_iff_modEq.2 hmod2
  rw [zpow_one] at hgk
  have hzg : z * g * z⁻¹ = g := by
    rw [← hk]
    exact hgk
  have hcomm : Commute z g := mul_inv_eq_iff_eq_mul.1 hzg
  intro y hy
  have hy' : y ∈ zpowers g := by
    rw [hzp]
    exact hy
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy'
  exact (hcomm.zpow_right n).eq

private theorem p622Klein_sq {U : Subgroup C} {z : C} (hzU : z ∈ normalizer (U : Set C))
    (hz3 : orderOf z = 3) (hU4 : Nat.card U = 4) (hnc : ∃ y ∈ U, z * y ≠ y * z) :
    ∀ g ∈ U, g ^ 2 = 1 := by
  intro g hg
  have hdvd : orderOf g ∣ 4 := by
    have h := orderOf_dvd_natCard (⟨g, hg⟩ : U)
    rwa [orderOf_mk, hU4] at h
  have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  rcases (by omega : orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 4) with
    h | h | h | h
  · rw [orderOf_eq_one_iff.1 h, one_pow]
  · exact orderOf_dvd_iff_pow_eq_one.1 (by simp [h])
  · rw [h] at hdvd
    norm_num at hdvd
  · obtain ⟨y, hyU, hzy⟩ := hnc
    exact absurd (p622Klein_comm_of_orderOf_four hzU hz3 hU4 hg h y hyU) hzy

private theorem p622Klein_iso {U : Subgroup C} [Nontrivial U] (h4 : Nat.card U = 4)
    (hsq : ∀ g ∈ U, g ^ 2 = 1) :
    Nonempty (↥U ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have hsq' : ∀ g : U, g ^ 2 = 1 := fun g => Subtype.ext (by simpa using hsq g.1 g.2)
  haveI : IsKleinFour U :=
    ⟨h4, (Monoid.exponent_eq_prime_iff Nat.prime_two).2 fun g hg => orderOf_eq_prime (hsq' g) hg⟩
  obtain ⟨f⟩ : Nonempty (U ≃* Multiplicative (ZMod 2 × ZMod 2)) := IsKleinFour.nonempty_mulEquiv
  exact ⟨f.trans (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2))⟩

theorem p622Exit_klein {L : Subgroup C} [L.Normal] (e : ↥L ≃* GL32) {x z : C}
    (hx : x ∈ Subgroup.center C) (hx3 : orderOf x = 3)
    (hcent : centralizer (L : Set C) = zpowers x) (hcard : Nat.card C = 504 ∨ Nat.card C = 1008)
    (hzL : z ∈ L) (hz3 : orderOf z = 3) {U : Subgroup C} (hU : IsPGroup 2 U)
    (hzU : z ∈ normalizer (U : Set C)) (hnc : ∃ y ∈ U, z * y ≠ y * z) :
    Nonempty (↥U ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have hU2 : ∀ g ∈ U, ∃ k : ℕ, g ^ 2 ^ k = 1 := fun g hg => by
    obtain ⟨k, hk⟩ := hU ⟨g, hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hVne : U ⊓ L ≠ ⊥ := by
    intro hbot
    have hle := p622Klein_card_le_two e hcard hU hbot
    obtain ⟨y, hyU, hzy⟩ := hnc
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hzy (by simp)
    exact hzy (mul_inv_eq_iff_eq_mul.1 (p622Klein_conj_eq hzU hle hyU hy1))
  have hSL : U ⊓ L ≤ L := inf_le_right
  have hS2 : ∀ g ∈ U ⊓ L, ∃ k : ℕ, g ^ 2 ^ k = 1 := fun g hg =>
    hU2 g (Subgroup.mem_inf.1 hg).1
  have hzS : z ∈ normalizer ((U ⊓ L : Subgroup C) : Set C) :=
    p622Klein_normalizer_inf (L := L) hzU
  obtain ⟨hpg, hne'⟩ := p622Klein_props e hSL hS2 hVne
  have hlS := p622Klein_normalizer e hzL hzS
  have hUL : U ≤ L := by
    intro u hu
    have hun := p622Klein_normalizer_inf (L := L) (p622Klein_mem_normalizer hu)
    let κ : ↥L ≃* ↥L :=
      { toFun := fun w => ⟨u * (w : C) * u⁻¹, Subgroup.Normal.conj_mem ‹L.Normal› _ w.2 u⟩
        invFun := fun w => ⟨u⁻¹ * (w : C) * u⁻¹⁻¹, Subgroup.Normal.conj_mem ‹L.Normal› _ w.2 u⁻¹⟩
        left_inv := fun w => Subtype.ext (by
          show u⁻¹ * (u * (w : C) * u⁻¹) * u⁻¹⁻¹ = (w : C)
          group)
        right_inv := fun w => Subtype.ext (by
          show u * (u⁻¹ * (w : C) * u⁻¹⁻¹) * u⁻¹ = (w : C)
          group)
        map_mul' := fun a b => Subtype.ext (by
          show u * ((a : C) * (b : C)) * u⁻¹ = (u * (a : C) * u⁻¹) * (u * (b : C) * u⁻¹)
          group) }
    let φ : MulAut GL32 := e.symm.trans (κ.trans e)
    have hφapp : ∀ h : GL32, φ h = e (κ (e.symm h)) := fun h => rfl
    have hkapp : ∀ w : ↥L, ((κ w : ↥L) : C) = u * (w : C) * u⁻¹ := fun w => rfl
    have hmemφ : ∀ h : GL32, φ h ∈ ((U ⊓ L).subgroupOf L).map e.toMonoidHom ↔
        h ∈ ((U ⊓ L).subgroupOf L).map e.toMonoidHom := by
      intro h
      rw [p622Klein_mem_map e, p622Klein_mem_map e, hφapp, MulEquiv.symm_apply_apply, hkapp]
      exact (mem_normalizer_iff.1 hun _).symm
    have hφS : (((U ⊓ L).subgroupOf L).map e.toMonoidHom).map φ.toMonoidHom =
        ((U ⊓ L).subgroupOf L).map e.toMonoidHom := by
      ext g
      rw [Subgroup.mem_map_equiv (f := φ)]
      have h := hmemφ (φ.symm g)
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    obtain ⟨g, hg⟩ := mem_Inn.1 (mem_Inn_of_map_eq_of_normalized
      (p622Klein_orderOf e hzL hz3) hpg hne' hlS hφS)
    obtain ⟨l1, rfl⟩ : ∃ l1 : ↥L, g = e l1 := ⟨e.symm g, (e.apply_symm_apply g).symm⟩
    have hcj : ∀ w : ↥L, u * (w : C) * u⁻¹ =
        ((l1 : ↥L) : C) * (w : C) * ((l1 : ↥L) : C)⁻¹ := by
      intro w
      have h2 : φ (e w) = MulAut.conj (e l1) (e w) := by rw [hg]
      rw [hφapp, MulEquiv.symm_apply_apply] at h2
      have h1 : e (κ w) = e (l1 * w * l1⁻¹) := by
        rw [h2, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have h3 : κ w = l1 * w * l1⁻¹ := e.injective h1
      have h4 := congrArg Subtype.val h3
      rw [hkapp] at h4
      simpa using h4
    have hc : ((l1 : ↥L) : C)⁻¹ * u ∈ centralizer (L : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhL : h ∈ L := hh
      have hh' : u * h * u⁻¹ = ((l1 : ↥L) : C) * h * ((l1 : ↥L) : C)⁻¹ := hcj ⟨h, hhL⟩
      calc h * (((l1 : ↥L) : C)⁻¹ * u)
          = ((l1 : ↥L) : C)⁻¹ * (((l1 : ↥L) : C) * h * ((l1 : ↥L) : C)⁻¹ * u) := by group
        _ = ((l1 : ↥L) : C)⁻¹ * ((u * h * u⁻¹) * u) := by rw [hh']
        _ = ((l1 : ↥L) : C)⁻¹ * u * h := by group
    have hc' : ((l1 : ↥L) : C)⁻¹ * u ∈ zpowers x := by
      rw [← hcent]
      exact hc
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hc'
    have hu_eq : u = ((l1 : ↥L) : C) * x ^ i := by
      rw [hi]
      group
    have hcomm : Commute ((l1 : ↥L) : C) (x ^ i) :=
      Commute.zpow_right (show Commute ((l1 : ↥L) : C) x from
        Subgroup.mem_center_iff.1 hx ((l1 : ↥L) : C)) i
    have hu2 : u = x ^ i * ((l1 : ↥L) : C) := by
      rw [hu_eq, hcomm.eq]
    obtain ⟨m, hm⟩ := hU2 u hu
    exact p622Klein_mem_of_pow e hx hx3 hcent l1.2 hu2 hm
  have h4S := p622Klein_card_four e hzL hz3 hSL hS2 hVne hzS
  have hUeq : U ⊓ L = U := inf_eq_left.2 hUL
  have h4 : Nat.card U = 4 := by
    rw [← hUeq]
    exact h4S
  haveI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.1 (by rw [h4]; norm_num)
  exact p622Klein_iso h4 (p622Klein_sq hzU hz3 h4 hnc)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
