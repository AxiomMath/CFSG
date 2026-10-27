module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeCosetPoints
public import CFSG.Walter.Ree.Model.Fusion

public noncomputable section

namespace CFSG.ComponentClassification.LiteratureLocal.SmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model
open scoped MatrixGroups

theorem card_dvd_ncard_of_free {G α : Type*} [Group G] [Finite G] [MulAction G α] :
    ∀ (n : ℕ) (S : Set α), S.ncard = n → S.Finite → (∀ g : G, ∀ x ∈ S, g • x ∈ S) →
      (∀ g : G, ∀ x ∈ S, g • x = x → g = 1) → Nat.card G ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS hinv hfree
    rcases S.eq_empty_or_nonempty with h0 | ⟨x, hx⟩
    · rw [← hn, h0, Set.ncard_empty]
      exact dvd_zero _
    set O : Set α := Set.range fun g : G => g • x with hO
    have hOS : O ⊆ S := by
      rintro _ ⟨g, rfl⟩
      exact hinv g x hx
    have hOinj : Function.Injective fun g : G => g • x := by
      intro g g' h
      have h1 : (g'⁻¹ * g) • x = x := by
        rw [mul_smul]
        simp only at h
        rw [h, inv_smul_smul]
      have := hfree _ x hx h1
      rw [inv_mul_eq_one] at this
      exact this.symm
    have hOcard : O.ncard = Nat.card G := Set.ncard_range_of_injective hOinj
    have hpos : 0 < Nat.card G := Nat.card_pos
    have hle : Nat.card G ≤ n := by
      rw [← hOcard, ← hn]
      exact Set.ncard_le_ncard hOS hS
    have hdiff : (S \ O).ncard = n - Nat.card G := by
      rw [Set.ncard_sdiff hOS (hS.subset hOS), hn, hOcard]
    have hdvd := ih (n - Nat.card G) (by omega) (S \ O) hdiff (hS.subset fun _ h => h.1)
      (fun g y hy => ⟨hinv g y hy.1, fun ⟨g', hg'⟩ => hy.2 ⟨g⁻¹ * g', by
        simp only at hg' ⊢
        rw [mul_smul, hg', inv_smul_smul]⟩⟩)
      (fun g y hy h => hfree g y hy.1 h)
    have : n = (n - Nat.card G) + Nat.card G := by omega
    rw [this]
    exact dvd_add hdvd dvd_rfl

theorem isConj_of_orderOf_eq_two {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : Odd r)
    (hG : Nat.card G = 2 * r) {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card G).factorization 2 = 1 := by
    rw [hG, Nat.factorization_mul (by norm_num) (by rintro rfl; exact (Nat.not_odd_zero hr)),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hr)
        (even_iff_two_dvd.mpr h))]
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hP⟩ := hx2.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hy2.exists_le_sylow
  have hcardP : Nat.card (P : Subgroup G) = 2 := by rw [P.card_eq_multiplicity, hfac, pow_one]
  have hcardQ : Nat.card (Q : Subgroup G) = 2 := by rw [Q.card_eq_multiplicity, hfac, pow_one]
  have hPx : (P : Subgroup G) = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge hP (by rw [hcardP, Nat.card_zpowers, hx])).symm
  have hQy : (Q : Subgroup G) = Subgroup.zpowers y :=
    (Subgroup.eq_of_le_of_card_ge hQ (by rw [hcardQ, Nat.card_zpowers, hy])).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hmem : g * x * g⁻¹ ∈ Subgroup.zpowers y := by
    rw [← hQy, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rw [hPx]
    simp [MulAut.smul_def, MulAut.conj_symm_apply, mul_assoc]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : y ^ k = y ∨ y ^ k = 1 := by
    rw [← zpow_mod_orderOf, hy]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  rcases hk' with h1 | h1
  · rw [h1] at hk
    exact isConj_iff.mpr ⟨g, hk.symm⟩
  · rw [h1] at hk
    exfalso
    have hx1 : x = 1 := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [← hk]; group
    rw [hx1, orderOf_one] at hx
    norm_num at hx

theorem eq_of_cube_add_one_mul_sub_one_eq {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : (x ^ 3 + 1) * (x - 1) = (y ^ 3 + 1) * (y - 1)) : x = y := by
  by_contra hxy
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
  · have h1 : x ^ 3 + 1 < y ^ 3 + 1 := by
      have := Nat.pow_lt_pow_left hlt (by norm_num : (3 : ℕ) ≠ 0)
      omega
    have h2 : x - 1 < y - 1 := by omega
    have := Nat.mul_lt_mul'' h1 h2
    omega
  · have h1 : y ^ 3 + 1 < x ^ 3 + 1 := by
      have := Nat.pow_lt_pow_left hlt (by norm_num : (3 : ℕ) ≠ 0)
      omega
    have h2 : y - 1 < x - 1 := by omega
    have := Nat.mul_lt_mul'' h1 h2
    omega

theorem three_pow_odd_mod_eight (a : ℕ) : 3 ^ (2 * a + 1) % 8 = 3 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem card_torusIn (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card ((ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a)) =
      3 ^ (2 * a + 1) - 1 := by
  have hle : ReeTag.G2.reeFixedTorus K a ≤ ReeTag.G2.reeGamma K a :=
    ReeTag.reeFixedTorus_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  have hbij : Function.Bijective (fun s : Kˣ =>
      (⟨smallReeH a K s, smallReeH_mem hK s⟩ : ReeTag.G2.reeFixedTorus K a)) := by
    refine ⟨fun s s' h => smallReeH_injective (congrArg Subtype.val h), fun g => ?_⟩
    obtain ⟨s, hs⟩ := exists_smallReeH_eq g.2
    exact ⟨s, Subtype.ext hs⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_units, hK]

theorem card_midXIn (hK : Nat.card K = 3 ^ (2 * a + 1)) {t : ReeTag.G2.reeGamma K a}
    (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1)) :
    Nat.card ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) ⊓
      Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) :
        Subgroup (ReeTag.G2.reeGamma K a)) = 3 ^ (2 * a + 1) := by
  set X := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) ⊓
    Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) with hX
  have hmem : ∀ b : K, midIn hK b ∈ X := by
    intro b
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (midIn_mem hK b), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, midIn_val, ht]
    exact (smallReeU_commute_iff (a := a) hK 0 b 0).2 ⟨rfl, rfl⟩
  have hbij : Function.Bijective (fun b : K => (⟨midIn hK b, hmem b⟩ : X)) := by
    refine ⟨fun b b' h => ?_, fun g => ?_⟩
    · have h2 : midIn hK b = midIn hK b' := Subtype.mk.inj h
      have h1 : smallReeU a K 0 b 0 = smallReeU a K 0 b' 0 := by
        rw [← midIn_val hK, ← midIn_val hK, h2]
      exact (smallReeU_inj h1).2.1
    · obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.1 g.2
      obtain ⟨v, b, c, hvbc⟩ := exists_smallReeU_eq hK (Subgroup.mem_subgroupOf.1 hgU)
      have hcomm : smallReeU a K v b c * smallReeH a K (-1) =
          smallReeH a K (-1) * smallReeU a K v b c := by
        have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hgC)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ht, ← hvbc] at h1
        exact h1
      obtain ⟨rfl, rfl⟩ := (smallReeU_commute_iff hK v b c).1 hcomm
      refine ⟨b, Subtype.ext (Subtype.ext ?_)⟩
      change ((midIn hK b : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) = _
      rw [midIn_val]
      exact hvbc
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hK]

theorem sq_eq_one_of_isPGroup_two (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup ReeTag.G2.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)
    {P : Subgroup (ReeTag.G2.reeGamma K a)} (hP : IsPGroup 2 P) {p : ReeTag.G2.reeGamma K a}
    (hp : p ∈ P) : p ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨hE, -, Q, hQ⟩ := smallRee_E8_sylow hK hw₀
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ReeTag.G2.reeGamma K a) R Q
  have hpQ : g * p * g⁻¹ ∈ (Q : Subgroup (ReeTag.G2.reeGamma K a)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_symm_apply, mul_assoc] using hR hp
  rw [hQ] at hpQ
  have h2 := @elemPow_eq_one_of_isElementaryAbelian 2 _ _ _ hE _ hpQ
  have h3 : g * p ^ 2 * g⁻¹ = 1 := by
    rw [← conj_pow]
    exact h2
  calc p ^ 2 = g⁻¹ * (g * p ^ 2 * g⁻¹) * g := by group
    _ = 1 := by rw [h3]; group

section Orbit

variable (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)
  {t : ReeTag.G2.reeGamma K a} (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1))
include hK hw₀ ht

omit hK in
theorem longestIn_mem_centralizer :
    longestIn a K hw₀ ∈ Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ht]
  exact canonicalRep_commute_smallReeH hw₀

omit hw₀ in
theorem torusIn_le_centralizer :
    (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) ≤
      Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) := by
  intro h hh
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ht]
  exact (smallReeH_commute_of_mem hK (Subgroup.mem_subgroupOf.1 hh)).symm

omit hw₀ in
theorem midIn_mem_centralizer (b : K) :
    midIn hK b ∈ Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, midIn_val, ht]
  exact (smallReeU_commute_iff (a := a) hK 0 b 0).2 ⟨rfl, rfl⟩

theorem fixed_subset_orbit {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≤ M) :
    {ω : ReeTag.G2.reeGamma K a ⧸
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) | t • ω = ω} ⊆
      MulAction.orbit M (basePt a K) := by
  intro ω hω
  rcases (torusInv_smul_eq_iff hK hw₀ ht ω).1 hω with rfl | ⟨b, rfl⟩
  · exact MulAction.mem_orbit_self _
  · have hm : midIn hK b * longestIn a K hw₀ ∈ M :=
      hCM (mul_mem (midIn_mem_centralizer hK ht b) (longestIn_mem_centralizer hw₀ ht))
    refine ⟨⟨_, hm⟩, ?_⟩
    change (midIn hK b * longestIn a K hw₀) • basePt a K = midIn hK b • oppPt a K hw₀
    rw [mul_smul, oppPt, basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

end Orbit

theorem isMulCommutative_of_sq_eq_one {G : Type*} [Group G] (h : ∀ g : G, g ^ 2 = 1) :
    IsMulCommutative G := by
  refine isMulCommutative_iff.mpr fun x y => ?_
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, h])
  have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, h])
  have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (by rw [← sq, h])
  calc x * y = (x * y)⁻¹ := hxy.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx, hy]

theorem orbit_size_cases {a q d j k m : ℕ} (ha : 1 ≤ a) (hq : q = 3 ^ (2 * a + 1))
    (hDM : (q - 1) * 3 ^ j * d = m) (hkm : m = q * (q ^ 2 - 1) * k)
    (hmΓ : m ∣ q ^ 3 * (q - 1) * (q ^ 3 + 1)) (hX : q ∣ d - 1) (hH : q - 1 ∣ d - (q + 1))
    (hqd : q + 1 ≤ d) : d = q + 1 ∨ d = q ^ 3 + 1 := by
  have hq27 : 27 ≤ q := by
    rw [hq]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq8 : q % 8 = 3 := hq ▸ three_pow_odd_mod_eight a
  have hq3 : q % 3 = 0 := by rw [hq, pow_succ, Nat.mul_mod_left]
  have hq1 : 0 < q - 1 := by omega
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  have hmain : 3 ^ j * d = q * (q + 1) * k := by
    have h1 : (q - 1) * 3 ^ j * d = q * ((q - 1) * (q + 1)) * k := by rw [hDM, hkm, hsq]
    apply Nat.eq_of_mul_eq_mul_left hq1
    calc (q - 1) * (3 ^ j * d) = (q - 1) * 3 ^ j * d := by ring
      _ = q * ((q - 1) * (q + 1)) * k := h1
      _ = (q - 1) * (q * (q + 1) * k) := by ring
  have hcop3 : Nat.Coprime (q + 1) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  obtain ⟨e, he⟩ : q + 1 ∣ d := by
    have h1 : q + 1 ∣ 3 ^ j * d := ⟨q * k, by rw [hmain]; ring⟩
    exact (Nat.Coprime.pow_right j hcop3).dvd_of_dvd_mul_left h1
  have hek : 3 ^ j * e = q * k := by
    have h1 : 3 ^ j * ((q + 1) * e) = q * (q + 1) * k := by rw [← he]; exact hmain
    apply Nat.eq_of_mul_eq_mul_left (show 0 < q + 1 by omega)
    calc (q + 1) * (3 ^ j * e) = 3 ^ j * ((q + 1) * e) := by ring
      _ = q * (q + 1) * k := h1
      _ = (q + 1) * (q * k) := by ring
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [he, h0, mul_zero] at hqd
      omega
    · exact h0
  set m₀ := (q - 1) / 2 with hm₀
  have hm₀2 : q - 1 = 2 * m₀ := by omega
  have hqe : q ∣ e - 1 := by
    have h1 : d - 1 = q * e + (e - 1) := by
      rw [he]
      have : (q + 1) * e = q * e + e := by ring
      omega
    rw [h1] at hX
    exact (Nat.dvd_add_right (dvd_mul_right q e)).1 hX
  have hq1e : m₀ ∣ e - 1 := by
    have h1 : d - (q + 1) = (q - 1) * (e - 1) + 2 * (e - 1) := by
      rw [he]
      have h2 : (q + 1) * e = (q + 1) * (e - 1) + (q + 1) := by
        have : e = (e - 1) + 1 := by omega
        conv_lhs => rw [this]
        ring
      have h3 : (q + 1) * (e - 1) = (q - 1) * (e - 1) + 2 * (e - 1) := by
        have : q + 1 = (q - 1) + 2 := by omega
        rw [this]
        ring
      omega
    rw [h1] at hH
    have h2 : q - 1 ∣ 2 * (e - 1) := (Nat.dvd_add_right (dvd_mul_right _ _)).1 hH
    rw [hm₀2] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  have hcopq : Nat.Coprime q m₀ := by
    rw [hq]
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    omega
  have hm0e : q * m₀ ∣ e - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopq hqe hq1e
  set N := q * (q - 1) + 1 with hNdef
  have hkN : k ∣ q ^ 2 * N := by
    rw [hkm] at hmΓ
    have h1 : q ^ 3 * (q - 1) * (q ^ 3 + 1) = q * (q ^ 2 - 1) * (q ^ 2 * N) := by
      rw [hsq, hNdef]
      have h2 : 1 ≤ q := by omega
      zify [h2]
      ring
    rw [h1] at hmΓ
    have hpos : 0 < q * (q ^ 2 - 1) := by
      rw [hsq]
      positivity
    exact (Nat.mul_dvd_mul_iff_left hpos).1 hmΓ
  have hcope3 : Nat.Coprime e 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have h4 : 3 ∣ e - 1 := (Nat.dvd_of_mod_eq_zero hq3).trans hqe
    omega
  have hcopeq : Nat.Coprime e q := by
    rw [hq]
    exact Nat.Coprime.pow_right _ hcope3
  have heN : e ∣ N := by
    have h1 : e ∣ q * k := ⟨3 ^ j, by rw [← hek]; ring⟩
    have h2 : e ∣ k := hcopeq.dvd_of_dvd_mul_left h1
    exact (Nat.Coprime.pow_right 2 hcopeq).dvd_of_dvd_mul_left (h2.trans hkN)
  have hecases : e = 1 ∨ e = N := by
    by_cases he1' : e = 1
    · exact Or.inl he1'
    right
    obtain ⟨r, hr⟩ := hm0e
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, mul_zero] at hr
        omega
      · exact h0
    have hbig : q * m₀ + 1 ≤ e := by
      have : q * m₀ ≤ q * m₀ * r := Nat.le_mul_of_pos_right _ hr1
      omega
    obtain ⟨f, hf⟩ := heN
    have hN2 : N = 2 * (q * m₀) + 1 := by
      rw [hNdef, hm₀2]
      ring
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · interval_cases f
      · rw [mul_zero] at hf
        omega
      · rw [mul_one] at hf
        exact hf.symm
    · exfalso
      have : 2 * e ≤ e * f := by
        calc 2 * e = e * 2 := by ring
          _ ≤ e * f := Nat.mul_le_mul_left _ hf2
      omega
  rcases hecases with h | h
  · left
    rw [he, h, mul_one]
  · right
    rw [he, h, hNdef]
    have h2 : 1 ≤ q := by omega
    zify [h2]
    ring

section Overgroups

variable (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)
  {t : ReeTag.G2.reeGamma K a} (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1))

include hK hw₀ ht in
theorem card_centralizer_torusInv :
    Nat.card (Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a))) =
      3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) := by
  have hmap : (Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a))).map
      (ReeTag.G2.reeGamma K a).subtype = smallReeInvCentralizer a K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ht] at h1
      exact h1
    · intro hx
      obtain ⟨hxΓ, hxC⟩ := Subgroup.mem_inf.1 hx
      refine ⟨⟨x, hxΓ⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ht]
      exact Subgroup.mem_centralizer_singleton_iff.1 hxC
  rw [← Subgroup.card_map_of_injective (ReeTag.G2.reeGamma K a).subtype_injective, hmap,
    card_smallReeInvCentralizer hw₀ hK]

include hK ht in
theorem centralizer_torusInv_ne_top :
    Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≠ ⊤ := by
  intro h
  have hu : smallReeU a K 1 0 0 ∈ ReeTag.G2.reeGamma K a :=
    ReeTag.reeFixedPosUnipotent_le_reeGamma (smallReeU_mem hK 1 0 0)
  have hmem : (⟨_, hu⟩ : ReeTag.G2.reeGamma K a) ∈
      Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) := h ▸ Subgroup.mem_top _
  have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hmem)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ht] at h1
  exact one_ne_zero ((smallReeU_commute_iff hK 1 0 0).1 h1).1

theorem card_stabilizer_mul_ncard_orbit (M : Subgroup (ReeTag.G2.reeGamma K a)) :
    Nat.card (MulAction.stabilizer M (basePt a K)) * (MulAction.orbit M (basePt a K)).ncard =
      Nat.card M := by
  rw [← MulAction.index_stabilizer]
  exact Subgroup.card_mul_index _

include hK hw₀ ht in
theorem exists_card_stabilizer_basePt {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≤ M) :
    ∃ j, Nat.card (MulAction.stabilizer M (basePt a K)) = (3 ^ (2 * a + 1) - 1) * 3 ^ j := by
  obtain ⟨-, -, -, -, -, -, -, -, hcardBorel, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  set D := MulAction.stabilizer M (basePt a K) with hDdef
  have hDB : Nat.card D ∣ (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) := by
    have hle : D.map M.subtype ≤
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) := by
      rintro _ ⟨m, hm, rfl⟩
      exact Subgroup.mem_subgroupOf.2 (mem_borel_of_smul_basePt (MulAction.mem_stabilizer_iff.1 hm))
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective M.subtype_injective] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ReeTag.reeFixedBorel_le_reeGamma).toEquiv,
      hcardBorel] at h1
  have hHM : (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) ≤ M :=
    (torusIn_le_centralizer hK ht).trans hCM
  have hHD : 3 ^ (2 * a + 1) - 1 ∣ Nat.card D := by
    have hle : ((ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a)).subgroupOf M ≤
        D := by
      intro h hh
      rw [MulAction.mem_stabilizer_iff]
      exact smul_basePt_of_mem_borel (ReeTag.reeFixedTorus_le_reeFixedBorel
        (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hh)))
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv, card_torusIn hK] at h1
  have hq1 : 0 < 3 ^ (2 * a + 1) - 1 := by
    have : 3 ≤ 3 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 3
    omega
  obtain ⟨r, hr⟩ := hHD
  have hr3 : r ∣ (3 ^ (2 * a + 1)) ^ 3 := by
    rw [hr, mul_comm ((3 ^ (2 * a + 1)) ^ 3)] at hDB
    exact (Nat.mul_dvd_mul_iff_left hq1).1 hDB
  rw [← pow_mul] at hr3
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hr3
  exact ⟨j, hr⟩

include hK hw₀ ht in
theorem dvd_ncard_orbit_sub_one {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≤ M) :
    3 ^ (2 * a + 1) ∣ (MulAction.orbit M (basePt a K)).ncard - 1 := by
  set Δ := MulAction.orbit M (basePt a K) with hΔdef
  have hΔfin : Δ.Finite := Set.toFinite _
  have hξΔ : basePt a K ∈ Δ := MulAction.mem_orbit_self _
  set X := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) ⊓
    Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) with hXdef
  have hXM : X ≤ M := inf_le_right.trans hCM
  have h1 := card_dvd_ncard_of_free (G := X) (Δ.ncard - 1) (Δ \ {basePt a K})
    (Set.ncard_sdiff_singleton_of_mem hξΔ) (hΔfin.subset fun _ h => h.1)
    (fun x ω hω => by
      refine ⟨MulAction.mem_orbit_of_mem_orbit (⟨x, hXM x.2⟩ : M) hω.1, fun h => hω.2 ?_⟩
      have hxB : ((x : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) ∈
          ReeTag.G2.reeFixedBorel K a :=
        ReeTag.reeFixedPosUnipotent_le_reeFixedBorel
          (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1)
      have h2 : (x : ReeTag.G2.reeGamma K a) • ω = basePt a K := h
      calc ω = (x : ReeTag.G2.reeGamma K a)⁻¹ • ((x : ReeTag.G2.reeGamma K a) • ω) := by
            rw [inv_smul_smul]
        _ = (x : ReeTag.G2.reeGamma K a)⁻¹ • basePt a K := by rw [h2]
        _ = basePt a K := smul_basePt_of_mem_borel (inv_mem hxB))
    (fun x ω hω h => by
      by_contra hx1
      exact hω.2 (eq_basePt_of_smul_eq hK hw₀
        (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1)
        (fun h' => hx1 (Subtype.ext h')) h))
  rwa [card_midXIn hK ht] at h1

include hK hw₀ ht in
theorem basePt_oppPt_mem_fixed :
    t • basePt a K = basePt a K ∧ t • oppPt a K hw₀ = oppPt a K hw₀ := by
  refine ⟨(torusInv_smul_eq_iff hK hw₀ ht _).2 (Or.inl rfl),
    (torusInv_smul_eq_iff hK hw₀ ht _).2 (Or.inr ⟨0, ?_⟩)⟩
  rw [show midIn hK (0 : K) = 1 from Subtype.ext smallReeCoord_zero, one_smul]

include hK hw₀ ht in
theorem dvd_ncard_orbit_sub_fixed {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≤ M) :
    3 ^ (2 * a + 1) - 1 ∣ (MulAction.orbit M (basePt a K)).ncard - (3 ^ (2 * a + 1) + 1) := by
  set Δ := MulAction.orbit M (basePt a K) with hΔdef
  have hΔfin : Δ.Finite := Set.toFinite _
  set Fix := {ω : ReeTag.G2.reeGamma K a ⧸
    (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) | t • ω = ω} with hFixdef
  have hFixΔ : Fix ⊆ Δ := fixed_subset_orbit hK hw₀ ht hCM
  have hFixcard : Fix.ncard = 3 ^ (2 * a + 1) + 1 := ncard_fixed_torusInv hK hw₀ ht
  obtain ⟨hξFix, hηFix⟩ := basePt_oppPt_mem_fixed hK hw₀ ht
  have hHM : (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) ≤ M :=
    (torusIn_le_centralizer hK ht).trans hCM
  have h1 := card_dvd_ncard_of_free
    (G := (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a))
    (Δ.ncard - (3 ^ (2 * a + 1) + 1)) (Δ \ Fix)
    (by rw [Set.ncard_sdiff hFixΔ (hΔfin.subset hFixΔ), hFixcard])
    (hΔfin.subset fun _ h => h.1)
    (fun h ω hω => by
      refine ⟨MulAction.mem_orbit_of_mem_orbit (⟨h, hHM h.2⟩ : M) hω.1, fun hfix => hω.2 ?_⟩
      have hht : (h : ReeTag.G2.reeGamma K a) * t = t * h :=
        Subgroup.mem_centralizer_singleton_iff.1 (torusIn_le_centralizer hK ht h.2)
      have h2 : t • ((h : ReeTag.G2.reeGamma K a) • ω) = (h : ReeTag.G2.reeGamma K a) • ω := hfix
      rw [smul_smul, ← hht, mul_smul] at h2
      exact smul_left_cancel _ h2)
    (fun h ω hω hfix => by
      obtain ⟨s, hs⟩ := exists_smallReeH_eq (Subgroup.mem_subgroupOf.1 h.2)
      by_cases hs1 : s = 1
      · apply Subtype.ext
        apply Subtype.ext
        rw [← hs, hs1]
        exact smallReeH_one
      by_cases hs2 : s = -1
      · exfalso
        have hht : (h : ReeTag.G2.reeGamma K a) = t := Subtype.ext (by rw [← hs, hs2, ht])
        apply hω.2
        change t • ω = ω
        rw [← hht]
        exact hfix
      · exfalso
        rcases eq_basePt_or_eq_oppPt_of_torus_smul hK hw₀ hs1 hs2 hs.symm hfix with h0 | h0
        · exact hω.2 (h0 ▸ hξFix)
        · exact hω.2 (h0 ▸ hηFix))
  rwa [card_torusIn hK] at h1

include hK hw₀ ht in
theorem ncard_orbit_cases (ha : 1 ≤ a) {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≤ M) :
    (MulAction.orbit M (basePt a K)).ncard = 3 ^ (2 * a + 1) + 1 ∨
      (MulAction.orbit M (basePt a K)).ncard = (3 ^ (2 * a + 1)) ^ 3 + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hcardΓ, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  obtain ⟨j, hj⟩ := exists_card_stabilizer_basePt hK hw₀ ht hCM
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hCM
  have hMΓ := Subgroup.card_subgroup_dvd_card M
  have hqd : 3 ^ (2 * a + 1) + 1 ≤ (MulAction.orbit M (basePt a K)).ncard := by
    rw [← ncard_fixed_torusInv hK hw₀ ht]
    exact Set.ncard_le_ncard (fixed_subset_orbit hK hw₀ ht hCM) (Set.toFinite _)
  rw [hcardΓ] at hMΓ
  exact orbit_size_cases (m := Nat.card M) (k := k) (j := j) ha rfl
    (by rw [← hj, card_stabilizer_mul_ncard_orbit])
    (by rw [hk, card_centralizer_torusInv hK hw₀ ht]) hMΓ
    (dvd_ncard_orbit_sub_one hK hw₀ ht hCM) (dvd_ncard_orbit_sub_fixed hK hw₀ ht hCM) hqd

end Overgroups

section Cases

variable (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)
  {t : ReeTag.G2.reeGamma K a} (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1))
include hK hw₀ ht

theorem le_centralizer_of_ncard_orbit {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≤ M)
    (hd : (MulAction.orbit M (basePt a K)).ncard = 3 ^ (2 * a + 1) + 1) :
    M ≤ Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) := by
  set Δ := MulAction.orbit M (basePt a K) with hΔdef
  set Fix := {ω : ReeTag.G2.reeGamma K a ⧸
    (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) | t • ω = ω} with hFixdef
  have hFixΔ : Fix ⊆ Δ := fixed_subset_orbit hK hw₀ ht hCM
  have hΔeq : Fix = Δ := Set.eq_of_subset_of_ncard_le hFixΔ
    (by rw [ncard_fixed_torusInv hK hw₀ ht, ← hd]) (Set.toFinite _)
  intro m hm
  have hfix : ∀ ω : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a),
      t • ω = ω → (m * t * m⁻¹) • ω = ω := by
    intro ω hω
    have h1 : m⁻¹ • ω ∈ Δ :=
      MulAction.mem_orbit_of_mem_orbit (⟨m⁻¹, inv_mem hm⟩ : M) (hFixΔ hω)
    rw [← hΔeq] at h1
    have h2 : t • (m⁻¹ • ω) = m⁻¹ • ω := h1
    rw [mul_smul, mul_smul, h2, smul_inv_smul]
  rcases eq_one_or_eq_of_forall_fixed hK hw₀ ht hfix with h | h
  · exfalso
    have h1 : t = 1 := by
      calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
        _ = 1 := by rw [h]; group
    have h2 : (t : ModGL ReeTag.G2.tag K) = 1 := by rw [h1]; rfl
    rw [ht] at h2
    exact smallReeH_neg_one_ne_one h2
  · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc m * t = (m * t * m⁻¹) * m := by group
      _ = t * m := by rw [h]

theorem isConj_of_ncard_orbit {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≤ M)
    (hd : (MulAction.orbit M (basePt a K)).ncard = (3 ^ (2 * a + 1)) ^ 3 + 1) (y : M)
    (hy : orderOf y = 2) :
    IsConj (⟨t, hCM (Subgroup.mem_centralizer_singleton_iff.2 rfl)⟩ : M) y := by
  obtain ⟨-, -, -, -, -, -, -, hcardΩ, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  set Δ := MulAction.orbit M (basePt a K) with hΔdef
  have hΔuniv : Δ = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, hcardΩ, ← hd]
  set tM : M := ⟨t, hCM (Subgroup.mem_centralizer_singleton_iff.2 rfl)⟩ with htMdef
  obtain ⟨htξ, -⟩ := basePt_oppPt_mem_fixed hK hw₀ ht
  have htMD : tM ∈ MulAction.stabilizer M (basePt a K) := MulAction.mem_stabilizer_iff.2 htξ
  obtain ⟨j, hj⟩ := exists_card_stabilizer_basePt hK hw₀ ht hCM
  set q := 3 ^ (2 * a + 1) with hqdef
  have hq8 : q % 8 = 3 := three_pow_odd_mod_eight a
  set m₀ := (q - 1) / 2 with hm₀
  have hm₀2 : q - 1 = 2 * m₀ := by omega
  have hDodd : Odd (m₀ * 3 ^ j) := by
    refine Nat.odd_mul.2 ⟨?_, Odd.pow (by decide)⟩
    rw [Nat.odd_iff]
    omega
  have hD2 : Nat.card (MulAction.stabilizer M (basePt a K)) = 2 * (m₀ * 3 ^ j) := by
    rw [hj, hm₀2]
    ring
  obtain ⟨-, -, -, -, -, hfus⟩ := small_Ree_prime_field_involution_fusion a K hK w₀ hw₀
  have hy' : orderOf ((y : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  obtain ⟨g, hgΓ, hg⟩ := hfus _ (y : ReeTag.G2.reeGamma K a).2 hy'
  set g' : ReeTag.G2.reeGamma K a := ⟨g, hgΓ⟩ with hg'def
  have hg' : g' * (y : ReeTag.G2.reeGamma K a) * g'⁻¹ = t := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht]
    exact hg)
  have hω : (y : ReeTag.G2.reeGamma K a) • (g'⁻¹ • basePt a K) = g'⁻¹ • basePt a K := by
    have e : (y : ReeTag.G2.reeGamma K a) = g'⁻¹ * t * g' := by rw [← hg']; group
    rw [e, mul_smul, mul_smul, smul_inv_smul, htξ]
  have hωΔ : g'⁻¹ • basePt a K ∈ Δ := hΔuniv ▸ Set.mem_univ _
  obtain ⟨m, hm0⟩ := hωΔ
  have hm : m • basePt a K = g'⁻¹ • basePt a K := hm0
  have hyD : m⁻¹ * y * m ∈ MulAction.stabilizer M (basePt a K) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hm]
    change (m⁻¹ : M) • ((y : ReeTag.G2.reeGamma K a) • (g'⁻¹ • basePt a K)) = basePt a K
    rw [hω, ← hm, inv_smul_smul]
  have hyo : orderOf (m⁻¹ * y * m) = 2 := by
    have hsc : SemiconjBy m⁻¹ y (m⁻¹ * y * m) := by
      simp only [SemiconjBy]
      group
    rw [← SemiconjBy.orderOf_eq m⁻¹ hsc, hy]
  have hto : orderOf tM = 2 := by
    rw [htMdef, Subgroup.orderOf_mk]
    have h1 : orderOf (t : ModGL ReeTag.G2.tag K) = 2 := by
      rw [ht]
      exact (Subgroup.orderOf_mk _ _).symm.trans (orderOf_smallReeH_neg_one hK)
    rwa [Subgroup.orderOf_coe] at h1
  have hc := isConj_of_orderOf_eq_two hDodd hD2 (x := ⟨tM, htMD⟩) (y := ⟨m⁻¹ * y * m, hyD⟩)
    (by rw [Subgroup.orderOf_mk]; exact hto) (by rw [Subgroup.orderOf_mk]; exact hyo)
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hc' := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc'
  refine isConj_iff.mpr ⟨m * c, ?_⟩
  calc m * c * tM * (m * c)⁻¹ = m * ((c : M) * tM * (c : M)⁻¹) * m⁻¹ := by group
    _ = m * (m⁻¹ * y * m) * m⁻¹ := by rw [hc']
    _ = y := by group

end Cases

section Final

variable (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)
  {t : ReeTag.G2.reeGamma K a} (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1))

include hK hw₀ ht in
theorem index_ne_two_of_isConj {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a)) ≤ M)
    (hconj : ∀ y : M, orderOf y = 2 →
      IsConj (⟨t, hCM (Subgroup.mem_centralizer_singleton_iff.2 rfl)⟩ : M) y)
    (N : Subgroup M) : N.index ≠ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tM : M := ⟨t, hCM (Subgroup.mem_centralizer_singleton_iff.2 rfl)⟩ with htMdef
  intro hN
  have hNn : N.Normal := Subgroup.normal_of_index_eq_two hN
  have hNM : Nat.card N * 2 = Nat.card M := by rw [← hN]; exact N.card_mul_index
  have h8C : 8 ∣ Nat.card (Subgroup.centralizer ({t} : Set (ReeTag.G2.reeGamma K a))) := by
    rw [card_centralizer_torusInv hK hw₀ ht]
    refine Dvd.dvd.mul_left ?_ _
    have h1 : ((3 ^ (2 * a + 1)) ^ 2) % 8 = 1 := by
      rw [Nat.pow_mod, three_pow_odd_mod_eight a]
    have h2 : 1 ≤ (3 ^ (2 * a + 1)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  have h8M : 8 ∣ Nat.card M := h8C.trans (Subgroup.card_dvd_of_le hCM)
  have h2N : 2 ∣ Nat.card N := by omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2N
  have hzM : orderOf (z : M) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have htN : tM ∈ N := by
    obtain ⟨c, hc⟩ := isConj_iff.mp (hconj _ hzM)
    have h1 : tM = c⁻¹ * (z : M) * c⁻¹⁻¹ := by rw [← hc]; group
    rw [h1]
    exact hNn.conj_mem _ z.2 c⁻¹
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := inferInstance
  have hPN : ¬ (P : Subgroup M) ≤ N := by
    intro hle
    have h1 := Subgroup.card_dvd_of_le hle
    rw [P.card_eq_multiplicity] at h1
    have h3 : 2 ^ ((Nat.card M).factorization 2 + 1) ∣ Nat.card M := by
      rw [pow_succ]
      calc 2 ^ (Nat.card M).factorization 2 * 2 ∣ Nat.card N * 2 := Nat.mul_dvd_mul_right h1 2
        _ = Nat.card M := hNM
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_two h3
  obtain ⟨p, hpP, hpN⟩ := Set.not_subset.mp hPN
  have hp2 : p ^ 2 = 1 := by
    have hPΓ : IsPGroup 2 ((P : Subgroup M).map M.subtype) := P.isPGroup'.map _
    have h1 := sq_eq_one_of_isPGroup_two hK hw₀ hPΓ ⟨p, hpP, rfl⟩
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h1)
  have hp1 : p ≠ 1 := fun h => hpN (h ▸ N.one_mem)
  have hpo : orderOf p = 2 := orderOf_eq_prime hp2 hp1
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj p hpo)
  exact hpN (hc ▸ hNn.conj_mem tM htN c)

end Final

theorem eq_top_of_ncard_orbit (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    {M : Subgroup (ReeTag.G2.reeGamma K a)}
    (hCM : Subgroup.centralizer ({(smallReeJTHyp ha hK).t} : Set (ReeTag.G2.reeGamma K a)) ≤ M)
    (hd : (MulAction.orbit M (basePt a K)).ncard = (3 ^ (2 * a + 1)) ^ 3 + 1) : M = ⊤ := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  set J := smallReeJTHyp ha hK with hJ
  have ht : (J.t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1) := rfl
  set tM : M := ⟨J.t, hCM (Subgroup.mem_centralizer_singleton_iff.2 rfl)⟩ with htMdef
  have hconj := isConj_of_ncard_orbit hK hw₀ ht hCM hd
  have hidx := index_ne_two_of_isConj hK hw₀ ht hCM hconj
  have hFM : J.F ≤ M := J.le_centralizer.trans hCM
  have habel : CFSG.Walter.HasAbelianSylowTwo M := by
    intro P
    apply isMulCommutative_of_sq_eq_one
    intro x
    have hPΓ : IsPGroup 2 ((P : Subgroup M).map M.subtype) := P.isPGroup'.map _
    have h1 := sq_eq_one_of_isPGroup_two hK hw₀ hPΓ ⟨(x : M), x.2, rfl⟩
    exact Subtype.ext (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, OneMemClass.coe_one, OneMemClass.coe_one]
      exact h1))
  have hcentM : Subgroup.centralizer ({tM} : Set M) = Subgroup.zpowers tM ⊔ J.F.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hFM]
    change _ = Subgroup.zpowers J.t ⊔ J.F
    rw [← J.centralizer_eq]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy))
    · intro hx
      refine ⟨⟨x, hCM hx⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.1 hx
  let JM : CFSG.Walter.JT.JTHyp M :=
    { p := 3
      f := 2 * a + 1
      five_lt := J.five_lt
      abelian_sylow := habel
      index_ne_two := hidx
      t := tM
      orderOf_t := by rw [htMdef, Subgroup.orderOf_mk]; exact J.orderOf_t
      F := J.F.subgroupOf M
      le_centralizer := by
        intro x hx
        refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
        exact Subgroup.mem_centralizer_singleton_iff.1
          (J.le_centralizer (Subgroup.mem_subgroupOf.1 hx))
      t_not_mem := fun h => J.t_not_mem (Subgroup.mem_subgroupOf.1 h)
      centralizer_eq := hcentM
      iso := (Subgroup.subgroupOfEquivOfLe hFM).trans J.iso }
  obtain ⟨-, -, -, -, ⟨hR⟩⟩ := JM.jt_theoremA_of_ne_two (show (3 : ℕ) ≠ 2 by decide)
  obtain ⟨⟨k', hk'1, hq'⟩, hcardM⟩ := CFSG.Walter.Ward.ward_order hR
  obtain ⟨-, -, -, -, -, -, -, -, -, hcardΓ, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  obtain ⟨j, hj⟩ := exists_card_stabilizer_basePt hK hw₀ ht hCM
  have hM1 : Nat.card M = (3 ^ (2 * a + 1)) ^ 3 * 0 + ((3 ^ (2 * a + 1)) ^ 3 + 1) *
      (3 ^ (2 * a + 1) - 1) * 3 ^ j := by
    rw [← card_stabilizer_mul_ncard_orbit M, hj, hd]
    ring
  set q := 3 ^ (2 * a + 1) with hqdef
  set q' := hR.q with hq'def
  have hq27 : 27 ≤ q := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq'3 : 3 ≤ q' := by rw [hq']; exact Nat.le_self_pow (by omega) 3
  have hq3 : q % 3 = 0 := by rw [hqdef, pow_succ, Nat.mul_mod_left]
  have hq'm : q' % 3 = 0 := by rw [hq', pow_succ, Nat.mul_mod_left]
  have hA : Nat.Coprime ((q ^ 3 + 1) * (q - 1)) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
    · have : (q ^ 3) % 3 = 0 := by rw [Nat.pow_mod, hq3]
      omega
    · omega
  have hA' : Nat.Coprime ((q' ^ 3 + 1) * (q' - 1)) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
    · have : (q' ^ 3) % 3 = 0 := by rw [Nat.pow_mod, hq'm]
      omega
    · omega
  have heq : (q ^ 3 + 1) * (q - 1) * 3 ^ j = q' ^ 3 * ((q' ^ 3 + 1) * (q' - 1)) := by
    rw [← mul_assoc, ← hcardM, hM1]
    ring
  have hAA : (q ^ 3 + 1) * (q - 1) = (q' ^ 3 + 1) * (q' - 1) := by
    apply Nat.dvd_antisymm
    · have h1 : (q ^ 3 + 1) * (q - 1) ∣ q' ^ 3 * ((q' ^ 3 + 1) * (q' - 1)) :=
        ⟨3 ^ j, heq.symm⟩
      have h2 : Nat.Coprime ((q ^ 3 + 1) * (q - 1)) (q' ^ 3) := by
        have h3 : Nat.Coprime ((q ^ 3 + 1) * (q - 1)) q' := by
          rw [hq']
          exact Nat.Coprime.pow_right _ hA
        exact Nat.Coprime.pow_right 3 h3
      exact h2.dvd_of_dvd_mul_left h1
    · have h1 : (q' ^ 3 + 1) * (q' - 1) ∣ 3 ^ j * ((q ^ 3 + 1) * (q - 1)) :=
        ⟨q' ^ 3, by rw [mul_comm (3 ^ j), heq]; ring⟩
      exact (Nat.Coprime.pow_right j hA').dvd_of_dvd_mul_left h1
  have hqq : q = q' := eq_of_cube_add_one_mul_sub_one_eq (by omega) (by omega) hAA
  have h3j : 3 ^ j = q ^ 3 := by
    have hApos : 0 < (q ^ 3 + 1) * (q - 1) := Nat.mul_pos (by positivity) (by omega)
    rw [← hqq] at heq
    apply Nat.eq_of_mul_eq_mul_left hApos
    calc (q ^ 3 + 1) * (q - 1) * 3 ^ j = q ^ 3 * ((q ^ 3 + 1) * (q - 1)) := heq
      _ = (q ^ 3 + 1) * (q - 1) * q ^ 3 := by ring
  rw [← Subgroup.card_eq_iff_eq_top, hM1, h3j, hcardΓ]
  ring

theorem centralizer_torusInv_isCoatom (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    IsCoatom (Subgroup.centralizer
      ({(smallReeJTHyp ha hK).t} : Set (ReeTag.G2.reeGamma K a))) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have ht : ((smallReeJTHyp ha hK).t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1) := rfl
  refine ⟨centralizer_torusInv_ne_top hK ht, fun M hCM => ?_⟩
  rcases ncard_orbit_cases hK hw₀ ht ha hCM.le with hd | hd
  · exact absurd (le_centralizer_of_ncard_orbit hK hw₀ ht hCM.le hd) hCM.not_ge
  · exact eq_top_of_ncard_orbit ha hK hCM.le hd

end CFSG.ComponentClassification.LiteratureLocal.SmallRee
