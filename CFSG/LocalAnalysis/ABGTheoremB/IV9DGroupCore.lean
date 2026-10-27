module

public import CFSG.LocalAnalysis.ABGTheoremB.Facts
public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupCyclingOddControlSupport
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.Wreathed

universe u

section KleinFour

variable {G : Type*} [Group G]

private theorem ii52_isKleinFour_of_mulEquiv {A B : Type*} [Group A] [Group B] [IsKleinFour A]
    (e : A ≃* B) : IsKleinFour B :=
  ⟨by rw [← Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

private theorem ii52_conj_mem {V : Subgroup G} {g v : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) : g * v * g⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp hg v).mp hv

private theorem ii52_conj_ne_one {g v : G} (hv : v ≠ 1) : g * v * g⁻¹ ≠ 1 := by
  intro h
  apply hv
  calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

private theorem ii52_conj_injective {g v w : G} (h : g * v * g⁻¹ = g * w * g⁻¹) : v = w := by
  simpa using h

private theorem ii52_mul_self (V : Subgroup G) [IsKleinFour V] {a : G} (ha : a ∈ V) :
    a * a = 1 := by
  have h := Monoid.pow_exponent_eq_one (⟨a, ha⟩ : V)
  rw [IsKleinFour.exponent_two, pow_two] at h
  exact congrArg Subtype.val h

private theorem ii52_fixedPointFree_of_cube (V : Subgroup G) [IsKleinFour V] {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (h3 : g ^ 3 ∈ Subgroup.centralizer (V : Set G))
    (h1 : g ∉ Subgroup.centralizer (V : Set G)) : ∀ v ∈ V, v ≠ 1 → g * v * g⁻¹ ≠ v := by
  intro a ha ha1 hfix
  apply h1
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  by_contra hne
  have hmove : g * b * g⁻¹ ≠ b := by
    intro h
    apply hne
    calc b * g = (g * b * g⁻¹) * g := by rw [h]
      _ = g * b := by group
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hmove (by group)
  have hba : b ≠ a := by
    rintro rfl
    exact hmove hfix
  obtain ⟨c, hc⟩ : ∃ c, c = g * b * g⁻¹ := ⟨_, rfl⟩
  have hcV : c ∈ V := hc ▸ ii52_conj_mem hg hb
  have hc1 : c ≠ 1 := hc ▸ ii52_conj_ne_one hb1
  have hcb : c ≠ b := hc ▸ hmove
  have hca : c ≠ a := by
    intro h
    apply hba
    apply ii52_conj_injective (g := g)
    rw [← hc, h, hfix]
  have hcab : c = a * b := by
    rcases CFSG.Semidihedral.Local.kleinFour_mem_cases V ha hb ha1 hb1 hba.symm hcV with
      h | h | h | h
    · exact h
    · exact absurd h hca
    · exact absurd h hcb
    · exact absurd h hc1
  have hcomm := Subgroup.mem_centralizer_iff.mp h3 b hb
  have h3b : g ^ 3 * b * (g ^ 3)⁻¹ = b := by
    rw [← hcomm]
    group
  have h3c : g ^ 3 * b * (g ^ 3)⁻¹ = c := by
    calc g ^ 3 * b * (g ^ 3)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := by rw [hc, pow_three]; group
      _ = g * (g * (a * b) * g⁻¹) * g⁻¹ := by rw [hcab]
      _ = g * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g⁻¹ := by group
      _ = g * (a * (a * b)) * g⁻¹ := by rw [hfix, ← hc, hcab]
      _ = g * b * g⁻¹ := by rw [← mul_assoc a a b, ii52_mul_self V ha, one_mul]
      _ = c := hc.symm
  exact hcb (h3c.symm.trans h3b)

private theorem ii52_centralizer_subgroupOf_normal {K : Type*} [Group K] (T : Subgroup K) :
    ((Subgroup.centralizer (T : Set K)).subgroupOf (Subgroup.normalizer (T : Set K))).Normal := by
  rw [← Subgroup.normalizerMonoidHom_ker]
  exact MonoidHom.normal_ker _

private theorem ii52_exists_of_three_dvd_automizerIndex {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} (h : 3 ∣ automizerIndex T) :
    ∃ g ∈ Subgroup.normalizer (T : Set K), g ^ 3 ∈ Subgroup.centralizer (T : Set K) ∧
      g ∉ Subgroup.centralizer (T : Set K) := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have : (Ct.subgroupOf Nt).Normal := ii52_centralizer_subgroupOf_normal T
  have h3 : 3 ∣ Nat.card (Nt ⧸ Ct.subgroupOf Nt) := by
    rw [← Subgroup.index_eq_card]
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, g.2, ?_, ?_⟩
  · have : ((g ^ 3 : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hg
    have : ((g : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)

private theorem ii52_mem_normalizer_subgroupOf_iff {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.normalizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.mem_subgroupOf]

private theorem ii52_mem_centralizer_subgroupOf_iff {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.centralizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.centralizer (T : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTH ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h _ ht)

private theorem ii52_exists_of_three_dvd_automizerIndex_subgroupOf [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (h : 3 ∣ automizerIndex (T.subgroupOf H)) :
    ∃ g ∈ H, g ∈ Subgroup.normalizer (T : Set G) ∧ g ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧
      g ∉ Subgroup.centralizer (T : Set G) := by
  obtain ⟨g, hgN, hg3, hg1⟩ := ii52_exists_of_three_dvd_automizerIndex h
  refine ⟨g, g.2, (ii52_mem_normalizer_subgroupOf_iff hTH).mp hgN, ?_, ?_⟩
  · simpa using (ii52_mem_centralizer_subgroupOf_iff hTH).mp hg3
  · exact fun h' => hg1 ((ii52_mem_centralizer_subgroupOf_iff hTH).mpr h')


end KleinFour

section Wreath

private theorem ii52_half_add_half (k : ℕ) :
    ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by
  have h := (two_smul_eq_zero_iff k ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))).mpr (Or.inr rfl)
  rwa [two_nsmul] at h

private theorem ii52_wreath_commute_outside (k : ℕ) (a : ZMod (2 ^ (k + 1)))
    {y : Wreath (2 ^ (k + 1))} (hy : orderOf y = 2)
    (hc : y * element _ a (-a) 1 = element _ a (-a) 1 * y) :
    y = element _ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 ∨
      y = element _ a (-a) 1 ∨
      y = element _ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 *
        element _ a (-a) 1 := by
  have hhh := ii52_half_add_half k
  have hne := half_residue_ne_zero k
  obtain ⟨⟨c, d, e⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective y
  change orderOf (element _ c d e) = 2 at hy
  change element _ c d e * _ = _ * element _ c d e at hc
  change element _ c d e = _ ∨ element _ c d e = _ ∨ element _ c d e = _
  have hconj : element _ a (-a) 1 * element _ c d e * (element _ a (-a) 1)⁻¹ =
      element _ c d e := by
    rw [← hc]
    group
  rcases swap_exponent_cases e with rfl | rfl
  · rw [conjugate_base_by_swap, element_eq_iff] at hconj
    rcases (element_base_involution_iff k c d).mp hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact absurd hconj.1 (Ne.symm hne)
    · exact absurd hconj.1 hne
  · have hcd : c + d = 0 := (element_swap_involution_iff _ c d).mp hy
    have hd : d = -c := by linear_combination hcd
    subst hd
    rw [conjugate_swap_by_swap, element_eq_iff] at hconj
    have h2 : 2 • (c - a) = 0 := by
      rw [two_nsmul]
      linear_combination -hconj.1
    rcases (two_smul_eq_zero_iff k (c - a)).mp h2 with h | h
    · right; left
      have : c = a := by linear_combination h
      rw [this]
    · right; right
      have hc' : c = a + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by linear_combination h
      rw [element_base_mul, hc']
      simp only [element_eq_iff, and_true]
      constructor
      · ring
      · linear_combination -hhh

private theorem ii52_wreath_commute_x2 (k : ℕ) {y : Wreath (2 ^ (k + 1))} (hy : orderOf y = 2)
    (hc : y * element _ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 =
      element _ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 * y) :
    y = element _ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 ∨
      y = element _ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 ∨
      y = element _ 0 ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 := by
  have hne := half_residue_ne_zero k
  obtain ⟨⟨c, d, e⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective y
  change orderOf (element _ c d e) = 2 at hy
  change element _ c d e * _ = _ * element _ c d e at hc
  change element _ c d e = _ ∨ element _ c d e = _ ∨ element _ c d e = _
  rcases swap_exponent_cases e with rfl | rfl
  · rcases (element_base_involution_iff k c d).mp hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exfalso
    have hconj : element _ c d 1 * element _ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 *
        (element _ c d 1)⁻¹ = element _ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 := by
      rw [hc]
      group
    rw [conjugate_base_by_swap, element_eq_iff] at hconj
    exact hne hconj.1.symm

private theorem ii52_exists_two {W : Type*} [Group W] (V : Subgroup W) [IsKleinFour V] :
    ∃ v₁ ∈ V, ∃ v₂ ∈ V, v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ := by
  have h4 : Nat.card V = 4 := IsKleinFour.card_four
  have hne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h4
    norm_num at h4
  obtain ⟨⟨v₁, hv₁⟩, hv₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hv₁1' : v₁ ≠ 1 := fun h => hv₁1 (Subtype.ext h)
  by_contra hcon
  push Not at hcon
  apply IsKleinFour.not_isCyclic (G := V)
  refine ⟨⟨v₁, hv₁⟩, fun ⟨v₂, hv₂⟩ => ?_⟩
  by_cases h1 : v₂ = 1
  · exact ⟨0, Subtype.ext (by simp [h1])⟩
  · have h2 : v₁ = v₂ := hcon v₁ hv₁ v₂ hv₂ hv₁1' h1
    exact ⟨1, Subtype.ext (by simp [h2])⟩

private theorem ii52_wreath_mem_of_commute (k : ℕ) (V : Subgroup (Wreath (2 ^ (k + 1))))
    [IsKleinFour V] {y : Wreath (2 ^ (k + 1))} (hy : orderOf y = 2)
    (hyV : ∀ v ∈ V, v * y = y * v) : y ∈ V := by
  have hhh := ii52_half_add_half k
  set h : ZMod (2 ^ (k + 1)) := ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) with hh
  obtain ⟨v₁, hv₁, v₂, hv₂, hv₁1, hv₂1, hv₁₂⟩ := ii52_exists_two V
  by_cases hout : ∃ a : ZMod (2 ^ (k + 1)), element _ a (-a) 1 ∈ V
  · obtain ⟨a, ha⟩ := hout
    have hsq : element _ a (-a) 1 * element _ a (-a) 1 = 1 := by
      rw [← pow_two, element_swap_sq, add_neg_cancel, element_zero]
    have hx₁ : element _ h h 0 ∈ V := by
      obtain ⟨w, hw, hw1, hwo⟩ : ∃ w ∈ V, w ≠ 1 ∧ w ≠ element _ a (-a) 1 := by
        by_cases h₁ : v₁ = element _ a (-a) 1
        · exact ⟨v₂, hv₂, hv₂1, fun h₂ => hv₁₂ (h₁.trans h₂.symm)⟩
        · exact ⟨v₁, hv₁, hv₁1, h₁⟩
      rcases ii52_wreath_commute_outside k a (CFSG.Semidihedral.Local.kleinFour_orderOf V hw hw1)
        (CFSG.Semidihedral.Local.kleinFour_mul_comm V hw ha) with h₁ | h₁ | h₁
      · rw [← h₁]
        exact hw
      · exact absurd h₁ hwo
      · have hx := V.mul_mem hw ha
        rwa [h₁, mul_assoc, hsq, mul_one] at hx
    rcases ii52_wreath_commute_outside k a hy (hyV _ ha).symm with h₁ | h₁ | h₁
    · rw [h₁]
      exact hx₁
    · rw [h₁]
      exact ha
    · rw [h₁]
      exact V.mul_mem hx₁ ha
  · push Not at hout
    have hbase : ∀ v ∈ V, v ≠ 1 →
        v = element _ h h 0 ∨ v = element _ h 0 0 ∨ v = element _ 0 h 0 := by
      intro v hv hv1
      have hv2 := CFSG.Semidihedral.Local.kleinFour_orderOf V hv hv1
      obtain ⟨⟨c, d, e⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective v
      change orderOf (element _ c d e) = 2 at hv2
      change element _ c d e ∈ V at hv
      change element _ c d e = _ ∨ element _ c d e = _ ∨ element _ c d e = _
      rcases swap_exponent_cases e with rfl | rfl
      · rcases (element_base_involution_iff k c d).mp hv2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · have hcd : c + d = 0 := (element_swap_involution_iff _ c d).mp hv2
        have hd : d = -c := by linear_combination hcd
        rw [hd] at hv
        exact absurd hv (hout c)
    have hall : element _ h h 0 ∈ V ∧ element _ h 0 0 ∈ V ∧ element _ 0 h 0 ∈ V := by
      have hp := V.mul_mem hv₁ hv₂
      rcases hbase v₁ hv₁ hv₁1 with rfl | rfl | rfl <;>
        rcases hbase v₂ hv₂ hv₂1 with rfl | rfl | rfl <;>
        simp only [element_base_mul, hhh, add_zero, zero_add] at hp
      · exact absurd rfl hv₁₂
      · exact ⟨hv₁, hv₂, hp⟩
      · exact ⟨hv₁, hp, hv₂⟩
      · exact ⟨hv₂, hv₁, hp⟩
      · exact absurd rfl hv₁₂
      · exact ⟨hp, hv₁, hv₂⟩
      · exact ⟨hv₂, hp, hv₁⟩
      · exact ⟨hp, hv₂, hv₁⟩
      · exact absurd rfl hv₁₂
    obtain ⟨hx₁, hx₂, hx₃⟩ := hall
    rcases ii52_wreath_commute_x2 k hy (hyV _ hx₂).symm with h₁ | h₁ | h₁
    · rw [h₁]
      exact hx₁
    · rw [h₁]
      exact hx₂
    · rw [h₁]
      exact hx₃

end Wreath

section Rank

variable {G : Type*} [Group G]

private theorem ii52_mem_of_commute {h : ℕ} (hS : HasQDOrWreathedSylowOfHeight G h)
    (V : Subgroup G) [IsKleinFour V] {y : G} (hy : orderOf y = 2)
    (hyV : ∀ v ∈ V, v * y = y * v) : y ∈ V := by
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [← hyV v hv, mul_inv_cancel_right]
      exact hv
    · intro hv
      have h1 : y * v * y⁻¹ * y = y * (y * v * y⁻¹) := hyV _ hv
      have h2 : y * v = y * (y * v * y⁻¹) := by
        rw [← h1]
        group
      rw [mul_left_cancel h2]
      exact hv
  obtain ⟨S', hS'⟩ := (IsPGroup.to_sup_of_normal_right' hy2 hV2 hyN).exists_le_sylow
  have hVS' : V ≤ (S' : Subgroup G) := le_sup_right.trans hS'
  have hyS' : y ∈ (S' : Subgroup G) := hS' (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
  rcases hS with ⟨-, n, hn, hSD⟩ | ⟨hh2, hW⟩
  · obtain ⟨f⟩ := hSD S'
    obtain ⟨-, -, hC⟩ := CFSG.Semidihedral.Local.kleinFour_sylow_facts hn S' f V hVS'
    exact hC ⟨hyS', Subgroup.mem_centralizer_iff.mpr hyV⟩
  · obtain ⟨e⟩ := hW S'
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    have : IsKleinFour ((V.subgroupOf (S' : Subgroup G)).map e.toMonoidHom) :=
      ii52_isKleinFour_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hVS').symm.trans
        ((V.subgroupOf (S' : Subgroup G)).equivMapOfInjective e.toMonoidHom e.injective))
    have hy' : orderOf (e ⟨y, hyS'⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
    have hyV' : ∀ v ∈ (V.subgroupOf (S' : Subgroup G)).map e.toMonoidHom,
        v * e ⟨y, hyS'⟩ = e ⟨y, hyS'⟩ * v := by
      rintro _ ⟨v, hv, rfl⟩
      change e v * e ⟨y, hyS'⟩ = e ⟨y, hyS'⟩ * e v
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hyV v hv)
    obtain ⟨v, hv, hve⟩ := ii52_wreath_mem_of_commute k _ hy' hyV'
    have hvy : v = ⟨y, hyS'⟩ := e.injective hve
    have hv' : ((v : (S' : Subgroup G)) : G) ∈ V := hv
    rwa [hvy] at hv'

end Rank

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem T_le_pPrimeCoreIn_of_even (hσ : σ.IsValid) (_hII : σ.ChapterIIFacts) {r : ℕ} :
    ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ¬ Odd (Nat.card (pPrimeCoreIn r H)) → σ.T ≤ pPrimeCoreIn r H := by
  intro H hTH hDW hev
  have : IsKleinFour (σ.T.subgroupOf H) := hDW.2.1
  have : IsKleinFour σ.T := ii52_isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTH)
  obtain ⟨g, hgH, hgN, hg3, hg1⟩ := ii52_exists_of_three_dvd_automizerIndex_subgroupOf hTH hDW.2.2
  have hgfree := ii52_fixedPointFree_of_cube σ.T hgN hg3 hg1
  have hMH : H ≤ Subgroup.normalizer ((pPrimeCoreIn r H : Subgroup G) : Set G) :=
    le_normalizer_map_subtype H (CFSG.pPrimeCore r H)
  obtain ⟨b, hbT, hbM, hb1⟩ : ∃ b ∈ σ.T, b ∈ pPrimeCoreIn r H ∧ b ≠ 1 := by
    have heven : 2 ∣ Nat.card (CFSG.pPrimeCore r H) := by
      have h := Nat.not_odd_iff_even.mp hev
      rw [pPrimeCoreIn, Subgroup.card_map_of_injective H.subtype_injective] at h
      exact even_iff_two_dvd.mp h
    have hT2 : IsPGroup 2 (σ.T.subgroupOf H) :=
      IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
    obtain ⟨Q, hTQ⟩ := hT2.exists_le_sylow
    have hne : (CFSG.pPrimeCore r H).subgroupOf (Q : Subgroup H) ≠ ⊥ := by
      intro hbot
      apply not_dvd_relIndex_of_normal Q (CFSG.pPrimeCore r H)
      have hbot' : (Q : Subgroup H).subgroupOf (CFSG.pPrimeCore r H) = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot] at hbot ⊢
        exact hbot.symm
      rw [hbot', Subgroup.index_bot]
      exact heven
    have : Group.IsNilpotent (Q : Subgroup H) := Q.isPGroup'.isNilpotent
    have hnorm : ((CFSG.pPrimeCore r H).subgroupOf (Q : Subgroup H)).Normal :=
      Subgroup.normal_subgroupOf
    have hK := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    have hK2 : IsPGroup 2 ((CFSG.pPrimeCore r H).subgroupOf (Q : Subgroup H) ⊓
        Subgroup.center (Q : Subgroup H) : Subgroup (Q : Subgroup H)) :=
      Q.isPGroup'.to_subgroup _
    have hdvd : 2 ∣ Nat.card ((CFSG.pPrimeCore r H).subgroupOf (Q : Subgroup H) ⊓
        Subgroup.center (Q : Subgroup H) : Subgroup (Q : Subgroup H)) := by
      rcases hK2.card_eq_or_dvd with h1 | h2
      · exact absurd (Subgroup.card_eq_one.mp h1) hK
      · exact h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    obtain ⟨hzB, hzZ⟩ := Subgroup.mem_inf.mp z.2
    have hy2 : orderOf (((z : (Q : Subgroup H)) : H) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    refine ⟨(((z : (Q : Subgroup H)) : H) : G), ?_, ⟨_, Subgroup.mem_subgroupOf.mp hzB, rfl⟩, ?_⟩
    · apply ii52_mem_of_commute hσ.sylow σ.T hy2
      intro v hv
      have hvQ : (⟨v, hTH hv⟩ : H) ∈ (Q : Subgroup H) := hTQ (Subgroup.mem_subgroupOf.mpr hv)
      have h := Subgroup.mem_center_iff.mp hzZ ⟨_, hvQ⟩
      exact congrArg (fun q : (Q : Subgroup H) => ((q : H) : G)) h
    · intro h1
      rw [h1, orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
  intro v hv
  have hb'T := ii52_conj_mem hgN hbT
  have hb'M := ii52_conj_mem (hMH hgH) hbM
  have hb'1 : g * b * g⁻¹ ≠ 1 := ii52_conj_ne_one hb1
  have hbb' : b ≠ g * b * g⁻¹ := fun h => hgfree b hbT hb1 h.symm
  rcases CFSG.Semidihedral.Local.kleinFour_mem_cases σ.T hbT hb'T hb1 hb'1 hbb' hv with
    h | h | h | h
  · rw [h]
    exact Subgroup.mul_mem _ hbM hb'M
  · rw [h]
    exact hbM
  · rw [h]
    exact hb'M
  · rw [h]
    exact Subgroup.one_mem _

end Setting

end CFSG.ABGTheoremB
