module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSetup
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup CFSG.GorensteinWalter

section SimpleEight

variable {G : Type} [Group G] [Finite G]

theorem exists_fourGroup_le_sylow (hrank : pRank 2 G = 2) (P : Sylow 2 G) :
    ∃ E : Subgroup G, E ≤ (P : Subgroup G) ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, -, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup G)
  rw [← SectionRank.pRank_eq_open_pRank_top, hrank] at hcard
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 2) hcard
  obtain ⟨Q, hQ⟩ := hE2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_, SectionRank.isElemAbelian_map hE _, ?_⟩
  · rw [← hg, Sylow.coe_subgroup_smul, pointwise_smul_def]
    exact map_mono hQ
  · rw [card_map_of_injective (MulAut.conj g).injective, hcard]
    norm_num

theorem not_elemAbelian_eight (hrank : pRank 2 G = 2) (E : Subgroup G)
    (hE : Open.IsElemAbelian 2 E) (hcard : Nat.card E = 8) : False := by
  have h := SectionRank.le_pRank (p := 2) (by norm_num) (le_top : E ≤ ⊤) hE
    (k := 3) (by rw [hcard]; norm_num)
  rw [← SectionRank.pRank_eq_open_pRank_top, hrank] at h
  omega

end SimpleEight

section AbelianEight

variable {G : Type} [Group G]

theorem commute_of_odd_of_sq_commute [Finite G] {g u : G} (hg : Odd (orderOf g))
    (h : Commute (g ^ 2) u) : Commute g u := by
  obtain ⟨k, hk⟩ := hg
  have hgk : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, ← hk, pow_orderOf_eq_one,
      one_mul]
  rw [hgk]
  exact h.pow_left _

theorem commute_of_odd_of_fourTwo {P : Subgroup G} (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {x y : G} (hxP : x ∈ P) (hx4 : orderOf x = 4) (hyP : y ∈ P) (hy2 : orderOf y = 2)
    (hyx : y ∉ zpowers x) (hidx : (zpowers x).relIndex P = 2) [Finite G] {g : G}
    (hg : g ∈ normalizer (P : Set G)) (hodd : Odd (orderOf g)) : ∀ u ∈ P, g * u = u * g := by
  have hxle : zpowers x ≤ P := zpowers_le.mpr hxP
  have hcoset : ∀ u ∈ P, u ∈ zpowers x ∨ u * y⁻¹ ∈ zpowers x := by
    intro u hu
    by_cases h1 : u ∈ zpowers x
    · exact Or.inl h1
    · right
      have key := (Subgroup.mul_mem_iff_of_index_two (H := (zpowers x).subgroupOf P) hidx
        (a := (⟨u, hu⟩ : P)) (b := (⟨y, hyP⟩ : P)⁻¹)).2 (by
          rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          exact iff_of_false h1 hyx)
      exact Subgroup.mem_subgroupOf.1 key
  set z := x ^ 2 with hz
  have hx2 : x ^ 4 = 1 := by rw [← hx4, pow_orderOf_eq_one]
  have hy2' : y ^ 2 = 1 := by rw [← hy2, pow_orderOf_eq_one]
  have hz2 : z ^ 2 = 1 := by rw [hz, ← pow_mul]; exact hx2
  have hsqx : ∀ v ∈ zpowers x, v ^ 2 = 1 ∨ v ^ 2 = z := by
    intro v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
    rcases Int.even_or_odd' i with ⟨m, rfl | rfl⟩
    · left
      rw [← zpow_natCast, ← zpow_mul, show (2 * m : ℤ) * ((2 : ℕ) : ℤ) = 4 * m by push_cast; ring,
        zpow_mul, show x ^ (4 : ℤ) = 1 by exact_mod_cast hx2, one_zpow]
    · right
      rw [← zpow_natCast, ← zpow_mul, show (2 * m + 1 : ℤ) * ((2 : ℕ) : ℤ) = 4 * m + 2 by
        push_cast; ring, zpow_add, zpow_mul, show x ^ (4 : ℤ) = 1 by exact_mod_cast hx2,
        one_zpow, one_mul, hz]
      exact_mod_cast rfl
  have hzne : z ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hx4] at this
    norm_num at this
  have hzx : z ∈ zpowers x := pow_mem (mem_zpowers x) 2
  have hsq : ∀ u ∈ P, u ^ 2 = 1 ∨ u ^ 2 = z := by
    intro u hu
    rcases hcoset u hu with h1 | h1
    · exact hsqx u h1
    · have hvy : u = u * y⁻¹ * y := by group
      have hcomm : Commute (u * y⁻¹) y :=
        hPc _ (P.mul_mem hu (P.inv_mem hyP)) _ hyP
      rw [hvy, hcomm.mul_pow, hy2', mul_one]
      exact hsqx _ h1
  have hinvx : ∀ v ∈ zpowers x, v ^ 2 = 1 → v = 1 ∨ v = z := by
    intro v hv hv2
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
    rw [← zpow_mod_orderOf, hx4] at hv2 ⊢
    have h0 : 0 ≤ i % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h4 : i % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r : ℕ, i % ((4 : ℕ) : ℤ) = r := ⟨(i % ((4 : ℕ) : ℤ)).toNat, by omega⟩
    rw [hr] at hv2 ⊢
    have hr4 : r < 4 := by omega
    rw [zpow_natCast] at hv2 ⊢
    interval_cases r
    · exact Or.inl (pow_zero x)
    · exfalso
      exact hzne (by rw [hz]; simpa using hv2)
    · exact Or.inr rfl
    · exfalso
      apply hzne
      have h6 : x ^ 6 = 1 := by rw [← pow_mul] at hv2; exact hv2
      rw [hz, show x ^ 2 = x ^ 6 * (x ^ 4)⁻¹ by
        rw [show x ^ 6 = x ^ 2 * x ^ 4 by rw [← pow_add]]; group, h6, hx2]
      group
  have hinv : ∀ u ∈ P, u ^ 2 = 1 → u = 1 ∨ u = z ∨ u = y ∨ u = z * y := by
    intro u hu hu2
    rcases hcoset u hu with h1 | h1
    · rcases hinvx u h1 hu2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · have hcomm : Commute (u * y⁻¹) y :=
        hPc _ (P.mul_mem hu (P.inv_mem hyP)) _ hyP
      have hv2 : (u * y⁻¹) ^ 2 = 1 := by
        have : u ^ 2 = (u * y⁻¹) ^ 2 * y ^ 2 := by
          rw [← hcomm.mul_pow]; group
        rw [hu2, hy2', mul_one] at this
        exact this.symm
      rcases hinvx _ h1 hv2 with h2 | h2
      · right; right; left
        calc u = u * y⁻¹ * y := by group
          _ = y := by rw [h2, one_mul]
      · right; right; right
        calc u = u * y⁻¹ * y := by group
          _ = z * y := by rw [h2]
  have hcP : ∀ u ∈ P, g * u * g⁻¹ ∈ P := fun u hu => (mem_normalizer_iff.mp hg u).mp hu
  have hcmul : ∀ a b : G, g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by
    intro a b; group
  have hcpow : ∀ (a : G) (n : ℕ), g * a ^ n * g⁻¹ = (g * a * g⁻¹) ^ n := by
    intro a n; rw [conj_pow]
  have hcinj : ∀ a b : G, g * a * g⁻¹ = g * b * g⁻¹ → a = b := by
    intro a b h; simpa using h
  have hcz : g * z * g⁻¹ = z := by
    have hcx2 : (g * x * g⁻¹) ^ 2 = g * z * g⁻¹ := by rw [hz, hcpow]
    rcases hsq _ (hcP x hxP) with h1 | h1
    · exfalso
      rw [hcx2] at h1
      exact hzne (hcinj z 1 (by rw [h1]; group))
    · rw [← hcx2, h1]
  have hcy : g * y * g⁻¹ = y ∨ g * y * g⁻¹ = z * y := by
    have h2 : (g * y * g⁻¹) ^ 2 = 1 := by rw [← hcpow, hy2']; group
    rcases hinv _ (hcP y hyP) h2 with h1 | h1 | h1 | h1
    · exfalso
      have : y = 1 := hcinj y 1 (by rw [h1]; group)
      rw [this, orderOf_one] at hy2
      norm_num at hy2
    · exfalso
      have : y = z := hcinj y z (by rw [h1, hcz])
      exact hyx (this ▸ hzx)
    · exact Or.inl h1
    · exact Or.inr h1
  have hgy : Commute g y := by
    apply commute_of_odd_of_sq_commute hodd
    have h1 : g ^ 2 * y * (g ^ 2)⁻¹ = y := by
      rw [sq, show g * g * y * (g * g)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ by group]
      rcases hcy with h | h
      · rw [h, h]
      · rw [h, hcmul, hcz, h, ← mul_assoc, ← sq, hz2, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  have hcy' : g * y * g⁻¹ = y := by rw [hgy.eq, mul_inv_cancel_right]
  have hcfix : ∀ w ∈ P, w ^ 2 = 1 → g * w * g⁻¹ = w := by
    intro w hw hw2
    rcases hinv w hw hw2 with rfl | rfl | rfl | rfl
    · group
    · exact hcz
    · exact hcy'
    · rw [hcmul, hcz, hcy']
  have hgx : Commute g x := by
    apply commute_of_odd_of_sq_commute hodd
    set w := x⁻¹ * (g * x * g⁻¹) with hw
    have hwP : w ∈ P := P.mul_mem (P.inv_mem hxP) (hcP x hxP)
    have hcomm : Commute x⁻¹ (g * x * g⁻¹) := hPc _ (P.inv_mem hxP) _ (hcP x hxP)
    have hw2 : w ^ 2 = 1 := by
      have hcx2 : (g * x * g⁻¹) ^ 2 = z := by
        rw [← hcpow, ← hz, hcz]
      rw [hw, hcomm.mul_pow, hcx2, hz, inv_pow, inv_mul_cancel]
    have hcx : g * x * g⁻¹ = x * w := by rw [hw]; group
    have h1 : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
      rw [sq, show g * g * x * (g * g)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ by group, hcx, hcmul, hcx,
        hcfix w hwP hw2, mul_assoc, ← sq, hw2, mul_one]
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  intro u hu
  rcases hcoset u hu with h1 | h1
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp h1
    exact (hgx.zpow_right i).eq
  · have hu' : u = u * y⁻¹ * y := by group
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h1
    rw [hu', ← hi]
    exact ((hgx.zpow_right i).mul_right hgy).eq

theorem normalizer_le_centralizer_of_odd [Finite G] (P : Sylow 2 G)
    (hPc : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a)
    (hodd : ∀ g ∈ normalizer (P : Set G), Odd (orderOf g) →
      ∀ u ∈ (P : Subgroup G), g * u = u * g) :
    normalizer (P : Set G) ≤ centralizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  rw [mem_centralizer_iff]
  intro u hu
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hm0 : m ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hm) (by norm_num)
  have hord1 : orderOf (g ^ m) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hm0 (by rw [hord]; exact dvd_mul_left m _), hord,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have h2 : g ^ m ∈ (P : Subgroup G) := by
    have hp : IsPGroup 2 (zpowers (g ^ m)) :=
      IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hord1])
    have hmem : g ^ m ∈ zpowers (g ^ m) ⊓ normalizer (P : Set G) :=
      ⟨mem_zpowers _, pow_mem hg m⟩
    rw [hp.inf_normalizer_sylow P] at hmem
    exact hmem.2
  have hord2 : orderOf (g ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hord]; exact dvd_mul_right _ m),
      hord, Nat.mul_div_cancel_left _ (Nat.two_pow_pos a)]
  have hc1 : Commute (g ^ m) u := (hPc _ h2 u hu)
  have hc2 : Commute (g ^ 2 ^ a) u :=
    hodd _ (pow_mem hg _) (by rw [hord2]; exact hm) u hu
  have hcop : Nat.gcd (2 ^ a) m = 1 :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ a) m
  rw [hcop, Nat.cast_one] at hbez
  have hg' : g = (g ^ 2 ^ a) ^ (Nat.gcdA (2 ^ a) m) * (g ^ m) ^ (Nat.gcdB (2 ^ a) m) := by
    rw [← zpow_natCast, ← zpow_natCast (g) m, ← zpow_mul, ← zpow_mul, ← zpow_add]
    conv_lhs => rw [← zpow_one g]
    congr 1
  rw [hg']
  exact ((hc2.zpow_left _).mul_left (hc1.zpow_left _)).eq.symm

end AbelianEight

section Dihedral

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mul_inv_mem_of_index_two {P U : Subgroup G} (hU : U.relIndex P = 2) {a b : G}
    (haP : a ∈ P) (hbP : b ∈ P) (haU : a ∉ U) (hbU : b ∉ U) : a * b⁻¹ ∈ U := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf P) hU
    (a := (⟨a, haP⟩ : P)) (b := (⟨b, hbP⟩ : P)⁻¹)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haU hbU)
  exact Subgroup.mem_subgroupOf.1 key

omit [Finite G] in
private theorem eq_or_eq_inv_of_orderOf_four {x u : G} (hx4 : orderOf x = 4)
    (hu : u ∈ zpowers x) (hu4 : orderOf u = 4) : u = x ∨ u = x⁻¹ := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  rw [← zpow_mod_orderOf, hx4] at hu4 ⊢
  have h0 : 0 ≤ i % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h4 : i % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, i % ((4 : ℕ) : ℤ) = r := ⟨(i % ((4 : ℕ) : ℤ)).toNat, by omega⟩
  rw [hr] at hu4 ⊢
  have hr4 : r < 4 := by omega
  rw [zpow_natCast] at hu4 ⊢
  have hx4' : x ^ 4 = 1 := by rw [← hx4, pow_orderOf_eq_one]
  interval_cases r
  · rw [pow_zero, orderOf_one] at hu4; norm_num at hu4
  · exact Or.inl (pow_one x)
  · exfalso
    have h2 : (x ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hx4'
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hu4] at this
    norm_num at this
  · right
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx4']

theorem sylow_mulEquiv_dihedral_of_simple [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : pRank 2 G = 2) (P : Sylow 2 G)
    (hP8 : Nat.card (P : Subgroup G) = 8) :
    Nonempty ((P : Subgroup G) ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEP, hE, hE4⟩ := exists_fourGroup_le_sylow hrank P
  obtain ⟨x, hxP, hx2⟩ : ∃ x ∈ (P : Subgroup G), x ^ 2 ≠ 1 := by
    by_contra h
    push Not at h
    refine not_elemAbelian_eight hrank (P : Subgroup G) ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, h⟩ hP8
    have ha := h a a.2
    have hb := h b b.2
    have hab := h _ (P.mul_mem a.2 b.2)
    have hainv : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha)
    have hbinv : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb)
    have habinv : ((a : G) * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hab)
    simp only [coe_mul]
    rw [← habinv, mul_inv_rev, hainv, hbinv]
  have hxdvd : orderOf x ∣ 8 := by rw [← hP8]; exact Subgroup.orderOf_dvd_natCard _ hxP
  have hx48 : orderOf x = 4 ∨ orderOf x = 8 := by
    have h1 : orderOf x ≠ 1 := by
      intro h; rw [orderOf_eq_one_iff] at h; rw [h, one_pow] at hx2; exact hx2 rfl
    have h2 : orderOf x ≠ 2 := by
      intro h; rw [← h, pow_orderOf_eq_one] at hx2; exact hx2 rfl
    have : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hxdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hEnc : ∀ u ∈ E, orderOf u ≠ 4 := by
    intro u hu h4
    have := hE.2 u hu
    have h := orderOf_dvd_of_pow_eq_one this
    rw [h4] at h
    norm_num at h
  have hxord : orderOf x = 4 := by
    rcases hx48 with h | h
    · exact h
    · exfalso
      have hPx : zpowers x = (P : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxP)
        rw [hP8, Nat.card_zpowers, h]
      have hEc : IsCyclic E := by
        have : IsCyclic (zpowers x) := inferInstance
        have hEx : E ≤ zpowers x := hPx ▸ hEP
        exact Subgroup.isCyclic_of_le hEx
      obtain ⟨⟨g, hgE⟩, hg⟩ := hEc.exists_generator
      have hgo : orderOf g = 4 := by
        have : zpowers (⟨g, hgE⟩ : E) = ⊤ := by
          rw [eq_top_iff]; intro w _; exact hg w
        rw [← Subgroup.orderOf_mk g hgE, ← Nat.card_zpowers, this, card_top, hE4]
      exact hEnc g hgE hgo
  have hxle : zpowers x ≤ (P : Subgroup G) := zpowers_le.mpr hxP
  have hidx : (zpowers x).relIndex (P : Subgroup G) = 2 := by
    have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (zpowers x) (P : Subgroup G)
      bot_le hxle
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Nat.card_zpowers, hxord,
      hP8] at h
    omega
  obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ zpowers x := by
    by_contra h
    push Not at h
    have hEx : E = zpowers x :=
      Subgroup.eq_of_le_of_card_ge h (by rw [hE4, Nat.card_zpowers, hxord])
    exact hEnc x (hEx ▸ mem_zpowers x) hxord
  have hyP : y ∈ (P : Subgroup G) := hEP hyE
  have hy2 : orderOf y = 2 := by
    apply orderOf_eq_prime (hE.2 y hyE)
    rintro rfl
    exact hyx (one_mem _)
  have hcoset : ∀ u ∈ (P : Subgroup G), u ∈ zpowers x ∨ u * y⁻¹ ∈ zpowers x := by
    intro u hu
    by_cases h1 : u ∈ zpowers x
    · exact Or.inl h1
    · exact Or.inr (mul_inv_mem_of_index_two hidx hu hyP h1 hyx)
  by_cases hab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a
  ·
    exfalso
    have hNC := normalizer_le_centralizer_of_odd P hab fun g hg hodd =>
      commute_of_odd_of_fourTwo hab hxP hxord hyP hy2 hyx hidx hg hodd
    obtain ⟨K, hKn, hK2, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hNC
    rcases hKn.eq_bot_or_eq_top with hK | hK
    ·
      rw [hK, Subgroup.index_bot, hP8] at hKidx
      have hG2 : IsPGroup 2 G := IsPGroup.of_card (n := 3) (by rw [hKidx]; norm_num)
      have : Nontrivial G := IsSimpleGroup.toNontrivial
      have hZ := hG2.center_nontrivial
      rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hZb | hZt
      · rw [hZb] at hZ
        exact (not_nontrivial_iff_subsingleton.mpr (by infer_instance) hZ)
      · obtain ⟨a, b, hne⟩ := hnonab
        have ha : a ∈ center G := by rw [hZt]; exact mem_top a
        exact hne ((mem_center_iff.mp ha b).symm)
    · rw [hK, Subgroup.index_top, hP8] at hKidx
      norm_num at hKidx
  ·
    have hnorm : ((zpowers x).subgroupOf (P : Subgroup G)).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    have hc : y * x * y⁻¹ ∈ zpowers x := by
      have := hnorm.conj_mem ⟨x, hxP⟩ (by rw [mem_subgroupOf]; exact mem_zpowers x) ⟨y, hyP⟩
      rw [mem_subgroupOf] at this
      simpa using this
    have hco : orderOf (y * x * y⁻¹) = 4 := by
      rw [show y * x * y⁻¹ = (MulAut.conj y) x from rfl, MulEquiv.orderOf_eq, hxord]
    have hrel : y * x * y⁻¹ = x⁻¹ := by
      rcases eq_or_eq_inv_of_orderOf_four hxord hc hco with h | h
      · exfalso
        have hxy : Commute x y := by
          have : y * x = x * y := by rw [← mul_inv_eq_iff_eq_mul, h]
          exact this.symm
        have hcommP : ∀ u ∈ (P : Subgroup G), Commute u x ∧ Commute u y := by
          intro u hu
          rcases hcoset u hu with h1 | h1
          · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp h1
            exact ⟨(Commute.refl x).zpow_left i, hxy.zpow_left i⟩
          · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h1
            have hu' : u = x ^ i * y := by rw [hi]; group
            rw [hu']
            exact ⟨((Commute.refl x).zpow_left i).mul_left hxy.symm,
              (hxy.zpow_left i).mul_left (Commute.refl y)⟩
        apply hab
        intro a ha b hb
        rcases hcoset b hb with h1 | h1
        · obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp h1
          exact ((hcommP a ha).1.zpow_right j).eq
        · obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h1
          have hb' : b = x ^ j * y := by rw [hj]; group
          rw [hb']
          exact (((hcommP a ha).1.zpow_right j).mul_right (hcommP a ha).2).eq
      · exact h
    set ρ : (P : Subgroup G) := ⟨x, hxP⟩ with hρ
    set σ : (P : Subgroup G) := ⟨y, hyP⟩ with hσ
    have hgen : (⊤ : Subgroup (P : Subgroup G)) = zpowers ρ ⊔ zpowers σ := by
      rw [eq_comm, eq_top_iff]
      rintro ⟨u, hu⟩ -
      rcases hcoset u hu with h1 | h1
      · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h1
        apply mem_sup_left
        refine mem_zpowers_iff.mpr ⟨i, Subtype.ext ?_⟩
        simp [hρ, hi]
      · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h1
        have hu' : (⟨u, hu⟩ : (P : Subgroup G)) = ρ ^ i * σ := by
          apply Subtype.ext
          simp only [hρ, hσ, coe_mul, coe_zpow]
          rw [hi]; group
        rw [hu']
        exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers ρ) i)) (mem_sup_right (mem_zpowers σ))
    have hσ2 : σ ^ 2 = 1 := by
      apply Subtype.ext
      simp only [hσ, coe_pow, coe_one]
      rw [← hy2, pow_orderOf_eq_one]
    have hrelP : σ * ρ * σ⁻¹ = ρ⁻¹ := by
      apply Subtype.ext
      simp only [hρ, hσ, coe_mul, coe_inv]
      exact hrel
    have hσρ : σ ∉ zpowers ρ := by
      intro h
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h
      apply hyx
      refine mem_zpowers_iff.mpr ⟨i, ?_⟩
      have := congrArg Subtype.val hi
      simpa [hρ, hσ] using this
    obtain ⟨e⟩ := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrelP hσρ
    have hρo : orderOf ρ = 4 := by rw [hρ, Subgroup.orderOf_mk, hxord]
    rw [hρo] at e
    exact ⟨e⟩

end Dihedral

section LType

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

theorem Config.hasDihedralSylowTwo (h : Config t L) :
    HasDihedralSylowTwo (L ⧸ pPrimeCore 2 L) := by
  have hs := h.isSimpleGroup
  intro S
  obtain ⟨e⟩ := sylow_mulEquiv_dihedral_of_simple h.quot_nonabelian h.pRank_eq S (h.card_sylow S)
  exact ⟨2, by norm_num, ⟨e⟩⟩

theorem Config.pPrimeCore_quot_eq_bot (h : Config t L) :
    pPrimeCore 2 (L ⧸ pPrimeCore 2 L) = ⊥ := by
  have hs := h.isSimpleGroup
  rcases (pPrimeCore_normal (p := 2) (G := L ⧸ pPrimeCore 2 L)).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 (L ⧸ pPrimeCore 2 L))) :=
      pPrimeCore_coprime_card
    rw [ht, card_top] at hcop
    have h2 : 2 ∣ Nat.card (L ⧸ pPrimeCore 2 L) := (by norm_num : 2 ∣ 8).trans h.eight_dvd_card
    have := Nat.Coprime.eq_one_of_dvd hcop h2
    norm_num at this

theorem Config.sixty_le_card (h : Config t L) : 60 ≤ Nat.card (L ⧸ pPrimeCore 2 L) :=
  CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty h.isSimpleGroup h.quot_nonabelian

theorem Config.type (h : Config t L) :
    Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
      ∃ (K : Type) (_ : Field K) (_ : Finite K), IsOddPrimePower (Nat.card K) ∧
        3 < Nat.card K ∧ Nonempty (L ⧸ pPrimeCore 2 L ≃* PSL2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := L ⧸ pPrimeCore 2 L with hQ
  have hs : IsSimpleGroup Q := h.isSimpleGroup
  have h60 : 60 ≤ Nat.card Q := h.sixty_le_card
  let eQ : Q ⧸ pPrimeCore 2 Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq h.pPrimeCore_quot_eq_bot).trans QuotientGroup.quotientBot
  rcases gorensteinWalter.{0} Q h.hasDihedralSylowTwo with ⟨-, hTwo⟩ | ⟨-, ⟨h7⟩⟩ |
      ⟨-, K, hK, M, hMn, hModd, hMmodel⟩
  ·
    exfalso
    have hQ2 : IsPGroup 2 Q := hTwo.of_equiv eQ
    have : Nontrivial Q := IsSimpleGroup.toNontrivial
    have hZ := hQ2.center_nontrivial
    rw [h.center_quot_eq_bot] at hZ
    exact (not_nontrivial_iff_subsingleton.mpr (by infer_instance) hZ)
  · exact Or.inl ⟨eQ.symm.trans h7⟩
  · obtain ⟨p, n, hp, hpodd, hn, hKcard⟩ := hK
    have hK' : IsOddPrimePower (Nat.card K) := ⟨p, n, hp, hpodd, hn, hKcard⟩
    set M' : Subgroup Q := M.map eQ.toMonoidHom with hM'
    have hM'n : M'.Normal := hMn.map eQ.toMonoidHom eQ.surjective
    have hM'odd : Odd M'.index := by
      rw [hM', Subgroup.index_map_of_injective _ eQ.injective,
        MonoidHom.range_eq_top.mpr eQ.surjective, Subgroup.index_top, mul_one]
      exact hModd
    have hM'top : M' = ⊤ := by
      rcases hM'n.eq_bot_or_eq_top with hb | ht
      · exfalso
        rw [hb, Subgroup.index_bot] at hM'odd
        exact (Nat.not_even_iff_odd.mpr hM'odd)
          (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 8).trans h.eight_dvd_card))
      · exact ht
    let eM : M ≃* Q := (M.equivMapOfInjective eQ.toMonoidHom eQ.injective).trans
      ((MulEquiv.subgroupCongr hM'top).trans Subgroup.topEquiv)
    have hq3 : 3 ≤ Nat.card K := by
      rw [hKcard]
      have := hp.two_le
      have : p ≠ 2 := fun h2 => by rw [h2] at hpodd; exact absurd hpodd (by decide)
      calc 3 ≤ p := by omega
        _ ≤ p ^ n := Nat.le_self_pow (by omega) p
    rcases hMmodel with hPSL | hPGL
    ·
      obtain ⟨ePSL⟩ := hPSL
      have eQK : Q ≃* PSL2 K := eM.symm.trans ePSL
      refine Or.inr ⟨K, inferInstance, inferInstance, hK', ?_, ⟨eQK⟩⟩
      by_contra hle
      have hq : Nat.card K = 3 := by omega
      have hc := (Nat.card_congr eQK.toEquiv).trans (psl2_card_formula K hK')
      rw [hq] at hc
      norm_num at hc
      omega
    ·
      exfalso
      obtain ⟨ePGL⟩ := hPGL
      have eQK : Q ≃* PGL2 K := eM.symm.trans ePGL
      have hc := (Nat.card_congr eQK.toEquiv).trans (pgl2_card_formula K)
      by_cases h3 : 3 < Nat.card K
      · let eT : (⊤ : Subgroup Q) ≃* PGL2 K := Subgroup.topEquiv.trans eQK
        obtain ⟨L'', hL''n, -, ⟨eL''⟩⟩ :=
          exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three (⊤ : Subgroup Q)
            inferInstance K hK' h3 eT
        have hc'' := (Nat.card_congr eL''.toEquiv).trans (psl2_card_formula K hK')
        have hqodd : Odd (Nat.card K) := hKcard ▸ hpodd.pow
        have heven : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
          (Nat.Odd.sub_odd hqodd.pow odd_one).two_dvd.mul_left _
        have hpos : 0 < Nat.card K * (Nat.card K ^ 2 - 1) := by
          have : 1 < Nat.card K ^ 2 := by nlinarith
          have : 0 < Nat.card K ^ 2 - 1 := by omega
          positivity
        rcases hL''n.eq_bot_or_eq_top with hb | ht
        · rw [hb, card_bot] at hc''
          omega
        · rw [ht, card_top, hc] at hc''
          omega
      · have hq : Nat.card K = 3 := by omega
        rw [hq] at hc
        norm_num at hc
        omega

theorem Config.not_sixteen_dvd (h : Config t L) : ¬ 16 ∣ Nat.card (L ⧸ pPrimeCore 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h16
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := L ⧸ pPrimeCore 2 L) 2
    (n := 4) (by norm_num; exact h16)
  have hH2 : IsPGroup 2 H := IsPGroup.of_card hH
  obtain ⟨S, hS⟩ := hH2.exists_le_sylow
  have := Subgroup.card_dvd_of_le hS
  rw [hH, h.card_sylow S] at this
  norm_num at this

theorem Config.card_quot_cases (h : Config t L) :
    7 ∣ Nat.card (L ⧸ pPrimeCore 2 L) ∨ 9 ∣ Nat.card (L ⧸ pPrimeCore 2 L) ∨
      2000 < Nat.card (L ⧸ pPrimeCore 2 L) := by
  have h8 := h.eight_dvd_card
  have h16 := h.not_sixteen_dvd
  rcases h.type with he | ⟨K, _, _, hK, h3, he⟩
  · obtain ⟨e⟩ := he
    left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · obtain ⟨e⟩ := he
    have hc := (Nat.card_congr e.toEquiv).trans (psl2_card_formula K hK)
    rw [hc] at h8 h16 ⊢
    obtain ⟨p, n, hp, hpodd, hn, hKcard⟩ := hK
    have hqodd : Odd (Nat.card K) := hKcard ▸ hpodd.pow
    generalize Nat.card K = q at hqodd h3 h8 h16 ⊢
    by_cases hq : 23 ≤ q
    · right; right
      have h1 : 23 * (23 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
        apply Nat.mul_le_mul hq
        have : 23 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
        omega
      have : 23 * (23 ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / 2 := Nat.div_le_div_right h1
      norm_num at this
      omega
    · obtain ⟨k, rfl⟩ := hqodd
      have hk : k ≤ 10 := by omega
      interval_cases k <;> (revert h8 h16 h3; decide)

end LType

end CFSG.ComponentClassification.HSFLit
