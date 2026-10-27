module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts
public import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizerSplit
public import CFSG.GroupTheory.QuasiDihedralFusion.Classes

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion

section KleinFourActions

variable {G : Type*} [Group G]

private theorem qdd_conj_mem {V : Subgroup G} {g v : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) : g * v * g⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp hg v).mp hv

private theorem qdd_conj_ne_one {g v : G} (hv : v ≠ 1) : g * v * g⁻¹ ≠ 1 := by
  intro h
  apply hv
  calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

private theorem qdd_conj_injective {g v w : G} (h : g * v * g⁻¹ = g * w * g⁻¹) : v = w := by
  simpa using h

private theorem qdd_mul_self (V : Subgroup G) [IsKleinFour V] {a : G} (ha : a ∈ V) :
    a * a = 1 := by
  have h := Monoid.pow_exponent_eq_one (⟨a, ha⟩ : V)
  rw [IsKleinFour.exponent_two, pow_two] at h
  exact congrArg Subtype.val h

private theorem qdd_mul_comm (V : Subgroup G) [IsKleinFour V] {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a :=
  Local.kleinFour_mul_comm V ha hb

private theorem qdd_cube_mem_centralizer (V : Subgroup G) [IsKleinFour V] {y : G}
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (hfree : ∀ v ∈ V, v ≠ 1 → y * v * y⁻¹ ≠ v) :
    y ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1, one_mul, mul_one]
  obtain ⟨w, hw⟩ : ∃ w, w = y * v * y⁻¹ := ⟨_, rfl⟩
  have hwV : w ∈ V := hw ▸ qdd_conj_mem hy hv
  have hw1 : w ≠ 1 := hw ▸ qdd_conj_ne_one hv1
  have hwv : w ≠ v := hw ▸ hfree v hv hv1
  obtain ⟨u, hu⟩ : ∃ u, u = y * w * y⁻¹ := ⟨_, rfl⟩
  have huV : u ∈ V := hu ▸ qdd_conj_mem hy hwV
  have hu1 : u ≠ 1 := hu ▸ qdd_conj_ne_one hw1
  have huw : u ≠ w := hu ▸ hfree w hwV hw1
  have huv : u ≠ v := by
    intro huv
    have hvw1 : v * w ≠ 1 := by
      intro h
      apply hwv
      calc w = (v * v) * w := by rw [qdd_mul_self V hv, one_mul]
        _ = v * (v * w) := by group
        _ = v := by rw [h, mul_one]
    apply hfree (v * w) (V.mul_mem hv hwV) hvw1
    calc y * (v * w) * y⁻¹ = (y * v * y⁻¹) * (y * w * y⁻¹) := by group
      _ = w * v := by rw [← hw, ← hu, huv]
      _ = v * w := qdd_mul_comm V hwV hv
  have huvw : u = v * w := by
    rcases Local.kleinFour_mem_cases V hv hwV hv1 hw1 hwv.symm huV with h | h | h | h
    · exact h
    · exact absurd h huv
    · exact absurd h huw
    · exact absurd h hu1
  have h3 : y * u * y⁻¹ = v := by
    calc y * u * y⁻¹ = (y * v * y⁻¹) * (y * w * y⁻¹) := by rw [huvw]; group
      _ = w * (v * w) := by rw [← hw, ← hu, huvw]
      _ = (w * w) * v := by rw [qdd_mul_comm V hv hwV]; group
      _ = v := by rw [qdd_mul_self V hwV, one_mul]
  have h4 : y ^ 3 * v * (y ^ 3)⁻¹ = v := by
    calc y ^ 3 * v * (y ^ 3)⁻¹ = y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹ := by
          rw [pow_three]; group
      _ = v := by rw [← hw, ← hu, h3]
  calc v * y ^ 3 = (y ^ 3 * v * (y ^ 3)⁻¹) * y ^ 3 := by rw [h4]
    _ = y ^ 3 * v := by group

private theorem qdd_fixedPointFree_of_cube (V : Subgroup G) [IsKleinFour V] {g : G}
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
  have hcV : c ∈ V := hc ▸ qdd_conj_mem hg hb
  have hc1 : c ≠ 1 := hc ▸ qdd_conj_ne_one hb1
  have hcb : c ≠ b := hc ▸ hmove
  have hca : c ≠ a := by
    intro h
    apply hba
    apply qdd_conj_injective (g := g)
    rw [← hc, h, hfix]
  have hcab : c = a * b := by
    rcases Local.kleinFour_mem_cases V ha hb ha1 hb1 hba.symm hcV with h | h | h | h
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
      _ = g * b * g⁻¹ := by rw [← mul_assoc a a b, qdd_mul_self V ha, one_mul]
      _ = c := hc.symm
  exact hcb (h3c.symm.trans h3b)

private theorem qdd_exists_fixedPointFree (V : Subgroup G) [IsKleinFour V] {g x : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hgfree : ∀ v ∈ V, v ≠ 1 → g * v * g⁻¹ ≠ v)
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hx1 : x ∉ Subgroup.centralizer (V : Set G)) :
    ∃ y, (y = x ∨ y = x * (g * x * g⁻¹)) ∧ ∀ v ∈ V, v ≠ 1 → y * v * y⁻¹ ≠ v := by
  by_cases hfree : ∀ v ∈ V, v ≠ 1 → x * v * x⁻¹ ≠ v
  · exact ⟨x, Or.inl rfl, hfree⟩
  push Not at hfree
  obtain ⟨a, ha, ha1, hxa⟩ := hfree
  have hxmove : ∀ v ∈ V, v ≠ 1 → v ≠ a → x * v * x⁻¹ ≠ v := by
    intro v hv hv1 hva hxv
    apply hx1
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hxw : x * w * x⁻¹ = w := by
      rcases Local.kleinFour_mem_cases V ha hv ha1 hv1 (Ne.symm hva) hw with h | h | h | h
      · rw [h]
        calc x * (a * v) * x⁻¹ = (x * a * x⁻¹) * (x * v * x⁻¹) := by group
          _ = a * v := by rw [hxa, hxv]
      · rw [h, hxa]
      · rw [h, hxv]
      · rw [h]
        group
    calc w * x = (x * w * x⁻¹) * x := by rw [hxw]
      _ = x * w := by group
  obtain ⟨a', ha'⟩ : ∃ a', a' = g * a * g⁻¹ := ⟨_, rfl⟩
  have ha'V : a' ∈ V := ha' ▸ qdd_conj_mem hg ha
  have ha'1 : a' ≠ 1 := ha' ▸ qdd_conj_ne_one ha1
  have ha'a : a' ≠ a := ha' ▸ hgfree a ha ha1
  obtain ⟨x', hx'⟩ : ∃ x', x' = g * x * g⁻¹ := ⟨_, rfl⟩
  have hx'a' : x' * a' * x'⁻¹ = a' := by
    rw [hx', ha']
    calc g * x * g⁻¹ * (g * a * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * a * x⁻¹) * g⁻¹ := by group
      _ = g * a * g⁻¹ := by rw [hxa]
  have hginv : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hg
  have hx'move : ∀ v ∈ V, v ≠ 1 → v ≠ a' → x' * v * x'⁻¹ ≠ v := by
    intro v hv hv1 hva' h
    have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ V := qdd_conj_mem hginv hv
    rw [inv_inv] at hv'
    have hv'1 : g⁻¹ * v * g ≠ 1 := by
      have := qdd_conj_ne_one (g := g⁻¹) hv1
      rwa [inv_inv] at this
    have hv'a : g⁻¹ * v * g ≠ a := by
      intro h'
      apply hva'
      rw [ha', ← h']
      group
    apply hxmove _ hv' hv'1 hv'a
    calc x * (g⁻¹ * v * g) * x⁻¹ = g⁻¹ * (x' * v * x'⁻¹) * g := by rw [hx']; group
      _ = g⁻¹ * v * g := by rw [h]
  have hx'aV : x' * a * x'⁻¹ ∈ V := by
    rw [hx']
    exact qdd_conj_mem (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx) hginv) ha
  have hx'a : x' * a * x'⁻¹ = a * a' := by
    have hm := hx'move a ha ha1 (Ne.symm ha'a)
    have hm1 : x' * a * x'⁻¹ ≠ 1 := qdd_conj_ne_one ha1
    have hma' : x' * a * x'⁻¹ ≠ a' := by
      intro h
      exact ha'a (qdd_conj_injective (h.trans hx'a'.symm)).symm
    rcases Local.kleinFour_mem_cases V ha ha'V ha1 ha'1 (Ne.symm ha'a) hx'aV with h | h | h | h
    · exact h
    · exact absurd h hm
    · exact absurd h hma'
    · exact absurd h hm1
  refine ⟨x * (g * x * g⁻¹), Or.inr rfl, ?_⟩
  rw [← hx']
  intro v hv hv1
  rcases Local.kleinFour_mem_cases V ha ha'V ha1 ha'1 (Ne.symm ha'a) hv with h | h | h | h
  · intro hfix
    have hy : x * x' * v * (x * x')⁻¹ = a := by
      calc x * x' * v * (x * x')⁻¹ = x * ((x' * a * x'⁻¹) * (x' * a' * x'⁻¹)) * x⁻¹ := by
            rw [h]; group
        _ = x * a * x⁻¹ := by rw [hx'a, hx'a', mul_assoc a a' a', qdd_mul_self V ha'V, mul_one]
        _ = a := hxa
    rw [hfix, h] at hy
    exact ha'1 (by simpa using hy)
  · intro hfix
    have hy : x * x' * v * (x * x')⁻¹ = a * (x * a' * x⁻¹) := by
      calc x * x' * v * (x * x')⁻¹ = x * (x' * a * x'⁻¹) * x⁻¹ := by rw [h]; group
        _ = (x * a * x⁻¹) * (x * a' * x⁻¹) := by rw [hx'a]; group
        _ = a * (x * a' * x⁻¹) := by rw [hxa]
    rw [hfix, h] at hy
    exact qdd_conj_ne_one (g := x) ha'1 (by simpa using hy.symm)
  · intro hfix
    apply hxmove a' ha'V ha'1 ha'a
    calc x * a' * x⁻¹ = x * (x' * a' * x'⁻¹) * x⁻¹ := by rw [hx'a']
      _ = x * x' * v * (x * x')⁻¹ := by rw [h]; group
      _ = v := hfix
      _ = a' := h
  · exact absurd h hv1

end KleinFourActions

section Automizers

variable {G : Type*} [Group G]

private theorem qdd_centralizer_subgroupOf_normal {K : Type*} [Group K] (T : Subgroup K) :
    ((Subgroup.centralizer (T : Set K)).subgroupOf (Subgroup.normalizer (T : Set K))).Normal := by
  rw [← Subgroup.normalizerMonoidHom_ker]
  exact MonoidHom.normal_ker _

private theorem qdd_exists_of_three_dvd_automizerIndex {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} (h : 3 ∣ automizerIndex T) :
    ∃ g ∈ Subgroup.normalizer (T : Set K), g ^ 3 ∈ Subgroup.centralizer (T : Set K) ∧
      g ∉ Subgroup.centralizer (T : Set K) := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have : (Ct.subgroupOf Nt).Normal := qdd_centralizer_subgroupOf_normal T
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

private theorem qdd_three_dvd_automizerIndex_of {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} {g : K} (hg : g ∈ Subgroup.normalizer (T : Set K))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set K))
    (h1 : g ∉ Subgroup.centralizer (T : Set K)) : 3 ∣ automizerIndex T := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have : (Ct.subgroupOf Nt).Normal := qdd_centralizer_subgroupOf_normal T
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using h3
    · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h1
  have := orderOf_dvd_natCard ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt)
  rw [hord, ← Subgroup.index_eq_card] at this
  exact this

private theorem qdd_mem_normalizer_subgroupOf_iff {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.normalizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.mem_subgroupOf]

private theorem qdd_mem_centralizer_subgroupOf_iff {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.centralizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.centralizer (T : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTH ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h _ ht)

private theorem qdd_exists_of_three_dvd_automizerIndex_subgroupOf [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (h : 3 ∣ automizerIndex (T.subgroupOf H)) :
    ∃ g ∈ H, g ∈ Subgroup.normalizer (T : Set G) ∧ g ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧
      g ∉ Subgroup.centralizer (T : Set G) := by
  obtain ⟨g, hgN, hg3, hg1⟩ := qdd_exists_of_three_dvd_automizerIndex h
  refine ⟨g, g.2, (qdd_mem_normalizer_subgroupOf_iff hTH).mp hgN, ?_, ?_⟩
  · simpa using (qdd_mem_centralizer_subgroupOf_iff hTH).mp hg3
  · exact fun h' => hg1 ((qdd_mem_centralizer_subgroupOf_iff hTH).mpr h')

private theorem qdd_three_dvd_automizerIndex_subgroupOf_of [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) {g : G} (hgH : g ∈ H) (hg : g ∈ Subgroup.normalizer (T : Set G))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set G)) (h1 : g ∉ Subgroup.centralizer (T : Set G)) :
    3 ∣ automizerIndex (T.subgroupOf H) :=
  qdd_three_dvd_automizerIndex_of (g := ⟨g, hgH⟩) ((qdd_mem_normalizer_subgroupOf_iff hTH).mpr hg)
    ((qdd_mem_centralizer_subgroupOf_iff hTH).mpr (by simpa using h3))
    (fun h' => h1 ((qdd_mem_centralizer_subgroupOf_iff hTH).mp h'))

private theorem qdd_exists_ne_one (V : Subgroup G) [IsKleinFour V] : ∃ v ∈ V, v ≠ 1 := by
  have hne : V ≠ ⊥ := by
    intro h
    have h4 := IsKleinFour.card_four (G := V)
    rw [h, Subgroup.card_bot] at h4
    norm_num at h4
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  exact ⟨v, hv, fun h => hv1 (Subtype.ext h)⟩

private theorem qdd_three_dvd_of_normal [Finite G] {H X V : Subgroup G} [IsKleinFour V]
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) (hVX : V ≤ X) {g : G} (hgH : g ∈ H)
    (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgfree : ∀ v ∈ V, v ≠ 1 → g * v * g⁻¹ ≠ v)
    {x : G} (hxX : x ∈ X) (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hx1 : x ∉ Subgroup.centralizer (V : Set G)) : 3 ∣ automizerIndex (V.subgroupOf X) := by
  obtain ⟨y, hy, hyfree⟩ := qdd_exists_fixedPointFree V hgN hgfree hxN hx1
  have hyX : y ∈ X := by
    rcases hy with rfl | rfl
    · exact hxX
    · exact X.mul_mem hxX (qdd_conj_mem (hHX hgH) hxX)
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
    rcases hy with rfl | rfl
    · exact hxN
    · exact Subgroup.mul_mem _ hxN
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hxN) (Subgroup.inv_mem _ hgN))
  have hy3 := qdd_cube_mem_centralizer V hyN hyfree
  have hy1 : y ∉ Subgroup.centralizer (V : Set G) := by
    obtain ⟨v, hv, hv1⟩ := qdd_exists_ne_one V
    intro hyC
    apply hyfree v hv hv1
    rw [← Subgroup.mem_centralizer_iff.mp hyC v hv]
    group
  exact qdd_three_dvd_automizerIndex_subgroupOf_of hVX hyX hyN hy3 hy1

end Automizers

section SemidihedralLocal

variable {G : Type*} [Group G] [Finite G] {n : ℕ}

private theorem qdd_le_of_le_centralizer (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (V : Subgroup G) [IsKleinFour V] {R : Subgroup G}
    (hR : IsPGroup 2 R) (hRC : R ≤ Subgroup.centralizer (V : Set G)) : R ≤ V := by
  set C := Subgroup.centralizer (V : Set G)
  obtain ⟨P, hP⟩ := Local.kleinFour_sylow_of_centralizer n hn S f V
  have hPn : (P : Subgroup C).Normal := by
    rw [hP]
    constructor
    intro x hx c
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hc := Subgroup.mem_centralizer_iff.mp c.2 x hx
    have h : ((c * x * c⁻¹ : C) : G) = x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hc]
      group
    rw [h]
    exact hx
  have hR' : IsPGroup 2 (R.subgroupOf C) :=
    hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
  obtain ⟨Q, hQ⟩ := hR'.exists_le_sylow
  have hQP : Q = P := by
    have := Sylow.unique_of_normal P hPn
    exact Subsingleton.elim Q P
  intro x hx
  have hmem : (⟨x, hRC hx⟩ : C) ∈ (Q : Subgroup C) := hQ hx
  rw [hQP, hP] at hmem
  exact hmem

private theorem qdd_isSolvable_normalizer (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (V : Subgroup G) [hV : IsKleinFour V] :
    Group.IsSolvable (Subgroup.normalizer (V : Set G)) := by
  obtain ⟨-, -, -, N, -, ⟨hNodd, -⟩, -, -, -, -, e, -⟩ :=
    Local.semidihedral_four_subgroup_centralizer_split n hn S f V hV
  have : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have : Group.IsSolvable (V.subgroupOf (Subgroup.centralizer (V : Set G))) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext
      (qdd_mul_comm V (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)))
  have : Group.IsSolvable (Subgroup.centralizer (V : Set G)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have : Group.IsSolvable (MulAut V) := by
    obtain ⟨ψ⟩ := Local.nonempty_mulAut_equiv_perm_three (V := V)
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
  have hCN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have : Group.IsSolvable ((Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G))) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hCN).toMonoidHom)
      (MulEquiv.injective _)
  exact Group.isSolvable_of_ker_le_range ((Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G))).subtype V.normalizerMonoidHom
    (by rw [Subgroup.normalizerMonoidHom_ker, Subgroup.range_subtype])

end SemidihedralLocal

section Solvable

variable {G : Type*} [Group G] [Finite G] {n : ℕ}

private theorem qdd_top_not_le_pPrimeCore {H V : Subgroup G} [IsKleinFour V] (hVH : V ≤ H) :
    ¬ (⊤ : Subgroup H) ≤ pPrimeCore 2 H := by
  intro htop
  have hcop : Nat.Coprime 2 (Nat.card H) := by
    have h := (pPrimeCore_coprime_card (p := 2) (G := H))
    rwa [le_antisymm le_top htop, Subgroup.card_top] at h
  have h4 : Nat.card (V.subgroupOf H) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv, IsKleinFour.card_four]
  have hdvd : 2 ∣ Nat.card H :=
    dvd_trans ⟨2, by norm_num⟩ (h4 ▸ Subgroup.card_subgroup_dvd_card (V.subgroupOf H))
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)

private theorem qdd_le_oddCoreIn_of_isSolvable (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {H V : Subgroup G} [IsKleinFour V] (hVH : V ≤ H)
    (h3 : 3 ∣ automizerIndex (V.subgroupOf H)) (hsolv : Group.IsSolvable H) {X : Subgroup G}
    (hXH : X ≤ H) (hX : Odd (Nat.card X)) (hVX : V ≤ Subgroup.normalizer (X : Set G)) :
    X ≤ oddCoreIn H := by
  obtain ⟨g, hgH, hgN, hg3, hg1⟩ := qdd_exists_of_three_dvd_automizerIndex_subgroupOf hVH h3
  have hgfree := qdd_fixedPointFree_of_cube V hgN hg3 hg1
  obtain ⟨k, hk, hk1⟩ : ∃ k, ¬ derivedSeries H k ≤ pPrimeCore 2 H ∧
      derivedSeries H (k + 1) ≤ pPrimeCore 2 H := by
    classical
    have hex : ∃ m, derivedSeries H m ≤ pPrimeCore 2 H := by
      obtain ⟨m, hm⟩ := hsolv.solvable
      exact ⟨m, hm ▸ bot_le⟩
    have hm0 : Nat.find hex ≠ 0 := by
      intro h0
      have h := Nat.find_spec hex
      rw [h0, derivedSeries_zero] at h
      exact qdd_top_not_le_pPrimeCore hVH h
    refine ⟨Nat.find hex - 1, Nat.find_min hex (by omega), ?_⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
    exact Nat.find_spec hex
  set A : Subgroup G := (derivedSeries H k).map H.subtype with hAdef
  have hAH : A ≤ H := Subgroup.map_subtype_le _
  have hAsub : A.subgroupOf H = derivedSeries H k :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hAn : (A.subgroupOf H).Normal := by
    rw [hAsub]
    infer_instance
  have hHA : H ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAn
  have hAeven : 2 ∣ Nat.card (derivedSeries H k) := by
    by_contra hodd
    apply hk
    exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd⟩
  obtain ⟨b, hbV, hbA, hb1⟩ : ∃ b ∈ V, b ∈ A ∧ b ≠ 1 := by
    have hV2 : IsPGroup 2 (V.subgroupOf H) := IsPGroup.of_card (n := 2) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv, IsKleinFour.card_four]
      norm_num)
    obtain ⟨Q, hVQ⟩ := hV2.exists_le_sylow
    have hne : (derivedSeries H k).subgroupOf (Q : Subgroup H) ≠ ⊥ := by
      intro hbot
      apply not_dvd_relIndex_of_normal Q (derivedSeries H k)
      have hbot' : (Q : Subgroup H).subgroupOf (derivedSeries H k) = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot] at hbot ⊢
        exact hbot.symm
      rw [hbot', Subgroup.index_bot]
      exact hAeven
    have : Group.IsNilpotent (Q : Subgroup H) := Q.isPGroup'.isNilpotent
    have hnorm : ((derivedSeries H k).subgroupOf (Q : Subgroup H)).Normal :=
      Subgroup.normal_subgroupOf
    obtain ⟨⟨y, hyB, hyZ⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    refine ⟨((y : H) : G), ?_, ⟨y, Subgroup.mem_subgroupOf.mp hyB, rfl⟩, ?_⟩
    · have hyC : ((y : H) : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hvQ : (⟨v, hVH hv⟩ : H) ∈ (Q : Subgroup H) := hVQ (Subgroup.mem_subgroupOf.mpr hv)
        have h := Subgroup.mem_center_iff.mp hyZ ⟨_, hvQ⟩
        exact congrArg (fun q : (Q : Subgroup H) => ((q : H) : G)) h
      have hy2 : IsPGroup 2 (Subgroup.zpowers ((y : H) : G)) := by
        have hQ2 : IsPGroup 2 (((Q : Subgroup H).map H.subtype : Subgroup G)) :=
          Q.isPGroup'.map H.subtype
        exact hQ2.to_le (Subgroup.zpowers_le.mpr ⟨y, y.2, rfl⟩)
      exact qdd_le_of_le_centralizer hn S f V hy2 (Subgroup.zpowers_le.mpr hyC)
        (Subgroup.mem_zpowers _)
    · intro h
      apply hy1'
      exact Subtype.ext (Subtype.ext h)
  have hVA : V ≤ A := by
    intro v hv
    have hb'V := qdd_conj_mem hgN hbV
    have hb'A := qdd_conj_mem (hHA hgH) hbA
    have hb'1 : g * b * g⁻¹ ≠ 1 := qdd_conj_ne_one hb1
    have hbb' : b ≠ g * b * g⁻¹ := fun h => hgfree b hbV hb1 h.symm
    rcases Local.kleinFour_mem_cases V hbV hb'V hb1 hb'1 hbb' hv with h | h | h | h
    · rw [h]
      exact A.mul_mem hbA hb'A
    · rw [h]
      exact hbA
    · rw [h]
      exact hb'A
    · rw [h]
      exact A.one_mem
  have hcomm : ∀ a ∈ A, ∀ c ∈ A, a * c * a⁻¹ * c⁻¹ ∈ (pPrimeCore 2 A).map A.subtype := by
    have h1 : ⁅A, A⁆ ≤ (pPrimeCore 2 H).map H.subtype := by
      rw [hAdef, ← Subgroup.map_commutator, ← derivedSeries_succ]
      exact Subgroup.map_mono hk1
    have hOn : H ≤ Subgroup.normalizer (((pPrimeCore 2 H).map H.subtype : Subgroup G) : Set G) :=
      ABGTheoremB.le_normalizer_map_subtype H (pPrimeCore 2 H)
    have h2 : (pPrimeCore 2 H).map H.subtype ⊓ A ≤ (pPrimeCore 2 A).map A.subtype := by
      refine Local.le_map_pPrimeCore_of_le_normalizer 2 inf_le_right
        (fun a ha => Subgroup.inf_normalizer_le_normalizer_inf ⟨hOn (hAH ha),
          Subgroup.le_normalizer ha⟩) ?_
      refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) ?_
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact pPrimeCore_coprime_card
    intro a ha c hc
    refine h2 ⟨h1 ?_, ?_⟩
    · rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator ha hc
    · exact A.mul_mem (A.mul_mem (A.mul_mem ha hc) (A.inv_mem ha)) (A.inv_mem hc)
  have htc : (QuotientGroup.mk (⟨b, hVA hbV⟩ : A) : A ⧸ pPrimeCore 2 A) ∈
      Subgroup.center (A ⧸ pPrimeCore 2 A) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h := hcomm _ (A.inv_mem (hVA hbV)) _ (A.inv_mem a.2)
      rw [inv_inv, inv_inv] at h
      have h' : (((a * ⟨b, hVA hbV⟩)⁻¹ * (⟨b, hVA hbV⟩ * a) : A) : G) =
          b⁻¹ * (a : G)⁻¹ * b * a := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      exact (Subgroup.mem_map_iff_mem A.subtype_injective).mp (by
        change (((a * ⟨b, hVA hbV⟩)⁻¹ * (⟨b, hVA hbV⟩ * a) : A) : G) ∈ _
        rw [h']
        exact h)
  obtain ⟨-, -, -, -, -, -, -, hctrl⟩ :=
    Local.four_group_cycling_normal_subgroup_controls_invariant_odd_subgroups n hn S f H A V hAH
      hAn hVA b hbV hb1 htc g hgH hgN hgfree
  rw [oddCoreIn, QuaternionFocalFactorization.oddCore_eq_twoPrimeCore]
  exact hctrl X hXH hX hVX

end Solvable

section NormalSubgroups

variable {G : Type*} [Group G] [Finite G] {n : ℕ}

private theorem qdd_exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {V P : Subgroup G}
    (hP : IsPGroup p P) (hVP : V < P) :
    ∃ x ∈ P, x ∈ Subgroup.normalizer (V : Set G) ∧ x ∉ V := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : V.subgroupOf P < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hVP.not_ge (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨x, hxN, hxV⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  exact ⟨x, x.2, (qdd_mem_normalizer_subgroupOf_iff hVP.le).mp hxN,
    fun h => hxV (Subgroup.mem_subgroupOf.mpr h)⟩

private theorem qdd_sylow_of_normalizer_le (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {X V : Subgroup G} [IsKleinFour V] (hVX : V ≤ X)
    (hcon : ∀ x ∈ X, x ∈ Subgroup.normalizer (V : Set G) →
      x ∈ Subgroup.centralizer (V : Set G)) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = V.subgroupOf X := by
  have h4 : Nat.card (V.subgroupOf X) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv, IsKleinFour.card_four]
  have hV2 : IsPGroup 2 (V.subgroupOf X) := IsPGroup.of_card (n := 2) (by rw [h4]; norm_num)
  obtain ⟨P, hVP⟩ := hV2.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hVP⟩
  by_contra hnot
  have hP2 : IsPGroup 2 ((P : Subgroup X).map X.subtype) := P.isPGroup'.map X.subtype
  have hVP' : V < (P : Subgroup X).map X.subtype := by
    refine lt_of_le_of_ne (fun v hv => ⟨⟨v, hVX hv⟩, hVP hv, rfl⟩) ?_
    intro heq
    apply hnot
    intro x hx
    have hx' : (x : G) ∈ V := by
      rw [heq]
      exact ⟨x, hx, rfl⟩
    exact hx'
  obtain ⟨y, hyP, hyN, hyV⟩ := qdd_exists_mem_normalizer_not_mem hP2 hVP'
  have hyC := hcon y (Subgroup.map_subtype_le _ hyP) hyN
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) := hP2.to_le (Subgroup.zpowers_le.mpr hyP)
  exact hyV (qdd_le_of_le_centralizer hn S f V hy2 (Subgroup.zpowers_le.mpr hyC)
    (Subgroup.mem_zpowers y))

private theorem qdd_isSolvable_of_normalizer_le (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {H X V : Subgroup G} [IsKleinFour V] (hXH : X ≤ H)
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) (hVX : V ≤ X)
    (hcon : ∀ x ∈ X, x ∈ Subgroup.normalizer (V : Set G) →
      x ∈ Subgroup.centralizer (V : Set G)) :
    Group.IsSolvable H := by
  have h4 : Nat.card (V.subgroupOf X) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv, IsKleinFour.card_four]
  obtain ⟨P, hPV⟩ := qdd_sylow_of_normalizer_le hn S f hVX hcon
  have hPN : Subgroup.normalizer ((P : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    intro x hx
    rw [hPV] at hx ⊢
    exact (qdd_mem_centralizer_subgroupOf_iff hVX).mpr
      (hcon x x.2 ((qdd_mem_normalizer_subgroupOf_iff hVX).mp hx))
  obtain ⟨K, hKn, hK2, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hPN
  have hXs : Group.IsSolvable X := by
    have : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr
      (Nat.two_dvd_ne_zero.mp hK2))
    have : Group.IsSolvable (X ⧸ K) := by
      have hq : IsPGroup 2 (X ⧸ K) := IsPGroup.of_card (n := 2) (by
        rw [← Subgroup.index_eq_card, hKidx, hPV, h4]
        norm_num)
      have := hq.isNilpotent
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient K
  have hcard : Nat.card V = 2 ^ (Nat.card X).factorization 2 := by
    rw [← Sylow.card_eq_multiplicity P, hPV,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv]
  have hXn : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX
  have hF := Local.sup_inf_normalizer_eq hXH hXn hVX hcard
  have hNs : Group.IsSolvable (H ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) := by
    have := qdd_isSolvable_normalizer hn S f V
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_right : H ⊓ Subgroup.normalizer (V : Set G) ≤ _))
  have hXHs : Group.IsSolvable (X.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXH).toMonoidHom) (MulEquiv.injective _)
  have hq : Group.IsSolvable (H ⧸ X.subgroupOf H) := by
    let φ : (H ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) →* H ⧸ X.subgroupOf H :=
      (QuotientGroup.mk' (X.subgroupOf H)).comp (Subgroup.inclusion inf_le_left)
    refine Group.isSolvable_of_surjective (f := φ) ?_
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have htop : (H ⊓ Subgroup.normalizer (V : Set G)).subgroupOf H ⊔ X.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup inf_le_left hXH, sup_comm, hF, Subgroup.subgroupOf_self]
    obtain ⟨m, hm, x, hx, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (htop ▸ Subgroup.mem_top h)
    refine ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, ?_⟩
    change QuotientGroup.mk' (X.subgroupOf H) m = QuotientGroup.mk' (X.subgroupOf H) (m * x)
    rw [map_mul, show QuotientGroup.mk' (X.subgroupOf H) x = 1 from
      (QuotientGroup.eq_one_iff x).mpr hx, mul_one]
  exact Group.isSolvable_of_subgroup_quotient (X.subgroupOf H)

private theorem qdd_card_le_eight (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {H X V : Subgroup G} [IsKleinFour V]
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) (hVX : V ≤ X) (P : Sylow 2 X)
    (hPV : (P : Subgroup X) = V.subgroupOf X) {Q : Subgroup G} (hQH : Q ≤ H)
    (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q) : Nat.card Q ≤ 8 := by
  have hQX : Q ⊓ X = V := by
    have hR : IsPGroup 2 ((Q ⊓ X).subgroupOf X) :=
      (hQ.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hle : (P : Subgroup X) ≤ (Q ⊓ X).subgroupOf X := by
      rw [hPV]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hVQ (Subgroup.mem_subgroupOf.mp hx),
        Subgroup.mem_subgroupOf.mp hx |> hVX⟩
    have heq := P.is_maximal' hR hle
    rw [hPV] at heq
    apply le_antisymm _ (le_inf hVQ hVX)
    intro x hx
    have hx' : (⟨x, hx.2⟩ : X) ∈ (Q ⊓ X).subgroupOf X := Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at hx'
    exact Subgroup.mem_subgroupOf.mp hx'
  have hQN : Q ≤ Subgroup.normalizer (V : Set G) := by
    intro q hq
    rw [← hQX]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact ⟨Q.mul_mem (Q.mul_mem hq hy.1) (Q.inv_mem hq),
        (Subgroup.mem_normalizer_iff.mp (hHX (hQH hq)) y).mp hy.2⟩
    · intro hy
      have h1 : y = q⁻¹ * (q * y * q⁻¹) * q := by group
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hHX (hQH hq)) y).mpr hy.2⟩
      rw [h1]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hy.1) hq
  obtain ⟨S₂, hQS₂⟩ := hQ.exists_le_sylow
  obtain ⟨-, h8, -⟩ := Local.kleinFour_sylow_facts hn S₂ (f.trans (Sylow.equiv S S₂)) V
    (hVQ.trans hQS₂)
  rw [← h8]
  exact Subgroup.card_le_of_le (le_inf hQS₂ hQN)

private theorem qdd_sixteen_le_card_sylow {K : Type*} [Group K] [Finite K] (hQD : IsQDGroup K)
    (Q : Sylow 2 K) : 16 ≤ Nat.card Q := by
  rcases exists_sylow_model hQD.sylow Q with ⟨m, hm, ⟨fQ⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · rw [← Nat.card_congr fQ.toEquiv, CFSG.Semidihedral.card m (by omega)]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · rw [Nat.card_congr e.toEquiv, Wreathed.card_wreath]
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    nlinarith

private theorem qdd_three_dvd_automizerIndex_of_isQDGroup (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {H V : Subgroup G} [IsKleinFour V] (hVH : V ≤ H)
    (hQD : IsQDGroup H) : 3 ∣ automizerIndex (V.subgroupOf H) := by
  have : IsKleinFour (V.subgroupOf H) :=
    Local.isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  have hV2 : IsPGroup 2 (V.subgroupOf H) :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨Q, hVQ⟩ := hV2.exists_le_sylow
  rcases exists_sylow_model hQD.sylow Q with ⟨m, hm, ⟨fQ⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · have ha : IsConj (FocalFusion.ambientHom m (Q : Subgroup H) fQ (s m))
        (FocalFusion.ambientHom m (Q : Subgroup H) fQ (z m)) :=
      hQD.involutions_isConj _ _ (by rw [orderOf_ambientHom, orderOf_s m (by omega)])
        (by rw [orderOf_ambientHom, orderOf_z m (by omega)])
    have h6 := automizerIndex_qdFour_eq_six hm Q fQ ha
    obtain ⟨w, -, hw⟩ := exists_conj_eq_qdFour hm (Q : Subgroup H) fQ (V.subgroupOf H) hVQ
    rw [hw, automizerIndex_eq_card_range, Local.card_normalizerMonoidHom_range_map_conj,
      ← automizerIndex_eq_card_range, h6]
    norm_num
  · exfalso
    have huZ : Wreathed.wreathModelHom Q e (Wreathed.Original.a (2 ^ m)) ∈
        centerOf (Q : Subgroup H) := by
      rw [centerOf_eq_modelCenter hm Q e]
      exact ⟨_, Subgroup.mem_zpowers _, rfl⟩
    have huC : (Wreathed.wreathModelHom Q e (Wreathed.Original.a (2 ^ m)) : G) ∈
        Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h := Subgroup.mem_centralizer_iff.mp huZ.2 ⟨v, hVH hv⟩
        (hVQ (Subgroup.mem_subgroupOf.mpr hv))
      exact congrArg Subtype.val h
    have hu2 : IsPGroup 2 (Subgroup.zpowers
        (Wreathed.wreathModelHom Q e (Wreathed.Original.a (2 ^ m)) : G)) := by
      have hQ2 : IsPGroup 2 (((Q : Subgroup H).map H.subtype : Subgroup G)) :=
        Q.isPGroup'.map H.subtype
      exact hQ2.to_le (Subgroup.zpowers_le.mpr ⟨_, huZ.1, rfl⟩)
    have huV := qdd_le_of_le_centralizer hn S f V hu2 (Subgroup.zpowers_le.mpr huC)
      (Subgroup.mem_zpowers _)
    have ho : orderOf (Wreathed.wreathModelHom Q e (Wreathed.Original.a (2 ^ m)) : G) =
        2 ^ m := by
      rw [Subgroup.orderOf_coe, orderOf_wreathModelHom, Wreathed.Original.orderOf_a]
    have hsq : (Wreathed.wreathModelHom Q e (Wreathed.Original.a (2 ^ m)) : G) ^ 2 = 1 := by
      rw [pow_two]
      exact qdd_mul_self V huV
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [ho] at hdvd
    have h1 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega

end NormalSubgroups

section Frontier

variable {G : Type} [Group G]

private theorem qdd_frontier_T_facts {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    IsKleinFour (frontierSetting S fS t p f).T ∧
      (frontierSetting S fS t p f).T ≤ (frontierSetting S fS t p f).D := by
  refine ⟨?_, le_inf ?_ Subgroup.le_normalizer⟩
  · rw [frontierSetting_T hn S fS t ht p f]
    exact qdFour_isKleinFour hn _ fS
  · rw [frontierSetting_T hn S fS t ht p f]
    exact qdFour_le _ fS

end Frontier

theorem frontier_solvable_dgroup_signalizer {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ H : Subgroup G, (frontierSetting S fS t p f).D ≤ H →
      IsDGroupWrt ((frontierSetting S fS t p f).T.subgroupOf H) →
      Group.IsSolvable H → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ X : Subgroup G, X ≤ H →
        IsPGroup r X → (frontierSetting S fS t p f).T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H := by
  intro H hDH hDW hsolv ℓ hℓ hℓ2 X hXH hX hTX
  obtain ⟨hK, hTD⟩ := qdd_frontier_T_facts hn S fS t ht p f
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hXodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
    rw [hk]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  exact qdd_le_oddCoreIn_of_isSolvable hn S fS (hTD.trans hDH) hDW.2.2 hsolv hXH hXodd hTX

theorem frontier_normal_contains_three {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ H : Subgroup G, (frontierSetting S fS t p f).D ≤ H →
      (IsQDGroup H ∨ (IsDGroupWrt ((frontierSetting S fS t p f).T.subgroupOf H) ∧
        ¬ Group.IsSolvable H)) →
      ∀ X : Subgroup G, X ≤ H → H ≤ Subgroup.normalizer (X : Set G) →
        (frontierSetting S fS t p f).T ≤ X →
          ∃ T₁ : Subgroup G, T₁ ≤ X ∧ IsKleinFour T₁ ∧
            3 ∣ automizerIndex (T₁.subgroupOf X) := by
  intro H hDH hH X hXH hHX hTX
  obtain ⟨hK, hTD⟩ := qdd_frontier_T_facts hn S fS t ht p f
  have hTH := hTD.trans hDH
  refine ⟨_, hTX, hK, ?_⟩
  have h3H : 3 ∣ automizerIndex ((frontierSetting S fS t p f).T.subgroupOf H) := by
    rcases hH with hQD | ⟨hDW, -⟩
    · exact qdd_three_dvd_automizerIndex_of_isQDGroup hn S fS hTH hQD
    · exact hDW.2.2
  obtain ⟨g, hgH, hgN, hg3, hg1⟩ := qdd_exists_of_three_dvd_automizerIndex_subgroupOf hTH h3H
  have hgfree := qdd_fixedPointFree_of_cube _ hgN hg3 hg1
  obtain ⟨x, hxX, hxN, hx1⟩ : ∃ x ∈ X, x ∈ Subgroup.normalizer
      ((frontierSetting S fS t p f).T : Set G) ∧
      x ∉ Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) := by
    by_contra hcon
    push Not at hcon
    rcases hH with hQD | ⟨-, hns⟩
    · obtain ⟨P, hPV⟩ := qdd_sylow_of_normalizer_le hn S fS hTX hcon
      have hT2 : IsPGroup 2 ((frontierSetting S fS t p f).T.subgroupOf H) :=
        IsPGroup.of_card (n := 2) (by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, IsKleinFour.card_four]
          norm_num)
      obtain ⟨Q, hTQ⟩ := hT2.exists_le_sylow
      have h16 := qdd_sixteen_le_card_sylow hQD Q
      have h8 := qdd_card_le_eight hn S fS hHX hTX P hPV (Subgroup.map_subtype_le _)
        (Q.isPGroup'.map H.subtype) (fun v hv => ⟨⟨v, hTH hv⟩, hTQ hv, rfl⟩)
      rw [Subgroup.card_map_of_injective H.subtype_injective] at h8
      omega
    · exact hns (qdd_isSolvable_of_normalizer_le hn S fS hXH hHX hTX hcon)
  exact qdd_three_dvd_of_normal hHX hTX hgH hgN hgfree hxX hxN hx1

end CFSG.Semidihedral.AllPrime
