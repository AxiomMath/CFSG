module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec7l771_inv_mul_comm {x y : G} (h : x * y = y * x) : x⁻¹ * y = y * x⁻¹ := by
  calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
    _ = x⁻¹ * (x * y) * x⁻¹ := by rw [← h]
    _ = y * x⁻¹ := by group

private def sec7l771_infSubgroupOfEquiv (A C : Subgroup G) :
    C.subgroupOf A ≃ (A ⊓ C : Subgroup G) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sec7l771_comm_mem [Finite G] {K : Subgroup G}
    (hZ : K ⊓ centralizer (K : Set G) = ⊥)
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (K : Set G)) → IsCyclic P)
    (hout : ∀ x ∈ normalizer (K : Set G), Odd (orderOf x) → InnerOn K x)
    {s b ν : G} (hs : s ∈ centralizer (K : Set G)) (hs2 : orderOf s = 2)
    (hb : b ∈ normalizer (K : Set G)) (hν : ν ∈ normalizer (K : Set G))
    (hbs : b * s = s * b) (hνs : ν * s = s * ν) (hν3 : ν ^ 3 = 1)
    (hbν : (b * (ν * b⁻¹ * ν⁻¹)) ^ 2 = 1) :
    b * (ν * b⁻¹ * ν⁻¹) ∈ K := by
  classical
  have hνodd : Odd (orderOf ν) :=
    Odd.of_dvd_nat (by norm_num) (orderOf_dvd_of_pow_eq_one hν3)
  obtain ⟨l, hl, c, hc, hdecomp⟩ := innerOn_decompose (hout ν hν hνodd)
  have hcomm_lc : Commute l c := Subgroup.mem_centralizer_iff.mp hc l hl
  have hν3lc : (l * c) ^ 3 = 1 := by rw [← hdecomp]; exact hν3
  have hl3c3 : l ^ 3 * c ^ 3 = 1 := by rw [← hcomm_lc.mul_pow 3]; exact hν3lc
  have hl3 : l ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hl3c3
  have hl3one : l ^ 3 = 1 := by
    have hmem : l ^ 3 ∈ (⊥ : Subgroup G) := by
      rw [← hZ]
      exact ⟨pow_mem hl 3,
        by rw [hl3]; exact (centralizer (K : Set G)).inv_mem (pow_mem hc 3)⟩
    exact Subgroup.mem_bot.mp hmem
  have hc3one : c ^ 3 = 1 := by
    rw [hl3one, one_mul] at hl3c3
    exact hl3c3
  set c₁ : G := b * c * b⁻¹ with hc₁def
  set l₁ : G := b * l * b⁻¹ with hl₁def
  set c' : G := c₁ * c⁻¹ with hc'def
  set k : G := l₁ * l⁻¹ with hkdef
  have hc1C : c₁ ∈ centralizer (K : Set G) := by
    rw [hc₁def]
    have hbinv : b⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem hb
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hyb : b⁻¹ * y * b ∈ K := by
      have h := (Subgroup.mem_normalizer_iff.mp hbinv y).mp hy
      simpa using h
    have hxy := hc (b⁻¹ * y * b) hyb
    calc y * (b * c * b⁻¹) = b * ((b⁻¹ * y * b) * c) * b⁻¹ := by group
      _ = b * (c * (b⁻¹ * y * b)) * b⁻¹ := by rw [hxy]
      _ = (b * c * b⁻¹) * y := by group
  have hl1K : l₁ ∈ K := by
    rw [hl₁def]
    exact (Subgroup.mem_normalizer_iff.mp hb l).mp hl
  have hc'C : c' ∈ centralizer (K : Set G) := by
    rw [hc'def]
    exact (centralizer (K : Set G)).mul_mem hc1C ((centralizer (K : Set G)).inv_mem hc)
  have hkK : k ∈ K := by
    rw [hkdef]
    exact K.mul_mem hl1K (K.inv_mem hl)
  have hkc' : k * c' = c' * k := Subgroup.mem_centralizer_iff.mp hc'C k hkK
  have hcomm_c'l : c' * l⁻¹ = l⁻¹ * c' :=
    (Subgroup.mem_centralizer_iff.mp hc'C l⁻¹ (K.inv_mem hl)).symm
  have hstep1 : b * (ν * b⁻¹ * ν⁻¹) = l₁ * c' * l⁻¹ := by
    rw [hdecomp, mul_inv_rev, hl₁def, hc'def, hc₁def]
    group
  have hstep2 : l₁ * c' * l⁻¹ = k * c' := by
    rw [mul_assoc, hcomm_c'l, ← mul_assoc, ← hkdef]
  have hbν_eq : b * (ν * b⁻¹ * ν⁻¹) = k * c' := hstep1.trans hstep2
  have hkc2 : (k * c') ^ 2 = 1 := by rw [← hbν_eq]; exact hbν
  have hk2c2 : k ^ 2 * c' ^ 2 = 1 := by
    rw [← (show Commute k c' from hkc').mul_pow 2]
    exact hkc2
  have hk2 : k ^ 2 = (c' ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hk2c2
  have hk2one : k ^ 2 = 1 := by
    have hmem : k ^ 2 ∈ (⊥ : Subgroup G) := by
      rw [← hZ]
      exact ⟨pow_mem hkK 2,
        by rw [hk2]; exact (centralizer (K : Set G)).inv_mem (pow_mem hc'C 2)⟩
    exact Subgroup.mem_bot.mp hmem
  have hc'2 : c' * c' = 1 := by
    have h := hk2c2
    rw [hk2one, one_mul] at h
    simpa [pow_two] using h
  have hsl : l * s = s * l := Subgroup.mem_centralizer_iff.mp hs l hl
  have hcsl : c * s = s * c := by
    have hc_eq : c = l⁻¹ * ν := by rw [hdecomp]; group
    rw [hc_eq]
    calc (l⁻¹ * ν) * s = l⁻¹ * (ν * s) := by group
      _ = l⁻¹ * (s * ν) := by rw [hνs]
      _ = (l⁻¹ * s) * ν := by group
      _ = (s * l⁻¹) * ν := by rw [sec7l771_inv_mul_comm hsl]
      _ = s * (l⁻¹ * ν) := by group
  have hbs_inv : b⁻¹ * s = s * b⁻¹ := sec7l771_inv_mul_comm hbs
  have hcs_inv : c⁻¹ * s = s * c⁻¹ := sec7l771_inv_mul_comm hcsl
  have hc1s : c₁ * s = s * c₁ := by
    rw [hc₁def]
    calc (b * c * b⁻¹) * s = b * c * (b⁻¹ * s) := by group
      _ = b * c * (s * b⁻¹) := by rw [hbs_inv]
      _ = b * (c * s) * b⁻¹ := by group
      _ = b * (s * c) * b⁻¹ := by rw [hcsl]
      _ = (b * s) * c * b⁻¹ := by group
      _ = (s * b) * c * b⁻¹ := by rw [← hbs]
      _ = s * (b * c * b⁻¹) := by group
  have hc's : c' * s = s * c' := by
    rw [hc'def]
    calc (c₁ * c⁻¹) * s = c₁ * (c⁻¹ * s) := by group
      _ = c₁ * (s * c⁻¹) := by rw [hcs_inv]
      _ = (c₁ * s) * c⁻¹ := by group
      _ = (s * c₁) * c⁻¹ := by rw [hc1s]
      _ = s * (c₁ * c⁻¹) := by group
  have hcase : c' = 1 ∨ c' = s :=
    eq_one_or_eq_of_commute hcyc hc'C hs hc'2 hs2 hc's
  rw [hbν_eq]
  rcases hcase with hc'1 | hc's_eq
  · rw [hc'1, mul_one]
    exact hkK
  · exfalso
    have hsne1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hs2
      omega
    have hss : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs2] at h
      simpa [pow_two] using h
    have hs3 : s ^ 3 = s := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, hss, one_mul]
    have hc1_s : c₁ = s * c := by
      rw [← hc's_eq, hc'def]
      group
    have hc1_cube : c₁ ^ 3 = 1 := by
      have hconj : b * c * b⁻¹ = (MulAut.conj b) c := by
        rw [MulAut.conj_apply]
      rw [hc₁def, hconj, ← map_pow, hc3one, map_one]
    have hsc_cube : (s * c) ^ 3 = s := by
      rw [(show Commute s c from hcsl.symm).mul_pow 3, hc3one, mul_one, hs3]
    exact hsne1 (by rw [← hsc_cube, ← (show c₁ ^ 3 = (s * c) ^ 3 from by rw [hc1_s]),
      hc1_cube])

theorem sec7l771_nu_to_l [Finite G] {K : Subgroup G}
    (hZ : K ⊓ centralizer (K : Set G) = ⊥)
    (hout : ∀ x ∈ normalizer (K : Set G), Odd (orderOf x) → InnerOn K x)
    {ν : G} (hν : ν ∈ normalizer (K : Set G)) (hν3 : ν ^ 3 = 1) :
    ∃ l ∈ K, l ^ 3 = 1 ∧ ∀ e ∈ K, l * e * l⁻¹ = ν * e * ν⁻¹ := by
  obtain ⟨l, hl, c, hc, hdecomp⟩ := innerOn_decompose
    (hout ν hν (Odd.of_dvd_nat (by norm_num) (orderOf_dvd_of_pow_eq_one hν3)))
  have hcomm_lc : Commute l c := Subgroup.mem_centralizer_iff.mp hc l hl
  have hν3lc : (l * c) ^ 3 = 1 := by rw [← hdecomp]; exact hν3
  have hl3c3 : l ^ 3 * c ^ 3 = 1 := by rw [← hcomm_lc.mul_pow 3]; exact hν3lc
  have hl3 : l ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hl3c3
  have hl3one : l ^ 3 = 1 := by
    have hmem : l ^ 3 ∈ (⊥ : Subgroup G) := by
      rw [← hZ]
      exact ⟨pow_mem hl 3,
        by rw [hl3]; exact (centralizer (K : Set G)).inv_mem (pow_mem hc 3)⟩
    exact Subgroup.mem_bot.mp hmem
  refine ⟨l, hl, hl3one, ?_⟩
  intro e he
  have hce : c * e = e * c := (Subgroup.mem_centralizer_iff.mp hc e he).symm
  have hact : (l * c) * e * (l * c)⁻¹ = l * e * l⁻¹ := by
    calc (l * c) * e * (l * c)⁻¹ = l * (c * e * c⁻¹) * l⁻¹ := by group
      _ = l * e * l⁻¹ := by
        have h : c * e * c⁻¹ = e := by rw [hce]; group
        rw [h]
  rw [hdecomp]
  exact hact.symm

theorem sec7l771_le_sylow [Finite G] {K P D : Subgroup G} (hP : IsSylow2Of P K) (hDK : D ≤ K)
    (hD : IsPGroup 2 D) (hN : P ≤ normalizer (D : Set G)) : D ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPSyl : CFSG.ABGLocalTools.IsSylowOf 2 P K :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hP
  have hsup : IsPGroup 2 ↥(P ⊔ D) := IsPGroup.to_sup_of_normal_right' hP.2.1 hD hN
  have heq : P ⊔ D = P :=
    CFSG.ABGLocalTools.IsSylowOf.eq_of_le hPSyl le_sup_left (sup_le hP.1 hDK) hsup
  rw [← heq]
  exact le_sup_right

theorem sec7l771_count [Finite G] {X C A : Subgroup G} (hAX : A ≤ X) (hX : C.relIndex X ≤ 32)
    (hA : 64 ≤ Nat.card A) (hAC2 : Nat.card ↥(A ⊓ C) = 2) :
    ∀ x ∈ X, ∃ a ∈ A, ∃ c ∈ C, x = a * c := by
  have hcardCA : Nat.card (C.subgroupOf A) = 2 :=
    (Nat.card_congr (sec7l771_infSubgroupOfEquiv A C)).trans hAC2
  have hidx : (C.subgroupOf A).index * 2 = Nat.card A := by
    have h := Subgroup.index_mul_card (C.subgroupOf A)
    rwa [hcardCA] at h
  have hdom : 32 ≤ Nat.card (A ⧸ C.subgroupOf A) := by
    change 32 ≤ (C.subgroupOf A).index
    omega
  have hcod : Nat.card (X ⧸ C.subgroupOf X) ≤ 32 := by
    simpa only [Subgroup.relIndex, Subgroup.index] using hX
  have hsurj : Function.Surjective
      (Subgroup.quotientSubgroupOfEmbeddingOfLE (s := A) (t := X) C hAX :
        A ⧸ C.subgroupOf A → X ⧸ C.subgroupOf X) := by
    have hinj : Function.Injective
        (Subgroup.quotientSubgroupOfEmbeddingOfLE (s := A) (t := X) C hAX :
          A ⧸ C.subgroupOf A → X ⧸ C.subgroupOf X) :=
      (Subgroup.quotientSubgroupOfEmbeddingOfLE (s := A) (t := X) C hAX).injective
    exact (hinj.bijective_of_nat_card_le (hcod.trans hdom)).2
  intro x hx
  obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk (⟨x, hx⟩ : X))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (s := C.subgroupOf A) q
  simp only [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk] at hq
  have hcX : (Subgroup.inclusion hAX a)⁻¹ * (⟨x, hx⟩ : X) ∈ C.subgroupOf X :=
    QuotientGroup.eq.mp hq
  have hcC : (a : G)⁻¹ * x ∈ C := by
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inclusion] using hcX
  exact ⟨(a : G), a.2, (a : G)⁻¹ * x, hcC, by group⟩

theorem sec7l771_mem_A [Finite G] {K A : Subgroup G}
    (hZ : K ⊓ centralizer (K : Set G) = ⊥)
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (K : Set G)) → IsCyclic P)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hA2 : ∀ a ∈ A, a * a = 1)
    {s : G} (hsA : s ∈ A) (hs : s ∈ centralizer (K : Set G)) (hs2 : orderOf s = 2)
    {a b c : G} (ha : a ∈ A) (hb : b ∈ K) (hc : c ∈ centralizer (K : Set G))
    (habc : a = b * c) : b ∈ A := by
  have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.mp hc b hb
  have hbbcc : (b * b) * (c * c) = 1 := by
    have h1 : (b * c) * (b * c) = (b * b) * (c * c) := by
      calc (b * c) * (b * c) = b * (c * b) * c := by group
        _ = b * (b * c) * c := by rw [hbc]
        _ = (b * b) * (c * c) := by group
    rw [← hA2 a ha, habc, h1]
  have hbb1 : b * b = 1 := by
    have hmemC : b * b ∈ centralizer (K : Set G) := by
      rw [eq_inv_of_mul_eq_one_left hbbcc]
      exact (centralizer (K : Set G)).inv_mem ((centralizer (K : Set G)).mul_mem hc hc)
    have hmem : b * b ∈ (⊥ : Subgroup G) := by
      rw [← hZ]
      exact ⟨mul_mem hb hb, hmemC⟩
    exact Subgroup.mem_bot.mp hmem
  have hcc1 : c * c = 1 := by
    have h := hbbcc
    rw [hbb1, one_mul] at h
    exact h
  have hcs : c * s = s * c := by
    have hc_eq : c = b⁻¹ * a := by rw [habc]; group
    have hbs' : b * s = s * b := Subgroup.mem_centralizer_iff.mp hs b hb
    have has : a * s = s * a := hAc a ha s hsA
    rw [hc_eq]
    calc (b⁻¹ * a) * s = b⁻¹ * (a * s) := by group
      _ = b⁻¹ * (s * a) := by rw [has]
      _ = (b⁻¹ * s) * a := by group
      _ = (s * b⁻¹) * a := by rw [sec7l771_inv_mul_comm hbs']
      _ = s * (b⁻¹ * a) := by group
  rcases eq_one_or_eq_of_commute hcyc hc hs hcc1 hs2 hcs with hc1 | hcseq
  · have hb_eq : b = a := by rw [habc, hc1, mul_one]
    rw [hb_eq]
    exact ha
  · have hss : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs2] at h
      simpa [pow_two] using h
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hb_eq0 : b = a * c⁻¹ := by rw [habc]; group
    have hb_eq : b = a * s := by rw [hb_eq0, hcseq, hsinv]
    rw [hb_eq]
    exact A.mul_mem ha hsA

end CFSG.OddStandard.SmallF3.Omega
