module

public import CFSG.GH74.GLS.Stage2.Local.P27M12Basic
public import CFSG.GH74.GLS.Stage2.Local.P27.FullG
public import CFSG.GH74.GLS.Stage2.Local.P34S5Jbar
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCov
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.NCDm12

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.L52Two

section Four

variable {G : Type} [Group G]

@[expose] def fourSg (x y : G) : Subgroup G := Subgroup.closure {x, y}

theorem mem_fourSg {x y : G} (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) {g : G} :
    g ∈ fourSg x y ↔ g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  unfold fourSg
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have e1 : x * (x * y) = y := by rw [← mul_assoc, hx2, one_mul]
  have e2 : y * (x * y) = x := by
    calc y * (x * y) = (y * x) * y := (mul_assoc _ _ _).symm
      _ = (x * y) * y := by rw [← hxy]
      _ = x * (y * y) := mul_assoc _ _ _
      _ = x := by rw [hy2, mul_one]
  have e3 : x * y * x = y := by
    calc x * y * x = x * (y * x) := mul_assoc _ _ _
      _ = x * (x * y) := by rw [← hxy]
      _ = y := e1
  have e4 : x * y * y = x := by rw [mul_assoc, hy2, mul_one]
  have e5 : x * y * (x * y) = 1 := by
    calc x * y * (x * y) = (x * y * x) * y := (mul_assoc _ _ _).symm
      _ = y * y := by rw [e3]
      _ = 1 := hy2
  have e6 : y * x = x * y := hxy.symm
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl (Set.mem_singleton_iff.1 ha)))
    | one => exact Or.inl rfl
    | mul a b _ _ ha hb =>
      rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
        simp [hx2, hy2, e1, e2, e3, e4, e5, e6]
    | inv a _ ha =>
      rcases ha with ha | ha | ha | ha <;> rw [ha]
      · simp
      · simp [hxi]
      · simp [hyi]
      · have : (x * y)⁻¹ = x * y := by rw [mul_inv_rev, hxi, hyi, e6]
        simp [this]
  · intro h
    rcases h with h | h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem x_mem_fourSg (x y : G) : x ∈ fourSg x y :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem y_mem_fourSg (x y : G) : y ∈ fourSg x y :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem isKleinFour_fourSg {x y : G} (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) : IsKleinFour ↥(fourSg x y) := by
  have hmem := fun g : G => mem_fourSg hx2 hy2 hxy (g := g)
  have hxy1 : x * y ≠ 1 := by
    intro h
    exact hne ((mul_eq_one_iff_eq_inv.1 h).trans (inv_eq_of_mul_eq_one_right hy2))
  have hxyx : x * y ≠ x := by
    intro h
    apply hy1
    simpa using h
  have hxyy : x * y ≠ y := by
    intro h
    apply hx1
    simpa using h
  have hset : (fourSg x y : Set G) = {1, x, y, x * y} := by
    ext g
    simp only [SetLike.mem_coe, hmem, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hcard : Nat.card ↥(fourSg x y) = 4 := by
    have h1 : Nat.card ↥(fourSg x y) = (fourSg x y : Set G).ncard :=
      Nat.card_coe_set_eq (fourSg x y : Set G)
    rw [h1, hset]
    have n1 : (1 : G) ∉ ({x, y, x * y} : Set G) := by simp [hx1.symm, hy1.symm, hxy1.symm]
    have n2 : x ∉ ({y, x * y} : Set G) := by simp [hne, hxyx.symm]
    have n3 : y ∉ ({x * y} : Set G) := by simp [hxyy.symm]
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_insert_of_notMem n3,
      Set.ncard_singleton]
  refine ⟨hcard, ?_⟩
  have hsq : ∀ g : ↥(fourSg x y), g ^ 2 = 1 := by
    intro g
    apply Subtype.ext
    have hg := (hmem g).1 g.2
    show (g : G) ^ 2 = 1
    have e5 : x * y * (x * y) = 1 := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    rcases hg with h | h | h | h <;> rw [h]
    · simp
    · rw [pow_two]; exact hx2
    · rw [pow_two]; exact hy2
    · rw [pow_two]; exact e5
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with h | h
  · have : Subsingleton ↥(fourSg x y) := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : ↥(fourSg x y))
    omega
  · exact h

theorem isPGroup_fourSg {x y : G} (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) : IsPGroup 2 ↥(fourSg x y) := by
  have := isKleinFour_fourSg hx2 hy2 hxy hx1 hy1 hne
  exact IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)

theorem isDihedral_fourSg {x y : G} (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) : IsDihedral ↥(fourSg x y) := by
  have := isKleinFour_fourSg hx2 hy2 hxy hx1 hy1 hne
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥(fourSg x y)) (G₂ := DihedralGroup 2)
  exact ⟨4, 2, rfl, le_rfl, ⟨e⟩⟩

end Four

section Sylow

variable {G : Type} [Group G]

theorem exists_isSylowOf_ge {C P : Subgroup G} (hPC : P ≤ C) (hP : IsPGroup 2 ↥P) :
    ∃ T : Subgroup G, IsSylowOf 2 T C ∧ P ≤ T := by
  have hP' : IsPGroup 2 ↥(P.subgroupOf C) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥C).map C.subtype, ⟨Q, rfl⟩, fun p hp => ?_⟩
  exact ⟨⟨p, hPC hp⟩, hQ (Subgroup.mem_subgroupOf.2 hp), rfl⟩

theorem odd_orderOf_of_mem {N : Subgroup G} (hN : Odd (Nat.card ↥N)) {n : G} (hn : n ∈ N) :
    Odd (orderOf n) :=
  Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard _ hn)

theorem inf_sup_le_of_normalizes {N J T C : Subgroup G} (hNC : C ≤ normalizer (N : Set G))
    (hJC : J ≤ C) (hJn : C ≤ normalizer (J : Set G)) (hTC : T ≤ C) (hN : Odd (Nat.card ↥N))
    (hT : IsPGroup 2 ↥T) : T ⊓ (N ⊔ J) ≤ J := by
  intro m hm
  obtain ⟨hmT, hmNJ⟩ := Subgroup.mem_inf.1 hm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N J (hJC.trans hNC)] at hmNJ
  obtain ⟨n, hn, j, hj, hnj⟩ := hmNJ
  have hzpT : zpowers m ≤ T := (Subgroup.zpowers_le).2 hmT
  have hzp : IsPGroup 2 ↥(zpowers m) := hT.to_le hzpT
  have hmem : n ∈ J ⊔ zpowers m := by
    have h1 : m * j⁻¹ ∈ zpowers m ⊔ J := Subgroup.mul_mem_sup (Subgroup.mem_zpowers m) (J.inv_mem hj)
    have h2 : n = m * j⁻¹ := by rw [← hnj]; group
    rw [h2, sup_comm]
    exact h1
  obtain ⟨k, hk⟩ := exists_pow_mem_of_sup (L := J) (T := zpowers m) hzp
    (fun g hg => hJn (hTC (hzpT hg))) hmem
  have hnJ : n ∈ J := mem_of_odd_orderOf_of_pow_mem (odd_orderOf_of_mem hN hn) hk
  rw [← hnj]
  exact J.mul_mem hnJ hj

theorem mem_zpowers_of_mul_odd {x u n : G} (hx2 : x * x = 1) (hxu : x * u = u * x)
    (hn : Odd (orderOf n)) (hnxu : n = x * u) : x ∈ zpowers u := by
  obtain ⟨k, hk⟩ := hn
  have hcomm : Commute x u := hxu
  have h1 : n ^ orderOf n = 1 := pow_orderOf_eq_one n
  rw [hk, hnxu, hcomm.mul_pow] at h1
  have hxp : x ^ (2 * k + 1) = x := by
    rw [pow_succ, pow_mul, pow_two, hx2, one_pow, one_mul]
  rw [hxp] at h1
  have h2 : x = (u ^ (2 * k + 1))⁻¹ := mul_eq_one_iff_eq_inv.1 h1
  rw [h2]
  exact (zpowers u).inv_mem ((zpowers u).pow_mem (Subgroup.mem_zpowers u) _)

theorem fourSg_inf_le_bot {N K : Subgroup G} {x y : G} (hN : Odd (Nat.card ↥N))
    (hKN : K ≤ normalizer (N : Set G)) (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (hxK : ∀ k ∈ K, x * k = k * x) (hKy : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hyK : y ∉ K)
    (hxL : x ∉ K ⊔ zpowers y) : fourSg x y ⊓ (N ⊔ K) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg4, hgNK⟩
  rw [Subgroup.mem_bot]
  have hyL : y ∈ K ⊔ zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hdec : ∀ {g : G}, g ∈ N ⊔ K → ∃ n ∈ N, ∃ k ∈ K, n * k = g := by
    intro g hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N K hKN] at hg
    exact Set.mem_mul.1 hg
  rcases (mem_fourSg hx2 hy2 hxy).1 hg4 with h | h | h | h
  · exact h
  ·
    exfalso
    rw [h] at hgNK
    obtain ⟨n, hn, k, hk, hnk⟩ := hdec hgNK
    have hnx : n = x * k⁻¹ := eq_mul_inv_of_mul_eq hnk
    have hc : x * k⁻¹ = k⁻¹ * x := hxK _ (K.inv_mem hk)
    have hxz : x ∈ zpowers k⁻¹ := mem_zpowers_of_mul_odd hx2 hc (odd_orderOf_of_mem hN hn) hnx
    exact hxL (Subgroup.mem_sup_left ((Subgroup.zpowers_le).2 (K.inv_mem hk) hxz))
  ·
    exfalso
    rw [h] at hgNK
    obtain ⟨n, hn, k, hk, hnk⟩ := hdec hgNK
    have hny : n = y * k⁻¹ := eq_mul_inv_of_mul_eq hnk
    have hsq : n ^ 2 ^ 1 ∈ K := by
      have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have h1 : n ^ 2 ^ 1 = (y * k⁻¹ * y⁻¹) * k⁻¹ := by
        rw [pow_one, pow_two, hny, hyi]
        group
      rw [h1]
      exact K.mul_mem (hKy _ (K.inv_mem hk)) (K.inv_mem hk)
    have hnK : n ∈ K := mem_of_odd_orderOf_of_pow_mem (odd_orderOf_of_mem hN hn) hsq
    apply hyK
    rw [← hnk]
    exact K.mul_mem hnK hk
  ·
    exfalso
    rw [h] at hgNK
    obtain ⟨n, hn, k, hk, hnk⟩ := hdec hgNK
    have hnx : n = x * (y * k⁻¹) := by
      have := eq_mul_inv_of_mul_eq hnk
      rw [this]
      group
    have hc : x * (y * k⁻¹) = (y * k⁻¹) * x := by
      have hk' : x * k⁻¹ = k⁻¹ * x := hxK _ (K.inv_mem hk)
      calc x * (y * k⁻¹) = (x * y) * k⁻¹ := (mul_assoc _ _ _).symm
        _ = (y * x) * k⁻¹ := by rw [hxy]
        _ = y * (x * k⁻¹) := mul_assoc _ _ _
        _ = y * (k⁻¹ * x) := by rw [hk']
        _ = (y * k⁻¹) * x := (mul_assoc _ _ _).symm
    have hxz : x ∈ zpowers (y * k⁻¹) := mem_zpowers_of_mul_odd hx2 hc (odd_orderOf_of_mem hN hn) hnx
    have hu : y * k⁻¹ ∈ K ⊔ zpowers y :=
      Subgroup.mul_mem _ hyL (Subgroup.mem_sup_left (K.inv_mem hk))
    exact hxL ((Subgroup.zpowers_le).2 hu hxz)

end Sylow

section PGL

variable {G : Type} [Group G] [Finite G]

theorem five_le_of_isL2 {X K : Subgroup G} {q : ℕ} (hKc : IsPCompIn 2 X K)
    (hKL2 : IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q)) (hq8 : q % 8 = 3 ∨ q % 8 = 5) :
    5 ≤ q := by
  by_contra hlt
  obtain ⟨F₀, iF₀, fF₀, hF₀, ⟨e₀⟩⟩ := hKL2
  have h3 : Nat.card F₀ ≤ 3 := by omega
  have hsol : Group.IsSolvable (GorensteinWalter.PSL2 F₀) := P34.psl2_solvable_of_card_le_three h3
  have hsol' : Group.IsSolvable (↥K ⧸ pPrimeCore 2 ↥K) :=
    Group.isSolvable_of_surjective (f := (e₀.trans (IVK.L2.equivPSL F₀)).symm.toMonoidHom)
      (e₀.trans (IVK.L2.equivPSL F₀)).symm.surjective
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple
    (TwoThin.isQuasisimple_hat hKc) hsol'

theorem not_mem_of_pgl {K : Subgroup G} {y : G} {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hL : IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q)) (hP : PGLModO K (zpowers y) q) :
    y ∉ K := by
  classical
  obtain ⟨hN, F₁, iF₁, fF₁, hF₁, ⟨e⟩⟩ := hP
  obtain ⟨F₀, iF₀, fF₀, hF₀, ⟨e₀⟩⟩ := hL
  set A : Subgroup G := K ⊔ zpowers y with hA
  set O' : Subgroup G := pPrimeCoreOf 2 K with hO'
  have hKA : K ≤ A := le_sup_left
  have hO'K : O' ≤ K := TwoThin.pPrimeCoreOf_le K
  have hO'A : O' ≤ A := hO'K.trans hKA
  have hL0 : IVK.L2Field F₀ := ⟨by rw [hF₀]; exact hq, by rw [hF₀]; omega⟩
  have hL1 : IVK.L2Field F₁ := ⟨by rw [hF₁]; exact hq, by rw [hF₁]; omega⟩
  have hcardPSL : Nat.card (GorensteinWalter.PSL2 F₁) = Nat.card (GorensteinWalter.PSL2 F₀) := by
    rw [GorensteinWalter.psl2_card_formula F₁ (IVK.isOddPrimePower_of_L2Field hL1),
      GorensteinWalter.psl2_card_formula F₀ (IVK.isOddPrimePower_of_L2Field hL0), hF₀, hF₁]
  have hcardK : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = Nat.card (GorensteinWalter.PSL2 F₀) :=
    Nat.card_congr (e₀.trans (IVK.L2.equivPSL F₀)).toEquiv
  have hcardAbar : Nat.card (↥A ⧸ O'.subgroupOf A) = 2 * Nat.card (GorensteinWalter.PSL2 F₀) := by
    rw [Nat.card_congr e.toEquiv, IVK.card_pgl2_eq_two_mul hL1, hcardPSL]
  have hO'card : Nat.card ↥(O'.subgroupOf A) = Nat.card ↥(pPrimeCore 2 ↥K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO'A).toEquiv, hO']
    exact Subgroup.card_map_of_injective K.subtype_injective
  have hcardA : Nat.card ↥A = Nat.card ↥(pPrimeCore 2 ↥K) * (2 * Nat.card (GorensteinWalter.PSL2 F₀)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (O'.subgroupOf A), hcardAbar, hO'card]
    ring
  have hcardK' : Nat.card ↥K = Nat.card ↥(pPrimeCore 2 ↥K) * Nat.card (GorensteinWalter.PSL2 F₀) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K), hcardK]
    ring
  have hpos : 0 < Nat.card ↥(pPrimeCore 2 ↥K) * Nat.card (GorensteinWalter.PSL2 F₀) := by
    rw [← hcardK']
    exact Nat.card_pos
  intro hyK
  have hAK : A ≤ K := sup_le le_rfl ((Subgroup.zpowers_le).2 hyK)
  have hAeq : A = K := le_antisymm hAK hKA
  have hcardeq : Nat.card ↥A = Nat.card ↥K := by rw [hAeq]
  rw [hcardA, hcardK'] at hcardeq
  nlinarith [hpos]

end PGL

section Dih

variable {G : Type} [Group G] [Finite G]

theorem isDihedral_inf_Jx {x : G} {T : Subgroup G} {q : ℕ}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hq : Odd q)
    (hL2J : IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q)) :
    IsDihedral ↥(T ⊓ Jx x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDih : P34.DihJ (HBar (Jx x)) := by
    obtain ⟨F, iF, fF, hF, e⟩ := hL2J
    exact Or.inl ⟨F, iF, fF, by rw [hF]; exact hq, e⟩
  have hS : IsSylowOf 2 (T ⊓ Jx x) (Jx x) :=
    hT.inf_of_le_normalizer (P34.Jx_le_centralizer x) (le_normalizer_pLayerOf _)
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  let π : ↥(Jx x) →* HBar (Jx x) := QuotientGroup.mk' (pPrimeCore 2 ↥(Jx x))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let S : Sylow 2 (HBar (Jx x)) := Sylow.mapSurjective hπ Q
  have hSm : (S : Subgroup (HBar (Jx x))) = (Q : Subgroup ↥(Jx x)).map π := rfl
  obtain ⟨m, hm, ⟨d⟩⟩ := hDih.hasDihedralSylowTwo S
  have hinj : Function.Injective (π.comp (Q : Subgroup ↥(Jx x)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : π (a : ↥(Jx x)) = 1 := ha
    have hO : (a : ↥(Jx x)) ∈ pPrimeCore 2 ↥(Jx x) := (QuotientGroup.eq_one_iff _).1 ha'
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 Q.isPGroup' a
    have hd1 : orderOf (a : ↥(Jx x)) ∣ Nat.card ↥(pPrimeCore 2 ↥(Jx x)) :=
      Subgroup.orderOf_dvd_natCard _ hO
    have hd2 : orderOf (a : ↥(Jx x)) = 2 ^ k := (Subgroup.orderOf_coe a).trans hk
    rw [hd2] at hd1
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(pPrimeCore 2 ↥(Jx x))) :=
      Nat.Coprime.pow_left k pPrimeCore_coprime_card
    have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop hd1
    exact orderOf_eq_one_iff.1 (hk.trans h1)
  have hrange : (π.comp (Q : Subgroup ↥(Jx x)).subtype).range = (Q : Subgroup ↥(Jx x)).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eB : ↥(Q : Subgroup ↥(Jx x)) ≃* ↥(S : Subgroup (HBar (Jx x))) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hrange.trans hSm.symm))
  let eA : ↥(T ⊓ Jx x) ≃* ↥(Q : Subgroup ↥(Jx x)) :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ Jx x ≤ Jx x)).symm.trans
      (MulEquiv.subgroupCongr hQ.symm)
  refine ⟨2 * 2 ^ m, 2 ^ m, rfl, ?_, ⟨eA.trans (eB.trans d)⟩⟩
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

end Dih

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.NCDm12
