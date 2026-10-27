module

public import CFSG.CGT.T75H.Split

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjPerm (T H : Subgroup G) (hH : H ≤ Subgroup.normalizer (T : Set G)) :
    ↥H →* Equiv.Perm {t : G // t ∈ T ∧ t ≠ 1} where
  toFun h :=
    { toFun := fun t => ⟨(h : G) * t * (h : G)⁻¹,
        conj_mem_of_mem_normalizer (hH h.2) t.2.1, fun hh => t.2.2 (by
          calc (t : G) = (h : G)⁻¹ * ((h : G) * t * (h : G)⁻¹) * (h : G) := by group
            _ = 1 := by rw [hh]; group)⟩
      invFun := fun t => ⟨(h : G)⁻¹ * t * (h : G)⁻¹⁻¹,
        by simpa using conj_mem_of_mem_normalizer (hH (H.inv_mem h.2)) t.2.1, fun hh => t.2.2 (by
          calc (t : G) = (h : G) * ((h : G)⁻¹ * t * (h : G)⁻¹⁻¹) * (h : G)⁻¹ := by group
            _ = 1 := by rw [hh]; group)⟩
      left_inv := fun t => Subtype.ext (by simp [mul_assoc])
      right_inv := fun t => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext t
    simp
  map_mul' := fun g h => by
    ext t
    simp [mul_assoc]

theorem conjPerm_apply (T H : Subgroup G) (hH : H ≤ Subgroup.normalizer (T : Set G)) (h : ↥H)
    (t : {t : G // t ∈ T ∧ t ≠ 1}) : ((conjPerm T H hH h t : {t : G // t ∈ T ∧ t ≠ 1}) : G) =
      (h : G) * t * (h : G)⁻¹ := rfl

theorem mem_ker_conjPerm (T H : Subgroup G) (hH : H ≤ Subgroup.normalizer (T : Set G)) (h : ↥H) :
    h ∈ (conjPerm T H hH).ker ↔ (h : G) ∈ Subgroup.centralizer (T : Set G) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hh t ht
    by_cases ht1 : t = 1
    · rw [ht1]; simp
    · have := congrArg Subtype.val (Equiv.ext_iff.1 hh ⟨t, ht, ht1⟩)
      simp only [conjPerm_apply, Equiv.Perm.coe_one, id_eq] at this
      calc t * (h : G) = ((h : G) * t * (h : G)⁻¹) * (h : G) := by rw [this]
        _ = (h : G) * t := by group
  · intro hh
    ext t
    simp only [conjPerm_apply, Equiv.Perm.coe_one, id_eq]
    rw [← hh t t.2.1]
    group

theorem card_nontrivial_le_three {T : Subgroup G} {a b : G}
    (hT : ∀ t ∈ T, t = 1 ∨ t = a ∨ t = b ∨ t = b * a) :
    Nat.card {t : G // t ∈ T ∧ t ≠ 1} ≤ 3 := by
  have hsub : {t : G | t ∈ T ∧ t ≠ 1} ⊆ {a, b, b * a} := by
    rintro t ⟨ht, ht1⟩
    rcases hT t ht with h | h | h | h
    · exact absurd h ht1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have h1 : Nat.card {t : G // t ∈ T ∧ t ≠ 1} = Set.ncard {t : G | t ∈ T ∧ t ≠ 1} :=
    Nat.card_coe_set_eq _
  have h2 : Set.ncard {t : G | t ∈ T ∧ t ≠ 1} ≤ Set.ncard ({a, b, b * a} : Set G) :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : Set.ncard ({a, b, b * a} : Set G) ≤ 3 := by
    calc Set.ncard ({a, b, b * a} : Set G) ≤ Set.ncard ({b, b * a} : Set G) + 1 :=
          Set.ncard_insert_le _ _
      _ ≤ (Set.ncard ({b * a} : Set G) + 1) + 1 := by
          have := Set.ncard_insert_le b ({b * a} : Set G)
          omega
      _ = 3 := by rw [Set.ncard_singleton]
  omega

theorem relIndex_centralizer_dvd_six {T H : Subgroup G} {a b : G}
    (hT : ∀ t ∈ T, t = 1 ∨ t = a ∨ t = b ∨ t = b * a) (hH : H ≤ Subgroup.normalizer (T : Set G))
    [Finite G] : (Subgroup.centralizer (T : Set G)).relIndex H ∣ 6 := by
  have hker : (conjPerm T H hH).ker = (Subgroup.centralizer (T : Set G)).subgroupOf H := by
    ext h
    rw [mem_ker_conjPerm, Subgroup.mem_subgroupOf]
  have h1 : (conjPerm T H hH).ker.index = Nat.card (conjPerm T H hH).range :=
    Subgroup.index_ker _
  have h2 : Nat.card (conjPerm T H hH).range ∣ Nat.card (Equiv.Perm {t : G // t ∈ T ∧ t ≠ 1}) :=
    Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (Equiv.Perm {t : G // t ∈ T ∧ t ≠ 1}) ∣ 6 := by
    have : Finite {t : G // t ∈ T ∧ t ≠ 1} := inferInstance
    rw [Nat.card_perm]
    have := card_nontrivial_le_three hT
    exact (Nat.factorial_dvd_factorial this).trans (by decide)
  unfold Subgroup.relIndex
  rw [← hker, h1]
  exact h2.trans h3

variable {T T₁ : Subgroup G}

theorem two_dvd_relIndex_centralizer {T H : Subgroup G} (hH : H ≤ Subgroup.normalizer (T : Set G))
    [Finite G] {ℓ : G} (hℓH : ℓ ∈ H) (hℓ2 : ℓ * ℓ = 1)
    (hℓ : ℓ ∉ Subgroup.centralizer (T : Set G)) :
    2 ∣ (Subgroup.centralizer (T : Set G)).relIndex H := by
  classical
  have hker : (conjPerm T H hH).ker = (Subgroup.centralizer (T : Set G)).subgroupOf H := by
    ext h
    rw [mem_ker_conjPerm, Subgroup.mem_subgroupOf]
  set u := conjPerm T H hH ⟨ℓ, hℓH⟩ with hu
  have hu1 : u ≠ 1 := by
    intro h
    have : (⟨ℓ, hℓH⟩ : ↥H) ∈ (conjPerm T H hH).ker := h
    rw [mem_ker_conjPerm] at this
    exact hℓ this
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← map_pow]
    have : (⟨ℓ, hℓH⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hℓ2)
    rw [this, map_one]
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hmem : u ∈ (conjPerm T H hH).range := ⟨_, rfl⟩
  have h1 : orderOf (⟨u, hmem⟩ : (conjPerm T H hH).range) ∣ Nat.card (conjPerm T H hH).range :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at h1
  have h2 : (conjPerm T H hH).ker.index = Nat.card (conjPerm T H hH).range := Subgroup.index_ker _
  unfold Subgroup.relIndex
  rw [← hker, h2]
  exact h1

theorem exists_card_H [Finite G] (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T))) :
    ∃ m : ℕ, Odd m ∧ Nat.card (hSub T (normIn T₁ T)) = 8 * m := by
  classical
  have hS3 := hc.sec3
  have hL₁T := normIn_inf_left_eq_bot hS3
  have hcard8 : 8 ≤ Nat.card (sStar T T₁) := by
    have := card_mul_le_card_sStar hL₁T
    rwa [card_normIn_swap_two hc, show Nat.card T = 4 by simpa using hc.hT] at this
  have hSH : sStar T T₁ ≤ hSub T (normIn T₁ T) := sup_le left_le_hSub le_hSub
  have hSp : IsPGroup 2 ((sStar T T₁).subgroupOf (hSub T (normIn T₁ T))) :=
    (isPGroup_sStar hS3).comap_subtype
  obtain ⟨P₀, hP₀⟩ := hSp.exists_le_sylow
  have hP₀le : Nat.card (P₀ : Subgroup ↥(hSub T (normIn T₁ T))) ≤ 8 := by
    have hmap : IsPGroup 2 ((P₀ : Subgroup ↥(hSub T (normIn T₁ T))).map
        (hSub T (normIn T₁ T)).subtype) := P₀.isPGroup'.map _
    have := card_le_eight_of_pGroup_le hc h48 hmap (by
      rintro _ ⟨x, -, rfl⟩
      exact x.2)
    rwa [Subgroup.card_map_of_injective (hSub T (normIn T₁ T)).subtype_injective] at this
  have hP₀ge : 8 ≤ Nat.card (P₀ : Subgroup ↥(hSub T (normIn T₁ T))) := by
    have h1 := Subgroup.card_le_of_le hP₀
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv] at h1
    omega
  have hP₀8 : Nat.card (P₀ : Subgroup ↥(hSub T (normIn T₁ T))) = 8 := le_antisymm hP₀le hP₀ge
  refine ⟨(P₀ : Subgroup ↥(hSub T (normIn T₁ T))).index, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := P₀.not_dvd_index
    exact Nat.odd_iff.2 (by omega)
  · rw [← hP₀8]
    exact ((P₀ : Subgroup ↥(hSub T (normIn T₁ T))).card_mul_index).symm

theorem exists_oddComplement [Finite G] (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T))) {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) :
    ∃ N : Subgroup G, N ≤ hSub T (normIn T₁ T) ∧ N ≤ Subgroup.centralizer (T : Set G) ∧
      Odd (Nat.card N) ∧ T ⊓ N = ⊥ ∧
      (∀ c ∈ Subgroup.centralizer (T : Set G) ⊓ hSub T (normIn T₁ T),
        ∃ t ∈ T, ∃ n ∈ N, c = t * n) ∧
      (∀ s ∈ Subgroup.normalizer (T : Set G), ∀ n ∈ N, s * n * s⁻¹ ∈ N) ∧
      N.relIndex (hSub T (normIn T₁ T)) ∣ 24 := by
  classical
  set H := hSub T (normIn T₁ T) with hHdef
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  have hHN : H ≤ Subgroup.normalizer (T : Set G) := hSub_le_normalizer hL₁N
  have hTab := hc.hy.pair.wc.1
  have hT4 : Nat.card T = 4 := by simpa using hc.hT
  set C : Subgroup G := Subgroup.centralizer (T : Set G) ⊓ H with hCdef
  have hTC : T ≤ C := fun t ht => ⟨Subgroup.mem_centralizer_iff.2
    (fun u hu => elemAbelian_mul_comm hTab hu ht), left_le_hSub ht⟩
  have hCH : C ≤ H := inf_le_right
  have hCcent : ∀ c ∈ C, ∀ t ∈ T, c * t = t * c := fun c hc t ht =>
    (Subgroup.mem_centralizer_iff.1 hc.1 t ht).symm
  have hi6 : C.relIndex H ∣ 6 := by
    have := relIndex_centralizer_dvd_six (G := G) D.hT hHN
    rwa [← Subgroup.inf_relIndex_right (Subgroup.centralizer (T : Set G)) H] at this
  have hℓH : ℓ ∈ H := le_hSub D.hℓ
  have hℓnc : ℓ ∉ Subgroup.centralizer (T : Set G) := by
    intro hℓ
    have hbℓ : b * ℓ = ℓ * b := Subgroup.mem_centralizer_iff.1 hℓ b D.hb
    apply D.ha1
    have h1 : ℓ * a = ℓ * 1 := by
      calc ℓ * a = b * ℓ * b := D.conj_ℓ_b.symm
        _ = ℓ * b * b := by rw [hbℓ]
        _ = ℓ * 1 := by rw [mul_assoc, D.bb]
    exact mul_left_cancel h1
  have hieven : 2 ∣ C.relIndex H := by
    have := two_dvd_relIndex_centralizer hHN hℓH D.ℓℓ hℓnc
    rwa [← Subgroup.inf_relIndex_right (Subgroup.centralizer (T : Set G)) H] at this
  obtain ⟨m, hmodd, hHcard⟩ := exists_card_H hc h48
  have hCcard : Nat.card C * C.relIndex H = Nat.card H := by
    have := (C.subgroupOf H).card_mul_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv] at this
  set TC : Subgroup C := T.subgroupOf C with hTCdef
  have hTCcard : Nat.card TC * TC.index = Nat.card C := TC.card_mul_index
  have hTCcard4 : Nat.card TC = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv]
    exact hT4
  obtain ⟨i', hi'⟩ := hieven
  have hjodd : Odd TC.index := by
    have h1 : 4 * TC.index * (2 * i') = 8 * m := by
      rw [← hTCcard4, hTCcard, ← hi', hCcard, hHcard]
    have h2 : TC.index * i' = m := by nlinarith
    rw [← h2] at hmodd
    exact (Nat.odd_mul.1 hmodd).1
  have hTCn : TC.Normal := by
    refine ⟨fun t ht g => ?_⟩
    have ht' : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    rw [Subgroup.mem_subgroupOf]
    show (g : G) * t * (g : G)⁻¹ ∈ T
    have := hCcent g g.2 t ht'
    rw [this, mul_inv_cancel_right]
    exact ht'
  have hcop : Nat.Coprime (Nat.card TC) TC.index := by
    rw [hTCcard4]
    have : Nat.Coprime 2 TC.index := Nat.coprime_two_left.2 hjodd
    exact Nat.Coprime.pow_left 2 this
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set N : Subgroup G := K.map C.subtype with hNdef
  have hNC : N ≤ C := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hNcard : Nat.card N = TC.index := by
    have h1 := hK.card_mul_card
    have h2 : Nat.card N = Nat.card K :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [h2]
    have : Nat.card TC * Nat.card K = Nat.card TC * TC.index := by rw [h1, hTCcard]
    exact Nat.eq_of_mul_eq_mul_left (by rw [hTCcard4]; norm_num) this
  have hdec : ∀ c ∈ C, ∃ t ∈ T, ∃ n ∈ N, c = t * n := by
    intro c hcC
    obtain ⟨⟨⟨t, ht⟩, ⟨k, hk⟩⟩, hkp⟩ := hK.2 ⟨c, hcC⟩
    refine ⟨t, Subgroup.mem_subgroupOf.1 ht, k, ⟨k, hk, rfl⟩, ?_⟩
    have := congrArg Subtype.val hkp
    exact this.symm
  have hTN : T ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, k, hk, hkx⟩
    have hxC : x ∈ C := hkx ▸ k.2
    have h1 : (⟨x, hxC⟩ : C) ∈ TC := Subgroup.mem_subgroupOf.2 hxT
    have h2 : (⟨x, hxC⟩ : C) ∈ K := by
      have : k = ⟨x, hxC⟩ := Subtype.ext hkx
      rwa [this] at hk
    have h3 : (⟨x, hxC⟩ : C) ∈ TC ⊓ K := ⟨h1, h2⟩
    rw [hK.disjoint.eq_bot, Subgroup.mem_bot] at h3
    exact congrArg Subtype.val h3
  have hoddN : ∀ c ∈ C, Odd (orderOf c) → c ∈ N := by
    intro c hcC hcodd
    obtain ⟨t, ht, n, hn, rfl⟩ := hdec c hcC
    have hnC : n ∈ C := hNC hn
    have hc' : Commute t n := (hCcent n hnC t ht).symm
    have h1 : (t * n) ^ orderOf (t * n) = 1 := pow_orderOf_eq_one _
    rw [hc'.mul_pow] at h1
    have h2 : t ^ orderOf (t * n) = (n ^ orderOf (t * n))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : t ^ orderOf (t * n) ∈ T ⊓ N :=
      ⟨T.pow_mem ht _, by rw [h2]; exact N.inv_mem (N.pow_mem hn _)⟩
    rw [hTN, Subgroup.mem_bot] at h3
    have htt : t * t = 1 := elemAbelian_mul_self hTab ht
    obtain ⟨k, hk⟩ := hcodd
    have h4 : t ^ orderOf (t * n) = t := by
      rw [hk, pow_succ, pow_mul, sq, htt, one_pow, one_mul]
    rw [h4] at h3
    rw [h3, one_mul]
    exact hn
  have hNodd : Odd (Nat.card N) := hNcard ▸ hjodd
  have hNnorm : ∀ s ∈ Subgroup.normalizer (T : Set G), ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    intro s hs n hn
    have hnC := hNC hn
    have hn' : s * n * s⁻¹ ∈ C := by
      refine ⟨Subgroup.mem_centralizer_iff.2 fun t ht => ?_, mul_mul_inv_mem_hSub hs hnC.2⟩
      have ht' : s⁻¹ * t * s ∈ T := by
        simpa using conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hs) ht
      have := hCcent n hnC _ ht'
      calc t * (s * n * s⁻¹) = s * ((s⁻¹ * t * s) * n) * s⁻¹ := by group
        _ = s * (n * (s⁻¹ * t * s)) * s⁻¹ := by rw [this]
        _ = (s * n * s⁻¹) * t := by group
    apply hoddN _ hn'
    have hord : orderOf (s * n * s⁻¹) = orderOf n := by
      have := MulEquiv.orderOf_eq (MulAut.conj s) n
      simpa [MulAut.conj_apply] using this
    rw [hord]
    have hnodd : Odd (Nat.card N) := hNodd
    have h5 : orderOf n ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hnodd h5
  have hNrel : N.relIndex C = 4 := by
    have h1 := (N.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv, hNcard] at h1
    have h2 : Nat.card C = 4 * TC.index := by rw [← hTCcard, hTCcard4]
    rw [h2] at h1
    have hpos : 0 < TC.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    unfold Subgroup.relIndex
    exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  refine ⟨N, hNC.trans hCH, fun n hn => (hNC hn).1, hNodd, hTN, fun c hcC => hdec c hcC, hNnorm, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex N C H hNC hCH, hNrel]
  have : 4 * 6 = 24 := by norm_num
  rw [← this]
  exact Nat.mul_dvd_mul_left 4 hi6

theorem exists_mul_of_mem_normalizer [Finite G]
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    ∃ h ∈ hSub T (normIn T₁ T), ∃ c ∈ Subgroup.centralizer (T : Set G), g = h * c := by
  have hℓH : ℓ ∈ hSub T (normIn T₁ T) := le_hSub D.hℓ
  have hga : g * a * g⁻¹ ∈ T := conj_mem_of_mem_normalizer hg D.haT
  have hga1 : g * a * g⁻¹ ≠ 1 := fun h => D.ha1 (by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨h₁, hh₁, hh₁e⟩ := h57 a D.haT D.ha1 _ hga hga1
  set g₁ := h₁⁻¹ * g with hg₁
  have hh₁N : h₁ ∈ Subgroup.normalizer (T : Set G) :=
    hSub_le_normalizer (fun w hw => (mem_normIn.1 hw).2) hh₁
  have hg₁N : g₁ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem ((Subgroup.normalizer (T : Set G)).inv_mem hh₁N) hg
  have hg₁a : g₁ * a * g₁⁻¹ = a := by
    calc g₁ * a * g₁⁻¹ = h₁⁻¹ * (g * a * g⁻¹) * h₁ := by rw [hg₁]; group
      _ = h₁⁻¹ * (h₁ * a * h₁⁻¹) * h₁ := by rw [hh₁e]
      _ = a := by group
  have hg₁b : g₁ * b * g₁⁻¹ ∈ T := conj_mem_of_mem_normalizer hg₁N D.hb
  have hb1 : b ≠ 1 := fun h => D.hbL (by rw [h]; exact (normIn T T₁).one_mem)
  have hne1 : g₁ * b * g₁⁻¹ ≠ 1 := fun h => hb1 (by
    calc b = g₁⁻¹ * (g₁ * b * g₁⁻¹) * g₁ := by group
      _ = 1 := by rw [h]; group)
  have hnea : g₁ * b * g₁⁻¹ ≠ a := fun h => D.hbL (by
    have : b = a := by
      calc b = g₁⁻¹ * (g₁ * b * g₁⁻¹) * g₁ := by group
        _ = g₁⁻¹ * a * g₁ := by rw [h]
        _ = g₁⁻¹ * (g₁ * a * g₁⁻¹) * g₁ := by rw [hg₁a]
        _ = a := by group
    rw [this]; exact D.ha)
  rcases D.hT _ hg₁b with h | h | h | h
  · exact absurd h hne1
  · exact absurd h hnea
  ·
    refine ⟨h₁, hh₁, g₁, ?_, by rw [hg₁]; group⟩
    rw [Subgroup.mem_centralizer_iff]
    exact D.comm_of_ab (comm_of_conj hg₁a) (comm_of_conj h)
  ·
    have hℓg₁a : (ℓ * g₁) * a * (ℓ * g₁)⁻¹ = a := by
      calc (ℓ * g₁) * a * (ℓ * g₁)⁻¹ = ℓ * (g₁ * a * g₁⁻¹) * ℓ⁻¹ := by group
        _ = ℓ * a * ℓ := by rw [hg₁a, D.inv_ℓ]
        _ = a := by
          calc ℓ * a * ℓ = a * ℓ * ℓ := by rw [D.comm_aℓ]
            _ = a * (ℓ * ℓ) := by group
            _ = a := by rw [D.ℓℓ, mul_one]
    have hℓaℓ : ℓ * a * ℓ = a := by
      calc ℓ * a * ℓ = a * ℓ * ℓ := by rw [D.comm_aℓ]
        _ = a * (ℓ * ℓ) := by group
        _ = a := by rw [D.ℓℓ, mul_one]
    have hℓba : ℓ * (b * a) * ℓ = b := by
      calc ℓ * (b * a) * ℓ = (ℓ * b * ℓ) * (ℓ * a * ℓ) := by
            calc ℓ * (b * a) * ℓ = ℓ * b * (ℓ * ℓ) * a * ℓ := by rw [D.ℓℓ]; group
              _ = (ℓ * b * ℓ) * (ℓ * a * ℓ) := by
                  calc ℓ * b * (ℓ * ℓ) * a * ℓ = ℓ * b * ℓ * ℓ * a * ℓ := by group
                    _ = (ℓ * b * ℓ) * (ℓ * a * ℓ) := by group
        _ = (b * a) * a := by rw [D.conj_b_ℓ, hℓaℓ]
        _ = b := by rw [mul_assoc, D.aa, mul_one]
    have hℓg₁b : (ℓ * g₁) * b * (ℓ * g₁)⁻¹ = b := by
      calc (ℓ * g₁) * b * (ℓ * g₁)⁻¹ = ℓ * (g₁ * b * g₁⁻¹) * ℓ⁻¹ := by group
        _ = ℓ * (b * a) * ℓ := by rw [h, D.inv_ℓ]
        _ = b := hℓba
    refine ⟨h₁ * ℓ, (hSub T (normIn T₁ T)).mul_mem hh₁ hℓH, ℓ * g₁, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      exact D.comm_of_ab (comm_of_conj hℓg₁a) (comm_of_conj hℓg₁b)
    · calc g = h₁ * g₁ := by rw [hg₁]; group
        _ = (h₁ * ℓ) * (ℓ * g₁) := by
            calc h₁ * g₁ = h₁ * (ℓ * ℓ) * g₁ := by rw [D.ℓℓ, mul_one]
              _ = (h₁ * ℓ) * (ℓ * g₁) := by group

theorem hSub_le_closure_conj [Finite G] (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T)))
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) :
    hSub T (normIn T₁ T) ≤
      Subgroup.closure {z | ∃ h ∈ hSub T (normIn T₁ T), z = h * ℓ * h⁻¹} := by
  classical
  obtain ⟨N, hNH, hNc, hNodd, hTN, hdec, hNnorm, -⟩ := exists_oddComplement hc h48 D
  set H := hSub T (normIn T₁ T) with hHdef
  set Ω : Set G := {z | ∃ h ∈ H, z = h * ℓ * h⁻¹} with hΩ
  set H₁ := Subgroup.closure Ω with hH₁
  have hℓH : ℓ ∈ H := le_hSub D.hℓ
  have hTab := hc.hy.pair.wc.1
  have hnormH : ∀ h ∈ H, ∀ z ∈ H₁, h * z * h⁻¹ ∈ H₁ := by
    intro h hh z hz
    have key : H₁ ≤ H₁.comap (MulAut.conj h).toMonoidHom := by
      refine (Subgroup.closure_le _).2 (fun w hw => ?_)
      obtain ⟨h', hh', rfl⟩ := hw
      show h * (h' * ℓ * h'⁻¹) * h⁻¹ ∈ H₁
      apply Subgroup.subset_closure
      refine ⟨h * h', H.mul_mem hh hh', ?_⟩
      group
    exact key hz
  have hℓ1 : ℓ ∈ H₁ := Subgroup.subset_closure ⟨1, H.one_mem, by group⟩
  have haH₁ : a ∈ H₁ := by
    have hbℓ : b * ℓ * b⁻¹ ∈ H₁ := Subgroup.subset_closure ⟨b, left_le_hSub D.hb, rfl⟩
    have : a = ℓ * (b * ℓ * b⁻¹) := by
      rw [D.inv_b, D.conj_ℓ_b, ← mul_assoc, D.ℓℓ, one_mul]
    rw [this]
    exact H₁.mul_mem hℓ1 hbℓ
  have hTH₁ : T ≤ H₁ := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]; exact H₁.one_mem
    · obtain ⟨h, hh, he⟩ := h57 a D.haT D.ha1 t ht ht1
      rw [← he]
      exact hnormH h hh a haH₁
  have hconjc : ∀ c ∈ Subgroup.centralizer (T : Set G), c * ℓ * c⁻¹ ∈ H₁ := by
    intro c hcT
    have hcN : c ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.centralizer_le_normalizer (T : Set G)) hcT
    have hcc : ∀ t ∈ T, c * t = t * c := fun t ht => (Subgroup.mem_centralizer_iff.1 hcT t ht).symm
    have hyH : c * ℓ * c⁻¹ ∈ H := by
      refine Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem c
        (Subgroup.mem_iSup_of_mem hcN (mem_conjSubgroup.2 ?_)))
      rw [show c⁻¹ * (c * ℓ * c⁻¹) * c = ℓ by group]
      exact D.hℓ
    set yy := c * ℓ * c⁻¹ with hyy
    have hyy2 : yy * yy = 1 := by
      calc yy * yy = c * (ℓ * ℓ) * c⁻¹ := by rw [hyy]; group
        _ = 1 := by rw [D.ℓℓ]; group
    have hyyinv : yy⁻¹ = yy := inv_eq_of_mul_eq_one_right hyy2
    have hc₀t : ∀ t ∈ T, (yy * ℓ) * t * (yy * ℓ)⁻¹ = t := by
      intro t ht
      have ht' : ℓ * t * ℓ⁻¹ ∈ T := conj_mem_of_mem_normalizer D.hℓN ht
      have h1 : c⁻¹ * (ℓ * t * ℓ⁻¹) * c = ℓ * t * ℓ⁻¹ := by
        calc c⁻¹ * (ℓ * t * ℓ⁻¹) * c = c⁻¹ * ((ℓ * t * ℓ⁻¹) * c) := by group
          _ = c⁻¹ * (c * (ℓ * t * ℓ⁻¹)) := by rw [hcc _ ht']
          _ = ℓ * t * ℓ⁻¹ := by group
      calc (yy * ℓ) * t * (yy * ℓ)⁻¹
          = c * ℓ * (c⁻¹ * (ℓ * t * ℓ⁻¹) * c) * ℓ⁻¹ * c⁻¹ := by rw [hyy]; group
        _ = c * ℓ * (ℓ * t * ℓ⁻¹) * ℓ⁻¹ * c⁻¹ := by rw [h1]
        _ = c * ((ℓ * ℓ) * t * (ℓ * ℓ)⁻¹) * c⁻¹ := by group
        _ = c * t * c⁻¹ := by rw [D.ℓℓ]; group
        _ = t := by rw [hcc t ht]; group
    have hc₀cent : (yy * ℓ) ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      calc t * (yy * ℓ) = ((yy * ℓ) * t * (yy * ℓ)⁻¹) * (yy * ℓ) := by rw [hc₀t t ht]
        _ = (yy * ℓ) * t := by group
    obtain ⟨t, ht, n, hn, hc₀e⟩ := hdec (yy * ℓ) ⟨hc₀cent, H.mul_mem hyH hℓH⟩
    have hnc : ∀ u ∈ T, u * n = n * u := fun u hu =>
      Subgroup.mem_centralizer_iff.1 (hNc hn) u hu
    have hinvc : ℓ * (yy * ℓ) * ℓ⁻¹ = (yy * ℓ)⁻¹ := by
      calc ℓ * (yy * ℓ) * ℓ⁻¹ = ℓ * yy := by group
        _ = ℓ⁻¹ * yy⁻¹ := by rw [D.inv_ℓ, hyyinv]
        _ = (yy * ℓ)⁻¹ := (mul_inv_rev yy ℓ).symm
    have ht' : ℓ * t * ℓ⁻¹ ∈ T := conj_mem_of_mem_normalizer D.hℓN ht
    have hn' : ℓ * n * ℓ⁻¹ ∈ N := hNnorm ℓ D.hℓN n hn
    have h1 : (ℓ * t * ℓ⁻¹) * (ℓ * n * ℓ⁻¹) = n⁻¹ * t⁻¹ := by
      calc (ℓ * t * ℓ⁻¹) * (ℓ * n * ℓ⁻¹) = ℓ * (t * n) * ℓ⁻¹ := by group
        _ = ℓ * (yy * ℓ) * ℓ⁻¹ := by rw [hc₀e]
        _ = (yy * ℓ)⁻¹ := hinvc
        _ = n⁻¹ * t⁻¹ := by rw [hc₀e, mul_inv_rev]
    have htn' : t * n⁻¹ = n⁻¹ * t := Subgroup.mem_centralizer_iff.1 (hNc (N.inv_mem hn)) t ht
    have h2 : t * (ℓ * t * ℓ⁻¹) = n⁻¹ * (ℓ * n * ℓ⁻¹)⁻¹ := by
      calc t * (ℓ * t * ℓ⁻¹) = t * ((ℓ * t * ℓ⁻¹) * (ℓ * n * ℓ⁻¹)) * (ℓ * n * ℓ⁻¹)⁻¹ := by group
        _ = t * (n⁻¹ * t⁻¹) * (ℓ * n * ℓ⁻¹)⁻¹ := by rw [h1]
        _ = (t * n⁻¹) * t⁻¹ * (ℓ * n * ℓ⁻¹)⁻¹ := by group
        _ = n⁻¹ * (ℓ * n * ℓ⁻¹)⁻¹ := by rw [htn']; group
    have hmemTN : t * (ℓ * t * ℓ⁻¹) ∈ T ⊓ N :=
      ⟨T.mul_mem ht ht', by rw [h2]; exact N.mul_mem (N.inv_mem hn) (N.inv_mem hn')⟩
    rw [hTN, Subgroup.mem_bot, h2] at hmemTN
    have hℓn : ℓ * n * ℓ⁻¹ = n⁻¹ := by
      have : (ℓ * n * ℓ⁻¹)⁻¹ = n := by
        calc (ℓ * n * ℓ⁻¹)⁻¹ = n * (n⁻¹ * (ℓ * n * ℓ⁻¹)⁻¹) := by group
          _ = n := by rw [hmemTN, mul_one]
      calc ℓ * n * ℓ⁻¹ = ((ℓ * n * ℓ⁻¹)⁻¹)⁻¹ := by rw [inv_inv]
        _ = n⁻¹ := by rw [this]
    have hnodd : Odd (orderOf n) := by
      have h5 : orderOf n ∣ Nat.card N := by
        have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
        rwa [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hNodd h5
    obtain ⟨k, hk⟩ := hnodd
    set u := n ^ (k + 1) with hu
    have huN : u ∈ N := N.pow_mem hn _
    have huu : u * u = n := by
      have h1 : u * u = n ^ (2 * k + 1 + 1) := by
        rw [hu, ← pow_add]
        congr 1
        ring
      rw [h1, pow_succ, ← hk, pow_orderOf_eq_one, one_mul]
    have hℓu : ℓ * u * ℓ⁻¹ = u⁻¹ := by
      rw [hu, ← conj_pow, hℓn, inv_pow]
    have hw : u * ℓ * u⁻¹ = n * ℓ := by
      calc u * ℓ * u⁻¹ = u * (ℓ * u⁻¹ * ℓ⁻¹) * ℓ := by group
        _ = u * (ℓ * u * ℓ⁻¹)⁻¹ * ℓ := by rw [show ℓ * u⁻¹ * ℓ⁻¹ = (ℓ * u * ℓ⁻¹)⁻¹ by group]
        _ = u * u * ℓ := by rw [hℓu, inv_inv]
        _ = n * ℓ := by rw [huu]
    have hyyeq : yy = t * (n * ℓ) := by
      calc yy = (yy * ℓ) * ℓ⁻¹ := by group
        _ = (t * n) * ℓ⁻¹ := by rw [hc₀e]
        _ = t * (n * ℓ) := by rw [D.inv_ℓ]; group
    have hnℓ : n * ℓ ∈ H₁ := by
      rw [← hw]
      exact Subgroup.subset_closure ⟨u, hNH huN, rfl⟩
    rw [hyyeq]
    exact H₁.mul_mem (hTH₁ ht) hnℓ
  refine sup_le hTH₁ (iSup₂_le fun g hg x hx => ?_)
  have hx' : g⁻¹ * x * g ∈ normIn T₁ T := mem_conjSubgroup.1 hx
  rcases D.hL₁ _ hx' with h | h
  · have : x = 1 := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this]
    exact H₁.one_mem
  · have : x = g * ℓ * g⁻¹ := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * ℓ * g⁻¹ := by rw [h]
    rw [this]
    obtain ⟨h', hh', c, hcc, hgc⟩ := exists_mul_of_mem_normalizer h57 D hg
    rw [hgc]
    have e : h' * c * ℓ * (h' * c)⁻¹ = h' * (c * ℓ * c⁻¹) * h'⁻¹ := by group
    rw [e]
    exact hnormH h' hh' _ (hconjc c hcc)

end CFSG.CGT.T75H
