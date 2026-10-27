module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki
public import CFSG.CharacterTheory.Semidihedral.StructureTransport

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section CyclicHelpers

theorem exists_two_mul_eq_mul_odd {n a : ℤ} (h2 : n ∣ 2 * a) (ha : ¬ n ∣ a) :
    ∃ j : ℤ, 2 * a = n * (2 * j + 1) := by
  obtain ⟨k, hk⟩ := h2
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h : 2 * a = 2 * (n * j) := by linear_combination hk
    have hd : n ∣ a := ⟨j, mul_left_cancel₀ two_ne_zero h⟩
    exact absurd hd ha
  · exact ⟨j, hk⟩

theorem eq_of_sq_eq_one_of_isCyclic_group {G : Type*} [Group G] [IsCyclic G] {x z : G}
    (hx : x ^ 2 = 1) (hz : z ^ 2 = 1) (hx1 : x ≠ 1) (hz1 : z ≠ 1) : x = z := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg z)
  have hxa : g ^ (2 * a) = 1 := by
    have h := hx
    rw [← zpow_natCast, ← zpow_mul] at h
    simpa [mul_comm] using h
  have hzb : g ^ (2 * b) = 1 := by
    have h := hz
    rw [← zpow_natCast, ← zpow_mul] at h
    simpa [mul_comm] using h
  have hna : ¬ (orderOf g : ℤ) ∣ a := fun hd => hx1 (orderOf_dvd_iff_zpow_eq_one.mp hd)
  have hnb : ¬ (orderOf g : ℤ) ∣ b := fun hd => hz1 (orderOf_dvd_iff_zpow_eq_one.mp hd)
  obtain ⟨j, hj⟩ := exists_two_mul_eq_mul_odd (orderOf_dvd_iff_zpow_eq_one.mpr hxa) hna
  obtain ⟨i, hi⟩ := exists_two_mul_eq_mul_odd (orderOf_dvd_iff_zpow_eq_one.mpr hzb) hnb
  have h2 : 2 * (a - b) = 2 * ((orderOf g : ℤ) * (j - i)) := by linear_combination hj - hi
  have hab : a - b = (orderOf g : ℤ) * (j - i) := mul_left_cancel₀ two_ne_zero h2
  have hgab : g ^ (a - b) = 1 := orderOf_dvd_iff_zpow_eq_one.mp ⟨j - i, hab⟩
  rw [zpow_sub, mul_inv_eq_one] at hgab
  exact hgab

theorem isCyclic_of_natCard_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) :
    IsCyclic G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (show Nat.card G = 1 ∨ Nat.card G = 2 by omega) with h1 | h2
  · have : Subsingleton G := Finite.card_le_one_iff_subsingleton.mp h1.le
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2

theorem comm_of_mem_isCyclic {P : Type} [Group P] {C : Subgroup P} (hC : IsCyclic C) {a b : P}
    (ha : a ∈ C) (hb : b ∈ C) : a * b = b * a := by
  have := hC
  letI := IsCyclic.commGroup (α := C)
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : C) ⟨b, hb⟩)

theorem relIndex_le_index_of_finite {P : Type} [Group P] [Finite P] (C H : Subgroup P) :
    C.relIndex H ≤ C.index := by
  have hpos : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : (C ⊓ H).index = C.relIndex H * H.index := Subgroup.index_inf
  have h2 : (C ⊓ H).index ≤ C.index * H.index := Subgroup.index_inf_le
  rw [h1] at h2
  exact Nat.le_of_mul_le_mul_right h2 hpos

theorem card_le_two_mul_inf {P : Type} [Group P] [Finite P] {C : Subgroup P} (hi : C.index ≤ 2)
    (U : Subgroup P) : Nat.card U ≤ 2 * Nat.card (U ⊓ C : Subgroup P) := by
  have h : C.relIndex U * Nat.card (C ⊓ U : Subgroup P) = Nat.card U :=
    Subgroup.relIndex_mul_card C U
  rw [inf_comm] at h
  rw [← h]
  exact Nat.mul_le_mul_right _ ((relIndex_le_index_of_finite C U).trans hi)

theorem inv_mul_mem_of_not_mem_of_index_le_two {P : Type} [Group P] [Finite P] {C : Subgroup P}
    (hi : C.index ≤ 2) {u v : P} (hu : u ∉ C) (hv : v ∉ C) : u⁻¹ * v ∈ C := by
  have hne : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : C.index ≠ 1 := fun h => hu (by
    rw [Subgroup.index_eq_one.mp h]
    exact Subgroup.mem_top u)
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp (by omega : C.index = 2)
  have hau : a * u ∈ C := by
    rcases ha u with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact h1
    · exact absurd h2 hu
  have hav : a * v ∈ C := by
    rcases ha v with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact h1
    · exact absurd h2 hv
  have heq : u⁻¹ * v = (a * u)⁻¹ * (a * v) := by group
  rw [heq]
  exact C.mul_mem (C.inv_mem hau) hav

end CyclicHelpers

theorem mem_center_of_involution_mem_cyclic_normal {P : Type} [Group P] {C : Subgroup P} [C.Normal]
    (hC : IsCyclic C) {c : P} (hcC : c ∈ C) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    c ∈ Subgroup.center P := by
  have := hC
  rw [Subgroup.mem_center_iff]
  intro g
  have hconj : g * c * g⁻¹ ∈ C := Subgroup.Normal.conj_mem inferInstance c hcC g
  have hx2 : (⟨g * c * g⁻¹, hconj⟩ : C) ^ 2 = 1 := by
    apply Subtype.ext
    simp [conj_pow, hc2]
  have hz2 : (⟨c, hcC⟩ : C) ^ 2 = 1 := Subtype.ext (by simpa using hc2)
  have hx1 : (⟨g * c * g⁻¹, hconj⟩ : C) ≠ 1 := by
    intro h
    apply hc1
    have h' : g * c * g⁻¹ = 1 := congrArg Subtype.val h
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  have hz1 : (⟨c, hcC⟩ : C) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have heq : g * c * g⁻¹ = c :=
    congrArg Subtype.val (eq_of_sq_eq_one_of_isCyclic_group hx2 hz2 hx1 hz1)
  calc g * c = (g * c * g⁻¹) * g := by group
    _ = c * g := by rw [heq]

theorem rank_le_two_of_cyclic_index_le_two {P : Type} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCyclic C) (hi : C.index ≤ 2) (U : Subgroup P) : Group.rank U ≤ 2 := by
  classical
  have := hC
  have : IsCyclic (U ⊓ C : Subgroup P) := Subgroup.isCyclic_of_le inf_le_right
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := (U ⊓ C : Subgroup P))
  have hyU : (y : P) ∈ U := (Subgroup.mem_inf.mp y.2).1
  have hpow : ∀ w : P, w ∈ U → w ∈ C → ∃ k : ℤ, (y : P) ^ k = w := by
    intro w hwU hwC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨w, Subgroup.mem_inf.mpr ⟨hwU, hwC⟩⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨a, ha⟩ : ∃ a : U, (a : P) = (y : P) := ⟨⟨y, hyU⟩, rfl⟩
  by_cases hUC : U ≤ C
  · have hspan : Subgroup.closure (({a} : Finset U) : Set U) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨k, hk⟩ := hpow x x.2 (hUC x.2)
      have hx : x = a ^ k := Subtype.ext (by simp [ha, hk])
      rw [hx]
      exact zpow_mem (Subgroup.subset_closure (by simp)) k
    calc Group.rank U ≤ ({a} : Finset U).card := Group.rank_le hspan
      _ ≤ 2 := by simp
  · obtain ⟨g, hgU, hgC⟩ : ∃ g ∈ U, g ∉ C := IsConcreteLE.not_le_iff_exists.mp hUC
    obtain ⟨b, hb⟩ : ∃ b : U, (b : P) = g := ⟨⟨g, hgU⟩, rfl⟩
    have hspan : Subgroup.closure (({a, b} : Finset U) : Set U) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      by_cases hxC : (x : P) ∈ C
      · obtain ⟨k, hk⟩ := hpow x x.2 hxC
        have hx : x = a ^ k := Subtype.ext (by simp [ha, hk])
        rw [hx]
        exact zpow_mem (Subgroup.subset_closure (by simp)) k
      · have hgx : g⁻¹ * (x : P) ∈ C := inv_mul_mem_of_not_mem_of_index_le_two hi hgC hxC
        have hgxU : g⁻¹ * (x : P) ∈ U := U.mul_mem (U.inv_mem hgU) x.2
        obtain ⟨k, hk⟩ := hpow _ hgxU hgx
        have hx : x = b * a ^ k := Subtype.ext (by simp [ha, hb, hk])
        rw [hx]
        exact mul_mem (Subgroup.subset_closure (by simp))
          (zpow_mem (Subgroup.subset_closure (by simp)) k)
    calc Group.rank U ≤ ({a, b} : Finset U).card := Group.rank_le hspan
      _ ≤ 2 := Finset.card_le_two

theorem mem_of_not_isCyclic_of_cyclic_index_le_two {P : Type} [Group P] [Finite P] {C : Subgroup P}
    (hP : IsPGroup 2 P) (hC : IsCyclic C) (hi : C.index ≤ 2) {c : P} (hcC : c ∈ C)
    (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (U : Subgroup P) (hU : ¬ IsCyclic U) : c ∈ U := by
  have := hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : U ⊓ C ≠ ⊥ := by
    intro hbot
    apply hU
    have h := card_le_two_mul_inf hi U
    rw [hbot, Subgroup.card_bot] at h
    exact isCyclic_of_natCard_le_two (by omega)
  have : Nontrivial (U ⊓ C : Subgroup P) := (Subgroup.nontrivial_iff_ne_bot _).mpr hK
  have h1 : 1 < Nat.card (U ⊓ C : Subgroup P) := Finite.one_lt_card
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hP.to_subgroup (U ⊓ C))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hn, pow_zero] at h1
    exact lt_irrefl 1 h1
  have h2dvd : 2 ∣ Nat.card (U ⊓ C : Subgroup P) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (U ⊓ C : Subgroup P)) 2 h2dvd
  have hy2 : (y : P) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa using congrArg Subtype.val h
  have hy1 : (y : P) ≠ 1 := by
    intro h
    have hy' : y = 1 := Subtype.ext h
    rw [hy', orderOf_one] at hy
    norm_num at hy
  have hyC : (y : P) ∈ C := (Subgroup.mem_inf.mp y.2).2
  have hyU : (y : P) ∈ U := (Subgroup.mem_inf.mp y.2).1
  have hyC2 : (⟨(y : P), hyC⟩ : C) ^ 2 = 1 := Subtype.ext (by simpa using hy2)
  have hyC1 : (⟨(y : P), hyC⟩ : C) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hcC2 : (⟨c, hcC⟩ : C) ^ 2 = 1 := Subtype.ext (by simpa using hc2)
  have hcC1 : (⟨c, hcC⟩ : C) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have heq : (y : P) = c :=
    congrArg Subtype.val (eq_of_sq_eq_one_of_isCyclic_group hyC2 hcC2 hyC1 hcC1)
  rw [← heq]
  exact hyU

theorem card_centralizer_le_of_not_mem {P : Type} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCyclic C) (hi : C.index ≤ 2) {t x : P} (ht : t ∉ C) (hx : x ∉ C) :
    Nat.card (Subgroup.centralizer ({x} : Set P)) ≤
      Nat.card (Subgroup.centralizer ({t} : Set P)) := by
  have := hC
  obtain ⟨c, hcC, rfl⟩ : ∃ c ∈ C, x = t * c :=
    ⟨t⁻¹ * x, inv_mul_mem_of_not_mem_of_index_le_two hi ht hx, by group⟩
  have hcomm : ∀ y ∈ C, y ∈ Subgroup.centralizer ({t * c} : Set P) ↔
      y ∈ Subgroup.centralizer ({t} : Set P) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have hcy : c * y = y * c := comm_of_mem_isCyclic hC hcC hy
    constructor
    · intro h
      calc y * t = y * (t * c) * c⁻¹ := by group
        _ = t * c * y * c⁻¹ := by rw [h]
        _ = t * (c * y) * c⁻¹ := by group
        _ = t * (y * c) * c⁻¹ := by rw [hcy]
        _ = t * y := by group
    · intro h
      calc y * (t * c) = (y * t) * c := by group
        _ = (t * y) * c := by rw [h]
        _ = t * (y * c) := by group
        _ = t * (c * y) := by rw [hcy]
        _ = t * c * y := by group
  have hD : Subgroup.centralizer ({t * c} : Set P) ⊓ C =
      Subgroup.centralizer ({t} : Set P) ⊓ C := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hcomm y h2).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hcomm y h2).mpr h1, h2⟩
  have ht_mem : t ∈ Subgroup.centralizer ({t} : Set P) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hHt : Nat.card (Subgroup.centralizer ({t} : Set P)) =
      2 * Nat.card (Subgroup.centralizer ({t} : Set P) ⊓ C : Subgroup P) := by
    have h : C.relIndex (Subgroup.centralizer ({t} : Set P)) *
        Nat.card (C ⊓ Subgroup.centralizer ({t} : Set P) : Subgroup P) =
        Nat.card (Subgroup.centralizer ({t} : Set P)) :=
      Subgroup.relIndex_mul_card C _
    rw [inf_comm] at h
    rw [← h]
    congr 1
    have h2 : C.relIndex (Subgroup.centralizer ({t} : Set P)) ≤ 2 :=
      (relIndex_le_index_of_finite C _).trans hi
    have h0 : C.relIndex (Subgroup.centralizer ({t} : Set P)) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have h1 : C.relIndex (Subgroup.centralizer ({t} : Set P)) ≠ 1 := by
      intro h1
      have hle := Subgroup.relIndex_eq_one.mp h1
      exact ht (hle ht_mem)
    omega
  calc Nat.card (Subgroup.centralizer ({t * c} : Set P))
      ≤ 2 * Nat.card (Subgroup.centralizer ({t * c} : Set P) ⊓ C : Subgroup P) :=
        card_le_two_mul_inf hi _
    _ = 2 * Nat.card (Subgroup.centralizer ({t} : Set P) ⊓ C : Subgroup P) := by rw [hD]
    _ = Nat.card (Subgroup.centralizer ({t} : Set P)) := hHt.symm

theorem exists_cyclic_index_le_two {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P) {t : P}
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) (hC : Nat.card (Subgroup.centralizer ({t} : Set P)) ≤ 4) :
    ∃ C : Subgroup P, IsCyclic C ∧ C.index ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Subgroup P, C₁ = Subgroup.centralizer ({t} : Set P) := ⟨_, rfl⟩
  rw [← hC₁] at hC
  have hmemC₁ : ∀ g : P, g ∈ C₁ ↔ g * t = t * g := fun g => by
    rw [hC₁, Subgroup.mem_centralizer_singleton_iff]
  have htC₁ : t ∈ C₁ := (hmemC₁ t).mpr rfl
  have hnt : 1 < Nat.card C₁ := by
    have : Nontrivial C₁ := ⟨⟨t, htC₁⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩
    exact Finite.one_lt_card
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (hP.to_subgroup C₁)
  have hm2 : m ≤ 2 := by
    by_contra h
    rw [not_le] at h
    have h8 : 8 ≤ 2 ^ m := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    rw [hm] at hC
    exact absurd (le_trans h8 hC) (by norm_num)
  have hcard24 : Nat.card C₁ = 2 ∨ Nat.card C₁ = 4 := by
    interval_cases m
    · rw [hm] at hnt
      norm_num at hnt
    · left
      rw [hm]
      norm_num
    · right
      rw [hm]
      norm_num
  by_cases hcyc : IsCyclic C₁
  ·
    refine ⟨C₁, hcyc, ?_⟩
    have htop : C₁ = ⊤ := by
      by_contra hne
      have : Group.IsNilpotent P := IsPGroup.isNilpotent hP
      have hlt : C₁ < Subgroup.normalizer C₁ :=
        (Group.normalizerCondition_of_isNilpotent (G := P)) C₁ (lt_top_iff_ne_top.mpr hne)
      have hnle : ¬ Subgroup.normalizer C₁ ≤ C₁ := fun h => lt_irrefl C₁ (lt_of_lt_of_le hlt h)
      obtain ⟨g, hgN, hgC⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
      have hgt : g * t * g⁻¹ ∈ C₁ := (Subgroup.mem_normalizer_iff.mp hgN t).mp htC₁
      have hsq : (g * t * g⁻¹) ^ 2 = 1 := by
        rw [conj_pow, ht, mul_one, mul_inv_cancel]
      have hgt1 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group)
      have heq : g * t * g⁻¹ = t :=
        congrArg Subtype.val (eq_of_sq_eq_one_of_isCyclic_group (G := C₁)
          (x := ⟨g * t * g⁻¹, hgt⟩) (z := ⟨t, htC₁⟩)
          (Subtype.ext (by simpa using hsq)) (Subtype.ext (by simpa using ht))
          (fun h => hgt1 (congrArg Subtype.val h)) (fun h => ht1 (congrArg Subtype.val h)))
      apply hgC
      rw [hmemC₁]
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [heq]
    rw [htop, Subgroup.index_top]
    norm_num
  · have hcard4 : Nat.card C₁ = 4 := by
      rcases hcard24 with h2 | h4
      · exact absurd (isCyclic_of_prime_card h2) hcyc
      · exact h4
    have hsq : ∀ x ∈ C₁, x ^ 2 = 1 := by
      intro x hx
      have hdvd : orderOf x ∣ 2 ^ 2 := by
        have h := orderOf_dvd_natCard (⟨x, hx⟩ : C₁)
        rw [Subgroup.orderOf_mk, hcard4] at h
        simpa using h
      obtain ⟨i, hi, hxi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      interval_cases i
      · rw [pow_zero, orderOf_eq_one_iff] at hxi
        rw [hxi, one_pow]
      · rw [pow_one] at hxi
        calc x ^ 2 = x ^ orderOf x := by rw [hxi]
          _ = 1 := pow_orderOf_eq_one x
      · exfalso
        apply hcyc
        refine isCyclic_of_orderOf_eq_card (⟨x, hx⟩ : C₁) ?_
        rw [Subgroup.orderOf_mk, hxi, hcard4]
        norm_num
    by_cases htop : C₁ = ⊤
    ·
      refine ⟨Subgroup.zpowers t, inferInstance, ?_⟩
      have hord : orderOf t = 2 := orderOf_eq_prime ht ht1
      have hcardP : Nat.card P = 4 := by
        rw [← hcard4, htop]
        exact Subgroup.card_top.symm
      have h : Nat.card (Subgroup.zpowers t) * (Subgroup.zpowers t).index = Nat.card P :=
        Subgroup.card_mul_index (Subgroup.zpowers t)
      rw [Nat.card_zpowers, hord, hcardP] at h
      omega
    ·
      have hCtop : (⊤ : Subgroup P) ⊓ Subgroup.centralizer (C₁ : Set P) ≤ C₁ := by
        intro g hg
        have h := Subgroup.mem_centralizer_iff.mp hg.2 t (SetLike.mem_coe.mpr htC₁)
        exact (hmemC₁ g).mpr h.symm
      rcases CFSG.QuasithinUnique.suzuki_selfCentralizing_four (G := P) (T := ⊤) (U := C₁)
          (hP.to_subgroup ⊤) le_top hcard4 hsq hCtop htop with
        ⟨k, _, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      ·
        obtain ⟨f⟩ : Nonempty (DihedralGroup (2 ^ k) ≃* P) := ⟨e.symm.trans Subgroup.topEquiv⟩
        refine ⟨Subgroup.zpowers (f (DihedralGroup.r (1 : ZMod (2 ^ k)))), inferInstance, ?_⟩
        have hidx : (Subgroup.zpowers (DihedralGroup.r (1 : ZMod (2 ^ k)))).index = 2 := by
          have h : Nat.card (Subgroup.zpowers (DihedralGroup.r (1 : ZMod (2 ^ k)))) *
              (Subgroup.zpowers (DihedralGroup.r (1 : ZMod (2 ^ k)))).index =
              Nat.card (DihedralGroup (2 ^ k)) :=
            Subgroup.card_mul_index (Subgroup.zpowers (DihedralGroup.r (1 : ZMod (2 ^ k))))
          rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h
          have hpos : 0 < 2 ^ k := by positivity
          apply Nat.eq_of_mul_eq_mul_left hpos
          rw [h, mul_comm]
        have hmap : Subgroup.zpowers (f (DihedralGroup.r (1 : ZMod (2 ^ k)))) =
            (Subgroup.zpowers (DihedralGroup.r (1 : ZMod (2 ^ k)))).map
              (f : DihedralGroup (2 ^ k) →* P) :=
          (MonoidHom.map_zpowers (f : DihedralGroup (2 ^ k) →* P)
            (DihedralGroup.r (1 : ZMod (2 ^ k)))).symm
        rw [hmap, Subgroup.index_map_equiv]
        exact le_of_eq hidx
      ·
        obtain ⟨f⟩ : Nonempty (SemidihedralGroup n ≃* P) := ⟨e.symm.trans Subgroup.topEquiv⟩
        refine ⟨Subgroup.zpowers (f (CFSG.Semidihedral.r n)), inferInstance, ?_⟩
        exact le_of_eq ((CFSG.Semidihedral.supplied_index_two n hn f _).mpr (Or.inl rfl))

end CFSG.EvenSporadicStandard.Fin76b
