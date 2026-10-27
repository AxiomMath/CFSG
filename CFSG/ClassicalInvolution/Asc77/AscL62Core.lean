module

public import CFSG.ClassicalInvolution.Asc77.AscL62Quat

public section

namespace CFSG.ClassicalInvolution.Asc77.AscL62

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

structure CoreCfg (R V : Subgroup G) (z t : G) : Prop where
  quat : IsQuatSub R
  hz : IsUniqueInvolution R z
  V2 : IsPGroup 2 ↥V
  norm : ∀ y ∈ V, conjSub y R = R
  inter : ∀ g ∈ V, g ∈ R → g = 1
  ht : IsUniqueInvolution V t

variable {R V : Subgroup G} {z t : G}

theorem CoreCfg.t_comm_z (h : CoreCfg R V z t) : t * z = z * t := by
  have := h.hz.conj_eq (h.norm t h.ht.mem)
  calc t * z = (t * z * t⁻¹) * t := by group
    _ = z * t := by rw [this]

theorem CoreCfg.exists_order_four (h : CoreCfg R V z t) (hV : V ≠ Subgroup.zpowers t) :
    ∃ x ∈ V, orderOf x = 4 ∧ x * x = t := by
  have hle : Subgroup.zpowers t ≤ V := Subgroup.zpowers_le.mpr h.ht.mem
  obtain ⟨y, hyV, hy⟩ : ∃ y ∈ V, y ∉ Subgroup.zpowers t := by
    by_contra hcon
    push Not at hcon
    exact hV (le_antisymm hcon hle)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, orderOf y = 2 ^ j := by
    have := (IsPGroup.iff_orderOf (p := 2) (G := ↥V)).mp h.V2 ⟨y, hyV⟩
    simpa [Subgroup.orderOf_mk] using this
  have hy1 : y ≠ 1 := fun h1 => hy (h1 ▸ Subgroup.one_mem _)
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    interval_cases j
    · exact hy1 (orderOf_eq_one_iff.mp (by simpa using hj))
    · have hsq : y * y = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hj, pow_one, pow_two] at this
      rcases h.ht.unique y hyV hsq with h1 | h1
      · exact hy1 h1
      · exact hy (h1 ▸ Subgroup.mem_zpowers t)
  have hdvd : 2 ^ (j - 2) ∣ orderOf y := by
    rw [hj]
    exact pow_dvd_pow 2 (by omega)
  have hx4 : orderOf (y ^ 2 ^ (j - 2)) = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hj]
    have : 2 ^ j = 2 ^ (j - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [this]
    exact Nat.mul_div_cancel_left 4 (by positivity)
  refine ⟨y ^ 2 ^ (j - 2), V.pow_mem hyV _, hx4, ?_⟩
  set x := y ^ 2 ^ (j - 2) with hx
  have hxV : x ∈ V := V.pow_mem hyV _
  have hx4' : x ^ 4 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx4] at this
  have hsq : (x * x) * (x * x) = 1 := by
    rw [← hx4']; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hne : x * x ≠ 1 := by
    intro h1
    have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h1
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx4] at this
    omega
  rcases h.ht.unique (x * x) (V.mul_mem hxV hxV) hsq with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem exists_natCard_eq_two_pow {R C : Subgroup G} (hR : IsQuatSub R)
    (hcard : Nat.card R = 2 * Nat.card C) : ∃ j : ℕ, 2 ≤ j ∧ Nat.card C = 2 ^ j := by
  obtain ⟨k, hk, hkc⟩ := hR.natCard_eq
  refine ⟨k + 1, by omega, ?_⟩
  have : 2 * Nat.card C = 2 * 2 ^ (k + 1) := by rw [← hcard, hkc]; ring
  omega

theorem exists_sq_centralizes_order_four [Finite G] {C : Subgroup G} (hC : IsCyclic ↥C)
    (h4 : 4 ∣ Nat.card C) {x : G} (hx : ∀ c ∈ C, x * c * x⁻¹ ∈ C) :
    ∃ c₁ ∈ C, orderOf c₁ = 4 ∧ (x * x) * c₁ * (x * x)⁻¹ = c₁ := by
  obtain ⟨g, hg⟩ := hC.exists_generator
  set c₀ : G := (g : G) with hc₀
  set M := Nat.card C with hM
  have hM0 : 0 < M := Nat.card_pos
  have hord : orderOf c₀ = M := by
    rw [hc₀, Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm⟩ := h4
  have hm0 : 0 < m := by omega
  have hc₁ord : orderOf (c₀ ^ m) = 4 := by
    have hdvd : m ∣ orderOf c₀ := by rw [hord, hm]; exact ⟨4, by ring⟩
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, hm]
    exact Nat.mul_div_cancel 4 hm0
  have hc₁mem : c₀ ^ m ∈ C := C.pow_mem g.2 m
  refine ⟨c₀ ^ m, hc₁mem, hc₁ord, ?_⟩
  have hxc₀ : x * c₀ * x⁻¹ ∈ C := hx c₀ g.2
  obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x * c₀ * x⁻¹, hxc₀⟩)
  have hu' : x * c₀ * x⁻¹ = c₀ ^ u := by
    have := congrArg Subtype.val hu
    simpa using this.symm
  have hxc₁ : x * c₀ ^ m * x⁻¹ = (c₀ ^ m) ^ u := by
    rw [← conj_pow, hu', ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hxx : (x * x) * (c₀ ^ m) * (x * x)⁻¹ = (c₀ ^ m) ^ (u * u) := by
    have e1 : (x * x) * (c₀ ^ m) * (x * x)⁻¹ = x * (x * c₀ ^ m * x⁻¹) * x⁻¹ := by group
    rw [e1, hxc₁, ← conj_zpow, hxc₁, ← zpow_mul]
  have hodd : Odd u := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨r, hr⟩ := hev
    have h2 : (c₀ ^ u) ^ (M / 2) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, hr]
      have hM2 : ((M / 2 : ℕ) : ℤ) * 2 = (M : ℤ) := by omega
      have : (r + r) * ((M / 2 : ℕ) : ℤ) = r * (M : ℤ) := by rw [← hM2]; ring
      rw [this]
      exact orderOf_dvd_iff_zpow_eq_one.mp ⟨r, by rw [hord]; ring⟩
    have h3 : orderOf (x * c₀ * x⁻¹) = M := by
      have := MulEquiv.orderOf_eq (MulAut.conj x) c₀
      simpa [MulAut.conj_apply, hord] using this
    rw [hu'] at h3
    have h4 := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at h4
    have := Nat.le_of_dvd (by omega) h4
    omega
  obtain ⟨s, hs⟩ := hodd
  have hdvd4 : ((orderOf (c₀ ^ m) : ℕ) : ℤ) ∣ u * u - 1 := by
    rw [hc₁ord, hs]
    exact ⟨s * (s + 1), by push_cast; ring⟩
  have h1 := orderOf_dvd_iff_zpow_eq_one.mp hdvd4
  rw [hxx]
  calc (c₀ ^ m) ^ (u * u) = (c₀ ^ m) ^ (u * u - 1) * (c₀ ^ m) := by
        rw [← zpow_add_one]; congr 1; ring
    _ = c₀ ^ m := by rw [h1, one_mul]

theorem CoreCfg.exists_cent_order_four [Finite G] (h : CoreCfg R V z t)
    (hV : V ≠ Subgroup.zpowers t) : ∃ c ∈ R, orderOf c = 4 ∧ c * t = t * c := by
  obtain ⟨x, hxV, -, hxx⟩ := h.exists_order_four hV
  obtain ⟨C, hCR, hCc, hCcard, hCinv⟩ := exists_invariant_cyclic h.quat h.hz h.V2 h.norm
  obtain ⟨j, hj, hjC⟩ := exists_natCard_eq_two_pow h.quat hCcard
  have h4 : 4 ∣ Nat.card C := by
    rw [hjC, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hj
  have hxC : ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro c hc
    have := conj_mem_conjSub (n := x) hc
    rwa [hCinv x hxV] at this
  obtain ⟨c₁, hc₁C, hc₁, hc₁t⟩ := exists_sq_centralizes_order_four hCc h4 hxC
  refine ⟨c₁, hCR hc₁C, hc₁, ?_⟩
  rw [hxx] at hc₁t
  calc c₁ * t = (t * c₁ * t⁻¹) * t := by rw [hc₁t]
    _ = t * c₁ := by group

theorem CoreCfg.four_le_natCard_cent [Finite G] (h : CoreCfg R V z t)
    (hV : V ≠ Subgroup.zpowers t) :
    4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨c, hcR, hc4, hct⟩ := h.exists_cent_order_four hV
  have hle : Subgroup.zpowers c ≤ R ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact ⟨hcR, Subgroup.mem_centralizer_singleton_iff.mpr hct⟩
  calc 4 = Nat.card (Subgroup.zpowers c) := by rw [Nat.card_zpowers, hc4]
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem exists_sq_mem_not_mem {C F : Subgroup G} (hC : ∀ c ∈ C, ∃ j : ℕ, orderOf c = 2 ^ j)
    (hne : ¬ C ≤ F) : ∃ d ∈ C, d ∉ F ∧ d * d ∈ F := by
  classical
  obtain ⟨c, hcC, hcF⟩ : ∃ c ∈ C, c ∉ F := by
    by_contra hcon
    push Not at hcon
    exact hne hcon
  obtain ⟨j, hj⟩ := hC c hcC
  have hex : ∃ i : ℕ, c ^ 2 ^ i ∈ F := by
    refine ⟨j, ?_⟩
    rw [← hj, pow_orderOf_eq_one]
    exact F.one_mem
  have hi₀ := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hi₀
    exact hcF (by simpa using hi₀)
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨c ^ 2 ^ i, C.pow_mem hcC _, ?_, ?_⟩
  · exact Nat.find_min hex (by omega : i < Nat.find hex)
  · rw [← pow_add, ← two_mul, ← pow_succ']
    rw [hi] at hi₀
    exact hi₀

theorem CoreCfg.t_mem_zpowers (h : CoreCfg R V z t) {y : G} (hy : y ∈ V) (hy1 : y ≠ 1) :
    t ∈ Subgroup.zpowers y := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, orderOf y = 2 ^ j := by
    have := (IsPGroup.iff_orderOf (p := 2) (G := ↥V)).mp h.V2 ⟨y, hy⟩
    simpa [Subgroup.orderOf_mk] using this
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0] at hj
    exact hy1 (orderOf_eq_one_iff.mp (by simpa using hj))
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hne : y ^ 2 ^ i ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at this
    have := Nat.le_of_dvd (by positivity) this
    have h2 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hsq : (y ^ 2 ^ i) * (y ^ 2 ^ i) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    have := pow_orderOf_eq_one y
    rwa [hj] at this
  rcases h.ht.unique _ (V.pow_mem hy _) hsq with h1 | h1
  · exact absurd h1 hne
  · rw [← h1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _

theorem CoreCfg.cyclic_le_centralizer [Finite G] (h : CoreCfg R V z t) {C : Subgroup G}
    (hCR : C ≤ R) (hCc : IsCyclic ↥C) (hCinv : ∀ y ∈ V, conjSub y C = C) {x : G} (hxV : x ∈ V)
    (hxx : x * x = t)
    (hcomm : ∀ u ∈ R ⊓ Subgroup.centralizer ({t} : Set G), ∀ v ∈ V, u * v = v * u) :
    ∀ c ∈ C, c * x = x * c := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hcC, hcx⟩ := hcon
  set F : Subgroup G := C ⊓ Subgroup.centralizer ({x} : Set G) with hF
  have hCF : ¬ C ≤ F := fun hle =>
    hcx (Subgroup.mem_centralizer_singleton_iff.mp (hle hcC).2)
  have hC2 : ∀ c ∈ C, ∃ j : ℕ, orderOf c = 2 ^ j := fun c hc =>
    orderOf_eq_two_pow_of_isQuatSub h.quat (hCR hc)
  obtain ⟨d, hdC, hdF, hd2F⟩ := exists_sq_mem_not_mem hC2 hCF
  have hdx : ¬ d * x = x * d := fun hh =>
    hdF ⟨hdC, Subgroup.mem_centralizer_singleton_iff.mpr hh⟩
  have hd2x : (d * d) * x = x * (d * d) := Subgroup.mem_centralizer_singleton_iff.mp hd2F.2
  have hxd : x * d * x⁻¹ ∈ C := by
    have := conj_mem_conjSub (n := x) hdC
    rwa [hCinv x hxV] at this
  set e := d⁻¹ * (x * d * x⁻¹) with he
  have heC : e ∈ C := C.mul_mem (C.inv_mem hdC) hxd
  have he1 : e ≠ 1 := by
    intro h1
    apply hdx
    have h3 : x * d * x⁻¹ = d := by
      have := congrArg (fun w => d * w) h1
      simpa [he, mul_assoc] using this
    calc d * x = (x * d * x⁻¹) * x := by rw [h3]
      _ = x * d := by group
  have hee : e * e = 1 := by
    have h1 : d⁻¹ * (x * d * x⁻¹) = (x * d * x⁻¹) * d⁻¹ :=
      cyclic_comm hCc (C.inv_mem hdC) hxd
    have h2 : (x * d * x⁻¹) * (x * d * x⁻¹) = d * d := by
      calc (x * d * x⁻¹) * (x * d * x⁻¹) = x * (d * d) * x⁻¹ := by group
        _ = ((d * d) * x) * x⁻¹ := by rw [hd2x]
        _ = d * d := by group
    calc e * e = (d⁻¹ * (x * d * x⁻¹)) * (d⁻¹ * (x * d * x⁻¹)) := rfl
      _ = d⁻¹ * ((x * d * x⁻¹) * d⁻¹) * (x * d * x⁻¹) := by group
      _ = d⁻¹ * (d⁻¹ * (x * d * x⁻¹)) * (x * d * x⁻¹) := by rw [← h1]
      _ = (d⁻¹ * d⁻¹) * ((x * d * x⁻¹) * (x * d * x⁻¹)) := by group
      _ = 1 := by rw [h2]; group
  have hez : e = z := by
    rcases h.hz.unique e (hCR heC) hee with h1 | h1
    · exact absurd h1 he1
    · exact h1
  have hxdz : x * d * x⁻¹ = d * z := by
    have : d * e = x * d * x⁻¹ := by rw [he]; group
    rw [← this, hez]
  have hxz : x * z * x⁻¹ = z := h.hz.conj_eq (h.norm x hxV)
  have htd : (x * x) * d * (x * x)⁻¹ = d := by
    calc (x * x) * d * (x * x)⁻¹ = x * (x * d * x⁻¹) * x⁻¹ := by group
      _ = x * (d * z) * x⁻¹ := by rw [hxdz]
      _ = (x * d * x⁻¹) * (x * z * x⁻¹) := by group
      _ = (d * z) * z := by rw [hxdz, hxz]
      _ = d := by rw [mul_assoc, h.hz.sq, mul_one]
  rw [hxx] at htd
  have hdt : d * t = t * d := by
    calc d * t = (t * d * t⁻¹) * t := by rw [htd]
      _ = t * d := by group
  exact hdx (hcomm d ⟨hCR hdC, Subgroup.mem_centralizer_singleton_iff.mpr hdt⟩ x hxV)

theorem CoreCfg.translate_mem [Finite G] (h : CoreCfg R V z t) {C : Subgroup G} (hCR : C ≤ R)
    (hCcard : Nat.card R = 2 * Nat.card C) (hCinv : ∀ y ∈ V, conjSub y C = C) {y g : G}
    (hy : y ∈ V) (hgR : g ∈ R) (hgC : g ∉ C) : g⁻¹ * (y * g * y⁻¹) ∈ C := by
  have h1 : y * g * y⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := y) hgR
    rwa [h.norm y hy] at this
  have h2 : y * g * y⁻¹ ∉ C := by
    intro hc
    apply hgC
    have := conj_mem_conjSub (n := y⁻¹) hc
    rw [hCinv y⁻¹ (V.inv_mem hy)] at this
    simpa [mul_assoc] using this
  exact inv_mul_mem_of_index_two hCR hCcard hgR h1 hgC h2

theorem CoreCfg.exists_phi [Finite G] (h : CoreCfg R V z t) {C : Subgroup G} (hCR : C ≤ R)
    (hCcard : Nat.card R = 2 * Nat.card C) (hCinv : ∀ y ∈ V, conjSub y C = C)
    (hcomm : ∀ c ∈ C, ∀ v ∈ V, c * v = v * c) {b₀ : G} (hb₀R : b₀ ∈ R) (hb₀C : b₀ ∉ C) :
    ∃ φ : ↥V →* ↥C, ∀ y : ↥V, (φ y : G) = b₀⁻¹ * ((y : G) * b₀ * (y : G)⁻¹) := by
  refine ⟨{ toFun := fun y => ⟨b₀⁻¹ * ((y : G) * b₀ * (y : G)⁻¹),
              h.translate_mem hCR hCcard hCinv y.2 hb₀R hb₀C⟩
            map_one' := ?_
            map_mul' := ?_ }, fun y => rfl⟩
  · apply Subtype.ext
    simp
  · intro y y'
    apply Subtype.ext
    have hg' : b₀⁻¹ * ((y' : G) * b₀ * (y' : G)⁻¹) ∈ C :=
      h.translate_mem hCR hCcard hCinv y'.2 hb₀R hb₀C
    set g' := b₀⁻¹ * ((y' : G) * b₀ * (y' : G)⁻¹) with hg'def
    have hy'b : (y' : G) * b₀ * (y' : G)⁻¹ = b₀ * g' := by rw [hg'def]; group
    have hyg : (y : G) * g' * (y : G)⁻¹ = g' := by
      have := hcomm g' hg' y y.2
      calc (y : G) * g' * (y : G)⁻¹ = ((y : G) * g') * (y : G)⁻¹ := rfl
        _ = (g' * (y : G)) * (y : G)⁻¹ := by rw [← this]
        _ = g' := by group
    show b₀⁻¹ * (((y : G) * (y' : G)) * b₀ * ((y : G) * (y' : G))⁻¹) =
      (b₀⁻¹ * ((y : G) * b₀ * (y : G)⁻¹)) * g'
    calc b₀⁻¹ * (((y : G) * (y' : G)) * b₀ * ((y : G) * (y' : G))⁻¹)
        = b₀⁻¹ * ((y : G) * ((y' : G) * b₀ * (y' : G)⁻¹) * (y : G)⁻¹) := by group
      _ = b₀⁻¹ * ((y : G) * (b₀ * g') * (y : G)⁻¹) := by rw [hy'b]
      _ = b₀⁻¹ * (((y : G) * b₀ * (y : G)⁻¹) * ((y : G) * g' * (y : G)⁻¹)) := by group
      _ = (b₀⁻¹ * ((y : G) * b₀ * (y : G)⁻¹)) * g' := by rw [hyg]; group

theorem CoreCfg.phi_injective [Finite G] (h : CoreCfg R V z t) {C : Subgroup G} (hCR : C ≤ R)
    (hCcard : Nat.card R = 2 * Nat.card C) (hcomm : ∀ c ∈ C, ∀ v ∈ V, c * v = v * c)
    (hU : R ⊓ Subgroup.centralizer ({t} : Set G) = C) {b₀ : G} (hb₀R : b₀ ∈ R) (hb₀C : b₀ ∉ C)
    (φ : ↥V →* ↥C) (hφ : ∀ y : ↥V, (φ y : G) = b₀⁻¹ * ((y : G) * b₀ * (y : G)⁻¹)) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro y hy1
  by_contra hne
  have hyne : (y : G) ≠ 1 := fun h' => hne (Subtype.ext h')
  have h1 : b₀⁻¹ * ((y : G) * b₀ * (y : G)⁻¹) = 1 := by rw [← hφ y, hy1]; rfl
  have hyb : (y : G) * b₀ = b₀ * y := by
    have h2 : (y : G) * b₀ * (y : G)⁻¹ = b₀ := by
      have := congrArg (fun w => b₀ * w) h1
      simpa using this
    calc (y : G) * b₀ = ((y : G) * b₀ * (y : G)⁻¹) * y := by group
      _ = b₀ * y := by rw [h2]
  have hyR : ∀ r ∈ R, (y : G) * r = r * y := by
    intro r hr
    by_cases hrC : r ∈ C
    · exact (hcomm r hrC y y.2).symm
    · have hc := inv_mul_mem_of_index_two hCR hCcard hb₀R hr hb₀C hrC
      have hcy := hcomm _ hc y y.2
      have hr' : r = b₀ * (b₀⁻¹ * r) := by group
      rw [hr']
      calc (y : G) * (b₀ * (b₀⁻¹ * r)) = ((y : G) * b₀) * (b₀⁻¹ * r) := by group
        _ = (b₀ * y) * (b₀⁻¹ * r) := by rw [hyb]
        _ = b₀ * ((y : G) * (b₀⁻¹ * r)) := by group
        _ = b₀ * ((b₀⁻¹ * r) * y) := by rw [← hcy]
        _ = (b₀ * (b₀⁻¹ * r)) * y := by group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.t_mem_zpowers y.2 hyne)
  have hRt : ∀ r ∈ R, r * t = t * r := by
    intro r hr
    have hcm : Commute ((y : G) ^ k) r := (show Commute (y : G) r from hyR r hr).zpow_left k
    rw [← hk]
    exact hcm.symm.eq
  have hRU : R ≤ C := fun r hr =>
    hU ▸ ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr (hRt r hr)⟩
  have := Subgroup.card_le_of_le hRU
  have h0 : 0 < Nat.card C := Nat.card_pos
  omega

theorem CoreCfg.natCard_sup (h : CoreCfg R V z t) :
    Nat.card ↥(R ⊔ V) = Nat.card R * Nat.card V := by
  refine CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R V ?_ ?_
  · intro y hy
    exact mem_normalizer_iff_conjSub_eq.mpr (h.norm y hy)
  · rw [Subgroup.disjoint_def]
    intro x hxR hxV
    exact h.inter x hxV hxR

theorem CoreCfg.isWreathed_of_card_eq [Finite G] (h : CoreCfg R V z t) {C : Subgroup G}
    (hCR : C ≤ R) (hCc : IsCyclic ↥C) (hCcard : Nat.card R = 2 * Nat.card C)
    (hCinv : ∀ y ∈ V, conjSub y C = C) (hcomm : ∀ c ∈ C, ∀ v ∈ V, c * v = v * c)
    (hU : R ⊓ Subgroup.centralizer ({t} : Set G) = C) (hVc : IsCyclic ↥V)
    (hVcard : Nat.card V = Nat.card C) : IsWreathed (R ⊔ V) := by
  obtain ⟨j, hj2, hjM⟩ := exists_natCard_eq_two_pow h.quat hCcard
  have hM4 : 4 ≤ Nat.card C := four_le_natCard_of_index_two h.quat hCcard
  have hM4d : 4 ∣ Nat.card C := by
    rw [hjM, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hj2
  set M := Nat.card C with hM
  have hM2 : M / 2 * 2 = M := by omega
  obtain ⟨b₀, hb₀R, hb₀C⟩ : ∃ b₀ ∈ R, b₀ ∉ C := by
    by_contra hcon
    push Not at hcon
    have hle : R ≤ C := hcon
    have := Subgroup.card_le_of_le hle
    have h0 : 0 < Nat.card C := Nat.card_pos
    omega
  obtain ⟨φ, hφ⟩ := h.exists_phi hCR hCcard hCinv hcomm hb₀R hb₀C
  have hinj := h.phi_injective hCR hCcard hcomm hU hb₀R hb₀C φ hφ
  obtain ⟨v, hv⟩ := hVc.exists_generator
  have hvord : orderOf (v : G) = M := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hv, hVcard]
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => cyclic_comm hVc hx hy
  have hzC : z ∈ C := mem_of_index_two h.quat h.hz hCR hCcard
  have hz2 : z * z = 1 := h.hz.sq
  have ht2 : t * t = 1 := h.ht.sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htv : (v : G) ^ (M / 2) = t := by
    have hsq : (v : G) ^ (M / 2) * (v : G) ^ (M / 2) = 1 := by
      rw [← pow_add, ← two_mul, mul_comm, hM2, ← hvord, pow_orderOf_eq_one]
    have hne : (v : G) ^ (M / 2) ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hvord] at this
      have := Nat.le_of_dvd (by omega) this
      omega
    rcases h.ht.unique _ (V.pow_mem v.2 _) hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  set γ : G := b₀⁻¹ * ((v : G) * b₀ * (v : G)⁻¹) with hγ
  have hγC : γ ∈ C := h.translate_mem hCR hCcard hCinv v.2 hb₀R hb₀C
  have hγord : orderOf γ = M := by
    have h1 := orderOf_injective φ hinj v
    have h2 : orderOf ((φ v : ↥C) : G) = orderOf (φ v) := Subgroup.orderOf_coe _
    have h3 : orderOf (v : G) = orderOf v := Subgroup.orderOf_coe _
    have h4 : ((φ v : ↥C) : G) = γ := hφ v
    rw [← h4, h2, h1, ← h3, hvord]
  have hφt : b₀⁻¹ * (t * b₀ * t⁻¹) = z := by
    have htV : t ∈ V := h.ht.mem
    have h1 : (⟨t, htV⟩ : ↥V) = v ^ (M / 2) := Subtype.ext (by simp [htv])
    have h2 := hφ ⟨t, htV⟩
    have h4 : ((φ ⟨t, htV⟩ : ↥C) : G) = γ ^ (M / 2) := by
      rw [h1, map_pow, Subgroup.coe_pow]
      exact congrArg (· ^ (M / 2)) (hφ v)
    have h3 : b₀⁻¹ * (t * b₀ * t⁻¹) = γ ^ (M / 2) := h2.symm.trans h4
    rw [h3]
    have hsq : γ ^ (M / 2) * γ ^ (M / 2) = 1 := by
      rw [← pow_add, ← two_mul, mul_comm, hM2, ← hγord, pow_orderOf_eq_one]
    have hne : γ ^ (M / 2) ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hγord] at this
      have := Nat.le_of_dvd (by omega) this
      omega
    rcases h.hz.unique _ (hCR (C.pow_mem hγC _)) hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hb₀sq : b₀ * b₀ = z := sq_eq_of_not_mem h.quat h.hz hCR hCc hCcard hb₀R hb₀C
  have htb : t * b₀ * t⁻¹ = b₀ * z := by
    have := congrArg (fun w => b₀ * w) hφt
    simpa [mul_assoc] using this
  obtain ⟨b, hb⟩ : ∃ b : G, b = b₀ * t := ⟨_, rfl⟩
  have hbb : b * b = 1 := by
    calc b * b = b₀ * (t * b₀ * t⁻¹) * (t * t) := by rw [hb]; group
      _ = b₀ * (b₀ * z) * 1 := by rw [htb, ht2]
      _ = (b₀ * b₀) * z := by group
      _ = 1 := by rw [hb₀sq, hz2]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have htv' : t * (v : G) = (v : G) * t := hVcomm t h.ht.mem v v.2
  have hzv : z * (v : G) = (v : G) * z := hcomm z hzC v v.2
  have hzγ : z * γ = γ * z := cyclic_comm hCc hzC hγC
  have hvb : (v : G) * b₀ = b₀ * γ * (v : G) := by rw [hγ]; group
  have hb₀inv : b₀⁻¹ = b₀ * z := by
    apply inv_eq_of_mul_eq_one_right
    calc b₀ * (b₀ * z) = (b₀ * b₀) * z := by group
      _ = 1 := by rw [hb₀sq, hz2]
  have htvt : t * (v : G) * t⁻¹ = (v : G) := by rw [htv']; group
  have hbvb : b * (v : G) * b⁻¹ = γ * (v : G) := by
    calc b * (v : G) * b⁻¹ = b₀ * (t * (v : G) * t⁻¹) * b₀⁻¹ := by rw [hb]; group
      _ = b₀ * (v : G) * b₀⁻¹ := by rw [htvt]
      _ = b₀ * (v : G) * (b₀ * z) := by rw [hb₀inv]
      _ = b₀ * ((v : G) * b₀) * z := by group
      _ = b₀ * (b₀ * γ * (v : G)) * z := by rw [hvb]
      _ = (b₀ * b₀) * γ * (v : G) * z := by group
      _ = z * γ * (v : G) * z := by rw [hb₀sq]
      _ = γ * (z * (v : G)) * z := by rw [hzγ]; group
      _ = γ * ((v : G) * z) * z := by rw [hzv]
      _ = γ * (v : G) * (z * z) := by group
      _ = γ * (v : G) := by rw [hz2, mul_one]
  have hγv : γ * (v : G) = (v : G) * γ := hcomm γ hγC v v.2
  refine ⟨(v : G), b * (v : G) * b⁻¹, b, ?_, ?_, ?_, ?_, hbb, rfl, ?_, ?_⟩
  · rw [hvord]; exact hM4
  · have := MulEquiv.orderOf_eq (MulAut.conj b) (v : G)
    simpa [MulAut.conj_apply] using this
  · rw [hbvb]
    calc (v : G) * (γ * (v : G)) = ((v : G) * γ) * (v : G) := by group
      _ = (γ * (v : G)) * (v : G) := by rw [hγv]
  · rw [h.natCard_sup, hCcard, hVcard, hvord]
    ring
  · rw [hbinv]
    calc b * (b * (v : G) * b) * b = (b * b) * (v : G) * (b * b) := by group
      _ = (v : G) := by rw [hbb]; group
  · set cl := Subgroup.closure ({(v : G), b * (v : G) * b⁻¹, b} : Set G) with hcl
    have hvcl : (v : G) ∈ cl := Subgroup.subset_closure (by simp)
    have hbcl : b ∈ cl := Subgroup.subset_closure (by simp)
    have hccl : b * (v : G) * b⁻¹ ∈ cl := Subgroup.subset_closure (by simp)
    apply le_antisymm
    · rw [hcl, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      have hvP : (v : G) ∈ R ⊔ V := Subgroup.mem_sup_right v.2
      have htP : t ∈ R ⊔ V := Subgroup.mem_sup_right h.ht.mem
      have hb₀P : b₀ ∈ R ⊔ V := Subgroup.mem_sup_left hb₀R
      have hbP : b ∈ R ⊔ V := by rw [hb]; exact (R ⊔ V).mul_mem hb₀P htP
      rcases hx with hx | hx | hx
      · rw [hx]; exact hvP
      · rw [hx]; exact (R ⊔ V).mul_mem ((R ⊔ V).mul_mem hbP hvP) ((R ⊔ V).inv_mem hbP)
      · rw [hx]; exact hbP
    · have htcl : t ∈ cl := htv ▸ cl.pow_mem hvcl _
      have hb₀cl : b₀ ∈ cl := by
        have : b₀ = b * t := by
          rw [hb]
          calc b₀ = b₀ * (t * t) := by rw [ht2, mul_one]
            _ = b₀ * t * t := by group
        rw [this]
        exact cl.mul_mem hbcl htcl
      have hγcl : γ ∈ cl := by
        have : γ = (b * (v : G) * b⁻¹) * (v : G)⁻¹ := by rw [hbvb]; group
        rw [this]
        exact cl.mul_mem hccl (cl.inv_mem hvcl)
      have hCcl : C ≤ cl := by
        have hzp : Subgroup.zpowers γ = C := Subgroup.eq_of_le_of_card_ge
          (Subgroup.zpowers_le.mpr hγC) (by rw [Nat.card_zpowers, hγord])
        rw [← hzp]
        exact Subgroup.zpowers_le.mpr hγcl
      refine sup_le ?_ ?_
      · intro r hr
        by_cases hrC : r ∈ C
        · exact hCcl hrC
        · have hc := inv_mul_mem_of_index_two hCR hCcard hb₀R hr hb₀C hrC
          have : r = b₀ * (b₀⁻¹ * r) := by group
          rw [this]
          exact cl.mul_mem hb₀cl (hCcl hc)
      · intro y hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hv ⟨y, hy⟩)
        have : y = (v : G) ^ k := by simpa using (congrArg Subtype.val hk).symm
        rw [this]
        exact cl.zpow_mem hvcl _

@[expose] def CoreDich (R V : Subgroup G) (t : G) : Prop :=
  R ⊓ Subgroup.centralizer ({t} : Set G) = R ∨
    ∃ C : Subgroup G, R ⊓ Subgroup.centralizer ({t} : Set G) = C ∧ C ≤ R ∧ IsCyclic ↥C ∧
      Nat.card R = 2 * Nat.card C ∧ (∀ y ∈ V, conjSub y C = C) ∧
      IsCyclic ↥V ∧ Nat.card V ≤ Nat.card C ∧
      (∀ y ∈ V, ∀ g ∈ R, g ∉ C → g⁻¹ * (y * g * y⁻¹) ∈ C) ∧
      (Nat.card V = Nat.card C → IsWreathed (R ⊔ V))

theorem CoreCfg.core_dichotomy [Finite G] (h : CoreCfg R V z t) (hV : V ≠ Subgroup.zpowers t)
    (hcomm : ∀ u ∈ R ⊓ Subgroup.centralizer ({t} : Set G), ∀ v ∈ V, u * v = v * u) :
    CoreDich R V t := by
  unfold CoreDich
  obtain ⟨x, hxV, -, hxx⟩ := h.exists_order_four hV
  obtain ⟨C, hCR, hCc, hCcard, hCinv⟩ := exists_invariant_cyclic h.quat h.hz h.V2 h.norm
  have hCx := h.cyclic_le_centralizer hCR hCc hCinv hxV hxx hcomm
  have hCU : C ≤ R ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro c hc
    refine ⟨hCR hc, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hxx]
    calc c * (x * x) = (c * x) * x := by group
      _ = (x * c) * x := by rw [hCx c hc]
      _ = x * (c * x) := by group
      _ = x * (x * c) := by rw [hCx c hc]
      _ = (x * x) * c := by group
  rcases eq_or_eq_of_natCard_eq_two_mul hCU inf_le_left hCcard with hUC | hUR
  · right
    have hcommC : ∀ c ∈ C, ∀ v ∈ V, c * v = v * c := fun c hc v hv =>
      hcomm c (hUC ▸ hc) v hv
    obtain ⟨b₀, hb₀R, hb₀C⟩ : ∃ b₀ ∈ R, b₀ ∉ C := by
      by_contra hcon
      push Not at hcon
      have hle : R ≤ C := hcon
      have := Subgroup.card_le_of_le hle
      have h0 : 0 < Nat.card C := Nat.card_pos
      omega
    obtain ⟨φ, hφ⟩ := h.exists_phi hCR hCcard hCinv hcommC hb₀R hb₀C
    have hinj := h.phi_injective hCR hCcard hcommC hUC hb₀R hb₀C φ hφ
    have hVc : IsCyclic ↥V := by
      have := hCc
      exact isCyclic_of_injective φ hinj
    exact ⟨C, hUC, hCR, hCc, hCcard, hCinv, hVc, Nat.card_le_card_of_injective φ hinj,
      fun y hy g hg hgC => h.translate_mem hCR hCcard hCinv hy hg hgC,
      fun hcard => h.isWreathed_of_card_eq hCR hCc hCcard hCinv hcommC hUC hVc hcard⟩
  · exact Or.inl hUR

theorem exists_sq_eq_of_index_two [Finite G] {R C : Subgroup G} (hR : IsQuatSub R) {z : G}
    (hz : IsUniqueInvolution R z) (hCR : C ≤ R) (hCc : IsCyclic ↥C)
    (hcard : Nat.card R = 2 * Nat.card C) : ∃ c₁ ∈ C, c₁ * c₁ = z := by
  obtain ⟨g, hg⟩ := hCc.exists_generator
  set c₀ : G := (g : G) with hc₀
  obtain ⟨j, hj2, hjM⟩ := exists_natCard_eq_two_pow hR hcard
  have hord : orderOf c₀ = Nat.card C := by
    rw [hc₀, Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have h4 : 4 ∣ Nat.card C := by
    rw [hjM, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hj2
  obtain ⟨m, hm⟩ := h4
  have hm0 : 0 < m := by
    have := four_le_natCard_of_index_two hR hcard
    omega
  refine ⟨c₀ ^ m, C.pow_mem g.2 m, ?_⟩
  have hsq : (c₀ ^ m * c₀ ^ m) * (c₀ ^ m * c₀ ^ m) = 1 := by
    calc (c₀ ^ m * c₀ ^ m) * (c₀ ^ m * c₀ ^ m) = c₀ ^ (4 * m) := by
          rw [show 4 * m = m + m + (m + m) by ring, pow_add, pow_add]
      _ = 1 := by rw [← hm, ← hord, pow_orderOf_eq_one]
  have hne : c₀ ^ m * c₀ ^ m ≠ 1 := by
    intro h1
    have h2 : c₀ ^ (2 * m) = 1 := by rw [two_mul, pow_add]; exact h1
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord, hm] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  rcases hz.unique _ (R.mul_mem (hCR (C.pow_mem g.2 m)) (hCR (C.pow_mem g.2 m))) hsq with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem orderOf_eq_of_not_sq {C : Subgroup G} (hCc : IsCyclic ↥C) {j : ℕ}
    (hjM : Nat.card C = 2 ^ j) {γ : G} (hγ : γ ∈ C) (hnsq : ¬ ∃ d ∈ C, d * d = γ) :
    orderOf γ = Nat.card C := by
  obtain ⟨g, hg⟩ := hCc.exists_generator
  set c₀ : G := (g : G) with hc₀
  have hord : orderOf c₀ = Nat.card C := by
    rw [hc₀, Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨γ, hγ⟩)
  have hk' : c₀ ^ k = γ := by simpa using congrArg Subtype.val hk
  have hkodd : Odd k := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    exact hnsq ⟨c₀ ^ m, C.zpow_mem g.2 m, by rw [← hk', hm, ← zpow_add]⟩
  obtain ⟨m, hm⟩ := hkodd
  have hcop : IsCoprime k ((2 : ℤ) ^ j) := by
    refine IsCoprime.pow_right ?_
    exact ⟨1, -m, by rw [hm]; ring⟩
  obtain ⟨u, v, huv⟩ := hcop
  have hc₀mem : c₀ ∈ Subgroup.zpowers γ := by
    refine ⟨u, ?_⟩
    show γ ^ u = c₀
    rw [← hk', ← zpow_mul]
    have h1 : c₀ ^ ((2 : ℤ) ^ j) = 1 := by
      rw [← hord] at hjM
      have : ((2 : ℤ) ^ j) = (orderOf c₀ : ℤ) := by rw [hjM]; push_cast; ring
      rw [this]
      exact orderOf_dvd_iff_zpow_eq_one.mp dvd_rfl
    calc c₀ ^ (k * u) = c₀ ^ (1 - v * 2 ^ j) := by congr 1; linarith
      _ = c₀ := by rw [zpow_sub, zpow_mul' c₀ v ((2 : ℤ) ^ j), h1, one_zpow, zpow_one]; simp
  have hCle : Subgroup.zpowers γ ≤ C := Subgroup.zpowers_le.mpr hγ
  have hCge : C ≤ Subgroup.zpowers γ := by
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have : y = c₀ ^ n := by simpa using (congrArg Subtype.val hn).symm
    rw [this]
    exact (Subgroup.zpowers γ).zpow_mem hc₀mem n
  have : Subgroup.zpowers γ = C := le_antisymm hCle hCge
  rw [← Nat.card_zpowers, this]

theorem CoreCfg.eq_one_or_eq_z_of_comm [Finite G] (h : CoreCfg R V z t)
    (hU : ¬ 4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G))) {c : G} (hc : c ∈ R)
    (hct : c * t = t * c) : c = 1 ∨ c = z := by
  have hcU : c ∈ R ⊓ Subgroup.centralizer ({t} : Set G) :=
    ⟨hc, Subgroup.mem_centralizer_singleton_iff.mpr hct⟩
  have hle : Subgroup.zpowers c ≤ R ⊓ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr hcU
  have hcard := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at hcard
  obtain ⟨j, hj⟩ := orderOf_eq_two_pow_of_isQuatSub h.quat hc
  rw [hj] at hcard
  have hj1 : j ≤ 1 := by
    by_contra hj2
    have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsq : c * c = 1 := by
    interval_cases j
    · have : c = 1 := orderOf_eq_one_iff.mp (by simpa using hj)
      rw [this, mul_one]
    · have := pow_orderOf_eq_one c
      rwa [hj, pow_one, pow_two] at this
  exact h.hz.unique c hc hsq

theorem CoreCfg.exists_theta_eq_sq [Finite G] (h : CoreCfg R V z t) {C : Subgroup G}
    (hCR : C ≤ R) (hCc : IsCyclic ↥C) (hCcard : Nat.card R = 2 * Nat.card C)
    (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (hsmall : ∀ c ∈ R, c * t = t * c → c = 1 ∨ c = z) :
    ∀ d ∈ C, ∃ c ∈ C, c * (t * c * t⁻¹)⁻¹ = d * d := by
  have hz2 : z * z = 1 := h.hz.sq
  have ht2 : t * t = 1 := h.ht.sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  simp only [htinv] at htC ⊢
  have hzC : z ∈ C := mem_of_index_two h.quat h.hz hCR hCcard
  have hz1 : z ≠ 1 := h.hz.ne_one
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := fun x hx y hy => cyclic_comm hCc hx hy
  have htz : t * z * t = z := by
    have := h.hz.conj_eq (h.norm t h.ht.mem)
    rwa [htinv] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hN : ∀ c ∈ C, c * (t * c * t) = 1 ∨ c * (t * c * t) = z := by
    intro c hc
    have hu : t * c * t ∈ C := htC c hc
    have hNC : c * (t * c * t) ∈ C := C.mul_mem hc hu
    apply hsmall _ (hCR hNC)
    have e1 : t * (c * (t * c * t)) * t = c * (t * c * t) := by
      calc t * (c * (t * c * t)) * t = (t * c * t) * c * (t * t) := by group
        _ = (t * c * t) * c := by rw [ht2, mul_one]
        _ = c * (t * c * t) := hcomm _ hu _ hc
    calc c * (t * c * t) * t = (t * (c * (t * c * t)) * t) * t := by rw [e1]
      _ = t * (c * (t * c * t)) * (t * t) := by group
      _ = t * (c * (t * c * t)) := by rw [ht2, mul_one]
  obtain ⟨c₁, hc₁C, hc₁sq⟩ := exists_sq_eq_of_index_two h.quat h.hz hCR hCc hCcard
  have hc₁t : t * c₁ * t = c₁⁻¹ := by
    have hu : t * c₁ * t ∈ C := htC c₁ hc₁C
    have huu : (t * c₁ * t) * (t * c₁ * t) = z := by
      calc (t * c₁ * t) * (t * c₁ * t) = t * c₁ * (t * t) * c₁ * t := by group
        _ = t * (c₁ * c₁) * t := by rw [ht2]; group
        _ = t * z * t := by rw [hc₁sq]
        _ = z := htz
    have h1 : ((t * c₁ * t) * c₁⁻¹) * ((t * c₁ * t) * c₁⁻¹) = 1 := by
      have hc₁i : c₁⁻¹ ∈ C := C.inv_mem hc₁C
      calc ((t * c₁ * t) * c₁⁻¹) * ((t * c₁ * t) * c₁⁻¹)
          = (t * c₁ * t) * ((c₁⁻¹ * (t * c₁ * t)) * c₁⁻¹) := by group
        _ = (t * c₁ * t) * (((t * c₁ * t) * c₁⁻¹) * c₁⁻¹) := by rw [hcomm _ hc₁i _ hu]
        _ = ((t * c₁ * t) * (t * c₁ * t)) * (c₁⁻¹ * c₁⁻¹) := by group
        _ = z * (c₁ * c₁)⁻¹ := by rw [huu]; group
        _ = 1 := by rw [hc₁sq, hzinv, hz2]
    have hmem : (t * c₁ * t) * c₁⁻¹ ∈ R := hCR (C.mul_mem hu (C.inv_mem hc₁C))
    rcases h.hz.unique _ hmem h1 with h2 | h2
    · exfalso
      have hu1 : t * c₁ * t = c₁ := by
        have := congrArg (fun w => w * c₁) h2
        simpa [mul_assoc] using this
      have hcomm' : c₁ * t = t * c₁ := by
        calc c₁ * t = (t * c₁ * t) * t := by rw [hu1]
          _ = t * c₁ * (t * t) := by group
          _ = t * c₁ := by rw [ht2, mul_one]
      rcases hsmall c₁ (hCR hc₁C) hcomm' with h3 | h3
      · rw [h3, mul_one] at hc₁sq
        exact hz1 hc₁sq.symm
      · rw [h3, hz2] at hc₁sq
        exact hz1 hc₁sq.symm
    · have hu2 : t * c₁ * t = z * c₁ := by
        have := congrArg (fun w => w * c₁) h2
        simpa [mul_assoc] using this
      rw [hu2]
      apply eq_inv_of_mul_eq_one_left
      calc z * c₁ * c₁ = z * (c₁ * c₁) := by group
        _ = 1 := by rw [hc₁sq, hz2]
  intro d hd
  rcases hN d hd with hd1 | hd1
  · refine ⟨d, hd, ?_⟩
    have : t * d * t = d⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      exact hd1
    rw [this]
    group
  · refine ⟨d * c₁, C.mul_mem hd hc₁C, ?_⟩
    have hdt : t * d * t = d⁻¹ * z := by
      have : d * (t * d * t) = z := hd1
      calc t * d * t = d⁻¹ * (d * (t * d * t)) := by group
        _ = d⁻¹ * z := by rw [this]
    have hct : t * (d * c₁) * t = (t * d * t) * (t * c₁ * t) := by
      calc t * (d * c₁) * t = (t * d * t) * (t * c₁ * t) * 1 := by
            calc t * (d * c₁) * t = t * d * (t * t) * c₁ * t := by rw [ht2]; group
              _ = (t * d * t) * (t * c₁ * t) * 1 := by group
        _ = (t * d * t) * (t * c₁ * t) := by rw [mul_one]
    rw [hct, hdt, hc₁t]
    have hdi : d⁻¹ ∈ C := C.inv_mem hd
    have hc₁i : c₁⁻¹ ∈ C := C.inv_mem hc₁C
    have e : (d⁻¹ * z * c₁⁻¹)⁻¹ = c₁ * z * d := by
      calc (d⁻¹ * z * c₁⁻¹)⁻¹ = c₁ * z⁻¹ * d := by group
        _ = c₁ * z * d := by rw [hzinv]
    rw [e]
    calc d * c₁ * (c₁ * z * d) = (d * d) * (c₁ * c₁) * z := by
          calc d * c₁ * (c₁ * z * d) = d * (c₁ * (c₁ * z) * d) := by group
            _ = d * (d * (c₁ * (c₁ * z))) := by
              rw [hcomm _ (C.mul_mem hc₁C (C.mul_mem hc₁C hzC)) _ hd]
            _ = (d * d) * (c₁ * c₁) * z := by group
      _ = d * d := by rw [hc₁sq, mul_assoc, hz2, mul_one]

theorem CoreCfg.eq_zpowers_and_isSemidihedral [Finite G] (h : CoreCfg R V z t)
    (hU : ¬ 4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G))) :
    V = Subgroup.zpowers t ∧ IsSemidihedral (R ⊔ V) := by
  have hV : V = Subgroup.zpowers t := by
    by_contra hV
    exact hU (h.four_le_natCard_cent hV)
  refine ⟨hV, ?_⟩
  have hsmall : ∀ c ∈ R, c * t = t * c → c = 1 ∨ c = z := fun c hc hct =>
    h.eq_one_or_eq_z_of_comm hU hc hct
  obtain ⟨C, hCR, hCc, hCcard, hCinv⟩ := exists_invariant_cyclic h.quat h.hz h.V2 h.norm
  have htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C := by
    intro c hc
    have := conj_mem_conjSub (n := t) hc
    rwa [hCinv t h.ht.mem] at this
  obtain ⟨j, hj2, hjM⟩ := exists_natCard_eq_two_pow h.quat hCcard
  have hM4 : 4 ≤ Nat.card C := four_le_natCard_of_index_two h.quat hCcard
  have hM4d : 4 ∣ Nat.card C := by
    rw [hjM, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hj2
  set M := Nat.card C with hM
  have hjM' : M = 2 ^ j := hjM
  have hM2 : M / 2 * 2 = M := by omega
  have hz2 : z * z = 1 := h.hz.sq
  have ht2 : t * t = 1 := h.ht.sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzC : z ∈ C := mem_of_index_two h.quat h.hz hCR hCcard
  have hz1 : z ≠ 1 := h.hz.ne_one
  have hzt : z * t = t * z := h.t_comm_z.symm
  obtain ⟨b₀, hb₀R, hb₀C⟩ : ∃ b₀ ∈ R, b₀ ∉ C := by
    by_contra hcon
    push Not at hcon
    have hle : R ≤ C := hcon
    have := Subgroup.card_le_of_le hle
    have h0 : 0 < Nat.card C := Nat.card_pos
    omega
  have hb₀sq : b₀ * b₀ = z := sq_eq_of_not_mem h.quat h.hz hCR hCc hCcard hb₀R hb₀C
  obtain ⟨γ, hγ⟩ : ∃ γ : G, γ = b₀⁻¹ * (t * b₀ * t⁻¹) := ⟨_, rfl⟩
  have hγC : γ ∈ C := by
    rw [hγ]
    exact h.translate_mem hCR hCcard hCinv h.ht.mem hb₀R hb₀C
  have htb : t * b₀ * t⁻¹ = b₀ * γ := by rw [hγ]; group
  have hγord : orderOf γ = M := by
    refine orderOf_eq_of_not_sq hCc hjM hγC ?_
    rintro ⟨d, hdC, hdd⟩
    obtain ⟨c, hcC, hθ⟩ := h.exists_theta_eq_sq hCR hCc hCcard htC hsmall d hdC
    have hγθ : γ = c * (t * c * t⁻¹)⁻¹ := by rw [← hdd, hθ]
    have hfix : (b₀ * c) * t = t * (b₀ * c) := by
      have h1 : t * (b₀ * c) * t⁻¹ = b₀ * c := by
        calc t * (b₀ * c) * t⁻¹ = (t * b₀ * t⁻¹) * (t * c * t⁻¹) := by group
          _ = (b₀ * γ) * (t * c * t⁻¹) := by rw [htb]
          _ = b₀ * (γ * (t * c * t⁻¹)) := by group
          _ = b₀ * c := by rw [hγθ]; group
      calc (b₀ * c) * t = (t * (b₀ * c) * t⁻¹) * t := by rw [h1]
        _ = t * (b₀ * c) := by group
    have hb₀ : b₀ = (b₀ * c) * c⁻¹ := by group
    rcases hsmall (b₀ * c) (R.mul_mem hb₀R (hCR hcC)) hfix with h1 | h1
    · apply hb₀C
      rw [hb₀, h1, one_mul]
      exact C.inv_mem hcC
    · apply hb₀C
      rw [hb₀, h1]
      exact C.mul_mem hzC (C.inv_mem hcC)
  have hzγpow : γ ^ (M / 2) = z := by
    have hsq : γ ^ (M / 2) * γ ^ (M / 2) = 1 := by
      rw [← pow_add, ← two_mul, mul_comm, hM2, ← hγord, pow_orderOf_eq_one]
    have hne : γ ^ (M / 2) ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hγord] at this
      have := Nat.le_of_dvd (by omega) this
      omega
    rcases h.hz.unique _ (hCR (C.pow_mem hγC _)) hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hzγ : z * γ = γ ^ (M / 2 + 1) := by rw [pow_succ, hzγpow]
  have hzγC : z * γ ∈ C := C.mul_mem hzC hγC
  obtain ⟨a, ha⟩ : ∃ a : G, a = b₀ * t := ⟨_, rfl⟩
  have ha2 : a * a = z * γ := by
    calc a * a = b₀ * (t * b₀ * t⁻¹) * (t * t) := by rw [ha]; group
      _ = b₀ * (b₀ * γ) * 1 := by rw [htb, ht2]
      _ = (b₀ * b₀) * γ := by group
      _ = z * γ := by rw [hb₀sq]
  have hzγord : orderOf (z * γ) = M := by
    rw [hzγ]
    have hodd : Odd (M / 2 + 1) := by
      refine ⟨M / 4, ?_⟩
      omega
    have hcop : (orderOf γ).Coprime (M / 2 + 1) := by
      have h1 : Nat.Coprime (2 ^ j) (M / 2 + 1) :=
        Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
      rw [hγord]
      rwa [← hjM'] at h1
    rw [orderOf_pow' (x := γ) (by omega : M / 2 + 1 ≠ 0), hcop.gcd_eq_one, Nat.div_one, hγord]
  have hcz : z * γ = γ * z := cyclic_comm hCc hzC hγC
  have haM : a ^ M = z := by
    have h1 : a ^ M = (a * a) ^ (M / 2) := by
      rw [← pow_two, ← pow_mul, mul_comm, hM2]
    rw [h1, ha2, (Commute.mul_pow (show Commute z γ from hcz) (M / 2))]
    have hz' : z ^ (M / 2) = 1 := by
      have : M / 2 = 2 * (M / 4) := by omega
      rw [this, pow_mul, pow_two, hz2, one_pow]
    rw [hz', one_mul, hzγpow]
  have haord : orderOf a = 2 ^ (j + 1) := by
    apply orderOf_eq_prime_pow (p := 2) (n := j)
    · rw [← hjM', haM]
      exact hz1
    · rw [pow_succ, ← hjM', pow_mul, haM, pow_two, hz2]
  have haord' : orderOf a = 2 * M := by rw [haord, pow_succ, ← hjM']; ring
  have hM8 : 8 ≤ orderOf a := by rw [haord']; omega
  have hVcard : Nat.card V = 2 := by
    rw [hV, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) h.ht.ne_one
  have hPcard : Nat.card ↥(R ⊔ V) = 2 * orderOf a := by
    rw [h.natCard_sup, hCcard, hVcard, haord']; ring
  have hb₀inv : b₀⁻¹ = b₀ * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hb₀sq, hz2])
  have hzb₀ : b₀ * z = z * b₀ := uniqueInvolution_comm h.hz hb₀R
  have haM1 : a ^ (M - 1) * a = z := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ M), haM]
  have hpm : a ^ (M - 1) = z * a⁻¹ := eq_mul_inv_of_mul_eq haM1
  have key : z * (t * b₀⁻¹) = t * b₀ := by
    calc z * (t * b₀⁻¹) = z * (t * (b₀ * z)) := by rw [hb₀inv]
      _ = (z * t) * (b₀ * z) := by group
      _ = (t * z) * (b₀ * z) := by rw [hzt]
      _ = t * (z * b₀) * z := by group
      _ = t * (b₀ * z) * z := by rw [hzb₀]
      _ = t * b₀ * (z * z) := by group
      _ = t * b₀ := by rw [hz2, mul_one]
  have hrel : t * a * t⁻¹ = a ^ (M - 1) := by
    calc t * a * t⁻¹ = t * b₀ := by rw [ha]; group
      _ = z * (t * b₀⁻¹) := key.symm
      _ = z * a⁻¹ := by rw [ha, mul_inv_rev, htinv]
      _ = a ^ (M - 1) := hpm.symm
  have hnot : t ∉ Subgroup.zpowers a := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcomm : t * a = a * t := by
      rw [← hk]
      exact (Commute.zpow_left (Commute.refl a) k).eq
    have h1 : t * a * t⁻¹ = a := by
      calc t * a * t⁻¹ = a * t * t⁻¹ := by rw [hcomm]
        _ = a := by group
    rw [h1, hpm] at hrel
    have haa : a * a = z := by
      calc a * a = (z * a⁻¹) * a := by rw [← hrel]
        _ = z := by group
    have hγ1 : γ = 1 := by
      have : z * γ = z * 1 := by rw [← ha2, haa, mul_one]
      exact mul_left_cancel this
    rw [hγ1, orderOf_one] at hγord
    omega
  have hcl : Subgroup.closure ({a, t} : Set G) = R ⊔ V := by
    set cl := Subgroup.closure ({a, t} : Set G) with hcl
    have hacl : a ∈ cl := Subgroup.subset_closure (by simp)
    have htcl : t ∈ cl := Subgroup.subset_closure (by simp)
    apply le_antisymm
    · rw [hcl, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx, ha]
        exact (R ⊔ V).mul_mem (Subgroup.mem_sup_left hb₀R) (Subgroup.mem_sup_right h.ht.mem)
      · rw [hx]; exact Subgroup.mem_sup_right h.ht.mem
    · have hb₀cl : b₀ ∈ cl := by
        have : b₀ = a * t := by
          rw [ha]
          calc b₀ = b₀ * (t * t) := by rw [ht2, mul_one]
            _ = b₀ * t * t := by group
        rw [this]
        exact cl.mul_mem hacl htcl
      have hγcl : γ ∈ cl := by
        rw [hγ]
        exact cl.mul_mem (cl.inv_mem hb₀cl) (cl.mul_mem (cl.mul_mem htcl hb₀cl) (cl.inv_mem htcl))
      have hCcl : C ≤ cl := by
        have hzp : Subgroup.zpowers γ = C := Subgroup.eq_of_le_of_card_ge
          (Subgroup.zpowers_le.mpr hγC) (by rw [Nat.card_zpowers, hγord])
        rw [← hzp]
        exact Subgroup.zpowers_le.mpr hγcl
      refine sup_le ?_ ?_
      · intro r hr
        by_cases hrC : r ∈ C
        · exact hCcl hrC
        · have hc := inv_mul_mem_of_index_two hCR hCcard hb₀R hr hb₀C hrC
          have : r = b₀ * (b₀⁻¹ * r) := by group
          rw [this]
          exact cl.mul_mem hb₀cl (hCcl hc)
      · rw [hV]
        exact Subgroup.zpowers_le.mpr htcl
  refine ⟨a, t, hM8, hPcard, ht2, hnot, ?_, hcl⟩
  rw [haord']
  have : 2 * M / 2 - 1 = M - 1 := by omega
  rw [this]
  exact hrel

end CFSG.ClassicalInvolution.Asc77.AscL62
