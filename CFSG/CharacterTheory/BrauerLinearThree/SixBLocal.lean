module

public import CFSG.CharacterTheory.BrauerLinearThree.NineLocal

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem eq_one_or_eq_J_of_pow_four (hq : Nat.card F % 4 = 3) {x : G} (hx : x ∈ centerSub φ)
    (h4 : x ^ 4 = 1) : x = 1 ∨ x = J := by
  obtain ⟨u, hu, hcard⟩ := card_centerSub_eq_two_mul_odd φ hZ hZodd hq
  have hfin : Finite (centerSub φ) := Nat.finite_of_card_ne_zero (by
    obtain ⟨k, hk⟩ := hu
    rw [hcard]
    omega)
  have hx2u : x ^ (2 * u) = 1 := by
    have h := pow_card_eq_one' (G := centerSub φ) (x := ⟨x, hx⟩)
    rw [hcard] at h
    exact congrArg Subtype.val h
  have hg : Nat.gcd 4 (2 * u) = 2 := by
    obtain ⟨k, hk⟩ := hu
    rw [hk, show 2 * (2 * k + 1) = 2 * (2 * k + 1) from rfl, Nat.gcd_comm,
      show 4 = 2 * 2 from rfl, Nat.gcd_mul_left]
    simp [Nat.gcd_comm, Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr (by
      rw [Nat.odd_iff]; omega : Odd (2 * k + 1)))]
  have hsq : x ^ 2 = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h4, hx2u⟩
    rwa [hg] at this
  exact eq_one_or_eq_J_of_mem_centerSub φ hZ hZodd h2 hJ hx (by rw [← sq]; exact hsq)

omit [Finite F] in
theorem eq_one_of_mem_rootX₁_of_mem_centerSub [Finite F] {x : G} (hx₁ : x ∈ rootX₁ φ)
    (hxC : x ∈ centerSub φ) : x = 1 := by
  obtain ⟨a, rfl⟩ := (mem_centerSub φ).mp hxC
  have hpow : linearCentralizerHom φ (GeneralLinearGroup.scalar (Fin 2) a) ^
      (Nat.card F - 1) = 1 := by
    have ha : a ^ (Nat.card F - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    rw [← map_pow, ← map_pow, ha, map_one, map_one]
  have hp : linearCentralizerHom φ (GeneralLinearGroup.scalar (Fin 2) a) ^ ringChar F = 1 :=
    pow_ringChar_of_mem_rootX₁ hx₁
  have hcop : Nat.Coprime (ringChar F) (Nat.card F - 1) := coprime_ringChar_card_sub_one F
  have := pow_gcd_eq_one.mpr ⟨hp, hpow⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

include hZ hZodd h2 in
theorem mem_centerSub_of_commute_rootUp {c : F} (hc : c ≠ 0) {t : G} (htJ : J * t = t * J)
    (htc : t * rootUp φ c = rootUp φ c * t) {k : ℕ} (ht : t ^ 2 ^ k = 1) :
    t ∈ centerSub φ := by
  obtain ⟨a, b, rfl⟩ := centralizer_rootUp φ hZ hZodd h2 hc htJ htc
  set s := linearCentralizerHom φ (GeneralLinearGroup.scalar (Fin 2) a) with hs
  have hsC : s ∈ centerSub φ := (mem_centerSub φ).mpr ⟨a, rfl⟩
  have hcomm : Commute s (rootUp φ b) :=
    commute_of_mem_centerSub φ hsC (linearCentralizerHom_commute φ _)
  rw [hcomm.mul_pow] at ht
  have hx : rootUp φ b ^ 2 ^ k = (s ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right ht
  have hx1 : rootUp φ b ^ 2 ^ k = 1 := by
    apply eq_one_of_mem_rootX₁_of_mem_centerSub φ
    · exact (rootX₁ φ).pow_mem ((mem_rootX₁ φ).mpr ⟨b, rfl⟩) _
    · rw [hx]
      exact (centerSub φ).inv_mem ((centerSub φ).pow_mem hsC _)
  have hb1 : rootUp φ b = 1 := by
    have hp := rootUp_pow_ringChar φ b
    have hodd : Odd (ringChar F) :=
      ((CharP.char_is_prime F (ringChar F)).eq_two_or_odd').resolve_left (ringChar_ne_two h2)
    have hcop : Nat.Coprime (2 ^ k) (ringChar F) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have := pow_gcd_eq_one.mpr ⟨hx1, hp⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  rw [hb1, mul_one]
  exact hsC

include φ hZ hZodd h2 hJ in
theorem not_four_dvd_card_centralizer [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) {Q : G} (hQ1 : Q ≠ 1)
    (hQp : Q ^ ringChar F = 1) : ¬ 4 ∣ Nat.card (Subgroup.centralizer ({Q} : Set G)) := by
  intro h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2)
    (G := Subgroup.centralizer ({Q} : Set G)) (by simpa using h4)
  have hTp : IsPGroup 2 T := IsPGroup.of_card hT
  have : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial, hT]
    norm_num
  have hcen := hTp.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center T) := hTp.to_subgroup _
  obtain ⟨k, hk⟩ := hcp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hcen).ne' hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  set t : G := ((((z : Subgroup.center T) : T) : Subgroup.centralizer ({Q} : Set G)) : G)
  have ht2 : orderOf t = 2 := by
    rw [← hz]
    simp only [t, Subgroup.orderOf_coe]
  have htQ : Q * t = t * Q :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (((z : Subgroup.center T) : T) : Subgroup.centralizer ({Q} : Set G)).2).symm
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_J_of_involution φ hZ hZodd h2 hJ hnonab ht2)
  have hQ₁J : J * (g⁻¹ * Q * g) = (g⁻¹ * Q * g) * J := by
    rw [show J = g⁻¹ * t * g by rw [← hg]; group]
    calc g⁻¹ * t * g * (g⁻¹ * Q * g) = g⁻¹ * (t * Q) * g := by group
      _ = g⁻¹ * (Q * t) * g := by rw [htQ]
      _ = g⁻¹ * Q * g * (g⁻¹ * t * g) := by group
  have hQ₁p : (g⁻¹ * Q * g) ^ ringChar F = 1 := by
    rw [show g⁻¹ * Q * g = g⁻¹ * Q * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hQp]
    group
  obtain ⟨h, hhJ, hhx⟩ := exists_conj_mem_rootX₁ φ hZ h2 hQ₁J hQ₁p
  obtain ⟨c, hc⟩ := (mem_rootX₁ φ).mp hhx
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [rootUp, upperGL_zero, map_one] at hc
    apply hQ1
    calc Q = g * h⁻¹ * (h * (g⁻¹ * Q * g) * h⁻¹) * h * g⁻¹ := by group
      _ = 1 := by rw [← hc]; group
  set k := h * g⁻¹ with hk_def
  have hkQ : k * Q * k⁻¹ = rootUp φ c := by
    rw [hc, hk_def]
    group
  have hkt : k * t * k⁻¹ = J := by
    rw [hk_def]
    calc h * g⁻¹ * t * (h * g⁻¹)⁻¹ = h * (g⁻¹ * t * g) * h⁻¹ := by group
      _ = h * J * h⁻¹ := by rw [show g⁻¹ * t * g = J by rw [← hg]; group]
      _ = J := by rw [← hhJ, mul_inv_cancel_right]
  have hmem : ∀ y : T, k * ((y : Subgroup.centralizer ({Q} : Set G)) : G) * k⁻¹ = 1 ∨
      k * ((y : Subgroup.centralizer ({Q} : Set G)) : G) * k⁻¹ = J := by
    intro y
    set w := k * ((y : Subgroup.centralizer ({Q} : Set G)) : G) * k⁻¹ with hw
    have hyQ : ((y : Subgroup.centralizer ({Q} : Set G)) : G) * Q =
        Q * ((y : Subgroup.centralizer ({Q} : Set G)) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (y : Subgroup.centralizer ({Q} : Set G)).2
    have hyt : ((y : Subgroup.centralizer ({Q} : Set G)) : G) * t =
        t * ((y : Subgroup.centralizer ({Q} : Set G)) : G) := by
      have := Subgroup.mem_center_iff.mp (z : Subgroup.center T).2 y
      have h' := congrArg (fun x : T => ((x : Subgroup.centralizer ({Q} : Set G)) : G)) this
      simpa [t] using h'
    have hwJ : J * w = w * J := by
      rw [← hkt, hw]
      calc k * t * k⁻¹ * (k * ↑↑y * k⁻¹) = k * (t * ↑↑y) * k⁻¹ := by group
        _ = k * (↑↑y * t) * k⁻¹ := by rw [hyt]
        _ = k * ↑↑y * k⁻¹ * (k * t * k⁻¹) := by group
    have hwc : w * rootUp φ c = rootUp φ c * w := by
      rw [← hkQ, hw]
      calc k * ↑↑y * k⁻¹ * (k * Q * k⁻¹) = k * (↑↑y * Q) * k⁻¹ := by group
        _ = k * (Q * ↑↑y) * k⁻¹ := by rw [hyQ]
        _ = k * Q * k⁻¹ * (k * ↑↑y * k⁻¹) := by group
    have hw4 : w ^ 2 ^ 2 = 1 := by
      have hy4 : y ^ 2 ^ 2 = 1 := by
        rw [← hT]
        exact pow_card_eq_one'
      have h' := congrArg (fun x : T => ((x : Subgroup.centralizer ({Q} : Set G)) : G)) hy4
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
      rw [hw, conj_pow, h']
      group
    have hwC := mem_centerSub_of_commute_rootUp φ hZ hZodd h2 hc0 hwJ hwc hw4
    exact eq_one_or_eq_J_of_pow_four φ hZ hZodd h2 hJ hq hwC (by simpa using hw4)
  have hinj : Function.Injective fun y : T =>
      k * ((y : Subgroup.centralizer ({Q} : Set G)) : G) * k⁻¹ := by
    intro a b hab
    have hab' : k * ((a : Subgroup.centralizer ({Q} : Set G)) : G) * k⁻¹ =
        k * ((b : Subgroup.centralizer ({Q} : Set G)) : G) * k⁻¹ := hab
    have := mul_left_cancel (mul_right_cancel hab')
    exact Subtype.ext (Subtype.ext this)
  have hle : Nat.card T ≤ Nat.card ({1, J} : Set G) := by
    let f : T → ({1, J} : Set G) := fun y =>
      ⟨k * ((y : Subgroup.centralizer ({Q} : Set G)) : G) * k⁻¹, by
      rcases hmem y with h | h
      · rw [h]; exact Set.mem_insert _ _
      · rw [h]; exact Set.mem_insert_of_mem _ rfl⟩
    have hf : Function.Injective f := fun a b hab => hinj (congrArg Subtype.val hab)
    exact Nat.card_le_card_of_injective f hf
  have h2' : Nat.card ({1, J} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le 1 {J}).trans (by rw [Set.ncard_singleton])
  rw [hT] at hle
  omega

include φ hZ hZodd h2 hJ in
theorem exists_conj_mem_rootX₁_of_even [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {Q : G} (hQp : Q ^ ringChar F = 1)
    (hev : 2 ∣ Nat.card (Subgroup.centralizer ({Q} : Set G))) :
    ∃ g : G, g * Q * g⁻¹ ∈ rootX₁ φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({Q} : Set G)) 2 hev
  have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have htQ : Q * t = t * Q := (Subgroup.mem_centralizer_singleton_iff.mp t.2).symm
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_J_of_involution φ hZ hZodd h2 hJ hnonab ht2)
  have hQ₁J : J * (g⁻¹ * Q * g) = (g⁻¹ * Q * g) * J := by
    rw [show J = g⁻¹ * t * g by rw [← hg]; group]
    calc g⁻¹ * t * g * (g⁻¹ * Q * g) = g⁻¹ * (t * Q) * g := by group
      _ = g⁻¹ * (Q * t) * g := by rw [htQ]
      _ = g⁻¹ * Q * g * (g⁻¹ * t * g) := by group
  have hQ₁p : (g⁻¹ * Q * g) ^ ringChar F = 1 := by
    rw [show g⁻¹ * Q * g = g⁻¹ * Q * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hQp]
    group
  obtain ⟨h, -, hhx⟩ := exists_conj_mem_rootX₁ φ hZ h2 hQ₁J hQ₁p
  exact ⟨h * g⁻¹, by rwa [show h * g⁻¹ * Q * (h * g⁻¹)⁻¹ = h * (g⁻¹ * Q * g) * h⁻¹ by group]⟩

end CFSG.BrauerLinearThree
