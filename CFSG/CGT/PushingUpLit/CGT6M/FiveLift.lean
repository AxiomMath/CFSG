module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveLocal
public import CFSG.CGT.PushingUpLit.CGT6M.Orders
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

variable {L Q : Type*} [Group L] [Group Q]

theorem exists_lift_five [Finite L] (π : L →* Q) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center L) (hK5 : ¬ 5 ∣ Nat.card π.ker)
    {Pbar : Subgroup Q} (hP : IsPGroup 5 Pbar) :
    ∃ P : Subgroup L, (∀ x ∈ P, ∀ y ∈ P, π x = π y → x = y) ∧ P.map π = Pbar ∧
      ∀ g : L, π g ∈ Subgroup.normalizer (Pbar : Set Q) → ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite Q := Finite.of_surjective π hπ
  let Q₁ : Subgroup L := Pbar.comap π
  let π₁ : Q₁ →* Pbar := π.subgroupComap Pbar
  have hπ₁ : Function.Surjective π₁ := by
    intro p
    obtain ⟨x, hx⟩ := hπ p.1
    exact ⟨⟨x, by simp [Q₁, hx]⟩, Subtype.ext hx⟩
  have hker : π₁.ker ≤ Subgroup.center Q₁ := by
    intro x hx
    have h1 : π x.1 = 1 := congrArg Subtype.val hx
    have h2 : x.1 ∈ Subgroup.center L := hK h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro g
    exact Subtype.ext (h2 g.1)
  have : Group.IsNilpotent Pbar := hP.isNilpotent
  have : Group.IsNilpotent Q₁ := Subgroup.isNilpotent_of_ker_le_center π₁ hker
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 5 Q₁))
  have hSc : (S : Subgroup Q₁).Characteristic := Sylow.characteristic_of_normal S inferInstance
  let P : Subgroup L := S.map Q₁.subtype
  have hS5 : IsPGroup 5 (S : Subgroup Q₁) := S.2
  have hinj : ∀ x ∈ P, ∀ y ∈ P, π x = π y → x = y := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hx) hy
    have hz1 : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, hk⟩ := hS5 ⟨s, hs⟩
    have hk' : (x⁻¹ * y) ^ (5 ^ k) = 1 := by
      rw [← hsz]
      have h2 : s ^ (5 ^ k) = 1 := congrArg Subtype.val hk
      have h3 := congrArg Subtype.val h2
      simpa using h3
    have hd1 : orderOf (x⁻¹ * y) ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf (x⁻¹ * y) ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hz1
    have hcop : Nat.Coprime (5 ^ k) (Nat.card π.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hK5)
    have h1 : orderOf (x⁻¹ * y) ∣ 1 := hcop ▸ Nat.dvd_gcd hd1 hd2
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  have hmapS : S.map π₁ = ⊤ := by
    have htop : IsPGroup 5 (⊤ : Subgroup Pbar) := hP.of_equiv Subgroup.topEquiv.symm
    exact ((Sylow.mapSurjective hπ₁ S).is_maximal' htop le_top).symm
  have hPmap : P.map π = Pbar := by
    have h1 : P.map π = (S.map π₁).map Pbar.subtype := by
      simp only [P, Subgroup.map_map]
      rfl
    rw [h1, hmapS, Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨P, hinj, hPmap, fun g hg x hx => ?_⟩
  have hgQ : g ∈ Subgroup.normalizer (Q₁ : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show π h ∈ Pbar ↔ π (g * h * g⁻¹) ∈ Pbar
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hg (π h)
  let φ : MulAut Q₁ := Q₁.normalizerMonoidHom ⟨g, hgQ⟩
  have hφ : S.map φ.toMonoidHom = S := Subgroup.characteristic_iff_map_eq.mp hSc φ
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hx
  have hs' : φ s ∈ (S : Subgroup Q₁) := by
    rw [← hφ]
    exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  refine Subgroup.mem_map.mpr ⟨φ s, hs', ?_⟩
  rw [← hsx]
  rfl

theorem isPGroup_c55 : IsPGroup 5 C55 := by
  refine IsPGroup.of_card (n := 2) ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod,
    ZMod.card]
  norm_num

theorem exists_comb_mapM :
    ∀ w : ZMod 5 × ZMod 5, w ≠ 0 → ∃ c d : Fin 5, (c : ℕ) • w + (d : ℕ) • mapM w = (1, 0) := by
  decide

theorem mapM_surjective : Function.Surjective (AddMonoidHom.toMultiplicative mapM) := by
  intro u
  refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd u).2 - (Multiplicative.toAdd u).1,
    -(Multiplicative.toAdd u).1), ?_⟩
  obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
  simp only [AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, mapM, AddMonoidHom.mk'_apply]
  congr 1
  ext <;> simp

section Data

variable {a b g : Q}

theorem phi_injective (ha1 : a ≠ 1) (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1) (hab : Commute a b)
    (hga : g * a * g⁻¹ = b) (hgb : g * b * g⁻¹ = (a * b)⁻¹) :
    Function.Injective (phi a b ha5 hb5 hab) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  by_contra hne
  obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
  have hw : (i, j) ≠ 0 := fun h => hne (by rw [h]; rfl)
  obtain ⟨c, d, hcd⟩ := exists_comb_mapM (i, j) hw
  have hM := phi_mapM ha5 hb5 hab hga hgb (Multiplicative.ofAdd (i, j))
  rw [hu, mul_one, mul_inv_cancel, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd] at hM
  have h10 : phi a b ha5 hb5 hab (Multiplicative.ofAdd ((1 : ZMod 5), (0 : ZMod 5))) = 1 := by
    rw [← hcd, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow, hu, hM]
    simp
  rw [phi_ofAdd, val_one_zmod5, val_zero_zmod5, pow_one, pow_zero, mul_one] at h10
  exact ha1 h10

theorem mem_normalizer_phi_range (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1) (hab : Commute a b)
    (hga : g * a * g⁻¹ = b) (hgb : g * b * g⁻¹ = (a * b)⁻¹) :
    g ∈ Subgroup.normalizer ((phi a b ha5 hb5 hab).range : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨AddMonoidHom.toMultiplicative mapM u, phi_mapM ha5 hb5 hab hga hgb u⟩
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := mapM_surjective v
    refine ⟨u, ?_⟩
    have h1 := phi_mapM ha5 hb5 hab hga hgb u
    have h2 : g * h * g⁻¹ = g * phi a b ha5 hb5 hab u * g⁻¹ := by rw [← h1]; exact hv.symm
    exact (mul_left_cancel (mul_right_cancel h2)).symm

theorem exists_five_data_of_surjective [Finite L] (π : L →* Q) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center L) (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (ha1 : a ≠ 1) (ha5 : a ^ 5 = 1) (hab : Commute a b) (hga : g * a * g⁻¹ = b)
    (hgb : g * b * g⁻¹ = (a * b)⁻¹) :
    ∃ a' b' g' : L, a' ≠ 1 ∧ a' ^ 5 = 1 ∧ Commute a' b' ∧ g' * a' * g'⁻¹ = b' ∧
      g' * b' * g'⁻¹ = (a' * b')⁻¹ := by
  have hb5 : b ^ 5 = 1 := by
    rw [← hga, conj_pow, ha5]
    group
  have hPbar : IsPGroup 5 (phi a b ha5 hb5 hab).range :=
    isPGroup_c55.of_surjective (phi a b ha5 hb5 hab).rangeRestrict
      (phi a b ha5 hb5 hab).rangeRestrict_surjective
  obtain ⟨P, hinj, hmap, hnorm⟩ := exists_lift_five π hπ hK hK5 hPbar
  obtain ⟨g₁, hg₁⟩ := hπ g
  have hgN' : π g₁ ∈ Subgroup.normalizer (((phi a b ha5 hb5 hab).range : Subgroup Q) : Set Q) := by
    rw [hg₁]
    exact mem_normalizer_phi_range ha5 hb5 hab hga hgb
  have ha_mem : a ∈ (phi a b ha5 hb5 hab).range := ⟨Multiplicative.ofAdd (1, 0), by
    rw [phi_ofAdd, val_one_zmod5, val_zero_zmod5, pow_one, pow_zero, mul_one]⟩
  have hb_mem : b ∈ (phi a b ha5 hb5 hab).range := ⟨Multiplicative.ofAdd (0, 1), by
    rw [phi_ofAdd, val_one_zmod5, val_zero_zmod5, pow_one, pow_zero, one_mul]⟩
  rw [← hmap] at ha_mem hb_mem
  obtain ⟨a', ha'P, ha'⟩ := Subgroup.mem_map.mp ha_mem
  obtain ⟨b', hb'P, hb'⟩ := Subgroup.mem_map.mp hb_mem
  refine ⟨a', b', g₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply ha1
    rw [← ha', h, map_one]
  · exact hinj _ (P.pow_mem ha'P 5) 1 P.one_mem (by rw [map_pow, ha', ha5, map_one])
  · exact hinj _ (P.mul_mem ha'P hb'P) _ (P.mul_mem hb'P ha'P)
      (by rw [map_mul, map_mul, ha', hb']; exact hab.eq)
  · exact hinj _ (hnorm g₁ hgN' a' ha'P) _ hb'P
      (by rw [map_mul, map_mul, map_inv, hg₁, ha', hb', hga])
  · exact hinj _ (hnorm g₁ hgN' b' hb'P) _ (P.inv_mem (P.mul_mem ha'P hb'P))
      (by rw [map_mul, map_mul, map_inv, map_inv, map_mul, hg₁, ha', hb', hgb])

theorem false_of_five_data_image {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hcard : Nat.card V ≤ 2 ^ 8) [Finite L] (ρ : L →* MulAut V) (hρ : Function.Injective ρ)
    (π : L →* Q) (hπ : Function.Surjective π) (hK : π.ker ≤ Subgroup.center L)
    (ha1 : a ≠ 1) (ha5 : a ^ 5 = 1) (hab : Commute a b) (hga : g * a * g⁻¹ = b)
    (hgb : g * b * g⁻¹ = (a * b)⁻¹) : False := by
  have hb5 : b ^ 5 = 1 := by
    rw [← hga, conj_pow, ha5]
    group
  have h25 : 25 ∣ Nat.card Q := by
    have h1 : Nat.card (phi a b ha5 hb5 hab).range = 25 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective (phi_injective ha1 ha5 hb5 hab hga hgb)).toEquiv,
        Nat.card_eq_fintype_card, Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod,
        ZMod.card]
    exact h1 ▸ Subgroup.card_subgroup_dvd_card _
  have hK5 : ¬ 5 ∣ Nat.card π.ker := by
    intro h5
    have hL : Nat.card π.ker * Nat.card Q = Nat.card L :=
      Subgroup.card_ker_mul_card_of_surjective hπ
    have h125 : 5 ^ 3 ∣ Nat.card L := by
      rw [← hL]
      simpa using Nat.mul_dvd_mul h5 h25
    exact not_dvd_cardGL8.2.2 (h125.trans (card_dvd_cardGL8 hV hcard ρ hρ))
  obtain ⟨a', b', g', ha1', ha5', hab', hga', hgb'⟩ :=
    exists_five_data_of_surjective π hπ hK hK5 ha1 ha5 hab hga hgb
  have hW2 : IsPGroup 2 V := fun w => ⟨1, by simpa using hV w⟩
  obtain ⟨d, hd⟩ := hW2.exists_card_eq
  have hd8 : d ≤ 8 := by
    by_contra h
    have : 2 ^ 9 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine false_of_five_local (A := ρ a') (B := ρ b') (G := ρ g') hd hd8 ?_ ?_ ?_ ?_ ?_
  · exact fun h => ha1' (hρ (by rw [h, map_one]))
  · rw [← map_pow, ha5', map_one]
  · exact hab'.map ρ
  · rw [← map_mul, ← map_inv, ← map_mul, hga']
  · rw [← map_mul, ← map_inv, ← map_mul, hgb', map_inv, map_mul]

end Data

end CFSG.CGT.PushingUpLit.CGT6M
