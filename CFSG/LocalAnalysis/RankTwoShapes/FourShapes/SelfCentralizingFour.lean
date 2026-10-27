module

public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.CyclicNormal
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.RankTwoShapes

open CFSG.LargeEvenClassification

theorem top_eq_sup_zpowers_of_index_two {G : Type*} [Group G] {H : Subgroup G}
    (hH : H.index = 2) {g : G} (hg : g ∉ H) : ⊤ = H ⊔ Subgroup.zpowers g := by
  have hHK : H ≤ H ⊔ Subgroup.zpowers g := le_sup_left
  have hdvd : (H ⊔ Subgroup.zpowers g).index ∣ 2 := hH ▸ Subgroup.index_dvd_of_le hHK
  have hK2 : (H ⊔ Subgroup.zpowers g).index ≠ 2 := by
    intro hK2
    have h1 := Subgroup.relIndex_mul_index hHK
    rw [hK2, hH] at h1
    have h2 : H.relIndex (H ⊔ Subgroup.zpowers g) = 1 := by omega
    rw [Subgroup.relIndex_eq_one] at h2
    exact hg (h2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers g)))
  have hK1 : (H ⊔ Subgroup.zpowers g).index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd h hK2
  exact (Subgroup.index_eq_one.mp hK1).symm

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {z g : G} (hoz : orderOf z = 2)
    (hg : g ∈ Subgroup.zpowers z) : g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, hoz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_one]

theorem eq_of_mem_card_four {G : Type*} [Group G] {V : Subgroup G} (hV : Nat.card V = 4)
    {a b : G} (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hab1 : a * b ≠ 1) (haba : a * b ≠ a) (habb : a * b ≠ b) {g : G} (hg : g ∈ V) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hg1, hga, hgb, hgab⟩ := hcon
  have hsub : (({1, a, b, a * b, g} : Finset G) : Set G) ⊆ (V : Set G) := by
    intro k hk
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact ha
    · exact hb
    · exact V.mul_mem ha hb
    · exact hg
  have h5 : ({1, a, b, a * b, g} : Finset G).card = 5 := by
    have h1 : (1 : G) ∉ ({a, b, a * b, g} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm, hg1.symm⟩
    have h2 : a ∉ ({b, a * b, g} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, haba.symm, hga.symm⟩
    have h3 : b ∉ ({a * b, g} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨habb.symm, hgb.symm⟩
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_pair hgab.symm]
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, h5, ← Nat.card_coe_set_eq,
    show Nat.card (V : Set G) = Nat.card V from rfl, hV] at hcard
  omega

open CFSG.Open in
theorem semidihedral_of_generators {P : Type*} [Group P] [Finite P] {a : ℕ} (ha : 3 ≤ a)
    (h t : P) (hh : orderOf h = 2 ^ a) (ht : t ^ 2 = 1)
    (hconj : t * h * t⁻¹ = h ^ (2 ^ (a - 1) - 1))
    (hgen : ⊤ = Subgroup.zpowers h ⊔ Subgroup.zpowers t) (hcard : Nat.card P = 2 ^ (a + 1)) :
    Nonempty (P ≃* SemidihedralGroup (a + 1)) := by
  let f : SemidihedralGroup (a + 1) →* P := PresentedGroup.toGroup (f := ![h, t]) (by
    intro w hw
    simp only [semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero]
      rw [show a + 1 - 1 = a by omega, ← hh, pow_orderOf_eq_one]
    · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
        Matrix.cons_val_zero] using ht
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [show a + 1 - 2 = a - 1 by omega, hconj, mul_inv_cancel])
  have hh' : h ∈ f.range := ⟨PresentedGroup.of 0, by simp [f]⟩
  have ht' : t ∈ f.range := ⟨PresentedGroup.of 1, by simp [f]⟩
  have hsurj : Function.Surjective f := by
    intro g
    have hg : g ∈ (⊤ : Subgroup P) := Subgroup.mem_top g
    rw [hgen] at hg
    exact (sup_le (Subgroup.zpowers_le.mpr hh') (Subgroup.zpowers_le.mpr ht')) hg
  have : Finite (SemidihedralGroup (a + 1)) := CFSG.Semidihedral.presentation_finite (a + 1)
    (by omega)
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (by rw [hcard, CFSG.Semidihedral.card (a + 1) (by omega)])
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

theorem dihedral_four_of_normal_four {P : Type*} [Group P] [Finite P] (H : Subgroup P)
    (hHn : H.Normal) (hHcard : Nat.card H = 4) (hHexp : ∀ k ∈ H, k ^ 2 = 1)
    (hHcent : Subgroup.centralizer (H : Set P) = H) {z : P} (hzH : z ∈ H) (hz1 : z ≠ 1)
    (hzc : ∀ g : P, g * z = z * g) (hHtop : H ≠ ⊤) :
    Nonempty (P ≃* DihedralGroup 4) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := hHexp z hzH
  have hoz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  obtain ⟨w, hwH, hwz⟩ : ∃ w ∈ H, w ∉ Subgroup.zpowers z := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show H ≤ Subgroup.zpowers z from hall)
    rw [hHcard, Nat.card_zpowers, hoz] at h1
    norm_num at h1
  have hw1 : w ≠ 1 := fun h => hwz (h ▸ Subgroup.one_mem _)
  have hwz' : w ≠ z := fun h => hwz (h ▸ Subgroup.mem_zpowers z)
  have hw2 : w ^ 2 = 1 := hHexp w hwH
  have hzw1 : z * w ≠ 1 := fun h => hwz' (by
    have e : w = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [e]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, hz2]))
  have hzwz : z * w ≠ z := fun h => hw1 (mul_eq_left.mp h)
  have hzww : z * w ≠ w := fun h => hz1 (mul_eq_right.mp h)
  have hHcases : ∀ k ∈ H, k = 1 ∨ k = z ∨ k = w ∨ k = z * w := fun k hk =>
    eq_of_mem_card_four hHcard hzH hwH hz1 hw1 hwz'.symm hzw1 hzwz hzww hk
  have hcentw : ∀ g : P, g * w = w * g → g ∈ H := by
    intro g hg
    rw [← hHcent, Subgroup.mem_centralizer_iff]
    intro k hk
    rcases hHcases k hk with rfl | rfl | rfl | rfl
    · simp
    · exact (hzc g).symm
    · exact hg.symm
    · calc z * w * g = z * (w * g) := mul_assoc _ _ _
        _ = z * (g * w) := by rw [hg]
        _ = g * (z * w) := by rw [← mul_assoc, ← hzc g, mul_assoc]
  have hout : ∀ g : P, g ∉ H → g * w * g⁻¹ = z * w := by
    intro g hg
    have hmem : g * w * g⁻¹ ∈ H := hHn.conj_mem w hwH g
    rcases hHcases _ hmem with h1 | h1 | h1 | h1
    · exfalso
      apply hw1
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply hwz'
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * (z * g) := by rw [h1, mul_assoc]
        _ = z := by rw [← hzc g, inv_mul_cancel_left]
    · exfalso
      apply hg
      apply hcentw
      calc g * w = g * w * g⁻¹ * g := by group
        _ = w * g := by rw [h1]
    · exact h1
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ ∉ H := by
    by_contra hall
    push Not at hall
    exact hHtop (eq_top_iff.mpr fun g _ => hall g)
  have hprod : ∀ g g' : P, g ∉ H → g' ∉ H → g * g' ∈ H := by
    intro g g' hg hg'
    apply hcentw
    have h1 : (g * g') * w * (g * g')⁻¹ = w := by
      calc (g * g') * w * (g * g')⁻¹ = g * (g' * w * g'⁻¹) * g⁻¹ := by group
        _ = g * (z * w) * g⁻¹ := by rw [hout g' hg']
        _ = z * (g * w * g⁻¹) := by rw [← mul_assoc, hzc g]; group
        _ = z * (z * w) := by rw [hout g hg]
        _ = w := by rw [← mul_assoc, ← pow_two, hz2, one_mul]
    calc g * g' * w = (g * g') * w * (g * g')⁻¹ * (g * g') := by group
      _ = w * (g * g') := by rw [h1]
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨g₀, fun b => ?_⟩
    by_cases hb : b ∈ H
    · have hbg : b * g₀ ∉ H := fun h => hg₀ (by simpa using H.mul_mem (H.inv_mem hb) h)
      exact Or.inr ⟨hb, hbg⟩
    · exact Or.inl ⟨hprod b g₀ hb hg₀, hb⟩
  have hPcard : Nat.card P = 8 := by
    have h1 := Subgroup.card_mul_index H
    rw [hHcard, hidx] at h1
    omega
  obtain ⟨u, huH, hu2⟩ : ∃ u, u ∉ H ∧ u ^ 2 = 1 := by
    have hsq : g₀ ^ 2 ∈ H := by
      rw [pow_two]
      exact Subgroup.mul_self_mem_of_index_two hidx g₀
    have hcomm : g₀ * g₀ ^ 2 = g₀ ^ 2 * g₀ := by rw [← pow_succ', ← pow_succ]
    rcases hHcases _ hsq with h1 | h1 | h1 | h1
    · exact ⟨g₀, hg₀, h1⟩
    · refine ⟨g₀ * w, fun h => hg₀ (by simpa using H.mul_mem h (H.inv_mem hwH)), ?_⟩
      calc (g₀ * w) ^ 2 = (g₀ * w * g₀⁻¹) * (g₀ * g₀) * w := by rw [pow_two]; group
        _ = z * w * z * w := by rw [hout g₀ hg₀, ← pow_two, h1]
        _ = z * (w * z) * w := by group
        _ = z * (z * w) * w := by rw [hzc w]
        _ = z ^ 2 * w ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hz2, hw2, one_mul]
    · exfalso
      apply hg₀
      apply hcentw
      rw [← h1]
      exact hcomm
    · exfalso
      apply hg₀
      apply hcentw
      have h2 : g₀ * (z * w) = (z * w) * g₀ := by rw [← h1]; exact hcomm
      calc g₀ * w = z⁻¹ * (z * (g₀ * w)) := by group
        _ = z⁻¹ * (g₀ * (z * w)) := by rw [← mul_assoc z, ← hzc g₀, mul_assoc]
        _ = z⁻¹ * ((z * w) * g₀) := by rw [h2]
        _ = w * g₀ := by group
  have huw : u * w * u⁻¹ = z * w := hout u huH
  have hr2 : (w * u) ^ 2 = z := by
    calc (w * u) ^ 2 = w * (u * w * u⁻¹) * u ^ 2 := by rw [pow_two, pow_two]; group
      _ = w * (z * w) := by rw [huw, hu2, mul_one]
      _ = z := by rw [← mul_assoc, hzc w, mul_assoc, ← pow_two, hw2, mul_one]
  have hor : orderOf (w * u) = 4 := by
    have h1 : ¬ (w * u) ^ 2 ^ 1 = 1 := by rw [pow_one, hr2]; exact hz1
    have h2 : (w * u) ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hr2, hz2]
    simpa using orderOf_eq_prime_pow h1 h2
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hu2])
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hw2])
  have hrel : u * (w * u) * u⁻¹ = (w * u)⁻¹ := by
    rw [show u * (w * u) * u⁻¹ = u * w by group, mul_inv_rev, hu', hw']
  have hur : u ∉ Subgroup.zpowers (w * u) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcomm : u * (w * u) = (w * u) * u := by
      have hc : Commute ((w * u) ^ k) (w * u) := Commute.zpow_self (w * u) k
      rw [hk] at hc
      exact hc.eq
    apply huH
    apply hcentw
    have h1 : u * w * u = w * u * u := by simpa only [mul_assoc] using hcomm
    exact mul_right_cancel h1
  have hidxr : (Subgroup.zpowers (w * u)).index = 2 := by
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers (w * u))
    rw [Nat.card_zpowers, hor, hPcard] at h1
    omega
  have hD := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (w * u) u
    (top_eq_sup_zpowers_of_index_two hidxr hur) hu2 hrel hur
  rw [hor] at hD
  exact hD

open CFSG.Open in
theorem selfCentralizing_four_shapes {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (V : Subgroup P) (hVab : IsMulCommutative V) (hVexp : ∀ v ∈ V, v ^ 2 = 1)
    (hVcard : Nat.card V = 4) (hcent : Subgroup.centralizer (V : Set P) = V) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ (n - 1)))) ∨
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* SemidihedralGroup n)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVne : V ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hVcard
    norm_num at hVcard
  obtain ⟨⟨v₀, hv₀V⟩, hv₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hVne
  have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have : Nontrivial P := ⟨⟨v₀, 1, hv₀1'⟩⟩
  by_cases hVtop : V = ⊤
  ·
    left
    refine ⟨2, le_rfl, ?_⟩
    have hPab : ∀ g k : P, g * k = k * g := fun g k =>
      setLike_mul_comm (s := V) (hVtop ▸ Subgroup.mem_top g) (hVtop ▸ Subgroup.mem_top k)
    have hPexp : ∀ g : P, g ^ 2 = 1 := fun g => hVexp g (hVtop ▸ Subgroup.mem_top g)
    have hPcard : Nat.card P = 4 := by rw [← hVcard, hVtop, Subgroup.card_top]
    have hord : orderOf v₀ = 2 := orderOf_eq_prime (hPexp v₀) hv₀1'
    have hidx : (Subgroup.zpowers v₀).index = 2 := by
      have h1 := Subgroup.card_mul_index (Subgroup.zpowers v₀)
      rw [Nat.card_zpowers, hord, hPcard] at h1
      omega
    have hne : Subgroup.zpowers v₀ ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hidx
      norm_num at hidx
    obtain ⟨σ, -, hσ⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    have hrel : σ * v₀ * σ⁻¹ = v₀⁻¹ := by
      rw [hPab σ v₀, mul_inv_cancel_right]
      exact (inv_eq_of_mul_eq_one_right (by rw [← pow_two, hPexp])).symm
    have hD := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem v₀ σ
      (top_eq_sup_zpowers_of_index_two hidx hσ) (hPexp σ) hrel hσ
    rw [hord] at hD
    rw [show 2 ^ (2 - 1) = 2 by norm_num]
    exact hD
  have hZV : Subgroup.center P ≤ V := hcent ▸ Subgroup.center_le_centralizer (V : Set P)
  have hZne : Subgroup.center P ≠ V := by
    intro h
    apply hVtop
    rw [← hcent, Subgroup.centralizer_eq_top_iff_subset]
    intro v hv
    rw [SetLike.mem_coe, h]
    exact hv
  have hZbot : Subgroup.center P ≠ ⊥ := (IsPGroup.bot_lt_center hP).ne'
  have hZcard : Nat.card (Subgroup.center P) = 2 := by
    have hdvd : Nat.card (Subgroup.center P) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hVcard]
      exact Subgroup.card_dvd_of_le hZV
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk')) hZbot
    · simpa using hk'
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZV (by rw [hVcard, hk']; norm_num)) hZne
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZbot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzV : z ∈ V := hZV hzZ
  have hz2 : z ^ 2 = 1 := hVexp z hzV
  have hoz : orderOf z = 2 := orderOf_eq_prime hz2 hz1'
  have hZeq : Subgroup.center P = Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ)
    rw [hZcard, Nat.card_zpowers, hoz]
  have hzc : ∀ g : P, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hzZ g
  obtain ⟨t, htV, htZ⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hZV hZne)
  have ht2 : t ^ 2 = 1 := hVexp t htV
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ Subgroup.one_mem _)
  have hzt : z ≠ t := fun h => htZ (h ▸ hzZ)
  have hzt1 : z * t ≠ 1 := fun h => htZ (by
    have e : t = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [e]
    exact Subgroup.inv_mem _ hzZ)
  have hztz : z * t ≠ z := fun h => ht1 (mul_eq_left.mp h)
  have hztt : z * t ≠ t := fun h => hz1' (mul_eq_right.mp h)
  have hVcases : ∀ g ∈ V, g = 1 ∨ g = z ∨ g = t ∨ g = z * t := fun g hg =>
    eq_of_mem_card_four hVcard hzV htV hz1' ht1 hzt hzt1 hztz hztt hg
  have hCt : ∀ g : P, g * t = t * g → g ∈ V := by
    intro g hg
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro k hk
    rcases hVcases k hk with rfl | rfl | rfl | rfl
    · simp
    · exact (hzc g).symm
    · exact hg.symm
    · calc z * t * g = z * (t * g) := mul_assoc _ _ _
        _ = z * (g * t) := by rw [hg]
        _ = g * (z * t) := by rw [← mul_assoc, ← hzc g, mul_assoc]
  have hPcard8 : 8 ≤ Nat.card P := by
    obtain ⟨k, hk⟩ : 4 ∣ Nat.card P := hVcard ▸ Subgroup.card_subgroup_dvd_card V
    have hne4 : Nat.card P ≠ 4 := fun h =>
      hVtop (Subgroup.eq_top_of_card_eq V (by rw [hVcard, h]))
    have hpos : 0 < Nat.card P := Nat.card_pos
    omega
  by_cases hall : ∀ A : Subgroup P, A.Normal → IsMulCommutative A → IsCyclic A
  ·
    obtain ⟨H, hHn, hHcyc, hHidx⟩ := cyclic_abelian_normal_index_two hP hall
    have hHidx2 : H.index = 2 := by
      have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1 : H.index ≠ 1 := by
        intro h1
        rw [Subgroup.index_eq_one] at h1
        apply hVtop
        rw [← hcent, Subgroup.centralizer_eq_top_iff_subset]
        intro v _
        rw [SetLike.mem_coe, Subgroup.mem_center_iff]
        intro g
        exact setLike_mul_comm (s := H) (h1 ▸ Subgroup.mem_top g) (h1 ▸ Subgroup.mem_top v)
      omega
    obtain ⟨h, hhH⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hHcyc
    have hhH' : h ∈ H := hhH ▸ Subgroup.mem_zpowers h
    have hcardP : Nat.card P = 2 * orderOf h := by
      have h1 := Subgroup.card_mul_index H
      rw [hHidx2, ← hhH, Nat.card_zpowers] at h1
      omega
    obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hP h
    have hhpow : h ^ 2 ^ a = 1 := by rw [← ha]; exact pow_orderOf_eq_one h
    have htH : t ∉ H := by
      intro htH
      have hcomm : h * t = t * h := setLike_mul_comm (s := H) hhH' htH
      have h2 := hVexp h (hCt h hcomm)
      have h3 : orderOf h ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
      omega
    have ha2 : 2 ≤ a := by
      by_contra hlt
      push Not at hlt
      have h1 : 2 ^ a ≤ 2 := by
        calc 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      omega
    have htH' : t ∉ Subgroup.zpowers h := by rw [hhH]; exact htH
    have hidxh : (Subgroup.zpowers h).index = 2 := by rw [hhH]; exact hHidx2
    have hgen : ⊤ = Subgroup.zpowers h ⊔ Subgroup.zpowers t :=
      top_eq_sup_zpowers_of_index_two hidxh htH'
    have hfin : IsOfFinOrder h := orderOf_pos_iff.mp (by rw [ha]; positivity)
    have hthH : t * h * t⁻¹ ∈ Subgroup.zpowers h := by
      rw [hhH]
      exact hHn.conj_mem h hhH' t
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
      (hfin.mem_powers_iff_mem_zpowers.mpr hthH)
    have hkk : h ^ (k * k) = h ^ 1 := by
      calc h ^ (k * k) = (h ^ k) ^ k := pow_mul h k k
        _ = (t * h * t⁻¹) ^ k := by rw [hk]
        _ = t * h ^ k * t⁻¹ := conj_pow
        _ = t * (t * h * t⁻¹) * t⁻¹ := by rw [hk]
        _ = t ^ 2 * h * (t ^ 2)⁻¹ := by rw [pow_two]; group
        _ = h ^ 1 := by rw [ht2, pow_one]; group
    have hkz : ((k : ZMod (2 ^ a))) ^ 2 = 1 := by
      have h1 := pow_eq_pow_iff_modEq.mp hkk
      rw [ha] at h1
      have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
      push_cast at h2
      rw [pow_two]
      exact h2
    have hpowcast : ∀ m : ℕ, (k : ZMod (2 ^ a)) = (m : ZMod (2 ^ a)) → h ^ k = h ^ m := by
      intro m hm
      rw [ZMod.natCast_eq_natCast_iff'] at hm
      rw [← pow_mod_orderOf, ha, hm, ← ha, pow_mod_orderOf]
    have hcommV : ∀ j : ℕ, t * h ^ j * t⁻¹ = h ^ j → (h ^ j) ^ 2 = 1 := by
      intro j hj
      apply hVexp
      apply hCt
      calc h ^ j * t = (t * h ^ j * t⁻¹) * t := by rw [hj]
        _ = t * h ^ j := by group
    have hnot1 : (k : ZMod (2 ^ a)) ≠ 1 := by
      intro h1
      have e : h ^ k = h ^ 1 := hpowcast 1 (by rw [h1, Nat.cast_one])
      have h2 := hcommV 1 (by rw [← conj_pow, pow_one, ← hk, e])
      rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ha] at h2
      have h3 := Nat.le_of_dvd (by norm_num) h2
      have h4 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
      omega
    have hnot1p : 3 ≤ a → (k : ZMod (2 ^ a)) ≠ 1 + 2 ^ (a - 1) := by
      intro ha3 h1
      have e : h ^ k = h ^ (1 + 2 ^ (a - 1)) := hpowcast _ (by rw [h1]; simp)
      have hc2 : t * h ^ 2 * t⁻¹ = h ^ 2 := by
        rw [← conj_pow, ← hk, e, ← pow_mul,
          show (1 + 2 ^ (a - 1)) * 2 = 2 + 2 ^ a by
            rw [add_mul, one_mul, ← pow_succ, Nat.sub_add_cancel (by omega)],
          pow_add, hhpow, mul_one]
      have h2 := hcommV 2 hc2
      rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ha] at h2
      have h3 := Nat.le_of_dvd (by norm_num) h2
      have h4 : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
      omega
    have hdih : (k : ZMod (2 ^ a)) = -1 →
        (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ (n - 1)))) ∨
        (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* SemidihedralGroup n)) := by
      intro h1
      have e : h ^ k = h ^ (2 ^ a - 1) := hpowcast _ (by
        rw [h1, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
        rw [show (2 : ZMod (2 ^ a)) ^ a = ((2 ^ a : ℕ) : ZMod (2 ^ a)) by push_cast; rfl,
          ZMod.natCast_self, zero_sub])
      have hrel : t * h * t⁻¹ = h⁻¹ := by
        rw [← hk, e]
        exact eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul (by positivity), hhpow])
      have hD := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem h t hgen ht2 hrel htH'
      rw [ha] at hD
      left
      refine ⟨a + 1, by omega, ?_⟩
      rw [show a + 1 - 1 = a by omega]
      exact hD
    rcases Nat.lt_or_ge a 3 with ha3 | ha3
    · have ha2' : a = 2 := by omega
      subst ha2'
      rcases zmod_four_sq_eq_one _ hkz with h1 | h1
      · exact absurd h1 hnot1
      · exact hdih h1
    · rcases zmod_sq_eq_one_two_pow ha3 _ hkz with h1 | h1 | h1 | h1
      · exact absurd h1 hnot1
      · exact hdih h1
      · exact absurd h1 (hnot1p ha3)
      · have e : h ^ k = h ^ (2 ^ (a - 1) - 1) := hpowcast _ (by
          rw [h1, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
          ring)
        have hrel : t * h * t⁻¹ = h ^ (2 ^ (a - 1) - 1) := by rw [← hk, e]
        have hcard : Nat.card P = 2 ^ (a + 1) := by rw [hcardP, ha, pow_succ, mul_comm]
        right
        exact ⟨a + 1, by omega, semidihedral_of_generators ha3 h t ha ht2 hrel hgen hcard⟩
  ·
    push Not at hall
    obtain ⟨A, hAn, hAab, hAnc⟩ := hall
    have : Finite (Subgroup P) :=
      Finite.of_injective (fun H : Subgroup P => (H : Set P)) SetLike.coe_injective
    obtain ⟨H, hAH, hHmax⟩ :=
      (Set.toFinite {B : Subgroup P | B.Normal ∧ IsMulCommutative B}).exists_le_maximal
        (a := A) ⟨hAn, hAab⟩
    obtain ⟨hHn, hHab⟩ := hHmax.1
    have hHnc : ¬ IsCyclic H := fun hc => hAnc (Subgroup.isCyclic_of_le hAH)
    have hHcent : Subgroup.centralizer (H : Set P) = H :=
      Helpers.maximal_abelian_normal_selfCentralizing Nat.prime_two hP H hHab
        (fun L hL hLab hHL => hHmax.2 ⟨hL, hLab⟩ hHL)
    have hHbot : H ≠ ⊥ := by
      intro h
      apply hHnc
      rw [h]
      infer_instance
    have hzH : z ∈ H := by
      have : Group.IsNilpotent P := hP.isNilpotent
      have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hHbot
      obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h1
      have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
      have hgZ : g ∈ Subgroup.zpowers z := hZeq ▸ hg.2
      rcases eq_one_or_eq_of_mem_zpowers hoz hgZ with h2 | h2
      · exact absurd h2 hg1'
      · exact h2 ▸ hg.1
    obtain ⟨hH4, hHexp, hHtop⟩ : Nat.card H = 4 ∧ (∀ k ∈ H, k ^ 2 = 1) ∧ H ≠ ⊤ := by
      by_cases htH : t ∈ H
      · have hHV : H ≤ V := fun k hk => hCt k (setLike_mul_comm (s := H) hk htH)
        have hdvd : Nat.card H ∣ 2 ^ 2 := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hVcard]
          exact Subgroup.card_dvd_of_le hHV
        have h1 : Nat.card H ≠ 1 := fun h => hHbot (Subgroup.card_eq_one.mp h)
        have h2 : Nat.card H ≠ 2 := fun h => hHnc (isCyclic_of_prime_card h)
        have hH4 : Nat.card H = 4 := by
          obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
          interval_cases j
          · exact absurd (by simpa using hj') h1
          · exact absurd (by simpa using hj') h2
          · simpa using hj'
        have hHeqV : H = V := Subgroup.eq_of_le_of_card_ge hHV (by rw [hH4, hVcard])
        exact ⟨hH4, fun k hk => hVexp k (hHV hk), hHeqV ▸ hVtop⟩
      · have hzfix : MulAut.conjNormal t (⟨z, hzH⟩ : H) = ⟨z, hzH⟩ := by
          apply Subtype.ext
          rw [MulAut.conjNormal_apply, hzc t, mul_inv_cancel_right]
        have hfix : Nat.card {k : H // MulAut.conjNormal t k = k} = 2 := by
          rw [Nat.card_eq_two_iff]
          refine ⟨⟨1, map_one _⟩, ⟨⟨z, hzH⟩, hzfix⟩, ?_, ?_⟩
          · intro h
            apply hz1'
            exact (congrArg (fun w : {k : H // MulAut.conjNormal t k = k} => ((w : H) : P)) h).symm
          · ext ⟨⟨k, hkH⟩, hk⟩
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
            have hk' : t * k * t⁻¹ = k := by
              have := congrArg Subtype.val hk
              rwa [MulAut.conjNormal_apply] at this
            have hkV : k ∈ V := hCt k (by
              calc k * t = t * k * t⁻¹ * t := by rw [hk']
                _ = t * k := by group)
            rcases hVcases k hkV with rfl | rfl | rfl | rfl
            · left
              rfl
            · right
              rfl
            · exact absurd hkH htH
            · exact absurd (by simpa using H.mul_mem (H.inv_mem hzH) hkH) htH
        have hHp : IsPGroup 2 H := hP.to_subgroup H
        have hα2 : (MulAut.conjNormal t : MulAut H) ^ 2 = 1 := by
          rw [← map_pow, ht2, map_one]
        obtain ⟨hH4, hHexp'⟩ := open scoped IsMulCommutative in
          noncyclic_abelian_involution_fixed_two hHp hHnc (MulAut.conjNormal t) hα2 hfix
        refine ⟨hH4, fun k hk => ?_, fun h => htH (h ▸ Subgroup.mem_top t)⟩
        simpa using congrArg Subtype.val (hHexp' ⟨k, hk⟩)
    left
    refine ⟨3, by norm_num, ?_⟩
    rw [show 2 ^ (3 - 1) = 4 by norm_num]
    exact dihedral_four_of_normal_four H hHn hH4 hHexp hHcent hzH hz1' hzc hHtop

end CFSG.RankTwoShapes
