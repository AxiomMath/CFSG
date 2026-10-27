module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanHeisList
public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsZ2Pure

public section

namespace CFSG.AGLEmbedding.KFactProofs.M12Z2

open CFSG.RankThree.PartTwo.Sec19.Step1917Steps

theorem upperCentralSeries_two_eq_top_of_card_eq_prime_cube {p : ℕ} [Fact p.Prime] {P : Type*}
    [Group P] (hP : Nat.card P = p ^ 3) : Subgroup.upperCentralSeries P 2 = ⊤ := by
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hP (by norm_num)
  have hdvd : Nat.card (Subgroup.center P) ∣ p ^ 3 := hP ▸ Subgroup.card_subgroup_dvd_card _
  have hk3 : k ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).1 (hk ▸ hdvd)
  have hq : Nat.card (P ⧸ Subgroup.center P) * p ^ k = p ^ 3 := by
    rw [← hk, ← hP, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)]
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  have hcomm : IsMulCommutative (P ⧸ Subgroup.center P) := by
    interval_cases k
    · have : Nat.card (P ⧸ Subgroup.center P) = p ^ 2 := by
        have h2 : Nat.card (P ⧸ Subgroup.center P) * p ^ 1 = p ^ 2 * p ^ 1 := by rw [hq]; ring
        exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq this
    · have : Nat.card (P ⧸ Subgroup.center P) = p := by
        have h2 : Nat.card (P ⧸ Subgroup.center P) * p ^ 2 = p * p ^ 2 := by rw [hq]; ring
        exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
      have := isCyclic_of_prime_card this
      infer_instance
    · have : Nat.card (P ⧸ Subgroup.center P) = 1 := by
        have h2 : Nat.card (P ⧸ Subgroup.center P) * p ^ 3 = 1 * p ^ 3 := by rw [hq]; ring
        exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
      have : Subsingleton (P ⧸ Subgroup.center P) := (Nat.card_eq_one_iff_unique.1 this).1
      infer_instance
  refine eq_top_iff.2 fun x _ => ?_
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one, ← QuotientGroup.ker_mk' (Subgroup.center P),
    MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm.is_comm.comm _ _)

theorem threeCentralZ2_of_sylow_data {G : Type} [Group G] [Finite G] {K : Subgroup G} {m : ℕ}
    (hm : ¬ 3 ∣ m) (hG : Nat.card G = 3 ^ 3 * m) (hK : Nat.card K = 3 ^ 3)
    {a b h z : G} (haK : a ∈ K) (hbK : b ∈ K)
    (hcen : ∀ y ∈ K, a * y = y * a → b * y = y * b → y = 1 ∨ y = z ∨ y = z⁻¹)
    (hh : z * h = h * a) (hab : a * b ≠ b * a) : ThreeCentralZ2 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro x hx1 ⟨S, hxS, hxc⟩
  have hKp : IsPGroup 3 K := IsPGroup.of_card hK
  have hidx : ¬ 3 ∣ K.index := by
    have h1 := K.card_mul_index
    rw [hK, hG] at h1
    rwa [Nat.eq_of_mul_eq_mul_left (by norm_num) h1]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hKp.toSylow hidx) S
  have hS : ∀ y : G, y ∈ (S : Subgroup G) ↔ ∃ u ∈ K, g * u * g⁻¹ = y := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.smul_def, MulAut.conj_apply]
  obtain ⟨x', hx'K, hx'⟩ := (hS x).1 hxS
  have hcomm : ∀ u ∈ K, u * x' = x' * u := by
    intro u hu
    have := hxc _ ((hS _).2 ⟨u, hu, rfl⟩)
    rw [← hx'] at this
    have h2 := congrArg (fun w => g⁻¹ * w * g) this
    simpa [mul_assoc] using h2
  have hx'1 : x' ≠ 1 := by
    rintro rfl
    exact hx1 (by simpa using hx'.symm)
  have hz : z = h * a * h⁻¹ := by rw [← hh]; group
  obtain ⟨e, heK, heb, hxe⟩ : ∃ e ∈ K, e * b ≠ b * e ∧ x = (g * h) * e * (g * h)⁻¹ := by
    rcases hcen x' hx'K (hcomm a haK) (hcomm b hbK) with h1 | h1 | h1
    · exact absurd h1 hx'1
    · refine ⟨a, haK, hab, ?_⟩
      rw [← hx', h1, hz]
      group
    · refine ⟨a⁻¹, K.inv_mem haK, ?_, ?_⟩
      · intro hba
        apply hab
        have := congrArg (fun w => a * w * a) hba
        simpa [mul_assoc] using this.symm
      · rw [← hx', h1, hz]
        group
  set k : G := g * h with hk
  set P : Subgroup G := K.map (MulAut.conj k).toMonoidHom with hP
  have hPcard : Nat.card P = 3 ^ 3 := by
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj k).injective, hK]
  have hxP : x ∈ P := ⟨e, heK, by simp [MulAut.conj_apply, hxe]⟩
  refine ⟨P, hKp.map _, hxP, ?_, ?_⟩
  · rw [upperCentralSeries_two_eq_top_of_card_eq_prime_cube (p := 3) hPcard]
    trivial
  · intro hc
    have hbP : k * b * k⁻¹ ∈ P := ⟨b, hbK, by simp [MulAut.conj_apply]⟩
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨_, hbP⟩)
    simp only [hxe] at this
    apply heb
    have h2 := congrArg (fun w => k⁻¹ * w * k) this
    simpa [mul_assoc] using h2.symm

theorem mem_heisList {Γ : Type*} [Group Γ] {a b c x : Γ} :
    x ∈ heisList a b c ↔ ∃ i < 3, ∃ j < 3, ∃ k < 3, x = a ^ i * b ^ j * c ^ k := by
  simp only [heisList, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, j, hj, k, hk, rfl⟩
    exact ⟨i, hi, j, hj, k, hk, rfl⟩
  · rintro ⟨i, hi, j, hj, k, hk, rfl⟩
    exact ⟨i, hi, j, hj, k, hk, rfl⟩

theorem one_mem_heisList {Γ : Type*} [Group Γ] (a b c : Γ) : 1 ∈ heisList a b c :=
  mem_heisList.2 ⟨0, by norm_num, 0, by norm_num, 0, by norm_num, by simp⟩

theorem length_heisList {Γ : Type*} [Group Γ] (a b c : Γ) : (heisList a b c).length = 27 := by
  simp [heisList, List.length_flatMap]

theorem mem_closure_of_mem_heisList {Γ : Type*} [Group Γ] {a b c : Γ}
    (hc : c ∈ Subgroup.closure ({a, b} : Set Γ)) {x : Γ} (hx : x ∈ heisList a b c) :
    x ∈ Subgroup.closure ({a, b} : Set Γ) := by
  obtain ⟨i, -, j, -, k, -, rfl⟩ := mem_heisList.1 hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)) (Subgroup.pow_mem _ hc _)

theorem mem_closure_pair_iff_mem_heisList {Γ : Type*} [Group Γ] {a b c : Γ} (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (hc : c ∈ Subgroup.closure ({a, b} : Set Γ))
    (hF : ∀ x ∈ heisList a b c, a * x ∈ heisList a b c ∧ b * x ∈ heisList a b c) (x : Γ) :
    x ∈ Subgroup.closure ({a, b} : Set Γ) ↔ x ∈ heisList a b c := by
  refine ⟨fun hx => ?_, mem_closure_of_mem_heisList hc⟩
  have hai : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact ha3)
  have hbi : b⁻¹ = b * b := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hb3)
  induction hx using Subgroup.closure_induction_left with
  | one => exact one_mem_heisList a b c
  | mul_left y hy z _ hz =>
    rcases hy with rfl | hy
    · exact (hF z hz).1
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hF z hz).2
  | inv_mul_cancel y hy z _ hz =>
    rcases hy with rfl | hy
    · rw [hai, mul_assoc]
      exact (hF _ (hF z hz).1).1
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [hbi, mul_assoc]
      exact (hF _ (hF z hz).2).2

theorem card_closure_pair_of_heisList {Γ : Type*} [Group Γ] {a b c : Γ} (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (hc : c ∈ Subgroup.closure ({a, b} : Set Γ))
    (hnd : (heisList a b c).Nodup)
    (hF : ∀ x ∈ heisList a b c, a * x ∈ heisList a b c ∧ b * x ∈ heisList a b c) :
    Nat.card (Subgroup.closure ({a, b} : Set Γ)) = 27 := by
  classical
  have hset : ((Subgroup.closure ({a, b} : Set Γ) : Subgroup Γ) : Set Γ) =
      ↑(heisList a b c).toFinset := by
    ext x
    simpa using mem_closure_pair_iff_mem_heisList ha3 hb3 hc hF x
  show Nat.card ((Subgroup.closure ({a, b} : Set Γ) : Subgroup Γ) : Set Γ) = 27
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    length_heisList]

theorem threeCentralZ2_of_heisList {Γ : Type} [Group Γ] {M : Subgroup Γ} [Finite M] {m : ℕ}
    (hm : ¬ 3 ∣ m) (hM : Nat.card M = 3 ^ 3 * m) {a b h : Γ} (haM : a ∈ M) (hbM : b ∈ M)
    (hhM : h ∈ M) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hnd : (heisList a b (a * b * a⁻¹ * b⁻¹)).Nodup)
    (hF : ∀ x ∈ heisList a b (a * b * a⁻¹ * b⁻¹),
      a * x ∈ heisList a b (a * b * a⁻¹ * b⁻¹) ∧ b * x ∈ heisList a b (a * b * a⁻¹ * b⁻¹))
    (hcen : ∀ y ∈ heisList a b (a * b * a⁻¹ * b⁻¹), a * y = y * a → b * y = y * b →
      y = 1 ∨ y = a * b * a⁻¹ * b⁻¹ ∨ y = (a * b * a⁻¹ * b⁻¹)⁻¹)
    (hh : (a * b * a⁻¹ * b⁻¹) * h = h * a) (hab : a * b ≠ b * a) : ThreeCentralZ2 M := by
  set c : Γ := a * b * a⁻¹ * b⁻¹ with hc
  set K : Subgroup Γ := Subgroup.closure ({a, b} : Set Γ) with hK
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hbK : b ∈ K := Subgroup.subset_closure (by simp)
  have hcK : c ∈ K := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haK hbK)
    (Subgroup.inv_mem _ haK)) (Subgroup.inv_mem _ hbK)
  have hKM : K ≤ M := (Subgroup.closure_le M).2 (by
    rintro _ (rfl | hx)
    · exact haM
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hbM)
  have hcM : c ∈ M := hKM hcK
  refine threeCentralZ2_of_sylow_data (K := K.subgroupOf M) hm hM ?_
    (a := ⟨a, haM⟩) (b := ⟨b, hbM⟩) (h := ⟨h, hhM⟩) (z := ⟨c, hcM⟩) haK hbK ?_ ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
    exact card_closure_pair_of_heisList ha3 hb3 hcK hnd hF
  · intro y hy hya hyb
    have hyF : (y : Γ) ∈ heisList a b c :=
      (mem_closure_pair_iff_mem_heisList ha3 hb3 hcK hF _).1 hy
    rcases hcen y hyF (congrArg Subtype.val hya) (congrArg Subtype.val hyb) with h1 | h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Or.inl (Subtype.ext h1))
    · exact Or.inr (Or.inr (Subtype.ext h1))
  · exact Subtype.ext hh
  · intro hba
    exact hab (congrArg Subtype.val hba)

end CFSG.AGLEmbedding.KFactProofs.M12Z2
