module

public import CFSG.CGT.Timmesfeld75.Sec4NineAbs
public import CFSG.GroupTheory.CentralQuotientCoprime

public section

namespace CFSG.GroupTheory.StronglyClosedTI

open Subgroup

variable {G : Type*} [Group G]

section OddNormal

variable [Finite G] {Y : Subgroup G}

theorem commute_of_odd_normal (hY2 : ∀ y ∈ Y, y * y = 1) (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G))
    {O : Subgroup G} (hOn : O.Normal) (hOodd : Odd (Nat.card O)) :
    ∀ o ∈ O, ∀ y ∈ Y, y * o = o * y := by
  have hYe : CFSG.Open.IsElemAbelian 2 Y := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => by rw [pow_two]; exact hY2 x hx⟩
    have h1 : ∀ x : Y, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (Subtype.ext (hY2 x x.2))
    have h2 : (a * b)⁻¹ = a * b := h1 (a * b)
    rw [mul_inv_rev, h1, h1] at h2
    exact h2.symm
  have hYO : Y ≤ normalizer (O : Set G) := by
    rw [normalizer_eq_top_iff.mpr hOn]
    exact le_top
  refine CFSG.CGT.Timmesfeld75.oddNormal_comm_of_le_normalizer hYe hY4 O hYO hOodd ?_
  intro n hn u hu hu1 hun y hy
  have hnN := hTI u hu hu1 n hun.symm
  have hc1 : n * y * n⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem ((mem_normalizer_iff.mp hnN y).mp hy) (Y.inv_mem hy)
  have hc2 : n * y * n⁻¹ * y⁻¹ ∈ O := by
    have : n * (y * n⁻¹ * y⁻¹) ∈ O := O.mul_mem hn (hOn.conj_mem _ (O.inv_mem hn) y)
    simpa [mul_assoc] using this
  have hc : n * y * n⁻¹ * y⁻¹ = 1 := by
    have h2 : orderOf (n * y * n⁻¹ * y⁻¹) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hY2 _ hc1)
    have h3 := Nat.dvd_gcd h2 (Subgroup.orderOf_dvd_natCard O hc2)
    rw [(Nat.coprime_two_left.mpr hOodd).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
  exact hc.symm

theorem commute_normalClosure_of_odd_normal (hY2 : ∀ y ∈ Y, y * y = 1) (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G))
    {O : Subgroup G} (hOn : O.Normal) (hOodd : Odd (Nat.card O)) :
    ∀ o ∈ O, ∀ x ∈ normalClosure (Y : Set G), o * x = x * o := by
  haveI := hOn
  intro o ho x hx
  have hC : normalClosure (Y : Set G) ≤ centralizer (O : Set G) := by
    refine normalClosure_le_normal ?_
    intro y hy
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro o' ho'
    exact (commute_of_odd_normal hY2 hY4 hTI hOn hOodd o' ho' y hy).symm
  exact mem_centralizer_iff.mp (hC hx) o ho

end OddNormal

section CentralQuotient

variable {X : Type*} [Group X] [Finite X]

theorem isNilpotent_comap_pCore {C : Subgroup X} [C.Normal] (hC : C ≤ center X) :
    Group.IsNilpotent ↥((CFSG.pCore 2 (X ⧸ C)).comap (QuotientGroup.mk' C)) := by
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 (X ⧸ C)) := CFSG.pCore_isNilpotent
  refine Subgroup.isNilpotent_of_ker_le_center
    ((QuotientGroup.mk' C).subgroupComap (CFSG.pCore 2 (X ⧸ C))) ?_
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro z
  have hxC : (x : X) ∈ C := by
    have h : (QuotientGroup.mk' C) (x : X) = 1 := congrArg Subtype.val hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact Subtype.ext ((Subgroup.mem_center_iff.mp (hC hxC)) z)

theorem pCore_quotient_eq_bot {C : Subgroup X} [C.Normal] (hC : C ≤ center X)
    (hX : CFSG.pCore 2 X = ⊥) : CFSG.pCore 2 (X ⧸ C) = ⊥ := by
  set P := (CFSG.pCore 2 (X ⧸ C)).comap (QuotientGroup.mk' C) with hPdef
  have hPn : P.Normal := (CFSG.pCore_normal (p := 2) (G := X ⧸ C)).comap _
  have hPodd : ¬ 2 ∣ Nat.card P := by
    intro h2
    obtain ⟨Q⟩ : Nonempty (Sylow 2 P) := inferInstance
    have hQ := Sylow.map_le_pCore hPn (isNilpotent_comap_pCore hC) 2 Q
    rw [hX, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
      at hQ
    exact Q.ne_bot_of_dvd_card h2 hQ
  have hmap : P.map (QuotientGroup.mk' C) = CFSG.pCore 2 (X ⧸ C) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) _
  have hdvd : Nat.card (CFSG.pCore 2 (X ⧸ C)) ∣ Nat.card P :=
    hmap ▸ Subgroup.card_map_dvd _ _
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X ⧸ C)).exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hk ▸ hdvd)) hPodd

end CentralQuotient

section TI

variable {Y : Subgroup G}

theorem mem_normalizer_map_of_commute {M : Subgroup G} (hYM : Y ≤ M) {O : Subgroup ↥M}
    [O.Normal] (hOc : O ≤ center ↥M) (hOodd : Odd (Nat.card O)) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G))
    {a : ↥M ⧸ O} (ha : a ∈ (Y.subgroupOf M).map (QuotientGroup.mk' O)) (ha1 : a ≠ 1)
    {x : ↥M ⧸ O} (hxa : x * a = a * x) :
    x ∈ normalizer (((Y.subgroupOf M).map (QuotientGroup.mk' O) : Subgroup (↥M ⧸ O)) :
      Set (↥M ⧸ O)) := by
  obtain ⟨y, hy, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hyY : (y : G) ∈ Y := hy
  have hy1 : (y : G) ≠ 1 := by
    rintro h
    apply ha1
    rw [show y = 1 from Subtype.ext h, map_one]
  have hyy : y * y = 1 := Subtype.ext (hY2 _ hyY)
  have heq : m * y * m⁻¹ = y := by
    refine CFSG.GroupTheory.eq_of_mk_eq_of_pow_eq_one_of_coprime hOc (r := 2)
      (Nat.coprime_two_left.mpr hOodd) ?_ ?_ ?_
    · rw [pow_two]
      calc m * y * m⁻¹ * (m * y * m⁻¹) = m * (y * y) * m⁻¹ := by group
        _ = 1 := by rw [hyy]; group
    · rw [pow_two]
      exact hyy
    · have h : QuotientGroup.mk' O m * QuotientGroup.mk' O y * (QuotientGroup.mk' O m)⁻¹ =
          QuotientGroup.mk' O y := by
        rw [hxa]
        group
      simpa [map_mul, map_inv] using h
  have hmY : (m : G) ∈ normalizer (Y : Set G) := by
    refine hTI y hyY hy1 m ?_
    have h := congrArg Subtype.val heq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  have hm' : m ∈ normalizer ((Y.subgroupOf M : Subgroup M) : Set M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hYM]
    exact hmY
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' O) ⟨m, hm', rfl⟩

end TI

end CFSG.GroupTheory.StronglyClosedTI

end
