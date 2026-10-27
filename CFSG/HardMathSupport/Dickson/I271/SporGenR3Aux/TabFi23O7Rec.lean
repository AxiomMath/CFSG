module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7Y

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.YGroups
open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.RankThree.PartOne.N143.O7 (Om)
open scoped commutatorElement

private theorem card_range_mul_card_ker_aux {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem tabFi23_recog_abstract {Y G O : Type*} [Group Y] [Group G] [Group O] [Finite Y] [Finite G]
    [IsSimpleGroup O] (hO : Subgroup.center O = ⊥)
    (π : Y →* O) (hπ : Function.Surjective π) (hk : Nat.card π.ker = 2)
    (φ : Y →* G) (hnc : ∃ a ∈ φ.range, ∃ b ∈ φ.range, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 3) (hzc : ∀ g ∈ φ.range, g * z = z * g)
    (N : Subgroup G) (hN : φ.range ≤ N) (hzN : z ∈ N) (hNcard : Nat.card N ≤ 3 * Nat.card O) :
    φ.ker = π.ker ∧ z ∉ φ.range := by
  have : Finite O := Finite.of_surjective π hπ
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hle : φ.ker ≤ π.ker := by
    have hnorm : (φ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal O _ _ (φ.ker.map π) hnorm with h | h
    · exact (Subgroup.map_eq_bot_iff _).1 h
    · exfalso
      have hcyc : IsCyclic π.ker := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact isCyclic_of_prime_card hk
      have key : ∀ y : Y, ∃ k : π.ker, φ k = φ y := by
        intro y
        have hy : π y ∈ φ.ker.map π := by rw [h]; trivial
        obtain ⟨m, hm, hmy⟩ := hy
        refine ⟨⟨y * m⁻¹, ?_⟩, ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hmy, mul_inv_cancel]
        · simp only [map_mul, map_inv, MonoidHom.mem_ker.1 hm, inv_one, mul_one]
      obtain ⟨_, ⟨y₁, rfl⟩, _, ⟨y₂, rfl⟩, hab⟩ := hnc
      obtain ⟨k₁, hk₁⟩ := key y₁
      obtain ⟨k₂, hk₂⟩ := key y₂
      apply hab
      rw [← hk₁, ← hk₂, ← map_mul, ← map_mul]
      have hkk : k₁ * k₂ = k₂ * k₁ :=
        isMulCommutative_iff.1 (inferInstance : IsMulCommutative π.ker) k₁ k₂
      have := congrArg (fun k : π.ker => φ k) hkk
      simpa using this
  have hzr : z ∉ φ.range := by
    rintro ⟨y₀, rfl⟩
    have hcen : π y₀ ∈ Subgroup.center O := by
      rw [Subgroup.mem_center_iff]
      intro o
      obtain ⟨y, rfl⟩ := hπ o
      have h1 : ⁅y, y₀⁆ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hzc (φ y) ⟨y, rfl⟩
      have h2 := hle h1
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2
    rw [hO, Subgroup.mem_bot] at hcen
    have hmem : y₀ ∈ π.ker := hcen
    have hsq : (φ y₀) ^ 2 = 1 := by
      rw [← map_pow]
      have h := pow_card_eq_one' (G := π.ker) (x := ⟨y₀, hmem⟩)
      rw [hk] at h
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_pow] at h'
      rw [show y₀ ^ 2 = 1 from h', map_one]
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hz] at this
    omega
  refine ⟨?_, hzr⟩
  by_contra hne
  have hdvd : Nat.card φ.ker ∣ 2 := hk ▸ Subgroup.card_dvd_of_le hle
  have h2 : Nat.card φ.ker ≠ 2 := fun h2 =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hk, h2]))
  have h1 : Nat.card φ.ker = 1 := ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_right h2
  have hY : Nat.card Y = Nat.card O * 2 := by
    have := card_range_mul_card_ker_aux π
    rw [MonoidHom.range_eq_top.2 hπ, Subgroup.card_top, hk] at this
    omega
  have hR : Nat.card φ.range = Nat.card Y := by
    have := card_range_mul_card_ker_aux φ
    rwa [h1, mul_one] at this
  have hlt : Nat.card φ.range < Nat.card N := by
    by_contra hge
    exact hzr (Subgroup.eq_of_le_of_card_ge hN (not_lt.1 hge) ▸ hzN)
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hN
  have h2R : 2 * Nat.card φ.range ≤ Nat.card N := by
    rw [hc] at hlt ⊢
    rcases c with _ | _ | c
    · simp at hlt
    · simp at hlt
    · nlinarith
  omega

@[expose] def y322Img {G : Type*} [Group G] (s : Fin 8 → G) (c : ℕ) : G :=
  if h : c < 8 then s ⟨c, h⟩ else 1

private theorem image_y322Img {G : Type*} [Group G] (s : Fin 8 → G) :
    y322Img s '' Set.Iio (ngen 3 2 2) = Set.range s := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c < 8 := hc
    exact ⟨⟨c, hc'⟩, by simp [y322Img, hc']⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, by simp [y322Img, i.2]⟩

theorem tabFi23_y322_recognition
    {G : Type} [Group G] [Finite G] (s : Fin 8 → G)
    (hrel : ∀ w ∈ yRels 3 2 2, evalWord (y322Img s) w = 1)
    (hnc : ∃ i j, s i * s j ≠ s j * s i)
    (z : G) (hz : orderOf z = 3) (hzc : ∀ i, s i * z = z * s i)
    (hcard : Nat.card ↥(Subgroup.closure (Set.range s ∪ {z})) ≤ 3 * 4585351680) :
    Nonempty (↥(Subgroup.closure (Set.range s)) ≃* ↥Om) ∧
    Nat.card ↥(Subgroup.closure (Set.range s)) = 4585351680 ∧
    z ∉ Subgroup.closure (Set.range s) := by
  obtain ⟨π, hπ, hker, hk⟩ := tabFi23_y322_to_om
  haveI : Finite (YGroup 3 2 2) := Nat.finite_of_card_ne_zero (by rw [card_y322]; norm_num)
  haveI := tabFi23_isSimpleGroup_om
  set φ : YGroup 3 2 2 →* G := yModelHom (y322Img s) hrel with hφ
  have hrange : φ.range = Subgroup.closure (Set.range s) := by
    rw [hφ, range_yModelHom, image_y322Img]
  have hnc' : ∃ a ∈ φ.range, ∃ b ∈ φ.range, a * b ≠ b * a := by
    obtain ⟨i, j, hij⟩ := hnc
    refine ⟨s i, ?_, s j, ?_, hij⟩ <;>
    · rw [hrange]
      exact Subgroup.subset_closure ⟨_, rfl⟩
  have hzc' : ∀ g ∈ φ.range, g * z = z * g := by
    intro g hg
    rw [hrange] at hg
    have hle : Subgroup.closure (Set.range s) ≤ Subgroup.centralizer {z} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hzc i)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  have hN : φ.range ≤ Subgroup.closure (Set.range s ∪ {z}) := by
    rw [hrange]
    exact Subgroup.closure_mono Set.subset_union_left
  have hzN : z ∈ Subgroup.closure (Set.range s ∪ {z}) :=
    Subgroup.subset_closure (Set.mem_union_right _ rfl)
  obtain ⟨hkerEq, hzr⟩ := tabFi23_recog_abstract tabFi23_center_om π hπ hk φ hnc' z hz hzc'
    (Subgroup.closure (Set.range s ∪ {z})) hN hzN (by rw [tabFi23_card_om]; exact hcard)
  let e₀ : ↥φ.range ≃* ↥Om :=
    (QuotientGroup.quotientKerEquivRange φ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
        (QuotientGroup.quotientKerEquivOfSurjective π hπ))
  let e : ↥(Subgroup.closure (Set.range s)) ≃* ↥Om :=
    (MulEquiv.subgroupCongr hrange.symm).trans e₀
  refine ⟨⟨e⟩, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, tabFi23_card_om]
  · rw [← hrange]
    exact hzr

end CFSG.HardMathSupport.Dickson.I271
