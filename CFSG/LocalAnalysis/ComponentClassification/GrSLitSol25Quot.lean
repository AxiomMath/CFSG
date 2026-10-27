module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoprime
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25Comp

public section

namespace CFSG.ComponentClassification.GrSLit.Sol25

open CFSG Subgroup CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

@[expose] def solD (S T : Subgroup G) : Subgroup G :=
  (pPrimeCore 2 (centralizer (S : Set G))).map (centralizer (S : Set G)).subtype ⊓
    centralizer (T : Set G)

noncomputable abbrev solπ (T : Subgroup G) :
    ↥(centralizer (T : Set G)) →* ↥(centralizer (T : Set G)) ⧸
      pPrimeCore 2 ↥(centralizer (T : Set G)) :=
  QuotientGroup.mk' _

abbrev QC (T : Subgroup G) : Type :=
  ↥(centralizer (T : Set G)) ⧸ pPrimeCore 2 ↥(centralizer (T : Set G))

noncomputable abbrev imageS (S T : Subgroup G) :=
  (S.subgroupOf (centralizer (T : Set G))).map (solπ T)

noncomputable abbrev imageD (S T : Subgroup G) :=
  ((solD S T).subgroupOf (centralizer (T : Set G))).map (solπ T)

theorem odd_card_solD (S T : Subgroup G) : Odd (Nat.card (solD S T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Odd (Nat.card ((pPrimeCore 2 (centralizer (S : Set G))).map
      (centralizer (S : Set G)).subtype)) := by
    rw [card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact h1.of_dvd_nat (card_dvd_of_le inf_le_left)

omit [Finite G] in
theorem solD_commute {S T : Subgroup G} {d s : G} (hd : d ∈ solD S T) (hs : s ∈ S) :
    d * s = s * d := by
  obtain ⟨⟨c, -, rfl⟩, -⟩ := mem_inf.mp hd
  exact ((mem_centralizer_iff.mp c.2) s hs).symm

omit [Finite G] in
theorem le_normalizer_solD (S T : Subgroup G) :
    centralizer (T : Set G) ⊓ centralizer (S : Set G) ≤ normalizer (solD S T : Set G) := by
  intro c hc
  obtain ⟨hcT, hcS⟩ := mem_inf.mp hc
  have key : ∀ g ∈ centralizer (T : Set G) ⊓ centralizer (S : Set G), ∀ x ∈ solD S T,
      g * x * g⁻¹ ∈ solD S T := by
    intro g hg x hx
    obtain ⟨hgT, hgS⟩ := mem_inf.mp hg
    obtain ⟨⟨y, hy, rfl⟩, hxT⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨⟨⟨g, hgS⟩ * y * ⟨g, hgS⟩⁻¹, ?_, by simp⟩, ?_⟩
    · exact (inferInstance : (pPrimeCore 2 ↥(centralizer (S : Set G))).Normal).conj_mem y hy _
    · exact mul_mem (mul_mem hgT hxT) (inv_mem hgT)
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key c hc x, fun h => ?_⟩
  have := key c⁻¹ (inv_mem hc) _ h
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this

variable {S T : Subgroup G}

omit [Finite G] in
theorem imageS_mul_self (hS2 : ∀ s ∈ S, s * s = 1) : ∀ a ∈ imageS S T, a * a = 1 := by
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_mul]
  have : s * s = 1 := Subtype.ext (hS2 _ (mem_subgroupOf.mp hs))
  rw [this, map_one]

theorem odd_card_imageD : Odd (Nat.card (imageD S T)) := by
  refine (odd_card_solD S T).of_dvd_nat ?_
  refine (card_map_dvd _ _).trans ?_
  rw [← card_map_of_injective (centralizer (T : Set G)).subtype_injective, subgroupOf_map_subtype]
  exact card_dvd_of_le inf_le_left

theorem eq_one_of_mem_odd_of_pow {X : Type*} [Group X] [Finite X] {Y : Subgroup X}
    (hY : Odd (Nat.card Y)) {x : X} (hx : x ∈ Y) {n : ℕ} (hn : x ^ (2 ^ n) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : Odd (orderOf x) := odd_orderOf_of_mem hY hx
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases k with _ | k
  · rwa [pow_zero, orderOf_eq_one_iff] at hk
  · exfalso
    rw [hk] at h2
    exact (Nat.not_even_iff_odd.mpr h2) (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.succ_ne_zero k)))

theorem exists_lift_centralizer (hS2 : ∀ s ∈ S, s * s = 1)
    (hST : S ≤ centralizer (T : Set G)) {h : QC T}
    (hh : h ∈ centralizer (imageS S T : Set (QC T))) :
    ∃ c : ↥(centralizer (T : Set G)), (c : G) ∈ centralizer (S : Set G) ∧ solπ T c = h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(centralizer (T : Set G))) h
  have hP : IsPGroup 2 (S.subgroupOf (centralizer (T : Set G))) := fun s => ⟨1, Subtype.ext
    (by rw [pow_one, pow_two]; exact Subtype.ext (hS2 _ (mem_subgroupOf.mp s.2)))⟩
  have hN : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(centralizer (T : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have hPN : S.subgroupOf (centralizer (T : Set G)) ≤
      normalizer (pPrimeCore 2 ↥(centralizer (T : Set G)) : Set ↥(centralizer (T : Set G))) := by
    rw [normalizer_eq_top]
    exact le_top
  obtain ⟨n, hn, hcn⟩ := FooteLit.exists_mul_mem_centralizer hP hN hPN (y := c₀) (fun u hu => by
    have hc : solπ T u * solπ T c₀ = solπ T c₀ * solπ T u :=
      (mem_centralizer_iff.mp hh) (solπ T u) (mem_map_of_mem _ hu)
    rw [← QuotientGroup.eq_one_iff]
    change solπ T (c₀⁻¹ * (u * c₀ * u⁻¹)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hc]
    group)
  refine ⟨c₀ * n, mem_centralizer_iff.mpr fun s hs => ?_, ?_⟩
  · have := (mem_centralizer_iff.mp hcn) ⟨s, hST hs⟩ (mem_subgroupOf.mpr hs)
    exact congrArg Subtype.val this
  · have h1 : solπ T n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, h1, mul_one]

omit [Finite G] in
theorem mem_normalizer_solD_subgroupOf {c : ↥(centralizer (T : Set G))}
    (hc : (c : G) ∈ centralizer (S : Set G)) :
    c ∈ normalizer ((solD S T).subgroupOf (centralizer (T : Set G)) : Set _) := by
  have hN := le_normalizer_solD S T (mem_inf.mpr ⟨c.2, hc⟩)
  rw [mem_normalizer_iff] at hN ⊢
  intro x
  rw [mem_subgroupOf, mem_subgroupOf]
  simpa using hN x

theorem normalizer_imageD (hS2 : ∀ s ∈ S, s * s = 1) (hST : S ≤ centralizer (T : Set G)) :
    centralizer (imageS S T : Set (QC T)) ≤ normalizer (imageD S T : Set (QC T)) := by
  intro h hh
  obtain ⟨c, hcS, rfl⟩ := exists_lift_centralizer hS2 hST hh
  exact Subgroup.le_normalizer_map _ (mem_map_of_mem _ (mem_normalizer_solD_subgroupOf hcS))

omit [Finite G] in
theorem imageD_commute {y a : QC T}
    (hy : y ∈ imageD S T) (ha : a ∈ imageS S T) : y * a = a * y := by
  obtain ⟨d, hd, rfl⟩ := hy
  obtain ⟨s, hs, rfl⟩ := ha
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (solD_commute (mem_subgroupOf.mp hd) (mem_subgroupOf.mp hs))

theorem commutator_pCore_imageD (hS2 : ∀ s ∈ S, s * s = 1) (hST : S ≤ centralizer (T : Set G)) :
    ⁅pCore 2 (↥(centralizer (T : Set G)) ⧸ pPrimeCore 2 ↥(centralizer (T : Set G))),
      imageD S T⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := ↥(centralizer (T : Set G)) ⧸ pPrimeCore 2 ↥(centralizer (T : Set G))
  have hBn : (pCore 2 Q).Normal := pCore_normal
  refine GorensteinWalter.ThompsonPQ.thompson_p_times_q (p := 2) (imageS S T) (imageD S T)
    (pCore 2 Q) ?_ (pCore_isPGroup (p := 2) (G := Q)) (Nat.coprime_two_left.mpr odd_card_imageD)
    ?_ ?_ ?_ ?_
  · exact fun a => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact imageS_mul_self hS2 _ a.2)⟩
  · rw [normalizer_eq_top]; exact le_top
  · rw [normalizer_eq_top]; exact le_top
  · rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact mem_centralizer_iff.mpr fun y hy => imageD_commute hy ha
  · intro b hb
    obtain ⟨hbB, hbS⟩ := mem_inf.mp hb
    obtain ⟨c, hcS, rfl⟩ := exists_lift_centralizer hS2 hST hbS
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have hcN := mem_normalizer_solD_subgroupOf hcS
    have hz : c⁻¹ * d⁻¹ * c * d ∈ (solD S T).subgroupOf (centralizer (T : Set G)) := by
      have := (mem_normalizer_iff.mp (inv_mem hcN) d⁻¹).mp (inv_mem hd)
      rw [inv_inv] at this
      exact mul_mem this hd
    have hzB : solπ T (c⁻¹ * d⁻¹ * c * d) ∈ pCore 2 Q := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have e : (solπ T c)⁻¹ * (solπ T d)⁻¹ * solπ T c * solπ T d =
          (solπ T c)⁻¹ * ((solπ T d)⁻¹ * solπ T c * ((solπ T d)⁻¹)⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem hbB) (hBn.conj_mem _ hbB _)
    obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := Q) ⟨_, hzB⟩
    have h1 : solπ T (c⁻¹ * d⁻¹ * c * d) = 1 :=
      eq_one_of_mem_odd_of_pow odd_card_imageD (mem_map_of_mem _ hz)
        (n := n) (congrArg Subtype.val hn)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc solπ T d * solπ T c = solπ T d * solπ T c *
          ((solπ T c)⁻¹ * (solπ T d)⁻¹ * solπ T c * solπ T d) := by rw [h1, mul_one]
      _ = solπ T c * solπ T d := by group

theorem imageD_commute_center_layer (hS2 : ∀ s ∈ S, s * s = 1)
    (hST : S ≤ centralizer (T : Set G)) :
    ∀ y ∈ imageD S T, ∀ z ∈ (center (layer (QC T))).map (layer (QC T)).subtype, y * z = z * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (QC T) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hWn : ((center (layer (QC T))).map (layer (QC T)).subtype).Normal := center_layer_normal
  have hWab : ∀ a ∈ (center (layer (QC T))).map (layer (QC T)).subtype,
      ∀ b ∈ (center (layer (QC T))).map (layer (QC T)).subtype, a * b = b * a := by
    intro a ha b hb
    exact ((LocalAnalysis.ComponentInitial.mem_map_center_iff.mp ha).2 b
      (LocalAnalysis.ComponentInitial.mem_map_center_iff.mp hb).1).symm
  have hW2 := isPGroup_two_of_normal_comm hO hWab
  have hWB : (center (layer (QC T))).map (layer (QC T)).subtype ≤ pCore 2 (QC T) :=
    le_sSup ⟨hWn, hW2⟩
  intro y hy z hz
  exact mem_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (commutator_pCore_imageD hS2 hST) (hWB hz)) y hy

theorem imageD_le_normalizer (hS2 : ∀ s ∈ S, s * s = 1) (hST : S ≤ centralizer (T : Set G))
    {K : Subgroup (QC T)} (hK : IsComponent K) : imageD S T ≤ normalizer (K : Set (QC T)) :=
  normalizes_components_of_odd (imageS_mul_self hS2) odd_card_imageD
    (fun _ hy _ ha => imageD_commute hy ha) (normalizer_imageD hS2 hST)
    (imageD_commute_center_layer hS2 hST) hK

omit [Finite G] in
theorem isComponent_image {L : Subgroup G}
    (hL : IsPComponent 2 (L.subgroupOf (centralizer (T : Set G)))) :
    IsComponent ((L.subgroupOf (centralizer (T : Set G))).map (solπ T)) := by
  obtain ⟨K, hK, -, hmap, -⟩ := hL
  rw [show (L.subgroupOf (centralizer (T : Set G))).map (solπ T) = K from hmap]
  exact hK

theorem mem_normalizer_of_image {L : Subgroup G} (hLC : L ≤ centralizer (T : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer (T : Set G))))
    {g : ↥(centralizer (T : Set G))}
    (hg : solπ T g ∈ normalizer
      (((L.subgroupOf (centralizer (T : Set G))).map (solπ T) : Subgroup (QC T)) : Set (QC T))) :
    (g : G) ∈ normalizer (L : Set G) := by
  have hJC : conjugate L (g : G)⁻¹ ≤ centralizer (T : Set G) := fun x hx => by
    rw [UnbalancedLayer.mem_conjugate_iff, inv_inv] at hx
    have h := mul_mem (mul_mem g.2 (hLC hx)) (inv_mem g.2)
    rwa [show (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x by group] at h
  have hJ : IsPComponent 2 ((conjugate L (g : G)⁻¹).subgroupOf (centralizer (T : Set G))) :=
    UnbalancedCorr.isPComponent_conjugate_subgroupOf (inv_mem g.2) hL
  have hle : conjugate L (g : G)⁻¹ ≤ oddIn (centralizer (T : Set G)) ⊔ L := fun x hx => by
    have hx' := hx
    rw [UnbalancedLayer.mem_conjugate_iff, inv_inv] at hx'
    set l₁ : ↥(centralizer (T : Set G)) := ⟨(g : G)⁻¹ * x * g, hLC hx'⟩
    have h1 : solπ T g * solπ T l₁ * (solπ T g)⁻¹ ∈
        (L.subgroupOf (centralizer (T : Set G))).map (solπ T) :=
      (mem_normalizer_iff.mp hg _).mp (mem_map_of_mem _ (mem_subgroupOf.mpr hx'))
    obtain ⟨l', hl', hl'e⟩ := h1
    have h2 : l'⁻¹ * (g * l₁ * g⁻¹) ∈ pPrimeCore 2 ↥(centralizer (T : Set G)) := by
      rw [← QuotientGroup.eq_one_iff]
      change solπ T (l'⁻¹ * (g * l₁ * g⁻¹)) = 1
      rw [map_mul, map_inv, hl'e, map_mul, map_mul, map_inv, inv_mul_cancel]
    have e : x = (l' : G) * ((l'⁻¹ * (g * l₁ * g⁻¹) : ↥(centralizer (T : Set G))) : G) := by
      simp only [l₁, coe_mul, coe_inv]
      group
    rw [e]
    exact mul_mem (mem_sup_right (mem_subgroupOf.mp hl')) (mem_sup_left ⟨_, h2, rfl⟩)
  have heq := GrS4.eq_of_le_oddIn_sup hJC hLC hJ hL hle
  have h := UnbalancedLayer.mem_normalizer_of_conjugate_eq heq
  simpa using inv_mem h

end CFSG.ComponentClassification.GrSLit.Sol25
