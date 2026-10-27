module

public import CFSG.CharacterTheory.Semidihedral.Principal.ControlledDefectCorrespondence
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralizerBrauerDefect
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralRotationInvolutionStructure
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.GorensteinWalter

namespace DihedralAssociates

variable {G : Type*} [Group G]

theorem dihedral_facts [Finite G] {n : ℕ} (hn : 2 ≤ n) (S : Subgroup G)
    (hScard : Nat.card S = 2 * 2 ^ (n - 1)) (r s : G) (hr : orderOf r = 2 ^ (n - 1))
    (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹) (hgen : Subgroup.closure ({r, s} : Set G) = S) :
    r ∈ S ∧ s ∈ S ∧ Subgroup.zpowers r ≤ S ∧
    (∀ y ∈ S, y * r ^ 2 ^ (n - 2) = r ^ 2 ^ (n - 2) * y) ∧ orderOf (r ^ 2 ^ (n - 2)) = 2 ∧
    (∀ a ∈ Subgroup.zpowers r, a * a = 1 → a = 1 ∨ a = r ^ 2 ^ (n - 2)) ∧
    (∀ x ∈ S, x ∉ Subgroup.zpowers r → x * x = 1) ∧
    (∀ x ∈ S, x ∉ Subgroup.zpowers r → ∃ j : ℕ, x = s * r ^ j) ∧
    (∀ x ∈ S, x ∉ Subgroup.zpowers r →
      Nat.card (Subgroup.closure ({r ^ 2 ^ (n - 2), x} : Set G)) = 4) := by
  have hrS : r ∈ S := hgen ▸ Subgroup.subset_closure (Set.mem_insert r {s})
  have hsS : s ∈ S := hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem r rfl)
  have hM2 : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let r' : S := ⟨r, hrS⟩
  let s' : S := ⟨s, hsS⟩
  have hr' : orderOf r' = 2 ^ (n - 1) := by rw [Subgroup.orderOf_mk]; exact hr
  have hs' : orderOf s' = 2 := by rw [Subgroup.orderOf_mk]; exact hs
  have hrel' : s' * r' * s' = r'⁻¹ := Subtype.ext hrel
  have hgen' : Subgroup.closure ({r', s'} : Set S) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective S)
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have hrM' : r' ^ 2 ^ (n - 1) = 1 := hr' ▸ pow_orderOf_eq_one r'
  have hss' : s' * s' = 1 := by rw [← pow_two, ← hs', pow_orderOf_eq_one]
  have hdih : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* S) := by
    obtain ⟨e, -, -⟩ := exists_dihedral_mulEquiv hM2 hScard hgen' hrM' hss' hrel'
    exact ⟨e⟩
  obtain ⟨-, hall⟩ := dihedral_rotation_involution_structure hn hdih
  obtain ⟨-, -, hnf, ⟨-, hzord, hzuniq⟩, hinvol, hzcenter, -, -, hcentx, -⟩ :=
    hall r' s' hr' hs' hrel' hgen'
  have hA : ∀ (y : G) (hy : y ∈ S), (⟨y, hy⟩ : S) ∈ Subgroup.zpowers r' ↔
      y ∈ Subgroup.zpowers r := by
    intro y hy
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [r'] using congrArg Subtype.val hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa [r'] using hk)⟩
  have hAS : Subgroup.zpowers r ≤ S := (Subgroup.zpowers_le).mpr hrS
  refine ⟨hrS, hsS, hAS, fun y hy => ?_, ?_, fun a ha haa => ?_, fun x hx hxA => ?_,
    fun x hx hxA => ?_, fun x hx hxA => ?_⟩
  · have hc := Subgroup.mem_center_iff.mp hzcenter ⟨y, hy⟩
    exact congrArg Subtype.val hc
  · have h := hzord
    rw [← Subgroup.orderOf_coe] at h
    exact h
  · by_cases ha1 : a = 1
    · exact Or.inl ha1
    · right
      have haS : a ∈ S := hAS ha
      have hord : orderOf (⟨a, haS⟩ : S) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [pow_two, haa]) ha1
      have heq := hzuniq ⟨a, haS⟩ ((hA a haS).mpr ha) hord
      exact congrArg Subtype.val heq
  · have hord := hinvol ⟨x, hx⟩ (fun h => hxA ((hA x hx).mp h))
    rw [Subgroup.orderOf_mk] at hord
    rw [← pow_two, ← hord, pow_orderOf_eq_one]
  · obtain ⟨c, hc, -⟩ := hnf ⟨x, hx⟩
    have h2 := c.1.isLt
    rcases (by omega : (c.1 : ℕ) = 0 ∨ (c.1 : ℕ) = 1) with h0 | h1
    · exfalso
      rw [h0, pow_zero, one_mul] at hc
      apply hxA
      rw [← hA x hx, hc]
      exact Subgroup.npow_mem_zpowers r' _
    · rw [h1, pow_one] at hc
      exact ⟨c.2, by simpa [r', s'] using congrArg Subtype.val hc⟩
  · obtain ⟨-, hK4⟩ := hcentx ⟨x, hx⟩ (fun h => hxA ((hA x hx).mp h))
    have hmap : (Subgroup.closure ({r' ^ 2 ^ (n - 2), ⟨x, hx⟩} : Set S)).map S.subtype =
        Subgroup.closure ({r ^ 2 ^ (n - 2), x} : Set G) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective S)]
    exact hK4.card_four

theorem reflection_inverts (S A : Subgroup G) (hAS : A ≤ S)
    (hinv : ∀ x ∈ S, x ∉ A → x * x = 1) {x : G} (hx : x ∈ S) (hxA : x ∉ A) {a : G}
    (ha : a ∈ A) : x * a * x⁻¹ = a⁻¹ := by
  have hxa : x * a ∉ A := fun h => hxA (by simpa using A.mul_mem h (A.inv_mem ha))
  have h1 : (x * a) * (x * a) = 1 := hinv _ (S.mul_mem hx (hAS ha)) hxa
  have hx2 : x * x = 1 := hinv x hx hxA
  rw [inv_eq_of_mul_eq_one_right hx2]
  calc x * a * x = x * a * x * (a * a⁻¹) := by rw [mul_inv_cancel, mul_one]
    _ = ((x * a) * (x * a)) * a⁻¹ := by group
    _ = a⁻¹ := by rw [h1, one_mul]

theorem mem_centralizer_zpowers_of_commute {t g : G} (h : g * t = t * g) :
    g ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : Commute t g := (show Commute g t from h).symm
  exact (hc.zpow_left k).eq

theorem dichotomy (S A : Subgroup G) {t : G} (hAS : A ≤ S) (htA : t ∈ A) (ht1 : t ≠ 1)
    (htt : t * t = 1) (htc : ∀ y ∈ S, y * t = t * y)
    (huniq : ∀ a ∈ A, a * a = 1 → a = 1 ∨ a = t) (hinv : ∀ x ∈ S, x ∉ A → x * x = 1)
    (hidx : ∀ x ∈ S, ∀ y ∈ S, x ∉ A → y ∉ A → x⁻¹ * y ∈ A) (D : Subgroup G) (htD : t ∈ D)
    (hDS : D ≤ S) :
    (∃ x ∈ D, x ∉ A ∧ D = Subgroup.closure ({t, x} : Set G)) ∨
      Subgroup.normalizer (D : Set G) ≤
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  by_cases hcase : ∃ x ∈ D, x ∉ A ∧ ∀ a ∈ D, a ∈ A → a = 1 ∨ a = t
  · left
    obtain ⟨x, hxD, hxA, hsmall⟩ := hcase
    refine ⟨x, hxD, hxA, le_antisymm ?_ ((Subgroup.closure_le D).mpr
      (Set.insert_subset_iff.mpr ⟨htD, Set.singleton_subset_iff.mpr hxD⟩))⟩
    intro y hy
    have htmem : t ∈ Subgroup.closure ({t, x} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert t {x})
    have hxmem : x ∈ Subgroup.closure ({t, x} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem t rfl)
    by_cases hyA : y ∈ A
    · rcases hsmall y hy hyA with rfl | rfl
      · exact Subgroup.one_mem _
      · exact htmem
    · have hxy := hidx x (hDS hxD) y (hDS hy) hxA hyA
      have hy' : y = x * (x⁻¹ * y) := by group
      rcases hsmall (x⁻¹ * y) (D.mul_mem (D.inv_mem hxD) hy) hxy with h | h
      · rw [hy', h, mul_one]
        exact hxmem
      · rw [hy', h]
        exact Subgroup.mul_mem _ hxmem htmem
  · right
    intro g hg
    apply mem_centralizer_zpowers_of_commute
    have hnorm := Subgroup.mem_normalizer_iff.mp hg
    have ht'D : g * t * g⁻¹ ∈ D := (hnorm t).mp htD
    have ht't' : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have ht'c : ∀ y ∈ D, y * (g * t * g⁻¹) = (g * t * g⁻¹) * y := by
      intro y hy
      have hy' : g⁻¹ * y * g ∈ D := by
        apply (hnorm (g⁻¹ * y * g)).mpr
        have hval : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [hval]
        exact hy
      have hcomm := htc _ (hDS hy')
      calc y * (g * t * g⁻¹) = g * ((g⁻¹ * y * g) * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * t * g⁻¹) * y := by group
    have ht'eq : g * t * g⁻¹ = t := by
      by_cases ht'A : g * t * g⁻¹ ∈ A
      · rcases huniq _ ht'A ht't' with h | h
        · exact absurd (conj_eq_one_iff.mp h) ht1
        · exact h
      · exfalso
        apply hcase
        refine ⟨g * t * g⁻¹, ht'D, ht'A, fun a haD haA => huniq a haA ?_⟩
        have hinvert := reflection_inverts S A hAS hinv (hDS ht'D) ht'A haA
        have hc := ht'c a haD
        have hfix : (g * t * g⁻¹) * a * (g * t * g⁻¹)⁻¹ = a := by
          rw [← hc]
          group
        rw [hfix] at hinvert
        calc a * a = a * a⁻¹ := by rw [← hinvert]
          _ = 1 := mul_inv_cancel a
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [ht'eq]

theorem subgroupsConjugate_subgroupOf {K X : Subgroup G} (hXK : X ≤ K) {c : G} (hc : c ∈ K) :
    subgroupsConjugate (X.subgroupOf K) ((X.map (MulAut.conj c).toMonoidHom).subgroupOf K) := by
  refine ⟨⟨c, hc⟩, ?_⟩
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨⟨z, hXK hz⟩, hz, Subtype.ext hzy⟩

theorem coefficientBlockDefect_of_conj [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {p : ℕ} [Fact p.Prime]
    {χ : basis.index} {D D' : Subgroup G} (hD : coefficientBlockDefect basis ideal p χ D)
    (hDD' : subgroupsConjugate D D') : coefficientBlockDefect basis ideal p χ D' := by
  obtain ⟨X, hX, hXval⟩ := hD.1
  refine ⟨⟨X, classDefect_of_subgroupsConjugate p hX hDD', hXval⟩, fun Y other hY hYval => ?_⟩
  exact subgroupSubconjugate_trans
    (subgroupsConjugate_subconjugate (subgroupsConjugate_symm hDD')) (hD.2 Y other hY hYval)

end DihedralAssociates

open DihedralAssociates

theorem dihedral_distinct_linear_block_associates_have_four_group_defect {G : Type*} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (hScard : Nat.card (S : Subgroup G) = 2 * 2 ^ (n - 1)) (r s : G)
    (hr : orderOf r = 2 ^ (n - 1)) (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹)
    (hgen : Subgroup.closure ({r, s} : Set G) = S) (t : G) (ht : t = r ^ 2 ^ (n - 2))
    (htp : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
    (ν : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) →* ℂˣ)
    (νLabel : localBasis.index)
    (hν : ∀ c, (localBasis.representation νLabel).character c = ν c) (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) htp
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis νLabel =
        centralCharacterResidueHom basis ideal B) :
    coefficientBlockDefect basis ideal 2 B S ∧
    coefficientBlockDefect localBasis ideal 2 νLabel ((S : Subgroup G).subgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) ∧
    (∀ b : localBasis.index,
      ¬ sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) νLabel b →
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) htp
          (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis b =
        centralCharacterResidueHom basis ideal B →
      ∃ j : ℤ, coefficientBlockDefect localBasis ideal 2 b
          ((Subgroup.closure ({t, s * r ^ j} : Set G)).subgroupOf
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) ∧
        Nat.card (Subgroup.closure ({t, s * r ^ j} : Set G)) = 4) ∧
    (3 ≤ n →
      (∀ b : localBasis.index, coefficientBlockDefect localBasis ideal 2 b
          ((S : Subgroup G).subgroupOf
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) →
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) htp
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) localBasis b =
          centralCharacterResidueHom basis ideal B →
        sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) νLabel b) ∧
      ∀ b : localBasis.index,
        ¬ sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) νLabel b →
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) htp
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) localBasis b =
          centralCharacterResidueHom basis ideal B →
        coefficientBlockDefect localBasis ideal 2 b
            ((Subgroup.closure ({t, s} : Set G)).subgroupOf
              (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) ∨
          coefficientBlockDefect localBasis ideal 2 b
            ((Subgroup.closure ({t, s * r} : Set G)).subgroupOf
              (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))) ∧
    (n = 2 → ∀ b : localBasis.index,
      ¬ sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) νLabel b →
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) htp
          (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis b =
        centralCharacterResidueHom basis ideal B →
      coefficientBlockDefect localBasis ideal 2 b ((S : Subgroup G).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))) := by
  obtain ⟨hrS, hsS, hAS, htc, htord, huniq, hinvol, hform, hcard4⟩ :=
    dihedral_facts hn (S : Subgroup G) hScard r s hr hs hrel hgen
  rw [← ht] at htc htord huniq hcard4
  let C := Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)
  have htS : t ∈ (S : Subgroup G) := ht ▸ (S : Subgroup G).pow_mem hrS _
  have htA : t ∈ Subgroup.zpowers r := ht ▸ Subgroup.npow_mem_zpowers r _
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at htord
    norm_num at htord
  have htt : t * t = 1 := by rw [← pow_two, ← htord, pow_orderOf_eq_one]
  have hss : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hSC : (S : Subgroup G) ≤ C := fun y hy => mem_centralizer_zpowers_of_commute (htc y hy)
  have hPS : Subgroup.zpowers t ≤ (S : Subgroup G) := (Subgroup.zpowers_le).mpr htS
  have hsA : s ∉ Subgroup.zpowers r := by
    intro hsr
    have hle : (S : Subgroup G) ≤ Subgroup.zpowers r := by
      rw [← hgen, Subgroup.closure_le]
      exact Set.insert_subset_iff.mpr ⟨Subgroup.mem_zpowers r, Set.singleton_subset_iff.mpr hsr⟩
    have hcard := Subgroup.card_le_of_le hle
    rw [hScard, Nat.card_zpowers, hr] at hcard
    have hpos : 0 < 2 ^ (n - 1) := by positivity
    omega
  have hidx : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x ∉ Subgroup.zpowers r →
      y ∉ Subgroup.zpowers r → x⁻¹ * y ∈ Subgroup.zpowers r := by
    intro x hx y hy hxA hyA
    obtain ⟨i, rfl⟩ := hform x hx hxA
    obtain ⟨j, rfl⟩ := hform y hy hyA
    have hprod : (s * r ^ i)⁻¹ * (s * r ^ j) = r ^ ((j : ℤ) - i) := by
      rw [zpow_sub, zpow_natCast, zpow_natCast]
      group
    rw [hprod]
    exact Subgroup.zpow_mem_zpowers r _
  have hdich := dichotomy (S : Subgroup G) (Subgroup.zpowers r) hAS htA ht1 htt htc huniq hinvol
    hidx
  have hconjrot : ∀ k j : ℤ, r ^ k * (s * r ^ j) * (r ^ k)⁻¹ = s * r ^ (j - 2 * k) := by
    intro k j
    have h := dihedral_reflection_conj_zpow hss hrel 0 (-k)
    simp only [pow_zero, mul_one] at h
    have h' : r ^ k * s = s * r ^ (-k) := by
      rw [zpow_neg, inv_inv] at h
      calc r ^ k * s = s * (r ^ k)⁻¹ * s⁻¹ * s := by rw [h]
        _ = s * r ^ (-k) := by rw [zpow_neg]; group
    calc r ^ k * (s * r ^ j) * (r ^ k)⁻¹ = (r ^ k * s) * r ^ j * (r ^ k)⁻¹ := by group
      _ = s * r ^ (-k) * r ^ j * (r ^ k)⁻¹ := by rw [h']
      _ = s * r ^ (j - 2 * k) := by group
  let SC : Sylow 2 C := S.subtype hSC
  have hνdefect : coefficientBlockDefect localBasis ideal 2 νLabel
      ((S : Subgroup G).subgroupOf C) :=
    (CFSG.Wreathed.linear_character_block_has_sylow_defect localBasis ideal 2 ν νLabel hν SC).1
  have hBdefect : coefficientBlockDefect basis ideal 2 B S := by
    obtain ⟨-, E, hE, hSE⟩ := centralizer_brauer_image_defect_contains_local_defect basis ideal 2
      (Subgroup.zpowers t) htp S S.isPGroup' hPS hSC localBasis νLabel hνdefect B hB
    have hEp := coefficientBlockDefect_isPGroup basis ideal hE
    have hES := CompatibleFamily.pSubgroup_subconjugate_sylow S hEp
    exact coefficientBlockDefect_of_conj basis ideal hE
      (subgroupsConjugate_of_subconjugate_card_ge hES (subgroupSubconjugate_card_le hSE))
  have hNS : 3 ≤ n → Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ C := by
    intro hn3
    rcases hdich S htS le_rfl with ⟨x, hxS, hxA, hSeq⟩ | hND
    · exfalso
      have h4 := hcard4 x hxS hxA
      rw [← hSeq, hScard] at h4
      have h8 : 4 ≤ 2 ^ (n - 1) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact hND
  have hmain : ∀ b : localBasis.index,
      ¬ sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) νLabel b →
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) htp C le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis b =
        centralCharacterResidueHom basis ideal B →
      ∃ x ∈ (S : Subgroup G), x ∉ Subgroup.zpowers r ∧ coefficientBlockDefect localBasis ideal 2 b
        ((Subgroup.closure ({t, x} : Set G)).subgroupOf C) := by
    intro b hb hbB
    obtain ⟨Db, hDb⟩ := coefficientBlockDefect_exists localBasis ideal 2 b
    obtain ⟨c, hc⟩ := CompatibleFamily.pSubgroup_subconjugate_sylow SC
      (coefficientBlockDefect_isPGroup localBasis ideal hDb)
    obtain ⟨D', hD'def⟩ : ∃ D', D' = Db.map (MulAut.conj c).toMonoidHom := ⟨_, rfl⟩
    have hD' : coefficientBlockDefect localBasis ideal 2 b D' :=
      coefficientBlockDefect_of_conj localBasis ideal hDb ⟨c, hD'def.symm⟩
    have hD'S : D' ≤ (S : Subgroup G).subgroupOf C := hD'def ▸ hc
    have hPnormal : ((Subgroup.zpowers t).subgroupOf C).Normal := by
      constructor
      intro a ha g
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have hga : (g : G) * a = a * g := (Subgroup.mem_centralizer_iff.mp g.property a ha).symm
      have hval : ((g * a * g⁻¹ : C) : G) = a := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hga]
        group
      rw [hval]
      exact ha
    have hPD' : (Subgroup.zpowers t).subgroupOf C ≤ D' :=
      normal_p_le_coefficientBlockDefect localBasis ideal 2 ((Subgroup.zpowers t).subgroupOf C)
        htp.comap_subtype hD'
    obtain ⟨D, hDdef⟩ : ∃ D, D = D'.map C.subtype := ⟨_, rfl⟩
    have hDsub : D.subgroupOf C = D' := by
      rw [hDdef]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective C) D'
    have hDS : D ≤ (S : Subgroup G) := by
      rw [hDdef]
      exact Subgroup.map_le_iff_le_comap.mpr hD'S
    have htC : t ∈ C := hSC htS
    have htD : t ∈ D := by
      rw [hDdef]
      exact Subgroup.mem_map_of_mem C.subtype (hPD' (show (⟨t, htC⟩ : C) ∈
        (Subgroup.zpowers t).subgroupOf C from Subgroup.mem_zpowers t))
    rcases hdich D htD hDS with ⟨x, hxD, hxA, hDeq⟩ | hND
    · exact ⟨x, hDS hxD, hxA, by rw [← hDeq, hDsub]; exact hD'⟩
    · have hDC : D ≤ C := hDS.trans hSC
      have hDp : IsPGroup 2 D := by
        rw [hDdef]
        exact (coefficientBlockDefect_isPGroup localBasis ideal hD').map C.subtype
      have hPD : Subgroup.zpowers t ≤ D := (Subgroup.zpowers_le).mpr htD
      obtain ⟨-, hmapdef, -, hinj⟩ := intermediate_normalizer_controlled_defect_correspondence
        basis ideal 2 (Subgroup.zpowers t) htp C le_rfl (Subgroup.centralizer_le_normalizer _) D
        hDp hPD hDC hND localBasis
      have hBD : coefficientBlockDefect basis ideal 2 B D := hmapdef b B (hDsub ▸ hD') hbB
      obtain ⟨g, hg⟩ := coefficientBlockDefect_conjugate basis ideal hBD hBdefect
      have hcardD : Nat.card (S : Subgroup G) = Nat.card D := by
        rw [← hg, conjugation_subgroup_card]
      have hDeqS : D = (S : Subgroup G) := Subgroup.eq_of_le_of_card_ge hDS hcardD.le
      subst hDeqS
      by_cases hn2 : n = 2
      · refine ⟨s, hsS, hsA, ?_⟩
        have hts : Subgroup.closure ({t, s} : Set G) = (S : Subgroup G) := by
          rw [← hgen, ht, hn2]
          norm_num
        rw [hts, hDsub]
        exact hD'
      · exfalso
        exact hb (hinj νLabel b hνdefect (hDsub ▸ hD') (hB.trans hbB.symm))
  refine ⟨hBdefect, hνdefect, fun b hb hbB => ?_, fun hn3 => ⟨fun b hbS hbB => ?_,
    fun b hb hbB => ?_⟩, fun hn2 b hb hbB => ?_⟩
  · obtain ⟨x, hxS, hxA, hxdef⟩ := hmain b hb hbB
    obtain ⟨j, rfl⟩ := hform x hxS hxA
    refine ⟨(j : ℤ), ?_, ?_⟩
    · rw [zpow_natCast]
      exact hxdef
    · rw [zpow_natCast]
      exact hcard4 _ hxS hxA
  · obtain ⟨-, -, -, hinj⟩ := intermediate_normalizer_controlled_defect_correspondence
      basis ideal 2 (Subgroup.zpowers t) htp C le_rfl (Subgroup.centralizer_le_normalizer _) S
      S.isPGroup' hPS hSC (hNS hn3) localBasis
    exact hinj νLabel b hνdefect hbS (hB.trans hbB.symm)
  · obtain ⟨x, hxS, hxA, hxdef⟩ := hmain b hb hbB
    obtain ⟨j, rfl⟩ := hform x hxS hxA
    set k : ℤ := (j : ℤ) / 2 with hk
    have hrk : r ^ k ∈ C := hSC ((S : Subgroup G).zpow_mem hrS k)
    have hle : Subgroup.closure ({t, s * r ^ j} : Set G) ≤ C := by
      rw [Subgroup.closure_le]
      exact Set.insert_subset_iff.mpr ⟨hSC htS, Set.singleton_subset_iff.mpr (hSC hxS)⟩
    have hmap : (Subgroup.closure ({t, s * r ^ j} : Set G)).map (MulAut.conj (r ^ k)).toMonoidHom =
        Subgroup.closure ({t, s * r ^ ((j : ℤ) % 2)} : Set G) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      have h1 : (MulAut.conj (r ^ k)).toMonoidHom t = t := by
        change r ^ k * t * (r ^ k)⁻¹ = t
        rw [htc _ ((S : Subgroup G).zpow_mem hrS k)]
        group
      have h2 : (MulAut.conj (r ^ k)).toMonoidHom (s * r ^ j) = s * r ^ ((j : ℤ) % 2) := by
        change r ^ k * (s * r ^ j) * (r ^ k)⁻¹ = _
        rw [← zpow_natCast r j, hconjrot, hk]
        congr 2
        omega
      rw [h1, h2]
    have hconjdef := coefficientBlockDefect_of_conj localBasis ideal hxdef
      (subgroupsConjugate_subgroupOf hle hrk)
    rw [hmap] at hconjdef
    rcases Int.emod_two_eq_zero_or_one (j : ℤ) with h0 | h1
    · left
      rw [h0, zpow_zero, mul_one] at hconjdef
      exact hconjdef
    · right
      rw [h1, zpow_one] at hconjdef
      exact hconjdef
  · obtain ⟨x, hxS, hxA, hxdef⟩ := hmain b hb hbB
    have hle : Subgroup.closure ({t, x} : Set G) ≤ (S : Subgroup G) := by
      rw [Subgroup.closure_le]
      exact Set.insert_subset_iff.mpr ⟨htS, Set.singleton_subset_iff.mpr hxS⟩
    have heq : Subgroup.closure ({t, x} : Set G) = (S : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [hcard4 x hxS hxA, hScard, hn2]
      norm_num
    rw [heq] at hxdef
    exact hxdef

end CFSG.Semidihedral.Principal
