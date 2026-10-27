module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Simple
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Action
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Maximal
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsA7
public import CFSG.Milestones.LR_dihedral_simple_recognition

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.Open CFSG.GorensteinWalter
open scoped Pointwise

theorem simple_dihedral_cases {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnonab : ∃ x y : L, x * y ≠ y * x) (hL : HasDihedralSylowTwo L) :
    Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (p f : ℕ), p.Prime ∧ Nat.card K = p ^ f ∧
        IsOddPrimePower (Nat.card K) ∧ 3 < Nat.card K ∧ Nonempty (L ≃* PSL2 K) := by
  obtain ⟨S, n, hn, hS⟩ := hL
  rcases CFSG.Milestones.lr_dihedral_simple_recognition L hnonab S n hn hS with
    ⟨p, f, hp, hp2, hf, hmodel⟩ | h7
  · right
    obtain ⟨⟨-, -, -, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hqodd : Odd (p ^ f) := hpodd.pow
    have hq3 : 3 < p ^ f := by
      have h1 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
      have h2 : 3 ≤ p ^ f := by
        have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
        have : 3 ≤ p := by
          have := hp.two_le
          omega
        omega
      omega
    refine ⟨K, inferInstance, inferInstance, p, f, hp, hK, ⟨p, f, hp, hpodd, hf, hK⟩,
      hK ▸ hq3, ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
        2 K).symm⟩⟩
  · exact Or.inl h7

theorem mem_zpowers_sup_iff {G : Type*} [Group G] {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha2 : a ^ 2 = 1) {x : G} :
    x ∈ Subgroup.zpowers a ⊔ L ↔ ∃ l ∈ L, x = l ∨ x = a * l := by
  have hle : Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr haN
  constructor
  · intro hx
    have hx' : x ∈ (Subgroup.zpowers a : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
      exact hx
    obtain ⟨y, hy, l, hl, rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have ha2' : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact ha2
    refine ⟨l, hl, ?_⟩
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [← Int.mul_ediv_add_emod k 2, hk, add_zero, zpow_mul, ha2', one_zpow, one_mul]
    · right
      rw [← Int.mul_ediv_add_emod k 2, hk, zpow_add, zpow_mul, ha2', one_zpow, one_mul,
        zpow_one]
  · rintro ⟨l, hl, rfl | rfl⟩
    · exact Subgroup.mem_sup_right hl
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
        (Subgroup.mem_sup_right hl)

theorem conclusions_of_mulEquiv_pgl2 {G : Type} [Group G] {A A₀ : Subgroup G} {a : G}
    (haA : a ∈ A) (hA₀ : ∀ x : G, x ∈ A₀ ↔ x ∈ A ∧ x * a = a * x)
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {g : PGL2 K}
    (hg : g ^ 2 = 1) (hgJ : g ∉ pslRange K) (Θ : A ≃* PGL2 K) (hΘ : Θ ⟨a, haA⟩ = g) :
    (∀ K' : Subgroup G, A₀ ≤ K' → K' ≤ A → K' = A₀ ∨ K' = A) ∧
      (∀ y ∈ A₀, (∀ m ∈ A₀, y * m = m * y) → y ∈ Subgroup.zpowers a) := by
  have hcorr : ∀ x : A, (x : G) ∈ A₀ ↔ Θ x ∈ Subgroup.centralizer ({g} : Set (PGL2 K)) := by
    intro x
    rw [hA₀, Subgroup.mem_centralizer_singleton_iff, ← hΘ, ← map_mul, ← map_mul]
    constructor
    · rintro ⟨-, h⟩
      congr 1
      exact Subtype.ext h
    · intro h
      exact ⟨x.2, congrArg Subtype.val (Θ.injective h)⟩
  refine ⟨fun K' hK₀ hKA => ?_, fun y hy hcent => ?_⟩
  · let H : Subgroup (PGL2 K) := (K'.subgroupOf A).map Θ.toMonoidHom
    have hCH : Subgroup.centralizer ({g} : Set (PGL2 K)) ≤ H := by
      intro h hh
      refine ⟨Θ.symm h, ?_, by simp⟩
      exact hK₀ ((hcorr _).mpr (by simpa using hh))
    rcases outer_involution_centralizer_maximal hKcard hK hcard hg hgJ H hCH with hH | hH
    · left
      apply le_antisymm _ hK₀
      intro x hx
      have hxH : Θ ⟨x, hKA hx⟩ ∈ H := ⟨⟨x, hKA hx⟩, hx, rfl⟩
      rw [hH] at hxH
      exact (hcorr ⟨x, hKA hx⟩).mpr hxH
    · right
      apply le_antisymm hKA
      intro x hx
      have hxH : Θ ⟨x, hx⟩ ∈ H := by rw [hH]; trivial
      obtain ⟨x', hx', hx'e⟩ := hxH
      have : x' = ⟨x, hx⟩ := Θ.injective hx'e
      rw [this] at hx'
      exact hx'
  · have hyA : y ∈ A := ((hA₀ y).mp hy).1
    have hyC := (hcorr ⟨y, hyA⟩).mp hy
    have hz := outer_involution_centralizer_center hK hcard hg hgJ _ hyC (by
      intro m hm
      have hxm := (hcorr (Θ.symm m)).mpr (by simpa using hm)
      have h1 := hcent _ hxm
      have h2 : (⟨y, hyA⟩ : A) * Θ.symm m = Θ.symm m * ⟨y, hyA⟩ := Subtype.ext h1
      have h3 := congrArg Θ h2
      simpa using h3)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h1 : Θ (⟨a, haA⟩ ^ k) = Θ ⟨y, hyA⟩ := by rw [map_zpow, hΘ, hk]
    have h2 := congrArg Subtype.val (Θ.injective h1)
    rw [Subgroup.coe_zpow] at h2
    exact ⟨k, h2⟩

theorem dihedral_outer_involution_holds : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (a : G),
    IsSimpleGroup L → HasDihedralSylowTwo L → a ∈ Subgroup.normalizer (L : Set G) → a ^ 2 = 1 →
    HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) →
    a ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
    (∀ K : Subgroup G, Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K →
      K ≤ Subgroup.zpowers a ⊔ L →
      K = Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ∨
        K = Subgroup.zpowers a ⊔ L) ∧
    (∀ y ∈ Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)),
      (∀ m ∈ Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)), y * m = m * y) →
      y ∈ Subgroup.zpowers a) ∧
    (∀ b ∈ Subgroup.normalizer (L : Set G), b ^ 2 = 1 →
      HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) →
      a * b ∈ L ⊔ Subgroup.centralizer (L : Set G)) := by
  intro G _ _ L a hLs hLd haN ha2 hcyc
  have hinner : ∀ n : G, n ^ 2 = 1 →
      HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({n} : Set G) : Subgroup G) →
      n ∉ L ⊔ Subgroup.centralizer (L : Set G) := by
    intro n hn2 hncyc hin
    obtain ⟨u, w, hu, hw, hu2, hw2, hu1, hw1, huw, hc⟩ := inner_commuting_pair hLd hn2 hin
    exact not_hasCyclicSylowTwo_of_commuting_involutions _ hu hw hu2 hw2 hu1 hw1 huw hc hncyc
  have hconj1 := hinner a ha2 hcyc
  refine ⟨hconj1, ?_⟩
  have hnonab := exists_ne_comm_of_simple_dihedral hLd
  set R := Subgroup.normalizer (L : Set G) with hRdef
  have hLR : L ≤ R := Subgroup.le_normalizer
  let N : Subgroup R := L.subgroupOf R
  have hNn : N.Normal := Subgroup.normal_in_normalizer
  have hpair : ∀ r : R,
      HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({(r : G)} : Set G) : Subgroup G) →
      ∀ u w : N, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 → u ≠ w → u * w = w * u →
        r * u = u * r → r * w = w * r → False := by
    intro r hrcyc u w hu hw hu1 hw1 huw hc hru hrw
    have hval : ∀ v : N, ((v : R) : G) ∈ L := fun v => v.2
    refine not_hasCyclicSylowTwo_of_commuting_involutions _ (u := ((u : R) : G))
      (w := ((w : R) : G)) (Subgroup.mem_inf.mpr ⟨hval u, ?_⟩)
      (Subgroup.mem_inf.mpr ⟨hval w, ?_⟩) ?_ ?_ ?_ ?_ ?_ ?_ hrcyc
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val hru).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val hrw).symm
    · exact congrArg (fun v : N => ((v : R) : G)) hu
    · exact congrArg (fun v : N => ((v : R) : G)) hw
    · exact fun h => hu1 (Subtype.ext (Subtype.ext h))
    · exact fun h => hw1 (Subtype.ext (Subtype.ext h))
    · exact fun h => huw (Subtype.ext (Subtype.ext h))
    · exact congrArg (fun v : N => ((v : R) : G)) hc
  rcases simple_dihedral_cases hnonab hLd with hA7 | ⟨K, _, _, p, f, hp, hKcard, hK, hcard, ⟨eL⟩⟩
  ·
    exfalso
    obtain ⟨eA⟩ := hA7
    let eN : N ≃* alternatingGroup (Fin 7) := (Subgroup.subgroupOfEquivOfLe hLR).trans eA
    obtain ⟨u, w, hu, hw, hu1, hw1, huw, hc, hru, hrw⟩ :=
      a7_involution_commuting_pair N eN ⟨a, haN⟩ (Subtype.ext ha2)
    exact hpair ⟨a, haN⟩ hcyc u w hu hw hu1 hw1 huw hc hru hrw
  have : Fact p.Prime := ⟨hp⟩
  let eN : N ≃* PSL2 K := (Subgroup.subgroupOfEquivOfLe hLR).trans eL
  have heN : ∀ n : N, eN n = eL ⟨((n : R) : G), n.2⟩ := fun n => rfl
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard
  set ψ := normalPSL2ToPGammaL2 N K hK hcard eN hsurj with hψdef
  have hJ2 := pslRange_index_eq_two hK
  have hdiag : ∀ r : R, (r : G) ^ 2 = 1 →
      HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({(r : G)} : Set G) : Subgroup G) →
      ∃ g : PGL2 K, ψ r = SemidirectProduct.inl g ∧ g ∉ pslRange K ∧ g ^ 2 = 1 := by
    intro r hr2 hrcyc
    obtain ⟨g, hg⟩ := psl2Action_involution_linear N hK hcard eN hsurj r (Subtype.ext hr2)
      (hpair r hrcyc)
    refine ⟨g, hg, ?_, ?_⟩
    · intro hgJ
      apply hinner r hr2 hrcyc
      have hmem : ψ r ∈ pGammaL2PSLRange K := by
        obtain ⟨y, hy⟩ := hgJ
        rw [hg, ← hy]
        exact ⟨y, rfl⟩
      obtain ⟨m, hm⟩ := psl2Action_mem_pslRange N hK hcard eN hsurj r hmem
      have hc : (r : G) * ((m : R) : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := congrArg Subtype.val (hm ⟨⟨y, hLR hy⟩, hy⟩)
        exact this.symm
      have : (r : G) = (r : G) * ((m : R) : G)⁻¹ * ((m : R) : G) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left m.2)
    · have h1 : (SemidirectProduct.inl (g ^ 2) : PGammaL2 K) = SemidirectProduct.inl 1 := by
        rw [map_pow, ← hg, ← map_pow, show r ^ 2 = 1 from Subtype.ext hr2, map_one, map_one]
      exact SemidirectProduct.inl_injective h1
  obtain ⟨g, hga, hgJ, hg2⟩ := hdiag ⟨a, haN⟩ ha2 hcyc
  have haA : a ∈ Subgroup.zpowers a ⊔ L := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hAR : Subgroup.zpowers a ⊔ L ≤ R := sup_le (Subgroup.zpowers_le.mpr haN) hLR
  let ψA : (Subgroup.zpowers a ⊔ L : Subgroup G) →* PGammaL2 K :=
    ψ.comp (Subgroup.inclusion hAR)
  have hψAl : ∀ (x : (Subgroup.zpowers a ⊔ L : Subgroup G)) (hx : (x : G) ∈ L),
      ψA x = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (eL ⟨x, hx⟩)) := by
    intro x hx
    exact psl2Action_apply N hK hcard eN hsurj ⟨Subgroup.inclusion hAR x, hx⟩
  have hψAa : ψA ⟨a, haA⟩ = SemidirectProduct.inl g := hga
  have hψAinj : Function.Injective ψA := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : ∀ y ∈ L, (x : G) * y = y * x := by
      intro y hy
      have h1 := (psl2Action_commute_iff N hK hcard eN hsurj (Subgroup.inclusion hAR x)
        ⟨⟨y, hLR hy⟩, hy⟩).mpr (by
          have : ψ (Subgroup.inclusion hAR x) = 1 := hx
          rw [this, one_mul, mul_one])
      exact congrArg Subtype.val h1
    obtain ⟨l, hl, hx' | hx'⟩ := (mem_zpowers_sup_iff haN ha2).mp x.2
    · apply Subtype.ext
      rw [hx']
      exact eq_one_of_mem_center_of_simple_dihedral hLd hl
        (fun y hy => by rw [← hx']; exact hxC y hy)
    · exfalso
      apply hconj1
      have : a = (x : G) * l⁻¹ := by rw [hx']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right
        (Subgroup.mem_centralizer_iff.mpr fun y hy => (hxC y hy).symm))
        (Subgroup.mem_sup_left (L.inv_mem hl))
  have hψArange : ψA.range = pGammaL2PGLRange K := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨l, hl, hx' | hx'⟩ := (mem_zpowers_sup_iff haN ha2).mp x.2
      · rw [hψAl x (hx' ▸ hl)]
        exact ⟨_, rfl⟩
      · have hxe : x = ⟨a, haA⟩ * ⟨l, Subgroup.mem_sup_right hl⟩ := Subtype.ext hx'
        rw [hxe, map_mul, hψAa, hψAl _ hl, ← map_mul]
        exact ⟨_, rfl⟩
    · rintro _ ⟨h, rfl⟩
      by_cases hhJ : h ∈ pslRange K
      · obtain ⟨y, rfl⟩ := hhJ
        refine ⟨⟨eL.symm y, Subgroup.mem_sup_right (eL.symm y).2⟩, ?_⟩
        rw [hψAl _ (eL.symm y).2]
        simp
      · have hhg : h * g ∈ pslRange K :=
          (Subgroup.mul_mem_iff_of_index_two hJ2).mpr (iff_of_false hhJ hgJ)
        obtain ⟨y, hy⟩ := hhg
        refine ⟨⟨eL.symm y, Subgroup.mem_sup_right (eL.symm y).2⟩ * ⟨a, haA⟩, ?_⟩
        rw [map_mul, hψAl _ (eL.symm y).2, hψAa, ← map_mul]
        congr 1
        have : eL ⟨((eL.symm y : L) : G), (eL.symm y).2⟩ = y := by simp
        rw [this, hy, mul_assoc, ← pow_two, hg2, mul_one]
  let Θ : (Subgroup.zpowers a ⊔ L : Subgroup G) ≃* PGL2 K :=
    ((MonoidHom.ofInjective hψAinj).trans (MulEquiv.subgroupCongr hψArange)).trans
      (pGammaL2PGLRangeEquiv K).symm
  have hΘinl : ∀ x, SemidirectProduct.inl (Θ x) = ψA x := by
    intro x
    rw [← pGammaL2PGLRangeEquiv_coe K (Θ x)]
    simp only [Θ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact MonoidHom.ofInjective_apply hψAinj
  have hΘa : Θ ⟨a, haA⟩ = g := by
    have h1 : (SemidirectProduct.inl (Θ ⟨a, haA⟩) : PGammaL2 K) = SemidirectProduct.inl g := by
      rw [hΘinl, hψAa]
    exact SemidirectProduct.inl_injective h1
  have hA₀ : ∀ x : G, x ∈ Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ↔
      x ∈ Subgroup.zpowers a ⊔ L ∧ x * a = a * x := by
    intro x
    constructor
    · intro hx
      have hle' : Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤
          Subgroup.zpowers a ⊔ L := sup_le_sup_left inf_le_left _
      refine ⟨hle' hx, ?_⟩
      have hle : Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤
          Subgroup.centralizer ({a} : Set G) :=
        sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
          inf_le_right
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    · rintro ⟨hx, hxa⟩
      obtain ⟨l, hl, rfl | rfl⟩ := (mem_zpowers_sup_iff haN ha2).mp hx
      · exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr
          ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr hxa⟩)
      · have hla : l * a = a * l := mul_left_cancel (by rwa [mul_assoc] at hxa)
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
          (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr
            ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr hla⟩))
  obtain ⟨hmax, hcen⟩ := conclusions_of_mulEquiv_pgl2 haA hA₀ hKcard hK hcard hg2 hgJ Θ hΘa
  refine ⟨hmax, hcen, ?_⟩
  ·
    intro b hbN hb2 hbcyc
    obtain ⟨g', hgb, hg'J, -⟩ := hdiag ⟨b, hbN⟩ hb2 hbcyc
    have hgg : g * g' ∈ pslRange K :=
      (Subgroup.mul_mem_iff_of_index_two hJ2).mpr (iff_of_false hgJ hg'J)
    obtain ⟨y, hy⟩ := hgg
    have hmem : ψ (⟨a, haN⟩ * ⟨b, hbN⟩) ∈ pGammaL2PSLRange K := by
      rw [map_mul, hga, hgb, ← map_mul, ← hy]
      exact ⟨y, rfl⟩
    obtain ⟨m, hm⟩ := psl2Action_mem_pslRange N hK hcard eN hsurj _ hmem
    have hc : a * b * ((m : R) : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := congrArg Subtype.val (hm ⟨⟨y, hLR hy⟩, hy⟩)
      exact this.symm
    have : a * b = a * b * ((m : R) : G)⁻¹ * ((m : R) : G) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left m.2)

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
