module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Prop41
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_iSup_of_center_eq_bot {Y : Type} [Group Y] [Finite Y]
    (s : Finset (Subgroup Y)) (hs : ∀ K ∈ s, IsComponent K ∧ center ↥K = ⊥) {z : Y}
    (hz : z ∈ ⨆ K ∈ s, K) (hzc : ∀ y ∈ ⨆ K ∈ s, K, z * y = y * z) : z = 1 := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, mem_bot] at hz
    exact hz
  | insert K₀ s hK₀ ih =>
    have hs' : ∀ K ∈ s, IsComponent K ∧ center ↥K = ⊥ := fun K hK =>
      hs K (Finset.mem_insert_of_mem hK)
    obtain ⟨hK₀c, hK₀z⟩ := hs K₀ (Finset.mem_insert_self K₀ s)
    rw [Finset.iSup_insert] at hz hzc
    set N := ⨆ K ∈ s, K with hN
    have hNK₀ : N ≤ centralizer (K₀ : Set Y) := by
      refine iSup₂_le fun K hK => ?_
      rcases LocalCores.distinct_components_commute hK₀c (hs' K hK).1 with h | h
      · exact absurd (h ▸ hK) hK₀
      · exact Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
    have hK₀N : K₀ ≤ normalizer (N : Set Y) := fun k hk => mem_normalizer_of_commute
      fun n hn => mem_centralizer_iff.mp (hNK₀ hn) k hk
    have hz' : z ∈ ((K₀ ⊔ N : Subgroup Y) : Set Y) := hz
    rw [coe_mul_of_left_le_normalizer_right K₀ N hK₀N] at hz'
    obtain ⟨k, hk, n, hn, hkn⟩ := hz'
    have hkn' : k * n = z := hkn
    have hkc : (⟨k, hk⟩ : ↥K₀) ∈ center ↥K₀ := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      have h1 := hzc y (mem_sup_left y.2)
      rw [← hkn'] at h1
      have h2 : (y : Y) * n = n * y := mem_centralizer_iff.mp (hNK₀ hn) y y.2
      show (y : Y) * k = k * y
      calc (y : Y) * k = y * (k * n) * n⁻¹ := by group
        _ = k * n * y * n⁻¹ := by rw [h1]
        _ = k * (n * y) * n⁻¹ := by group
        _ = k * (y * n) * n⁻¹ := by rw [h2]
        _ = k * y := by group
    rw [hK₀z, mem_bot] at hkc
    have hk1 : k = 1 := congrArg Subtype.val hkc
    rw [hk1, one_mul] at hkn'
    subst hkn'
    exact ih hs' hn fun y hy => hzc y (mem_sup_right hy)

theorem isComponent_map_of_isL2Type {C K : Subgroup G} (hKC : K ≤ C)
    (hKp : IsPComponent 2 (K.subgroupOf C)) {q : ℕ} (hK : IsL2Type q (K ⧸ pPrimeCore 2 K)) :
    IsComponent ((K.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C))) ∧
      center ↥((K.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set K' := K.subgroupOf C with hK'
  set M := K'.map π with hM
  have hMc : IsComponent M := by
    obtain ⟨M', hM', -, hmap, -⟩ := hKp
    rw [hM, hmap]
    exact hM'
  refine ⟨hMc, ?_⟩
  let e : ↥K' ≃* ↥K := subgroupOfEquivOfLe hKC
  have hsK : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) := isSimpleGroup_of_lieModel_psl_two hK
  let eO : ↥K' ⧸ pPrimeCore 2 ↥K' ≃* ↥K ⧸ pPrimeCore 2 ↥K :=
    QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
  have hsK' : IsSimpleGroup (↥K' ⧸ pPrimeCore 2 ↥K') := eO.isSimpleGroup
  have hker : pPrimeCore 2 ↥K' ≤ (π.subgroupMap K').ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have h1 : ((k : ↥C) : G) ∈ (pPrimeCore 2 ↥K).map K.subtype := by
      have h2 : e k ∈ pPrimeCore 2 ↥K := by
        rw [← pPrimeCore_map_iso 2 e]
        exact mem_map_of_mem _ hk
      exact ⟨e k, h2, subgroupOfEquivOfLe_apply_coe hKC k⟩
    obtain ⟨c, hc, hcc⟩ := GSLit.map_pPrimeCore_le_of_isPComponent hKC hKp h1
    have hck : c = (k : ↥C) := Subtype.ext hcc
    apply Subtype.ext
    rw [MonoidHom.subgroupMap_apply_coe, OneMemClass.coe_one, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← hck]
    exact hc
  let f := QuotientGroup.lift (pPrimeCore 2 ↥K') (π.subgroupMap K') hker
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective _ _ (MonoidHom.subgroupMap_surjective π K') hker
  have hnt : Nontrivial ↥M := LocalCores.isQuasisimple_nontrivial hMc.1
  have hsM : IsSimpleGroup ↥M := IsSimpleGroup.isSimpleGroup_of_surjective f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥M) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hMc.1
    have : Subsingleton (↥M ⧸ center ↥M) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact hab (Subsingleton.elim _ _)

theorem two_dvd_card_of_isPComponent {C K : Subgroup G} (hKC : K ≤ C)
    (hKp : IsPComponent 2 (K.subgroupOf C)) : 2 ∣ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsQuasisimple (K ⧸ pPrimeCore 2 K) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ hKC).mp hKp).2.2
  have h1 := Burgoyne.even_card_of_isQuasisimple hq
  exact (even_iff_two_dvd.mp h1).trans (Subgroup.card_quotient_dvd_card _)

theorem inf_ne_bot_of_isPComponent {C K T : Subgroup G} (hTsyl : IsSylowTwoIn T C) (hKC : K ≤ C)
    (hKp : IsPComponent 2 (K.subgroupOf C)) : T ⊓ K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : (K.subgroupOf C).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ hKC).mp hKp).1
  have hTK := isSylowTwoIn_inf_of_isSubnormal hTsyl hKC hsub
  have h1 := card_eq_two_pow_twoExp hTK
  have h2 := le_twoExp_of_dvd (H := K) (k := 1)
    (by rw [pow_one]; exact two_dvd_card_of_isPComponent hKC hKp)
  intro h
  rw [h, card_bot] at h1
  have h3 : 2 ^ 1 ≤ 2 ^ twoExp K := Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem false_of_isL2Type_of_center {u : G} {T K : Subgroup G} (hu2 : orderOf u = 2)
    (hTsyl : IsSylowTwoIn T (centralizer ({u} : Set G)))
    (hZT : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → orderOf w = 2 → w = u)
    (hKu : K ≤ centralizer ({u} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))))
    (hK : IsL2Type 5 (K ⧸ pPrimeCore 2 K) ∨ IsL2Type 7 (K ⧸ pPrimeCore 2 K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  set C := centralizer ({u} : Set G) with hC
  have hTC : T ≤ C := hTsyl.1
  have hT2 : IsPGroup 2 T := IsSylowTwoIn.isPGroup hTsyl
  have hconj : ∀ g ∈ T, conjugate K g ≤ C ∧ IsPComponent 2 ((conjugate K g).subgroupOf C) ∧
      (IsL2Type 5 (conjugate K g ⧸ pPrimeCore 2 (conjugate K g)) ∨
        IsL2Type 7 (conjugate K g ⧸ pPrimeCore 2 (conjugate K g))) := by
    intro g hg
    obtain ⟨h1, h2⟩ := GSThmB.Six.isPComponent_conjugate hKu hKp g
    have hCg : conjugate C g = C := conjugate_eq_self (le_normalizer (hTC hg))
    rw [hCg] at h1 h2
    refine ⟨h1, h2, ?_⟩
    let e : ↥K ≃* ↥(conjugate K g) :=
      K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    let eO : K ⧸ pPrimeCore 2 K ≃* conjugate K g ⧸ pPrimeCore 2 (conjugate K g) :=
      QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
    rcases hK with h | h
    · exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv eO h)
    · exact Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eO h)
  set N := ⨆ g : ↥T, conjugate K (g : G) with hN
  have hKN : K ≤ N := by
    have h1 := le_iSup (fun g : ↥T => conjugate K (g : G)) ⟨1, one_mem T⟩
    rwa [conjugate_one] at h1
  have hconjN : ∀ h ∈ T, ∀ x ∈ N, h⁻¹ * x * h ∈ N := by
    intro h hh x hx
    refine iSup_induction (fun g : ↥T => conjugate K (g : G))
      (C := fun x => h⁻¹ * x * h ∈ N) hx ?_ ?_ ?_
    · intro g y hy
      have h1 : h⁻¹ * y * h ∈ conjugate K ((g : G) * h) := by
        rw [← conjugate_conjugate]
        exact conj_mem_conjugate hy h
      exact le_iSup (fun g : ↥T => conjugate K (g : G)) ⟨(g : G) * h, mul_mem g.2 hh⟩ h1
    · rw [mul_one, inv_mul_cancel]
      exact one_mem _
    · intro x y hx hy
      rw [show h⁻¹ * (x * y) * h = (h⁻¹ * x * h) * (h⁻¹ * y * h) by group]
      exact mul_mem hx hy
  have hTK := inf_ne_bot_of_isPComponent hTsyl hKu hKp
  have hTN : T ⊓ N ≠ ⊥ := fun h => hTK (eq_bot_iff.mpr fun x hx => by
    have h1 : x ∈ T ⊓ N := mem_inf.mpr ⟨(mem_inf.mp hx).1, hKN (mem_inf.mp hx).2⟩
    rw [h] at h1
    exact h1)
  have hnorm : T ≤ normalizer ((T ⊓ N : Subgroup G) : Set G) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      refine mem_inf.mpr ⟨mul_mem (mul_mem hh (mem_inf.mp hx).1) (inv_mem hh), ?_⟩
      have h1 := hconjN h⁻¹ (inv_mem hh) x (mem_inf.mp hx).2
      rwa [inv_inv] at h1
    · intro hx
      have hx' : x = h⁻¹ * (h * x * h⁻¹) * h := by group
      rw [hx']
      refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hh) (mem_inf.mp hx).1) hh, ?_⟩
      exact hconjN h hh _ (mem_inf.mp hx).2
  obtain ⟨w, hwTN, hw2, hwc⟩ := GSLit.exists_involution_mem_center hT2 inf_le_left hnorm hTN
  have hwu : w = u := hZT w (mem_inf.mp hwTN).1 hwc hw2
  have huN : u ∈ N := hwu ▸ (mem_inf.mp hwTN).2
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  let Kb : ↥T → Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := fun g =>
    ((conjugate K (g : G)).subgroupOf C).map π
  have : Fintype ↥T := Fintype.ofFinite _
  let s : Finset (Subgroup (↥C ⧸ pPrimeCore 2 ↥C)) := Finset.univ.image Kb
  have hs : ∀ M ∈ s, IsComponent M ∧ center ↥M = ⊥ := by
    intro M hM
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨h1, h2, h3⟩ := hconj g g.2
    rcases h3 with h3 | h3
    · exact isComponent_map_of_isL2Type h1 h2 h3
    · exact isComponent_map_of_isL2Type h1 h2 h3
  have huC : u ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hubN : π ⟨u, huC⟩ ∈ ⨆ M ∈ s, M := by
    have hle : N ≤ ((⨆ M ∈ s, M).comap π).map C.subtype := by
      refine iSup_le fun g x hx => ?_
      have hxC : x ∈ C := (hconj g g.2).1 hx
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap]
      have h1 : π ⟨x, hxC⟩ ∈ Kb g := mem_map_of_mem π (mem_subgroupOf.mpr hx)
      exact le_iSup₂ (f := fun (M : Subgroup (↥C ⧸ pPrimeCore 2 ↥C)) (_ : M ∈ s) => M) (Kb g)
        (Finset.mem_image_of_mem Kb (Finset.mem_univ g)) h1
    obtain ⟨c, hc, hcu⟩ := hle huN
    have hcu' : c = ⟨u, huC⟩ := Subtype.ext hcu
    rw [← hcu']
    exact hc
  have hubc : ∀ y ∈ ⨆ M ∈ s, M, π ⟨u, huC⟩ * y = y * π ⟨u, huC⟩ := by
    intro y _
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥C) y
    rw [hπ, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp y'.2).symm
  have hub1 := eq_one_of_mem_iSup_of_center_eq_bot s hs hubN hubc
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hub1
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥C)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hdvd := orderOf_dvd_natCard (⟨⟨u, huC⟩, hub1⟩ : pPrimeCore 2 ↥C)
  have hou : orderOf (⟨u, huC⟩ : ↥C) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hu2
  rw [Subgroup.orderOf_mk, hou] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem mem_zStarIn_of_le_normalizer {u : G} {T K : Subgroup G}
    (hTsyl : IsSylowTwoIn T (centralizer ({u} : Set G)))
    (hZT : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → orderOf w = 2 → w = u)
    (hKu : K ≤ centralizer ({u} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))))
    (hTK : T ≤ normalizer (K : Set G)) : u ∈ zStarIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := IsSylowTwoIn.isPGroup hTsyl
  have hne := inf_ne_bot_of_isPComponent hTsyl hKu hKp
  have hnorm : T ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp (le_normalizer hh) x
    have h2 := mem_normalizer_iff.mp (hTK hh) x
    simp only [mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  obtain ⟨w, hwTK, hw2, hwc⟩ := GSLit.exists_involution_mem_center hT2 inf_le_left hnorm hne
  have hwu : w = u := hZT w (mem_inf.mp hwTK).1 hwc hw2
  have huK : u ∈ K := hwu ▸ (mem_inf.mp hwTK).2
  refine ⟨⟨u, huK⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Sol78.fusionZStar_eq_comap, mem_comap, mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) y
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (hKu y'.2)

theorem mem_zStarIn_of_unbalancing_center
    (hMax : MaximalTwoComponentInput) (hbase : L34BaseSetting G)
    {u x : G} {T K₁ : Subgroup G} (hTsyl : IsSylowTwoIn T ⊤) (huT : u ∈ T) (hxT : x ∈ T)
    (huc : ∀ s ∈ T, s * u = u * s)
    (hZT : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → orderOf w = 2 → w = u)
    (hT₁ : GSUnbalancingTriple u x K₁)
    (hmax₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁) → GSWeakMaximalComponent K₁) :
    u ∈ zStarIn K₁ ∧ IsL34Type (K₁ ⧸ Open.fusionZStar K₁) := by
  have hTu : IsSylowTwoIn T (centralizer ({u} : Set G)) :=
    isSylowTwoIn_of_le_of_le hTsyl (fun s hs => mem_centralizer_singleton_iff.mpr (huc s hs))
      le_top
  rcases hbase.2.2.2.2.2.2.2 u x K₁ hT₁ with h | h | h
  · exact (false_of_isL2Type_of_center hT₁.1 hTu hZT hT₁.2.2.2.1 hT₁.2.2.2.2.1 (Or.inl h)).elim
  · exact (false_of_isL2Type_of_center hT₁.1 hTu hZT hT₁.2.2.2.1 hT₁.2.2.2.2.1 (Or.inr h)).elim
  · have hset₁ := l34Sec4Setting_of_mem_center hMax hbase hT₁ h (hmax₁ h) hTsyl huT hxT huc
    exact ⟨mem_zStarIn_of_le_normalizer hTu hZT hT₁.2.2.2.1 hT₁.2.2.2.2.1 hset₁.2.2.2.2.1.1, h⟩

end CFSG.ComponentClassification.GrSLit.GrS5
