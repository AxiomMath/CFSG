module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem eq_of_sq_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (hC : IsCyclic C) {u v : G} (hu : u ∈ C) (hv : v ∈ C) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  classical
  have : Fintype C := Fintype.ofFinite C
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  by_contra huv
  set u' : C := ⟨u, hu⟩
  set v' : C := ⟨v, hv⟩
  have h1u : (1 : C) ≠ u' := fun he => hu1 (congrArg Subtype.val he).symm
  have h1v : (1 : C) ≠ v' := fun he => hv1 (congrArg Subtype.val he).symm
  have huv' : u' ≠ v' := fun he => huv (congrArg Subtype.val he)
  have h3 : ({1, u', v'} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hu2)
    · exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hv2)
  have hc3 : ({1, u', v'} : Finset C).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, u', v', h1u, h1v, huv', rfl⟩
  have := Finset.card_le_card h3
  omega

theorem commute_of_mem_isCyclic {G : Type*} [Group G] {B : Subgroup G} (hB : IsCyclic B)
    {u v : G} (hu : u ∈ B) (hv : v ∈ B) : u * v = v * u := by
  obtain ⟨g, hg⟩ := hB.exists_generator
  obtain ⟨m, hm⟩ := hg ⟨u, hu⟩
  obtain ⟨n, hn⟩ := hg ⟨v, hv⟩
  have hu' : u = (g : G) ^ m := by
    rw [← SubgroupClass.coe_zpow]; exact (congrArg Subtype.val hm).symm
  have hv' : v = (g : G) ^ n := by
    rw [← SubgroupClass.coe_zpow]; exact (congrArg Subtype.val hn).symm
  rw [hu', hv', ← zpow_add, ← zpow_add, add_comm]

theorem card_le_of_isPGroup_of_sylow {G : Type*} [Group G] [Finite G] {C B Y : Subgroup G}
    (hBC : B ≤ C) (hBsyl : ∃ R : Sylow 2 ↥C, (R : Subgroup ↥C) = B.subgroupOf C)
    (hYC : Y ≤ C) (hY : IsPGroup 2 Y) : Nat.card Y ≤ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hBsyl
  obtain ⟨Q, hQ⟩ := (hY.comap_subtype (K := C)).exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup ↥C) = Nat.card B := by
    rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity R, hR,
      ← Subgroup.card_map_of_injective C.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hBC]
  have hY' : Nat.card (Y.subgroupOf C) = Nat.card Y := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hYC]
  rw [← hY', ← hQcard]
  exact Subgroup.card_le_of_le hQ

theorem isPGroup_of_sylow {G : Type*} [Group G] {C B : Subgroup G} (hBC : B ≤ C)
    (hBsyl : ∃ R : Sylow 2 ↥C, (R : Subgroup ↥C) = B.subgroupOf C) : IsPGroup 2 B := by
  obtain ⟨R, hR⟩ := hBsyl
  have h1 : IsPGroup 2 (B.subgroupOf C) := hR ▸ R.isPGroup'
  exact h1.of_equiv (subgroupOfEquivOfLe hBC)

theorem isPGroup_zpowers_of_sq_eq_one {G : Type*} [Group G] {e : G} (he2 : e ^ 2 = 1) :
    IsPGroup 2 (zpowers e) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have hd : orderOf (⟨e ^ k, hg⟩ : zpowers e) ∣ 2 ^ 1 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    have h1 : (e ^ k) ^ 2 ^ 1 = 1 := by
      rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he2, one_zpow]
    simpa using h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨m, hm⟩

theorem eq_of_involution_of_isCyclic_sylow {G : Type*} [Group G] [Finite G] {C B : Subgroup G}
    (hBC : B ≤ C) (hBsyl : ∃ R : Sylow 2 ↥C, (R : Subgroup ↥C) = B.subgroupOf C)
    (hBc : IsCyclic B) {b w : G} (hbB : b ∈ B) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1)
    (hwC : w ∈ C) (hwb : w * b = b * w) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) : w = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := C ⊓ centralizer ({b} : Set G) with hX
  have hBX : B ≤ X := fun y hy => mem_inf.mpr ⟨hBC hy,
    mem_centralizer_singleton_iff.mpr (commute_of_mem_isCyclic hBc hy hbB)⟩
  have hwX : w ∈ X := mem_inf.mpr ⟨hwC, mem_centralizer_singleton_iff.mpr hwb⟩
  obtain ⟨P, hP⟩ := ((isPGroup_of_sylow hBC hBsyl).comap_subtype (K := X)).exists_le_sylow
  replace hP : B.subgroupOf X ≤ P := hP
  have hPB : (P : Subgroup ↥X) = B.subgroupOf X := by
    refine le_antisymm_iff.mpr ⟨?_, hP⟩
    have hcard := card_le_of_isPGroup_of_sylow hBC hBsyl
      ((map_subtype_le _).trans inf_le_left) (P.isPGroup'.map X.subtype)
    have hc1 : Nat.card ((P : Subgroup ↥X).map X.subtype) = Nat.card (P : Subgroup ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    have hc2 : Nat.card (B.subgroupOf X) = Nat.card B := by
      rw [← Subgroup.card_map_of_injective X.subtype_injective, subgroupOf_map_subtype,
        inf_of_le_left hBX]
    exact (Subgroup.eq_of_le_of_card_ge hP (by rw [hc2, ← hc1]; exact hcard)).symm.le
  have hw2' : IsPGroup 2 (zpowers (⟨w, hwX⟩ : ↥X)) :=
    isPGroup_zpowers_of_sq_eq_one (Subtype.ext (by simpa using hw2))
  obtain ⟨Q, hQ⟩ := hw2'.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥X P Q
  have hwQ : (⟨w, hwX⟩ : ↥X) ∈ (Q : Subgroup ↥X) := hQ (mem_zpowers _)
  rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hPB,
    mem_subgroupOf] at hwQ
  set y' : G := (y : G) with hy'
  have hconj : (((MulAut.conj y)⁻¹ • (⟨w, hwX⟩ : ↥X) : ↥X) : G) = y'⁻¹ * w * y' := by
    simp [MulAut.smul_def, hy']
  rw [hconj] at hwQ
  have hyb : y' * b = b * y' := mem_centralizer_singleton_iff.mp (mem_inf.mp y.2).2
  have h2 : (y'⁻¹ * w * y') ^ 2 = 1 := by
    rw [pow_two]
    calc y'⁻¹ * w * y' * (y'⁻¹ * w * y') = y'⁻¹ * (w * w) * y' := by group
      _ = 1 := by rw [← pow_two, hw2]; group
  have h1 : y'⁻¹ * w * y' ≠ 1 := fun h => hw1 (by
    calc w = y' * (y'⁻¹ * w * y') * y'⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hb := eq_of_sq_eq_one_of_isCyclic hBc hwQ hbB h2 hb2 h1 hb1
  calc w = y' * (y'⁻¹ * w * y') * y'⁻¹ := by group
    _ = y' * b * y'⁻¹ := by rw [hb]
    _ = b := by rw [hyb, mul_inv_cancel_right]

theorem centralizer_le_normalizer_of_isPComponent {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} {b u : G} (hKC : K ≤ centralizer ({b} : Set G))
    (hK1 : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set G))))
    (hinv : ∀ w ∈ centralizer ({b} : Set G), w ∈ coreActionKernel K → w ^ 2 = 1 → w ≠ 1 →
      w = b)
    (huK : u ∈ K) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (hub : u ≠ b) :
    centralizer ({b} : Set G) ≤ normalizer (K : Set G) := by
  set C := centralizer ({b} : Set G) with hC
  intro y hy
  by_contra hyN
  set K' := conjugate K y with hK'
  have hK'C : K' ≤ C := fun v hv => by
    rw [hK', mem_conjugate_iff] at hv
    have h1 := mul_mem (mul_mem (inv_mem hy) (hKC hv)) hy
    rwa [show y⁻¹ * (y * v * y⁻¹) * y = v by group] at h1
  have hne : K.subgroupOf C ≠ K'.subgroupOf C := by
    intro he
    apply hyN
    apply mem_normalizer_of_conjugate_eq
    have h1 : K ⊓ C = K' ⊓ C := (subgroupOf_inj).mp he
    rw [inf_of_le_left hKC, inf_of_le_left hK'C] at h1
    exact h1.symm
  have hK1' : IsPComponent 2 (K'.subgroupOf C) :=
    (conjugate_subgroupOf_eq K C ⟨y, hy⟩) ▸ isPComponent_conjugate hK1 (⟨y, hy⟩ : ↥C)
  obtain ⟨hN', -, hc, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hK1
      hK1').2 hne
  set v := y⁻¹ * u * y with hv
  have hvK' : v ∈ K' := by
    rw [hK', mem_conjugate_iff, hv, show y * (y⁻¹ * u * y) * y⁻¹ = u by group]
    exact huK
  have hvC : v ∈ C := hK'C hvK'
  have hvN : (⟨v, hvC⟩ : ↥C) ∈ normalizer ((K.subgroupOf C : Subgroup ↥C) : Set ↥C) :=
    hN' (mem_subgroupOf.mpr hvK')
  have hvK : v ∈ coreActionKernel K := by
    refine mem_coreActionKernel.mpr ⟨mem_normalizer_iff.mpr fun g => ?_, fun j hj => ?_⟩
    · constructor
      · intro hg
        have h1 := (mem_normalizer_iff.mp hvN ⟨g, hKC hg⟩).mp (mem_subgroupOf.mpr hg)
        rw [mem_subgroupOf] at h1
        simpa using h1
      · intro hg
        have hgC : g ∈ C := by
          have h1 := mul_mem (mul_mem (inv_mem hvC) (hKC hg)) hvC
          rwa [show v⁻¹ * (v * g * v⁻¹) * v = g by group] at h1
        have h1 := (mem_normalizer_iff.mp hvN ⟨g, hgC⟩).mpr (by
          rw [mem_subgroupOf]; simpa using hg)
        exact mem_subgroupOf.mp h1
    · have hmem : ⁅(⟨j⁻¹, inv_mem (hKC hj)⟩ : ↥C), (⟨v⁻¹, inv_mem hvC⟩ : ↥C)⁆ ∈
          (pPrimeCore 2 ↥(K.subgroupOf C)).map (K.subgroupOf C).subtype :=
        (hc (commutator_mem_commutator (mem_subgroupOf.mpr (inv_mem hj))
          (mem_subgroupOf.mpr (inv_mem hvK')))).1
      have h2 := mem_map_of_mem C.subtype hmem
      rw [pPrimeCore_map_subgroupOf 2 K C hKC] at h2
      convert h2 using 1
      simp [commutatorElement_def]
  have hv2 : v ^ 2 = 1 := by
    rw [hv, pow_two]
    calc y⁻¹ * u * y * (y⁻¹ * u * y) = y⁻¹ * (u * u) * y := by group
      _ = 1 := by rw [← pow_two, hu2]; group
  have hv1 : v ≠ 1 := fun h => hu1 (by
    calc u = y * v * y⁻¹ := by rw [hv]; group
      _ = 1 := by rw [h]; group)
  have hvb := hinv v hvC hvK hv2 hv1
  apply hub
  have hyb : y * b = b * y := mem_centralizer_singleton_iff.mp hy
  calc u = y * v * y⁻¹ := by rw [hv]; group
    _ = y * b * y⁻¹ := by rw [hvb]
    _ = b := by rw [hyb, mul_inv_cancel_right]

theorem exists_conj_mem_normalizer_of_sylow {G : Type*} [Group G] [Finite G]
    {Y A B : Subgroup G} (hBY : B ≤ Y) (hBA : B ≤ A)
    (hBsyl : ∃ R : Sylow 2 ↥A, (R : Subgroup ↥A) = B.subgroupOf A)
    (hYA : ∀ y ∈ Y, ∀ g ∈ A, y * g * y⁻¹ ∈ A) {e : G} (heY : e ∈ Y) (he2 : e ^ 2 = 1) :
    ∃ y ∈ Y, y * e * y⁻¹ ∈ normalizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := ((isPGroup_of_sylow hBA hBsyl).comap_subtype (K := Y)).exists_le_sylow
  replace hP : B.subgroupOf Y ≤ P := hP
  set P' : Subgroup G := (P : Subgroup ↥Y).map Y.subtype with hP'
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map Y.subtype
  have hBP' : B ≤ P' := fun g hg => ⟨⟨g, hBY hg⟩, hP (mem_subgroupOf.mpr hg), rfl⟩
  have hPA : P' ⊓ A = B := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hBP' hBA) ?_).symm
    exact card_le_of_isPGroup_of_sylow hBA hBsyl inf_le_right (hP'2.to_le inf_le_left)
  have hP'N : P' ≤ normalizer (B : Set G) := by
    intro r hr
    have hrY : r ∈ Y := by
      obtain ⟨r', -, rfl⟩ := hr
      exact r'.2
    rw [mem_normalizer_iff]
    intro g
    rw [← hPA, mem_inf, mem_inf]
    constructor
    · rintro ⟨hg1, hg2⟩
      exact ⟨mul_mem (mul_mem hr hg1) (inv_mem hr), hYA r hrY g hg2⟩
    · rintro ⟨hg1, hg2⟩
      refine ⟨?_, ?_⟩
      · have h1 := mul_mem (mul_mem (inv_mem hr) hg1) hr
        rwa [show r⁻¹ * (r * g * r⁻¹) * r = g by group] at h1
      · have h1 := hYA r⁻¹ (inv_mem hrY) _ hg2
        rwa [inv_inv, show r⁻¹ * (r * g * r⁻¹) * r = g by group] at h1
  have he2' : IsPGroup 2 (zpowers (⟨e, heY⟩ : ↥Y)) :=
    isPGroup_zpowers_of_sq_eq_one (Subtype.ext (by simpa using he2))
  obtain ⟨Q, hQ⟩ := he2'.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥Y P Q
  have heQ : (⟨e, heY⟩ : ↥Y) ∈ (Q : Subgroup ↥Y) := hQ (mem_zpowers _)
  rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at heQ
  refine ⟨(y : G)⁻¹, inv_mem y.2, hP'N ⟨_, heQ, ?_⟩⟩
  simp [MulAut.smul_def]

end CFSG.ComponentClassification.GSThmB
