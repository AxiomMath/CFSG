module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Comp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW36
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Normal

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l34K_le_centralizer (L : Subgroup G) (u : G) :
    l34K L u ≤ centralizer ({u} : Set G) :=
  iSup_le fun _ => iSup_le fun h => iSup_le fun _ => iSup_le fun _ => h

theorem le_l34K {L K : Subgroup G} {u : G} (hKu : K ≤ centralizer ({u} : Set G))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))))
    (hKY : ¬ ⁅K, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K) : K ≤ l34K L u :=
  le_iSup_of_le K (le_iSup_of_le hKu (le_iSup_of_le hK (le_iSup_of_le hKY le_rfl)))

theorem commutator_le_of_ne {C K K' : Subgroup G} (hKC : K ≤ C) (hK'C : K' ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) (hK' : IsPComponent 2 (K'.subgroupOf C))
    (hne : K ≠ K') : ⁅K, K'⁆ ≤ oddIn C ∧ K' ≤ normalizer (K : Set G) := by
  have hne' : K.subgroupOf C ≠ K'.subgroupOf C := by
    intro h
    apply hne
    have h1 := congrArg (Subgroup.map C.subtype) h
    rwa [map_subgroupOf_eq_of_le hKC, map_subgroupOf_eq_of_le hK'C] at h1
  obtain ⟨-, h2⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
    _ _ hK hK'
  obtain ⟨hN, -, hc, -⟩ := h2 hne'
  refine ⟨?_, ?_⟩
  · have hc' : ⁅K.subgroupOf C, K'.subgroupOf C⁆ ≤ pPrimeCore 2 ↥C := by
      refine hc.trans (inf_le_left.trans ?_)
      exact (UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal
        (hK.choose_spec.2.1)).le.trans inf_le_right
    have h3 := map_mono (f := C.subtype) hc'
    rwa [map_commutator, map_subgroupOf_eq_of_le hKC, map_subgroupOf_eq_of_le hK'C] at h3
  · intro k' hk'
    have h4 := hN (show (⟨k', hK'C hk'⟩ : C) ∈ K'.subgroupOf C from hk')
    rw [mem_normalizer_iff] at h4 ⊢
    intro y
    constructor
    · intro hy
      have h5 := mem_subgroupOf.mp ((h4 ⟨y, hKC hy⟩).mp (mem_subgroupOf.mpr hy))
      simpa using h5
    · intro hy
      have hyC : y ∈ C := by
        have h6 : k' * y * k'⁻¹ ∈ C := hKC hy
        have := mul_mem (mul_mem (inv_mem (hK'C hk')) h6) (hK'C hk')
        simpa [mul_assoc] using this
      exact mem_subgroupOf.mp ((h4 ⟨y, hyC⟩).mpr (mem_subgroupOf.mpr (by simpa using hy)))

theorem layerIn_le_normalizer {C K : Subgroup G} (hKC : K ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) : layerIn C ≤ normalizer (K : Set G) := by
  rintro _ ⟨p, hp, rfl⟩
  have h1 := pLayer_le_normalizer_of_isPComponent hK hp
  rw [mem_normalizer_iff] at h1 ⊢
  intro y
  constructor
  · intro hy
    have h5 := mem_subgroupOf.mp ((h1 ⟨y, hKC hy⟩).mp (mem_subgroupOf.mpr hy))
    simpa using h5
  · intro hy
    have hyC : y ∈ C := by
      have h6 : (p : G) * y * (p : G)⁻¹ ∈ C := hKC hy
      have := mul_mem (mul_mem (inv_mem p.2) h6) p.2
      simpa [mul_assoc] using this
    exact mem_subgroupOf.mp ((h1 ⟨y, hyC⟩).mpr (mem_subgroupOf.mpr (by simpa using hy)))

omit [Finite G] in
theorem le_layerIn {C K : Subgroup G} (hKC : K ≤ C) (hK : IsPComponent 2 (K.subgroupOf C)) :
    K ≤ layerIn C :=
  GSLit.le_map_pLayer_of_isPComponent hKC hK

theorem isSubnormal_l34K (L : Subgroup G) (u : G) :
    ((l34K L u).subgroupOf (centralizer ({u} : Set G))).IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({u} : Set G) with hC
  set K := l34K L u with hK
  have hKC : K ≤ C := l34K_le_centralizer L u
  have hKP : K ≤ layerIn C :=
    iSup_le fun K₁ => iSup_le fun hK₁ => iSup_le fun hK₁p => iSup_le fun _ => le_layerIn hK₁ hK₁p
  have hPN : layerIn C ≤ normalizer (K : Set G) := by
    intro p hp
    have hpC : p ∈ C := map_subtype_le _ hp
    have hconj : ∀ g ∈ layerIn C, conjugate K g ≤ K := by
      intro g hg
      rw [hK, l34K]
      simp only [conjugate]
      rw [Subgroup.map_iSup]
      refine iSup_le fun K₁ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hK₁ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hK₁p => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hK₁Y => ?_
      have hN := layerIn_le_normalizer hK₁ hK₁p (inv_mem hg)
      have heq : K₁.map (MulAut.conj g⁻¹).toMonoidHom = K₁ := by
        ext y
        simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact (mem_normalizer_iff.mp hN k).mp hk
        · intro hy
          refine ⟨g * y * g⁻¹, ?_, by group⟩
          have := (mem_normalizer_iff.mp hN (g * y * g⁻¹)).mpr (by simpa [mul_assoc] using hy)
          exact this
      rw [heq]
      exact le_l34K hK₁ hK₁p hK₁Y
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := hconj p⁻¹ (inv_mem hp) ⟨y, hy, rfl⟩
      simpa using h1
    · intro hy
      have h1 := hconj p hp (show y ∈ conjugate K p from ⟨p * y * p⁻¹, hy, by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩)
      exact h1
  have hP : ((layerIn C).subgroupOf C).IsSubnormal := by
    have : (pLayer ↥C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    have hP' : (layerIn C).subgroupOf C = pLayer ↥C 2 :=
      comap_map_eq_self_of_injective C.subtype_injective _
    rw [hP']
    exact Subgroup.Normal.isSubnormal inferInstance
  have hKn : ((K.subgroupOf C).subgroupOf ((layerIn C).subgroupOf C)).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
    have hgP : ((g : C) : G) ∈ layerIn C := mem_subgroupOf.mp g.2
    have := (mem_normalizer_iff.mp (hPN hgP) _).mp hx
    simpa using this
  exact Subgroup.IsSubnormal.trans (fun x hx => hKP hx) hKn.isSubnormal hP

omit [Finite G] in
theorem conjugate_eq_self {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    conjugate H g = H := by
  ext y
  simp only [conjugate, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have := (mem_normalizer_iff.mp (inv_mem hg) h).mp hh
    simpa using this
  · intro hy
    exact ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hg y).mp hy, by group⟩

omit [Finite G] in
theorem conjugate_conjugate'' (H : Subgroup G) (a b : G) :
    conjugate (conjugate H a) b = conjugate H (a * b) := by
  ext y
  simp only [conjugate, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    exists_exists_and_eq_and]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by group⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by group⟩

theorem commutator_l34K_le {L H : Subgroup G} {u : G}
    (h : ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      ⁅H, K₁⁆ ≤ oddIn (centralizer ({u} : Set G))) :
    ⁅H, l34K L u⁆ ≤ oddIn (centralizer ({u} : Set G)) := by
  set C := centralizer ({u} : Set G) with hC
  have hconjO : ∀ c ∈ C, ∀ x ∈ oddIn C, c * x * c⁻¹ ∈ oddIn C := fun c hc x hx =>
    (mem_normalizer_iff.mp (normalizer_le_normalizer_oddIn C (le_normalizer hc)) x).mp hx
  let M : Subgroup G :=
    { carrier := {g | g ∈ C ∧ ∀ x ∈ H, x * g * x⁻¹ * g⁻¹ ∈ oddIn C}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun x hx => by
        have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem (ha.2 x hx) (hconjO a ha.1 _ (hb.2 x hx))⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun x hx => by
        have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hconjO a⁻¹ (inv_mem ha.1) _ (inv_mem (ha.2 x hx))⟩ }
  have hKM : l34K L u ≤ M := by
    refine iSup_le fun K₁ => iSup_le fun hK₁ => iSup_le fun hK₁p => iSup_le fun hK₁Y => ?_
    intro g hg
    refine ⟨hK₁ hg, fun x hx => ?_⟩
    have := h K₁ hK₁ hK₁p hK₁Y (commutator_mem_commutator hx hg)
    rwa [commutatorElement_def] at this
  rw [commutator_le]
  intro x hx g hg
  rw [commutatorElement_def]
  exact (hKM hg).2 x hx

omit [Finite G] in
theorem ne_bot_of_isPComponent {X : Type*} [Group X] {K : Subgroup X} (hK : IsPComponent 2 K) :
    K ≠ ⊥ := by
  rintro rfl
  obtain ⟨K', hK', -, hmap, -⟩ := hK
  rw [Subgroup.map_bot] at hmap
  subst hmap
  obtain ⟨⟨-, hs, -⟩, -⟩ := hK'
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  congr 1
  exact Subsingleton.elim _ _

omit [Finite G] in
theorem ne_bot_of_isPComponent_subgroupOf {C K : Subgroup G}
    (hK : IsPComponent 2 (K.subgroupOf C)) : K ≠ ⊥ := by
  rintro rfl
  exact ne_bot_of_isPComponent hK (by rw [bot_subgroupOf])

omit [Finite G] in
theorem conjugate_conjugate_inv'' (X : Subgroup G) (g : G) :
    conjugate (conjugate X g) g⁻¹ = X := by
  rw [conjugate_conjugate'', mul_inv_cancel]
  ext y
  simp [conjugate]

omit [Finite G] in
theorem conjugate_commutator (A B : Subgroup G) (x : G) :
    conjugate ⁅A, B⁆ x = ⁅conjugate A x, conjugate B x⁆ :=
  map_commutator _ _ _

theorem conjugate_l34K_le {L : Subgroup G} {u g : G}
    (hg : ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ → conjugate K₁ g ≤ l34K L u) :
    conjugate (l34K L u) g ≤ l34K L u := by
  rw [conjugate, map_le_iff_le_comap]
  refine iSup_le fun K₁ => iSup_le fun hK₁ => iSup_le fun hK₁p => iSup_le fun hK₁Y => ?_
  exact map_le_iff_le_comap.mp (hg K₁ hK₁ hK₁p hK₁Y)

theorem not_commutator_le_of_le_l34K {L K₁ : Subgroup G} {u : G} (hK₁K : K₁ ≤ l34K L u)
    (hK₁C : K₁ ≤ centralizer ({u} : Set G))
    (hK₁ : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G)))) :
    ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({u} : Set G) with hC
  intro hK₁Y
  have hcomm : ⁅K₁, l34K L u⁆ ≤ oddIn C := by
    refine commutator_l34K_le fun K₂ hK₂C hK₂ hK₂Y => ?_
    have hne : K₁ ≠ K₂ := by
      rintro rfl
      exact hK₂Y hK₁Y
    exact (commutator_le_of_ne hK₁C hK₂C hK₁ hK₂ hne).1
  have hperf : ⁅K₁, K₁⁆ = K₁ := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hK₁
    have h2 : Group.IsPerfect K₁ := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hK₁C).toMonoidHom) (subgroupOfEquivOfLe hK₁C).surjective
    exact (Subgroup.isPerfect_iff (H := K₁)).mp h2
  have hK₁O : K₁ ≤ oddIn C := by
    rw [← hperf]
    exact (commutator_mono le_rfl hK₁K).trans hcomm
  have hodd : Odd (Nat.card K₁) := by
    refine Odd.of_dvd_nat ?_ (card_dvd_of_le hK₁O)
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hperf' : _root_.commutator ↥K₁ = ⊤ := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hK₁
    have h2 : Group.IsPerfect K₁ := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hK₁C).toMonoidHom) (subgroupOfEquivOfLe hK₁C).surjective
    exact h2.commutator_eq_top
  exact ne_bot_of_isPComponent_subgroupOf hK₁
    (ClassicalInvolution.Balance.eq_bot_of_perfect_of_odd hperf' hodd)

theorem l34Notation54_of_inputs (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
      L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S,
        l34K L u ≠ ⊥ ∧
        (∀ K₁ : Subgroup G, K₁ ≤ l34K L u → IsPComponent 2 (K₁.subgroupOf (l34K L u)) →
          K₁ ≤ centralizer ({u} : Set G) ∧
            IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) ∧
            IsUnbalancingComponent K₁) ∧
        l34K L u ≤ (⨆ (K₁ : Subgroup G) (_ : K₁ ≤ l34K L u)
            (_ : IsPComponent 2 (K₁.subgroupOf (l34K L u))), K₁) ⊔ oddIn (l34K L u) ∧
        centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G) ≤
          normalizer ((l34K L u : Subgroup G) : Set G) := by
  intro G _ _ L t S T hset u hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  obtain ⟨-, hfam, -, -, htS, -, -⟩ := hset
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -, -, -⟩ := hfam
  obtain ⟨huU, huo, huX⟩ := hu
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS)) huU
  have htu : t * u = u * t := (hZS u huS).symm
  set C := centralizer ({u} : Set G) with hC
  set Y := oddIn L ⊓ C with hY
  have hYD : Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ C :=
    inf_le_inf_right C (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hKC := l34K_le_centralizer L u
  have hsub := isSubnormal_l34K L u
  have hgen : ∀ K₁ : Subgroup G, K₁ ≤ l34K L u → K₁ ≤ C → IsPComponent 2 (K₁.subgroupOf C) →
      ¬ ⁅K₁, Y⁆ ≤ oddIn K₁ := fun K₁ hK₁K hK₁C hK₁ => not_commutator_le_of_le_l34K hK₁K hK₁C hK₁
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨K₁, hK₁C, hK₁, hK₁Y⟩ := exists_isPComponent_not_le hSol hto huo htu hYD huX
    intro hbot
    have h1 : K₁ ≤ l34K L u := le_l34K hK₁C hK₁ hK₁Y
    rw [hbot, le_bot_iff] at h1
    exact ne_bot_of_isPComponent_subgroupOf hK₁ h1
  ·
    intro K₁ hK₁K hK₁
    have hK₁C : K₁ ≤ C := hK₁K.trans hKC
    have hK₁p : IsPComponent 2 (K₁.subgroupOf C) :=
      isPComponent_subgroupOf_of_isSubnormal hK₁K hKC hsub hK₁
    exact ⟨hK₁C, hK₁p, u, t, gsUnbalancingTriple_of_not_le hSol hto huo htu hK₁C hK₁p hYD
      (hgen K₁ hK₁K hK₁C hK₁p)⟩
  ·
    refine le_trans ?_ le_sup_left
    refine iSup_le fun K₁ => iSup_le fun hK₁C => iSup_le fun hK₁ => iSup_le fun hK₁Y => ?_
    have hK₁K : K₁ ≤ l34K L u := le_l34K hK₁C hK₁ hK₁Y
    have hK₁' : IsPComponent 2 (K₁.subgroupOf (l34K L u)) := by
      have h1 := CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hK₁
        (show K₁.subgroupOf C ≤ (l34K L u).subgroupOf C from fun x hx => hK₁K hx)
      exact (LieType.AlgebraicGroups.isPComponent_subgroupOf_subgroupOf_iff hKC 2
        Nat.prime_two).mp h1
    exact le_iSup_of_le K₁ (le_iSup_of_le hK₁K (le_iSup_of_le hK₁' le_rfl))
  ·
    intro c hc
    obtain ⟨hcu, hct⟩ := mem_inf.mp hc
    have hcL : c ∈ normalizer (L : Set G) := hCN hct
    have hcY : c ∈ normalizer (Y : Set G) := by
      have h1 : c ∈ normalizer (oddIn L : Set G) := normalizer_le_normalizer_oddIn L hcL
      have h2 : c ∈ normalizer (C : Set G) := le_normalizer hcu
      rw [mem_normalizer_iff] at h1 h2 ⊢
      intro y
      rw [hY, mem_inf, mem_inf, h1 y, h2 y]
    have hconj : ∀ g ∈ normalizer (Y : Set G), g ∈ C →
        conjugate (l34K L u) g ≤ l34K L u := by
      intro g hgY hgC
      refine conjugate_l34K_le fun K₁ hK₁C hK₁ hK₁Y => ?_
      obtain ⟨h1, h2⟩ := GSThmB.isPComponent_conjugate_centralizer_singleton hK₁C hK₁ hgC
      refine le_l34K h1 h2 fun hle => hK₁Y ?_
      have h3 := map_mono (f := (MulAut.conj g⁻¹⁻¹).toMonoidHom) hle
      change conjugate ⁅conjugate K₁ g, Y⁆ g⁻¹ ≤ conjugate (oddIn (conjugate K₁ g)) g⁻¹ at h3
      rw [conjugate_commutator, conjugate_conjugate_inv'', conjugate_eq_self (inv_mem hgY)] at h3
      have hO : conjugate (oddIn (conjugate K₁ g)) g⁻¹ = oddIn K₁ := by
        have h4 := GSLit.conjugate_map_pPrimeCore (conjugate K₁ g) g⁻¹
        rw [conjugate_conjugate_inv''] at h4
        exact h4
      rw [hO] at h3
      exact h3
    have hle := hconj c hcY hcu
    have hle' := hconj c⁻¹ (inv_mem hcY) (inv_mem hcu)
    apply mem_normalizer_of_conjugate_eq
    refine le_antisymm hle ?_
    calc l34K L u = conjugate (conjugate (l34K L u) c⁻¹) c := by
          rw [conjugate_conjugate'', inv_mul_cancel]
          ext y
          simp [conjugate]
      _ ≤ conjugate (l34K L u) c := map_mono hle'

end CFSG.ComponentClassification.GrSLit.GrS5
