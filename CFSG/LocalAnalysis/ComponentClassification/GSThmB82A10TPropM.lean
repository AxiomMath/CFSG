module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TLayer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TPump
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10THN

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

section General

variable {G : Type} [Group G]

private theorem propM_mem_centralizer {H : Subgroup G} {x : G}
    (h : H ≤ centralizer ({x} : Set G)) : x ∈ centralizer (H : Set G) :=
  mem_centralizer_iff.mpr fun _ hy => mem_centralizer_singleton_iff.mp (h hy)

private theorem propM_normalizer_le (F : Subgroup G) :
    normalizer (F : Set G) ≤ normalizer (centralizer (F : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (F : Set G), ∀ c ∈ centralizer (F : Set G),
      g * c * g⁻¹ ∈ centralizer (F : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff]
    intro f hf
    have h1 : g⁻¹ * f * g ∈ F := by
      have := (mem_normalizer_iff.mp (inv_mem hg) f).mp hf
      rwa [inv_inv] at this
    have h2 := mem_centralizer_iff.mp hc _ h1
    calc f * (g * c * g⁻¹) = g * ((g⁻¹ * f * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * f * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * f := by group
  intro g hg
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

private theorem propM_conjugate_le {C H : Subgroup G} {g : G} (hg : g ∈ C) (hH : H ≤ C) :
    conjugate H g ≤ C := by
  intro x hx
  rw [UnbalancedLayer.mem_conjugate_iff] at hx
  have h := mul_mem (mul_mem (inv_mem hg) (hH hx)) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

private theorem propM_isPGroup_zpowers {a : G} (ha : orderOf a = 2) : IsPGroup 2 (zpowers a) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])

private theorem propM_le_coreActionKernel {F M : Subgroup G}
    (hMC : M ≤ centralizer (F : Set G)) : F ≤ coreActionKernel M := by
  intro f hf
  have hcomm : ∀ m ∈ M, f * m = m * f := fun m hm => mem_centralizer_iff.mp (hMC hm) f hf
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun m hm => (hcomm m hm).symm), fun j hj => ?_⟩
  have h1 : j⁻¹ * f⁻¹ * j * f = 1 := by
    calc j⁻¹ * f⁻¹ * j * f = j⁻¹ * f⁻¹ * (j * f) := by group
      _ = j⁻¹ * f⁻¹ * (f * j) := by rw [← hcomm j hj]
      _ = 1 := by group
  rw [h1]
  exact one_mem _

private theorem propM_card_conjugate (M : Subgroup G) (g : G) :
    Nat.card (↥(conjugate M g) ⧸ Open.fusionZStar ↥(conjugate M g)) =
      Nat.card (↥M ⧸ Open.fusionZStar ↥M) :=
  (Nat.card_congr (Sol78.fusionZStarQuotCongr (M.equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)).toEquiv).symm

variable [Finite G]

private theorem propM_exists_orbit_component {a : G} (ha : orderOf a = 2) {C : Subgroup G}
    (haC : a ∈ C) {T : Subgroup G} (hT : T ≤ centralizer ({a} : Set G) ⊓ C)
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ C)))
    (hTE : T ≤ layerIn C) :
    ∃ M : Subgroup G, M ≤ C ∧ IsPComponent 2 (M.subgroupOf C) ∧ T ≤ M ⊔ conjugate M a ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G)
  have hTC : T ≤ C := hT.trans inf_le_right
  have ha' : orderOf (⟨a, haC⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena := UGSChain.centralizer_mk_eq_subgroupOf haC
  have hT'C : T.subgroupOf C ≤ centralizer ({(⟨a, haC⟩ : C)} : Set C) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hT (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf C).subgroupOf
      (centralizer ({(⟨a, haC⟩ : C)} : Set C))) := by
    rw [hcena, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact hTpc
  have hTE' : T ≤ (pLayer C 2).map C.subtype := hTE
  have hT'E : T.subgroupOf C ≤ pLayer C 2 := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := mem_map.mp (hTE' (mem_subgroupOf.mp hy))
    rwa [← Subtype.ext hzy]
  obtain ⟨M', hM', hT'K, hT'Kpc⟩ :=
    UnbalancedLayer.two_layer_fixed_component_orbit_location ha' hT'C hT'pc hT'E
  obtain ⟨M, hMC, rfl⟩ : ∃ M : Subgroup G, M ≤ C ∧ M.subgroupOf C = M' :=
    ⟨M'.map C.subtype, map_subtype_le _, comap_map_eq_self_of_injective C.subtype_injective _⟩
  have hMaC : conjugate M a ≤ C := propM_conjugate_le haC hMC
  have hK'eq : M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨a, haC⟩ =
      (M ⊔ conjugate M a).subgroupOf C := by
    rw [UnbalancedLayer.conjugate_subgroupOf_eq M C ⟨a, haC⟩, subgroupOf_sup hMC hMaC]
  have hKC : M ⊔ conjugate M a ≤ C := sup_le hMC hMaC
  have hCeq : (M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨a, haC⟩) ⊓
      centralizer ({(⟨a, haC⟩ : C)} : Set C) = ((M ⊔ conjugate M a) ⊓ Ca).subgroupOf C := by
    rw [hK'eq, hcena]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  refine ⟨M, hMC, hM', fun t ht => ?_, ?_⟩
  · have h1 := hT'K (show (⟨t, hTC ht⟩ : C) ∈ T.subgroupOf C from ht)
    rw [hK'eq] at h1
    exact h1
  · rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKC) 2 Nat.prime_two] at hT'Kpc
    exact hT'Kpc

private theorem propM_card_of_swap {a : G} (ha : orderOf a = 2) {C : Subgroup G} (haC : a ∈ C)
    {M T : Subgroup G} (hMC : M ≤ C) (hM : IsPComponent 2 (M.subgroupOf C))
    (hne : M ≠ conjugate M a) (hTK : T ≤ (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))
    (hT : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G)))) :
    Nat.card (↥T ⧸ Open.fusionZStar ↥T) = Nat.card (↥M ⧸ Open.fusionZStar ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G)
  have ha' : orderOf (⟨a, haC⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena := UGSChain.centralizer_mk_eq_subgroupOf haC
  have hMaC : conjugate M a ≤ C := propM_conjugate_le haC hMC
  have hKC : M ⊔ conjugate M a ≤ C := sup_le hMC hMaC
  have hTC : T ≤ C := hTK.trans (inf_le_left.trans hKC)
  have hconj : conjugate (M.subgroupOf C) ⟨a, haC⟩ = (conjugate M a).subgroupOf C :=
    UnbalancedLayer.conjugate_subgroupOf_eq M C ⟨a, haC⟩
  have hK'eq : M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨a, haC⟩ =
      (M ⊔ conjugate M a).subgroupOf C := by
    rw [hconj, subgroupOf_sup hMC hMaC]
  have hCeq : (M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨a, haC⟩) ⊓
      centralizer ({(⟨a, haC⟩ : C)} : Set C) = ((M ⊔ conjugate M a) ⊓ Ca).subgroupOf C := by
    rw [hK'eq, hcena]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  have hT'C : T.subgroupOf C ≤ (M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨a, haC⟩) ⊓
      centralizer ({(⟨a, haC⟩ : C)} : Set C) := by
    rw [hCeq]
    intro y hy
    exact mem_subgroupOf.mpr (hTK (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf C).subgroupOf
      ((M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨a, haC⟩) ⊓
        centralizer ({(⟨a, haC⟩ : C)} : Set C))) := by
    rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKC) 2 Nat.prime_two]
    exact hT
  have hne' : M.subgroupOf C ≠ conjugate (M.subgroupOf C) ⟨a, haC⟩ := by
    rw [hconj]
    intro h
    rw [subgroupOf_inj, inf_of_le_left hMC, inf_of_le_left hMaC] at h
    exact hne h
  obtain ⟨e⟩ := CatLeaf.swap_case_type ha' (M.subgroupOf C) hM hne' (T.subgroupOf C) hT'C hT'pc
  calc Nat.card (↥T ⧸ Open.fusionZStar ↥T)
      = Nat.card (↥(T.subgroupOf C) ⧸ Open.fusionZStar ↥(T.subgroupOf C)) :=
        Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hTC)).symm.toEquiv
    _ = Nat.card (↥(M.subgroupOf C) ⧸ Open.fusionZStar ↥(M.subgroupOf C)) :=
        Nat.card_congr e.toEquiv
    _ = Nat.card (↥M ⧸ Open.fusionZStar ↥M) :=
        Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hMC)).toEquiv

end General

structure PropMCfg (X : Type) [Group X] [Finite X] where
  a : X
  J : Subgroup X
  B₀ : Subgroup X
  orderOf_a : orderOf a = 2
  J_le : J ≤ centralizer ({a} : Set X)
  isPComponent_J : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X)))
  card_J : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) ≤ 360
  isPGroup_B₀ : IsPGroup 2 B₀
  B₀_le_kernel : B₀ ≤ coreActionKernel J
  B₀_le_centralizer : B₀ ≤ centralizer ({a} : Set X)
  J₀_le : GSLit.fixedLayer J B₀ ≤ layerIn (centralizer (B₀ : Set X))
  equiv_L : Nonempty (↥(layerIn (centralizer (B₀ : Set X))) ⧸
    pPrimeCore 2 ↥(layerIn (centralizer (B₀ : Set X))) ≃* alternatingGroup (Fin 10))
  kGroup : ∀ F : Subgroup X, F ≤ B₀ → F ≠ ⊥ → SectionRank.IsKGroupCat ↥(normalizer (F : Set X))

namespace PropMCfg

variable {X : Type} [Group X] [Finite X] (c : PropMCfg X)

abbrev L : Subgroup X := layerIn (centralizer (c.B₀ : Set X))

theorem isPComponent_L : IsPComponent 2 (c.L.subgroupOf (centralizer (c.B₀ : Set X))) := by
  apply isPComponent_layerIn_of_isSimpleGroup
  obtain ⟨e⟩ := c.equiv_L
  have : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  exact e.isSimpleGroup

theorem isPerfect_L : Group.IsPerfect c.L :=
  isPerfect_layerIn _

private theorem L_le : c.L ≤ centralizer (c.B₀ : Set X) :=
  map_subtype_le _

private theorem isQuasisimple_L : IsQuasisimple (↥c.L ⧸ pPrimeCore 2 ↥c.L) :=
  isQuasisimple_of_isPComponent c.L_le c.isPComponent_L

private theorem card_quot_fusionZStar_L :
    Nat.card (↥c.L ⧸ Open.fusionZStar ↥c.L) = 1814400 := by
  obtain ⟨e⟩ := c.equiv_L
  calc Nat.card (↥c.L ⧸ Open.fusionZStar ↥c.L) = Nat.card (↥c.L ⧸ pPrimeCore 2 ↥c.L) := by
        rw [EvenPump.fusionZStar_eq_of_alt (by norm_num) e]
    _ = Nat.card (alternatingGroup (Fin 10)) := Nat.card_congr e.toEquiv
    _ = 1814400 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        rfl

private theorem isQuasisimple_J : IsQuasisimple (↥c.J ⧸ pPrimeCore 2 ↥c.J) :=
  isQuasisimple_of_isPComponent c.J_le c.isPComponent_J

private theorem B₀_le_normalizer_L : c.B₀ ≤ normalizer (c.L : Set X) :=
  le_normalizer.trans (Seven.normalizer_le_normalizer_layerIn_centralizer c.B₀)

private theorem fixedLayer_le (F : Subgroup X) :
    GSLit.fixedLayer c.J F ≤ centralizer ({c.a} : Set X) ⊓ centralizer (F : Set X) :=
  le_inf ((GSLit.fixedLayer_le_inf _ _).trans (inf_le_left.trans c.J_le))
    ((GSLit.fixedLayer_le_inf _ _).trans inf_le_right)

private theorem card_quot_fusionZStar_fixedLayer_le (F : Subgroup X) :
    Nat.card (↥(GSLit.fixedLayer c.J F) ⧸ Open.fusionZStar ↥(GSLit.fixedLayer c.J F)) ≤ 360 :=
  (card_quot_fusionZStar_le_of_le ((GSLit.fixedLayer_le_inf _ _).trans inf_le_left)).trans c.card_J

theorem fixedLayer_isPComponent {F : Subgroup X} (hFB : F ≤ c.B₀) :
    IsPComponent 2 ((GSLit.fixedLayer c.J F).subgroupOf
      (centralizer ({c.a} : Set X) ⊓ centralizer (F : Set X))) ∧
    ¬ Group.IsSolvable ↥(GSLit.fixedLayer c.J F) := by
  obtain ⟨-, -, hs, -, -⟩ := c.isPComponent_J
  have hpc := GSLit.fixedLayer_isPComponent c.J_le hs (hFB.trans c.B₀_le_centralizer)
    (hFB.trans c.B₀_le_kernel) (c.isPGroup_B₀.to_le hFB) c.isQuasisimple_J
  exact ⟨hpc, not_isSolvable_of_isQuasisimple (isQuasisimple_of_isPComponent (c.fixedLayer_le F)
    hpc)⟩

theorem a_mem_normalizer_L : c.a ∈ normalizer (c.L : Set X) :=
  mem_normalizer_layerIn (propM_mem_centralizer c.B₀_le_centralizer)

theorem exists_unique_component {F : Subgroup X} (hFB : F ≤ c.B₀)
    (hFn : c.B₀ ≤ normalizer (F : Set X)) :
    ∃ M : Subgroup X, M ≤ centralizer (F : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer (F : Set X))) ∧ c.L ≤ M ∧
      (∀ M' : Subgroup X, M' ≤ centralizer (F : Set X) →
        IsPComponent 2 (M'.subgroupOf (centralizer (F : Set X))) → c.L ≤ M' → M' = M) ∧
      normalizer (c.L : Set X) ⊓ normalizer (F : Set X) ≤ normalizer (M : Set X) ∧
      GSLit.fixedLayer c.J F ≤ M := by
  set C := centralizer (F : Set X)
  have haC : c.a ∈ C := propM_mem_centralizer (hFB.trans c.B₀_le_centralizer)
  have hCB : centralizer (c.B₀ : Set X) ≤ C := centralizer_le hFB
  have hB₀C : c.B₀ ≤ normalizer (C : Set X) := hFn.trans (propM_normalizer_le F)
  have hLq := c.isQuasisimple_L
  have hLns := not_isSolvable_of_isQuasisimple hLq
  have hLC : c.L ≤ C := c.L_le.trans hCB
  have hLlay : c.L ≤ layerIn C := by
    have h := layerIn_inf_centralizer_le c.isPGroup_B₀ hB₀C
    rwa [inf_of_le_right hCB] at h
  obtain ⟨hJFpc, -⟩ := c.fixedLayer_isPComponent hFB
  obtain ⟨hJ₀pc, hJ₀ns⟩ := c.fixedLayer_isPComponent le_rfl
  have hJ₀JF : GSLit.fixedLayer c.J c.B₀ ≤ GSLit.fixedLayer c.J F :=
    (GSLit.fixedLayer_nested c.isQuasisimple_J c.B₀_le_kernel c.isPGroup_B₀ hFB).1
  have hJFle : GSLit.fixedLayer c.J F ≤ centralizer ({c.a} : Set X) ⊓ C := c.fixedLayer_le F
  have hJFlay : GSLit.fixedLayer c.J F ≤ layerIn C := by
    apply le_layerIn_of_isPComponent_inf_centralizer (propM_isPGroup_zpowers c.orderOf_a)
      (zpowers_le.mpr (le_normalizer haC))
    · rw [UnbalancedLayer.centralizer_zpowers_eq, inf_comm]
      exact hJFle
    · rw [UnbalancedLayer.centralizer_zpowers_eq, inf_comm]
      exact hJFpc
  obtain ⟨M₀, hM₀C, hM₀, hJFK, hJFKpc⟩ :=
    propM_exists_orbit_component c.orderOf_a haC hJFle hJFpc hJFlay
  by_cases hMa : M₀ = conjugate M₀ c.a
  swap
  ·
    exfalso
    have hMaC : conjugate M₀ c.a ≤ C := propM_conjugate_le haC hM₀C
    obtain ⟨-, hM₀a⟩ := isPComponent_conjugate (le_normalizer haC) hM₀C hM₀
    have hcard := propM_card_of_swap c.orderOf_a haC hM₀C hM₀ hMa
      (le_inf hJFK (hJFle.trans inf_le_left)) hJFKpc
    have h360 := c.card_quot_fusionZStar_fixedLayer_le F
    have hL := c.card_quot_fusionZStar_L
    have hlt : Nat.card (↥M₀ ⧸ Open.fusionZStar ↥M₀) <
        Nat.card (↥c.L ⧸ Open.fusionZStar ↥c.L) := by omega
    have hlt' : Nat.card (↥(conjugate M₀ c.a) ⧸ Open.fusionZStar ↥(conjugate M₀ c.a)) <
        Nat.card (↥c.L ⧸ Open.fusionZStar ↥c.L) := by
      rw [propM_card_conjugate]
      exact hlt
    have h1 := commutator_le_oddCoreIn_of_card_lt hM₀C hM₀ hLlay c.isPerfect_L hLq hlt
    have h2 := commutator_le_oddCoreIn_of_card_lt hMaC hM₀a hLlay c.isPerfect_L hLq hlt'
    have h3 := commutator_sup_le_oddCoreIn hLC hM₀C hMaC h1 h2
    have h4 : ⁅GSLit.fixedLayer c.J c.B₀, GSLit.fixedLayer c.J c.B₀⁆ ≤ oddCoreIn C :=
      (commutator_mono c.J₀_le (hJ₀JF.trans hJFK)).trans h3
    rw [Subgroup.isPerfect_iff.mp (isPerfect_of_isPComponent (c.fixedLayer_le c.B₀) hJ₀pc)]
      at h4
    exact hJ₀ns (isSolvable_of_le_oddCoreIn h4)
  have hJFM₀ : GSLit.fixedLayer c.J F ≤ M₀ := by
    have h := hJFK
    rwa [← hMa, sup_idem] at h
  have hLM₀ : c.L ≤ M₀ := le_of_le_layerIn_of_nonsolvable_quasisimple hM₀C hM₀ hLlay
    c.isPerfect_L hLq c.J₀_le (hJ₀JF.trans hJFM₀) hJ₀ns
  have huniq : ∀ M' : Subgroup X, M' ≤ C → IsPComponent 2 (M'.subgroupOf C) → c.L ≤ M' →
      M' = M₀ :=
    fun M' hM'C hM' hLM' => eq_of_le_of_le_of_not_isSolvable hM'C hM₀C hM' hM₀ hLM' hLM₀ hLns
  refine ⟨M₀, hM₀C, hM₀, hLM₀, huniq, fun g hg => ?_, hJFM₀⟩
  obtain ⟨hgL, hgF⟩ := mem_inf.mp hg
  obtain ⟨hgM₀C, hgM₀⟩ := isPComponent_conjugate (propM_normalizer_le F hgF) hM₀C hM₀
  have hLg : c.L ≤ conjugate M₀ g :=
    (UnbalancedLayer.conjugate_eq_of_mem_normalizer hgL).symm.le.trans (map_mono hLM₀)
  exact UnbalancedLayer.mem_normalizer_of_conjugate_eq (huniq _ hgM₀C hgM₀ hLg)

theorem component_type (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    {F : Subgroup X} (hFB : F ≤ c.B₀) (hFn : c.B₀ ≤ normalizer (F : Set X)) (hF1 : F ≠ ⊥)
    {M : Subgroup X} (hMC : M ≤ centralizer (F : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (F : Set X)))) (hLM : c.L ≤ M) :
    (∃ n : ℕ, Even n ∧ 10 ≤ n ∧ Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))) ∨
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.Carrier .HN) := by
  induction hk : Nat.card c.B₀ - Nat.card F using Nat.strong_induction_on generalizing F M with
  | _ k ih =>
  set C := centralizer (F : Set X) with hC
  have hCN : C ≤ normalizer (F : Set X) := centralizer_le_normalizer _
  have hCB : centralizer (c.B₀ : Set X) ≤ C := centralizer_le hFB
  have hLns := not_isSolvable_of_isQuasisimple c.isQuasisimple_L
  obtain ⟨M₁, -, -, -, huniq, hnorm, -⟩ := c.exists_unique_component hFB hFn
  obtain rfl : M = M₁ := huniq M hMC hM hLM
  have hB₀M : c.B₀ ≤ normalizer (M : Set X) := fun u hu =>
    hnorm (mem_inf.mpr ⟨c.B₀_le_normalizer_L hu, hFn hu⟩)
  have hMN : M ≤ normalizer (F : Set X) := hMC.trans hCN
  have hMNpc : IsPComponent 2 (M.subgroupOf (normalizer (F : Set X))) :=
    isPComponent_of_le_of_subnormal hMC hCN
      (normal_subgroupOf_centralizer_normalizer (F : Set X)).isSubnormal hM
  have hLpcN : IsPComponent 2 (c.L.subgroupOf
      (normalizer (F : Set X) ⊓ centralizer (c.B₀ : Set X))) := by
    rw [inf_of_le_right (hCB.trans hCN)]
    exact c.isPComponent_L
  have hfin : ((∃ n : ℕ, Even n ∧ 10 ≤ n ∧
        Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin n))) ∨
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.Carrier .HN)) →
      (∃ n : ℕ, Even n ∧ 10 ≤ n ∧
        Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))) ∨
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.Carrier .HN) := by
    rintro (⟨n, hn, hn10, ⟨eM⟩⟩ | hHNM)
    · obtain ⟨eL⟩ := c.equiv_L
      exact Or.inl ⟨n, hn, hn10, nonempty_pPrimeCore_equiv_alt_of_fixed' hMN hMNpc hFn
        c.isPGroup_B₀ hB₀M hLM c.L_le hLpcN (by norm_num) eL (by omega) eM⟩
    · exact Or.inr hHNM
  by_cases hFB' : F = c.B₀
  ·
    have hML : M = c.L := le_antisymm
      (by have h := le_layerIn_of_isPComponent hMC hM; rwa [hC, hFB'] at h) hLM
    subst hML
    exact Or.inl ⟨10, by decide, le_rfl, c.equiv_L⟩
  obtain ⟨F', hFF', hF'B, hF'n, hF'card⟩ := exists_normal_index_two c.isPGroup_B₀ hFB hFn hFB'
  have hF'1 : F' ≠ ⊥ := fun h => hF1 (le_bot_iff.mp (h ▸ hFF'))
  have hF'2 : IsPGroup 2 F' := c.isPGroup_B₀.to_le hF'B
  have hC'C : centralizer (F' : Set X) ≤ C := centralizer_le hFF'
  obtain ⟨M', hM'C, hM', hLM', -, -, -⟩ := c.exists_unique_component hF'B hF'n
  have hlt : Nat.card c.B₀ - Nat.card F' < k := by
    have h1 : Nat.card F' ≤ Nat.card c.B₀ := Subgroup.card_le_of_le hF'B
    have h2 : 0 < Nat.card F := Nat.card_pos
    omega
  have hM't := ih _ hlt hF'B hF'n hF'1 hM'C hM' hLM' rfl
  have hF'N : F' ≤ normalizer (C : Set X) := (hF'B.trans hFn).trans (propM_normalizer_le F)
  have hM'lay : M' ≤ layerIn C := by
    apply le_layerIn_of_isPComponent_inf_centralizer hF'2 hF'N
    · rw [inf_of_le_right hC'C]
      exact hM'C
    · rw [inf_of_le_right hC'C]
      exact hM'
  have hM'M : M' ≤ M := le_of_le_layerIn_of_nonsolvable_quasisimple hMC hM hM'lay
    (isPerfect_of_isPComponent hM'C hM') (isQuasisimple_of_isPComponent hM'C hM') hLM' hLM hLns
  have hEk : Nat.card F' ≤ 2 * Nat.card ↥(F' ⊓ coreActionKernel M) := by
    have h : Nat.card F ≤ Nat.card ↥(F' ⊓ coreActionKernel M) :=
      Subgroup.card_le_of_le (le_inf hFF' (propM_le_coreActionKernel hMC))
    omega
  have hM'pc : IsPComponent 2 (M'.subgroupOf
      (normalizer (F : Set X) ⊓ centralizer (F' : Set X))) := by
    rw [inf_of_le_right (hC'C.trans hCN)]
    exact hM'
  exact hfin (pumpStep' hcore hHN (c.kGroup F hFB hF1) hMN hMNpc (hF'B.trans hFn) hF'2
    (hF'B.trans hB₀M) hEk hM'M hM'C hM'pc hM't)

theorem component_alt (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hHNfix : HNFixedComponents) {b : X} (hbB : b ∈ c.B₀) (hb : orderOf b = 2)
    (hbZ : ∀ u ∈ c.B₀, u * b = b * u) {M : Subgroup X} (hMC : M ≤ centralizer ({b} : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X)))) (hLM : c.L ≤ M) :
    ∃ n : ℕ, Even n ∧ 10 ≤ n ∧ Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) := by
  have hCb : centralizer ((zpowers b : Subgroup X) : Set X) = centralizer ({b} : Set X) :=
    UnbalancedLayer.centralizer_zpowers_eq b
  have hFB : zpowers b ≤ c.B₀ := zpowers_le.mpr hbB
  have hFn : c.B₀ ≤ normalizer ((zpowers b : Subgroup X) : Set X) := fun u hu =>
    centralizer_le_normalizer _ (by rw [hCb]; exact mem_centralizer_singleton_iff.mpr (hbZ u hu))
  have hF1 : zpowers b ≠ ⊥ := by
    intro h
    have h1 : b ∈ zpowers b := mem_zpowers b
    rw [h, mem_bot] at h1
    rw [h1, orderOf_one] at hb
    exact absurd hb (by norm_num)
  rw [← hCb] at hMC hM
  rcases c.component_type hcore hHN hFB hFn hF1 hMC hM hLM with h | hHNM
  · exact h
  exfalso
  obtain ⟨eHN⟩ := hHNM
  obtain ⟨M₁, -, -, -, huniq, hnorm, hJM₁⟩ := c.exists_unique_component hFB hFn
  obtain rfl : M = M₁ := huniq M hMC hM hLM
  obtain ⟨hJbpc, -⟩ := c.fixedLayer_isPComponent hFB
  have haC : c.a ∈ centralizer ((zpowers b : Subgroup X) : Set X) :=
    propM_mem_centralizer (hFB.trans c.B₀_le_centralizer)
  have haM : c.a ∈ normalizer (M : Set X) :=
    hnorm (mem_inf.mpr ⟨c.a_mem_normalizer_L, centralizer_le_normalizer _ haC⟩)
  have hE2 : ∀ e ∈ zpowers c.a, e * e = 1 := by
    intro e he
    rcases Seven.eq_one_or_of_mem_zpowers c.orderOf_a he with rfl | rfl
    · exact one_mul 1
    · rw [← pow_two, ← c.orderOf_a, pow_orderOf_eq_one]
  have hEc : Nat.card (zpowers c.a) ≤ 2 := by rw [Nat.card_zpowers, c.orderOf_a]
  have hJE : GSLit.fixedLayer c.J (zpowers b) ≤
      centralizer ((zpowers c.a : Subgroup X) : Set X) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact (c.fixedLayer_le _).trans inf_le_left
  have hJpc : IsPComponent 2 ((GSLit.fixedLayer c.J (zpowers b)).subgroupOf
      (centralizer ((zpowers b : Subgroup X) : Set X) ⊓
        centralizer ((zpowers c.a : Subgroup X) : Set X))) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq c.a, inf_comm]
    exact hJbpc
  obtain ⟨S, _, _, ⟨eS⟩, Q, hQ2, hQc, Tb, hTbF, hTb, hTbcard⟩ :=
    exists_autFixed_pComponent_image' hMC hM (zpowers_le.mpr haC) (zpowers_le.mpr haM) hE2 hEc
      hJM₁ hJE hJpc
  have h1 := lt_card_of_hnFixedComponents hHNfix (eS.trans eHN) hQ2 hQc hTbF hTb
  have h2 := c.card_quot_fusionZStar_fixedLayer_le (zpowers b)
  omega

end PropMCfg

theorem nonempty_layer_equiv_alt10 {X : Type} [Group X] [Finite X] {a : X} (ha : orderOf a = 2)
    {B₀ L J₀ : Subgroup X} (hB₀a : B₀ ≤ centralizer ({a} : Set X))
    (hLC : L ≤ centralizer (B₀ : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer (B₀ : Set X))))
    (haL : a ∈ normalizer (L : Set X)) (hJ₀L : J₀ ≤ L)
    (hJ₀C : J₀ ≤ centralizer ({a} : Set X) ⊓ centralizer (B₀ : Set X))
    (hJ₀ : IsPComponent 2 (J₀.subgroupOf (centralizer ({a} : Set X) ⊓ centralizer (B₀ : Set X))))
    (eJ₀ : ↥J₀ ⧸ pPrimeCore 2 ↥J₀ ≃* alternatingGroup (Fin 6))
    (eL : ↥L ⧸ Open.fusionZStar ↥L ≃* alternatingGroup (Fin 10)) :
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 10)) := by
  set N := normalizer (B₀ : Set X)
  have hCN : centralizer (B₀ : Set X) ≤ N := centralizer_le_normalizer _
  have haN : a ∈ N := hCN (propM_mem_centralizer hB₀a)
  have hLpc : IsPComponent 2 (L.subgroupOf N) := isPComponent_of_le_of_subnormal hLC hCN
    (normal_subgroupOf_centralizer_normalizer (B₀ : Set X)).isSubnormal hL
  have hUV : centralizer ({a} : Set X) ⊓ centralizer (B₀ : Set X) ≤
      N ⊓ centralizer ((zpowers a : Subgroup X) : Set X) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact le_inf (inf_le_right.trans hCN) inf_le_left
  have hUn : ((centralizer ({a} : Set X) ⊓ centralizer (B₀ : Set X)).subgroupOf
      (N ⊓ centralizer ((zpowers a : Subgroup X) : Set X))).Normal := by
    rw [normal_subgroupOf_iff hUV]
    intro h k hh hk
    rw [UnbalancedLayer.centralizer_zpowers_eq] at hk
    obtain ⟨hha, hhB⟩ := mem_inf.mp hh
    obtain ⟨hkN, hka⟩ := mem_inf.mp hk
    refine mem_inf.mpr ⟨mul_mem (mul_mem hka hha) (inv_mem hka), ?_⟩
    exact (normal_subgroupOf_iff hCN).mp (normal_subgroupOf_centralizer_normalizer _) h k hhB hkN
  have hT : IsPComponent 2 (J₀.subgroupOf
      (N ⊓ centralizer ((zpowers a : Subgroup X) : Set X))) :=
    isPComponent_of_le_of_subnormal hJ₀C hUV hUn.isSubnormal hJ₀
  have hTE : J₀ ≤ centralizer ((zpowers a : Subgroup X) : Set X) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact hJ₀C.trans inf_le_left
  exact nonempty_pPrimeCore_equiv_alt_of_fixed' (hLC.trans hCN) hLpc (zpowers_le.mpr haN)
    (propM_isPGroup_zpowers ha) (zpowers_le.mpr haL) hJ₀L hTE hT (by norm_num) eJ₀
    (by norm_num) eL

end CFSG.ComponentClassification.GSThmB.A10T
