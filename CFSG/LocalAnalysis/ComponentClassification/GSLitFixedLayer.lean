module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type*} [Group G]

@[expose] def fixedLayer (J E : Subgroup G) : Subgroup G :=
  (pLayer ↥(J ⊓ centralizer (E : Set G)) 2).map (J ⊓ centralizer (E : Set G)).subtype

theorem fixedLayer_le_inf (J E : Subgroup G) :
    fixedLayer J E ≤ J ⊓ centralizer (E : Set G) :=
  map_subtype_le _

theorem fixedLayer_zpowers (J : Subgroup G) (t : G) :
    fixedLayer J (zpowers t) = gsFixedLayer J t := by
  rw [fixedLayer, gsFixedLayer, centralizer_zpowers_eq]

variable [Finite G]

theorem fixedLayer_nested_core {J D : Subgroup G} (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hD : D ≤ coreActionKernel J) (hD2 : IsPGroup 2 D) :
    (∀ B : Subgroup G, B ≤ D → fixedLayer J B =
      closure {x : G | x ∈ J ⊓ centralizer (B : Set G) ∧ ∃ k : ℕ, orderOf x = 2 ^ k}) ∧
    ∀ B₁ B₂ : Subgroup G, B₁ ≤ B₂ → B₂ ≤ D → fixedLayer J B₂ ≤ fixedLayer J B₁ ∧
      fixedLayer J B₂ ⊔ (pPrimeCore 2 (fixedLayer J B₁)).map (fixedLayer J B₁).subtype =
        fixedLayer J B₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDN : D ≤ normalizer (J : Set G) := fun x hx => (mem_coreActionKernel.mp (hD hx)).1
  let α : D →* MulAut J := J.normalizerMonoidHom.comp (inclusion hDN)
  have hα : ∀ (c : D) (j : J), ((α c j : J) : G) = (c : G) * j * (c : G)⁻¹ :=
    fun c j => normalizerMonoidHom_apply_apply_coe J _ j
  have htriv : ∀ (c : D) (j : J),
      ((α c j : J) : J ⧸ pPrimeCore 2 J) = (j : J ⧸ pPrimeCore 2 J) := by
    intro c j
    rw [eq_comm, QuotientGroup.eq]
    apply (mem_map_iff_mem J.subtype_injective).mp
    have h1 := (mem_coreActionKernel.mp (inv_mem (hD c.2))).2 j j.2
    rw [inv_inv] at h1
    show (j : G)⁻¹ * ((α c j : J) : G) ∈ (pPrimeCore 2 J).map J.subtype
    rw [hα]
    rwa [show (j : G)⁻¹ * ((c : G) * j * (c : G)⁻¹) = (j : G)⁻¹ * c * j * (c : G)⁻¹ by group]
  set C : Subgroup D → Subgroup J := fun B =>
    (centralizer ((B.map D.subtype : Subgroup G) : Set G)).subgroupOf J with hCdef
  have hC : ∀ (B : Subgroup D) (x : J), x ∈ C B ↔ ∀ c ∈ B, α c x = x := by
    intro B x
    show (x : G) ∈ centralizer ((B.map D.subtype : Subgroup G) : Set G) ↔ _
    rw [mem_centralizer_iff]
    constructor
    · intro h1 c hc
      apply Subtype.ext
      rw [hα, h1 (c : G) ⟨c, hc, rfl⟩, mul_inv_cancel_right]
    · intro h1 g hg
      obtain ⟨c, hc, rfl⟩ := mem_map.mp hg
      have h2 := congrArg Subtype.val (h1 c hc)
      rw [hα] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
  set Tf : Subgroup D → Subgroup J := fun B => (pLayer (C B) 2).map (C B).subtype with hTfdef
  obtain ⟨hclos, hnest⟩ :=
    UnbalancedGS.nested_fixed_prime_layer_covering 2 hD2 α hJq htriv C hC Tf (fun B => rfl)
  have hTfB : ∀ B : Subgroup G, B ≤ D →
      (Tf (B.subgroupOf D)).map J.subtype = fixedLayer J B := by
    intro B hBD
    have h1 : ((B.subgroupOf D).map D.subtype : Subgroup G) = B := map_subgroupOf_eq_of_le hBD
    have h2 : (Tf (B.subgroupOf D)).map J.subtype =
        fixedLayer J ((B.subgroupOf D).map D.subtype) :=
      map_pLayer_subgroupOf_eq J _
    rw [h1] at h2
    exact h2
  refine ⟨fun B hBD => ?_, fun B₁ B₂ h12 h2D => ?_⟩
  · rw [← hTfB B hBD, hclos, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨hyC, k, hk⟩, rfl⟩
      refine ⟨mem_inf.mpr ⟨y.2, ?_⟩, k, by
        show orderOf (y : G) = 2 ^ k
        rw [Subgroup.orderOf_coe, hk]⟩
      have h1 : (y : G) ∈ centralizer (((B.subgroupOf D).map D.subtype : Subgroup G) : Set G) :=
        hyC
      rwa [map_subgroupOf_eq_of_le hBD] at h1
    · rintro ⟨hx, k, hk⟩
      refine ⟨⟨x, (mem_inf.mp hx).1⟩, ⟨?_, k, ?_⟩, rfl⟩
      · show x ∈ centralizer (((B.subgroupOf D).map D.subtype : Subgroup G) : Set G)
        rw [map_subgroupOf_eq_of_le hBD]
        exact (mem_inf.mp hx).2
      · rw [← Subgroup.orderOf_coe]
        exact hk
  · obtain ⟨hle, hsup, -⟩ := hnest (B₁.subgroupOf D) (B₂.subgroupOf D)
      (fun x hx => mem_subgroupOf.mpr (h12 (mem_subgroupOf.mp hx)))
    refine ⟨?_, ?_⟩
    · rw [← hTfB B₁ (h12.trans h2D), ← hTfB B₂ h2D]
      exact map_mono hle
    · have h1 := congrArg (Subgroup.map J.subtype) hsup
      rw [Subgroup.map_sup, map_map_pPrimeCore_subtype, hTfB B₁ (h12.trans h2D),
        hTfB B₂ h2D] at h1
      exact h1

theorem fixedLayer_eq_closure {J E : Subgroup G} (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hE : E ≤ coreActionKernel J) (hE2 : IsPGroup 2 E) :
    fixedLayer J E =
      closure {x : G | x ∈ J ⊓ centralizer (E : Set G) ∧ ∃ k : ℕ, orderOf x = 2 ^ k} :=
  (fixedLayer_nested_core hJq hE hE2).1 E le_rfl

theorem fixedLayer_le_of_twoElements {J E K : Subgroup G}
    (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J)) (hE : E ≤ coreActionKernel J)
    (hE2 : IsPGroup 2 E)
    (hK : ∀ x ∈ J ⊓ centralizer (E : Set G), (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ K) :
    fixedLayer J E ≤ K := by
  rw [fixedLayer_eq_closure hJq hE hE2, closure_le]
  rintro x ⟨hx, hk⟩
  exact hK x hx hk

theorem fixedLayer_nested {J B D : Subgroup G} (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hD : D ≤ coreActionKernel J) (hD2 : IsPGroup 2 D) (hBD : B ≤ D) :
    fixedLayer J D ≤ fixedLayer J B ∧
      fixedLayer J D ⊔ (pPrimeCore 2 (fixedLayer J B)).map (fixedLayer J B).subtype =
        fixedLayer J B :=
  (fixedLayer_nested_core hJq hD hD2).2 B D hBD le_rfl

theorem fixedLayer_sup_pPrimeCore {J E : Subgroup G}
    (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J)) (hE : E ≤ coreActionKernel J)
    (hE2 : IsPGroup 2 E) :
    fixedLayer J E ⊔ (pPrimeCore 2 J).map J.subtype = J ∧
      (pPrimeCore 2 (fixedLayer J E)).map (fixedLayer J E).subtype =
        fixedLayer J E ⊓ (pPrimeCore 2 J).map J.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : E ≤ normalizer (J : Set G) := fun x hx => (mem_coreActionKernel.mp (hE hx)).1
  let α : E →* MulAut J := J.normalizerMonoidHom.comp (inclusion hEN)
  have hα : ∀ (c : E) (j : J), ((α c j : J) : G) = (c : G) * j * (c : G)⁻¹ :=
    fun c j => normalizerMonoidHom_apply_apply_coe J _ j
  have htriv : ∀ (c : E) (j : J),
      ((α c j : J) : J ⧸ pPrimeCore 2 J) = (j : J ⧸ pPrimeCore 2 J) := by
    intro c j
    rw [eq_comm, QuotientGroup.eq]
    apply (mem_map_iff_mem J.subtype_injective).mp
    have h1 := (mem_coreActionKernel.mp (inv_mem (hE c.2))).2 j j.2
    rw [inv_inv] at h1
    show (j : G)⁻¹ * ((α c j : J) : G) ∈ (pPrimeCore 2 J).map J.subtype
    rw [hα]
    rwa [show (j : G)⁻¹ * ((c : G) * j * (c : G)⁻¹) = (j : G)⁻¹ * c * j * (c : G)⁻¹ by group]
  set C : Subgroup J := (centralizer (E : Set G)).subgroupOf J with hCdef
  have hC : ∀ x : J, x ∈ C ↔ ∀ c : E, α c x = x := by
    intro x
    show (x : G) ∈ centralizer (E : Set G) ↔ _
    rw [mem_centralizer_iff]
    constructor
    · intro h1 c
      apply Subtype.ext
      rw [hα, h1 (c : G) c.2, mul_inv_cancel_right]
    · intro h1 g hg
      have h2 := congrArg Subtype.val (h1 ⟨g, hg⟩)
      rw [hα] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
  obtain ⟨hsup, hcore, -⟩ := UnbalancedGS.fixed_prime_layer_covers_core_quotient 2 hE2 α hJq
    htriv C hC _ rfl
  have hmap : ((pLayer C 2).map C.subtype).map J.subtype = fixedLayer J E :=
    map_pLayer_subgroupOf_eq J _
  refine ⟨?_, ?_⟩
  · have h1 := congrArg (Subgroup.map J.subtype) hsup
    rw [Subgroup.map_sup, hmap, ← MonoidHom.range_eq_map, range_subtype] at h1
    exact h1
  · have h1 := congrArg (Subgroup.map J.subtype) hcore
    rw [map_map_pPrimeCore_subtype, hmap, map_inf_eq _ _ _ J.subtype_injective, hmap] at h1
    exact h1

theorem fixedLayer_isPComponent {X J E : Subgroup G} (hJX : J ≤ X)
    (hJsub : (J.subgroupOf X).IsSubnormal) (hEX : E ≤ X) (hE : E ≤ coreActionKernel J)
    (hE2 : IsPGroup 2 E) (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J)) :
    IsPComponent 2 ((fixedLayer J E).subgroupOf (X ⊓ centralizer (E : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J' := J.subgroupOf X with hJ'
  set E' := E.subgroupOf X with hE'
  have hcore : ∀ x : X, x ∈ (pPrimeCore 2 J').map J'.subtype ↔
      (x : G) ∈ (pPrimeCore 2 J).map J.subtype := by
    intro x
    have h3 := pPrimeCore_map_subgroupOf 2 J X hJX
    constructor
    · intro hx
      rw [← h3]
      exact mem_map_of_mem X.subtype hx
    · intro hx
      rw [← h3] at hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
      have hyeq : y = x := Subtype.ext hyx
      rwa [← hyeq]
  have hBN : E' ≤ normalizer (J' : Set X) := fun x hx =>
    mem_normalizer_subgroupOf_of_mem (mem_coreActionKernel.mp (hE hx)).1
  have hB : IsPGroup 2 E' := hE2.comap_subtype
  have hQ : IsQuasisimple (J' ⧸ pPrimeCore 2 J') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hJX)).symm
      hJq
  have hcomm' : ⁅J', E'⁆ ≤ (pPrimeCore 2 J').map J'.subtype := by
    rw [commutator_le]
    intro j hj g hg
    rw [hcore]
    have h1 := (mem_coreActionKernel.mp (hE (inv_mem (show (g : G) ∈ E from hg)))).2 _
      (inv_mem (show ((j : X) : G) ∈ J from hj))
    rw [inv_inv, inv_inv] at h1
    exact h1
  have hcen : centralizer ((E' : Subgroup X) : Set X) =
      (X ⊓ centralizer (E : Set G)).subgroupOf X := by
    ext x
    rw [mem_centralizer_iff, mem_subgroupOf, mem_inf, mem_centralizer_iff]
    constructor
    · intro h1
      refine ⟨x.2, fun g hg => ?_⟩
      exact congrArg Subtype.val (h1 ⟨g, hEX hg⟩ (show (⟨g, hEX hg⟩ : X) ∈ E' from hg))
    · intro h1 g hg
      exact Subtype.ext (h1.2 (g : G) hg)
  have hC : J' ⊓ centralizer ((E' : Subgroup X) : Set X) =
      (J ⊓ centralizer (E : Set G)).subgroupOf X := by
    rw [hcen]
    ext x
    simp only [mem_inf, mem_subgroupOf, hJ']
    tauto
  obtain ⟨-, -, -, -, hpc, -⟩ := UnbalancedGS.trivial_quotient_action_fixed_layer_is_p_component 2
    J' hJsub E' hBN hB hQ hcomm' _ rfl _ rfl
  have hTX : (pLayer ↥(J' ⊓ centralizer ((E' : Subgroup X) : Set X)) 2).map
      (J' ⊓ centralizer ((E' : Subgroup X) : Set X)).subtype =
      (fixedLayer J E).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le ((fixedLayer_le_inf J E).trans (inf_le_left.trans hJX)), hC,
      map_pLayer_subgroupOf_eq X _, inf_of_le_right (inf_le_left.trans hJX)]
    rfl
  rw [hTX, hcen] at hpc
  exact (isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two).mp hpc

theorem map_pPrimeCore_subgroupOf_le {Y L : Subgroup G} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) :
    ((pPrimeCore 2 L).map L.subtype).subgroupOf Y ≤ pPrimeCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hs, -, -⟩ := id hL
  have h1 := pPrimeCore_map_subgroupOf 2 L Y hLY
  have h2 : ((pPrimeCore 2 L).map L.subtype).subgroupOf Y =
      (pPrimeCore 2 (L.subgroupOf Y)).map (L.subgroupOf Y).subtype := by
    rw [← h1, subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective]
  rw [h2, map_pPrimeCore_eq_inf_of_isSubnormal hs]
  exact inf_le_right

theorem map_mk_eq_of_sup_pPrimeCore {Y L K : Subgroup G} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) (hK : K ⊔ (pPrimeCore 2 L).map L.subtype = L) :
    (L.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 Y)) =
      (K.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 Y)) := by
  have hKL : K ≤ L := hK ▸ le_sup_left
  have hOL : (pPrimeCore 2 L).map L.subtype ≤ L := map_subtype_le _
  have hbot : (((pPrimeCore 2 L).map L.subtype).subgroupOf Y).map
      (QuotientGroup.mk' (pPrimeCore 2 Y)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact map_pPrimeCore_subgroupOf_le hLY hL
  conv_lhs => rw [← hK]
  rw [subgroupOf_sup (hKL.trans hLY) (hOL.trans hLY), Subgroup.map_sup, hbot, sup_bot_eq]

theorem eq_of_isPComponent_cover {Y L₁ L₂ K : Subgroup G} (h1 : L₁ ≤ Y)
    (hp1 : IsPComponent 2 (L₁.subgroupOf Y)) (h2 : L₂ ≤ Y)
    (hp2 : IsPComponent 2 (L₂.subgroupOf Y))
    (hK1 : K ⊔ (pPrimeCore 2 L₁).map L₁.subtype = L₁)
    (hK2 : K ⊔ (pPrimeCore 2 L₂).map L₂.subtype = L₂) : L₁ = L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heq := pComponent_eq_of_map_eq hp1 hp2
    (by rw [map_mk_eq_of_sup_pPrimeCore h1 hp1 hK1, map_mk_eq_of_sup_pPrimeCore h2 hp2 hK2])
  rw [subgroupOf_inj, inf_of_le_left h1, inf_of_le_left h2] at heq
  exact heq

theorem eq_or_eq_of_le_sup {Y N M M' : Subgroup G} (hN : N ≤ Y)
    (hNp : IsPComponent 2 (N.subgroupOf Y)) (hM : M ≤ Y) (hMp : IsPComponent 2 (M.subgroupOf Y))
    (hM' : M' ≤ Y) (hM'p : IsPComponent 2 (M'.subgroupOf Y)) (hle : N ≤ M ⊔ M') :
    N = M ∨ N = M' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  set π := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ
  have hcomm : ∀ A : Subgroup G, A ≤ Y → IsPComponent 2 (A.subgroupOf Y) → N ≠ A →
      ⁅(N.subgroupOf Y).map π, (A.subgroupOf Y).map π⁆ = ⊥ := by
    intro A hA hAp hNA
    have hne' : N.subgroupOf Y ≠ A.subgroupOf Y := fun h => by
      rw [subgroupOf_inj, inf_of_le_left hN, inf_of_le_left hA] at h
      exact hNA h
    obtain ⟨-, -, hc, -⟩ :=
      (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hNp hAp).2
        hne'
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    obtain ⟨-, -, hs, -, -⟩ := id hNp
    refine hc.trans (inf_le_left.trans ?_)
    rw [map_pPrimeCore_eq_inf_of_isSubnormal hs]
    exact inf_le_right
  have hc1 := hcomm M hM hMp hne1
  have hc2 := hcomm M' hM' hM'p hne2
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at hc1 hc2
  have hNle : (N.subgroupOf Y).map π ≤ (M.subgroupOf Y).map π ⊔ (M'.subgroupOf Y).map π := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup hM hM']
    exact map_mono fun x hx => mem_subgroupOf.mpr (hle (mem_subgroupOf.mp hx))
  have hab : (N.subgroupOf Y).map π ≤ centralizer ((N.subgroupOf Y).map π : Set _) :=
    hNle.trans (sup_le hc1 hc2)
  have hbot : ⁅(N.subgroupOf Y).map π, (N.subgroupOf Y).map π⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr hab
  obtain ⟨Kc, hKc, -, hmap, -⟩ := id hNp
  rw [hmap, Subgroup.isPerfect_iff.mp hKc.1.1] at hbot
  subst hbot
  obtain ⟨x, y, hxy⟩ := hKc.1.2.2
  have h1 : ∀ z : ↥(⊥ : Subgroup (Y ⧸ pPrimeCore 2 Y)) ⧸
      center ↥(⊥ : Subgroup (Y ⧸ pPrimeCore 2 Y)), z = 1 := fun z => by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    rw [Subsingleton.elim w 1]
    rfl
  exact hxy (by rw [h1 x, h1 y])

end CFSG.ComponentClassification.GSLit
