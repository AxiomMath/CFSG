module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Stmt
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
open scoped commutatorElement

@[expose] noncomputable def centerQuotAut {L : Type} [Group L] (α : MulAut L) :
    MulAut (L ⧸ center L) :=
  QuotientGroup.congr (center L) (center L) α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance _)

theorem centerQuotAut_apply_mk {L : Type} [Group L] (α : MulAut L) (x : L) :
    centerQuotAut α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  QuotientGroup.congr_mk _ _ _ _ x

namespace AbsHyp

section Central

variable {G : Type*} [Group G]

theorem commutatorElement_mul_central_left {x y z : G} (hz : z ∈ center G) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h := Subgroup.mem_center_iff.mp hz y
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * z * y * (z⁻¹ * x⁻¹) * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [← h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_central_right {x y z : G} (hz : z ∈ center G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h := Subgroup.mem_center_iff.mp hz x⁻¹
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * (y * z) * x⁻¹ * (z⁻¹ * y⁻¹) = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [← h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

end Central

section Abstract

variable {C F : Type*} [Group C] [Group F]

theorem normal_of_commutator_top_le {H : Subgroup F} (h : ⁅(⊤ : Subgroup F), ⊤⁆ ≤ H) :
    H.Normal :=
  ⟨fun n hn g => by
    have hc : ⁅g, n⁆ ∈ H := h (Subgroup.commutator_mem_commutator (mem_top g) (mem_top n))
    have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact H.mul_mem hc hn⟩

theorem not_le_ker_of_isQuasisimple {f : C →* F} (hker : f.ker ≤ center C) {K : Subgroup C}
    (hK : IsQuasisimple K) : ¬ K ≤ f.ker := by
  intro hle
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
  have hbot : K = ⊥ := by
    refine le_bot_iff.mp ?_
    calc K = ⁅K, K⁆ := hperf.symm
      _ ≤ ⁅center C, K⁆ := Subgroup.commutator_mono (hle.trans hker) le_rfl
      _ = ⊥ := Subgroup.commutator_center_left K
  have : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hK
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this hbot

theorem exists_component_lift (f : C →* F) (hker : f.ker ≤ center C)
    (hcomm : ⁅(⊤ : Subgroup F), ⊤⁆ ≤ f.range) {X : Subgroup F} (hX : IsComponent X) :
    ∃ Y : Subgroup C, IsComponent Y ∧ Y.map f = X := by
  have hXperf : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.mp hX.1.1
  have hXle : X ≤ f.range := by
    calc X = ⁅X, X⁆ := hXperf.symm
      _ ≤ ⁅(⊤ : Subgroup F), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ ≤ f.range := hcomm
  set X' : Subgroup C := X.comap f
  have hX'sub : X'.IsSubnormal := hX.2.comap f
  let g : ↥X' →* ↥X := (f.comp X'.subtype).codRestrict X (fun x => x.2)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := hXle hy
    exact ⟨⟨c, hy⟩, rfl⟩
  have hgker : g.ker ≤ center ↥X' := by
    intro x hx
    have h1 : f x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : C) ∈ center C := hker (MonoidHom.mem_ker.mpr h1)
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro y
    exact Subtype.ext (h2 y)
  have hq := LocalCores.quasisimple_central_extension_derived_of_surjective g hg hgker hX.1
  obtain ⟨-, -, hsurj⟩ := LocalCores.central_extension_derived_of_surjective g hg hgker hX.1.1
  refine ⟨(commutator ↥X').map X'.subtype, ⟨?_, ?_⟩, ?_⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥X') X'.subtype X'.subtype_injective) hq
  · exact Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hX'sub
  · ext y
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact (g z).2
    · intro hy
      obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
      exact ⟨z.1.1, ⟨z.1, z.2, rfl⟩, congrArg Subtype.val hz⟩

theorem isComponent_map (f : C →* F) (hker : f.ker ≤ center C)
    (hcomm : ⁅(⊤ : Subgroup F), ⊤⁆ ≤ f.range) {K : Subgroup C} (hK : IsComponent K) :
    IsComponent (K.map f) := by
  refine ⟨LocalCores.isQuasisimple_map hK.1 f (not_le_ker_of_isQuasisimple hker hK.1), ?_⟩
  have hRn : f.range.Normal := normal_of_commutator_top_le hcomm
  have h1 : (K.map f.rangeRestrict).IsSubnormal := hK.2.map f.rangeRestrict_surjective
  have h2 := Subgroup.IsSubnormal.trans' h1 hRn.isSubnormal
  rwa [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2

theorem layer_eq_map_of_unique_component (f : C →* F) (hker : f.ker ≤ center C)
    (hcomm : ⁅(⊤ : Subgroup F), ⊤⁆ ≤ f.range) {K₀ : Subgroup C} (hK₀ : IsComponent K₀)
    (huniq : ∀ Y : Subgroup C, IsComponent Y → Y = K₀) : layer F = K₀.map f := by
  refine le_antisymm (sSup_le fun X hX => ?_) (le_sSup (isComponent_map f hker hcomm hK₀))
  obtain ⟨Y, hY, rfl⟩ := exists_component_lift f hker hcomm hX
  rw [huniq Y hY]

end Abstract

section Fixed

variable {L : Type} [Group L] (α : MulAut L)

theorem mem_fixedSubgroup_iff {Q : Type*} [Group Q] {φ : MulAut Q} {x : Q} :
    x ∈ fixedSubgroup Q φ ↔ φ x = x := Iff.rfl

noncomputable def fixedLift :
    ↥(fixedSubgroup L α) →* ↥(fixedSubgroup (L ⧸ center L) (centerQuotAut α)) :=
  ((QuotientGroup.mk' (center L)).comp (fixedSubgroup L α).subtype).codRestrict _ (fun c => by
    rw [mem_fixedSubgroup_iff]
    show centerQuotAut α (QuotientGroup.mk (c : L)) = QuotientGroup.mk (c : L)
    rw [centerQuotAut_apply_mk]
    congr 1
    exact c.2)

theorem ker_fixedLift_le_center : (fixedLift α).ker ≤ center ↥(fixedSubgroup L α) := by
  intro c hc
  have h1 : (QuotientGroup.mk (c : L) : L ⧸ center L) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
  have h2 : (c : L) ∈ center L := (QuotientGroup.eq_one_iff _).mp h1
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro y
  exact Subtype.ext (h2 y)

theorem commutator_top_le_range_fixedLift :
    ⁅(⊤ : Subgroup ↥(fixedSubgroup (L ⧸ center L) (centerQuotAut α))), ⊤⁆ ≤
      (fixedLift α).range := by
  rw [Subgroup.commutator_le]
  rintro g₁ - g₂ -
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (g₁ : L ⧸ center L)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (g₂ : L ⧸ center L)
  have hg₁ : centerQuotAut α (g₁ : L ⧸ center L) = g₁ := g₁.2
  have hg₂ : centerQuotAut α (g₂ : L ⧸ center L) = g₂ := g₂.2
  rw [← hx, centerQuotAut_apply_mk] at hg₁
  rw [← hy, centerQuotAut_apply_mk] at hg₂
  have hz₁ : (α x)⁻¹ * x ∈ center L := QuotientGroup.eq.mp hg₁
  have hz₂ : (α y)⁻¹ * y ∈ center L := QuotientGroup.eq.mp hg₂
  have key : ⁅α x * ((α x)⁻¹ * x), α y * ((α y)⁻¹ * y)⁆ = ⁅α x, α y⁆ := by
    rw [commutatorElement_mul_central_left hz₁, commutatorElement_mul_central_right hz₂]
  have e1 : α x * ((α x)⁻¹ * x) = x := by group
  have e2 : α y * ((α y)⁻¹ * y) = y := by group
  rw [e1, e2] at key
  have hfix : α ⁅x, y⁆ = ⁅x, y⁆ := by
    rw [map_commutatorElement, key]
  refine ⟨⟨⁅x, y⁆, hfix⟩, Subtype.ext ?_⟩
  show (QuotientGroup.mk ⁅x, y⁆ : L ⧸ center L) = ⁅(g₁ : L ⧸ center L), (g₂ : L ⧸ center L)⁆
  rw [← hx, ← hy]
  exact map_commutatorElement (QuotientGroup.mk' (center L)) x y

end Fixed

section PPrimeCore

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem pPrimeCore_eq_ker {G S : Type*} [Group G] [Finite G] [Group S] [IsSimpleGroup S]
    (hS : Even (Nat.card S)) (π : G →* S) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) : pPrimeCore 2 G = π.ker := by
  refine le_antisymm ?_ (le_sSup ⟨π.normal_ker, Nat.coprime_two_left.mpr hker⟩)
  have hOn : (pPrimeCore 2 G).Normal := pPrimeCore_normal
  have hmapn : ((pPrimeCore 2 G).map π).Normal := hOn.map π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 G).map π) with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have h1 : Nat.card ((pPrimeCore 2 G).map π) ∣ Nat.card (pPrimeCore 2 G) :=
      Subgroup.card_map_dvd _ π
    rw [h, Subgroup.card_top] at h1
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    have h2 : 2 ∣ Nat.card (pPrimeCore 2 G) := (even_iff_two_dvd.mp hS).trans h1
    exact absurd (hcop.eq_one_of_dvd h2) (by norm_num)

theorem exists_quotient_pPrimeCore_equiv {P G S : Type*} [Group P] [Group G] [Finite G] [Group S]
    [IsSimpleGroup S] (hS : Even (Nat.card S)) (ψ : P →* G) (hψ : Function.Surjective ψ)
    (π₀ : P →* S) (hπ₀ : Function.Surjective π₀) (hle : ψ.ker ≤ π₀.ker)
    (hodd : Odd (Nat.card π₀.ker)) : Nonempty (G ⧸ pPrimeCore 2 G ≃* S) := by
  obtain ⟨π, hπ⟩ : ∃ π : G →* S, ∀ p, π (ψ p) = π₀ p :=
    ⟨ψ.liftOfSurjective hψ ⟨π₀, hle⟩, fun p => ψ.liftOfRightInverse_comp_apply _ _ ⟨π₀, hle⟩ p⟩
  have hπsurj : Function.Surjective π := fun s => by
    obtain ⟨p, hp⟩ := hπ₀ s
    exact ⟨ψ p, by rw [hπ, hp]⟩
  have hkerπ : π.ker = π₀.ker.map ψ := by
    ext g
    obtain ⟨p, rfl⟩ := hψ g
    simp only [MonoidHom.mem_ker, Subgroup.mem_map, hπ]
    constructor
    · intro h
      exact ⟨p, h, rfl⟩
    · rintro ⟨p', hp', hpp⟩
      have h1 : p'⁻¹ * p ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpp, inv_mul_cancel]
      have h2 := hle h1
      rwa [MonoidHom.mem_ker, map_mul, map_inv, hp', inv_one, one_mul] at h2
  have hoddπ : Odd (Nat.card π.ker) := by
    rw [hkerπ]
    exact Odd.of_dvd_nat hodd (Subgroup.card_map_dvd _ ψ)
  have hcore := pPrimeCore_eq_ker hS π hπsurj hoddπ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπsurj)⟩

end PPrimeCore

end AbsHyp

open AbsHyp in
theorem ivk714Hyp_of_unique_component {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (α : MulAut L) (A : Subgroup L) (hAfix : A ≤ fixedSubgroup L α)
    (hA7 : Nonempty ((↥A ⧸ center ↥A) ≃* alternatingGroup (Fin 7)))
    (hZodd : Odd (Nat.card (center ↥A)))
    (hAcomp : CFSG.IsComponent (A.subgroupOf (fixedSubgroup L α)))
    (huniq : ∀ B : Subgroup L, B ≤ fixedSubgroup L α →
      CFSG.IsComponent (B.subgroupOf (fixedSubgroup L α)) → B = A) :
    Ivk714Hyp (L ⧸ center L) (centerQuotAut α) := by
  have _ := hL
  obtain ⟨e⟩ := hA7
  have hker := ker_fixedLift_le_center α
  have hcomm := commutator_top_le_range_fixedLift α
  have huniq' : ∀ Y : Subgroup ↥(fixedSubgroup L α), IsComponent Y →
      Y = A.subgroupOf (fixedSubgroup L α) := by
    intro Y hY
    have hle : Y.map (fixedSubgroup L α).subtype ≤ fixedSubgroup L α := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hsub : (Y.map (fixedSubgroup L α).subtype).subgroupOf (fixedSubgroup L α) = Y :=
      Subgroup.comap_map_eq_self_of_injective (fixedSubgroup L α).subtype_injective Y
    have hB := huniq _ hle (by rw [hsub]; exact hY)
    rw [← hsub, hB]
  have hlayer := layer_eq_map_of_unique_component (fixedLift α) hker hcomm hAcomp huniq'
  let ψ₀ : ↥A →* ↥(fixedSubgroup (L ⧸ center L) (centerQuotAut α)) :=
    (fixedLift α).comp (Subgroup.inclusion hAfix)
  have hψ₀mem : ∀ a : ↥A,
      ψ₀ a ∈ layer ↥(fixedSubgroup (L ⧸ center L) (centerQuotAut α)) := by
    intro a
    rw [hlayer]
    exact ⟨Subgroup.inclusion hAfix a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  let ψ : ↥A →* ↥(layer ↥(fixedSubgroup (L ⧸ center L) (centerQuotAut α))) :=
    ψ₀.codRestrict _ hψ₀mem
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ (A.subgroupOf (fixedSubgroup L α)).map (fixedLift α) := hlayer ▸ hg
    obtain ⟨k, hk, rfl⟩ := hg'
    exact ⟨⟨k.1, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
  have hψker : ψ.ker ≤ center ↥A := by
    intro x hx
    have h1 : fixedLift α (Subgroup.inclusion hAfix x) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : Subgroup.inclusion hAfix x ∈ center ↥(fixedSubgroup L α) :=
      hker (MonoidHom.mem_ker.mpr h1)
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro y
    have h3 := congrArg (Subtype.val : ↥(fixedSubgroup L α) → L)
      (h2 (Subgroup.inclusion hAfix y))
    exact Subtype.ext h3
  let π₀ : ↥A →* alternatingGroup (Fin 7) := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))
  have hπ₀surj : Function.Surjective π₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ₀ker : π₀.ker = center ↥A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hS : Even (Nat.card (alternatingGroup (Fin 7))) := by
    rw [card_alternatingGroup_seven]
    decide
  have := alternatingGroup.isSimpleGroup (α := Fin 7) (by norm_num)
  exact exists_quotient_pPrimeCore_equiv hS ψ hψsurj π₀ hπ₀surj (hπ₀ker ▸ hψker)
    (hπ₀ker ▸ hZodd)

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
