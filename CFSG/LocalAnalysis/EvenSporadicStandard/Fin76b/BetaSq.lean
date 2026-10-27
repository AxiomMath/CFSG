module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaFor

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def BetaDataSq (X : Type*) [Group X] : Prop :=
  ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ β : X, t * β = β * t ∧ BetaFor X β

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}

theorem BetaFor.transport {L : Subgroup G} {X : Type*} [Group X] [Finite X] (φ : X ≃* L) {β : X}
    (hX : BetaFor X β) :
    orderOf ((φ β : L) : G) = 3 ∧
      Nonempty (↥(L ⊓ centralizer ({((φ β : L) : G)} : Set G)) ⧸
        fusionOddCore ↥(L ⊓ centralizer ({((φ β : L) : G)} : Set G)) ≃*
        alternatingGroup (Fin 6)) ∧
      fusionOddCoreOf (L ⊓ centralizer ({((φ β : L) : G)} : Set G)) ≤
        zpowers ((φ β : L) : G) := by
  obtain ⟨hβ3, ⟨eD⟩, hO⟩ := hX
  let ι : X →* G := L.subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp φ.injective
  have hιL : ∀ x, ι x ∈ L := fun x => (φ x).2
  have hDsub : L ⊓ centralizer ({ι β} : Set G) = (centralizer ({β} : Set X)).map ι := by
    ext y
    constructor
    · rintro ⟨hyL, hyc⟩
      obtain ⟨x, hx⟩ : ∃ x : X, ι x = y := ⟨φ.symm ⟨y, hyL⟩, by simp [ι]⟩
      refine ⟨x, mem_centralizer_singleton_iff.2 ?_, hx⟩
      apply hι
      rw [map_mul, map_mul, hx]
      exact mem_centralizer_singleton_iff.1 hyc
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hιL x, mem_centralizer_singleton_iff.2 ?_⟩
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hx]
  let e : ↥(centralizer ({β} : Set X)) ≃* ↥(L ⊓ centralizer ({ι β} : Set G)) :=
    ((centralizer ({β} : Set X)).equivMapOfInjective ι hι).trans
      (MulEquiv.subgroupCongr hDsub.symm)
  have he : ∀ x : ↥(centralizer ({β} : Set X)),
      ((e x : ↥(L ⊓ centralizer ({ι β} : Set G))) : G) = ι x := fun x => rfl
  change orderOf (ι β) = 3 ∧
    Nonempty (↥(L ⊓ centralizer ({ι β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({ι β} : Set G)) ≃* alternatingGroup (Fin 6)) ∧
    fusionOddCoreOf (L ⊓ centralizer ({ι β} : Set G)) ≤ zpowers (ι β)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hβ3]
    exact orderOf_injective ι hι β
  · have hmap : (fusionOddCore ↥(L ⊓ centralizer ({ι β} : Set G))).map e.symm.toMonoidHom =
        fusionOddCore ↥(centralizer ({β} : Set X)) := map_fusionOddCore_mulEquiv e.symm
    exact ⟨(QuotientGroup.congr _ _ e.symm hmap).trans eD⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : e.symm y ∈ fusionOddCore ↥(centralizer ({β} : Set X)) :=
      map_fusionOddCore_le e.symm ⟨y, hy, rfl⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hO ⟨e.symm y, hy', rfl⟩)
    have hj' : β ^ j = ((e.symm y : ↥(centralizer ({β} : Set X))) : X) := hj
    have h1 : ((y : ↥(L ⊓ centralizer ({ι β} : Set G))) : G) =
        ι ((e.symm y : ↥(centralizer ({β} : Set X))) : X) := by
      rw [← he]
      simp
    show ((y : ↥(L ⊓ centralizer ({ι β} : Set G))) : G) ∈ zpowers (ι β)
    rw [h1, ← hj', map_zpow]
    exact zpow_mem (mem_zpowers _) j

@[expose] def BetaDataSqB (X : Type*) [Group X] : Prop :=
  ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ (B : Subgroup X) (β : X),
    B ≤ centralizer ({t} : Set X) ∧ Nonempty (↥B ≃* alternatingGroup (Fin 5)) ∧ β ∈ B ∧
      BetaFor X β

theorem BetaDataSqB.betaDataSq {X : Type*} [Group X] (h : BetaDataSqB X) : BetaDataSq X := by
  intro t ht2 hsq
  obtain ⟨B, β, hB, -, hβB, hβ⟩ := h t ht2 hsq
  exact ⟨β, (mem_centralizer_singleton_iff.1 (hB hβB)).symm, hβ⟩

theorem BetaDataSqB.of_class {X : Type*} [Group X] [Finite X] (t₀ β₀ : X) (B₀ : Subgroup X)
    (hcls : ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ g : X, t = g * t₀ * g⁻¹)
    (hB : B₀ ≤ centralizer ({t₀} : Set X)) (hiso : Nonempty (↥B₀ ≃* alternatingGroup (Fin 5)))
    (hβB : β₀ ∈ B₀) (hβ : BetaFor X β₀) : BetaDataSqB X := by
  intro t ht2 hsq
  obtain ⟨g, rfl⟩ := hcls t ht2 hsq
  refine ⟨B₀.map (MulAut.conj g).toMonoidHom, g * β₀ * g⁻¹, ?_, ?_, ⟨β₀, hβB, rfl⟩, hβ.conj g⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hbt := mem_centralizer_singleton_iff.1 (hB hb)
    show g * b * g⁻¹ * (g * t₀ * g⁻¹) = g * t₀ * g⁻¹ * (g * b * g⁻¹)
    calc g * b * g⁻¹ * (g * t₀ * g⁻¹) = g * (b * t₀) * g⁻¹ := by group
      _ = g * (t₀ * b) * g⁻¹ := by rw [hbt]
      _ = g * t₀ * g⁻¹ * (g * b * g⁻¹) := by group
  · obtain ⟨e⟩ := hiso
    exact ⟨((B₀.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).symm.trans e⟩

theorem BetaDataSqB.of_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) (h : BetaDataSqB X) : BetaDataSqB Y := by
  intro t ht2 ⟨g, hg⟩
  have ht2' : orderOf (e.symm t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
  obtain ⟨B, β, hB, ⟨eB⟩, hβB, hβ⟩ := h (e.symm t) ht2' ⟨e.symm g, by rw [← map_mul, hg]⟩
  refine ⟨B.map e.toMonoidHom, e β, ?_, ⟨((B.equivMapOfInjective e.toMonoidHom
    e.injective)).symm.trans eB⟩, ⟨β, hβB, rfl⟩, hβ.map e⟩
  rintro _ ⟨b, hb, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have hbt := mem_centralizer_singleton_iff.1 (hB hb)
  have := congrArg e hbt
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  exact this

theorem lemma64_of_betaDataSqB (hSol : SolomonZ2A6)
    (hKG : ∀ β : G, orderOf β = 3 → CFSG.SectionRank.IsKGroupCat ↥(centralizer ({β} : Set G)))
    (h : InnerConfig G A z t T₀) {X : Type*} [Group X] [Finite X] (φ : X ≃* A)
    (hX : BetaDataSqB X) :
    ∃ (B : Subgroup G) (β : G), B ≤ A ∧ B ≤ centralizer ({t} : Set G) ∧
      Nonempty (↥B ≃* alternatingGroup (Fin 5)) ∧ β ∈ B ∧ orderOf β = 3 ∧
      ∃ hz : z ∈ centralizer ({β} : Set G),
        Lemma64Conclusion ↥(centralizer ({β} : Set G))
          (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G)))) := by
  let tA : ↥A := ⟨t, h.t_mem_A⟩
  have htA2 : orderOf tA = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h.t_order
  obtain ⟨g, hgA, hg⟩ := h.t_square
  have hsq : ∃ g' : X, g' * g' = φ.symm tA :=
    ⟨φ.symm ⟨g, hgA⟩, by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hg⟩
  obtain ⟨B, β, hB, ⟨eB⟩, hβB, hβ⟩ := hX (φ.symm tA) (by rw [MulEquiv.orderOf_eq]; exact htA2) hsq
  obtain ⟨hβ3, hD, hO⟩ := hβ.transport φ
  let ι : X →* G := A.subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := A.subtype_injective.comp φ.injective
  have hβA : ((φ β : A) : G) ∈ A := (φ β).2
  have hz : z ∈ centralizer ({((φ β : A) : G)} : Set G) :=
    mem_centralizer_singleton_iff.2 (h.z_comm_of_mem_A hβA).symm
  refine ⟨B.map ι, ((φ β : A) : G), ?_, ?_, ⟨((B.equivMapOfInjective ι hι)).symm.trans eB⟩,
    ⟨β, hβB, rfl⟩, hβ3, hz, lemma64_of_innerConfig hSol h rfl (hKG _ hβ3) hD hO rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact (φ b).2
  · rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hbt := mem_centralizer_singleton_iff.1 (hB hb)
    have := congrArg (fun y : X => ((φ y : A) : G)) hbt
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at this
    exact this

end CFSG.EvenSporadicStandard.Fin76b
