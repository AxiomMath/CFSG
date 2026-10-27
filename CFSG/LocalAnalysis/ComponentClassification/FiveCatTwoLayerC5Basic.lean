module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

@[expose] def LitLayer {G : Type} [Group G] (L : Subgroup G) : Prop :=
  IsComponent L ∧ Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 5)) ∧
    ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z * z = 1 → z = 1

@[expose] def TwoLayers (G : Type) [Group G] : Prop :=
  ∃ L₁ L₂ : Subgroup G, LitLayer L₁ ∧ LitLayer L₂ ∧ L₁ ≠ L₂ ∧
    ∀ L' : Subgroup G, IsComponent L' → L' = L₁ ∨ L' = L₂

theorem LitLayer.map {G H : Type} [Group G] [Group H] (e : G ≃* H) {L : Subgroup G}
    (h : LitLayer L) : LitLayer (L.map e.toMonoidHom) := by
  obtain ⟨hL, ⟨eA⟩, hz⟩ := h
  refine ⟨LocalCores.isComponent_map_mulEquiv e hL, ?_, ?_⟩
  · exact ⟨(QuotientGroup.congr _ _ (L.equivMapOfInjective e.toMonoidHom e.injective)
      (Subgroup.map_center_eq _)).symm.trans eA⟩
  · intro z hz' hc hzz
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.1 hz'
    have h1 : z₀ = 1 := hz z₀ hz₀
      (fun y hy => e.injective (by
        simpa using hc (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy)))
      (e.injective (by simpa using hzz))
    rw [h1]
    exact map_one e

private theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem LitLayer.card_eq {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : LitLayer L) :
    Nat.card L = 60 * Nat.card (center L) ∧ Odd (Nat.card (center L)) := by
  obtain ⟨-, ⟨eA⟩, hz⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), Nat.card_congr eA.toEquiv,
      card_alt_five]
  · by_contra hodd
    have heven : 2 ∣ Nat.card (center L) := by
      rcases Nat.even_or_odd (Nat.card (center L)) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hodd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center L) 2 heven
    have hx2 : x * x = 1 := by rw [← sq]; exact hx ▸ pow_orderOf_eq_one x
    have hxc : (x : L) ∈ center L := x.2
    have h1 := hz (x : L) (x : L).2
      (fun y hy => by
        have := mem_center_iff.mp hxc ⟨y, hy⟩
        exact congrArg Subtype.val this.symm)
      (by simpa using congrArg (fun t : center L => ((t : L) : G)) hx2)
    have hx1 : x = 1 := Subtype.ext (Subtype.ext h1)
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)

theorem card_SL_two {K : Type} [Field K] [Finite K] :
    Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
  simp

@[expose] def NoLitLayer (G : Type) [Group G] : Prop := ∀ L : Subgroup G, ¬ LitLayer L

@[expose] def LitUnique (G : Type) [Group G] : Prop :=
  ∀ L₁ L₂ : Subgroup G, LitLayer L₁ → LitLayer L₂ → L₁ = L₂

theorem LitUnique.not_twoLayers {G : Type} [Group G] (h : LitUnique G) : ¬ TwoLayers G := by
  rintro ⟨L₁, L₂, h₁, h₂, hne, -⟩
  exact hne (h L₁ L₂ h₁ h₂)

theorem LitUnique.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : LitUnique H) :
    LitUnique G := by
  intro L₁ L₂ h₁ h₂
  have := h _ _ (h₁.map e) (h₂.map e)
  have h3 := congrArg (Subgroup.map e.symm.toMonoidHom) this
  rwa [Subgroup.map_map, Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom =
    MonoidHom.id G from by ext; simp, Subgroup.map_id, Subgroup.map_id] at h3

theorem NoLitLayer.litUnique {G : Type} [Group G] (h : NoLitLayer G) : LitUnique G :=
  fun L₁ _ h₁ _ => (h L₁ h₁).elim

theorem NoLitLayer.not_twoLayers {G : Type} [Group G] (h : NoLitLayer G) : ¬ TwoLayers G := by
  rintro ⟨L₁, -, h₁, -⟩
  exact h L₁ h₁

private theorem eq_one_of_mem_center_of_zStar {P : Type} [Group P] [Finite P]
    (hZ : Open.fusionZStar P = pPrimeCore 2 P) {w : P} (hw : w ∈ center P) (hww : w * w = 1) :
    w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwZ : w ∈ Open.fusionZStar P := by
    rw [GrSLit.GrS4.fusionZStar_eq_comap_pPrimeCore, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw y]
  rw [hZ] at hwZ
  have hcop := LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore (p := 2) hwZ
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hww)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm h2)

theorem properFixedComponent_of_isComponent {S : Type} [Group S] [Finite S] {σ : MulAut S}
    (hσ : ∀ y, σ (σ y) = y) (hσ1 : σ ≠ 1) {L : Subgroup (fixedSubgroup σ)} (hL : IsComponent L) :
    ProperFixedComponent σ (L.map (fixedSubgroup σ).subtype) := by
  have hLL : (L.map (fixedSubgroup σ).subtype).subgroupOf (fixedSubgroup σ) = L :=
    comap_map_eq_self_of_injective (subtype_injective _) L
  refine ⟨hσ, map_subtype_le L, ?_, fun htop => hσ1 ?_⟩
  · rw [hLL]
    exact isPComponent_two_of_isComponent hL
  · have hF : fixedSubgroup σ = ⊤ := top_le_iff.mp (htop ▸ map_subtype_le L)
    ext x
    have hx : x ∈ fixedSubgroup σ := hF ▸ mem_top x
    exact hx

theorem litLayer_of_properFixed {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hq : IsQuasisimple (P.subgroupOf (fixedSubgroup σ)))
    (hZ : Open.fusionZStar ↥P = pPrimeCore 2 ↥P)
    (eP : Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5))) :
    LitLayer (P.subgroupOf (fixedSubgroup σ)) := by
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  refine ⟨hcomp, ⟨eZ.symm.trans eP.some⟩, ?_⟩
  intro z hzL hzc hzz
  have hzP : (z : S) ∈ P := mem_subgroupOf.mp hzL
  have hwc : (⟨(z : S), hzP⟩ : ↥P) ∈ center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := hzc ⟨(y : S), h.2.1 y.2⟩ (mem_subgroupOf.mpr y.2)
    exact Subtype.ext (congrArg Subtype.val h1).symm
  have hzz' : (z : S) * (z : S) = 1 := congrArg Subtype.val hzz
  have hww : (⟨(z : S), hzP⟩ : ↥P) * ⟨(z : S), hzP⟩ = 1 := Subtype.ext hzz'
  have h1 := eq_one_of_mem_center_of_zStar hZ hwc hww
  have h2 : (z : S) = 1 := congrArg Subtype.val h1
  exact Subtype.ext h2

theorem twoLayers_of_clause {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hq : ∀ α : MulAut S, α * α = 1 → α ≠ 1 →
      ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L)
    {σ : MulAut S} {P₁ P₂ : Subgroup S} (h₁ : ProperFixedComponent σ P₁)
    (h₂ : ProperFixedComponent σ P₂) (hne : P₁ ≠ P₂)
    (hZ₁ : Open.fusionZStar ↥P₁ = pPrimeCore 2 ↥P₁)
    (hZ₂ : Open.fusionZStar ↥P₂ = pPrimeCore 2 ↥P₂)
    (e₁ : Nonempty (↥P₁ ⧸ Open.fusionZStar ↥P₁ ≃* alternatingGroup (Fin 5)))
    (e₂ : Nonempty (↥P₂ ⧸ Open.fusionZStar ↥P₂ ≃* alternatingGroup (Fin 5)))
    (huniq : ∀ P' : Subgroup S, ProperFixedComponent σ P' → P' = P₁ ∨ P' = P₂) :
    TwoLayers (fixedSubgroup σ) := by
  have hσ1 : σ ≠ 1 := h₁.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h₁.1 y
  have hq' := hq σ hσσ hσ1
  refine ⟨P₁.subgroupOf (fixedSubgroup σ), P₂.subgroupOf (fixedSubgroup σ),
    litLayer_of_properFixed h₁ (hq' _ h₁.2.2.1) hZ₁ e₁,
    litLayer_of_properFixed h₂ (hq' _ h₂.2.2.1) hZ₂ e₂, ?_, ?_⟩
  · intro heq
    apply hne
    have := (Subgroup.subgroupOf_inj).1 heq
    rwa [inf_eq_left.2 h₁.2.1, inf_eq_left.2 h₂.2.1] at this
  · intro L' hL'
    have hLL : (L'.map (fixedSubgroup σ).subtype).subgroupOf (fixedSubgroup σ) = L' :=
      comap_map_eq_self_of_injective (subtype_injective _) L'
    rcases huniq _ (properFixedComponent_of_isComponent h₁.1 hσ1 hL') with h | h
    · left
      rw [← hLL, h]
    · right
      rw [← hLL, h]

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5
