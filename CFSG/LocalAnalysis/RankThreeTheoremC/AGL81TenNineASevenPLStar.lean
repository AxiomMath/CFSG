module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.KerThetaTwoCore
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Reduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

noncomputable def barMEquivOfMulEquiv (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (e : ↥(barM M L) ≃* alternatingGroup (Fin 7)) :
    ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin 7) :=
  (Proving.barMEquiv hL.le le_sup_left
    (Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL)).symm.trans e

theorem center_barM_sup_eq_bot (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (e : ↥(barM M L) ≃* alternatingGroup (Fin 7)) :
    Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ := by
  let e' := barMEquivOfMulEquiv hA hL hSL e
  have hZ7 : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e' z ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨w, rfl⟩ := e'.surjective y
    rw [← map_mul, ← map_mul, hz w]
  rw [hZ7, Subgroup.mem_bot] at hz'
  exact e'.injective (by rw [hz', map_one])

theorem nonempty_barM_sup_quot_center (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (e : ↥(barM M L) ≃* alternatingGroup (Fin 7)) :
    Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin 7)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_barM_sup_eq_bot hA hL hSL e)).trans
    (QuotientGroup.quotientBot.trans (barMEquivOfMulEquiv hA hL hSL e))⟩

theorem sup_inf_centralizer_blockV_le (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥) :
    (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ S :=
  (AlternatingGeometry.inf_centralizer_blockV_le_pCoreOf
    (Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL)
    (Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1
      hA.twoRadical.isPGroup hSL)
    hSL (Coordinator.not_le_centralizer_blockV hA hL hSL) hZ).trans
    (Coordinator.twoCore_sup_le hA hL hSL)

omit [Finite G] in
theorem autOn_le_autOn_of_act
    (hact : ∀ s ∈ S, ∃ l ∈ L, ∀ v ∈ blockV S L, s * v * s⁻¹ = l * v * l⁻¹) :
    autOn S (blockV S L) ≤ autOn L (blockV S L) := by
  intro x hx
  obtain ⟨g, hgS, rfl⟩ := Setup.mem_autOn_iff.mp hx
  obtain ⟨l, hlL, hact'⟩ := hact (g : G) hgS
  have hcen : l⁻¹ * (g : G) ∈ Subgroup.centralizer (blockV S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h := hact' v hv
    have hrel : (l⁻¹ * (g : G)) * v = v * (l⁻¹ * (g : G)) := by
      calc (l⁻¹ * (g : G)) * v = l⁻¹ * ((g : G) * v * (g : G)⁻¹) * (g : G) := by group
        _ = l⁻¹ * (l * v * l⁻¹) * (g : G) := by rw [h]
        _ = v * (l⁻¹ * (g : G)) := by group
    exact hrel.symm
  have hlV : l ∈ Subgroup.normalizer (blockV S L : Set G) := by
    have h1 : l⁻¹ * (g : G) ∈ Subgroup.normalizer (blockV S L : Set G) :=
      Subgroup.centralizer_le_normalizer _ hcen
    have h3 : l = (g : G) * (l⁻¹ * (g : G))⁻¹ := by group
    rw [h3]
    exact Subgroup.mul_mem (Subgroup.normalizer _) g.2 ((Subgroup.normalizer _).inv_mem h1)
  refine Setup.mem_autOn_iff.mpr ⟨⟨l, hlV⟩, hlL, ?_⟩
  ext v
  rw [Setup.coe_conjAct_apply, Setup.coe_conjAct_apply]
  exact (hact' v v.2).symm

theorem conj_mem_of_conjAct_mem_normalizer_autOn (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥) {x : G} (hxL : x ∈ L)
    (hxV : x ∈ Subgroup.normalizer (blockV S L : Set G))
    (hn : conjAct (blockV S L) ⟨x, hxV⟩ ∈
      Subgroup.normalizer (autOn S (blockV S L) : Set (MulAut ↥(blockV S L)))) :
    ∀ t ∈ S, x * t * x⁻¹ ∈ S := by
  have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) :=
    le_sup_left.trans (Coordinator.sup_le_normalizer_blockV S L)
  have hKN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    Coordinator.sup_le_normalizer_blockV S L
  have hn' : conjAct (blockV S L) ⟨x, hLV hxL⟩ ∈
      Subgroup.normalizer (autOn S (blockV S L) : Set (MulAut ↥(blockV S L))) := by
    have h : (⟨x, hLV hxL⟩ : Subgroup.normalizer (blockV S L : Set G)) = ⟨x, hxV⟩ :=
      Subtype.ext rfl
    rw [h]
    exact hn
  intro t ht
  have hxst : x * t * x⁻¹ ∈ L ⊔ S :=
    (L ⊔ S).mul_mem ((L ⊔ S).mul_mem (Subgroup.mem_sup_left hxL) (Subgroup.mem_sup_right ht))
      ((L ⊔ S).inv_mem (Subgroup.mem_sup_left hxL))
  have hmem : conjAct (blockV S L) ⟨x * t * x⁻¹, hKN hxst⟩ ∈
      autOn S (blockV S L) := by
    have hcast : (⟨x * t * x⁻¹, hKN hxst⟩ :
        Subgroup.normalizer (blockV S L : Set G)) =
        (⟨x, hLV hxL⟩ : Subgroup.normalizer (blockV S L : Set G)) *
          ⟨t, hKN (Subgroup.mem_sup_right ht)⟩ *
            ((⟨x, hLV hxL⟩ : Subgroup.normalizer (blockV S L : Set G)))⁻¹ :=
      Subtype.ext rfl
    rw [hcast, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hn' _).mp
      (AutOn.conjAct_mem_autOn ⟨t, hKN (Subgroup.mem_sup_right ht)⟩ ht)
  exact AutOn.mem_of_conjAct_mem_autOn hKN le_sup_right
    (sup_inf_centralizer_blockV_le hA hL hSL hZ) hxst hmem

theorem mem_normalizer_of_conjAct_mem_normalizer (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥)
    {l : G} (hl : l ∈ L) (hlV : l ∈ Subgroup.normalizer (blockV S L : Set G))
    (hn : conjAct (blockV S L) ⟨l, hlV⟩ ∈
      Subgroup.normalizer (autOn S (blockV S L) : Set (MulAut ↥(blockV S L)))) :
    l ∈ Subgroup.normalizer (S : Set G) := by
  have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) :=
    le_sup_left.trans (Coordinator.sup_le_normalizer_blockV S L)
  have hfwd : ∀ t ∈ S, l * t * l⁻¹ ∈ S :=
    conj_mem_of_conjAct_mem_normalizer_autOn hA hL hSL hZ hl hlV hn
  have hbwd : ∀ t ∈ S, l⁻¹ * t * l ∈ S := by
    have hninv : conjAct (blockV S L) ⟨l⁻¹, (Subgroup.normalizer (blockV S L : Set G)).inv_mem
        (hLV hl)⟩ ∈
        Subgroup.normalizer (autOn S (blockV S L) : Set (MulAut ↥(blockV S L))) := by
      have hcast : (⟨l⁻¹, (Subgroup.normalizer (blockV S L : Set G)).inv_mem (hLV hl)⟩ :
          Subgroup.normalizer (blockV S L : Set G)) =
          (⟨l, hLV hl⟩ : Subgroup.normalizer (blockV S L : Set G))⁻¹ := Subtype.ext rfl
      rw [hcast, map_inv]
      exact (Subgroup.normalizer _).inv_mem (by
        have h : (⟨l, hLV hl⟩ : Subgroup.normalizer (blockV S L : Set G)) = ⟨l, hlV⟩ :=
          Subtype.ext rfl
        rw [h]
        exact hn)
    have h := conj_mem_of_conjAct_mem_normalizer_autOn hA hL hSL hZ (L.inv_mem hl) _ hninv
    simpa only [inv_inv] using h
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hfwd a
  · intro ha
    have h1 := hbwd (l * a * l⁻¹) ha
    rwa [show l⁻¹ * (l * a * l⁻¹) * l = a from by group] at h1

theorem isSylowTwoOf_inf_of_relIndex (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥)
    (hSs : autOn S (blockV S L) ≤ autOn L (blockV S L))
    (hodd : ¬ 2 ∣ (autOn S (blockV S L)).relIndex (autOn L (blockV S L))) :
    IsSylowTwoOf (S ⊓ L) L := by
  have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) :=
    le_sup_left.trans (Coordinator.sup_le_normalizer_blockV S L)
  have hKN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    Coordinator.sup_le_normalizer_blockV S L
  have hpg : IsPGroup 2 ↥(S ⊓ L) := by
    intro x
    obtain ⟨e, he⟩ := hA.twoRadical.isPGroup ⟨(x : G), x.2.1⟩
    exact ⟨e, Subtype.ext (by simpa using congrArg Subtype.val he)⟩
  let P : Subgroup ↥(autOn L (blockV S L)) :=
    (autOn S (blockV S L)).subgroupOf (autOn L (blockV S L))
  have hmem_iff : ∀ l : ↥L, ((InternalSec.autOnHom hLV l : ↥(autOn L (blockV S L))) :
      MulAut ↥(blockV S L)) ∈ autOn S (blockV S L) ↔ (l : G) ∈ S := by
    intro l
    have hval : ((InternalSec.autOnHom hLV l : ↥(autOn L (blockV S L))) :
        MulAut ↥(blockV S L)) = conjAct (blockV S L) ⟨(l : G), hLV l.2⟩ := rfl
    rw [hval]
    constructor
    · intro h
      refine AutOn.mem_of_conjAct_mem_autOn hKN le_sup_right
        (sup_inf_centralizer_blockV_le hA hL hSL hZ) (Subgroup.mem_sup_left l.2) ?_
      have hproof : (⟨(l : G), hLV l.2⟩ : Subgroup.normalizer (blockV S L : Set G)) =
          ⟨(l : G), hKN (Subgroup.mem_sup_left l.2)⟩ := Subtype.ext rfl
      rwa [hproof] at h
    · intro h
      exact AutOn.conjAct_mem_autOn ⟨(l : G), hLV l.2⟩ h
  have hcomap : ((S ⊓ L).subgroupOf L) = P.comap (InternalSec.autOnHom hLV) := by
    ext l
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      hmem_iff l]
    exact ⟨fun h => h.1, fun h => ⟨h, l.2⟩⟩
  have hindex : ((S ⊓ L).subgroupOf L).index =
      (autOn S (blockV S L)).relIndex (autOn L (blockV S L)) := by
    rw [hcomap, Subgroup.index_comap_of_surjective _ (InternalSec.autOnHom_surjective hLV)]
    rfl
  exact ⟨inf_le_right, hpg, by rw [hindex]; exact hodd⟩

theorem exists_barMEquiv_autOn (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥) :
    ∃ θ : ↥(barM M L) ≃* ↥(autOn L (blockV S L)),
      ∀ (l : G) (hl : l ∈ L) (hlV : l ∈ Subgroup.normalizer (blockV S L : Set G)),
        ((θ (Proving.barMHomSub hL.le ⟨l, hl⟩) : ↥(autOn L (blockV S L))) :
          MulAut ↥(blockV S L)) = conjAct (blockV S L) ⟨l, hlV⟩ := by
  have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) :=
    le_sup_left.trans (Coordinator.sup_le_normalizer_blockV S L)
  have hcore : L ⊓ pCoreOf 2 M = L ⊓ Subgroup.centralizer (blockV S L : Set G) := by
    have h2 : L ⊓ pCoreOf 2 M ≤ L ⊓ Subgroup.centralizer (blockV S L : Set G) := by
      rw [hL.toIsTwoPrimeComponent.inf_twoCore]
      exact le_inf (Subgroup.map_subtype_le (CFSG.pCore 2 L))
        (Coordinator.pCoreOf_le_centralizer_blockV hA hL)
    have h3 : L ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ L ⊓ pCoreOf 2 M := by
      have hle : L ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ L ⊓ pCoreOf 2 (L ⊔ S) :=
        le_inf inf_le_left ((le_inf (inf_le_left.trans le_sup_left) inf_le_right).trans
          (AlternatingGeometry.inf_centralizer_blockV_le_pCoreOf
            (Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL)
            (Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1
              hA.twoRadical.isPGroup hSL)
            hSL (Coordinator.not_le_centralizer_blockV hA hL hSL) hZ))
      rwa [← Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL] at hle
    exact le_antisymm h2 h3
  have hker : (Proving.barMHomSub hL.le).ker = (InternalSec.autOnHom hLV).ker := by
    rw [Proving.ker_barMHomSub, Proving.subgroupOf_eq_of_inf_eq hcore]
    ext l
    rw [Subgroup.mem_subgroupOf, InternalSec.mem_ker_autOnHom]
  set θ : ↥(barM M L) ≃* ↥(autOn L (blockV S L)) :=
    (QuotientGroup.quotientKerEquivOfSurjective _ (Proving.barMHomSub_surjective hL.le)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ (InternalSec.autOnHom_surjective hLV)))
    with hθ
  refine ⟨θ, ?_⟩
  intro l hl hlV
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _
      (Proving.barMHomSub_surjective hL.le)).symm
      (Proving.barMHomSub hL.le ⟨l, hl⟩) =
      (QuotientGroup.mk ⟨l, hl⟩ : ↥L ⧸ (Proving.barMHomSub hL.le).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 : θ (Proving.barMHomSub hL.le ⟨l, hl⟩) = InternalSec.autOnHom hLV ⟨l, hl⟩ := by
    rw [hθ, MulEquiv.trans_apply, MulEquiv.trans_apply, h1,
      QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  rw [h2]
  exact congrArg (conjAct (blockV S L)) (Subtype.ext rfl)

end CFSG.LocalAnalysis.RankThreeTheoremC
