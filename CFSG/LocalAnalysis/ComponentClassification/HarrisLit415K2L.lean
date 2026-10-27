module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415K2U
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415H
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415KB0

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem isSolvable_of_isPGroup_quot {B : Type*} [Group B] [Finite B]
    (hB : IsPGroup 2 (B ⧸ pPrimeCore 2 B)) : Group.IsSolvable B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pPrimeCore 2 B).Normal := pPrimeCore_normal
  have hodd : Odd (Nat.card (pPrimeCore 2 B)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := B))
  have : Group.IsSolvable (pPrimeCore 2 B) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsNilpotent (B ⧸ pPrimeCore 2 B) := hB.isNilpotent
  exact Group.isSolvable_of_subgroup_quotient (pPrimeCore 2 B)

theorem pComponent_centralizer_eq_of {G : Type} [Group G] [Finite G] (hO : pPrimeCore 2 G = ⊥)
    (hSchG : LBalance.SchreierSections G) {Kb₁ Kb₂ : Subgroup G} {s : G}
    (hprod : IsProd (layer G) Kb₁ Kb₂ s) {c : G} (hcK₁ : c ∈ Kb₁) (hco : orderOf c = 2)
    (hsolv : Group.IsSolvable ↥(Kb₁ ⊓ centralizer {c}))
    (J : Subgroup ↥(centralizer ({c} : Set G))) (hJ : IsPComponent 2 J) :
    J = Kb₂.subgroupOf (centralizer {c}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : ∃ n : ℕ, c ^ 2 ^ n = 1 := by
    refine ⟨1, ?_⟩
    have h1 := pow_orderOf_eq_one c
    rw [hco] at h1
    rwa [pow_one]
  have hbal := LBalance.pLayer_centralizer_element_le hSchG hc2
  rw [ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot hO] at hbal
  have hJE : J.map (centralizer ({c} : Set G)).subtype ≤ layer G :=
    (map_mono (le_sSup (s := {L : Subgroup ↥(centralizer ({c} : Set G)) | IsPComponent 2 L}) hJ :
      J ≤ pLayer ↥(centralizer ({c} : Set G)) 2)).trans hbal
  have hJH : J.map (centralizer ({c} : Set G)).subtype ≤ layer G ⊓ centralizer {c} :=
    le_inf hJE (map_subtype_le J)
  have hJ' : IsPComponent 2 ((J.map (centralizer ({c} : Set G)).subtype).subgroupOf
      (layer G ⊓ centralizer {c})) := by
    refine UnbalancedCorr.isPComponent_subgroupOf_of_le hJH inf_le_right ?_
    rwa [subgroupOf_map_subtype_eq J]
  have hprod' := hprod.symm
  have hcomm : ∀ a ∈ Kb₁, ∀ b ∈ Kb₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hprod.le_centralizer ha) b hb).symm
  have hK₂E : Kb₂ ≤ layer G := hprod.sup_eq ▸ le_sup_right
  have hK₁E : Kb₁ ≤ layer G := hprod.sup_eq ▸ le_sup_left
  have hK₂C : Kb₂ ≤ centralizer {c} := fun b hb =>
    mem_centralizer_singleton_iff.mpr (hcomm c hcK₁ b hb).symm
  have hK₂H : Kb₂ ≤ layer G ⊓ centralizer {c} := le_inf hK₂E hK₂C
  have hEN : layer G ≤ normalizer (Kb₂ : Set G) := by
    rw [← hprod.sup_eq]
    exact sup_le (hprod.le_centralizer.trans (centralizer_le_normalizer _)) le_normalizer
  have hNn : (Kb₂.subgroupOf (layer G ⊓ centralizer {c})).Normal := by
    refine ⟨fun x hx h => ?_⟩
    exact (mem_normalizer_iff.mp (hEN (mem_inf.mp h.2).1) x).mp hx
  have : IsSimpleGroup ↥Kb₂ := hprod'.simple
  have hNq : CFSG.IsQuasisimple ↥(Kb₂.subgroupOf (layer G ⊓ centralizer {c})) :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hK₂H).symm
      (LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hprod'.nonabelian)
  have hN'H : Kb₁ ⊓ centralizer {c} ≤ layer G ⊓ centralizer {c} :=
    le_inf (inf_le_left.trans hK₁E) inf_le_right
  let ψ : ↥(Kb₁ ⊓ centralizer {c}) →* ↥(layer G ⊓ centralizer {c}) ⧸
      Kb₂.subgroupOf (layer G ⊓ centralizer {c}) := (QuotientGroup.mk' _).comp (inclusion hN'H)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxE : (x : G) ∈ Kb₁ ⊔ Kb₂ := by
      rw [hprod.sup_eq]
      exact (mem_inf.mp x.2).1
    obtain ⟨a, ha, b, hb, hab⟩ := L415.mem_sup_of_commute hcomm hxE
    have haC : a ∈ centralizer ({c} : Set G) := by
      have h1 : a = (x : G) * b⁻¹ := by rw [hab]; group
      rw [h1]
      exact mul_mem (mem_inf.mp x.2).2 (inv_mem (hK₂C hb))
    refine ⟨⟨a, mem_inf.mpr ⟨ha, haC⟩⟩, ?_⟩
    change (QuotientGroup.mk (inclusion hN'H ⟨a, _⟩) :
      ↥(layer G ⊓ centralizer {c}) ⧸ Kb₂.subgroupOf (layer G ⊓ centralizer {c})) =
        QuotientGroup.mk x
    rw [QuotientGroup.eq, mem_subgroupOf]
    have h2 : ((((inclusion hN'H) ⟨a, mem_inf.mpr ⟨ha, haC⟩⟩)⁻¹ * x :
        ↥(layer G ⊓ centralizer {c})) : G) = a⁻¹ * (x : G) := rfl
    rw [h2, hab, inv_mul_cancel_left]
    exact hb
  have : Group.IsSolvable (↥(layer G ⊓ centralizer {c}) ⧸
      Kb₂.subgroupOf (layer G ⊓ centralizer {c})) := Group.isSolvable_of_surjective hψ
  have h3 := L415.pComponent_eq_of_normal_quasisimple 2 _ hNq hJ'
  have h4 : J.map (centralizer ({c} : Set G)).subtype = Kb₂ := by
    have h5 := congrArg (fun K => K.map (layer G ⊓ centralizer {c}).subtype) h3
    simp only [subgroupOf_map_subtype, inf_eq_left.mpr hJH, inf_eq_left.mpr hK₂H] at h5
    exact h5
  rw [← h4, subgroupOf_map_subtype_eq J]

end L415

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem pComponent_centralizer_eq [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hI : AutPSL2InvolutionCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (J : Subgroup ↥(centralizer {(QuotientGroup.mk ⟨z₁, hc.isSylowOf_W.le hc.z₁_mem⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}))
    (hJ : IsPComponent 2 J) :
    J = Kb₂.subgroupOf (centralizer {(QuotientGroup.mk ⟨z₁, hc.isSylowOf_W.le hc.z₁_mem⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have hne := hs.setup.centralizer_beta_ne_top hnab i j
  have hKM := UnbalancedCorr.isKGroupCat_of_ne_top hK hne
  have hKMbar : SectionRank.IsKGroupCat (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    GSThmB.OddQuot.isKGroupCat_of_surjective hKM _ (QuotientGroup.mk'_surjective _)
  have hSchM := GSThmB.schreierSections_of_isKGroupCat hSch hKMbar
  obtain ⟨e₁⟩ := hc.equiv₁
  have hlie := GSThmB.OddQuot.lieModel_of_equiv e₁.symm (hs.lieModel_KBar h412)
  have hQC : centralizer ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≤
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [h412.pCore_eq.1, h412.pCore_eq.2]
  have hodd2 := h412.oddGenerated_le
  have hCb := hc.prod.isPGroup_centralizer hE hI hs.prime_p hs.p_ne_two hlie pCore_isPGroup hQC
    (fun g hg x hx => ((mem_centralizer_iff.mp
      (hodd2 (subset_closure (show g ∈ {x : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) |
        Odd (orderOf x)} from hg)))) x hx).symm)
    (hc.mk_z₁ _) hc.orderOf_mk_z₁
  have hN'le : Kb₁ ⊓ centralizer {(QuotientGroup.mk ⟨z₁, hc.isSylowOf_W.le hc.z₁_mem⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} ≤
      centralizer {(QuotientGroup.mk ⟨z₁, hc.isSylowOf_W.le hc.z₁_mem⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} ⊓ centralizer (Kb₂ : Set _) :=
    le_inf inf_le_right (inf_le_left.trans hc.prod.le_centralizer)
  have hN'2 := L415.isPGroup_quot_of_injective (inclusion hN'le) (inclusion_injective hN'le) hCb
  exact L415.pComponent_centralizer_eq_of (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hSchM hc.prod
    (hc.mk_z₁ _) hc.orderOf_mk_z₁ (L415.isSolvable_of_isPGroup_quot hN'2) J hJ

theorem layerIn_eq_K₂ [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hI : AutPSL2InvolutionCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    {K₂ : Subgroup X}
    (hK₂ : IsTwoComponentIn K₂
      (centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) :
    GSThmB.layerIn (centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) =
      K₂ := by
  have hz₁o : orderOf z₁ = 2 := by
    refine orderOf_eq_prime hc.sq_z₁ ?_
    intro h1
    exact hc.z₁_ne (by rw [h1]; group)
  have hY := hc.pComponent_centralizer_eq hnab hK hSch hI h412
  refine L415.layerIn_eq_of_unique hK₂ fun J' hJ' => ?_
  rw [inf_comm] at hJ' hK₂
  exact L415.eq_of_isTwoComponentIn_of_unique (hc.isSylowOf_W.le hc.z₁_mem) hz₁o hY hJ' hK₂

end Config415

end CFSG.ComponentClassification.HarrisLit
