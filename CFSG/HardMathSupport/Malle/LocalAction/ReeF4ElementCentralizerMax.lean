module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizer
public import CFSG.HardMathSupport.Malle.LocalAction.AbelianTwentyFiveGL4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local

public noncomputable section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4

section Max

variable {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem centralizer_normalizer_maximal (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    (P : Sylow 5 (ReeTag.F4.reeGamma K 2)) (E : Subgroup (ReeTag.F4.reeGamma K 2))
    (hEP : E ≤ (P : Subgroup (ReeTag.F4.reeGamma K 2))) (hE : CFSG.Open.IsElemAbelian 5 E)
    (x : ReeTag.F4.reeGamma K 2) (hxE : x ∈ E) (hx1 : x ≠ 1)
    {H : Subgroup (ReeTag.F4.reeGamma K 2)}
    (hH₁ : Subgroup.normalizer ((P : Subgroup (ReeTag.F4.reeGamma K 2)) : Set _) ⊓
      Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)) ≤ H)
    (hH₂ : H ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2))) :
    H = Subgroup.normalizer ((P : Subgroup (ReeTag.F4.reeGamma K 2)) : Set _) ⊓
        Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)) ∨
      H = Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨A, S, hAP, hAc, hAcyc, hcomm, hinf, hsup, hSc, ⟨eSz⟩, hPSc, hPsup, hxA⟩ :=
    exists_centralizer_decomp hK P E hEP hE x hxE hx1
  set N := Subgroup.normalizer ((P : Subgroup (ReeTag.F4.reeGamma K 2)) : Set (ReeTag.F4.reeGamma K 2)) with hN
  set C := Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)) with hC
  have hK' : Nat.card K = 32 := by rw [hK]; norm_num
  obtain ⟨eP⟩ := sylowShape_five hK (P : Subgroup (ReeTag.F4.reeGamma K 2)) P.isPGroup'
    P.not_dvd_index
  have hPcomm : ∀ p ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)),
      ∀ q ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)), p * q = q * p := by
    intro p hp q hq
    have := mul_comm (eP ⟨p, hp⟩) (eP ⟨q, hq⟩)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (eP.injective this)
  let T' : Subgroup ↥S := ((P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S).subgroupOf S
  have hT'card : Nat.card T' = 25 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S ≤ S)).toEquiv]
    exact hPSc
  have hT'comm : ∀ a ∈ T', ∀ b ∈ T', a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hPcomm _ (Subgroup.mem_subgroupOf.1 ha).1 _ (Subgroup.mem_subgroupOf.1 hb).1)
  let f : ↥S →* GL (Fin 4) K := (suzukiGroup 2 K).subtype.comp eSz.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp eSz.injective
  have hcyc : IsCyclic T' := by
    have hc : IsCyclic ↥(T'.map f) := by
      refine isCyclic_of_abelian_card_twentyfive hK' (T'.map f) ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hT'comm a ha b hb]
      · rw [Subgroup.card_map_of_injective hf, hT'card]
    have e := T'.equivMapOfInjective f hf
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hfac : 5 ^ (Nat.card ↥S).factorization 5 = 25 := by
    rw [hSc, CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
    norm_num
  let T : Sylow 5 ↥S := Sylow.ofCard T' (by rw [hT'card, hfac])
  have hTcoe : (T : Subgroup ↥S) = T' := Sylow.coe_ofCard _ _
  let σ : K ≃+* CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    CFSG.AGLEmbedding.KFactProofs.Sz32.F32.ringEquiv K hK
  let ε : ↥S ≃* suzukiGroup 2 CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    eSz.trans (CFSG.AGLEmbedding.KFactProofs.Sz32Local.modelEquiv σ)
  have hdata : CFSG.AGLEmbedding.KFactProofs.Sz32Local.Sz32Data ↥S T' :=
    ⟨hSc, hT'card, hcyc, fun t ht ht1 g hg => by
      have := CFSG.AGLEmbedding.KFactProofs.Sz32Local.centralizer_le_of_equiv ε T t
        (by rw [hTcoe]; exact ht) ht1 g hg
      rwa [hTcoe] at this⟩
  have hSC : S ≤ C := by rw [← hsup]; exact le_sup_right
  have hAC : A ≤ C := by rw [← hsup]; exact le_sup_left
  have hnorm : ∀ s : ↥S, s ∈ Subgroup.normalizer (T' : Set ↥S) →
      ∀ p ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)),
        (s : ReeTag.F4.reeGamma K 2) * p * (s : ReeTag.F4.reeGamma K 2)⁻¹ ∈
          (P : Subgroup (ReeTag.F4.reeGamma K 2)) := by
    intro s hs p hp
    have hcAP : ∀ a ∈ A, ∀ b ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S, a * b = b * a :=
      fun a ha b hb => hcomm a ha b hb.2
    have hp' : p ∈ A ⊔ ((P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S) := hPsup ▸ hp
    obtain ⟨a, ha, t, ht, rfl⟩ := mem_sup_of_commute hcAP hp'
    have hts : (⟨t, ht.2⟩ : ↥S) ∈ T' := Subgroup.mem_subgroupOf.2 ht
    have h1 := (Subgroup.mem_normalizer_iff.1 hs _).1 hts
    have h2 := (Subgroup.mem_subgroupOf.1 h1).1
    have : (s : ReeTag.F4.reeGamma K 2) * (a * t) * (s : ReeTag.F4.reeGamma K 2)⁻¹ =
        a * ((s : ReeTag.F4.reeGamma K 2) * t * (s : ReeTag.F4.reeGamma K 2)⁻¹) := by
      have := hcomm a ha s s.2
      calc (s : ReeTag.F4.reeGamma K 2) * (a * t) * (s : ReeTag.F4.reeGamma K 2)⁻¹
          = (s * a) * t * (s : ReeTag.F4.reeGamma K 2)⁻¹ := by group
        _ = (a * s) * t * (s : ReeTag.F4.reeGamma K 2)⁻¹ := by rw [← this]
        _ = _ := by group
    rw [this]
    exact mul_mem (hAP ha) h2
  have hnormN : ∀ s : ↥S, s ∈ Subgroup.normalizer (T' : Set ↥S) →
      (s : ReeTag.F4.reeGamma K 2) ∈ N := by
    intro s hs
    rw [hN, Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hnorm s hs p hp, fun hp => ?_⟩
    have h := hnorm s⁻¹ (inv_mem hs) _ hp
    simp only [Subgroup.coe_inv, inv_inv] at h
    have e : ((s : ReeTag.F4.reeGamma K 2))⁻¹ * ((s : ReeTag.F4.reeGamma K 2) * p *
        ((s : ReeTag.F4.reeGamma K 2))⁻¹) * (s : ReeTag.F4.reeGamma K 2) = p := by group
    rw [e] at h
    exact h
  have hAN : A ≤ N := hAP.trans Subgroup.le_normalizer
  have hAH : A ≤ H := fun a ha => hH₁ ⟨hAN ha, hAC ha⟩
  have hcA : ∀ a ∈ A, ∀ s ∈ S, a * s = s * a := hcomm
  let Y : Subgroup ↥S := H.comap S.subtype
  have hNY : Subgroup.normalizer (T' : Set ↥S) ≤ Y := fun s hs =>
    hH₁ ⟨hnormN s hs, hSC s.2⟩
  rcases hdata.maximal hNY with hY | hY
  ·
    left
    apply le_antisymm
    · intro h hh
      have hhC : h ∈ A ⊔ S := hsup ▸ hH₂ hh
      obtain ⟨a, ha, s, hs, rfl⟩ := mem_sup_of_commute hcA hhC
      have hsH : s ∈ H := by
        have : s = a⁻¹ * (a * s) := by group
        rw [this]
        exact mul_mem (inv_mem (hAH ha)) hh
      have hsY : (⟨s, hs⟩ : ↥S) ∈ Y := hsH
      rw [hY] at hsY
      exact ⟨mul_mem (hAN ha) (hnormN _ hsY), hH₂ hh⟩
    · exact hH₁
  · right
    apply le_antisymm hH₂
    rw [← hsup]
    refine sup_le hAH ?_
    intro s hs
    have : (⟨s, hs⟩ : ↥S) ∈ Y := by rw [hY]; trivial
    exact this

end Max

end CFSG.HardMathSupport.Malle.LocalAction
