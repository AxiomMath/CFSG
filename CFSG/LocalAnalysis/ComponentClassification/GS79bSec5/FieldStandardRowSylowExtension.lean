module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowSylowBounds
public import CFSG.GroupTheory.SubgroupTransport
import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Closure
import CFSG.CGT.Timmesfeld75.StronglyClosedSimple
public import CFSG.CGT.Timmesfeld75.GoldschmidtMilestone
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

open Matrix Subgroup
open scoped commutatorElement
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_proper_sylow_extension_of_standard_row
  {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F)
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
  let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
  let E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
  let J : Subgroup G := E ⊔ Subgroup.zpowers t
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let C : Subgroup G := Subgroup.centralizer (J : Set G)
  let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
  let ι : (Fin 2 → F) → G := fun v =>
    ρ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F (-(v 1)) 0 (v 0))
  let lev : Matrix.SpecialLinearGroup (Fin 2) F →* G :=
    ρ.comp (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F)
  let tor : Fˣ →* G :=
    ρ.comp (CFSG.LocalAnalysis.EvenBN.LinearThree.torSLZero F)
  CFSG.Open.IsElemAbelian 2 J ∧
  Nat.card J = 2 * (Nat.card F) ^ 2 ∧
  CFSG.ABGLocalTools.IsSylowOf 2 J C ∧
  J.subgroupOf C ≤ Subgroup.center C ∧
  N ≤ Subgroup.normalizer (E : Set G) ∧
  ∃ O : Subgroup G,
    O ≤ C ∧ Odd (Nat.card O) ∧
    (O.subgroupOf C).Characteristic ∧
    N ≤ Subgroup.normalizer (O : Set G) ∧
    O ≤ Subgroup.centralizer (A : Set G) ∧
    J ⊔ O = C ∧ J ⊓ O = ⊥ ∧
    ∃ Q : Subgroup G,
      Q ≤ X ∧ IsPGroup 2 Q ∧ J ≤ Q ∧
      CFSG.ABGLocalTools.IsSylowOf 2 Q X ∧
      (∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 R X → R = Q) ∧
      (Q.subgroupOf X).Characteristic ∧
      N ≤ Subgroup.normalizer (Q : Set G) ∧
      Q ⊔ O = X ∧ Q ⊓ O = ⊥ ∧
      Q ≤ Subgroup.centralizer (O : Set G) ∧
      Q ⊓ Subgroup.centralizer ({t} : Set G) = J ∧
      Nat.card Q = 2 * (Nat.card F) ^ 4 ∧
      (∃ κQ : Q →* E,
        (∀ x : Q, ((κQ x : E) : G) =
          t * ((x : G) * t * (x : G)⁻¹)) ∧
        κQ.ker = J.subgroupOf Q ∧ Function.Surjective κQ) ∧
      ∃ S : CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.XSetting G F,
        S.X = Q ∧ S.t = t ∧ S.ι = ι ∧ S.lev = lev ∧ S.tor = tor ∧
        ∃ W : Subgroup G,
          (
            W ≤ Q ∧ CFSG.Open.IsElemAbelian 2 W ∧
            Nat.card W = (Nat.card F) ^ 4 ∧
            E < W ∧ t ∉ W ∧
            Q = W ⊔ Subgroup.zpowers t ∧
            (∀ x ∈ Q, x ∈ W ∨ x * t ∈ W) ∧
            (W.subgroupOf Q).Characteristic ∧
            N ≤ Subgroup.normalizer (W : Set G) ∧
            W ⊓ Subgroup.centralizer ({t} : Set G) = E ∧
            ⁅W, Subgroup.zpowers t⁆ = E ∧
            W ≤ Subgroup.centralizer (O : Set G) ∧
            lev.range ≤ Subgroup.normalizer (W : Set G) ∧
            tor.range ≤ Subgroup.normalizer (W : Set G) ∧
            ⁅W, lev.range⁆ = W ∧
            ∀ W' : Subgroup G, W' ≤ Q →
              (∀ a ∈ W', ∀ b ∈ W', a * b = b * a) →
              Nat.card W' = (Nat.card F) ^ 4 → W' = W) ∧
          ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 2 P N →
            Q ≤ P ∧
            P ≤ Subgroup.normalizer (W : Set G) ∧
            t ∈ P ∧
            (∀ B : Subgroup G, B ≤ P → CFSG.Open.IsElemAbelian 2 B →
              W.relIndex B ≤ 4 * Nat.card F) ∧
            (∀ x ∈ P, x ∉ W → x * x = 1 →
              Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) ≤ (Nat.card F) ^ 2) ∧
            ¬ CFSG.ABGLocalTools.IsSylowOf 2 P
              (Subgroup.normalizer (W : Set G)) ∧
            ∃ T : Subgroup G, P < T ∧
              CFSG.ABGLocalTools.IsSylowOf 2 T
                (Subgroup.normalizer (W : Set G))
:= by
  classical
  dsimp only
  let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
  let E : Subgroup G := (unipOne F).map ρ
  let J : Subgroup G := E ⊔ Subgroup.zpowers t
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let C : Subgroup G := Subgroup.centralizer (J : Set G)
  let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
  let ι : (Fin 2 → F) → G := fun v => ρ (unipU F (-(v 1)) 0 (v 0))
  let lev : Matrix.SpecialLinearGroup (Fin 2) F →* G := ρ.comp (leviOne F)
  let tor : Fˣ →* G := ρ.comp (torSLZero F)
  obtain ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO, hOA, hJO,
    hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO, hQdisj, hQCO, hQCt,
    hQcard, κQpart, hSpart⟩ :=
    exists_sylow_bounds_of_standard_row hnonab hF A hA hZ e φ hφsurj hφproj hcyc t ht htC
  obtain ⟨κQ, hκQformula, hκQker, hκQsurj⟩ := κQpart
  obtain ⟨S, hSX, hSt, hSι, hSlev, hStor, hWpart⟩ := hSpart
  obtain ⟨W, hWclauses, hPbound⟩ := hWpart
  obtain ⟨hWQ, hWelem, hWcard, hEltW, htW, hQsup, hWcoset, hWchar, hNW, hWfixE,
    hcomm_t, hWCO, hlevN, htorN, hcomm_lev, hWuniq⟩ := hWclauses
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    simpa using hWelem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO, hOA, hJO,
    hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO, hQdisj, hQCO, hQCt,
    hQcard, ⟨κQ, hκQformula, hκQker, hκQsurj⟩, S, hSX, hSt, hSι, hSlev, hStor, W,
    ⟨hWQ, hWelem, hWcard, hEltW, htW, hQsup, hWcoset, hWchar, hNW, hWfixE, hcomm_t,
      hWCO, hlevN, htorN, hcomm_lev, hWuniq⟩, ?_⟩
  intro P hP
  obtain ⟨hQleP, hPM, htP, hBelem, hFix⟩ := hPbound P hP
  have hnotSyl : ¬ CFSG.ABGLocalTools.IsSylowOf 2 P
      (Subgroup.normalizer (W : Set G)) := by
    intro hPsyl
    obtain ⟨G₀, instGroupG₀, instFintypeG₀, ⟨eG⟩⟩ :=
      (Finite.exists_type_univ_nonempty_mulEquiv (G := G) :
        ∃ (G₀ : Type) (_ : Group G₀) (_ : Fintype G₀), Nonempty (G ≃* G₀))
    let ginst : Group G₀ := instGroupG₀
    let finst : Fintype G₀ := instFintypeG₀
    have hsimpleG₀ : IsSimpleGroup G₀ := eG.symm.isSimpleGroup
    let E₀ : Subgroup G₀ := W.map eG.toMonoidHom
    let S₀ : Subgroup G₀ := P.map eG.toMonoidHom
    have hmapConj : ∀ (A : Subgroup G) (g : G),
        (rightConjugate A g).map eG.toMonoidHom =
          rightConjugate (A.map eG.toMonoidHom) (eG g) := by
      intro A g
      simpa using
        (CFSG.StandardSubgroupAPI.rightConjugate_map_mulEquiv A eG (eG g)).symm
    have hE₀S₀ : E₀ ≤ S₀ := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map_of_mem eG.toMonoidHom (hWQ.trans hQleP hw)
    have hE₀el : ∀ e ∈ E₀, e * e = 1 := by
      intro e he
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp he
      rw [← map_mul]
      have hw2 : w * w = 1 := by
        have := hWelem.2 w hw
        simpa [pow_two] using this
      rw [hw2, map_one]
    have hE₀ab : IsMulCommutative E₀ := by
      have hWmc : IsMulCommutative W := hWelem.1
      exact Subgroup.map_isMulCommutative W eG.toMonoidHom
    have hE₀ne : E₀ ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card E₀ = Nat.card W :=
        Subgroup.card_map_of_injective eG.injective
      rw [hbot, hWcard] at hcard
      rw [Subgroup.card_bot] at hcard
      have hq2 : 2 ≤ Nat.card F := by omega
      have hgt : 1 < (Nat.card F) ^ 4 := by
        have h2 : (2 : ℕ) ^ 4 ≤ (Nat.card F) ^ 4 := Nat.pow_le_pow_left hq2 4
        exact lt_of_lt_of_le (by norm_num) h2
      omega
    have hS₀syl : CFSG.ABGLocalTools.IsSylowOf 2 S₀
        (Subgroup.normalizer (E₀ : Set G₀)) := by
      have h := (CFSG.GroupTheory.isSylowOf_map_mulEquiv (p := 2) eG
        (P := P) (K := Subgroup.normalizer (W : Set G))).mpr hPsyl
      rwa [Subgroup.map_equiv_normalizer_eq] at h
    have hH : ∀ U ≤ E₀, ∀ h : G₀, rightConjugate U h ≤ S₀ →
        ¬ rightConjugate U h ≤ E₀ →
        ∃ w ∈ rightConjugate U h,
          E₀.relIndex (rightConjugate U h) < Nat.card ↥⁅E₀, Subgroup.zpowers w⁆ := by
      intro U hUE h0 hUS hUnE
      let U' : Subgroup G := U.comap eG.toMonoidHom
      have hU'E : U'.map eG.toMonoidHom = U := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨eG.symm x, by simpa [U'] using hx, by simp⟩
      have hU'W : U' ≤ W := by
        intro x hx
        have hxU : eG x ∈ U := by simpa [U'] using hx
        have hxE : eG x ∈ E₀ := hUE hxU
        have hxW : eG.symm (eG x) ∈ W := by
          rw [← Subgroup.mem_map_equiv (f := eG) (K := W)]
          exact hxE
        simpa using hxW
      have hU'el : CFSG.Open.IsElemAbelian 2 U' := hWelem.mono hU'W
      let g' : G := eG.symm h0
      let B' : Subgroup G := rightConjugate U' g'
      have hB'map : B'.map eG.toMonoidHom = rightConjugate U h0 := by
        rw [show B' = rightConjugate U' g' from rfl, hmapConj, hU'E]
        congr 1
        exact eG.apply_symm_apply h0
      have hB'P : B' ≤ P := by
        apply (Subgroup.map_le_map_iff_of_injective (f := eG.toMonoidHom)
          eG.injective).mp
        rw [hB'map]
        exact hUS
      have hB'notW : ¬ B' ≤ W := by
        intro hle
        apply hUnE
        rw [← hB'map]
        exact Subgroup.map_mono hle
      have hB'elem : CFSG.Open.IsElemAbelian 2 B' := by
        simpa [B', rightConjugate] using
          hU'el.map (MulAut.conj g'⁻¹).toMonoidHom
      obtain ⟨x, hxB', hxW⟩ : ∃ x, x ∈ B' ∧ x ∉ W := by
        by_contra hcon
        push Not at hcon
        exact hB'notW (fun x hx => hcon x hx)
      have hxP : x ∈ P := hB'P hxB'
      have hx2 : x * x = 1 :=
        CFSG.Open.IsElemAbelian.mul_self_eq_one hB'elem hxB'
      have hfix := hFix x hxP hxW hx2
      have hrel := hBelem B' hB'P hB'elem
      have hltW : Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) *
          W.relIndex B' < Nat.card W := by
        have hprod : Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) *
            W.relIndex B' ≤ (Nat.card F) ^ 2 * (4 * Nat.card F) :=
          Nat.mul_le_mul hfix hrel
        have hlt : (Nat.card F) ^ 2 * (4 * Nat.card F) < (Nat.card F) ^ 4 := by
          have hq4 : 4 < Nat.card F := by omega
          have hqpos : 0 < Nat.card F := by omega
          calc (Nat.card F) ^ 2 * (4 * Nat.card F) = 4 * (Nat.card F) ^ 3 := by ring
            _ < (Nat.card F) * (Nat.card F) ^ 3 :=
                Nat.mul_lt_mul_of_pos_right hq4 (pow_pos hqpos 3)
            _ = (Nat.card F) ^ 4 := by ring
        rw [hWcard]
        exact lt_of_le_of_lt hprod hlt
      have hE₀rel : E₀.relIndex (rightConjugate U h0) = W.relIndex B' := by
        rw [← hB'map]
        change (W.map eG.toMonoidHom).relIndex (B'.map eG.toMonoidHom) = W.relIndex B'
        exact Subgroup.relIndex_map_map_of_injective W B' eG.injective
      have hCEmap : (W ⊓ Subgroup.centralizer ({x} : Set G)).map eG.toMonoidHom =
          E₀ ⊓ Subgroup.centralizer ({eG x} : Set G₀) := by
        rw [show E₀ = W.map eG.toMonoidHom from rfl,
          Subgroup.map_inf W _ eG.toMonoidHom eG.injective,
          CFSG.Walter.map_centralizer_singleton_mulEquiv eG x]
      have hcardCE : Nat.card ↥(E₀ ⊓ Subgroup.centralizer ({eG x} : Set G₀)) =
          Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) := by
        rw [← hCEmap, Subgroup.card_map_of_injective eG.injective]
      have hcardE : Nat.card E₀ = Nat.card W :=
        Subgroup.card_map_of_injective eG.injective
      have hlt0 : Nat.card ↥(E₀ ⊓ Subgroup.centralizer ({eG x} : Set G₀)) *
          E₀.relIndex (rightConjugate U h0) < Nat.card E₀ := by
        rw [hcardCE, hcardE, hE₀rel]
        exact hltW
      have hcommE0 : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
        intro a ha b hb
        simpa using congrArg Subtype.val
          (hE₀ab.is_comm.comm (⟨a, ha⟩ : ↥E₀) (⟨b, hb⟩ : ↥E₀))
      have hxM₀ : eG x ∈ Subgroup.normalizer (E₀ : Set G₀) := by
        rw [← Subgroup.map_equiv_normalizer_eq W eG]
        exact Subgroup.mem_map_of_mem eG.toMonoidHom (hPM hxP)
      have hcomm0 :=
        CFSG.SeitzReduction.RankOne.GMS43.lt_card_commutator_of_mul_lt
          hcommE0 hxM₀ hlt0
      refine ⟨eG x, ?_, hcomm0⟩
      rw [← hB'map]
      exact Subgroup.mem_map_of_mem eG.toMonoidHom hxB'
    obtain ⟨P₀, hP₀coe, hstrong⟩ :=
      CFSG.SeitzReduction.RankOne.GMS43.exists_sylow_stronglyClosed_of_commutator_bound
        hE₀S₀ hE₀el hS₀syl hH
    have hnonab₀ : ∃ a b : G₀, a * b ≠ b * a :=
      CFSG.CGT.Timmesfeld75.exists_noncomm_of_mulEquiv' eG hnonab
    have ht0P : eG t ∈ (P₀ : Subgroup G₀) := by
      rw [hP₀coe]
      exact Subgroup.mem_map_of_mem eG.toMonoidHom htP
    have ht0sq : (eG t) * (eG t) = 1 := by
      rw [← map_mul]
      have ht2 : t * t = 1 := by
        have := pow_orderOf_eq_one t
        rw [ht] at this
        simpa [pow_two] using this
      rw [ht2, map_one]
    have hcl : ∀ a ∈ E₀, ∀ g : G₀, g⁻¹ * a * g ∈ (P₀ : Subgroup G₀) →
        g⁻¹ * a * g ∈ E₀ := by
      intro a ha g hg
      exact hstrong a ha g (by rwa [hP₀coe] at hg)
    have ht0E : eG t ∈ E₀ :=
      CFSG.CGT.Timmesfeld75.stronglyClosed_contains_involutions
        CFSG.CGT.Timmesfeld75.goldschmidt1974_of_milestone hnonab₀ P₀ hE₀ne
        (by rw [hP₀coe]; exact hE₀S₀) hE₀ab hcl (eG t) ht0P ht0sq
    have htW' : t ∈ W := by
      have hmem : eG.symm (eG t) ∈ W := by
        rw [← Subgroup.mem_map_equiv (f := eG) (K := W)]
        exact ht0E
      simpa using hmem
    exact htW htW'
  refine ⟨hQleP, hPM, htP, hBelem, hFix, hnotSyl, ?_⟩
  have hP2M : IsPGroup 2 (P.subgroupOf (Subgroup.normalizer (W : Set G))) :=
    hP.isPGroup.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hP2M.exists_le_sylow
  let T : Subgroup G :=
    (Q₀ : Subgroup ↥(Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T
      (Subgroup.normalizer (W : Set G)) := ⟨Q₀, rfl⟩
  have hPT : P ≤ T := by
    intro x hx
    have hxM : x ∈ Subgroup.normalizer (W : Set G) := hPM hx
    exact Subgroup.mem_map_of_mem (Subgroup.normalizer (W : Set G)).subtype
      (hQ₀ (show (⟨x, hxM⟩ : ↥(Subgroup.normalizer (W : Set G))) ∈
        P.subgroupOf (Subgroup.normalizer (W : Set G)) from
          Subgroup.mem_subgroupOf.mpr hx))
  have hne : P ≠ T := by
    intro heq
    apply hnotSyl
    have := hTsyl
    rw [← heq] at this
    exact this
  exact ⟨T, lt_of_le_of_ne hPT hne, hTsyl⟩


end CFSG.ComponentClassification.GS79bSec5

end
