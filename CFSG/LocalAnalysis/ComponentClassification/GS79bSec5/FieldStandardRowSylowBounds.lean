module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.LocalAnalysis.EvenBN.LinearThree.WLocalAbelian
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowElementary
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowSemilinear
import CFSG.GroupTheory.SemilinearElementaryTwoBound
import CFSG.Quasithin.Vol2.Ch6SL2Fix
import CFSG.GroupTheory.CommutingConjugatePair
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowCoordinates

public section

open Matrix Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_sylow_bounds_of_standard_row
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
              Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) ≤ (Nat.card F) ^ 2)
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
  let V := Fin 2 → F
  obtain ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO, hOA, hJO,
    hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO, hQdisj, hQCO, hQCt,
    hQcard, κQpart, hSpart⟩ :=
    exists_elementary_extension_of_standard_row hnonab hF A hA hZ e φ hφsurj hφproj hcyc
      t ht htC
  obtain ⟨κQ, hκQformula, hκQker, hκQsurj⟩ := κQpart
  obtain ⟨S, hSX, hSt, hSι, hSlev, hStor, hWpart⟩ := hSpart
  obtain ⟨W, hWQ, hWelem, hWcard, hEltW, htW, hQsup, hWcoset, hWchar, hNW, hWfixE,
    hcomm_t, hWCO, hlevN, htorN, hcomm_lev, hWuniq⟩ := hWpart
  obtain ⟨hNE', α, hαact, hαker⟩ :=
    exists_semilinear_action_of_standard_row hnonab hF A hA hZ e φ hφsurj hφproj hcyc
      t ht htC
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht] at this
    simpa [pow_two] using this
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hEW : E ≤ W := le_of_lt hEltW
  have htE : t ∉ E := fun h => htW (hEW h)
  have hEA : E ≤ A := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact (φ z).2
  have hEct : ∀ e ∈ E, e * t = t * e := by
    intro e he
    exact Subgroup.mem_centralizer_iff.mp htC e (hEA he)
  have hE2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have := hWelem.2 e (hEW he)
    simpa [pow_two] using this
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    simpa using hWelem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  have hcommEt : ∀ e ∈ E, ∀ z ∈ Subgroup.zpowers t, Commute e z := by
    intro e he z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_right (show Commute e t from hEct e he) k
  let ιE : Multiplicative (Fin 2 → F) ≃* E := literalRowEquiv A e φ hφproj
  have hEcard : Nat.card E = (Nat.card F) ^ 2 := by
    calc Nat.card E = Nat.card (Multiplicative (Fin 2 → F)) :=
          (Nat.card_congr ιE.toEquiv).symm
      _ = Nat.card (Fin 2 → F) := rfl
      _ = (Nat.card F) ^ 2 := by rw [Nat.card_fun, Nat.card_fin]
  have hιE : ∀ v : Multiplicative (Fin 2 → F),
      ((ιE v : E) : G) = ρ (rowSLHom F v) := by
    intro v
    have h := literalRowEquiv_apply A e φ hφproj v
    simpa [ιE, ρ, rowSLHom] using h
  have hι_eq : ∀ v : Fin 2 → F, ι v = ((ιE (Multiplicative.ofAdd v) : E) : G) := by
    intro v
    rw [hιE]
    simp [ι, rowSLHom]
  have hι_inj : Function.Injective ι := by
    intro u v huv
    have hrow : ιE (Multiplicative.ofAdd u) = ιE (Multiplicative.ofAdd v) := by
      apply Subtype.ext
      simpa [hι_eq u, hι_eq v] using huv
    have hof := ιE.injective hrow
    exact Multiplicative.ofAdd.injective hof
  have hι_memE : ∀ v : Fin 2 → F, ι v ∈ E := by
    intro v
    rw [hι_eq v]
    exact (ιE (Multiplicative.ofAdd v)).2
  have hWJ : W ⊓ J = E := by
    apply le_antisymm
    · intro y hy
      obtain ⟨e, he, z, hz, hzeq⟩ :=
        CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := E)
          (B := Subgroup.zpowers t) hcommEt
          (show y ∈ E ⊔ Subgroup.zpowers t from hy.2)
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two ht).1 hz with h1 | h1
      · have hyE : y = e := by rw [← hzeq, h1, mul_one]
        rwa [hyE]
      · exfalso
        have hy_eq : y = e * t := by rw [← hzeq, h1]
        have htW' : t ∈ W := by
          have h1' : t = e⁻¹ * y := by rw [hy_eq]; group
          rw [h1']
          exact W.mul_mem (W.inv_mem (hEW he)) hy.1
        exact htW htW'
    · intro y hy
      exact ⟨hEW hy, Subgroup.mem_sup_left hy⟩
  have hntn : ∀ n ∈ N, ∃ e ∈ E, n * t * n⁻¹ = t * e := by
    intro n hn
    have hntJ : n * t * n⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp hn t).mp
        (show t ∈ J from Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    obtain ⟨e, he, z, hz, hzeq⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := E)
        (B := Subgroup.zpowers t) hcommEt
        (show n * t * n⁻¹ ∈ E ⊔ Subgroup.zpowers t from hntJ)
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two ht).1 hz with h1 | h1
    · exfalso
      have hyE : n * t * n⁻¹ ∈ E := by
        rw [← hzeq, h1, mul_one]
        exact he
      have htE' : t ∈ E := by
        have hmem : n⁻¹ * (n * t * n⁻¹) * n ∈ E := by
          simpa [E, ρ] using
            (Subgroup.mem_normalizer_iff.mp (hNE (N.inv_mem hn)) (n * t * n⁻¹)).mp hyE
        simpa [show n⁻¹ * (n * t * n⁻¹) * n = t by group] using hmem
      exact htE htE'
    · refine ⟨e, he, ?_⟩
      rw [← hzeq, h1]
      exact hEct e he
  have hcov : ∀ (n : G) (hn : n ∈ N) (w : G) (hw : w ∈ W),
      ((κQ ⟨n * w * n⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hNQ hn) w).mp (hWQ hw)⟩ : E) : G) =
        n * ((κQ ⟨w, hWQ hw⟩ : E) : G) * n⁻¹ := by
    intro n hn w hw
    obtain ⟨e, he, hne⟩ := hntn n hn
    let u : G := n * w * n⁻¹
    have huW : u ∈ W := (Subgroup.mem_normalizer_iff.mp (hNW hn) w).mp hw
    have heu : e * u = u * e := hWcomm e (hEW he) u huW
    have hee : e * e = 1 := hE2 e he
    have halg' : (t * e) * u * (t * e) * u⁻¹ = t * u * t * u⁻¹ := by
      calc (t * e) * u * (t * e) * u⁻¹
          = t * (e * u) * (t * e) * u⁻¹ := by group
        _ = t * (u * e) * (t * e) * u⁻¹ := by rw [heu]
        _ = t * u * (e * t) * e * u⁻¹ := by group
        _ = t * u * (t * e) * e * u⁻¹ := by rw [hEct e he]
        _ = t * u * t * (e * e) * u⁻¹ := by group
        _ = t * u * t * u⁻¹ := by rw [hee]; group
    calc ((κQ ⟨n * w * n⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hNQ hn) w).mp (hWQ hw)⟩ : E) : G)
        = t * u * t * u⁻¹ := by
          simpa [u, mul_assoc] using hκQformula ⟨n * w * n⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hNQ hn) w).mp (hWQ hw)⟩
      _ = (t * e) * u * (t * e) * u⁻¹ := halg'.symm
      _ = (n * t * n⁻¹) * u * (n * t * n⁻¹) * u⁻¹ := by rw [hne]
      _ = n * (t * w * t * w⁻¹) * n⁻¹ := by dsimp [u]; group
      _ = n * ((κQ ⟨w, hWQ hw⟩ : E) : G) * n⁻¹ := by
            rw [hκQformula]; group
  have hQrelW : W.relIndex Q = 2 := by
    have h := Subgroup.relIndex_mul_card W Q
    rw [inf_eq_left.mpr hWQ, hQcard, hWcard] at h
    have hq4 : 0 < (Nat.card F) ^ 4 := pow_pos (by omega) 4
    exact Nat.eq_of_mul_eq_mul_right hq4 h
  have hWrelB_eq : ∀ B : Subgroup G, W.relIndex B = (B ⊓ W).relIndex B := by
    intro B
    simp [Subgroup.relIndex, inf_comm]
  refine ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO, hOA, hJO,
    hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO, hQdisj, hQCO, hQCt,
    hQcard, ⟨κQ, hκQformula, hκQker, hκQsurj⟩, S, hSX, hSt, hSι, hSlev, hStor, W,
    ⟨hWQ, hWelem, hWcard, hEltW, htW, hQsup, hWcoset, hWchar, hNW, hWfixE, hcomm_t,
      hWCO, hlevN, htorN, hcomm_lev, hWuniq⟩, ?_⟩
  intro P hP
  have hPN : P ≤ N := hP.le
  have hP2 : IsPGroup 2 P := hP.isPGroup
  have hQleN : Q ≤ N := hQX.trans inf_le_left
  have hQleP : Q ≤ P := by
    have hsupP : IsPGroup 2 ↥(P ⊔ Q) :=
      hP2.to_sup_of_normal_right' hQ2 (hPN.trans hNQ)
    have hsupN : (P ⊔ Q : Subgroup G) ≤ N := sup_le hPN hQleN
    have heq : (P ⊔ Q : Subgroup G) = P := hP.eq_of_le le_sup_left hsupN hsupP
    exact (le_sup_right : Q ≤ P ⊔ Q).trans heq.le
  have hPM : P ≤ Subgroup.normalizer (W : Set G) := hPN.trans hNW
  have htP : t ∈ P := hQleP (hJQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  have hPinfO : P ⊓ O = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hP2 hOodd
  have hPX : P ⊓ X = Q := by
    apply le_antisymm
    · intro x hx
      have hxP : x ∈ P := hx.1
      have hxX : x ∈ X := hx.2
      obtain ⟨q, hq, o, ho, hqo⟩ :=
        CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := Q) (B := O)
          (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hQCO ha) b hb).symm)
          (show x ∈ Q ⊔ O from hQO.symm ▸ hxX)
      have hoP : o ∈ P := by
        have ho_eq : o = q⁻¹ * x := by
          rw [← hqo]
          group
        rw [ho_eq]
        exact P.mul_mem (P.inv_mem (hQleP hq)) hxP
      have ho1 : o = 1 := by
        have ho_bot : o ∈ P ⊓ O := ⟨hoP, ho⟩
        rw [hPinfO] at ho_bot
        exact ho_bot
      have hxq : x = q := by rw [← hqo, ho1, mul_one]
      rwa [hxq]
    · exact le_inf hQleP hQX
  refine ⟨hQleP, hPM, htP, ?_, ?_⟩
  · intro B hBP hBelem
    have hBN : B ≤ N := hBP.trans hPN
    let inclBN : B →* N :=
      { toFun := fun b => ⟨b.1, hBN b.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let αB : B →* ↥(CFSG.LieType.ChevTwo.OppCl.semilinGroup F V) := α.comp inclBN
    let D : Subgroup (Equiv.Perm V) :=
      αB.range.map (CFSG.LieType.ChevTwo.OppCl.semilinGroup F V).subtype
    have hDsem : D ≤ CFSG.LieType.ChevTwo.OppCl.semilinGroup F V := by
      rintro d ⟨z, -, rfl⟩
      exact z.2
    have hD : CFSG.Open.IsElemAbelian 2 D := by
      have hBcomm : IsMulCommutative B := hBelem.1
      have hcommD : IsMulCommutative D := by
        have hRangeComm : IsMulCommutative ↥αB.range := Subgroup.range_isMulCommutative αB
        exact Subgroup.map_isMulCommutative αB.range
          (CFSG.LieType.ChevTwo.OppCl.semilinGroup F V).subtype
      refine ⟨hcommD, ?_⟩
      rintro d ⟨z, hz, rfl⟩
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hz
      have hb2 : b * b = 1 :=
        Subtype.ext (by simpa [pow_two] using hBelem.2 b.1 b.2)
      have hmul : (αB b) * (αB b) = 1 := by
        rw [← map_mul, hb2, map_one]
      simpa [pow_two] using congrArg
        (fun z : ↥(CFSG.LieType.ChevTwo.OppCl.semilinGroup F V) => (z : Equiv.Perm V)) hmul
    have hDcard : Nat.card D = (B ⊓ Q).relIndex B := by
      have hker : αB.ker = (B ⊓ Q).subgroupOf B := by
        ext b
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · intro hb
          have hbX : (b : G) ∈ X := by
            have hmemN : (⟨b.1, hBN b.2⟩ : N) ∈ α.ker := by
              rw [MonoidHom.mem_ker]
              change α (inclBN b) = 1
              exact hb
            rw [hαker] at hmemN
            exact Subgroup.mem_subgroupOf.mp hmemN
          have hbQ : (b : G) ∈ Q := by
            rw [← hPX]
            exact ⟨hBP b.2, hbX⟩
          exact ⟨b.2, hbQ⟩
        · rintro ⟨-, hbQ⟩
          have hbX : (b : G) ∈ X := hQX hbQ
          have hmemN : (⟨b.1, hBN b.2⟩ : N) ∈ α.ker := by
            rw [hαker]
            exact Subgroup.mem_subgroupOf.mpr hbX
          rw [MonoidHom.mem_ker] at hmemN
          change α (inclBN b) = 1
          exact hmemN
      have hcardker : Nat.card αB.ker = Nat.card ↥(B ⊓ Q) := by
        rw [hker]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : B ⊓ Q ≤ B)).toEquiv
      have hcardrange : Nat.card αB.range = Nat.card D := by
        simpa [D] using (Subgroup.card_map_of_injective (K := αB.range)
          (f := (CFSG.LieType.ChevTwo.OppCl.semilinGroup F V).subtype)
          (Subgroup.subtype_injective _)).symm
      have hBcard : Nat.card B = Nat.card ↥(B ⊓ Q) * Nat.card D := by
        rw [← hcardrange, ← hcardker, Subgroup.card_ker_mul_card_range αB]
      have hrel := Subgroup.relIndex_mul_card (B ⊓ Q) B
      have hinf : (B ⊓ Q) ⊓ B = B ⊓ Q := by
        ext x
        simp
      rw [hinf] at hrel
      have hpos : 0 < Nat.card ↥(B ⊓ Q) := Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc Nat.card ↥(B ⊓ Q) * Nat.card D = Nat.card B := hBcard.symm
        _ = (B ⊓ Q).relIndex B * Nat.card ↥(B ⊓ Q) := hrel.symm
        _ = Nat.card ↥(B ⊓ Q) * (B ⊓ Q).relIndex B := Nat.mul_comm _ _
    have hBQbound : (B ⊓ Q).relIndex B ≤ 2 * Nat.card F := by
      rw [← hDcard]
      exact CFSG.GroupTheory.card_le_two_mul_card_of_isElemAbelian_semilinear_two D hD hDsem
    have hstep : (B ⊓ W).relIndex (B ⊓ Q) ≤ 2 := by
      have hself : (B ⊓ Q).relIndex (B ⊓ Q) = 1 := by
        simp [Subgroup.relIndex]
      have hWQinf : W ⊓ (B ⊓ Q) = B ⊓ W := by
        ext x
        constructor
        · rintro ⟨hxW, hxB, -⟩
          exact ⟨hxB, hxW⟩
        · rintro ⟨hxB, hxW⟩
          exact ⟨hxW, hxB, hWQ hxW⟩
      have hle : (B ⊓ W).relIndex (B ⊓ Q) ≤ W.relIndex (B ⊓ Q) := by
        have h := Subgroup.relIndex_inf_le (H := W) (K := B ⊓ Q) (L := B ⊓ Q)
        simpa [hWQinf, hself] using h
      have hle2 : W.relIndex (B ⊓ Q) ≤ W.relIndex Q :=
        Subgroup.relIndex_le_of_le_right inf_le_right (by rw [hQrelW]; norm_num)
      have h := hle.trans hle2
      rwa [hQrelW] at h
    have hBWleBQ : B ⊓ W ≤ B ⊓ Q := le_inf inf_le_left (inf_le_right.trans hWQ)
    calc W.relIndex B = (B ⊓ W).relIndex B := hWrelB_eq B
      _ = (B ⊓ W).relIndex (B ⊓ Q) * (B ⊓ Q).relIndex B :=
            (Subgroup.relIndex_mul_relIndex (H := B ⊓ W) (K := B ⊓ Q) (L := B)
              hBWleBQ inf_le_left).symm
      _ ≤ 2 * (2 * Nat.card F) := Nat.mul_le_mul hstep hBQbound
      _ = 4 * Nat.card F := by ring
  · intro x hxP hxW hx2
    by_cases hxQ : x ∈ Q
    · have hxQtW : x * t ∈ W := by
        rcases hWcoset x hxQ with h | h
        · exact absurd h hxW
        · exact h
      have hCWx : W ⊓ Subgroup.centralizer ({x} : Set G) = E := by
        apply le_antisymm
        · intro z hz
          have hzW : z ∈ W := hz.1
          have hzC : x * z = z * x :=
            Subgroup.mem_centralizer_iff.mp hz.2 x (Set.mem_singleton x)
          have hzy : z * (x * t) = (x * t) * z := hWcomm z hzW _ hxQtW
          have hzt : z * t = t * z := by
            have hxeq : x = (x * t) * t := by rw [mul_assoc, ht2, mul_one]
            have h1 : z * ((x * t) * t) = ((x * t) * t) * z := by
              rw [← hxeq]
              exact hzC.symm
            have h2 : z * ((x * t) * t) = (x * t) * (z * t) := by
              rw [← mul_assoc, hzy, mul_assoc]
            have h3 : ((x * t) * t) * z = (x * t) * (t * z) := by rw [mul_assoc]
            rw [h2, h3] at h1
            exact mul_left_cancel h1
          have hzCt : z ∈ Subgroup.centralizer ({t} : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff.mp hy]
            exact hzt.symm
          have hmem : z ∈ W ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hzW, hzCt⟩
          rwa [hWfixE] at hmem
        · intro z hz
          have hzW : z ∈ W := hEW hz
          have hzt : z * t = t * z := hEct z hz
          refine ⟨hzW, ?_⟩
          change z ∈ Subgroup.centralizer ({x} : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff.mp hy]
          have hxeq : x = (x * t) * t := by rw [mul_assoc, ht2, mul_one]
          have hzy : z * (x * t) = (x * t) * z := hWcomm z hzW _ hxQtW
          calc x * z = ((x * t) * t) * z := by
                conv_lhs => rw [hxeq]
            _ = (x * t) * (t * z) := by group
            _ = (x * t) * (z * t) := by rw [← hzt]
            _ = ((x * t) * z) * t := by group
            _ = (z * (x * t)) * t := by rw [hzy]
            _ = z * ((x * t) * t) := by group
            _ = z * x := by
                conv_rhs => rw [hxeq]
      have hcard : Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) =
          (Nat.card F) ^ 2 := by
        rw [hCWx, hEcard]
      rw [hcard]
    · have hxN : x ∈ N := hPN hxP
      have hαxne : (α ⟨x, hxN⟩) ≠ 1 := by
        intro h
        have hxX : x ∈ X := by
          have hmemN : (⟨x, hxN⟩ : N) ∈ α.ker := MonoidHom.mem_ker.mpr h
          rw [hαker] at hmemN
          exact Subgroup.mem_subgroupOf.mp hmemN
        exact hxQ (by rw [← hPX]; exact ⟨hxP, hxX⟩)
      let gT : V ≃+ V :=
        { toEquiv := (α ⟨x, hxN⟩ : Equiv.Perm V)
          map_add' := (α ⟨x, hxN⟩).2.1 }
      let σ : F ≃+* F := Classical.choose (α ⟨x, hxN⟩).2.2
      have hσ : ∀ a v, gT (a • v) = σ a • gT v :=
        Classical.choose_spec (α ⟨x, hxN⟩).2.2
      have hact' : ∀ v : V,
          ι ((α ⟨x, hxN⟩ : Equiv.Perm V) v) = x * ι v * x⁻¹ :=
        fun v => hαact ⟨x, hxN⟩ v
      have hgmove : ∃ v : V, gT v ≠ v := by
        by_contra hcon
        push Not at hcon
        apply hαxne
        apply Subtype.ext
        apply Equiv.ext
        intro v
        show (α ⟨x, hxN⟩ : Equiv.Perm V) v = v
        simpa [gT] using hcon v
      have hfix := CFSG.Quasithin.H13.card_fixed_le_semilinear gT σ hσ hgmove
      let hCE : Subgroup G := E ⊓ Subgroup.centralizer ({x} : Set G)
      have hι_val : ∀ e : ↥hCE,
          ι (Multiplicative.toAdd (ιE.symm ⟨e.1, e.2.1⟩)) = e.1 := by
        intro e
        rw [hι_eq]
        simp
      let toFix : ↥hCE → {v : V // gT v = v} := fun e =>
        ⟨Multiplicative.toAdd (ιE.symm ⟨e.1, e.2.1⟩), by
          apply hι_inj
          have harg : ι (Multiplicative.toAdd (ιE.symm ⟨e.1, e.2.1⟩)) = e.1 := hι_val e
          have h := hact' (Multiplicative.toAdd (ιE.symm ⟨e.1, e.2.1⟩))
          rw [harg] at h
          change ι ((α ⟨x, hxN⟩ : Equiv.Perm V)
            (Multiplicative.toAdd (ιE.symm ⟨e.1, e.2.1⟩))) =
              ι (Multiplicative.toAdd (ιE.symm ⟨e.1, e.2.1⟩))
          rw [h, harg]
          have hxC : x * e.1 = e.1 * x :=
            Subgroup.mem_centralizer_iff.mp e.2.2 x (Set.mem_singleton x)
          calc x * e.1 * x⁻¹ = (e.1 * x) * x⁻¹ := by rw [hxC]
            _ = e.1 := by group⟩
      have htoFix_inj : Function.Injective toFix := by
        intro e f hef
        have hval : (toFix e : V) = (toFix f : V) := congrArg Subtype.val hef
        apply Subtype.ext
        have h1 : ι (toFix e : V) = ι (toFix f : V) := by rw [hval]
        simpa [toFix, hι_val e, hι_val f] using h1
      have hCEcard : Nat.card hCE ≤ Nat.card F :=
        (Nat.card_le_card_of_injective toFix htoFix_inj).trans hfix
      let CW : Subgroup G := W ⊓ Subgroup.centralizer ({x} : Set G)
      have hCWQ : CW ≤ Q := inf_le_left.trans hWQ
      let inclCW : CW →* Q :=
        { toFun := fun c => ⟨c.1, hCWQ c.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      let κC : CW →* E := κQ.comp inclCW
      have hκC_ker_mem : ∀ c : CW, c ∈ κC.ker ↔ (c.1 : G) ∈ hCE := by
        intro c
        constructor
        · intro hc
          have hcJ : (c.1 : G) ∈ J := by
            have hk : (⟨c.1, hCWQ c.2⟩ : Q) ∈ κQ.ker := by
              rw [MonoidHom.mem_ker]
              change κQ (inclCW c) = 1
              exact MonoidHom.mem_ker.mp hc
            rw [hκQker] at hk
            exact Subgroup.mem_subgroupOf.mp hk
          have hcE : (c.1 : G) ∈ E := by
            have hmem : (c.1 : G) ∈ W ⊓ J := ⟨c.2.1, hcJ⟩
            rwa [hWJ] at hmem
          exact ⟨hcE, c.2.2⟩
        · rintro ⟨hcE, hcC⟩
          rw [MonoidHom.mem_ker]
          change κQ (inclCW c) = 1
          have hk : (⟨c.1, hCWQ c.2⟩ : Q) ∈ κQ.ker := by
            rw [hκQker]
            exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hcE)
          exact MonoidHom.mem_ker.mp hk
      have hκC_ker : Subgroup.map CW.subtype κC.ker = hCE := by
        ext y
        constructor
        · rintro ⟨c, hc, rfl⟩
          exact (hκC_ker_mem c).mp hc
        · intro hy
          have hyCW : y ∈ CW := ⟨hEW hy.1, hy.2⟩
          refine ⟨⟨y, hyCW⟩, ?_, rfl⟩
          exact (hκC_ker_mem ⟨y, hyCW⟩).mpr hy
      have hkerκC : Nat.card κC.ker = Nat.card hCE := by
        calc Nat.card κC.ker = Nat.card (κC.ker.map CW.subtype) :=
              (Subgroup.card_map_of_injective (K := κC.ker) (f := CW.subtype)
                (Subgroup.subtype_injective CW)).symm
          _ = Nat.card hCE := by rw [hκC_ker]
      have hκC_range : κC.range.map E.subtype ≤ hCE := by
        rintro z ⟨w, hw, rfl⟩
        obtain ⟨c, rfl⟩ := hw
        have hcC : x * (c.1 : G) = (c.1 : G) * x :=
          Subgroup.mem_centralizer_iff.mp c.2.2 x (Set.mem_singleton x)
        have hcommx : x * ((κQ ⟨c.1, hCWQ c.2⟩ : E) : G) * x⁻¹ =
            ((κQ ⟨c.1, hCWQ c.2⟩ : E) : G) := by
          have h := hcov x hxN c.1 c.2.1
          have hxc : x * (c.1 : G) * x⁻¹ = c.1 := by rw [hcC]; group
          have harg : (⟨x * (c.1 : G) * x⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hNQ hxN) (c.1 : G)).mp
                (hWQ c.2.1)⟩ : Q) = ⟨c.1, hCWQ c.2⟩ := Subtype.ext hxc
          rw [harg] at h
          have hq : (⟨c.1, hWQ c.2.1⟩ : Q) = ⟨c.1, hCWQ c.2⟩ := Subtype.ext rfl
          rw [hq] at h
          exact h.symm
        refine ⟨(κQ ⟨c.1, hCWQ c.2⟩ : E).2, ?_⟩
        change ((κQ ⟨c.1, hCWQ c.2⟩ : E) : G) ∈
          Subgroup.centralizer ({x} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        calc x * ((κQ ⟨c.1, hCWQ c.2⟩ : E) : G)
            = (x * ((κQ ⟨c.1, hCWQ c.2⟩ : E) : G) * x⁻¹) * x := by group
          _ = ((κQ ⟨c.1, hCWQ c.2⟩ : E) : G) * x := by rw [hcommx]
      have hCWcard : Nat.card CW ≤ (Nat.card F) ^ 2 := by
        calc Nat.card CW = Nat.card κC.ker * Nat.card κC.range :=
              (Subgroup.card_ker_mul_card_range κC).symm
          _ = Nat.card hCE * Nat.card κC.range := by rw [hkerκC]
          _ = Nat.card hCE * Nat.card (κC.range.map E.subtype) := by
              rw [Subgroup.card_map_of_injective E.subtype_injective]
          _ ≤ Nat.card hCE * Nat.card hCE :=
              Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hκC_range)
          _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul hCEcard hCEcard
          _ = (Nat.card F) ^ 2 := by ring
      exact hCWcard

end CFSG.ComponentClassification.GS79bSec5

end
