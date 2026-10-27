module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowOddComplement
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowTranslations
public import CFSG.GroupTheory.RegularTranslationsOddComplement
public import CFSG.LocalAnalysis.EvenBN.LinearThree.WLocalAbelian

public noncomputable section

open Matrix Subgroup
open Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree

namespace CFSG.ComponentClassification.GS79bSec5

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem exists_characteristic_two_factor_of_standard_row
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
          κQ.ker = J.subgroupOf Q ∧ Function.Surjective κQ) := by
  classical
  dsimp only
  let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
  let E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
  let J : Subgroup G := E ⊔ Subgroup.zpowers t
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let C : Subgroup G := Subgroup.centralizer (J : Set G)
  let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
  have hfirst :=
    exists_characteristic_odd_complement_of_standard_row hnonab hF A hA hZ e φ hφsurj
      hφproj hcyc t ht htC
  dsimp only at hfirst
  obtain ⟨hJea, hJcard, hJsylow, hJcent, O, hOC, hOodd, hOchar, hNO, hOA,
    hJO, hJOdisj⟩ := hfirst
  have htrans :=
    regular_translations_of_standard_row hnonab hF A hA hZ e φ hφsurj hφproj hcyc
      t ht htC
  dsimp only at htrans
  obtain ⟨hNE, -, κ, hκformula, hκker, hκsurj, -⟩ := htrans
  let ιE : Multiplicative (Fin 2 → F) ≃* E :=
    literalRowEquiv A e φ hφproj
  have hιE : ∀ v : Multiplicative (Fin 2 → F),
      ((ιE v : E) : G) = ρ (rowSLHom F v) := by
    intro v
    have h := literalRowEquiv_apply A e φ hφproj v
    simpa [ιE, ρ, rowSLHom] using h
  have hq8 : 8 ≤ Nat.card F := by omega
  obtain ⟨lam, hlam⟩ := CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.exists_unit_cube_ne_one
    (K := F) hq8
  let l : G := ρ (torSLZero F lam)
  have htor_conj : ∀ μ : Fˣ, ∀ v : Multiplicative (Fin 2 → F),
      ρ (torSLZero F μ) * (ιE v : G) * (ρ (torSLZero F μ))⁻¹ =
        (ιE (Multiplicative.ofAdd
          (((μ : F) ^ 3) • Multiplicative.toAdd v)) : G) := by
    intro μ v
    rw [hιE v, hιE (Multiplicative.ofAdd _)]
    rw [← map_inv, ← map_mul, ← map_mul, torSLZero_conj_rowSLHom]
  have htor_map_le : ∀ μ : Fˣ,
      E.map (MulAut.conj (ρ (torSLZero F μ))).toMonoidHom ≤ E := by
    intro μ x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, hv⟩ := ιE.surjective ⟨e, he⟩
    have hev : ((ιE v : E) : G) = e := congrArg (fun t : E => (t : G)) hv
    rw [← hev]
    change ρ (torSLZero F μ) * (ιE v : G) * (ρ (torSLZero F μ))⁻¹ ∈ E
    rw [htor_conj μ v]
    exact (ιE _).2
  have htorE : l ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · exact htor_map_le lam
    · intro x hx
      obtain ⟨v, hv⟩ := ιE.surjective ⟨x, hx⟩
      have hxval : ((ιE v : E) : G) = x := congrArg (fun t : E => (t : G)) hv
      rw [← hxval]
      have hx' : l⁻¹ * (ιE v : G) * l ∈ E := by
        have hmem : ρ (torSLZero F lam⁻¹) * (ιE v : G) *
            (ρ (torSLZero F lam⁻¹))⁻¹ ∈ E := by
          rw [htor_conj lam⁻¹ v]
          exact (ιE _).2
        have hl_inv : ρ (torSLZero F lam⁻¹) = l⁻¹ := by
          simp [l, map_inv]
        simpa [hl_inv] using hmem
      refine Subgroup.mem_map.mpr ⟨l⁻¹ * (ιE v : G) * l, hx', ?_⟩
      change l * (l⁻¹ * (ιE v : G) * l) * l⁻¹ = (ιE v : G)
      group
  have hlA : l ∈ A := (φ (torSLZero F lam)).2
  have hlO : l ∈ Subgroup.centralizer (O : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact (Subgroup.mem_centralizer_iff.mp (hOA ho) l hlA).symm
  have hlt : Commute l t :=
    Subgroup.mem_centralizer_iff.mp htC l hlA
  have htorJ : l ∈ N := by
    change l ∈ Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hEmap : E.map (MulAut.conj l).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htorE
    have htmap : (Subgroup.zpowers t).map (MulAut.conj l).toMonoidHom =
        Subgroup.zpowers t := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change l * t * l⁻¹ = t
      rw [hlt.eq, mul_inv_cancel_right]
    calc (E ⊔ Subgroup.zpowers t).map (MulAut.conj l).toMonoidHom
        = E.map (MulAut.conj l).toMonoidHom ⊔
            (Subgroup.zpowers t).map (MulAut.conj l).toMonoidHom := by
          rw [Subgroup.map_sup]
      _ = E ⊔ Subgroup.zpowers t := by rw [hEmap, htmap]
  have hlfree : ∀ x ∈ E, l * x * l⁻¹ = x → x = 1 := by
    intro x hx heq
    obtain ⟨v, hv⟩ := ιE.surjective ⟨x, hx⟩
    have hxval : ((ιE v : E) : G) = x := congrArg (fun t : E => (t : G)) hv
    rw [← hxval] at heq ⊢
    have hconj := htor_conj lam v
    rw [show l = ρ (torSLZero F lam) from rfl] at heq
    rw [hconj] at heq
    have hveq : Multiplicative.ofAdd
        ((((lam : F) ^ 3) • Multiplicative.toAdd v)) = v := by
      apply ιE.injective
      exact Subtype.ext heq
    have hscalar : (((lam : F) ^ 3) • Multiplicative.toAdd v) =
        Multiplicative.toAdd v := Multiplicative.ofAdd.injective hveq
    have hv0 : Multiplicative.toAdd v = 0 := by
      funext i
      have hi : ((lam : F) ^ 3) * (Multiplicative.toAdd v) i =
          (Multiplicative.toAdd v) i := by
        simpa [Pi.smul_apply] using congrFun hscalar i
      have hzero : (((lam : F) ^ 3) - 1) * (Multiplicative.toAdd v) i = 0 := by
        linear_combination hi
      exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hlam)
    have hv1 : v = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hv0
    rw [hv1]
    simp
  have hJpow : ∀ j ∈ E ⊔ Subgroup.zpowers t, j ^ 2 = 1 := by
    intro j hj
    exact hJea.2 j hj
  have hgen :=
    CFSG.exists_characteristic_two_factor_of_regular_translation
      (G := G) E t hJpow hNE O hOC hOodd hNO hJO hJOdisj κ hκformula hκker
        hκsurj l htorJ hlO hlt hlfree
  dsimp only at hgen
  obtain ⟨Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO, hQdisj,
    hQCO, hQCt, hQcard, κQ, hκQformula, hκQker, hκQsurj⟩ := hgen
  have hEcard : Nat.card E = (Nat.card F) ^ 2 := by
    calc Nat.card E = Nat.card (Multiplicative (Fin 2 → F)) :=
          (Nat.card_congr ιE.toEquiv).symm
      _ = Nat.card (Fin 2 → F) := rfl
      _ = (Nat.card F) ^ 2 := by rw [Nat.card_fun, Nat.card_fin]
  have hQcard4 : Nat.card Q = 2 * (Nat.card F) ^ 4 := by
    rw [hQcard, hJcard, hEcard]
    ring
  exact ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO,
    hOA, hJO, hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO,
    hQdisj, hQCO, hQCt, hQcard4, κQ, hκQformula, hκQker, hκQsurj⟩

theorem exists_xSetting_of_standard_row
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
          S.X = Q ∧ S.t = t ∧ S.ι = ι ∧ S.lev = lev ∧ S.tor = tor := by
  classical
  dsimp only
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
  have hQ :=
    exists_characteristic_two_factor_of_standard_row hnonab hF A hA hZ e φ hφsurj
      hφproj hcyc t ht htC
  dsimp only at hQ
  obtain ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO,
    hOA, hJO, hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO,
    hQdisj, hQCO, hQCt, hQcard, κQ, hκQformula, hκQker, hκQsurj⟩ := hQ
  let ιE : Multiplicative (Fin 2 → F) ≃* E :=
    literalRowEquiv A e φ hφproj
  have hιE : ∀ v : Multiplicative (Fin 2 → F),
      ((ιE v : E) : G) = ρ (rowSLHom F v) := by
    intro v
    have h := literalRowEquiv_apply A e φ hφproj v
    simpa [ιE, ρ, rowSLHom] using h
  have hι : ∀ v : Fin 2 → F,
      ι v = ((ιE (Multiplicative.ofAdd v) : E) : G) := by
    intro v
    rw [hιE]
    simp [ι, rowSLHom]
  have hEJ : E ≤ J := le_sup_left
  have hJX : J ≤ X := hJQ.trans hQX
  have hXCE : X ≤ Subgroup.centralizer (E : Set G) := inf_le_right
  have hι_memE : ∀ v : Fin 2 → F, ι v ∈ E := by
    intro v
    rw [hι v]
    exact (ιE (Multiplicative.ofAdd v)).2
  have hι_add : ∀ u v : Fin 2 → F, ι (u + v) = ι u * ι v := by
    intro u v
    calc ι (u + v) = ((ιE (Multiplicative.ofAdd (u + v)) : E) : G) := hι (u + v)
      _ = ((ιE (Multiplicative.ofAdd u * Multiplicative.ofAdd v) : E) : G) := by
          rw [← ofAdd_add]
      _ = ((ιE (Multiplicative.ofAdd u) : E) : G) *
          ((ιE (Multiplicative.ofAdd v) : E) : G) :=
          congrArg (fun t : E => (t : G))
            (map_mul ιE (Multiplicative.ofAdd u) (Multiplicative.ofAdd v))
      _ = ι u * ι v := by rw [hι u, hι v]
  have hι_inj : Function.Injective ι := by
    intro u v huv
    have hE : ιE (Multiplicative.ofAdd u) = ιE (Multiplicative.ofAdd v) := by
      apply Subtype.ext
      simpa [hι u, hι v] using huv
    exact Multiplicative.ofAdd.injective (ιE.injective hE)
  have hEA : E ≤ A := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (φ y).2
  have hιQ : ∀ v : Fin 2 → F, ι v ∈ Q := fun v => hJQ (hEJ (hι_memE v))
  have hι_comm : ∀ v : Fin 2 → F, ∀ x ∈ Q, ι v * x = x * ι v := by
    intro v x hx
    have hxX : x ∈ X := hQX hx
    have hxCE : x ∈ Subgroup.centralizer (E : Set G) := hxX.2
    exact Subgroup.mem_centralizer_iff.mp hxCE (ι v) (hι_memE v)
  have htJ : t ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htQ : t ∈ Q := hJQ htJ
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht] at this
    simpa [pow_two] using this
  have htor_conj : ∀ μ : Fˣ, ∀ v : Multiplicative (Fin 2 → F),
      ρ (torSLZero F μ) * (ιE v : G) * (ρ (torSLZero F μ))⁻¹ =
        (ιE (Multiplicative.ofAdd
          (((μ : F) ^ 3) • Multiplicative.toAdd v)) : G) := by
    intro μ v
    rw [hιE v, hιE (Multiplicative.ofAdd _)]
    rw [← map_inv, ← map_mul, ← map_mul, torSLZero_conj_rowSLHom]
  have hlev_conj : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v : Multiplicative (Fin 2 → F),
      ρ (leviOne F B) * (ιE v : G) * (ρ (leviOne F B))⁻¹ =
        (ιE (Multiplicative.ofAdd
          ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) : G) := by
    intro B v
    rw [hιE v, hιE (Multiplicative.ofAdd _)]
    rw [← map_inv, ← map_mul, ← map_mul, leviOne_conj_rowSLHom]
  have htor_map_le : ∀ μ : Fˣ,
      E.map (MulAut.conj (ρ (torSLZero F μ))).toMonoidHom ≤ E := by
    intro μ x hx
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, hv⟩ := ιE.surjective ⟨e', he'⟩
    have hev : ((ιE v : E) : G) = e' := congrArg (fun t : E => (t : G)) hv
    rw [← hev]
    change ρ (torSLZero F μ) * (ιE v : G) * (ρ (torSLZero F μ))⁻¹ ∈ E
    rw [htor_conj μ v]
    exact (ιE _).2
  have htorN : ∀ μ : Fˣ, ρ (torSLZero F μ) ∈ Subgroup.normalizer (E : Set G) := by
    intro μ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · exact htor_map_le μ
    · intro x hx
      obtain ⟨v, hv⟩ := ιE.surjective ⟨x, hx⟩
      have hxval : ((ιE v : E) : G) = x := congrArg (fun t : E => (t : G)) hv
      rw [← hxval]
      have hx' : ρ (torSLZero F μ⁻¹) * (ιE v : G) *
          (ρ (torSLZero F μ⁻¹))⁻¹ ∈ E := by
        rw [htor_conj μ⁻¹ v]
        exact (ιE _).2
      refine Subgroup.mem_map.mpr ⟨ρ (torSLZero F μ⁻¹) * (ιE v : G) *
        (ρ (torSLZero F μ⁻¹))⁻¹, hx', ?_⟩
      rw [show ρ (torSLZero F μ⁻¹) = (ρ (torSLZero F μ))⁻¹ by simp [map_inv]]
      show (MulAut.conj (ρ (torSLZero F μ)))
        ((ρ (torSLZero F μ))⁻¹ * (ιE v : G) * (ρ (torSLZero F μ))⁻¹⁻¹) = (ιE v : G)
      rw [MulAut.conj_apply]
      simp only [inv_inv]
      group
  have hlev_map_le : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      E.map (MulAut.conj (ρ (leviOne F B))).toMonoidHom ≤ E := by
    intro B x hx
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, hv⟩ := ιE.surjective ⟨e', he'⟩
    have hev : ((ιE v : E) : G) = e' := congrArg (fun t : E => (t : G)) hv
    rw [← hev]
    change ρ (leviOne F B) * (ιE v : G) * (ρ (leviOne F B))⁻¹ ∈ E
    rw [hlev_conj B v]
    exact (ιE _).2
  have hlevN : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      ρ (leviOne F B) ∈ Subgroup.normalizer (E : Set G) := by
    intro B
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · exact hlev_map_le B
    · intro x hx
      obtain ⟨v, hv⟩ := ιE.surjective ⟨x, hx⟩
      have hxval : ((ιE v : E) : G) = x := congrArg (fun t : E => (t : G)) hv
      rw [← hxval]
      have hx' : ρ (leviOne F B⁻¹) * (ιE v : G) *
          (ρ (leviOne F B⁻¹))⁻¹ ∈ E := by
        rw [hlev_conj B⁻¹ v]
        exact (ιE _).2
      refine Subgroup.mem_map.mpr ⟨ρ (leviOne F B⁻¹) * (ιE v : G) *
        (ρ (leviOne F B⁻¹))⁻¹, hx', ?_⟩
      rw [show ρ (leviOne F B⁻¹) = (ρ (leviOne F B))⁻¹ by simp [map_inv]]
      show (MulAut.conj (ρ (leviOne F B)))
        ((ρ (leviOne F B))⁻¹ * (ιE v : G) * (ρ (leviOne F B))⁻¹⁻¹) = (ιE v : G)
      rw [MulAut.conj_apply]
      simp only [inv_inv]
      group
  have hmemN_of : ∀ g : G, g ∈ Subgroup.normalizer (E : Set G) → Commute g t → g ∈ N := by
    intro g hgE hgt
    change g ∈ Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hEmap : E.map (MulAut.conj g).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgE
    have htmap : (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers t := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change g * t * g⁻¹ = t
      rw [hgt.eq, mul_inv_cancel_right]
    calc (E ⊔ Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom
        = E.map (MulAut.conj g).toMonoidHom ⊔
            (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_sup]
      _ = E ⊔ Subgroup.zpowers t := by rw [hEmap, htmap]
  have hlevA : ∀ B, ρ (leviOne F B) ∈ A := fun B => (φ (leviOne F B)).2
  have htorA : ∀ μ, ρ (torSLZero F μ) ∈ A := fun μ => (φ (torSLZero F μ)).2
  have hlevN' : ∀ B, ρ (leviOne F B) ∈ N := fun B =>
    hmemN_of _ (hlevN B) (Subgroup.mem_centralizer_iff.mp htC _ (hlevA B))
  have htorN' : ∀ μ, ρ (torSLZero F μ) ∈ N := fun μ =>
    hmemN_of _ (htorN μ) (Subgroup.mem_centralizer_iff.mp htC _ (htorA μ))
  have hι_addS : ∀ u v, ι (u + v) = ι u * ι v := hι_add
  have hι_injS : Function.Injective ι := hι_inj
  have hι_memS : ∀ v, ι v ∈ Q := hιQ
  have hι_commS : ∀ v, ∀ x ∈ Q, ι v * x = x * ι v := hι_comm
  have ht_memS : t ∈ Q := htQ
  have ht2S : t * t = 1 := ht2
  have hcomm_memS : ∀ x ∈ Q, ∃ v : Fin 2 → F, t * x * t * x⁻¹ = ι v := by
    intro x hx
    let xQ : Q := ⟨x, hx⟩
    obtain ⟨v, hv⟩ := ιE.surjective (κQ xQ)
    refine ⟨Multiplicative.toAdd v, ?_⟩
    have hxκ : ((κQ xQ : E) : G) = (ιE v : G) := congrArg (fun t : E => (t : G)) hv.symm
    have hιv : ι (Multiplicative.toAdd v) = ((κQ xQ : E) : G) := by
      calc ι (Multiplicative.toAdd v) = (ιE v : G) := by
            simpa using hι (Multiplicative.toAdd v)
        _ = ((κQ xQ : E) : G) := hxκ.symm
    calc t * x * t * x⁻¹ = t * (x * t * x⁻¹) := by group
      _ = ((κQ xQ : E) : G) := (hκQformula xQ).symm
      _ = ι (Multiplicative.toAdd v) := hιv.symm
  have hcomm_surjS : ∀ v : Fin 2 → F, ∃ x ∈ Q, t * x * t * x⁻¹ = ι v := by
    intro v
    obtain ⟨xQ, hxQ⟩ := hκQsurj (ιE (Multiplicative.ofAdd v))
    refine ⟨xQ, xQ.2, ?_⟩
    have hxκ : ((κQ xQ : E) : G) = (ιE (Multiplicative.ofAdd v) : G) :=
      congrArg (fun t : E => (t : G)) hxQ
    calc t * (xQ : G) * t * (xQ : G)⁻¹ = t * ((xQ : G) * t * (xQ : G)⁻¹) := by group
      _ = ((κQ xQ : E) : G) := (hκQformula xQ).symm
      _ = (ιE (Multiplicative.ofAdd v) : G) := hxκ
      _ = ι v := (hι v).symm
  have hcomm_eq_oneS : ∀ x ∈ Q, t * x * t * x⁻¹ = 1 →
      ∃ v : Fin 2 → F, x = ι v ∨ x = ι v * t := by
    intro x hxQ hxone
    let xQ : Q := ⟨x, hxQ⟩
    have hκx1 : κQ xQ = 1 := by
      apply Subtype.ext
      rw [hκQformula xQ]
      have hxq : (xQ : G) = x := rfl
      rw [hxq]
      change t * (x * t * x⁻¹) = 1
      rw [← hxone]
      group
    have hxJ : x ∈ J := by
      have hxker : xQ ∈ κQ.ker := MonoidHom.mem_ker.mpr hκx1
      rw [hκQker] at hxker
      exact Subgroup.mem_subgroupOf.mp hxker
    let xJ : J := ⟨x, hxJ⟩
    have htCE : t ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_iff.mp htC e (hEA he)
    have htE : t ∈ Subgroup.normalizer (E : Set G) :=
      Subgroup.centralizer_le_normalizer (E : Set G) htCE
    have hJsub : E.subgroupOf J ⊔ (Subgroup.zpowers t).subgroupOf J = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      change (E ⊔ Subgroup.zpowers t).subgroupOf J = ⊤
      rw [Subgroup.subgroupOf_self]
    have hxmem : xJ ∈ E.subgroupOf J ⊔ (Subgroup.zpowers t).subgroupOf J := by
      rw [hJsub]; exact Subgroup.mem_top xJ
    have hEjnorm : (E.subgroupOf J).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htE))
    let : (E.subgroupOf J).Normal := hEjnorm
    obtain ⟨eJ, heJ, zJ, hzJ, hxz⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := E.subgroupOf J)
        (t := (Subgroup.zpowers t).subgroupOf J)).mp hxmem
    have heE : (eJ : G) ∈ E := Subgroup.mem_subgroupOf.mp heJ
    have hzT : (zJ : G) ∈ Subgroup.zpowers t := Subgroup.mem_subgroupOf.mp hzJ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzT
    have hzmod : (zJ : G) = t ^ (k % 2) := by
      calc (zJ : G) = t ^ k := hk.symm
        _ = t ^ (k % (orderOf t : ℤ)) := (zpow_mod_orderOf t k).symm
        _ = t ^ (k % 2) := by
            congr 1
            rw [ht]
            norm_num
    have hzcase : (zJ : G) = 1 ∨ (zJ : G) = t := by
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · left
        rw [hzmod, h0, zpow_zero]
      · right
        rw [hzmod, h1, zpow_one]
    obtain ⟨v, hv⟩ := ιE.surjective ⟨(eJ : G), heE⟩
    have hxv' : x = (eJ : G) * (zJ : G) := by
      have h := congrArg (fun t : J => (t : G)) hxz
      change (eJ : G) * (zJ : G) = x at h
      exact h.symm
    have heJv : (eJ : G) = ((ιE v : E) : G) :=
      (congrArg (fun t : E => (t : G)) hv).symm
    have hxv : x = ((ιE v : E) : G) * (zJ : G) := by
      rw [hxv', heJv]
    refine ⟨Multiplicative.toAdd v, ?_⟩
    have hιv : ι (Multiplicative.toAdd v) = ((ιE v : E) : G) := by
      simpa using hι (Multiplicative.toAdd v)
    rcases hzcase with hz1 | hzt
    · left
      rw [hxv, hz1, mul_one]
      exact hιv.symm
    · right
      rw [hxv, hzt]
      exact congrArg (fun y => y * t) hιv.symm
  have hlev_memS : ∀ B, ∀ x ∈ Q, lev B * x * (lev B)⁻¹ ∈ Q := by
    intro B x hx
    exact (Subgroup.mem_normalizer_iff.mp (hNQ (hlevN' B)) x).mp hx
  have hlev_tS : ∀ B, lev B * t = t * lev B := by
    intro B
    exact Subgroup.mem_centralizer_iff.mp htC _ (hlevA B)
  have hlev_ιS : ∀ B v, lev B * ι v * (lev B)⁻¹ = ι ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
    intro B v
    calc lev B * ι v * (lev B)⁻¹ =
        ρ (leviOne F B) * ((ιE (Multiplicative.ofAdd v) : E) : G) *
          (ρ (leviOne F B))⁻¹ := by rw [show lev B = ρ (leviOne F B) from rfl, hι v]
      _ = (ιE (Multiplicative.ofAdd
            ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd
              (Multiplicative.ofAdd v))) : G) := hlev_conj B (Multiplicative.ofAdd v)
      _ = (ιE (Multiplicative.ofAdd
            ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) : G) := by rw [toAdd_ofAdd]
      _ = ι ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := (hι _).symm
  have htor_memS : ∀ μ, ∀ x ∈ Q, tor μ * x * (tor μ)⁻¹ ∈ Q := by
    intro μ x hx
    exact (Subgroup.mem_normalizer_iff.mp (hNQ (htorN' μ)) x).mp hx
  have htor_tS : ∀ μ, tor μ * t = t * tor μ := by
    intro μ
    exact Subgroup.mem_centralizer_iff.mp htC _ (htorA μ)
  have htor_ιS : ∀ μ v, tor μ * ι v * (tor μ)⁻¹ = ι (((μ : F) ^ 3) • v) := by
    intro μ v
    calc tor μ * ι v * (tor μ)⁻¹ =
        ρ (torSLZero F μ) * ((ιE (Multiplicative.ofAdd v) : E) : G) *
          (ρ (torSLZero F μ))⁻¹ := by rw [show tor μ = ρ (torSLZero F μ) from rfl, hι v]
      _ = (ιE (Multiplicative.ofAdd
            (((μ : F) ^ 3) • Multiplicative.toAdd (Multiplicative.ofAdd v))) : G) :=
          htor_conj μ (Multiplicative.ofAdd v)
      _ = (ιE (Multiplicative.ofAdd (((μ : F) ^ 3) • v)) : G) := by rw [toAdd_ofAdd]
      _ = ι (((μ : F) ^ 3) • v) := (hι _).symm
  have htor_levS : ∀ μ B, tor μ * lev B = lev B * tor μ := by
    intro μ B
    have h := congrArg ρ (torSL_zero_mul_leviOne (K := F) μ B)
    simpa [tor, lev, torSL] using h
  let S : CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.XSetting G F :=
    { X := Q
      t := t
      ι := ι
      lev := lev
      tor := tor
      ι_add := hι_addS
      ι_injective := hι_injS
      ι_mem := hι_memS
      ι_comm := hι_commS
      t_mem := ht_memS
      t_mul_self := ht2S
      comm_mem := hcomm_memS
      comm_surj := hcomm_surjS
      comm_eq_one := hcomm_eq_oneS
      lev_mem := hlev_memS
      lev_t := hlev_tS
      lev_ι := hlev_ιS
      tor_mem := htor_memS
      tor_t := htor_tS
      tor_ι := htor_ιS
      tor_lev := htor_levS }
  refine ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO,
    hOA, hJO, hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO,
    hQdisj, hQCO, hQCt, hQcard, ?_⟩
  exact ⟨⟨κQ, hκQformula, hκQker, hκQsurj⟩, ⟨S, rfl, rfl, rfl, rfl, rfl⟩⟩

end CFSG.ComponentClassification.GS79bSec5
