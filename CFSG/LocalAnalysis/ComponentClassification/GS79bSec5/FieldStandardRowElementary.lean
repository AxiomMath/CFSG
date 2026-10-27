module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowTwoGroup
public import CFSG.LocalAnalysis.EvenBN.LinearThree.WLocalElementary

public noncomputable section

open Matrix Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_elementary_extension_of_standard_row
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
              Nat.card W' = (Nat.card F) ^ 4 → W' = W := by
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
  have hq8 : 8 ≤ Nat.card F := by omega
  have hQ :=
    exists_xSetting_of_standard_row hnonab hF A hA hZ e φ hφsurj hφproj hcyc t ht htC
  dsimp only at hQ
  obtain ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO,
    hOA, hJO, hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO,
    hQdisj, hQCO, hQCt, hQcard, κQpart, hSpart⟩ := hQ
  obtain ⟨κQ, hκQformula, hκQker, hκQsurj⟩ := κQpart
  let S : CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.XSetting G F := Classical.choose hSpart
  obtain ⟨hSX, hSt, hSι, hSlev, hStor⟩ := Classical.choose_spec hSpart
  have hSι' : S.ι = ι := hSι
  have hSlev' : S.lev = lev := hSlev
  have hStor' : S.tor = tor := hStor
  obtain ⟨W, hW_le_SX, hWcomm, hWsq, hWcard, hιW, htW, hWcoset, _, hWfix, hWcomm_surj, hWuniq⟩ := S.exists_W hq8
  have hιW' : ∀ v : Fin 2 → F, ι v ∈ W := fun v => hSι' ▸ hιW v
  have hWQ : W ≤ Q := by
    rw [← hSX]
    exact hW_le_SX
  have hWuniqQ : ∀ W' : Subgroup G, W' ≤ Q →
      (∀ a ∈ W', ∀ b ∈ W', a * b = b * a) →
      Nat.card W' = (Nat.card F) ^ 4 → W' = W := by
    intro W' hW'Q hcomm' hcard'
    exact hWuniq W' (by rw [hSX]; exact hW'Q) hcomm' hcard'
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
  have hι_memE : ∀ v : Fin 2 → F, ι v ∈ E := by
    intro v
    rw [hι v]
    exact (ιE (Multiplicative.ofAdd v)).2
  have hEcard : Nat.card E = (Nat.card F) ^ 2 := by
    calc Nat.card E = Nat.card (Multiplicative (Fin 2 → F)) :=
          (Nat.card_congr ιE.toEquiv).symm
      _ = Nat.card (Fin 2 → F) := rfl
      _ = (Nat.card F) ^ 2 := by rw [Nat.card_fun, Nat.card_fin]
  have hEA : E ≤ A := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (φ y).2
  have hEW : E ≤ W := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← rowSLHom_range] at hy
    obtain ⟨v, rfl⟩ := hy
    have hxv : ρ (rowSLHom F v) = ι (Multiplicative.toAdd v) := by
      rw [hι (Multiplicative.toAdd v)]
      simpa using (hιE v).symm
    rw [hxv]
    exact hιW' (Multiplicative.toAdd v)
  have hEneW : E ≠ W := by
    intro hEW'
    have hc : Nat.card E = Nat.card W := by rw [hEW']
    rw [hEcard, hWcard] at hc
    have hlt : (Nat.card F) ^ 2 < (Nat.card F) ^ 4 := by
      have hq2 : 2 ≤ Nat.card F := by omega
      have h1 : 1 < (Nat.card F) ^ 2 := by nlinarith
      calc (Nat.card F) ^ 2 = (Nat.card F) ^ 2 * 1 := by rw [mul_one]
        _ < (Nat.card F) ^ 2 * (Nat.card F) ^ 2 :=
            Nat.mul_lt_mul_of_pos_left h1 (pow_pos (by omega : 0 < Nat.card F) 2)
        _ = (Nat.card F) ^ 4 := by ring
    exact (ne_of_lt hlt) hc
  have hEltW : E < W := lt_of_le_of_ne hEW hEneW
  have hWelem : CFSG.Open.IsElemAbelian 2 W := by
    refine ⟨isMulCommutative_iff.mpr (fun a b => Subtype.ext ?_), ?_⟩
    · exact hWcomm a a.2 b b.2
    · intro x hx
      simpa [pow_two] using hWsq x hx
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht] at this
    simpa [pow_two] using this
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hQsup : Q = W ⊔ Subgroup.zpowers t := by
    apply le_antisymm
    · intro x hx
      have hxcoset : x ∈ W ∨ x * t ∈ W := by
        rcases hWcoset x (by rw [hSX]; exact hx) with h | h
        · exact Or.inl h
        · exact Or.inr (hSt ▸ h)
      rcases hxcoset with hxW | hxWt
      · exact Subgroup.mem_sup_left hxW
      · have hxt : x = (x * t) * t := by rw [mul_assoc, ht2, mul_one]
        rw [hxt]
        exact mul_mem (Subgroup.mem_sup_left hxWt)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    · exact sup_le hWQ (Subgroup.zpowers_le.mpr (hJQ (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers t))))
  have hWcosetQ : ∀ x ∈ Q, x ∈ W ∨ x * t ∈ W := by
    intro x hx
    rcases hWcoset x (by rw [hSX]; exact hx) with h | h
    · exact Or.inl h
    · exact Or.inr (hSt ▸ h)
  have hE_Ct : E ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp htC x (hEA hx)).symm
  have hWfixE : W ⊓ Subgroup.centralizer ({t} : Set G) = E := by
    apply le_antisymm
    · intro x hx
      have hxW : x ∈ W := hx.1
      have hxC : x ∈ Subgroup.centralizer ({t} : Set G) := hx.2
      have hxt : S.t * x = x * S.t := by
        have h : t * x = x * t :=
          Subgroup.mem_centralizer_iff.mp hxC t (Set.mem_singleton t)
        calc S.t * x = t * x := by rw [hSt]
          _ = x * t := h
          _ = x * S.t := by rw [hSt]
      have hEq : S.t * x * S.t * x⁻¹ = 1 := by
        calc S.t * x * S.t * x⁻¹ = (S.t * x) * S.t * x⁻¹ := by group
          _ = (x * S.t) * S.t * x⁻¹ := by rw [hxt]
          _ = x * (S.t * S.t) * x⁻¹ := by group
          _ = x * 1 * x⁻¹ := by rw [S.t_mul_self]
          _ = 1 := by group
      obtain ⟨v, hv⟩ := hWfix x hxW hEq
      rw [← hv, hSι]
      exact hι_memE v
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hEW hx, hE_Ct hx⟩
  have hcomm_t : ⁅W, Subgroup.zpowers t⁆ = E := by
    apply le_antisymm
    · refine Subgroup.commutator_le.mpr ?_
      intro x hxW z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hk : t ^ k = 1 ∨ t ^ k = t := by
        have h2 : ((orderOf t : ℕ) : ℤ) = 2 := by exact_mod_cast ht
        have hmod := zpow_mod_orderOf t k
        rw [h2] at hmod
        rcases Int.emod_two_eq_zero_or_one k with h0 | h1
        · left
          rw [← hmod, h0, zpow_zero]
        · right
          rw [← hmod, h1, zpow_one]
      rcases hk with hk1 | hkt
      · rw [hk1]
        simp
      · rw [hkt]
        have hxSX : x ∈ S.X := hW_le_SX hxW
        obtain ⟨v, hv⟩ := S.comm_mem x hxSX
        have hmem : S.t * x * S.t * x⁻¹ ∈ E := by
          rw [hv, hSι]
          exact hι_memE v
        have hcomm_eq : ⁅x, t⁆ = (S.t * x * S.t * x⁻¹)⁻¹ := by
          have h : ⁅x, t⁆ = (t * x * t * x⁻¹)⁻¹ := by
            calc ⁅x, t⁆ = x * t * x⁻¹ * t⁻¹ := commutatorElement_def x t
              _ = x * t * x⁻¹ * t := by rw [ht_inv]
              _ = (t * x * t * x⁻¹)⁻¹ := by
                  rw [show (t * x * t * x⁻¹)⁻¹ = x * t⁻¹ * x⁻¹ * t⁻¹ by group,
                    ht_inv]
          rw [hSt]
          exact h
        rw [hcomm_eq]
        exact inv_mem hmem
    · intro e he
      obtain ⟨y, hy⟩ := ιE.surjective ⟨e, he⟩
      have hyval : e = ι (Multiplicative.toAdd y) := by
        rw [hι (Multiplicative.toAdd y)]
        exact (congrArg (fun z : E => (z : G)) hy).symm
      rw [hyval]
      obtain ⟨x, hxW, hxeq⟩ := hWcomm_surj (Multiplicative.toAdd y)
      have hmem : ⁅x, t⁆ ∈ ⁅W, Subgroup.zpowers t⁆ :=
        Subgroup.commutator_mem_commutator hxW (Subgroup.mem_zpowers t)
      have hιv : ι (Multiplicative.toAdd y) = ⁅x, t⁆⁻¹ := by
        have hcomm_eq : ⁅x, t⁆ = (S.t * x * S.t * x⁻¹)⁻¹ := by
          have h : ⁅x, t⁆ = (t * x * t * x⁻¹)⁻¹ := by
            calc ⁅x, t⁆ = x * t * x⁻¹ * t⁻¹ := commutatorElement_def x t
              _ = x * t * x⁻¹ * t := by rw [ht_inv]
              _ = (t * x * t * x⁻¹)⁻¹ := by
                  rw [show (t * x * t * x⁻¹)⁻¹ = x * t⁻¹ * x⁻¹ * t⁻¹ by group,
                    ht_inv]
          rw [hSt]
          exact h
        have hxeq' : S.t * x * S.t * x⁻¹ = ι (Multiplicative.toAdd y) := hSι' ▸ hxeq
        rw [hcomm_eq, hxeq', inv_inv]
      rw [hιv]
      exact inv_mem hmem
  have hWCO : W ≤ Subgroup.centralizer (O : Set G) := hWQ.trans hQCO
  have hnormalizer_of_map_eq : ∀ u : G, (∀ x ∈ W, u * x * u⁻¹ ∈ Q) →
      u ∈ Subgroup.normalizer (W : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : W.map (MulAut.conj u).toMonoidHom ≤ Q := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact hu y hy
    have hcomm' : ∀ a ∈ W.map (MulAut.conj u).toMonoidHom,
        ∀ b ∈ W.map (MulAut.conj u).toMonoidHom, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
      change u * a0 * u⁻¹ * (u * b0 * u⁻¹) = u * b0 * u⁻¹ * (u * a0 * u⁻¹)
      calc u * a0 * u⁻¹ * (u * b0 * u⁻¹) = u * (a0 * b0) * u⁻¹ := by group
        _ = u * (b0 * a0) * u⁻¹ := by rw [hWcomm a0 ha0 b0 hb0]
        _ = u * b0 * u⁻¹ * (u * a0 * u⁻¹) := by group
    have hcard' : Nat.card (W.map (MulAut.conj u).toMonoidHom) =
        (Nat.card F) ^ 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj u).injective, hWcard]
    exact hWuniqQ _ hle hcomm' hcard'
  have hNW : N ≤ Subgroup.normalizer (W : Set G) := by
    intro n hn
    have hnQ : n ∈ Subgroup.normalizer (Q : Set G) := hNQ hn
    refine hnormalizer_of_map_eq n ?_
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp hnQ x).mp (hWQ hx)
  have hlevN : lev.range ≤ Subgroup.normalizer (W : Set G) := by
    intro u hu
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hu
    refine hnormalizer_of_map_eq (lev B) ?_
    intro x hx
    have hmem := S.lev_mem B x (hW_le_SX hx)
    rw [hSlev', hSX] at hmem
    exact hmem
  have htorN : tor.range ≤ Subgroup.normalizer (W : Set G) := by
    intro u hu
    obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hu
    refine hnormalizer_of_map_eq (tor l) ?_
    intro x hx
    have hmem := S.tor_mem l x (hW_le_SX hx)
    rw [hStor', hSX] at hmem
    exact hmem
  have hWchar : (W.subgroupOf Q).Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro α
    let W' : Subgroup G := ((W.subgroupOf Q).map α.toMonoidHom).map Q.subtype
    have hW'le : W' ≤ Q := Subgroup.map_subtype_le _
    have hWsub_comm : ∀ a ∈ W.subgroupOf Q, ∀ b ∈ W.subgroupOf Q, a * b = b * a := by
      intro a ha b hb
      exact Subtype.ext (hWcomm a (Subgroup.mem_subgroupOf.mp ha) b
        (Subgroup.mem_subgroupOf.mp hb))
    have hW'comm : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a := by
      intro a ha b hb
      obtain ⟨aQ, haQ, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨bQ, hbQ, rfl⟩ := Subgroup.mem_map.mp hb
      obtain ⟨aW, haW, rfl⟩ := Subgroup.mem_map.mp haQ
      obtain ⟨bW, hbW, rfl⟩ := Subgroup.mem_map.mp hbQ
      calc Q.subtype (α aW) * Q.subtype (α bW)
          = Q.subtype (α aW * α bW) := by rw [map_mul]
        _ = Q.subtype (α (aW * bW)) := by rw [← map_mul]
        _ = Q.subtype (α (bW * aW)) := by rw [hWsub_comm aW haW bW hbW]
        _ = Q.subtype (α bW * α aW) := by rw [map_mul]
        _ = Q.subtype (α bW) * Q.subtype (α aW) := by rw [map_mul]
    have hW'card : Nat.card W' = (Nat.card F) ^ 4 := by
      dsimp only [W']
      rw [Subgroup.card_map_of_injective Q.subtype_injective,
        Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ).toEquiv, hWcard]
    have huniq := hWuniqQ W' hW'le hW'comm hW'card
    have hWqmap : (W.subgroupOf Q).map Q.subtype = W :=
      Subgroup.map_subgroupOf_eq_of_le hWQ
    have hEq : ((W.subgroupOf Q).map α.toMonoidHom).map Q.subtype =
        (W.subgroupOf Q).map Q.subtype := by
      change W' = (W.subgroupOf Q).map Q.subtype
      rw [huniq, hWqmap]
    exact (Subgroup.map_injective (f := Q.subtype) Q.subtype_injective) hEq
  obtain ⟨lam, hlam⟩ :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.exists_unit_cube_ne_one (K := F) hq8
  let B : Matrix.SpecialLinearGroup (Fin 2) F :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat lam
  let u : G := S.lev B
  have hu_range : u ∈ lev.range := by
    refine MonoidHom.mem_range.mpr ⟨B, ?_⟩
    rw [← hSlev']
  have huN : u ∈ Subgroup.normalizer (W : Set G) := hlevN hu_range
  have hfreeW : ∀ w ∈ W, u * w * u⁻¹ = w → w = 1 := by
    intro w hw hfix
    have hwSX : w ∈ S.X := hW_le_SX hw
    have hψeq : S.ψ w = (B : Matrix (Fin 2) (Fin 2) F) *ᵥ S.ψ w := by
      calc S.ψ w = S.ψ (u * w * u⁻¹) := by rw [hfix]
        _ = (B : Matrix (Fin 2) (Fin 2) F) *ᵥ S.ψ w := by
            simpa [u] using S.ψ_lev hwSX B
    have h0 : (lam : F) * S.ψ w 0 = S.ψ w 0 := by
      have h := congrFun hψeq 0
      rw [show B = CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat lam from rfl,
        CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat_mulVec] at h
      exact h.symm
    have h1 : (((lam⁻¹ : Fˣ) : F)) * S.ψ w 1 = S.ψ w 1 := by
      have h := congrFun hψeq 1
      rw [show B = CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat lam from rfl,
        CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat_mulVec] at h
      exact h.symm
    have hψzero : S.ψ w = 0 := by
      funext i
      fin_cases i
      · have hmul : ((lam : F) - 1) * S.ψ w 0 = 0 := by linear_combination h0
        have hne : (lam : F) - 1 ≠ 0 := by
          apply sub_ne_zero.mpr
          intro h1
          exact hlam (by rw [h1]; norm_num)
        exact (mul_eq_zero.mp hmul).resolve_left hne
      · have hmul : ((((lam⁻¹ : Fˣ) : F)) - 1) * S.ψ w 1 = 0 := by
          linear_combination h1
        have hne : ((((lam⁻¹ : Fˣ) : F)) - 1) ≠ 0 := by
          apply sub_ne_zero.mpr
          intro h1
          apply hlam
          have hmul' : (lam : F) * (((lam⁻¹ : Fˣ) : F)) = 1 := by simp
          rw [h1, mul_one] at hmul'
          rw [hmul']
          norm_num
        exact (mul_eq_zero.mp hmul).resolve_left hne
    have hwt : S.t * w * S.t * w⁻¹ = 1 := (S.ψ_eq_zero_iff hwSX).mp hψzero
    obtain ⟨v, hv⟩ := hWfix w hw hwt
    have hBv : (B : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
      have h := S.lev_ι B v
      rw [show S.lev B = u from rfl, show S.ι v = w from hv, hfix] at h
      exact S.ι_injective (h.symm.trans hv.symm)
    have hv0 : v = 0 := by
      have h0 : (lam : F) * v 0 = v 0 := by
        have h := congrFun hBv 0
        rw [show B = CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat lam from rfl,
          CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat_mulVec] at h
        exact h
      have h1 : (((lam⁻¹ : Fˣ) : F)) * v 1 = v 1 := by
        have h := congrFun hBv 1
        rw [show B = CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat lam from rfl,
          CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal.dmat_mulVec] at h
        exact h
      funext i
      fin_cases i
      · have hmul : ((lam : F) - 1) * v 0 = 0 := by linear_combination h0
        have hne : (lam : F) - 1 ≠ 0 := by
          apply sub_ne_zero.mpr
          intro h1
          exact hlam (by rw [h1]; norm_num)
        exact (mul_eq_zero.mp hmul).resolve_left hne
      · have hmul : ((((lam⁻¹ : Fˣ) : F)) - 1) * v 1 = 0 := by
          linear_combination h1
        have hne : ((((lam⁻¹ : Fˣ) : F)) - 1) ≠ 0 := by
          apply sub_ne_zero.mpr
          intro h1
          apply hlam
          have hmul' : (lam : F) * (((lam⁻¹ : Fˣ) : F)) = 1 := by simp
          rw [h1, mul_one] at hmul'
          rw [hmul']
          norm_num
        exact (mul_eq_zero.mp hmul).resolve_left hne
    rw [← hv, hv0, S.ι_zero]
  have hcomm_u : ⁅W, Subgroup.zpowers u⁆ = W :=
    CFSG.commutator_zpowers_eq_of_fixedPointFree W u hWcomm huN hfreeW
  have hcomm_lev : ⁅W, lev.range⁆ = W := by
    apply le_antisymm
    · refine Subgroup.commutator_le.mpr ?_
      intro x hxW y hy
      have hyN : y ∈ Subgroup.normalizer (W : Set G) := hlevN hy
      have hconj : y * x⁻¹ * y⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (W.inv_mem hxW)
      rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
      exact W.mul_mem hxW hconj
    · calc W = ⁅W, Subgroup.zpowers u⁆ := hcomm_u.symm
        _ ≤ ⁅W, lev.range⁆ :=
            Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hu_range)
  have htW' : t ∉ W := hSt ▸ htW
  exact ⟨hJea, hJcard, hJsylow, hJcent, hNE, O, hOC, hOodd, hOchar, hNO,
    hOA, hJO, hJOdisj, Q, hQX, hQ2, hJQ, hQsylow, hQuniq, hQchar, hNQ, hQO,
    hQdisj, hQCO, hQCt, hQcard, ⟨κQ, hκQformula, hκQker, hκQsurj⟩, S, hSX,
    hSt, hSι, hSlev, hStor, W, hWQ, hWelem, hWcard, hEltW, htW', hQsup,
    hWcosetQ, hWchar, hNW, hWfixE, hcomm_t, hWCO, hlevN, htorN, hcomm_lev,
    hWuniqQ⟩

end CFSG.ComponentClassification.GS79bSec5

end
