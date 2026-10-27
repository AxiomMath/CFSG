module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCommute
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Layer
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoProduct
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common

namespace ProductG0Aux

variable {G : Type} [Group G] [Finite G]

theorem map_subgroupOf_diagonalHom {A B : Subgroup G} {t : G}
    (hA : ⁅A, Aᵍ[t]⁆ = ⊥) (hB : ⁅B, Bᵍ[t]⁆ = ⊥) (hAB : A ≤ B) :
    (A.subgroupOf B).map (diagonalHom B t hB) = (diagonalHom A t hA).range := by
  ext y
  constructor
  · rintro ⟨⟨a, _⟩, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨⟨a, hAB ha⟩, ha, rfl⟩

theorem range_diagonalHom_le_sup {A : Subgroup G} {t : G} (hA : ⁅A, Aᵍ[t]⁆ = ⊥) :
    (diagonalHom A t hA).range ≤ A ⊔ Aᵍ[t] := by
  rintro _ ⟨a, rfl⟩
  exact mul_mem (mem_sup_left a.2) (mem_sup_right (conj_mem_map_conj_inv t a.2))

theorem isPerfect_of_injective {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) [Group.IsPerfect f.range] : Group.IsPerfect H := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.2 hf, f.rangeRestrict_surjective⟩
  exact Group.IsPerfect.ofSurjective (f := (e.symm : f.range →* H)) e.symm.surjective

theorem eq_sup_of_range_eq {A T₁ T₂ : Subgroup G} {t : G} (hA : ⁅A, Aᵍ[t]⁆ = ⊥)
    (hinj : Function.Injective (diagonalHom A t hA)) (h₁ : T₁ ≤ A) (h₂ : T₂ ≤ A)
    (hr : (diagonalHom A t hA).range = (T₁.subgroupOf A).map (diagonalHom A t hA) ⊔
      (T₂.subgroupOf A).map (diagonalHom A t hA)) :
    A = T₁ ⊔ T₂ := by
  refine le_antisymm (fun a ha => ?_) (sup_le h₁ h₂)
  have hmem : diagonalHom A t hA ⟨a, ha⟩ ∈
      (T₁.subgroupOf A ⊔ T₂.subgroupOf A).map (diagonalHom A t hA) := by
    rw [Subgroup.map_sup, ← hr]
    exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨b, hb, hba⟩ := hmem
  have hb' := hinj hba
  subst hb'
  rw [← subgroupOf_sup h₁ h₂] at hb
  exact hb

theorem map_conj_inv_le {K : Subgroup G} {g : G} (hg : g ∈ K) {A : Subgroup G} (hA : A ≤ K) :
    Aᵍ[g] ≤ K := by
  rintro _ ⟨a, ha, rfl⟩
  change g⁻¹ * a * g⁻¹⁻¹ ∈ K
  exact mul_mem (mul_mem (inv_mem hg) (hA ha)) (by rw [inv_inv]; exact hg)

theorem map_conj_inv_le_of_centralizer {L : Subgroup G} {t : G}
    (htL : t ∈ centralizer (L : Set G)) : Lᵍ[t] ≤ L := by
  rintro _ ⟨l, hl, rfl⟩
  have h1 : l * t = t * l := mem_centralizer_iff.1 htL l hl
  change t⁻¹ * l * t⁻¹⁻¹ ∈ L
  rw [inv_inv, mul_assoc, h1, inv_mul_cancel_left]
  exact hl

end ProductG0Aux

namespace DiagonalPair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q f : ℕ} {t : G}

theorem commutator_sup_eq_bot {d : TrialityD4Data L q} (X : DiagonalPair d t)
    (htL : t ∈ centralizer (L : Set G)) (ht : t * t = 1) :
    ⁅X.A₁ ⊔ X.A₂, (X.A₁ ⊔ X.A₂)ᵍ[t]⁆ = ⊥ := by
  obtain ⟨h₁₂, h₂₁⟩ := I5_commute X ht htL
  have hA₁A₁ : X.A₁ ≤ centralizer (X.A₁ᵍ[t] : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 X.comm₁
  have hA₂A₂ : X.A₂ ≤ centralizer (X.A₂ᵍ[t] : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 X.comm₂
  have hA₁A₂ : X.A₁ ≤ centralizer (X.A₂ᵍ[t] : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 h₁₂
  have hA₂A₁ : X.A₂ ≤ centralizer (X.A₁ᵍ[t] : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact h₂₁
  rw [Subgroup.map_sup, commutator_eq_bot_iff_le_centralizer]
  refine sup_le ?_ ?_
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 hA₁A₁) (le_centralizer_iff.1 hA₁A₂)
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 hA₂A₁) (le_centralizer_iff.1 hA₂A₂)

theorem range_and_isPerfect (h : Setup G L f t) {d : TrialityD4Data L (2 ^ f)} (hf : 2 ≤ f)
    (X : DiagonalPair d t) :
    (diagonalHom (X.A₁ ⊔ X.A₂) t (X.commutator_sup_eq_bot h.htL h.t_mul_t)).range = L ∧
      Group.IsPerfect ↥(X.A₁ ⊔ X.A₂) := by
  obtain ⟨-, -, -, -, h5, h6₁, h6₂⟩ := I1_facts d hf
  refine ⟨?_, ?_⟩
  · set hcomm := X.commutator_sup_eq_bot h.htL h.t_mul_t
    have hmap₁ := ProductG0Aux.map_subgroupOf_diagonalHom X.comm₁ hcomm
      (le_sup_left : X.A₁ ≤ X.A₁ ⊔ X.A₂)
    have hmap₂ := ProductG0Aux.map_subgroupOf_diagonalHom X.comm₂ hcomm
      (le_sup_right : X.A₂ ≤ X.A₁ ⊔ X.A₂)
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self (X.A₁ ⊔ X.A₂),
      Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.map_sup, hmap₁, hmap₂,
      X.range₁, X.range₂, h5]
  · haveI : Group.IsPerfect ↥X.A₁ := by
      haveI : Group.IsPerfect (diagonalHom X.A₁ t X.comm₁).range := by
        rw [Subgroup.isPerfect_iff, X.range₁]
        exact h6₁
      exact ProductG0Aux.isPerfect_of_injective _ X.injective₁
    haveI : Group.IsPerfect ↥X.A₂ := by
      haveI : Group.IsPerfect (diagonalHom X.A₂ t X.comm₂).range := by
        rw [Subgroup.isPerfect_iff, X.range₂]
        exact h6₂
      exact ProductG0Aux.isPerfect_of_injective _ X.injective₂
    exact isPerfect_sup_of_isPerfect

end DiagonalPair

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace ProductG0Aux

theorem A₁_eq_sup {d : TrialityD4Data L (2 ^ f)} (hf : 2 ≤ f) (X : DiagonalPair d t)
    (htt : t * t = 1) (htL : t ∈ centralizer (L : Set G)) :
    X.A₁ = X.P₀ ⊔ X.P₀ᵍ[uG d] := by
  obtain ⟨⟨_, -, hT₁⟩, -, -, -⟩ := I2_transport X htt htL
  obtain ⟨-, hle, hdiag⟩ := hT₁ X.P₀ le_rfl
  obtain ⟨-, -, -, h4, -⟩ := I1_facts d hf
  have h1 : X.diag₁ X.P₀ = d.S.map L.subtype := X.rangeP
  rw [h1] at hdiag
  refine eq_sup_of_range_eq X.comm₁ X.injective₁ X.le₁ hle ?_
  rw [X.range₁]
  change cLV d = X.diag₁ X.P₀ ⊔ X.diag₁ (X.P₀ᵍ[uG d])
  rw [h1, hdiag]
  exact h4.1

theorem A₂_eq_sup {d : TrialityD4Data L (2 ^ f)} (hf : 2 ≤ f) (X : DiagonalPair d t)
    (htt : t * t = 1) (htL : t ∈ centralizer (L : Set G)) :
    X.A₂ = X.P₀ ⊔ X.P₀ᵍ[vG d] := by
  obtain ⟨-, ⟨_, -, hT₂⟩, -, -⟩ := I2_transport X htt htL
  obtain ⟨-, hle, hdiag⟩ := hT₂ X.P₀ le_rfl
  obtain ⟨-, -, -, h4, -⟩ := I1_facts d hf
  have h1 : X.diag₂ X.P₀ = d.S.map L.subtype := by
    rw [← X.rangeP]
    ext y
    constructor
    · rintro ⟨⟨p, _⟩, hpP, rfl⟩
      exact ⟨⟨p, X.le₁ hpP⟩, hpP, rfl⟩
    · rintro ⟨⟨p, _⟩, hpP, rfl⟩
      exact ⟨⟨p, X.le₂ hpP⟩, hpP, rfl⟩
  rw [h1] at hdiag
  refine eq_sup_of_range_eq X.comm₂ X.injective₂ X.le₂ hle ?_
  rw [X.range₂]
  change lvM d = X.diag₂ X.P₀ ⊔ X.diag₂ (X.P₀ᵍ[vG d])
  rw [h1, hdiag]
  exact h4.2

theorem sup_conj_eq_yamadaP_sup_L (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : 2 ≤ f) (X : DiagonalPair d t) (hP : yamadaP d t = X.P₀ ⊔ X.P₀ᵍ[t]) :
    (X.A₁ ⊔ X.A₂) ⊔ (X.A₁ ⊔ X.A₂)ᵍ[t] = yamadaP d t ⊔ L := by
  have htt := h.t_mul_t
  have hcomm := X.commutator_sup_eq_bot h.htL htt
  obtain ⟨hL, -⟩ := X.range_and_isPerfect h hf
  apply le_antisymm
  · set K : Subgroup G := yamadaP d t ⊔ L with hK
    have hPK : yamadaP d t ≤ K := le_sup_left
    have hLK : L ≤ K := le_sup_right
    have hPt : (yamadaP d t)ᵍ[t] ≤ yamadaP d t := by
      rw [hP, Subgroup.map_sup, map_conj_inv_map_conj_inv htt, sup_comm]
    have hKt : Kᵍ[t] ≤ K := by
      rw [hK, Subgroup.map_sup]
      exact sup_le_sup hPt (map_conj_inv_le_of_centralizer h.htL)
    have hP₀ : X.P₀ ≤ K := by
      rw [hP] at hPK
      exact le_sup_left.trans hPK
    have hA₁K : X.A₁ ≤ K := by
      rw [A₁_eq_sup hf X htt h.htL]
      exact sup_le hP₀ (map_conj_inv_le (hLK d.u.2) hP₀)
    have hA₂K : X.A₂ ≤ K := by
      rw [A₂_eq_sup hf X htt h.htL]
      exact sup_le hP₀ (map_conj_inv_le (hLK d.v.2) hP₀)
    refine sup_le (sup_le hA₁K hA₂K) ?_
    rw [Subgroup.map_sup]
    exact sup_le ((Subgroup.map_mono hA₁K).trans hKt) ((Subgroup.map_mono hA₂K).trans hKt)
  · refine sup_le ?_ ?_
    · rw [hP]
      exact sup_le (X.le₁.trans ((le_sup_left : X.A₁ ≤ X.A₁ ⊔ X.A₂).trans le_sup_left))
        (((Subgroup.map_mono X.le₁).trans (Subgroup.map_mono
          (le_sup_left : X.A₁ ≤ X.A₁ ⊔ X.A₂))).trans le_sup_right)
    · exact hL.symm.le.trans (range_diagonalHom_le_sup hcomm)

end ProductG0Aux

theorem J6_normalizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    (X : DiagonalPair d t) (hP : yamadaP d t = X.P₀ ⊔ X.P₀ᵍ[t]) :
    normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
      normalizer (((X.A₁ ⊔ X.A₂) ⊔ (X.A₁ ⊔ X.A₂)ᵍ[t] : Subgroup G) : Set G) := by
  rw [ProductG0Aux.sup_conj_eq_yamadaP_sup_L h d hp.two_le X hP, (h.yamada_5_3_3_all d).1]
  have htP : t ∈ normalizer (yamadaP d t : Set G) := h.t_mem_normalizer_yamadaP d hp.layer
  have htL : t ∈ normalizer (L : Set G) := h.centralizer_le_normalizer h.t_mem_centralizer
  have htPL : t ∈ normalizer ((yamadaP d t ⊔ L : Subgroup G) : Set G) :=
    Common.mem_normalizer_sup htP htL
  have hD₁ : yamadaD₁ d t ≤ yamadaP d t :=
    (le_inf ((h.yamadaD₁_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t))
      (Setup.yamadaD₁_le_centralizer_yamadaV₁ d) : yamadaD₁ d t ≤ yamadaD₅ d t).trans
      (yamadaD₅_le_yamadaP d t)
  refine sup_le ?_ ?_
  · rw [(h.yamada_5_6_1 d hp.layer).1]
    exact sup_le (hD₁.trans (le_sup_left.trans le_normalizer)) ((zpowers_le).2 htPL)
  · intro c hc
    exact Common.mem_normalizer_sup (ncs_le_normalizer_yamadaP h d hp.layer hc)
      (h.centralizer_le_normalizer hc.1)

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
