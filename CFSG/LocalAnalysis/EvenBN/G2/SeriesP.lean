module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalNDefs
public import CFSG.LocalAnalysis.EvenBN.G2.LocalQ55
public import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductDefs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso)
open scoped commutatorElement Pointwise MatrixGroups

namespace SeriesPAux

section Generic

variable {G : Type*} [Group G]

theorem mul_self_eq_one_of_mem {A : Subgroup G} [CFSG.IsElementaryAbelian 2 A] {x : G}
    (hx : x ∈ A) : x * x = 1 := by
  rw [← sq]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hx

theorem elemModulo_of_isElementaryAbelian {N A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 A) :
    ElemModulo N A := fun x hx y hy => by
  have := hA
  have hxy : x * y = y * x := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  refine ⟨?_, ?_⟩
  · rw [mul_self_eq_one_of_mem (A := A) hx]
    exact one_mem _
  · rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = 1 by rw [hxy]; group]
    exact one_mem _

theorem normal_subgroupOf_of_elemModulo {N A : Subgroup G} (hNA : N ≤ A) (h : ElemModulo N A) :
    (N.subgroupOf A).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_of_elemModulo hNA h)

theorem isElementaryAbelian_quotient_of_elemModulo {N A : Subgroup G} (h : ElemModulo N A)
    [(N.subgroupOf A).Normal] : CFSG.IsElementaryAbelian 2 (A ⧸ N.subgroupOf A) := by
  refine
    { is_comm := ⟨fun a b => ?_⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_ }
  · obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    change (x * y)⁻¹ * (y * x) ∈ N
    have h1 := (h y⁻¹ (inv_mem hy) x⁻¹ (inv_mem hx)).2
    have e : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact h1
  · obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    change x ^ 2 ∈ N
    rw [sq]
    exact (h x hx x hx).1

theorem mul_self_eq_one_of_mem_map_conj {E : Subgroup G} (g : G) (hE : ∀ x ∈ E, x * x = 1) :
    ∀ y ∈ E.map (MulAut.conj g).toMonoidHom, y * y = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  change g * x * g⁻¹ * (g * x * g⁻¹) = 1
  calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    _ = 1 := by rw [hE x hx]; group

theorem le_closure_involutions {P E : Subgroup G} (hEP : E ≤ P) (hE : ∀ x ∈ E, x * x = 1) :
    E ≤ closure {x | x ∈ P ∧ orderOf x = 2} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  · exact subset_closure ⟨hEP hx, orderOf_eq_prime (by rw [sq]; exact hE x hx) hx1⟩

end Generic

end SeriesPAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


@[expose] noncomputable def yamadaSeries (d : G2Data L K) (t : G) : Fin 7 → Subgroup G :=
  ![⊥, yamadaU₁ d t, yamadaY₂ d t, yamadaW₃ d t, yamadaF₅ d t, yamadaM₆ d t, yamadaP d t]

private theorem t_mem_normalizer_S (h : Setup G L f t) (d : G2Data L K) :
    t ∈ normalizer (d.S : Set G) :=
  Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun s hs => mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs))

private theorem yamadaP_inf_centralizer_eq_S (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ⊓ centralizer ({t} : Set G) = d.S := by
  have hSP : d.S ≤ yamadaP d t := by
    obtain ⟨-, -, -, -, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
    exact (S_le_yamadaS₆ d t).trans hS₆P
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨-, -, htP⟩, -⟩ := h.yamada_5_51 hW d hK hQ
  refine le_antisymm (fun x hx => ?_) (le_inf hSP (h.S_le_centralizer d))
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxR : x ∈ yamadaR d t := by
    rw [← (h.yamada_5_49_1 hW d hK hQ).2.2]
    exact Subgroup.mem_inf.2 ⟨hPR₈ hxP, hxC⟩
  rw [yamadaR, h.centralizer_L_inf] at hxR
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (t_mem_normalizer_S h d)).1 hxR with
      hs | ⟨s, hs, e⟩
  · exact hs
  · exfalso
    apply htP
    have := mul_mem (inv_mem (hSP hs)) hxP
    rwa [e, inv_mul_cancel_left] at this

private theorem yamadaM₆_inf_centralizer_eq_M (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊓ centralizer ({t} : Set G) = d.M := by
  obtain ⟨-, -, -, -, -, -, -, -, hMS, hSL⟩ := d.inclusions
  refine le_antisymm (fun x hx => ?_) (le_inf (h.M_le_yamadaM₆ hW d hK hQ)
    ((hMS.trans hSL).trans h.L_le_centralizer))
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxS : x ∈ d.S := by
    rw [← yamadaP_inf_centralizer_eq_S hW h d hK hQ]
    exact Subgroup.mem_inf.2 ⟨h.yamadaM₆_le_yamadaP hW d hK hQ hxM, hxC⟩
  rw [← h.yamadaL₆_inf_S hW d hK hQ]
  exact Subgroup.mem_inf.2 ⟨h.yamadaM₆_le_yamadaL₆ hW d hK hQ hxM, hxS⟩

private theorem yamadaW₃_inf_centralizer_eq_W (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ⊓ centralizer ({t} : Set G) = d.W := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  obtain ⟨hW₃V₃, -, -, hW₂W₃, htW₃, -, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, hV₃E₃, -, hV₃R₂, -, -, -, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  have hWC : d.W ≤ centralizer ({t} : Set G) := (d.image_le _).trans h.L_le_centralizer
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := by
    rw [(h.yamada_5_27_2 hW d hK hD).1.1]
    exact le_sup_left
  have hWW₂ : d.W ≤ yamadaW₂ d t := le_sup_left
  refine le_antisymm (fun x hx => ?_) (le_inf (hWW₂.trans hW₂W₃) hWC)
  obtain ⟨hxW₃, hxt⟩ := Subgroup.mem_inf.1 hx
  have hxR₃ : x ∈ yamadaR₃ d t :=
    (hV₃E₃.trans (inf_le_left.trans le_sup_left)) (hW₃V₃ hxW₃)
  have hxR : x ∈ yamadaR d t := by
    rw [← (h.yamada_5_27_1 hW d hK hD).2.2]
    exact Subgroup.mem_inf.2 ⟨hR₃R₅ hxR₃, hxt⟩
  have hxR₂ : x ∈ yamadaR₂ d t := (h.yamadaR₂_inf_centralizer d hK).1 hxR
  have hxV₂ : x ∈ yamadaV₂ d t := by
    rw [← hV₃R₂]
    exact Subgroup.mem_inf.2 ⟨hW₃V₃ hxW₃, hxR₂⟩
  have hxW₂ : x ∈ yamadaW₂ d t := by
    rcases (mem_sup_zpowers_iff_of htt (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1 hxV₂ with
      h1 | ⟨a, ha, rfl⟩
    · exact h1
    · exfalso
      refine htW₃ ?_
      have := mul_mem (inv_mem (hW₂W₃ ha)) hxW₃
      rwa [inv_mul_cancel_left] at this
  rw [← h.yamadaW₂_inf_centralizer d hK hD]
  exact Subgroup.mem_inf.2 ⟨hxW₂, hxt⟩

theorem yamada_series_inf_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaU₁ d t ⊓ centralizer ({t} : Set G) = d.U ∧
      yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y ∧
      yamadaW₃ d t ⊓ centralizer ({t} : Set G) = d.W ∧
      yamadaF₅ d t ⊓ centralizer ({t} : Set G) = d.F ∧
      yamadaM₆ d t ⊓ centralizer ({t} : Set G) = d.M ∧
      yamadaP d t ⊓ centralizer ({t} : Set G) = d.S := by
  have hD := hQ.doubling
  have hPC := yamadaP_inf_centralizer_eq_S hW h d hK hQ
  refine ⟨hQ.doubling.yamada_5_10_1.2.1, h.yamadaY₂_inf_centralizer d hK hD,
    yamadaW₃_inf_centralizer_eq_W hW h d hK hQ, ?_,
    yamadaM₆_inf_centralizer_eq_M hW h d hK hQ, hPC⟩
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -, -⟩ := d.inclusions
  refine le_antisymm (fun x hx => ?_) (le_inf (Q44.F_le_F₅ d t)
    ((hFD.trans hDS).trans (h.S_le_centralizer d)))
  obtain ⟨hxF₅, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxS : x ∈ d.S := by
    rw [← hPC]
    exact Subgroup.mem_inf.2 ⟨(h.yamadaF₅_le_yamadaM₆ hW d hK hQ).trans
      (h.yamadaM₆_le_yamadaP hW d hK hQ) hxF₅, hxC⟩
  rw [← (yamadaS₅_eq_sup hW h d hK hQ).2.1]
  exact Subgroup.mem_inf.2 ⟨hxS, hxF₅⟩

theorem yamada_series_card (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaU₁ d t) = Nat.card K ^ 2 ∧ Nat.card (yamadaY₂ d t) = Nat.card K ^ 4 ∧
      Nat.card (yamadaW₃ d t) = Nat.card K ^ 6 ∧ Nat.card (yamadaF₅ d t) = Nat.card K ^ 8 ∧
      Nat.card (yamadaM₆ d t) = Nat.card K ^ 10 ∧ Nat.card (yamadaP d t) = Nat.card K ^ 12 := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hF₅c, -, -, hM₆c, -, -⟩ := h.card_yamada_five_six hW d hK hQ
  exact ⟨hQ.doubling.yamada_5_10_1.2.2, h.card_yamadaY₂ d hK hD,
    (h.yamada_5_33_3_uniform hW d hK hQ.doubling).2.1, hF₅c, hM₆c, h.card_yamadaP hW d hK hQ⟩

private theorem series_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaU₁ d t ≤ yamadaY₂ d t ∧ yamadaY₂ d t ≤ yamadaW₃ d t ∧ yamadaW₃ d t ≤ yamadaF₅ d t ∧
      yamadaF₅ d t ≤ yamadaM₆ d t ∧ yamadaM₆ d t ≤ yamadaP d t :=
  ⟨yamadaU₁_le_yamadaY₂ d t, (h.yamada_5_46_1 hW d hK hQ).1, Q44.W₃_le_F₅ d t,
    h.yamadaF₅_le_yamadaM₆ hW d hK hQ, h.yamadaM₆_le_yamadaP hW d hK hQ⟩

private theorem series_normalizes (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaU₁ d t : Set G) ∧ t ∈ normalizer (yamadaY₂ d t : Set G) ∧
      t ∈ normalizer (yamadaW₃ d t : Set G) ∧ t ∈ normalizer (yamadaF₅ d t : Set G) ∧
      t ∈ normalizer (yamadaM₆ d t : Set G) ∧ t ∈ normalizer (yamadaP d t : Set G) := by
  have hD := hQ.doubling
  exact ⟨(h.t_mem_normalizer_yamadaU₁ d hK hD).1,
    h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD
      (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))),
    Q44.t_mem_normalizer_W₃ hW h d hK hD, (h.yamada_5_37_2 hW d hK hQ).2.2.2.2.2.1,
    (h.yamada_5_44_1 hW d hK hQ).1.2.1, (h.yamada_5_51 hW d hK hQ).1.2.1⟩

private theorem series_elemModulo (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ElemModulo ⊥ (yamadaU₁ d t) ∧ ElemModulo (yamadaU₁ d t) (yamadaY₂ d t) ∧
      ElemModulo (yamadaY₂ d t) (yamadaW₃ d t) ∧ ElemModulo (yamadaW₃ d t) (yamadaF₅ d t) ∧
      ElemModulo (yamadaF₅ d t) (yamadaM₆ d t) ∧ ElemModulo (yamadaM₆ d t) (yamadaP d t) := by
  obtain ⟨hU₁Y₂, hY₂W₃, -, hF₅M₆, hM₆P⟩ := series_le hW h d hK hQ
  have hWel := (h.yamada_5_33_3_uniform hW d hK hQ.doubling).1
  obtain ⟨-, -, -, -, hF₅el, -⟩ := h.yamada_5_46_1 hW d hK hQ
  obtain ⟨-, -, -, -, -, -, hPel⟩ := h.yamada_5_57_2 hW d hK hQ
  exact ⟨(SeriesPAux.elemModulo_of_isElementaryAbelian hWel).anti (hU₁Y₂.trans hY₂W₃),
    (SeriesPAux.elemModulo_of_isElementaryAbelian hWel).anti hY₂W₃,
    SeriesPAux.elemModulo_of_isElementaryAbelian hWel, hF₅el.mono hY₂W₃,
    hPel.anti hM₆P, hPel.mono hF₅M₆⟩

theorem yamadaP_conj_coset (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ y ∈ yamadaP d t, orderOf (t * y) = 2 → ∃ m ∈ yamadaP d t, t * y = m⁻¹ * t * m := by
  intro y hy hord
  obtain ⟨hU₁Y₂, hY₂W₃, hW₃F₅, hF₅M₆, hM₆P⟩ := series_le hW h d hK hQ
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := series_normalizes hW h d hK hQ
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := series_elemModulo hW h d hK hQ
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := yamada_series_inf_centralizer hW h d hK hQ
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := yamada_series_card hW h d hK hQ
  have hnorm : ∀ i : Fin 6, ((yamadaSeries d t i.castSucc).subgroupOf
      (yamadaSeries d t i.succ)).Normal := by
    intro i
    fin_cases i
    · exact SeriesPAux.normal_subgroupOf_of_elemModulo bot_le e1
    · exact SeriesPAux.normal_subgroupOf_of_elemModulo hU₁Y₂ e2
    · exact SeriesPAux.normal_subgroupOf_of_elemModulo hY₂W₃ e3
    · exact SeriesPAux.normal_subgroupOf_of_elemModulo hW₃F₅ e4
    · exact SeriesPAux.normal_subgroupOf_of_elemModulo hF₅M₆ e5
    · exact SeriesPAux.normal_subgroupOf_of_elemModulo hM₆P e6
  have helem : ∀ i : Fin 6, CFSG.IsElementaryAbelian 2 (yamadaSeries d t i.succ ⧸
      (yamadaSeries d t i.castSucc).subgroupOf (yamadaSeries d t i.succ)) := by
    intro i
    fin_cases i
    · exact SeriesPAux.isElementaryAbelian_quotient_of_elemModulo e1
    · haveI := SeriesPAux.normal_subgroupOf_of_elemModulo hU₁Y₂ e2
      exact SeriesPAux.isElementaryAbelian_quotient_of_elemModulo e2
    · haveI := SeriesPAux.normal_subgroupOf_of_elemModulo hY₂W₃ e3
      exact SeriesPAux.isElementaryAbelian_quotient_of_elemModulo e3
    · haveI := SeriesPAux.normal_subgroupOf_of_elemModulo hW₃F₅ e4
      exact SeriesPAux.isElementaryAbelian_quotient_of_elemModulo e4
    · haveI := SeriesPAux.normal_subgroupOf_of_elemModulo hF₅M₆ e5
      exact SeriesPAux.isElementaryAbelian_quotient_of_elemModulo e5
    · haveI := SeriesPAux.normal_subgroupOf_of_elemModulo hM₆P e6
      exact SeriesPAux.isElementaryAbelian_quotient_of_elemModulo e6
  have hcard : ∀ i : Fin 6, Nat.card (yamadaSeries d t i.succ ⊓ centralizer {t} : Subgroup G) ^ 2 =
      Nat.card (yamadaSeries d t i.succ) := by
    intro i
    fin_cases i
    · show Nat.card (yamadaU₁ d t ⊓ centralizer {t} : Subgroup G) ^ 2 = Nat.card (yamadaU₁ d t)
      rw [c1, k1, d.cards.1]
    · show Nat.card (yamadaY₂ d t ⊓ centralizer {t} : Subgroup G) ^ 2 = Nat.card (yamadaY₂ d t)
      rw [c2, k2, d.cards.2.1]
      ring
    · show Nat.card (yamadaW₃ d t ⊓ centralizer {t} : Subgroup G) ^ 2 = Nat.card (yamadaW₃ d t)
      rw [c3, k3, d.cards.2.2.2.1]
      ring
    · show Nat.card (yamadaF₅ d t ⊓ centralizer {t} : Subgroup G) ^ 2 = Nat.card (yamadaF₅ d t)
      rw [c4, k4, d.cards.2.2.2.2.1]
      ring
    · show Nat.card (yamadaM₆ d t ⊓ centralizer {t} : Subgroup G) ^ 2 = Nat.card (yamadaM₆ d t)
      rw [c5, k5, d.cards.2.2.2.2.2.2.1]
      ring
    · show Nat.card (yamadaP d t ⊓ centralizer {t} : Subgroup G) ^ 2 = Nat.card (yamadaP d t)
      rw [c6, k6, d.cards.2.2.2.2.2.2.2]
      ring
  have haV : ∀ i : Fin 7, t ∈ normalizer (yamadaSeries d t i : Set G) := by
    intro i
    fin_cases i
    · show t ∈ normalizer ((⊥ : Subgroup G) : Set G)
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top t
    · exact n1
    · exact n2
    · exact n3
    · exact n4
    · exact n5
    · exact n6
  exact Common.involution_coset_conj_of_card_sq (W := yamadaP d t) h.ht (yamadaSeries d t) rfl rfl
    (fun i => by
      fin_cases i
      · exact bot_le
      · exact hU₁Y₂
      · exact hY₂W₃
      · exact hW₃F₅
      · exact hF₅M₆
      · exact hM₆P) haV hcard hy hord

theorem yamadaP_le_closure_involutions (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ≤ closure {x | x ∈ yamadaP d t ∧ orderOf x = 2} := by
  have hWel := (h.yamada_5_33_3_uniform hW d hK hQ.doubling).1
  have hXel := (h.yamada_5_45_3 hW d hK hQ).1
  obtain ⟨hM₆eq, -, -⟩ := h.yamada_5_44_2 hW d hK hQ
  obtain ⟨hD₇eq, -, -⟩ := h.yamada_5_54_2 hW d hK hQ
  obtain ⟨-, -, hF₅eq, -, -, -⟩ := h.yamada_5_46_1 hW d hK hQ
  obtain ⟨-, -, hM₆P, hD₇P, hPeq, -, -⟩ := h.yamada_5_57_2 hW d hK hQ
  obtain ⟨-, -, hW₃F₅, hF₅M₆, -⟩ := series_le hW h d hK hQ
  have hF₅P : yamadaF₅ d t ≤ yamadaP d t := hF₅M₆.trans hM₆P
  have hF₅bM₆ : (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom ≤ yamadaM₆ d t :=
    le_sup_right.trans hM₆eq.ge
  have hW₃aD₇ : (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom ≤ yamadaD₇ d t :=
    le_sup_right.trans hD₇eq.ge
  have hW₃sq : ∀ x ∈ yamadaW₃ d t, x * x = 1 := fun x hx =>
    SeriesPAux.mul_self_eq_one_of_mem (A := yamadaW₃ d t) hx
  have hX₄sq : ∀ x ∈ yamadaX₄ d t, x * x = 1 := fun x hx =>
    SeriesPAux.mul_self_eq_one_of_mem (A := yamadaX₄ d t) hx
  have hW₃I := SeriesPAux.le_closure_involutions (hW₃F₅.trans hF₅P) hW₃sq
  have hX₄I := SeriesPAux.le_closure_involutions ((Q44.X₄_le_F₅ d t).trans hF₅P) hX₄sq
  have hW₃bI := SeriesPAux.le_closure_involutions
    ((Subgroup.map_mono hW₃F₅).trans (hF₅bM₆.trans hM₆P))
    (SeriesPAux.mul_self_eq_one_of_mem_map_conj d.wb hW₃sq)
  have hX₄bI := SeriesPAux.le_closure_involutions
    ((Subgroup.map_mono (Q44.X₄_le_F₅ d t)).trans (hF₅bM₆.trans hM₆P))
    (SeriesPAux.mul_self_eq_one_of_mem_map_conj d.wb hX₄sq)
  have hW₃aI := SeriesPAux.le_closure_involutions (hW₃aD₇.trans hD₇P)
    (SeriesPAux.mul_self_eq_one_of_mem_map_conj d.wa hW₃sq)
  have hF₅I : yamadaF₅ d t ≤ closure {x | x ∈ yamadaP d t ∧ orderOf x = 2} :=
    hF₅eq.ge.trans (sup_le hW₃I hX₄I)
  have hF₅bI : (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom ≤
      closure {x | x ∈ yamadaP d t ∧ orderOf x = 2} := by
    rw [← hF₅eq, Subgroup.map_sup]
    exact sup_le hW₃bI hX₄bI
  have hM₆I : yamadaM₆ d t ≤ closure {x | x ∈ yamadaP d t ∧ orderOf x = 2} :=
    hM₆eq.le.trans (sup_le hF₅I hF₅bI)
  have hD₇I : yamadaD₇ d t ≤ closure {x | x ∈ yamadaP d t ∧ orderOf x = 2} :=
    hD₇eq.le.trans (sup_le hW₃I hW₃aI)
  exact hPeq.ge.trans (sup_le hM₆I hD₇I)

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
