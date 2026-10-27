module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductN1

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductN1CenterAux

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (mem_centerMod_iff)

section Generic

variable {G : Type*} [Group G]

theorem mem_conj_iff {A : Subgroup G} {g y : G} : y ∈ Aᵍ[g] ↔ g * y * g⁻¹ ∈ A := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem mem_centerMod_conj_iff {V Q : Subgroup G} (hVQ : V ≤ Q) {g : G}
    (hg : g ∈ normalizer (V : Set G)) {x : G} :
    x ∈ centerMod V (Qᵍ[g]) ↔ g * x * g⁻¹ ∈ centerMod V Q := by
  have hgi : g⁻¹ ∈ normalizer (V : Set G) := inv_mem hg
  have hVQg : V ≤ Qᵍ[g] := fun v hv =>
    mem_conj_iff.2 (hVQ ((mem_normalizer_iff.1 hg v).1 hv))
  rw [mem_centerMod_iff hVQg, mem_centerMod_iff hVQ]
  constructor
  · rintro ⟨hxQ, hxN, hxc⟩
    refine ⟨mem_conj_iff.1 hxQ, mul_mem (mul_mem hg hxN) hgi, fun a haQ haN => ?_⟩
    have haQ' : g⁻¹ * a * g ∈ Qᵍ[g] := by
      rw [mem_conj_iff]
      simpa [mul_assoc] using haQ
    have haN' : g⁻¹ * a * g ∈ normalizer (V : Set G) := mul_mem (mul_mem hgi haN) hg
    have h1 := hxc _ haQ' haN'
    have e : g * x * g⁻¹ * a * (g * x * g⁻¹)⁻¹ * a⁻¹ =
        g * (x * (g⁻¹ * a * g) * x⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 hg _).1 h1
  · rintro ⟨hxQ, hxN, hxc⟩
    refine ⟨mem_conj_iff.2 hxQ, ?_, fun a haQ haN => ?_⟩
    · have := mul_mem (mul_mem hgi hxN) hg
      simpa [mul_assoc] using this
    · have haQ' : g * a * g⁻¹ ∈ Q := mem_conj_iff.1 haQ
      have haN' : g * a * g⁻¹ ∈ normalizer (V : Set G) := mul_mem (mul_mem hg haN) hgi
      have h1 := hxc _ haQ' haN'
      have e : g * x * g⁻¹ * (g * a * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ =
          g * (x * a * x⁻¹ * a⁻¹) * g⁻¹ := by group
      rw [e] at h1
      exact (mem_normalizer_iff.1 hg _).2 h1

theorem mem_normalizer_centerMod {V Q : Subgroup G} (hVQ : V ≤ Q) {g : G}
    (hV : g ∈ normalizer (V : Set G)) (hQ : g ∈ normalizer (Q : Set G)) :
    g ∈ normalizer ((centerMod V Q : Subgroup G) : Set G) := by
  have key : ∀ g' ∈ normalizer (V : Set G), g' ∈ normalizer (Q : Set G) →
      ∀ x ∈ centerMod V Q, g' * x * g'⁻¹ ∈ centerMod V Q := by
    intro g' hV' hQ' x hx
    obtain ⟨hxQ, hxN, hxc⟩ := (mem_centerMod_iff hVQ).1 hx
    refine (mem_centerMod_iff hVQ).2
      ⟨(mem_normalizer_iff.1 hQ' x).1 hxQ, mul_mem (mul_mem hV' hxN) (inv_mem hV'),
        fun a haQ haN => ?_⟩
    have ha'Q : g'⁻¹ * a * g' ∈ Q := by
      simpa using (mem_normalizer_iff.1 (inv_mem hQ') a).1 haQ
    have ha'N : g'⁻¹ * a * g' ∈ normalizer (V : Set G) :=
      mul_mem (mul_mem (inv_mem hV') haN) hV'
    have h1 := hxc _ ha'Q ha'N
    have h2 : g' * x * g'⁻¹ * a * (g' * x * g'⁻¹)⁻¹ * a⁻¹ =
        g' * (x * (g'⁻¹ * a * g') * x⁻¹ * (g'⁻¹ * a * g')⁻¹) * g'⁻¹ := by group
    rw [h2]
    exact (mem_normalizer_iff.1 hV' _).1 h1
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g hV hQ x
  · intro hx
    have := key g⁻¹ (inv_mem hV) (inv_mem hQ) _ hx
    simpa [mul_assoc] using this

theorem mem_normalizer_sup_conj {P Λ : Subgroup G} {r : G} (hrr : r * r = 1)
    (hΛ : Λ = P ⊔ Pᵍ[r]) : r ∈ normalizer (Λ : Set G) := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have hww : ∀ x : G, r * (r * x * r⁻¹) * r⁻¹ = x := fun x => by
    rw [hri]
    calc r * (r * x * r) * r = (r * r) * x * (r * r) := by group
      _ = x := by rw [hrr]; group
  subst hΛ
  have hfwd : ∀ x ∈ P ⊔ Pᵍ[r], r * x * r⁻¹ ∈ P ⊔ Pᵍ[r] := by
    have hle : P ⊔ Pᵍ[r] ≤ (P ⊔ Pᵍ[r]).comap (MulAut.conj r).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun y hy => ?_)
      · show r * x * r⁻¹ ∈ P ⊔ Pᵍ[r]
        exact mem_sup_right (mem_conj_iff.2 (by rwa [hww]))
      · exact mem_sup_left (mem_conj_iff.1 hy)
    exact fun x hx => hle hx
  rw [mem_normalizer_iff]
  intro x
  exact ⟨hfwd x, fun hx => by simpa [hww] using hfwd _ hx⟩

theorem le_of_mem_conj_of_commutator_mem
    {U Y D P₁ Λ : Subgroup G} {t r : G}
    (htt : t * t = 1) (htr : t * r = r * t)
    (hUY : U ≤ Y) (hYD : Y ≤ D) (hDP : D ≤ P₁) (hPΛ : P₁ ≤ Λ)
    (hPU : P₁ ≤ normalizer (U : Set G)) (htU : t ∈ normalizer (U : Set G))
    (hrU : r ∈ normalizer (U : Set G)) (htY : t ∈ normalizer (Y : Set G))
    (hrD : r ∈ normalizer (D : Set G)) (hrΛ : r ∈ normalizer (Λ : Set G))
    (hΛt : ⁅Λ, Λᵍ[t]⁆ ≤ D)
    (hY : Y ≤ centerMod U P₁) (hH : centerMod U P₁ ⊓ centerMod U (P₁ᵍ[r]) ≤ U)
    {c : G} (hcr : r * c * r⁻¹ ∈ Y) (hcY : ∀ p ∈ P₁, p * c * p⁻¹ * c⁻¹ ∈ Y) : c ∈ U := by
  have hUP : U ≤ P₁ := hUY.trans (hYD.trans hDP)
  have hUQ : U ≤ P₁ᵍ[r] := fun u hu =>
    mem_conj_iff.2 (hUP ((mem_normalizer_iff.1 hrU u).1 hu))
  have hDQ : D ≤ P₁ᵍ[r] := fun d hd =>
    mem_conj_iff.2 (hDP ((mem_normalizer_iff.1 hrD d).1 hd))
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hstable : ∀ p ∈ P₁, ∀ w : G, t * w * t⁻¹ ∈ centerMod U (P₁ᵍ[r]) →
      t * (p * w * p⁻¹) * t⁻¹ ∈ centerMod U (P₁ᵍ[r]) := by
    intro p hp w hw
    set p' := t * p * t⁻¹ with hp'
    have hp'Λ : p' ∈ Λᵍ[t] := by
      rw [mem_conj_iff]
      have e : t * p' * t⁻¹ = p := by
        rw [hp', hti]
        calc t * (t * p * t) * t = (t * t) * p * (t * t) := by group
          _ = p := by rw [htt]; group
      rw [e]
      exact hPΛ hp
    have hp'iΛ : p'⁻¹ ∈ Λᵍ[t] := inv_mem hp'Λ
    have hQΛ : ∀ y ∈ P₁ᵍ[r], y ∈ Λ := fun y hy => by
      have := hPΛ (mem_conj_iff.1 hy)
      exact (mem_normalizer_iff.1 hrΛ y).2 this
    have hconj : ∀ q ∈ Λᵍ[t], ∀ y ∈ P₁ᵍ[r], q * y * q⁻¹ ∈ P₁ᵍ[r] := by
      intro q hq y hy
      have h1 : q * y * q⁻¹ * y⁻¹ ∈ D := by
        have h := Subgroup.commutator_mem_commutator hq (hQΛ y hy)
        rw [Subgroup.commutator_comm] at h
        exact hΛt h
      have h2 : q * y * q⁻¹ = (q * y * q⁻¹ * y⁻¹) * y := by group
      rw [h2]
      exact mul_mem (hDQ h1) hy
    have hp'N : p' ∈ normalizer ((P₁ᵍ[r] : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      exact ⟨fun hy => hconj _ hp'Λ y hy, fun hy => by
        have := hconj _ hp'iΛ _ hy
        simpa [mul_assoc] using this⟩
    have hp'U : p' ∈ normalizer (U : Set G) :=
      mul_mem (mul_mem htU (hPU hp)) (inv_mem htU)
    have h3 := mem_normalizer_centerMod hUQ hp'U hp'N
    have := (mem_normalizer_iff.1 h3 _).1 hw
    have e : t * (p * w * p⁻¹) * t⁻¹ = p' * (t * w * t⁻¹) * p'⁻¹ := by
      rw [hp']; group
    rw [e]
    exact this
  have hctZr : t * c * t⁻¹ ∈ centerMod U (P₁ᵍ[r]) := by
    rw [mem_centerMod_conj_iff hUP hrU]
    refine hY ?_
    have e : r * (t * c * t⁻¹) * r⁻¹ = t * (r * c * r⁻¹) * t⁻¹ := by
      calc r * (t * c * t⁻¹) * r⁻¹ = (r * t) * c * (r * t)⁻¹ := by group
        _ = (t * r) * c * (t * r)⁻¹ := by rw [htr]
        _ = t * (r * c * r⁻¹) * t⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 htY _).1 hcr
  have hYU : ∀ w ∈ Y, t * w * t⁻¹ ∈ centerMod U (P₁ᵍ[r]) → w ∈ U := by
    intro w hw hwr
    have h1 : t * w * t⁻¹ ∈ Y := (mem_normalizer_iff.1 htY _).1 hw
    have h2 : t * w * t⁻¹ ∈ U := hH (Subgroup.mem_inf.2 ⟨hY h1, hwr⟩)
    have := (mem_normalizer_iff.1 (inv_mem htU) _).1 h2
    rwa [show t⁻¹ * (t * w * t⁻¹) * t⁻¹⁻¹ = w by group] at this
  have hcomm : ∀ p ∈ P₁, p * c * p⁻¹ * c⁻¹ ∈ U := by
    intro p hp
    refine hYU _ (hcY p hp) ?_
    have e : t * (p * c * p⁻¹ * c⁻¹) * t⁻¹ =
        (t * (p * c * p⁻¹) * t⁻¹) * (t * c * t⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem (hstable p hp c hctZr) (inv_mem hctZr)
  have hcD : c ∈ D := (mem_normalizer_iff.1 hrD c).2 (hYD hcr)
  have hcZ : c ∈ centerMod U P₁ := by
    refine (mem_centerMod_iff hUP).2 ⟨hDP hcD, hPU (hDP hcD),
      fun a ha _ => ?_⟩
    have := inv_mem (hcomm a ha)
    simpa [mul_assoc] using this
  have hcZr : c ∈ centerMod U (P₁ᵍ[r]) := by
    rw [mem_centerMod_conj_iff hUP hrU]
    exact hY hcr
  exact hH (Subgroup.mem_inf.2 ⟨hcZ, hcZr⟩)

end Generic

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem P_le_normalizer_F₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ≤ normalizer (yamadaF₅ d t : Set G) := by
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨hFR₅, -, -, -⟩, hFchar, -, -, -⟩ := h.yamada_5_46_4 hW d hK hQ
  have hNF := normalizer_le_normalizer_of_characteristic_subgroupOf hFR₅ hFchar
  exact hPR₈.trans ((yamadaR₈_le d t).trans hNF)

theorem exists_mul_of_mem_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    ∀ x ∈ yamadaD₇ d t, ∃ a : G, d.wa * a * d.wa⁻¹ ∈ yamadaY₂ d t ∧
      ∃ y ∈ yamadaF₅ d t, x = a * y := by
  have hD := hQ.doubling
  set U₁' : Subgroup G := (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom with hU₁'
  set A₄ : Subgroup G := U₁'.map (MulAut.conj d.wa).toMonoidHom with hA₄
  have hmemA₄ : ∀ y, y ∈ A₄ ↔ ∃ u ∈ yamadaU₁ d t, y = d.wa * (d.wb * u * d.wb⁻¹) * d.wa⁻¹ := by
    intro y
    simp only [hA₄, hU₁', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have hY₂D₇ := h.yamadaY₂_le_yamadaD₇ hW d hK hQ
  have hwaD := h.wa_mem_normalizer_yamadaD₇ hW d hK hQ
  have hA₄D : A₄ ≤ yamadaD₇ d t := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (hmemA₄ y).1 hy
    have hu' : d.wb * u * d.wb⁻¹ ∈ yamadaY₂ d t := le_sup_right (a := yamadaU₁ d t) ⟨u, hu, rfl⟩
    exact (mem_normalizer_iff.1 hwaD _).1 (hY₂D₇ hu')
  have hJ₅U : d.J₅ ≤ centralizer ((yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom : Set G) :=
    h.J₅_le_centralizer_map_wb d hD
  have hJ₄ : d.J₄ = d.J₅.map (MulAut.conj d.wa).toMonoidHom := (d.Ji_conj_G.2.1).symm
  have hJ₄A₄ : ∀ j ∈ d.J₄, ∀ y ∈ A₄, j * y = y * j := by
    intro j hj y hy
    rw [hJ₄] at hj
    obtain ⟨j₅, hj₅, rfl⟩ := Subgroup.mem_map.1 hj
    obtain ⟨u, hu, rfl⟩ := (hmemA₄ y).1 hy
    have h1 : (d.wb * u * d.wb⁻¹) * j₅ = j₅ * (d.wb * u * d.wb⁻¹) :=
      mem_centralizer_iff.1 (hJ₅U hj₅) _ ⟨u, hu, rfl⟩
    have e : ∀ a b : G, d.wa * a * d.wa⁻¹ * (d.wa * b * d.wa⁻¹) = d.wa * (a * b) * d.wa⁻¹ := by
      intros; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e, e, h1]
  have hF₅M₆ := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
  have hF₅D₇ := h.yamadaF₅_le_yamadaD₇ hW d hK hQ
  have hPN₂ : yamadaP d t ≤ yamadaN₂ d t := hp.sylow₂.le
  have hDP := yamadaD₇_le_yamadaP d t
  have hwa2 : d.wa * d.wa = 1 := (d.yamada_3_7_G (hK ▸ h.four_le)).2.2.1
  have hwai : d.wa⁻¹ = d.wa := inv_eq_of_mul_eq_one_right hwa2
  have hY₂W₃ : yamadaY₂ d t ≤ yamadaW₃ d t :=
    (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans (h.yamadaW₃_facts hW d hK hD).2.2.2.1
  have hbot : A₄ ⊓ yamadaF₅ d t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxA, hxF⟩ := Subgroup.mem_inf.1 hx
    have hxC : x ∈ yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) :=
      Subgroup.mem_inf.2 ⟨hPN₂ (hDP (hA₄D hxA)),
        mem_centralizer_iff.2 fun j hj => hJ₄A₄ j hj x hxA⟩
    have hxY : x ∈ yamadaY₂ d t := hp.inf₂ (Subgroup.mem_inf.2 ⟨hxC, hF₅M₆ hxF⟩)
    obtain ⟨u, hu, rfl⟩ := (hmemA₄ x).1 hxA
    have hvY : d.wb * u * d.wb⁻¹ ∈ yamadaY₂ d t := le_sup_right (a := yamadaU₁ d t) ⟨u, hu, rfl⟩
    have hv : d.wb * u * d.wb⁻¹ ∈
        yamadaW₃ d t ⊓ (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨hY₂W₃ hvY, ?_⟩
      rw [mem_map_conj_iff, hwai]
      have := hY₂W₃ hxY
      rwa [hwai] at this
    rw [Setup.Q52.yamadaW₃_inf_map_wa hW h d hK hQ] at hv
    have hv' : d.wb * u * d.wb⁻¹ ∈
        yamadaU₁ d t ⊓ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom :=
      Subgroup.mem_inf.2 ⟨hv, ⟨u, hu, rfl⟩⟩
    rw [(h.yamada_5_13_1 d hK hD).1.1, Subgroup.mem_bot] at hv'
    rw [hv', mul_one, mul_inv_cancel]
    exact one_mem _
  have hA₄c : Nat.card A₄ = Nat.card K ^ 2 := by
    rw [hA₄, Subgroup.card_map_of_injective (MulAut.conj d.wa).injective, hU₁',
      Subgroup.card_map_of_injective (MulAut.conj d.wb).injective, hD.card_eq]
  have hA₄F : A₄ ≤ normalizer (yamadaF₅ d t : Set G) := fun x hx =>
    P_le_normalizer_F₅ hW h d hK hQ (hDP (hA₄D hx))
  have hcard := Common.card_sup_mul_card_inf_eq (A := yamadaF₅ d t) (B := A₄) hA₄F
  rw [inf_comm, hbot, Subgroup.card_bot, mul_one, hA₄c,
    (h.card_yamada_five_six hW d hK hQ).2.2.2.1] at hcard
  have hsup : A₄ ⊔ yamadaF₅ d t = yamadaD₇ d t := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hA₄D hF₅D₇) ?_
    rw [sup_comm, hcard, h.card_yamadaD₇ hW d hK hQ]
    ring_nf
    exact le_rfl
  intro x hx
  rw [← hsup] at hx
  obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hA₄F x hx
  refine ⟨a, ?_, y, hy, rfl⟩
  obtain ⟨u, hu, rfl⟩ := (hmemA₄ a).1 ha
  have e : d.wa * (d.wa * (d.wb * u * d.wb⁻¹) * d.wa⁻¹) * d.wa⁻¹ = d.wb * u * d.wb⁻¹ := by
    rw [hwai]
    calc d.wa * (d.wa * (d.wb * u * d.wb⁻¹) * d.wa) * d.wa
        = (d.wa * d.wa) * (d.wb * u * d.wb⁻¹) * (d.wa * d.wa) := by group
      _ = d.wb * u * d.wb⁻¹ := by rw [hwa2]; group
  rw [e]
  exact le_sup_right (a := yamadaU₁ d t) ⟨u, hu, rfl⟩

theorem t_normalizes (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaP d t : Set G) ∧ t ∈ normalizer (yamadaD₇ d t : Set G) ∧
      t ∈ normalizer (yamadaU₁ d t : Set G) ∧ t ∈ normalizer (yamadaY₂ d t : Set G) ∧
      t ∈ normalizer (yamadaF₅ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨⟨hsup, htP, -⟩, -, ⟨-, htD₇, -⟩⟩ := h.yamada_5_51 hW d hK hQ
  have htR₈ : t ∈ yamadaR₈ d t := hsup ▸ mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨⟨hFR₅, -, -, -⟩, hFchar, -, -, -⟩ := h.yamada_5_46_4 hW d hK hQ
  have hNF := normalizer_le_normalizer_of_characteristic_subgroupOf hFR₅ hFchar
  exact ⟨htP, htD₇, (h.t_mem_normalizer_yamadaU₁ d hK hD).1,
    Setup.Q52.yamadaR₈_le_normalizer_yamadaY₂ hW h d hK hQ htR₈,
    hNF ((yamadaR₈_le d t) htR₈)⟩

theorem exists_mem_yamadaD₇_inf_not_mem_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂) :
    ∃ e ∈ yamadaD₇ d t, e ∈ yamadaP d t ⊓ Λ₂ ∧ e ∉ yamadaF₅ d t := by
  by_contra hcon'
  have hcon : ∀ e ∈ yamadaD₇ d t, e ∈ yamadaP d t ⊓ Λ₂ → e ∈ yamadaF₅ d t :=
    fun e he he' => by
      by_contra hne
      exact hcon' ⟨e, he, he', hne⟩
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨htP, -, -, -, -⟩ := t_normalizes hW h d hK hQ
  have hM₆P := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hF₅M₆ := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
  have hDP := yamadaD₇_le_yamadaP d t
  have hM₆Λ₂ : yamadaM₆ d t ≤ Λ₂ := hL.fac₂.X_le
  have hPM : ∀ x ∈ yamadaP d t, ∃ m ∈ yamadaM₆ d t, ∃ e ∈ yamadaD₇ d t, x = m * e := by
    intro x hx
    have : x ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
      rw [← h.yamadaP_eq_mul hW d hK hQ]
      exact hx
    obtain ⟨m, hm, e, he, rfl⟩ := Set.mem_mul.1 this
    exact ⟨m, hm, e, he, rfl⟩
  have hM₆P₂ : ∀ m ∈ yamadaM₆ d t, m ∈ yamadaP d t ⊓ Λ₂ := fun m hm =>
    Subgroup.mem_inf.2 ⟨hM₆P hm, hM₆Λ₂ hm⟩
  have hPΛ₂ : ∀ x ∈ yamadaP d t ⊓ Λ₂, x ∈ yamadaM₆ d t := by
    intro x hx
    obtain ⟨m, hm, e, he, rfl⟩ := hPM x (Subgroup.mem_inf.1 hx).1
    have he' : e ∈ yamadaP d t ⊓ Λ₂ := by
      have := mul_mem (inv_mem (hM₆P₂ m hm)) hx
      rwa [inv_mul_cancel_left] at this
    exact mul_mem hm (hF₅M₆ (hcon e he he'))
  have hY₂N : yamadaP d t ≤ normalizer (yamadaY₂ d t : Set G) :=
    hPR₈.trans (Setup.Q52.yamadaR₈_le_normalizer_yamadaY₂ hW h d hK hQ)
  have hY₂P₂ : yamadaY₂ d t ≤ yamadaP d t ⊓ Λ₂ := fun y hy =>
    hM₆P₂ y (h.yamadaY₂_le_yamadaM₆ hW d hK hQ hy)
  have hM₆Z : yamadaM₆ d t ≤ centerMod (yamadaY₂ d t) (yamadaP d t ⊓ Λ₂) := by
    intro g hg
    refine (mem_centerMod_iff hY₂P₂).2 ⟨hM₆P₂ g hg, hY₂N (hM₆P hg),
      fun a ha _ => ?_⟩
    have hcomm := (h.yamada_5_55_1 hW d hK hQ).2.2
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator hg (hPΛ₂ a ha)
  have hPΛ₁ : yamadaP d t ≤ Λ₁ := by
    intro x hx
    obtain ⟨m, hm, e, he, rfl⟩ := hPM x hx
    have hx' : t⁻¹ * (m * e) * t⁻¹⁻¹ ∈ yamadaP d t := (mem_normalizer_iff.1 (inv_mem htP) _).1 hx
    obtain ⟨m', hm', e', he', hxe⟩ := hPM _ hx'
    have hmem : t⁻¹ * (m * e) * t⁻¹⁻¹ ∈ (yamadaP d t ⊓ Λ₁)ᵍ[t] := by
      rw [hL.label, hxe]
      exact mul_mem (mem_sup_left (hM₆Z hm')) (mem_sup_right he')
    have := (Subgroup.mem_inf.1 (mem_conj_iff.1 hmem)).2
    rwa [show t * (t⁻¹ * (m * e) * t⁻¹⁻¹) * t⁻¹ = m * e by group] at this
  obtain ⟨φ, -, hφk⟩ := hL.fac₁.quot
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hf : 1 ≤ f := by
    have := h.two_le
    omega
  have hD₇Λ₁ : yamadaD₇ d t ≤ Λ₁ := hL.fac₁.X_le
  set H : Subgroup ↥Λ₁ := (yamadaP d t).subgroupOf Λ₁ with hH
  have hH2 : IsPGroup 2 H :=
    (h.isPGroup_yamadaP d hPR₈).of_equiv (Subgroup.subgroupOfEquivOfLe hPΛ₁).symm
  have hcard := Common.card_map_mul_card_inf_ker φ H
  have hinf : H ⊓ φ.ker = (yamadaD₇ d t).subgroupOf Λ₁ := by
    rw [hφk]
    exact inf_of_le_right fun x hx => Subgroup.mem_subgroupOf.2 (hDP (Subgroup.mem_subgroupOf.1 hx))
  rw [hinf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₇Λ₁).toEquiv,
    hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΛ₁).toEquiv, h.card_yamadaP hW d hK hQ,
    h.card_yamadaD₇ hW d hK hQ] at hcard
  have hcard' : Nat.card (H.map φ) = Nat.card K ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card K ^ 10 from pow_pos Nat.card_pos 10) ?_
    rw [hcard]
    ring
  have hle := Common.card_le_of_isPGroup_SL2 hf hK' (hH2.map φ)
  rw [hcard', ← hK] at hle
  nlinarith [hQ.four_le]

theorem commutator_mem_yamadaY₂_of_labelled (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂) :
    ∀ e ∈ yamadaD₇ d t, t⁻¹ * e * t ∈ yamadaP d t ⊓ Λ₂ →
      ∀ p ∈ yamadaP d t ⊓ Λ₁, p * e * p⁻¹ * e⁻¹ ∈ yamadaY₂ d t := by
  intro e he he₁ p hp
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, htD₇, -, htY₂, -⟩ := t_normalizes hW h d hK hQ
  have hDP := yamadaD₇_le_yamadaP d t
  have hY₂N : yamadaP d t ≤ normalizer (yamadaY₂ d t : Set G) :=
    hPR₈.trans (Setup.Q52.yamadaR₈_le_normalizer_yamadaY₂ hW h d hK hQ)
  have hPD₇ : yamadaP d t ≤ normalizer (yamadaD₇ d t : Set G) :=
    (h.yamadaP_le_normalizer_D₇_M₆ hW d hK hQ).1
  have hY₂P₂ : yamadaY₂ d t ≤ yamadaP d t ⊓ Λ₂ := fun y hy =>
    Subgroup.mem_inf.2 ⟨hDP (h.yamadaY₂_le_yamadaD₇ hW d hK hQ hy),
      hL.fac₂.X_le (h.yamadaY₂_le_yamadaM₆ hW d hK hQ hy)⟩
  have hU₁Y₂ : yamadaU₁ d t ≤ yamadaY₂ d t := le_sup_left
  set p' := t⁻¹ * p * t with hp'
  have hp'mem : p' ∈ (yamadaP d t ⊓ Λ₁)ᵍ[t] := by
    rw [mem_conj_iff]
    rwa [show t * p' * t⁻¹ = p by rw [hp']; group]
  rw [hL.label] at hp'mem
  have hCN : centerMod (yamadaY₂ d t) (yamadaP d t ⊓ Λ₂) ≤ normalizer (yamadaD₇ d t : Set G) := by
    intro z hz
    obtain ⟨hzP₂, -, -⟩ := (mem_centerMod_iff hY₂P₂).1 hz
    exact hPD₇ (Subgroup.mem_inf.1 hzP₂).1
  obtain ⟨z, hz, d₀, hd₀, hpd⟩ := Common.exists_mul_of_le_normalizer' hCN _ hp'mem
  obtain ⟨hzP₂, -, hzc⟩ := (mem_centerMod_iff hY₂P₂).1 hz
  set e₁ := t⁻¹ * e * t with he₁def
  have he₁D : e₁ ∈ yamadaD₇ d t := (mem_normalizer_iff.1 (inv_mem htD₇) e).1 he |> fun h' => by
    rwa [show t⁻¹ * e * t⁻¹⁻¹ = e₁ by rw [he₁def]; group] at h'
  have hzP : z ∈ yamadaP d t := (Subgroup.mem_inf.1 hzP₂).1
  have hc₁ : d₀ * e₁ * d₀⁻¹ * e₁⁻¹ ∈ yamadaU₁ d t := by
    have := Subgroup.commutator_mem_commutator hd₀ he₁D
    rwa [(h.yamada_5_55_1 hW d hK hQ).1.2] at this
  have h1 : z * (d₀ * e₁ * d₀⁻¹ * e₁⁻¹) * z⁻¹ ∈ yamadaY₂ d t :=
    (mem_normalizer_iff.1 (hY₂N hzP) _).1 (hU₁Y₂ hc₁)
  have h2 : z * e₁ * z⁻¹ * e₁⁻¹ ∈ yamadaY₂ d t :=
    hzc e₁ he₁ (hY₂N (hDP he₁D))
  have key : p' * e₁ * p'⁻¹ * e₁⁻¹ ∈ yamadaY₂ d t := by
    rw [hpd, show z * d₀ * e₁ * (z * d₀)⁻¹ * e₁⁻¹ =
      (z * (d₀ * e₁ * d₀⁻¹ * e₁⁻¹) * z⁻¹) * (z * e₁ * z⁻¹ * e₁⁻¹) by group]
    exact mul_mem h1 h2
  have := (mem_normalizer_iff.1 htY₂ _).1 key
  rwa [show t * (p' * e₁ * p'⁻¹ * e₁⁻¹) * t⁻¹ = p * e * p⁻¹ * e⁻¹ by
    rw [hp', he₁def]; group] at this

end Local

end ProductN1CenterAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

open ProductN1CenterAux

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


theorem yamada_7_8 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂) :
    yamadaU₁ d t < centerMod (yamadaU₁ d t) Λ₁ := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  obtain ⟨⟨-, hΛeq, -⟩, -, ⟨-, hZt, hZr⟩, -⟩ := h.yamada_7_6 hW d hK hQ hp hL.fac₁
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, htD₇, htU₁, htY₂, htF₅⟩ := t_normalizes hW h d hK hQ
  refine lt_of_le_of_ne (Common.NormalizerQuotient.le_lift _) ?_
  intro hne
  have hwa := d.wa_mem_inf_normalizer_U
  have hwa2 : d.wa * d.wa = 1 := (d.yamada_3_7_G (hK ▸ h.four_le)).2.2.1
  have htr : t * d.wa = d.wa * t :=
    (mem_centralizer_singleton_iff.1 (h.L_le_centralizer hwa.1)).symm
  have hrU : d.wa ∈ normalizer (yamadaU₁ d t : Set G) :=
    hD.inf_normalizer_U_le_normalizer hK hwa
  have hrD := h.wa_mem_normalizer_yamadaD₇ hW d hK hQ
  have hrΛ : d.wa ∈ normalizer (Λ₁ : Set G) := mem_normalizer_sup_conj hwa2 hΛeq
  have hDP := yamadaD₇_le_yamadaP d t
  have hU₁Y₂ : yamadaU₁ d t ≤ yamadaY₂ d t := le_sup_left
  have hY₂D₇ := h.yamadaY₂_le_yamadaD₇ hW d hK hQ
  have hD₇Λ₁ : yamadaD₇ d t ≤ Λ₁ := hL.fac₁.X_le
  have hY : yamadaY₂ d t ≤ centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) := by
    rw [← hZt]
    exact inf_le_left
  have hH : centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) ⊓
      centerMod (yamadaU₁ d t) ((yamadaP d t ⊓ Λ₁)ᵍ[d.wa]) ≤ yamadaU₁ d t := by
    rw [← hZr, ← hne]
  obtain ⟨e₀, he₀D, he₀P₂, he₀F⟩ :=
    exists_mem_yamadaD₇_inf_not_mem_yamadaF₅ hW h d hK hQ hL
  have hee : t⁻¹ * (t * e₀ * t⁻¹) * t = e₀ := by group
  have heD : t * e₀ * t⁻¹ ∈ yamadaD₇ d t := (mem_normalizer_iff.1 htD₇ e₀).1 he₀D
  have heF : t * e₀ * t⁻¹ ∉ yamadaF₅ d t := fun hF => he₀F (by
    have := (mem_normalizer_iff.1 (inv_mem htF₅) _).1 hF
    rwa [show t⁻¹ * (t * e₀ * t⁻¹) * t⁻¹⁻¹ = e₀ by group] at this)
  have hecomm := commutator_mem_yamadaY₂_of_labelled hW h d hK hQ hL _ heD
    (by rw [hee]; exact he₀P₂)
  obtain ⟨c, hcr, y, hy, hey⟩ := exists_mul_of_mem_yamadaD₇ hW h d hK hQ hp _ heD
  have hY₂N : yamadaP d t ≤ normalizer (yamadaY₂ d t : Set G) :=
    hPR₈.trans (Setup.Q52.yamadaR₈_le_normalizer_yamadaY₂ hW h d hK hQ)
  have hcy : c = (t * e₀ * t⁻¹) * y⁻¹ := eq_mul_inv_of_mul_eq hey.symm
  have hcY : ∀ p ∈ yamadaP d t ⊓ Λ₁, p * c * p⁻¹ * c⁻¹ ∈ yamadaY₂ d t := by
    intro p hp
    have hpP : p ∈ yamadaP d t := (Subgroup.mem_inf.1 hp).1
    have h1 := hecomm p hp
    have h2 : y⁻¹ * p * y⁻¹⁻¹ * p⁻¹ ∈ yamadaY₂ d t := by
      have := h.commutator_yamadaF₅_yamadaP_le hW d hK hQ y⁻¹ (inv_mem hy) p hpP
      rwa [commutatorElement_def] at this
    have h3 : (t * e₀ * t⁻¹) * (p * y⁻¹ * p⁻¹ * y) * (t * e₀ * t⁻¹)⁻¹ ∈ yamadaY₂ d t := by
      refine (mem_normalizer_iff.1 (hY₂N (hDP heD)) _).1 ?_
      have := inv_mem h2
      rwa [show (y⁻¹ * p * y⁻¹⁻¹ * p⁻¹)⁻¹ = p * y⁻¹ * p⁻¹ * y by group] at this
    have e : p * c * p⁻¹ * c⁻¹ =
        (p * (t * e₀ * t⁻¹) * p⁻¹ * (t * e₀ * t⁻¹)⁻¹) *
          ((t * e₀ * t⁻¹) * (p * y⁻¹ * p⁻¹ * y) * (t * e₀ * t⁻¹)⁻¹) := by
      rw [hcy]; group
    rw [e]
    exact mul_mem h1 h3
  have hPU : yamadaP d t ⊓ Λ₁ ≤ normalizer (yamadaU₁ d t : Set G) :=
    (inf_le_left.trans hPR₈).trans (Setup.Q52.yamadaR₈_le_normalizer_yamadaU₁ hW h d hK hQ)
  have hcU : c ∈ yamadaU₁ d t :=
    le_of_mem_conj_of_commutator_mem (U := yamadaU₁ d t) (Y := yamadaY₂ d t)
      (D := yamadaD₇ d t) (P₁ := yamadaP d t ⊓ Λ₁) (Λ := Λ₁) (t := t) (r := d.wa) htt htr
      hU₁Y₂ hY₂D₇ (le_inf hDP hD₇Λ₁) inf_le_right hPU htU₁ hrU htY₂ hrD hrΛ hL.fac₁.comm hY hH
      hcr hcY
  exact heF (by
    rw [hey]
    exact mul_mem (Setup.JWeight.U₁_le_F₅ d t hcU) hy)

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
