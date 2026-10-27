module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem card_piSub_V0
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    Nat.card (piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (W ⊓ oP W))) = 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hβZ, -⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hS' := hJ.card_piSub_W hW
  obtain ⟨ζ, hζS, -, hζc, hζR, o₁, o₂, ho₁, ho₂, hodd₁, hodd₂, hcl⟩ :=
    sylow_centralizer_facts (piSub_le_P _ _) hS'
  have hζP : ζ ∈ P := piSub_le_P _ _ hζS
  have hCζ : centralizerIn P ζ ≤
      piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (oP W)) := by
    rw [← hcl, closure_le]
    intro o ho
    rcases ho with rfl | rfl
    · exact hJ.mem_piSub_oP hKC hW hUW hζP hζR ho₁ hodd₁
    · exact hJ.mem_piSub_oP hKC hW hUW hζP hζR ho₂ hodd₂
  have hS'le : piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≤
      piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (oP W)) :=
    fun s hs' => hCζ (mem_centralizerIn.mpr ⟨piSub_le_P _ _ hs', (hζc s hs').symm⟩)
  have hWM : W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := hW.le
  have hWP : W ≤ centralizer (zW W : Set X) := fun y hy =>
    mem_centralizer_iff.mpr fun x hx => (mem_centralizer_iff.mp (mem_inf.mp hx).2 y hy).symm
  have hPM : centralizer (zW W : Set X) ≤
      centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy _ hβZ).symm
  have h1 : IsSylowOf 2 W (centralizer (zW W : Set X)) := hW.of_le hWP hPM
  have hOP : oP W ≤ centralizer (zW W : Set X) := by
    rw [oP, closure_le]
    exact fun x hx => hx.1
  have hPN : centralizer (zW W : Set X) ≤ normalizer (oP W : Set X) :=
    le_normalizer_of_conj_mem (conj_mem_oP_of fun y hy x hx => mul_mem (mul_mem hy hx) (inv_mem hy))
  have h2 : IsSylowOf 2 (W ⊓ oP W) (oP W) := h1.inf_of_le_normalizer hOP hPN
  have hOM := hOP.trans hPM
  have h3 : IsSylowOf 2 ((W ⊓ oP W).subgroupOf
      (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
      ((oP W).subgroupOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) := by
    rw [← isSylowOf_map_subtype_iff, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left (inf_le_right.trans hOM), inf_of_le_left hOM]
    exact h2
  have h4 := HarrisLit.isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2
    ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) h3
  have h5 := isSylowOf_piSub π h4 (hJ.barOf_oP_le hβZ)
  have hS'2 : IsPGroup 2 (piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :=
    IsPGroup.of_card (n := 7) (by rw [hS']; norm_num)
  apply le_antisymm (card_le_128 h5.isPGroup (piSub_le_P _ _))
  rw [← hS']
  calc Nat.card (piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
      ≤ twoPart (piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (oP W))) :=
        card_le_twoPart hS'2 hS'le
    _ = _ := h5.card_eq.symm

theorem commutator_cW_le
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    ⁅cW W, W⁆ ≤ preimageOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  have hcard := hJ.card_piSub_V0 hKC hW hUW
  obtain ⟨ζ, hζS, hζ1, hζc, hζR, -⟩ := sylow_centralizer_facts (piSub_le_P _ _) hcard
  have hζP : ζ ∈ P := piSub_le_P _ _ hζS
  have hWM : W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := hW.le
  rw [commutator_le]
  intro c hc w' hw'
  have hcM := hWM (mem_inf.mp hc).1
  have hwM := hWM hw'
  have hcwM : ⁅c, w'⁆ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hcM hwM) (inv_mem hcM)) (inv_mem hwM)
  rw [mem_preimageOf hcwM, ← hJ.theta_eq_one_iff]
  have heq' : (⟨⁅c, w'⁆, hcwM⟩ :
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) =
      ⁅(⟨c, hcM⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))),
        ⟨w', hwM⟩⁆ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have heq : (QuotientGroup.mk ⟨⁅c, w'⁆, hcwM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      ⁅(QuotientGroup.mk ⟨c, hcM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        QuotientGroup.mk ⟨w', hwM⟩⁆ := by
    rw [heq']
    exact map_commutatorElement (QuotientGroup.mk' _) _ _
  rw [heq]
  refine hJ.theta_commutator_eq_one hζP hζ1 hζc hζR ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    have h1 : (v : X) * c = c * v := mem_centralizer_iff.mp (mem_inf.mp hc).2 _ hv
    change (QuotientGroup.mk (⟨c, hcM⟩ * v) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk (v * ⟨c, hcM⟩)
    rw [show (⟨c, hcM⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) * v =
      v * ⟨c, hcM⟩ from Subtype.ext h1.symm]
  · rintro _ ⟨v, hv, rfl⟩
    have h1 : w'⁻¹ * v * w' ∈ W ⊓ oP W := by
      have := conj_mem_inf' conj_mem_W conj_mem_oP w'⁻¹ (inv_mem (le_normalizer_self hw'))
        (v : X) hv
      rwa [inv_inv] at this
    refine ⟨⟨w', hwM⟩⁻¹ * v * ⟨w', hwM⟩, h1, ?_⟩
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem normalizer_W_le
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≠
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    normalizer (W : Set X) ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hβZ, -⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hWM : W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := hW.le
  have htW : t ∈ W := hUW (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  have hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ W := (mem_inf.mp hβZ).1
  have hK := hJ.commutator_cW_le hKC hW hUW
  have hβ2 := orderOf_eq_prime hs.betaBar_sq hs.betaBar_ne_one
  have hU : ∀ x ∈ uW W, x = 1 ∨ x = w ^ (orderOf w / 2) * t ^ i * z ^ j := by
    intro x hx
    obtain ⟨hxK, hxZ⟩ := mem_inf.mp hx
    have hxW : x ∈ W := (mem_inf.mp hxZ).1
    have hxQ := (mem_preimageOf (hWM hxW)).mp (hK hxK)
    have hxt : (QuotientGroup.mk ⟨x, hWM hxW⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        centralizer {hs.setup.tBar i j} := by
      rw [mem_centralizer_singleton_iff]
      have h1 : t * x = x * t := mem_centralizer_iff.mp (mem_inf.mp hxZ).2 t htW
      change (QuotientGroup.mk (⟨x, hWM hxW⟩ * ⟨t, hWM htW⟩) :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = QuotientGroup.mk (⟨t, hWM htW⟩ * ⟨x, _⟩)
      rw [show (⟨x, hWM hxW⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
        Set X))) * ⟨t, hWM htW⟩ = ⟨t, hWM htW⟩ * ⟨x, hWM hxW⟩ from Subtype.ext h1.symm]
    have hx' : (QuotientGroup.mk ⟨x, hWM hxW⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [← hs.pCore_inf_centralizer_tBar]
      exact ⟨hxQ, hxt⟩
    rcases eq_one_or_eq_of_mem_zpowers hβ2 hx' with h | h
    · left
      exact mk_injOn hWM hW.isPGroup hxW (one_mem W) (by rw [h]; rfl)
    · right
      exact mk_injOn hWM hW.isPGroup hxW hβW (by rw [h]; rfl)
  have hKne : ⁅cW W, W⁆ ≠ ⊥ := by
    have hQt : ¬ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
        centralizer {hs.setup.tBar i j} := by
      intro h
      apply hQ
      rw [← hs.pCore_inf_centralizer_tBar, inf_of_le_left h]
    obtain ⟨q, hq, hqt⟩ := IsConcreteLE.not_le_iff_exists.mp hQt
    have hqW := le_of_isSylowOf_top (isSylowOf_barOf hW) pCore_isPGroup hq
    obtain ⟨x, hxW, rfl⟩ := hqW
    have hxC : (x : X) ∈ cW W := by
      refine mem_inf.mpr ⟨hxW, mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hvW : v ∈ W := (mem_inf.mp hv).1
      have hvE : (QuotientGroup.mk ⟨v, hWM hvW⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
          layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
        hJ.barOf_oP_le hβZ ⟨⟨v, hWM hvW⟩, (mem_inf.mp hv).2, rfl⟩
      have hq' := hq
      rw [← hs.centralizer_layer_eq hJ.h412] at hq'
      have h1 := mem_centralizer_iff.mp hq' _ hvE
      refine mk_injOn hWM hW.isPGroup (mul_mem hvW hxW) (mul_mem hxW hvW) ?_
      change (QuotientGroup.mk (⟨v, hWM hvW⟩ * x) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
        QuotientGroup.mk (x * ⟨v, hWM hvW⟩)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact h1
    intro hbot
    have hmem := commutator_mem_commutator hxC htW
    rw [hbot, mem_bot, commutatorElement_def] at hmem
    apply hqt
    rw [mem_centralizer_singleton_iff]
    have hxt : (x : X) * t = t * x := by
      calc (x : X) * t = (x * t * (x : X)⁻¹ * t⁻¹) * (t * x) := by group
        _ = t * x := by rw [hmem, one_mul]
    change (QuotientGroup.mk (x * ⟨t, hWM htW⟩) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk (⟨t, hWM htW⟩ * x)
    rw [show x * (⟨t, hWM htW⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
      Set X))) = ⟨t, hWM htW⟩ * x from Subtype.ext hxt]
  have hKW : ⁅cW W, W⁆ ≤ W := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    have haW := (mem_inf.mp ha).1
    exact mul_mem (mul_mem (mul_mem haW hb) (inv_mem haW)) (inv_mem hb)
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_zW_ne_bot hW.isPGroup hKW le_normalizer_commutator_cW hKne)
  have hβU : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ uW W := by
    rcases hU x hx with h | h
    · exact absurd (Subtype.ext h) hx1
    · rw [← h]
      exact hx
  exact normalizer_le_of_uW hβU hs.beta.ne_one hU

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
