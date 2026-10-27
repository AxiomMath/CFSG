module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub4

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

theorem piSub_W_le_oP
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≤
      piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (oP W)) := by
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
  exact fun s hs' => hCζ (mem_centralizerIn.mpr ⟨piSub_le_P _ _ hs', (hζc s hs').symm⟩)

theorem mem_oP_of_bar {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    {d : X} (hdW : d ∈ W)
    (hd : (QuotientGroup.mk ⟨d, hW.le hdW⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (oP W)) : d ∈ oP W := by
  obtain ⟨o, ho, hoeq⟩ := mem_barOf.mp hd
  rw [QuotientGroup.eq] at hoeq
  set k : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
    o⁻¹ * ⟨d, hW.le hdW⟩ with hk
  have hkodd : Odd (orderOf (k : X)) := by
    rw [Subgroup.orderOf_coe]
    have hdvd := orderOf_dvd_natCard (⟨k, hoeq⟩ : ↥(pPrimeCore 2
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))))
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hdvd
  have hoC : (o : X) ∈ centralizer (zW W : Set X) := by
    have : oP W ≤ centralizer (zW W : Set X) := by
      rw [oP, closure_le]
      exact fun x hx => hx.1
    exact this ho
  have hdC : d ∈ centralizer (zW W : Set X) :=
    mem_centralizer_iff.mpr fun x hx => (mem_centralizer_iff.mp (mem_inf.mp hx).2 d hdW).symm
  have hkC : (k : X) ∈ centralizer (zW W : Set X) := by
    rw [hk, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem hoC) hdC
  have hkO : (k : X) ∈ oP W := Subgroup.subset_closure ⟨hkC, hkodd⟩
  have : d = (o : X) * k := by rw [hk, Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [this]
  exact mul_mem ho hkO

theorem mem_V0_of_bar_mem
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) (hπi : Function.Injective π)
    {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) {d : X}
    (hdW : d ∈ W)
    (hdE : (QuotientGroup.mk ⟨d, hW.le hdW⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : d ∈ W ⊓ oP W := by
  refine mem_inf.mpr ⟨hdW, mem_oP_of_bar hW hdW ?_⟩
  have h1 : ((π ⟨_, hdE⟩ : P) : Equiv.Perm (Fin 315)) ∈
      piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    mem_piSub.mpr ⟨⟨_, hdE⟩, ⟨mk_mem_barOf _ hdW, hdE⟩, rfl⟩
  obtain ⟨a, haO, hae⟩ := mem_piSub.mp (hJ.piSub_W_le_oP hKC hW hUW h1)
  have : a = ⟨_, hdE⟩ := hπi (Subtype.ext hae)
  rw [this] at haO
  exact haO

theorem exists_V0_mul
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) (hπi : Function.Injective π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) {x : X}
    (hxW : x ∈ W) :
    ∃ v ∈ W ⊓ oP W, (x = v ∨ x = v * t ∨ x = v * (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∨
      x = v * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * t)) := by
  have hWM := hW.le
  have htW : t ∈ W := hUW (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  obtain ⟨hβZ, -⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ W := (mem_inf.mp hβZ).1
  have hn : ∀ k ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      hs.setup.tBar i j * k * (hs.setup.tBar i j)⁻¹ ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := fun k hk =>
    (inferInstance : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal).conj_mem k hk _
  have hsq : hs.setup.tBar i j ^ 2 ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [hs.tBar_sq]
    exact one_mem _
  have hct : ∀ e, betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * e =
      e * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    fun e => (mem_center_iff.mp (betaBar_mem_center _) e).symm
  have hmk : ∀ (a b : X) (ha : a ∈ W) (hb : b ∈ W),
      (QuotientGroup.mk ⟨a * b⁻¹, hWM (mul_mem ha (inv_mem hb))⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk ⟨a, hWM ha⟩ * (QuotientGroup.mk ⟨b, hWM hb⟩)⁻¹ := by
    intro a b ha hb
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  obtain ⟨a, haA, ha⟩ := hJ.exists_mem_A hQ (QuotientGroup.mk ⟨x, hWM hxW⟩)
  rcases (mem_sup_zpowers_iff hn hsq).mp haA with haE | haE <;> rcases ha with ha | ha
  · exact ⟨x, hJ.mem_V0_of_bar_mem hKC hπi hW hUW hxW (ha ▸ haE), Or.inl rfl⟩
  · refine ⟨x * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹, hJ.mem_V0_of_bar_mem hKC hπi hW hUW
      (mul_mem hxW (inv_mem hβW)) ?_, Or.inr (Or.inr (Or.inl (by group)))⟩
    rw [hmk _ _ hxW hβW, ha]
    change betaBar _ * a * (betaBar _)⁻¹ ∈ _
    rw [hct a, mul_inv_cancel_right]
    exact haE
  · refine ⟨x * t⁻¹, hJ.mem_V0_of_bar_mem hKC hπi hW hUW (mul_mem hxW (inv_mem htW)) ?_,
      Or.inr (Or.inl (by group))⟩
    rw [hmk _ _ hxW htW, ha]
    exact haE
  · refine ⟨x * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * t)⁻¹, hJ.mem_V0_of_bar_mem hKC hπi hW
      hUW (mul_mem hxW (inv_mem (mul_mem hβW htW))) ?_, Or.inr (Or.inr (Or.inr (by group)))⟩
    rw [hmk _ _ hxW (mul_mem hβW htW), ha]
    change betaBar _ * a * (betaBar _ * hs.setup.tBar i j)⁻¹ ∈ _
    have hconj : ∀ y, betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y *
        (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ = y := fun y => by
      rw [hct y, mul_inv_cancel_right]
    rw [show betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * a *
      (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * hs.setup.tBar i j)⁻¹ =
        betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (a * (hs.setup.tBar i j)⁻¹) *
          (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ by group, hconj]
    exact haE

theorem card_W_ge
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) (hπi : Function.Injective π)
    {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W)
    (hV₀ : Nat.card ↥(W ⊓ oP W) = 128) : 512 ≤ Nat.card W := by
  have hWM := hW.le
  have htW : t ∈ W := hUW (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  obtain ⟨hβZ, -⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ W := (mem_inf.mp hβZ).1
  have hVbE := hJ.barOf_V0_le hKC hW hUW
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
    hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hconjV : ∀ g ∈ W, ∀ v ∈ W ⊓ oP W, g * v * g⁻¹ ∈ W ⊓ oP W := fun g hg =>
    conj_mem_inf' conj_mem_W conj_mem_oP g (le_normalizer_self hg)
  have htE : hs.setup.tBar i j ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [← hJ.theta_mem_inner_iff]
    exact hJ.alpha_not_mem
  have hβV : w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ W ⊓ oP W := fun h =>
    hJ.betaBar_not_mem_layer hπi (hVbE (mk_mem_barOf (mem_centralizer_singleton_iff.mpr rfl) h))
  have hK₁ := card_sup_zpowers (fun v hv => hconjV _ hβW v hv) (by rw [hβ2]; exact one_mem _) hβV
  rw [hV₀] at hK₁
  have hnK : ∀ k ∈ (W ⊓ oP W) ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      t * k * t⁻¹ ∈ (W ⊓ oP W) ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    intro k hk
    rcases (mem_sup_zpowers_iff (fun v hv => hconjV _ hβW v hv)
      (by rw [hβ2]; exact one_mem _)).mp hk with h | h
    · exact mem_sup_left (hconjV t htW k h)
    · have htβ : t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
          (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t :=
        mem_centralizer_singleton_iff.mp (hs.setup.t_mem_centralizer_beta i j)
      rw [show t * k * t⁻¹ = (t * (k * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹) * t⁻¹) *
        (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t⁻¹) by group, htβ,
        show (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t * t⁻¹ =
          w ^ (orderOf w / 2) * t ^ i * z ^ j by group]
      exact mul_mem (mem_sup_left (hconjV t htW _ h)) (mem_sup_right (mem_zpowers _))
  have htK : t ∉ (W ⊓ oP W) ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    intro h
    rcases (mem_sup_zpowers_iff (fun v hv => hconjV _ hβW v hv)
      (by rw [hβ2]; exact one_mem _)).mp h with h1 | h1
    · apply htE
      exact mem_sup_left (hVbE (mk_mem_barOf (hs.setup.t_mem_centralizer_beta i j) h1))
    · apply htE
      have h2 := hVbE (mk_mem_barOf (hWM (mul_mem htW (inv_mem hβW))) h1)
      rw [show hs.setup.tBar i j = (QuotientGroup.mk ⟨t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹,
        hWM (mul_mem htW (inv_mem hβW))⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
          betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) by
        rw [Standing.Setup42.tBar, betaBar, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group]
      exact mul_mem (mem_sup_left h2) (mem_sup_right hs.betaBar_mem_pCore)
  have hK₂ := card_sup_zpowers hnK (by rw [ht2]; exact one_mem _) htK
  rw [hK₁] at hK₂
  have hle : (W ⊓ oP W) ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers t ≤ W :=
    sup_le (sup_le inf_le_left (zpowers_le.mpr hβW)) (zpowers_le.mpr htW)
  have := Subgroup.card_le_of_le hle
  omega

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
