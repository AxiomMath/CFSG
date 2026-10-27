module

public import CFSG.ClassicalInvolution.Asc77.AscCX1
public import CFSG.ClassicalInvolution.Asc77.AscCX2
public import CFSG.ClassicalInvolution.Asc77.AscC25W14
import CFSG.ClassicalInvolution.Asc77.AscCX6Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section TwoGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_sq_mem {A H : Subgroup G} (hA : IsPGroup 2 A) (hHA : H ≤ A)
    (hne : H ≠ A) :
    ∃ x ∈ A, x ∉ H ∧ x ∈ Subgroup.normalizer (H : Set G) ∧ x * x ∈ H := by
  classical
  have hnil : Group.IsNilpotent ↥A := hA.isNilpotent
  have hlt : H.subgroupOf A < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    refine le_antisymm hHA fun a ha => ?_
    have : (⟨a, ha⟩ : ↥A) ∈ H.subgroupOf A := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨y, hyN, hyH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  obtain ⟨k, hk⟩ := (hA.to_le (le_refl A)) y
  have hex : ∃ j, (y : G) ^ (2 ^ j) ∈ H := ⟨k, by
    have : y ^ (2 ^ k) = 1 := hk
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
    exact H.one_mem⟩
  let j := Nat.find hex
  have hj0 : j ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [show Nat.find hex = 0 from h0, pow_zero, pow_one] at this
    exact hyH (Subgroup.mem_subgroupOf.mpr this)
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hiH : (y : G) ^ (2 ^ i) ∉ H := Nat.find_min hex (by omega)
  have hjH : (y : G) ^ (2 ^ (i + 1)) ∈ H := hi ▸ Nat.find_spec hex
  refine ⟨(y : G) ^ (2 ^ i), A.pow_mem y.2 _, hiH, ?_, ?_⟩
  · have hyN' : (y : G) ∈ Subgroup.normalizer (H : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        by_cases hhA : h ∈ A
        · have h1 := (Subgroup.mem_normalizer_iff.mp hyN ⟨h, hhA⟩).mp
            (Subgroup.mem_subgroupOf.mpr hh)
          exact Subgroup.mem_subgroupOf.mp h1
        · exact absurd (hHA hh) hhA
      · intro hh
        have hA' : (y : G) * h * (y : G)⁻¹ ∈ A := hHA hh
        have hhA : h ∈ A := by
          have : h = (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * y := by group
          rw [this]
          exact A.mul_mem (A.mul_mem (A.inv_mem y.2) hA') y.2
        have h1 := (Subgroup.mem_normalizer_iff.mp hyN ⟨h, hhA⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hh)
        exact Subgroup.mem_subgroupOf.mp h1
    exact Subgroup.pow_mem _ hyN' _
  · rw [← pow_two, ← pow_mul, ← pow_succ]
    exact hjH

theorem exists_central_involution {E B : Subgroup G} (hE : IsPGroup 2 E) (hBE : B ≤ E)
    (hEB : E ≤ Subgroup.normalizer (B : Set G)) (hB : B ≠ ⊥) :
    ∃ b ∈ B, b ≠ 1 ∧ b * b = 1 ∧ ∀ e ∈ E, e * b = b * e := by
  classical
  have hnil : Group.IsNilpotent ↥E := hE.isNilpotent
  have hnormal : (B.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEB
  have hne : B.subgroupOf E ≠ ⊥ := by
    intro h
    apply hB
    rw [← Subgroup.map_subgroupOf_eq_of_le hBE, h, Subgroup.map_bot]
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hZ2 : IsPGroup 2 ↥(B.subgroupOf E ⊓ Subgroup.center ↥E) := hE.to_subgroup _
  have hcard : 2 ∣ Nat.card ↥(B.subgroupOf E ⊓ Subgroup.center ↥E) :=
    hZ2.card_eq_or_dvd.resolve_left fun h => hZ (Subgroup.card_eq_one.mp h)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B.subgroupOf E ⊓ Subgroup.center ↥E))
    2 hcard
  refine ⟨((v : ↥E) : G), Subgroup.mem_subgroupOf.mp v.2.1, ?_, ?_, ?_⟩
  · intro h1
    have : v = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hv
    omega
  · have h2 : v ^ 2 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
    have : ((v : ↥E) : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, h2]
      rfl
    rwa [pow_two] at this
  · intro e he
    have hc := Subgroup.mem_center_iff.mp v.2.2 ⟨e, he⟩
    exact congrArg Subtype.val hc

theorem inf_conjSub_ne_bot {D : Subgroup G} {z x : G} (hzc : ∀ d ∈ D, d * z = z * d)
    (hcover : ∀ h ∈ conjSub x D, h ∈ D ∨ h * z ∈ D) (h4 : 4 ≤ Nat.card D) :
    D ⊓ conjSub x D ≠ ⊥ := by
  classical
  intro hbot
  have hzD : ∀ g : G, z⁻¹ * g * z ∈ D → g ∈ D := by
    intro g hg
    have h1 : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
    have hc := hzc _ hg
    rw [← h1]
    have h2 : z * (z⁻¹ * g * z) * z⁻¹ = z⁻¹ * g * z := by
      calc z * (z⁻¹ * g * z) * z⁻¹ = (z⁻¹ * g * z) * z * z⁻¹ := by rw [← hc]
        _ = z⁻¹ * g * z := by group
    rw [h2]
    exact hg
  have hmem : ∀ u ∈ conjSub x D, u ≠ 1 → u * z ∈ D := by
    intro u hu hu1
    rcases hcover u hu with h | h
    · exfalso
      have : u ∈ D ⊓ conjSub x D := ⟨h, hu⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hu1 this
    · exact h
  have hinj : Function.Injective
      (fun u : conjSub x D => if (u : G) = 1 then (0 : Fin 2) else 1) := by
    intro u v huv
    apply Subtype.ext
    by_cases hu : (u : G) = 1 <;> by_cases hv : (v : G) = 1 <;>
      simp only [hu, hv, ↓reduceIte] at huv
    · rw [hu, hv]
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · have h1 := hmem u u.2 hu
      have h2 := hmem v v.2 hv
      have h3 : (u : G)⁻¹ * v ∈ D := by
        apply hzD
        have : z⁻¹ * ((u : G)⁻¹ * v) * z = ((u : G) * z)⁻¹ * ((v : G) * z) := by group
        rw [this]
        exact D.mul_mem (D.inv_mem h1) h2
      have h4' : (u : G)⁻¹ * v ∈ conjSub x D :=
        (conjSub x D).mul_mem ((conjSub x D).inv_mem u.2) v.2
      have : (u : G)⁻¹ * v ∈ D ⊓ conjSub x D := ⟨h3, h4'⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (inv_mul_eq_one.mp this)
  have h2 : Nat.card (conjSub x D) ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective _ hinj
  have h3 : Nat.card (conjSub x D) = Nat.card D := by
    unfold conjSub
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  rw [Nat.card_fin, h3] at h2
  omega

theorem exists_sup_central {D : Subgroup G} {z : G} (hz2 : z * z = 1)
    (hzc : ∀ d ∈ D, d * z = z * d) : ∃ H : Subgroup G, ∀ g, g ∈ H ↔ g ∈ D ∨ g * z ∈ D := by
  have hzi : z⁻¹ = z := by
    calc z⁻¹ = z⁻¹ * (z * z) := by rw [hz2, mul_one]
      _ = z := by group
  have hcomm : ∀ g, g * z ∈ D → g * z = z * g := by
    intro g hg
    have h1 := hzc _ hg
    calc g * z = (g * z) * z * z⁻¹ := by group
      _ = z * (g * z) * z⁻¹ := by rw [h1]
      _ = z * g := by group
  have hmul : ∀ {a b : G}, a ∈ {g | g ∈ D ∨ g * z ∈ D} → b ∈ {g | g ∈ D ∨ g * z ∈ D} →
      a * b ∈ {g | g ∈ D ∨ g * z ∈ D} := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (D.mul_mem ha hb)
    · right
      simpa [mul_assoc] using D.mul_mem ha hb
    · right
      have : a * b * z = a * z * b := by rw [mul_assoc, mul_assoc, hzc b hb]
      show a * b * z ∈ D
      rw [this]
      exact D.mul_mem ha hb
    · left
      have : a * b = (a * z) * (b * z) := by
        calc a * b = a * (z * z) * b := by rw [hz2, mul_one]
          _ = (a * z) * (z * b) := by group
          _ = (a * z) * (b * z) := by rw [hcomm b hb]
      show a * b ∈ D
      rw [this]
      exact D.mul_mem ha hb
  have hinv : ∀ {a : G}, a ∈ {g | g ∈ D ∨ g * z ∈ D} → a⁻¹ ∈ {g | g ∈ D ∨ g * z ∈ D} := by
    rintro a (ha | ha)
    · exact Or.inl (D.inv_mem ha)
    · right
      show a⁻¹ * z ∈ D
      have h1 : a⁻¹ * z = (a * z)⁻¹ := by
        rw [mul_inv_rev, hzi]
        calc a⁻¹ * z = a⁻¹ * z * (a * a⁻¹) := by group
          _ = a⁻¹ * (z * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * z) * a⁻¹ := by rw [hcomm a ha]
          _ = z * a⁻¹ := by group
      rw [h1]
      exact D.inv_mem ha
  let H : Subgroup G :=
    { carrier := {g | g ∈ D ∨ g * z ∈ D}
      one_mem' := Or.inl D.one_mem
      mul_mem' := hmul
      inv_mem' := hinv }
  exact ⟨H, fun g => Iff.rfl⟩

end TwoGroups

section Choice

variable {E M : Type} [Group E] [Group M]

theorem eq_of_card_le_four [Finite M] {P : Subgroup M} (hP4 : Nat.card P ≤ 4) {β ζ g : M}
    (hβ : β ∈ P) (hζ : ζ ∈ P) (hg : g ∈ P) (h1 : β ≠ 1) (h2 : β ≠ ζ) (h3 : ζ ≠ 1) (h4 : β * ζ ≠ 1)
    (_h5 : β * ζ ≠ β) (_h6 : β * ζ ≠ ζ) : g = 1 ∨ g = β ∨ g = ζ ∨ g = β * ζ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨g1, gβ, gζ, gβζ⟩ := hcon
  let v : Fin 5 → P := ![⟨1, P.one_mem⟩, ⟨β, hβ⟩, ⟨ζ, hζ⟩, ⟨β * ζ, P.mul_mem hβ hζ⟩, ⟨g, hg⟩]
  have hinj : Function.Injective v := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [v, eq_comm]
  have := Nat.card_le_card_of_injective v hinj
  rw [Nat.card_fin] at this
  omega

theorem exists_beta [Finite M] (lam : E →* M) (hexp : ∀ e : E, lam e * lam e = 1)
    (hcard : Nat.card lam.range ≤ 4) {z₀ : E} (hζ1 : lam z₀ ≠ 1) {D : Subgroup E}
    (hD : ∀ d ∈ D, lam d ≠ lam z₀) :
    ∃ β : M, β * β = 1 ∧ β ≠ lam z₀ ∧ (β = 1 ∨ ∃ e : E, lam e = β) ∧
      (∀ d ∈ D, lam d = 1 ∨ lam d = β) ∧
      ∀ e : E, (lam e = 1 ∨ lam e = β) ∨ (lam (e * z₀) = 1 ∨ lam (e * z₀) = β) := by
  classical
  set ζ := lam z₀ with hζ
  have hζζ : ζ * ζ = 1 := hexp z₀
  have hζi : ζ⁻¹ = ζ := by
    calc ζ⁻¹ = ζ⁻¹ * (ζ * ζ) := by rw [hζζ, mul_one]
      _ = ζ := by group
  have hmemP : ∀ e : E, lam e ∈ lam.range := fun e => ⟨e, rfl⟩
  have hfour : ∀ e : E, lam e ≠ 1 → lam e ≠ ζ → ∀ g : E,
      lam g = 1 ∨ lam g = lam e ∨ lam g = ζ ∨ lam g = lam e * ζ := by
    intro e he1 heζ g
    refine eq_of_card_le_four hcard (hmemP e) (hmemP z₀) (hmemP g) he1 heζ hζ1 ?_ ?_ ?_
    · intro h
      apply heζ
      calc lam e = lam e * (ζ * ζ) := by rw [hζζ, mul_one]
        _ = (lam e * ζ) * ζ := by group
        _ = ζ := by rw [h, one_mul]
    · intro h
      apply hζ1
      calc ζ = (lam e)⁻¹ * (lam e * ζ) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
    · intro h
      apply he1
      calc lam e = lam e * ζ * ζ⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]
  have hmulz : ∀ g : E, lam (g * z₀) = lam g * ζ := fun g => map_mul lam g z₀
  by_cases hex : ∃ e : E, lam e ≠ 1 ∧ lam e ≠ ζ ∧ ∀ d ∈ D, lam d = 1 ∨ lam d = lam e
  · obtain ⟨e, he1, heζ, heD⟩ := hex
    refine ⟨lam e, hexp e, heζ, Or.inr ⟨e, rfl⟩, heD, fun g => ?_⟩
    rcases hfour e he1 heζ g with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · right; left
      rw [hmulz, h, hζζ]
    · right; right
      rw [hmulz, h, mul_assoc, hζζ, mul_one]
  · push Not at hex
    have hD1 : ∀ d ∈ D, lam d = 1 := by
      intro d hd
      by_contra hd1
      obtain ⟨d', hd', hd'1, hd'd⟩ := hex d hd1 (hD d hd)
      rcases hfour d hd1 (hD d hd) d' with h | h | h | h
      · exact hd'1 h
      · exact hd'd h
      · exact hD d' hd' h
      · apply hD (d⁻¹ * d') (D.mul_mem (D.inv_mem hd) hd')
        rw [map_mul, map_inv, h]
        group
    refine ⟨1, one_mul 1, fun h => hζ1 h.symm, Or.inl rfl, fun d hd => Or.inl (hD1 d hd),
      fun g => ?_⟩
    by_cases hg1 : lam g = 1
    · exact Or.inl (Or.inl hg1)
    · by_cases hgζ : lam g = ζ
      · right; left
        rw [hmulz, hgζ, hζζ]
      · exfalso
        obtain ⟨d, hd, hd1, -⟩ := hex g hg1 hgζ
        exact hd1 (hD1 d hd)

end Choice

section Core

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem twinFacts_of_bad (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {b : G} (hbA : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbad : z ∉ zStarOf (Subgroup.centralizer ({b} : Set G))) :
    ∃ hzY : z ∈ exactLayer Ω b, K ∈ tqMembers Ω b ∧ K' ∈ tqMembers Ω b ∧
      LayerTwinFacts (T7H.exactImg Ω b K) (T7H.exactImg Ω b K') (T7H.toBar Ω b z hzY) := by
  have hst := hyp.std.setting.stand
  have hcent := Subgroup.mem_centralizer_iff.mp hbA.2
  have haR : ∀ x ∈ R, b * x = x * b := fun x hx => (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', b * x = x * b := fun x hx => (hcent x (Subgroup.mem_sup_right hx)).symm
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', -, -, htw⟩ := C25X.layer_a_frame hyp hb2 hb1 haR haR'
  rcases C25X.layer_a_typed_proved hyp hb2 hb1 haR haR' with h | h | h
  · exact absurd h hbad
  · obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h
    exact ⟨hzY, hK₂, hK₂', layerTwinFacts_five hst.odd hst.five D hD1
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw⟩
  · obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h
    exact ⟨hzY, hK₂, hK₂', h6 _ _ D _ _ _ _ _ hD1 ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw⟩

theorem mk_ne_one_of_involution {Y : Subgroup G} {z : G} (hzY : z ∈ Y) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) :
    (QuotientGroup.mk ⟨z, hzY⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff] at h
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hdvd : orderOf (⟨⟨z, hzY⟩, h⟩ : ↥(classicalInvolutionOddCore ↥Y)) ∣
      Nat.card (classicalInvolutionOddCore ↥Y) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzo] at hdvd
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card ↥Y))
    (even_iff_two_dvd.mpr hdvd)

theorem conj_ne_one_of_center_eq_bot {M : Type} [Group M] (hcen : Subgroup.center M = ⊥)
    {w : M} (hw : w ≠ 1) : MulAut.conj w ≠ 1 := by
  intro h
  apply hw
  have hwc : w ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut M => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * w = w * g * w⁻¹ * w := by rw [h1]
      _ = w * g := by group
  rwa [hcen, Subgroup.mem_bot] at hwc

theorem false_of_growth (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {D₀ D : Subgroup G}
    (hDA : D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hD₀D : D₀ ≤ D) (hbad : z ∉ zStarOf (Subgroup.centralizer (D : Set G)))
    (hmax : ∀ F : Subgroup G,
      F ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) → D₀ ≤ F →
        z ∉ zStarOf (Subgroup.centralizer (F : Set G)) → Nat.card F ≤ Nat.card D)
    {x b : G}
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hxD : x ∉ D) (hxzD : x * z ∉ D) (hbD : b ∈ D) (hb1 : b ≠ 1) (hb2 : b * b = 1)
    (hbx : x * b = b * x) (hbc : ∀ d ∈ D, d * b = b * d) : False := by
  classical
  have hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    T7T.z_mem_centralizer_of_hyp hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaMod p f Ω := hyp.std.setting.stand.hyp
  set E := D ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers z with hE
  have hEA : E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    sup_le (sup_le hDA (Subgroup.zpowers_le.mpr hxA)) (Subgroup.zpowers_le.mpr hzA)
  have hE2 : IsPGroup 2 E := S.isPGroup'.to_le (hEA.trans inf_le_left)
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hbc d hd)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbx)
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (hzS b (hDA hbD).1).symm)
  have hbbad : z ∉ zStarOf (Subgroup.centralizer ({b} : Set G)) :=
    C25W.not_mem_zStarOf_of_mem_badSub hbD (fun y hy => hzS y (hDA hy).1) hbad
  obtain ⟨hzY, hK₂, hK₂', hcen, hO, hO', hT2, hT3⟩ :=
    twinFacts_of_bad h6 hyp (hDA hbD) hb2 hb1 hbbad
  have hEY : ∀ e ∈ E, conjSub e (exactLayer Ω b) = exactLayer Ω b := fun e he =>
    conjSub_exactLayer hΩ.conjInvariant (hEb he)
  set lam := layerHom (exactLayer Ω b) E hEY with hlam
  have hb2' : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  have hfixK : ∀ e : E, ∀ y ∈ T7H.exactImg Ω b K, lam e y = y := fun e y hy =>
    layerAut_fix_exactImg hΩ hb2' hK₂ hO (hEb e.2) (mem_trivialOnQuot_of_mem_A hyp (hEA e.2)).1
      y hy
  have hfixK' : ∀ e : E, ∀ y ∈ T7H.exactImg Ω b K', lam e y = y := fun e y hy =>
    layerAut_fix_exactImg hΩ hb2' hK₂' hO' (hEb e.2) (mem_trivialOnQuot_of_mem_A hyp (hEA e.2)).2
      y hy
  have hP2 : IsPGroup 2 lam.range := by
    rw [MonoidHom.range_eq_map]
    exact (hE2.to_subgroup ⊤).map lam
  obtain ⟨hexpP, hcardP⟩ := hT2 lam.range hP2 fun β hβ => by
    obtain ⟨e, rfl⟩ := hβ
    exact ⟨hfixK e, hfixK' e⟩
  let z₀ : E := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  have hlamz : lam z₀ = MulAut.conj (T7H.toBar Ω b z hzY) := by
    ext y
    refine QuotientGroup.induction_on y fun y => ?_
    rw [hlam, layerHom_apply, C25Y.layerAut_mk, MulAut.conj_apply]
    unfold T7H.toBar
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1
  have hζ1 : lam z₀ ≠ 1 := by
    rw [hlamz]
    exact conj_ne_one_of_center_eq_bot hcen (mk_ne_one_of_involution hzY hz2 hz1)
  have hD : ∀ d ∈ D.subgroupOf E, lam d ≠ lam z₀ := by
    intro d hd heq
    apply hbad
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hzd : z ∈ Subgroup.centralizer ({(d : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hzS d (hDA hdD).1).symm
    have h1 := mem_zStarOf_of_layerAut_eq_conj hΩ (hEb d.2)
      (hEb (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))) hzd hzY hcen fun y => by
        have := congrArg (fun φ => φ y) heq
        simp only [hlamz, MulAut.conj_apply] at this
        exact this
    refine T7T.mem_zStarOf_of_le ?_ h1 ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hg b hbD).symm,
        Subgroup.mem_centralizer_singleton_iff.mpr (hg d hdD).symm⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hzS g (hDA hg).1
  obtain ⟨β, hβ2, hβζ, hβr, hβD, hcov⟩ := exists_beta lam (fun e => hexpP _ ⟨e, rfl⟩)
    hcardP hζ1 hD
  set F := ((Subgroup.zpowers β).comap lam).map E.subtype with hF
  have hzpow : ∀ γ ∈ Subgroup.zpowers β, γ = 1 ∨ γ = β := by
    intro γ hγ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
    rcases Int.even_or_odd' k with ⟨k', hk | hk⟩
    · left
      rw [hk, zpow_mul, zpow_two, hβ2, one_zpow]
    · right
      rw [hk, zpow_add_one, zpow_mul, zpow_two, hβ2, one_zpow, one_mul]
  have hmemF : ∀ e : E, (lam e = 1 ∨ lam e = β) → (e : G) ∈ F := by
    intro e he
    refine ⟨e, ?_, rfl⟩
    show lam e ∈ Subgroup.zpowers β
    rcases he with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers β
  have hFprop : ∀ g ∈ F, ∃ e : E, (e : G) = g ∧ (lam e = 1 ∨ lam e = β) := by
    rintro g ⟨e, he, rfl⟩
    exact ⟨e, rfl, hzpow _ he⟩
  have hDF : D ≤ F := fun d hd =>
    hmemF ⟨d, Subgroup.mem_sup_left (Subgroup.mem_sup_left hd)⟩
      (hβD _ (Subgroup.mem_subgroupOf.mpr hd))
  have hFE : F ≤ E := Subgroup.map_subtype_le _
  have hFA := hFE.trans hEA
  have hFb := hFE.trans hEb
  have hF2 : IsPGroup 2 F := hE2.to_le hFE
  let x₀ : E := ⟨x, Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))⟩
  have hxF : x ∈ F ∨ x * z ∈ F := by
    rcases hcov x₀ with h | h
    · exact Or.inl (hmemF x₀ h)
    · exact Or.inr (hmemF (x₀ * z₀) h)
  have hDltF : Nat.card D < Nat.card F := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne hDF fun hDFeq => ?_)
    rcases hxF with h | h
    · exact hxD (hDFeq ▸ h)
    · exact hxzD (hDFeq ▸ h)
  have hzC : z ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hzS g (hFA hg).1
  have hFbad : z ∉ zStarOf (Subgroup.centralizer (F : Set G)) := by
    by_cases hβ1 : β = 1
    · refine not_mem_zStarOf_of_layerAut_trivial hΩ hF2 hFb hzC hzY hz2 hz1 hcen ?_
      intro g hg y
      obtain ⟨e, rfl, he⟩ := hFprop g hg
      have h1 : lam e = 1 := by
        rcases he with h | h
        · exact h
        · rw [h, hβ1]
      have := congrArg (fun φ => φ y) h1
      simpa [hlam, layerHom_apply] using this
    · obtain ⟨e₁, he₁⟩ := hβr.resolve_left hβ1
      obtain ⟨xb, hxbfix, hxbz, hxbc⟩ := hT3 β (he₁ ▸ hfixK e₁) (he₁ ▸ hfixK' e₁) hβ2 hβ1
        (by rw [← hlamz]; exact hβζ)
      refine not_mem_zStarOf_of_layerAut_fix hΩ hF2 hFb hzY hz2 (x := xb) ?_ hxbz hxbc
      intro g hg
      obtain ⟨e, rfl, he⟩ := hFprop g hg
      rcases he with h | h
      · have := congrArg (fun φ => φ xb) h
        simpa [hlam, layerHom_apply] using this
      · have := congrArg (fun φ => φ xb) h
        simp only [hlam, layerHom_apply] at this
        rw [this, hxbfix]
  exact absurd (hmax F hFA (hD₀D.trans hDF) hFbad) (not_le.mpr hDltF)

theorem exists_bad_complement (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {D₀ : Subgroup G}
    (hD₀A : D₀ ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hD₀bad : z ∉ zStarOf (Subgroup.centralizer (D₀ : Set G))) (hD₀1 : D₀ ≠ ⊥)
    (hsmall : Nat.card D₀ < 4 → ∃ x ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), x ∉ D₀ ∧ x * z ∉ D₀ ∧
        (∀ d ∈ D₀, x * d = d * x) ∧ (x * x ∈ D₀ ∨ x * x * z ∈ D₀)) :
    ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
      D₀ ≤ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧
      ∀ g ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        g ∈ D ∨ g * z ∈ D := by
  exact CFSG.ClassicalInvolution.Asc77.CX6Eng.exists_bad_complement_gen hyp.std.setting.hz.sq
    hyp.hzS (T7T.z_mem_centralizer_of_hyp hyp) (false_of_growth h6 hyp)
    exists_mem_normalizer_sq_mem exists_central_involution inf_conjSub_ne_bot exists_sup_central
    hD₀A hD₀bad hD₀1 hsmall

end Core

end CFSG.ClassicalInvolution.Asc77.CX
