module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S4AFacts
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D7

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

theorem commute_of_le_normalizer_mem (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hJK : J ≤ normalizer (K : Set G)) (hKJ' : K ≤ normalizer (J : Set G)) {x v : G}
    (hxK : x ∈ K) (hxW : x ∈ normalizer (sec4W Ω S : Set G)) (hvJ : v ∈ J)
    (hvW : v ∈ sec4W Ω S) : x * v = v * x := by
  have hc := CFSG.ComponentClassification.Asc76.L26.commutatorElement_mem_inf hxK hvJ
    (hKJ' hxK) (hJK hvJ)
  have hcW : x * v * x⁻¹ * v⁻¹ ∈ sec4W Ω S :=
    mul_mem ((mem_normalizer_iff.mp hxW v).mp hvW) (inv_mem hvW)
  have hbot : (K ⊓ J) ⊓ sec4W Ω S = ⊥ :=
    eq_bot_of_isPGroup_of_odd ((sec4W_isPGroup hS).to_le inf_le_right)
      ((hΩ.inter K hK J hJ hKJ).of_dvd_nat (card_dvd_of_le inf_le_left))
  have h1 : x * v * x⁻¹ * v⁻¹ = 1 := by
    have := mem_inf.mpr ⟨hc, hcW⟩
    rwa [hbot, mem_bot] at this
  calc x * v = x * v * x⁻¹ * v⁻¹ * (v * x) := by group
    _ = v * x := by rw [h1, one_mul]

theorem commute_rot_of_ne_of_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    {K J T₁ T₂ V₂ : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (h₁ : IsSylowOf 2 T₁ K) (h₂ : IsSylowOf 2 T₂ J)
    (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G)) (hT₂W : T₂ ≤ normalizer (sec4W Ω S : Set G))
    (hV₂ : IsDihedralRot V₂ T₂) {d₁ d₂ : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁) (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂)
    (hc : d₁ * d₂ = d₂ * d₁) {x v : G} (hx : x ∈ T₁) (hv : v ∈ V₂) : x * v = v * x := by
  have hsyl : T₂ ≤ normalizer (K : Set G) := by
    by_contra hnot
    exact bar_not_commute_of_not_sylow H hS hK hJ hKJ h₁ h₂ hT₁W hT₂W hnot hd₁ hd₂ hc
  obtain ⟨hJK, hKJ'⟩ := le_normalizer_of_sylow H.h22 H.hΩ hK hJ hKJ h₂ hsyl
  exact commute_of_le_normalizer_mem H.hΩ hS hK hJ hKJ hJK hKJ' (h₁.le hx) (hT₁W hx)
    (h₂.le (hV₂.le hv)) (DSet.rot_le H.hΩ hS ⟨⟨J, hJ, h₂⟩, hT₂W⟩ hV₂ hv)

theorem member_eq_of_bar_eq (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    {K J T₁ T₂ : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h₁ : IsSylowOf 2 T₁ K) (h₂ : IsSylowOf 2 T₂ J)
    (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G)) (hT₂W : T₂ ≤ normalizer (sec4W Ω S : Set G))
    {d : NBar (sec4W Ω S)} (hd₁ : IsBarOf (sec4W Ω S) T₁ d)
    (hd₂ : IsBarOf (sec4W Ω S) T₂ d) : K = J := by
  by_contra hKJ
  obtain ⟨V₂, hV₂, s, hsT, hsV, hds⟩ := id hd₂
  obtain ⟨U₁, hU₁, x, hxT, hxU, hdx⟩ := id hd₁
  have hxs : (x : G)⁻¹ * s ∈ centralizer (sec4W Ω S : Set G) := by
    have h1 : (x : NBar (sec4W Ω S)) = (s : NBar (sec4W Ω S)) := hdx.symm.trans hds
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    simpa using h1
  obtain ⟨ρ, hρ, hρo⟩ := hV₂.exists_gen
  have hρV : ρ ∈ V₂ := hρ ▸ mem_zpowers ρ
  have hρW : ρ ∈ sec4W Ω S := DSet.rot_le H.hΩ hS ⟨⟨J, hJ, h₂⟩, hT₂W⟩ hV₂ hρV
  have hxρ : (x : G) * ρ = ρ * x :=
    commute_rot_of_ne_of_commute H hS hK hJ hKJ h₁ h₂ hT₁W hT₂W hV₂ hd₁ hd₂ rfl hxT hρV
  have hcρ : ((x : G)⁻¹ * s) * ρ = ρ * ((x : G)⁻¹ * s) :=
    ((mem_centralizer_iff.mp hxs) ρ hρW).symm
  have hinv := hV₂.conj_eq s hsT hsV ρ hρV
  have h1 : (s : G) * ρ * (s : G)⁻¹ = ρ := by
    calc (s : G) * ρ * (s : G)⁻¹
        = (x : G) * (((x : G)⁻¹ * s) * ρ) * ((x : G)⁻¹ * s)⁻¹ * (x : G)⁻¹ := by group
      _ = (x : G) * ρ * (x : G)⁻¹ := by rw [hcρ]; group
      _ = ρ := by rw [hxρ]; group
  rw [h1] at hinv
  apply hV₂.gen_mul_self_ne_one hρo
  calc ρ * ρ = ρ * ρ⁻¹ := by rw [← hinv]
    _ = 1 := mul_inv_cancel ρ

theorem DSet.rot_eq_of_bar_eq (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {T₁ T₂ V₁ V₂ : Subgroup G}
    (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S))
    (hV₁ : IsDihedralRot V₁ T₁) (hV₂ : IsDihedralRot V₂ T₂) {d : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d) (hd₂ : IsBarOf (sec4W Ω S) T₂ d) : V₁ = V₂ := by
  obtain ⟨⟨K, hK, h₁⟩, hT₁W⟩ := hT₁
  obtain ⟨⟨J, hJ, h₂⟩, hT₂W⟩ := hT₂
  obtain rfl := member_eq_of_bar_eq H hS hK hJ h₁ h₂ hT₁W hT₂W hd₁ hd₂
  exact rot_eq_of_le_sec4W H.hΩ hS hK h₁ hV₁ h₂ hV₂ (rot_le_sec4W H.hΩ hS hK h₁ hV₁ hT₁W)
    (rot_le_sec4W H.hΩ hS hK h₂ hV₂ hT₂W)

theorem DSet.zOf_eq_of_bar_eq (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {T₁ T₂ : Subgroup G}
    (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S)) {z₁ z₂ : G}
    (hz₁ : IsZOf T₁ z₁) (hz₂ : IsZOf T₂ z₂) {d : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d) (hd₂ : IsBarOf (sec4W Ω S) T₂ d) : z₁ = z₂ := by
  obtain ⟨V₁, hV₁⟩ := DSet.exists_rot H.hΩ hT₁
  obtain ⟨V₂, hV₂⟩ := DSet.exists_rot H.hΩ hT₂
  have h1 := (hz₁.mem_rot hV₁).1
  rw [DSet.rot_eq_of_bar_eq H hS hT₁ hT₂ hV₁ hV₂ hd₁ hd₂] at h1
  exact ((hz₂.mem_rot hV₂).2 z₁ h1 hz₁.mul_self).resolve_left hz₁.ne_one

theorem DSet.bar_eq_of_zOf_eq (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {T₁ T₂ : Subgroup G}
    (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S)) {z : G}
    (hz₁ : IsZOf T₁ z) (hz₂ : IsZOf T₂ z) {d₁ d₂ : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁) (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂) : d₁ = d₂ := by
  obtain ⟨⟨K, hK, h₁⟩, hT₁W⟩ := hT₁
  obtain ⟨⟨J, hJ, h₂⟩, hT₂W⟩ := hT₂
  obtain rfl := eq_of_mem_of_mem H.hΩ hK hJ (h₁.le hz₁.mem) (h₂.le hz₂.mem) hz₁.ne_one
    hz₁.mul_self
  exact bar_eq_of_same H hS hK h₁ h₂ hT₁W hT₂W hd₁ hd₂

theorem DSet.commute_rot_of_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    {T₁ T₂ V₂ : Subgroup G} (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S))
    (hV₂ : IsDihedralRot V₂ T₂) {d₁ d₂ : NBar (sec4W Ω S)} (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁)
    (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂) (hc : d₁ * d₂ = d₂ * d₁) (hne : d₁ ≠ d₂) {x v : G}
    (hx : x ∈ T₁) (hv : v ∈ V₂) : x * v = v * x := by
  obtain ⟨⟨K, hK, h₁⟩, hT₁W⟩ := hT₁
  obtain ⟨⟨J, hJ, h₂⟩, hT₂W⟩ := hT₂
  have hKJ : K ≠ J := by
    rintro rfl
    exact hne (bar_eq_of_same H hS hK h₁ h₂ hT₁W hT₂W hd₁ hd₂)
  exact commute_rot_of_ne_of_commute H hS hK hJ hKJ h₁ h₂ hT₁W hT₂W hV₂ hd₁ hd₂ hc hx hv

theorem DSet.inv_mul_conj_mem_rot (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {T V : Subgroup G}
    (hT : T ∈ DSet Ω (sec4W Ω S)) (hV : IsDihedralRot V T) {x w : G} (hx : x ∈ T)
    (hw : w ∈ sec4W Ω S) : w⁻¹ * (x⁻¹ * w * x) ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨K, hK, hTK⟩, hTW⟩ := hT
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := sec4W_isPGroup hS
  have hVW : V ≤ W := rot_le_sec4W H.hΩ hS hK hTK hV hTW
  have hwV : ∀ u ∈ V, u * w = w * u := fun u hu => sec4W_comm H.hΩ hS (hVW hu) hw
  have hV2 : IsPGroup 2 V := hV.isPGroup.to_le hV.le
  have hVbot : V ≠ ⊥ := fun h => by
    have := hV.four_le
    rw [h, card_bot] at this
    omega
  have hwK : w ∈ normalizer (K : Set G) :=
    centralizer_two_subgroup_le K V (Assumption41.tightlyEmbedded H.hΩ hK) hV2
      (hV.le.trans hTK.le) hVbot (mem_centralizer_iff.mpr hwV)
  have hA : IsPGroup 2 (zpowers w) := hW2.to_le ((zpowers_le).mpr hw)
  obtain ⟨o, ho, hAR₁⟩ := exists_oddCore_normalizes hTK (H.hnil K hK T hTK) hTW hA
    ((zpowers_le).mpr hwK) ((zpowers_le).mpr (le_normalizer hw))
  have hoC : o ∈ centralizer (W : Set G) := oddCoreIn_normalizer_le_centralizer hW2
    (oddCoreIn_inf_normalizer_le H.hΩ hK hTK hV hW2 hVW ho)
  have hcw : ∀ a ∈ W, o * a = a * o := fun a ha => ((mem_centralizer_iff.mp hoC) a ha).symm
  set R₁ := AschbacherTightEmbedding.rightConjugate T o⁻¹ with hR₁def
  have hoV : o⁻¹ ∈ normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _ (inv_mem (centralizer_le hVW hoC))
  have hV₁ : IsDihedralRot V R₁ := by
    have h1 := hV.rightConjugate o⁻¹
    rwa [(rightConjugate_eq_self_iff V o⁻¹).mpr hoV] at h1
  have hR₁V : R₁ ≤ normalizer (V : Set G) := le_normalizer.trans hV₁.normalizer_le
  set y := o * x * o⁻¹ with hy
  have hyR : y ∈ R₁ := by
    rw [mem_rightConjugate_iff, inv_inv]
    simpa [hy, mul_assoc] using hx
  set r₁ := w⁻¹ * (y⁻¹ * w * y) with hr₁
  have hwR₁ : w⁻¹ ∈ normalizer (R₁ : Set G) := inv_mem (hAR₁ (mem_zpowers w))
  have hr₁R : r₁ ∈ R₁ := by
    have h1 : w⁻¹ * y⁻¹ * w⁻¹⁻¹ ∈ R₁ := (mem_normalizer_iff.mp hwR₁ _).mp (inv_mem hyR)
    have e : r₁ = (w⁻¹ * y⁻¹ * w⁻¹⁻¹) * y := by rw [hr₁]; group
    rw [e]
    exact mul_mem h1 hyR
  have hr₁c : ∀ u ∈ V, r₁ * u = u * r₁ := by
    intro u hu
    have hyu : y * u * y⁻¹ ∈ V := (mem_normalizer_iff.mp (hR₁V hyR) u).mp hu
    have e1 : y⁻¹ * w * y * u = u * (y⁻¹ * w * y) := by
      calc y⁻¹ * w * y * u = y⁻¹ * (w * (y * u * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * u * y⁻¹) * w) * y := by rw [hwV _ hyu]
        _ = u * (y⁻¹ * w * y) := by group
    have e2 : w⁻¹ * u = u * w⁻¹ := by
      calc w⁻¹ * u = w⁻¹ * (u * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * u) * w⁻¹ := by rw [hwV u hu]
        _ = u * w⁻¹ := by group
    calc r₁ * u = w⁻¹ * (y⁻¹ * w * y * u) := by rw [hr₁]; group
      _ = w⁻¹ * u * (y⁻¹ * w * y) := by rw [e1]; group
      _ = u * r₁ := by rw [e2, hr₁]; group
  have hr₁V : r₁ ∈ V := hV₁.mem_of_commute hr₁R hr₁c
  have hxw : x⁻¹ * w * x ∈ W := by
    have h1 := (mem_normalizer_iff.mp (inv_mem (hTW hx)) w).mp hw
    rwa [inv_inv] at h1
  have how : o⁻¹ * w * o = w := by
    calc o⁻¹ * w * o = o⁻¹ * (w * o) := by group
      _ = o⁻¹ * (o * w) := by rw [hcw w hw]
      _ = w := by group
  have key : y⁻¹ * w * y = x⁻¹ * w * x := by
    calc y⁻¹ * w * y = o * (x⁻¹ * (o⁻¹ * w * o) * x) * o⁻¹ := by rw [hy]; group
      _ = o * (x⁻¹ * w * x) * o⁻¹ := by rw [how]
      _ = (x⁻¹ * w * x) * o * o⁻¹ := by rw [hcw _ hxw]
      _ = x⁻¹ * w * x := by group
  rw [← key]
  exact hr₁V

omit [Finite G] in
theorem conj_mem_sec4W {x w : G} (hx : x ∈ normalizer (sec4W Ω S : Set G))
    (hw : w ∈ sec4W Ω S) : x⁻¹ * w * x ∈ sec4W Ω S := by
  have h1 := (mem_normalizer_iff.mp (inv_mem hx) w).mp hw
  rwa [inv_inv] at h1

theorem inv_mul_conj_mul (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) {x a b : G}
    (hx : x ∈ normalizer (sec4W Ω S : Set G)) (ha : a ∈ sec4W Ω S) (hb : b ∈ sec4W Ω S) :
    (a * b)⁻¹ * (x⁻¹ * (a * b) * x) = (a⁻¹ * (x⁻¹ * a * x)) * (b⁻¹ * (x⁻¹ * b * x)) := by
  have hc : b⁻¹ * (a⁻¹ * (x⁻¹ * a * x)) = (a⁻¹ * (x⁻¹ * a * x)) * b⁻¹ :=
    sec4W_comm hΩ hS (inv_mem hb) (mul_mem (inv_mem ha) (conj_mem_sec4W hx ha))
  calc (a * b)⁻¹ * (x⁻¹ * (a * b) * x) = b⁻¹ * (a⁻¹ * (x⁻¹ * a * x)) * (x⁻¹ * b * x) := by
        group
    _ = (a⁻¹ * (x⁻¹ * a * x)) * b⁻¹ * (x⁻¹ * b * x) := by rw [hc]
    _ = (a⁻¹ * (x⁻¹ * a * x)) * (b⁻¹ * (x⁻¹ * b * x)) := by group

theorem inv_mul_conj_pow (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) {x w : G}
    (hx : x ∈ normalizer (sec4W Ω S : Set G)) (hw : w ∈ sec4W Ω S) (n : ℕ) :
    (w ^ n)⁻¹ * (x⁻¹ * w ^ n * x) = (w⁻¹ * (x⁻¹ * w * x)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, inv_mul_conj_mul hΩ hS hx (pow_mem hw n) hw, ih, pow_succ]

theorem inv_mul_conj_inv (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) {x a : G}
    (hx : x ∈ normalizer (sec4W Ω S : Set G)) (ha : a ∈ sec4W Ω S) :
    a⁻¹⁻¹ * (x⁻¹ * a⁻¹ * x) = (a⁻¹ * (x⁻¹ * a * x))⁻¹ := by
  have hc : a * (x⁻¹ * a * x)⁻¹ = (x⁻¹ * a * x)⁻¹ * a :=
    sec4W_comm hΩ hS ha (inv_mem (conj_mem_sec4W hx ha))
  calc a⁻¹⁻¹ * (x⁻¹ * a⁻¹ * x) = a * (x⁻¹ * a * x)⁻¹ := by group
    _ = (x⁻¹ * a * x)⁻¹ * a := hc
    _ = (a⁻¹ * (x⁻¹ * a * x))⁻¹ := by group

theorem inv_mul_conj_zpow (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) {x w : G}
    (hx : x ∈ normalizer (sec4W Ω S : Set G)) (hw : w ∈ sec4W Ω S) (n : ℤ) :
    (w ^ n)⁻¹ * (x⁻¹ * w ^ n * x) = (w⁻¹ * (x⁻¹ * w * x)) ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast, inv_mul_conj_pow hΩ hS hx hw]
  · simp only [zpow_neg, zpow_natCast]
    rw [inv_mul_conj_inv hΩ hS hx (pow_mem hw m), inv_mul_conj_pow hΩ hS hx hw]

theorem IsZOf.eq_pow_half {T V : Subgroup G} {z : G} (hz : IsZOf T z) (hV : IsDihedralRot V T)
    {ρ : G} (hρ : zpowers ρ = V) (hρo : orderOf ρ = Nat.card V) :
    ρ ^ (Nat.card V / 2) = z := by
  have hρV : ρ ∈ V := hρ ▸ mem_zpowers ρ
  obtain ⟨m, hm⟩ := hV.two_dvd_card
  have h4 := hV.four_le
  have hm0 : Nat.card V / 2 = m := by omega
  rcases hV.pow_half_eq (hz.mem_rot hV).2 hρV with h | h
  · exfalso
    rw [hm0] at h
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hρo]; omega) h
  · exact h

theorem DSet.card_rot_eq (hΩ : Assumption41 Ω) {W T₁ T₂ V₁ V₂ : Subgroup G}
    (hT₁ : T₁ ∈ DSet Ω W) (hT₂ : T₂ ∈ DSet Ω W) (hV₁ : IsDihedralRot V₁ T₁)
    (hV₂ : IsDihedralRot V₂ T₂) : Nat.card V₁ = Nat.card V₂ := by
  obtain ⟨⟨K, hK, h₁⟩, -⟩ := hT₁
  obtain ⟨⟨J, hJ, h₂⟩, -⟩ := hT₂
  have h := Assumption41.card_sylow_eq hΩ hK hJ h₁ h₂
  rw [hV₁.card_eq, hV₂.card_eq] at h
  omega

theorem DSet.zpowers_inv_mul_conj_eq (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    {T₁ T₂ U₁ V₂ : Subgroup G} (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S))
    (hU₁ : IsDihedralRot U₁ T₁) (hV₂ : IsDihedralRot V₂ T₂) {d₁ d₂ : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁) (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂)
    (hnc : d₁ * d₂ ≠ d₂ * d₁) {x : G} (hx : x ∈ T₁) (hxU : x ∉ U₁) {ρ : G}
    (hρ : zpowers ρ = V₂) (hρo : orderOf ρ = Nat.card V₂) :
    zpowers (ρ⁻¹ * (x⁻¹ * ρ * x)) = U₁ ∧ orderOf (ρ⁻¹ * (x⁻¹ * ρ * x)) = Nat.card U₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := ρ⁻¹ * (x⁻¹ * ρ * x) with hc
  have hρV : ρ ∈ V₂ := hρ ▸ mem_zpowers ρ
  have hρW : ρ ∈ sec4W Ω S := DSet.rot_le H.hΩ hS hT₂ hV₂ hρV
  have hxN : x ∈ normalizer (sec4W Ω S : Set G) := by
    obtain ⟨-, h⟩ := hT₁
    exact h hx
  have hcU : c ∈ U₁ := DSet.inv_mul_conj_mem_rot H hS hT₁ hU₁ hx hρW
  have hcard : Nat.card U₁ = Nat.card V₂ := DSet.card_rot_eq H.hΩ hT₁ hT₂ hU₁ hV₂
  obtain ⟨z₁, hz₁⟩ := IsZOf.exists_of_rot hU₁
  obtain ⟨z₂, hz₂⟩ := IsZOf.exists_of_rot hV₂
  have hz₂eq : ρ ^ (Nat.card V₂ / 2) = z₂ := hz₂.eq_pow_half hV₂ hρ hρo
  have hconj : x⁻¹ * z₂ * x = z₂ * z₁ :=
    conj_z_of_not_commute H hS hT₁ hT₂ hU₁ hz₁ hz₂ hd₁ hd₂ hnc hx hxU
  have hpow : c ^ (Nat.card V₂ / 2) = z₁ := by
    rw [hc, ← inv_mul_conj_pow H.hΩ hS hxN hρW, hz₂eq, hconj]
    group
  obtain ⟨n, hn⟩ := (hU₁.isPGroup.to_le hU₁.le).exists_card_eq
  have hdvd : orderOf c ∣ Nat.card U₁ := Subgroup.orderOf_dvd_natCard U₁ hcU
  rw [hn] at hdvd
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h4 := hU₁.four_le
  have hjn : j = n := by
    by_contra hjn
    have hlt : j < n := lt_of_le_of_ne hj hjn
    apply hz₁.ne_one
    rw [← hpow, ← hcard, hn]
    have hdiv : 2 ^ n / 2 = 2 ^ (n - 1) := by
      rw [← Nat.pow_div (by omega : 1 ≤ n) (by norm_num : 0 < 2), pow_one]
    rw [hdiv]
    exact orderOf_dvd_iff_pow_eq_one.mp (hjo ▸ Nat.pow_dvd_pow 2 (by omega))
  have hco : orderOf c = Nat.card U₁ := by rw [hjo, hjn, hn]
  refine ⟨?_, hco⟩
  have hle : zpowers c ≤ U₁ := (zpowers_le).mpr hcU
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hco])

end CFSG.ComponentClassification.Asc76.Sec4
