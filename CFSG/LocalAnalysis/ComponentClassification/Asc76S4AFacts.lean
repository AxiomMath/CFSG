module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S4ABasic

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

theorem bar_eq_of_same (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {K T₁ T₂ : Subgroup G}
    (hK : K ∈ Ω) (h₁ : IsSylowOf 2 T₁ K) (h₂ : IsSylowOf 2 T₂ K)
    (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G)) (hT₂W : T₂ ≤ normalizer (sec4W Ω S : Set G))
    {d₁ d₂ : NBar (sec4W Ω S)} (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁)
    (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂) : d₁ = d₂ := by
  have hT₁ : T₁ ∈ DSet Ω (sec4W Ω S) := ⟨⟨K, hK, h₁⟩, hT₁W⟩
  have hT₂ : T₂ ∈ DSet Ω (sec4W Ω S) := ⟨⟨K, hK, h₂⟩, hT₂W⟩
  obtain ⟨V₂, hV₂, s, hsT, hsV, rfl⟩ := hd₂
  obtain ⟨U₁, hU₁⟩ := DSet.exists_rot H.hΩ hT₁
  have hUW := DSet.rot_le H.hΩ hS hT₁ hU₁
  have hVW := DSet.rot_le H.hΩ hS hT₂ hV₂
  have hW2 := sec4W_isPGroup (Ω := Ω) hS
  obtain ⟨o, ho, r', hr', hseq⟩ := H.hnil K hK T₁ h₁ s (h₂.le hsT)
  have hoW : o ∈ normalizer (sec4W Ω S : Set G) := by
    have : o = (s : G) * r'⁻¹ := by rw [hseq]; group
    rw [this]
    exact mul_mem s.2 (inv_mem (hT₁W hr'))
  have hoC : o ∈ centralizer (sec4W Ω S : Set G) := oddCoreIn_normalizer_le_centralizer hW2
    (oddCoreIn_inf_normalizer_le H.hΩ hK h₁ hU₁ hW2 hUW (mem_inf.mpr ⟨ho, hoW⟩))
  have hr'U : r' ∉ U₁ := fun h => not_mem_centralizer hV₂ hVW hsT hsV (by
    rw [hseq]
    exact mul_mem hoC (sec4W_le_centralizer H.hΩ hS (hUW h)))
  rw [IsBarOf.eq_mk H.hΩ hS hT₁ hd₁ hU₁ (x := ⟨r', hT₁W hr'⟩) hr' hr'U, QuotientGroup.eq,
    mem_subgroupOf]
  simp only [coe_mul, coe_inv]
  have e : r'⁻¹ * (s : G) = r'⁻¹ * o * r'⁻¹⁻¹ := by rw [hseq]; group
  rw [e]
  exact conj_mem_centralizer (inv_mem (hT₁W hr')) hoC

omit [Finite G] in
theorem mk_commute_of_commutator_mem {W : Subgroup G} {x y : normalizer (W : Set G)}
    (h : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ centralizer (W : Set G)) :
    (x : NBar W) * (y : NBar W) = (y : NBar W) * (x : NBar W) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
  have e : ((x * y : normalizer (W : Set G))⁻¹ * (y * x) : normalizer (W : Set G)) =
      ((x * y)⁻¹ * ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹)⁻¹ * ((x * y)⁻¹)⁻¹ : G) := by
    simp only [coe_mul, coe_inv]
    group
  rw [e]
  exact conj_mem_centralizer (inv_mem (x * y).2) (inv_mem h)

theorem bar_commute_of_sylow (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {K J T₁ T₂ : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (h₁ : IsSylowOf 2 T₁ K) (h₂ : IsSylowOf 2 T₂ J)
    (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G)) (hJK : J ≤ normalizer (K : Set G))
    (hKJ' : K ≤ normalizer (J : Set G)) {d₁ d₂ : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁) (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂) :
    d₁ * d₂ = d₂ * d₁ := by
  obtain ⟨U₁, hU₁, r, hrT, -, rfl⟩ := hd₁
  obtain ⟨-, -, s, hsT, -, rfl⟩ := hd₂
  have hUW := DSet.rot_le H.hΩ hS ⟨⟨K, hK, h₁⟩, hT₁W⟩ hU₁
  exact mk_commute_of_commutator_mem (commutator_mem_centralizer H.hΩ hK hJ hKJ h₁ hU₁
    (sec4W_isPGroup hS) hUW hJK hKJ' (h₁.le hrT) (h₂.le hsT) r.2 s.2)

theorem commute_z_of_sylow (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤)
    {K J T₁ T₂ : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (h₁ : IsSylowOf 2 T₁ K)
    (h₂ : IsSylowOf 2 T₂ J) (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G))
    (hT₂W : T₂ ≤ normalizer (sec4W Ω S : Set G)) (hJK : J ≤ normalizer (K : Set G))
    (hKJ' : K ≤ normalizer (J : Set G)) {z₂ : G} (hz₂ : IsZOf T₂ z₂) {x : G} (hx : x ∈ T₁) :
    x * z₂ = z₂ * x := by
  have hT₂ : T₂ ∈ DSet Ω (sec4W Ω S) := ⟨⟨J, hJ, h₂⟩, hT₂W⟩
  have hzT := hz₂.mem
  obtain ⟨V₂, hV₂, hzV, -, -⟩ := hz₂
  have hzW : z₂ ∈ sec4W Ω S := DSet.rot_le hΩ hS hT₂ hV₂ hzV
  have hc := CFSG.ComponentClassification.Asc76.L26.commutatorElement_mem_inf (h₁.le hx)
    (h₂.le hzT) (hKJ' (h₁.le hx)) (hJK (h₂.le hzT))
  have hcW : x * z₂ * x⁻¹ * z₂⁻¹ ∈ sec4W Ω S :=
    mul_mem ((mem_normalizer_iff.mp (hT₁W hx) z₂).mp hzW) (inv_mem hzW)
  have hbot : (K ⊓ J) ⊓ sec4W Ω S = ⊥ :=
    eq_bot_of_isPGroup_of_odd ((sec4W_isPGroup hS).to_le inf_le_right)
      ((hΩ.inter K hK J hJ hKJ).of_dvd_nat (card_dvd_of_le inf_le_left))
  have h1 : x * z₂ * x⁻¹ * z₂⁻¹ = 1 := by
    have := mem_inf.mpr ⟨hc, hcW⟩
    rwa [hbot, mem_bot] at this
  calc x * z₂ = x * z₂ * x⁻¹ * z₂⁻¹ * (z₂ * x) := by group
    _ = z₂ * x := by rw [h1, one_mul]

theorem conj_z_of_not_sylow (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {K J T₁ T₂ U₁ : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (h₁ : IsSylowOf 2 T₁ K) (h₂ : IsSylowOf 2 T₂ J)
    (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G)) (hT₂W : T₂ ≤ normalizer (sec4W Ω S : Set G))
    (hU₁ : IsDihedralRot U₁ T₁) (hnot : ¬ T₂ ≤ normalizer (K : Set G)) {z₁ z₂ : G}
    (hz₁ : IsZOf T₁ z₁) (hz₂ : IsZOf T₂ z₂) {x : G} (hx : x ∈ T₁) (hxU : x ∉ U₁) :
    x⁻¹ * z₂ * x = z₂ * z₁ := by
  have hT₁ : T₁ ∈ DSet Ω (sec4W Ω S) := ⟨⟨K, hK, h₁⟩, hT₁W⟩
  have hT₂ : T₂ ∈ DSet Ω (sec4W Ω S) := ⟨⟨J, hJ, h₂⟩, hT₂W⟩
  obtain ⟨V₂, hV₂⟩ := DSet.exists_rot H.hΩ hT₂
  obtain ⟨hzU, hzuniq⟩ := hz₁.mem_rot hU₁
  exact conj_eq_mul_of_not_sylow H.h22 H.hΩ hK hJ hKJ h₁ h₂ hU₁ hV₂ (H.hnil K hK T₁ h₁) hT₁W
    (sec4W_isPGroup hS) (fun a ha b hb => sec4W_comm H.hΩ hS ha hb) (DSet.rot_le H.hΩ hS hT₁ hU₁)
    (DSet.rot_le H.hΩ hS hT₂ hV₂) hnot (hz₂.mem_rot hV₂).1 hz₂.ne_one hz₂.mul_self hzU hzuniq
    hx hxU

theorem bar_not_commute_of_not_sylow (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    {K J T₁ T₂ : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (h₁ : IsSylowOf 2 T₁ K)
    (h₂ : IsSylowOf 2 T₂ J) (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G))
    (hT₂W : T₂ ≤ normalizer (sec4W Ω S : Set G)) (hnot : ¬ T₂ ≤ normalizer (K : Set G))
    {d₁ d₂ : NBar (sec4W Ω S)} (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁)
    (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂) : d₁ * d₂ ≠ d₂ * d₁ := by
  have hnot' : ¬ T₁ ≤ normalizer (J : Set G) := fun h =>
    hnot (h₂.le.trans (le_normalizer_of_sylow H.h22 H.hΩ hJ hK (Ne.symm hKJ) h₁ h).2)
  obtain ⟨U₁, hU₁, r, hrT, hrU, rfl⟩ := hd₁
  obtain ⟨V₂, hV₂, s, hsT, hsV, rfl⟩ := hd₂
  obtain ⟨z₁, hz₁⟩ := IsZOf.exists_of_rot hU₁
  obtain ⟨z₂, hz₂⟩ := IsZOf.exists_of_rot hV₂
  have e1 := conj_z_of_not_sylow H hS hK hJ hKJ h₁ h₂ hT₁W hT₂W hU₁ hnot hz₁ hz₂ hrT hrU
  have e2 := conj_z_of_not_sylow H hS hJ hK (Ne.symm hKJ) h₂ h₁ hT₂W hT₁W hV₂ hnot' hz₂ hz₁ hsT
    hsV
  have hz₁W : z₁ ∈ sec4W Ω S :=
    DSet.rot_le H.hΩ hS ⟨⟨K, hK, h₁⟩, hT₁W⟩ hU₁ (hz₁.mem_rot hU₁).1
  have hz₂W : z₂ ∈ sec4W Ω S :=
    DSet.rot_le H.hΩ hS ⟨⟨J, hJ, h₂⟩, hT₂W⟩ hV₂ (hz₂.mem_rot hV₂).1
  have hz₁r : (r : G)⁻¹ * z₁ * r = z₁ := by
    rw [mul_assoc, ← hz₁.commute hrT]
    group
  intro h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at h
  simp only [coe_mul, coe_inv] at h
  set c := ((r : G) * s)⁻¹ * ((s : G) * r) with hcdef
  set w := ((r : G) * s)⁻¹ * z₁ * ((r : G) * s) with hwdef
  have hw : w ∈ sec4W Ω S := by
    have := (mem_normalizer_iff.mp (inv_mem (mul_mem r.2 s.2)) z₁).mp hz₁W
    simpa [hwdef, mul_assoc] using this
  have hcw : w * c = c * w := (mem_centralizer_iff.mp h) w hw
  have key : ((s : G) * r)⁻¹ * z₁ * ((s : G) * r) = w := by
    have hsr : (s : G) * r = (r : G) * s * c := by rw [hcdef]; group
    rw [hsr]
    calc ((r : G) * s * c)⁻¹ * z₁ * ((r : G) * s * c) = c⁻¹ * (w * c) := by rw [hwdef]; group
      _ = c⁻¹ * (c * w) := by rw [hcw]
      _ = w := by group
  have lhs : ((s : G) * r)⁻¹ * z₁ * ((s : G) * r) = z₂ := by
    calc ((s : G) * r)⁻¹ * z₁ * ((s : G) * r) = (r : G)⁻¹ * ((s : G)⁻¹ * z₁ * s) * r := by group
      _ = ((r : G)⁻¹ * z₁ * r) * ((r : G)⁻¹ * z₂ * r) := by rw [e2]; group
      _ = z₁ * (z₂ * z₁) := by rw [hz₁r, e1]
      _ = z₂ := by
        rw [sec4W_comm H.hΩ hS hz₂W hz₁W, ← mul_assoc, hz₁.mul_self, one_mul]
  have rhs : w = z₁ * z₂ := by
    calc w = (s : G)⁻¹ * ((r : G)⁻¹ * z₁ * r) * s := by rw [hwdef]; group
      _ = z₁ * z₂ := by rw [hz₁r, e2]
  rw [lhs, rhs] at key
  apply hz₁.ne_one
  calc z₁ = z₁ * z₂ * z₂⁻¹ := by group
    _ = 1 := by rw [← key, mul_inv_cancel]

theorem conj_z_of_not_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {T₁ T₂ U₁ : Subgroup G}
    (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S)) (hU₁ : IsDihedralRot U₁ T₁)
    {z₁ z₂ : G} (hz₁ : IsZOf T₁ z₁) (hz₂ : IsZOf T₂ z₂) {d₁ d₂ : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁) (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂)
    (hnc : d₁ * d₂ ≠ d₂ * d₁) {x : G} (hx : x ∈ T₁) (hxU : x ∉ U₁) :
    x⁻¹ * z₂ * x = z₂ * z₁ := by
  obtain ⟨⟨K, hK, h₁⟩, hT₁W⟩ := hT₁
  obtain ⟨⟨J, hJ, h₂⟩, hT₂W⟩ := hT₂
  have hKJ : K ≠ J := by
    rintro rfl
    exact hnc (by rw [bar_eq_of_same H hS hK h₁ h₂ hT₁W hT₂W hd₁ hd₂])
  have hnot : ¬ T₂ ≤ normalizer (K : Set G) := by
    intro h
    obtain ⟨hJK, hKJ'⟩ := le_normalizer_of_sylow H.h22 H.hΩ hK hJ hKJ h₂ h
    exact hnc (bar_commute_of_sylow H hS hK hJ hKJ h₁ h₂ hT₁W hJK hKJ' hd₁ hd₂)
  exact conj_z_of_not_sylow H hS hK hJ hKJ h₁ h₂ hT₁W hT₂W hU₁ hnot hz₁ hz₂ hx hxU

theorem commute_z_of_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {T₁ T₂ : Subgroup G}
    (hT₁ : T₁ ∈ DSet Ω (sec4W Ω S)) (hT₂ : T₂ ∈ DSet Ω (sec4W Ω S)) {z₂ : G}
    (hz₂ : IsZOf T₂ z₂) {d₁ d₂ : NBar (sec4W Ω S)} (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁)
    (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂) (hc : d₁ * d₂ = d₂ * d₁) (hne : d₁ ≠ d₂) {x : G}
    (hx : x ∈ T₁) : x * z₂ = z₂ * x := by
  obtain ⟨⟨K, hK, h₁⟩, hT₁W⟩ := hT₁
  obtain ⟨⟨J, hJ, h₂⟩, hT₂W⟩ := hT₂
  have hKJ : K ≠ J := by
    rintro rfl
    exact hne (bar_eq_of_same H hS hK h₁ h₂ hT₁W hT₂W hd₁ hd₂)
  have hsyl : T₂ ≤ normalizer (K : Set G) := by
    by_contra hnot
    exact bar_not_commute_of_not_sylow H hS hK hJ hKJ h₁ h₂ hT₁W hT₂W hnot hd₁ hd₂ hc
  obtain ⟨hJK, hKJ'⟩ := le_normalizer_of_sylow H.h22 H.hΩ hK hJ hKJ h₂ hsyl
  exact commute_z_of_sylow H.hΩ hS hK hJ hKJ h₁ h₂ hT₁W hT₂W hJK hKJ' hz₂ hx

end CFSG.ComponentClassification.Asc76.Sec4
