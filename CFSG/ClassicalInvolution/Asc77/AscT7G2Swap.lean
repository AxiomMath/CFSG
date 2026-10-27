module

public import CFSG.ClassicalInvolution.Asc77.AscT7G2Data

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7G2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


section Swap

variable (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)

include hyp

theorem data_of_normalizes {g : G} (hg : g * z * g⁻¹ = t) (ht2 : t * t = 1)
    (hRt : conjSub t R = R) :
    ∃ x c₁ ω : G, c₁ ∈ R ∧ orderOf c₁ = 4 ∧ ω * c₁ = c₁ * ω ∧ ω * ω = 1 ∧ t * ω = ω * t ∧
      ω ≠ 1 ∧ ω ≠ z ∧ x⁻¹ * t * x = t * ω := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW₀ : W ∈ WSet Ω := hyp.hW
  have hE4 : MuIsoE4 Ω W := hyp.hE4
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz'
    (hRsyl.1) (hR'syl.1) (S.isPGroup'.to_le (sup_le hRS hR'S))
  have hRq : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp hyp.hR.1
  have hR'q : IsQuatSub R' := hΩ.isQuatSub_of_mem_RSet hp hyp.hR'.1
  have hzR : IsUniqueInvolution R z :=
    ⟨T7C.mem_of_isSylow2In hp hΩ hK hRsyl hz, hz.ne_one, hz.sq,
      fun y hy hy2 => hz.unique y (hRsyl.1 hy) hy2⟩
  have hzR' : IsUniqueInvolution R' z :=
    ⟨T7C.mem_of_isSylow2In hp hΩ hK' hR'syl hz', hz.ne_one, hz.sq,
      fun y hy hy2 => hz'.unique y (hR'syl.1 hy) hy2⟩
  have hRR'inf : Nat.card ↥(R ⊓ R') ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK hK' hKK'.symm
      (hRsyl.2.1.to_le (inf_le_left : R ⊓ R' ≤ R)) (inf_le_left.trans hRsyl.1)
      (inf_le_right.trans hR'syl.1)
  have hinf : ∀ y ∈ R, y ∈ R' → orderOf y ≠ 4 := by
    intro y hyR hyR' hy4
    have hle : Subgroup.zpowers y ≤ R ⊓ R' := Subgroup.zpowers_le.mpr ⟨hyR, hyR'⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hy4] at h1
    omega
  obtain ⟨htS, htz, -⟩ := hyp.ht
  have hRt' : conjSub t R' = R' := by
    have hmem : conjSub t R' ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR'.1 t
    have hle : conjSub t R' ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htS (hR'S hx)) (Subgroup.inv_mem _ htS)
      simpa [mul_assoc] using h1
    rcases hyp.hRS _ hmem hle with h | h
    · exfalso
      have h1 : conjSub t (conjSub t R') = conjSub t R := by rw [h]
      have h2 : conjSub t (conjSub t R') = R' := by
        rw [← conjSub_mul]
        have : t * t = 1 := ht2
        rw [this, conjSub_one]
      rw [h2, hRt] at h1
      have hRR' : R = R' := h1.symm
      have : Nat.card ↥R ≤ 2 := by
        have := hΩ.card_le_two_of_le_inf hK hK' hKK'.symm hRsyl.2.1 hRsyl.1
          (hRR' ▸ hR'syl.1)
        exact this
      have := hRq.eight_le
      omega
    · exact h
  have htR : ∀ r ∈ R, t * r * t⁻¹ ∈ R := fun r hr => by
    have := conj_mem_conjSub (n := t) hr
    rwa [hRt] at this
  have htR' : ∀ r ∈ R', t * r * t⁻¹ ∈ R' := fun r hr => by
    have := conj_mem_conjSub (n := t) hr
    rwa [hRt'] at this
  have hfix : ∀ {J : Subgroup G} {a : G}, J ∈ Ω → IsUniqueInvolution J a →
      (∀ y : G, y * z * y⁻¹ = t → t ≠ a → ∀ x ∈ J, orderOf x = 4 → t * x * t⁻¹ ≠ x) := by
    intro J a hJ ha y hy hta x hx hx4 h
    have := T7ER.not_commute_of_conj hs hW₀ hE4 hJ ha (y := y) (by rw [hy]; exact hta) hx hx4
    rw [hy] at this
    apply this
    have h1 := congrArg (fun w => w * t) h
    simpa [mul_assoc] using h1
  have hfixR : ∀ x ∈ R, orderOf x = 4 → t * x * t⁻¹ ≠ x :=
    fun x hx hx4 => hfix hK hz g hg htz x (hRsyl.1 hx) hx4
  have hfixR' : ∀ x ∈ R', orderOf x = 4 → t * x * t⁻¹ ≠ x :=
    fun x hx hx4 => hfix hK' hz' g hg htz x (hR'syl.1 hx) hx4
  obtain ⟨x, c₁, ω, hc₁R, hc₁4, hωc₁, hω2, htω, hω1, hωz, hxt⟩ :=
    T7ER.exists_twisted_conj hRq hR'q hzR hzR' hc hinf ht2 htR htR' hfixR hfixR'
  exact ⟨x, c₁, ω, hc₁R, hc₁4, hωc₁, hω2, htω, hω1, hωz, hxt⟩


theorem exists_swap_nonfused :
    ∃ t' ∈ (S : Subgroup G), t' * t' = 1 ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧
      ¬ ∃ y : G, y * z * y⁻¹ = t' * z := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  obtain ⟨htS, htz, g, hg⟩ := hyp.ht
  have ht2 : t * t = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hmem : conjSub t R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR.1 t
  have hle : conjSub t R ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ htS (hRS hx)) (Subgroup.inv_mem _ htS)
    simpa [mul_assoc] using h1
  have hdata : ∃ x c₁ ω : G, c₁ ∈ R ∧ orderOf c₁ = 4 ∧ ω * c₁ = c₁ * ω ∧ ω * ω = 1 ∧
      t * ω = ω * t ∧ ω ≠ 1 ∧ ω ≠ z ∧ x⁻¹ * t * x = t * ω := by
    rcases hyp.hRS _ hmem hle with hRt | hRt
    · exact data_of_normalizes hyp hg ht2 hRt
    · exact data_of_swap hyp ht2 hRt
  obtain ⟨x, c₁, ω, hc₁R, hc₁4, hωc₁, hω2, htω, hω1, hωz, hxt⟩ := hdata
  obtain ⟨s', hs'2, hs'z, ⟨y, hy⟩, hs'K, hs'nf⟩ :=
    exists_nonfused_of_data hyp hg ht2 hc₁R hc₁4 hωc₁ hω2 htω hω1 hωz hxt
  obtain ⟨c, hcz, hcS⟩ := T7ER.exists_conj_mem_sylow_of_centralizes S hyp.hzS hs'2 hs'z
  refine ⟨c⁻¹ * s' * c, hcS, ?_, ⟨c⁻¹ * y, ?_⟩, ?_, ?_⟩
  · calc c⁻¹ * s' * c * (c⁻¹ * s' * c) = c⁻¹ * (s' * s') * c := by group
      _ = 1 := by rw [hs'2]; group
  · calc c⁻¹ * y * z * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * z * y⁻¹) * c := by group
      _ = c⁻¹ * s' * c := by rw [hy]
  · have hmem' : conjSub (c⁻¹ * s' * c) R ∈ RSet Ω :=
      RSet.conj hΩ.conjInvariant hyp.hR.1 _
    have hle' : conjSub (c⁻¹ * s' * c) R ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : (c⁻¹ * s' * c) * ((c⁻¹ * s' * c)⁻¹ * x * (c⁻¹ * s' * c)) * (c⁻¹ * s' * c)⁻¹ ∈
          (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hcS (hRS hx)) (Subgroup.inv_mem _ hcS)
      simpa [mul_assoc] using h1
    rcases hyp.hRS _ hmem' hle' with h | h
    · exfalso
      have hKt : conjSub (c⁻¹ * s' * c) K = K := by
        by_contra hne
        have hK2 : conjSub (c⁻¹ * s' * c) K ∈ Ω := hΩ.conjInvariant _ K hK
        have hRK : R ≤ conjSub (c⁻¹ * s' * c) K := h ▸ conjSub_mono hRsyl.1
        have := hΩ.card_le_two_of_le_inf hK hK2 (Ne.symm hne) hRsyl.2.1 hRsyl.1 hRK
        have h8 := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR.1).eight_le
        omega
      have h1 : conjSub s' (conjSub c K) = conjSub c K := by
        have h2 : conjSub (c * (c⁻¹ * s' * c)) K = conjSub (s' * c) K := by
          congr 1; group
        rw [conjSub_mul, hKt, conjSub_mul] at h2
        exact h2.symm
      rcases T7ER.conjSub_eq_of_centralizes hs hcz with h3 | h3
      · rw [h3] at h1
        exact hs'K h1
      · rw [h3] at h1
        exact hs'K ((T7ER.normalizes_iff_of_centralizes hs hs'z).mpr h1)
    · exact h
  · rintro ⟨y', hy'⟩
    apply hs'nf
    refine ⟨c * y', ?_⟩
    have hsz : c⁻¹ * s' * c * z = c⁻¹ * (s' * z) * c := by
      calc c⁻¹ * s' * c * z = c⁻¹ * s' * (c * z) := by group
        _ = c⁻¹ * s' * (z * c) := by rw [hcz]
        _ = c⁻¹ * (s' * z) * c := by group
    rw [hsz] at hy'
    calc c * y' * z * (c * y')⁻¹ = c * (y' * z * y'⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * (s' * z) * c) * c⁻¹ := by rw [hy']
      _ = s' * z := by group

theorem not_normalizes_of_nonfused {t'' g : G} (hg : g * z * g⁻¹ = t'') (hne : z ≠ t'')
    (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t'' * z) : conjSub z (conjSub g K) ≠ conjSub g K := by
  intro hN
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hW₀ : W ∈ WSet Ω := hyp.hW
  have hE4 : MuIsoE4 Ω W := hyp.hE4
  have hJt : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have htJ : IsUniqueInvolution (conjSub g K) t'' := by
    have := hz.conj g
    rwa [hg] at this
  have hz2 : z * z = 1 := hz.sq
  have hzN : z ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hN
  obtain ⟨Rt, hRtsyl, hRtinv⟩ := T3.exists_sylow_normalized (T7ER.isPGroup_zpowers_of_sq hz2)
    (Subgroup.zpowers_le.mpr hzN)
  have hRtmem : Rt ∈ RSet Ω := mem_RSet_of_isSylow2In hJt hRtsyl
  have hRtq : IsQuatSub Rt := hΩ.isQuatSub_of_mem_RSet hp hRtmem
  have htRt : t'' ∈ Rt := T7C.mem_of_isSylow2In hp hΩ hJt hRtsyl htJ
  have hzRt : IsUniqueInvolution Rt t'' :=
    ⟨htRt, htJ.ne_one, htJ.sq, fun y hy hy2 => htJ.unique y (hRtsyl.1 hy) hy2⟩
  have hsRt : conjSub z Rt = Rt := hRtinv _ (Subgroup.mem_zpowers _)
  have hbR : ∀ r ∈ Rt, z * r * z⁻¹ ∈ Rt := fun r hr => by
    have := conj_mem_conjSub (n := z) hr
    rwa [hsRt] at this
  have hfixt : ∀ r ∈ Rt, orderOf r = 4 → z * r * z⁻¹ ≠ r := by
    intro r hr hr4 h
    have := T7ER.not_commute_of_conj hs hW₀ hE4 hJt htJ (y := 1) (by simpa using hne)
      (hRtsyl.1 hr) hr4
    apply this
    simp only [one_mul, inv_one, mul_one]
    have h1 := congrArg (fun w => w * z) h
    simpa [mul_assoc] using h1
  obtain ⟨ρ, hρ, hρs⟩ := T7ER.exists_conj_eq_mul_inv hRtq hzRt hz2 hbR hfixt
  apply hnf
  refine ⟨ρ⁻¹, ?_⟩
  calc ρ⁻¹ * z * ρ⁻¹⁻¹ = ρ⁻¹ * z * ρ := by rw [inv_inv]
    _ = ρ⁻¹ * (z * ρ * z⁻¹) * z := by group
    _ = ρ⁻¹ * (ρ * t'') * z := by rw [hρs]
    _ = t'' * z := by group

end Swap

end T7G2

end CFSG.ClassicalInvolution.Asc77
