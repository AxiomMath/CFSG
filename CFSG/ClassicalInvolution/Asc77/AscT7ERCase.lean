module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERAlg
public import CFSG.ClassicalInvolution.Asc77.AscT7ERNoFour

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7ER

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem exists_notNormalizing_conj (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {g : G}
    (hg : g * z * g⁻¹ = t) (hRt : conjSub t R = R) :
    ∃ s' : G, s' * s' = 1 ∧ s' * z = z * s' ∧ (∃ y : G, y * z * y⁻¹ = s') ∧
      conjSub s' K ≠ K := by
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
  have ht2 : t * t = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
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
    have := not_commute_of_conj hs hW₀ hE4 hJ ha (y := y) (by rw [hy]; exact hta) hx hx4
    rw [hy] at this
    apply this
    have h1 := congrArg (fun w => w * t) h
    simpa [mul_assoc] using h1
  have hfixR : ∀ x ∈ R, orderOf x = 4 → t * x * t⁻¹ ≠ x :=
    fun x hx hx4 => hfix hK hz g hg htz x (hRsyl.1 hx) hx4
  have hfixR' : ∀ x ∈ R', orderOf x = 4 → t * x * t⁻¹ ≠ x :=
    fun x hx hx4 => hfix hK' hz' g hg htz x (hR'syl.1 hx) hx4
  obtain ⟨x, c₁, ω, hc₁R, hc₁4, hωc₁, hω2, htω, hω1, hωz, hxt⟩ :=
    exists_twisted_conj hRq hR'q hzR hzR' hc hinf ht2 htR htR' hfixR hfixR'
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs2 : (t * ω) * (t * ω) = 1 := by
    calc (t * ω) * (t * ω) = (t * (ω * t)) * ω := by group
      _ = (t * (t * ω)) * ω := by rw [htω]
      _ = (t * t) * (ω * ω) := by group
      _ = 1 := by rw [ht2, hω2]; group
  have hst : (t * ω) * t = t * (t * ω) := by
    calc (t * ω) * t = t * (ω * t) := by group
      _ = t * (t * ω) := by rw [htω]
  have hsne : t * ω ≠ t := by
    intro h
    apply hω1
    have := congrArg (fun w => t⁻¹ * w) h
    simpa using this
  obtain ⟨hsy⟩ : Nonempty (∃ y : G, y * z * y⁻¹ = t * ω) := by
    refine ⟨⟨x⁻¹ * g, ?_⟩⟩
    calc x⁻¹ * g * z * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * z * g⁻¹) * x := by group
      _ = x⁻¹ * t * x := by rw [hg]
      _ = t * ω := hxt
  have hts : t * (t * ω) = ω := by
    calc t * (t * ω) = (t * t) * ω := by group
      _ = ω := by rw [ht2]; group
  have hnotz : ¬ ∃ y : G, y * z * y⁻¹ = t * (t * ω) := by
    rintro ⟨y, hy⟩
    rw [hts] at hy
    have := not_commute_of_conj hs hW₀ hE4 hK hz (y := y) (by rw [hy]; exact hωz)
      (hRsyl.1 hc₁R) hc₁4
    rw [hy] at this
    exact this hωc₁
  have hnotN : conjSub (t * ω) (conjSub g K) ≠ conjSub g K := by
    intro hN
    have hJt : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
    have htJ : IsUniqueInvolution (conjSub g K) t := by
      have := hz.conj g
      rwa [hg] at this
    have hsN : t * ω ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr hN
    obtain ⟨Rt, hRtsyl, hRtinv⟩ := T3.exists_sylow_normalized (isPGroup_zpowers_of_sq hs2)
      (Subgroup.zpowers_le.mpr hsN)
    have hRtmem : Rt ∈ RSet Ω := mem_RSet_of_isSylow2In hJt hRtsyl
    have hRtq : IsQuatSub Rt := hΩ.isQuatSub_of_mem_RSet hp hRtmem
    have htRt : t ∈ Rt := T7C.mem_of_isSylow2In hp hΩ hJt hRtsyl htJ
    have hzRt : IsUniqueInvolution Rt t :=
      ⟨htRt, htJ.ne_one, htJ.sq, fun y hy hy2 => htJ.unique y (hRtsyl.1 hy) hy2⟩
    have hsRt : conjSub (t * ω) Rt = Rt := hRtinv _ (Subgroup.mem_zpowers _)
    have hbR : ∀ r ∈ Rt, (t * ω) * r * (t * ω)⁻¹ ∈ Rt := fun r hr => by
      have := conj_mem_conjSub (n := t * ω) hr
      rwa [hsRt] at this
    have hfixt : ∀ r ∈ Rt, orderOf r = 4 → (t * ω) * r * (t * ω)⁻¹ ≠ r := by
      intro r hr hr4 h
      obtain ⟨y, hy⟩ := hsy
      have := not_commute_of_conj hs hW₀ hE4 hJt htJ (y := y) (by rw [hy]; exact hsne)
        (hRtsyl.1 hr) hr4
      rw [hy] at this
      apply this
      have h1 := congrArg (fun w => w * (t * ω)) h
      simpa [mul_assoc] using h1
    obtain ⟨ρ, hρ, hρs⟩ := exists_conj_eq_mul_inv hRtq hzRt hs2 hbR hfixt
    apply hnotz
    obtain ⟨y, hy⟩ := hsy
    refine ⟨ρ⁻¹ * y, ?_⟩
    calc ρ⁻¹ * y * z * (ρ⁻¹ * y)⁻¹ = ρ⁻¹ * (y * z * y⁻¹) * ρ := by group
      _ = ρ⁻¹ * (t * ω) * ρ := by rw [hy]
      _ = ρ⁻¹ * ((t * ω) * ρ * (t * ω)⁻¹) * (t * ω) := by group
      _ = ρ⁻¹ * (ρ * t) * (t * ω) := by rw [hρs]
      _ = t * (t * ω) := by group
  refine ⟨g⁻¹ * (t * ω) * g, ?_, ?_, ?_, ?_⟩
  · calc g⁻¹ * (t * ω) * g * (g⁻¹ * (t * ω) * g) = g⁻¹ * ((t * ω) * (t * ω)) * g := by group
      _ = 1 := by rw [hs2]; group
  · have hzg : z = g⁻¹ * t * g := by rw [← hg]; group
    calc g⁻¹ * (t * ω) * g * z = g⁻¹ * ((t * ω) * t) * g := by rw [hzg]; group
      _ = g⁻¹ * (t * (t * ω)) * g := by rw [hst]
      _ = z * (g⁻¹ * (t * ω) * g) := by rw [hzg]; group
  · obtain ⟨y, hy⟩ := hsy
    refine ⟨g⁻¹ * y, ?_⟩
    calc g⁻¹ * y * z * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * z * y⁻¹) * g := by group
      _ = g⁻¹ * (t * ω) * g := by rw [hy]
  · intro hN
    apply hnotN
    have h1 : conjSub (g * (g⁻¹ * (t * ω) * g)) K = conjSub ((t * ω) * g) K := by
      congr 1; group
    rw [conjSub_mul, hN, conjSub_mul] at h1
    exact h1.symm

end T7ER

end CFSG.ClassicalInvolution.Asc77
