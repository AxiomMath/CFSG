module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3FrMv
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Plus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnNF
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPolar
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.SP


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem d4_normalizesPSub_toralMinus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (s : 𝒞) (hs : D4MinusToral p f hp K σ s) :
    NormalizesPSub p (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₄, hF, hfin, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  obtain ⟨-, U₀, hU₀le, hU₀p, hU₀card⟩ :=
    un_polarity hp2 hf hq hK₄ σ₄ ε hσ₄ hε b hb3 hb1 s₄ hs₄
  have hfixR : ∀ y ∈ U₀.comap ψ₄, (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) y = y := by
    intro y hy
    apply hinj
    rw [hint]
    exact mem_foldFix.1 (Subgroup.mem_inf.1 (hU₀le hy)).1
  have hbij : Function.Bijective (ψ₄.subgroupComap U₀) := by
    refine ⟨fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (hfix z).1 (mem_foldFix.1 (Subgroup.mem_inf.1 (hU₀le hz)).2)
    exact ⟨⟨y, hz⟩, rfl⟩
  have hcard : Nat.card (U₀.comap ψ₄) = Nat.card U₀ := Nat.card_congr (Equiv.ofBijective _ hbij)
  have hq1 : 1 < (p ^ f) ^ 3 :=
    Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) hp.one_lt)
  refine ⟨U₀.comap ψ₄, fun hbot => ?_, hU₀p.of_injective (ψ₄.subgroupComap U₀) hbij.1, ?_⟩
  · have h1 := Subgroup.card_eq_one.2 hbot
    omega
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hfixR y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hfixR x hx⟩

theorem d4_ord3Alt_outer_minus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hq : (p ^ f) % 3 = 2) (φ : MulAut 𝒞) (hφ : orderOf φ = 3)
    (hout : φ ∉ (MulAut.conj : 𝒞 →* MulAut 𝒞).range) : Ord3Alt p φ := by
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : Fact p.Prime := ⟨hp⟩
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  obtain ⟨g, hg, hφg⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ φ hφ hout
  suffices key : Ord3Alt p (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) by
    rcases hφg with h | h
    · rw [h]
      exact key
    · apply ord3Alt_of_inv
      rw [h]
      exact key
  have hfA3 := d4_fieldActor_cube σ hK hσ
  rcases d4MinusNF p f hp hp2 hp3 hf hq K hK σ hσ g hg with ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ |
      ⟨y, n, hn, hyn⟩
  · refine ord3Alt_of_conj (MulAut.conj y) ?_
    rw [hy]
    have h := d4_normalizesPSub_toral σ (ℓ := p) (h := 1) (one_mem _) σ
    rw [map_one, one_mul] at h
    exact Or.inl h
  · refine ord3Alt_of_conj (MulAut.conj y) ?_
    rw [hys]
    exact Or.inl (d4_normalizesPSub_toralMinus σ hp hp2 hf hq hK hσ s hs)
  · refine ord3Alt_of_conj (MulAut.conj y) ?_
    rw [hyn]
    have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
      rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hfA3, map_one, one_mul, mul_one, mul_inv_cancel]
    have hN := normSeq_eq_one_of_pow_eq_one hZ hfA3 hcube
    obtain ⟨L, _, _, _, _, g₀, hg₀, hnM, hnT⟩ := hn
    rw [← d4MinusPsi_apply] at hnM hnT
    exact Or.inr (d4_frame_movesAbelianTwo_outer σ hp2 hf hK hσ hg₀ n hnM hnT hN)

end CFSG.OddStandard.GH71.S55
