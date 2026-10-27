module

public import CFSG.ClassicalInvolution.Q3.TL4S3DichA
public import CFSG.ClassicalInvolution.Asc77.WP1Defs
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.S3Dich

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance.Q27
open scoped MatrixGroups

section Transport

variable {S T : Type} [Group S] [Group T]

@[expose] def InvDich (S : Type) [Group S] (R : Subgroup S) : Prop :=
  ∀ ρ : MulAut S, ρ * ρ = 1 → (∀ r ∈ R, ρ r = r) → ∃ k ∈ R, k * k = 1 ∧ ρ = MulAut.conj k

theorem InvDich.map (e : S ≃* T) {R : Subgroup S} (h : InvDich S R) :
    InvDich T (R.map e.toMonoidHom) := by
  intro ρ hρ2 hρR
  have h2 : MulAut.congr e.symm ρ * MulAut.congr e.symm ρ = 1 := by
    rw [← map_mul, hρ2, map_one]
  have hfix : ∀ r ∈ R, MulAut.congr e.symm ρ r = r := by
    intro r hr
    have h1 : ρ (e r) = e r := hρR _ ⟨r, hr, rfl⟩
    simp [MulAut.congr_apply, h1]
  obtain ⟨k, hkR, hk2, hρk⟩ := h _ h2 hfix
  refine ⟨e k, ⟨k, hkR, rfl⟩, by rw [← map_mul, hk2, map_one], ?_⟩
  have hback : MulAut.congr e (MulAut.congr e.symm ρ) = ρ := by
    ext y
    simp [MulAut.congr_apply]
  rw [← hback, hρk]
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem isSylow2In_map (e : S ≃* T) {V P : Subgroup S} (h : IsSylow2In V P) :
    IsSylow2In (V.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, fun V' hV'P hV'2 hle => ?_⟩
  have h1 : V'.comap e.toMonoidHom ≤ P := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hV'P hx
    rwa [← e.injective hxy]
  have h3 : V ≤ V'.comap e.toMonoidHom := fun x hx => hle ⟨x, hx, rfl⟩
  rw [← h.2.2 _ h1 (hV'2.comap_of_injective _ e.injective) h3,
    Subgroup.map_comap_eq_self_of_surjective e.surjective]

theorem isSylow2In_conj {V P : Subgroup S} (g : S) (h : IsSylow2In V (conjSub g P)) :
    IsSylow2In (conjSub g⁻¹ V) P := by
  have h1 := isSylow2In_map (MulAut.conj g⁻¹) h
  change IsSylow2In (conjSub g⁻¹ V) (conjSub g⁻¹ (conjSub g P)) at h1
  rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at h1

end Transport

section Chart

variable {Y : Type} [Group Y] (ι : SL(2, ZMod 3) →* Y) (hι : Function.Injective ι)

theorem pow_four_of_pow_eight : ∀ a : SL(2, ZMod 3), a ^ 8 = 1 → a ^ 4 = 1 := by
  decide +kernel

theorem pow_four_of_pow_two_pow {a : SL(2, ZMod 3)} {n : ℕ} (ha : a ^ 2 ^ n = 1) : a ^ 4 = 1 := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha)
  have h24 : orderOf a ∣ 8 * 3 := by
    have h := orderOf_dvd_natCard a
    rwa [natCard_sl2Three] at h
  have h8 : orderOf a ∣ 8 := by
    rw [hm] at h24 ⊢
    exact (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right h24
  exact pow_four_of_pow_eight a (orderOf_dvd_iff_pow_eq_one.mp h8)

include hι

theorem sylow_eq_map {L₀ : Subgroup Y} (hL₀ : IsSylow2In L₀ ι.range) :
    L₀ = sl2ThreeQ.map ι := by
  have hQ : IsPGroup 2 (sl2ThreeQ.map ι) :=
    (IsPGroup.of_card (n := 3) (by rw [natCard_sl2ThreeQ]; rfl)).map ι
  refine (hL₀.2.2 _ (Subgroup.map_le_range ι _) hQ fun x hx => ?_).symm
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp (hL₀.1 hx)
  obtain ⟨n, hn⟩ := hL₀.2.1 ⟨ι y, hx⟩
  refine ⟨y, mem_sl2ThreeQ_iff.mpr (pow_four_of_pow_two_pow (n := n) (hι ?_)), rfl⟩
  have h := congrArg Subtype.val hn
  simpa using h

theorem mem_of_pow_four {L₀ : Subgroup Y} (hL₀ : IsSylow2In L₀ ι.range) {k : SL(2, ZMod 3)}
    (hk : k ^ 4 = 1) : ι k ∈ L₀ := by
  rw [sylow_eq_map ι hι hL₀]
  exact ⟨k, mem_sl2ThreeQ_iff.mpr hk, rfl⟩

theorem isUniqueInvolution_range : IsUniqueInvolution ι.range (ι (-1)) where
  mem := ⟨-1, rfl⟩
  ne_one h := neg_one_ne_one (hι (h.trans (map_one ι).symm))
  sq := by rw [← map_mul, neg_one_mul_self, map_one]
  unique y hy hy2 := by
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    have hx2 : x * x = 1 := hι (by rw [map_mul, hy2, map_one])
    rcases eq_of_mul_self x hx2 with rfl | rfl
    · exact Or.inl (map_one ι)
    · exact Or.inr rfl

theorem isUniqueInvolution_sylow {L₀ : Subgroup Y} (hL₀ : IsSylow2In L₀ ι.range) :
    IsUniqueInvolution L₀ (ι (-1)) where
  mem := mem_of_pow_four ι hι hL₀ neg_one_pow_four
  ne_one := (isUniqueInvolution_range ι hι).ne_one
  sq := (isUniqueInvolution_range ι hι).sq
  unique y hy hy2 := (isUniqueInvolution_range ι hι).unique y (hL₀.1 hy) hy2

theorem normalizes_of_noTwins
    (hT : ∀ g : Y, IsUniqueInvolution (conjSub g ι.range) (ι (-1)) →
      conjSub g ι.range = ι.range) :
    ∀ g : Y, g * ι (-1) = ι (-1) * g → ∀ x, ∃ x', g * ι x * g⁻¹ = ι x' := by
  intro g hg x
  have hU := (isUniqueInvolution_range ι hι).conj g
  rw [hg, mul_inv_cancel_right] at hU
  have h1 : g * ι x * g⁻¹ ∈ conjSub g ι.range := conj_mem_conjSub ⟨x, rfl⟩
  rw [hT g hU] at h1
  obtain ⟨x', hx'⟩ := MonoidHom.mem_range.mp h1
  exact ⟨x', hx'.symm⟩

theorem invDich_of_upgrade (hO : InvolutionOddCoreTrivial Y)
    (hN : ∀ g : Y, g * ι (-1) = ι (-1) * g → ∀ x, ∃ x', g * ι x * g⁻¹ = ι x')
    (hfg : InvDich Y ι.range) {L₀ : Subgroup Y} (hL₀ : IsSylow2In L₀ ι.range) :
    InvDich Y L₀ := by
  intro ρ hρ2 hρL
  have hfix := fixes_of_fixes_q8 hO ι hι hN ρ fun k hk => hρL _ (mem_of_pow_four ι hι hL₀ hk)
  obtain ⟨k, hkR, hk2, hρk⟩ := hfg ρ hρ2 (by
    rintro _ ⟨x, rfl⟩
    exact hfix x)
  refine ⟨k, ?_, hk2, hρk⟩
  rcases (isUniqueInvolution_range ι hι).unique k hkR hk2 with rfl | rfl
  · exact L₀.one_mem
  · exact (isUniqueInvolution_sylow ι hι hL₀).mem

end Chart

end CFSG.ClassicalInvolution.Q3.TL4.S3Dich
