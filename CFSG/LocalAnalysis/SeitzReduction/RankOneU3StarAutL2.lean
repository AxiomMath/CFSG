module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3Outer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem card_eq_card_inf_centralizer_mul_card_range {G : Type*} [Group G] {Q D : Subgroup G}
    (hQD : Q ≤ normalizer (D : Set G)) :
    Nat.card Q = Nat.card (Q ⊓ centralizer (D : Set G) : Subgroup G) *
      Nat.card (D.normalizerMonoidHom.comp (inclusion hQD)).range := by
  set φ := D.normalizerMonoidHom.comp (inclusion hQD) with hφ
  have hφapp : ∀ (q : Q) (d : D), ((φ q d : D) : G) = (q : G) * d * (q : G)⁻¹ := fun q d => rfl
  have hker : φ.ker.map Q.subtype = Q ⊓ centralizer (D : Set G) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine mem_inf.mpr ⟨q.2, mem_centralizer_iff.mpr fun d hd => ?_⟩
      have h1 := congrArg (fun β : MulAut D => ((β ⟨d, hd⟩ : D) : G)) (MonoidHom.mem_ker.mp hq)
      simp only [hφapp, MulAut.one_apply] at h1
      calc d * (q : G) = (q : G) * d * (q : G)⁻¹ * q := by rw [h1]
        _ = (q : G) * d := by group
    · intro hx
      obtain ⟨hxQ, hxC⟩ := mem_inf.mp hx
      refine ⟨⟨x, hxQ⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      refine MulEquiv.ext fun d => Subtype.ext ?_
      rw [hφapp, MulAut.one_apply]
      have hdx := mem_centralizer_iff.mp hxC d d.2
      calc x * (d : G) * x⁻¹ = (d : G) * x * x⁻¹ := by rw [hdx]
        _ = d := by group
  have hcardker : Nat.card φ.ker = Nat.card (Q ⊓ centralizer (D : Set G) : Subgroup G) := by
    rw [← hker, card_map_of_injective Q.subtype_injective]
  rw [← hcardker, Subgroup.card_ker_mul_card_range]

theorem center_eq_bot_of_simple_nonabelian {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ center X := h ▸ mem_top a
    exact hab (mem_center_iff.mp ha b).symm

theorem card_le_of_isPGroup_mulAut_psl2 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* CFSG.Theory.Comparator.PSL2Model f) {P : Subgroup (MulAut X)} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 2 ^ f * 2 ^ padicValNat 2 f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut X) :=
    Finite.of_injective (fun β : MulAut X => (β : X → X)) DFunLike.coe_injective
  have hB : CFSG.GH74.Uniqueness.Bender.BenderType X f 1 1 := .linear f hf e
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = f :=
    hB.outer_linear.2
  obtain ⟨hs, a, b, hab⟩ := psl2Model_simple_nonabelian hf
  have hXs : IsSimpleGroup X := e.isSimpleGroup
  have hXnab : ∃ a b : X, a * b ≠ b * a := ⟨e.symm a, e.symm b, fun h => hab (by
    have := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this)⟩
  have hZ := center_eq_bot_of_simple_nonabelian hXs hXnab
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ center X := by
      rw [mem_center_iff]
      intro y
      have h1 := congrArg (fun β : MulAut X => β y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = g * y * g⁻¹ * g := by rw [h1]
        _ = g * y := by group
    rw [hZ] at hgZ
    exact mem_bot.mp hgZ
  have hcardInn : Nat.card (MulAut.conj : X →* MulAut X).range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcardAut : Nat.card (MulAut X) = Nat.card X * f := by
    rw [← (MulAut.conj : X →* MulAut X).range.card_mul_index, hcardInn, ← hout]
    rfl
  have hcardX : Nat.card X = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.GH74.Uniqueness.Bender.card_psl2_even f (by omega)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 2 ^ k ∣ ((2 ^ f) ^ 2 - 1) * (2 ^ f * f) := by
    have h1 := Subgroup.card_subgroup_dvd_card P
    rw [hk, hcardAut, hcardX] at h1
    have h2 : 2 ^ f * ((2 ^ f) ^ 2 - 1) * f = ((2 ^ f) ^ 2 - 1) * (2 ^ f * f) := by ring
    rwa [h2] at h1
  have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
    have h4 : 4 ≤ (2 ^ f) ^ 2 := by
      have : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
      nlinarith
    have hev : Even ((2 ^ f) ^ 2) := by
      rw [← pow_mul]
      exact (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨m, hm⟩ := hev
    exact ⟨m - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) ((2 ^ f) ^ 2 - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have hdvd' : 2 ^ k ∣ 2 ^ f * f := hcop.dvd_of_dvd_mul_left hdvd
  have hf0 : f ≠ 0 := by omega
  have hle : k ≤ f + padicValNat 2 f := by
    have h1 := (padicValNat_dvd_iff_le (p := 2) (by positivity)).mp hdvd'
    rwa [padicValNat.mul (by positivity) hf0, padicValNat.prime_pow] at h1
  rw [hk, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) hle

end CFSG.SeitzReduction.RankOne
