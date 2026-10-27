module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I131

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem conj_injective_of_center_eq_bot {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut S => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem card_le_nine_of_normalizes
    {S : Type} [Group S] [Finite S]
    (φ : S ≃* ↥CFSG.Quasithin.trialityGroup8) (hS : Nat.card S = 211341312)
    (hZ : Subgroup.center S = ⊥) (hO : Nat.card (Outer S) = 3)
    (Y : Subgroup (MulAut S)) (hYc : ∀ y ∈ Y, ∀ z ∈ Y, y * z = z * y) (hY3 : ∀ y ∈ Y, y ^ 3 = 1)
    (W : Subgroup S) (hW2 : IsPGroup 2 W) (hW : W ≠ ⊥)
    (hYW : ∀ y ∈ Y, ∀ w ∈ W, y w ∈ W) : Nat.card Y ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := conj_injective_of_center_eq_bot hZ
  have hW3 : ¬ 3 ∣ Nat.card W := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 hW2
    rw [hm]
    intro h
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  let E : Subgroup S := Y.comap (MulAut.conj : S →* MulAut S)
  have hmemE : ∀ x : S, x ∈ E ↔ MulAut.conj x ∈ Y := fun x => Iff.rfl
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    apply hinj
    rw [map_mul, map_mul]
    exact hYc _ ((hmemE x).1 hx) _ ((hmemE y).1 hy)
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hY3 _ ((hmemE x).1 hx)
  have hEnorm : ∀ x ∈ E, x ∈ Subgroup.normalizer (W : Set S) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hYW _ ((hmemE x).1 hx) h hh
      rwa [MulAut.conj_apply] at this
    · intro hh
      have hinv : MulAut.conj x⁻¹ ∈ Y := by
        rw [map_inv]
        exact Y.inv_mem ((hmemE x).1 hx)
      have := hYW _ hinv _ hh
      have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rw [MulAut.conj_apply, e] at this
      exact this
  have hEcard : Nat.card E ≤ 3 := by
    have hP : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEexp x.1 x.2)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hP
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · rw [hn]
      interval_cases n <;> norm_num
    · exfalso
      have hdvd : 3 ^ 2 ∣ Nat.card E := by
        rw [hn]
        exact pow_dvd_pow 3 hn2
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
      let F : Subgroup S := K.map E.subtype
      have hFcard : Nat.card F = 9 := by
        rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
        norm_num
      have hFle : F ≤ E := by
        rintro _ ⟨x, _, rfl⟩
        exact x.2
      have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
        rintro _ ⟨x, _, rfl⟩ _ ⟨y, _, rfl⟩
        exact hEcomm _ x.2 _ y.2
      have hFexp : ∀ a ∈ F, a ^ 3 = 1 := by
        rintro _ ⟨x, _, rfl⟩
        exact hEexp _ x.2
      have hFab : CFSG.Open.IsElemAbelian 3 F :=
        ⟨⟨⟨fun a b => Subtype.ext (hFcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hFexp x hx⟩
      have hFW : F ≤ Subgroup.normalizer (W : Set S) := fun x hx => hEnorm x (hFle hx)
      exact hW (CFSG.RankThree.PartTwo.Sec4.Item434D42.d4_k3_of_equiv φ hS hFab hFcard hW3 hFW)
  let q : MulAut S →* Outer S := QuotientGroup.mk' (inner S)
  let f : Y →* Outer S := q.comp Y.subtype
  have hY_eq : Nat.card Y = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hrange : Nat.card f.range ≤ 3 := by
    rw [← hO]
    exact Subgroup.card_le_card_group _
  have hk1 : ∀ x : Y, x ∈ f.ker ↔ ∃ s : S, MulAut.conj s = (x : MulAut S) := by
    intro x
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (inner S) (x : MulAut S) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (MonoidHom.mem_range (f := (MulAut.conj : S →* MulAut S)) (y := (x : MulAut S)))
  have hker : Nat.card f.ker ≤ 3 := by
    refine le_trans ?_ hEcard
    refine Nat.card_le_card_of_surjective
      (fun s : E => (⟨⟨MulAut.conj (s : S), (hmemE s).1 s.2⟩, (hk1 _).2 ⟨s, rfl⟩⟩ : f.ker)) ?_
    rintro ⟨⟨y, hy⟩, hk⟩
    obtain ⟨s, hs⟩ := (hk1 _).1 hk
    refine ⟨⟨s, (hmemE s).2 (by rw [hs]; exact hy)⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hs
  calc Nat.card Y = Nat.card f.range * Nat.card f.ker := hY_eq
    _ ≤ 3 * 3 := Nat.mul_le_mul hrange hker
    _ = 9 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.I131

end
