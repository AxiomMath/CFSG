module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakRes

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

theorem HasDiagOuterThree.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : HasDiagOuterThree X) : HasDiagOuterThree Y := by
  obtain ⟨α, hα⟩ := h
  refine ⟨MulAut.congr e α, fun k hk => hα k ?_⟩
  obtain ⟨y, hy⟩ := hk
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, map_pow]
  exact hy

theorem isCube_of_pow_eq_cube {G : Type*} [CommGroup G] {x y : G} {m : ℕ}
    (hm : Nat.Coprime m 3) (h : x ^ m = y ^ 3) : ∃ z : G, z ^ 3 = x := by
  have h1 : (QuotientGroup.mk x : G ⧸ (powMonoidHom 3 : G →* G).range) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  have h2 : (QuotientGroup.mk x : G ⧸ (powMonoidHom 3 : G →* G).range) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, h, QuotientGroup.eq_one_iff]
    exact ⟨y, rfl⟩
  have h3 : (QuotientGroup.mk x : G ⧸ (powMonoidHom 3 : G →* G).range) ^ Nat.gcd m 3 = 1 :=
    pow_gcd_eq_one.2 ⟨h2, h1⟩
  rw [hm, pow_one, QuotientGroup.eq_one_iff] at h3
  obtain ⟨z, hz⟩ := h3
  exact ⟨z, hz⟩

theorem exists_not_cube {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ μ : Kˣ, ∀ c : Kˣ, c ^ 3 ≠ μ := by
  by_contra hall
  push Not at hall
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective (powMonoidHom 3 : Kˣ →* Kˣ) := fun μ => hall μ
  have hinj : Function.Injective (powMonoidHom 3 : Kˣ →* Kˣ) :=
    Finite.injective_iff_surjective.2 hsurj
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x = 1 := hinj (by simpa using hx3)
  rw [hx1, orderOf_one] at hx
  omega

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
