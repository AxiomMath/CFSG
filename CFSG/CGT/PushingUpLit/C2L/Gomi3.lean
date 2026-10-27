module

public import CFSG.CGT.PushingUpLit.C2L.GomiMax
public import CFSG.CGT.PushingUpLit.C2L.Tame
public import CFSG.CGT.PushingUpLit.C2L.StrongTI

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG.ABGLocalTools

variable {G : Type} [Group G]

@[expose] def IsLeastGomiH0 (P H : Subgroup G) : Prop :=
  GomiH0In P H ∧ ∀ K : Subgroup G, GomiH0In P K → H ≤ K

namespace IsLeastGomiH0

theorem unique {P H H' : Subgroup G} (h : IsLeastGomiH0 P H) (h' : IsLeastGomiH0 P H') :
    H = H' :=
  le_antisymm (h.2 H' h'.1) (h'.2 H h.1)

theorem map_conj [Finite G] {P H : Subgroup G} (h : IsLeastGomiH0 P H) (g : G) :
    IsLeastGomiH0 (P.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨⟨h.1.1.map_conj g, Subgroup.map_mono h.1.2⟩, fun K hK => ?_⟩
  have h1 : GomiH0In P (K.map (MulAut.conj g⁻¹).toMonoidHom) := by
    refine ⟨hK.1.map_conj g⁻¹, ?_⟩
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hK.2
    rwa [map_conj_inv_map_conj] at this
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (h.2 _ h1)
  rwa [map_conj_map_conj_inv] at h2

theorem eq_of_link {A B HA HB D : Subgroup G} (hlink : TameLink D A B)
    (hA : IsLeastGomiH0 A HA) (hB : IsLeastGomiH0 B HB) : HA = HB := by
  have hK : GomiH0 (A ⊓ B) := hlink.2.2.2.2.2
  have h1 : HA ≤ A ⊓ B := hA.2 _ ⟨hK, inf_le_left⟩
  have h2 : HB ≤ A ⊓ B := hB.2 _ ⟨hK, inf_le_right⟩
  exact le_antisymm (hA.2 HB ⟨hB.1.1, h2.trans inf_le_left⟩)
    (hB.2 HA ⟨hA.1.1, h1.trans inf_le_right⟩)

end IsLeastGomiH0

variable [Finite G]

theorem exists_isLeastGomiH0_of_sylow {P H : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hH : IsLeastGomiH0 P H) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) :
    ∃ H' : Subgroup G, IsLeastGomiH0 S H' := by
  obtain ⟨g, -, hg⟩ := exists_eq_map_conj_of_isSylowOf hP hS
  exact ⟨H.map (MulAut.conj g).toMonoidHom, by rw [hg]; exact hH.map_conj g⟩

theorem IsLeastGomiH0.eq_of_inf_ne_bot {X Y HX HY : Subgroup G} (hX : IsSylowOf 2 X ⊤)
    (hY : IsSylowOf 2 Y ⊤) (hXY : X ⊓ Y ≠ ⊥)
    (hall : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ∃ H, IsLeastGomiH0 S H)
    (hHX : IsLeastGomiH0 X HX) (hHY : IsLeastGomiH0 Y HY) : HX = HY := by
  have hchain := tameChain_of_inf_ne_bot hX hY hXY
  suffices h : ∀ S : Subgroup G, Relation.ReflTransGen (TameLink (X ⊓ Y)) X S →
      ∀ H, IsLeastGomiH0 S H → H = HX from (h Y hchain HY hHY).symm
  intro S hS
  induction hS with
  | refl => exact fun H hH => hH.unique hHX
  | @tail S S' _ hlink ih =>
    intro H' hH'
    obtain ⟨H, hH⟩ := hall S hlink.1
    rw [← IsLeastGomiH0.eq_of_link hlink hH hH', ih H hH]

omit [Finite G] in
private theorem mem_map_conj_inv_iff'' {H : Subgroup G} {g y : G} :
    y ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

theorem not_exists_isLeast_gomiH0In
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    {P : Subgroup G} (hP : IsSylowOf 2 P ⊤) : ¬ ∃ H, IsLeastGomiH0 P H := by
  rintro ⟨H₁, hH₁⟩
  have hall : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ∃ H, IsLeastGomiH0 S H :=
    fun S hS => exists_isLeastGomiH0_of_sylow hP hH₁ hS
  have hgomi : GomiH H₁ := hH₁.1.1.1
  have hH₁P : H₁ ≤ P := hH₁.1.2
  have hH₁ne : H₁ ≠ ⊥ := hgomi.ne_bot
  have hH₁2 : IsPGroup 2 H₁ := hgomi.isPGroup
  have hleast : ∀ Q : Subgroup G, IsSylowOf 2 Q ⊤ → P ⊓ Q ≠ ⊥ → IsLeastGomiH0 Q H₁ := by
    intro Q hQ hPQ
    obtain ⟨HQ, hHQ⟩ := hall Q hQ
    rw [IsLeastGomiH0.eq_of_inf_ne_bot hP hQ hPQ hall hH₁ hHQ]
    exact hHQ
  have hPN : P ≤ Subgroup.normalizer (H₁ : Set G) := by
    intro x hx
    have hxP : P.map (MulAut.conj x).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hx)
    have h1 : GomiH0In P (H₁.map (MulAut.conj x).toMonoidHom) :=
      ⟨hH₁.1.1.map_conj x, hxP ▸ Subgroup.map_mono hH₁P⟩
    have h2 : H₁ ≤ H₁.map (MulAut.conj x).toMonoidHom := hH₁.2 _ h1
    have h3 : H₁.map (MulAut.conj x).toMonoidHom = H₁ :=
      (Subgroup.eq_of_le_of_card_ge h2 (by
        rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])).symm
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h3
  set N : Subgroup G := Subgroup.normalizer (H₁ : Set G) with hN
  have hH₁N : H₁ ≤ N := Subgroup.le_normalizer
  have hPN' : IsSylowOf 2 P N := hP.of_le hPN le_top
  have hNsyl : ∀ Q : Subgroup G, IsSylowOf 2 Q N → IsSylowOf 2 Q ⊤ := by
    intro Q hQ
    obtain ⟨n, -, hn⟩ := exists_eq_map_conj_of_isSylowOf hPN' hQ
    rw [hn]
    exact isSylowOf_top_map_conj hP n
  have hNleast : ∀ Q : Subgroup G, IsSylowOf 2 Q N → IsLeastGomiH0 Q H₁ := by
    intro Q hQ
    have hH₁Q : H₁ ≤ Q := le_of_isSylowOf_of_normal hQ hH₁N le_rfl hH₁2
    refine hleast Q (hNsyl Q hQ) fun h => hH₁ne ?_
    have := le_inf hH₁P hH₁Q
    rw [h] at this
    exact le_bot_iff.1 this
  have hSE : CFSG.Open.fusionStronglyEmbedded N := by
    refine ⟨?_, ?_, ?_⟩
    · intro htop
      exact hH₁ne (hO2 H₁ (Subgroup.normalizer_eq_top_iff.1 htop) hH₁2)
    · have hP0 : P ≠ ⊥ := fun h => hH₁ne (le_bot_iff.1 (h ▸ hH₁P))
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP.isPGroup
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hP0 ((Subgroup.eq_bot_iff_card P).2 (by simpa using hk))
      exact even_iff_two_dvd.2 ((hk ▸ dvd_pow_self 2 hk0).trans (Subgroup.card_dvd_of_le hPN))
    · intro g hg
      by_contra hodd
      rw [Nat.not_odd_iff_even] at hodd
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
      have htN : (t : G) ∈ N := t.2.1
      have htNg : (t : G) ∈ N.map (MulAut.conj g⁻¹).toMonoidHom := t.2.2
      have hord : orderOf (t : G) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact ht
      have ht1 : (t : G) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hord
        omega
      have hvN : g * (t : G) * g⁻¹ ∈ N := mem_map_conj_inv_iff''.1 htNg
      have hvord : orderOf (g * (t : G) * g⁻¹) = 2 := by
        rw [← hord]
        simpa [mul_assoc] using orderOf_injective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective (t : G)
      have hzp : ∀ s : G, orderOf s = 2 → IsPGroup 2 (Subgroup.zpowers s) := fun s hs => by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, hs, pow_one]
      obtain ⟨Q, hQ, hQt⟩ := exists_isSylowOf_ge ((Subgroup.zpowers_le).2 htN) (hzp _ hord)
      obtain ⟨R, hR, hRv⟩ := exists_isSylowOf_ge ((Subgroup.zpowers_le).2 hvN) (hzp _ hvord)
      have htQ : (t : G) ∈ Q := hQt (Subgroup.mem_zpowers _)
      have hvR : g * (t : G) * g⁻¹ ∈ R := hRv (Subgroup.mem_zpowers _)
      have hRg : IsSylowOf 2 (R.map (MulAut.conj g⁻¹).toMonoidHom) ⊤ :=
        isSylowOf_top_map_conj (hNsyl R hR) g⁻¹
      have htRg : (t : G) ∈ R.map (MulAut.conj g⁻¹).toMonoidHom := mem_map_conj_inv_iff''.2 hvR
      have hne : Q ⊓ R.map (MulAut.conj g⁻¹).toMonoidHom ≠ ⊥ := by
        intro h
        have : (t : G) ∈ Q ⊓ R.map (MulAut.conj g⁻¹).toMonoidHom := ⟨htQ, htRg⟩
        rw [h, Subgroup.mem_bot] at this
        exact ht1 this
      have heq := IsLeastGomiH0.eq_of_inf_ne_bot (hNsyl Q hQ) hRg hne hall (hNleast Q hQ)
        ((hNleast R hR).map_conj g⁻¹)
      have hginv : g⁻¹ ∈ N := Subgroup.mem_normalizer_iff_map_conj_eq.2 heq.symm
      exact hg (by simpa using N.inv_mem hginv)
  obtain ⟨R, hR, hRP, hH₁R⟩ := hgomi.exists_sylow_ne P
  have hTI := StrongTI.sylow_inf_eq_bot_of_stronglyEmbedded hSE hO hO2 hP hR (Ne.symm hRP)
  have := le_inf hH₁P hH₁R
  rw [hTI] at this
  exact hH₁ne (le_bot_iff.1 this)

theorem gomiH0In_not_existsUnique_minimal
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    {P : Subgroup G} (hP : IsSylowOf 2 P ⊤) : ¬ ∃! H : Subgroup G, Minimal (GomiH0In P) H := by
  rintro ⟨H, hmin, huniq⟩
  refine not_exists_isLeast_gomiH0In hO hO2 hP ⟨H, hmin.1, fun K hK => ?_⟩
  obtain ⟨M, hMK, hM⟩ := exists_minimal_le_of_wellFoundedLT (GomiH0In P) K hK
  rw [← huniq M hM]
  exact hMK

theorem gomiH0In_empty_or_two_minimal
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    {P : Subgroup G} (hP : IsSylowOf 2 P ⊤) :
    (∀ H : Subgroup G, ¬ GomiH0In P H) ∨
      ∃ H₁ H₂ : Subgroup G, H₁ ≠ H₂ ∧ Minimal (GomiH0In P) H₁ ∧ Minimal (GomiH0In P) H₂ := by
  by_cases hne : ∃ H, GomiH0In P H
  · right
    obtain ⟨H₁, hH₁⟩ := exists_minimal_of_wellFoundedLT (GomiH0In P) hne
    by_contra hcon
    refine gomiH0In_not_existsUnique_minimal hO hO2 hP ⟨H₁, hH₁, fun H₂ hH₂ => ?_⟩
    by_contra hne'
    exact hcon ⟨H₁, H₂, Ne.symm hne', hH₁, hH₂⟩
  · left
    exact fun H hH => hne ⟨H, hH⟩

theorem gomiH0In_empty_or_two
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    {P : Subgroup G} (hP : IsSylowOf 2 P ⊤) :
    (∀ H : Subgroup G, ¬ GomiH0In P H) ∨
      ∃ H₁ H₂ : Subgroup G, H₁ ≠ H₂ ∧ GomiH0In P H₁ ∧ GomiH0In P H₂ := by
  rcases gomiH0In_empty_or_two_minimal hO hO2 hP with h | ⟨H₁, H₂, hne, h₁, h₂⟩
  · exact Or.inl h
  · exact Or.inr ⟨H₁, H₂, hne, h₁.1, h₂.1⟩

end CFSG.CGT.PushingUpLit.C2L
