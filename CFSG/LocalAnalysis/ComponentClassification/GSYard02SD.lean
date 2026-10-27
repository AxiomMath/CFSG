module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Wreath
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup
open scoped Pointwise

private theorem eq_one_of_isPGroup_two {G : Type} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {m₀ : ℕ} (hm₀ : Odd m₀) {x : G} (hx : x ∈ P) (hxm : x ^ m₀ = 1) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  have h1 : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hx]; exact hk
  have h2 : orderOf x ∣ m₀ := orderOf_dvd_of_pow_eq_one hxm
  rw [h1] at h2
  have hcop : Nat.Coprime (2 ^ k) m₀ := (Nat.coprime_two_left.mpr hm₀).pow_left k
  have h3 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop h2
  rw [h3] at h1
  exact orderOf_eq_one_iff.mp h1

theorem sylowFourJoined_of_wreath_sylow {G Y : Type} [Group G] [Finite G] [Group Y]
    (π : G →* Y) (hπ : Function.Surjective π) {m₀ : ℕ} (hm₀ : Odd m₀)
    (hker : ∀ x : G, π x = 1 → x ^ m₀ = 1) (S : Sylow 2 G) {A B : Subgroup G} {τ z₁ c : G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB1 : A ⊓ B = ⊥)
    (hτ : τ * τ = 1) (hτA : ∀ a ∈ A, τ * a * τ ∈ B) (hτB : ∀ b ∈ B, τ * b * τ ∈ A)
    (hS : ∀ s ∈ (S : Subgroup G), ∃ a ∈ A, ∃ b ∈ B, s = a * b ∨ s = a * b * τ)
    (hAS : A ≤ S) (hBS : B ≤ S) (hτS : τ ∈ (S : Subgroup G))
    (hz₁ : z₁ ∈ A) (hz₁2 : z₁ * z₁ = 1) (hz₁1 : z₁ ≠ 1) (hz₁c : ∀ a ∈ A, a * z₁ = z₁ * a)
    (hc : c ∈ A) (hc2 : c * c = 1) (hcz : c ≠ z₁) (hc1 : c ≠ 1) : SylowFourJoined Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Y := Finite.of_surjective π hπ
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hinj : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), π x = π y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y = 1 := eq_one_of_isPGroup_two hSp hm₀ (S.mul_mem (S.inv_mem hx) hy)
      (hker _ (by rw [map_mul, map_inv, hxy, inv_mul_cancel]))
    exact inv_mul_eq_one.mp h1
  refine sylowFourJoined_of_sylow (S.mapSurjective hπ) fun E F hE hES hF hFS => ?_
  rw [Sylow.coe_mapSurjective] at hES hFS
  refine reflTransGen_commFourAdj_of_wreath (S := (S : Subgroup G).map π) (A := A.map π)
    (B := B.map π) (τ := π τ) (z₁ := π z₁) (c := π c) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ hE hES hF hFS
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAB a ha b hb]
  · rw [eq_bot_iff]
    rintro _ hx
    obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩ := Subgroup.mem_inf.mp hx
    have hab' : a = b := hinj a (hAS ha) b (hBS hb) hab.symm
    have : a ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨ha, hab' ▸ hb⟩
    rw [hAB1] at this
    rw [Subgroup.mem_bot.mp this, map_one]
    exact Subgroup.one_mem _
  · rw [← map_mul, hτ, map_one]
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, hτA a ha, by rw [map_mul, map_mul]⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨_, hτB b hb, by rw [map_mul, map_mul]⟩
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha, b, hb, h | h⟩ := hS s hs
    · exact ⟨π a, ⟨a, ha, rfl⟩, π b, ⟨b, hb, rfl⟩, Or.inl (by rw [h, map_mul])⟩
    · exact ⟨π a, ⟨a, ha, rfl⟩, π b, ⟨b, hb, rfl⟩, Or.inr (by rw [h, map_mul, map_mul])⟩
  · exact Subgroup.map_mono hAS
  · exact Subgroup.map_mono hBS
  · exact ⟨τ, hτS, rfl⟩
  · exact ⟨z₁, hz₁, rfl⟩
  · rw [← map_mul, hz₁2, map_one]
  · intro h
    exact hz₁1 (hinj z₁ (hAS hz₁) 1 (Subgroup.one_mem _) (by rw [h, map_one]))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, hz₁c a ha]
  · exact ⟨c, hc, rfl⟩
  · rw [← map_mul, hc2, map_one]
  · intro h
    exact hcz (hinj c (hAS hc) z₁ (hAS hz₁) h)
  · intro h
    exact hc1 (hinj c (hAS hc) 1 (Subgroup.one_mem _) (by rw [h, map_one]))

private theorem natCard_sup_of_le_normalizer {G : Type} [Group G] (E K : Subgroup G)
    (hK : K ≤ normalizer (E : Set G)) (hdisj : ∀ x ∈ E, x ∈ K → x = 1) :
    Nat.card ↥(E ⊔ K) = Nat.card E * Nat.card K := by
  have hset : ((E ⊔ K : Subgroup G) : Set G) = (E : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left E K hK
  rw [← Nat.card_prod]
  refine (Nat.card_eq_of_bijective (fun p : E × K => (⟨(p.1 : G) * p.2,
    mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ : ↥(E ⊔ K)))
    ⟨?_, ?_⟩).symm
  · rintro ⟨⟨e₁, he₁⟩, ⟨k₁, hk₁⟩⟩ ⟨⟨e₂, he₂⟩, ⟨k₂, hk₂⟩⟩ h
    have h' : e₁ * k₁ = e₂ * k₂ := congrArg Subtype.val h
    have hmem : e₂⁻¹ * e₁ ∈ E := mul_mem (inv_mem he₂) he₁
    have hmem' : e₂⁻¹ * e₁ ∈ K := by
      have : e₂⁻¹ * e₁ = k₂ * k₁⁻¹ := by
        calc e₂⁻¹ * e₁ = e₂⁻¹ * (e₁ * k₁) * k₁⁻¹ := by group
          _ = e₂⁻¹ * (e₂ * k₂) * k₁⁻¹ := by rw [h']
          _ = k₂ * k₁⁻¹ := by group
      rw [this]
      exact mul_mem hk₂ (inv_mem hk₁)
    have he : e₁ = e₂ := (inv_mul_eq_one.mp (hdisj _ hmem hmem')).symm
    subst he
    have hk : k₁ = k₂ := mul_left_cancel h'
    subst hk
    rfl
  · rintro ⟨x, hx⟩
    have hx' : x ∈ (E : Set G) * (K : Set G) := hset ▸ hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

private theorem eq_one_or_eq_of_mem_zpowers {G : Type} [Group G] {τ t : G} (hτ : τ * τ = 1)
    (ht : t ∈ zpowers τ) : t = 1 ∨ t = τ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have h2 : τ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hτ
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_one, h2, one_zpow, one_mul]

theorem exists_sylow_wreath {G Γ : Type} [Group G] [Group Γ] (emb : Γ × Γ →* G)
    (hemb : Function.Injective emb) {τ : G} (hτ : τ * τ = 1)
    (hτemb : ∀ g h, τ * emb (g, h) * τ = emb (h, g)) (hτne : ∀ g h, emb (g, h) ≠ τ)
    (D : Subgroup Γ) {k m : ℕ} (hD : Nat.card D = 2 ^ k) (hm : Odd m)
    (hcard : Nat.card G = 2 ^ (2 * k + 1) * m) :
    ∃ S : Sylow 2 G, (∀ s ∈ (S : Subgroup G), ∃ a ∈ D.map (emb.comp (MonoidHom.inl Γ Γ)),
        ∃ b ∈ D.map (emb.comp (MonoidHom.inr Γ Γ)), s = a * b ∨ s = a * b * τ) ∧
      D.map (emb.comp (MonoidHom.inl Γ Γ)) ≤ S ∧ D.map (emb.comp (MonoidHom.inr Γ Γ)) ≤ S ∧
      τ ∈ (S : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set fA : Γ →* G := emb.comp (MonoidHom.inl Γ Γ) with hfA
  set fB : Γ →* G := emb.comp (MonoidHom.inr Γ Γ) with hfB
  have hfA' : ∀ x, fA x = emb (x, 1) := fun x => rfl
  have hfB' : ∀ x, fB x = emb (1, x) := fun x => rfl
  have hfA_inj : Function.Injective fA := fun x y h => by
    have := hemb h
    simpa using congrArg Prod.fst this
  have hfB_inj : Function.Injective fB := fun x y h => by
    have := hemb h
    simpa using congrArg Prod.snd this
  set A : Subgroup G := D.map fA with hA
  set B : Subgroup G := D.map fB with hB
  have hcomm : ∀ x y, fA x * fB y = fB y * fA x := fun x y => by
    rw [hfA', hfB', ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, one_mul,
      one_mul, mul_one]
  have hABcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    exact hcomm x y
  have hBnorm : B ≤ normalizer (A : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer (A : Set G) (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      hABcomm a ha b hb)
  have hAB1 : ∀ x ∈ A, x ∈ B → x = 1 := by
    rintro _ ⟨x, -, rfl⟩ ⟨y, -, hxy⟩
    have h1 : (1, y) = (x, 1) := hemb (by rw [← hfB', ← hfA', hxy])
    have hx : x = 1 := (Prod.mk.inj h1).1.symm
    rw [hx, map_one]
  have hAcard : Nat.card A = 2 ^ k := by rw [hA, Subgroup.card_map_of_injective hfA_inj, hD]
  have hBcard : Nat.card B = 2 ^ k := by rw [hB, Subgroup.card_map_of_injective hfB_inj, hD]
  set E : Subgroup G := A ⊔ B with hE
  have hEcard : Nat.card E = 2 ^ k * 2 ^ k := by
    rw [hE, natCard_sup_of_le_normalizer A B hBnorm hAB1, hAcard, hBcard]
  have hτA : ∀ a ∈ A, τ * a * τ ∈ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [hfA', hfB', hτemb]⟩
  have hτB : ∀ b ∈ B, τ * b * τ ∈ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [hfA', hfB', hτemb]⟩
  have hEA : A ≤ E := le_sup_left
  have hEB : B ≤ E := le_sup_right
  have hEmul : ∀ e ∈ E, ∃ a ∈ A, ∃ b ∈ B, e = a * b := by
    intro e he
    have he' : e ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hBnorm]
      exact he
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp he'
    exact ⟨a, ha, b, hb, rfl⟩
  have hτE : ∀ e ∈ E, τ * e * τ ∈ E := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := hEmul e he
    have : τ * (a * b) * τ = (τ * a * τ) * (τ * b * τ) := by
      calc τ * (a * b) * τ = τ * a * (τ * τ) * b * τ := by rw [hτ]; group
        _ = (τ * a * τ) * (τ * b * τ) := by group
    rw [this]
    exact E.mul_mem (hEB (hτA a ha)) (hEA (hτB b hb))
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hτnorm : τ ∈ normalizer (E : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun e => ⟨fun he => ?_, fun he => ?_⟩
    · rw [hτinv]
      exact hτE e he
    · rw [hτinv] at he
      have := hτE _ he
      have h2 : τ * (τ * e * τ) * τ = e := by
        calc τ * (τ * e * τ) * τ = (τ * τ) * e * (τ * τ) := by group
          _ = e := by rw [hτ]; group
      rwa [h2] at this
  have hzn : zpowers τ ≤ normalizer (E : Set G) := Subgroup.zpowers_le.mpr hτnorm
  have hτ1 : τ ≠ 1 := by
    intro h
    exact hτne 1 1 ((map_one emb).trans h.symm)
  have hτcard : Nat.card (zpowers τ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hτ) hτ1
  have hdisj : ∀ x ∈ E, x ∈ zpowers τ → x = 1 := by
    intro x hxE hxz
    rcases eq_one_or_eq_of_mem_zpowers hτ hxz with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hEmul x hxE
      obtain ⟨u, -, rfl⟩ := ha
      obtain ⟨v, -, rfl⟩ := hb
      apply hτne u v
      rw [← h, hab, hfA', hfB', ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  set P : Subgroup G := E ⊔ zpowers τ with hP
  have hPcard : Nat.card P = 2 ^ (2 * k + 1) := by
    rw [hP, natCard_sup_of_le_normalizer E (zpowers τ) hzn hdisj, hEcard, hτcard]
    ring
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hPcard
  have hidx : ¬ 2 ∣ P.index := by
    have h1 := Subgroup.card_mul_index P
    rw [hPcard, hcard] at h1
    have h2 : P.index = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    exact hm.not_two_dvd_nat
  refine ⟨hP2.toSylow hidx, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : s ∈ (E : Set G) * (zpowers τ : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left E (zpowers τ) hzn]
      exact hs
    obtain ⟨e, he, t, ht, rfl⟩ := Set.mem_mul.mp hs'
    obtain ⟨a, ha, b, hb, rfl⟩ := hEmul e he
    rcases eq_one_or_eq_of_mem_zpowers hτ ht with rfl | rfl
    · exact ⟨a, ha, b, hb, Or.inl (mul_one _)⟩
    · exact ⟨a, ha, b, hb, Or.inr rfl⟩
  · exact (hEA.trans le_sup_left : A ≤ P)
  · exact (hEB.trans le_sup_left : B ≤ P)
  · exact (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ) : τ ∈ P)

theorem exists_sylow_two_containing {Γ : Type} [Group Γ] [Finite Γ] {z r : Γ} (hz2 : z * z = 1)
    (hr2 : r * r = 1) (hz1 : z ≠ 1) (hr1 : r ≠ 1) (hzr : z ≠ r) (hc : Commute z r) :
    ∃ D : Subgroup Γ, z ∈ D ∧ r ∈ D ∧ Nat.card D = 2 ^ (Nat.card Γ).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions z r hz2 hr2 hz1 hr1 hzr hc
  have hV2 : IsPGroup 2 (GorensteinWalter.kleinFourOfCommutingInvolutions z r hz2 hr2 hc) :=
    IsPGroup.of_card (n := 2) (by rw [hK.card_four]; norm_num)
  obtain ⟨Q, hQ⟩ := hV2.exists_le_sylow
  exact ⟨Q, hQ (Or.inr (Or.inl rfl)), hQ (Or.inr (Or.inr (Or.inl rfl))), Q.card_eq_multiplicity⟩

theorem sylowFourJoined_of_wreath_embedding {M Γ Y : Type} [Group M] [Group Γ] [Group Y]
    (H : Subgroup M) [Finite H] (π : H →* Y) (hπ : Function.Surjective π) {m₀ : ℕ}
    (hm₀ : Odd m₀) (hker : ∀ x : H, π x = 1 → x ^ m₀ = 1)
    (emb : Γ × Γ →* M) (hemb : Function.Injective emb) (hembH : ∀ p, emb p ∈ H)
    {τ : M} (hτH : τ ∈ H) (hτ : τ * τ = 1) (hτemb : ∀ g h, τ * emb (g, h) * τ = emb (h, g))
    (hτne : ∀ g h, emb (g, h) ≠ τ) (D : Subgroup Γ) {k m : ℕ} (hD : Nat.card D = 2 ^ k)
    (hm : Odd m) (hcard : Nat.card H = 2 ^ (2 * k + 1) * m) {z r : Γ} (hzD : z ∈ D) (hrD : r ∈ D)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hr2 : r * r = 1) (hr1 : r ≠ 1) (hrz : r ≠ z)
    (hzc : ∀ d ∈ D, d * z = z * d) : SylowFourJoined Y := by
  let emb' : Γ × Γ →* H := emb.codRestrict H hembH
  have hemb' : Function.Injective emb' := fun x y h => hemb (congrArg Subtype.val h)
  let τ' : H := ⟨τ, hτH⟩
  have hτ' : τ' * τ' = 1 := Subtype.ext hτ
  have hτemb' : ∀ g h, τ' * emb' (g, h) * τ' = emb' (h, g) := fun g h =>
    Subtype.ext (hτemb g h)
  have hτne' : ∀ g h, emb' (g, h) ≠ τ' := fun g h hh => hτne g h (congrArg Subtype.val hh)
  obtain ⟨S, hS, hAS, hBS, hτS⟩ := exists_sylow_wreath emb' hemb' hτ' hτemb' hτne' D hD hm hcard
  have hm2 : ∀ a b c d : Γ, emb' (a, b) * emb' (c, d) = emb' (a * c, b * d) := fun a b c d => by
    rw [← map_mul, Prod.mk_mul_mk]
  have hone : emb' (1, 1) = 1 := map_one emb'
  have hfst : ∀ a b : Γ, emb' (a, 1) = emb' (b, 1) → a = b := fun a b h => by
    simpa using congrArg Prod.fst (hemb' h)
  refine sylowFourJoined_of_wreath_sylow π hπ hm₀ hker S (τ := τ')
    (z₁ := emb' (z, 1)) (c := emb' (r, 1)) ?_ ?_ hτ' ?_ ?_ hS hAS hBS hτS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    show emb' (x, 1) * emb' (1, y) = emb' (1, y) * emb' (x, 1)
    rw [hm2, hm2, mul_one, one_mul, one_mul, mul_one]
  · rw [eq_bot_iff]
    rintro _ hx
    obtain ⟨⟨x, -, rfl⟩, ⟨y, -, hxy⟩⟩ := Subgroup.mem_inf.mp hx
    have h1 : (1, y) = (x, 1) := hemb' hxy
    have hx : x = 1 := (Prod.mk.inj h1).1.symm
    rw [Subgroup.mem_bot]
    show emb' (x, 1) = 1
    rw [hx]
    exact hone
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hτemb' x 1).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hτemb' 1 x).symm⟩
  · exact ⟨z, hzD, rfl⟩
  · rw [hm2, hz2, mul_one]
    exact hone
  · intro h
    exact hz1 (hfst z 1 (by rw [h, ← hone]))
  · rintro _ ⟨x, hx, rfl⟩
    show emb' (x, 1) * emb' (z, 1) = emb' (z, 1) * emb' (x, 1)
    rw [hm2, hm2, mul_one, hzc x hx]
  · exact ⟨r, hrD, rfl⟩
  · rw [hm2, hr2, mul_one]
    exact hone
  · intro h
    exact hrz (hfst r z h)
  · intro h
    exact hr1 (hfst r 1 (by rw [h, ← hone]))

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
