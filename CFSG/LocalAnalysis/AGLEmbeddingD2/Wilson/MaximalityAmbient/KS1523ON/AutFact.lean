module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.GenThree
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def centerInvolutions {G : Type*} [Group G] (R₁ : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ R₁ ∧ (∀ r ∈ R₁, r * z = z * r) ∧ z * z = 1}
  one_mem' := ⟨one_mem _, fun r _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hac, ha2⟩ ⟨hb, hbc, hb2⟩
    refine ⟨mul_mem ha hb, fun r hr => ?_, ?_⟩
    · rw [← mul_assoc, hac r hr, mul_assoc, hbc r hr, mul_assoc]
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hbc a ha]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨ha, hac, ha2⟩
    refine ⟨inv_mem ha, fun r hr => ?_, ?_⟩
    · have := hac r hr
      calc r * a⁻¹ = a⁻¹ * (a * r) * a⁻¹ := by group
        _ = a⁻¹ * (r * a) * a⁻¹ := by rw [this]
        _ = a⁻¹ * r := by group
    · calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [ha2]; simp


theorem inf_inner_eq_bot {G : Type} [Group G] [Finite G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hrank : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] (hS512 : 512 < Nat.card S)
    (hbad : ∀ t : G, orderOf t = 2 → ∀ (W : Type) [Group W] [Finite W] (ψ : W →* G),
      Function.Injective ψ → (∀ w, ψ w ∈ Subgroup.centralizer ({t} : Set G)) →
      ∀ f : W →* S, Function.Surjective f → False)
    (R : Subgroup (MulAut G)) (X : Subgroup G) (hR : IsPGroup 2 R)
    (f : ↥X →* S) (hf : Function.Surjective f)
    (hnorm : ∀ x ∈ X, MulAut.conj x ∈ normalizer (R : Set (MulAut G))) :
    R ⊓ inner G = ⊥ := by
  classical
  by_contra hne
  set R₁ : Subgroup G := (R ⊓ inner G).comap (MulAut.conj : G →* MulAut G) with hR₁def
  obtain ⟨r, hr, hr1⟩ : ∃ r ∈ R ⊓ inner G, r ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_bot_iff.2 fun r hr => Subgroup.mem_bot.2 (h r hr))
  obtain ⟨g, rfl⟩ := hr.2
  have hgR₁ : g ∈ R₁ := hr
  have hg1 : g ≠ 1 := fun h => hr1 (by rw [h, map_one])
  have hker : IsPGroup 2 (MulAut.conj : G →* MulAut G).ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hR₁ : IsPGroup 2 R₁ := (hR.to_le inf_le_left).comap_of_ker_isPGroup _ hker
  have hXR₁ : ∀ x ∈ X, ∀ y ∈ R₁, x * y * x⁻¹ ∈ R₁ := by
    intro x hx y hy
    have hy' : MulAut.conj y ∈ R ⊓ inner G := hy
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 (hnorm x hx) (MulAut.conj y)).1 hy'.1
    · rw [map_mul, map_mul, map_inv]
      exact (inner G).mul_mem ((inner G).mul_mem ⟨x, rfl⟩ hy'.2) ((inner G).inv_mem ⟨x, rfl⟩)
  set E : Subgroup G := centerInvolutions R₁ with hEdef
  have hEmem : ∀ y, y ∈ E ↔ y ∈ R₁ ∧ (∀ r ∈ R₁, r * y = y * r) ∧ y * y = 1 := fun y => Iff.rfl
  have hEel : CFSG.Assembly.IsElemAbelian 2 E := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [isMulCommutative_iff]
      intro a b
      exact Subtype.ext (((hEmem a.1).1 a.2).2.1 b.1 ((hEmem b.1).1 b.2).1).symm
    · rw [pow_two]; exact ((hEmem x).1 hx).2.2
  have h8 : Nat.card E ≤ 8 := hrank E hEel
  have : Nontrivial R₁ := ⟨⟨⟨g, hgR₁⟩, 1, fun h => hg1 (congrArg Subtype.val h)⟩⟩
  have hZ : Nontrivial (Subgroup.center R₁) := hR₁.center_nontrivial
  have hZcard : 2 ∣ Nat.card (Subgroup.center R₁) := by
    have hp : IsPGroup 2 (Subgroup.center R₁) := hR₁.to_subgroup _
    obtain ⟨n, hn0, hn⟩ := hp.nontrivial_iff_card.1 hZ
    rw [hn]
    exact dvd_pow_self 2 hn0.ne'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R₁) 2 hZcard
  set t : G := ((z' : R₁) : G) with ht
  have htE : t ∈ E := by
    rw [hEmem]
    refine ⟨z'.1.2, fun r hr => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.1 z'.2 ⟨r, hr⟩
      exact congrArg Subtype.val this
    · have h2 : (z' : Subgroup.center R₁) ^ 2 = 1 := by rw [← hz']; exact pow_orderOf_eq_one _
      have h3 := congrArg (fun a : Subgroup.center R₁ => ((a : R₁) : G)) h2
      simpa [pow_two] using h3
  have ht2 : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz']
  have hconj : ∀ x ∈ X, ∀ y ∈ E, x * y * x⁻¹ ∈ E := by
    intro x hx y hy
    obtain ⟨hy1, hyc, hy2⟩ := (hEmem y).1 hy
    refine (hEmem _).2 ⟨hXR₁ x hx y hy1, fun r hr => ?_, ?_⟩
    · have h1 := hXR₁ x⁻¹ (inv_mem hx) r hr
      have h2 := hyc _ h1
      calc r * (x * y * x⁻¹) = x * ((x⁻¹ * r * x⁻¹⁻¹) * y) * x⁻¹ := by group
        _ = x * (y * (x⁻¹ * r * x⁻¹⁻¹)) * x⁻¹ := by rw [h2]
        _ = x * y * x⁻¹ * r := by group
    · calc x * y * x⁻¹ * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
        _ = 1 := by rw [hy2]; group
  have hXE : ∀ x ∈ X, x ∈ normalizer (E : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj x hx y hy, fun hy => ?_⟩
    have := hconj x⁻¹ (inv_mem hx) _ hy
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [e] at this
  let α : ↥X →* MulAut E :=
    E.normalizerMonoidHom.comp (X.subtype.codRestrict (normalizer (E : Set G)) (fun x => hXE x.1 x.2))
  have hαval : ∀ (x : X) (e : E), ((α x e : E) : G) = x * e * x⁻¹ := fun x e => rfl
  set U : Subgroup X := α.ker with hU
  have hUidx : U.index ≤ 512 := by
    have hfin : Finite E := inferInstance
    rw [hU, Subgroup.index_ker]
    exact (Nat.card_le_card_of_injective α.range.subtype Subtype.val_injective).trans
      (card_mulAut_le h8)
  have hUpos : 0 < U.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hUn : (U.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hUf : U.map f = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U.map f) with h | h
    · exfalso
      have hle : U ≤ f.ker := by
        intro w hw
        have : f w ∈ U.map f := ⟨w, hw, rfl⟩
        rw [h] at this
        exact this
      have h1 : f.ker.index ∣ U.index := Subgroup.index_dvd_of_le hle
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hf, Subgroup.card_top] at h1
      have := Nat.le_of_dvd hUpos h1
      omega
    · exact h
  refine hbad t ht2 U (X.subtype.comp U.subtype) ?_ ?_ (f.comp U.subtype) ?_
  · exact Subtype.val_injective.comp Subtype.val_injective
  · intro w
    rw [mem_centralizer_singleton_iff]
    have h1 : α w.1 = 1 := w.2
    have h2 := congrArg (fun a : MulAut E => ((a ⟨t, htE⟩ : E) : G)) h1
    simp only [hαval, MulAut.one_apply] at h2
    have h3 : w.1.1 * t * w.1.1⁻¹ = t := by simpa [Subgroup.coe_inv] using h2
    change w.1.1 * t = t * w.1.1
    calc w.1.1 * t = (w.1.1 * t * w.1.1⁻¹) * w.1.1 := by group
      _ = t * w.1.1 := by rw [h3]
  · intro s
    have : s ∈ U.map f := by rw [hUf]; trivial
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨⟨w, hw⟩, rfl⟩

theorem eq_bot_of_normalized {G : Type} [Group G] [Finite G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hout : Nat.card (Outer G) ∣ 2)
    (hrank : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8)
    (hI3 : ∀ τ : MulAut G, τ ^ 2 = 1 → τ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G → ∀ E : Subgroup G, Nat.card E = 9 →
      (∀ g ∈ E, τ g = g) → False)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] (hS512 : 512 < Nat.card S)
    (hS9 : 9 ∣ Nat.card S)
    (hbad : ∀ t : G, orderOf t = 2 → ∀ (W : Type) [Group W] [Finite W] (ψ : W →* G),
      Function.Injective ψ → (∀ w, ψ w ∈ Subgroup.centralizer ({t} : Set G)) →
      ∀ f : W →* S, Function.Surjective f → False)
    (R : Subgroup (MulAut G)) (X : Subgroup G) (hR : IsPGroup 2 R)
    (f : ↥X →* S) (hf : Function.Surjective f)
    (hnorm : ∀ x ∈ X, MulAut.conj x ∈ normalizer (R : Set (MulAut G))) :
    R = ⊥ := by
  classical
  have hinf := inf_inner_eq_bot hinj hrank hS512 hbad R X hR f hf hnorm
  by_contra hR1
  obtain ⟨τ, hτR, hτ1⟩ : ∃ τ ∈ R, τ ≠ 1 := by
    by_contra h
    push Not at h
    exact hR1 (eq_bot_iff.2 fun r hr => Subgroup.mem_bot.2 (h r hr))
  let ι : R →* Outer G := (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner G)).comp R.subtype
  have hι : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    have h1 : (r : MulAut G) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
      have := (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner G) (r : MulAut G)).1 (MonoidHom.mem_ker.1 hr)
      exact this
    have : (r : MulAut G) ∈ R ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner G := ⟨r.2, h1⟩
    rw [hinf] at this
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 this))
  have hR2 : Nat.card R = 2 := by
    have hd : Nat.card R ∣ 2 := (Subgroup.card_dvd_of_injective ι hι).trans hout
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exfalso
      have := (Nat.card_eq_one_iff_unique.1 h).1
      exact hτ1 (congrArg Subtype.val (Subsingleton.elim (⟨τ, hτR⟩ : R) 1))
    · exact h
  obtain ⟨u, -, huq⟩ := (Nat.card_eq_two_iff' (1 : R)).1 hR2
  have hτ' : (⟨τ, hτR⟩ : R) ≠ 1 := fun h => hτ1 (congrArg Subtype.val h)
  have hτsq : τ ^ 2 = 1 := by
    by_contra h
    have h2 : (⟨τ ^ 2, R.pow_mem hτR 2⟩ : R) ≠ 1 := fun h' => h (congrArg Subtype.val h')
    have := (huq _ h2).trans (huq _ hτ').symm
    exact hτ1 (by
      have h3 : τ ^ 2 = τ := congrArg Subtype.val this
      calc τ = τ ^ 2 * τ⁻¹ := by group
        _ = 1 := by rw [h3]; group)
  have hτinner : τ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
    intro h
    have : τ ∈ R ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner G := ⟨hτR, h⟩
    rw [hinf] at this
    exact hτ1 (Subgroup.mem_bot.1 this)
  have hfix : ∀ x ∈ X, τ x = x := by
    intro x hx
    have hσ := (mem_normalizer_iff.1 (hnorm x hx) τ).1 hτR
    have hσ1 : (MulAut.conj x) * τ * (MulAut.conj x)⁻¹ ≠ 1 := by
      intro h
      apply hτ1
      calc τ = (MulAut.conj x)⁻¹ * ((MulAut.conj x) * τ * (MulAut.conj x)⁻¹) * (MulAut.conj x) := by
            group
        _ = 1 := by rw [h]; group
    have heq : (MulAut.conj x) * τ * (MulAut.conj x)⁻¹ = τ :=
      congrArg Subtype.val ((huq ⟨_, hσ⟩ (fun h => hσ1 (congrArg Subtype.val h))).trans
        (huq _ hτ').symm)
    have hcomm : (MulAut.conj x) * τ = τ * (MulAut.conj x) := by
      calc (MulAut.conj x) * τ = ((MulAut.conj x) * τ * (MulAut.conj x)⁻¹) * (MulAut.conj x) := by
            group
        _ = τ * (MulAut.conj x) := by rw [heq]
    have hcx : (MulAut.conj x : MulAut G) = MulAut.conj (τ x) := by
      ext g'
      obtain ⟨g, rfl⟩ := τ.surjective g'
      have h1 := congrArg (fun a : MulAut G => a g) hcomm
      simp only [MulAut.mul_apply, MulAut.conj_apply] at h1 ⊢
      rw [h1, map_mul, map_mul, map_inv]
    exact (hinj hcx).symm
  obtain ⟨H, hH⟩ : ∃ H : Subgroup X, Nat.card H = 3 ^ 2 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine Sylow.exists_subgroup_card_pow_prime 3 ?_
    have h1 : Nat.card S ∣ Nat.card X := Subgroup.card_dvd_of_surjective hf
    have h2 : 3 ^ 2 ∣ Nat.card S := by simpa using hS9
    exact h2.trans h1
  refine hI3 τ hτsq hτinner (H.map X.subtype) ?_ ?_
  · rw [Subgroup.card_map_of_injective (Subtype.val_injective), hH]; norm_num
  · rintro _ ⟨h, -, rfl⟩
    exact hfix h.1 h.2

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON
