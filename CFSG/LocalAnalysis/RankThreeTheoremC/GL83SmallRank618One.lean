module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618L32

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped MatrixGroups

private lemma layerAbs_ker_surj {Y C R : Type} [Group Y] [CommGroup C] [Group R]
    [IsSimpleGroup R] (ρ : Y →* C) {D : Subgroup Y} (hR : ∃ a b : R, a * b ≠ b * a)
    (f : ↥D →* R) (hf : Function.Surjective f) :
    ∀ r : R, ∃ d : ↥D, ρ (d : Y) = 1 ∧ f d = r := by
  set N : Subgroup ↥D := (ρ.comp D.subtype).ker with hN
  have : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hR
    obtain ⟨d₁, rfl⟩ := hf a
    obtain ⟨d₂, rfl⟩ := hf b
    have hmem : d₁ * d₂ * d₁⁻¹ * d₂⁻¹ ∈ N := by
      simp [hN]
    have h1 : f (d₁ * d₂ * d₁⁻¹ * d₂⁻¹) ∈ N.map f := Subgroup.mem_map_of_mem f hmem
    rw [h, Subgroup.mem_bot] at h1
    apply hab
    simpa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] using h1
  · intro r
    have hr : r ∈ N.map f := h ▸ Subgroup.mem_top r
    obtain ⟨d, hd, rfl⟩ := hr
    exact ⟨d, hd, rfl⟩

private lemma layerAbs_layer_surj {Y A C R : Type} [Group Y] [Group A] [CommGroup C] [Group R]
    [Finite R] [IsSimpleGroup R] (ρ : Y →* C) (π : Y →* A) {I : Subgroup A} [I.Normal]
    (hindex : ¬ 3 ∣ I.index) {D : Subgroup Y} (hR : ∃ a b : R, a * b ≠ b * a)
    (h3 : 3 ∣ Nat.card R) (f : ↥D →* R) (hf : Function.Surjective f) :
    ∀ r : R, ∃ d : ↥D, ρ (d : Y) = 1 ∧ π (d : Y) ∈ I ∧ f d = r := by
  have hker := layerAbs_ker_surj ρ hR f hf
  set N : Subgroup ↥D := (ρ.comp D.subtype).ker ⊓ I.comap (π.comp D.subtype) with hN
  have : N.Normal := by
    have : ((ρ.comp D.subtype).ker).Normal := MonoidHom.normal_ker _
    have : (I.comap (π.comp D.subtype)).Normal := Subgroup.normal_comap _
    exact Subgroup.normal_inf_normal _ _
  have : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
  · exfalso
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨d, hd, rfl⟩ := hker r
    have hdn : d ^ I.index ∈ N := by
      refine ⟨?_, ?_⟩
      · simp [hd]
      · simpa using I.pow_index_mem (π d)
    have h1 : f (d ^ I.index) ∈ N.map f := Subgroup.mem_map_of_mem f hdn
    rw [h, Subgroup.mem_bot, map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hr] at h2
    exact hindex h2
  · intro r
    have hr : r ∈ N.map f := h ▸ Subgroup.mem_top r
    obtain ⟨d, hd, rfl⟩ := hr
    exact ⟨d, hd.1, hd.2, rfl⟩

private lemma layerAbs_bijective {G R : Type} [Group G] [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ∃ a b : R, a * b ≠ b * a) (g : G →* PSL(3, ZMod 2)) (hg : Function.Injective g)
    (φ : G →* R) (hφ : Function.Surjective φ) :
    Function.Bijective g ∧ Function.Bijective φ := by
  let f₁ : ↥g.range →* R := φ.comp (MonoidHom.ofInjective hg).symm.toMonoidHom
  have hf₁ : Function.Surjective f₁ := by
    intro r
    obtain ⟨x, rfl⟩ := hφ r
    exact ⟨MonoidHom.ofInjective hg x, by simp [f₁]⟩
  obtain ⟨htop, hinj⟩ := eq_top_of_surjective_simple hR f₁ hf₁
  have hgs : Function.Surjective g := MonoidHom.range_eq_top.mp htop
  have hφi : Function.Injective φ := by
    intro x y hxy
    apply (MonoidHom.ofInjective hg).injective
    apply hinj
    simpa [f₁] using hxy
  exact ⟨⟨hg, hgs⟩, ⟨hφi, hφ⟩⟩

private lemma layerAbs_trivial {Y A C : Type} [Group Y] [Group A] [Group C] (ρ : Y →* C)
    (hC3 : ∀ c : C, c ^ 3 = 1) (π : Y →* A) (hinj : ∀ y : Y, ρ y = 1 → π y = 1 → y = 1)
    {I : Subgroup A} [I.Normal] [IsSimpleGroup I] (h3I : 3 ∣ Nat.card I)
    (hcent : ∀ a : A, (∀ i ∈ I, a * i = i * a) → a = 1)
    {L : Subgroup Y} (hL : ∀ i ∈ I, ∃ l ∈ L, π l = i) {Q : Subgroup Y}
    (hQ : Nat.Coprime 3 (Nat.card Q)) (hQL : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) : Q = ⊥ := by
  have hρ : ∀ q ∈ Q, ρ q = 1 := by
    intro q hq
    have h1 : orderOf (ρ q) ∣ 3 := orderOf_dvd_of_pow_eq_one (hC3 _)
    have h2 : orderOf (ρ q) ∣ Nat.card Q := (orderOf_map_dvd ρ q).trans (Q.orderOf_dvd_natCard hq)
    have h3 : orderOf (ρ q) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hQ) h2
    exact orderOf_eq_one_iff.mp h3
  have hconj : ∀ i ∈ I, ∀ a ∈ Q.map π, i * a * i⁻¹ ∈ Q.map π := by
    intro i hi a ha
    obtain ⟨l, hl, rfl⟩ := hL i hi
    obtain ⟨q, hq, rfl⟩ := ha
    exact ⟨l * q * l⁻¹, hQL l hl q hq, by simp⟩
  have : ((Q.map π).subgroupOf I).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj g g.2 n hn
  have hmeet : ∀ a ∈ Q.map π, a ∈ I → a = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q.map π).subgroupOf I) with h | h
    · intro a ha haI
      have : (⟨a, haI⟩ : ↥I) ∈ (Q.map π).subgroupOf I := ha
      rw [h, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    · exfalso
      have hle : I ≤ Q.map π := fun i hi => by
        have : (⟨i, hi⟩ : ↥I) ∈ (Q.map π).subgroupOf I := h ▸ Subgroup.mem_top _
        exact this
      have h4 : 3 ∣ Nat.card Q := h3I.trans ((Subgroup.card_dvd_of_le hle).trans
        (Subgroup.card_map_dvd Q π))
      exact absurd (Nat.Coprime.eq_one_of_dvd hQ h4) (by norm_num)
  have hQ1 : Q.map π = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    refine hcent a fun i hi => ?_
    have h1 : i * a * i⁻¹ * a⁻¹ ∈ Q.map π :=
      (Q.map π).mul_mem (hconj i hi a ha) ((Q.map π).inv_mem ha)
    have h2 : i * a * i⁻¹ * a⁻¹ ∈ I := by
      have h5 : a * i⁻¹ * a⁻¹ ∈ I := ‹I.Normal›.conj_mem i⁻¹ (I.inv_mem hi) a
      simpa [mul_assoc] using I.mul_mem hi h5
    have h3 : i * a * i⁻¹ * a⁻¹ = 1 := hmeet _ h1 h2
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)).symm
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  exact hinj q (hρ q hq) (by simpa [hQ1] using Subgroup.mem_map_of_mem π hq)

theorem exists_layer_abstract {Y A : Type} [Group Y] [Finite Y] [Group A]
    (e : Y ≃* Multiplicative (ZMod 3) × A) {I : Subgroup A} [I.Normal]
    (eI : ↥I ≃* PSL(3, ZMod 2)) (hindex : ¬ 3 ∣ I.index)
    (hcent : ∀ a : A, (∀ i ∈ I, a * i = i * a) → a = 1)
    {D : Subgroup Y} {R : Type} [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ∃ a b : R, a * b ≠ b * a) (h3 : 3 ∣ Nat.card R) (f : ↥D →* R)
    (hf : Function.Surjective f) :
    ∃ L : Subgroup Y, ∃ hLD : L ≤ D, Nonempty (↥L ≃* PSL(3, ZMod 2)) ∧
      Function.Bijective (f.comp (Subgroup.inclusion hLD)) ∧
      ∀ Q : Subgroup Y, Nat.Coprime 3 (Nat.card Q) →
        (∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) → Q = ⊥ := by
  classical
  let ρ : Y →* Multiplicative (ZMod 3) := (MonoidHom.fst _ _).comp e.toMonoidHom
  let π : Y →* A := (MonoidHom.snd _ _).comp e.toMonoidHom
  have hinj : ∀ y : Y, ρ y = 1 → π y = 1 → y = 1 := fun y h1 h2 =>
    e.injective (by rw [map_one]; exact Prod.ext h1 h2)
  have hC3 : ∀ c : Multiplicative (ZMod 3), c ^ 3 = 1 := by decide
  let L : Subgroup Y := D ⊓ ρ.ker ⊓ I.comap π
  have hmem : ∀ y, y ∈ L ↔ y ∈ D ∧ ρ y = 1 ∧ π y ∈ I := fun y => by
    simp [L, and_assoc]
  have hLD : L ≤ D := fun y hy => ((hmem y).1 hy).1
  obtain ⟨g, hg⟩ : ∃ g : ↥L →* PSL(3, ZMod 2), ∀ y : ↥L,
      g y = eI ⟨π y, ((hmem y).1 y.2).2.2⟩ :=
    ⟨eI.toMonoidHom.comp ((π.comp L.subtype).codRestrict I fun y => ((hmem y).1 y.2).2.2),
      fun _ => rfl⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    rw [hg, hg] at hxy
    have hπ : π x = π y := congrArg Subtype.val (eI.injective hxy)
    apply Subtype.ext
    have hx : ρ x = 1 := ((hmem x).1 x.2).2.1
    have hy : ρ y = 1 := ((hmem y).1 y.2).2.1
    have h := hinj ((x : Y)⁻¹ * y)
      (by rw [map_mul, map_inv, hx, hy]; exact (mul_one _).trans inv_one)
      (by rw [map_mul, map_inv, hπ]; simp)
    exact inv_mul_eq_one.mp h
  have hsurj : Function.Surjective (f.comp (Subgroup.inclusion hLD)) := by
    intro r
    obtain ⟨d, hd1, hd2, hdr⟩ := layerAbs_layer_surj ρ π hindex hR h3 f hf r
    exact ⟨⟨d, (hmem d).2 ⟨d.2, hd1, hd2⟩⟩, hdr⟩
  obtain ⟨hgbij, hφbij⟩ := layerAbs_bijective hR g hginj _ hsurj
  refine ⟨L, hLD, ⟨MulEquiv.ofBijective g hgbij⟩, hφbij, ?_⟩
  intro Q hQ hQL
  have : IsSimpleGroup PSL(3, ZMod 2) := isSimpleGroup_psl_three_two
  have : IsSimpleGroup ↥I := eI.isSimpleGroup
  have h3I : 3 ∣ Nat.card I := by
    rw [Nat.card_congr eI.toEquiv, card_psl_three_two]
    norm_num
  have hL : ∀ i ∈ I, ∃ l ∈ L, π l = i := by
    intro i hi
    obtain ⟨x, hx⟩ := hgbij.2 (eI ⟨i, hi⟩)
    rw [hg] at hx
    exact ⟨x, x.2, congrArg Subtype.val (eI.injective hx)⟩
  exact layerAbs_trivial ρ hC3 π hinj h3I hcent hL hQ hQL

end CFSG.LocalAnalysis.RankThreeTheoremC
