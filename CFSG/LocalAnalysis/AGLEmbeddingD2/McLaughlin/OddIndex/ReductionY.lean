module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.ReductionQuot
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenGroup

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {N : Type} [Group N] [Finite N]

theorem mem_pCore_of_mem_pPrimeCore {Y : Subgroup N}
    (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) (y : ↥Y) (hy : (y : N) ∈ CFSG.pPrimeCore 3 N) :
    y ∈ CFSG.pCore 2 ↥Y := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 N)) := CFSG.pPrimeCore_coprime_card
  have hsimple := isLThreeTwo_simple hY
  set mk : ↥Y →* (↥Y ⧸ CFSG.pCore 2 ↥Y) := QuotientGroup.mk' _ with hmk
  have hmks : Function.Surjective mk := QuotientGroup.mk'_surjective _
  set T : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := (CFSG.pPrimeCore 3 N |>.subgroupOf Y).map mk with hT
  have hTn : T.Normal := by
    have : (CFSG.pPrimeCore 3 N |>.subgroupOf Y).Normal := Subgroup.Normal.subgroupOf inferInstance Y
    exact Subgroup.Normal.map inferInstance mk hmks
  rcases hsimple.eq_bot_or_eq_top_of_normal T with hbot | htop
  · have : mk y ∈ T := Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff y).mp this
  · exfalso
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 3 (isLThreeTwo_three_dvd_card hY)
    have hsT : s ∈ T := by rw [htop]; exact Subgroup.mem_top s
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hsT
    have hu' : (u : N) ∈ CFSG.pPrimeCore 3 N := Subgroup.mem_subgroupOf.mp hu
    have h1 : orderOf (mk u) ∣ orderOf u := orderOf_map_dvd mk u
    have h2 : orderOf u ∣ Nat.card (CFSG.pPrimeCore 3 N) := by
      have := orderOf_dvd_natCard (⟨(u : N), hu'⟩ : CFSG.pPrimeCore 3 N)
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe u] at this
    have : 3 ∣ Nat.card (CFSG.pPrimeCore 3 N) := by
      have h12 := h1.trans h2
      rwa [hs] at h12
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop this) (by norm_num)

theorem not_two_power_of_orderOf_three {G : Type*} [Group G] {g : G} (hg : orderOf g = 3)
    (k : ℕ) : g ^ 2 ^ k ≠ 1 := by
  intro h
  have : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  rw [hg] at this
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

theorem exists_psi {X Y A : Subgroup N} [X.Normal] (hA : Nat.card A = 3) (hAX : A ≤ X)
    (hAY : A ≤ Y) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    ∃ ψ : ↥(X ⊓ Y) →* (↥Y ⧸ CFSG.pCore 2 ↥Y),
      Function.Surjective ψ ∧ (∀ z ∈ ψ.ker, ∃ k : ℕ, z ^ 2 ^ k = 1) ∧
        (∀ z : ↥(X ⊓ Y), (z : N) ∈ CFSG.pPrimeCore 3 N → ψ z = 1) := by
  classical
  have hsimple := isLThreeTwo_simple hY
  set mk : ↥Y →* (↥Y ⧸ CFSG.pCore 2 ↥Y) := QuotientGroup.mk' _ with hmk
  have hmks : Function.Surjective mk := QuotientGroup.mk'_surjective _
  set ψ : ↥(X ⊓ Y) →* (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    mk.comp (Subgroup.inclusion (inf_le_right : X ⊓ Y ≤ Y)) with hψ
  have hψapp : ∀ z : ↥(X ⊓ Y), ψ z = mk ⟨(z : N), z.2.2⟩ := fun z => rfl
  have hker : ∀ z : ↥(X ⊓ Y), ψ z = 1 ↔ (⟨(z : N), z.2.2⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
    intro z
    rw [hψapp]
    exact QuotientGroup.eq_one_iff _
  have hrn : ψ.range.Normal := by
    refine ⟨fun t ht q => ?_⟩
    obtain ⟨z, rfl⟩ := ht
    obtain ⟨y, rfl⟩ := hmks q
    refine ⟨⟨(y : N) * z * (y : N)⁻¹, ?_, ?_⟩, ?_⟩
    · exact Subgroup.Normal.conj_mem inferInstance (z : N) z.2.1 (y : N)
    · exact Y.mul_mem (Y.mul_mem y.2 z.2.2) (Y.inv_mem y.2)
    · rw [hψapp]
      rfl
  have hrange : ψ.range = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.range with hb | ht
    · exfalso
      obtain ⟨a, haA, -, hao⟩ := exists_ne_one_of_card_three hA
      have : ψ ⟨a, hAX haA, hAY haA⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hb, Subgroup.mem_bot, hker] at this
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨_, this⟩
      refine not_two_power_of_orderOf_three (g := a) hao k ?_
      have := congrArg (fun g : ↥Y => (g : N)) (congrArg Subtype.val hk)
      simpa using this
    · exact ht
  refine ⟨ψ, MonoidHom.range_eq_top.mp hrange, ?_, ?_⟩
  · intro z hz
    have := (hker z).mp hz
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨_, this⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun g : ↥Y => (g : N)) (congrArg Subtype.val hk)
    simpa using this
  · intro z hz
    exact (hker z).mpr (mem_pCore_of_mem_pPrimeCore hY _ hz)

@[expose] def zToRed (X Y : Subgroup N) [X.Normal] : ↥(X ⊓ Y) →* Red X (CFSG.pPrimeCore 3 N) :=
  (redMk X (CFSG.pPrimeCore 3 N)).comp (Subgroup.inclusion (inf_le_left : X ⊓ Y ≤ X))

omit [Finite N] in
theorem zToRed_apply (X Y : Subgroup N) [X.Normal] (z : ↥(X ⊓ Y)) :
    zToRed X Y z = redMk X (CFSG.pPrimeCore 3 N) ⟨(z : N), z.2.1⟩ := rfl

omit [Finite N] in
theorem zToRed_eq_one_iff (X Y : Subgroup N) [X.Normal] (z : ↥(X ⊓ Y)) :
    zToRed X Y z = 1 ↔ (z : N) ∈ CFSG.pPrimeCore 3 N := by
  rw [zToRed_apply, redMk_eq_one_iff]

theorem isLThreeTwo_range {X Y A : Subgroup N} [X.Normal] (hA : Nat.card A = 3) (hAX : A ≤ X)
    (hAY : A ≤ Y) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    IsLThreeTwo (↥(zToRed X Y).range ⧸ CFSG.pCore 2 ↥(zToRed X Y).range) := by
  classical
  obtain ⟨ψ, hψs, hψk, hψI⟩ := exists_psi hA hAX hAY hY
  set f := zToRed X Y with hf
  have hf's : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hker : f.rangeRestrict.ker ≤ ψ.ker := by
    intro z hz
    have h1 : f z = 1 := by
      have := (MonoidHom.mem_ker.mp hz)
      exact congrArg Subtype.val this
    exact MonoidHom.mem_ker.mpr (hψI z ((zToRed_eq_one_iff X Y z).mp h1))
  set ψb : ↥f.range →* (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    MonoidHom.liftOfSurjective f.rangeRestrict hf's ⟨ψ, hker⟩ with hψb
  have hψb_apply : ∀ z : ↥(X ⊓ Y), ψb (f.rangeRestrict z) = ψ z := fun z =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hψbs : Function.Surjective ψb := by
    intro q
    obtain ⟨z, rfl⟩ := hψs q
    exact ⟨f.rangeRestrict z, hψb_apply z⟩
  refine isLThreeTwo_quot_pCore_of_surj hY ψb hψbs ?_
  intro y hy
  obtain ⟨z, rfl⟩ := hf's y
  have hz : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, ← hψb_apply]
    exact MonoidHom.mem_ker.mp hy
  obtain ⟨k, hk⟩ := hψk z hz
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem red_not_comm {X Y A : Subgroup N} [X.Normal] (hA : Nat.card A = 3) (hAX : A ≤ X)
    (hAY : A ≤ Y) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    ∃ a b : Red X (CFSG.pPrimeCore 3 N), a * b ≠ b * a := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨ψ, hψs, hψk, hψI⟩ := exists_psi hA hAX hAY hY
  obtain ⟨a, haA, ha1, hao⟩ := exists_ne_one_of_card_three hA
  set f := zToRed X Y with hf
  set a' : ↥(X ⊓ Y) := ⟨a, hAX haA, hAY haA⟩ with ha'
  have hperf : commutator (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.AGLEmbedding.TrialityTwo.Seven.isPerfect_of_isLThreeTwo hY)
  have hcomm : (commutator ↥(X ⊓ Y)).map ψ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hψs, ← commutator_def, hperf]
  have hψa : ψ a' ∈ (commutator ↥(X ⊓ Y)).map ψ := by rw [hcomm]; exact Subgroup.mem_top _
  obtain ⟨c, hc, hψc⟩ := Subgroup.mem_map.mp hψa
  have hfc : f c = 1 := by
    have hle : commutator ↥(X ⊓ Y) ≤ f.ker := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
      rw [MonoidHom.mem_ker, commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [hcon (f g₁) (f g₂)]
      group
    exact hle hc
  have hψt : ψ (c⁻¹ * a') = 1 := by rw [map_mul, map_inv, hψc, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hψk _ hψt
  have hfa : f a' = redMk X (CFSG.pPrimeCore 3 N) ⟨a, hAX haA⟩ := rfl
  have hfa1 : f a' ≠ 1 := by
    intro h
    have hI : a ∈ CFSG.pPrimeCore 3 N := (zToRed_eq_one_iff X Y a').mp h
    have hdisj : Disjoint A (CFSG.pPrimeCore 3 N) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact Subgroup.disjoint_of_coprime_natCard
        (by rw [hA]; exact CFSG.pPrimeCore_coprime_card)
    exact ha1 (Subgroup.mem_bot.mp (hdisj.le_bot ⟨haA, hI⟩))
  have hfa3 : f a' ^ 3 = 1 := by
    rw [← map_pow]
    have : a' ^ 3 = 1 := Subtype.ext (by
      have := pow_orderOf_eq_one a
      rw [hao] at this
      simpa using this)
    rw [this, map_one]
  have hord : orderOf (f a') = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hfa3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hfa1
    · exact h
  refine not_two_power_of_orderOf_three hord k ?_
  have hfat : f a' = f (c⁻¹ * a') := by
    rw [map_mul, map_inv, hfc, inv_one, one_mul]
  rw [hfat, ← map_pow, hk, map_one]

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
