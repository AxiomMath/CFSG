module

public import CFSG.GH74.Uniqueness.SU.SU8Act
public import CFSG.GH74.Uniqueness.SU.SU2ONan

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup Pointwise CFSG.GH74.Uniqueness.SU.SU2 CFSG.GH74.Uniqueness.SU.SU8.Setup
open CFSG.GH74.Uniqueness.SU.SU8.Act
open scoped commutatorElement

namespace Glob

section AOA

variable {V : Type} [Group V]

theorem exists_ne_one_of_ne_bot' {G : Type*} [Group G] {H : Subgroup G} (h : H ≠ ⊥) :
    ∃ w ∈ H, w ≠ 1 := by
  by_contra hcon
  exact h ((Subgroup.eq_bot_iff_forall _).2 fun w hw => by_contra fun h' => hcon ⟨w, hw, h'⟩)

theorem exists_mem_ne_of_three_le [Finite V] {W : Subgroup V} (h3 : 3 ≤ Nat.card W) (a b : V) :
    ∃ u ∈ W, u ≠ a ∧ u ≠ b := by
  by_contra hcon
  have hsub : (W : Set V) ⊆ {a, b} := by
    intro u hu
    by_contra hu'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu'
    exact hcon ⟨u, hu, hu'.1, hu'.2⟩
  have h1 : (W : Set V).ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      ((Set.ncard_insert_le a {b}).trans (by simp))
  have h2 : Nat.card W = (W : Set V).ncard := Nat.card_coe_set_eq (W : Set V)
  omega

theorem smul_subgroup_eq_of_forall {X : Type} [Group X] [MulDistribMulAction X V] (F : Subgroup V)
    (x₁ x₂ : X) (h : ∀ s ∈ F, (x₂⁻¹ * x₁) • s ∈ F) (h' : ∀ s ∈ F, (x₁⁻¹ * x₂) • s ∈ F) :
    x₁ • F = x₂ • F := by
  ext w
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(x₂⁻¹ * x₁) • s, h s hs, ?_⟩
    rw [smul_smul, mul_inv_cancel_left]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(x₁⁻¹ * x₂) • s, h' s hs, ?_⟩
    rw [smul_smul, mul_inv_cancel_left]

theorem transitive_of_seven_dvd {X V : Type} [Group X] [Finite X] [Group V] [Finite V]
    [MulDistribMulAction X V] (hV : Nat.card V = 8) (h7 : 7 ∣ Nat.card X)
    (hfaith : ∀ x : X, (∀ v : V, x • v = v) → x = 1) :
    ∀ u v : V, u ≠ 1 → v ≠ 1 → ∃ x : X, x • u = v := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 7 h7
  set U : Subgroup X := Subgroup.zpowers g with hU
  have hUcard : Nat.card U = 7 := by rw [hU, Nat.card_zpowers, hg]
  have hUp : IsPGroup 7 U := by
    refine IsPGroup.of_card (n := 1) ?_
    simpa using hUcard
  have hmod := hUp.card_modEq_card_fixedPoints (α := V)
  rw [hV] at hmod
  have h1mem : (1 : V) ∈ MulAction.fixedPoints U V := fun y => smul_one (y : X)
  have hFle : Nat.card (MulAction.fixedPoints U V) ≤ 8 := by
    rw [← hV]; exact Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
  have hFpos : 1 ≤ Nat.card (MulAction.fixedPoints U V) := by
    have : Nonempty (MulAction.fixedPoints U V) := ⟨⟨1, h1mem⟩⟩
    exact Nat.card_pos
  have hF : Nat.card (MulAction.fixedPoints U V) = 1 := by
    have h8 : Nat.card (MulAction.fixedPoints U V) % 7 = 1 := by
      have := hmod.symm
      unfold Nat.ModEq at this
      omega
    by_contra hne
    have h8' : Nat.card (MulAction.fixedPoints U V) = 8 := by omega
    have hall : ∀ v : V, v ∈ MulAction.fixedPoints U V := by
      intro v
      have hsub : (MulAction.fixedPoints U V) = Set.univ := by
        apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
        rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hV, h8']
      rw [hsub]; trivial
    have : g = 1 := hfaith g (fun v => hall v ⟨g, Subgroup.mem_zpowers g⟩)
    rw [this, orderOf_one] at hg
    omega
  have hnofix : ∀ u : V, u ≠ 1 → u ∉ MulAction.fixedPoints U V := by
    intro u hu hfix
    have h2 : ({1, u} : Set V) ⊆ MulAction.fixedPoints U V := by
      intro w hw
      rcases hw with rfl | rfl
      · exact h1mem
      · exact hfix
    have h3 : ({1, u} : Set V).ncard ≤ (MulAction.fixedPoints U V).ncard :=
      Set.ncard_le_ncard h2 (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm hu), ← Nat.card_coe_set_eq, hF] at h3
    omega
  intro u v hu hv
  have hmemF := hnofix u hu
  have hidx : (MulAction.stabilizer U u).index = (MulAction.orbit U u).ncard :=
    MulAction.index_stabilizer U u
  have hmul : (MulAction.stabilizer U u).index * Nat.card (MulAction.stabilizer U u) = 7 := by
    rw [← hUcard]; exact Subgroup.index_mul_card _
  have hidx7 : (MulAction.orbit U u).ncard = 7 := by
    have hd : (MulAction.orbit U u).ncard ∣ 7 := ⟨_, hidx ▸ hmul.symm⟩
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
    · exfalso
      apply hmemF
      intro y
      have hsub : ({u} : Set V) ⊆ MulAction.orbit U u := by
        intro w hw
        rw [Set.mem_singleton_iff.mp hw]
        exact MulAction.mem_orbit_self u
      have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h, Set.ncard_singleton])
        (Set.toFinite _)
      have hyu : y • u ∈ MulAction.orbit U u := ⟨y, rfl⟩
      rw [← heq] at hyu
      exact Set.mem_singleton_iff.mp hyu
    · exact h
  have hsub2 : MulAction.orbit U u ⊆ {w : V | w ≠ 1} := by
    rintro _ ⟨y, rfl⟩ h
    apply hu
    have : (y : X)⁻¹ • ((y : X) • u) = (y : X)⁻¹ • (1 : V) := by
      show (y : X)⁻¹ • ((y : X) • u) = _
      rw [show (y : X) • u = 1 from h]
    simpa using this
  have hcard2 : ({w : V | w ≠ 1} : Set V).ncard = 7 := by
    have : ({w : V | w ≠ 1} : Set V) = Set.univ \ {1} := by
      ext w; simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ, hV]
  have heq2 := Set.eq_of_subset_of_ncard_le hsub2 (by rw [hcard2, hidx7]) (Set.toFinite _)
  have hvmem : v ∈ MulAction.orbit U u := by rw [heq2]; exact hv
  obtain ⟨y, hy⟩ := hvmem
  exact ⟨(y : X), hy⟩

theorem goPair_of_data [Finite V] (X C : Subgroup (MulAut V)) (hCX : C ≤ X) (XL : Subgroup ↥X)
    (V₁ V₀ : Subgroup V) (hexp : ∀ v : V, v * v = 1) (hcyc : IsCyclic ↥C)
    (hodd : Odd (Nat.card C)) (hC1 : C ≠ ⊥) (hV₀ : V₀ ≠ ⊥) (hV₁ : 3 ≤ Nat.card V₁)
    (hsplit : ∀ v : V, ∃ u ∈ V₁, ∃ w ∈ V₀, v = u * w)
    (hfixV₀ : ∀ c ∈ C, ∀ v ∈ V₀, c v = v) (hinvV₁ : ∀ c ∈ C, ∀ u ∈ V₁, c u ∈ V₁)
    (htrans : ∀ u ∈ V₁, u ≠ 1 → ∀ v ∈ V₁, v ≠ 1 → ∃ c ∈ C, c u = v)
    (hfree : ∀ c ∈ C, c ≠ 1 → ∀ u ∈ V₁, u ≠ 1 → c u = u → False)
    (hTI : ∀ x : ↥X, ∀ v ∈ V₀, v ≠ 1 → (x : MulAut V) v ∈ V₀ → x ∈ XL)
    (hXL : ∀ x ∈ XL, ∀ v ∈ V₀, (x : MulAut V) v ∈ V₀)
    (hCXL : ∀ x ∈ XL, ∀ y ∈ C.subgroupOf X, x * y * x⁻¹ ∈ C.subgroupOf X) :
    GOPair V (C.subgroupOf X) ∧ fixSub V (C.subgroupOf X) = V₀ ∧
      commSub V (C.subgroupOf X) = V₁ := by
  have hsmul : ∀ (y : ↥X) (v : V), y • v = (y : MulAut V) v := fun y v => rfl
  obtain ⟨c₀, hc₀, hc₀1⟩ := exists_ne_one_of_ne_bot' hC1
  have hfix : fixSub V (C.subgroupOf X) = V₀ := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, w, hw, rfl⟩ := hsplit v
      have hu1 : u = 1 := by
        by_contra hu1
        refine hfree c₀ hc₀ hc₀1 u hu hu1 ?_
        have h1 := hv ⟨c₀, hCX hc₀⟩ hc₀
        rw [hsmul] at h1
        simp only [map_mul] at h1
        have h2 := hfixV₀ c₀ hc₀ w hw
        rw [h2] at h1
        exact mul_right_cancel h1
      rw [hu1, one_mul]; exact hw
    · intro hv y hy
      rw [hsmul]
      exact hfixV₀ (y : MulAut V) hy v hv
  have hcomm : commSub V (C.subgroupOf X) = V₁ := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨y, hy, v, rfl⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := hsplit v
      rw [hsmul]
      simp only [map_mul]
      rw [hfixV₀ (y : MulAut V) hy w hw]
      have := V₁.mul_mem (hinvV₁ _ hy u hu) (V₁.inv_mem hu)
      simpa [mul_assoc] using this
    · have hgen : ∀ x ∈ V₁, x ≠ 1 → ∀ u₀ ∈ V₁, u₀ ≠ 1 →
          x * u₀ ∈ commSub V (C.subgroupOf X) := by
        intro x hx hx1 u₀ hu₀ hu₀1
        obtain ⟨c, hc, hcu⟩ := htrans u₀ hu₀ hu₀1 x hx hx1
        have hgen : (c u₀) * u₀⁻¹ ∈ commSub V (C.subgroupOf X) :=
          Subgroup.subset_closure ⟨⟨c, hCX hc⟩, hc, u₀, by rw [hsmul]⟩
        have hu₀inv : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right (hexp u₀)
        rw [hcu, hu₀inv] at hgen
        exact hgen
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact Subgroup.one_mem _
      · obtain ⟨u₀, hu₀, hu₀1, hu₀x⟩ := exists_mem_ne_of_three_le hV₁ 1 x
        have hxu₀ : x * u₀ ∈ V₁ := V₁.mul_mem hx hu₀
        have hxu₀1 : x * u₀ ≠ 1 := by
          intro h1; apply hu₀x
          have := mul_eq_one_iff_eq_inv.mp h1
          rw [inv_eq_of_mul_eq_one_right (hexp u₀)] at this
          exact this.symm
        have h2 := hgen (x * u₀) hxu₀ hxu₀1 u₀ hu₀ hu₀1
        have : x * u₀ * u₀ = x := by rw [mul_assoc, hexp u₀, mul_one]
        rw [this] at h2
        exact h2
  refine ⟨⟨hexp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hfix, hcomm⟩
  · intro x hx
    have : (x : MulAut V) = 1 := MulEquiv.ext fun v => by simpa [hsmul] using hx v
    exact Subtype.ext this
  · have := hcyc
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hCX).symm.toMonoidHom
      (MulEquiv.surjective _)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv]; exact hodd
  · intro h
    apply hc₀1
    have : (⟨c₀, hCX hc₀⟩ : ↥X) ∈ C.subgroupOf X := hc₀
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · rw [hcomm]
    intro v hv hv1 w hw hw1
    obtain ⟨c, hc, hcv⟩ := htrans v hv hv1 w hw hw1
    exact ⟨⟨c, hCX hc⟩, hc, by rw [hsmul]; exact hcv⟩
  · rw [hfix]; exact hV₀
  · intro x₁ x₂ hne
    by_contra hinf
    apply hne
    obtain ⟨v, hv, hv1⟩ := exists_ne_one_of_ne_bot' hinf
    obtain ⟨hv₁, hv₂⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨s₁, hs₁, hs₁v⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hv₁
    obtain ⟨s₂, hs₂, hs₂v⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hv₂
    rw [hfix] at hs₁ hs₂
    have hs₁1 : s₁ ≠ 1 := by
      rintro rfl
      apply hv1; rw [← hs₁v, smul_one]
    have hs₂eq : (x₂⁻¹ * x₁) • s₁ = s₂ := by
      rw [mul_smul, hs₁v, ← hs₂v, inv_smul_smul]
    have hmem : x₂⁻¹ * x₁ ∈ XL := hTI _ s₁ hs₁ hs₁1 (by rw [← hsmul, hs₂eq]; exact hs₂)
    rw [hfix]
    have h1 : ∀ s ∈ V₀, (x₂⁻¹ * x₁) • s ∈ V₀ := fun s hs => by
      rw [hsmul]; exact hXL _ hmem s hs
    have h2 : ∀ s ∈ V₀, (x₁⁻¹ * x₂) • s ∈ V₀ := fun s hs => by
      have : x₁⁻¹ * x₂ = (x₂⁻¹ * x₁)⁻¹ := by group
      rw [this, hsmul]; exact hXL _ (XL.inv_mem hmem) s hs
    exact smul_subgroup_eq_of_forall V₀ x₁ x₂ h1 h2
  · intro x hx y hy
    rw [hfix] at hx
    obtain ⟨v, hv, hv1⟩ := exists_ne_one_of_ne_bot' hV₀
    have h6 : x • v ∈ x • V₀ := Subgroup.smul_mem_pointwise_smul _ _ _ hv
    have h7 : x • v ∈ V₀ := by rw [← hx]; exact h6
    exact hCXL x (hTI x v hv hv1 (by rw [← hsmul]; exact h7)) y hy

end AOA

end Glob

namespace Act

variable {G : Type} [Group G] [Finite G] {A L AC : Subgroup G} {n : ℕ}

theorem ActData.mem_AC_iff (h : ActData A L AC n) {a : G} :
    a ∈ AC ↔ a ∈ A ∧ ∀ g ∈ L ⊓ normalizer (A : Set G), g * a * g⁻¹ = a := by
  constructor
  · intro ha
    exact ⟨h.ac_le ha, fun g hg => h.act_C g hg a ha⟩
  · rintro ⟨haA, hg⟩
    obtain ⟨u, hu, c, hc, rfl⟩ := h.split a haA
    have hu1 : u = 1 := by
      by_contra hu1
      have hfix : ∀ g ∈ L ⊓ normalizer (A : Set G), g * u * g⁻¹ = u := by
        intro g hgm
        have h1 := hg g hgm
        have h2 := h.act_C g hgm c hc
        calc g * u * g⁻¹ = (g * (u * c) * g⁻¹) * (g * c * g⁻¹)⁻¹ := by group
          _ = (u * c) * c⁻¹ := by rw [h1, h2]
          _ = u := by group
      have h4 : 3 ≤ Nat.card ↥(A ⊓ L) := by
        rw [h.card_AL]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
      obtain ⟨v, hv, hv1, hvu⟩ := Glob.exists_mem_ne_of_three_le h4 1 u
      obtain ⟨g, hgm, hgv⟩ := h.trans u hu hu1 v hv hv1
      have := hfix g hgm
      exact hvu (hgv.symm.trans this)
    rw [hu1, one_mul]
    exact hc

omit [Finite G] in
theorem ActData.image_cyclic (h : ActData A L AC n) :
    IsCyclic ↥((L.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom) ∧
    Odd (Nat.card ↥((L.subgroupOf (normalizer (A : Set G))).map A.normalizerMonoidHom)) := by
  obtain ⟨g₀, hg₀, hcyc, k, hk, hkA⟩ := h.cyclic
  set ρ := A.normalizerMonoidHom with hρ
  have hρapp : ∀ (m : ↥(normalizer (A : Set G))) (a : ↥A),
      (((ρ m) a : ↥A) : G) = (m : G) * a * (m : G)⁻¹ := fun m a => rfl
  let n₀ : ↥(normalizer (A : Set G)) := ⟨g₀, hg₀.2⟩
  have hC : (L.subgroupOf (normalizer (A : Set G))).map ρ = Subgroup.zpowers (ρ n₀) := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨j, hj⟩ := hcyc (m : G) ⟨Subgroup.mem_subgroupOf.mp hm, m.2⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
      ext a
      rw [← map_zpow, hρapp, hρapp]
      simpa using (hj a a.2).symm
    · rw [Subgroup.zpowers_le]
      exact ⟨n₀, Subgroup.mem_subgroupOf.mpr hg₀.1, rfl⟩
  rw [hC]
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_zpowers]
  have hx : (ρ n₀) ^ k = 1 := by
    rw [← map_pow]
    ext a
    rw [hρapp]
    simpa using hkA a a.2
  exact Odd.of_dvd_nat hk (orderOf_dvd_of_pow_eq_one hx)

end Act

namespace Glob

section Core

variable {G : Type} [Group G] [Finite G] {A L AC : Subgroup G} {n : ℕ}

theorem lemma203_core {z : G}
    (hact : ActData A L AC n) (hAexp : ∀ a ∈ A, a * a = 1) (hz : z ∈ AC) (hz1 : z ≠ 1)
    (hTI : ∀ g : G, ∀ v ∈ AC, v ≠ 1 → g * v * g⁻¹ ∈ AC → g ∈ normalizer (L : Set G))
    (hirr : ∀ B : Subgroup G, B ≤ A → B ≠ ⊥ → normalizer (A : Set G) ≤ normalizer (B : Set G) →
      B = A)
    (hno : ∀ H₀ : Subgroup G, H₀ ≤ normalizer (A : Set G) →
      (H₀.subgroupOf (normalizer (A : Set G))).index ≠ 2) :
    Nat.card ↥A = 8 ∧ Nat.card ↥AC = 2 ∧ n = 2 ∧
      (∀ u ∈ A, u ≠ 1 → ∀ v ∈ A, v ≠ 1 → ∃ g ∈ normalizer (A : Set G), g * u * g⁻¹ = v) ∧
      ∃ _ : ((centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))).Normal,
        Nat.card (↥(normalizer (A : Set G)) ⧸
          (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))) = 21 ∧
        ∃ a b : ↥(normalizer (A : Set G)) ⧸
          (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)), a * b ≠ b * a := by
  set Nn : Subgroup G := normalizer (A : Set G) with hNn
  set ρ : ↥Nn →* MulAut ↥A := A.normalizerMonoidHom with hρ
  have hρapp : ∀ (m : ↥Nn) (a : ↥A), (((ρ m) a : ↥A) : G) = (m : G) * a * (m : G)⁻¹ :=
    fun m a => rfl
  set X : Subgroup (MulAut ↥A) := ρ.range with hX
  set C : Subgroup (MulAut ↥A) := (L.subgroupOf Nn).map ρ with hC
  have hCX : C ≤ X := Subgroup.map_le_range _ _
  set NL' : Subgroup ↥Nn := (normalizer (L : Set G)).subgroupOf Nn with hNL'
  set XL : Subgroup ↥X := (NL'.map ρ).subgroupOf X with hXL
  set V₁ : Subgroup ↥A := (A ⊓ L).subgroupOf A with hV₁
  set V₀ : Subgroup ↥A := AC.subgroupOf A with hV₀
  obtain ⟨hcyc, hodd⟩ := hact.image_cyclic
  have h4 : 4 ≤ 2 ^ n := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hact.two_le
  have hV₁card : Nat.card V₁ = 2 ^ n := by
    rw [hV₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ L ≤ A)).toEquiv]
    exact hact.card_AL
  have hmemC : ∀ c ∈ C, ∃ m : ↥Nn, (m : G) ∈ L ∧ ρ m = c := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
  have hC1 : C ≠ ⊥ := by
    intro hbot
    obtain ⟨u, hu, hu1, -⟩ := exists_mem_ne_of_three_le (W := A ⊓ L)
      (by rw [hact.card_AL]; omega) 1 1
    obtain ⟨v, hv, hv1, hvu⟩ := exists_mem_ne_of_three_le (W := A ⊓ L)
      (by rw [hact.card_AL]; omega) 1 u
    obtain ⟨g, hg, hgu⟩ := hact.trans u hu hu1 v hv hv1
    have hgC : ρ ⟨g, hg.2⟩ ∈ C := ⟨⟨g, hg.2⟩, Subgroup.mem_subgroupOf.mpr hg.1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hgC
    have h2 := congrArg (fun φ : MulAut ↥A => ((φ ⟨u, hu.1⟩ : ↥A) : G)) hgC
    simp only [hρapp] at h2
    exact hvu (hgu.symm.trans h2)
  have hV₀ne : V₀ ≠ ⊥ := by
    intro h
    have : (⟨z, hact.ac_le hz⟩ : ↥A) ∈ V₀ := hz
    rw [h, Subgroup.mem_bot] at this
    exact hz1 (congrArg Subtype.val this)
  have hsplit : ∀ v : ↥A, ∃ u ∈ V₁, ∃ w ∈ V₀, v = u * w := by
    intro v
    obtain ⟨u, hu, c, hc, hvc⟩ := hact.split v v.2
    exact ⟨⟨u, hu.1⟩, hu, ⟨c, hact.ac_le hc⟩, hc, Subtype.ext hvc⟩
  have hfixV₀ : ∀ c ∈ C, ∀ v ∈ V₀, c v = v := by
    intro c hc v hv
    obtain ⟨m, hmL, rfl⟩ := hmemC c hc
    apply Subtype.ext
    rw [hρapp]
    exact hact.act_C (m : G) ⟨hmL, m.2⟩ (v : G) hv
  have hinvV₁ : ∀ c ∈ C, ∀ u ∈ V₁, c u ∈ V₁ := by
    intro c hc u hu
    obtain ⟨m, hmL, rfl⟩ := hmemC c hc
    have hu' : (u : G) ∈ A ⊓ L := hu
    have h1 : (m : G) * u * (m : G)⁻¹ ∈ A := by
      have := (ρ m u).2
      rwa [hρapp] at this
    have h2 : (m : G) * u * (m : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem hmL hu'.2) (L.inv_mem hmL)
    show ((ρ m u : ↥A) : G) ∈ A ⊓ L
    rw [hρapp]
    exact ⟨h1, h2⟩
  have htrans : ∀ u ∈ V₁, u ≠ 1 → ∀ v ∈ V₁, v ≠ 1 → ∃ c ∈ C, c u = v := by
    intro u hu hu1 v hv hv1
    obtain ⟨g, hg, hgu⟩ := hact.trans (u : G) hu (fun h => hu1 (Subtype.ext h)) (v : G) hv
      (fun h => hv1 (Subtype.ext h))
    exact ⟨ρ ⟨g, hg.2⟩, ⟨⟨g, hg.2⟩, Subgroup.mem_subgroupOf.mpr hg.1, rfl⟩,
      Subtype.ext (by rw [hρapp]; exact hgu)⟩
  have hfree : ∀ c ∈ C, c ≠ 1 → ∀ u ∈ V₁, u ≠ 1 → c u = u → False := by
    intro c hc hc1 u hu hu1 hcu
    obtain ⟨m, hmL, rfl⟩ := hmemC c hc
    have h1 : (m : G) * u * (m : G)⁻¹ = u := by
      have := congrArg Subtype.val hcu
      rwa [hρapp] at this
    have h2 := hact.free (m : G) ⟨hmL, m.2⟩ (u : G) hu (fun h => hu1 (Subtype.ext h)) h1
    apply hc1
    ext a
    rw [hρapp]
    simpa using h2 a a.2
  have hTI' : ∀ x : ↥X, ∀ v ∈ V₀, v ≠ 1 → (x : MulAut ↥A) v ∈ V₀ → x ∈ XL := by
    intro x v hv hv1 hxv
    obtain ⟨m, hm⟩ := x.2
    have h1 : (m : G) * v * (m : G)⁻¹ ∈ AC := by
      have : (((x : MulAut ↥A) v : ↥A) : G) ∈ AC := hxv
      rwa [← hm, hρapp] at this
    have hmL : (m : G) ∈ normalizer (L : Set G) :=
      hTI (m : G) v hv (fun h => hv1 (Subtype.ext h)) h1
    exact ⟨m, Subgroup.mem_subgroupOf.mpr hmL, hm⟩
  have hXL' : ∀ x ∈ XL, ∀ v ∈ V₀, (x : MulAut ↥A) v ∈ V₀ := by
    intro x hx v hv
    obtain ⟨m, hmNL, hm⟩ := Subgroup.mem_subgroupOf.mp hx
    have hmN : (m : G) ∈ normalizer (L : Set G) := Subgroup.mem_subgroupOf.mp hmNL
    rw [← hm]
    show ((ρ m v : ↥A) : G) ∈ AC
    rw [hρapp, hact.mem_AC_iff]
    refine ⟨?_, fun g hg => ?_⟩
    · have := (ρ m v).2
      rwa [hρapp] at this
    · have hv'' : ∀ g ∈ L ⊓ normalizer (A : Set G), g * (v : G) * g⁻¹ = (v : G) :=
        (hact.mem_AC_iff.mp hv).2
      have hgL : (m : G)⁻¹ * g * (m : G) ∈ L := by
        have h2 : (m : G) * ((m : G)⁻¹ * g * (m : G)) * (m : G)⁻¹ = g := by group
        exact (Subgroup.mem_normalizer_iff.mp hmN _).mpr (by rw [h2]; exact hg.1)
      have hgN : (m : G)⁻¹ * g * (m : G) ∈ Nn :=
        Nn.mul_mem (Nn.mul_mem (Nn.inv_mem m.2) hg.2) m.2
      calc g * ((m : G) * v * (m : G)⁻¹) * g⁻¹
          = (m : G) * (((m : G)⁻¹ * g * (m : G)) * v * ((m : G)⁻¹ * g * (m : G))⁻¹) *
              (m : G)⁻¹ := by group
        _ = (m : G) * v * (m : G)⁻¹ := by rw [hv'' _ ⟨hgL, hgN⟩]
  have hCXL' : ∀ x ∈ XL, ∀ y ∈ C.subgroupOf X, x * y * x⁻¹ ∈ C.subgroupOf X := by
    intro x hx y hy
    obtain ⟨m, hmNL, hm⟩ := Subgroup.mem_subgroupOf.mp hx
    have hmN : (m : G) ∈ normalizer (L : Set G) := Subgroup.mem_subgroupOf.mp hmNL
    have hy' : (y : MulAut ↥A) ∈ C := hy
    obtain ⟨m', hm'L, hm'⟩ := hmemC _ hy'
    show ((x * y * x⁻¹ : ↥X) : MulAut ↥A) ∈ C
    have : ((x * y * x⁻¹ : ↥X) : MulAut ↥A) = ρ (m * m' * m⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hm, hm']
    rw [this]
    refine ⟨m * m' * m⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp hmN (m' : G)).mp hm'L
    simpa using h2
  have hirr' : ∀ W : Subgroup ↥A, (∀ x : ↥X, x • W = W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hW1 : W = ⊥
    · exact Or.inl hW1
    · right
      set B : Subgroup G := W.map A.subtype with hB
      have hBA : B ≤ A := Subgroup.map_subtype_le W
      have hB1 : B ≠ ⊥ := by
        intro hbot
        apply hW1
        rw [eq_bot_iff]
        intro w hw
        have : (w : G) ∈ B := ⟨w, hw, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact (Subgroup.mem_bot).mpr (Subtype.ext this)
      have hNB : Nn ≤ normalizer (B : Set G) := by
        intro n hn
        refine mem_normalizer_of_conj_le (fun b hb => ?_)
        obtain ⟨w, hw, rfl⟩ := hb
        let x : ↥X := ⟨ρ ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩⟩
        have h6 : x • w ∈ x • W := Subgroup.smul_mem_pointwise_smul _ _ _ hw
        rw [hW x] at h6
        refine ⟨x • w, h6, ?_⟩
        show (((ρ ⟨n, hn⟩) w : ↥A) : G) = n * (w : G) * n⁻¹
        exact hρapp ⟨n, hn⟩ w
      have hBeq := hirr B hBA hB1 hNB
      rw [eq_top_iff]
      intro a _
      have : (a : G) ∈ B := by rw [hBeq]; exact a.2
      obtain ⟨w, hw, hwa⟩ := this
      have : w = a := Subtype.ext hwa
      rwa [← this]
  have hno' : ∀ N₀ : Subgroup ↥X, N₀.Normal → N₀.index ≠ 2 := by
    intro N₀ _ hidx
    have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
    set K₀ : Subgroup ↥Nn := N₀.comap ρ.rangeRestrict with hK₀
    have hK₀idx : K₀.index = 2 := by
      rw [hK₀, Subgroup.index_comap_of_surjective _ hsurj]; exact hidx
    apply hno (K₀.map Nn.subtype) (Subgroup.map_subtype_le K₀)
    have h1 : (K₀.map Nn.subtype).subgroupOf Nn = K₀ :=
      Subgroup.comap_map_eq_self_of_injective Nn.subtype_injective K₀
    rw [h1]; exact hK₀idx
  have hAexp' : ∀ v : ↥A, v * v = 1 := fun v => Subtype.ext (hAexp v v.2)
  obtain ⟨hGO, hfixeq, hcommeq⟩ :=
    goPair_of_data X C hCX XL V₁ V₀ hAexp' hcyc hodd hC1 hV₀ne (by rw [hV₁card]; omega) hsplit
      hfixV₀ hinvV₁ htrans hfree hTI' hXL' hCXL'
  obtain ⟨h1, h2, h3, h4⟩ := hGO.onan_irreducible hirr' hno'
  have hV₀card : Nat.card V₀ = 2 := by rw [← hfixeq]; exact h2
  have hAC2 : Nat.card ↥AC = 2 := by
    have := hV₀card
    rw [hV₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hact.ac_le).toEquiv] at this
    exact this
  have hn2 : n = 2 := by
    have hm := hGO.card_mul
    rw [hcommeq, hfixeq, hV₁card, hV₀card, h1] at hm
    have h4' : 2 ^ n = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) h4'
  have hfaith : ∀ x : ↥X, (∀ v : ↥A, x • v = v) → x = 1 := hGO.faithful
  have htransA : ∀ u v : ↥A, u ≠ 1 → v ≠ 1 → ∃ x : ↥X, x • u = v :=
    transitive_of_seven_dvd h1 (by rw [h3]; norm_num) hfaith
  have htransG : ∀ u ∈ A, u ≠ 1 → ∀ v ∈ A, v ≠ 1 →
      ∃ g ∈ normalizer (A : Set G), g * u * g⁻¹ = v := by
    intro u hu hu1 v hv hv1
    obtain ⟨x, hx⟩ := htransA ⟨u, hu⟩ ⟨v, hv⟩ (fun h => hu1 (congrArg Subtype.val h))
      (fun h => hv1 (congrArg Subtype.val h))
    obtain ⟨m, hm⟩ := x.2
    refine ⟨(m : G), m.2, ?_⟩
    have h5 : (((x : MulAut ↥A) ⟨u, hu⟩ : ↥A) : G) = v := congrArg Subtype.val hx
    rw [← hm, hρapp] at h5
    exact h5
  have hker : ρ.ker = (centralizer (A : Set G)).subgroupOf Nn :=
    Subgroup.normalizerMonoidHom_ker A
  have hN : ((centralizer (A : Set G)).subgroupOf Nn).Normal := hker ▸ ρ.normal_ker
  let e : (↥Nn ⧸ (centralizer (A : Set G)).subgroupOf Nn) ≃* ↥X :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ρ)
  have hcard : Nat.card (↥Nn ⧸ (centralizer (A : Set G)).subgroupOf Nn) = Nat.card ↥X :=
    Nat.card_congr e.toEquiv
  refine ⟨h1, hAC2, hn2, htransG, hN, by rw [hcard, h3], ?_⟩
  obtain ⟨a, b, hab⟩ := h4
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

end Core

end Glob

end CFSG.GH74.Uniqueness.SU.SU8
