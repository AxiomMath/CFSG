module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.TightEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_18Aux

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

structure L2pAmb {G : Type} [Group G] (K : Subgroup G) : Prop where
  center_trivial : ∀ x ∈ K, (∀ y ∈ K, y * x = x * y) → x = 1
  gen_three : ∀ H : Subgroup G, (∀ g ∈ K, (∃ n : ℕ, orderOf g = 3 ^ n) → g ∈ H) → K ≤ H
  involution : ∃ i ∈ K, orderOf i = 2
  three_dvd : 3 ∣ Nat.card K
  single_class : ∀ i ∈ K, ∀ j ∈ K, orderOf i = 2 → orderOf j = 2 → ∃ k ∈ K, k * i * k⁻¹ = j
  inner_three : ∀ g ∈ Subgroup.normalizer (K : Set G), (∃ n : ℕ, orderOf g = 3 ^ n) →
    ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹
  fix_centralizes : ∀ g ∈ Subgroup.normalizer (K : Set G), (∃ n : ℕ, orderOf g = 3 ^ n) →
    ∀ i ∈ K, orderOf i = 2 → g * i * g⁻¹ = i → ∀ x ∈ K, g * x * g⁻¹ = x
  a4 : ∃ V : Subgroup G, V ≤ K ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
    3 ∣ Nat.card ↥(K ⊓ Subgroup.normalizer (V : Set G)) ∧
    ∀ x ∈ K ⊓ Subgroup.normalizer (V : Set G),
      (∀ y ∈ K ⊓ Subgroup.normalizer (V : Set G), y * x = x * y) → x ^ 3 = 1 → x = 1
  nonab : ∀ P : Subgroup G, IsSylowTwoOf P K → ∃ y ∈ P, y ^ 2 ≠ 1
  aut_two : ∀ P : Subgroup G, IsSylowTwoOf P K → ∀ g ∈ Subgroup.normalizer (K : Set G),
    (∀ y ∈ P, g * y * g⁻¹ = y) → ∀ x ∈ K, g * (g * x * g⁻¹) * g⁻¹ = x

section Abstract

variable {X : Type} [Group X]

theorem L2pData.three_dvd (h : L2pData X) : 3 ∣ Nat.card X := by
  obtain ⟨V, -, -, h3, -⟩ := h.a4
  exact h3.trans (Subgroup.card_subgroup_dvd_card _)

theorem L2pData.center_trivial (h : L2pData X) (x : X) (hx : ∀ y : X, y * x = x * y) :
    x = 1 := by
  have := h.simple
  have : (Subgroup.center X).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · have hx' : x ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun g => hx g
    rw [h1, Subgroup.mem_bot] at hx'
    exact hx'
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonabelian
    have ha : a ∈ Subgroup.center X := by rw [h1]; exact Subgroup.mem_top _
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem L2pData.gen_three [Finite X] (h : L2pData X) (H : Subgroup X)
    (hH : ∀ g : X, (∃ n : ℕ, orderOf g = 3 ^ n) → g ∈ H) : H = ⊤ := by
  have := h.simple
  let N : Subgroup X := Subgroup.closure {g : X | ∃ n : ℕ, orderOf g = 3 ^ n}
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨m, hm⟩ := hy
      refine Subgroup.subset_closure ⟨m, ?_⟩
      rw [← hm]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h.three_dvd
  have hxN : x ∈ N := Subgroup.subset_closure ⟨1, by simpa using hx⟩
  have hx1 : x ≠ 1 := by
    intro e; rw [e] at hx; simp at hx
  have hNtop : N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · exfalso; rw [h1, Subgroup.mem_bot] at hxN; exact hx1 hxN
    · exact h1
  have hle : N ≤ H := by
    show Subgroup.closure {g : X | ∃ n : ℕ, orderOf g = 3 ^ n} ≤ H
    rw [Subgroup.closure_le]
    exact fun g hg => hH g hg
  rw [eq_top_iff]
  rw [hNtop] at hle
  exact hle

theorem L2pData.exists_involution [Finite X] (h : L2pData X) : ∃ i : X, orderOf i = 2 := by
  obtain ⟨P, hP⟩ := exists_isSylowTwoOf (⊤ : Subgroup X)
  obtain ⟨y, hyP, hy2⟩ := h.nonab P hP
  have hy1 : y ≠ 1 := fun e => hy2 (by rw [e]; simp)
  obtain ⟨n, hn1, hn2⟩ := Tight.exists_involution_pow hP.2.1 hyP hy1
  exact ⟨y ^ n, orderOf_eq_prime hn2 hn1⟩

theorem L2pData.eq_one_of_fix [Finite X] (h : L2pData X) {α : MulAut X}
    (hα : ∃ n : ℕ, orderOf α = 3 ^ n) {i : X} (hi : orderOf i = 2) (hfix : α i = i) : α = 1 := by
  obtain ⟨k, hk⟩ := h.inner_three α hα
  have hkc : k ∈ Subgroup.centralizer ({i} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := hk y
    rw [hfix] at this
    calc y * k = (k * y * k⁻¹) * k := by rw [← this]
      _ = k * y := by group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp (h.cent_two i hi) ⟨k, hkc⟩
  have hkm : orderOf k = 2 ^ m := by
    rw [← hm]; exact (Subgroup.orderOf_mk k hkc).symm
  have hαk : α = MulAut.conj k := by
    ext x
    rw [hk x]; simp [MulAut.conj_apply]
  have hdvd : orderOf α ∣ 2 ^ m := by
    rw [hαk, ← hkm]
    exact orderOf_map_dvd (MulAut.conj : X →* MulAut X) k
  obtain ⟨n, hn⟩ := hα
  rw [hn] at hdvd
  have hcop : Nat.Coprime (3 ^ n) (2 ^ m) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have h1 : 3 ^ n = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [h1] at hn
  exact orderOf_eq_one_iff.mp hn

end Abstract

section Ambient

variable {G : Type} [Group G]

theorem isSylowTwoOf_subgroupOf_top {P K : Subgroup G} (hP : IsSylowTwoOf P K) :
    IsSylowTwoOf (P.subgroupOf K) ⊤ := by
  refine ⟨le_top, hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.le).symm, ?_⟩
  have h : ((P.subgroupOf K).subgroupOf (⊤ : Subgroup K)).index = (P.subgroupOf K).index :=
    Subgroup.relIndex_top_right (P.subgroupOf K)
  rw [h]
  exact hP.2.2

theorem orderOf_conjAct_dvd (K : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    orderOf (conjAct K ⟨g, hg⟩) ∣ orderOf g := by
  have := orderOf_map_dvd (conjAct K) (⟨g, hg⟩ : Subgroup.normalizer (K : Set G))
  rwa [Subgroup.orderOf_mk] at this

theorem conjAct_apply'' (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (x : ↥V) :
    ((conjAct V g x : ↥V) : G) = (g : G) * x * (g : G)⁻¹ := rfl

theorem L2pAmb.of_data [Finite G] (K : Subgroup G) (h : L2pData ↥K) : L2pAmb K := by
  have hdvd3 : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)),
      (∃ n : ℕ, orderOf g = 3 ^ n) → ∃ n : ℕ, orderOf (conjAct K ⟨g, hg⟩) = 3 ^ n := by
    intro g hg ⟨n, hn⟩
    have := orderOf_conjAct_dvd K hg
    rw [hn] at this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp this
    exact ⟨k, hk⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hxc
    have := h.center_trivial ⟨x, hx⟩ (fun y => Subtype.ext (hxc y y.2))
    exact congrArg Subtype.val this
  · intro H hH
    have := h.gen_three (H.subgroupOf K) (fun g ⟨n, hn⟩ =>
      hH g g.2 ⟨n, by rw [← hn]; exact (Subgroup.orderOf_coe g)⟩)
    intro k hk
    have hk' : (⟨k, hk⟩ : ↥K) ∈ H.subgroupOf K := by rw [this]; exact Subgroup.mem_top _
    exact hk'
  · obtain ⟨i, hi⟩ := h.exists_involution
    exact ⟨i, i.2, by rw [← hi]; exact (Subgroup.orderOf_coe i)⟩
  · exact h.three_dvd
  · intro i hi j hj hio hjo
    obtain ⟨k, hk⟩ := h.single_class ⟨i, hi⟩ ⟨j, hj⟩ (by rw [Subgroup.orderOf_mk]; exact hio)
      (by rw [Subgroup.orderOf_mk]; exact hjo)
    exact ⟨k, k.2, congrArg Subtype.val hk⟩
  · intro g hg h3
    obtain ⟨k, hk⟩ := h.inner_three (conjAct K ⟨g, hg⟩) (hdvd3 hg h3)
    refine ⟨k, k.2, fun x hx => ?_⟩
    have := congrArg Subtype.val (hk ⟨x, hx⟩)
    simpa [conjAct_apply''] using this
  · intro g hg h3 i hi hio hfix x hx
    have hα := h.eq_one_of_fix (hdvd3 hg h3) (i := ⟨i, hi⟩)
      (by rw [Subgroup.orderOf_mk]; exact hio)
      (Subtype.ext (by simpa [conjAct_apply''] using hfix))
    have := congrArg Subtype.val (DFunLike.congr_fun hα ⟨x, hx⟩)
    simpa [conjAct_apply''] using this
  · obtain ⟨V, hV1, hV2, hV3, hV4⟩ := h.a4
    have hVK : V.map K.subtype ≤ K := Subgroup.map_subtype_le V
    have hsub : (V.map K.subtype).subgroupOf K = V :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective V
    have hnorm := map_subtype_normalizer hVK
    rw [hsub] at hnorm
    refine ⟨V.map K.subtype, hVK, ?_, ?_, ?_, ?_⟩
    · intro e
      exact hV1 ((Subgroup.map_eq_bot_iff_of_injective V K.subtype_injective).mp e)
    · exact hV2.of_equiv (Subgroup.equivMapOfInjective V K.subtype K.subtype_injective)
    · rw [← hnorm, Subgroup.card_map_of_injective K.subtype_injective]
      exact hV3
    · intro x hx hxc hx3
      rw [← hnorm] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      have := hV4 x' hx' (fun y hy => by
        have hy' : K.subtype y ∈ K ⊓
            Subgroup.normalizer ((V.map K.subtype : Subgroup G) : Set G) := by
          rw [← hnorm]; exact ⟨y, hy, rfl⟩
        exact Subtype.ext (hxc _ hy')) (Subtype.ext (by simpa using hx3))
      simp [this]
  · intro P hP
    obtain ⟨y, hy, hy2⟩ := h.nonab _ (isSylowTwoOf_subgroupOf_top hP)
    refine ⟨y, hy, fun e => hy2 (Subtype.ext ?_)⟩
    simpa using e
  · intro P hP g hg hfix x hx
    have hS := isSylowTwoOf_subgroupOf_top hP
    have := h.aut_two _ hS (conjAct K ⟨g, hg⟩) (fun y hy => Subtype.ext (by
      simpa [conjAct_apply''] using hfix y hy)) ⟨x, hx⟩
    have h2 := congrArg Subtype.val this
    simpa [conjAct_apply''] using h2

end Ambient

section Pair

variable {G : Type} [Group G]

theorem commutator_eq_bot_of_commute' {H₁ H₂ : Subgroup G}
    (h : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) : ⁅H₁, H₂⁆ = ⊥ :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (h a ha b hb).symm

theorem pCoreOf_centralizer_ne_bot [Finite G] {i : G} (hi : orderOf i = 2) :
    pCoreOf 2 (Subgroup.centralizer ({i} : Set G)) ≠ ⊥ := by
  have hi1 : i ≠ 1 := fun e => by rw [e] at hi; simp at hi
  have hzp : IsPGroup 2 (Subgroup.zpowers i) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hi]; simp)
  have hle : Subgroup.zpowers i ≤ Subgroup.centralizer ({i} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]
  have hnorm : Subgroup.centralizer ({i} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers i : Set G) := fun g hg =>
    Tight.mem_normalizer_zpowers_of_commute
      ((Subgroup.mem_centralizer_iff.mp hg i (Set.mem_singleton i)).symm)
  have := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm) hzp
  intro e
  rw [e] at this
  exact hi1 (Subgroup.mem_bot.mp (this (Subgroup.mem_zpowers i)))

theorem three_elt_mem [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2) {A B : Subgroup G}
    (hA : L2pAmb A) (hB : L2pAmb B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {i : G} (hiB : i ∈ B) (hi : orderOf i = 2)
    (hcomp : IsComponentIn A (Subgroup.centralizer ({i} : Set G)))
    {g : G} (hg : g ∈ Subgroup.centralizer ({i} : Set G))
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) (h3 : ∃ n : ℕ, orderOf g = 3 ^ n) : g ∈ A := by
  have hcen : Unc25G2.CentreTwo A := fun x hx hxc => ⟨0, by simp [hA.center_trivial x hx hxc]⟩
  obtain ⟨n, hn⟩ := h3
  have hodd : Odd (orderOf g) := by rw [hn]; exact Odd.pow (by decide)
  have hgA : g ∈ Subgroup.normalizer (A : Set G) :=
    odd_mem_normalizer_component he (pCoreOf_centralizer_ne_bot hi) hcomp hcen hg hodd
  obtain ⟨a, haA, hconj⟩ := hA.inner_three g hgA ⟨n, hn⟩
  have hgi : g * i * g⁻¹ = i := by
    have := Subgroup.mem_centralizer_iff.mp hg i (Set.mem_singleton i)
    calc g * i * g⁻¹ = (g * i) * g⁻¹ := rfl
      _ = (i * g) * g⁻¹ := by rw [this]
      _ = i := by group
  have hgB' := hB.fix_centralizes g hgB ⟨n, hn⟩ i hiB hi hgi
  set c : G := a⁻¹ * g with hc
  have hcA : ∀ x ∈ A, c * x * c⁻¹ = x := fun x hx => by
    have := hconj x hx
    calc c * x * c⁻¹ = a⁻¹ * (g * x * g⁻¹) * a := by rw [hc]; group
      _ = x := by rw [this]; group
  have hcB : ∀ y ∈ B, c * y * c⁻¹ = y := fun y hy => by
    have h1 := hgB' y hy
    have h2 : a⁻¹ * y * a = y := by
      have := hAB a haA y hy
      calc a⁻¹ * y * a = a⁻¹ * (y * a) := by group
        _ = a⁻¹ * (a * y) := by rw [this]
        _ = y := by group
    calc c * y * c⁻¹ = a⁻¹ * (g * y * g⁻¹) * a := by rw [hc]; group
      _ = a⁻¹ * y * a := by rw [h1]
      _ = y := h2
  have hcommA : ∀ x ∈ A, x * c = c * x := fun x hx => by
    have := hcA x hx
    calc x * c = (c * x * c⁻¹) * c := by rw [this]
      _ = c * x := by group
  have hcommB : ∀ y ∈ B, y * c = c * y := fun y hy => by
    have := hcB y hy
    calc y * c = (c * y * c⁻¹) * c := by rw [this]
      _ = c * y := by group
  have hac : a * c = c * a := hcommA a haA
  have hg_eq : g = a * c := by rw [hc]; group
  have hcn : c ^ (3 ^ n) = 1 := by
    have hpowg : g ^ (3 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one g
    have h1 : a ^ (3 ^ n) * c ^ (3 ^ n) = 1 := by
      rw [← (show Commute a c from hac).mul_pow, ← hg_eq]; exact hpowg
    have h2 : a ^ (3 ^ n) = (c ^ (3 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a ^ (3 ^ n) = 1 := by
      apply hA.center_trivial _ (A.pow_mem haA _)
      intro y hy
      rw [h2]
      exact (((show Commute y c from hcommA y hy).pow_right (3 ^ n)).inv_right).eq
    rw [h3, one_mul] at h1
    exact h1
  have hc1 : c = 1 := by
    by_contra hne
    obtain ⟨m, hm⟩ : ∃ m, orderOf c = 3 ^ m := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hcn)
      exact ⟨k, hk⟩
    have hm1 : 1 ≤ m := by
      by_contra h0
      have : m = 0 := by omega
      subst this
      exact hne (orderOf_eq_one_iff.mp (by simpa using hm))
    obtain ⟨V, hVB, hV1, hV2, hV3, hV4⟩ := hB.a4
    have hcz : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ B, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.zpow_left (show Commute c y from (hcommB y hy).symm) k)).eq
    have hcza : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.zpow_left (show Commute c y from (hcommA y hy).symm) k)).eq
    have h12 : ⁅A, B ⊓ Subgroup.normalizer (V : Set G)⁆ = ⊥ :=
      commutator_eq_bot_of_commute' fun a ha b hb => hAB a ha b hb.1
    have h13 : ⁅A, Subgroup.zpowers c⁆ = ⊥ :=
      commutator_eq_bot_of_commute' fun a ha b hb => (hcza b hb a ha).symm
    have h23 : ⁅B ⊓ Subgroup.normalizer (V : Set G), Subgroup.zpowers c⁆ = ⊥ :=
      commutator_eq_bot_of_commute' fun a ha b hb => (hcz b hb a ha.1).symm
    obtain ⟨E, hEle, hE, hEcard⟩ := Unc25G2.exists_elemAbelian_card_cube_of_commuting
      Nat.prime_three h12 h13 h23
      (fun x hx hxc _ => hA.center_trivial x hx hxc) hV4 hA.three_dvd hV3
      (by rw [Nat.card_zpowers, hm]; exact dvd_pow_self 3 (by omega))
    have hAN : A ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (hAB a ha v (hVB hv)).symm)
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (hcz x hx v (hVB hv)).symm)
    have hEN : E ≤ Subgroup.normalizer (V : Set G) :=
      hEle.trans (sup_le (sup_le hAN inf_le_right) hcN)
    have hX : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≠ ⊥ := by
      have := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V _
        Subgroup.le_normalizer
        ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hV2
      intro e
      rw [e] at this
      exact hV1 (le_bot_iff.mp this)
    exact Unc25G2.false_of_isElemAbelian_card_cube he hX hEN Nat.prime_three (by norm_num) hE
      hEcard
  rw [hg_eq, hc1, mul_one]
  exact haA

theorem orderOf_conj_mul (h y : G) : orderOf (h * y * h⁻¹) = orderOf y := by
  simpa [MulAut.conj_apply] using
    orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective y

theorem normalizer_le_of_involution [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2)
    {A B : Subgroup G} (hA : L2pAmb A) (hB : L2pAmb B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {i : G} (hiB : i ∈ B) (hi : orderOf i = 2)
    (hcomp : IsComponentIn A (Subgroup.centralizer ({i} : Set G))) :
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  have hgiB : g * i * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg i).mp hiB
  have hgio : orderOf (g * i * g⁻¹) = 2 := by rw [orderOf_conj_mul]; exact hi
  obtain ⟨k, hkB, hk⟩ := hB.single_class i hiB (g * i * g⁻¹) hgiB hi hgio
  set h : G := k⁻¹ * g with hh
  have hhi : h * i * h⁻¹ = i := by
    calc h * i * h⁻¹ = k⁻¹ * (g * i * g⁻¹) * k := by rw [hh]; group
      _ = k⁻¹ * (k * i * k⁻¹) * k := by rw [hk]
      _ = i := by group
  have hhB : h ∈ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normalizer (B : Set G)).mul_mem
      ((Subgroup.normalizer (B : Set G)).inv_mem (Subgroup.le_normalizer hkB)) hg
  have hAN : ∀ y ∈ A, y ∈ Subgroup.normalizer (B : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hAB y hy b hb).symm)
  have hAle : A ≤ CFSG.conjugate A h := by
    apply hA.gen_three
    intro y hyA h3
    rw [BenderBranch.mem_conjugate_iff]
    refine three_elt_mem he hA hB hAB hiB hi hcomp (g := h * y * h⁻¹) ?_ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have hyi : i * y = y * i := (hAB y hyA i hiB).symm
      calc i * (h * y * h⁻¹) = (h * i * h⁻¹) * (h * y * h⁻¹) := by rw [hhi]
        _ = h * (i * y) * h⁻¹ := by group
        _ = h * (y * i) * h⁻¹ := by rw [hyi]
        _ = (h * y * h⁻¹) * (h * i * h⁻¹) := by group
        _ = (h * y * h⁻¹) * i := by rw [hhi]
    · exact (Subgroup.normalizer (B : Set G)).mul_mem
        ((Subgroup.normalizer (B : Set G)).mul_mem hhB (hAN y hyA))
        ((Subgroup.normalizer (B : Set G)).inv_mem hhB)
    · obtain ⟨n, hn⟩ := h3
      exact ⟨n, by rw [orderOf_conj_mul]; exact hn⟩
  have hcard : A = CFSG.conjugate A h :=
    Subgroup.eq_of_le_of_card_ge hAle (BenderBranch.card_conjugate A _).le
  have hhA : h ∈ Subgroup.normalizer (A : Set G) :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mp hcard.symm
  have hkA : k ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hAB a ha k hkB)
  have hgkh : g = k * h := by rw [hh]; group
  rw [hgkh]
  exact (Subgroup.normalizer (A : Set G)).mul_mem hkA hhA

theorem normalizer_eq_of_pair [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2) {A B : Subgroup G}
    (hA : L2pAmb A) (hB : L2pAmb B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hcompAB : ∀ i ∈ B, orderOf i = 2 → IsComponentIn A (Subgroup.centralizer ({i} : Set G)))
    (hcompBA : ∀ j ∈ A, orderOf j = 2 → IsComponentIn B (Subgroup.centralizer ({j} : Set G))) :
    Subgroup.normalizer (A : Set G) = Subgroup.normalizer (B : Set G) := by
  obtain ⟨i, hiB, hi⟩ := hB.involution
  obtain ⟨j, hjA, hj⟩ := hA.involution
  apply le_antisymm
  · exact normalizer_le_of_involution he hB hA (fun b hb a ha => (hAB a ha b hb).symm) hjA hj
      (hcompBA j hjA hj)
  · exact normalizer_le_of_involution he hA hB hAB hiB hi (hcompAB i hiB hi)

theorem three_elt_centralizer [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2) {A B : Subgroup G}
    (hA : L2pAmb A) (hB : L2pAmb B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (heq : Subgroup.normalizer (A : Set G) = Subgroup.normalizer (B : Set G))
    {i : G} (hiB : i ∈ B) (hi : orderOf i = 2)
    (hcomp : IsComponentIn A (Subgroup.centralizer ({i} : Set G)))
    {g : G} (hg : g ∈ Subgroup.centralizer ({i} : Set G)) (h3 : ∃ n : ℕ, orderOf g = 3 ^ n) :
    g ∈ A := by
  have hcen : Unc25G2.CentreTwo A := fun x hx hxc => ⟨0, by simp [hA.center_trivial x hx hxc]⟩
  obtain ⟨n, hn⟩ := h3
  have hodd : Odd (orderOf g) := by rw [hn]; exact Odd.pow (by decide)
  have hgA : g ∈ Subgroup.normalizer (A : Set G) :=
    odd_mem_normalizer_component he (pCoreOf_centralizer_ne_bot hi) hcomp hcen hg hodd
  exact three_elt_mem he hA hB hAB hiB hi hcomp hg (by rw [← heq]; exact hgA) ⟨n, hn⟩

theorem mem_normalizer_of_conj [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2) {A B : Subgroup G}
    (hA : L2pAmb A) (hB : L2pAmb B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (heq : Subgroup.normalizer (A : Set G) = Subgroup.normalizer (B : Set G))
    (hcompAB : ∀ i ∈ B, orderOf i = 2 → IsComponentIn A (Subgroup.centralizer ({i} : Set G)))
    {g i : G} (hiB : i ∈ B) (hi : orderOf i = 2) (hgi : g * i * g⁻¹ ∈ B) :
    g ∈ Subgroup.normalizer (B : Set G) := by
  have hj : orderOf (g * i * g⁻¹) = 2 := by rw [orderOf_conj_mul]; exact hi
  have hAle : A ≤ CFSG.conjugate A g := by
    apply hA.gen_three
    intro y hyA h3
    rw [BenderBranch.mem_conjugate_iff]
    refine three_elt_centralizer he hA hB hAB heq hgi hj (hcompAB _ hgi hj) ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have hyi : i * y = y * i := (hAB y hyA i hiB).symm
      calc (g * i * g⁻¹) * (g * y * g⁻¹) = g * (i * y) * g⁻¹ := by group
        _ = g * (y * i) * g⁻¹ := by rw [hyi]
        _ = (g * y * g⁻¹) * (g * i * g⁻¹) := by group
    · obtain ⟨n, hn⟩ := h3
      exact ⟨n, by rw [orderOf_conj_mul]; exact hn⟩
  have hcard : A = CFSG.conjugate A g :=
    Subgroup.eq_of_le_of_card_ge hAle (BenderBranch.card_conjugate A _).le
  have hgA : g ∈ Subgroup.normalizer (A : Set G) :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mp hcard.symm
  rw [← heq]; exact hgA

theorem tightlyEmbedded_of_pair [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2) {A B : Subgroup G}
    (hA : L2pAmb A) (hB : L2pAmb B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (heq : Subgroup.normalizer (A : Set G) = Subgroup.normalizer (B : Set G))
    (hcompAB : ∀ i ∈ B, orderOf i = 2 → IsComponentIn A (Subgroup.centralizer ({i} : Set G))) :
    CFSG.ComponentClassification.AschbacherTightEmbedding.TightlyEmbedded B := by
  refine ⟨?_, fun g hg => ?_⟩
  · obtain ⟨i, hiB, hi⟩ := hB.involution
    exact even_iff_two_dvd.mpr (hi ▸ Subgroup.orderOf_dvd_natCard B hiB)
  · by_contra hodd
    have heven : Even (Nat.card ↥(B ⊓
        CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate B g)) :=
      Nat.not_odd_iff_even.mp hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    have hxB : (x : G) ∈ B := x.2.1
    have hxg : g * (x : G) * g⁻¹ ∈ B := by
      have : (x : G) ∈ CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate B g :=
        x.2.2
      rw [CFSG.ComponentClassification.AschbacherTightEmbedding.mem_rightConjugate_iff] at this
      exact this
    exact hg (mem_normalizer_of_conj he hA hB hAB heq hcompAB hxB
      (by rw [← hx]; exact Subgroup.orderOf_coe x) hxg)

theorem isComponentIn_of_conj_into_sylow [Finite G] {A B S : Subgroup G}
    (hQ : IsSylowTwoOf (S ⊓ B) B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hS : ∀ j ∈ S ⊓ B, orderOf j = 2 → IsComponentIn A (Subgroup.centralizer ({j} : Set G)))
    {i : G} (hiB : i ∈ B) (hi : orderOf i = 2) :
    IsComponentIn A (Subgroup.centralizer ({i} : Set G)) := by
  have hzp : IsPGroup 2 (Subgroup.zpowers i) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hi]; simp)
  obtain ⟨Q', hQ'le, hQ'⟩ := exists_isSylowTwoOf_of_le (Subgroup.zpowers_le.mpr hiB) hzp
  obtain ⟨h, hhB, hQ'eq⟩ := hQ.exists_conj hQ'
  have hiQ' : i ∈ Q' := hQ'le (Subgroup.mem_zpowers i)
  rw [hQ'eq] at hiQ'
  obtain ⟨j, hj, hji⟩ := hiQ'
  have hji' : h * j * h⁻¹ = i := by simpa [MulAut.conj_apply] using hji
  have hjo : orderOf j = 2 := by
    rw [← hi, ← hji', orderOf_conj_mul]
  have hcomp := BenderBranch.isComponentIn_map (MulAut.conj h) (hS j hj hjo)
  have hA : A.map (MulAut.conj h).toMonoidHom = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 := hAB y hy h hhB
      have e : h * y * h⁻¹ = y := by
        calc h * y * h⁻¹ = (y * h) * h⁻¹ := by rw [h1]
          _ = y := by group
      show h * y * h⁻¹ ∈ A
      rw [e]; exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      have h1 := hAB x hx h hhB
      show h * x * h⁻¹ = x
      calc h * x * h⁻¹ = (x * h) * h⁻¹ := by rw [h1]
        _ = x := by group
  have hC : (Subgroup.centralizer ({j} : Set G)).map (MulAut.conj h).toMonoidHom =
      Subgroup.centralizer ({i} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hjy := Subgroup.mem_centralizer_iff.mp hy j (Set.mem_singleton j)
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff] at hz
      rw [hz, ← hji']
      show (h * j * h⁻¹) * (h * y * h⁻¹) = (h * y * h⁻¹) * (h * j * h⁻¹)
      calc (h * j * h⁻¹) * (h * y * h⁻¹) = h * (j * y) * h⁻¹ := by group
        _ = h * (y * j) * h⁻¹ := by rw [hjy]
        _ = (h * y * h⁻¹) * (h * j * h⁻¹) := by group
    · intro hx
      refine ⟨h⁻¹ * x * h, ?_, ?_⟩
      · have hx' := Subgroup.mem_centralizer_iff.mp hx i (Set.mem_singleton i)
        refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have hi_eq : i = h * j * h⁻¹ := hji'.symm
        rw [hi_eq] at hx'
        calc j * (h⁻¹ * x * h) = h⁻¹ * ((h * j * h⁻¹) * x) * h := by group
          _ = h⁻¹ * (x * (h * j * h⁻¹)) * h := by rw [hx']
          _ = (h⁻¹ * x * h) * j := by group
      · show h * (h⁻¹ * x * h) * h⁻¹ = x
        group
  rw [hA, hC] at hcomp
  exact hcomp

end Pair

end CFSG.QuasithinUnique
