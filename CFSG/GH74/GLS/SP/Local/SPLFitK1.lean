module

public import CFSG.GH74.GLS.SP.Local.SPLCtC1a

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

open CFSG.GH74.GLS.IVK in
@[expose] def SPLFitA1 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F →
  ∀ (K : Type) [Group K] [Finite K], (K ≃* SL2 F) →
  ∀ u₁ : K, u₁ ^ 2 ∈ Subgroup.center K → u₁ ^ 2 ≠ 1 →
  ∀ (M : Type) [Group M] [Finite M] (α : M →* MulAut K),
    (∀ m : M, α m u₁ * u₁⁻¹ ∈ Subgroup.center K) →
  ∀ W : Subgroup M, Odd (Nat.card ↥W) → (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) →
    (∀ k : K, Odd (orderOf k) → k * u₁ = u₁ * k →
      ∃ m : M, α m = MulAut.conj k ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) →
    ∀ w ∈ W, ∃ k : K, Odd (orderOf k) ∧ k * u₁ = u₁ * k ∧ α w = MulAut.conj k

section Aux

variable {G : Type} [Group G]

theorem fitK1_conj_pow_mem (K : Subgroup G) {g : G} (hg : ∀ a ∈ K, g * a * g⁻¹ ∈ K) (n : ℕ) :
    ∀ a ∈ K, g ^ n * a * (g ^ n)⁻¹ ∈ K := by
  induction n with
  | zero => intro a ha; simpa using ha
  | succ n ih =>
    intro a ha
    have h1 := ih _ (hg a ha)
    have h2 : g ^ (n + 1) * a * (g ^ (n + 1))⁻¹ = g ^ n * (g * a * g⁻¹) * (g ^ n)⁻¹ := by
      rw [pow_succ, mul_inv_rev]; simp only [mul_assoc]
    rwa [h2]

theorem fitK1_mem_normalizer [Finite G] {K : Subgroup G} {g : G} (hg : ∀ a ∈ K, g * a * g⁻¹ ∈ K) :
    g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hg a ha, fun h => ?_⟩
  have hpos : 0 < orderOf g := orderOf_pos g
  have hinv : g ^ (orderOf g - 1) = g⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have h2 := fitK1_conj_pow_mem K hg (orderOf g - 1) _ h
  rw [hinv, inv_inv] at h2
  have h3 : g⁻¹ * (g * a * g⁻¹) * g = a := by group
  rwa [h3] at h2

end Aux

section Defs

variable {G : Type} [Group G] (D : SPLNot1 G)

theorem fitK1_not_mem_zpowers (hs : SPLSetup D.toSPLNot0) {u₁ : G} (hu₁sq : u₁ ^ 2 = D.z)
    {c : G} (hc : c ∈ D.C) : c * u₁ * c⁻¹ ∉ zpowers D.z := by
  intro h
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h
  have hcz : c * D.z * c⁻¹ = D.z := by
    have := mem_centralizer_singleton_iff.mp hc
    calc c * D.z * c⁻¹ = D.z * c * c⁻¹ := by rw [this]
      _ = D.z := by group
  have hsq : (c * u₁ * c⁻¹) ^ 2 = D.z := by rw [conj_pow, hu₁sq, hcz]
  rcases zpow_z_cases' D hs j with h1 | h1
  · rw [h1] at hj
    rw [← hj] at hsq
    exact z_ne_one' D hs (by simpa using hsq.symm)
  · rw [h1] at hj
    rw [← hj, sq, z_mul_z' D hs] at hsq
    exact z_ne_one' D hs hsq.symm

@[expose] def fitK1N (u : G) : Subgroup G :=
  (D.C ⊓ centralizer ({u} : Set G)) ⊓ normalizer (D.K₁ : Set G)

variable {D}

theorem mem_fitK1N {u g : G} :
    g ∈ fitK1N D u ↔ (g ∈ D.C ∧ g ∈ centralizer ({u} : Set G)) ∧ g ∈ normalizer (D.K₁ : Set G) :=
  Iff.rfl

variable (D)

theorem fitK1N_le (u : G) : fitK1N D u ≤ normalizer (D.K₁ : Set G) := inf_le_right

@[expose] noncomputable def fitK1Act (u : G) : ↥(fitK1N D u) →* MulAut ↥D.K₁ :=
  D.K₁.normalizerMonoidHom.comp (Subgroup.inclusion (fitK1N_le D u))

end Defs

section Fit

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

theorem fitK1_normalizes_K₂ (hs : SPLSetup D.toSPLNot0) {u₁ : G} (hu₁ : u₁ ∈ D.K₁)
    (hu₁sq : u₁ ^ 2 = D.z) {c : G} (hc : c ∈ D.C) (hK₁ : ∀ a ∈ D.K₁, c * a * c⁻¹ ∈ D.K₁) :
    ∀ a ∈ D.K₂, c * a * c⁻¹ ∈ D.K₂ := by
  rcases hs.comps.perm' c hc with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · exfalso
    apply fitK1_not_mem_zpowers D hs hu₁sq hc
    rw [← hs.comps.inf_eq]
    exact ⟨hK₁ u₁ hu₁, h1 u₁ hu₁⟩

theorem fitK1_normalizes_of_odd (hs : SPLSetup D.toSPLNot0) {u₁ : G} (hu₁ : u₁ ∈ D.K₁)
    (hu₁sq : u₁ ^ 2 = D.z) {c : G} (hc : c ∈ D.C) (hodd : Odd (orderOf c)) :
    ∀ a ∈ D.K₁, c * a * c⁻¹ ∈ D.K₁ := by
  rcases hs.comps.perm' c hc with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    obtain ⟨m, hm⟩ := hodd
    have hsq : ∀ a ∈ D.K₁, c ^ 2 * a * (c ^ 2)⁻¹ ∈ D.K₁ := by
      intro a ha
      have h3 := h2 _ (h1 a ha)
      have e : c ^ 2 * a * (c ^ 2)⁻¹ = c * (c * a * c⁻¹) * c⁻¹ := by
        rw [sq, mul_inv_rev]; simp only [mul_assoc]
      rwa [e]
    have hpow : (c ^ 2) ^ (m + 1) = c := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have hfix : ∀ a ∈ D.K₁, c * a * c⁻¹ ∈ D.K₁ := by
      intro a ha
      have h3 := fitK1_conj_pow_mem D.K₁ hsq (m + 1) a ha
      rwa [hpow] at h3
    apply fitK1_not_mem_zpowers D hs hu₁sq hc
    rw [← hs.comps.inf_eq]
    exact ⟨hfix u₁ hu₁, h1 u₁ hu₁⟩

end Fit

theorem fit_K1_side (hA1 : SPLFitA1) {G : Type} [Group G] [Finite G] (D : SPLNot1 G)
    (hs : SPLSetup D.toSPLNot0) {u : G}
    (hdec : ∃ u₁ ∈ D.K₁, ∃ u₂ ∈ D.K₂, u = u₁ * u₂ ∧ u₁ ^ 2 = D.z ∧ u₂ ^ 2 = D.z)
    (Y : Subgroup G) (hYle : Y ≤ D.C ⊓ centralizer ({u} : Set G))
    (hYnorm : ∀ c ∈ D.C ⊓ centralizer ({u} : Set G), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    (hYodd : Odd (Nat.card ↥Y)) (hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) :
    ∀ y ∈ Y, ∃ k ∈ D.K₁, ∀ x ∈ D.K₁, y * x * y⁻¹ = k * x * k⁻¹ := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hu, hu₁sq, -⟩ := hdec
  obtain ⟨F, iF, fF, hq, ⟨e⟩⟩ := hs.comps.sl₁
  have hq' : Nat.card F = D.q := hq
  have hL2 : IVK.L2Field F := by
    refine ⟨?_, ?_⟩
    · rw [hq']; exact hs.odd_q
    · rw [hq']; have := hs.q_ge; omega
  have hcen : ∀ x : ↥D.K₁, (x : G) ∈ zpowers D.z → x ∈ center ↥D.K₁ := by
    intro x hx
    have hx' : (x : G) ∈ (center ↥D.K₁).map D.K₁.subtype := by rw [hs.comps.cen₁]; exact hx
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx'
    have hcx' : c = x := Subtype.ext hcx
    rwa [← hcx']
  let u₁' : ↥D.K₁ := ⟨u₁, hu₁⟩
  have hu₁'sq : ((u₁' ^ 2 : ↥D.K₁) : G) = D.z := hu₁sq
  have hcen_sq : u₁' ^ 2 ∈ center ↥D.K₁ :=
    hcen _ (by rw [hu₁'sq]; exact mem_zpowers D.z)
  have hne : u₁' ^ 2 ≠ 1 := by
    intro h
    apply z_ne_one' D hs
    rw [← hu₁'sq, h]
    rfl
  have hYN : Y ≤ fitK1N D u := by
    intro y hy
    have hodd : Odd (orderOf y) :=
      Odd.of_dvd_nat hYodd (Subgroup.orderOf_dvd_natCard Y hy)
    have hyC : y ∈ D.C := (hYle hy).1
    exact mem_fitK1N.mpr ⟨hYle hy,
      fitK1_mem_normalizer (fitK1_normalizes_of_odd D hs hu₁ hu₁sq hyC hodd)⟩
  have hWodd : Odd (Nat.card ↥(Y.subgroupOf (fitK1N D u))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv]
    exact hYodd
  have hWab : ∀ a ∈ Y.subgroupOf (fitK1N D u), ∀ b ∈ Y.subgroupOf (fitK1N D u), a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hYab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  have hα : ∀ m : ↥(fitK1N D u), fitK1Act D u m u₁' * u₁'⁻¹ ∈ center ↥D.K₁ := by
    intro m
    obtain ⟨⟨hmC, hmu'⟩, hmN⟩ := mem_fitK1N.mp m.2
    have hmu : (m : G) * u = u * m := mem_centralizer_singleton_iff.mp hmu'
    have hmK₁ : ∀ a ∈ D.K₁, (m : G) * a * (m : G)⁻¹ ∈ D.K₁ :=
      fun a ha => (mem_normalizer_iff.mp hmN a).mp ha
    have hmK₂ := fitK1_normalizes_K₂ D hs hu₁ hu₁sq hmC hmK₁
    apply hcen
    show (m : G) * u₁ * (m : G)⁻¹ * u₁⁻¹ ∈ zpowers D.z
    have ha : (m : G) * u₁ * (m : G)⁻¹ ∈ D.K₁ := hmK₁ u₁ hu₁
    have hb : (m : G) * u₂ * (m : G)⁻¹ ∈ D.K₂ := hmK₂ u₂ hu₂
    have hab : ((m : G) * u₁ * (m : G)⁻¹) * ((m : G) * u₂ * (m : G)⁻¹) = u₁ * u₂ := by
      have h1 : ((m : G) * u₁ * (m : G)⁻¹) * ((m : G) * u₂ * (m : G)⁻¹) =
          (m : G) * (u₁ * u₂) * (m : G)⁻¹ := by group
      rw [h1, ← hu]
      calc (m : G) * u * (m : G)⁻¹ = u * m * (m : G)⁻¹ := by rw [hmu]
        _ = u := by group
    generalize (m : G) * u₁ * (m : G)⁻¹ = a at ha hab ⊢
    generalize (m : G) * u₂ * (m : G)⁻¹ = b at hb hab
    have hv : a * u₁⁻¹ = u₂ * b⁻¹ := by
      have h1 : a = u₁ * (u₂ * b⁻¹) := by
        calc a = a * b * b⁻¹ := by group
          _ = u₁ * u₂ * b⁻¹ := by rw [hab]
          _ = u₁ * (u₂ * b⁻¹) := by group
      have h2 : u₁ * (u₂ * b⁻¹) = (u₂ * b⁻¹) * u₁ :=
        hs.comps.comm u₁ hu₁ _ (D.K₂.mul_mem hu₂ (D.K₂.inv_mem hb))
      calc a * u₁⁻¹ = u₁ * (u₂ * b⁻¹) * u₁⁻¹ := by rw [← h1]
        _ = (u₂ * b⁻¹) * u₁ * u₁⁻¹ := by rw [h2]
        _ = u₂ * b⁻¹ := by group
    rw [← hs.comps.inf_eq]
    refine ⟨D.K₁.mul_mem ha (D.K₁.inv_mem hu₁), ?_⟩
    rw [hv]
    exact D.K₂.mul_mem hu₂ (D.K₂.inv_mem hb)
  have hX : ∀ k : ↥D.K₁, Odd (orderOf k) → k * u₁' = u₁' * k →
      ∃ m : ↥(fitK1N D u), fitK1Act D u m = MulAut.conj k ∧
        ∀ w ∈ Y.subgroupOf (fitK1N D u), m * w * m⁻¹ ∈ Y.subgroupOf (fitK1N D u) := by
    intro k _ hk
    have hkC : (k : G) ∈ D.C := K₁_le_C' D hs k.2
    have hku₁ : (k : G) * u₁ = u₁ * k := congrArg Subtype.val hk
    have hku₂ : (k : G) * u₂ = u₂ * k := hs.comps.comm _ k.2 _ hu₂
    have hku : (k : G) * u = u * k := by
      rw [hu]
      calc (k : G) * (u₁ * u₂) = (k * u₁) * u₂ := by group
        _ = (u₁ * k) * u₂ := by rw [hku₁]
        _ = u₁ * (k * u₂) := by group
        _ = u₁ * (u₂ * k) := by rw [hku₂]
        _ = u₁ * u₂ * k := by group
    have hkcu : (k : G) ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr hku
    refine ⟨⟨k, mem_fitK1N.mpr ⟨⟨hkC, hkcu⟩, Subgroup.le_normalizer k.2⟩⟩, ?_, ?_⟩
    · ext x
      rfl
    · intro w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact hYnorm k ⟨hkC, hkcu⟩ w hw
  have key := hA1 F hL2 ↥D.K₁ e u₁' hcen_sq hne ↥(fitK1N D u) (fitK1Act D u) hα
    (Y.subgroupOf (fitK1N D u)) hWodd hWab hX
  intro y hy
  obtain ⟨k, -, -, hk⟩ := key ⟨y, hYN hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
  refine ⟨(k : G), k.2, fun x hx => ?_⟩
  exact congrArg Subtype.val (DFunLike.congr_fun hk ⟨x, hx⟩)

end CFSG.GH74.GLS.SP.Local
