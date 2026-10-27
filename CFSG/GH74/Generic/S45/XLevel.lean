module

public import CFSG.GH74.Generic.S45.AutE8
public import CFSG.GH74.Generic.S45.AutCard
public import CFSG.GH74.Generic.S45.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.ABGLocalTools Subgroup

section Central

variable {X : Type} [Group X] {z : X}

theorem comm_of_mem_zpowers (hzc : ∀ g : X, g * z = z * g) {y : X} (hy : y ∈ zpowers z) (g : X) :
    g * y = y * g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  exact (Commute.zpow_right (show Commute g z from hzc g) k).eq

theorem normal_zpowers (hzc : ∀ g : X, g * z = z * g) : (zpowers z).Normal :=
  ⟨fun n hn g => by
    rw [comm_of_mem_zpowers hzc hn g, mul_inv_cancel_right]
    exact hn⟩

theorem eq_one_or_eq_of_mem_zpowers (hzz : z * z = 1) {y : X} (hy : y ∈ zpowers z) :
    y = 1 ∨ y = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
  have hk : 2 * (k / 2) + k % 2 = k := Int.mul_ediv_add_emod k 2
  have h1 : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [← hk]
    rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h1, h, zpow_zero]
  · right; rw [h1, h, zpow_one]

end Central

section SK

variable {X : Type} [Group X] {K : Subgroup X} [K.Normal] {z : X} {R : Subgroup X}

omit [K.Normal] in
theorem sup_inf_eq (hRK : R ≤ K) (hzc : ∀ g : X, g * z = z * g) (hzz : z * z = 1) (hzK : z ∉ K) :
    (R ⊔ zpowers z) ⊓ K = R := by
  have : (zpowers z).Normal := normal_zpowers hzc
  apply le_antisymm
  · rintro a ⟨ha, haK⟩
    obtain ⟨r, hr, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
    have hyK : y ∈ K := by
      have : y = r⁻¹ * (r * y) := by group
      rw [this]
      exact mul_mem (inv_mem (hRK hr)) haK
    have hy1 : y = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers hzz hy with h | h
      · exact h
      · exact absurd (h ▸ hyK) hzK
    rw [hy1, mul_one]
    exact hr
  · exact le_inf le_sup_left hRK

theorem normalizer_sup_eq (hRK : R ≤ K) (hzc : ∀ g : X, g * z = z * g) (hzz : z * z = 1)
    (hzK : z ∉ K) :
    normalizer ((R ⊔ zpowers z : Subgroup X) : Set X) = normalizer (R : Set X) := by
  have : (zpowers z).Normal := normal_zpowers hzc
  have hSK := sup_inf_eq hRK hzc hzz hzK
  have key : ∀ m : X, (∀ h, h ∈ R ↔ m * h * m⁻¹ ∈ R) → ∀ h ∈ R ⊔ zpowers z,
      m * h * m⁻¹ ∈ R ⊔ zpowers z := by
    intro m hm h hh
    obtain ⟨r, hr, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hh
    have hy' : y * m⁻¹ = m⁻¹ * y := (comm_of_mem_zpowers hzc hy m⁻¹).symm
    have : m * (r * y) * m⁻¹ = (m * r * m⁻¹) * y := by
      calc m * (r * y) * m⁻¹ = m * r * (y * m⁻¹) := by group
        _ = m * r * (m⁻¹ * y) := by rw [hy']
        _ = (m * r * m⁻¹) * y := by group
    rw [this]
    exact mul_mem_sup ((hm r).1 hr) hy
  ext n
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn g
    constructor
    · intro hg
      have h1 : n * g * n⁻¹ ∈ R ⊔ zpowers z := (hn g).1 (mem_sup_left hg)
      have h2 : n * g * n⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance g (hRK hg) n
      rw [← hSK]
      exact ⟨h1, h2⟩
    · intro hg
      have h1 : g ∈ R ⊔ zpowers z := (hn g).2 (mem_sup_left hg)
      have h2 : g ∈ K := by
        have := Subgroup.Normal.conj_mem inferInstance (n * g * n⁻¹) (hRK hg) n⁻¹
        have e : n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g := by group
        rwa [e] at this
      rw [← hSK]
      exact ⟨h1, h2⟩
  · intro hn g
    constructor
    · exact key n hn g
    · intro hg
      have hn' : ∀ h, h ∈ R ↔ n⁻¹ * h * n⁻¹⁻¹ ∈ R := by
        intro h
        rw [inv_inv]
        have h1 := hn (n⁻¹ * h * n)
        have h2 : n * (n⁻¹ * h * n) * n⁻¹ = h := by group
        rw [h2] at h1
        exact h1.symm
      have := key n⁻¹ hn' (n * g * n⁻¹) hg
      have e : n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g := by group
      rwa [e] at this

theorem centralizer_sup_eq (hzc : ∀ g : X, g * z = z * g) :
    centralizer ((R ⊔ zpowers z : Subgroup X) : Set X) = centralizer (R : Set X) := by
  have : (zpowers z).Normal := normal_zpowers hzc
  apply le_antisymm
  · exact Subgroup.centralizer_le (by exact_mod_cast (le_sup_left : R ≤ R ⊔ zpowers z))
  · intro n hn
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro h hh
    obtain ⟨r, hr, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hh
    calc r * y * n = r * (y * n) := by group
      _ = r * (n * y) := by rw [← comm_of_mem_zpowers hzc hy n]
      _ = (r * n) * y := by group
      _ = (n * r) * y := by rw [hn r hr]
      _ = n * (r * y) := by group

end SK

section Transport

variable {X : Type} [Group X] {K : Subgroup X} {R : Subgroup X}

theorem card_subgroupOf_eq (H K : Subgroup X) : Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.subgroupOf_map_subtype H K, Subgroup.card_map_of_injective K.subtype_injective]

theorem comap_subtype_eq {Q : Subgroup ↥K} (hQR : Q.map K.subtype = R) : R.subgroupOf K = Q := by
  rw [← hQR]
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q

theorem card_normalizer_inf {Q : Subgroup ↥K} (hQR : Q.map K.subtype = R) (hRK : R ≤ K) :
    Nat.card ↥(normalizer (Q : Set ↥K)) = Nat.card ↥(normalizer (R : Set X) ⊓ K) := by
  have h1 := Subgroup.subgroupOf_normalizer_eq hRK
  rw [comap_subtype_eq hQR] at h1
  rw [← h1, card_subgroupOf_eq]

theorem card_centralizer_inf {Q : Subgroup ↥K} (hQR : Q.map K.subtype = R) :
    Nat.card ↥(centralizer (Q : Set ↥K)) = Nat.card ↥(centralizer (R : Set X) ⊓ K) := by
  have h1 : centralizer (Q : Set ↥K) = (centralizer (R : Set X)).subgroupOf K := by
    ext k
    simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h g hg
      rw [← hQR] at hg
      obtain ⟨q, hq, rfl⟩ := hg
      exact congrArg Subtype.val (h q hq)
    · intro h q hq
      exact Subtype.ext (h q (by rw [← hQR]; exact ⟨q, hq, rfl⟩))
  rw [h1, card_subgroupOf_eq]

end Transport

section Main

variable {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal] {R : Subgroup X}

theorem card_aut_eq_21 (hR8 : Nat.card ↥R = 8) (hRsq : ∀ x : ↥R, x * x = 1)
    (hNK : Nat.card ↥(normalizer (R : Set X) ⊓ K) =
      21 * Nat.card ↥(centralizer (R : Set X) ⊓ K)) :
    Nat.card ↥R.normalizerMonoidHom.range = 21 ∧
    ∃ a ∈ R.normalizerMonoidHom.range, orderOf a = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set N₀ : Subgroup X := normalizer (R : Set X) ⊓ K with hN₀
  have hN₀le : N₀ ≤ normalizer (R : Set X) := inf_le_left
  let ρ := R.normalizerMonoidHom
  let ρ₀ : ↥N₀ →* MulAut ↥R := ρ.comp (Subgroup.inclusion hN₀le)
  have hker : ρ₀.ker = (centralizer (R : Set X)).subgroupOf N₀ := by
    ext n
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ρ₀ n = 1 ↔ (Subgroup.inclusion hN₀le n) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]; rfl
    rw [h1, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  have hCK : Nat.card ↥(centralizer (R : Set X) ⊓ N₀) = Nat.card ↥(centralizer (R : Set X) ⊓ K) := by
    have : centralizer (R : Set X) ⊓ N₀ = centralizer (R : Set X) ⊓ K := by
      rw [hN₀, ← inf_assoc, inf_eq_left.2 (Subgroup.centralizer_le_normalizer _)]
    rw [this]
  have hB : Nat.card ↥ρ₀.range = 21 := by
    have h1 := card_range_mul_card_ker ρ₀
    rw [hker, card_subgroupOf_eq, hCK, hNK] at h1
    have hpos : 0 < Nat.card ↥(centralizer (R : Set X) ⊓ K) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hBA : ρ₀.range ≤ ρ.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨Subgroup.inclusion hN₀le n, rfl⟩
  have hnormB : ∀ f ∈ ρ.range, ∀ b ∈ ρ₀.range, f * b * f⁻¹ ∈ ρ₀.range := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    have hm' : (n : X) * (m : X) * (n : X)⁻¹ ∈ N₀ := by
      refine ⟨?_, ?_⟩
      · exact (normalizer (R : Set X)).mul_mem
          ((normalizer (R : Set X)).mul_mem n.2 (hN₀le m.2))
          ((normalizer (R : Set X)).inv_mem n.2)
      · exact Subgroup.Normal.conj_mem inferInstance (m : X) m.2.2 n
    refine ⟨⟨(n : X) * (m : X) * (n : X)⁻¹, hm'⟩, ?_⟩
    simp only [ρ₀, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥ρ₀.range) 7 (by rw [hB]; norm_num)
  have hb7 : orderOf (b : MulAut ↥R) = 7 := by rw [Subgroup.orderOf_coe]; exact hb
  have hbA : (b : MulAut ↥R) ∈ ρ.range := hBA b.2
  have hnorm : ∀ f ∈ ρ.range, f * (b : MulAut ↥R) * f⁻¹ ∈ zpowers (b : MulAut ↥R) := fun f hf =>
    mem_zpowers_of_subgroup_card_21 hB b.2 (hnormB f hf b b.2) hb7 (by rw [orderOf_conj_eq, hb7])
  have hle : Nat.card ↥ρ.range ≤ 21 := card_le_21 hR8 hRsq hb7 hbA hnorm
  have hge : 21 ≤ Nat.card ↥ρ.range := hB ▸ Subgroup.card_le_of_le hBA
  exact ⟨le_antisymm hle hge, b, hbA, hb7⟩

theorem KBase.xlevel (hK : KBase ↥K) {z : X} (hzc : ∀ g : X, g * z = z * g) (hzz : z * z = 1)
    (hzK : z ∉ K) {R : Subgroup X} (hR : IsSylowOf 2 R K) :
    (∀ r ∈ R, r ≠ 1 → ∀ s ∈ R, s ≠ 1 →
      ∃ n ∈ normalizer ((R ⊔ zpowers z : Subgroup X) : Set X), n * r * n⁻¹ = s) ∧
    Nat.card ↥(normalizer ((R ⊔ zpowers z : Subgroup X) : Set X)) =
      21 * Nat.card ↥(centralizer ((R ⊔ zpowers z : Subgroup X) : Set X)) := by
  obtain ⟨Q, hQR⟩ := hR
  obtain ⟨-, hRsq, hRcard, hNC⟩ := hK.2.2 Q
  have hRK : R ≤ K := hQR ▸ Subgroup.map_subtype_le _
  have hR8 : Nat.card ↥R = 8 := by
    rw [← hQR, Subgroup.card_map_of_injective K.subtype_injective]
    exact hRcard
  have hRsq' : ∀ x : ↥R, x * x = 1 := by
    rintro ⟨x, hx⟩
    rw [← hQR] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact Subtype.ext (congrArg (fun u : ↥(Q : Subgroup ↥K) => ((u : ↥K) : X)) (hRsq ⟨q, hq⟩))
  have hNK : Nat.card ↥(normalizer (R : Set X) ⊓ K) =
      21 * Nat.card ↥(centralizer (R : Set X) ⊓ K) := by
    rw [← card_normalizer_inf hQR hRK, ← card_centralizer_inf hQR]
    exact hNC
  obtain ⟨hA21, a, haA, ha7⟩ := card_aut_eq_21 hR8 hRsq' hNK
  rw [normalizer_sup_eq hRK hzc hzz hzK, centralizer_sup_eq hzc]
  refine ⟨?_, ?_⟩
  · intro r hr hr1 s hs hs1
    obtain ⟨n₀, rfl⟩ := haA
    obtain ⟨g, hg, hgrs⟩ := exists_zpowers_apply_eq hR8 ha7 (r := ⟨r, hr⟩) (s := ⟨s, hs⟩)
      (fun h => hr1 (congrArg Subtype.val h)) (fun h => hs1 (congrArg Subtype.val h))
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨((n₀ ^ k : ↥(normalizer (R : Set X))) : X), (n₀ ^ k).2, ?_⟩
    rw [← map_zpow R.normalizerMonoidHom n₀ k] at hgrs
    exact congrArg Subtype.val hgrs
  · have h1 := card_range_normalizerMonoidHom_mul R
    rw [hA21] at h1
    exact h1.symm

end Main

end CFSG.GH74.Generic.S45
