module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding

variable {G X K₀ : Type*} [Group G] [Finite G] [Group X] [Finite X] [Group K₀]

theorem false_of_inner_cover {p : ℕ} [hp : Fact p.Prime] {Y : Subgroup G}
    (f : Y →* K₀) (hf : Function.Surjective f) [IsSimpleGroup K₀]
    (hnab : ∃ a b : K₀, a * b ≠ b * a) (hfk : ∀ y : Y, f y = 1 → p.Coprime (orderOf y))
    (g : Y →* X) (hgk : ∀ y : Y, g y = 1 → p.Coprime (orderOf y))
    (K C : Subgroup X) [K.Normal] [C.Normal] (hKC : K ⊓ C = ⊥)
    (hcomm : ∀ x ∈ K, ∀ y ∈ C, x * y = y * x) {k c : X} (hk : k ∈ K) (hc : c ∈ C)
    (hk1 : k ≠ 1) (hkp : k ^ p = 1) (hg : ∀ y : Y, g y ∈ K ⊔ C)
    (hgz : ∀ y : Y, g y * (k * c) = k * c * g y) {t s m : ℕ}
    (hm : ∀ S : Sylow p K₀, m ≤ Nat.card S)
    (ht : ∀ P : Subgroup X, P ≤ K → IsPGroup p P → Nat.card P ≤ t)
    (hs : ∀ P : Subgroup X, P ≤ C → IsPGroup p P → Nat.card P ≤ s)
    (h1 : t * s ≤ p * m) (h2 : p ≤ s) (h3 : p < t) : False := by
  have hp1 : 1 < p := hp.out.one_lt
  have htm : t ≤ m := by
    have h4 : t * p ≤ p * m := (Nat.mul_le_mul_left t h2).trans h1
    rw [mul_comm] at h4
    exact Nat.le_of_mul_le_mul_left h4 (by omega)
  set φ₁ := QuotientGroup.mk' C with hφ₁
  have hcommk : ∀ y : Y, φ₁ (g y) * φ₁ k = φ₁ k * φ₁ (g y) := by
    intro y
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp (hg y)
    have hb1 : φ₁ b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
    have hgy : φ₁ (g y) = φ₁ a := by rw [← hab, map_mul, hb1, mul_one]
    have hak := comm_of_mul_comm hKC hcomm ha hb hk hc (by rw [hab]; exact hgz y)
    rw [hgy, ← map_mul, hak, map_mul]
  have hinjK : ∀ x ∈ K, φ₁ x = 1 → x = 1 := by
    intro x hx h
    have hxC : x ∈ C := (QuotientGroup.eq_one_iff x).mp h
    have : x ∈ K ⊓ C := ⟨hx, hxC⟩
    rwa [hKC, Subgroup.mem_bot] at this
  set N := C.comap g with hN
  have hNn : N.Normal := Subgroup.normal_comap g
  have hNf : (N.map f).Normal := hNn.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with hbot | htop
  ·
    have hNk : ∀ y : Y, g y ∈ C → f y = 1 := fun y hy => by
      have h5 : f y ∈ N.map f := ⟨y, hy, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at h5
    obtain ⟨Q⟩ : Nonempty (Sylow p Y) := inferInstance
    have hQp : IsPGroup p (Q : Subgroup Y) := Q.isPGroup'
    have hmQ : m ≤ Nat.card (Q : Subgroup Y) := (hm (Q.mapSurjective hf)).trans (by
      rw [Sylow.coe_mapSurjective]; exact card_map_le f _)
    set ψ := φ₁.comp g with hψ
    have hψk : ∀ y, ψ y = 1 → p.Coprime (orderOf y) := fun y hy =>
      hfk y (hNk y ((QuotientGroup.eq_one_iff _).mp hy))
    set Q₁ := (Q : Subgroup Y).map ψ with hQ₁
    have hQ₁c : Nat.card Q₁ = Nat.card (Q : Subgroup Y) := card_map_of_coprime ψ hψk hQp
    have hQ₁p : IsPGroup p Q₁ := hQp.map ψ
    have hQ₁K : Q₁ ≤ K.map φ₁ := by
      rintro _ ⟨y, -, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp (hg y)
      have hb1 : φ₁ b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
      exact ⟨a, ha, by rw [hψ, MonoidHom.comp_apply, ← hab, map_mul, hb1, mul_one]⟩
    have hx1 : φ₁ k ≠ 1 := fun h => hk1 (hinjK k hk h)
    have hxp : orderOf (φ₁ k) = p := orderOf_eq_prime (by rw [← map_pow, hkp, map_one]) hx1
    have hxQ : φ₁ k ∈ Q₁ := by
      by_contra hx
      set Z₁ := Subgroup.zpowers (φ₁ k) with hZ₁
      have hZc : Nat.card Z₁ = p := by rw [Nat.card_zpowers, hxp]
      have hdisj : Q₁ ⊓ Z₁ = ⊥ := by
        have hdvd : Nat.card (Q₁ ⊓ Z₁ : Subgroup _) ∣ p :=
          hZc ▸ Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime hp.out).mp hdvd with h6 | h6
        · exact Subgroup.card_eq_one.mp h6
        · exfalso
          have h7 : Q₁ ⊓ Z₁ = Z₁ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h6, hZc])
          exact hx ((h7 ▸ inf_le_left : Z₁ ≤ Q₁) (Subgroup.mem_zpowers _))
      have hZp : IsPGroup p Z₁ := IsPGroup.of_card (n := 1) (by rw [hZc, pow_one])
      have hQZ : Q₁ ≤ Subgroup.normalizer (Z₁ : Set _) := by
        refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
        refine Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr ?_)
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨y, -, rfl⟩
        exact hcommk y
      have hPp : IsPGroup p (Q₁ ⊔ Z₁ : Subgroup _) := hQ₁p.to_sup_of_normal_right' hZp hQZ
      have hPK : Q₁ ⊔ Z₁ ≤ K.map φ₁ :=
        sup_le hQ₁K (Subgroup.zpowers_le.mpr ⟨k, hk, rfl⟩)
      have hle := mul_card_le_of_inf_eq_bot (le_sup_left : Q₁ ≤ Q₁ ⊔ Z₁) le_sup_right hdisj
      have hPt := card_le_of_le_map φ₁ hinjK ht hPK hPp
      rw [hQ₁c, hZc] at hle
      have h8 : m * p ≤ t := (Nat.mul_le_mul_right p hmQ).trans (hle.trans hPt)
      have h9 : m * p ≤ m := h8.trans htm
      have hm0 : 0 < m := lt_of_lt_of_le (by omega) htm
      nlinarith
    obtain ⟨q₀, hq₀Q, hq₀⟩ := hxQ
    have hcen : f q₀ ∈ Subgroup.center K₀ := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := hf x
      have h10 : g (q₀ * y * q₀⁻¹ * y⁻¹) ∈ C := by
        rw [← QuotientGroup.eq_one_iff]
        change φ₁ (g (q₀ * y * q₀⁻¹ * y⁻¹)) = 1
        have h11 : φ₁ (g q₀) = φ₁ k := hq₀
        simp only [map_mul, map_inv, h11]
        rw [(hcommk y).symm]
        group
      have h12 := hNk _ h10
      simp only [map_mul, map_inv] at h12
      have : f q₀ * f y = f y * f q₀ := by
        calc f q₀ * f y = f q₀ * f y * (f q₀)⁻¹ * (f y)⁻¹ * (f y * f q₀) := by group
          _ = f y * f q₀ := by rw [h12, one_mul]
      exact this.symm
    have hZ : Subgroup.center K₀ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K₀) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        have ha : a ∈ Subgroup.center K₀ := h ▸ Subgroup.mem_top a
        exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
    rw [hZ, Subgroup.mem_bot] at hcen
    have hq₁ : q₀ = 1 := eq_one_of_mem_of_coprime hQp hq₀Q (hfk q₀ hcen).symm
    rw [hq₁, map_one] at hq₀
    exact hx1 hq₀.symm
  ·
    have hfN : Function.Surjective (f.comp N.subtype) := by
      intro x
      have hx : x ∈ N.map f := htop ▸ Subgroup.mem_top x
      obtain ⟨n, hn, rfl⟩ := hx
      exact ⟨⟨n, hn⟩, rfl⟩
    obtain ⟨Q⟩ : Nonempty (Sylow p N) := inferInstance
    have hmQ : m ≤ Nat.card (Q : Subgroup N) := (hm (Q.mapSurjective hfN)).trans (by
      rw [Sylow.coe_mapSurjective]; exact card_map_le _ _)
    set Q' := (Q : Subgroup N).map N.subtype with hQ'
    have hQ'p : IsPGroup p Q' := Q.isPGroup'.map _
    have hQ'c : Nat.card Q' = Nat.card (Q : Subgroup N) :=
      Subgroup.card_map_of_injective N.subtype_injective
    have hgQ : Nat.card (Q'.map g) = Nat.card Q' := card_map_of_coprime g hgk hQ'p
    have hgC : Q'.map g ≤ C := by
      rintro _ ⟨y, ⟨n, -, rfl⟩, rfl⟩
      exact n.2
    have hms : m ≤ s := hmQ.trans (hQ'c ▸ hgQ ▸ hs _ hgC (hQ'p.map g))
    have h13 : t * s ≤ p * s := h1.trans (Nat.mul_le_mul_left p hms)
    have h14 : t ≤ p := Nat.le_of_mul_le_mul_right h13 (by omega)
    omega

end CFSG.AGLEmbedding
