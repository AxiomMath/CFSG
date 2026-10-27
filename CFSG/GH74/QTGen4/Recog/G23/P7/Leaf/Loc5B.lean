module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]



theorem loc5_mem_sup {S T : Subgroup G} (h : ∀ t ∈ T, ∀ s ∈ S, t * s * t⁻¹ ∈ S) {x : G} :
    x ∈ S ⊔ T ↔ ∃ s ∈ S, ∃ t ∈ T, s * t = x := by
  let Q : Subgroup G :=
    { carrier := {x | ∃ s ∈ S, ∃ t ∈ T, s * t = x}
      mul_mem' := by
        rintro _ _ ⟨s₁, hs₁, t₁, ht₁, rfl⟩ ⟨s₂, hs₂, t₂, ht₂, rfl⟩
        exact ⟨s₁ * (t₁ * s₂ * t₁⁻¹), S.mul_mem hs₁ (h t₁ ht₁ s₂ hs₂), t₁ * t₂,
          T.mul_mem ht₁ ht₂, by group⟩
      one_mem' := ⟨1, S.one_mem, 1, T.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨s, hs, t, ht, rfl⟩
        exact ⟨t⁻¹ * s⁻¹ * t⁻¹⁻¹, h t⁻¹ (T.inv_mem ht) s⁻¹ (S.inv_mem hs), t⁻¹,
          T.inv_mem ht, by group⟩ }
  have hle : S ⊔ T ≤ Q := sup_le (fun s hs => ⟨s, hs, 1, T.one_mem, mul_one s⟩)
    (fun t ht => ⟨1, S.one_mem, t, ht, one_mul t⟩)
  constructor
  · intro hx
    exact hle hx
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right ht)

theorem loc5_card_sup_le {S T : Subgroup G} [Finite G]
    (h : ∀ t ∈ T, ∀ s ∈ S, t * s * t⁻¹ ∈ S) :
    Nat.card ↥(S ⊔ T) ≤ Nat.card ↥S * Nat.card ↥T := by
  let f : ↥S × ↥T → ↥(S ⊔ T) := fun p =>
    ⟨p.1.1 * p.2.1, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨s, hs, t, ht, rfl⟩ := (loc5_mem_sup h).mp hy
    exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

theorem loc5_card_centralizer_conj (c x : G) :
    Nat.card ↥(Subgroup.centralizer ({c * x * c⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
  have key : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      c * y * c⁻¹ ∈ Subgroup.centralizer ({c * x * c⁻¹} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc c * y * c⁻¹ * (c * x * c⁻¹) = c * (y * x) * c⁻¹ := by group
      _ = c * (x * y) * c⁻¹ := by rw [hy]
      _ = c * x * c⁻¹ * (c * y * c⁻¹) := by group
  have key' : ∀ y : G, y ∈ Subgroup.centralizer ({c * x * c⁻¹} : Set G) →
      c⁻¹ * y * c⁻¹⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc c⁻¹ * y * c⁻¹⁻¹ * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [hy]
      _ = x * (c⁻¹ * y * c⁻¹⁻¹) := by group
  exact Nat.card_congr
    { toFun := fun y => ⟨c⁻¹ * y.1 * c⁻¹⁻¹, key' _ y.2⟩
      invFun := fun y => ⟨c * y.1 * c⁻¹, key _ y.2⟩
      left_inv := fun y => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group) }

theorem loc5_card_fix_modEq (τ : G) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (X : Subgroup G) [Finite G]
    (hX : τ ∈ Subgroup.normalizer (X : Set G)) :
    Nat.card ↥(X ⊓ Subgroup.centralizer ({τ} : Set G)) ≡ Nat.card ↥X [MOD 3] := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hτord : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
  have hG : IsPGroup 3 ↥(Subgroup.zpowers τ) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hτord]
    norm_num
  have hzN : Subgroup.zpowers τ ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr hX
  letI : MulAction ↥(Subgroup.zpowers τ) ↥X :=
    { smul := fun q x => ⟨(q : G) * (x : G) * (q : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hzN q.2) x).mp x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        show ((1 : ↥(Subgroup.zpowers τ)) : G) * (x : G) * ((1 : ↥(Subgroup.zpowers τ)) : G)⁻¹ = (x : G)
        simp
      mul_smul := fun q₁ q₂ x => by
        apply Subtype.ext
        show ((q₁ * q₂ : ↥(Subgroup.zpowers τ)) : G) * (x : G) * ((q₁ * q₂ : ↥(Subgroup.zpowers τ)) : G)⁻¹
          = (q₁ : G) * ((q₂ : G) * (x : G) * (q₂ : G)⁻¹) * (q₁ : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group }
  have hkey := hG.card_modEq_card_fixedPoints ↥X
  have hset : MulAction.fixedPoints ↥(Subgroup.zpowers τ) ↥X =
      {a : ↥X | (a : G) ∈ Subgroup.centralizer ({τ} : Set G)} := by
    ext a
    constructor
    · intro ha
      have h1 := ha ⟨τ, Subgroup.mem_zpowers τ⟩
      have h2 : τ * (a : G) * τ⁻¹ = a := congrArg Subtype.val h1
      rw [Set.mem_setOf_eq, Subgroup.mem_centralizer_singleton_iff]
      have h3 : τ * (a : G) = (a : G) * τ := by
        calc τ * (a : G) = (τ * (a : G) * τ⁻¹) * τ := by group
          _ = (a : G) * τ := by rw [h2]
      exact h3.symm
    · intro ha
      rw [Set.mem_setOf_eq, Subgroup.mem_centralizer_singleton_iff] at ha
      intro g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      apply Subtype.ext
      show (g : G) * (a : G) * (g : G)⁻¹ = (a : G)
      have hc : Commute τ (a : G) := ha.symm
      have hc' : Commute (τ ^ k) (a : G) := hc.zpow_left k
      rw [← hk]
      calc τ ^ k * (a : G) * (τ ^ k)⁻¹ = (a : G) * τ ^ k * (τ ^ k)⁻¹ := by rw [hc'.eq]
        _ = (a : G) := by group
  have hcard : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers τ) ↥X) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({τ} : Set G)) := by
    rw [hset]
    exact Nat.card_congr
      { toFun := fun a => ⟨a.1.1, Subgroup.mem_inf.mpr ⟨a.1.2, a.2⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩, (Subgroup.mem_inf.mp x.2).2⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
  rw [← hcard]
  exact hkey.symm

theorem loc5_conj_center {M : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (M : Set G))
    {a : G} (ha : a ∈ M ⊓ Subgroup.centralizer (M : Set G)) :
    g * a * g⁻¹ ∈ M ⊓ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.mem_inf] at ha ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg a).mp ha.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have hm' : g⁻¹ * m * g ∈ M := by
    apply (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * m * g)).mpr
    have e : g * (g⁻¹ * m * g) * g⁻¹ = m := by group
    rw [e]
    exact hm
  have hc := Subgroup.mem_centralizer_iff.mp ha.2 (g⁻¹ * m * g) hm'
  calc m * (g * a * g⁻¹) = g * ((g⁻¹ * m * g) * a) * g⁻¹ := by group
    _ = g * (a * (g⁻¹ * m * g)) * g⁻¹ := by rw [hc]
    _ = (g * a * g⁻¹) * m := by group

theorem loc5_rel_conj {x y : G} (hrel : x⁻¹ * y⁻¹ * x * y⁻¹ * x⁻¹ * y = 1) (A : Subgroup G)
    (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hyA : ∀ a ∈ A, y * a = a * y) :
    ∀ a ∈ A, x * a = a * x := by
  intro a ha
  have E1 : y⁻¹ * x * y⁻¹ = x * y⁻¹ * x := by
    calc y⁻¹ * x * y⁻¹ = x * (x⁻¹ * y⁻¹ * x * y⁻¹ * x⁻¹ * y) * y⁻¹ * x := by group
      _ = x * y⁻¹ * x := by rw [hrel]; group
  have hyinv : ∀ c ∈ A, y⁻¹ * c * y = c := by
    intro c hc
    calc y⁻¹ * c * y = y⁻¹ * (c * y) := by group
      _ = y⁻¹ * (y * c) := by rw [← hyA c hc]
      _ = c := by group
  have hb : x * a * x⁻¹ ∈ A := hxA a ha
  have hR : (y⁻¹ * x * y⁻¹) * a * (y⁻¹ * x * y⁻¹)⁻¹ = x * a * x⁻¹ := by
    calc (y⁻¹ * x * y⁻¹) * a * (y⁻¹ * x * y⁻¹)⁻¹ = y⁻¹ * (x * (y⁻¹ * a * y) * x⁻¹) * y := by
          group
      _ = y⁻¹ * (x * a * x⁻¹) * y := by rw [hyinv a ha]
      _ = x * a * x⁻¹ := hyinv _ hb
  have hL : (x * y⁻¹ * x) * a * (x * y⁻¹ * x)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by
    calc (x * y⁻¹ * x) * a * (x * y⁻¹ * x)⁻¹ = x * (y⁻¹ * (x * a * x⁻¹) * y) * x⁻¹ := by
          group
      _ = x * (x * a * x⁻¹) * x⁻¹ := by rw [hyinv _ hb]
  have hfix : x * (x * a * x⁻¹) * x⁻¹ = x * a * x⁻¹ := by
    rw [← hL, ← E1, hR]
  have h1 : x⁻¹ * (x * a * x⁻¹) * x = a := by group
  have h2 : x⁻¹ * (x * a * x⁻¹) * x = x * a * x⁻¹ := by
    calc x⁻¹ * (x * a * x⁻¹) * x = x⁻¹ * (x * (x * a * x⁻¹) * x⁻¹) * x := by rw [hfix]
      _ = x * a * x⁻¹ := by group
  have hfin : a = x * a * x⁻¹ := h1.symm.trans h2
  calc x * a = x * a * x⁻¹ * x := by group
    _ = a * x := by rw [← hfin]

theorem loc5_not_central {x y z : G} (hrel : x⁻¹ * y⁻¹ * x * y⁻¹ * x⁻¹ * y = 1)
    (hz : z = y * x * (y * x)) (A : Subgroup G) (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hyA : ∀ a ∈ A, y * a = a * y) (hexp : ∀ a ∈ A, a ^ 3 = 1)
    (hneg : ∃ a ∈ A, a ≠ 1 ∧ z * a * z⁻¹ = a⁻¹) : False := by
  obtain ⟨a, ha, ha1, hza⟩ := hneg
  have hxa := loc5_rel_conj hrel A hxA hyA a ha
  have hxa' : x * a * x⁻¹ = a := by rw [hxa]; group
  have hya' : y * a * y⁻¹ = a := by rw [hyA a ha]; group
  have hconj : y * x * a * (y * x)⁻¹ = a := by
    calc y * x * a * (y * x)⁻¹ = y * (x * a * x⁻¹) * y⁻¹ := by group
      _ = a := by rw [hxa', hya']
  have hz' : z * a * z⁻¹ = a := by
    rw [hz]
    calc y * x * (y * x) * a * (y * x * (y * x))⁻¹ = (y * x) * ((y * x) * a * (y * x)⁻¹) * (y * x)⁻¹ := by
          group
      _ = a := by rw [hconj, hconj]
  have hsq : a * a = 1 := by
    have h : a = a⁻¹ := hz'.symm.trans hza
    calc a * a = a * a⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel a
  apply ha1
  have h3 : a ^ 3 = a * (a * a) := pow_three a
  have := hexp a ha
  rw [h3, hsq, mul_one] at this
  exact this

theorem loc5_inv_part (z σ : G) (M : Subgroup G) [Finite G]
    (hexp : ∀ m ∈ M, m ^ 3 = 1)
    (hA : Nat.card ↥(M ⊓ Subgroup.centralizer (M : Set G)) = 27)
    (hzN : z ∈ Subgroup.normalizer (M : Set G))
    (hσA : σ ∈ M ⊓ Subgroup.centralizer (M : Set G)) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hzσ : z * σ = σ * z) (hz2 : z * z = 1)
    (hzinv : ∀ m ∈ M, z * m * z⁻¹ * m ∈ Subgroup.zpowers σ) :
    ∃ Am : Subgroup G, (∀ x, x ∈ Am ↔ x ∈ M ⊓ Subgroup.centralizer (M : Set G) ∧
        z * x * z⁻¹ = x⁻¹) ∧ Nat.card ↥Am = 9 ∧
      ∀ a ∈ M ⊓ Subgroup.centralizer (M : Set G), ∃ p ∈ Subgroup.zpowers σ, ∃ q ∈ Am,
        a = p * q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup G := M ⊓ Subgroup.centralizer (M : Set G) with hAdef
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  have hconjA : ∀ g ∈ Subgroup.normalizer (M : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun g hg a ha => loc5_conj_center hg ha
  have hzz : ∀ x : G, z * (z * x * z⁻¹) * z⁻¹ = x := by
    intro x
    calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ := by group
      _ = x := by rw [hz2]; group
  have hfixed : ∀ c ∈ A, z * c * z⁻¹ = c → c ∈ Subgroup.zpowers σ := by
    intro c hc hzc
    have h1 : z * c * z⁻¹ * c ∈ Subgroup.zpowers σ := hzinv c hc.1
    rw [hzc] at h1
    have h3 : c ^ 3 = 1 := hexp c hc.1
    have h4 : (c * c) * (c * c) = c := by
      calc (c * c) * (c * c) = c * c ^ 3 := by rw [pow_three]; simp only [mul_assoc]
        _ = c := by rw [h3, mul_one]
    rw [← h4]
    exact (Subgroup.zpowers σ).mul_mem h1 h1
  let ψ : ↥A →* ↥A :=
    { toFun := fun a => ⟨(a : G) * (z * (a : G) * z⁻¹), A.mul_mem a.2 (hconjA z hzN a a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hza : z * (a : G) * z⁻¹ ∈ A := hconjA z hzN a a.2
        have hcm : (b : G) * (z * (a : G) * z⁻¹) = (z * (a : G) * z⁻¹) * (b : G) :=
          hcomm _ b.2 _ hza
        show (a : G) * b * (z * ((a : G) * b) * z⁻¹) =
          (a : G) * (z * a * z⁻¹) * ((b : G) * (z * b * z⁻¹))
        calc (a : G) * b * (z * ((a : G) * b) * z⁻¹)
            = (a : G) * ((b : G) * (z * (a : G) * z⁻¹)) * (z * (b : G) * z⁻¹) := by group
          _ = (a : G) * ((z * (a : G) * z⁻¹) * (b : G)) * (z * (b : G) * z⁻¹) := by rw [hcm]
          _ = (a : G) * (z * (a : G) * z⁻¹) * ((b : G) * (z * (b : G) * z⁻¹)) := by group }
  have hψ : ∀ a : ↥A, ((ψ a : ↥A) : G) = (a : G) * (z * (a : G) * z⁻¹) := fun a => rfl
  have hzfix : ∀ a ∈ A, z * (a * (z * a * z⁻¹)) * z⁻¹ = a * (z * a * z⁻¹) := by
    intro a ha
    have hza : z * a * z⁻¹ ∈ A := hconjA z hzN a ha
    calc z * (a * (z * a * z⁻¹)) * z⁻¹ = (z * a * z⁻¹) * (z * (z * a * z⁻¹) * z⁻¹) := by group
      _ = (z * a * z⁻¹) * a := by rw [hzz]
      _ = a * (z * a * z⁻¹) := hcomm _ hza a ha
  let σA : ↥A := ⟨σ, hσA⟩
  have hσA_ord : orderOf σA = 3 := by
    rw [show σA = ⟨σ, hσA⟩ from rfl, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hσ3 hσ1
  have hzs : z * σ * z⁻¹ = σ := by rw [hzσ]; group
  have hzs2 : z * σ ^ 2 * z⁻¹ = σ ^ 2 := by
    calc z * σ ^ 2 * z⁻¹ = (z * σ * z⁻¹) * (z * σ * z⁻¹) := by rw [pow_two]; group
      _ = σ * σ := by rw [hzs]
      _ = σ ^ 2 := (pow_two σ).symm
  have hrange : ψ.range = Subgroup.zpowers σA := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      have hc : ((ψ a : ↥A) : G) ∈ Subgroup.zpowers σ := by
        apply hfixed _ (A.mul_mem a.2 (hconjA z hzN a a.2))
        exact hzfix a a.2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by
        show σ ^ k = ((ψ a : ↥A) : G)
        exact hk)⟩
    · apply Subgroup.zpowers_le.mpr
      refine ⟨σA ^ 2, Subtype.ext ?_⟩
      rw [hψ]
      show σ ^ 2 * (z * σ ^ 2 * z⁻¹) = σ
      rw [hzs2]
      calc σ ^ 2 * σ ^ 2 = σ * σ ^ 3 := by group
        _ = σ := by rw [hσ3, mul_one]
  have hcardR : Nat.card ↥ψ.range = 3 := by
    rw [hrange, Nat.card_zpowers, hσA_ord]
  have hker : Nat.card ↥ψ.ker = 9 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hcardR, hA] at h
    omega
  let Am : Subgroup G := ψ.ker.map A.subtype
  have hAm_mem : ∀ x, x ∈ Am ↔ x ∈ A ∧ z * x * z⁻¹ = x⁻¹ := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hy1 : ψ y = 1 := hy
      have h : ((ψ y : ↥A) : G) = 1 := congrArg Subtype.val hy1
      rw [hψ] at h
      have hzy : z * (y : G) * z⁻¹ = (y : G)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
      rw [← hyx]
      exact ⟨y.2, hzy⟩
    · rintro ⟨hxA, hzx⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hψ]
      show x * (z * x * z⁻¹) = 1
      rw [hzx]
      group
  have hAm_card : Nat.card ↥Am = 9 := by
    rw [show Am = ψ.ker.map A.subtype from rfl, Subgroup.card_map_of_injective
      (f := A.subtype) (fun x y h => Subtype.ext h)]
    exact hker
  refine ⟨Am, hAm_mem, hAm_card, ?_⟩
  intro a ha
  have hbA : z * a * z⁻¹ ∈ A := hconjA z hzN a ha
  have hab : a * (z * a * z⁻¹) ∈ A := A.mul_mem ha hbA
  have hab' : a * (z * a * z⁻¹)⁻¹ ∈ A := A.mul_mem ha (A.inv_mem hbA)
  have hba : (z * a * z⁻¹) * a = a * (z * a * z⁻¹) := hcomm _ hbA a ha
  have hzab : z * (a * (z * a * z⁻¹)) * z⁻¹ = a * (z * a * z⁻¹) := hzfix a ha
  have hzzA : z * (z * a * z⁻¹) * z⁻¹ = a := hzz a
  have hzab' : z * (a * (z * a * z⁻¹)⁻¹) * z⁻¹ = (a * (z * a * z⁻¹)⁻¹)⁻¹ := by
    calc z * (a * (z * a * z⁻¹)⁻¹) * z⁻¹ = (z * a * z⁻¹) * (z * (z * a * z⁻¹) * z⁻¹)⁻¹ := by
          group
      _ = (z * a * z⁻¹) * a⁻¹ := by rw [hzzA]
      _ = (a * (z * a * z⁻¹)⁻¹)⁻¹ := by group
  have huv : (a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹) = a * a := by
    calc (a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹)
        = a * ((z * a * z⁻¹) * a) * (z * a * z⁻¹)⁻¹ := by group
      _ = a * (a * (z * a * z⁻¹)) * (z * a * z⁻¹)⁻¹ := by rw [hba]
      _ = a * a := by group
  have hcomm_uv := hcomm _ hab _ hab'
  have hsplit : (a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)) *
      ((a * (z * a * z⁻¹)⁻¹) * (a * (z * a * z⁻¹)⁻¹)) =
      ((a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹)) *
        ((a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹)) := by
    calc (a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)) *
          ((a * (z * a * z⁻¹)⁻¹) * (a * (z * a * z⁻¹)⁻¹))
        = (a * (z * a * z⁻¹)) * ((a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹)) *
            (a * (z * a * z⁻¹)⁻¹) := by group
      _ = (a * (z * a * z⁻¹)) * ((a * (z * a * z⁻¹)⁻¹) * (a * (z * a * z⁻¹))) *
            (a * (z * a * z⁻¹)⁻¹) := by rw [hcomm_uv]
      _ = ((a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹)) *
            ((a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹)) := by group
  have h3 : a ^ 3 = 1 := hexp a ha.1
  have hfour : (a * a) * (a * a) = a := by
    calc (a * a) * (a * a) = a * a ^ 3 := by rw [pow_three]; simp only [mul_assoc]
      _ = a := by rw [h3, mul_one]
  have hp : (a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)) ∈ Subgroup.zpowers σ := by
    apply hfixed _ (A.mul_mem hab hab)
    calc z * ((a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹))) * z⁻¹
        = (z * (a * (z * a * z⁻¹)) * z⁻¹) * (z * (a * (z * a * z⁻¹)) * z⁻¹) := by group
      _ = (a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)) := by rw [hzab]
  have hq : (a * (z * a * z⁻¹)⁻¹) * (a * (z * a * z⁻¹)⁻¹) ∈ Am := by
    rw [hAm_mem]
    refine ⟨A.mul_mem hab' hab', ?_⟩
    calc z * ((a * (z * a * z⁻¹)⁻¹) * (a * (z * a * z⁻¹)⁻¹)) * z⁻¹
        = (z * (a * (z * a * z⁻¹)⁻¹) * z⁻¹) * (z * (a * (z * a * z⁻¹)⁻¹) * z⁻¹) := by group
      _ = (a * (z * a * z⁻¹)⁻¹)⁻¹ * (a * (z * a * z⁻¹)⁻¹)⁻¹ := by rw [hzab']
      _ = ((a * (z * a * z⁻¹)⁻¹) * (a * (z * a * z⁻¹)⁻¹))⁻¹ := by group
  refine ⟨_, hp, _, hq, ?_⟩
  calc a = (a * a) * (a * a) := hfour.symm
    _ = ((a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹)) *
          ((a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)⁻¹)) := by rw [huv]
    _ = (a * (z * a * z⁻¹)) * (a * (z * a * z⁻¹)) *
          ((a * (z * a * z⁻¹)⁻¹) * (a * (z * a * z⁻¹)⁻¹)) := hsplit.symm

theorem loc5_tau_part (z σ τ : G) (M : Subgroup G) [Finite G] (Am : Subgroup G)
    (hexp : ∀ m ∈ M, m ^ 3 = 1)
    (hA : Nat.card ↥(M ⊓ Subgroup.centralizer (M : Set G)) = 27)
    (hσA : σ ∈ M ⊓ Subgroup.centralizer (M : Set G))
    (hAm : ∀ x, x ∈ Am ↔ x ∈ M ⊓ Subgroup.centralizer (M : Set G) ∧ z * x * z⁻¹ = x⁻¹)
    (hAm9 : Nat.card ↥Am = 9)
    (hdec : ∀ a ∈ M ⊓ Subgroup.centralizer (M : Set G), ∃ p ∈ Subgroup.zpowers σ,
      ∃ q ∈ Am, a = p * q)
    (hzN : z ∈ Subgroup.normalizer (M : Set G)) (hτN : τ ∈ Subgroup.normalizer (M : Set G))
    (hτz : z * τ = τ * z) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hστ : σ * τ = τ * σ)
    (hzσ : z * σ = σ * z) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hτnot : ¬ ∀ a ∈ M ⊓ Subgroup.centralizer (M : Set G), τ * a = a * τ) :
    ∃ F : Subgroup G, (∀ x, x ∈ F ↔ (x ∈ M ⊓ Subgroup.centralizer (M : Set G) ∧
        z * x * z⁻¹ = x⁻¹ ∧ x ∈ Subgroup.centralizer ({τ} : Set G))) ∧ Nat.card ↥F = 3 ∧
      Nat.card ↥(M ⊓ Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer ({τ} : Set G)) = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup G := M ⊓ Subgroup.centralizer (M : Set G) with hAdef
  have hconjAm : ∀ g ∈ Subgroup.normalizer (M : Set G), z * g = g * z →
      ∀ x ∈ Am, g * x * g⁻¹ ∈ Am := by
    intro g hg hgz x hx
    obtain ⟨hxA, hzx⟩ := (hAm x).mp hx
    refine (hAm _).mpr ⟨loc5_conj_center hg hxA, ?_⟩
    calc z * (g * x * g⁻¹) * z⁻¹ = (z * g) * x * (z * g)⁻¹ := by group
      _ = (g * z) * x * (g * z)⁻¹ := by rw [hgz]
      _ = g * (z * x * z⁻¹) * g⁻¹ := by group
      _ = g * x⁻¹ * g⁻¹ := by rw [hzx]
      _ = (g * x * g⁻¹)⁻¹ := by group
  have hτ'z : z * τ⁻¹ = τ⁻¹ * z := by
    calc z * τ⁻¹ = τ⁻¹ * (τ * z) * τ⁻¹ := by group
      _ = τ⁻¹ * (z * τ) * τ⁻¹ := by rw [hτz]
      _ = τ⁻¹ * z := by group
  have hτAmN : τ ∈ Subgroup.normalizer (Am : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconjAm τ hτN hτz h hh
    · intro hh
      have h2 := hconjAm τ⁻¹ ((Subgroup.normalizer (M : Set G)).inv_mem hτN) hτ'z _ hh
      have e : τ⁻¹ * (τ * h * τ⁻¹) * τ⁻¹⁻¹ = h := by group
      rwa [e] at h2
  have hcong := loc5_card_fix_modEq τ hτ3 hτ1 Am hτAmN
  rw [hAm9] at hcong
  have hdiv3 : 3 ∣ Nat.card ↥(Am ⊓ Subgroup.centralizer ({τ} : Set G)) := by
    unfold Nat.ModEq at hcong
    omega
  have hdvd9 : Nat.card ↥(Am ⊓ Subgroup.centralizer ({τ} : Set G)) ∣ 9 := by
    rw [← hAm9]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hσC : σ ∈ Subgroup.centralizer ({τ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hστ
  have hF3 : Nat.card ↥(Am ⊓ Subgroup.centralizer ({τ} : Set G)) = 3 := by
    have hne9 : Nat.card ↥(Am ⊓ Subgroup.centralizer ({τ} : Set G)) ≠ 9 := by
      intro h9
      have heq : Am ⊓ Subgroup.centralizer ({τ} : Set G) = Am :=
        Subgroup.eq_of_le_of_card_ge (inf_le_left : Am ⊓ Subgroup.centralizer ({τ} : Set G) ≤ Am)
          (by rw [h9, hAm9])
      apply hτnot
      intro a ha
      obtain ⟨p, hp, q, hq, rfl⟩ := hdec a ha
      have hqC : q ∈ Subgroup.centralizer ({τ} : Set G) := by
        have hqF : q ∈ Am ⊓ Subgroup.centralizer ({τ} : Set G) := by rw [heq]; exact hq
        exact hqF.2
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      have hc : Commute τ σ := hστ.symm
      have hpC : τ * σ ^ k = σ ^ k * τ := (hc.zpow_right k).eq
      rw [Subgroup.mem_centralizer_singleton_iff] at hqC
      calc τ * (σ ^ k * q) = (τ * σ ^ k) * q := by group
        _ = (σ ^ k * τ) * q := by rw [hpC]
        _ = σ ^ k * (τ * q) := by group
        _ = σ ^ k * (q * τ) := by rw [hqC]
        _ = σ ^ k * q * τ := by group
    generalize hn : Nat.card ↥(Am ⊓ Subgroup.centralizer ({τ} : Set G)) = n at *
    have hle : n ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd9
    interval_cases n <;> first | rfl | omega | (norm_num at hdvd9)
  refine ⟨Am ⊓ Subgroup.centralizer ({τ} : Set G), ?_, hF3, ?_⟩
  · intro x
    rw [Subgroup.mem_inf, hAm x]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  have hdvd27 : Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) ∣ 27 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne27 : Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) ≠ 27 := by
    intro h27
    apply hτnot
    have heq : A ⊓ Subgroup.centralizer ({τ} : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ Subgroup.centralizer ({τ} : Set G) ≤ A)
        (by rw [h27, hA])
    intro a ha
    have haK : a ∈ A ⊓ Subgroup.centralizer ({τ} : Set G) := by rw [heq]; exact ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp haK.2).symm
  have hσK : σ ∈ A ⊓ Subgroup.centralizer ({τ} : Set G) := Subgroup.mem_inf.mpr ⟨hσA, hσC⟩
  have hne1 : Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) ≠ 1 := by
    intro h1
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    have : σ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hσK
    exact hσ1 ((Subgroup.mem_bot).mp this)
  have hne3 : Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) ≠ 3 := by
    intro h3
    have hzp : Subgroup.zpowers σ ≤ A ⊓ Subgroup.centralizer ({τ} : Set G) :=
      Subgroup.zpowers_le.mpr hσK
    have hzpc : Nat.card ↥(Subgroup.zpowers σ) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hσ3 hσ1]
    have heqK : A ⊓ Subgroup.centralizer ({τ} : Set G) = Subgroup.zpowers σ :=
      (Subgroup.eq_of_le_of_card_ge hzp (by rw [h3, hzpc])).symm
    have hnt : Nontrivial ↥(Am ⊓ Subgroup.centralizer ({τ} : Set G)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hF3]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(Am ⊓ Subgroup.centralizer ({τ} : Set G)))
    have hxF := x.2
    have hxAm := (hAm _).mp (Subgroup.mem_inf.mp hxF).1
    have hxA : (x : G) ∈ M ⊓ Subgroup.centralizer (M : Set G) := hxAm.1
    have hzx : z * (x : G) * z⁻¹ = (x : G)⁻¹ := hxAm.2
    have hxK : (x : G) ∈ A ⊓ Subgroup.centralizer ({τ} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxA, (Subgroup.mem_inf.mp hxF).2⟩
    rw [heqK] at hxK
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxK
    have hcz : Commute z σ := hzσ
    have hzk : z * (x : G) * z⁻¹ = (x : G) := by
      rw [← hk]
      calc z * σ ^ k * z⁻¹ = σ ^ k * z * z⁻¹ := by rw [(hcz.zpow_right k).eq]
        _ = σ ^ k := by group
    have hxx : (x : G) = (x : G)⁻¹ := hzk.symm.trans hzx
    have hx2 : (x : G) * (x : G) = 1 := mul_eq_one_iff_eq_inv.mpr hxx
    have hxone : (x : G) = 1 := by
      have h3' := hexp _ hxA.1
      calc (x : G) = (x : G) * ((x : G) * (x : G)) := by rw [hx2, mul_one]
        _ = (x : G) ^ 3 := (pow_three _).symm
        _ = 1 := h3'
    exact hx (Subtype.ext hxone)
  have hle : Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) ≤ 27 :=
    Nat.le_of_dvd (by norm_num) hdvd27
  generalize hn : Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) = n at *
  interval_cases n <;> first | rfl | omega | (norm_num at hdvd27)

theorem loc5_comm_of_rel {a b : G} (h : a⁻¹ * b⁻¹ * a * b = 1) : a * b = b * a := by
  have h' : b⁻¹ * a * b = a := by
    calc b⁻¹ * a * b = a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = a := by rw [h, mul_one]
  calc a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [h']

theorem loc5_normalizer_of {M C : Subgroup G} {g : G} (hgC : g ∈ C)
    (hC : ∀ c ∈ C, ∀ n ∈ M, c * n * c⁻¹ ∈ M) : g ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    exact hC g hgC m hm
  · intro hm
    have h := hC g⁻¹ (C.inv_mem hgC) _ hm
    have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
    rwa [e] at h

theorem loc5_conj_commute {g y s : G} (hg : g * s = s * g) (hy : y * s = s * y) :
    (g * y * g⁻¹) * s = s * (g * y * g⁻¹) := by
  have hg' : g⁻¹ * s = s * g⁻¹ := by
    calc g⁻¹ * s = g⁻¹ * (s * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * s) * g⁻¹ := by rw [hg]
      _ = s * g⁻¹ := by group
  calc g * y * g⁻¹ * s = g * y * (g⁻¹ * s) := by group
    _ = g * y * (s * g⁻¹) := by rw [hg']
    _ = g * (y * s) * g⁻¹ := by group
    _ = g * (s * y) * g⁻¹ := by rw [hy]
    _ = s * (g * y * g⁻¹) := by
      calc g * (s * y) * g⁻¹ = (g * s) * y * g⁻¹ := by group
        _ = (s * g) * y * g⁻¹ := by rw [hg]
        _ = s * (g * y * g⁻¹) := by group

theorem loc5_inter_bot [Finite G] {s t : G} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (ht3 : t ^ 3 = 1)
    (ht1 : t ≠ 1) (hP : Nat.card ↥(Subgroup.closure ({s, t} : Set G)) = 9) :
    Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have htord : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  by_contra hg1
  have hgs := hg.1
  have hgt := hg.2
  have hgord : orderOf g = 3 := by
    have h1 : orderOf g ∣ 3 := hsord ▸ orderOf_dvd_of_mem_zpowers hgs
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1
    · exact h
  have hzs : Subgroup.zpowers g = Subgroup.zpowers s :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgs)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hgord, hsord])
  have hzt : Subgroup.zpowers g = Subgroup.zpowers t :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgt)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hgord, htord])
  have htS : t ∈ Subgroup.zpowers s := by
    have : t ∈ Subgroup.zpowers g := by rw [hzt]; exact Subgroup.mem_zpowers t
    rw [hzs] at this
    exact this
  have hle : Subgroup.closure ({s, t} : Set G) ≤ Subgroup.zpowers s := by
    apply (Subgroup.closure_le _).mpr
    exact Set.insert_subset_iff.mpr ⟨Subgroup.mem_zpowers s, Set.singleton_subset_iff.mpr htS⟩
  have hc := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hsord, hP] at hc
  omega

theorem loc5_P_cases [Finite G] {s t : G} (hst : s * t = t * s) (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1) (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) {p : G}
    (hp : p ∈ Subgroup.closure ({s, t} : Set G)) (hp1 : p ≠ 1) :
    ∃ q ∈ ({s, t, s * t, s * t⁻¹} : Set G), ∃ k : ℕ, p ^ k = q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hto : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have hcomm : ∀ x ∈ Subgroup.zpowers t, ∀ y ∈ Subgroup.zpowers s,
      x * y * x⁻¹ ∈ Subgroup.zpowers s := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute (s ^ j) (t ^ k) := Commute.zpow_zpow (show Commute s t from hst) j k
    have e : t ^ k * s ^ j * (t ^ k)⁻¹ = s ^ j := by
      rw [← hc.eq]
      group
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) j
  have hle : Subgroup.closure ({s, t} : Set G) ≤ Subgroup.zpowers s ⊔ Subgroup.zpowers t := by
    apply (Subgroup.closure_le _).mpr
    exact Set.insert_subset_iff.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers s),
      Set.singleton_subset_iff.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))⟩
  obtain ⟨a, ha, b, hb, hpab⟩ := (loc5_mem_sup hcomm).mp (hle hp)
  have hred : ∀ u : G, orderOf u = 3 → ∀ i : ℤ, ∃ n : ℕ, n < 3 ∧ u ^ i = u ^ n := by
    intro u hu i
    refine ⟨(i % 3).toNat, ?_, ?_⟩
    · have h1 := Int.emod_nonneg i (by norm_num : (3:ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos i (by norm_num : (0:ℤ) < 3)
      omega
    · have h3 : u ^ i = u ^ (i % (orderOf u : ℤ)) := (zpow_mod_orderOf u i).symm
      rw [hu] at h3
      simp only [Nat.cast_ofNat] at h3
      rw [h3, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))]
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  obtain ⟨i₀, hi₀, hsi⟩ := hred s hsord i
  obtain ⟨j₀, hj₀, htj⟩ := hred t hto j
  rw [hsi, htj] at hpab
  subst hpab
  have hmulpow : ∀ a b k : ℕ, (s ^ a * t ^ b) ^ k = s ^ (a * k) * t ^ (b * k) := by
    intro a b k
    rw [(Commute.pow_pow hst a b).mul_pow, ← pow_mul, ← pow_mul]
  have hs4 : s ^ 4 = s := by
    rw [show (4:ℕ) = 1 + 3 from rfl, pow_add, hs3, mul_one, pow_one]
  have ht4 : t ^ 4 = t := by
    rw [show (4:ℕ) = 1 + 3 from rfl, pow_add, ht3, mul_one, pow_one]
  have ht2inv : t ^ 2 = t⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact ht3
  interval_cases i₀ <;> interval_cases j₀
  · exact absurd (by simp) hp1
  · exact ⟨t, by simp, 1, by simp⟩
  · refine ⟨t, by simp, 2, ?_⟩
    simp only [pow_zero, one_mul]
    rw [← pow_mul]
    exact ht4
  · exact ⟨s, by simp, 1, by simp⟩
  · exact ⟨s * t, by simp, 1, by simp⟩
  · refine ⟨s * t⁻¹, by simp, 1, ?_⟩
    simp only [pow_one]
    rw [ht2inv]
  · refine ⟨s, by simp, 2, ?_⟩
    simp only [pow_zero, mul_one]
    rw [← pow_mul]
    exact hs4
  · refine ⟨s * t⁻¹, by simp, 2, ?_⟩
    rw [hmulpow]
    show s ^ 4 * t ^ 2 = s * t⁻¹
    rw [hs4, ht2inv]
  · refine ⟨s * t, by simp, 2, ?_⟩
    rw [hmulpow]
    show s ^ 4 * t ^ 4 = s * t
    rw [hs4, ht4]

theorem loc5_le_of_inv {Pb Y : Subgroup G} {z s : G} [Finite G]
    (hPbc : ∀ u ∈ Pb, ∀ v ∈ Pb, u * v = v * u) (hYPb : Y ≤ Pb)
    (hYz : ∀ y ∈ Y, z * y * z⁻¹ ∈ Y)
    (hYnorm : ∀ t ∈ Subgroup.zpowers s, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y)
    (hsplit : Pb ≤ Y ⊔ Subgroup.zpowers s) (hYs : ∀ y ∈ Y, y ∈ Subgroup.zpowers s → y = 1)
    (hsPb : Subgroup.zpowers s ≤ Pb)
    (hzs : z * s = s * z) (hs3 : s ^ 3 = 1) :
    ∀ x ∈ Pb, z * x * z⁻¹ = x⁻¹ → x ∈ Y := by
  intro x hx hzx
  obtain ⟨a, ha, b, hb, hab⟩ := (loc5_mem_sup hYnorm).mp (hsplit hx)
  subst hab
  have ha' : a ∈ Pb := hYPb ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hcz : Commute z s := hzs
  have hzb : z * b * z⁻¹ = b := by
    rw [← hk, (hcz.zpow_right k).eq]
    group
  have hb3 : b ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs3, one_zpow]
  have h1 : (z * a * z⁻¹) * b = b⁻¹ * a⁻¹ := by
    calc (z * a * z⁻¹) * b = (z * a * z⁻¹) * (z * b * z⁻¹) := by rw [hzb]
      _ = z * (a * b) * z⁻¹ := by group
      _ = (a * b)⁻¹ := hzx
      _ = b⁻¹ * a⁻¹ := by group
  have hb' : b ∈ Pb := hsPb hb
  have hca : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ :=
    hPbc _ (Pb.inv_mem ha') _ (Pb.inv_mem hb')
  have h2 : z * a * z⁻¹ = b⁻¹ * a⁻¹ * b⁻¹ := by
    calc z * a * z⁻¹ = ((z * a * z⁻¹) * b) * b⁻¹ := by group
      _ = (b⁻¹ * a⁻¹) * b⁻¹ := by rw [h1]
  have h4 : (b⁻¹ * a⁻¹ * b⁻¹) * a = b⁻¹ * b⁻¹ := by
    calc (b⁻¹ * a⁻¹ * b⁻¹) * a = b⁻¹ * (a⁻¹ * b⁻¹) * a := by group
      _ = b⁻¹ * (b⁻¹ * a⁻¹) * a := by rw [hca]
      _ = b⁻¹ * b⁻¹ := by group
  have h3 : b⁻¹ * b⁻¹ = (z * a * z⁻¹) * a := by
    rw [h2]
    exact h4.symm
  have hYb : b⁻¹ * b⁻¹ ∈ Y := by
    rw [h3]
    exact Y.mul_mem (hYz a ha) ha
  have hZb : b⁻¹ * b⁻¹ ∈ Subgroup.zpowers s :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) (Subgroup.inv_mem _ hb)
  have h5 : b⁻¹ * b⁻¹ = 1 := hYs _ hYb hZb
  have h6 : b⁻¹ = b := by
    have h := inv_eq_of_mul_eq_one_right h5
    rw [inv_inv] at h
    exact h.symm
  have hbb : b * b = 1 := by
    have h := mul_inv_cancel b
    rw [h6] at h
    exact h
  have e3 : b ^ 3 = b := by rw [pow_three, hbb, mul_one]
  have h7 : b = 1 := by
    calc b = b ^ 3 := e3.symm
      _ = 1 := hb3
  rw [h7, mul_one]
  exact ha

theorem loc5_conj_inv {t a : G} (ht : t * t = 1) (h : t * a * t * a = 1) :
    t * a * t⁻¹ = a⁻¹ := by
  have ti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [ti]
  exact eq_inv_of_mul_eq_one_left h

theorem loc5_zpow_red {u : G} (hu : orderOf u = 3) (i : ℤ) : ∃ n : ℕ, n < 3 ∧ u ^ i = u ^ n := by
  refine ⟨(i % 3).toNat, ?_, ?_⟩
  · have h1 := Int.emod_nonneg i (by norm_num : (3:ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos i (by norm_num : (0:ℤ) < 3)
    omega
  · have h3 : u ^ i = u ^ (i % (orderOf u : ℤ)) := (zpow_mod_orderOf u i).symm
    rw [hu] at h3
    simp only [Nat.cast_ofNat] at h3
    rw [h3, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))]

theorem loc5_cent_le {p q : G} {k : ℕ} (h : p ^ k = q) :
    Subgroup.centralizer ({p} : Set G) ≤ Subgroup.centralizer ({q} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  rw [← h]
  exact ((Commute.pow_right (show Commute x p from hx) k)).eq

end CFSG.GH74.QTGen4.Recog.G23.P7
