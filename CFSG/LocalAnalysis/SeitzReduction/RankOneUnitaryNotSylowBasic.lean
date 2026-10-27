module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartInner
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis

section General

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_conj_inv_iff' {T : Subgroup G} {g y : G} :
    y ∈ T.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ T := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mul_assoc] using hz
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

omit [Finite G] in
theorem exists_isSylowOf_le_of_isPGroup {p : ℕ} [Fact p.Prime] {K P : Subgroup G} (hPK : P ≤ K)
    (hP : IsPGroup p P) : ∃ R, IsSylowOf p R K ∧ P ≤ R := by
  have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  exact ⟨_, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPK hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩⟩

theorem exists_conj_mem_of_isSylowOf {p : ℕ} [Fact p.Prime] {K S P : Subgroup G}
    (hS : IsSylowOf p S K) (hPK : P ≤ K) (hP : IsPGroup p P) :
    ∃ a ∈ K, ∀ x ∈ P, a⁻¹ * x * a ∈ S := by
  obtain ⟨R, hR, hPR⟩ := exists_isSylowOf_le_of_isPGroup hPK hP
  obtain ⟨a, haK, ha⟩ := hS.exists_mem_conj hR
  exact ⟨a, haK, fun x hx => (ha x).mp (hPR hx)⟩

theorem exists_mem_normalizer_inv_mul_mem_of_weakClosed {S R N : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hSN : S ≤ normalizer (N : Set G)) (hRS : R ≤ S)
    (hcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' * r⁻¹ * r'⁻¹ ∈ N)
    (hwc : ∀ h ∈ normalizer (N : Set G), (∀ r ∈ R, h⁻¹ * r * h ∈ S) → ∀ r ∈ R, h⁻¹ * r * h ∈ R)
    {z k : G} (hz : z ∈ R) (hk : k ∈ normalizer (N : Set G)) (hx : k⁻¹ * z * k ∈ R) :
    ∃ n ∈ normalizer (R : Set G), (k⁻¹ * z * k)⁻¹ * (n⁻¹ * z * n) ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x := k⁻¹ * z * k with hxdef
  let C : Subgroup G :=
    { carrier := {y | y ∈ normalizer (N : Set G) ∧ x⁻¹ * (y⁻¹ * x * y) ∈ N}
      mul_mem' := by
        rintro y y' ⟨hy, hyN⟩ ⟨hy', hy'N⟩
        refine ⟨mul_mem hy hy', ?_⟩
        have e : x⁻¹ * ((y * y')⁻¹ * x * (y * y')) =
            x⁻¹ * (y'⁻¹ * x * y') * (y'⁻¹ * (x⁻¹ * (y⁻¹ * x * y)) * y') := by group
        rw [e]
        exact mul_mem hy'N ((mem_normalizer_iff''.mp hy' _).mp hyN)
      one_mem' := ⟨one_mem _, by rw [inv_one, one_mul, mul_one, inv_mul_cancel]; exact one_mem _⟩
      inv_mem' := by
        rintro y ⟨hy, hyN⟩
        refine ⟨inv_mem hy, ?_⟩
        have e : x⁻¹ * (y⁻¹⁻¹ * x * y⁻¹) = (y * (x⁻¹ * (y⁻¹ * x * y)) * y⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem ((mem_normalizer_iff.mp hy _).mp hyN) }
  have hCN : C ≤ normalizer (N : Set G) := fun y hy => hy.1
  have hRC : R ≤ C := by
    intro r hr
    refine ⟨hSN (hRS hr), ?_⟩
    have h1 := hcomm _ (inv_mem hx) _ (inv_mem hr)
    have e : x⁻¹ * (r⁻¹ * x * r) = x⁻¹ * r⁻¹ * x⁻¹⁻¹ * r⁻¹⁻¹ := by group
    rw [e]
    exact h1
  have hRkC : R.map (MulAut.conj k⁻¹).toMonoidHom ≤ C := by
    intro y hy
    have hy' : k * y * k⁻¹ ∈ R := mem_map_conj_inv_iff'.mp hy
    have hyr : y = k⁻¹ * (k * y * k⁻¹) * k := by group
    refine ⟨?_, ?_⟩
    · rw [hyr]
      exact mul_mem (mul_mem (inv_mem hk) (hSN (hRS hy'))) hk
    · have e : x⁻¹ * (y⁻¹ * x * y) =
          k⁻¹ * (z⁻¹ * (k * y * k⁻¹)⁻¹ * z⁻¹⁻¹ * (k * y * k⁻¹)⁻¹⁻¹) * k := by
        rw [hxdef]; group
      rw [e]
      exact (mem_normalizer_iff''.mp hk _).mp (hcomm _ (inv_mem hz) _ (inv_mem hy'))
  have hRp : IsPGroup 2 R := hS.isPGroup.to_le hRS
  have hRkp : IsPGroup 2 (R.map (MulAut.conj k⁻¹).toMonoidHom) := hRp.map _
  obtain ⟨P, hPC, hRP⟩ := exists_isSylowOf_le_of_isPGroup hRC hRp
  obtain ⟨c, hcC, hc⟩ := exists_conj_mem_of_isSylowOf hPC hRkC hRkp
  have hSsyl : IsSylowOf 2 S (normalizer (N : Set G)) := hS.of_le hSN le_top
  obtain ⟨m, hmN, hm⟩ := exists_conj_mem_of_isSylowOf hSsyl (hPC.le.trans hCN) hPC.isPGroup
  have hmR : ∀ r ∈ R, m⁻¹ * r * m ∈ R := hwc m hmN fun r hr => hm r (hRP hr)
  have hw : k * c * m ∈ normalizer (N : Set G) := mul_mem (mul_mem hk (hCN hcC)) hmN
  have hwR : ∀ r ∈ R, (k * c * m)⁻¹ * r * (k * c * m) ∈ R := by
    refine hwc _ hw fun r hr => ?_
    have h1 : c⁻¹ * (k⁻¹ * r * k) * c ∈ P := hc _ (by
      rw [mem_map_conj_inv_iff', show k * (k⁻¹ * r * k) * k⁻¹ = r by group]
      exact hr)
    have h2 := hm _ h1
    rwa [show m⁻¹ * (c⁻¹ * (k⁻¹ * r * k) * c) * m = (k * c * m)⁻¹ * r * (k * c * m) by group]
      at h2
  have hmN' : m ∈ normalizer (R : Set G) := mem_normalizer_of_forall_inv_mul_mul_mem hmR
  have hwN' : k * c * m ∈ normalizer (R : Set G) := mem_normalizer_of_forall_inv_mul_mul_mem hwR
  refine ⟨k * c, ?_, ?_⟩
  · have := mul_mem hwN' (inv_mem hmN')
    rwa [mul_inv_cancel_right] at this
  · have e : (k * c)⁻¹ * z * (k * c) = c⁻¹ * x * c := by rw [hxdef]; group
    rw [e]
    exact hcC.2

end General

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem isSylowOf_szT₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    IsSylowOf 2 (szT₁ L T) L := by
  obtain ⟨-, -, ⟨Q, hQ⟩, -⟩ := h.start_of_card_sylow hS2
  refine ⟨Q, ?_⟩
  rw [hQ, subgroupOf_map_subtype, inf_eq_left.mpr (szT₁_le_right L T)]

theorem exists_conj_mem_szA₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {ℓ : G} (hℓ : ℓ ∈ L)
    (hℓ2 : ℓ ^ 2 = 1) : ∃ m ∈ L, m⁻¹ * ℓ * m ∈ szA₁ (szT₁ L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hinvT₁, -, -⟩ := h.facts_of_card_sylow hS2
  have hP : IsPGroup 2 (zpowers ℓ) :=
    CFSG.GH74.Uniqueness.Bender.isPGroup_two_zpowers_of_mul_self_eq_one (by rw [← sq, hℓ2])
  obtain ⟨m, hmL, hm⟩ := exists_conj_mem_of_isSylowOf (h.isSylowOf_szT₁_of_card_sylow hS2)
    (zpowers_le.mpr hℓ) hP
  refine ⟨m, hmL, hinvT₁ _ (hm ℓ (mem_zpowers ℓ)) ?_⟩
  calc (m⁻¹ * ℓ * m) ^ 2 = m⁻¹ * ℓ ^ 2 * m := by rw [sq, sq]; group
    _ = 1 := by rw [hℓ2]; group

theorem exists_normalizer_szA₁_conj_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {g : G} (hA : ∀ a ∈ szA₁ (szT₁ L T), a * (g⁻¹ * t * g) = g⁻¹ * t * g * a)
    (hin : ∀ a ∈ szA₁ (szT₁ L T), g * a * g⁻¹ ∈ L ⊔ zpowers t) :
    ∃ g' ∈ normalizer (szA₁ (szT₁ L T) : Set G), g'⁻¹ * t * g' = g⁻¹ * t * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hinvT₁, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  have htL : t ∈ centralizer (L : Set G) := h.mem
  have hLt : ∀ m ∈ L, m * t = t * m := fun m hm => mem_centralizer_iff.mp htL m hm
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← sq, h.sq_eq_one]
  have hstep : ∀ a ∈ szA₁ (szT₁ L T), g * a * g⁻¹ ∈ L := by
    intro a ha
    set a' := g * a * g⁻¹ with ha'
    have hct : a' * t = t * a' := by
      have e := hA a ha
      calc a' * t = g * (a * (g⁻¹ * t * g)) * g⁻¹ := by rw [ha']; group
        _ = g * ((g⁻¹ * t * g) * a) * g⁻¹ := by rw [e]
        _ = t * a' := by rw [ha']; group
    have hsq : a' ^ 2 = 1 := by
      calc a' ^ 2 = g * a ^ 2 * g⁻¹ := by rw [ha', sq, sq]; group
        _ = 1 := by rw [hA₁sq a ha]; group
    obtain ⟨ℓ, hℓ, z, hz, hℓz⟩ := exists_mul_eq_of_mem_sup_zpowers htL
      (show a' ∈ L ⊔ zpowers t from hin a ha)
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · rw [hz1, mul_one] at hℓz
      rw [← hℓz]
      exact hℓ
    · exfalso
      rw [hz1] at hℓz
      have hℓ' : ℓ = a' * t := by
        rw [← hℓz, mul_assoc, ← sq, h.sq_eq_one, mul_one]
      have hℓ2 : ℓ ^ 2 = 1 := by
        calc ℓ ^ 2 = a' * (t * a') * t := by rw [hℓ', sq]; group
          _ = a' * (a' * t) * t := by rw [hct]
          _ = a' ^ 2 * t ^ 2 := by rw [sq, sq]; group
          _ = 1 := by rw [hsq, h.sq_eq_one, one_mul]
      obtain ⟨m, hmL, hm⟩ := h.exists_conj_mem_szA₁_of_card_sylow hS2 hℓ hℓ2
      obtain ⟨k, hk⟩ := h.exists_conj_eq_mul_of_card_sylow hS2 hm
      apply h.conj_not_mem_szA₁_of_card_sylow hS2 (k * m⁻¹ * g)
      have hmt := hLt m hmL
      have e : (k * m⁻¹ * g)⁻¹ * t * (k * m⁻¹ * g) = a := by
        calc (k * m⁻¹ * g)⁻¹ * t * (k * m⁻¹ * g) = g⁻¹ * m * (k⁻¹ * t * k) * m⁻¹ * g := by
              group
          _ = g⁻¹ * m * (m⁻¹ * ℓ * m * t) * m⁻¹ * g := by rw [hk]
          _ = g⁻¹ * ℓ * (m * t * m⁻¹) * g := by group
          _ = g⁻¹ * ℓ * t * g := by rw [hmt, mul_inv_cancel_right]
          _ = g⁻¹ * (ℓ * t) * g := by group
          _ = g⁻¹ * a' * g := by rw [hℓz]
          _ = a := by rw [ha']; group
      rw [e]
      exact ha
  have hP : IsPGroup 2 ((szA₁ (szT₁ L T)).map (MulAut.conj g).toMonoidHom) := by
    refine IsPGroup.map (fun a => ?_) _
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA₁sq a a.2
  have hPL : (szA₁ (szT₁ L T)).map (MulAut.conj g).toMonoidHom ≤ L := by
    rintro _ ⟨a, ha, rfl⟩
    exact hstep a ha
  obtain ⟨m, hmL, hm⟩ := exists_conj_mem_of_isSylowOf (h.isSylowOf_szT₁_of_card_sylow hS2) hPL hP
  have hmA : ∀ a ∈ szA₁ (szT₁ L T), (g⁻¹ * m)⁻¹ * a * (g⁻¹ * m) ∈ szA₁ (szT₁ L T) := by
    intro a ha
    have h1 : m⁻¹ * (g * a * g⁻¹) * m ∈ szT₁ L T := hm _ ⟨a, ha, by simp⟩
    rw [show (g⁻¹ * m)⁻¹ * a * (g⁻¹ * m) = m⁻¹ * (g * a * g⁻¹) * m by group]
    refine hinvT₁ _ h1 ?_
    calc (m⁻¹ * (g * a * g⁻¹) * m) ^ 2 = m⁻¹ * g * a ^ 2 * g⁻¹ * m := by rw [sq, sq]; group
      _ = 1 := by rw [hA₁sq a ha]; group
  have hN : g⁻¹ * m ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem hmA
  refine ⟨(g⁻¹ * m)⁻¹, inv_mem hN, ?_⟩
  have hmt := hLt m hmL
  calc (g⁻¹ * m)⁻¹⁻¹ * t * (g⁻¹ * m)⁻¹ = g⁻¹ * (m * t * m⁻¹) * g := by group
    _ = g⁻¹ * t * g := by rw [hmt, mul_inv_cancel_right]

theorem exists_normalizer_szA₁_conj_of_inner_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hinner : ∀ w ∈ centralizer ({t} : Set G), w ^ 2 = 1 → w ∈ L ⊔ zpowers t)
    {g : G} (hA : ∀ a ∈ szA₁ (szT₁ L T), a * (g⁻¹ * t * g) = g⁻¹ * t * g * a) :
    ∃ g' ∈ normalizer (szA₁ (szT₁ L T) : Set G), g'⁻¹ * t * g' = g⁻¹ * t * g := by
  obtain ⟨-, -, -, -, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  refine h.exists_normalizer_szA₁_conj_of_card_sylow hS2 hA fun a ha => hinner _ ?_ ?_
  · rw [mem_centralizer_singleton_iff]
    have e := hA a ha
    calc g * a * g⁻¹ * t = g * (a * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * a) * g⁻¹ := by rw [e]
      _ = t * (g * a * g⁻¹) := by group
  · calc (g * a * g⁻¹) ^ 2 = g * a ^ 2 * g⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hA₁sq a ha]; group

end U3Start

end CFSG.SeitzReduction.RankOne
