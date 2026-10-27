module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmDefs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open Subgroup CFSG.Open CFSG.LieType.BorelTits CFSG.ComponentClassification.GMS78.RuAsm
  CFSG.ComponentClassification.GMS78.RuPi7

theorem eleven_of_mul_eq : ∀ r ≤ 120, ∀ a ≤ 11, r ∣ 120 → r * 2 ^ a = 49152 → a = 11 := by
  decide

variable {G : Type} [Group G]

theorem conj_mem_center_of_mem_normalizer {R : Subgroup G} {g : G}
    (hg : g ∈ normalizer (R : Set G)) {x : G} (hx : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x) :
    g * x * g⁻¹ ∈ R ∧ ∀ r ∈ R, g * x * g⁻¹ * r = r * (g * x * g⁻¹) := by
  refine ⟨(mem_normalizer_iff.1 hg x).1 hx, fun r hr => ?_⟩
  have hr' : g⁻¹ * r * g ∈ R := by
    have := (mem_normalizer_iff.1 (inv_mem hg) r).1 hr
    rwa [inv_inv] at this
  have e := hxc _ hr'
  calc g * x * g⁻¹ * r = g * (x * (g⁻¹ * r * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * r * g * x) * g⁻¹ := by rw [e]
    _ = r * (g * x * g⁻¹) := by group

theorem map_le_normalizer_map {P : Type} [Group P] {H K : Subgroup P} (F : P →* G)
    (h : H ≤ normalizer (K : Set P)) : H.map F ≤ normalizer ((K.map F : Subgroup G) : Set G) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨m * k * m⁻¹, (mem_normalizer_iff.1 (h hm) k).1 hk, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨k, hk, hky⟩
    refine ⟨m⁻¹ * k * m⁻¹⁻¹, (mem_normalizer_iff.1 (inv_mem (h hm)) k).1 hk, ?_⟩
    rw [map_mul, map_mul, map_inv, inv_inv, hky]
    group

theorem le_map_of_model {f : G} {A Q X R : Subgroup G} {X₀ R₀ J : Subgroup Pi7}
    (hz0 : ruZ0 ∈ ruM2) (hM12 : ruM12 ≤ ruM2)
    (hM1 : ∀ m ∈ ruM2, m * ruZ0 = ruZ0 * m ↔ m ∈ ruM12) (hcard12 : Nat.card ruM12 = 49152)
    (hA0X : ruA0 ≤ X₀) (hXR : X₀ ≤ R₀) (hR0 : R₀ ≤ ruM2) (hcardX : Nat.card X₀ = 32)
    (hXn : ruM12 ≤ normalizer (X₀ : Set Pi7)) (hR0c : R₀.subgroupOf ruM2 = pCore 2 ruM2)
    (hZR0 : ∀ m ∈ R₀, (∀ r ∈ R₀, m * r = r * m) ↔ m ∈ ruA0)
    (hM3 : ∀ g ∈ ruM12, (∀ x ∈ X₀, g * x * g⁻¹ * x⁻¹ ∈ zpowers ruZ0) → g ∈ J)
    (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (hz : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂ m : ↥(normalizer (A : Set G))) : G) = f)
    (hA : ∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂ m : ↥(normalizer (A : Set G))) : G) ∈ A)
    (hR : R = pCoreOf 2 (normalizer (A : Set G))) (hQ : Nat.card Q = 2 ^ 11)
    (σ : ↥(centralizer ({f} : Set G)) →* Equiv.Perm (Fin 5))
    (hker : σ.ker = Q.subgroupOf (centralizer ({f} : Set G)))
    (hXQ : ∀ u ∈ Q, ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ zpowers f)
    (hXu : ∀ Y : Subgroup G, A ≤ Y → Y ≤ R → Nat.card Y = 32 →
      centralizer ({f} : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (Y : Set G) → Y = X) :
    ∀ g ∈ Q, ∃ m : ↥ruM2, (m : Pi7) ∈ J ∧ ((f₂ m : ↥(normalizer (A : Set G))) : G) = g := by
  classical
  set F : ↥ruM2 →* G := (normalizer (A : Set G)).subtype.comp f₂.toMonoidHom with hF
  have hFinj : Function.Injective F := Subtype.val_injective.comp f₂.injective
  have hFapp : ∀ m, F m = ((f₂ m : ↥(normalizer (A : Set G))) : G) := fun _ => rfl
  have hFN : ∀ m, F m ∈ normalizer (A : Set G) := fun m => (f₂ m).2
  have hFsurj : ∀ g (hg : g ∈ normalizer (A : Set G)), F (f₂.symm ⟨g, hg⟩) = g := fun g hg => by
    rw [hFapp, MulEquiv.apply_symm_apply]
  set z : ↥ruM2 := ⟨ruZ0, hz0⟩ with hzdef
  have hFz : F z = f := hz z rfl
  obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Subgroup G,
      H₁ = centralizer ({f} : Set G) ⊓ normalizer (A : Set G) := ⟨_, rfl⟩
  have hH1 : ∀ g : G, g ∈ H₁ ↔ ∃ m : ↥ruM2, (m : Pi7) ∈ ruM12 ∧ F m = g := by
    intro g
    rw [hH₁]
    constructor
    · rintro ⟨hgC, hgN⟩
      refine ⟨f₂.symm ⟨g, hgN⟩, ?_, hFsurj g hgN⟩
      have hc : g * f = f * g := mem_centralizer_singleton_iff.1 hgC
      rw [← hFsurj g hgN, ← hFz, ← map_mul, ← map_mul] at hc
      exact (hM1 _ (f₂.symm ⟨g, hgN⟩).2).1 (congrArg Subtype.val (hFinj hc))
    · rintro ⟨m, hm, rfl⟩
      refine ⟨mem_centralizer_singleton_iff.2 ?_, hFN m⟩
      have e : m * z = z * m := Subtype.ext ((hM1 _ m.2).2 hm)
      rw [← hFz, ← map_mul, e, map_mul]
  have hH1eq : H₁ = (ruM12.subgroupOf ruM2).map F := by
    ext g
    rw [hH1]
    rfl
  have hH1card : Nat.card H₁ = 49152 := by
    rw [hH1eq, Subgroup.card_map_of_injective hFinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM12).toEquiv, hcard12]
  have hH1C : H₁ ≤ centralizer ({f} : Set G) := by
    rw [hH₁]
    exact inf_le_left
  have hQH : Q ≤ H₁ := by
    let φ : ↥H₁ →* Equiv.Perm (Fin 5) := σ.comp (Subgroup.inclusion hH1C)
    have hcardφ : Nat.card H₁ = Nat.card φ.range * Nat.card φ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hr : Nat.card φ.range ∣ 120 := h120 ▸ Subgroup.card_subgroup_dvd_card φ.range
    have hkerQ : ∀ x : ↥H₁, x ∈ φ.ker ↔ (x : G) ∈ Q := by
      intro x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
        Subgroup.mem_subgroupOf]
      rfl
    set KQ := φ.ker.map H₁.subtype with hKQdef
    have hKQ : KQ ≤ Q := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hkerQ x).1 hx
    have hcardKQ : Nat.card KQ = Nat.card φ.ker :=
      Subgroup.card_map_of_injective H₁.subtype_injective
    have hk : Nat.card φ.ker ∣ 2 ^ 11 := hcardKQ ▸ hQ ▸ Subgroup.card_dvd_of_le hKQ
    obtain ⟨a, ha, hka⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk
    have h11 := eleven_of_mul_eq _ (Nat.le_of_dvd (by norm_num) hr) a ha hr
      (by rw [← hka, ← hcardφ, hH1card])
    have hQfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
    have heq : KQ = Q := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hQ, hcardKQ, hka, h11])
    intro g hg
    rw [← heq] at hg
    obtain ⟨x, -, rfl⟩ := hg
    exact x.2
  have hRimg : R = (R₀.subgroupOf ruM2).map F := by
    rw [hR, pCoreOf, ← map_pCore_mulEquiv 2 f₂, ← hR0c, Subgroup.map_map]
  have hAZ : ∀ x : G, x ∈ A ↔ x ∈ R ∧ ∀ r ∈ R, x * r = r * x := by
    intro x
    rw [hRimg]
    constructor
    · intro hx
      have hxN : x ∈ normalizer (A : Set G) := le_normalizer hx
      have hm := hFsurj x hxN
      have hmA : ((f₂.symm ⟨x, hxN⟩ : ↥ruM2) : Pi7) ∈ ruA0 :=
        (hA _).2 (by rw [← hFapp, hm]; exact hx)
      have hmR := hXR (hA0X hmA)
      refine ⟨⟨_, hmR, hm⟩, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      rw [← hm, ← map_mul, ← map_mul]
      exact congrArg F (Subtype.ext ((hZR0 _ hmR).2 hmA r hr))
    · rintro ⟨⟨m, hmR, rfl⟩, hcomm⟩
      refine (hA m).1 ((hZR0 _ hmR).1 fun r hr => ?_)
      have e := hcomm (F ⟨r, hR0 hr⟩) ⟨⟨r, hR0 hr⟩, hr, rfl⟩
      rw [← map_mul, ← map_mul] at e
      exact congrArg Subtype.val (hFinj e)
  have hNR : centralizer ({f} : Set G) ⊓ normalizer (R : Set G) ≤ H₁ := by
    rintro g ⟨hgC, hgR⟩
    rw [hH₁]
    refine ⟨hgC, mem_normalizer_iff.2 fun x => ?_⟩
    rw [hAZ, hAZ]
    constructor
    · rintro ⟨hxR, hxc⟩
      exact conj_mem_center_of_mem_normalizer hgR hxR hxc
    · rintro ⟨hxR, hxc⟩
      have h := conj_mem_center_of_mem_normalizer (inv_mem hgR) hxR hxc
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [e] at h
      exact h
  have hYX : (X₀.subgroupOf ruM2).map F = X := by
    refine hXu _ (fun a ha => ?_) ?_ ?_ (hNR.trans ?_)
    · have haN : a ∈ normalizer (A : Set G) := le_normalizer ha
      exact ⟨f₂.symm ⟨a, haN⟩, hA0X ((hA _).2 (by rw [← hFapp, hFsurj a haN]; exact ha)),
        hFsurj a haN⟩
    · rw [hRimg]
      exact Subgroup.map_mono fun x hx => hXR hx
    · rw [Subgroup.card_map_of_injective hFinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hXR.trans hR0)).toEquiv, hcardX]
    · rw [hH1eq]
      refine map_le_normalizer_map F fun m hm => ?_
      rw [mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact (mem_normalizer_iff.1 (hXn hm) x)
  intro g hg
  obtain ⟨m, hm12, hmg⟩ := (hH1 g).1 (hQH hg)
  refine ⟨m, hM3 _ hm12 fun x hx => ?_, hmg⟩
  set x' : ↥ruM2 := ⟨x, hR0 (hXR hx)⟩
  have hFx : F x' ∈ X := hYX ▸ ⟨x', hx, rfl⟩
  have hc := hXQ g hg (F x') hFx
  rw [← hmg, ← hFz, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hc
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hc
  rw [← map_zpow] at hk
  exact mem_zpowers_iff.2 ⟨k, congrArg Subtype.val (hFinj hk)⟩

end CFSG.ComponentClassification.GMS78.RuCz
