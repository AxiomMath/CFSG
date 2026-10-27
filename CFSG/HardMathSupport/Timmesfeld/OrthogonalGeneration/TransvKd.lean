module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvAction
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.OrthJ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {X : Type*} [Group X] {K : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

@[expose] def embK (e : ↥K ≃* ↥(elementaryGroup Q)) : ↥K →* (V ≃ₗ[ZMod 2] V) :=
  (elementaryGroup Q).subtype.comp e.toMonoidHom

theorem embK_apply (e : ↥K ≃* ↥(elementaryGroup Q)) (k : ↥K) :
    embK e k = (e k : V ≃ₗ[ZMod 2] V) := rfl

theorem embK_injective (e : ↥K ≃* ↥(elementaryGroup Q)) : Function.Injective (embK e) :=
  fun _ _ h => e.injective (Subtype.ext h)

theorem embK_mem (e : ↥K ≃* ↥(elementaryGroup Q)) (k : ↥K) : embK e k ∈ elementaryGroup Q :=
  (e k).2

theorem exists_embK_eq (e : ↥K ≃* ↥(elementaryGroup Q)) {z : V ≃ₗ[ZMod 2] V}
    (hz : z ∈ elementaryGroup Q) : ∃ k : ↥K, embK e k = z := by
  obtain ⟨k, hk⟩ := e.surjective ⟨z, hz⟩
  exact ⟨k, by rw [embK_apply, hk]⟩

@[expose] def liftSub (e : ↥K ≃* ↥(elementaryGroup Q)) (J : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Subgroup X :=
  (J.comap (embK e)).map K.subtype

theorem mem_liftSub {e : ↥K ≃* ↥(elementaryGroup Q)} {J : Subgroup (V ≃ₗ[ZMod 2] V)} {k : X} :
    k ∈ liftSub e J ↔ ∃ hk : k ∈ K, embK e ⟨k, hk⟩ ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hk, h⟩
    exact ⟨⟨k, hk⟩, h, rfl⟩

theorem liftSub_le (e : ↥K ≃* ↥(elementaryGroup Q)) (J : Subgroup (V ≃ₗ[ZMod 2] V)) :
    liftSub e J ≤ K := by
  rintro k hk
  exact (mem_liftSub.mp hk).1

theorem exists_mem_liftSub (e : ↥K ≃* ↥(elementaryGroup Q)) {J : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hJ : J ≤ elementaryGroup Q) {z : V ≃ₗ[ZMod 2] V} (hz : z ∈ J) :
    ∃ k : ↥K, (k : X) ∈ liftSub e J ∧ embK e k = z := by
  obtain ⟨k, hk⟩ := exists_embK_eq e (hJ hz)
  exact ⟨k, mem_liftSub.mpr ⟨k.2, by simpa [hk] using hz⟩, hk⟩

theorem liftSub_iSup_eq (e : ↥K ≃* ↥(elementaryGroup Q)) {ι : Sort*}
    (J : ι → Subgroup (V ≃ₗ[ZMod 2] V)) (hJ : ∀ i, J i ≤ elementaryGroup Q)
    (hsup : elementaryGroup Q ≤ ⨆ i, J i) : ⨆ i, liftSub e (J i) = K := by
  refine le_antisymm (iSup_le fun i => liftSub_le e (J i)) ?_
  set M := ⨆ i, liftSub e (J i) with hM
  have hMK : M ≤ K := iSup_le fun i => liftSub_le e (J i)
  set M' : Subgroup ↥K := M.subgroupOf K with hM'
  have hJle : ∀ i, J i ≤ M'.map (embK e) := by
    intro i z hz
    obtain ⟨k, hk1, hk2⟩ := exists_mem_liftSub e (hJ i) hz
    refine ⟨k, ?_, hk2⟩
    exact (Subgroup.mem_subgroupOf).mpr (le_iSup (fun i => liftSub e (J i)) i hk1)
  have hE : elementaryGroup Q ≤ M'.map (embK e) := hsup.trans (iSup_le hJle)
  intro k hk
  have := hE (embK_mem e ⟨k, hk⟩)
  obtain ⟨m, hm, hmk⟩ := this
  have : m = ⟨k, hk⟩ := embK_injective e hmk
  rw [this] at hm
  exact hm

namespace ActsAsConj

variable {e : ↥K ≃* ↥(elementaryGroup Q)} {x : X} {g : V ≃ₗ[ZMod 2] V}
  {J : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem conj_mem_liftSub (hx : x ∈ Subgroup.normalizer (K : Set X)) (h : ActsAsConj e x g)
    (hJ : ∀ z ∈ J, g * z * g⁻¹ ∈ J) {k : X} (hk : k ∈ liftSub e J) :
    x * k * x⁻¹ ∈ liftSub e J := by
  obtain ⟨hkK, hkJ⟩ := mem_liftSub.mp hk
  have hk' : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hx k).mp hkK
  refine mem_liftSub.mpr ⟨hk', ?_⟩
  have := h ⟨k, hkK⟩ hk'
  rw [embK_apply, this]
  exact hJ _ hkJ

theorem mem_normalizer_liftSub (hx : x ∈ Subgroup.normalizer (K : Set X)) (h : ActsAsConj e x g)
    (hJ : ∀ z, z ∈ J ↔ g * z * g⁻¹ ∈ J) : x ∈ Subgroup.normalizer (liftSub e J : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact conj_mem_liftSub hx h (fun z hz => (hJ z).mp hz) hk
  · intro hk
    obtain ⟨hk', hkJ⟩ := mem_liftSub.mp hk
    have hkK : k ∈ K := (Subgroup.mem_normalizer_iff.mp hx k).mpr hk'
    refine mem_liftSub.mpr ⟨hkK, ?_⟩
    have := h ⟨k, hkK⟩ hk'
    rw [embK_apply] at hkJ
    rw [this] at hkJ
    exact (hJ _).mpr hkJ

theorem commute_iff (hx : x ∈ Subgroup.normalizer (K : Set X)) (h : ActsAsConj e x g) {k : X}
    (hk : k ∈ K) : x * k = k * x ↔ g * embK e ⟨k, hk⟩ = embK e ⟨k, hk⟩ * g := by
  have hk' : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hx k).mp hk
  have h1 := h ⟨k, hk⟩ hk'
  constructor
  · intro hc
    have e1 : (⟨x * k * x⁻¹, hk'⟩ : ↥K) = ⟨k, hk⟩ := Subtype.ext (by simp [hc])
    rw [e1] at h1
    rw [embK_apply]
    calc g * (e ⟨k, hk⟩ : V ≃ₗ[ZMod 2] V) = g * (e ⟨k, hk⟩ : V ≃ₗ[ZMod 2] V) * g⁻¹ * g := by group
      _ = (e ⟨k, hk⟩ : V ≃ₗ[ZMod 2] V) * g := by rw [← h1]
  · intro hc
    have e1 : (⟨x * k * x⁻¹, hk'⟩ : ↥K) = ⟨k, hk⟩ := by
      apply e.injective
      apply Subtype.ext
      rw [h1]
      rw [embK_apply] at hc
      calc g * (e ⟨k, hk⟩ : V ≃ₗ[ZMod 2] V) * g⁻¹ = (e ⟨k, hk⟩ : V ≃ₗ[ZMod 2] V) * g * g⁻¹ := by
            rw [hc]
        _ = (e ⟨k, hk⟩ : V ≃ₗ[ZMod 2] V) := by group
    have := congrArg Subtype.val e1
    simp only at this
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [this]

theorem liftSub_le_inf_centralizer (hx : x ∈ Subgroup.normalizer (K : Set X)) (h : ActsAsConj e x g)
    (hJ : ∀ z ∈ J, g * z = z * g) : liftSub e J ≤ K ⊓ Subgroup.centralizer ({x} : Set X) := by
  intro k hk
  obtain ⟨hkK, hkJ⟩ := mem_liftSub.mp hk
  refine ⟨hkK, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  rw [Set.mem_singleton_iff.mp hy]
  exact (commute_iff hx h hkK).mpr (hJ _ hkJ)

end ActsAsConj

theorem normal_subgroupOf_liftSub {e : ↥K ≃* ↥(elementaryGroup Q)} {x : X}
    {J : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hle : liftSub e J ≤ K ⊓ Subgroup.centralizer ({x} : Set X))
    (hJ : ∀ (k : X) (hk : k ∈ K), k ∈ Subgroup.centralizer ({x} : Set X) → ∀ z ∈ J,
      embK e ⟨k, hk⟩ * z * (embK e ⟨k, hk⟩)⁻¹ ∈ J) :
    ((liftSub e J).subgroupOf (K ⊓ Subgroup.centralizer ({x} : Set X))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  obtain ⟨hhK, hhJ⟩ := mem_liftSub.mp hh
  obtain ⟨hkK, hkC⟩ := hk
  have hkh : k * h * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hkK hhK) (K.inv_mem hkK)
  refine mem_liftSub.mpr ⟨hkh, ?_⟩
  have e1 : (⟨k * h * k⁻¹, hkh⟩ : ↥K) = ⟨k, hkK⟩ * ⟨h, hhK⟩ * (⟨k, hkK⟩)⁻¹ := rfl
  rw [e1, map_mul, map_mul, map_inv]
  exact hJ k hkK hkC _ hhJ

theorem mem_orthJ_conj_iff {g r : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hc : g * r = r * g) (z : V ≃ₗ[ZMod 2] V) :
    z ∈ orthJ Q (fixSub (Subgroup.zpowers r)) ↔
      g * z * g⁻¹ ∈ orthJ Q (fixSub (Subgroup.zpowers r)) := by
  have key : ∀ {g : V ≃ₗ[ZMod 2] V}, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → g * r = r * g →
      ∀ w ∈ fixSub (Subgroup.zpowers r), g w ∈ fixSub (Subgroup.zpowers r) := by
    intro g hg hc w hw
    have hw' : r w = w := mem_fixSub_zpowers.mp hw
    rw [mem_fixSub_zpowers]
    calc r (g w) = (r * g) w := rfl
      _ = (g * r) w := by rw [hc]
      _ = g w := by rw [LinearEquiv.mul_apply, hw']
  constructor
  · intro hz
    exact conj_mem_orthJ hg (key hg hc) hz
  · intro hz
    have hg' : g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := inv_mem hg
    have hc' : g⁻¹ * r = r * g⁻¹ := by
      calc g⁻¹ * r = g⁻¹ * (r * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * r) * g⁻¹ := by rw [hc]
        _ = r * g⁻¹ := by group
    have := conj_mem_orthJ hg' (key hg' hc') hz
    simpa [mul_assoc] using this

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
