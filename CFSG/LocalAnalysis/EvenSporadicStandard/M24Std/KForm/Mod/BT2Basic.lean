module

public import CFSG.Foundations.Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG

theorem isCharacteristicP_two_of_two_radical {X : Type*} [Group X] (R : Subgroup X) [R.Normal]
    (hRp : IsPGroup 2 R)
    (hc : ∀ x ∈ centralizer (R : Set X), ∃ k : ℕ, x ^ 2 ^ k = 1) :
    IsCharacteristicP 2 X := by
  have hRle : R ≤ pCore 2 X := le_sSup ⟨inferInstance, hRp⟩
  have hZn : (centralizer (pCore 2 X : Set X)).Normal := by
    refine ⟨fun z hz g => ?_⟩
    rw [mem_centralizer_iff] at hz ⊢
    intro p hp
    have h1 : g⁻¹ * p * g ∈ pCore 2 X := by
      have := (pCore_normal (p := 2) (G := X)).conj_mem p hp g⁻¹
      simpa using this
    have h2 := hz _ h1
    calc p * (g * z * g⁻¹) = g * ((g⁻¹ * p * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * p * g)) * g⁻¹ := by rw [h2]
      _ = g * z * g⁻¹ * p := by group
  have hZp : IsPGroup 2 (centralizer (pCore 2 X : Set X)) := by
    intro g
    have hg : (g : X) ∈ centralizer (R : Set X) := by
      have h2 := mem_centralizer_iff.mp g.2
      exact mem_centralizer_iff.mpr fun r hr => h2 r (hRle hr)
    obtain ⟨k, hk⟩ := hc g hg
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hle : centralizer (pCore 2 X : Set X) ≤ pCore 2 X := le_sSup ⟨hZn, hZp⟩
  exact hle

theorem isCharacteristicP_two_of_isPGroup {X : Type*} [Group X] (h : IsPGroup 2 X) :
    IsCharacteristicP 2 X := by
  have hp : IsPGroup 2 (⊤ : Subgroup X) := fun g => by
    obtain ⟨k, hk⟩ := h (g : X)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  exact isCharacteristicP_two_of_two_radical ⊤ hp fun x _ => h x

theorem isCharacteristicP_two_centralizer_of_le {F : Type*} [Group F] {z : F} {Q : Subgroup F}
    (hQC : Q ≤ centralizer ({z} : Set F)) (hQp : IsPGroup 2 Q)
    (hnorm : ∀ c ∈ centralizer ({z} : Set F), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hcen : ∀ c ∈ centralizer ({z} : Set F), (∀ q ∈ Q, c * q = q * c) → c ∈ Q) :
    IsCharacteristicP 2 ↥(centralizer ({z} : Set F)) := by
  set C := centralizer ({z} : Set F) with hC
  set R : Subgroup C := Q.subgroupOf C with hR
  have hRn : R.Normal := by
    refine ⟨fun r hr g => ?_⟩
    rw [hR, mem_subgroupOf] at hr ⊢
    exact hnorm g g.2 r hr
  have hRp : IsPGroup 2 R := hQp.comap_of_injective C.subtype C.subtype_injective
  have hRle : R ≤ pCore 2 C := le_sSup ⟨hRn, hRp⟩
  intro x hx
  have hxQ : (x : F) ∈ Q := by
    refine hcen x x.2 fun q hq => ?_
    have hmem : (⟨q, hQC hq⟩ : C) ∈ R := by rw [hR, mem_subgroupOf]; exact hq
    have h := mem_centralizer_iff.mp hx _ (hRle hmem)
    exact (congrArg Subtype.val h).symm
  exact hRle (by rw [hR, mem_subgroupOf]; exact hxQ)

theorem isCharacteristicP_two_centralizer_of_two_radical {F M : Type*} [Group F] [Group M]
    (φ : F →* M) (hφ : Function.Injective φ) {z : F} (R : Subgroup M)
    (hRX : R ≤ φ.range ⊓ centralizer ({φ z} : Set M))
    (hnorm : ∀ x ∈ φ.range ⊓ centralizer ({φ z} : Set M), x ∈ normalizer (R : Set M))
    (hR : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1)
    (hcent : ∀ x ∈ φ.range ⊓ centralizer ({φ z} : Set M),
      x ∈ centralizer (R : Set M) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    IsCharacteristicP 2 ↥(centralizer ({z} : Set F)) := by
  set C := centralizer ({z} : Set F) with hC
  let ψ : C →* M := φ.comp C.subtype
  have hψ : Function.Injective ψ := hφ.comp C.subtype_injective
  have hψX : ∀ c : C, ψ c ∈ φ.range ⊓ centralizer ({φ z} : Set M) := by
    intro c
    refine mem_inf.mpr ⟨⟨c, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff]
    change φ (c : F) * φ z = φ z * φ (c : F)
    rw [← map_mul, ← map_mul]
    exact congrArg φ (mem_centralizer_singleton_iff.mp c.2)
  set U : Subgroup C := R.comap ψ with hU
  have hUn : U.Normal := by
    refine ⟨fun u hu c => ?_⟩
    have h1 := (mem_normalizer_iff.mp (hnorm _ (hψX c)) (ψ u)).mp hu
    rw [hU, mem_comap]
    simpa [map_mul, map_inv] using h1
  have hUp : IsPGroup 2 U := by
    intro g
    obtain ⟨k, hk⟩ := hR _ g.2
    exact ⟨k, Subtype.ext (hψ (by simpa [map_pow] using hk))⟩
  have hRU : ∀ r ∈ R, ∃ u : C, ψ u = r ∧ u ∈ U := by
    intro r hr
    obtain ⟨hrr, hrc⟩ := mem_inf.mp (hRX hr)
    obtain ⟨u, rfl⟩ := hrr
    have hu : u ∈ C := by
      rw [hC, mem_centralizer_singleton_iff]
      apply hφ
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp hrc
    exact ⟨⟨u, hu⟩, rfl, by rw [hU, mem_comap]; exact hr⟩
  haveI := hUn
  refine isCharacteristicP_two_of_two_radical U hUp fun x hx => ?_
  have hxc : ψ x ∈ centralizer (R : Set M) := by
    rw [mem_centralizer_iff]
    intro r hr
    obtain ⟨u, rfl, hu⟩ := hRU r hr
    have h := mem_centralizer_iff.mp hx u hu
    simpa [map_mul] using congrArg ψ h
  obtain ⟨k, hk⟩ := hcent _ (hψX x) hxc
  exact ⟨k, hψ (by simpa [map_pow] using hk)⟩

@[expose] def InvolutionCentralizersCharTwo (S : Type*) [Group S] : Prop :=
  ∀ t : S, orderOf t = 2 → IsCharacteristicP 2 ↥(centralizer ({t} : Set S))

private theorem map_centralizer_singleton_eq {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (t : S) : (centralizer ({t} : Set S)).map e.toMonoidHom = centralizer ({e t} : Set T) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x * t = t * x := mem_centralizer_singleton_iff.mp hx
    refine mem_centralizer_singleton_iff.mpr ?_
    change e x * e t = e t * e x
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    have hy' : y * e t = e t * y := mem_centralizer_singleton_iff.mp hy
    refine ⟨e.symm y, ?_, by simp⟩
    refine mem_centralizer_singleton_iff.mpr ?_
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy'

theorem isCharacteristicP_two_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsCharacteristicP 2 A) : IsCharacteristicP 2 B := by
  unfold IsCharacteristicP at h ⊢
  intro b hb
  rw [← pCore_map_iso 2 e] at hb ⊢
  refine ⟨e.symm b, h ?_, by simp⟩
  rw [mem_centralizer_iff] at hb ⊢
  intro a ha
  have h1 := hb (e a) ⟨a, ha, rfl⟩
  apply e.injective
  simpa using h1

theorem InvolutionCentralizersCharTwo.of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : InvolutionCentralizersCharTwo T) : InvolutionCentralizersCharTwo S := by
  intro t ht
  let φ : ↥(centralizer ({t} : Set S)) ≃* ↥(centralizer ({e t} : Set T)) :=
    ((centralizer ({t} : Set S)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_singleton_eq e t))
  have hord : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  exact isCharacteristicP_two_of_mulEquiv φ.symm (h (e t) hord)

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
