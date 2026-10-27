module

public import CFSG.GH74.GLS.LU.Local.KStep

public section

open Subgroup CFSG CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

variable {Y : Type} [Group Y] [Finite Y]

theorem isTwoComponent_subgroupOf_map_iff' {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (φ : G ≃* G') (X A : Subgroup G) :
    TwoComponents.IsTwoComponent ((A.map φ.toMonoidHom).subgroupOf (X.map φ.toMonoidHom)) ↔
      TwoComponents.IsTwoComponent (A.subgroupOf X) := by
  rw [← TwoComponentTransport.equiv_iff (φ.subgroupMap X) (A.subgroupOf X)]
  have hmap : (A.subgroupOf X).map (φ.subgroupMap X).toMonoidHom =
      (A.map φ.toMonoidHom).subgroupOf (X.map φ.toMonoidHom) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨⟨x, hxX⟩, hxA, hxy⟩
      exact ⟨x, hxA, congrArg Subtype.val hxy⟩
    · rintro ⟨a, haA, rfl⟩
      obtain ⟨x, hxX, hx⟩ := hy
      obtain rfl := φ.injective hx
      exact ⟨⟨x, hxX⟩, haA, rfl⟩
  rw [hmap]
  exact Iff.rfl

omit [Finite Y] in
theorem map_conj_centralizer' (y s : Y) :
    (centralizer ({y * s * y⁻¹} : Set Y)).map (MulAut.conj y⁻¹).toMonoidHom =
      centralizer ({s} : Set Y) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * (y * s * y⁻¹) = (y * s * y⁻¹) * c := mem_centralizer_singleton_iff.mp hc
    show y⁻¹ * c * y⁻¹⁻¹ ∈ centralizer ({s} : Set Y)
    rw [mem_centralizer_singleton_iff]
    calc y⁻¹ * c * y⁻¹⁻¹ * s = y⁻¹ * (c * (y * s * y⁻¹)) * y⁻¹⁻¹ := by group
      _ = y⁻¹ * ((y * s * y⁻¹) * c) * y⁻¹⁻¹ := by rw [hc']
      _ = s * (y⁻¹ * c * y⁻¹⁻¹) := by group
  · intro hx
    have hx' : x * s = s * x := mem_centralizer_singleton_iff.mp hx
    refine ⟨y * x * y⁻¹, ?_, by show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x; group⟩
    show y * x * y⁻¹ ∈ centralizer ({y * s * y⁻¹} : Set Y)
    rw [mem_centralizer_singleton_iff]
    calc y * x * y⁻¹ * (y * s * y⁻¹) = y * (x * s) * y⁻¹ := by group
      _ = y * (s * x) * y⁻¹ := by rw [hx']
      _ = (y * s * y⁻¹) * (y * x * y⁻¹) := by group

theorem KComp.conj {s : Y} {K : Subgroup Y} (h : KComp Y s K) (y : Y) :
    KComp Y (y * s * y⁻¹) (K.map (MulAut.conj y).toMonoidHom) := by
  have hmem : ∀ {k : Y}, k ∈ K.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * k * y ∈ K := by
    intro k
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ha
    · intro hk
      exact ⟨y⁻¹ * k * y, hk, by simp [MulAut.conj_apply, mul_assoc]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective s
    rw [h.ord] at this
    exact this
  · exact ⟨s, h.mem, rfl⟩
  · intro k hk
    rw [hmem] at hk
    rw [mem_centralizer_singleton_iff]
    have h1 : (y⁻¹ * k * y) * s = s * (y⁻¹ * k * y) := mem_centralizer_singleton_iff.mp (h.le hk)
    calc k * (y * s * y⁻¹) = y * ((y⁻¹ * k * y) * s) * y⁻¹ := by group
      _ = y * (s * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
      _ = (y * s * y⁻¹) * k := by group
  · intro c hc k hk
    rw [hmem] at hk ⊢
    have hc' : y⁻¹ * c * y ∈ centralizer ({s} : Set Y) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      have : c * (y * s * y⁻¹) = (y * s * y⁻¹) * c := hc
      calc y⁻¹ * c * y * s = y⁻¹ * (c * (y * s * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * s * y⁻¹) * c) * y := by rw [this]
        _ = s * (y⁻¹ * c * y) := by group
    have := h.norm _ hc' _ hk
    have e : y⁻¹ * (c * k * c⁻¹) * y = (y⁻¹ * c * y) * (y⁻¹ * k * y) * (y⁻¹ * c * y)⁻¹ := by group
    rw [e]; exact this
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective) h.quasi
  · intro k hk hcen
    rw [hmem] at hk
    have h1 : ∀ k' ∈ K, (y⁻¹ * k * y) * k' = k' * (y⁻¹ * k * y) := by
      intro k' hk'
      have := hcen (y * k' * y⁻¹) (hmem.mpr (by
        have e : y⁻¹ * (y * k' * y⁻¹) * y = k' := by group
        rw [e]; exact hk'))
      calc (y⁻¹ * k * y) * k' = y⁻¹ * (k * (y * k' * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * k' * y⁻¹) * k) * y := by rw [this]
        _ = k' * (y⁻¹ * k * y) := by group
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (h.cen _ hk h1)
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    calc (y * s * y⁻¹) ^ m = y * s ^ m * y⁻¹ := conj_zpow
      _ = k := by rw [hm]; group
  · intro Λ hΛ hΛ2
    set φ : Y ≃* Y := MulAut.conj y⁻¹ with hφ
    have hX : (centralizer ({y * s * y⁻¹} : Set Y)).map φ.toMonoidHom = centralizer ({s} : Set Y) :=
      map_conj_centralizer' y s
    have h2 : TwoComponents.IsTwoComponent
        ((Λ.map φ.toMonoidHom).subgroupOf (centralizer ({s} : Set Y))) := by
      rw [← hX]
      exact (isTwoComponent_subgroupOf_map_iff' φ _ Λ).mpr hΛ2
    have hle : Λ.map φ.toMonoidHom ≤ centralizer ({s} : Set Y) := by
      rw [← hX]; exact Subgroup.map_mono hΛ
    have heq := h.only _ hle h2
    have hcomp : (MulAut.conj y).toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Y := by
      ext x
      show y * (y⁻¹ * x * y⁻¹⁻¹) * y⁻¹ = x
      group
    have : Λ = (Λ.map φ.toMonoidHom).map (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [this, heq]


omit [Finite Y] in
theorem map_conj_pPrimeCore_inf_centralizer (g s : Y) :
    ((pPrimeCore 2 Y) ⊓ centralizer ({s} : Set Y)).map (MulAut.conj g).toMonoidHom =
      (pPrimeCore 2 Y) ⊓ centralizer ({g * s * g⁻¹} : Set Y) := by
  have hN : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
  ext y
  constructor
  · rintro ⟨a, ⟨haN, has⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨hN.conj_mem a haN g, ?_⟩
    have h1 : a * s = s * a := mem_centralizer_singleton_iff.mp has
    show g * a * g⁻¹ ∈ centralizer ({g * s * g⁻¹} : Set Y)
    rw [mem_centralizer_singleton_iff]
    calc g * a * g⁻¹ * (g * s * g⁻¹) = g * (a * s) * g⁻¹ := by group
      _ = g * (s * a) * g⁻¹ := by rw [h1]
      _ = (g * s * g⁻¹) * (g * a * g⁻¹) := by group
  · intro hy
    obtain ⟨hyN, hys⟩ := Subgroup.mem_inf.mp hy
    refine ⟨g⁻¹ * y * g, Subgroup.mem_inf.mpr ⟨by simpa using hN.conj_mem y hyN g⁻¹, ?_⟩, by
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group⟩
    have h1 : y * (g * s * g⁻¹) = (g * s * g⁻¹) * y := mem_centralizer_singleton_iff.mp hys
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * y * g * s = g⁻¹ * (y * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * y) * g := by rw [h1]
      _ = s * (g⁻¹ * y * g) := by group

theorem kstep_final₁ {p n : ℕ} (h95 : IVK_9_5At (p ^ n)) (h44a : IVK_4_4a) (hM3 : L3InvTorus)
    (hCov : L3Cover) (hY : IsKGroupNative Y) (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ n)
    {s s' : Y} {K : Subgroup Y} (h : KComp Y s K) (hsl : HasSL2Model ↥K (fun r => r = p ^ n))
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T)
    (hD1 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s} : Set Y) → s' * d = d * s')
    (hg : ∃ g : Y, g * s * g⁻¹ = s * s') (g' : Y) (hg' : g' * s * g'⁻¹ = s')
    {K' : Subgroup Y} (hK' : K' = K.map (MulAut.conj g').toMonoidHom) {ε : ℤ}
    (hcard : (Nat.card ↥(K ⊓ centralizer ({s'} : Set Y)) : ℤ) = ((p ^ n : ℕ) : ℤ) - ε) :
    (ε = 1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ n ∧
      ∃ α : SL(3, F) →* ↥(K ⊔ K'), Function.Surjective α) ∧
    (ε = -1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ n) ^ 2 ∧
      ∃ α : ↥(StatedSU 3 (p ^ n) F) →* ↥(K ⊔ K'), Function.Surjective α) := by
  obtain ⟨g, hg⟩ := hg
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by
    have := pow_orderOf_eq_one s
    rw [h.ord, pow_two] at this; exact this)
  have hord_ss' : orderOf (s * s') = 2 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
    rw [h.ord] at this
    have e : (MulAut.conj g).toMonoidHom s = s * s' := by
      show g * s * g⁻¹ = s * s'
      exact hg
    rw [e] at this
    exact this
  have hs'2 : s' * s' = 1 := by
    have h1 := orderOf_injective (MulAut.conj g').toMonoidHom (MulAut.conj g').injective s
    rw [h.ord] at h1
    have e : (MulAut.conj g').toMonoidHom s = s' := by
      show g' * s * g'⁻¹ = s'
      exact hg'
    rw [e] at h1
    have := pow_orderOf_eq_one s'
    rw [h1, pow_two] at this; exact this
  have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'2
  have hcomm : s * s' = s' * s := by
    have h1 : (s * s') * (s * s') = 1 := by
      have := pow_orderOf_eq_one (s * s')
      rw [hord_ss', pow_two] at this; exact this
    have h2 : s * s' = (s * s')⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [mul_inv_rev, hsi, hs'i] at h2
    exact h2
  have hne : s ≠ s' := by
    intro hss
    have h1 : s * s' = 1 := by rw [← hss]; exact (by
      have := pow_orderOf_eq_one s
      rw [h.ord, pow_two] at this; exact this)
    rw [h1] at hg
    have h2 : s = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) hg
      simpa [mul_assoc] using this
    have := h.ord
    rw [h2, orderOf_one] at this
    exact absurd this (by norm_num)
  set K'' : Subgroup Y := K.map (MulAut.conj g').toMonoidHom with hK''
  have h2 : KComp Y s' K'' := by
    have := h.conj g'
    rw [hg'] at this
    exact this
  have hnc : ∃ k ∈ K'', s * k ≠ k * s := by
    by_contra hcon
    push Not at hcon
    have hsC : s ∈ centralizer (K : Set Y) := by
      rw [mem_centralizer_iff]; intro k hk
      exact mem_centralizer_singleton_iff.mp (h.le hk)
    have hcC : g'⁻¹ * s * g' ∈ centralizer (K : Set Y) := by
      rw [mem_centralizer_iff]
      intro k hk
      have := hcon (g' * k * g'⁻¹) ⟨k, hk, rfl⟩
      calc k * (g'⁻¹ * s * g') = g'⁻¹ * ((g' * k * g'⁻¹) * s) * g' := by group
        _ = g'⁻¹ * (s * (g' * k * g'⁻¹)) * g' := by rw [← this]
        _ = (g'⁻¹ * s * g') * k := by group
    have hc2 : orderOf (g'⁻¹ * s * g') = 2 := by
      have := orderOf_injective (MulAut.conj g'⁻¹).toMonoidHom (MulAut.conj g'⁻¹).injective s
      rw [h.ord] at this
      have e : (MulAut.conj g'⁻¹).toMonoidHom s = g'⁻¹ * s * g' := by
        show g'⁻¹ * s * g'⁻¹⁻¹ = g'⁻¹ * s * g'
        rw [inv_inv]
      rw [e] at this
      exact this
    have hsc : ∀ x ∈ centralizer (K : Set Y), x * s = s * x := fun x hx =>
      ((mem_centralizer_iff.mp hx) s h.mem).symm
    have heq := involution_eq_of_cyclic_sylow hsC hcC h.ord hc2 hsc hcyc
    apply hne
    rw [← hg']
    calc s = g' * (g'⁻¹ * s * g') * g'⁻¹ := by group
      _ = g' * s * g'⁻¹ := by rw [heq]
  have hP : KPair Y s s' K K'' := ⟨h, h2, hne, hcomm, hnc⟩
  have hD2 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s'} : Set Y) → s * d = d * s := by
    intro d hdN hds'
    have hmap := map_conj_pPrimeCore_inf_centralizer g' s
    rw [hg'] at hmap
    have hle : pPrimeCore 2 Y ⊓ centralizer ({s} : Set Y) ≤
        pPrimeCore 2 Y ⊓ centralizer ({s'} : Set Y) := by
      intro x hx
      obtain ⟨hxN, hxs⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hxN, mem_centralizer_singleton_iff.mpr (hD1 x hxN hxs).symm⟩
    have hcard' : Nat.card ↥(pPrimeCore 2 Y ⊓ centralizer ({s'} : Set Y)) =
        Nat.card ↥(pPrimeCore 2 Y ⊓ centralizer ({s} : Set Y)) := by
      rw [← hmap, card_map_conj]
    have heqD := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard'])
    have hd : d ∈ pPrimeCore 2 Y ⊓ centralizer ({s} : Set Y) := by
      rw [heqD]; exact Subgroup.mem_inf.mpr ⟨hdN, hds'⟩
    exact (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).2).symm
  subst hK'
  exact kstep_final h95 h44a hM3 hCov hY hp hp2 hq5 hP hsl hcyc hD1 hD2 ⟨g, hg⟩ hcard

end CFSG.GH74.GLS.LU.Local
