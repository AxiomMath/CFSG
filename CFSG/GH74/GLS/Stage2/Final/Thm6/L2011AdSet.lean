module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Parts
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Lift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_conjugate_iff)
open scoped commutatorElement

structure PairG {G : Type} [Group G] (x : G) (K₁ K₂ : Subgroup G) (q : ℕ) : Prop where
  ord : orderOf x = 2
  le₁ : K₁ ≤ centralizer ({x} : Set G)
  le₂ : K₂ ≤ centralizer ({x} : Set G)
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  quasi₁ : IsQuasisimple ↥K₁
  quasi₂ : IsQuasisimple ↥K₂
  mem₁ : x ∈ K₁
  mem₂ : x ∈ K₂
  norm : ∀ c ∈ centralizer ({x} : Set G), ∀ a ∈ K₁ ⊔ K₂, c * a * c⁻¹ ∈ K₁ ⊔ K₂
  perf : ∀ M : Subgroup G, M ≤ centralizer ({x} : Set G) → ⁅M, M⁆ = M → M ≤ K₁ ⊔ K₂
  sl₁ : HasSL2Model (↥K₁ ⧸ pPrimeCore 2 ↥K₁) (fun r => r = q)
  sl₂ : HasSL2Model (↥K₂ ⧸ pPrimeCore 2 ↥K₂) (fun r => r = q)
  odd : Odd q
  five : 5 ≤ q

section Conj

variable {G : Type} [Group G]

theorem mem_conjugate_iff' {K : Subgroup G} {g y : G} : y ∈ conjugate K g ↔ g * y * g⁻¹ ∈ K :=
  bar_mem_conjugate_iff

theorem isQuasisimple_conjugate {K : Subgroup G} (g : G) (h : IsQuasisimple ↥K) :
    IsQuasisimple ↥(conjugate K g) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective) h

theorem hasSL2Model_conjugate {K : Subgroup G} (g : G) {P : ℕ → Prop}
    (h : HasSL2Model (↥K ⧸ pPrimeCore 2 ↥K) P) :
    HasSL2Model (↥(conjugate K g) ⧸ pPrimeCore 2 ↥(conjugate K g)) P :=
  CFSG.GH74.GLS.TwoThin.hasSL2Model_of_mulEquiv
    (CFSG.ComponentClassification.UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)) h

theorem PairG.conj {x : G} {K₁ K₂ : Subgroup G} {q : ℕ} (h : PairG x K₁ K₂ q) (g : G) :
    PairG (g⁻¹ * x * g) (conjugate K₁ g) (conjugate K₂ g) q := by
  have hc : ∀ {y : G}, y ∈ centralizer ({g⁻¹ * x * g} : Set G) ↔ g * y * g⁻¹ ∈ centralizer ({x} : Set G) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by rw [hy]
        _ = x * (g * y * g⁻¹) := by group
    · intro hy
      calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [hy]
        _ = (g⁻¹ * x * g) * y := by group
  have hsup : conjugate (K₁ ⊔ K₂) g = conjugate K₁ g ⊔ conjugate K₂ g := Subgroup.map_sup _ _ _
  refine ⟨?_, ?_, ?_, ?_, isQuasisimple_conjugate g h.quasi₁, isQuasisimple_conjugate g h.quasi₂, ?_, ?_, ?_, ?_,
    hasSL2Model_conjugate g h.sl₁, hasSL2Model_conjugate g h.sl₂, h.odd, h.five⟩
  · have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
    rw [MulAut.conj_apply] at this
    rw [show g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g by simp] at this
    rw [this]; exact h.ord
  · intro y hy
    rw [hc]
    exact h.le₁ (mem_conjugate_iff'.mp hy)
  · intro y hy
    rw [hc]
    exact h.le₂ (mem_conjugate_iff'.mp hy)
  · intro a ha b hb
    have h1 := mem_conjugate_iff'.mp ha
    have h2 := mem_conjugate_iff'.mp hb
    have := h.comm _ h1 _ h2
    calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [this]
      _ = b * a := by group
  · exact mem_conjugate_iff'.mpr (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact h.mem₁)
  · exact mem_conjugate_iff'.mpr (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact h.mem₂)
  · intro c hc' a ha
    rw [hc] at hc'
    rw [← hsup] at ha ⊢
    have h1 := mem_conjugate_iff'.mp ha
    have h2 := h.norm _ hc' _ h1
    rw [mem_conjugate_iff']
    have e : g * (c * a * c⁻¹) * g⁻¹ = (g * c * g⁻¹) * (g * a * g⁻¹) * (g * c * g⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  · intro M hM hMp
    have hM' : M.map (MulAut.conj g).toMonoidHom ≤ centralizer ({x} : Set G) := by
      rintro _ ⟨m, hm, rfl⟩
      have := hc.mp (hM hm)
      simpa [MulAut.conj_apply] using this
    have hperf : ⁅M.map (MulAut.conj g).toMonoidHom, M.map (MulAut.conj g).toMonoidHom⁆ =
        M.map (MulAut.conj g).toMonoidHom := by
      rw [← Subgroup.map_commutator, hMp]
    have := h.perf _ hM' hperf
    intro m hm
    have hm' : (MulAut.conj g) m ∈ K₁ ⊔ K₂ := this ⟨m, hm, rfl⟩
    rw [hsup.symm]
    rw [mem_conjugate_iff']
    simpa [MulAut.conj_apply] using hm'

end Conj


section Ctx

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

omit [Finite G] in
theorem Em_conj_mem' {H : Subgroup G} {h : G} (hh : h ∈ H) {j : G} (hj : j ∈ Em H) :
    h * j * h⁻¹ ∈ Em H := by
  obtain ⟨j', hj', rfl⟩ := hj
  have hc : (layer ↥H).Characteristic := CFSG.LocalCores.layer_characteristic
  have hn : (layer ↥H).Normal := inferInstance
  exact ⟨⟨h, hh⟩ * j' * ⟨h, hh⟩⁻¹, hn.conj_mem j' hj' _, rfl⟩

theorem exists_pair (hC : Ctx2011 G z k S) :
    ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1Pair G z S q L₁ L₂ := by
  rcases hC.2 with ⟨ε, q, _, L₁, L₂, h⟩ | ⟨q, _, L₁, L₂, h⟩
  · exact ⟨q, L₁, L₂, h.pair⟩
  · exact ⟨q, L₁, L₂, h.pair⟩

theorem thm4a_of_ctx (hC : Ctx2011 G z k S) : pLayerOf 2 (Cen z) = Em (Cen z) :=
  hC.1.ctx.thm4.1

theorem orderOf_z_of_ctx (hC : Ctx2011 G z k S) : orderOf z = 2 :=
  hC.1.ctx.ctx17.ctx.orderOf_z

theorem exists_data (hC : Ctx2011 G z k S) :
    ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (K₁ K₂ : Subgroup G),
      Stage1Pair G z S q L₁ L₂ ∧ CompData z K₁ K₂ L₁ L₂ := by
  obtain ⟨q, L₁, L₂, hP⟩ := exists_pair hC
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hP (thm4a_of_ctx hC)
  exact ⟨q, L₁, L₂, K₁, K₂, hP, hK⟩

theorem exists_K₂_eq_map {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) :
    ∃ s : G, K₁.map (MulAut.conj s).toMonoidHom = K₂ := by
  obtain ⟨s, -, hsw⟩ := hP.swap
  obtain ⟨hs, hcj⟩ := swaps_cj hsw
  obtain ⟨h1, h2⟩ := hK.swap s hs hcj
  have hle₁ : K₁.map (MulAut.conj s).toMonoidHom ≤ K₂ := by
    rintro _ ⟨a, ha, rfl⟩; exact h1 a ha
  have hle₂ : K₂.map (MulAut.conj s).toMonoidHom ≤ K₁ := by
    rintro _ ⟨a, ha, rfl⟩; exact h2 a ha
  have hc₁ : Nat.card ↥(K₁.map (MulAut.conj s).toMonoidHom) = Nat.card ↥K₁ :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hc₂ : Nat.card ↥(K₂.map (MulAut.conj s).toMonoidHom) = Nat.card ↥K₂ :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hcle₁ := Subgroup.card_le_of_le hle₁
  have hcle₂ := Subgroup.card_le_of_le hle₂
  exact ⟨s, Subgroup.eq_of_le_of_card_ge hle₁ (by omega)⟩

theorem quasi₂_of_data {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) : IsQuasisimple ↥K₂ := by
  obtain ⟨s, hs⟩ := exists_K₂_eq_map hP hK
  rw [← hs]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K₁.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective) hK.quasi₁

theorem hasSL2Model_quot_of_bar' {K : Subgroup G} {L : Subgroup (CentralizerBar z)} {q : ℕ}
    (hKC : K ≤ Cen z) (hbar : barOf z K = L) (hq : Odd q) (h5 : 5 ≤ q)
    (hL : HasSL2Model ↥L (fun r => r = q)) :
    HasSL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q) := by
  have hodd : ∀ y ∈ (toBar z).ker, Odd (orderOf y) := by
    intro y hy
    rw [ker_toBar] at hy
    exact odd_orderOf_of_mem_pPrimeCore hy
  have h1 := IVK.Proofs2.Ivk93Adapt.hasSL2Model_quot_of_hom (toBar z) hodd
    (A := K.subgroupOf (Cen z)) (L := L) hbar hq h5 hL
  exact IVK.Proofs2.Ivk93Adapt.hasSL2Model_quot_of_equiv (Subgroup.subgroupOfEquivOfLe hKC) h1

theorem PairG.of_data {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (hz2 : orderOf z = 2) (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) :
    PairG z K₁ K₂ q := by
  have hq5 := L2012.five_le_of_pair hP
  have hzL := IVK.Proofs2.Ivk93Adapt.zbarC_mem_inf hP
  have hzK : ∀ {K : Subgroup G} {L : Subgroup (CentralizerBar z)}, K ≤ Cen z → barOf z K = L →
      toBar z ⟨z, mem_Cen_self z⟩ ∈ L → z ∈ K := by
    intro K L hKC hbar hzL'
    rw [← hbar] at hzL'
    obtain ⟨k, hk, hkz⟩ := (SL2Bound.mem_barOf_iff hKC).1 hzL'
    exact z_mem_of_toBar_eq hz2 hk (hKC hk) hkz
  refine ⟨hz2, hK.le₁, hK.le₂, hK.comm, hK.quasi₁, quasi₂_of_data hP hK, hzK hK.le₁ hK.bar₁ hzL.1,
    hzK hK.le₂ hK.bar₂ hzL.2, ?_, ?_, hasSL2Model_quot_of_bar' hK.le₁ hK.bar₁ hP.odd hq5 hP.sl₁,
    hasSL2Model_quot_of_bar' hK.le₂ hK.bar₂ hP.odd hq5 hP.sl₂, hP.odd, hq5⟩
  · intro c hc a ha
    rw [← hK.layer] at ha ⊢
    exact Em_conj_mem' hc ha
  · intro M hM hMp
    rw [← hK.layer]
    exact hK.perfect M hM hMp

end Ctx

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
