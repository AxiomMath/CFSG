module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreRep
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreSection
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux

section Clifford
variable {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]

theorem irred_of_irred_transvection (Kh : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P))
    (t : LinearMap.GeneralLinearGroup (ZMod 2) P) (htr : IsF2Transvection t)
    (hn : ∀ k ∈ Kh, t * k * t⁻¹ ∈ Kh)
    (hirr : ∀ W : Submodule (ZMod 2) P, (∀ k ∈ Kh, ∀ x ∈ W, (k : P →ₗ[ZMod 2] P) x ∈ W) →
      (∀ x ∈ W, (t : P →ₗ[ZMod 2] P) x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ k ∈ Kh, k ≠ 1) (W : Submodule (ZMod 2) P)
    (hW : ∀ k ∈ Kh, ∀ x ∈ W, (k : P →ₗ[ZMod 2] P) x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hW0, hWtop⟩ := hcon
  haveI : Module.Finite (ZMod 2) P := Module.Finite.of_finite
  haveI : Finite (P →ₗ[ZMod 2] P) := Module.finite_of_finite (ZMod 2)
  have htt : t * t = 1 := isF2Transvection_mul_self htr
  have hn' : ∀ k ∈ Kh, t⁻¹ * k * t ∈ Kh := by
    have ht : t ∈ Subgroup.normalizer (Kh : Set (LinearMap.GeneralLinearGroup (ZMod 2) P)) :=
      Subgroup.mem_normalizer_fintype fun k hk => hn k hk
    intro k hk
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem ht) k).1 hk
    simpa using this
  have hts : ∀ w : P, (t : P →ₗ[ZMod 2] P) ((t : P →ₗ[ZMod 2] P) w) = w := fun w => by
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) P => (g : P →ₗ[ZMod 2] P) w) htt
    simpa using this
  let tl : P →ₗ[ZMod 2] P := (t : P →ₗ[ZMod 2] P)
  let W' : Submodule (ZMod 2) P := W.map tl
  have hW'mem : ∀ z, z ∈ W' ↔ ∃ w ∈ W, tl w = z := fun z => Submodule.mem_map
  have hkt : ∀ k ∈ Kh, ∀ w : P, (k : P →ₗ[ZMod 2] P) (tl w) =
      tl (((t⁻¹ * k * t : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) := by
    intro k hk w
    have h1 : k * t = t * (t⁻¹ * k * t) := by group
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) P => (g : P →ₗ[ZMod 2] P) w) h1
    simpa using this
  have hW'K : ∀ k ∈ Kh, ∀ x ∈ W', (k : P →ₗ[ZMod 2] P) x ∈ W' := by
    intro k hk x hx
    obtain ⟨w, hw, rfl⟩ := (hW'mem x).1 hx
    rw [hkt k hk]
    exact (hW'mem _).2 ⟨_, hW _ (hn' k hk) w hw, rfl⟩
  have hW'W : ∀ x ∈ W', tl x ∈ W := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (hW'mem x).1 hx
    rw [show tl (tl w) = w from hts w]; exact hw
  have hWW' : ∀ x ∈ W, tl x ∈ W' := fun x hx => (hW'mem _).2 ⟨x, hx, rfl⟩
  have hS : W ⊔ W' = ⊤ := by
    rcases hirr (W ⊔ W')
      (fun k hk x hx => by
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add]
        exact Submodule.add_mem_sup (hW k hk y hy) (hW'K k hk z hz))
      (fun x hx => by
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
        show tl (y + z) ∈ W ⊔ W'
        rw [map_add, add_comm]
        exact Submodule.add_mem_sup (hW'W z hz) (hWW' y hy)) with h | h
    · exact absurd (eq_bot_iff.2 (le_sup_left.trans h.le)) hW0
    · exact h
  have hD : W ⊓ W' = ⊥ := by
    rcases hirr (W ⊓ W')
      (fun k hk x hx => ⟨hW k hk x hx.1, hW'K k hk x hx.2⟩)
      (fun x hx => ⟨hW'W x hx.2, hWW' x hx.1⟩) with h | h
    · exact h
    · exact absurd (eq_top_iff.2 (fun x _ => (h ▸ Submodule.mem_top : x ∈ W ⊓ W').1)) hWtop
  have hinj : Function.Injective ((LinearMap.id + tl : P →ₗ[ZMod 2] P).domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (x : P) + tl x = 0 := by simpa using hx
    have h2 : tl x = x := by
      have := eq_neg_of_add_eq_zero_right hx'
      rw [this, zmod2_neg]
    have : (x : P) ∈ W ⊓ W' := ⟨x.2, by rw [← h2]; exact hWW' x x.2⟩
    rw [hD] at this
    exact Subtype.ext ((Submodule.mem_bot (ZMod 2)).1 this)
  have hdim : Module.finrank (ZMod 2) W ≤ 1 := by
    rw [← LinearMap.finrank_range_of_inj hinj, ← htr.2]
    apply Submodule.finrank_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hfix : ∀ k ∈ Kh, ∀ x ∈ W, (k : P →ₗ[ZMod 2] P) x = x := by
    intro k hk x hx
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
    have hpos : 0 < Module.finrank (ZMod 2) W := Module.finrank_pos_iff.2
      ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
    have hfr : Module.finrank (ZMod 2) W = 1 := le_antisymm hdim hpos
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hfr hx hx0
    have hkx : (k : P →ₗ[ZMod 2] P) x ∈ W := hW k hk x hx
    rw [hspan, Submodule.mem_span_singleton] at hkx
    obtain ⟨c, hc⟩ := hkx
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · exfalso
      rw [zero_smul] at hc
      apply hx0
      have hinvk : ∀ y, ((k⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P)
          ((k : P →ₗ[ZMod 2] P) y) = y := fun y => by
        show (((k⁻¹ * k : LinearMap.GeneralLinearGroup (ZMod 2) P)) : P →ₗ[ZMod 2] P) y = y
        rw [inv_mul_cancel]; rfl
      calc x = ((k⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P)
            ((k : P →ₗ[ZMod 2] P) x) := (hinvk x).symm
        _ = 0 := by rw [← hc, map_zero]
    · rw [one_smul] at hc; exact hc.symm
  obtain ⟨k, hk, hk1⟩ := hnt
  apply hk1
  apply Units.ext
  apply LinearMap.ext
  intro y
  have hy : y ∈ W ⊔ W' := by rw [hS]; exact Submodule.mem_top
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨w₀, hw₀, rfl⟩ := (hW'mem z).1 hz
  rw [map_add, hfix k hk w hw, hkt k hk, hfix _ (hn' k hk) w₀ hw₀]
  rfl

end Clifford

section KIrred
variable {X : Type} [Group X] [Finite X]

def secPre {U₁ : Subgroup X} {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    (φ : ↥U₁ →* Multiplicative P) (W : Submodule (ZMod 2) P) : Subgroup X where
  carrier := {x | ∃ hx : x ∈ U₁, Multiplicative.toAdd (φ ⟨x, hx⟩) ∈ W}
  one_mem' := ⟨U₁.one_mem, by
    have : φ ⟨1, U₁.one_mem⟩ = 1 := map_one φ
    rw [this]; exact W.zero_mem⟩
  mul_mem' := by
    rintro x y ⟨hx, hxW⟩ ⟨hy, hyW⟩
    refine ⟨U₁.mul_mem hx hy, ?_⟩
    have : (⟨x * y, U₁.mul_mem hx hy⟩ : ↥U₁) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, toAdd_mul]
    exact W.add_mem hxW hyW
  inv_mem' := by
    rintro x ⟨hx, hxW⟩
    refine ⟨U₁.inv_mem hx, ?_⟩
    have : (⟨x⁻¹, U₁.inv_mem hx⟩ : ↥U₁) = ⟨x, hx⟩⁻¹ := rfl
    rw [this, map_inv, toAdd_inv]
    exact W.neg_mem hxW

def secImg {U₁ : Subgroup X} {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    (φ : ↥U₁ →* Multiplicative P) (Y : Subgroup X) : Submodule (ZMod 2) P where
  carrier := {p | ∃ x : ↥U₁, (x : X) ∈ Y ∧ Multiplicative.toAdd (φ x) = p}
  zero_mem' := ⟨1, Y.one_mem, by simp⟩
  add_mem' := by
    rintro p q ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x * y, Y.mul_mem hx hy, ?_⟩
    rw [map_mul, toAdd_mul]
  smul_mem' := by
    rintro c p ⟨x, hx, rfl⟩
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · exact ⟨1, Y.one_mem, by simp⟩
    · exact ⟨x, hx, by simp⟩

theorem kirred_of_irredM_proof {a : X} {K V U₁ U₂ : Subgroup X}
    (hKa : ∀ x ∈ K, a * x * a⁻¹ ∈ K) (hV : IsElemAbelian 2 V)
    (hts : TransSectionM K V U₁ U₂ a) : SingleFactor K V U₁ U₂ := by
  have haN : a ∈ Subgroup.normalizer (K : Set X) := Subgroup.mem_normalizer_fintype hKa
  have hel : IsElemAbelian 2 U₁ := hV.mono hts.le.2
  obtain ⟨P, _, _, _, ρ, φ, hd⟩ := secRep_exists_proof K a U₁ U₂ hel hts.le.1 hts.inv₁ hts.inv₂
    hts.asec.inv₁ hts.asec.inv₂
  haveI : Module.Finite (ZMod 2) P := Module.Finite.of_finite
  have htr : IsF2Transvection (ρ (aM K a)) := rho_isF2Transvection hts.asec hd
  have hnormt := rho_aM_mem_normalizer_of_mem haN ρ
  have hKh : ∀ k ∈ (K.subgroupOf (Mof K a)).map ρ, ∀ u u' : ↥U₁, (∃ m : ↥(Mof K a), (m : X) ∈ K ∧
      ρ m = k ∧ (u' : X) = m * u * m⁻¹) → Multiplicative.toAdd (φ u') =
        (k : P →ₗ[ZMod 2] P) (Multiplicative.toAdd (φ u)) := by
    rintro k hk u u' ⟨m, -, rfl, hu'⟩
    rw [hd.equiv m u u' hu', toAdd_ofAdd]
  refine ⟨hts.toSFBase, fun Y hY₂ hYU hYK => ?_⟩
  let W : Submodule (ZMod 2) P := secImg φ Y
  have hWK : ∀ k ∈ (K.subgroupOf (Mof K a)).map ρ, ∀ x ∈ W, (k : P →ₗ[ZMod 2] P) x ∈ W := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨u, hu, rfl⟩
    have hmK : (m : X) ∈ K := Subgroup.mem_subgroupOf.1 hm
    have hu' : (m : X) * (u : X) * (m : X)⁻¹ ∈ U₁ := hts.inv₁ m hmK u u.2
    refine ⟨⟨_, hu'⟩, hYK m hmK u hu, ?_⟩
    rw [hd.equiv m u ⟨_, hu'⟩ rfl, toAdd_ofAdd]
  have hirrM : ∀ W' : Submodule (ZMod 2) P,
      (∀ k ∈ (K.subgroupOf (Mof K a)).map ρ, ∀ x ∈ W', (k : P →ₗ[ZMod 2] P) x ∈ W') →
      (∀ x ∈ W', (ρ (aM K a) : P →ₗ[ZMod 2] P) x ∈ W') → W' = ⊥ ∨ W' = ⊤ := by
    intro W' hK' ha'
    have h₂ : U₂ ≤ secPre φ W' := by
      intro x hx
      refine ⟨hts.le.1 hx, ?_⟩
      rw [(hd.ker ⟨x, hts.le.1 hx⟩).2 hx]
      exact W'.zero_mem
    have h₁ : secPre φ W' ≤ U₁ := fun x hx => hx.1
    have hYK' : ∀ k ∈ K, ∀ y ∈ secPre φ W', k * y * k⁻¹ ∈ secPre φ W' := by
      rintro k hk y ⟨hy, hyW⟩
      have hu' : k * y * k⁻¹ ∈ U₁ := hts.inv₁ k hk y hy
      refine ⟨hu', ?_⟩
      rw [hd.equiv ⟨k, Subgroup.mem_sup_left hk⟩ ⟨y, hy⟩ ⟨_, hu'⟩ rfl, toAdd_ofAdd]
      exact hK' _ ⟨⟨k, Subgroup.mem_sup_left hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩ _ hyW
    have hYa' : ∀ y ∈ secPre φ W', a * y * a⁻¹ ∈ secPre φ W' := by
      rintro y ⟨hy, hyW⟩
      have hu' : a * y * a⁻¹ ∈ U₁ := hts.asec.inv₁ y hy
      refine ⟨hu', ?_⟩
      rw [hd.equiv (aM K a) ⟨y, hy⟩ ⟨_, hu'⟩ rfl, toAdd_ofAdd]
      exact ha' _ hyW
    rcases hts.irredM _ h₂ h₁ hYK' hYa' with h | h
    · left
      rw [eq_bot_iff]
      intro p hp
      obtain ⟨x, hx⟩ := hd.surj (Multiplicative.ofAdd p)
      have hxp : Multiplicative.toAdd (φ x) = p := by rw [hx]; rfl
      have hxY : (x : X) ∈ secPre φ W' := ⟨x.2, by simpa [hxp] using hp⟩
      rw [h] at hxY
      have := (hd.ker x).2 hxY
      rw [this] at hxp
      rw [Submodule.mem_bot, ← hxp]; rfl
    · right
      rw [eq_top_iff]
      intro p _
      obtain ⟨x, hx⟩ := hd.surj (Multiplicative.ofAdd p)
      have hxp : Multiplicative.toAdd (φ x) = p := by rw [hx]; rfl
      have hxY : (x : X) ∈ secPre φ W' := by rw [h]; exact x.2
      obtain ⟨_, hxW⟩ := hxY
      rw [← hxp]; exact hxW
  have hnt : ∃ k ∈ (K.subgroupOf (Mof K a)).map ρ, k ≠ 1 := by
    obtain ⟨k, hk⟩ := rho_nontriv hts.toSFBase hd
    exact ⟨_, ⟨⟨k, Subgroup.mem_sup_left k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩, hk⟩
  have hn : ∀ k ∈ (K.subgroupOf (Mof K a)).map ρ, ρ (aM K a) * k * (ρ (aM K a))⁻¹ ∈
      (K.subgroupOf (Mof K a)).map ρ := fun k hk => (Subgroup.mem_normalizer_iff.1 hnormt k).1 hk
  rcases irred_of_irred_transvection _ _ htr hn hirrM hnt W hWK with h | h
  · left
    apply le_antisymm _ hY₂
    intro y hy
    have hyU : y ∈ U₁ := hYU hy
    have : Multiplicative.toAdd (φ ⟨y, hyU⟩) ∈ W := ⟨⟨y, hyU⟩, hy, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact (hd.ker ⟨y, hyU⟩).1 (by rw [← ofAdd_toAdd (φ ⟨y, hyU⟩), this]; rfl)
  · right
    apply le_antisymm hYU
    intro x hx
    have : Multiplicative.toAdd (φ ⟨x, hx⟩) ∈ W := by rw [h]; exact Submodule.mem_top
    obtain ⟨y, hyY, hyx⟩ := this
    have hker : φ (y⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      rw [← ofAdd_toAdd (φ y), hyx, ofAdd_toAdd]
    have hxy : (y : X)⁻¹ * x ∈ U₂ := (hd.ker _).1 hker
    have : x = (y : X) * ((y : X)⁻¹ * x) := by group
    rw [this]
    exact Y.mul_mem hyY (hY₂ hxy)

end KIrred

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
