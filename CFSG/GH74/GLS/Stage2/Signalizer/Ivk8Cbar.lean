module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.Stage1.Thm4.L97a
public import CFSG.GroupTheory.PCore.PrimeCoreImages

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.Uniqueness.SU.SU13.TA Equiv Equiv.Perm

section Setup

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem ly_sporadic (hctx : Stage2Ctx G z Kind.ly S) :
    ∃ n : ℕ, (n = 10 ∨ n = 11) ∧ Stage1Sporadic G z S n := by
  have h := hctx.data
  cases h with
  | ly h => exact h

theorem cbar_twoCover (hctx : Stage2Ctx G z Kind.ly S) :
    ∃ n : ℕ, (n = 10 ∨ n = 11) ∧ ∃ π : CentralizerBar z →* alternatingGroup (Fin n),
      TwoCover π ∧ π.ker = center (CentralizerBar z) := by
  obtain ⟨n, hn, hsp⟩ := ly_sporadic hctx
  exact ⟨n, hn, Stage1.Thm4.L97.exists_twoCover hsp.cover⟩

end Setup

section Embed

variable {G : Type} [Group G]

theorem conj_mem_centralizer {t c x : G} (hx : x ∈ centralizer ({t} : Set G)) :
    c * x * c⁻¹ ∈ centralizer ({c * t * c⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc c * x * c⁻¹ * (c * t * c⁻¹) = c * (x * t) * c⁻¹ := by group
    _ = c * (t * x) * c⁻¹ := by rw [hx]
    _ = c * t * c⁻¹ * (c * x * c⁻¹) := by group

theorem oddCore_conj_mem {z g y : G} (hg : g ∈ centralizer ({z} : Set G)) (hy : y ∈ OddCore z) :
    g * y * g⁻¹ ∈ OddCore z := by
  obtain ⟨m, hm, rfl⟩ := hy
  exact ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, (pPrimeCore_normal (G := ↥(Cen z))).conj_mem m hm ⟨g, hg⟩, rfl⟩

theorem oddCore_odd_card [Finite G] (z : G) : Odd (Nat.card ↥(OddCore z)) := by
  have h : Nat.card ↥(OddCore z) = Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
    Subgroup.card_map_of_injective (Cen z).subtype_injective
  rw [h, ← Nat.coprime_two_left]
  exact pPrimeCore_coprime_card

@[expose] def oddPart (c z : G) (H : Subgroup G) : Subgroup G :=
  H ⊓ (OddCore z).comap (MulAut.conj c).toMonoidHom

theorem oddPart_norm {t c z : G} (hc : c * t * c⁻¹ = z) {H : Subgroup G}
    (hH : H ≤ centralizer ({t} : Set G)) :
    ∀ h ∈ H, ∀ y ∈ oddPart c z H, h * y * h⁻¹ ∈ oddPart c z H := by
  intro h hh y hy
  refine ⟨H.mul_mem (H.mul_mem hh hy.1) (H.inv_mem hh), ?_⟩
  have h1 : c * h * c⁻¹ ∈ centralizer ({z} : Set G) := by
    have := conj_mem_centralizer (c := c) (hH hh)
    rwa [hc] at this
  have hy2 : c * y * c⁻¹ ∈ OddCore z := hy.2
  have h2 := oddCore_conj_mem h1 hy2
  show c * (h * y * h⁻¹) * c⁻¹ ∈ OddCore z
  convert h2 using 1
  group

theorem oddPart_odd [Finite G] (c z : G) (H : Subgroup G) : Odd (Nat.card ↥(oddPart c z H)) := by
  have hle : (oddPart c z H).map (MulAut.conj c).toMonoidHom ≤ OddCore z := by
    rintro _ ⟨m, hm, rfl⟩
    exact hm.2
  have h7 : Nat.card ↥((oddPart c z H).map (MulAut.conj c).toMonoidHom) =
      Nat.card ↥(oddPart c z H) := Subgroup.card_map_of_injective (MulAut.conj c).injective
  have h8 := Subgroup.card_dvd_of_le hle
  rw [h7] at h8
  exact (oddCore_odd_card z).of_dvd_nat h8

@[expose] def conjCen {t c : G} (z : G) (hc : c * t * c⁻¹ = z) (R : Subgroup G)
    (hR : R ≤ centralizer ({t} : Set G)) : ↥R →* ↥(Cen z) where
  toFun x := ⟨c * (x : G) * c⁻¹, by
    have := conj_mem_centralizer (c := c) (hR x.2)
    rwa [hc] at this⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjCen_coe {t c : G} {z : G} (hc : c * t * c⁻¹ = z) {R : Subgroup G}
    (hR : R ≤ centralizer ({t} : Set G)) (x : ↥R) :
    ((conjCen z hc R hR x : ↥(Cen z)) : G) = c * (x : G) * c⁻¹ := rfl

theorem conjCen_injective {t c : G} {z : G} (hc : c * t * c⁻¹ = z) {R : Subgroup G}
    (hR : R ≤ centralizer ({t} : Set G)) : Function.Injective (conjCen z hc R hR) := by
  intro a b h
  have h' := congrArg Subtype.val h
  rw [conjCen_coe, conjCen_coe] at h'
  exact Subtype.ext (by simpa using h')

variable [Finite G] {z : G} {S : Subgroup G}

theorem conjCen_ker_odd {t c : G} {z : G} (hc : c * t * c⁻¹ = z) {R : Subgroup G}
    (hR : R ≤ centralizer ({t} : Set G)) :
    ¬ 2 ∣ Nat.card ((toBar z).comp (conjCen z hc R hR)).ker := by
  have h2 : ((toBar z).comp (conjCen z hc R hR)).ker =
      (pPrimeCore 2 ↥(Cen z)).comap (conjCen z hc R hR) := by
    ext x
    simp [toBar, QuotientGroup.eq_one_iff]
  have h3 : Nat.card ((pPrimeCore 2 ↥(Cen z)).comap (conjCen z hc R hR)) ∣
      Nat.card (pPrimeCore 2 ↥(Cen z)) :=
    Subgroup.card_comap_dvd_of_injective _ _ (conjCen_injective hc hR)
  rw [h2]
  intro h
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card (h.trans h3)

theorem cbar_G (hctx : Stage2Ctx G z Kind.ly S) (t : G) (ht : orderOf t = 2)
    (R : Subgroup G) (hR : R ≤ centralizer ({t} : Set G)) :
    ∃ (n : ℕ) (K : Type) (_ : Group K) (R' : Subgroup K), (n = 10 ∨ n = 11) ∧
      IsDoubleCoverOfAlt K n ∧
      Nonempty ((↥R ⧸ pPrimeCore 2 ↥R) ≃* (↥R' ⧸ pPrimeCore 2 ↥R')) := by
  obtain ⟨n, hn, hsp⟩ := ly_sporadic hctx
  obtain ⟨c, hc⟩ := isConj_iff.mp (hsp.one_class t z ht hctx.central.1)
  let f : ↥R →* CentralizerBar z := (toBar z).comp (conjCen z hc R hR)
  let g : ↥R →* ↥f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hker : ¬ 2 ∣ Nat.card g.ker := by
    rw [show g.ker = f.ker from f.ker_rangeRestrict]
    exact conjCen_ker_odd hc hR
  obtain ⟨hcomap, -⟩ := CFSG.prime_complement_kernel_core_preimage (p := 2) g hg hker
  let h : ↥R →* (↥f.range ⧸ pPrimeCore 2 ↥f.range) := (QuotientGroup.mk' _).comp g
  have hh : Function.Surjective h := (QuotientGroup.mk'_surjective _).comp hg
  have hhk : h.ker = pPrimeCore 2 ↥R := by
    rw [← hcomap]
    ext x
    simp [h, QuotientGroup.eq_one_iff]
  exact ⟨n, CentralizerBar z, inferInstance, f.range, hn, hsp.cover,
    ⟨(QuotientGroup.quotientMulEquivOfEq hhk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective h hh)⟩⟩

end Embed

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
