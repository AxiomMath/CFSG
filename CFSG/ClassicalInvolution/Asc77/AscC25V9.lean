module

public import CFSG.ClassicalInvolution.Asc77.AscT7TFieldPart
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Ext

variable {G A : Type*} [Group G] [CommGroup A]

theorem exists_hom_extension_of_index_two (H N : Subgroup G) (hNH : N ≤ H) (t : G)
    (ht2 : t * t = 1) (hcov : ∀ g ∈ H, g ∈ N ∨ g * t ∈ N)
    (hconj : ∀ n ∈ N, t * n * t ∈ N) (ϕ₀ : N →* A)
    (hinv : ∀ (n : G) (hn : n ∈ N), ϕ₀ ⟨t * n * t, hconj n hn⟩ = ϕ₀ ⟨n, hn⟩) :
    ∃ ϕ : H →* A, ∀ (n : G) (hn : n ∈ N), ϕ ⟨n, hNH hn⟩ = ϕ₀ ⟨n, hn⟩ := by
  classical
  let F : H → A := fun g =>
    if hg : (g : G) ∈ N then ϕ₀ ⟨g, hg⟩
    else ϕ₀ ⟨(g : G) * t, (hcov g g.2).resolve_left hg⟩
  have hF1 : ∀ (g : H) (hg : (g : G) ∈ N), F g = ϕ₀ ⟨g, hg⟩ := fun g hg => by
    simp [F, hg]
  have hF2 : ∀ (g : H) (hg : (g : G) ∉ N) (hgt : (g : G) * t ∈ N),
      F g = ϕ₀ ⟨(g : G) * t, hgt⟩ := fun g hg hgt => by
    simp [F, hg]
  have hNm : ∀ {x y : G}, x ∈ N → x * y ∈ N → y ∈ N := fun hx hxy => by
    have := N.mul_mem (N.inv_mem hx) hxy
    simpa using this
  have hNm' : ∀ {x y : G}, y ∈ N → x * y ∈ N → x ∈ N := fun hy hxy => by
    have := N.mul_mem hxy (N.inv_mem hy)
    simpa using this
  have e1 : ∀ x y : G, x * t * (t * y * t) = x * y * t := fun x y => by
    calc x * t * (t * y * t) = x * (t * t) * y * t := by simp only [mul_assoc]
      _ = x * y * t := by rw [ht2, mul_one]
  have e2 : ∀ y : G, t * (y * t) * t = t * y := fun y => by
    calc t * (y * t) * t = t * y * (t * t) := by simp only [mul_assoc]
      _ = t * y := by rw [ht2, mul_one]
  have e3 : ∀ x y : G, x * t * (t * y) = x * y := fun x y => by
    calc x * t * (t * y) = x * (t * t) * y := by simp only [mul_assoc]
      _ = x * y := by rw [ht2, mul_one]
  have hmul : ∀ g h : H, F (g * h) = F g * F h := by
    intro g h
    by_cases hg : (g : G) ∈ N <;> by_cases hh : (h : G) ∈ N
    · have hgh : ((g * h : H) : G) ∈ N := N.mul_mem hg hh
      rw [hF1 _ hgh, hF1 g hg, hF1 h hh, ← map_mul]
      rfl
    · have hgh : ((g * h : H) : G) ∉ N := fun hc => hh (hNm hg hc)
      have hht : (h : G) * t ∈ N := (hcov h h.2).resolve_left hh
      have hght : ((g * h : H) : G) * t ∈ N := by
        have := N.mul_mem hg hht
        simpa [mul_assoc] using this
      rw [hF2 _ hgh hght, hF1 g hg, hF2 h hh hht, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]
    · have hgh : ((g * h : H) : G) ∉ N := fun hc => hg (hNm' hh hc)
      have hgt : (g : G) * t ∈ N := (hcov g g.2).resolve_left hg
      have hght : ((g * h : H) : G) * t ∈ N := by
        have := N.mul_mem hgt (hconj _ hh)
        rw [e1] at this
        exact this
      rw [hF2 _ hgh hght, hF2 g hg hgt, hF1 h hh]
      have h1 := hinv (h : G) hh
      rw [← h1, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (e1 g h).symm
    · have hgt : (g : G) * t ∈ N := (hcov g g.2).resolve_left hg
      have hht : (h : G) * t ∈ N := (hcov h h.2).resolve_left hh
      have hth : t * (h : G) ∈ N := by
        have := hconj _ hht
        rw [e2] at this
        exact this
      have hgh : (g : G) * h ∈ N := by
        have := N.mul_mem hgt hth
        rw [e3] at this
        exact this
      rw [hF1 _ hgh, hF2 g hg hgt, hF2 h hh hht]
      have h1 := hinv ((h : G) * t) hht
      have h2 : ϕ₀ ⟨t * ((h : G) * t) * t, hconj _ hht⟩ = ϕ₀ ⟨t * (h : G), hth⟩ := by
        congr 1
        apply Subtype.ext
        exact e2 h
      have h3 : ϕ₀ ⟨t * (h : G), hth⟩ = ϕ₀ ⟨(h : G) * t, hht⟩ := h2.symm.trans h1
      rw [← h3, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (e3 g h).symm
  refine ⟨MonoidHom.mk' F hmul, fun n hn => ?_⟩
  exact hF1 ⟨n, hNH hn⟩ hn

end Ext

section FieldChar

abbrev ringAutCommGroup (F : Type) [Field F] [Finite F] : CommGroup (F ≃+* F) :=
  { (inferInstance : Group (F ≃+* F)) with
    mul_comm := CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F }

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem gf_facts (hp : p ≠ 2) (hq : 5 ≤ p ^ f) :
    f ≠ 0 ∧ Nat.card (GaloisField p f) = p ^ f ∧
      CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) ∧
      3 < Nat.card (GaloisField p f) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  refine ⟨hf0, hcard, ⟨p, f, Fact.out,
    (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp, Nat.pos_of_ne_zero hf0, hcard⟩, ?_⟩
  rw [hcard]
  omega

@[expose] noncomputable def fieldChar (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) :
    Subgroup.normalizer (K : Set G) →* (GaloisField p f ≃+* GaloisField p f) :=
  SemidirectProduct.rightHom.comp
    (normalizerToPGammaL2Mod e (gf_facts hp hq).2.1 (gf_facts hp hq).2.2.1
      (gf_facts hp hq).2.2.2)

theorem isPGroup_two_zpowers_of_sq [Finite G] {a : G} (ha2 : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  have h2 : orderOf a ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [sq, ha2])
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact ⟨i, hi⟩

variable [Finite G]

theorem fieldChar_ne_one_of_isFAut (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K R : Subgroup G} {z a : G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (hRK : R ≤ K)
    (hR : IsQuatSub R) (hz : IsUniqueInvolution R z) (hFa : IsFAut R a) (ha2 : a * a = 1)
    (haN : a ∈ Subgroup.normalizer (K : Set G)) : fieldChar hp hq e ⟨a, haN⟩ ≠ 1 :=
  T7T.fieldPart_ne_one_of_isFAut e (gf_facts hp hq).2.1 (gf_facts hp hq).2.2.1
    (gf_facts hp hq).2.2.2 hp hRK hR hz hFa (isPGroup_two_zpowers_of_sq ha2) haN

end FieldChar

end CFSG.ClassicalInvolution.Asc77.C25V
