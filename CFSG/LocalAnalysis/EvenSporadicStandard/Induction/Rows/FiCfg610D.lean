module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma36Q

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.QuasithinUnique.Id2519 CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem mem_conjugate_iff' {J : Subgroup H} {g x : H} :
    x ∈ CFSG.conjugate J g ↔ g * x * g⁻¹ ∈ J := by
  unfold CFSG.conjugate
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩

theorem conjugate_conjugate' (J : Subgroup H) (a b : H) :
    CFSG.conjugate (CFSG.conjugate J a) b = CFSG.conjugate J (a * b) := by
  ext x
  rw [mem_conjugate_iff', mem_conjugate_iff', mem_conjugate_iff']
  have : a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ := by group
  rw [this]

end CFSG.EvenSporadicStandard.Induction

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {H : Type} [Group H]

theorem IsCompIn.not_commute {A X : Subgroup H} (hA : IsCompIn A X) :
    ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro h
  obtain ⟨a, b, hab⟩ := hA.isQuasisimple.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (h a' a'.2 b' b'.2)

variable [Finite H]

theorem IsCompIn.eq_of_le {A B X : Subgroup H} (hA : IsCompIn A X) (hB : IsCompIn B X)
    (hle : A ≤ B) : A = B := by
  by_contra hne
  exact hA.not_commute fun a ha b hb => hA.commute_of_ne hB hne a ha b (hle hb)

theorem IsCompIn.eq_or_eq_of_le_sup {A J₁ J₂ X : Subgroup H} (hA : IsCompIn A X)
    (h₁ : IsCompIn J₁ X) (h₂ : IsCompIn J₂ X) (hle : A ≤ J₁ ⊔ J₂) : A = J₁ ∨ A = J₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have c1 := hA.commute_of_ne h₁ hn1
  have c2 := hA.commute_of_ne h₂ hn2
  have hcen : ∀ a ∈ A, J₁ ⊔ J₂ ≤ centralizer ({a} : Set H) := by
    intro a ha
    refine sup_le (fun b hb => ?_) (fun b hb => ?_)
    · exact mem_centralizer_singleton_iff.2 (c1 a ha b hb).symm
    · exact mem_centralizer_singleton_iff.2 (c2 a ha b hb).symm
  refine hA.not_commute fun a ha b hb => ?_
  exact (mem_centralizer_singleton_iff.1 (hcen a ha (hle hb))).symm

end CFSG.EvenSporadicStandard.Solomon78

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.QuasithinUnique.Id2519 CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem conjugate_eq_of_two_alternatives {X Kh J J' : Subgroup H} {t y : H}
    (hJ : IsCompIn J X) (htX : t ∈ X) (hyX : y ∈ X) (hty : y * t = t * y)
    (ht2 : t * t = 1) (hJeq : Kh = J ⊔ CFSG.conjugate J t)
    (hJ' : IsCompIn J' X) (hne' : J' ≠ CFSG.conjugate J' y)
    (heq' : Kh = J' ⊔ CFSG.conjugate J' y) :
    CFSG.conjugate J y = CFSG.conjugate J t := by
  have hJt : IsCompIn (CFSG.conjugate J t) X := hJ.map_conj (X.inv_mem htX)
  have hJ'y : IsCompIn (CFSG.conjugate J' y) X := hJ'.map_conj (X.inv_mem hyX)
  have hJ'le : J' ≤ J ⊔ CFSG.conjugate J t := hJeq ▸ heq' ▸ le_sup_left
  have hJ'yle : CFSG.conjugate J' y ≤ J ⊔ CFSG.conjugate J t := hJeq ▸ heq' ▸ le_sup_right
  have h1 := hJ'.eq_or_eq_of_le_sup hJ hJt hJ'le
  have h2 := hJ'y.eq_or_eq_of_le_sup hJ hJt hJ'yle
  rcases h1 with rfl | rfl
  · rcases h2 with h2 | h2
    · exact absurd h2.symm hne'
    · exact h2
  · rcases h2 with h2 | h2
    ·
      have h3 : CFSG.conjugate (CFSG.conjugate J y) t = J := by
        rw [conjugate_conjugate', hty, ← conjugate_conjugate']
        exact h2
      have h4 := congrArg (fun S => CFSG.conjugate S t) h3
      simp only [conjugate_conjugate', mul_assoc, ht2, mul_one] at h4
      exact h4
    · exact absurd h2.symm hne'

theorem false_of_three_swaps {X Kh : Subgroup H} {t u : H} (htX : t ∈ X) (huX : u ∈ X)
    (hut : u * t = t * u) (ht2 : t * t = 1)
    (hBt : ∃ J, IsCompIn J X ∧ J ≠ CFSG.conjugate J t ∧ Kh = J ⊔ CFSG.conjugate J t)
    (hBu : ∃ J, IsCompIn J X ∧ J ≠ CFSG.conjugate J u ∧ Kh = J ⊔ CFSG.conjugate J u)
    (hBut : ∃ J, IsCompIn J X ∧ J ≠ CFSG.conjugate J (u * t) ∧
      Kh = J ⊔ CFSG.conjugate J (u * t)) : False := by
  obtain ⟨J, hJ, hJne, hJeq⟩ := hBt
  obtain ⟨J₁, hJ₁, hne₁, heq₁⟩ := hBu
  obtain ⟨J₂, hJ₂, hne₂, heq₂⟩ := hBut
  have hutX : u * t ∈ X := X.mul_mem huX htX
  have hutt : (u * t) * t = t * (u * t) := by
    calc (u * t) * t = (t * u) * t := by rw [← hut]
      _ = t * (u * t) := by group
  have s1 : CFSG.conjugate J u = CFSG.conjugate J t :=
    conjugate_eq_of_two_alternatives hJ htX huX hut ht2 hJeq hJ₁ hne₁ heq₁
  have s2 : CFSG.conjugate J (u * t) = CFSG.conjugate J t :=
    conjugate_eq_of_two_alternatives hJ htX hutX hutt ht2 hJeq hJ₂ hne₂ heq₂
  have s3 : CFSG.conjugate J (u * t) = J := by
    rw [← conjugate_conjugate', s1, conjugate_conjugate', ht2, conjugate_one]
  exact hJne (s3.symm.trans s2)

section Dichotomy

theorem isCompIn_of_alternative_A
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hZ : center H = ⊥) {u₀ t u : H}
    (hu₀ : orderOf u₀ = 2) (hB : BTheoremAt u₀) {K₀ : Subgroup H}
    (hKq : CFSG.IsQuasisimple ↥K₀) (hK₀X : K₀ ≤ centralizer ({u₀} : Set H))
    (ht2 : orderOf t = 2) (hu2 : orderOf u = 2) (hut2 : orderOf (u * t) = 2)
    (hut : u * t = t * u) (htX : t ∈ centralizer ({u₀} : Set H))
    (huX : u ∈ centralizer ({u₀} : Set H)) (hK₀t : K₀ ≤ centralizer ({t} : Set H))
    (hK₀u : K₀ ≤ centralizer ({u} : Set H)) (hK₀ut : K₀ ≤ centralizer ({u * t} : Set H))
    (hnt : (K₀.subgroupOf (centralizer ({u₀} : Set H) ⊓ centralizer ({t} : Set H))).Normal)
    (hnu : (K₀.subgroupOf (centralizer ({u₀} : Set H) ⊓ centralizer ({u} : Set H))).Normal)
    (hnut : (K₀.subgroupOf (centralizer ({u₀} : Set H) ⊓ centralizer ({u * t} : Set H))).Normal)
    (h12 : ∀ M : Subgroup H, IsCompIn M (centralizer ({u₀} : Set H)) → K₀ ≤ M →
      CFSG.conjugate M t = M → CFSG.conjugate M u = M → M = K₀) :
    IsCompIn K₀ (centralizer ({u₀} : Set H)) := by
  classical
  set X : Subgroup H := centralizer ({u₀} : Set H) with hX
  set Kh : Subgroup H := ⨆ g ∈ oddLayer X, CFSG.conjugate K₀ g with hKh
  have hK₀Kh : K₀ ≤ Kh :=
    le_iSup₂_of_le (f := fun g (_ : g ∈ oddLayer X) => CFSG.conjugate K₀ g) 1 (one_mem _)
      (by rw [conjugate_one])
  have dich : ∀ x : H, x ∈ X → orderOf x = 2 → K₀ ≤ centralizer ({x} : Set H) →
      (K₀.subgroupOf (X ⊓ centralizer ({x} : Set H))).Normal →
      (IsCompIn Kh X ∧ x ∈ normalizer (Kh : Set H)) ∨
        ∃ J, IsCompIn J X ∧ J ≠ CFSG.conjugate J x ∧ Kh = J ⊔ CFSG.conjugate J x := by
    intro x hxX hx2 hK₀x hn
    rcases layer_dichotomy_of_quasisimple_Q hkp hZ hxX hx2 hu₀ (B := K₀) hK₀X hK₀x hKq hn with
      ⟨hA, hxn⟩ | ⟨J, hJ, hJne, hJeq, -⟩
    · exact Or.inl ⟨hB _ hA, hxn⟩
    · exact Or.inr ⟨J, hB J hJ, hJne, hJeq⟩
  have claimA : ∀ {y : H}, y ∈ X → IsCompIn Kh X →
      (∃ J, IsCompIn J X ∧ J ≠ CFSG.conjugate J y ∧ Kh = J ⊔ CFSG.conjugate J y) → False := by
    intro y hyX hKhc ⟨J, hJ, hJne, hJeq⟩
    have hJy : IsCompIn (CFSG.conjugate J y) X := hJ.map_conj (X.inv_mem hyX)
    have h1 : J = Kh := hJ.eq_of_le hKhc (by rw [hJeq]; exact le_sup_left)
    have h2 : CFSG.conjugate J y = Kh := hJy.eq_of_le hKhc (by rw [hJeq]; exact le_sup_right)
    exact hJne (h1.trans h2.symm)
  have hutX : u * t ∈ X := X.mul_mem huX htX
  have t2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
  have dt := dich t htX ht2 hK₀t hnt
  have du := dich u huX hu2 hK₀u hnu
  have dut := dich (u * t) hutX hut2 hK₀ut hnut
  have key : IsCompIn Kh X ∧ t ∈ normalizer (Kh : Set H) ∧ u ∈ normalizer (Kh : Set H) := by
    rcases dt with ⟨hAt, htn⟩ | hBt
    · rcases du with ⟨-, hun⟩ | hBu
      · exact ⟨hAt, htn, hun⟩
      · exact (claimA huX hAt hBu).elim
    · rcases du with ⟨hAu, -⟩ | hBu
      · exact (claimA htX hAu hBt).elim
      · rcases dut with ⟨hAut, -⟩ | hBut
        · exact (claimA htX hAut hBt).elim
        · exact (false_of_three_swaps htX huX hut t2 hBt hBu hBut).elim
  obtain ⟨hKhc, htn, hun⟩ := key
  have hct : CFSG.conjugate Kh t = Kh :=
    Solomon78.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ htn)
  have hcu : CFSG.conjugate Kh u = Kh :=
    Solomon78.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ hun)
  exact h12 Kh hKhc hK₀Kh hct hcu ▸ hKhc

end Dichotomy

end CFSG.EvenSporadicStandard.Induction
