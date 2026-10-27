module

public import CFSG.ClassicalInvolution.AschTight.S19TStmt
public import CFSG.ClassicalInvolution.AschTight.S19TBr1
public import CFSG.ClassicalInvolution.AschTight.S19MCenter
public import CFSG.ClassicalInvolution.AschTight.S19MLift

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups

theorem nonempty_equiv_sl2_of_mem {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Type} [Group E]
    {Ω : Set (Subgroup E)} {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}
    (M : Ih8Model p f Ω t k e) (ht : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3))
    {L : Subgroup E} (hL : L ∈ Ω) : Nonempty (↥L ≃* SL(2, GaloisField p f)) := by
  have hG2 : t ≠ .G2 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have htag : S1911.IsT6Tag t k := by
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain rfl := M.exp_eq_f hD4
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff L).mp hL
  obtain ⟨ι₀⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  have : Finite (modelUniv t k p e Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (ih8_isFundTag_mf M.isFundTag) M.admissible
  have hodd := S19M.odd_natCard_ker M.ker_le_center
    (S19M.factM3 p e Fact.out hp2 t k htag M.admissible)
  have hinj : Function.Injective (M.ψ.domRestrict R) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgk : (g : (modelUniv t k p e Fact.out).K) ∈ M.ψ.ker := hg
    have hgc := M.ker_le_center hgk
    have hcen : ι₀ g ∈ Subgroup.center SL(2, GaloisField p e) := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨b', rfl⟩ := ι₀.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp hgc (b' : (modelUniv t k p e Fact.out).K))
    obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    have hr2 : r * r = 1 := by simpa [sq] using hr
    have hsq : ι₀ (g * g) = 1 := by
      rw [map_mul]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hrg, Matrix.SpecialLinearGroup.coe_one,
        ← map_mul, hr2, map_one]
    have hg2 : g * g = 1 := ι₀.injective (by rw [hsq, map_one])
    have hk2 : (⟨g, hgk⟩ : M.ψ.ker) * ⟨g, hgk⟩ = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hg2)
    have hord : orderOf (⟨g, hgk⟩ : M.ψ.ker) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hk2])
    have hordo : Odd (orderOf (⟨g, hgk⟩ : M.ψ.ker)) :=
      Odd.of_dvd_nat hodd (orderOf_dvd_natCard _)
    have h1 : orderOf (⟨g, hgk⟩ : M.ψ.ker) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact h
      · rw [h] at hordo
        exact absurd hordo (by decide)
    have := congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
    exact Subtype.ext this
  refine ⟨((MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range M.ψ (K := R)))).symm.trans ι₀⟩

theorem exists_conj_of_fixes (hFL : FactFL) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) {E : Type} [Group E] [Finite E] [IsSimpleGroup E] {Ω : Set (Subgroup E)}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}
    (ht : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) (M : Ih8Model p f Ω t k e)
    {L : Subgroup E} (hL : L ∈ Ω) (φ : MulAut E) (hφ2 : φ * φ = 1)
    (hφL : L.map φ.toMonoidHom = L)
    (hab : ∀ P : Subgroup E, IsPGroup 2 P → P ≤ L → (∀ x ∈ P, φ x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hc : ∃ c ∈ Subgroup.centralizer (L : Set E), φ c = c ∧ c * c ≠ 1) :
    ∃ y : E, φ = MulAut.conj y := by
  obtain ⟨ι⟩ := nonempty_equiv_sl2_of_mem hp2 M ht hL
  let φL : ↥L ≃* ↥L := (φ.subgroupMap L).trans (MulEquiv.subgroupCongr hφL)
  have hφL : ∀ x : ↥L, ((φL x : ↥L) : E) = φ x := fun _ => rfl
  let β : MulAut SL(2, GaloisField p f) := (ι.symm.trans φL).trans ι
  have hβ : ∀ b, β b = ι (φL (ι.symm b)) := fun _ => rfl
  have hφφ : ∀ w : E, φ (φ w) = w := fun w => by
    have := congrArg (fun ψ : MulAut E => ψ w) hφ2
    simpa [MulAut.mul_apply] using this
  have hβ2 : β * β = 1 := by
    ext b
    rw [MulAut.mul_apply, hβ, hβ, MulAut.one_apply, MulEquiv.symm_apply_apply]
    rw [show φL (φL (ι.symm b)) = ι.symm b from Subtype.ext (by rw [hφL, hφL, hφφ]),
      MulEquiv.apply_symm_apply]
  have hβab : ∀ P : Subgroup SL(2, GaloisField p f), IsPGroup 2 P → (∀ x ∈ P, β x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro P hP hfix x hx y hy
    have hQ : IsPGroup 2 ((P.map ι.symm.toMonoidHom).map L.subtype) := (hP.map _).map _
    have hQL : (P.map ι.symm.toMonoidHom).map L.subtype ≤ L := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hQfix : ∀ w ∈ (P.map ι.symm.toMonoidHom).map L.subtype, φ w = w := by
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have h1 := hfix v hv
      rw [hβ] at h1
      have h2 : φL (ι.symm v) = ι.symm v := by
        rw [← MulEquiv.symm_apply_apply ι (φL (ι.symm v)), h1]
      exact congrArg Subtype.val h2
    have h := hab _ hQ hQL hQfix _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    apply ι.symm.injective
    apply Subtype.ext
    simpa using h
  obtain ⟨G, hG⟩ := exists_semilinHom_refl_of_fixes_abelian hp2 h5 β hβ2 hβab
  have hyp : ∀ x : ↥L,
      ((ι.symm (semilinHom G (RingEquiv.refl _) (ι x)) : ↥L) : E) = φ x := by
    intro x
    rw [← hG, hβ, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, hφL]
  exact (hFL p f hp2 h5 E Ω t k e ht ⟨M⟩ L hL φ ⟨ι, G, hyp⟩).2 hφ2 hc

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
