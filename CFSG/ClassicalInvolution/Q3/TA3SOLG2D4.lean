module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDefs
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQuot
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

theorem exists_perfect_q8_of_sl2 {X : Type} [Group X] {t : X} {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (I : Subgroup (Subgroup.centralizer ({t} : Set X))) (e : I ≃* SL(2, F)) :
    ∃ H : Subgroup X, H = I.map (Subgroup.centralizer ({t} : Set X)).subtype ∧
      Group.IsPerfect H ∧ ∃ φ : QuaternionGroup 2 →* X, Function.Injective φ ∧ ∀ x, φ x ∈ H := by
  let e' : ↥(I.map (Subgroup.centralizer ({t} : Set X)).subtype) ≃* SL(2, F) :=
    (Subgroup.equivMapOfInjective I _
      (Subgroup.centralizer ({t} : Set X)).subtype_injective).symm.trans e
  obtain ⟨φ, hφ, hφH, -⟩ := exists_q8_of_mulEquiv_sl2 hF _ e'
  exact ⟨_, rfl, isPerfect_of_equiv_sl2 h4 e', φ, hφ, hφH⟩

theorem datum_not_fourGenerated_of_shape {X : Type} [Group X] [Finite X] {R : Subgroup X}
    {S : Sylow 2 R} {t : X} (hD : TightDatum R S t) {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (Sh : Shape ↥(Subgroup.centralizer ({t} : Set X)) F₁ F₂)
    (ho₁ : Odd (Nat.card F₁)) (ho₂ : Odd (Nat.card F₂)) (h4₁ : 4 ≤ Nat.card F₁)
    (h4₂ : 4 ≤ Nat.card F₂) : ¬ TwoSubgroupsFourGenerated X := by
  set C := Subgroup.centralizer ({t} : Set X)
  obtain ⟨H₁, rfl, hP₁, φ₁, hi₁, hr₁⟩ := exists_perfect_q8_of_sl2 ho₁ h4₁ Sh.I₁ Sh.e₁
  obtain ⟨H₂, rfl, hP₂, φ₂, hi₂, hr₂⟩ := exists_perfect_q8_of_sl2 ho₂ h4₂ Sh.I₂ Sh.e₂
  have hcomm : ∀ a ∈ Sh.I₁.map C.subtype, ∀ b ∈ Sh.I₂.map C.subtype, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Sh.comm a ha b hb)
  exact datum_not_fourGenerated hD (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) hcomm
    φ₁ φ₂ hi₁ hi₂ hr₁ hr₂

theorem odd_four_le_of_card {F : Type} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {k : ℕ} (hk : 1 ≤ k) (hF : Nat.card F = (p ^ f) ^ k) : Odd (Nat.card F) ∧ 4 ≤ Nat.card F := by
  rw [hF]
  refine ⟨((hp.eq_two_or_odd').resolve_left hp2).pow.pow, ?_⟩
  calc 4 ≤ p ^ f := by omega
    _ ≤ (p ^ f) ^ k := Nat.le_self_pow (by omega) _

theorem noDatumG2D4 : NoDatumG2D4 := by
  intro X _ _ _ t p f ht hp hp2 h5 hce hF ⟨R, S, z, hD⟩
  have hm : LieModel X t 0 p f :=
    Or.inr (Or.inl ⟨rfl, by rcases ht with rfl | rfl <;> decide, hce⟩)
  rcases ht with rfl | rfl
  · obtain ⟨F, _, _, Sh, hcard, -⟩ := GH74.GLS.IVK.GHInv.exists_shape_G2 hp hp2 hm z hD.order
    obtain ⟨ho, h4⟩ := odd_four_le_of_card hp hp2 h5 le_rfl (hcard.trans (pow_one _).symm)
    exact datum_not_fourGenerated_of_shape hD Sh ho ho h4 h4 hF
  · obtain ⟨F₁, F₂, _, _, _, _, Sh, hc₁, hc₂, -⟩ :=
      GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hm z hD.order
    obtain ⟨ho₁, h4₁⟩ := odd_four_le_of_card hp hp2 h5 (by norm_num) hc₁
    obtain ⟨ho₂, h4₂⟩ := odd_four_le_of_card hp hp2 h5 le_rfl (hc₂.trans (pow_one _).symm)
    exact datum_not_fourGenerated_of_shape hD Sh ho₁ ho₂ h4₁ h4₂ hF

end CFSG.ClassicalInvolution.Q3.TA3
