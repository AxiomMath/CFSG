module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCorePlanes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Assemble

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Planes

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable {E : Subgroup (V ≃ₗ[ZMod 2] V)} {k : ℕ} {X : Fin k → Submodule (ZMod 2) V}
  {ρf : Fin k → (V ≃ₗ[ZMod 2] V)}

def Fset (D : PieceData E X ρf) {p₁ p₂ : Fin k} (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2)
    (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | g ∈ E ∧ expo ρf X p₁ g = expo ρf X p₂ g}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨E.mul_mem ha hb, ?_⟩
    rw [expo_add D hp₁ ha hb, expo_add D hp₂ ha hb, ha', hb']
  one_mem' := by
    refine ⟨E.one_mem, ?_⟩
    rw [expo_eq_zero_of_fix D hp₁ E.one_mem (fun x _ => rfl),
      expo_eq_zero_of_fix D hp₂ E.one_mem (fun x _ => rfl)]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨E.inv_mem ha, ?_⟩
    have h1 : expo ρf X p₁ (a * a⁻¹) = expo ρf X p₁ a + expo ρf X p₁ a⁻¹ :=
      expo_add D hp₁ ha (E.inv_mem ha)
    have h2 : expo ρf X p₂ (a * a⁻¹) = expo ρf X p₂ a + expo ρf X p₂ a⁻¹ :=
      expo_add D hp₂ ha (E.inv_mem ha)
    rw [mul_inv_cancel, expo_eq_zero_of_fix D hp₁ E.one_mem (fun x _ => rfl)] at h1
    rw [mul_inv_cancel, expo_eq_zero_of_fix D hp₂ E.one_mem (fun x _ => rfl)] at h2
    have e1 : expo ρf X p₁ a⁻¹ = - expo ρf X p₁ a := eq_neg_of_add_eq_zero_right h1.symm
    have e2 : expo ρf X p₂ a⁻¹ = - expo ρf X p₂ a := eq_neg_of_add_eq_zero_right h2.symm
    rw [e1, e2, ha']

theorem mem_Fset (D : PieceData E X ρf) {p₁ p₂ : Fin k} (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2)
    (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2) {g : V ≃ₗ[ZMod 2] V} :
    g ∈ Fset D hp₁ hp₂ ↔ g ∈ E ∧ expo ρf X p₁ g = expo ρf X p₂ g := Iff.rfl

theorem expo_eq_one (D : PieceData E X ρf) {p : Fin k} (hp : Module.finrank (ZMod 2) (X p) = 2)
    {e : V ≃ₗ[ZMod 2] V} (he : e ∈ E) (h : ∀ x ∈ X p, e x = ρf p x) :
    expo ρf X p e = 1 :=
  expo_eq_of_pow D hp he (c := 1) (fun x hx => by
    show e x = (ρf p ^ (1 : ℕ)) x
    rw [pow_one_apply]
    exact h x hx)

noncomputable def chi (D : PieceData E X ρf) {p₁ p₂ : Fin k}
    (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2) (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2) :
    E →* Multiplicative (Fin 3) where
  toFun g := Multiplicative.ofAdd (expo ρf X p₁ (g : V ≃ₗ[ZMod 2] V) -
    expo ρf X p₂ (g : V ≃ₗ[ZMod 2] V))
  map_one' := by
    simp only [Subgroup.coe_one]
    rw [expo_eq_zero_of_fix D hp₁ E.one_mem (fun x _ => rfl),
      expo_eq_zero_of_fix D hp₂ E.one_mem (fun x _ => rfl), sub_self]
    rfl
  map_mul' := fun g h => by
    simp only [Subgroup.coe_mul]
    rw [expo_add D hp₁ g.2 h.2, expo_add D hp₂ g.2 h.2, ← ofAdd_add]
    congr 1
    exact add_sub_add_comm _ _ _ _

theorem chi_surjective (D : PieceData E X ρf) {p₁ p₂ : Fin k}
    (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2) (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2)
    {e₁ : V ≃ₗ[ZMod 2] V} (he₁ : e₁ ∈ E) (he₁a : ∀ x ∈ X p₁, e₁ x = ρf p₁ x)
    (he₁b : ∀ x ∈ X p₂, e₁ x = x) :
    Function.Surjective (chi D hp₁ hp₂) := by
  have hval1 : expo ρf X p₁ e₁ = 1 := expo_eq_one D hp₁ he₁ he₁a
  have hval2 : expo ρf X p₂ e₁ = 0 := expo_eq_zero_of_fix D hp₂ he₁ he₁b
  have hchi : chi D hp₁ hp₂ ⟨e₁, he₁⟩ = Multiplicative.ofAdd 1 := by
    show Multiplicative.ofAdd (expo ρf X p₁ e₁ - expo ρf X p₂ e₁) = _
    rw [hval1, hval2, sub_zero]
  have key : ∀ t : Fin 3, ∃ g : E, chi D hp₁ hp₂ g = Multiplicative.ofAdd t := by
    intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 := by fin_cases t <;> simp
    rcases ht with rfl | rfl | rfl
    · exact ⟨1, (map_one _).trans ofAdd_zero.symm⟩
    · exact ⟨⟨e₁, he₁⟩, hchi⟩
    · refine ⟨⟨e₁ * e₁, E.mul_mem he₁ he₁⟩, ?_⟩
      have hm := map_mul (chi D hp₁ hp₂) ⟨e₁, he₁⟩ ⟨e₁, he₁⟩
      rw [hchi, ← ofAdd_add] at hm
      exact hm
  intro y
  obtain ⟨g, hg⟩ := key (Multiplicative.toAdd y)
  exact ⟨g, hg.trans (ofAdd_toAdd y)⟩

theorem card_eq_three_mul (D : PieceData E X ρf) {p₁ p₂ : Fin k}
    (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2) (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2)
    {e₁ : V ≃ₗ[ZMod 2] V} (he₁ : e₁ ∈ E) (he₁a : ∀ x ∈ X p₁, e₁ x = ρf p₁ x)
    (he₁b : ∀ x ∈ X p₂, e₁ x = x) :
    Nat.card E = 3 * Nat.card (Fset D hp₁ hp₂) := by
  have hcard := (chi D hp₁ hp₂).ker.card_mul_index
  have hidx : (chi D hp₁ hp₂).ker.index = 3 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (chi_surjective D hp₁ hp₂ he₁ he₁a he₁b)]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    simp
  have hmap : ((chi D hp₁ hp₂).ker).map E.subtype = Fset D hp₁ hp₂ := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      have hx' : expo ρf X p₁ (x : V ≃ₗ[ZMod 2] V) = expo ρf X p₂ (x : V ≃ₗ[ZMod 2] V) := by
        have := hx
        change Multiplicative.ofAdd (expo ρf X p₁ (x : V ≃ₗ[ZMod 2] V) -
          expo ρf X p₂ (x : V ≃ₗ[ZMod 2] V)) = 1 at this
        rw [ofAdd_eq_one, sub_eq_zero] at this
        exact this
      exact ⟨x.2, hx'⟩
    · rintro ⟨hgE, hg⟩
      refine ⟨⟨g, hgE⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      change Multiplicative.ofAdd (expo ρf X p₁ g - expo ρf X p₂ g) = 1
      rw [hg, sub_self, ofAdd_zero]
  have hcardmap : Nat.card ((chi D hp₁ hp₂).ker.map E.subtype) = Nat.card (chi D hp₁ hp₂).ker :=
    Subgroup.card_map_of_injective Subtype.val_injective
  rw [hmap] at hcardmap
  rw [← hcardmap, hidx] at hcard
  rw [← hcard, mul_comm]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Assemble

end
