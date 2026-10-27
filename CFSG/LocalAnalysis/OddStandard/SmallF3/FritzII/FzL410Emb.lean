module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Ev
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open _root_.Certificates

variable {G : Type} [Group G]

structure Fz410Coord (P : Subgroup G) (emb : FzL410.A → G) : Prop where
  mul : ∀ a b, emb (a + b) = emb a * emb b
  inj : ∀ a b, emb a = emb b → a = b
  mem : ∀ g, g ∈ P ↔ ∃ a, emb a = g

structure Fz410EmbBase (P : Subgroup G) (rho : G) (emb : FzL410.A → G) : Prop
    extends Fz410Coord P emb where
  cj_rho : ∀ a, rho * emb a * rho⁻¹ = emb (FzL410.rho a)

structure Fz410EmbT (P : Subgroup G) (rho t : G) (emb : FzL410.A → G) : Prop
    extends Fz410EmbBase P rho emb where
  cj_t : ∀ a, t * emb a * t⁻¹ = emb (FzL410.tt a)

structure Fz410Emb (P : Subgroup G) (t s lam rho : G) (emb : FzL410.A → G) : Prop
    extends Fz410EmbT P rho t emb where
  cj_s : ∀ a, s * emb a * s⁻¹ = emb (FzL410.ss a)
  cj_lam : ∀ a, lam * emb a * lam⁻¹ = emb (FzL410.ll a)

theorem Fz410Coord.of_iso {P : Subgroup G} (φ : ↥P ≃* Multiplicative FzL410.A) :
    ∃ emb : FzL410.A → G, Fz410Coord P emb := by
  refine ⟨fun a => ((φ.symm (Multiplicative.ofAdd a) : ↥P) : G), ?_, ?_, ?_⟩
  · intro a b
    simp only [ofAdd_add, map_mul, Subgroup.coe_mul]
  · intro a b h
    have h1 : φ.symm (Multiplicative.ofAdd a) = φ.symm (Multiplicative.ofAdd b) := Subtype.ext h
    exact Multiplicative.ofAdd.injective (φ.symm.injective h1)
  · intro g
    constructor
    · intro hg
      refine ⟨Multiplicative.toAdd (φ ⟨g, hg⟩), ?_⟩
      simp
    · rintro ⟨a, rfl⟩
      exact (φ.symm (Multiplicative.ofAdd a)).2

namespace Fz410Coord

variable {P : Subgroup G} {emb : FzL410.A → G} (E : Fz410Coord P emb)

include E

theorem emb_zero : emb 0 = 1 := by
  have h := E.mul 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := emb 0) (by rw [mul_one]; exact h.symm)

theorem emb_neg (a : FzL410.A) : emb (-a) = (emb a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h0 : (-a + a : FzL410.A) = 0 := neg_add_cancel a
  rw [← E.mul, h0]
  exact E.emb_zero

theorem emb_nsmul (n : ℕ) (a : FzL410.A) : emb (n • a) = (emb a) ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact E.emb_zero
  | succ n ih => rw [succ_nsmul, E.mul, ih, pow_succ]

theorem emb_mem (a : FzL410.A) : emb a ∈ P := (E.mem _).mpr ⟨a, rfl⟩

theorem emb_comm (a b : FzL410.A) : emb a * emb b = emb b * emb a := by
  rw [← E.mul, ← E.mul, add_comm]

theorem P_comm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, rfl⟩ := (E.mem a).mp ha
  obtain ⟨y, rfl⟩ := (E.mem b).mp hb
  exact E.emb_comm x y

theorem exists_act {g : G} (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) :
    ∃ σ : FzL410.A →+ FzL410.A, ∀ a, g * emb a * g⁻¹ = emb (σ a) := by
  have hex : ∀ a, ∃ b, emb b = g * emb a * g⁻¹ := fun a => (E.mem _).mp (hg _ (E.emb_mem a))
  choose f hf using hex
  have hadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    apply E.inj
    rw [E.mul, hf, hf, hf, E.mul]
    group
  exact ⟨AddMonoidHom.mk' f hadd, fun a => (hf a).symm⟩

theorem comp {ψ : FzL410.A →+ FzL410.A} (hψ : Function.Injective ψ) :
    Fz410Coord P (fun a => emb (ψ a)) := by
  have hsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψ
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    simp only [map_add]
    exact E.mul _ _
  · intro a b h
    exact hψ (E.inj _ _ h)
  · intro g
    constructor
    · intro hg
      obtain ⟨b, rfl⟩ := (E.mem g).mp hg
      obtain ⟨a, rfl⟩ := hsurj b
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact E.emb_mem _

end Fz410Coord

end CFSG.OddStandard.SmallF3.FritzII
