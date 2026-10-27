module

public import CFSG.FeitThompson.Local.GeneralLinearTwoPrimeFieldOrder
public import CFSG.FeitThompson.Foundations.FiniteHomImageOrder
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

noncomputable section

variable {p n k : ℕ}

def addEquivEquivZModLinearEquiv (n : ℕ) (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod n) V] [Module (ZMod n) W] : (V ≃+ W) ≃ (V ≃ₗ[ZMod n] W) where
  toFun e := { e.toAddMonoidHom.toZModLinearMap n with
    invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv }
  invFun e := e.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem addEquivEquivZModLinearEquiv_apply (n : ℕ) {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod n) V] [Module (ZMod n) W] (e : V ≃+ W) (v : V) :
    addEquivEquivZModLinearEquiv n V W e v = e v := (rfl)

@[simp]
theorem addEquivEquivZModLinearEquiv_symm_apply (n : ℕ) {V W : Type*} [AddCommGroup V]
    [AddCommGroup W] [Module (ZMod n) V] [Module (ZMod n) W] (e : V ≃ₗ[ZMod n] W) (v : V) :
    (addEquivEquivZModLinearEquiv n V W).symm e v = e v := (rfl)

def mulEquivMultiplicativeSubmodule (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (T : Subgroup (Multiplicative V)) :
    ↥T ≃* Multiplicative ↥(AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup' T)) where
  toFun x := Multiplicative.ofAdd ⟨Multiplicative.toAdd x.1, x.2⟩
  invFun x := ⟨Multiplicative.ofAdd (Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem mulEquivMultiplicativeSubmodule_apply_coe (p : ℕ) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (T : Subgroup (Multiplicative V)) (x : ↥T) :
    ((Multiplicative.toAdd (mulEquivMultiplicativeSubmodule p T x) : _) : V) =
      Multiplicative.toAdd (x : Multiplicative V) := (rfl)

theorem nonempty_linearEquiv_of_natCard_eq_pow (p n : ℕ) [Fact p.Prime] (V : Type*)
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (h : Nat.card V = p ^ n) :
    Nonempty (V ≃ₗ[ZMod p] (Fin n → ZMod p)) := by
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hr : finrank (ZMod p) V = n := by
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [h, Nat.card_zmod] at h2
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h2).symm
  exact ⟨((finBasis (ZMod p) V).reindex (finCongr hr)).equivFun⟩

theorem natCard_mulAut_eq_natCard_GL [Fact p.Prime] {G : Type*} [Group G]
    (e : G ≃* Multiplicative (Fin n → ZMod p)) :
    Nat.card (MulAut G) = Nat.card (GL (Fin n) (ZMod p)) := by
  refine (Nat.card_congr (((MulAut.congr e).trans (MulAutMultiplicative _)).toEquiv.trans
    (Multiplicative.ofAdd.symm.trans
      (addEquivEquivZModLinearEquiv p (Fin n → ZMod p) (Fin n → ZMod p))))).trans ?_
  exact (Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) _)).toEquiv).symm

theorem nonempty_mulEquiv_of_subgroup [Fact p.Prime] {G : Type*} [Group G]
    (ψ : G ≃* Multiplicative (Fin n → ZMod p)) (L : Subgroup G) (hL : Nat.card L = p ^ k) :
    Nonempty (↥L ≃* Multiplicative (Fin k → ZMod p)) := by
  set T := Subgroup.map (ψ : G →* Multiplicative (Fin n → ZMod p)) L with hT
  have hcardT : Nat.card ↥T = p ^ k := by
    rw [hT, Subgroup.card_map_of_injective ψ.injective, hL]
  have hcardS : Nat.card ↥(AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup' T)) = p ^ k := by
    rw [← hcardT]; exact Nat.card_congr (Equiv.refl _)
  have : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  obtain ⟨e⟩ := nonempty_linearEquiv_of_natCard_eq_pow p k _ hcardS
  exact ⟨((MulEquiv.subgroupMap ψ L).trans (mulEquivMultiplicativeSubmodule p T)).trans
    (AddEquiv.toMultiplicative e.toAddEquiv)⟩

variable {P : Type*} [Group P] {D E : Subgroup P}

def conjOnNormalized (D : Subgroup P) (hEN : E ≤ Subgroup.normalizer (D : Set P)) :
    ↥E →* MulAut ↥D :=
  D.normalizerMonoidHom.comp (Subgroup.inclusion hEN)

theorem conjOnNormalized_apply_coe (hEN : E ≤ Subgroup.normalizer (D : Set P)) (x : ↥E)
    (d : ↥D) : ((conjOnNormalized D hEN x d : ↥D) : P) = (x : P) * (d : P) * (x : P)⁻¹ :=
  D.normalizerMonoidHom_apply_apply_coe _ d

theorem ker_conjOnNormalized (hEN : E ≤ Subgroup.normalizer (D : Set P)) :
    (conjOnNormalized D hEN).ker = (Subgroup.centralizer (D : Set P)).subgroupOf E := by
  rw [conjOnNormalized, ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

theorem mem_inf_centralizer_iff_mul_comm {x : P} :
    x ∈ E ⊓ Subgroup.centralizer (D : Set P) ↔ x ∈ E ∧ ∀ d ∈ D, x * d = d * x := by
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  exact and_congr_right' ⟨fun h d hd => (h d hd).symm, fun h d hd => (h d hd).symm⟩

theorem exists_elementaryAbelian_rank_two_le_inf_centralizer [Fact p.Prime] [Finite P]
    (hD : Nonempty (↥D ≃* Multiplicative (Fin 2 → ZMod p)))
    (hE : Nonempty (↥E ≃* Multiplicative (Fin 3 → ZMod p)))
    (hEN : E ≤ Subgroup.normalizer (D : Set P)) :
    ∃ K : Subgroup P, K ≤ E ⊓ Subgroup.centralizer (D : Set P) ∧
      Nonempty (↥K ≃* Multiplicative (Fin 2 → ZMod p)) := by
  obtain ⟨φD⟩ := hD
  obtain ⟨ψ⟩ := hE
  have hp : p.Prime := Fact.out
  set f := conjOnNormalized D hEN with hf
  have hcardE : Nat.card ↥E = p ^ 3 := by rw [Nat.card_congr ψ.toEquiv]; simp
  have hdvdE : Nat.card ↥f.range ∣ p ^ 3 := hcardE ▸ Subgroup.card_range_dvd f
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvdE
  have hdvdGL : p ^ j ∣ Nat.card (GL (Fin 2) (ZMod p)) := by
    rw [← natCard_mulAut_eq_natCard_GL φD, ← hj]
    exact natCard_range_dvd_natCard_codomain f
  have hj1 : j ≤ 1 := (pow_dvd_card_GL_two_zmod_iff p).1 hdvdGL
  have hmul : Nat.card ↥f.range * Nat.card ↥f.ker = p ^ 3 :=
    hcardE ▸ natCard_range_mul_natCard_ker f
  have hker : Nat.card ↥f.ker = p ^ (3 - j) := by
    have hpos : 0 < p ^ j := pow_pos hp.pos _
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← pow_add, Nat.add_sub_cancel' (by omega), ← hj, hmul]
  have hp2 : p ^ 2 ∣ Nat.card ↥f.ker := by
    rw [hker]; exact pow_dvd_pow p (by omega)
  obtain ⟨K₁, hK₁⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥f.ker) p (n := 2) hp2
  set K₂ : Subgroup ↥E := Subgroup.map f.ker.subtype K₁ with hK₂
  have hcardK₂ : Nat.card ↥K₂ = p ^ 2 := by
    rw [hK₂, Subgroup.card_map_of_injective f.ker.subtype_injective, hK₁]
  refine ⟨Subgroup.map E.subtype K₂, ?_, ?_⟩
  · refine le_inf (Subgroup.map_subtype_le K₂) ?_
    have h1 : K₂ ≤ (Subgroup.centralizer (D : Set P)).subgroupOf E := by
      rw [← ker_conjOnNormalized hEN, ← hf]
      exact hK₂ ▸ Subgroup.map_subtype_le K₁
    calc Subgroup.map E.subtype K₂
        ≤ Subgroup.map E.subtype ((Subgroup.centralizer (D : Set P)).subgroupOf E) :=
          Subgroup.map_mono h1
      _ ≤ Subgroup.centralizer (D : Set P) := Subgroup.map_comap_le _ _
  · obtain ⟨e⟩ := nonempty_mulEquiv_of_subgroup ψ K₂ hcardK₂
    exact ⟨(Subgroup.equivMapOfInjective K₂ E.subtype E.subtype_injective).symm.trans e⟩

end

end CFSG.FeitThompson
