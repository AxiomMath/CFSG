module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace WeakClosure

open Subgroup

variable {G : Type} [Group G]

@[expose] def kerIn (M H : Subgroup G) : Subgroup G :=
  ((M.subgroupOf H).normalCore).map H.subtype

theorem mem_kerIn {M H : Subgroup G} {x : G} :
    x ∈ kerIn M H ↔ x ∈ H ∧ ∀ h ∈ H, h * x * h⁻¹ ∈ M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun h hh => ?_⟩
    have := (Subgroup.normalCore_normal _).conj_mem y hy ⟨h, hh⟩
    have h2 := Subgroup.normalCore_le _ this
    simpa [Subgroup.mem_subgroupOf] using h2
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    intro b
    simpa [Subgroup.mem_subgroupOf] using h b b.2

theorem kerIn_le_left (M H : Subgroup G) : kerIn M H ≤ H := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

theorem kerIn_le_right (M H : Subgroup G) : kerIn M H ≤ M := by
  intro x hx
  obtain ⟨hxH, h⟩ := mem_kerIn.1 hx
  simpa using h 1 (one_mem H)

@[expose] noncomputable def minDegree (L : Type*) [Group L] : ℕ :=
  sInf {n | ∃ ρ : Representation (ZMod 2) L (Fin n → ZMod 2), ∃ g : L, ρ g ≠ 1}

@[expose] noncomputable def dOfPrime (p : ℕ) : ℕ := minDegree (Multiplicative (ZMod p))

theorem dOfPrime_eq_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    dOfPrime p = orderOf (2 : ZMod p) := by
  have cyclic_prime_rep_upper_interim (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
      ∃ (ρ : Representation (ZMod 2) (Multiplicative (ZMod p))
          (Fin (orderOf (2 : ZMod p)) → ZMod 2)), ∃ g, ρ g ≠ 1 := by
    set d := orderOf (2 : ZMod p) with hd_def
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h'
      exact hp this
    have hdpos : 0 < d := by
      rw [hd_def, orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
      exact ⟨p - 1, by have := (Fact.out : p.Prime).two_le; omega, ZMod.pow_card_sub_one_eq_one h2ne⟩
    have hpd : p ∣ 2 ^ d - 1 := by
      have h1 : (2 : ZMod p) ^ d = 1 := pow_orderOf_eq_one _
      have h3 : ((2 ^ d : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; exact h1
      rw [ZMod.natCast_eq_natCast_iff] at h3
      exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp h3.symm
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK : Module.finrank (ZMod 2) (GaloisField 2 d) = d := GaloisField.finrank 2 hdpos.ne'
    have hKu : p ∣ Nat.card (GaloisField 2 d)ˣ := by
      rw [Nat.card_units, GaloisField.card 2 d hdpos.ne']
      exact hpd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hKu
    have hζ : IsPrimitiveRoot ((x : (GaloisField 2 d)ˣ) : GaloisField 2 d) p :=
      IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hx)
    obtain ⟨φ, hφ⟩ := ZMod.exists_monoidHom_apply_ne_one ⟨_, hζ⟩ (a := 1) one_ne_zero
    let ψ : Multiplicative (ZMod p) →* Module.End (ZMod 2) (GaloisField 2 d) :=
      (Units.coeHom _).comp ((Units.map (Algebra.lmul (ZMod 2) (GaloisField 2 d)).toMonoidHom).comp φ)
    let b : Module.Basis (Fin d) (ZMod 2) (GaloisField 2 d) := Module.finBasisOfFinrankEq (ZMod 2) _ hK
    let e : GaloisField 2 d ≃ₗ[ZMod 2] (Fin d → ZMod 2) := b.equivFun
    let conjH : Module.End (ZMod 2) (GaloisField 2 d) →* Module.End (ZMod 2) (Fin d → ZMod 2) :=
      { toFun := fun f => (e : GaloisField 2 d →ₗ[ZMod 2] (Fin d → ZMod 2)).comp
          (f.comp (e.symm : (Fin d → ZMod 2) →ₗ[ZMod 2] GaloisField 2 d))
        map_one' := by ext v; simp
        map_mul' := fun f g => by ext v; simp }
    refine ⟨conjH.comp ψ, Multiplicative.ofAdd 1, ?_⟩
    intro h
    have key := congrArg (fun f => f (e 1)) h
    simp [conjH, ψ] at key
    exact hφ key
  have cyclic_prime_rep_lower_interim (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ)
      (ρ : Representation (ZMod 2) (Multiplicative (ZMod p)) (Fin n → ZMod 2))
      (h : ∃ g, ρ g ≠ 1) : orderOf (2 : ZMod p) ≤ n := by
    obtain ⟨g, hg⟩ := h
    let e : (Module.End (ZMod 2) (Fin n → ZMod 2)) ≃* Matrix (Fin n) (Fin n) (ZMod 2) :=
      (LinearMap.toMatrixAlgEquiv'.toRingEquiv).toMulEquiv
    let f : Multiplicative (ZMod p) →* GL (Fin n) (ZMod 2) :=
      MonoidHom.toHomUnits (e.toMonoidHom.comp ρ)
    have hfg : f g ≠ 1 := by
      intro h1
      apply hg
      have := congrArg (fun u : GL (Fin n) (ZMod 2) => (u : Matrix (Fin n) (Fin n) (ZMod 2))) h1
      simp [f] at this
      exact e.injective (by simpa using this)
    have hord : orderOf (f g) = p := by
      have h1 : orderOf (f g) ∣ p := by
        refine (orderOf_map_dvd f g).trans ?_
        have := orderOf_dvd_natCard g
        simpa [Nat.card_zmod] using this
      rcases (Nat.dvd_prime Fact.out).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hfg
      · exact h
    have hdvd : p ∣ Nat.card (GL (Fin n) (ZMod 2)) := hord ▸ orderOf_dvd_natCard (f g)
    rw [Matrix.card_GL_field] at hdvd
    simp only [ZMod.card] at hdvd
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff.1 Fact.out) _).1 hdvd
    have hi_lt := i.2
    have hle : 2 ^ (i : ℕ) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hi_lt.le
    have h2 : (2 : ZMod p) ^ n = 2 ^ (i : ℕ) := by
      have := (ZMod.natCast_eq_zero_iff _ _).2 hi
      rw [Nat.cast_sub hle] at this
      push_cast at this
      exact sub_eq_zero.1 this
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
    have h3 : (2 : ZMod p) ^ (n - i) = 1 := by
      have : (2 : ZMod p) ^ (i : ℕ) * 2 ^ (n - i) = 2 ^ (i : ℕ) * 1 := by
        rw [← pow_add, mul_one, Nat.add_sub_cancel' hi_lt.le, h2]
      exact mul_left_cancel₀ (pow_ne_zero _ h2ne) this
    have hpos : 0 < n - i := by omega
    exact (orderOf_le_of_pow_eq_one hpos h3).trans (by omega)
  haveI := Fact.mk hp
  unfold dOfPrime minDegree
  apply le_antisymm
  · exact Nat.sInf_le (cyclic_prime_rep_upper_interim p hp2)
  · refine le_csInf ⟨orderOf (2 : ZMod p), cyclic_prime_rep_upper_interim p hp2⟩ ?_
    intro n hn
    obtain ⟨ρ, g, hg⟩ := hn
    exact cyclic_prime_rep_lower_interim p hp2 n ρ ⟨g, hg⟩

end WeakClosure

end CFSG.LocalAnalysis.RankThreeUC
