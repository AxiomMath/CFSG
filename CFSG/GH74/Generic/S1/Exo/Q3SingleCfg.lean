module

public import CFSG.GH74.Generic.S1.Exo.Q3HReduce
public import CFSG.GH74.Generic.S1.Exo.NbSmall

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.L5U5
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices (quaternion_center)

structure Q3Cfg (N : Type) [Group N] [Finite N] (c y : N) (ψA ψB : Q8 →* N) : Prop where
  quasi : IsQuasisimple N
  hZ : IsPGroup 2 ↥(center N)
  gen4 : Gen4 N
  gh : GHList (N ⧸ center N)
  c_mem : c ∈ center N
  c_ne_one : c ≠ 1
  y_ne_one : y ≠ 1
  c_ne_y : c ≠ y
  zA : ψA (QuaternionGroup.a 2) = c
  zB : ψB (QuaternionGroup.a 2) = y
  injA : Function.Injective ψA
  injB : Function.Injective ψB
  comm : ∀ a b, ψA a * ψB b = ψB b * ψA a
  y_nc : y ∉ center N

theorem noCentral_of_equiv {N X : Type} [Group N] [Group X] (e : N ≃* X) (hX : NoCentral X) :
    NoCentral N := by
  intro ψ hψ hz
  apply hX (e.toMonoidHom.comp ψ) (e.injective.comp hψ)
  show e (ψ (QuaternionGroup.a 2, 1)) ∈ center X
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := Subgroup.mem_center_iff.1 hz (e.symm g)
  have h2 := congrArg e h1
  simpa using h2

namespace Q3Cfg

variable {N : Type} [Group N] [Finite N] {c y : N} {ψA ψB : Q8 →* N}
  (cfg : Q3Cfg N c y ψA ψB)

include cfg

theorem c_sq : c * c = 1 := by rw [← cfg.zA, ← map_mul, q8_z_sq, map_one]

theorem y_sq : y * y = 1 := by rw [← cfg.zB, ← map_mul, q8_z_sq, map_one]

theorem inter {u : N} (hA : u ∈ ψA.range) (hB : u ∈ ψB.range) : u = 1 := by
  obtain ⟨g₁, rfl⟩ := hA
  obtain ⟨g₂, hg⟩ := hB
  have h1 : ∀ m, g₁ * m = m * g₁ := by
    intro m
    apply cfg.injA
    rw [map_mul, map_mul, ← hg]
    exact (cfg.comm m g₂).symm
  rcases quaternion_center g₁ h1 with e1 | e1
  · rw [e1, map_one]
  · exfalso
    have h2 : ∀ m, g₂ * m = m * g₂ := by
      intro m
      apply cfg.injB
      rw [map_mul, map_mul, hg]
      exact cfg.comm g₁ m
    rcases quaternion_center g₂ h2 with e2 | e2
    · have : ψA g₁ = 1 := by rw [← hg, e2, map_one]
      rw [e1, cfg.zA] at this
      exact cfg.c_ne_one this
    · have : ψA g₁ = y := by rw [← hg, e2, cfg.zB]
      rw [e1, cfg.zA] at this
      exact cfg.c_ne_y this

theorem center_le : ∀ z ∈ center N, z = 1 ∨ z = c := by
  let φ : Q8 × Q8 →* N := ψA.noncommCoprod ψB fun m n => cfg.comm m n
  have hφ : ∀ g, φ g = ψA g.1 * ψB g.2 := fun g => rfl
  have hker : ∀ g, φ g = 1 → g = 1 ∨
      g = ((QuaternionGroup.a 2 : QuaternionGroup 2), (QuaternionGroup.a 2 : QuaternionGroup 2)) := by
    intro g hg
    left
    have hg' : ψA g.1 * ψB g.2 = 1 := hg
    have hu : ψA g.1 = 1 := by
      apply cfg.inter ⟨g.1, rfl⟩
      rw [eq_inv_of_mul_eq_one_left hg']
      exact ψB.range.inv_mem ⟨g.2, rfl⟩
    have hv : ψB g.2 = 1 := by
      rw [hu, one_mul] at hg'
      exact hg'
    exact Prod.ext (cfg.injA (hu.trans (map_one ψA).symm)) (cfg.injB (hv.trans (map_one ψB).symm))
  have hcomm : ∀ (a : Q8 × Q8) (t : N), t ∈ center N → φ a * t = t * φ a := by
    intro a t ht
    exact (Subgroup.mem_center_iff.1 ht (φ a))
  intro t ht
  obtain ⟨g, hg, hgc⟩ := q8q8_commuting_two_subgroup_le' cfg.gen4 φ hker (center N) cfg.hZ hcomm t ht
  have h1 := quaternion_center g.1 (fun x => by
    have := congrArg Prod.fst (hgc (x, 1))
    simpa using this)
  have h2 := quaternion_center g.2 (fun x => by
    have := congrArg Prod.snd (hgc (1, x))
    simpa using this)
  have hg' : ψA g.1 * ψB g.2 = t := hg
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left
    rw [h1, h2, map_one, map_one, mul_one] at hg'
    exact hg'.symm
  · exfalso
    rw [h1, h2, map_one, cfg.zB, one_mul] at hg'
    exact cfg.y_nc (hg' ▸ ht)
  · right
    rw [h1, h2, map_one, cfg.zA, mul_one] at hg'
    exact hg'.symm
  · exfalso
    rw [h1, h2, cfg.zA, cfg.zB] at hg'
    apply cfg.y_nc
    have hyc : y = c * t := by rw [← hg', ← mul_assoc, cfg.c_sq, one_mul]
    rw [hyc]
    exact Subgroup.mul_mem _ cfg.c_mem ht

theorem psiB_center {g : Q8} (hg : ψB g ∈ center N) : g = 1 := by
  rcases cfg.center_le _ hg with h | h
  · exact cfg.injB (h.trans (map_one ψB).symm)
  · exfalso
    have h1 : ∀ m, g * m = m * g := by
      intro m
      apply cfg.injB
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.1 hg (ψB m)).symm
    rcases quaternion_center g h1 with e | e
    · rw [e, map_one] at h
      exact cfg.c_ne_one h.symm
    · rw [e, cfg.zB] at h
      exact cfg.c_ne_y h.symm

theorem psiA_center {g : Q8} (hg : ψA g ∈ center N) : g = 1 ∨ g = QuaternionGroup.a 2 := by
  rcases cfg.center_le _ hg with h | h
  · left
    exact cfg.injA (h.trans (map_one ψA).symm)
  · right
    exact cfg.injA (h.trans cfg.zA.symm)

theorem quot_data {X : Type} [Group X] (π : N →* X) (hπ : ∀ n, π n = 1 ↔ n ∈ center N) :
    Function.Injective (π.comp ψB) ∧
      ∃ u v : X, u ∈ π.range ∧ v ∈ π.range ∧ u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
        u * v = v * u ∧
        (∀ g, u * π (ψB g) = π (ψB g) * u) ∧ (∀ g, v * π (ψB g) = π (ψB g) * v) := by
  have hi : (QuaternionGroup.a 1 : Q8) * QuaternionGroup.a 1 = QuaternionGroup.a 2 := by decide
  have hj : (QuaternionGroup.xa 0 : Q8) * QuaternionGroup.xa 0 = QuaternionGroup.a 2 := by decide
  have hji : (QuaternionGroup.xa 0 : Q8) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 * (QuaternionGroup.a 1 * QuaternionGroup.xa 0) := by decide
  have hi1 : (QuaternionGroup.a 1 : Q8) ≠ 1 ∧ (QuaternionGroup.a 1 : Q8) ≠ QuaternionGroup.a 2 := by decide
  have hj1 : (QuaternionGroup.xa 0 : Q8) ≠ 1 ∧ (QuaternionGroup.xa 0 : Q8) ≠ QuaternionGroup.a 2 := by decide
  have hij : (QuaternionGroup.a 1 : Q8)⁻¹ * QuaternionGroup.xa 0 ≠ 1 ∧
      (QuaternionGroup.a 1 : Q8)⁻¹ * QuaternionGroup.xa 0 ≠ QuaternionGroup.a 2 := by decide
  have hπc : π c = 1 := (hπ c).2 cfg.c_mem
  refine ⟨?_, π (ψA (QuaternionGroup.a 1)), π (ψA (QuaternionGroup.xa 0)), ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro g g' hgg
    have h1 : π (ψB g) = π (ψB g') := hgg
    have h2 : ψB (g⁻¹ * g') ∈ center N := by
      rw [← hπ]
      have : π (ψB (g⁻¹ * g')) = (π (ψB g))⁻¹ * π (ψB g') := by simp [map_mul, map_inv]
      rw [this, ← h1, inv_mul_cancel]
    exact inv_mul_eq_one.1 (cfg.psiB_center h2)
  · rw [← map_mul, ← map_mul, hi, cfg.zA]
    exact hπc
  · rw [← map_mul, ← map_mul, hj, cfg.zA]
    exact hπc
  · intro h
    rcases cfg.psiA_center ((hπ _).1 h) with e | e
    · exact hi1.1 e
    · exact hi1.2 e
  · intro h
    rcases cfg.psiA_center ((hπ _).1 h) with e | e
    · exact hj1.1 e
    · exact hj1.2 e
  · intro h
    have h' : π (ψA ((QuaternionGroup.a 1 : Q8)⁻¹ * QuaternionGroup.xa 0)) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, h, inv_mul_cancel]
    rcases cfg.psiA_center ((hπ _).1 h') with e | e
    · exact hij.1 e
    · exact hij.2 e
  · have hmul : ∀ a b : Q8, π (ψA a) * π (ψA b) = π (ψA (a * b)) := by
      intro a b
      rw [map_mul, map_mul]
    rw [hmul (QuaternionGroup.a 1) (QuaternionGroup.xa 0), hmul (QuaternionGroup.xa 0) (QuaternionGroup.a 1),
      hji, map_mul ψA (QuaternionGroup.a 2), cfg.zA, map_mul π c, hπc, one_mul]
  · intro g
    rw [← map_mul, ← map_mul, cfg.comm]
  · intro g
    rw [← map_mul, ← map_mul, cfg.comm]

theorem prod_injective :
    Function.Injective (ψA.noncommCoprod ψB fun m n => cfg.comm m n) := by
  refine (MonoidHom.noncommCoprod_injective _ _ _).2 ⟨cfg.injA, cfg.injB, ?_⟩
  exact Subgroup.disjoint_def.2 fun {u} hA hB => cfg.inter hA hB

theorem not_noCentral : ¬ NoCentral N := fun h =>
  h (ψA.noncommCoprod ψB fun m n => cfg.comm m n) cfg.prod_injective (by
    show ψA (QuaternionGroup.a 2) * ψB 1 ∈ center N
    rw [map_one, mul_one, cfg.zA]
    exact cfg.c_mem)

theorem false_of_sl2 (h : HasSL2Model N Odd) : False :=
  nb_false_of_sl2_model h cfg.c_sq cfg.y_sq cfg.c_ne_one cfg.y_ne_one cfg.c_ne_y

theorem false_of_exponent (h : Monoid.exponent ↥(center N) = 4) : False := by
  have h2 : Monoid.exponent ↥(center N) ∣ 2 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro z
    rcases cfg.center_le z.1 z.2 with e | e
    · have : z = 1 := Subtype.ext e
      rw [this, one_pow]
    · have : z.1 * z.1 = 1 := by rw [e, cfg.c_sq]
      apply Subtype.ext
      rw [sq]
      exact this
  rw [h] at h2
  omega

theorem false_of_sl4 (h : IsSL4Model N) : False := by
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · exact cfg.not_noCentral (noCentral_of_equiv e (noCentral_statedSL4 hF))
  · exact cfg.not_noCentral (noCentral_of_equiv e (noCentral_statedSU4 hF hq))

theorem false_of_sp {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (e : N ≃* ↥(StatedSp 2 F)) : False :=
  cfg.not_noCentral (noCentral_of_equiv e (noCentral_statedSp2 hF))

end Q3Cfg

end CFSG.GH74.Generic.S1.Exo
