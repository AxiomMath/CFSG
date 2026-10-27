module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Lam

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

local notation "A6" => alternatingGroup (Fin 6)

@[expose] def m1FirstFactor : Subgroup (A6 × A6) := (⊤ : Subgroup A6).map (MonoidHom.inl A6 A6)

theorem mem_m1FirstFactor {g : A6 × A6} : g ∈ m1FirstFactor ↔ g.2 = 1 := by
  constructor
  · rintro ⟨a, -, rfl⟩
    rfl
  · intro h
    exact ⟨g.1, trivial, Prod.ext rfl h.symm⟩

theorem m1FirstFactor_perfect : ⁅m1FirstFactor, m1FirstFactor⁆ = m1FirstFactor := by
  unfold m1FirstFactor
  rw [← Subgroup.map_commutator]
  have : ⁅(⊤ : Subgroup A6), (⊤ : Subgroup A6)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact commutator_alternatingGroup_eq_top (by simp)
  rw [this]

theorem m1f_comm_mul_left_central {G : Type*} [Group G] (a b k : G) (hk : ∀ g, g * k = k * g) :
    ⁅a * k, b⁆ = ⁅a, b⁆ := by
  have h : k * b * k⁻¹ = b := by
    rw [← hk b]
    group
  calc ⁅a * k, b⁆ = a * (k * b * k⁻¹) * a⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = ⁅a, b⁆ := by rw [h, commutatorElement_def]

theorem m1f_comm_mul_right_central {G : Type*} [Group G] (a b k : G) (hk : ∀ g, g * k = k * g) :
    ⁅a, b * k⁆ = ⁅a, b⁆ := by
  have h : k * a⁻¹ * k⁻¹ = a⁻¹ := by
    rw [← hk a⁻¹]
    group
  calc ⁅a, b * k⁆ = a * b * (k * a⁻¹ * k⁻¹) * b⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = ⁅a, b⁆ := by rw [h, commutatorElement_def]

theorem m1f_comm_mul_eq {G : Type*} [Group G] (a c b : G) :
    ⁅a * c, b⁆ = a * ⁅c, b⁆ * a⁻¹ * ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  group

theorem m1f_comm_comm_eq_one {G : Type*} [Group G] (x y b : G)
    (hx : ⁅x, b⁆ ∈ Subgroup.center G) (hy : ⁅y, b⁆ ∈ Subgroup.center G) :
    ⁅⁅x, y⁆, b⁆ = 1 := by
  have huc : ∀ g, g * ⁅x, b⁆ = ⁅x, b⁆ * g := Subgroup.mem_center_iff.1 hx
  have hvc : ∀ g, g * ⁅y, b⁆ = ⁅y, b⁆ * g := Subgroup.mem_center_iff.1 hy
  have hzc : ∀ g, g * (⁅x, b⁆ * ⁅y, b⁆) = (⁅x, b⁆ * ⁅y, b⁆) * g :=
    Subgroup.mem_center_iff.1 (Subgroup.mul_mem _ hx hy)
  have h1 : ⁅x * y, b⁆ = ⁅y, b⁆ * ⁅x, b⁆ := by
    rw [m1f_comm_mul_eq, hvc x]
    group
  have h2 : ⁅y * x, b⁆ = ⁅x, b⁆ * ⁅y, b⁆ := by
    rw [m1f_comm_mul_eq, huc y]
    group
  have h3 : x * y = ⁅x, y⁆ * (y * x) := by
    rw [commutatorElement_def]
    group
  have h4 : ⁅x * y, b⁆ = ⁅x, y⁆ * ⁅y * x, b⁆ * ⁅x, y⁆⁻¹ * ⁅⁅x, y⁆, b⁆ := by
    rw [h3]
    exact m1f_comm_mul_eq _ _ _
  have h5 : ⁅x, y⁆ * ⁅y * x, b⁆ * ⁅x, y⁆⁻¹ = ⁅y * x, b⁆ := by
    rw [h2, hzc ⁅x, y⁆]
    group
  rw [h4, h5, h2, huc ⁅y, b⁆] at h1
  refine mul_left_cancel (a := ⁅x, b⁆ * ⁅y, b⁆) ?_
  rw [mul_one]
  exact h1

theorem m1f_comm_prod_one {x y : A6 × A6} (hx : x.2 = 1) (hy : y.1 = 1) : ⁅x, y⁆ = 1 := by
  refine Prod.ext ?_ ?_ <;> simp [commutatorElement_def, hx, hy]

set_option linter.unusedVariables false in
theorem exists_M1 {T : Type} [Group T] [Finite T] (E : Subgroup T) (hE : ⁅E, E⁆ = E) (t : T)
    (ht2 : t * t = 1) (htE : ∀ g ∈ E, t * g * t⁻¹ ∈ E)
    (f : ↥E →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center ↥E)
    (hswap : ∀ (x : ↥E) (hx : t * (x : T) * t⁻¹ ∈ E), (f x).2 = 1 →
      (f ⟨t * (x : T) * t⁻¹, hx⟩).1 = 1) :
    ∃ M₁ : Subgroup T, M₁ ≤ E ∧ ⁅M₁, M₁⁆ = M₁ ∧
      (∃ f₁ : ↥M₁ →* alternatingGroup (Fin 6),
        Function.Surjective f₁ ∧ f₁.ker ≤ Subgroup.center ↥M₁) ∧
      ∀ a ∈ M₁, ∀ b ∈ M₁, Commute a (t * b * t⁻¹) := by
  obtain ⟨P, hP⟩ : ∃ P : Subgroup ↥E, P = m1FirstFactor.comap f := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup ↥E, Q = ⁅P, P⁆ := ⟨_, rfl⟩
  have hPmem : ∀ p : ↥E, p ∈ P ↔ (f p).2 = 1 := fun p => by
    rw [hP, Subgroup.mem_comap, mem_m1FirstFactor]
  have hfP : P.map f = m1FirstFactor := by
    rw [hP]
    exact Subgroup.map_comap_eq_self_of_surjective hf _
  have hfQ : Q.map f = m1FirstFactor := by
    rw [hQ, Subgroup.map_commutator, hfP, m1FirstFactor_perfect]
  have hQP : Q ≤ P := by
    rw [hQ]
    exact commutator_le_self_of_subgroup P
  have hdec : ∀ p ∈ P, ∃ q ∈ Q, ∃ k ∈ Subgroup.center ↥E, p = q * k := by
    intro p hp
    have h1 : f p ∈ Q.map f := by
      rw [hfQ, mem_m1FirstFactor]
      exact (hPmem p).1 hp
    obtain ⟨q, hq, hqp⟩ := h1
    refine ⟨q, hq, q⁻¹ * p, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqp, inv_mul_cancel]
  have hQperf : ⁅Q, Q⁆ = Q := by
    refine le_antisymm (commutator_le_self_of_subgroup Q) ?_
    calc Q = ⁅P, P⁆ := hQ
      _ ≤ ⁅Q, Q⁆ := by
        rw [Subgroup.commutator_le]
        intro p1 hp1 p2 hp2
        obtain ⟨q1, hq1, k1, hk1, rfl⟩ := hdec p1 hp1
        obtain ⟨q2, hq2, k2, hk2, rfl⟩ := hdec p2 hp2
        rw [m1f_comm_mul_right_central _ _ _ (Subgroup.mem_center_iff.1 hk2),
          m1f_comm_mul_left_central _ _ _ (Subgroup.mem_center_iff.1 hk1)]
        exact Subgroup.commutator_mem_commutator hq1 hq2
  refine ⟨Q.map E.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [← Subgroup.map_commutator, hQperf]
  · let ε : ↥Q ≃* ↥(Q.map E.subtype) := Subgroup.equivMapOfInjective Q E.subtype E.subtype_injective
    let g : ↥Q →* A6 := (MonoidHom.fst A6 A6).comp (f.comp Q.subtype)
    refine ⟨g.comp ε.symm.toMonoidHom, ?_, ?_⟩
    · intro a
      have h1 : ((a, 1) : A6 × A6) ∈ Q.map f := by
        rw [hfQ, mem_m1FirstFactor]
      obtain ⟨q, hq, hfq⟩ := h1
      refine ⟨ε ⟨q, hq⟩, ?_⟩
      show g (ε.symm (ε ⟨q, hq⟩)) = a
      rw [MulEquiv.symm_apply_apply]
      show (f q).1 = a
      rw [hfq]
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx1 : (f (ε.symm x : ↥Q)).1 = 1 := hx
      have hx2 : (f (ε.symm x : ↥Q)).2 = 1 := (hPmem _).1 (hQP (ε.symm x).2)
      have hq : ((ε.symm x : ↥Q) : ↥E) ∈ Subgroup.center ↥E := by
        apply hker
        rw [MonoidHom.mem_ker]
        exact Prod.ext hx1 hx2
      have hqc := Subgroup.mem_center_iff.1 hq
      rw [Subgroup.mem_center_iff]
      intro y
      apply ε.symm.injective
      rw [map_mul, map_mul]
      exact Subtype.ext (hqc ((ε.symm y : ↥Q) : ↥E))
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    set bb : ↥E := ⟨t * (b' : T) * t⁻¹, htE _ b'.2⟩ with hbbdef
    have hbb : (f bb).1 = 1 := hswap b' (htE _ b'.2) ((hPmem b').1 (hQP hb'))
    have hPcen : ∀ p ∈ P, ⁅p, bb⁆ ∈ Subgroup.center ↥E := by
      intro p hp
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact m1f_comm_prod_one ((hPmem p).1 hp) hbb
    have hQc : Q ≤ Subgroup.centralizer ({bb} : Set ↥E) := by
      rw [hQ, Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact ((commutatorElement_eq_one_iff_mul_comm).1
        (m1f_comm_comm_eq_one x y bb (hPcen x hx) (hPcen y hy))).symm
    have h := Subgroup.mem_centralizer_iff.1 (hQc ha') bb rfl
    exact (congrArg Subtype.val h).symm

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
