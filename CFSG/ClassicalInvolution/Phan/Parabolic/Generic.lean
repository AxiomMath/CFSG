module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.Phan

open Subgroup

variable {G Y : Type*} [Group G] [Group Y] {N T : Subgroup G}

@[expose] def conjAutOfNormalizer (hNT : T ≤ normalizer (N : Set G)) : T →* MulAut N where
  toFun t :=
    { toFun := fun n => ⟨t * n * (t : G)⁻¹, (mem_normalizer_iff.mp (hNT t.2) n).mp n.2⟩
      invFun := fun n => ⟨(t : G)⁻¹ * n * t, by
        simpa using (mem_normalizer_iff.mp (hNT (T.inv_mem t.2)) n).mp n.2⟩
      left_inv := fun n => by ext; simp [mul_assoc]
      right_inv := fun n => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp [mul_assoc]

theorem coe_conjAutOfNormalizer (hNT : T ≤ normalizer (N : Set G)) (t : T) (n : N) :
    ((conjAutOfNormalizer hNT t n : N) : G) = t * n * (t : G)⁻¹ :=
  rfl

theorem exists_hom_sup_of_normalizes (hNT : T ≤ normalizer (N : Set G))
    (φN : N →* Y) (φT : T →* Y)
    (hagree : ∀ g (hN : g ∈ N) (hT : g ∈ T), φN ⟨g, hN⟩ = φT ⟨g, hT⟩)
    (hconj : ∀ (t : T) (n : N), φT t * φN n * (φT t)⁻¹ = φN (conjAutOfNormalizer hNT t n)) :
    ∃ φ : ↥(N ⊔ T) →* Y, (∀ n : N, φ ⟨n, mem_sup_left n.2⟩ = φN n) ∧
      (∀ t : T, φ ⟨t, mem_sup_right t.2⟩ = φT t) := by
  let ρ : T →* MulAut N := conjAutOfNormalizer hNT
  let ψ : N ⋊[ρ] T →* Y := SemidirectProduct.lift φN φT (fun t => by
    ext n
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (hconj t n).symm)
  let m : N ⋊[ρ] T →* G := SemidirectProduct.lift N.subtype T.subtype (fun t => by
    ext n
    simp [ρ, coe_conjAutOfNormalizer])
  have hm : ∀ (n : N) (t : T), m ⟨n, t⟩ = n * t := fun n t => by
    simp [m, SemidirectProduct.lift]
  have hm1 : ∀ n : N, m (SemidirectProduct.inl n) = n := fun n => by simp [m]
  have hm2 : ∀ t : T, m (SemidirectProduct.inr t) = t := fun t => by simp [m]
  have hψ : ∀ (n : N) (t : T), ψ ⟨n, t⟩ = φN n * φT t := fun n t => by
    simp [ψ, SemidirectProduct.lift]
  have hψ1 : ∀ n : N, ψ (SemidirectProduct.inl n) = φN n := fun n => by simp [ψ]
  have hψ2 : ∀ t : T, ψ (SemidirectProduct.inr t) = φT t := fun t => by simp [ψ]
  have hrange : m.range = N ⊔ T := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨n, t⟩ := x
      rw [hm]
      exact mul_mem (mem_sup_left n.2) (mem_sup_right t.2)
    · intro g hg
      rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left N T hNT] at hg
      obtain ⟨n, hn, t, ht, rfl⟩ := hg
      exact ⟨⟨⟨n, hn⟩, ⟨t, ht⟩⟩, by rw [hm]⟩
  have hker : m.ker ≤ ψ.ker := by
    intro x hx
    obtain ⟨n, t⟩ := x
    have hx' : m ⟨n, t⟩ = 1 := hx
    rw [hm] at hx'
    have hn : (n : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_left hx'
    have hT : (n : G) ∈ T := by rw [hn]; exact T.inv_mem t.2
    have h1 := hagree n n.2 hT
    rw [MonoidHom.mem_ker, hψ, h1]
    have h2 : (⟨n, hT⟩ : T) = t⁻¹ := Subtype.ext hn
    rw [h2, map_inv, inv_mul_cancel]
  have hsurj : Function.Surjective m.rangeRestrict := m.rangeRestrict_surjective
  let φ0 : m.range →* Y := (MonoidHom.liftOfRightInverse m.rangeRestrict (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj)) ⟨ψ, by
      intro x hx
      apply hker
      simpa using hx⟩
  have hφ0 : ∀ x, φ0 (m.rangeRestrict x) = ψ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  refine ⟨φ0.comp (MulEquiv.subgroupCongr hrange.symm).toMonoidHom, ?_, ?_⟩
  · intro n
    have : (MulEquiv.subgroupCongr hrange.symm) ⟨n, mem_sup_left n.2⟩ =
        m.rangeRestrict (SemidirectProduct.inl n) := by
      apply Subtype.ext
      simp only [MulEquiv.subgroupCongr_apply, MonoidHom.coe_rangeRestrict, hm1]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this, hφ0, hψ1]
  · intro t
    have : (MulEquiv.subgroupCongr hrange.symm) ⟨t, mem_sup_right t.2⟩ =
        m.rangeRestrict (SemidirectProduct.inr t) := by
      apply Subtype.ext
      simp only [MulEquiv.subgroupCongr_apply, MonoidHom.coe_rangeRestrict, hm2]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this, hφ0, hψ2]

theorem exists_hom_sup_of_normalizes' (hNT : T ≤ normalizer (N : Set G))
    (φN : N →* Y) (φT : T →* Y)
    (hagree : ∀ g (hN : g ∈ N) (hT : g ∈ T), φN ⟨g, hN⟩ = φT ⟨g, hT⟩)
    (hconj : ∀ (t : T) (n : N), φT t * φN n * (φT t)⁻¹ = φN (conjAutOfNormalizer hNT t n)) :
    ∃ φ : ↥(T ⊔ N) →* Y, (∀ n : N, φ ⟨n, mem_sup_right n.2⟩ = φN n) ∧
      (∀ t : T, φ ⟨t, mem_sup_left t.2⟩ = φT t) := by
  obtain ⟨φ, h1, h2⟩ := exists_hom_sup_of_normalizes hNT φN φT hagree hconj
  refine ⟨φ.comp (MulEquiv.subgroupCongr (sup_comm T N)).toMonoidHom, fun n => ?_, fun t => ?_⟩
  · exact h1 n
  · exact h2 t

theorem forall_conj_of_gens (hNT : T ≤ normalizer (N : Set G)) (φN : N →* Y) (φT : T →* Y)
    {SN : Set N} {ST : Set T} (hSN : closure SN = ⊤) (hST : closure ST = ⊤)
    (h : ∀ t ∈ ST, ∀ x ∈ SN, φT t * φN x * (φT t)⁻¹ = φN (conjAutOfNormalizer hNT t x))
    (t : T) (n : N) : φT t * φN n * (φT t)⁻¹ = φN (conjAutOfNormalizer hNT t n) := by
  have h1 : ∀ t ∈ ST, ∀ n : N, φT t * φN n * (φT t)⁻¹ = φN (conjAutOfNormalizer hNT t n) := by
    intro t ht n
    have hle : closure SN ≤ MonoidHom.eqLocus ((MulAut.conj (φT t)).toMonoidHom.comp φN)
        (φN.comp (conjAutOfNormalizer hNT t).toMonoidHom) := by
      rw [closure_le]
      intro x hx
      exact h t ht x hx
    have hn : n ∈ closure SN := by rw [hSN]; trivial
    exact hle hn
  let S : Subgroup T :=
    { carrier := {t | ∀ n : N, φT t * φN n * (φT t)⁻¹ = φN (conjAutOfNormalizer hNT t n)}
      mul_mem' := fun {a b} ha hb n => by
        have e1 := hb n
        have e2 := ha (conjAutOfNormalizer hNT b n)
        calc φT (a * b) * φN n * (φT (a * b))⁻¹
            = φT a * (φT b * φN n * (φT b)⁻¹) * (φT a)⁻¹ := by rw [map_mul]; group
          _ = φT a * φN (conjAutOfNormalizer hNT b n) * (φT a)⁻¹ := by rw [e1]
          _ = φN (conjAutOfNormalizer hNT a (conjAutOfNormalizer hNT b n)) := e2
          _ = φN (conjAutOfNormalizer hNT (a * b) n) := by rw [map_mul]; rfl
      one_mem' := fun n => by simp
      inv_mem' := fun {a} ha n => by
        have e2 := ha (conjAutOfNormalizer hNT a⁻¹ n)
        have e3 : conjAutOfNormalizer hNT a (conjAutOfNormalizer hNT a⁻¹ n) = n := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
        rw [e3] at e2
        rw [map_inv]
        calc (φT a)⁻¹ * φN n * ((φT a)⁻¹)⁻¹
            = (φT a)⁻¹ * (φT a * φN (conjAutOfNormalizer hNT a⁻¹ n) * (φT a)⁻¹) * ((φT a)⁻¹)⁻¹ := by
              rw [e2]
          _ = φN (conjAutOfNormalizer hNT a⁻¹ n) := by group }
  have hle : closure ST ≤ S := (closure_le S).2 h1
  rw [hST] at hle
  exact hle (mem_top t) n

theorem le_normalizer_iSup₂ {ι : Type*} (T : Subgroup G) (J : Set ι) (S : ι → Subgroup G)
    (h : ∀ j, T ≤ normalizer (S j : Set G)) :
    T ≤ normalizer ((⨆ j ∈ J, S j : Subgroup G) : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ (⨆ j ∈ J, S j : Subgroup G), t * x * t⁻¹ ∈ (⨆ j ∈ J, S j) := by
    intro t ht x hx
    have hmap : (⨆ j ∈ J, S j : Subgroup G).map (MulAut.conj t).toMonoidHom ≤ ⨆ j ∈ J, S j := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun j => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hj => ?_
      refine le_trans ?_ (le_iSup₂ (f := fun j _ => S j) j hj)
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 (h j ht) y).1 hy
    exact hmap ⟨x, hx, rfl⟩
  intro t ht
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem hom_ext_of_le_closure {H : Subgroup G} (φ₁ φ₂ : H →* Y) {S : Set G} (hSH : S ⊆ H)
    (hS : H ≤ closure S) (h : ∀ (x : G) (hx : x ∈ S), φ₁ ⟨x, hSH hx⟩ = φ₂ ⟨x, hSH hx⟩) :
    φ₁ = φ₂ := by
  ext x
  have hle : closure S ≤ (MonoidHom.eqLocus φ₁ φ₂).map H.subtype := by
    rw [closure_le]
    intro y hy
    exact ⟨⟨y, hSH hy⟩, h y hy, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hle (hS x.2)
  have : z = x := Subtype.ext hzx
  subst this
  exact hz

theorem ofInjective_symm_apply_self {H : Type*} [Group H] {g : G →* H}
    (hg : Function.Injective g) (x : G) (h : g x ∈ g.range) :
    (MonoidHom.ofInjective hg).symm ⟨g x, h⟩ = x :=
  hg (by rw [MonoidHom.apply_ofInjective_symm])

theorem closure_eq_top_of_le_closure {H : Subgroup G} {S : Set G} (hSH : S ⊆ H)
    (hS : H ≤ closure S) : closure {x : H | (x : G) ∈ S} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hle : closure S ≤ (closure {x : H | (x : G) ∈ S}).map H.subtype := by
    rw [closure_le]
    intro y hy
    exact ⟨⟨y, hSH hy⟩, subset_closure hy, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hle (hS x.2)
  have : z = x := Subtype.ext hzx
  subst this
  exact hz

end CFSG.ClassicalInvolution.Phan
