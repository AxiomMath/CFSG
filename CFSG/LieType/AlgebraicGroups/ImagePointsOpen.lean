module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import TauCeti.RingTheory.FiniteType.PointSeparation

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

theorem exists_isOpen_mem_subset_of_isConstructible {X : Type*} [TopologicalSpace X] {η : X}
    (hη : ∀ U : Set X, IsOpen U → U.Nonempty → η ∈ U) {s : Set X}
    (hs : Topology.IsConstructible s) (hηs : η ∈ s) :
    ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ U ⊆ s := by
  have key := Topology.IsConstructible.empty_union_induction
    (p := fun s _ => (η ∈ s → ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ U ⊆ s) ∧
      (η ∉ s → ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ U ⊆ sᶜ))
    (fun U hU _ => ⟨fun h => ⟨U, hU, h, subset_rfl⟩, fun h => ⟨Set.univ, isOpen_univ,
      Set.mem_univ _, fun x _ hx => h (hη U hU ⟨x, hx⟩)⟩⟩)
    (fun s _ t _ hs ht => ⟨fun h => h.elim
        (fun h' => (hs.1 h').imp fun U hU => ⟨hU.1, hU.2.1, hU.2.2.trans Set.subset_union_left⟩)
        (fun h' => (ht.1 h').imp fun U hU => ⟨hU.1, hU.2.1, hU.2.2.trans Set.subset_union_right⟩),
      fun h => by
        obtain ⟨U, hU, hηU, hUs⟩ := hs.2 fun h' => h (Or.inl h')
        obtain ⟨V, hV, hηV, hVt⟩ := ht.2 fun h' => h (Or.inr h')
        exact ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩, fun x hx hst =>
          hst.elim (fun h' => hUs hx.1 h') (fun h' => hVt hx.2 h')⟩⟩)
    (fun s _ hs => ⟨fun h => hs.2 h, fun h => by
      obtain ⟨U, hU, hηU, hUs⟩ := hs.1 (not_not.mp h)
      exact ⟨U, hU, hηU, fun x hx => not_not.mpr (hUs hx)⟩⟩) hs
  exact key.1 hηs

theorem exists_forall_exists_comp_eq {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type v} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {B : Type w} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsDomain B]
    (φ : A →ₐ[k] B) :
    ∃ a : A, φ a ≠ 0 ∧ ∀ y : A →ₐ[k] k, (∀ x, φ x = 0 → y x = 0) → y a ≠ 0 →
      ∃ z : B →ₐ[k] k, z.comp φ = y := by
  classical
  set J := RingHom.ker φ
  let φ' : A ⧸ J →ₐ[k] B := Ideal.kerLiftAlg φ
  have hinj : Function.Injective φ' := Ideal.kerLiftAlg_injective φ
  have : IsDomain (A ⧸ J) := hinj.isDomain (φ' : A ⧸ J →+* B)
  have : IsNoetherianRing (A ⧸ J) := Algebra.FiniteType.isNoetherianRing k _
  have hfp : (φ' : A ⧸ J →+* B).FinitePresentation := by
    refine RingHom.FinitePresentation.of_finiteType.1 ?_
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (A ⧸ J)) ?_
    rw [show (φ' : A ⧸ J →+* B).comp (algebraMap k (A ⧸ J)) = algebraMap k B from
      φ'.comp_algebraMap]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  let η : PrimeSpectrum (A ⧸ J) := ⟨⊥, inferInstance⟩
  have hηs : η ∈ Set.range (PrimeSpectrum.comap (φ' : A ⧸ J →+* B)) := by
    refine ⟨⟨⊥, inferInstance⟩, PrimeSpectrum.ext ?_⟩
    ext x
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_bot, η]
    exact map_eq_zero_iff _ hinj
  have hgen : ∀ U : Set (PrimeSpectrum (A ⧸ J)), IsOpen U → U.Nonempty → η ∈ U := by
    rintro U hU ⟨p, hp⟩
    obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hU
    refine hfU ((PrimeSpectrum.mem_basicOpen _ _).mpr fun hf => ?_)
    have hf0 : f = 0 := by simpa [η] using hf
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hpf (by rw [hf0]; exact p.asIdeal.zero_mem)
  obtain ⟨U, hU, hηU, hUs⟩ := exists_isOpen_mem_subset_of_isConstructible hgen
    (PrimeSpectrum.isConstructible_range_comap hfp) hηs
  obtain ⟨_, ⟨ā, rfl⟩, hηā, hāU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηU hU
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ā
  refine ⟨a, fun h => ?_, fun y hy hya => ?_⟩
  · refine (PrimeSpectrum.mem_basicOpen _ _).mp hηā ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr h)]
    exact Ideal.zero_mem _
  · let y' : A ⧸ J →ₐ[k] k := Ideal.Quotient.liftₐ J y fun x hx => hy x hx
    let P : PrimeSpectrum (A ⧸ J) := ⟨RingHom.ker y', RingHom.ker_isPrime _⟩
    have hP : P ∈ PrimeSpectrum.basicOpen (Ideal.Quotient.mk J a) := by
      rw [PrimeSpectrum.mem_basicOpen]
      intro h
      exact hya (RingHom.mem_ker.mp h)
    obtain ⟨q, hq⟩ := hUs (hāU hP)
    have : Nontrivial (B ⧸ q.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr q.isPrime.ne_top
    have : IsDomain (B ⧸ q.asIdeal) := Ideal.Quotient.isDomain _
    obtain ⟨z₀, -⟩ := TauCeti.exists_algHom_apply_ne_zero_of_ne_zero (k := k) (K := k)
      (A := B ⧸ q.asIdeal) (one_ne_zero (α := B ⧸ q.asIdeal))
    refine ⟨z₀.comp (Ideal.Quotient.mkₐ k q.asIdeal), AlgHom.ext fun x => ?_⟩
    have hmem : Ideal.Quotient.mk J x - algebraMap k (A ⧸ J) (y x) ∈ P.asIdeal := by
      change y' _ = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      exact sub_eq_zero.mpr rfl
    rw [← hq, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hmem
    have hmem' : φ x - algebraMap k B (y x) ∈ q.asIdeal := by
      have h1 : (φ' : A ⧸ J →+* B) (Ideal.Quotient.mk J x - algebraMap k (A ⧸ J) (y x)) =
          φ x - algebraMap k B (y x) := by
        change φ' _ = _
        rw [map_sub, AlgHom.commutes, Ideal.kerLiftAlg_mk]
      rw [← h1]
      exact hmem
    have h0 := congrArg z₀ ((Ideal.Quotient.eq_zero_iff_mem (I := q.asIdeal)).mpr hmem')
    rw [map_sub, map_sub, Ideal.Quotient.mk_algebraMap, AlgHom.commutes, map_zero,
      Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h0
    exact h0

end CFSG.LieType.AlgebraicGroups.ClosedCone
