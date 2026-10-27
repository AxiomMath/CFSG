module

public import CFSG.LieType.AlgebraicGroups.CentralizerUnipotentFixed

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CartanComponent

universe u

variable {k : Type u} [Field k]

section LinearAlgebra

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

@[expose] def blockEnd (A p : Module.End k V) : Module.End k V := A * p + (1 - p)

omit [FiniteDimensional k V] in
theorem blockEnd_apply (A p : Module.End k V) (v : V) : blockEnd A p v = A (p v) + (v - p v) := by
  simp [blockEnd]

omit [FiniteDimensional k V] in
theorem blockEnd_mul {A B p : Module.End k V} (hp : IsIdempotentElem p) (hB : Commute B p) :
    blockEnd A p * blockEnd B p = blockEnd (A * B) p := by
  have hpp : ∀ v, p (p v) = p v := fun v => by
    rw [← Module.End.mul_apply, hp.eq]
  have hBp : ∀ v, p (B v) = B (p v) := fun v => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hB.eq]
  ext v
  simp only [Module.End.mul_apply, blockEnd_apply, map_add, map_sub, hpp, hBp, sub_self,
    add_zero]
  abel

theorem det_blockEnd_one_add {N p : Module.End k V} (hN : IsNilpotent N) (hNp : Commute N p) :
    LinearMap.det (blockEnd (1 + N) p) = 1 := by
  have he : blockEnd (1 + N) p = 1 + N * p := by
    unfold blockEnd
    noncomm_ring
  have hn : IsNilpotent (-(N * p)) := (hNp.isNilpotent_mul_right hN).neg
  have h := LinearMap.eval_charpoly (-(N * p)) 1
  rw [hn.charpoly_eq_X_pow_finrank, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one,
    sub_neg_eq_add] at h
  rw [he, ← h]

theorem det_blockEnd_of_mul_eq_smul {A p : Module.End k V} (hp : IsIdempotentElem p) {c : k}
    (hA : A * p = c • p) :
    LinearMap.det (blockEnd A p) = c ^ Module.finrank k (LinearMap.range p) := by
  have hpp : ∀ v, p (p v) = p v := fun v => by
    rw [← Module.End.mul_apply, hp.eq]
  have hAp : ∀ v, A (p v) = c • p v := fun v => by
    rw [← Module.End.mul_apply, hA, LinearMap.smul_apply]
  have he : ∀ v, blockEnd A p v = c • p v + (v - p v) := fun v => by
    rw [blockEnd_apply, hAp]
  let W := LinearMap.range p
  have hW : W ≤ W.comap (blockEnd A p) := by
    rintro _ ⟨v, rfl⟩
    refine ⟨c • p v, ?_⟩
    rw [map_smul, hpp, he, hpp, sub_self, add_zero]
  have hW' : ∀ x ∈ W, blockEnd A p x ∈ W := fun x hx => hW hx
  have h1 : (blockEnd A p).restrict hW' = c • LinearMap.id := by
    ext ⟨_, v, rfl⟩
    simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [he, hpp, sub_self, add_zero]
    rfl
  have h2 : W.mapQ W (blockEnd A p) hW = LinearMap.id := by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.id_comp]
    rw [Submodule.Quotient.eq, he]
    have : c • p v + (v - p v) - v = p ((c - 1) • v) := by
      rw [map_smul, sub_smul, one_smul]
      abel
    rw [this]
    exact LinearMap.mem_range_self p _
  rw [LinearMap.det_eq_det_mul_det W _ hW, h1, h2, LinearMap.det_smul, LinearMap.det_id,
    LinearMap.det_id, mul_one, mul_one]

end LinearAlgebra

section Regular

variable {M : Type u} [CommRing M] [HopfAlgebra k M]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]
  [FiniteDimensional k W]

theorem exists_apply_eq_det (P Q : Module.End k W) :
    ∃ f : M, ∀ g : WithConv (M →ₐ[k] k),
      g.ofConv f = LinearMap.det (basePointsRepresentation (H := M) W g * P + Q) := by
  classical
  let b := Module.finBasis k W
  let A : Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) M := Matrix.of fun a j =>
    matrixCoefficient (C := M) (b.coord a) (P (b j)) + algebraMap k M (b.coord a (Q (b j)))
  refine ⟨A.det, fun g => ?_⟩
  rw [AlgHom.map_det, ← LinearMap.det_toMatrix b]
  congr 1
  ext a j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
  change g.ofConv (matrixCoefficient (C := M) (b.coord a) (P (b j)) +
    algebraMap k M (b.coord a (Q (b j)))) = _
  rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    apply_matrixCoefficient, LinearMap.add_apply, Module.End.mul_apply, map_add]
  rfl

theorem exists_apply_eq_coeff_charpoly :
    ∃ c : ℕ → M, ∀ (g : WithConv (M →ₐ[k] k)) (i : ℕ),
      g.ofConv (c i) = (LinearMap.charpoly (basePointsRepresentation (H := M) W g)).coeff i := by
  classical
  let b := Module.finBasis k W
  let A : Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) M := Matrix.of fun a j =>
    matrixCoefficient (C := M) (b.coord a) (b j)
  refine ⟨fun i => A.charpoly.coeff i, fun g i => ?_⟩
  have hA : A.map g.ofConv = LinearMap.toMatrix b b (basePointsRepresentation (H := M) W g) := by
    ext a j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply]
    change g.ofConv (matrixCoefficient (C := M) (b.coord a) (b j)) = _
    rw [apply_matrixCoefficient]
    rfl
  rw [← LinearMap.charpoly_toMatrix _ b, ← hA,
    show A.map g.ofConv = A.map (g.ofConv : M →+* k) from rfl, Matrix.charpoly_map,
    Polynomial.coeff_map]
  rfl

end Regular

section Points

variable [IsAlgClosed k] (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)

theorem semisimplePart_mem {J : TauCeti.HopfIdeal k H} {x : WithConv (H →ₐ[k] k)}
    (hx : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k)) :
    TauCeti.HopfAlgebra.Point.semisimplePart k H k x ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨TauCeti.HopfAlgebra.Point.semisimplePart k _ k y, ?_⟩
  rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply,
    TauCeti.CommHopfAlgCat.quotientPointsHom_apply,
    TauCeti.HopfAlgebra.Point.semisimplePart_toConv_comp]

theorem unipotentPart_mem {J : TauCeti.HopfIdeal k H} {x : WithConv (H →ₐ[k] k)}
    (hx : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k)) :
    TauCeti.HopfAlgebra.Point.unipotentPart k H k x ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨TauCeti.HopfAlgebra.Point.unipotentPart k _ k y, ?_⟩
  rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply,
    TauCeti.CommHopfAlgCat.quotientPointsHom_apply,
    TauCeti.HopfAlgebra.Point.unipotentPart_toConv_comp]

theorem apply_eq_of_forall_mem_finset (J : TauCeti.HopfIdeal k H)
    [IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J)] (f : H) (Λ : Finset k)
    (hΛ : ∀ g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k),
      g.ofConv f ∈ Λ)
    {g : WithConv (H →ₐ[k] k)}
    (hg : g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k)) :
    g.ofConv f = (1 : WithConv (H →ₐ[k] k)).ofConv f := by
  let Z := TauCeti.FiniteTypeCommHopfAlgCat.quotient H J
  let πJ : H →ₐ[k] Z := (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H J) : H →ₐ[k] Z)
  have hpt : ∀ y : Z →ₐ[k] k, toConv (y.comp πJ) ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := fun y =>
    ⟨toConv y, by rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]; rfl⟩
  have hcover : ∀ y : Z →ₐ[k] k, ∃ i : Λ, ∀ a ∈ ({πJ f - algebraMap k Z i} : Set Z), y a = 0 := by
    intro y
    refine ⟨⟨(toConv (y.comp πJ)).ofConv f, hΛ _ (hpt y)⟩, ?_⟩
    rintro _ rfl
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero]
    rfl
  obtain ⟨i, hl⟩ := TorusConjugacy.exists_forall_apply_eq_zero_of_forall_exists (k := k)
    (fun i : Λ => ({πJ f - algebraMap k Z i} : Set Z)) hcover
  set l : k := i.1
  have key : ∀ g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k),
      g.ofConv f = l := by
    rintro _ ⟨y, rfl⟩
    have h := hl y.ofConv _ rfl
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h
    rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]
    exact h
  rw [key g hg, key 1 (one_mem _)]

end Points

section Weights

variable [IsAlgClosed k]

theorem exists_weight_projections (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    {I : TauCeti.HopfIdeal k M} (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (W : Type u) [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]
    [FiniteDimensional k W] :
    ∃ (m : ℕ) (p : Fin m → Module.End k W) (c : Fin m → WithConv (M →ₐ[k] k) → k),
      (∀ i, IsIdempotentElem (p i)) ∧ (∀ i, LinearMap.range (p i) ≠ ⊥) ∧
      (∀ v, ∑ i, p i v = v) ∧
      (∀ g : WithConv (M →ₐ[k] k), (∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
          (CommAlgCat.of k k), Commute g s) →
        ∀ i, Commute (basePointsRepresentation (H := M) W g) (p i)) ∧
      (∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k), ∀ i,
        basePointsRepresentation (H := M) W s * p i = c i s • p i) := by
  classical
  obtain ⟨n, π, hπ, hker⟩ := RegularCocharacter.exists_splitCoordinates M I
    ((TauCeti.HopfIdeal.isMaximalTorus_iff k M.obj I).mp hI).1
  have hTmem : ∀ s, s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) ↔ ∃ σ, TauCeti.AlgHom.mapDomain (A := k) π σ = s :=
    RegularCocharacter.mem_quotientPointsSubgroup_iff_exists_mapDomain M I π hπ hker
  have hSfin := TauCeti.DiagonalizableGroup.finite_setOf_weightSpace_ne_bot (V := W)
    (π := (π : M →ₗc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))
  let S := hSfin.toFinset
  have hS : ∀ χ, CentralizerUnipotent.wt π (W := W) χ ≠ ⊥ → χ ∈ S :=
    fun χ h => hSfin.mem_toFinset.mpr h
  obtain ⟨ψ, t₀, -, hc⟩ := CentralizerUnipotent.exists_separating (k := k) S
  have hμT : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k
      (RegularCocharacter.cocharacterOfAddHom ψ π) t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) := fun t =>
    (hTmem _).mpr ⟨_, (RegularCocharacter.pointsHom_cocharacterOfAddHom ψ π t).symm⟩
  let P := fun χ => CentralizerUnipotent.proj π W S ψ t₀ χ
  have hPf : ∀ χ ∈ S, ∀ f : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →₀ W,
      (∀ χ', f χ' ∈ CentralizerUnipotent.wt π χ') → P χ (f.sum fun _ x => x) = f χ :=
    fun χ hχ f hf => CentralizerUnipotent.proj_finsupp_sum π S hS ψ t₀ hc hχ hf
  have hPwt : ∀ χ ∈ S, ∀ v, P χ v ∈ CentralizerUnipotent.wt π (W := W) χ := by
    intro χ hχ v
    obtain ⟨f, hf, rfl⟩ := CentralizerUnipotent.exists_finsupp_mem_wt π v
    rw [hPf χ hχ f hf]
    exact hf χ
  have hPself : ∀ χ ∈ S, ∀ v ∈ CentralizerUnipotent.wt π (W := W) χ, P χ v = v := by
    intro χ hχ v hv
    have h := hPf χ hχ (Finsupp.single χ v) fun χ' => by
      by_cases h : χ = χ'
      · subst h
        simpa using hv
      · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
        exact Submodule.zero_mem _
    rwa [Finsupp.sum_single_index rfl, Finsupp.single_eq_same] at h
  have hPsum : ∀ v, ∑ χ ∈ S, P χ v = v := by
    intro v
    obtain ⟨f, hf, rfl⟩ := CentralizerUnipotent.exists_finsupp_mem_wt π v
    rw [Finset.sum_congr rfl fun χ hχ => hPf χ hχ f hf, Finsupp.sum]
    refine (Finset.sum_subset (fun χ hχ => hS χ fun hbot => Finsupp.mem_support_iff.mp hχ
      ((Submodule.eq_bot_iff _).mp hbot _ (hf χ))) fun χ _ hχ => ?_).symm
    exact Finsupp.notMem_support_iff.mp hχ
  let e := S.equivFin
  let χs : Fin S.card → Multiplicative (ULift.{u} (Fin n) →₀ ℤ) := fun i => e.symm i
  have hχs : ∀ i, χs i ∈ S := fun i => (e.symm i).2
  let σ : WithConv (M →ₐ[k] k) → WithConv (MonoidAlgebra k
      (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k] k) := fun s =>
    if hs : ∃ σ, TauCeti.AlgHom.mapDomain (A := k) π σ = s then hs.choose else 1
  refine ⟨S.card, fun i => P (χs i), fun i s => (σ s).ofConv (MonoidAlgebra.single (χs i) 1),
    fun i => ?_, fun i => ?_, fun v => ?_, fun g hg i => ?_, fun s hs i => ?_⟩
  · ext v
    rw [Module.End.mul_apply, hPself _ (hχs i) _ (hPwt _ (hχs i) v)]
  · intro hbot
    refine hSfin.mem_toFinset.mp (hχs i) ((Submodule.eq_bot_iff _).mpr fun v hv => ?_)
    have hmem : v ∈ LinearMap.range (P (χs i)) := ⟨v, hPself _ (hχs i) v hv⟩
    rw [hbot] at hmem
    exact (Submodule.mem_bot k).mp hmem
  · have h := e.symm.sum_comp (fun χ : S => P χ v)
    rw [Finset.sum_coe_sort S (fun χ => P χ v), hPsum v] at h
    exact h
  · ext v
    rw [Module.End.mul_apply, Module.End.mul_apply]
    refine CentralizerUnipotent.aeval_apply_comm ?_ _ v
    have h := (hg _ (hμT t₀)).eq
    change basePointsRepresentation (H := M) W g * _ = _ * basePointsRepresentation (H := M) W g
    rw [← map_mul, ← map_mul, h]
  · have hσ : TauCeti.AlgHom.mapDomain (A := k) π (σ s) = s := by
      have hs' := (hTmem s).mp hs
      simp only [σ, dif_pos hs']
      exact hs'.choose_spec
    ext v
    have h := CentralizerUnipotent.basePointsRepresentation_mapDomain_of_mem_wt π (σ s)
      (hPwt _ (hχs i) v)
    rw [hσ] at h
    rw [Module.End.mul_apply, LinearMap.smul_apply, h]

end Weights

section Unipotence

theorem isNilpotent_pow_sub_one_of_det_blockEnd {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {r : ℕ} (p : Fin r → Module.End k V)
    (hpidem : ∀ i, IsIdempotentElem (p i)) (hpsum : ∀ v, ∑ i, p i v = v)
    {S U : Module.End k V} (hSU : Commute S U) (hU : IsNilpotent (U - 1))
    (hUp : ∀ i, Commute U (p i)) {c : Fin r → k} (hS : ∀ i, S * p i = c i • p i)
    (hdet : ∀ i, LinearMap.det (blockEnd (S * U) (p i)) = 1) :
    IsNilpotent ((S * U) ^ (∏ i, Module.finrank k (LinearMap.range (p i))) - 1) := by
  set N := ∏ i, Module.finrank k (LinearMap.range (p i))
  have hcs : ∀ i, c i ^ Module.finrank k (LinearMap.range (p i)) = 1 := by
    intro i
    have h := hdet i
    have hU1 : LinearMap.det (blockEnd U (p i)) = 1 := by
      rw [show U = 1 + (U - 1) by abel]
      exact det_blockEnd_one_add hU ((hUp i).sub_left (Commute.one_left _))
    rw [← blockEnd_mul (hpidem i) (hUp i), map_mul, hU1, mul_one,
      det_blockEnd_of_mul_eq_smul (hpidem i) (hS i)] at h
    exact h
  have hSN : S ^ N = 1 := by
    ext v
    have hblock : ∀ i (j : ℕ), (S ^ j) (p i v) = c i ^ j • p i v := by
      intro i j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, ← Module.End.mul_apply, hS i,
          LinearMap.smul_apply, smul_smul, ← pow_succ]
    rw [Module.End.one_apply]
    conv_lhs => rw [← hpsum v]
    rw [map_sum]
    conv_rhs => rw [← hpsum v]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨q, hq⟩ : Module.finrank k (LinearMap.range (p i)) ∣ N :=
      Finset.dvd_prod_of_mem (fun i => Module.finrank k (LinearMap.range (p i)))
        (Finset.mem_univ i)
    rw [hblock, hq, pow_mul, hcs i, one_pow, one_smul]
  rw [hSU.mul_pow, hSN, one_mul]
  rw [← mul_geom_sum U N]
  exact (Commute.sum_right _ _ _ fun j _ => ((Commute.refl U).pow_right j).sub_left
    (Commute.one_left _)).isNilpotent_mul_right hU

open scoped _root_.Classical in
@[expose] def charpolys (N n : ℕ) : Finset (Polynomial k) :=
  ((Polynomial.nthRoots N (1 : k)).toFinset.sym n).image fun t : Sym k n =>
    ((t : Multiset k).map fun a => Polynomial.X - Polynomial.C a).prod

open scoped _root_.Classical in
theorem charpoly_mem_charpolys [IsAlgClosed k] {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {N : ℕ} (hN : 0 < N) {A : Module.End k V}
    (hA : IsNilpotent (A ^ N - 1)) :
    LinearMap.charpoly A ∈ charpolys N (Module.finrank k V) := by
  obtain ⟨K, hK⟩ := hA
  have hroots : ∀ a ∈ (LinearMap.charpoly A).roots,
      a ∈ (Polynomial.nthRoots N (1 : k)).toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hN]
    have hroot : (LinearMap.charpoly A).IsRoot a :=
      (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mp ha
    obtain ⟨v, hv⟩ :=
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ a).mpr hroot).exists_hasEigenvector
    have h := Module.End.aeval_apply_of_hasEigenvector (p := (Polynomial.X ^ N - 1) ^ K) hv
    rw [map_pow, map_sub, map_pow, Polynomial.aeval_X, map_one, hK, LinearMap.zero_apply,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at h
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero ((smul_eq_zero.mp h.symm).resolve_right hv.2))
  have hsplit := IsAlgClosed.splits (LinearMap.charpoly A)
  have hcard : (LinearMap.charpoly A).roots.card = Module.finrank k V := by
    rw [← hsplit.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]
  rw [charpolys, Finset.mem_image]
  exact ⟨⟨_, hcard⟩, Finset.mem_sym_iff.mpr fun a ha => hroots a ha,
    (hsplit.eq_prod_roots_of_monic (LinearMap.charpoly_monic _)).symm⟩

variable [IsAlgClosed k]

theorem isUnipotentPoint_of_isNilpotent_pow_sub_one (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (J : TauCeti.HopfIdeal k M) [IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J)]
    (V : Type u) [AddCommGroup V] [Module k V] [TauCeti.Comodule k M V] [Module.Finite k V]
    (hV : TauCeti.Comodule.IsFaithful (k := k) (H := M) (V := V)) {N : ℕ} (hN : 0 < N)
    (h : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      IsNilpotent (basePointsRepresentation (R := k) (H := M) V x ^ N - 1))
    {x : WithConv (M →ₐ[k] k)}
    (hx : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k)) :
    TauCeti.HopfAlgebra.IsUnipotentPoint x := by
  classical
  obtain ⟨cf, hcf⟩ := exists_apply_eq_coeff_charpoly (k := k) (M := M) (W := V)
  have hconst : LinearMap.charpoly (basePointsRepresentation (R := k) (H := M) V x) =
      (Polynomial.X - 1) ^ Module.finrank k V := by
    ext i
    have h' := apply_eq_of_forall_mem_finset M J (cf i)
      ((charpolys N (Module.finrank k V)).image fun P => P.coeff i)
      (fun g hg => by
        rw [hcf]
        exact Finset.mem_image_of_mem _ (charpoly_mem_charpolys hN (h g hg))) hx
    rw [hcf, hcf, map_one, LinearMap.charpoly_one] at h'
    exact h'
  have hCH := LinearMap.aeval_self_charpoly (basePointsRepresentation (R := k) (H := M) V x)
  rw [hconst, map_pow, map_sub, Polynomial.aeval_X, map_one] at hCH
  exact GradedKernel.isUnipotentPoint_of_isNilpotent_basePointsRepresentation_sub_one M V hV x
    ⟨_, hCH⟩

end Unipotence

section Cartan

variable [IsAlgClosed k]

theorem quotientPointsSubgroup_cartan_le_of_semisimple
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    {I : TauCeti.HopfIdeal k M} (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (hss : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj
        (TorusConjugacy.closureIdentityComponent M (Subgroup.centralizer
          (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
            Set (WithConv (M →ₐ[k] k))))) (CommAlgCat.of k k),
      TauCeti.HopfAlgebra.IsSemisimplePoint s →
        s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)) :
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj
        (TorusConjugacy.closureIdentityComponent M (Subgroup.centralizer
          (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
            Set (WithConv (M →ₐ[k] k))))) (CommAlgCat.of k k) ≤
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) := by
  classical
  let T := TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)
  let C := Subgroup.centralizer (T : Set (WithConv (M →ₐ[k] k)))
  let J₀ := TorusConjugacy.closureIdentityComponent M C
  let C0 := TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J₀ (CommAlgCat.of k k)
  change C0 ≤ T
  have hC0C : C0 ≤ C := by
    have h := TorusConjugacy.quotientPointsSubgroup_closureIdentityComponent_le M C
    rwa [CFSG.LieType.AlgebraicGroups.quotientPointsSubgroup_vanishingIdeal_centralizer] at h
  have hcomm : ∀ x ∈ C0, ∀ s ∈ T, Commute x s := fun x hx s hs =>
    ((Subgroup.mem_centralizer_iff.mp (hC0C hx)) s hs).symm
  have hNC : ∀ n ∈ Subgroup.normalizer (T : Set (WithConv (M →ₐ[k] k))), ∀ c ∈ C,
      n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : n⁻¹ * s * n ∈ T := by
      have h := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * s * n)).mpr
      rw [show n * (n⁻¹ * s * n) * n⁻¹ = s by group] at h
      exact h hs
    have h := (Subgroup.mem_centralizer_iff.mp hc) _ hs'
    calc s * (n * c * n⁻¹) = n * ((n⁻¹ * s * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * s * n)) * n⁻¹ := by rw [h]
      _ = n * c * n⁻¹ * s := by group
  have hNC0 : ∀ n ∈ Subgroup.normalizer (T : Set (WithConv (M →ₐ[k] k))), ∀ x ∈ C0,
      n * x * n⁻¹ ∈ C0 := fun n hn x hx =>
    TorusConjugacy.conj_mem_closureIdentityComponent M (hNC n hn) hx
  have hss' : ∀ x : WithConv (M →ₐ[k] k),
      TauCeti.HopfAlgebra.IsSemisimplePoint (TauCeti.HopfAlgebra.Point.semisimplePart k M k x) :=
    fun x => (TauCeti.HopfAlgebra.isSemisimplePoint_def _).mpr fun W =>
      TauCeti.HopfAlgebra.Point.isSemisimple_pointsAction_semisimplePart k M k x W
  have hun : ∀ x : WithConv (M →ₐ[k] k),
      TauCeti.HopfAlgebra.IsUnipotentPoint (TauCeti.HopfAlgebra.Point.unipotentPart k M k x) :=
    fun x => (TauCeti.HopfAlgebra.isUnipotentPoint_def _).mpr fun W =>
      TauCeti.HopfAlgebra.Point.isUnipotent_pointsAction_unipotentPart k M k x W
  let U : Set (WithConv (M →ₐ[k] k)) := {x | x ∈ C0 ∧ TauCeti.HopfAlgebra.IsUnipotentPoint x}
  let Ug := Subgroup.closure U
  have hUgC0 : Ug ≤ C0 := (Subgroup.closure_le C0).mpr fun x hx => hx.1
  let J := TorusConjugacy.closureIdentityComponent M Ug
  have : IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J) :=
    TorusConjugacy.isDomain_quotient_closureIdentityComponent M Ug
  have hvJ := TorusConjugacy.vanishingIdeal_le_closureIdentityComponent M Ug
  have hJC0 : TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) ≤ C0 :=
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le M.obj
      (((TauCeti.HopfIdeal.le_vanishingIdeal_iff Ug J₀).mpr hUgC0).trans hvJ) _
  have hJT : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      ∀ s ∈ T, Commute x s := fun x hx => hcomm x (hJC0 hx)
  have hJN : ∀ n ∈ Subgroup.normalizer (T : Set (WithConv (M →ₐ[k] k))),
      ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
        n * x * n⁻¹ ∈
          TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) := by
    intro n hn x hx
    refine TorusConjugacy.conj_mem_closureIdentityComponent M (fun y hy => ?_) hx
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      exact Subgroup.subset_closure ⟨hNC0 n hn y hy.1,
        (TauCeti.HopfAlgebra.isUnipotentPoint_conj_iff y n).mpr hy.2⟩
    | one => rw [mul_one, mul_inv_cancel]; exact Ug.one_mem
    | mul a b _ _ ha hb =>
      rw [show n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) by group]
      exact Ug.mul_mem ha hb
    | inv a _ ha =>
      rw [show n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ by group]
      exact Ug.inv_mem ha
  have hJu : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      TauCeti.HopfAlgebra.IsUnipotentPoint x := by
    obtain ⟨V, m, b, hb⟩ :=
      TauCeti.Comodule.exists_coordinateBialgHom_surjective (k := k) (H := M)
    let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    let : Module.Finite k V := Module.Finite.of_basis b
    have hV : TauCeti.Comodule.IsFaithful (k := k) (H := M) (V := V) := by
      rw [TauCeti.Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b,
        TauCeti.Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff]
      exact hb
    obtain ⟨r, p, c, hpidem, hpne, hpsum, hpcomm, hpT⟩ := exists_weight_projections M hI V
    let ρ := basePointsRepresentation (R := k) (H := M) V
    have hδ : ∀ i, ∃ f : M, ∀ g : WithConv (M →ₐ[k] k),
        g.ofConv f = LinearMap.det (blockEnd (ρ g) (p i)) := fun i =>
      exists_apply_eq_det (p i) (1 - p i)
    choose f hf using hδ
    have hpC0 : ∀ g ∈ C0, ∀ i, Commute (ρ g) (p i) := fun g hg => hpcomm g (hcomm g hg)
    have hδmul : ∀ g ∈ C0, ∀ h ∈ C0, ∀ i, LinearMap.det (blockEnd (ρ (g * h)) (p i)) =
        LinearMap.det (blockEnd (ρ g) (p i)) * LinearMap.det (blockEnd (ρ h) (p i)) := by
      intro g _ h hh i
      rw [map_mul, ← blockEnd_mul (hpidem i) (hpC0 h hh i), map_mul]
    have hδ1 : ∀ i, LinearMap.det (blockEnd (ρ 1) (p i)) = 1 := by
      intro i
      rw [map_one, show blockEnd (1 : Module.End k V) (p i) = 1 by unfold blockEnd; noncomm_ring,
        map_one]
    have hδu : ∀ u ∈ C0, TauCeti.HopfAlgebra.IsUnipotentPoint u → ∀ i,
        LinearMap.det (blockEnd (ρ u) (p i)) = 1 := by
      intro u hu hu' i
      have hN := CentralizerUnipotent.isNilpotent_basePointsRepresentation_sub_one (V := V) hu'
      rw [show ρ u = 1 + (ρ u - 1) by abel]
      exact det_blockEnd_one_add hN ((hpC0 u hu i).sub_left (Commute.one_left _))
    have hδUg : ∀ g ∈ Ug, ∀ i, LinearMap.det (blockEnd (ρ g) (p i)) = 1 := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg => exact hδu g hg.1 hg.2
      | one => exact hδ1
      | mul a b ha hb iha ihb =>
        intro i
        rw [hδmul a (hUgC0 ha) b (hUgC0 hb), iha, ihb, one_mul]
      | inv a ha iha =>
        intro i
        have h := hδmul a⁻¹ (C0.inv_mem (hUgC0 ha)) a (hUgC0 ha) i
        rw [inv_mul_cancel, hδ1, iha i, mul_one] at h
        exact h.symm
    have hNpos : 0 < ∏ i, Module.finrank k (LinearMap.range (p i)) :=
      Finset.prod_pos fun i _ => Nat.pos_of_ne_zero fun h => hpne i (Submodule.finrank_eq_zero.mp h)
    refine fun x hx => isUnipotentPoint_of_isNilpotent_pow_sub_one M J V hV hNpos
      (fun x hx => ?_) hx
    have hxC0 := hJC0 hx
    have hsC0 := semisimplePart_mem M hxC0
    have huC0 := unipotentPart_mem M hxC0
    have hsT := hss _ hsC0 (hss' x)
    have hxsu := TauCeti.HopfAlgebra.Point.semisimplePart_mul_unipotentPart k M k x
    have hsu := TauCeti.HopfAlgebra.Point.commute_semisimplePart_unipotentPart k M k x
    have hδx : ∀ i, LinearMap.det (blockEnd (ρ x) (p i)) = 1 := by
      intro i
      have hmem : f i - 1 ∈ TauCeti.HopfIdeal.vanishingIdeal Ug := by
        rw [TauCeti.HopfIdeal.mem_vanishingIdeal]
        intro g
        rw [map_sub, hf, hδUg g.1 g.2 i, map_one, sub_self]
      have h0 := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff M.obj J _ x).mp hx _
        (hvJ hmem)
      rwa [map_sub, map_one, sub_eq_zero, hf] at h0
    have hρx : ρ x = ρ (TauCeti.HopfAlgebra.Point.semisimplePart k M k x) *
        ρ (TauCeti.HopfAlgebra.Point.unipotentPart k M k x) := by
      rw [← map_mul, hxsu]
    rw [hρx] at hδx ⊢
    exact isNilpotent_pow_sub_one_of_det_blockEnd p hpidem hpsum (hsu.map ρ)
      (CentralizerUnipotent.isNilpotent_basePointsRepresentation_sub_one (V := V) (hun x))
      (hpC0 _ huC0) (hpT _ hsT) hδx
  have hJ1 : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      x = 1 := fun x hx =>
    CentralizerUnipotent.eq_one_of_reductive M hM hI J hJu hJT hJN hx
  have hUgfin : Finite Ug := by
    have h := TorusConjugacy.relIndex_closureIdentityComponent_ne_zero M Ug
    rw [(Subgroup.eq_bot_iff_forall _).mpr hJ1, Subgroup.relIndex_bot_left] at h
    exact Nat.finite_of_card_ne_zero h
  have hTC0 : T.relIndex C0 ≠ 0 := by
    change (T.subgroupOf C0).index ≠ 0
    rw [Subgroup.index_ne_zero_iff_finite]
    refine Finite.of_surjective
      (fun y : Ug => (QuotientGroup.mk ⟨y, hUgC0 y.2⟩ : C0 ⧸ T.subgroupOf C0)) ?_
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hsT := hss _ (semisimplePart_mem M hx) (hss' x)
    have huUg : TauCeti.HopfAlgebra.Point.unipotentPart k M k x ∈ Ug :=
      Subgroup.subset_closure ⟨unipotentPart_mem M hx, hun x⟩
    refine ⟨⟨_, huUg⟩, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (TauCeti.HopfAlgebra.Point.unipotentPart k M k x)⁻¹ * x ∈ T
    have hxsu := TauCeti.HopfAlgebra.Point.semisimplePart_mul_unipotentPart k M k x
    have hsu := TauCeti.HopfAlgebra.Point.commute_semisimplePart_unipotentPart k M k x
    have heq : (TauCeti.HopfAlgebra.Point.unipotentPart k M k x)⁻¹ * x =
        TauCeti.HopfAlgebra.Point.semisimplePart k M k x := by
      calc (TauCeti.HopfAlgebra.Point.unipotentPart k M k x)⁻¹ * x =
          (TauCeti.HopfAlgebra.Point.unipotentPart k M k x)⁻¹ *
            (TauCeti.HopfAlgebra.Point.unipotentPart k M k x *
              TauCeti.HopfAlgebra.Point.semisimplePart k M k x) := by
            rw [← hsu.eq, hxsu]
        _ = TauCeti.HopfAlgebra.Point.semisimplePart k M k x := inv_mul_cancel_left _ _
    rw [heq]
    exact hsT
  let π₀ : M →ₐc[k] TauCeti.FiniteTypeCommHopfAlgCat.quotient M J₀ :=
    TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M J₀)
  have hrange : (TauCeti.AlgHom.mapDomain (A := k) π₀).range = C0 := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]; rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]; rfl⟩
  have : IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J₀) :=
    TorusConjugacy.isDomain_quotient_closureIdentityComponent M C
  have h := TorusConjugacy.range_mapDomain_le_of_relIndex_ne_zero M π₀ I
    (by rw [hrange]; exact hTC0)
  rwa [hrange] at h

end Cartan

end CFSG.LieType.AlgebraicGroups.CartanComponent
