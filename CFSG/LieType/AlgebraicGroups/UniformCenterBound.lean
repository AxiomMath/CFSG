module

public import CFSG.LieType.AlgebraicGroups.CentralIsogenyLift
public import CFSG.Mathlib.RingTheory.ConnectedRegular
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Commutator
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Finite
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Reductive
import TauCeti.RingTheory.KrullDimension.FiniteType
import TauCeti.RingTheory.RingHom.FaithfullyFlat
import CFSG.Mathlib.RingTheory.TensorDomainAlgClosed
import CFSG.Mathlib.RingTheory.PrimeChainStabilize
import CFSG.Mathlib.RingTheory.FiniteFlatRankBound
public import TauCeti.RingTheory.Smooth.GeometricallyReduced

public section

open CategoryTheory TensorProduct WithConv
open scoped commutatorElement

universe u

namespace CFSG.LieType.AlgebraicGroups.UniformCenter

variable {k : Type u} [Field k]

theorem commutatorElement_mul_mul {G : Type*} [Group G] (x y z w : G)
    (hz : ∀ g, Commute z g) (hw : ∀ g, Commute w g) : ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : z * (y * w) * z⁻¹ = y * w := by rw [(hz (y * w)).eq, mul_inv_cancel_right]
  have h2 : w * x⁻¹ * w⁻¹ = x⁻¹ := by rw [(hw x⁻¹).eq, mul_inv_cancel_right]
  calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
      = x * (z * (y * w) * z⁻¹) * x⁻¹ * (w⁻¹ * y⁻¹) := by group
    _ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by rw [h1]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h2]

theorem faithfullyFlat_tensorProductMap {A B C D : Type u} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
    (f : A →ₐ[k] B) (g : C →ₐ[k] D)
    (hf : (f : A →+* B).FaithfullyFlat) (hg : (g : C →+* D).FaithfullyFlat) :
    ((Algebra.TensorProduct.map f g : A ⊗[k] C →ₐ[k] B ⊗[k] D) :
      A ⊗[k] C →+* B ⊗[k] D).FaithfullyFlat := by
  let cAC : A ⊗[k] C →ₐ[k] C ⊗[k] A := Algebra.TensorProduct.comm k A C
  let cCB : C ⊗[k] B →ₐ[k] B ⊗[k] C := Algebra.TensorProduct.comm k C B
  have h1 : ((Algebra.TensorProduct.lTensor B g : B ⊗[k] C →ₐ[k] B ⊗[k] D) :
      B ⊗[k] C →+* B ⊗[k] D).FaithfullyFlat := RingHom.FaithfullyFlat.lTensor B hg
  have h2 : ((Algebra.TensorProduct.lTensor C f : C ⊗[k] A →ₐ[k] C ⊗[k] B) :
      C ⊗[k] A →+* C ⊗[k] B).FaithfullyFlat := RingHom.FaithfullyFlat.lTensor C hf
  have hc1 : (cAC : A ⊗[k] C →+* C ⊗[k] A).FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (Algebra.TensorProduct.comm k A C).bijective
  have hc2 : (cCB : C ⊗[k] B →+* B ⊗[k] C).FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (Algebra.TensorProduct.comm k C B).bijective
  have heq : (Algebra.TensorProduct.map f g : A ⊗[k] C →ₐ[k] B ⊗[k] D) =
      (Algebra.TensorProduct.lTensor B g).comp
        (cCB.comp ((Algebra.TensorProduct.lTensor C f).comp cAC)) := by
    ext a <;> simp [cAC, cCB]
  rw [heq]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.stableUnderComposition _ _ hc1 h2) hc2) h1

theorem exists_commutator_lift {H K : CommHopfAlgCat.{u} k} (q : H ⟶ K)
    (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q) :
    ∃ c : K →ₐ[k] H ⊗[k] H,
      (Algebra.TensorProduct.map (q.hom : H →ₐ[k] K) (q.hom : H →ₐ[k] K)).comp c =
        TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := K) := by
  let HH : CommHopfAlgCat.{u} k := CommHopfAlgCat.of k (H ⊗[k] H)
  let KK : CommHopfAlgCat.{u} k := CommHopfAlgCat.of k (K ⊗[k] K)
  let Q : HH ⟶ KK := CommHopfAlgCat.ofHom (Bialgebra.TensorProduct.map q.hom q.hom)
  have hQmap : (Q.hom : H ⊗[k] H →ₐ[k] K ⊗[k] K) =
      Algebra.TensorProduct.map (q.hom : H →ₐ[k] K) (q.hom : H →ₐ[k] K) := rfl
  have hQ : ((Q.hom : H ⊗[k] H →ₐ[k] K ⊗[k] K) : H ⊗[k] H →+* K ⊗[k] K).FaithfullyFlat := by
    rw [hQmap]
    exact faithfullyFlat_tensorProductMap _ _ hq.faithfullyFlat hq.faithfullyFlat
  have hQt : ∀ a b : H, (Q.hom : H ⊗[k] H →ₐ[k] K ⊗[k] K) (a ⊗ₜ b) = q.hom a ⊗ₜ q.hom b := by
    intro a b
    rw [hQmap, Algebra.TensorProduct.map_tmul]
    rfl
  have hcen : ∀ {A : CommAlgCat.{u} k} {v w : WithConv (K →ₐ[k] A)},
      TauCeti.AlgHom.mapDomain q.hom v = TauCeti.AlgHom.mapDomain q.hom w →
        ∀ y, Commute (v⁻¹ * w) y := by
    intro A v w hvw y
    have hz : TauCeti.AlgHom.mapDomain q.hom (v⁻¹ * w) = 1 := by
      rw [map_mul, map_inv, hvw, inv_mul_cancel]
    have hm : (v⁻¹ * w : TauCeti.HopfAlgebra.points (R := k) (H := K) A) ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup K
          (TauCeti.CommHopfAlgCat.kernelHopfIdeal q) A := by
      apply (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff q A _).1
      rw [← TauCeti.AlgHom.mapDomain_apply]
      exact hz
    exact (TauCeti.CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup K _
      hq.isCentral_kernelHopfIdeal A hm).commute y
  have hmem : ∀ x : K, TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := K) x ∈
      (Q.hom : H ⊗[k] H →ₐ[k] K ⊗[k] K).range := by
    intro x
    rw [← TauCeti.CommHopfAlgCat.coinvariants_kernelHopfIdeal_eq_range Q hQ,
      TauCeti.CommHopfAlgCat.mem_coinvariants_kernelHopfIdeal_iff]
    intro A g g' hgg'
    rw [TauCeti.CommHopfAlgCat.mapPointsFunctor_app_apply,
      TauCeti.CommHopfAlgCat.mapPointsFunctor_app_apply] at hgg'
    have hgQ := congrArg WithConv.ofConv hgg'
    simp only at hgQ
    let G : K ⊗[k] K →ₐ[k] A := g.ofConv
    let G' : K ⊗[k] K →ₐ[k] A := g'.ofConv
    let g₁ : WithConv (K →ₐ[k] A) := toConv (G.comp Algebra.TensorProduct.includeLeft)
    let g₂ : WithConv (K →ₐ[k] A) := toConv (G.comp Algebra.TensorProduct.includeRight)
    let g₁' : WithConv (K →ₐ[k] A) := toConv (G'.comp Algebra.TensorProduct.includeLeft)
    let g₂' : WithConv (K →ₐ[k] A) := toConv (G'.comp Algebra.TensorProduct.includeRight)
    have hG : G = Algebra.TensorProduct.productMap g₁.ofConv g₂.ofConv := by
      ext a <;> simp [g₁, g₂]
    have hG' : G' = Algebra.TensorProduct.productMap g₁'.ofConv g₂'.ofConv := by
      ext a <;> simp [g₁', g₂']
    have h1 : TauCeti.AlgHom.mapDomain q.hom g₁ = TauCeti.AlgHom.mapDomain q.hom g₁' := by
      rw [TauCeti.AlgHom.mapDomain_apply, TauCeti.AlgHom.mapDomain_apply]
      congr 1
      ext a
      have := congrArg (fun φ : H ⊗[k] H →ₐ[k] A => φ (a ⊗ₜ 1)) hgQ
      simp only [AlgHom.comp_apply] at this
      erw [hQt] at this
      simpa [g₁, g₁', G, G'] using this
    have h2 : TauCeti.AlgHom.mapDomain q.hom g₂ = TauCeti.AlgHom.mapDomain q.hom g₂' := by
      rw [TauCeti.AlgHom.mapDomain_apply, TauCeti.AlgHom.mapDomain_apply]
      congr 1
      ext a
      have := congrArg (fun φ : H ⊗[k] H →ₐ[k] A => φ (1 ⊗ₜ a)) hgQ
      simp only [AlgHom.comp_apply] at this
      erw [hQt] at this
      simpa [g₂, g₂', G, G'] using this
    have hcomm : ⁅g₁', g₂'⁆ = ⁅g₁, g₂⁆ := by
      have e1 : g₁' = g₁ * (g₁⁻¹ * g₁') := by group
      have e2 : g₂' = g₂ * (g₂⁻¹ * g₂') := by group
      rw [e1, e2]
      exact commutatorElement_mul_mul _ _ _ _ (hcen h1) (hcen h2)
    have hev : ∀ (F : K ⊗[k] K →ₐ[k] A) (u v : WithConv (K →ₐ[k] A)),
        F = Algebra.TensorProduct.productMap u.ofConv v.ofConv →
          F (TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := K) x) = ⁅u, v⁆.ofConv x := by
      intro F u v hF
      rw [← TauCeti.HopfAlgebra.productMap_comp_commutatorAlgHom, ← hF]
      rfl
    change G _ = G' _
    rw [hev G g₁ g₂ hG, hev G' g₁' g₂' hG', hcomm]
  have hinj : Function.Injective (Q.hom : H ⊗[k] H →ₐ[k] K ⊗[k] K) := hQ.injective
  refine ⟨((AlgEquiv.ofInjective _ hinj).symm : _ →ₐ[k] H ⊗[k] H).comp
    ((TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := K)).codRestrict _ hmem), ?_⟩
  apply AlgHom.ext
  intro x
  have := AlgEquiv.ofInjective_apply (Q.hom : H ⊗[k] H →ₐ[k] K ⊗[k] K) hinj
    ((AlgEquiv.ofInjective _ hinj).symm
      ((TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := K)).codRestrict _ hmem x))
  rw [AlgEquiv.apply_symm_apply] at this
  rw [← hQmap, AlgHom.comp_apply, AlgHom.comp_apply]
  exact this.symm


section Iterated

variable (H : CommHopfAlgCat.{u} k)

noncomputable def iterAlg : ℕ → CommAlgCat.{u} k
  | 0 => CommAlgCat.of k k
  | n + 1 => CommAlgCat.of k (iterAlg n ⊗[k] (H ⊗[k] H))

noncomputable def iterInl (n : ℕ) : iterAlg H n →ₐ[k] iterAlg H (n + 1) :=
  Algebra.TensorProduct.includeLeft

noncomputable def iterInr (n : ℕ) : H ⊗[k] H →ₐ[k] iterAlg H (n + 1) :=
  Algebra.TensorProduct.includeRight

noncomputable def iterDesc (n : ℕ) {E : Type u} [CommRing E] [Algebra k E]
    (f : iterAlg H n →ₐ[k] E) (g : H ⊗[k] H →ₐ[k] E) : iterAlg H (n + 1) →ₐ[k] E :=
  Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _

theorem iterDesc_comp_iterInl (n : ℕ) {E : Type u} [CommRing E] [Algebra k E]
    (f : iterAlg H n →ₐ[k] E) (g : H ⊗[k] H →ₐ[k] E) :
    (iterDesc H n f g).comp (iterInl H n) = f :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _

theorem iterDesc_comp_iterInr (n : ℕ) {E : Type u} [CommRing E] [Algebra k E]
    (f : iterAlg H n →ₐ[k] E) (g : H ⊗[k] H →ₐ[k] E) :
    (iterDesc H n f g).comp (iterInr H n) = g :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _

noncomputable def iterComm : (n : ℕ) → WithConv (H →ₐ[k] iterAlg H n)
  | 0 => 1
  | n + 1 => TauCeti.AlgHom.mapValue (iterInl H n) (iterComm n) *
      TauCeti.AlgHom.mapValue (iterInr H n)
        (toConv (TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := H)))

theorem iterComm_succ (n : ℕ) : iterComm H (n + 1) =
    TauCeti.AlgHom.mapValue (iterInl H n) (iterComm H n) *
      TauCeti.AlgHom.mapValue (iterInr H n)
        (toConv (TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := H))) := by
  rw [iterComm]

variable {H} in
noncomputable def coverComm {K : CommHopfAlgCat.{u} k} (c : K →ₐ[k] H ⊗[k] H) :
    (n : ℕ) → WithConv (K →ₐ[k] iterAlg H n)
  | 0 => 1
  | n + 1 => TauCeti.AlgHom.mapValue (iterInl H n) (coverComm c n) *
      TauCeti.AlgHom.mapValue (iterInr H n) (toConv c)

variable {H} in
theorem mapDomain_coverComm {K : CommHopfAlgCat.{u} k} (q : H ⟶ K) (c : K →ₐ[k] H ⊗[k] H)
    (hc : c.comp (q.hom : H →ₐ[k] K) = TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := H))
    (n : ℕ) : TauCeti.AlgHom.mapDomain q.hom (coverComm c n) = iterComm H n := by
  induction n with
  | zero => exact map_one _
  | succ n ih =>
    change TauCeti.AlgHom.mapDomain q.hom (TauCeti.AlgHom.mapValue (iterInl H n) (coverComm c n) *
      TauCeti.AlgHom.mapValue (iterInr H n) (toConv c)) = _
    rw [iterComm_succ, map_mul, ← ih, ← hc]
    congr 1
    · apply WithConv.ofConv_injective
      simp only [TauCeti.AlgHom.mapDomain_apply, TauCeti.AlgHom.mapValue_apply,
        WithConv.ofConv_toConv, AlgHom.comp_assoc]
    · apply WithConv.ofConv_injective
      simp only [TauCeti.AlgHom.mapDomain_apply, TauCeti.AlgHom.mapValue_apply,
        WithConv.ofConv_toConv, AlgHom.comp_assoc]

noncomputable def iterForget (n : ℕ) : iterAlg H (n + 1) →ₐ[k] iterAlg H n :=
  iterDesc H n (AlgHom.id k (iterAlg H n))
    (Algebra.TensorProduct.productMap (1 : WithConv (H →ₐ[k] iterAlg H n)).ofConv
      (1 : WithConv (H →ₐ[k] iterAlg H n)).ofConv)

theorem mapValue_iterForget (n : ℕ) :
    TauCeti.AlgHom.mapValue (iterForget H n) (iterComm H (n + 1)) = iterComm H n := by
  rw [iterComm_succ, map_mul]
  have h1 : TauCeti.AlgHom.mapValue (iterForget H n)
      (TauCeti.AlgHom.mapValue (iterInl H n) (iterComm H n)) = iterComm H n := by
    apply WithConv.ofConv_injective
    simp only [TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
    rw [iterForget, iterDesc_comp_iterInl, AlgHom.id_comp]
  have h2 : TauCeti.AlgHom.mapValue (iterForget H n)
      (TauCeti.AlgHom.mapValue (iterInr H n)
        (toConv (TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := H)))) = 1 := by
    apply WithConv.ofConv_injective
    simp only [TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
    rw [iterForget, iterDesc_comp_iterInr,
      TauCeti.HopfAlgebra.productMap_comp_commutatorAlgHom, commutatorElement_one_left]
  rw [h1, h2, mul_one]

theorem ker_iterComm_succ_le (n : ℕ) :
    RingHom.ker (iterComm H (n + 1)).ofConv ≤ RingHom.ker (iterComm H n).ofConv := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  have h := congrArg (fun g : WithConv (H →ₐ[k] iterAlg H n) => g.ofConv a)
    (mapValue_iterForget H n)
  simp only [TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply] at h
  rw [← h, ha, map_zero]

theorem exists_eval_iterComm (g : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hg : g ∈ commutator (TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))) :
    ∃ (n : ℕ) (ev : iterAlg H n →ₐ[k] k), TauCeti.AlgHom.mapValue ev (iterComm H n) = g := by
  have hstep : ∀ (x y : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
      (g : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)),
      (∃ (n : ℕ) (ev : iterAlg H n →ₐ[k] k), TauCeti.AlgHom.mapValue ev (iterComm H n) = g) →
        ∃ (n : ℕ) (ev : iterAlg H n →ₐ[k] k),
          TauCeti.AlgHom.mapValue ev (iterComm H n) = g * ⁅x, y⁆ := by
    rintro x y g ⟨n, ev, rfl⟩
    refine ⟨n + 1, iterDesc H n ev (Algebra.TensorProduct.productMap x.ofConv y.ofConv), ?_⟩
    rw [iterComm_succ, map_mul]
    congr 1
    · apply WithConv.ofConv_injective
      simp only [TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
      rw [iterDesc_comp_iterInl]
    · apply WithConv.ofConv_injective
      simp only [TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
      rw [iterDesc_comp_iterInr, TauCeti.HopfAlgebra.productMap_comp_commutatorAlgHom]
  rw [commutator_def, Subgroup.commutator_def] at hg
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0, AlgHom.id k k, by rw [iterComm, map_one]⟩
  | mul_right g _ x hx ih =>
    obtain ⟨x₁, -, x₂, -, rfl⟩ := hx
    exact hstep x₁ x₂ g ih
  | mul_inv_cancel g _ x hx ih =>
    obtain ⟨x₁, -, x₂, -, rfl⟩ := hx
    rw [commutatorElement_inv]
    exact hstep x₂ x₁ g ih

end Iterated



section Injective

variable (H : CommHopfAlgCat.{u} k)

theorem exists_injective_iterComm [FiniteRingKrullDim H] (hdom : ∀ n, IsDomain (iterAlg H n))
    (hsep : ∀ a : H, (∀ g : commutator
      (TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)), g.val.ofConv a = 0) →
        a = 0) :
    ∃ N, Function.Injective (iterComm H N).ofConv := by
  let I : ℕ → Ideal H := fun n => RingHom.ker (iterComm H n).ofConv
  have hanti : Antitone I := antitone_nat_of_succ_le (ker_iterComm_succ_le H)
  have hprime : ∀ n, (I n).IsPrime := fun n => by
    have := hdom n
    exact RingHom.ker_isPrime _
  obtain ⟨N, hN⟩ := CFSG.exists_eq_of_antitone_isPrime I hanti hprime
  refine ⟨N, (injective_iff_map_eq_zero _).2 fun a ha => hsep a fun g => ?_⟩
  obtain ⟨n, ev, hev⟩ := exists_eval_iterComm H g.val g.property
  have han : a ∈ I n := by
    rcases le_total n N with h | h
    · exact hanti h ha
    · rw [hN n h]
      exact ha
  rw [← hev, TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    RingHom.mem_ker.1 han, map_zero]

end Injective


section Bound

open AlgebraicGeometry in
theorem isDomain_of_smooth_of_connectedSpace (k : Type u) [Field k] (A : Type u) [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] [ConnectedSpace (PrimeSpectrum A)] : IsDomain A :=
  CFSG.isDomain_of_smooth_of_connected (k := k) A

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem isDomain_semisimple (S : TauCeti.SemisimpleCommHopfAlgCat.{u} k) : IsDomain S.obj.obj := by
  have : Algebra.Smooth k S.obj.obj := S.property.smooth
  have : ConnectedSpace (PrimeSpectrum S.obj.obj) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k S.obj.obj
      S.property.reductive.geometricallyConnected
  exact isDomain_of_smooth_of_connectedSpace k S.obj.obj

omit [IsAlgClosed k] in
theorem finiteType_iterAlg (H : CommHopfAlgCat.{u} k) [Algebra.FiniteType k H] :
    ∀ n, Algebra.FiniteType k (iterAlg H n)
  | 0 => inferInstanceAs (Algebra.FiniteType k k)
  | n + 1 => by
    have := finiteType_iterAlg H n
    have : Algebra.FiniteType k (H ⊗[k] H) :=
      TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType _ _
    exact TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (iterAlg H n) (H ⊗[k] H)

theorem isDomain_iterAlg (H : CommHopfAlgCat.{u} k) [Algebra.FiniteType k H] [IsDomain H] :
    ∀ n, IsDomain (iterAlg H n)
  | 0 => inferInstanceAs (IsDomain k)
  | n + 1 => by
    have := isDomain_iterAlg H n
    have := finiteType_iterAlg H n
    have : IsDomain (H ⊗[k] H) := CFSG.isDomain_tensorProduct_of_isAlgClosed k H H
    have : Algebra.FiniteType k (H ⊗[k] H) :=
      TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType _ _
    exact CFSG.isDomain_tensorProduct_of_isAlgClosed k (iterAlg H n) (H ⊗[k] H)

theorem map_centerDefiningIdeal_le (D S : TauCeti.SemisimpleCommHopfAlgCat.{u} k)
    (q : D.obj.obj ⟶ S.obj.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q) :
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal D.obj.obj).toIdeal.map
        (q.hom : D.obj.obj →+* S.obj.obj) ≤
      (TauCeti.CommHopfAlgCat.centerDefiningIdeal S.obj.obj).toIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  let J := TauCeti.CommHopfAlgCat.centerDefiningIdeal S.obj.obj
  let E : CommAlgCat.{u} k := CommAlgCat.of k (S.obj.obj ⧸ J.toIdeal)
  let z : TauCeti.HopfAlgebra.points (R := k) (H := S.obj.obj) E :=
    toConv (Ideal.Quotient.mkₐ k J.toIdeal)
  have hz : TauCeti.HopfAlgebra.IsCentralPoint z := by
    rw [← TauCeti.CommHopfAlgCat.mem_centerPointsSubgroup_iff,
      TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro y hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (TauCeti.HopfIdeal.mem_toIdeal.mpr hy)
  let w : TauCeti.HopfAlgebra.points (R := k) (H := D.obj.obj) E :=
    TauCeti.AlgHom.mapDomain q.hom z
  have : Algebra.Smooth k D.obj.obj := D.property.smooth
  have : IsReduced D.obj.obj := TauCeti.isReduced_of_smooth k _
  have hft : ((q.hom : D.obj.obj →ₐ[k] S.obj.obj) : D.obj.obj →+* S.obj.obj).FiniteType :=
    hq.finite.finiteType
  have hw : TauCeti.HopfAlgebra.IsCentralPoint w := by
    apply CFSG.LieType.AlgebraicGroups.isCentralPoint_of_commute_base_points D.obj w
    intro p
    obtain ⟨p', hp'⟩ :=
      TauCeti.CommHopfAlgCat.mapPointsFunctor_app_surjective_of_faithfullyFlat k q hft
        hq.faithfullyFlat p
    obtain ⟨p₀, hp₀⟩ : ∃ p₀ : WithConv (S.obj.obj →ₐ[k] k),
        toConv (p₀.ofConv.comp (q.hom : D.obj.obj →ₐ[k] S.obj.obj)) = p :=
      ⟨p', by
        rw [← hp']
        exact (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_apply q _ p').symm⟩
    rw [← hp₀]
    have hnat : TauCeti.AlgHom.mapValue (Algebra.ofId k E)
        (toConv (p₀.ofConv.comp (q.hom : D.obj.obj →ₐ[k] S.obj.obj))) =
          TauCeti.AlgHom.mapDomain q.hom (TauCeti.AlgHom.mapValue (Algebra.ofId k E) p₀) := by
      apply WithConv.ofConv_injective
      simp only [TauCeti.AlgHom.mapValue_apply, TauCeti.AlgHom.mapDomain_apply,
        WithConv.ofConv_toConv, AlgHom.comp_assoc]
    rw [hnat]
    exact (hz.commute _).map (TauCeti.AlgHom.mapDomain q.hom)
  have hmem := (TauCeti.CommHopfAlgCat.mem_centerPointsSubgroup_iff _ E w).2 hw
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hmem
  have h0 := hmem x (TauCeti.HopfIdeal.mem_toIdeal.mp hx)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

theorem exists_bound_finrank_center (D : TauCeti.SemisimpleCommHopfAlgCat.{u} k)
    (hsep : ∀ a : D.obj.obj, (∀ g : commutator
      (TauCeti.HopfAlgebra.points (R := k) (H := D.obj.obj) (CommAlgCat.of k k)),
        g.val.ofConv a = 0) → a = 0) :
    ∃ b : ℕ, ∀ S : TauCeti.SemisimpleCommHopfAlgCat.{u} k,
      ∀ q : D.obj.obj ⟶ S.obj.obj, TauCeti.CommHopfAlgCat.IsCentralIsogeny q →
        Module.finrank k (TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra S.obj.obj) ≤ b := by
  let H := D.obj.obj
  have : IsDomain H := isDomain_semisimple D
  have : Algebra.FiniteType k H := TauCeti.FiniteTypeCommHopfAlgCat.finiteType D.obj
  have : FiniteRingKrullDim H := TauCeti.finiteRingKrullDim_of_finiteType k H
  obtain ⟨N, hN⟩ := exists_injective_iterComm H (isDomain_iterAlg H) hsep
  let P := iterAlg H N
  have : Algebra.FiniteType k P := finiteType_iterAlg H N
  let : Algebra H P := (iterComm H N).ofConv.toRingHom.toAlgebra
  have : IsScalarTower k H P :=
    IsScalarTower.of_algebraMap_eq fun x => ((iterComm H N).ofConv.commutes x).symm
  have : Algebra.FiniteType H P := Algebra.FiniteType.of_restrictScalars_finiteType k H P
  obtain ⟨d, hd⟩ := CFSG.exists_finrank_le_of_algHom H P hN
  let I := (TauCeti.CommHopfAlgCat.centerDefiningIdeal H).toIdeal
  have : Module.Finite k (H ⧸ I) := D.property.moduleFinite_centerCoordinate
  refine ⟨Module.finrank k (H ⧸ I) * d, fun S q hq => ?_⟩
  let B := S.obj.obj
  have : IsDomain B := isDomain_semisimple S
  let : Algebra H B := (q.hom : H →ₐ[k] B).toRingHom.toAlgebra
  have : IsScalarTower k H B :=
    IsScalarTower.of_algebraMap_eq fun x => ((q.hom : H →ₐ[k] B).commutes x).symm
  have : Module.Finite H B := hq.finite
  have : Module.Flat H B := hq.faithfullyFlat.flat
  obtain ⟨c, hc⟩ := exists_commutator_lift q hq
  have hc' : c.comp (q.hom : H →ₐ[k] B) =
      TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := H) := by
    have hinj := (faithfullyFlat_tensorProductMap (q.hom : H →ₐ[k] B) (q.hom : H →ₐ[k] B)
      hq.faithfullyFlat hq.faithfullyFlat).injective
    apply AlgHom.ext
    intro a
    apply hinj
    have h1 := congrArg (fun φ : B →ₐ[k] B ⊗[k] B => φ (q.hom a)) hc
    have h2 := congrArg (fun φ : H →ₐ[k] B ⊗[k] B => φ a)
      (TauCeti.HopfAlgebra.map_comp_commutatorAlgHom q.hom)
    simp only [AlgHom.comp_apply] at h1 h2
    change (Algebra.TensorProduct.map (q.hom : H →ₐ[k] B) (q.hom : H →ₐ[k] B)) (c (q.hom a)) =
      (Algebra.TensorProduct.map (q.hom : H →ₐ[k] B) (q.hom : H →ₐ[k] B))
        (TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := H) a)
    rw [h1]
    exact h2.symm
  have hcov := mapDomain_coverComm q c hc' N
  let φ : B →ₐ[H] P :=
    { (coverComm c N).ofConv.toRingHom with
      commutes' := fun a => by
        have := congrArg (fun g : WithConv (H →ₐ[k] iterAlg H N) => g.ofConv a) hcov
        simp only [TauCeti.AlgHom.mapDomain_apply, WithConv.ofConv_toConv,
          AlgHom.comp_apply] at this
        exact this }
  have hrank : Module.finrank H B ≤ d := hd B φ
  have hle : I.map (algebraMap H B) ≤
      (TauCeti.CommHopfAlgCat.centerDefiningIdeal S.obj.obj).toIdeal :=
    map_centerDefiningIdeal_le D S q hq
  have : Module.Finite k (B ⧸ I.map (algebraMap H B)) := CFSG.moduleFinite_quotient_map k I
  calc Module.finrank k (TauCeti.CommHopfAlgCat.centerCoordinateHopfAlgebra S.obj.obj)
      = Module.finrank k (B ⧸ (TauCeti.CommHopfAlgCat.centerDefiningIdeal S.obj.obj).toIdeal) :=
        rfl
    _ ≤ Module.finrank k (B ⧸ I.map (algebraMap H B)) :=
        LinearMap.finrank_le_finrank_of_surjective (f := (Ideal.Quotient.factorₐ k hle).toLinearMap)
          (Ideal.Quotient.factor_surjective hle)
    _ = Module.finrank k (H ⧸ I) * Module.finrank H B := CFSG.finrank_quotient_map_eq_mul k I
    _ ≤ Module.finrank k (H ⧸ I) * d := Nat.mul_le_mul_left _ hrank

end Bound

end CFSG.LieType.AlgebraicGroups.UniformCenter
