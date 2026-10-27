module

public import CFSG.Adapters.TauCetiExceptional.BigCellPoints

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem leadMinor_one {A : Type*} [CommRing A] {n : ℕ} (k : ℕ) :
    leadMinor (1 : Matrix (Fin n) (Fin n) A) k = 1 := by
  rw [leadMinor, Matrix.toBlock_one_self, Matrix.det_one]

theorem bigCellDet_one {A : Type*} [CommRing A] {n : ℕ} :
    bigCellDet (1 : Matrix (Fin n) (Fin n) A) = 1 :=
  Finset.prod_eq_one fun _ _ => leadMinor_one _

variable {L : Type} [Field L] [IsAlgClosed L]

theorem conj_mem_adjointGroup_of_oneParam
    (H : Subgroup (ModGL τ L))
    (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {z : ModGL τ L} (hz : z ∈ H) (u : L → ModGL τ L) (hu0 : u 0 = 1)
    (hadd : ∀ c d, u (c + d) = u c * u d) (huC : ∀ c, u c ∈ adjointGroup τ L)
    (A : Matrix (Fin (nLab τ)) (Fin (nLab τ)) (Polynomial L))
    (hA : ∀ c, (Polynomial.evalRingHom c).mapMatrix A =
      natMat τ L (u c : Module.End L (RootModule τ L))) (c : L) :
    z * u c * z⁻¹ ∈ adjointGroup τ L := by
  classical
  set F : Polynomial L := bigCellDet (Polynomial.C.mapMatrix (natMat τ L (z : Module.End L
    (RootModule τ L))) * A * Polynomial.C.mapMatrix (natMat τ L ((z⁻¹ : ModGL τ L) :
      Module.End L (RootModule τ L)))) with hFdef
  have hC : ∀ d (N : Matrix (Fin (nLab τ)) (Fin (nLab τ)) L),
      (Polynomial.evalRingHom d).mapMatrix (Polynomial.C.mapMatrix N) = N := fun d N => by
    ext i j
    simp
  have hF : ∀ d, F.eval d = bigCellDet (natMat τ L ((z * u d * z⁻¹ : ModGL τ L) :
      Module.End L (RootModule τ L))) := by
    intro d
    rw [← Polynomial.coe_evalRingHom, hFdef, map_bigCellDet, map_mul, map_mul, hC, hC, hA d]
    simp only [Units.val_mul, map_mul]
  have hF0 : F ≠ 0 := by
    intro h
    have h0 := hF 0
    rw [h, Polynomial.eval_zero, hu0, mul_one, mul_inv_cancel, Units.val_one, map_one,
      bigCellDet_one] at h0
    exact zero_ne_one h0
  have hgood : ∀ d, F.eval d ≠ 0 → z * u d * z⁻¹ ∈ adjointGroup τ L := fun d hd =>
    mem_adjointGroup_of_isUnit_bigCellDet _
      (hH _ (H.mul_mem (H.mul_mem hz (hCH (huC d))) (H.inv_mem hz))) (by rwa [← hF])
  obtain ⟨c₁, hc₁⟩ := Infinite.exists_notMem_finset
    (F.roots.toFinset ∪ F.roots.toFinset.image fun r => c - r)
  have h1 : F.eval c₁ ≠ 0 := fun h => hc₁ (Finset.mem_union_left _
    (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hF0).2 h)))
  have h2 : F.eval (c - c₁) ≠ 0 := fun h => hc₁ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨c - c₁, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hF0).2 h),
      by ring⟩))
  have hc : u c = u c₁ * u (c - c₁) := by rw [← hadd, add_sub_cancel]
  have e : z * u c * z⁻¹ = (z * u c₁ * z⁻¹) * (z * u (c - c₁) * z⁻¹) := by
    rw [hc]
    group
  rw [e]
  exact mul_mem (hgood _ h1) (hgood _ h2)

theorem conj_mem_adjointGroup
    (H : Subgroup (ModGL τ L)) (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {z : ModGL τ L} (hz : z ∈ H) {g : ModGL τ L} (hg : g ∈ adjointGroup τ L) :
    z * g * z⁻¹ ∈ adjointGroup τ L := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, c, hx | hy⟩ := hg
    · have hgx : g = xUnit τ L i c := Units.ext hx
      rw [hgx]
      refine conj_mem_adjointGroup_of_oneParam H hCH hH hz (xUnit τ L i) (xUnit_zero i)
        (xUnit_add i) (fun c => xUnit_mem_adjointGroup i c)
        (natMat τ (Polynomial L) (xOp τ (Polynomial L) i Polynomial.X)) (fun d => ?_) c
      rw [← natMat_of_baseChange (BaseChange.xOp (f := Polynomial.evalRingHom d) i Polynomial.X),
        Polynomial.coe_evalRingHom, Polynomial.eval_X]
      rfl
    · have hgy : g = yUnit τ L i c := Units.ext hy
      rw [hgy]
      refine conj_mem_adjointGroup_of_oneParam H hCH hH hz (yUnit τ L i) (yUnit_zero i)
        (yUnit_add i) (fun c => yUnit_mem_adjointGroup i c)
        (natMat τ (Polynomial L) (yOp τ (Polynomial L) i Polynomial.X)) (fun d => ?_) c
      rw [← natMat_of_baseChange (BaseChange.yOp (f := Polynomial.evalRingHom d) i Polynomial.X),
        Polynomial.coe_evalRingHom, Polynomial.eval_X]
      rfl
  | one => simp
  | mul g h _ _ hg hh =>
    have e : z * (g * h) * z⁻¹ = (z * g * z⁻¹) * (z * h * z⁻¹) := by group
    rw [e]
    exact mul_mem hg hh
  | inv g _ hg =>
    have e : z * g⁻¹ * z⁻¹ = (z * g * z⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hg

theorem le_normalizer_adjointGroup
    (H : Subgroup (ModGL τ L)) (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0) :
    H ≤ Subgroup.normalizer (adjointGroup τ L : Set (ModGL τ L)) := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_adjointGroup H hCH hH hz, fun hg => ?_⟩
  have := conj_mem_adjointGroup H hCH hH (H.inv_mem hz) hg
  rwa [inv_inv, show z⁻¹ * (z * g * z⁻¹) * z = g by group] at this

end CFSG.TauCetiBridge.BigCell
