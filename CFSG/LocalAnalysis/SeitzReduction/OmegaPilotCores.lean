module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCoresMonomial

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.SeitzReduction.SymplecticPilot (planeTorusParam mem_planeTorusParam)

section Frame

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {m : ℕ}

structure IsHypFrame (Q : QuadraticForm K (ι → K)) (a b : Fin m → ι) : Prop where
  hyp : ∀ k, IsHypCoord Q (a k) (b k)
  left_injective : Function.Injective a
  right_injective : Function.Injective b
  left_ne_right : ∀ k l, a k ≠ b l

@[expose] def frameEntry (a b : Fin m → ι) (t : Fin m → Kˣ) (i : ι) : Kˣ :=
  ∏ k, torusEntry (a k) (b k) (t k) i

theorem frameEntry_mul (a b : Fin m → ι) (t s : Fin m → Kˣ) (i : ι) :
    frameEntry a b (t * s) i = frameEntry a b t i * frameEntry a b s i := by
  simp only [frameEntry, Pi.mul_apply, torusEntry_mul, Finset.prod_mul_distrib]

theorem frameEntry_one (a b : Fin m → ι) (i : ι) : frameEntry a b (1 : Fin m → Kˣ) i = 1 := by
  simp only [frameEntry, Pi.one_apply, torusEntry_one, Finset.prod_const_one]

@[expose] noncomputable def frameLin (a b : Fin m → ι) :
    (Fin m → Kˣ) →* ((ι → K) ≃ₗ[K] (ι → K)) where
  toFun t := LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (frameEntry a b t i)
  map_one' := by
    ext v i
    change ((frameEntry a b 1 i : Kˣ) : K) * v i = v i
    rw [frameEntry_one, Units.val_one, one_mul]
  map_mul' t s := by
    ext v i
    change ((frameEntry a b (t * s) i : Kˣ) : K) * v i =
      (frameEntry a b t i : K) * ((frameEntry a b s i : K) * v i)
    rw [frameEntry_mul, Units.val_mul, mul_assoc]

theorem frameLin_apply (a b : Fin m → ι) (t : Fin m → Kˣ) (v : ι → K) (i : ι) :
    frameLin a b t v i = (frameEntry a b t i : K) * v i := rfl

theorem frameEntry_mulSingle (a b : Fin m → ι) (k : Fin m) (c : Kˣ) (i : ι) :
    frameEntry a b (Pi.mulSingle k c) i = torusEntry (a k) (b k) c i := by
  rw [frameEntry, Finset.prod_eq_single k (fun l _ hlk => by
    rw [Pi.mulSingle_eq_of_ne hlk, torusEntry_one]) (fun h => absurd (Finset.mem_univ k) h),
    Pi.mulSingle_eq_same]

theorem frameLin_mulSingle (a b : Fin m → ι) (k : Fin m) (c : Kˣ) :
    frameLin a b (Pi.mulSingle k c) = torusLin (a k) (b k) c := by
  ext v i
  rw [frameLin_apply, torusLin_apply, frameEntry_mulSingle]

theorem frameLin_comp_mulSingle (a b : Fin m → ι) (k : Fin m) :
    (frameLin (K := K) a b).comp (MonoidHom.mulSingle (fun _ : Fin m => Kˣ) k) =
      torusLin (a k) (b k) :=
  MonoidHom.ext fun c => frameLin_mulSingle a b k c

variable {Q : QuadraticForm K (ι → K)} {a b : Fin m → ι}

theorem IsHypFrame.frameEntry_left (h : IsHypFrame Q a b) (t : Fin m → Kˣ) (k : Fin m) :
    frameEntry a b t (a k) = t k := by
  rw [frameEntry, Finset.prod_eq_single k (fun l _ hlk => by
      unfold torusEntry
      rw [ite_eq_right (fun e => hlk (h.left_injective e).symm),
        ite_eq_right (h.left_ne_right k l)])
    (fun h' => absurd (Finset.mem_univ k) h')]
  unfold torusEntry
  rw [ite_eq_left rfl]

theorem IsHypFrame.frameEntry_right (h : IsHypFrame Q a b) (t : Fin m → Kˣ) (k : Fin m) :
    frameEntry a b t (b k) = (t k)⁻¹ := by
  rw [frameEntry, Finset.prod_eq_single k (fun l _ hlk => by
      unfold torusEntry
      rw [ite_eq_right (fun e => h.left_ne_right l k e.symm),
        ite_eq_right (fun e => hlk (h.right_injective e).symm)])
    (fun h' => absurd (Finset.mem_univ k) h')]
  unfold torusEntry
  rw [ite_eq_right (fun e => h.left_ne_right k k e.symm), ite_eq_left rfl]

theorem frameEntry_of_forall_ne (t : Fin m → Kˣ) {i : ι} (hia : ∀ k, i ≠ a k)
    (hib : ∀ k, i ≠ b k) : frameEntry a b t i = 1 := by
  refine Finset.prod_eq_one fun k _ => ?_
  unfold torusEntry
  rw [ite_eq_right (hia k), ite_eq_right (hib k)]

theorem IsHypFrame.frameLin_mem_orthDerived [Finite K] [CharP K 2] (h : IsHypFrame Q a b)
    (t : Fin m → Kˣ) : frameLin a b t ∈ orthDerived Q := by
  have hmem : t ∈ (orthDerived Q).comap (frameLin a b) := by
    rw [← Finset.univ_prod_mulSingle t]
    exact Subgroup.prod_mem _ fun k _ => by
      rw [Subgroup.mem_comap, frameLin_mulSingle]
      exact (h.hyp k).torusLin_mem_orthDerived (t k)
  exact hmem

theorem IsHypFrame.frameLin_mem_orthogonalGroup (h : IsHypFrame Q a b) (t : Fin m → Kˣ) :
    frameLin a b t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  have hmem : t ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).comap (frameLin a b) := by
    rw [← Finset.univ_prod_mulSingle t]
    exact Subgroup.prod_mem _ fun k _ => by
      rw [Subgroup.mem_comap, frameLin_mulSingle]
      exact (h.hyp k).torusLin_mem_orthogonalGroup (t k)
  exact hmem

theorem IsHypFrame.frameLin_injective (h : IsHypFrame Q a b) :
    Function.Injective (frameLin (K := K) a b) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  funext k
  have h1 := congrFun (LinearEquiv.congr_fun ht (Pi.single (a k) 1)) (a k)
  rw [frameLin_apply, h.frameEntry_left] at h1
  exact Units.ext (by simpa using h1)

end Frame

section FrameTorus

variable {K : Type} [Field K] {d m : ℕ}

@[expose] noncomputable def frameTorusOf (Q : QuadraticForm K (Fin d → K)) (a b : Fin m → Fin d)
    (P : Subgroup (Fin m → Kˣ)) : Subgroup (matrixProjectiveDerived Q) :=
  ((P.map (frameLin a b)).subgroupOf (orthDerived Q)).map (projHom Q)

variable {Q : QuadraticForm K (Fin d → K)} {a b : Fin m → Fin d}

theorem frameTorusOf_mono {P P' : Subgroup (Fin m → Kˣ)} (h : P ≤ P') :
    frameTorusOf Q a b P ≤ frameTorusOf Q a b P' :=
  map_mono fun _ hx => map_mono h hx

@[expose] def rootParam (k : Fin m) : Subgroup (Fin m → Kˣ) :=
  (MonoidHom.mulSingle (fun _ : Fin m => Kˣ) k).range

theorem mulSingle_mem_rootParam (k : Fin m) (c : Kˣ) : Pi.mulSingle k c ∈ rootParam (K := K) k :=
  ⟨c, rfl⟩

theorem frameTorusOf_rootParam (k : Fin m) :
    frameTorusOf Q a b (rootParam k) = pairTorusOf Q (a k) (b k) := by
  rw [frameTorusOf, pairTorusOf, rootParam, ← MonoidHom.range_comp, frameLin_comp_mulSingle]

@[expose] def levelParam (J : Finset (Fin m)) : Subgroup (Fin m → Kˣ) where
  carrier := {t | ∀ i ∈ J, ∀ j ∈ J, t i = t j}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := fun {t s} ht hs i hi j hj => by
    simp only [Pi.mul_apply, ht i hi j hj, hs i hi j hj]
  inv_mem' := fun {t} ht i hi j hj => by
    simp only [Pi.inv_apply, ht i hi j hj]

theorem mem_levelParam {J : Finset (Fin m)} {t : Fin m → Kˣ} :
    t ∈ levelParam (K := K) J ↔ ∀ i ∈ J, ∀ j ∈ J, t i = t j :=
  Iff.rfl

theorem levelParam_anti {J J' : Finset (Fin m)} (h : J ⊆ J') :
    levelParam (K := K) J' ≤ levelParam J :=
  fun _ ht i hi j hj => ht i (h hi) j (h hj)

theorem rootParam_le_planeTorusParam {k : Fin m} {I : Finset (Fin m)} (hk : k ∉ I) :
    rootParam (K := K) k ≤ planeTorusParam K I := by
  rintro _ ⟨c, rfl⟩ i hi
  have hik : i ≠ k := fun e => hk (e ▸ hi)
  exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Kˣ) hik c

theorem rootParam_le_levelParam {k : Fin m} {J : Finset (Fin m)} (hk : k ∉ J) :
    rootParam (K := K) k ≤ levelParam J := by
  rintro _ ⟨c, rfl⟩ i hi j hj
  have hik : i ≠ k := fun e => hk (e ▸ hi)
  have hjk : j ≠ k := fun e => hk (e ▸ hj)
  change (Pi.mulSingle k c : Fin m → Kˣ) i = (Pi.mulSingle k c : Fin m → Kˣ) j
  rw [Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Kˣ) hik c,
    Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Kˣ) hjk c]

variable [Finite K] [CharP K 2]

@[expose] noncomputable def IsHypFrame.frameHom (h : IsHypFrame Q a b) :
    (Fin m → Kˣ) →* matrixProjectiveDerived Q :=
  (projHom Q).comp ((frameLin a b).codRestrict (orthDerived Q) h.frameLin_mem_orthDerived)

theorem IsHypFrame.frameHom_apply (h : IsHypFrame Q a b) (t : Fin m → Kˣ) :
    h.frameHom t = projHom Q ⟨frameLin a b t, h.frameLin_mem_orthDerived t⟩ := rfl

theorem IsHypFrame.frameTorusOf_eq_map (h : IsHypFrame Q a b) (P : Subgroup (Fin m → Kˣ)) :
    frameTorusOf Q a b P = P.map h.frameHom := by
  ext x
  simp only [frameTorusOf, mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨y, ⟨t, ht, hty⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [IsHypFrame.frameHom_apply]
    congr 1
    exact Subtype.ext hty
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨frameLin a b t, h.frameLin_mem_orthDerived t⟩, ⟨t, ht, rfl⟩, rfl⟩

theorem IsHypFrame.frameHom_mem_frameTorusOf (h : IsHypFrame Q a b)
    {P : Subgroup (Fin m → Kˣ)} {t : Fin m → Kˣ} (ht : t ∈ P) :
    h.frameHom t ∈ frameTorusOf Q a b P := by
  rw [h.frameTorusOf_eq_map]
  exact ⟨t, ht, rfl⟩

theorem IsHypFrame.frameHom_injective (h : IsHypFrame Q a b) :
    Function.Injective h.frameHom := by
  intro t s hts
  have hm : m ≠ 0 ∨ m = 0 := (eq_or_ne m 0).symm
  rcases hm with hm | hm
  · obtain ⟨k⟩ : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    have hinj := projHom_injective (h.hyp k).exists_ne_zero hts
    exact h.frameLin_injective (congrArg Subtype.val hinj)
  · subst hm
    funext k
    exact k.elim0

theorem IsHypFrame.frameTorusOf_le_centralizer (h : IsHypFrame Q a b)
    (P P' : Subgroup (Fin m → Kˣ)) :
    frameTorusOf Q a b P ≤
      centralizer (frameTorusOf Q a b P' : Set (matrixProjectiveDerived Q)) := by
  rw [h.frameTorusOf_eq_map, h.frameTorusOf_eq_map]
  rintro _ ⟨t, -, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨s, -, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

end FrameTorus

end CFSG.SeitzReduction.OmegaPilot
