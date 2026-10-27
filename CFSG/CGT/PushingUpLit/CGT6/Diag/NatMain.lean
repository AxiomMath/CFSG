module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs
public import CFSG.CGT.PushingUpLit.CGT6.Diag.NatMatrix

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Nat

open Matrix Multiplicative CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open scoped MatrixGroups Pointwise

section Cols

variable {F : Type} [Field F]

def colMat (a b : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := !![a 0, b 0; a 1, b 1]

theorem mul_colMat (s : Matrix (Fin 2) (Fin 2) F) (a b : Fin 2 → F) :
    s * colMat a b = colMat (s.mulVec a) (s.mulVec b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def colEquiv : Multiplicative (Fin 2 → F) × Multiplicative (Fin 2 → F) ≃* Mg F where
  toFun x := ofAdd (colMat (toAdd x.1) (toAdd x.2))
  invFun M := (ofAdd (fun i => toAdd M i 0), ofAdd (fun i => toAdd M i 1))
  left_inv x := by
    ext i <;> fin_cases i <;> rfl
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

end Cols

section Coord

variable {V : Type} [CommGroup V] {K K' : Subgroup (MulAut V)} {n : ℕ}

theorem exists_coord (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (θ : ↥K ≃* SL(2, Fq n))
    (W : Subgroup V) (hW : IsNatSectionWith (slAct n) θ W ⊥) {k₀ : MulAut V} (hk₀ : k₀ ∈ K')
    (h1 : W ⊓ diagImg k₀ W = ⊥) (h2 : W ⊔ diagImg k₀ W = ⊤) :
    ∃ e : V ≃* Mg (Fq n), KEquivariant θ e := by
  obtain ⟨hWinv, β, hβs, hβk, hβe⟩ := hW
  have hker : β.ker = ⊥ := by simp [hβk]
  have hβi : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hker
  let eW : ↥W ≃* Multiplicative (Fin 2 → Fq n) := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  let Φ : ↥W × ↥W →* V :=
    { toFun := fun x => (x.1 : V) * k₀ (x.2 : V)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hΦi : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : V) * k₀ (b : V) = 1 := hab
    have hakb : (a : V) = (k₀ (b : V))⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have ha : (a : V) ∈ W ⊓ diagImg k₀ W := by
      refine ⟨a.2, (b : V)⁻¹, W.inv_mem b.2, ?_⟩
      show k₀ ((b : V)⁻¹) = a
      rw [hakb, map_inv]
    rw [h1, Subgroup.mem_bot] at ha
    have hb : k₀ (b : V) = 1 := by rw [ha, one_mul] at hab'; exact hab'
    have hb' : (b : V) = 1 := (map_eq_one_iff k₀ k₀.injective).mp hb
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb')
  have hΦs : Function.Surjective Φ := by
    intro v
    have hv : v ∈ W ⊔ diagImg k₀ W := by rw [h2]; exact Subgroup.mem_top v
    obtain ⟨y, hy, z, ⟨w, hw, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hv
    exact ⟨(⟨y, hy⟩, ⟨w, hw⟩), rfl⟩
  let eΦ : ↥W × ↥W ≃* V := MulEquiv.ofBijective Φ ⟨hΦi, hΦs⟩
  let e : V ≃* Mg (Fq n) := eΦ.symm.trans ((eW.prodCongr eW).trans colEquiv)
  have he : ∀ y : ↥W × ↥W, e (Φ y) = colEquiv (eW y.1, eW y.2) := by
    intro y
    show (eW.prodCongr eW).trans colEquiv (eΦ.symm (eΦ y)) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  refine ⟨e, fun k v => ?_⟩
  obtain ⟨y, rfl⟩ := hΦs v
  have hkΦ : (k : MulAut V) (Φ y) = Φ (⟨(k : MulAut V) (y.1 : V), hWinv _ k.2 _ y.1.2⟩,
      ⟨(k : MulAut V) (y.2 : V), hWinv _ k.2 _ y.2.2⟩) := by
    show (k : MulAut V) ((y.1 : V) * k₀ (y.2 : V)) =
      (k : MulAut V) (y.1 : V) * k₀ ((k : MulAut V) (y.2 : V))
    rw [map_mul]
    congr 1
    exact congrArg (fun φ : MulAut V => φ (y.2 : V)) (hcomm k k.2 k₀ hk₀)
  have hy1 := hβe k y.1 (hWinv _ k.2 _ y.1.2)
  have hy2 := hβe k y.2 (hWinv _ k.2 _ y.2.2)
  rw [hkΦ, he, he]
  show colEquiv (β _, β _) = _
  rw [hy1, hy2]
  show ofAdd (colMat _ _) = ofAdd (_ * colMat _ _)
  rw [mul_colMat]
  rfl

theorem commV_eq_top {F : Type} [Field F] (θ : ↥K ≃* SL(2, F)) (e : V ≃* Mg F)
    (he : KEquivariant θ e) : commV K = ⊤ := by
  rw [eq_top_iff]
  intro v _
  let T : AddSubgroup (Matrix (Fin 2) (Fin 2) F) :=
    { carrier := {M | e.symm (ofAdd M) ∈ commV K}
      zero_mem' := by
        show e.symm (ofAdd 0) ∈ commV K
        rw [ofAdd_zero, map_one]
        exact one_mem _
      add_mem' := fun {M N} hM hN => by
        show e.symm (ofAdd (M + N)) ∈ commV K
        rw [ofAdd_add, map_mul]
        exact mul_mem hM hN
      neg_mem' := fun {M} hM => by
        show e.symm (ofAdd (-M)) ∈ commV K
        rw [ofAdd_neg, map_inv]
        exact inv_mem hM }
  have hT : ∀ (s : SL(2, F)) (N : Matrix (Fin 2) (Fin 2) F),
      (s : Matrix (Fin 2) (Fin 2) F) * N - N ∈ T := by
    intro s N
    show e.symm (ofAdd ((s : Matrix (Fin 2) (Fin 2) F) * N - N)) ∈ commV K
    have h : e.symm (ofAdd ((s : Matrix (Fin 2) (Fin 2) F) * N - N)) =
        ((θ.symm s : ↥K) : MulAut V) (e.symm (ofAdd N)) * (e.symm (ofAdd N))⁻¹ := by
      rw [sub_eq_add_neg, ofAdd_add, map_mul, symm_smul θ e he s N, ofAdd_neg, map_inv]
    rw [h]
    exact Subgroup.subset_closure ⟨_, (θ.symm s).2, _, rfl⟩
  have h1 := mem_of_forall_sub T hT (toAdd (e v))
  have h2 : e.symm (ofAdd (toAdd (e v))) = v := by simp
  exact h2 ▸ h1

theorem inf_eq_bot {F : Type} [Field F] [CharP F 2] (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (θ : ↥K ≃* SL(2, F)) : K ⊓ K' = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxK'⟩
  rw [Subgroup.mem_bot]
  have hz : θ ⟨x, hxK⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨k, rfl⟩ := θ.surjective s
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm k k.2 x hxK')
  rw [sl2_center_eq_bot F, Subgroup.mem_bot] at hz
  have h1 : (⟨x, hxK⟩ : ↥K) = 1 := θ.injective (hz.trans (map_one θ).symm)
  exact congrArg Subtype.val h1

theorem exists_prodEquiv {S : Type*} [Group S] (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hinf : K ⊓ K' = ⊥) (θ : ↥K ≃* S) (C : ↥K' ≃* S) :
    ∃ ι : S × S ≃* ↥(K ⊔ K'), ∀ (k : ↥K) (g : ↥K'),
      ((ι (θ k, C g) : ↥(K ⊔ K')) : MulAut V) = (k : MulAut V) * g := by
  let f : S × S → ↥(K ⊔ K') := fun p =>
    ⟨(θ.symm p.1 : MulAut V) * (C.symm p.2 : MulAut V),
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (θ.symm p.1).2)
        (Subgroup.mem_sup_right (C.symm p.2).2)⟩
  have hf : ∀ p q, f (p * q) = f p * f q := by
    intro p q
    apply Subtype.ext
    have hc := hcomm (θ.symm q.1) (θ.symm q.1).2 (C.symm p.2) (C.symm p.2).2
    simp only [f, Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (θ.symm q.1 : MulAut V), hc, mul_assoc]
  let ι₀ : S × S →* ↥(K ⊔ K') := MonoidHom.mk' f hf
  have hinj : Function.Injective ι₀ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (θ.symm a : MulAut V) * (C.symm b : MulAut V) = 1 := congrArg Subtype.val hab
    have hmem : (θ.symm a : MulAut V) ∈ K ⊓ K' := by
      refine ⟨(θ.symm a).2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hab']
      exact K'.inv_mem (C.symm b).2
    rw [hinf, Subgroup.mem_bot] at hmem
    have ha : θ.symm a = 1 := Subtype.ext hmem
    have hb' : (C.symm b : MulAut V) = 1 := by rw [hmem, one_mul] at hab'; exact hab'
    have hb : C.symm b = 1 := Subtype.ext hb'
    exact Prod.ext (by simpa using congrArg θ ha) (by simpa using congrArg C hb)
  have hLE : K ≤ Subgroup.normalizer (K' : Set (MulAut V)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : x * h = h * x := hcomm x hx h hh
      rw [h1, mul_inv_cancel_right]
      exact hh
    · intro hh
      have h2 := hcomm x hx _ hh
      have h3 : x * (x * h * x⁻¹) = x * h := by rw [h2]; group
      have h4 : x * h * x⁻¹ = h := mul_left_cancel h3
      rwa [h4] at hh
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right K K' hLE
  have hsup : ∀ x ∈ K ⊔ K', ∃ k ∈ K, ∃ g ∈ K', k * g = x := by
    intro x hx
    have : x ∈ ((K : Set (MulAut V)) * (K' : Set (MulAut V))) := by rw [← hset]; exact hx
    obtain ⟨k, hk, g, hg, rfl⟩ := this
    exact ⟨k, hk, g, hg, rfl⟩
  have hsurj : Function.Surjective ι₀ := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk, g, hg, rfl⟩ := hsup x hx
    refine ⟨(θ ⟨k, hk⟩, C ⟨g, hg⟩), Subtype.ext ?_⟩
    show (θ.symm (θ ⟨k, hk⟩) : MulAut V) * (C.symm (C ⟨g, hg⟩) : MulAut V) = k * g
    simp
  refine ⟨MulEquiv.ofBijective ι₀ ⟨hinj, hsurj⟩, fun k g => ?_⟩
  show (θ.symm (θ k) : MulAut V) * (C.symm (C g) : MulAut V) = k * g
  simp

end Coord

end CFSG.CGT.PushingUpLit.CGT6.Diag.Nat

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.CGT.PushingUpLit.CGT6.Diag.Nat CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

theorem diagModNat_holds : DiagMod_nat := by
  intro V _ _ _ K K' n _ hcomm hperf hcard θ W hW k₀ hk₀ h1 h2
  obtain ⟨e, he⟩ := exists_coord hcomm θ W hW hk₀ h1 h2
  obtain ⟨C, hC⟩ := exists_rightAction θ e hcomm hperf hcard he
  obtain ⟨ι, hι⟩ := exists_prodEquiv hcomm (inf_eq_bot hcomm θ) θ C
  have htop : commV (K ⊔ K') = ⊤ :=
    eq_top_iff.mpr (le_of_eq_of_le (commV_eq_top θ e he).symm (commV_mono le_sup_left))
  refine ⟨fun x hx p hp => commV_invariant hx hp, ι.symm,
    e.toMonoidHom.comp (commV (K ⊔ K')).subtype, ?_, ?_, ?_⟩
  · intro m
    refine ⟨⟨e.symm m, ?_⟩, by simp⟩
    rw [htop]
    exact Subgroup.mem_top _
  · ext p
    simp
  · intro x p hp
    obtain ⟨⟨A, B⟩, hx⟩ := ι.surjective x
    obtain ⟨k, rfl⟩ := θ.surjective A
    obtain ⟨g, rfl⟩ := C.surjective B
    have hsymm : ι.symm x = (θ k, C g) := by rw [← hx, ι.symm_apply_apply]
    have hxv : (x : MulAut V) = (k : MulAut V) * g := by rw [← hx]; exact hι k g
    show e ((x : MulAut V) p) = omegaPlusAct n (ι.symm x) (e p)
    rw [hsymm, hxv, MulAut.mul_apply, he, hC]
    simp only [omegaPlusAct, mul_assoc, toAdd_ofAdd]

end CFSG.CGT.PushingUpLit.CGT6
