module

public import CFSG.CGT.PushingUpLit.T2K.Cohomology
public import CFSG.CGT.PushingUpLit.T2K.Sylow
public import CFSG.CGT.PushingUpLit.T2KR.GalDescent

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.CGT.PushingUpLit.BHS
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Twist

variable {L : Subgroup G} {n : ℕ}

@[expose] noncomputable def mulVecMul (A : Matrix (Fin 2) (Fin 2) (Fq n)) :
    Multiplicative (Fin 2 → Fq n) →* Multiplicative (Fin 2 → Fq n) :=
  AddMonoidHom.toMultiplicative (Matrix.mulVecLin A).toAddMonoidHom

theorem toAdd_mulVecMul (A : Matrix (Fin 2) (Fin 2) (Fq n)) (w : Multiplicative (Fin 2 → Fq n)) :
    Multiplicative.toAdd (mulVecMul A w) = A.mulVec (Multiplicative.toAdd w) := rfl

theorem mulVecMul_mulVecMul (A B : Matrix (Fin 2) (Fin 2) (Fq n))
    (w : Multiplicative (Fin 2 → Fq n)) : mulVecMul A (mulVecMul B w) = mulVecMul (A * B) w := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mulVecMul, Matrix.mulVec_mulVec]

theorem mulVecMul_one (w : Multiplicative (Fin 2 → Fq n)) : mulVecMul (1 : Matrix (Fin 2) (Fin 2) (Fq n)) w = w := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mulVecMul, Matrix.one_mulVec]

theorem coe_inv_mul (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    ((x₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n)) *
      (x₀ : Matrix (Fin 2) (Fin 2) (Fq n)) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_mul_inv (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    (x₀ : Matrix (Fin 2) (Fin 2) (Fq n)) *
      ((x₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n)) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

@[expose] noncomputable def NatData.twist (D : NatData L n)
    (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) : NatData L n where
  φ := (MulAut.conj x₀⁻¹).toMonoidHom.comp D.φ
  ψ := (mulVecMul ((x₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    Matrix (Fin 2) (Fin 2) (Fq n))).comp D.ψ
  φ_surj := (MulAut.conj x₀⁻¹).surjective.comp D.φ_surj
  φ_ker := fun l => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact D.φ_ker l
  ψ_surj := fun w => by
    obtain ⟨v, hv⟩ := D.ψ_surj (mulVecMul (x₀ : Matrix (Fin 2) (Fin 2) (Fq n)) w)
    refine ⟨v, ?_⟩
    simp only [MonoidHom.comp_apply, hv, mulVecMul_mulVecMul, coe_inv_mul, mulVecMul_one]
  ψ_ker := fun v => by
    simp only [MonoidHom.comp_apply]
    rw [← D.ψ_ker v]
    constructor
    · intro h
      have := congrArg (mulVecMul (x₀ : Matrix (Fin 2) (Fin 2) (Fq n))) h
      rw [map_one, mulVecMul_mulVecMul, coe_mul_inv, mulVecMul_one] at this
      exact this
    · intro h
      rw [h, map_one]
  ψ_conj := fun l v hv => by
    simp only [MonoidHom.comp_apply, D.ψ_conj l v hv]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mulVecMul, toAdd_ofAdd, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Matrix.SpecialLinearGroup.coe_mul, inv_inv, Matrix.mulVec_mulVec]
    congr 1
    rw [show (↑x₀⁻¹ * ↑(D.φ l) * ↑x₀ * ↑x₀⁻¹ : Matrix (Fin 2) (Fin 2) (Fq n)) =
      ↑x₀⁻¹ * ↑(D.φ l) * (↑x₀ * ↑x₀⁻¹) by simp only [mul_assoc], coe_mul_inv, mul_one]

end Twist

structure MData (G : Type) [Group G] [Finite G] (L M : Subgroup G) (n : ℕ) where
  D : NatData L n
  nat : NatBlock L n
  le : L ≤ M
  normal : M ≤ Subgroup.normalizer (L : Set G)
  C_G : Subgroup.centralizer (L : Set G) = ⊥
  Q_comm : ∀ a ∈ M ⊓ Subgroup.centralizer (blockU L : Set G),
    ∀ b ∈ M ⊓ Subgroup.centralizer (blockU L : Set G), a * b = b * a
  Q_sq : ∀ a ∈ M ⊓ Subgroup.centralizer (blockU L : Set G), a * a = 1

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem blockZ_eq : blockZ L = ⊥ :=
  eq_bot_iff.2 ((NatBlock.blockZ_le_centralizer L).trans H.C_G.le)

theorem psi_injective : Function.Injective H.D.ψ := by
  intro a b hab
  have h1 : H.D.ψ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
  have h2 := (H.D.ψ_ker (a⁻¹ * b)).1 h1
  rw [H.blockZ_eq, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.1 (Subtype.ext h2)

@[expose] noncomputable def psiEquiv : ↥(blockU L) ≃* Multiplicative (Fin 2 → Fq n) :=
  MulEquiv.ofBijective H.D.ψ ⟨H.psi_injective, H.D.ψ_surj⟩

@[expose] noncomputable def vec (w : Fin 2 → Fq n) : G :=
  ((H.psiEquiv.symm (Multiplicative.ofAdd w) : ↥(blockU L)) : G)

theorem vec_mem (w : Fin 2 → Fq n) : H.vec w ∈ blockU L :=
  (H.psiEquiv.symm (Multiplicative.ofAdd w)).2

theorem ψe_vec (w : Fin 2 → Fq n) : H.D.ψe (H.vec w) = w := by
  rw [H.D.ψe_of_mem (H.vec_mem w)]
  have : H.D.ψ ⟨H.vec w, H.vec_mem w⟩ = Multiplicative.ofAdd w := by
    have h := H.psiEquiv.apply_symm_apply (Multiplicative.ofAdd w)
    exact h
  rw [this, toAdd_ofAdd]

theorem vec_ψe {v : G} (hv : v ∈ blockU L) : H.vec (H.D.ψe v) = v := by
  have h1 : Multiplicative.ofAdd (H.D.ψe v) = H.psiEquiv ⟨v, hv⟩ := by
    rw [H.D.ψe_of_mem hv, ofAdd_toAdd]
    rfl
  unfold vec
  rw [h1, H.psiEquiv.symm_apply_apply]

theorem ψe_injOn {a b : G} (ha : a ∈ blockU L) (hb : b ∈ blockU L)
    (h : H.D.ψe a = H.D.ψe b) : a = b := by
  rw [← H.vec_ψe ha, ← H.vec_ψe hb, h]

theorem vec_add (w w' : Fin 2 → Fq n) : H.vec (w + w') = H.vec w * H.vec w' := by
  refine H.ψe_injOn (H.vec_mem _) (mul_mem (H.vec_mem _) (H.vec_mem _)) ?_
  rw [H.D.ψe_mul (H.vec_mem _) (H.vec_mem _), H.ψe_vec, H.ψe_vec, H.ψe_vec]

theorem vec_zero : H.vec 0 = 1 := by
  refine H.ψe_injOn (H.vec_mem _) (one_mem _) ?_
  rw [H.ψe_vec, H.D.ψe_one]

@[expose] noncomputable def act (m : G) (w : Fin 2 → Fq n) : Fin 2 → Fq n :=
  H.D.ψe (m * H.vec w * m⁻¹)

theorem conj_vec_mem {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) :
    m * H.vec w * m⁻¹ ∈ blockU L :=
  conj_mem_blockU (H.normal hm) (H.vec_mem w)

theorem act_add {m : G} (hm : m ∈ M) (w w' : Fin 2 → Fq n) :
    H.act m (w + w') = H.act m w + H.act m w' := by
  unfold act
  rw [H.vec_add, ← H.D.ψe_mul (H.conj_vec_mem hm w) (H.conj_vec_mem hm w')]
  congr 1
  group

theorem act_one (w : Fin 2 → Fq n) : H.act 1 w = w := by
  unfold act
  rw [one_mul, inv_one, mul_one, H.ψe_vec]

theorem act_mul {m m' : G} (hm' : m' ∈ M) (w : Fin 2 → Fq n) :
    H.act (m * m') w = H.act m (H.act m' w) := by
  unfold act
  rw [H.vec_ψe (H.conj_vec_mem hm' w)]
  congr 1
  group

theorem act_vec (m : G) {v : G} (hv : v ∈ blockU L) :
    H.act m (H.D.ψe v) = H.D.ψe (m * v * m⁻¹) := by
  unfold act
  rw [H.vec_ψe hv]

theorem act_inv_act {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) :
    H.act m⁻¹ (H.act m w) = w := by
  rw [← H.act_mul hm, inv_mul_cancel, H.act_one]

theorem act_act_inv {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) :
    H.act m (H.act m⁻¹ w) = w := by
  rw [← H.act_mul (M.inv_mem hm), mul_inv_cancel, H.act_one]

@[expose] noncomputable def actPerm (m : ↥M) : Equiv.Perm (Fin 2 → Fq n) where
  toFun := H.act m
  invFun := H.act (m : G)⁻¹
  left_inv w := H.act_inv_act m.2 w
  right_inv w := H.act_act_inv m.2 w

@[expose] noncomputable def actHom : ↥M →* Equiv.Perm (Fin 2 → Fq n) where
  toFun := H.actPerm
  map_one' := Equiv.ext fun w => H.act_one w
  map_mul' _ m' := Equiv.ext fun w => H.act_mul m'.2 w

theorem actHom_apply (m : ↥M) (w : Fin 2 → Fq n) : H.actHom m w = H.act m w := rfl

theorem actHom_add (m : ↥M) (w w' : Fin 2 → Fq n) :
    H.actHom m (w + w') = H.actHom m w + H.actHom m w' := H.act_add m.2 w w'

theorem act_L {l : G} (hl : l ∈ L) (w : Fin 2 → Fq n) :
    H.act l w = ((H.D.φ ⟨l, hl⟩ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
      Matrix (Fin 2) (Fin 2) (Fq n)).mulVec w := by
  unfold act
  rw [H.D.ψe_conj hl (H.vec_mem w), H.ψe_vec]

theorem actHom_L (l : ↥L) : H.actHom ⟨l, H.le l.2⟩ = slPerm (Fq n) (H.D.φ l) := by
  refine Equiv.ext fun w => ?_
  rw [H.actHom_apply, slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
  exact H.act_L l.2 w

theorem actHom_eq_one_iff (m : ↥M) :
    H.actHom m = 1 ↔ (m : G) ∈ Subgroup.centralizer (blockU L : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have h1 := congrArg (fun p : Equiv.Perm (Fin 2 → Fq n) => p (H.D.ψe v)) h
    simp only [H.actHom_apply, Equiv.Perm.one_apply] at h1
    rw [H.act_vec _ hv] at h1
    have h2 : (m : G) * v * (m : G)⁻¹ = v :=
      H.ψe_injOn (conj_mem_blockU (H.normal m.2) hv) hv h1
    calc v * (m : G) = ((m : G) * v * (m : G)⁻¹) * m := by rw [h2]
      _ = (m : G) * v := by group
  · intro hc
    refine Equiv.ext fun w => ?_
    show H.act m w = w
    have h1 : (m : G) * H.vec w * (m : G)⁻¹ = H.vec w := by
      have := Subgroup.mem_centralizer_iff.1 hc _ (H.vec_mem w)
      calc (m : G) * H.vec w * (m : G)⁻¹ = ((m : G) * H.vec w) * (m : G)⁻¹ := rfl
        _ = (H.vec w * (m : G)) * (m : G)⁻¹ := by rw [this]
        _ = H.vec w := by group
    unfold act
    rw [h1, H.ψe_vec]

theorem normalizes (m : ↥M) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    ∃ g' : Matrix.SpecialLinearGroup (Fin 2) (Fq n),
      (H.actHom m)⁻¹ * slPerm (Fq n) g * H.actHom m = slPerm (Fq n) g' := by
  set l : ↥L := H.D.sec g with hl
  have hm' : (m : G)⁻¹ * (l : G) * (m : G) ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (H.normal (M.inv_mem m.2)) (l : G)).1 l.2
    simpa using this
  refine ⟨H.D.φ ⟨(m : G)⁻¹ * (l : G) * (m : G), hm'⟩, ?_⟩
  rw [← H.actHom_L ⟨(m : G)⁻¹ * (l : G) * (m : G), hm'⟩]
  have e1 : (⟨(m : G)⁻¹ * (l : G) * (m : G), H.le hm'⟩ : ↥M) =
      m⁻¹ * ⟨(l : G), H.le l.2⟩ * m := Subtype.ext (by simp)
  have e2 : slPerm (Fq n) g = H.actHom ⟨(l : G), H.le l.2⟩ := by
    rw [H.actHom_L, hl, H.D.φ_sec]
  rw [e2, e1, map_mul, map_mul, map_inv]

theorem exists_sigma (m : ↥M) : ∃ σ : Fq n ≃+* Fq n, IsSemilinearWith (H.actHom m) σ :=
  exists_isSemilinearWith_of_normalizes (H.actHom m) (H.actHom_add m) (H.normalizes m)

@[expose] noncomputable def sigma (m : ↥M) : Fq n ≃+* Fq n := Classical.choose (H.exists_sigma m)

theorem isSemilinear_sigma (m : ↥M) : IsSemilinearWith (H.actHom m) (H.sigma m) :=
  Classical.choose_spec (H.exists_sigma m)

theorem sigma_unique {m : ↥M} {σ : Fq n ≃+* Fq n} (h : IsSemilinearWith (H.actHom m) σ) :
    σ = H.sigma m :=
  h.unique (H.isSemilinear_sigma m)

@[expose] noncomputable def chi : ↥M →* (Fq n ≃+* Fq n) where
  toFun := H.sigma
  map_one' := by
    symm
    exact H.sigma_unique (m := 1) (by rw [map_one]; exact IsSemilinearWith.one_perm)
  map_mul' a b := by
    symm
    exact H.sigma_unique (m := a * b)
      (by rw [map_mul]; exact (H.isSemilinear_sigma a).mul (H.isSemilinear_sigma b))

theorem isSemilinear_chi (m : ↥M) : IsSemilinearWith (H.actHom m) (H.chi m) :=
  H.isSemilinear_sigma m

theorem chi_eq_one_iff (m : ↥M) : H.chi m = 1 ↔ IsSemilinearWith (H.actHom m) (1 : Fq n ≃+* Fq n) :=
  ⟨fun h => h ▸ H.isSemilinear_chi m, fun h => (H.sigma_unique h).symm⟩

theorem chi_of_centralizer {m : ↥M} (hm : (m : G) ∈ Subgroup.centralizer (blockU L : Set G)) :
    H.chi m = 1 :=
  (H.chi_eq_one_iff m).2 (by rw [(H.actHom_eq_one_iff m).2 hm]; exact IsSemilinearWith.one_perm)

theorem chi_of_mem_L {l : G} (hl : l ∈ L) : H.chi ⟨l, H.le hl⟩ = 1 := by
  refine (H.chi_eq_one_iff _).2 ?_
  have := H.actHom_L ⟨l, hl⟩
  rw [this, slPerm_eq_semilinPerm]
  exact semilinPerm_isSemilinear _ _

abbrev QM (L M : Subgroup G) : Subgroup G :=
  M ⊓ Subgroup.centralizer (blockU L : Set G)

include H in
theorem mem_LQ_iff {m : G} :
    m ∈ L ⊔ QM L M ↔ ∃ l ∈ L, ∃ q ∈ QM L M, l * q = m := by
  have hLN : L ≤ Subgroup.normalizer ((QM L M : Subgroup G) : Set G) :=
    H.le.trans (NatBlock.le_normalizer_centralizer H.normal)
  have := Subgroup.coe_mul_of_left_le_normalizer_right L _ hLN
  rw [← SetLike.mem_coe, this]
  exact Set.mem_mul

theorem chi_of_mem_LQ {m : ↥M} (hm : (m : G) ∈ L ⊔ QM L M) : H.chi m = 1 := by
  obtain ⟨l, hl, q, hq, hlq⟩ := H.mem_LQ_iff.1 hm
  have : m = ⟨l, H.le hl⟩ * ⟨q, hq.1⟩ := Subtype.ext hlq.symm
  rw [this, map_mul, H.chi_of_mem_L hl, H.chi_of_centralizer hq.2, mul_one]

theorem mem_LQ_of_chi_eq_one {m : ↥M} {k : ℕ} (hk : m ^ 2 ^ k = 1) (hχ : H.chi m = 1) :
    (m : G) ∈ L ⊔ QM L M := by
  set π := H.actHom m with hπ
  have hlin : IsSemilinearWith π (1 : Fq n ≃+* Fq n) := (H.chi_eq_one_iff m).1 hχ
  have hadd : ∀ w w' : Fin 2 → Fq n, π (w + w') = π w + π w' := H.actHom_add m
  have hMv : ∀ w, (columnMat π).mulVec w = π w := fun w => by
    have := columnMat_mulVec hadd hlin w
    simpa using this
  have hdetpow : ∀ j : ℕ, columnDet (π ^ j) = columnDet π ^ j := by
    intro j
    induction j with
    | zero => simp [columnDet_one]
    | succ j ih =>
      rw [pow_succ', columnDet_mul hadd hlin (π ^ j)]
      have h1 : ∀ x : Fq n, (1 : Fq n ≃+* Fq n) x = x := fun x => rfl
      rw [h1, ih, pow_succ']
  have hπpow : π ^ 2 ^ k = 1 := by rw [hπ, ← map_pow, hk, map_one]
  have hdet1 : columnDet π = 1 := by
    apply eq_one_of_pow_two_pow_eq_one (k := k)
    rw [← hdetpow, hπpow, columnDet_one]
  have hdet : (columnMat π).det = 1 := by rw [det_columnMat, hdet1]
  set g : Matrix.SpecialLinearGroup (Fin 2) (Fq n) := ⟨columnMat π, hdet⟩ with hg
  have hslπ : slPerm (Fq n) g = π := by
    refine Equiv.ext fun w => ?_
    rw [slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
    exact hMv w
  obtain ⟨l, hl⟩ := H.D.φ_surj g
  have hπl : H.actHom ⟨(l : G), H.le l.2⟩ = π := by rw [H.actHom_L, hl, hslπ]
  have hq : H.actHom ((⟨(l : G), H.le l.2⟩ : ↥M)⁻¹ * m) = 1 := by
    rw [map_mul, map_inv, hπl, inv_mul_cancel]
  have hqC := (H.actHom_eq_one_iff _).1 hq
  rw [H.mem_LQ_iff]
  refine ⟨l, l.2, (l : G)⁻¹ * m, ⟨M.mul_mem (M.inv_mem (H.le l.2)) m.2, hqC⟩, by group⟩

include H in
theorem relIndex_le_two {B : Subgroup G} (hBM : B ≤ M) (hB2 : ∀ x ∈ B, x * x = 1) :
    (B ⊓ (L ⊔ QM L M)).relIndex B ≤ 2 := by
  let f : ↥B →* (Fq n ≃+* Fq n) := H.chi.comp (Subgroup.inclusion hBM)
  have hker : f.ker = (B ⊓ (L ⊔ QM L M)).subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have hx2 : (Subgroup.inclusion hBM x) ^ 2 ^ 1 = 1 :=
        Subtype.ext (by simpa [pow_two] using hB2 x x.2)
      exact H.mem_LQ_of_chi_eq_one hx2 hx
    · intro hx
      exact H.chi_of_mem_LQ hx.2
  have h1 : (B ⊓ (L ⊔ QM L M)).relIndex B = f.ker.index := by
    rw [hker]
    rfl
  rw [h1, Subgroup.index_ker]
  have hsq : ∀ y ∈ f.range, y * y = 1 := by
    rintro _ ⟨x, rfl⟩
    have : x * x = 1 := Subtype.ext (hB2 x x.2)
    rw [← map_mul, this, map_one]
  calc Nat.card f.range ≤ Nat.card {τ : Fq n ≃+* Fq n // τ * τ = 1} :=
        Nat.card_le_card_of_injective (fun y => ⟨y.1, hsq y.1 y.2⟩)
          (fun a b h => Subtype.ext
            (congrArg (fun z : {τ : Fq n ≃+* Fq n // τ * τ = 1} => z.1) h))
    _ ≤ 2 := card_involutions_le_two n

theorem chi_ne_one_of_not_mem {x : ↥M} (hx2 : x * x = 1) (hx : (x : G) ∉ L ⊔ QM L M) :
    H.chi x ≠ 1 := fun h =>
  hx (H.mem_LQ_of_chi_eq_one (k := 1) (by simpa [pow_two] using hx2) h)

theorem chi_involution {x : ↥M} (hx2 : x * x = 1) (y : Fq n) : H.chi x (H.chi x y) = y := by
  have : H.chi x * H.chi x = 1 := by rw [← map_mul, hx2, map_one]
  exact congrArg (fun s : Fq n ≃+* Fq n => s y) this

include H in
theorem even_of_not_mem {x : ↥M} (hx2 : x * x = 1) (hx : (x : G) ∉ L ⊔ QM L M) : Even n :=
  even_of_involution (by have := H.nat.two_le; omega) (H.chi x) (H.chi_ne_one_of_not_mem hx2 hx)
    (H.chi_involution hx2)

theorem card_fixed_actHom {b : ↥M} (hb : b * b = 1) (hχ : H.chi b ≠ 1) :
    Nat.card {w : Fin 2 → Fq n // H.actHom b w = w} = Nat.card (Fq n) := by
  let β : (Fin 2 → Fq n) →+ (Fin 2 → Fq n) := AddMonoidHom.mk' (H.actHom b) (H.actHom_add b)
  have hβ : ∀ (c : Fq n) (w : Fin 2 → Fq n), β (c • w) = H.chi b c • β w :=
    fun c w => H.isSemilinear_chi b c w
  have hββ : ∀ w, β (β w) = w := fun w => by
    have := congrArg (fun p : Equiv.Perm (Fin 2 → Fq n) => p w) (show H.actHom b * H.actHom b = 1 by
      rw [← map_mul, hb, map_one])
    exact this
  have h := card_eq_sq_card_fixed (H.chi b) hχ (H.chi_involution hb) β hβ hββ
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h).symm

theorem twist_ψe (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) {v : G} (hv : v ∈ blockU L) :
    (NatData.twist H.D x₀).ψe v = ((x₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
      Matrix (Fin 2) (Fin 2) (Fq n)).mulVec (H.D.ψe v) := by
  rw [(NatData.twist H.D x₀).ψe_of_mem hv, H.D.ψe_of_mem hv]
  rfl

@[expose] noncomputable def twist (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    MData G L M n :=
  { H with D := NatData.twist H.D x₀ }

theorem twist_vec (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (w : Fin 2 → Fq n) :
    (H.twist x₀).vec w = H.vec ((x₀ : Matrix (Fin 2) (Fin 2) (Fq n)).mulVec w) := by
  refine (H.twist x₀).ψe_injOn ((H.twist x₀).vec_mem w) (H.vec_mem _) ?_
  rw [(H.twist x₀).ψe_vec]
  show w = (NatData.twist H.D x₀).ψe (H.vec _)
  rw [H.twist_ψe x₀ (H.vec_mem _), H.ψe_vec, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]

theorem twist_actHom (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (m : ↥M) :
    (H.twist x₀).actHom m = slPerm (Fq n) x₀⁻¹ * H.actHom m * slPerm (Fq n) x₀ := by
  refine Equiv.ext fun w => ?_
  show (H.twist x₀).act m w = _
  unfold act
  rw [H.twist_vec x₀ w]
  show (NatData.twist H.D x₀).ψe _ = _
  rw [H.twist_ψe x₀ (H.conj_vec_mem m.2 _)]
  simp only [Equiv.Perm.mul_apply, slPerm_apply, Matrix.SpecialLinearGroup.smul_def,
    actHom_apply]
  rfl

end MData

end CFSG.CGT.PushingUpLit.T2KR
