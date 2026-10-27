module

public import CFSG.CGT.PushingUpLit.T2K.Setup
public import CFSG.CGT.PushingUpLit.BHS.SL2Normalizer

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

theorem eq_of_forall_mulVec {F : Type} [Field F] {g h : Matrix.SpecialLinearGroup (Fin 2) F}
    (hgh : ∀ v : Fin 2 → F,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec v = (h : Matrix (Fin 2) (Fin 2) F).mulVec v) :
    g = h := by
  apply Subtype.ext
  ext i j
  have := congrFun (hgh (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

@[expose] def conjU {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    ↥(blockU L) →* ↥(blockU L) :=
  MonoidHom.mk' (fun v => ⟨x * v * x⁻¹, conj_mem_blockU hx v.2⟩) fun a b => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

@[simp] theorem coe_conjU {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (v : ↥(blockU L)) :
    ((conjU hx v : ↥(blockU L)) : G) = x * v * x⁻¹ := rfl

@[expose] def conjL {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) : ↥L :=
  ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx l).1 l.2⟩

@[simp] theorem coe_conjL {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    ((conjL hx l : ↥L) : G) = x * l * x⁻¹ := rfl

namespace NatData

variable (D : NatData L n)

theorem ψ_conjU (l : ↥L) (v : ↥(blockU L)) :
    D.ψ (conjU (Subgroup.le_normalizer l.2) v) = Multiplicative.ofAdd
      (((D.φ l : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (D.ψ v))) :=
  D.ψ_conj l v _

theorem ψ_conjU_twisted {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (l : ↥L)
    (v : ↥(blockU L)) :
    D.ψ (conjU hx (conjU (Subgroup.le_normalizer l.2) v)) = Multiplicative.ofAdd
      (((D.φ (conjL hx l) : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd (D.ψ (conjU hx v)))) := by
  have e : conjU hx (conjU (Subgroup.le_normalizer l.2) v) =
      conjU (Subgroup.le_normalizer (conjL hx l).2) (conjU hx v) := by
    apply Subtype.ext
    simp only [coe_conjU, coe_conjL]
    group
  rw [e]
  exact D.ψ_conj (conjL hx l) (conjU hx v) _

theorem φ_conjL_eq {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (htriv : ∀ v : ↥(blockU L), D.ψ (conjU hx v) = D.ψ v) (l : ↥L) :
    D.φ (conjL hx l) = D.φ l := by
  apply eq_of_forall_mulVec
  intro w
  obtain ⟨v, hv⟩ := D.ψ_surj (Multiplicative.ofAdd w)
  have h1 := D.ψ_conjU_twisted hx l v
  have h2 := D.ψ_conjU l v
  rw [htriv (conjU (Subgroup.le_normalizer l.2) v), htriv v, h2] at h1
  have h3 := congrArg Multiplicative.toAdd h1
  rw [hv] at h3
  simpa using h3.symm

theorem φ_conjL_eq_of_comm {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ l : ↥L, (⁅x, (l : G)⁆ : G) ∈ oTwoIn L) (l : ↥L) : D.φ (conjL hx l) = D.φ l := by
  have e : conjL hx l = (conjL hx l * l⁻¹) * l := by group
  have hker : D.φ (conjL hx l * l⁻¹) = 1 := by
    apply (D.φ_ker _).2
    have : (((conjL hx l * l⁻¹ : ↥L)) : G) = ⁅x, (l : G)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact hc l
  rw [e, map_mul, hker, one_mul]

theorem comm_mem_oTwoIn {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (htriv : ∀ v : ↥(blockU L), D.ψ (conjU hx v) = D.ψ v) (l : ↥L) :
    (⁅x, (l : G)⁆ : G) ∈ oTwoIn L := by
  have hc : D.φ (conjL hx l * l⁻¹) = 1 := by
    rw [map_mul, map_inv, D.φ_conjL_eq hx htriv l, mul_inv_cancel]
  have := (D.φ_ker _).1 hc
  have e : (((conjL hx l * l⁻¹ : ↥L)) : G) = ⁅x, (l : G)⁆ := by
    simp [commutatorElement_def]
  rwa [e] at this

theorem exists_scalar {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ l : ↥L, (⁅x, (l : G)⁆ : G) ∈ oTwoIn L) :
    ∃ a : GaloisField 2 n, ∀ v : ↥(blockU L),
      D.ψ (conjU hx v) = Multiplicative.ofAdd (a • Multiplicative.toAdd (D.ψ v)) := by
  classical
  have hker : D.ψ.ker ≤ (D.ψ.comp (conjU hx)).ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    rw [MonoidHom.comp_apply]
    apply (D.ψ_ker _).2
    exact conj_mem_blockZ hx ((D.ψ_ker v).1 hv)
  let τ : Multiplicative (Fin 2 → GaloisField 2 n) →* Multiplicative (Fin 2 → GaloisField 2 n) :=
    MonoidHom.liftOfSurjective D.ψ D.ψ_surj ⟨D.ψ.comp (conjU hx), hker⟩
  have hτ : ∀ v, τ (D.ψ v) = D.ψ (conjU hx v) := fun v =>
    MonoidHom.liftOfRightInverse_comp_apply D.ψ _ (Function.rightInverse_surjInv D.ψ_surj)
      ⟨D.ψ.comp (conjU hx), hker⟩ v
  let c : (Fin 2 → GaloisField 2 n) →+ (Fin 2 → GaloisField 2 n) :=
    AddMonoidHom.mk' (fun w => Multiplicative.toAdd (τ (Multiplicative.ofAdd w))) fun a b => by
      simp [ofAdd_add, map_mul, toAdd_mul]
  have hcomm : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (w : Fin 2 → GaloisField 2 n),
      c ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w) =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (c w) := by
    intro g w
    obtain ⟨l, rfl⟩ := D.φ_surj g
    obtain ⟨v, hv⟩ := D.ψ_surj (Multiplicative.ofAdd w)
    have hcw : c w = Multiplicative.toAdd (D.ψ (conjU hx v)) := by
      show Multiplicative.toAdd (τ (Multiplicative.ofAdd w)) = _
      rw [← hv, hτ]
    have h1 : ((D.φ l : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w =
        Multiplicative.toAdd (D.ψ (conjU (Subgroup.le_normalizer l.2) v)) := by
      rw [D.ψ_conjU, hv]
      simp
    have hLHS : c (((D.φ l : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w) =
        Multiplicative.toAdd (D.ψ (conjU hx (conjU (Subgroup.le_normalizer l.2) v))) := by
      rw [h1]
      show Multiplicative.toAdd (τ (Multiplicative.ofAdd (Multiplicative.toAdd (D.ψ _)))) = _
      rw [ofAdd_toAdd, hτ]
    rw [hLHS, D.ψ_conjU_twisted hx l v, toAdd_ofAdd, D.φ_conjL_eq_of_comm hx hc l, hcw]
  obtain ⟨a, ha⟩ := BHS.exists_scalar_of_commutes_sl2 c hcomm
  refine ⟨a, fun v => ?_⟩
  rw [← hτ]
  have : τ (D.ψ v) = Multiplicative.ofAdd (c (Multiplicative.toAdd (D.ψ v))) := by
    show _ = Multiplicative.ofAdd (Multiplicative.toAdd
      (τ (Multiplicative.ofAdd (Multiplicative.toAdd (D.ψ v)))))
    simp
  rw [this, ha]

theorem ψ_conjU_pow {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) {a : GaloisField 2 n}
    (ha : ∀ v : ↥(blockU L),
      D.ψ (conjU hx v) = Multiplicative.ofAdd (a • Multiplicative.toAdd (D.ψ v)))
    (m : ℕ) (v : ↥(blockU L)) :
    D.ψ (conjU (Subgroup.pow_mem _ hx m) v) =
      Multiplicative.ofAdd (a ^ m • Multiplicative.toAdd (D.ψ v)) := by
  induction m generalizing v with
  | zero =>
    have : conjU (Subgroup.pow_mem _ hx 0) v = v := Subtype.ext (by simp)
    rw [this]
    simp
  | succ m ih =>
    have e : conjU (Subgroup.pow_mem _ hx (m + 1)) v =
        conjU hx (conjU (Subgroup.pow_mem _ hx m) v) := by
      apply Subtype.ext
      simp only [coe_conjU]
      rw [pow_succ']
      group
    rw [e, ha, ih, toAdd_ofAdd, smul_smul, pow_succ']

theorem scalar_eq_one {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) {a : GaloisField 2 n}
    (ha : ∀ v : ↥(blockU L),
      D.ψ (conjU hx v) = Multiplicative.ofAdd (a • Multiplicative.toAdd (D.ψ v)))
    {k : ℕ} (hk : ∀ v ∈ blockU L, x ^ 2 ^ k * v * (x ^ 2 ^ k)⁻¹ = v) : a = 1 := by
  obtain ⟨v, hv⟩ := D.ψ_surj (Multiplicative.ofAdd (Pi.single 0 1))
  have h1 := D.ψ_conjU_pow hx ha (2 ^ k) v
  have e : conjU (Subgroup.pow_mem _ hx (2 ^ k)) v = v := Subtype.ext (hk v v.2)
  rw [e, hv, toAdd_ofAdd] at h1
  have h2 : (Pi.single 0 (1 : GaloisField 2 n) : Fin 2 → GaloisField 2 n) =
      a ^ 2 ^ k • Pi.single 0 1 := Multiplicative.ofAdd.injective h1
  have h3 := congrFun h2 0
  simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] at h3
  have h4 : (a - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, ← h3]
    simp
  exact sub_eq_zero.1 (pow_eq_zero_iff (by positivity) |>.1 h4)

end NatData

namespace NatBlock

variable [Finite G]

theorem centralizes_blockU (h : NatBlock L n) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ l ∈ L, ⁅x, l⁆ ∈ oTwoIn L) (hz : ∀ v ∈ blockU L, ⁅x, v⁆ ∈ blockZ L) :
    ∀ v ∈ blockU L, x * v * x⁻¹ = v := by
  have hK : ∀ l ∈ L, ∀ v ∈ blockU L,
      x * (l * v * l⁻¹) * x⁻¹ = l * (x * v * x⁻¹) * l⁻¹ := by
    intro l hl v hv
    have hxv : x * v * x⁻¹ ∈ blockU L := conj_mem_blockU hx hv
    have hy : l * (x * v * x⁻¹) * l⁻¹ ∈ blockU L :=
      conj_mem_blockU (Subgroup.le_normalizer hl) hxv
    have hcomm := blockU_comm_of_short h.short _ hy _ (hc l hl)
    calc x * (l * v * l⁻¹) * x⁻¹
        = (⁅x, l⁆ * (l * (x * v * x⁻¹) * l⁻¹)) * ⁅x, l⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = l * (x * v * x⁻¹) * l⁻¹ := by
          rw [← hcomm, mul_inv_cancel_right]
  have hZc : ∀ z ∈ blockZ L, ∀ w ∈ L, z * w * z⁻¹ = w := by
    intro z hz w hw
    have := Subgroup.mem_centralizer_iff.1 (blockZ_le_centralizer L hz) w hw
    rw [← this, mul_inv_cancel_right]
  have hle : ⁅blockU L, L⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    refine Subgroup.commutator_le.2 fun v hv l hl => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hvL : v ∈ L := blockU_le L hv
    have hvl : l * v⁻¹ * l⁻¹ ∈ blockU L := conj_mem_blockU (Subgroup.le_normalizer hl) (inv_mem hv)
    have hW : v * (l * v⁻¹ * l⁻¹) ∈ blockU L := mul_mem hv hvl
    set zv : G := ⁅y, v⁆ with hzv
    have hzvZ : zv ∈ blockZ L := hz v hv
    have e1 : y * v * y⁻¹ = zv * v := by simp [hzv, commutatorElement_def]
    have e2 := hK l hl v⁻¹ (inv_mem hv)
    have e3 : y * v⁻¹ * y⁻¹ = (zv * v)⁻¹ := by rw [← e1]; group
    have e4 : l * zv * l⁻¹ = zv := by
      have := Subgroup.mem_centralizer_iff.1 (blockZ_le_centralizer L hzvZ) l hl
      rw [this, mul_inv_cancel_right]
    have e5 : l * (zv * v)⁻¹ * l⁻¹ = (l * v⁻¹ * l⁻¹) * zv⁻¹ := by
      have : l * zv⁻¹ * l⁻¹ = zv⁻¹ := by
        have h1 : l * zv⁻¹ * l⁻¹ = (l * zv * l⁻¹)⁻¹ := by group
        rw [h1, e4]
      calc l * (zv * v)⁻¹ * l⁻¹ = (l * v⁻¹ * l⁻¹) * (l * zv⁻¹ * l⁻¹) := by group
        _ = (l * v⁻¹ * l⁻¹) * zv⁻¹ := by rw [this]
    have e6 : y * (v * (l * v⁻¹ * l⁻¹)) * y⁻¹ =
        zv * (v * (l * v⁻¹ * l⁻¹)) * zv⁻¹ := by
      calc y * (v * (l * v⁻¹ * l⁻¹)) * y⁻¹
          = (y * v * y⁻¹) * (y * (l * v⁻¹ * l⁻¹) * y⁻¹) := by group
        _ = (zv * v) * (l * (y * v⁻¹ * y⁻¹) * l⁻¹) := by rw [e1, e2]
        _ = (zv * v) * (l * (zv * v)⁻¹ * l⁻¹) := by rw [e3]
        _ = (zv * v) * ((l * v⁻¹ * l⁻¹) * zv⁻¹) := by rw [e5]
        _ = zv * (v * (l * v⁻¹ * l⁻¹)) * zv⁻¹ := by group
    have e7 := hZc zv hzvZ _ ((blockU_le L) hW)
    have e8 : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e8]
    calc y * (v * (l * v⁻¹ * l⁻¹)) = (y * (v * (l * v⁻¹ * l⁻¹)) * y⁻¹) * y := by group
      _ = (v * (l * v⁻¹ * l⁻¹)) * y := by rw [e6, e7]
  intro v hv
  rw [← h.blockU_eq] at hv
  have := Subgroup.mem_centralizer_iff.1 (hle hv) x (Set.mem_singleton x)
  rw [this, mul_inv_cancel_right]

end NatBlock

end CFSG.CGT.PushingUpLit.T2K
