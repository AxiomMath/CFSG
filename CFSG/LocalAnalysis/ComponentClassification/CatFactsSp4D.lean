module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Outer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Sp4b

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

theorem exists_sylow_le_centralizer {G : Type*} [Group G] [Finite G] {w : G}
    (h2 : 2 ∣ Nat.card G) (hconj : ∀ z : G, orderOf z = 2 → ∃ l : G, l * w * l⁻¹ = z) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ centralizer {w} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 G) := inferInstance
  set T₁ : Subgroup G := (T₀ : Subgroup G) with hT₁
  have : Nontrivial T₁ := (nontrivial_iff_ne_bot T₁).mpr (T₀.ne_bot_of_dvd_card h2)
  have hZ : Nontrivial (center T₁) := T₀.isPGroup'.center_nontrivial
  have hZ2 : 2 ∣ Nat.card (center T₁) := by
    rcases (T₀.isPGroup'.to_subgroup (center _)).card_eq_or_dvd with h | h
    · exact absurd h Finite.one_lt_card.ne'
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  have hz' : orderOf ((z : T₁) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  obtain ⟨l, hl⟩ := hconj _ hz'
  refine ⟨l⁻¹ • T₀, fun x hx => ?_⟩
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hx
  have hx' : l * x * l⁻¹ ∈ T₁ := by simpa using hx
  have hzc := congrArg Subtype.val (mem_center_iff.mp z.2 ⟨_, hx'⟩)
  change l * x * l⁻¹ * ((z : T₁) : G) = ((z : T₁) : G) * (l * x * l⁻¹) at hzc
  rw [← hl] at hzc
  rw [mem_centralizer_singleton_iff]
  calc x * w = l⁻¹ * (l * x * l⁻¹ * (l * w * l⁻¹)) * l := by group
    _ = l⁻¹ * (l * w * l⁻¹ * (l * x * l⁻¹)) * l := by rw [hzc]
    _ = w * x := by group

theorem exists_conj_le_of_isSylowIn {X : Type} [Group X] [Finite X] {C D R : Subgroup X}
    (hDC : D ≤ C) (hD : IsPGroup 2 D) (hR : GSThmB.Seven.IsSylowIn R C) :
    ∃ c ∈ C, D.map (MulAut.conj c).toMonoidHom ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT⟩ := hR
  have hD' : IsPGroup 2 (D.subgroupOf C) := hD.of_equiv (subgroupOfEquivOfLe hDC).symm
  obtain ⟨T₀, hT₀⟩ := hD'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C T₀ T
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have h1 : (⟨d, hDC hd⟩ : C) ∈ (T₀ : Subgroup C) := hT₀ hd
  have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) (T₀ : Subgroup C) h1
  rw [← Sylow.coe_subgroup_smul, hg, hT, mem_subgroupOf] at h2
  exact h2

theorem nonempty_map_equiv_of_ker_eq {G A B : Type*} [Group G] [Group A] [Group B]
    (f : G →* A) (g : G →* B) (hker : f.ker = g.ker) (H : Subgroup G) :
    Nonempty (↥(H.map f) ≃* ↥(H.map g)) := by
  have hker' : (f.subgroupMap H).ker = (g.subgroupMap H).ker := by
    ext x
    simp only [MonoidHom.mem_ker, Subtype.ext_iff, MonoidHom.subgroupMap_apply_coe,
      OneMemClass.coe_one]
    rw [← MonoidHom.mem_ker, hker, MonoidHom.mem_ker]
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (f.subgroupMap_surjective H)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker').trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (g.subgroupMap_surjective H)))⟩

variable {K : Type} [Field K]

theorem J₁_mul_J₁_eq : (J₁ : Matrix (Fin 2) (Fin 2) K) * J₁ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁]

theorem eq_of_mul_J₁ {X Y : Matrix (Fin 2) (Fin 2) K} (h : X * J₁ = Y * J₁) : X = Y := by
  have h' := congrArg (· * (J₁ : Matrix (Fin 2) (Fin 2) K)) h
  simp only [Matrix.mul_assoc, J₁_mul_J₁_eq, Matrix.mul_neg, Matrix.mul_one, neg_inj] at h'
  exact h'

theorem transpose_mul_J₁_mul_eq (k : Matrix (Fin 2) (Fin 2) K) : kᵀ * J₁ * k = k.det • J₁ :=
  transpose_mul_J₁_mul k

theorem transpose_mul_self_of_comm {k : Matrix (Fin 2) (Fin 2) K} (hk : k.det = 1)
    (h : k * J₁ = J₁ * k) : kᵀ * k = 1 := by
  apply eq_of_mul_J₁
  rw [Matrix.one_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, transpose_mul_J₁_mul_eq, hk,
    one_smul]

theorem transpose_mul_self_of_anti {k : Matrix (Fin 2) (Fin 2) K} (hk : k.det = 1)
    (h : k * J₁ = -(J₁ * k)) : kᵀ * k = -1 := by
  apply eq_of_mul_J₁
  rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, transpose_mul_J₁_mul_eq, hk,
    one_smul, Matrix.neg_mul, Matrix.one_mul]

theorem not_comm_of_anti (h2 : (2 : K) ≠ 0) {k : Matrix (Fin 2) (Fin 2) K} (hk : k.det ≠ 0)
    (h : k * J₁ = -(J₁ * k)) : ¬ k * J₁ = J₁ * k := by
  intro h'
  have h3 : (2 : K) • (J₁ * k) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h']
    rw [h, neg_add_cancel]
  rcases smul_eq_zero.mp h3 with h3 | h3
  · exact h2 h3
  · have h4 := congrArg (fun X => J₁ * X) h3
    simp only [← Matrix.mul_assoc, J₁_mul_J₁_eq, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_zero, neg_eq_zero] at h4
    rw [h4, det_zero] at hk
    exact hk rfl

theorem gaussEmb_mul_J₁ (z : Gauss K) : gaussEmb z * J₁ = J₁ * gaussEmb z := by
  rw [← gaussEmb_omega, ← map_mul, ← map_mul, mul_comm]

theorem mul_gaussEmb_of_comm {k : Matrix (Fin 2) (Fin 2) K} (h : k * J₁ = J₁ * k) (z : Gauss K) :
    k * gaussEmb z = gaussEmb z * k := by
  rw [gaussEmb_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, h]

theorem mul_gaussEmb_of_anti {k : Matrix (Fin 2) (Fin 2) K} (h : k * J₁ = -(J₁ * k))
    (z : Gauss K) : k * gaussEmb z = gaussEmb (star z) * k := by
  rw [gaussEmb_apply, gaussEmb_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
    zero_mul, add_zero, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, h, smul_neg, neg_smul]

theorem gaussEmb_mul_star (z : Gauss K) :
    gaussEmb z * gaussEmb (star z) = QuadraticAlgebra.norm z • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [← map_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, gaussEmb_algebraMap]

variable (K) in
@[expose] def G1 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
  (centralizer {w0 K}).comap ((proj 2 K).comp (diagSL K))

theorem kron_neg_right (g h : Matrix (Fin 2) (Fin 2) K) : kron g (-h) = -kron g h := by
  simp only [kron, fromBlocks_neg, smul_neg]

theorem proj_eq_of_eq_or_neg {a b : StatedSp 2 K}
    (h : ((b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∨
      ((b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        -((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    proj 2 K a = proj 2 K b := by
  rcases h with h | h
  · rw [sp_ext h]
  · rw [← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
    right
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, h, Matrix.mul_neg, Units.inv_mul]

theorem coe_J₁SL : ((J₁SL : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = J₁ :=
  rfl

theorem proj_diagSL_commute_iff {k k' : Matrix.SpecialLinearGroup (Fin 2) K} :
    proj 2 K (diagSL K k) * proj 2 K (diagSL K k') = proj 2 K (diagSL K k') * proj 2 K (diagSL K k)
      ↔ (k : Matrix (Fin 2) (Fin 2) K) * k' = k' * k ∨
        (k : Matrix (Fin 2) (Fin 2) K) * k' = -((k' : Matrix (Fin 2) (Fin 2) K) * k) := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  constructor
  · intro h
    rcases eq_or_eq_neg_of_proj_eq h with h' | h' <;>
      rw [coe_diagSL, coe_diagSL, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul] at h'
    · exact Or.inl (kron_one_injective h').symm
    · rw [neg_kron] at h'
      right
      rw [kron_one_injective h', neg_neg]
  · intro h
    apply proj_eq_of_eq_or_neg
    rw [coe_diagSL, coe_diagSL, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    rcases h with h | h
    · exact Or.inl (by rw [h])
    · right
      rw [h, neg_kron, neg_neg]

theorem mem_G1_iff {k : Matrix.SpecialLinearGroup (Fin 2) K} :
    k ∈ G1 K ↔ (k : Matrix (Fin 2) (Fin 2) K) * J₁ = J₁ * (k : Matrix (Fin 2) (Fin 2) K) ∨
      (k : Matrix (Fin 2) (Fin 2) K) * J₁ = -(J₁ * (k : Matrix (Fin 2) (Fin 2) K)) := by
  rw [G1, mem_comap, MonoidHom.comp_apply, mem_centralizer_singleton_iff, w0,
    proj_diagSL_commute_iff, coe_J₁SL]

theorem det_ne_zero_of_SL (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    (k : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
  rw [k.2]
  exact one_ne_zero

open scoped Classical in
@[expose] def phiD (z : Gauss K) (k : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  if k * J₁ = J₁ * k then k else gaussEmb z * k

theorem phiD_of_comm (z : Gauss K) {k : Matrix (Fin 2) (Fin 2) K} (h : k * J₁ = J₁ * k) :
    phiD z k = k := by
  rw [phiD, ite_eq_left h]

theorem phiD_of_anti (h2 : (2 : K) ≠ 0) (z : Gauss K) {k : Matrix (Fin 2) (Fin 2) K}
    (hk : k.det ≠ 0) (h : k * J₁ = -(J₁ * k)) : phiD z k = gaussEmb z * k := by
  rw [phiD, ite_eq_right (not_comm_of_anti h2 hk h)]

theorem gaussEmb_transpose_mul_self' (z : Gauss K) :
    (gaussEmb z)ᵀ * gaussEmb z = QuadraticAlgebra.norm z • (1 : Matrix (Fin 2) (Fin 2) K) :=
  gaussEmb_transpose_mul_self z

theorem phiD_orth (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1)
    {k : Matrix.SpecialLinearGroup (Fin 2) K} (hk : k ∈ G1 K) :
    (phiD z (k : Matrix (Fin 2) (Fin 2) K))ᵀ * phiD z (k : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rcases mem_G1_iff.mp hk with h | h
  · rw [phiD_of_comm z h]
    exact transpose_mul_self_of_comm k.2 h
  · rw [phiD_of_anti h2 z (det_ne_zero_of_SL k) h, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (gaussEmb z), gaussEmb_transpose_mul_self', hz, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, transpose_mul_self_of_anti k.2 h, smul_neg, neg_smul,
      one_smul, neg_neg]

theorem kron_one_symplectic_of_orth {A : Matrix (Fin 2) (Fin 2) K} (hA : Aᵀ * A = 1) :
    (kron 1 A)ᵀ * formJ 2 K * kron 1 A = formJ 2 K := by
  rw [kron_symplectic_iff, det_one, one_smul, hA]

theorem phiD_comm_or_anti' (h2 : (2 : K) ≠ 0) (z : Gauss K) {a : Matrix (Fin 2) (Fin 2) K}
    (ha : a.det = 1) (h : a * J₁ = J₁ * a ∨ a * J₁ = -(J₁ * a)) :
    phiD z a * J₁ = J₁ * phiD z a ∨ phiD z a * J₁ = -(J₁ * phiD z a) := by
  rcases h with h | h
  · rw [phiD_of_comm z h]
    exact Or.inl h
  · rw [phiD_of_anti h2 z (by rw [ha]; exact one_ne_zero) h]
    right
    rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc (gaussEmb z) J₁,
      gaussEmb_mul_J₁, Matrix.mul_assoc]

theorem phiD_comm_or_anti (h2 : (2 : K) ≠ 0) (z : Gauss K)
    {k : Matrix.SpecialLinearGroup (Fin 2) K} (hk : k ∈ G1 K) :
    phiD z (k : Matrix (Fin 2) (Fin 2) K) * J₁ = J₁ * phiD z (k : Matrix (Fin 2) (Fin 2) K) ∨
      phiD z (k : Matrix (Fin 2) (Fin 2) K) * J₁ =
        -(J₁ * phiD z (k : Matrix (Fin 2) (Fin 2) K)) :=
  phiD_comm_or_anti' h2 z k.2 (mem_G1_iff.mp hk)

theorem comm_mul_comm {k h : Matrix (Fin 2) (Fin 2) K} (hk : k * J₁ = J₁ * k)
    (hh : h * J₁ = J₁ * h) : k * h * J₁ = J₁ * (k * h) := by
  rw [Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hk, Matrix.mul_assoc]

theorem comm_mul_anti {k h : Matrix (Fin 2) (Fin 2) K} (hk : k * J₁ = J₁ * k)
    (hh : h * J₁ = -(J₁ * h)) : k * h * J₁ = -(J₁ * (k * h)) := by
  rw [Matrix.mul_assoc, hh, Matrix.mul_neg, ← Matrix.mul_assoc, hk, Matrix.mul_assoc]

theorem anti_mul_comm {k h : Matrix (Fin 2) (Fin 2) K} (hk : k * J₁ = -(J₁ * k))
    (hh : h * J₁ = J₁ * h) : k * h * J₁ = -(J₁ * (k * h)) := by
  rw [Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hk, Matrix.neg_mul, Matrix.mul_assoc]

theorem anti_mul_anti {k h : Matrix (Fin 2) (Fin 2) K} (hk : k * J₁ = -(J₁ * k))
    (hh : h * J₁ = -(J₁ * h)) : k * h * J₁ = J₁ * (k * h) := by
  rw [Matrix.mul_assoc, hh, Matrix.mul_neg, ← Matrix.mul_assoc, hk, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc]

theorem phiD_mul' (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1)
    {a b : Matrix (Fin 2) (Fin 2) K} (ha : a.det = 1) (hb : b.det = 1)
    (ha' : a * J₁ = J₁ * a ∨ a * J₁ = -(J₁ * a)) (hb' : b * J₁ = J₁ * b ∨ b * J₁ = -(J₁ * b)) :
    phiD z (a * b) = phiD z a * phiD z b ∨ phiD z (a * b) = -(phiD z a * phiD z b) := by
  have h0 : ∀ {c : Matrix (Fin 2) (Fin 2) K}, c.det = 1 → c.det ≠ 0 := fun hc => by
    rw [hc]
    exact one_ne_zero
  have hab : (a * b).det ≠ 0 := by
    rw [det_mul, ha, hb, one_mul]
    exact one_ne_zero
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · left
    rw [phiD_of_comm z ha', phiD_of_comm z hb', phiD_of_comm z (comm_mul_comm ha' hb')]
  · left
    rw [phiD_of_comm z ha', phiD_of_anti h2 z (h0 hb) hb',
      phiD_of_anti h2 z hab (comm_mul_anti ha' hb'), ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      mul_gaussEmb_of_comm ha']
  · left
    rw [phiD_of_anti h2 z (h0 ha) ha', phiD_of_comm z hb',
      phiD_of_anti h2 z hab (anti_mul_comm ha' hb'), Matrix.mul_assoc]
  · right
    rw [phiD_of_anti h2 z (h0 ha) ha', phiD_of_anti h2 z (h0 hb) hb',
      phiD_of_comm z (anti_mul_anti ha' hb')]
    have e : gaussEmb z * a * (gaussEmb z * b) = -(a * b) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, mul_gaussEmb_of_anti ha', ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, gaussEmb_mul_star, hz, neg_smul, one_smul, Matrix.neg_mul,
        Matrix.neg_mul, Matrix.one_mul]
    rw [e, neg_neg]

theorem phiD_mul (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1)
    {k h : Matrix.SpecialLinearGroup (Fin 2) K} (hk : k ∈ G1 K) (hh : h ∈ G1 K) :
    phiD z ((k * h : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        phiD z (k : Matrix (Fin 2) (Fin 2) K) * phiD z (h : Matrix (Fin 2) (Fin 2) K) ∨
      phiD z ((k * h : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        -(phiD z (k : Matrix (Fin 2) (Fin 2) K) * phiD z (h : Matrix (Fin 2) (Fin 2) K)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact phiD_mul' h2 hz k.2 h.2 (mem_G1_iff.mp hk) (mem_G1_iff.mp hh)

@[expose] def fDfun (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1)
    (k : G1 K) : StatedProj (StatedSp 2 K) :=
  proj 2 K (toSp (kron 1 (phiD z ((k : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K))) (kron_one_symplectic_of_orth (phiD_orth h2 hz k.2)))

@[expose] def fD (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1) :
    G1 K →* StatedProj (StatedSp 2 K) where
  toFun := fDfun h2 hz
  map_one' := by
    rw [fDfun, ← map_one (proj 2 K)]
    congr 1
    apply sp_ext
    rw [coe_toSp, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one,
      phiD_of_comm z (by rw [Matrix.one_mul, Matrix.mul_one]), kron_one_one]
    rfl
  map_mul' k h := by
    simp only [fDfun]
    rw [← map_mul]
    apply proj_eq_of_eq_or_neg
    rw [Subgroup.coe_mul, Units.val_mul, coe_toSp, coe_toSp, coe_toSp, kron_mul, Matrix.one_mul,
      Subgroup.coe_mul]
    rcases phiD_mul h2 hz k.2 h.2 with e | e
    · left
      rw [e]
    · right
      rw [e, kron_neg_right, neg_neg]

theorem fD_apply (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1) (k : G1 K) :
    fD h2 hz k = proj 2 K (toSp (kron 1 (phiD z ((k : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K))) (kron_one_symplectic_of_orth (phiD_orth h2 hz k.2))) :=
  rfl

theorem fD_mem (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1) (k : G1 K) :
    fD h2 hz k ∈ centralizer {u2 K} ⊓ centralizer (Lsub K : Set (StatedProj (StatedSp 2 K))) := by
  rw [fD_apply, mem_inf]
  constructor
  · rw [mem_centralizer_singleton_iff, u2, ← map_mul, ← map_mul]
    apply proj_eq_of_eq_or_neg
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_toSp, coe_T2,
      kron_mul, kron_mul, Matrix.one_mul]
    rcases phiD_comm_or_anti h2 z k.2 with e | e
    · left
      rw [e]
    · right
      rw [e, kron_neg_right, neg_neg]
  · rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply sp_ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_toSp, coe_diagSL,
      kron_mul, kron_mul, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]

theorem kron_one_left_injective {A B : Matrix (Fin 2) (Fin 2) K} (h : kron 1 A = kron 1 B) :
    A = B := by
  have := (fromBlocks_inj.mp h).1
  simpa using this

theorem kron_one_neg_one : kron (1 : Matrix (Fin 2) (Fin 2) K) (-1) = -1 := by
  rw [kron_neg_right, kron_one_one]

theorem kron_one_eq_pm_iff {A : Matrix (Fin 2) (Fin 2) K} :
    (kron 1 A = 1 ∨ kron 1 A = -1) ↔ (A = 1 ∨ A = -1) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (kron_one_left_injective (h.trans kron_one_one.symm))
    · exact Or.inr (kron_one_left_injective (h.trans kron_one_neg_one.symm))
  · rintro (rfl | rfl)
    · exact Or.inl kron_one_one
    · exact Or.inr kron_one_neg_one

theorem kron_eq_pm_iff {g : Matrix (Fin 2) (Fin 2) K} :
    (kron g 1 = 1 ∨ kron g 1 = -1) ↔ (g = 1 ∨ g = -1) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (kron_one_injective (h.trans kron_one_one.symm))
    · exact Or.inr (kron_one_injective (h.trans kron_neg_one_one.symm))
  · rintro (rfl | rfl)
    · exact Or.inl kron_one_one
    · exact Or.inr kron_neg_one_one

theorem det_gaussEmb (z : Gauss K) : (gaussEmb z).det = QuadraticAlgebra.norm z := by
  rw [gaussEmb_eq, det_fin_two_of, QuadraticAlgebra.norm_def]
  ring

theorem phiD_eq_pm_iff (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1)
    {a : Matrix (Fin 2) (Fin 2) K} (ha : a.det = 1) (ha' : a * J₁ = J₁ * a ∨ a * J₁ = -(J₁ * a)) :
    (phiD z a = 1 ∨ phiD z a = -1) ↔ (a = 1 ∨ a = -1) := by
  have hpm : ∀ {c : Matrix (Fin 2) (Fin 2) K}, (c = 1 ∨ c = -1) → c * J₁ = J₁ * c := by
    rintro c (rfl | rfl)
    · rw [Matrix.one_mul, Matrix.mul_one]
    · rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]
  rcases ha' with h | h
  · rw [phiD_of_comm z h]
  · have hdet : a.det ≠ 0 := by
      rw [ha]
      exact one_ne_zero
    rw [phiD_of_anti h2 z hdet h]
    have hanti : gaussEmb z * a * J₁ = -(J₁ * (gaussEmb z * a)) := by
      rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc (gaussEmb z) J₁,
        gaussEmb_mul_J₁, Matrix.mul_assoc]
    have hdet' : (gaussEmb z * a).det ≠ 0 := by
      rw [det_mul, det_gaussEmb, hz, ha, mul_one]
      exact neg_ne_zero.mpr one_ne_zero
    constructor
    · intro h1
      exact absurd (hpm h1) (not_comm_of_anti h2 hdet' hanti)
    · intro h1
      exact absurd (hpm h1) (not_comm_of_anti h2 hdet h)

theorem ker_fD (h2 : (2 : K) ≠ 0) {z : Gauss K} (hz : QuadraticAlgebra.norm z = -1) :
    (fD h2 hz).ker = (((proj 2 K).comp (diagSL K)).comp (G1 K).subtype).ker := by
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, fD_apply, ← MonoidHom.mem_ker, ker_proj,
    mem_spScalars_iff, MonoidHom.comp_apply, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_proj,
    mem_spScalars_iff, coe_toSp, coe_diagSL, kron_one_eq_pm_iff, kron_eq_pm_iff]
  exact phiD_eq_pm_iff h2 hz k.1.2 (mem_G1_iff.mp k.2)

theorem le_range_G1 {x : StatedProj (StatedSp 2 K)} (hx : x ∈ Lsub K)
    (hxw : x ∈ centralizer {w0 K}) :
    x ∈ (((proj 2 K).comp (diagSL K)).comp (G1 K).subtype).range := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hx
  exact ⟨⟨k, hxw⟩, rfl⟩

theorem exists_D0 [Finite K] (hodd : Odd (Nat.card K))
    (hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) :
    ∃ T : Sylow 2 (Lsub K), ∃ D : Subgroup (StatedProj (StatedSp 2 K)),
      D ≤ centralizer {u2 K} ⊓ centralizer (Lsub K : Set (StatedProj (StatedSp 2 K))) ∧
      Nonempty (↥D ≃* ↥(T : Subgroup (Lsub K))) := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hdvd : 2 ∣ Nat.card (Lsub K) := by
    have := orderOf_dvd_natCard (⟨w0 K, w0_mem_Lsub⟩ : Lsub K)
    rwa [Subgroup.orderOf_mk, orderOf_w0] at this
  obtain ⟨T, hT⟩ := exists_sylow_le_centralizer (w := (⟨w0 K, w0_mem_Lsub⟩ : Lsub K)) hdvd
    (fun z hz => by
      obtain ⟨l, hl, hlz⟩ := exists_conj_w0 hpp z.2 (by rw [Subgroup.orderOf_coe, hz])
      exact ⟨⟨l, hl⟩, Subtype.ext hlz⟩)
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq h2 (-1)
  have hz : QuadraticAlgebra.norm (⟨a, b⟩ : Gauss K) = -1 := by
    rw [QuadraticAlgebra.norm_def]
    change a * a + 0 * a * b - (-1) * b * b = -1
    linear_combination hab
  set ψ₁ := ((proj 2 K).comp (diagSL K)).comp (G1 K).subtype with hψ₁
  set T' := (T : Subgroup (Lsub K)).map (Lsub K).subtype with hT'def
  have hT' : T' ≤ ψ₁.range := by
    rintro _ ⟨y, hy, rfl⟩
    apply le_range_G1 y.2
    have := hT hy
    rw [mem_centralizer_singleton_iff] at this ⊢
    exact congrArg Subtype.val this
  refine ⟨T, (T'.comap ψ₁).map (fD h2 hz), ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact fD_mem h2 hz k
  · obtain ⟨e⟩ := nonempty_map_equiv_of_ker_eq ψ₁ (fD h2 hz) (ker_fD h2 hz).symm (T'.comap ψ₁)
    exact ⟨e.symm.trans ((MulEquiv.subgroupCongr (map_comap_eq_self hT')).trans
      (equivMapOfInjective _ _ (Lsub K).subtype_injective).symm)⟩

theorem mem_normalizer_of_model {Y : Type} [Group Y] [Finite K] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (ψ : Y ≃* StatedProj (StatedSp 2 K)) {t : Y} (h : ψ t = u2 K)
    {M : Subgroup Y} (hL : M.map ψ.toMonoidHom = Lsub K) {x : Y} (hx : x ∈ centralizer {t}) :
    x ∈ normalizer (M : Set Y) := by
  apply mem_normalizer_of_map ψ hL
  apply mem_normalizer_Lsub hodd h5
  rw [← h, mem_centralizer_singleton_iff]
  rw [mem_centralizer_singleton_iff] at hx
  rw [← map_mul, ← map_mul, hx]

theorem cfSp4D : GSThmB.CFSp4D := by
  intro Y _ _ p f hp hp2 hf hY t ht M hMt hM hZ R hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hY
  have hodd := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd (u := e t) (by rw [MulEquiv.orderOf_eq, ht])
  set ψ : Y ≃* StatedProj (StatedSp 2 K) := e.trans φ with hψ
  have hψt : ψ t = u1 K ∨ ψ t = u2 K := hφ
  have hM' := isPComponent_map_subgroupOf 2 ψ hMt hM
  have hMX' := Subgroup.map_mono (f := ψ.toMonoidHom) hMt
  rw [map_centralizer_singleton] at hM' hMX'
  rcases hψt with h | h <;> rw [h] at hM' hMX'
  · exact absurd hZ (center_ne_bot_of_map ψ (center_ne_bot_of_u1 h2
      (pComponent_centralizer_u1 hodd hMX' hM').1))
  obtain ⟨hL, h5⟩ := pComponent_centralizer_u2 hodd hMX' hM'
  obtain ⟨T, D, hD, ⟨eD⟩⟩ := exists_D0 hodd hpp
  set D' := D.map ψ.symm.toMonoidHom with hD'def
  have eD' : ↥D' ≃* ↥(T : Subgroup (Lsub K)) :=
    (equivMapOfInjective D ψ.symm.toMonoidHom ψ.symm.injective).symm.trans eD
  have hD'C : D' ≤ centralizer {t} := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := mem_centralizer_singleton_iff.mp (hD hx).1
    rw [mem_centralizer_singleton_iff]
    apply ψ.injective
    change ψ (ψ.symm x * t) = ψ (t * ψ.symm x)
    rw [map_mul, map_mul, ψ.apply_symm_apply, h]
    exact hx'
  have hD'M : D' ≤ centralizer (M : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro m hm
    have hm' : ψ m ∈ Lsub K := hL ▸ mem_map_of_mem ψ.toMonoidHom hm
    have hx' := mem_centralizer_iff.mp (hD hx).2 _ hm'
    apply ψ.injective
    change ψ (m * ψ.symm x) = ψ (ψ.symm x * m)
    rw [map_mul, map_mul, ψ.apply_symm_apply]
    exact hx'
  have hD'2 : IsPGroup 2 D' := T.isPGroup'.of_equiv eD'.symm
  obtain ⟨c, hc, hcR⟩ := exists_conj_le_of_isSylowIn hD'C hD'2 hR
  have hcN := mem_normalizer_of_model hodd h5 ψ h hL hc
  set eL : Lsub K ≃* M := ((ψ.subgroupMap M).trans (MulEquiv.subgroupCongr hL)).symm
  refine ⟨D'.map (MulAut.conj c).toMonoidHom, hcR, ?_,
    T.mapSurjective (f := eL.toMonoidHom) eL.surjective, ⟨?_⟩⟩
  · rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_iff]
    intro m hm
    have hm' : c⁻¹ * m * c ∈ M := by
      have := (mem_normalizer_iff.mp (inv_mem hcN) m).mp hm
      simpa using this
    have hdm := mem_centralizer_iff.mp (hD'M hd) _ hm'
    change m * (c * d * c⁻¹) = c * d * c⁻¹ * m
    calc m * (c * d * c⁻¹) = c * ((c⁻¹ * m * c) * d) * c⁻¹ := by group
      _ = c * (d * (c⁻¹ * m * c)) * c⁻¹ := by rw [hdm]
      _ = c * d * c⁻¹ * m := by group
  · exact (equivMapOfInjective D' _ (MulAut.conj c).injective).symm.trans
      (eD'.trans (equivMapOfInjective _ eL.toMonoidHom eL.injective))

end CFSG.ComponentClassification.CatFactsSp4
