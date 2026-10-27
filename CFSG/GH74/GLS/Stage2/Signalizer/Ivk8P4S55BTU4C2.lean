module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4G3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4L2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4B

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher BS4 BL4
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

abbrev Hu (h : UnitaryFieldData p f K) (I : Subgroup (hypPSU h 2 0)) : Subgroup (hypSU h 2 0) :=
  ⁅I.comap (hypProj h 2 0), I.comap (hypProj h 2 0)⁆

theorem false_of_commU {I : Subgroup (hypPSU h 2 0)} (hI : ⁅I, I⁆ = I) (hIne : I ≠ ⊥)
    {G₂ : Type*} [Group G₂] {ψ : hypSU h 2 0 →* G₂} (hψ : Function.Injective ψ)
    (hc : ∀ z ∈ ⁅(Hu h I).map ψ, (Hu h I).map ψ⁆, ∀ w ∈ ⁅(Hu h I).map ψ, (Hu h I).map ψ⁆,
      z * w = w * z) : False := by
  have hD := comm_of_map hψ hc
  have hπ : (⁅⁅I.comap (hypProj h 2 0), I.comap (hypProj h 2 0)⁆,
      ⁅I.comap (hypProj h 2 0), I.comap (hypProj h 2 0)⁆⁆).map (hypProj h 2 0) = I := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      map_comap_eq_self_of_surjective (hypProj_surjective h 2 0), hI, hI]
  apply hIne
  rw [← hI, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  rw [← hπ] at ha hb
  obtain ⟨d, hd, rfl⟩ := hb
  obtain ⟨d', hd', rfl⟩ := ha
  rw [← map_mul, ← map_mul, hD d hd d' hd']

theorem ker_hypProj_le_center : (hypProj h 2 0).ker ≤ center (hypSU h 2 0) := by
  intro x hx
  rw [ker_hypProj] at hx
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (GeneralLinearGroup.scalar_commute c _).symm

theorem eq_of_mem_commutator_gen {G P : Type*} [Group G] [Group P] {π : G →* P}
    (hker : π.ker ≤ center G) {S : Subgroup G} {ψ : G →* G}
    (hψ : ∀ s ∈ S, π (ψ s) = π s) : ∀ s ∈ ⁅S, S⁆, ψ s = s := by
  have hc : ∀ s ∈ S, ∃ t ∈ center G, ψ s = t * s := by
    intro s hs
    refine ⟨ψ s * s⁻¹, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψ s hs, mul_inv_cancel]
  have hle : ⁅S, S⁆ ≤ MonoidHom.eqLocus ψ (MonoidHom.id G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨t, ht, hta⟩ := hc a ha
    obtain ⟨t', ht', htb⟩ := hc b hb
    show ψ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hta, htb, commutator_central_left ht,
      commutator_central_right ht']
  exact fun s hs => hle hs

@[expose] noncomputable def conjSU (x : semilinearSimilitudes h 2 0) :
    hypSU h 2 0 →* hypSU h 2 0 where
  toFun s := ⟨_, conj_mem_hypSU x.2 s⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]
    group

theorem hypProj_conjSU (x : semilinearSimilitudes h 2 0) (s : hypSU h 2 0) :
    hypProj h 2 0 (conjSU x s) =
      semilinearAutHom h (by norm_num) (by norm_num) x (hypProj h 2 0 s) :=
  (semilinearAutHom_apply h (by norm_num) (by norm_num) x s).symm

theorem comm_of_lin {B : GL (HypIndex 2 0) K}
    (hx : (⟨B, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    {I : Subgroup (hypPSU h 2 0)}
    (hI : ∀ y ∈ I, semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ y = y) :
    ∀ s ∈ Hu h I, B * (s : GL (HypIndex 2 0) K) = (s : GL (HypIndex 2 0) K) * B := by
  intro s hs
  have e := eq_of_mem_commutator_gen ker_hypProj_le_center (ψ := conjSU ⟨_, hx⟩)
    (fun t ht => by rw [hypProj_conjSU]; exact hI _ ht) s hs
  have e' : B * glAut (RingEquiv.refl K) (s : GL (HypIndex 2 0) K) * B⁻¹ = s :=
    congrArg Subtype.val e
  rw [show RingEquiv.refl K = 1 from rfl, map_one, MulAut.one_apply] at e'
  calc B * (s : GL (HypIndex 2 0) K) = B * s * B⁻¹ * B := by group
    _ = s * B := by rw [e']

theorem hypGram_ne_zero : hypGram 2 0 K ≠ 0 := by
  intro h0
  have := congrFun (congrFun h0 (Sum.inl 0)) (Sum.inr (Sum.inr 0))
  simp [hypGram_apply] at this

theorem coe_scalar_mul_hyp {n : Type*} [Fintype n] [DecidableEq n] (c : Kˣ) (X : GL n K) :
    ((GeneralLinearGroup.scalar n c * X : GL n K) : Matrix n n K) =
      (c : K) • (X : Matrix n n K) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul]

theorem semi_rel {B A A₃ : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {μ : K}
    (hB : (B.map h.bar)ᵀ * hypGram 2 0 K * B = hypGram 2 0 K)
    (hA : (A.map h.bar)ᵀ * hypGram 2 0 K * A = hypGram 2 0 K)
    (hA₃ : (A₃.map h.bar)ᵀ * hypGram 2 0 K * A₃ = hypGram 2 0 K) (h3 : A₃ = μ • (B * A))
    (hAA : A * A.map h.bar = 1) (hAA₃ : A₃ * A₃.map h.bar = 1) : B * A * B.map h.bar = A := by
  subst h3
  have hμ : μ * h.bar μ = 1 := norm_one_of_smul hypGram_ne_zero (herm_mul hB hA) hA₃
  have e : (μ • (B * A)).map h.bar = h.bar μ • (B.map h.bar * A.map h.bar) := by
    rw [← Matrix.map_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [e, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hμ, one_smul] at hAA₃
  have hAA' : A.map h.bar * A = 1 := mul_eq_one_comm.mp hAA
  calc B * A * B.map h.bar = B * A * B.map h.bar * (A.map h.bar * A) := by
        rw [hAA', Matrix.mul_one]
    _ = B * A * (B.map h.bar * A.map h.bar) * A := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hAA₃, Matrix.one_mul]

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
