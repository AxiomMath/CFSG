module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LConfig
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCU

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix CFSG Subgroup Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self)
open scoped MatrixGroups

namespace P58b3L

variable {K : Type} [Field K] {n : ℕ}

theorem two_ne_zero_of_three (h : UnitaryFieldData 3 1 K) : (2 : K) ≠ 0 := by
  have := h.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K 3] at e'
  norm_num at e'

theorem exists_scalar_of_projH {p f : ℕ} {z : StatedSU n (p ^ f) K}
    (hz : projH (StatedSU n (p ^ f) K) z = 1) :
    ∃ ζ : Kˣ, ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ζ : K) • 1 := by
  obtain ⟨ζ, hζ⟩ := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff z).mp hz)
  refine ⟨ζ, ?_⟩
  rw [← hζ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

section Lift

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem coe_uLift_one (A : uU h n) (y : StatedSU n (p ^ f) K) :
    ((uLift h A 1 y : StatedSU n (p ^ f) K) : GL (Fin n) K) =
      (A : GL (Fin n) K) * y * (A : GL (Fin n) K)⁻¹ := by
  apply Units.ext
  rw [coe_uLift, map_one_ringEquiv, Units.val_mul, Units.val_mul]

theorem uLift_one_surjective (A : uU h n) : Function.Surjective (uLift h A 1) := by
  intro y
  refine ⟨uLift h A⁻¹ 1 y, Subtype.ext ?_⟩
  rw [coe_uLift_one, coe_uLift_one, Subgroup.coe_inv]
  group

theorem uLift_sign_involutive (J : Finset (Fin n)) :
    Function.Involutive (uLift h (uSign h J) 1) := by
  intro y
  apply Subtype.ext
  have hss : (uSign h J : GL (Fin n) K) * (uSign h J : GL (Fin n) K) = 1 := by
    rw [← Subgroup.coe_mul, uSign_mul_self, Subgroup.coe_one]
  rw [coe_uLift_one, coe_uLift_one]
  calc (uSign h J : GL (Fin n) K) * ((uSign h J : GL (Fin n) K) * y *
        (uSign h J : GL (Fin n) K)⁻¹) * (uSign h J : GL (Fin n) K)⁻¹ =
      ((uSign h J : GL (Fin n) K) * (uSign h J : GL (Fin n) K)) * y *
        ((uSign h J : GL (Fin n) K) * (uSign h J : GL (Fin n) K))⁻¹ := by group
    _ = y := by rw [hss, one_mul, inv_one, mul_one]

theorem projH_eq_one_of_uLift (A : uU h n) {z : StatedSU n (p ^ f) K}
    (hz : projH (StatedSU n (p ^ f) K) (uLift h A 1 z) = 1) :
    projH (StatedSU n (p ^ f) K) z = 1 := by
  obtain ⟨ζ, hζ⟩ := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hz)
  rw [coe_uLift_one] at hζ
  refine (QuotientGroup.eq_one_iff z).mpr (mem_subgroupOf.mpr ⟨ζ, ?_⟩)
  have hc : ∀ x : GL (Fin n) K, GeneralLinearGroup.scalar (Fin n) ζ * x =
      x * GeneralLinearGroup.scalar (Fin n) ζ := fun x => by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  have e1 : (A : GL (Fin n) K)⁻¹ * GeneralLinearGroup.scalar (Fin n) ζ * A =
      GeneralLinearGroup.scalar (Fin n) ζ := by
    rw [mul_assoc, hc, inv_mul_cancel_left]
  rw [← e1, hζ]
  group

end Lift

theorem exists_large_half (hn : 6 ≤ n) (J : Finset (Fin n)) :
    ∃ I : Finset (Fin n), (I = J ∨ I = Jᶜ) ∧ 3 ≤ I.card := by
  have hsum : J.card + Jᶜ.card = n := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ J
    rw [Fintype.card_fin] at this
    omega
  by_cases hJ : 3 ≤ J.card
  · exact ⟨J, Or.inl rfl, hJ⟩
  · exact ⟨Jᶜ, Or.inr rfl, by omega⟩

variable (hu : UnitaryFieldData 3 1 K)

theorem false_of_su_block {X : Type} [Group X] [Finite X] (α : StatedSU n (3 ^ 1) K →* X)
    (hαs : Function.Surjective α)
    (hαZ : ∀ z, α z ∈ center X → projH (StatedSU n (3 ^ 1) K) z = 1) {t : X}
    {J I : Finset (Fin n)} (hI : I = J ∨ I = Jᶜ) (h3I : 3 ≤ I.card)
    (hf : ∀ y, t * α y * t⁻¹ = α (uLift hu (uSign hu J) 1 y)) {Q : Subgroup X}
    (hQt : Q ≤ centralizer {t}) (hQsub : (Q.subgroupOf (centralizer {t})).IsSubnormal)
    (hQsolv : Group.IsSolvable (↥Q ⧸ pPrimeCore 2 ↥Q)) {a b : X} (ha : a ∈ Q) (hb : b ∈ Q)
    {c : X} (hc1 : c ≠ 1) (hcZ : c ∈ center X) (hab : a * b = c * (b * a)) : False := by
  have := hu.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hu.charP
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_three hu
  have hn3 : 3 ≤ n := h3I.trans ((Finset.card_le_univ I).trans_eq (Fintype.card_fin n))
  have hker : α.ker ≤ center (StatedSU n (3 ^ 1) K) := by
    intro y hy
    apply scalars_subgroupOf_le_center
    have h1 : α y ∈ center X := by rw [MonoidHom.mem_ker.mp hy]; exact one_mem _
    exact (QuotientGroup.eq_one_iff y).mp (hαZ y h1)
  set δ : StatedSU n (3 ^ 1) K ≃* StatedSU n (3 ^ 1) K :=
    MulEquiv.ofBijective (uLift hu (uSign hu J) 1) (uLift_sign_involutive hu J).bijective
    with hδ
  have hq := isQuasisimple_uBlock hu (by norm_num) (by omega : 2 ≤ I.card) (Or.inl h3I)
  have hQF : uBlock 3 1 K I ≤ ClassicalInvolution.Balance.fixedGroup δ := by
    intro g hg
    exact (uLift_sign_eq_iff hu h2 J g).2
      (commute_compInd_of_or' hI (commute_compInd_of_mem_uBlock hg))
  have hQn : ((uBlock 3 1 K I).subgroupOf (ClassicalInvolution.Balance.fixedGroup δ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQF]
    intro g x hg hx
    have hxc := commute_compInd_of_or hI ((uLift_sign_eq_iff hu h2 J x).1 hx)
    refine conj_mem_uBlock (D := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Di := (((x⁻¹ : StatedSU n (3 ^ 1) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      ?_ ?_ hxc hg ?_
    · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  have hQc : Open.IsComponentOf (uBlock 3 1 K I) (ClassicalInvolution.Balance.fixedGroup δ) :=
    ⟨hQF, ClassicalInvolution.isSubnormal_of_normal_subgroupOf hQF hQn,
      ⟨hq.1.commutator_eq_top, hq.2.1⟩⟩
  have hδ' : ∀ y : StatedSU n (3 ^ 1) K, t * α (1 * y * 1⁻¹) * t⁻¹ = α (1 * δ y * 1⁻¹) := by
    intro y
    simp only [one_mul, inv_one, mul_one]
    exact hf y
  have hmain := ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 t δ hδ' hQc
  have e0 : α.comp (MulAut.conj (1 : StatedSU n (3 ^ 1) K)).toMonoidHom = α := by
    ext
    simp
  rw [e0, MonoidHom.range_eq_top.mpr hαs, top_inf_eq] at hmain
  set N := (uBlock 3 1 K I).map α with hN
  have hNC : N ≤ centralizer {t} := hmain.1
  have hNcomp : IsComponent (N.subgroupOf (centralizer {t})) :=
    (isComponentOf_iff_isComponent_subgroupOf hNC).mp
      ((AssemblyBPredicates.isComponentOf_iff_open _ _).mpr hmain)
  obtain ⟨i₁, hi₁, i₂, hi₂, hi₁₂⟩ := Finset.one_lt_card.1 (by omega : 1 < I.card)
  have hsub : ({i₁, i₂} : Finset (Fin n)) ⊆ I := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hi₁
    · rw [Finset.mem_singleton.1 hx]
      exact hi₂
  have huI : Burgoyne.C.uSignSU hu hi₁₂ ∈ uBlock 3 1 K I :=
    Burgoyne.C.uBlock_mono hsub (Burgoyne.C.uSignSU_mem_uBlock hu hi₁₂)
  have hord := Burgoyne.C.orderOf_projH_uSignSU hu h2 hn3 hi₁₂
  have hαu : α (Burgoyne.C.uSignSU hu hi₁₂) ≠ 1 := by
    intro h1
    rw [hαZ (Burgoyne.C.uSignSU hu hi₁₂) (by rw [h1]; exact one_mem _), orderOf_one] at hord
    exact absurd hord (by norm_num)
  have huu : Burgoyne.C.uSignSU hu hi₁₂ * Burgoyne.C.uSignSU hu hi₁₂ = 1 :=
    Subtype.ext (Units.ext (by
      change signMat K {i₁, i₂} * signMat K {i₁, i₂} = 1
      exact signMat_mul_self _))
  have hNeven : Even (Nat.card (N.subgroupOf (centralizer {t}))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNC).toEquiv]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord2 : orderOf (⟨α (Burgoyne.C.uSignSU hu hi₁₂), mem_map_of_mem α huI⟩ : N) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        change α (Burgoyne.C.uSignSU hu hi₁₂) ^ 2 = 1
        rw [← map_pow, pow_two, huu, map_one]
      · intro h1
        exact hαu (congrArg Subtype.val h1)
    have := orderOf_dvd_natCard (⟨α (Burgoyne.C.uSignSU hu hi₁₂), mem_map_of_mem α huI⟩ : N)
    rw [hord2] at this
    exact even_iff_two_dvd.mpr this
  have hcomm := P51Q.commute_of_isComponent hQt hQsub hQsolv hNcomp hNeven
  have hcen : ∀ y : StatedSU n (3 ^ 1) K, α y ∈ Q → ∀ g ∈ uBlock 3 1 K I, y * g = g * y := by
    intro y hy g hg
    have hψ : ∀ x, MulAut.conj (projH (StatedSU n (3 ^ 1) K) y) (projH _ x) =
        projH _ ((MulAut.conj y).toMonoidHom x) := fun x => by
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    have hfix : ∀ x ∈ uBlock 3 1 K I,
        MulAut.conj (projH (StatedSU n (3 ^ 1) K) y) (projH _ x) = projH _ x := by
      intro x hx
      have hxN : α x ∈ N := mem_map_of_mem α hx
      have h1 := hcomm ⟨α x, hNC hxN⟩ (mem_subgroupOf.mpr hxN) (α y) hy
      have h3 : α y * α x * (α y)⁻¹ = α x := by
        change α x * α y = α y * α x at h1
        rw [← h1, mul_inv_cancel_right]
      have h4 : α ((y * x * y⁻¹)⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, map_inv, h3, inv_mul_cancel]
      have h5 := hαZ ((y * x * y⁻¹)⁻¹ * x) (by rw [h4]; exact one_mem _)
      rw [map_mul, map_inv, inv_mul_eq_one] at h5
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      exact h5
    have h6 := lift_eq_of_commutator_eq (MulAut.conj y).toMonoidHom hψ
      (Burgoyne.PSL.commutator_eq_self_of_isQuasisimple hq) hfix hg
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h6
    exact mul_inv_eq_iff_eq_mul.mp h6
  have hmat : ∀ y : StatedSU n (3 ^ 1) K, α y ∈ Q → ∀ g ∈ uBlock 3 1 K I,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro y hy g hg
    have e := congrArg (fun z : StatedSU n (3 ^ 1) K =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hcen y hy g hg)
    simpa only [Subgroup.coe_mul, Units.val_mul] using e
  obtain ⟨A, rfl⟩ := hαs a
  obtain ⟨B, rfl⟩ := hαs b
  obtain ⟨hoffA, -⟩ := eq_of_commute_uBlock hu (by omega : 2 ≤ I.card) (hmat A ha)
  obtain ⟨hoffB, -⟩ := eq_of_commute_uBlock hu (by omega : 2 ≤ I.card) (hmat B hb)
  have hrow : ∀ D C : Matrix (Fin n) (Fin n) K, (∀ y, y ≠ i₁ → D i₁ y = 0) →
      (D * C) i₁ i₁ = D i₁ i₁ * C i₁ i₁ := by
    intro D C hD
    rw [Matrix.mul_apply, Finset.sum_eq_single i₁]
    · intro k _ hk
      rw [hD k hk, zero_mul]
    · intro h1
      exact absurd (Finset.mem_univ i₁) h1
  have hne : ∀ y : StatedSU n (3 ^ 1) K,
      (∀ z, z ≠ i₁ → ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₁ z = 0) →
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₁ i₁ ≠ 0 := by
    intro y hy h0
    have e : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((y⁻¹ : StatedSU n (3 ^ 1) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    have e1 := congrFun (congrFun e i₁) i₁
    rw [hrow _ _ hy, h0, zero_mul, Matrix.one_apply_eq] at e1
    exact zero_ne_one e1
  have hrA : ∀ z, z ≠ i₁ → ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₁ z = 0 :=
    fun z hz => (hoffA i₁ hi₁ z hz).1
  have hrB : ∀ z, z ≠ i₁ → ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₁ z = 0 :=
    fun z hz => (hoffB i₁ hi₁ z hz).1
  have hl := hne A hrA
  have hm := hne B hrB
  set w := A * B * (B * A)⁻¹ with hw
  have hαw : α w = c := by
    rw [hw, map_mul, map_inv, map_mul, map_mul, hab, mul_inv_cancel_right]
  obtain ⟨ν, hν⟩ := exists_scalar_of_projH (hαZ w (by rw [hαw]; exact hcZ))
  have hν1 : (ν : K) ≠ 1 := by
    intro h1
    apply hc1
    rw [← hαw]
    have hw1 : w = 1 := Subtype.ext (Units.ext (by
      rw [hν, h1, one_smul, Subgroup.coe_one, Units.val_one]))
    rw [hw1, map_one]
  have hAB : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (ν : K) • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have e : A * B = w * (B * A) := by rw [hw, inv_mul_cancel_right]
    have e' := congrArg (fun z : StatedSU n (3 ^ 1) K =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) e
    simp only [Subgroup.coe_mul, Units.val_mul] at e'
    rw [e', hν, Matrix.smul_mul, Matrix.one_mul]
  have k := congrFun (congrFun hAB i₁) i₁
  rw [Matrix.smul_apply, hrow _ _ hrA, hrow _ _ hrB, smul_eq_mul] at k
  have k' : (1 - (ν : K)) * (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₁ i₁ *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₁ i₁) = 0 := by
    linear_combination k
  rcases mul_eq_zero.mp k' with h1 | h1
  · exact hν1 (sub_eq_zero.mp h1).symm
  · exact mul_ne_zero hl hm h1

theorem exists_sign_lift {X : Type} [Group X] (hn : 1 ≤ n) (α : StatedSU n (3 ^ 1) K →* X)
    (hαs : Function.Surjective α)
    (hαZ : ∀ z, α z ∈ center X → projH (StatedSU n (3 ^ 1) K) z = 1) {c : X} (hc1 : c ≠ 1)
    (hcZ : c ∈ center X) {t : X} (ht : t * t = 1) :
    ∃ (H : uU hu n) (J : Finset (Fin n)), ∀ y,
      t * α (uLift hu H 1 y) * t⁻¹ = α (uLift hu H 1 (uLift hu (uSign hu J) 1 y)) := by
  have := hu.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hu.charP
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_three hu
  have hbar : ∀ x : K, hu.bar x = x ^ 3 := fun x => by rw [hu.bar_apply, pow_one]
  have hfour : ∀ (z : StatedSU n (3 ^ 1) K) (ω : K),
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ω • 1 → ω ^ 4 = 1 := by
    intro z ω hz
    have hU := ((mem_unitarySU_iff hu).1 z.2).2
    rw [hz, Matrix.map_smul' _ _ _ (map_mul hu.bar), Matrix.map_one _ (map_zero _) (map_one _),
      transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hU
    have e := congrFun (congrFun hU ⟨0, hn⟩) ⟨0, hn⟩
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hbar] at e
    linear_combination e
  obtain ⟨g, rfl⟩ := hαs t
  have hgg : α (g * g) = 1 := by rw [map_mul, ht]
  obtain ⟨ζ, hζ⟩ := exists_scalar_of_projH (hαZ (g * g) (by rw [hgg]; exact one_mem _))
  have hζ4 := hfour _ _ hζ
  obtain ⟨μ, hμ0, hμζ, hμN⟩ : ∃ μ : K, μ ≠ 0 ∧ μ ^ 2 = ζ ∧ hu.norm μ = 1 := by
    by_cases hζ2 : (ζ : K) ^ 2 = 1
    · have hpm : ((ζ : K) - 1) * ((ζ : K) + 1) = 0 := by linear_combination hζ2
      rcases mul_eq_zero.mp hpm with h | h
      · refine ⟨1, one_ne_zero, ?_, ?_⟩
        · rw [one_pow]
          exact (sub_eq_zero.mp h).symm
        · rw [UnitaryFieldData.norm, map_one, one_mul]
      · obtain ⟨μ, hμ0, hμN, hμ2⟩ := exists_norm_one_sq_ne_one hu
        have hμ4 : μ ^ 4 = 1 := by
          have e := hμN
          rw [UnitaryFieldData.norm, hbar] at e
          linear_combination e
        refine ⟨μ, hμ0, ?_, hμN⟩
        have hpm' : (μ ^ 2 - 1) * (μ ^ 2 + 1) = 0 := by linear_combination hμ4
        rcases mul_eq_zero.mp hpm' with h' | h'
        · exact absurd (sub_eq_zero.mp h') hμ2
        · linear_combination h' - h
    ·
      exfalso
      have hζm : (ζ : K) ^ 2 = -1 := by
        have hpm : ((ζ : K) ^ 2 - 1) * ((ζ : K) ^ 2 + 1) = 0 := by linear_combination hζ4
        rcases mul_eq_zero.mp hpm with h | h
        · exact absurd (sub_eq_zero.mp h) hζ2
        · linear_combination h
      obtain ⟨z, hz⟩ := hαs c
      obtain ⟨ω, hω⟩ := exists_scalar_of_projH (hαZ z (by rw [hz]; exact hcZ))
      have hω4 := hfour _ _ hω
      have hprod : ((ω : K) - 1) * ((ω : K) + 1) * ((ω : K) - ζ) * ((ω : K) + ζ) = 0 := by
        linear_combination hω4 + (1 - (ω : K) ^ 2) * hζm
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (ω : K) = (ζ : K) ^ k := by
        rcases mul_eq_zero.mp hprod with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact ⟨0, by rw [pow_zero]; linear_combination h⟩
            · exact ⟨2, by linear_combination h - hζm⟩
          · exact ⟨1, by rw [pow_one]; linear_combination h⟩
        · exact ⟨3, by linear_combination h - (ζ : K) * hζm⟩
      apply hc1
      rw [← hz]
      have hzk : z = (g * g) ^ k := by
        apply Subtype.ext
        apply Units.ext
        rw [hω, hk, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hζ, smul_pow, one_pow]
      rw [hzk, map_pow, hgg, one_pow]
  have hμN' : μ * hu.bar μ = 1 := hμN
  have hGU : ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map hu.bar)ᵀ *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := ((mem_unitarySU_iff hu).1 g.2).2
  have hGG : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ζ : K) • 1 := by
    simpa only [Subgroup.coe_mul, Units.val_mul] using hζ
  set M' : Matrix (Fin n) (Fin n) K := μ⁻¹ • ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hM'
  have hinv : (hu.bar μ)⁻¹ * μ⁻¹ = 1 := by rw [← mul_inv, mul_comm, hμN', inv_one]
  have hU' : (M'.map hu.bar)ᵀ * M' = 1 := by
    rw [hM', Matrix.map_smul' _ _ _ (map_mul hu.bar), transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, hGU, smul_smul, map_inv₀, hinv, one_smul]
  have hμμ : μ⁻¹ * μ⁻¹ * (ζ : K) = 1 := by
    rw [← hμζ, ← mul_inv, ← pow_two, inv_mul_cancel₀ (pow_ne_zero 2 hμ0)]
  have hMM' : M' * M' = 1 := by
    rw [hM', Matrix.smul_mul, Matrix.mul_smul, hGG, smul_smul, smul_smul, hμμ, one_smul]
  obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form hu h2 hU' hMM'
  set H : uU hu n := ⟨uGL hu Hm hHU, uGL_mem hu _ _⟩ with hH
  refine ⟨H, J, fun y => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : GL (Fin n) K, m = GeneralLinearGroup.scalar (Fin n) (Units.mk0 μ hμ0) :=
    ⟨_, rfl⟩
  have hmc : ∀ x : GL (Fin n) K, m * x = x * m := fun x => by
    rw [hm]
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  have hE : (g : GL (Fin n) K) * (H : GL (Fin n) K) =
      m * ((H : GL (Fin n) K) * (uSign hu J : GL (Fin n) K)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_uSign]
    change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Hm = _ * (Hm * signMat K J)
    rw [← hHA, hm, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, hM', Matrix.smul_mul,
      smul_smul, Units.val_mk0, mul_inv_cancel₀ hμ0, one_smul]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_uLift_one]
  calc (g : GL (Fin n) K) * ((H : GL (Fin n) K) * y * (H : GL (Fin n) K)⁻¹) *
        (g : GL (Fin n) K)⁻¹ =
      ((g : GL (Fin n) K) * H) * y * ((g : GL (Fin n) K) * H)⁻¹ := by group
    _ = (m * ((H : GL (Fin n) K) * (uSign hu J : GL (Fin n) K))) * y *
        (m * ((H : GL (Fin n) K) * (uSign hu J : GL (Fin n) K)))⁻¹ := by rw [hE]
    _ = m * (((H : GL (Fin n) K) * (uSign hu J : GL (Fin n) K)) * y *
        ((H : GL (Fin n) K) * (uSign hu J : GL (Fin n) K))⁻¹) * m⁻¹ := by group
    _ = ((H : GL (Fin n) K) * (uSign hu J : GL (Fin n) K)) * y *
        ((H : GL (Fin n) K) * (uSign hu J : GL (Fin n) K))⁻¹ := by
      rw [hmc, mul_inv_cancel_right]
    _ = _ := by group

theorem exists_su_cover {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hO : pPrimeCore 2 X = ⊥) (hn : 2 ≤ n) (hm : Blueprint.LieModel (X ⧸ center X) .PSU n 3 1) :
    ∃ (F : Type) (_ : Field F) (_ : UnitaryFieldData 3 1 F) (α : StatedSU n (3 ^ 1) F →* X),
      Function.Surjective α ∧ ∀ z, α z ∈ center X ↔ projH (StatedSU n (3 ^ 1) F) z = 1 := by
  have : Group.IsPerfect X := hX.1
  rcases hm with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp', hf, -, -⟩, F, _, _, hFc, ⟨θ⟩⟩ := hcl
  have hu : UnitaryFieldData 3 1 F := ⟨hp', hf, by rw [hFc, ← pow_mul, mul_comm]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hu.charP
  set β : StatedSU n (3 ^ 1) F →* X ⧸ center X :=
    θ.symm.toMonoidHom.comp (projH (StatedSU n (3 ^ 1) F)) with hβdef
  have hβ : Function.Surjective β := θ.symm.surjective.comp projH_surjective
  have hη : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨α, hαβ, hαs, -⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect
    (Burgoyne.B.statedSU_central_two_splitting hu.card_eq_sq (by norm_num) hn) hβ
    (QuotientGroup.mk'_surjective (center X)) hη.le
    (by rw [hη]; exact Sol78.center_isPGroup_two hO)
  refine ⟨F, inferInstance, hu, α, hαs, fun z => ?_⟩
  have h1 : QuotientGroup.mk' (center X) (α z) = θ.symm (projH _ z) := hαβ z
  constructor
  · intro hz
    have h2 : QuotientGroup.mk' (center X) (α z) = 1 := (QuotientGroup.eq_one_iff _).mpr hz
    rwa [h1, MulEquiv.map_eq_one_iff] at h2
  · intro hz
    have h2 : QuotientGroup.mk' (center X) (α z) = 1 := by rw [h1, hz, map_one]
    exact (QuotientGroup.eq_one_iff _).mp h2

end P58b3L

open P58b3L in
theorem harris82Lemma58bThreeRow_PSU_of_six_le (h51E4 : Harris82Lemma51E4) {n : ℕ}
    (hn : 6 ≤ n) : Harris82Lemma58bThreeRow .PSU n := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ he₁ hKc hO₁ _ _ hz₂K hz₂Z f hm
  obtain rfl := field_eq_one h51E4 hz₁ hz₂ hL₁ hz₁L he₁ hKc hO₁ hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  obtain ⟨Q, hQt, hQsub, -, hQsolv, a, ha, b, hb, -, -, hab⟩ :=
    exists_quat_config hz₁ hz₂ hL₁ hz₁L he₁ hKc.1 hO₁ hz₁K hz₂K
  obtain ⟨F, _, hu, α, hαs, hαZ⟩ := exists_su_cover hX hO (by omega) hmX
  obtain ⟨H, J, hf⟩ := exists_sign_lift hu (by omega) α hαs (fun z => (hαZ z).1)
    (mk_ne_one hz₁ hz₁K) (mk_mem_center hKc.1 hz₁K) (mk_mul_self hz₂ hz₂K)
  obtain ⟨I, hI, h3I⟩ := exists_large_half hn J
  exact false_of_su_block hu (α.comp (uLift hu H 1)) (hαs.comp (uLift_one_surjective hu H))
    (fun z hz => projH_eq_one_of_uLift hu H ((hαZ (uLift hu H 1 z)).1 hz)) hI h3I hf hQt hQsub
    hQsolv ha hb
    (mk_ne_one hz₁ hz₁K) (mk_mem_center hKc.1 hz₁K) hab

end CFSG.ComponentClassification.HarrisLit.T1
