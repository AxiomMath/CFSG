module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltInner

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Inner

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Psi

variable {Y : Type} [Group Y] [Finite Y]

section

variable {n : ℕ} (K : Subgroup Y) (hK : K.Normal)
  (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n))

@[expose] def piK : ↥K →* alternatingGroup (Fin n) :=
  eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))

theorem piK_surjective : Function.Surjective (piK K eK) :=
  eK.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piK_eq_one_iff (k : ↥K) : piK K eK k = 1 ↔ k ∈ Subgroup.center ↥K := by
  rw [piK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

@[expose] def cqEquiv (y : Y) : ↥K ⧸ Subgroup.center ↥K ≃* ↥K ⧸ Subgroup.center ↥K :=
  QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) (conjKequiv K hK y)
    (Subgroup.map_center_eq (conjKequiv K hK y))

@[expose] def alphaQ (y : Y) : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) :=
  eK.symm.trans ((cqEquiv K hK y).trans eK)

theorem alphaQ_piK (y : Y) (k : ↥K) :
    alphaQ K hK eK y (piK K eK k) = piK K eK (conjKequiv K hK y k) := by
  simp only [alphaQ, piK, MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, cqEquiv, QuotientGroup.mk'_apply, QuotientGroup.congr_mk]

theorem conjKequiv_one (k : ↥K) : conjKequiv K hK 1 k = k := by
  ext
  simp [conjKequiv_apply]

@[expose] def alphaHom : Y →* MulAut (alternatingGroup (Fin n)) where
  toFun y := alphaQ K hK eK y
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨k, rfl⟩ := piK_surjective K eK x
    show alphaQ K hK eK 1 (piK K eK k) = piK K eK k
    rw [alphaQ_piK, conjKequiv_one]
  map_mul' y z := by
    apply MulEquiv.ext
    intro x
    obtain ⟨k, rfl⟩ := piK_surjective K eK x
    show alphaQ K hK eK (y * z) (piK K eK k) = alphaQ K hK eK y (alphaQ K hK eK z (piK K eK k))
    rw [alphaQ_piK, alphaQ_piK, alphaQ_piK]
    congr 1
    ext
    simp [conjKequiv_apply, mul_assoc]

theorem alphaHom_piK (y : Y) (k : ↥K) :
    alphaHom K hK eK y (piK K eK k) = piK K eK (conjKequiv K hK y k) :=
  alphaQ_piK K hK eK y k

theorem alphaHom_pow_eq_one {y : Y} (hy : y ^ 3 = 1) : (alphaHom K hK eK y) ^ 3 = 1 := by
  rw [← map_pow, hy, map_one]

variable (hn : 5 ≤ n)

@[expose] noncomputable def psiFun (y : Y) (hy : y ^ 3 = 1) : alternatingGroup (Fin n) :=
  Classical.choose (exists_unique_inner (n := n) Nat.prime_three (by norm_num) hn
    (alphaHom_pow_eq_one K hK eK hy))

theorem psiFun_spec (y : Y) (hy : y ^ 3 = 1) :
    MulAut.conj (psiFun K hK eK hn y hy) = alphaHom K hK eK y :=
  (Classical.choose_spec (exists_unique_inner (n := n) Nat.prime_three (by norm_num) hn
    (alphaHom_pow_eq_one K hK eK hy))).symm

theorem psiFun_equiv (y : Y) (hy : y ^ 3 = 1) (k : ↥K) :
    piK K eK (conjKequiv K hK y k) =
      psiFun K hK eK hn y hy * piK K eK k * (psiFun K hK eK hn y hy)⁻¹ := by
  rw [← alphaHom_piK K hK eK y k]
  have h := DFunLike.congr_fun (psiFun_spec K hK eK hn y hy) (piK K eK k)
  simp only [MulAut.conj_apply] at h
  exact h.symm

@[expose] noncomputable def psiB (B : Subgroup Y) (hB : ∀ b ∈ B, b ^ 3 = 1) :
    B →* alternatingGroup (Fin n) :=
  MonoidHom.mk' (fun b => psiFun K hK eK hn (b : Y) (hB b b.2)) (fun b c => by
    apply conj_injective_alt hn
    rw [map_mul (MulAut.conj), psiFun_spec, psiFun_spec, psiFun_spec, Subgroup.coe_mul,
      map_mul (alphaHom K hK eK)])

theorem psiB_apply (B : Subgroup Y) (hB : ∀ b ∈ B, b ^ 3 = 1) (b : B) :
    psiB K hK eK hn B hB b = psiFun K hK eK hn (b : Y) (hB b b.2) := by
  simp only [psiB, MonoidHom.mk'_apply]

theorem conjK_eq_of_perfect (hq : CFSG.Open.IsQuasisimple ↥K) (y : Y)
    (hy : ∀ k : ↥K, piK K eK (conjKequiv K hK y k) = piK K eK k) (k : ↥K) :
    conjKequiv K hK y k = k := by
  have hcen : ∀ u : ↥K, conjKequiv K hK y u * u⁻¹ ∈ Subgroup.center ↥K := by
    intro u
    rw [← piK_eq_one_iff K eK, map_mul, map_inv, hy u, mul_inv_cancel]
  have hmul : ∀ u v : ↥K, conjKequiv K hK y (u * v) * (u * v)⁻¹ =
      (conjKequiv K hK y u * u⁻¹) * (conjKequiv K hK y v * v⁻¹) := by
    intro u v
    have hc : (conjKequiv K hK y v * v⁻¹) * u⁻¹ = u⁻¹ * (conjKequiv K hK y v * v⁻¹) :=
      (Subgroup.mem_center_iff.1 (hcen v) u⁻¹).symm
    calc conjKequiv K hK y (u * v) * (u * v)⁻¹
        = conjKequiv K hK y u * conjKequiv K hK y v * (u * v)⁻¹ := by rw [map_mul]
      _ = conjKequiv K hK y u * ((conjKequiv K hK y v * v⁻¹) * u⁻¹) := by group
      _ = conjKequiv K hK y u * (u⁻¹ * (conjKequiv K hK y v * v⁻¹)) := by rw [hc]
      _ = (conjKequiv K hK y u * u⁻¹) * (conjKequiv K hK y v * v⁻¹) := by group
  let φ : ↥K →* ↥K :=
    { toFun := fun u => conjKequiv K hK y u * u⁻¹
      map_one' := by simp
      map_mul' := hmul }
  have hφc : ∀ u v : ↥K, φ u * φ v = φ v * φ u := fun u v =>
    Subgroup.mem_center_iff.1 (hcen v) (φ u)
  have hcomm : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ ≤ φ.ker := by
    apply Subgroup.commutator_le.2
    intro u _ v _
    simp only [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
    calc φ u * φ v * (φ u)⁻¹ * (φ v)⁻¹ = φ v * φ u * (φ u)⁻¹ * (φ v)⁻¹ := by rw [hφc u v]
      _ = 1 := by group
  have htop : (⊤ : Subgroup ↥K) ≤ φ.ker := by
    calc (⊤ : Subgroup ↥K) = ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ := hq.1.symm
      _ ≤ φ.ker := hcomm
  have hφ : φ k = 1 := MonoidHom.mem_ker.1 (htop (Subgroup.mem_top k))
  exact mul_inv_eq_one.1 hφ

theorem psiFun_eq_one_iff (hq : CFSG.Open.IsQuasisimple ↥K) (y : Y) (hy : y ^ 3 = 1) :
    psiFun K hK eK hn y hy = 1 ↔ y ∈ Subgroup.centralizer (K : Set Y) := by
  have hspec := psiFun_spec K hK eK hn y hy
  constructor
  · intro h
    rw [h, map_one] at hspec
    have hact : ∀ k : ↥K, piK K eK (conjKequiv K hK y k) = piK K eK k := fun k => by
      rw [← alphaHom_piK K hK eK y k, ← hspec]
      rfl
    have hfix := conjK_eq_of_perfect K hK eK hq y hact
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh
    have h2 := congrArg Subtype.val (hfix ⟨h', hh⟩)
    simp only [conjKequiv_apply] at h2
    have h3 : y * h' = h' * y := by
      calc y * h' = (y * h' * y⁻¹) * y := by group
        _ = h' * y := by rw [h2]
    exact h3.symm
  · intro hc
    apply conj_injective_alt hn
    rw [hspec, map_one]
    apply MulEquiv.ext
    intro x
    obtain ⟨k, rfl⟩ := piK_surjective K eK x
    show alphaHom K hK eK y (piK K eK k) = piK K eK k
    rw [alphaHom_piK K hK eK y k]
    congr 1
    apply Subtype.ext
    simp only [conjKequiv_apply]
    have hck : (k : Y) * y = y * k := Subgroup.mem_centralizer_iff.1 hc k k.2
    rw [← hck, mul_inv_cancel_right]

end

end CFSG.LocalAnalysis.GLTheoremA.KD1426Psi
