module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeArr
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeCrit

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert

open Certificates.G2ThreeMax

section Action

variable {G : Type} [Group G]

@[ext] structure TwPt (_ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) (_ψ : G →* G) where
  val : Mat3

instance twPtAction (ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) (ψ : G →* G) :
    MulAction G (TwPt ρ ψ) where
  smul g P := ⟨((ρ g : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) * P.val *
    (((ρ (ψ g))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3)⟩
  one_smul P := by
    apply TwPt.ext
    show ((ρ 1 : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) * P.val *
      (((ρ (ψ 1))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) = P.val
    simp
  mul_smul g h P := by
    apply TwPt.ext
    show ((ρ (g * h) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) * P.val *
        (((ρ (ψ (g * h)))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      ((ρ g : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) *
        (((ρ h : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) * P.val *
          (((ρ (ψ h))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3)) *
        (((ρ (ψ g))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3)
    simp [map_mul, mul_assoc]

theorem twPt_smul_val (ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) (ψ : G →* G) (g : G)
    (P : TwPt ρ ψ) :
    (g • P).val = ((ρ g : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) * P.val *
      (((ρ (ψ g))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) := rfl

end Action

theorem size_idArr : idArr.size = 196 := size_ofFn' _

theorem lt_idArr {p : ℕ} (hp : p < 196) : idArr[p]! < 3 := by
  unfold idArr
  rw [ofFn_get _ hp]
  split_ifs <;> norm_num

theorem wordArr_nil : wordArr [] = idArr := by
  simp only [wordArr, List.foldr_nil]

theorem wordArr_cons (k : ℕ) (w : List ℕ) :
    wordArr (k :: w) = mmul (genArr k) (wordArr w) := by
  simp only [wordArr, List.foldr_cons]

theorem wordArr_valid (w : List ℕ) :
    (wordArr w).size = 196 ∧ ∀ p < 196, (wordArr w)[p]! < 3 := by
  induction w with
  | nil =>
    rw [wordArr_nil]
    exact ⟨size_idArr, fun p hp => lt_idArr hp⟩
  | cons k w ih =>
    rw [wordArr_cons]
    exact ⟨size_mmul _ _, fun p hp => lt_mmul _ _ hp⟩

theorem rowsArr_get {k : ℕ} (hk : k < 8) : rowsArr[k]! = rowsOf (genArr k) := by
  unfold rowsArr
  rw [getElem!_pos _ k (by simpa using hk)]
  simp

theorem colsInvArr_get (σ : List ℕ) {k : ℕ} (hk : k < 8) :
    (colsInvArr σ)[k]! = colsOf (genArr (invK σ[k]!)) := by
  unfold colsInvArr
  rw [getElem!_pos _ k (by simpa using hk)]
  simp

theorem invK_lt {k : ℕ} (hk : k < 8) : invK k < 8 := by
  unfold invK
  split_ifs <;> omega

theorem primCheck_coatom {G : Type} [Group G]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) (ψ : G →* G) (gens : ℕ → G)
    (hgen : Subgroup.closure (gens '' {k | k < 8}) = ⊤)
    (hρ : ∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (genArr k))
    (hinv : ∀ k < 8, gens (invK k) = (gens k)⁻¹)
    (inp : Input) (hψ : ∀ k < 8, ψ (gens k) = gens inp.sigma[k]!)
    (hcheck : primCheck inp = true) :
    IsCoatom (MulAction.stabilizer G (⟨M (wordArr inp.base)⟩ : TwPt ρ ψ)) := by
  have hpc := hcheck
  unfold primCheck at hpc
  simp only [Bool.and_eq_true] at hpc
  obtain ⟨⟨⟨⟨⟨⟨hσ, -⟩, -⟩, hnt⟩, -⟩, -⟩, -⟩ := hpc
  simp only [okSigma, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hσ
  have hσk : ∀ k < 8, inp.sigma[k]! < 8 := by
    intro k hk
    apply hσ.2
    rw [getElem!_pos inp.sigma k (by omega)]
    exact List.getElem_mem _
  have hsmul : ∀ k < 8, ∀ P : Array ℕ,
      gens k • (⟨M P⟩ : TwPt ρ ψ) =
        ⟨M (conjSparse rowsArr[k]! (colsInvArr inp.sigma)[k]! P)⟩ := by
    intro k hk P
    apply TwPt.ext
    rw [twPt_smul_val, rowsArr_get hk, colsInvArr_get _ hk, M_conjSparse, hρ k hk, hψ k hk,
      ← map_inv, ← hinv _ (hσk k hk), hρ _ (invK_lt (hσk k hk))]
  have hroot : (⟨M (decode (encode (wordArr inp.base)))⟩ : TwPt ρ ψ) = ⟨M (wordArr inp.base)⟩ := by
    rw [decode_encode _ (wordArr_valid _).1 (wordArr_valid _).2]
  have hact : ∀ k < 8, ∀ a, (⟨M (decode (actOf (colsInvArr inp.sigma) k a))⟩ : TwPt ρ ψ) =
      gens k • (⟨M (decode a)⟩ : TwPt ρ ψ) := by
    intro k hk a
    rw [hsmul k hk]
    unfold actOf
    rw [decode_encode _ (size_conjSparse _ _ _) (fun p hp => lt_conjSparse _ _ _ hp)]
  have hnt' : ∃ g : G, g • (⟨M (wordArr inp.base)⟩ : TwPt ρ ψ) ≠ ⟨M (wordArr inp.base)⟩ := by
    simp only [okNontriv, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hnt
    obtain ⟨k, hk, hne⟩ := hnt
    refine ⟨gens k, fun h => hne ?_⟩
    rw [hsmul k hk] at h
    exact M_inj _ _ (size_conjSparse _ _ _) (wordArr_valid _).1
      (fun p hp => lt_conjSparse _ _ _ hp) (wordArr_valid _).2 (congrArg TwPt.val h)
  exact coatom_of_checks inp (⟨M (wordArr inp.base)⟩ : TwPt ρ ψ) gens hgen
    (fun n => (⟨M (decode n)⟩ : TwPt ρ ψ)) hroot hact hnt' hcheck

theorem primCheck_invol {inp : Input} (h : primCheck inp = true) :
    mmul (wordArr inp.base) (wordArr inp.base) = idArr := by
  unfold primCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hinv⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  simpa [okInvol] using hinv

section Stabilizers

variable {G : Type} [Group G]

theorem units_conj_eq_iff {R : Type*} [Monoid R] (u : Rˣ) (b : R) :
    u.val * b * (u⁻¹).val = b ↔ u.val * b = b * u.val := by
  constructor
  · intro h
    calc u.val * b = (u.val * b * (u⁻¹).val) * u.val := by
          rw [mul_assoc (u.val * b), Units.inv_mul, mul_one]
      _ = b * u.val := by rw [h]
  · intro h
    rw [h, mul_assoc, Units.mul_inv, mul_one]

theorem units_hom_comm_iff {R : Type*} [Monoid R] (ρ : G →* Rˣ) (hρ : Function.Injective ρ)
    (g z : G) : (ρ g).val * (ρ z).val = (ρ z).val * (ρ g).val ↔ g * z = z * g := by
  have hmul : ∀ a b : G, ((ρ (a * b) : Rˣ) : R) = (ρ a : R) * (ρ b : R) := fun a b => by
    rw [map_mul, Units.val_mul]
  constructor
  · intro h
    have h2 : ρ (g * z) = ρ (z * g) := Units.ext (by rw [hmul, hmul]; exact h)
    exact hρ h2
  · intro h
    have h2 := congrArg (fun x => ((ρ x : Rˣ) : R)) h
    simp only [hmul] at h2
    exact h2

theorem stabilizer_id_eq_centralizer (ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3))
    (hρ : Function.Injective ρ) (z : G) :
    MulAction.stabilizer G (⟨(ρ z : Mat3)⟩ : TwPt ρ (MonoidHom.id G)) =
      Subgroup.centralizer ({z} : Set G) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
  have h1 : g • (⟨(ρ z : Mat3)⟩ : TwPt ρ (MonoidHom.id G)) = ⟨(ρ z : Mat3)⟩ ↔
      ((ρ g : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) * (ρ z : Mat3) =
        (ρ z : Mat3) * (ρ g : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) := by
    rw [TwPt.ext_iff, twPt_smul_val]
    simp only [MonoidHom.id_apply]
    exact units_conj_eq_iff (ρ g) (ρ z : Mat3)
  rw [h1]
  exact units_hom_comm_iff ρ hρ g z

theorem stabilizer_one_eq_eqLocus (ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3))
    (hρ : Function.Injective ρ) (ψ : G →* G) :
    MulAction.stabilizer G (⟨1⟩ : TwPt ρ ψ) = ψ.eqLocus (MonoidHom.id G) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change _ ↔ ψ g = (MonoidHom.id G) g
  rw [TwPt.ext_iff, twPt_smul_val, mul_one]
  constructor
  · intro h
    have h2 : ρ g * (ρ (ψ g))⁻¹ = 1 := Units.ext h
    have h3 : ρ g = ρ (ψ g) := mul_inv_eq_one.1 h2
    exact (hρ h3).symm
  · intro h
    have h3 : ρ g = ρ (ψ g) := by rw [show ψ g = g from h]
    have h2 : ρ g * (ρ (ψ g))⁻¹ = 1 := mul_inv_eq_one.2 h3
    exact congrArg Units.val h2

end Stabilizers

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert
