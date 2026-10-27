module

public import CFSG.CGT.Stroth77.Extension26
public import CFSG.CGT.Stroth77.Extension22Final
public import CFSG.CGT.Stroth77.ExtensionOver

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

section Adjust

variable (D : StrothTypeData B (StrothTypeIndex.t201 m))

noncomputable def zAdj201 (r θ η : ℕ) : B :=
  D.c ^ ((r : ℤ) * 2 ^ (m - 1)) * D.a ^ ((θ : ℤ) * 2 ^ (m + 1)) *
    D.b ^ (((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1))

theorem ec_zAdj201 (r θ η : ℕ) :
    D.ec (zAdj201 D r θ η) =
      ((r : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t201 m).k 0 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 1 +
          (((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 2 := by
  rw [zAdj201, D.ec_mul, D.ec_mul, D.ec_zpow, D.ec_zpow, D.ec_zpow, D.ec_c, D.ec_a, D.ec_b]

theorem zAdj201_sq (hm : 1 ≤ m) (r θ η : ℕ) :
    zAdj201 D r θ η * zAdj201 D r θ η = 1 := by
  apply D.ec_injective
  rw [D.ec_mul, ec_zAdj201, D.ec_one, gens_add]
  have h2m : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := two_pow_succ_int hm
  have h2m' : 2 * (2 : ℤ) ^ (m + 1) = 2 ^ (m + 2) := two_mul_two_pow_int (m + 1)
  have h0 : ((((r : ℤ) * 2 ^ (m - 1)) + ((r : ℤ) * 2 ^ (m - 1)) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t201 m).k 0)) = 0 := by
    rw [show (StrothTypeIndex.t201 m).k 0 = m from k201_zero m]
    have he : (((r : ℤ) * 2 ^ (m - 1)) + ((r : ℤ) * 2 ^ (m - 1)) : ℤ) =
        ((r * 2 ^ m : ℕ) : ℤ) := by
      push_cast
      linear_combination (r : ℤ) * h2m
    rw [he, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left _ _
  have h1 : ((((θ : ℤ) * 2 ^ (m + 1)) + ((θ : ℤ) * 2 ^ (m + 1)) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t201 m).k 1)) = 0 := by
    rw [show (StrothTypeIndex.t201 m).k 1 = m + 2 from k201_one m]
    have he : (((θ : ℤ) * 2 ^ (m + 1)) + ((θ : ℤ) * 2 ^ (m + 1)) : ℤ) =
        ((θ * 2 ^ (m + 2) : ℕ) : ℤ) := by
      push_cast
      linear_combination (θ : ℤ) * h2m'
    rw [he, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left _ _
  have h2 : (((((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) +
      (((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t201 m).k 2)) = 0 := by
    rw [show (StrothTypeIndex.t201 m).k 2 = m + 2 from k201_two m]
    have he : ((((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) +
        (((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) : ℤ) =
        ((((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 2) : ℤ)) := by
      linear_combination ((η : ℤ) + (θ : ℤ)) * h2m'
    rw [he]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨((η : ℤ) + (θ : ℤ)), ?_⟩
    push_cast
    ring_nf
  rw [show (0 : Torus (StrothTypeIndex.t201 m).k) =
    (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
      (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 2 by simp]
  refine gens_eq_of_coord ?_ ?_ ?_
  · simpa using h0
  · simpa using h1
  · simpa using h2


section Adjust'
variable (D : StrothTypeData B (StrothTypeIndex.t201 m))

noncomputable def zS201 (r θ η : ℕ) : S :=
  (zAdj201 D r θ η : S)

noncomputable def dAdj201 (d : S) (r θ η : ℕ) : S :=
  d * zS201 D r θ η

theorem zS201_mem (r θ η : ℕ) : zS201 D r θ η ∈ B :=
  (zAdj201 D r θ η).2

theorem zS201_sq (hm : 1 ≤ m) (r θ η : ℕ) :
    zS201 D r θ η * zS201 D r θ η = 1 := by
  have h := zAdj201_sq D hm r θ η
  simpa [zS201] using congrArg (Subtype.val) h

theorem dAdj201_mem (hBC : B ≤ C) {d : S} (hdC : d ∈ C) (r θ η : ℕ) :
    dAdj201 D d r θ η ∈ C :=
  C.mul_mem hdC (hBC (zAdj201 D r θ η).2)

theorem dAdj201_notMem (hm : 1 ≤ m) {d : S} (hdB : d ∉ B) (r θ η : ℕ) :
    dAdj201 D d r θ η ∉ B := by
  intro h
  apply hdB
  have hz : zS201 D r θ η * zS201 D r θ η = 1 := zS201_sq D hm r θ η
  show d ∈ B
  rw [show d = d * (zS201 D r θ η * zS201 D r θ η) by rw [hz, mul_one], ← mul_assoc]
  exact B.mul_mem h (zS201_mem D r θ η)

theorem dAdj201_sq (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) (hm : 1 ≤ m) (r θ η : ℕ) :
    dAdj201 D d r θ η * dAdj201 D d r θ η = (D.c : S) := by
  letI : CommGroup C := { mul_comm := comm_of_le_centralizer_of_type D hBC hC hrel }
  have hcomm : (⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ : C) =
      (⟨d, hdC⟩ : C) * ⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩ := rfl
  have hz : (⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩ : C) *
      ⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩ = 1 := by
    apply Subtype.ext
    exact zS201_sq D hm r θ η
  have hCeq : (⟨dAdj201 D d r θ η * dAdj201 D d r θ η,
        C.mul_mem (dAdj201_mem D hBC hdC r θ η) (dAdj201_mem D hBC hdC r θ η)⟩ : C) =
      Subgroup.inclusion hBC D.c := by
    calc (⟨dAdj201 D d r θ η * dAdj201 D d r θ η,
          C.mul_mem (dAdj201_mem D hBC hdC r θ η) (dAdj201_mem D hBC hdC r θ η)⟩ : C)
        = (⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ : C) *
            ⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ := rfl
      _ = ((⟨d, hdC⟩ : C) * ⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩) *
            ((⟨d, hdC⟩ : C) * ⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩) := by rw [hcomm]
      _ = (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ * (⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩ *
            ⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩) := by
          have h := mul_mul_mul_comm (⟨d, hdC⟩ : C) ⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩
            ⟨d, hdC⟩ ⟨zS201 D r θ η, hBC (zS201_mem D r θ η)⟩
          simpa [mul_assoc] using h
      _ = Subgroup.inclusion hBC D.c := by
          rw [show (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ = Subgroup.inclusion hBC D.c from
            dC_sq_of_type D hBC hdC hd2, hz, mul_one]
  exact congrArg (Subtype.val) hCeq

section ConjAdj
variable {D}
variable (hBC : B ≤ C) {d : S} (hdC : d ∈ C) (r θ η : ℕ)
  {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)

theorem conj_dAdj201 (hm : 1 ≤ m) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b) :
    conjBy hgC (⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ : C) =
      ⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ *
        Subgroup.inclusion hBC (zAdj201 D r θ η * b * conjBy hgB (zAdj201 D r θ η)) := by
  have hdC' : (⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ : C) =
      (⟨d, hdC⟩ : C) * Subgroup.inclusion hBC (zAdj201 D r θ η) := Subtype.ext rfl
  have hz : Subgroup.inclusion hBC (zAdj201 D r θ η) *
      Subgroup.inclusion hBC (zAdj201 D r θ η) = 1 := by
    rw [← map_mul]
    rw [show zAdj201 D r θ η * zAdj201 D r θ η = 1 from zAdj201_sq D hm r θ η, map_one]
  have hdinv : (⟨d, hdC⟩ : C) = (⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ : C) *
      Subgroup.inclusion hBC (zAdj201 D r θ η) := by
    rw [hdC', mul_assoc, hz, mul_one]
  calc conjBy hgC (⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ : C)
      = conjBy hgC ((⟨d, hdC⟩ : C) * Subgroup.inclusion hBC (zAdj201 D r θ η)) := by rw [hdC']
    _ = conjBy hgC (⟨d, hdC⟩ : C) * conjBy hgC (Subgroup.inclusion hBC (zAdj201 D r θ η)) :=
        conjBy_mul hgC _ _
    _ = (⟨d, hdC⟩ * Subgroup.inclusion hBC b) *
        Subgroup.inclusion hBC (conjBy hgB (zAdj201 D r θ η)) := by
        rw [hb, conjBy_inclusion hBC hgC hgB]
    _ = ((⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ : C) *
          Subgroup.inclusion hBC (zAdj201 D r θ η)) * Subgroup.inclusion hBC b *
        Subgroup.inclusion hBC (conjBy hgB (zAdj201 D r θ η)) := by rw [hdinv]
    _ = (⟨dAdj201 D d r θ η, dAdj201_mem D hBC hdC r θ η⟩ : C) *
          Subgroup.inclusion hBC (zAdj201 D r θ η * b * conjBy hgB (zAdj201 D r θ η)) := by
        rw [map_mul, map_mul]
        group

end ConjAdj

end Adjust'

section CocycleAdj201

variable (D : StrothTypeData B (StrothTypeIndex.t201 m))

theorem PhiU201_apply_tau (m : ℕ) {a b c : ℤ} :
    Type201.PhiU m (a • gen (StrothTypeIndex.t201 m).k 0 +
        b • gen (StrothTypeIndex.t201 m).k 1 + c • gen (StrothTypeIndex.t201 m).k 2) =
      (a • gen (StrothTypeIndex.t201 m).k 0 + c • gen (StrothTypeIndex.t201 m).k 1 +
        b • gen (StrothTypeIndex.t201 m).k 2 :
        Torus (StrothTypeIndex.t201 m).k) := by
  exact Type201.PhiU_apply_gens (m) a b c

theorem PhiT201_apply_tau (m : ℕ) {a b c : ℤ} :
    Type201.PhiT m (a • gen (StrothTypeIndex.t201 m).k 0 +
        b • gen (StrothTypeIndex.t201 m).k 1 + c • gen (StrothTypeIndex.t201 m).k 2) =
      ((a - (2 * 2 ^ m + 1) * c) • gen (StrothTypeIndex.t201 m).k 0 +
        (4 * a + (-1 + 2 ^ (m + 1)) * b - (2 * 2 ^ m + 2) * c) •
          gen (StrothTypeIndex.t201 m).k 1 +
          (-(2 * 2 ^ m + 1) * c) • gen (StrothTypeIndex.t201 m).k 2 :
        Torus (StrothTypeIndex.t201 m).k) := by
  exact Type201.PhiT_apply_gens (m) a b c

theorem PhiR201_apply_tau (m : ℕ) {a b c : ℤ} :
    Type201.PhiR m (a • gen (StrothTypeIndex.t201 m).k 0 +
        b • gen (StrothTypeIndex.t201 m).k 1 + c • gen (StrothTypeIndex.t201 m).k 2) =
      ((a - c) • gen (StrothTypeIndex.t201 m).k 0 + (-c) • gen (StrothTypeIndex.t201 m).k 1 +
        (b - c) • gen (StrothTypeIndex.t201 m).k 2 :
        Torus (StrothTypeIndex.t201 m).k) := by
  exact Type201.PhiR_apply_gens (m) a b c

theorem PhiUV201_apply_tau (m : ℕ) {a b c : ℤ} :
    Type201.PhiUV m (a • gen (StrothTypeIndex.t201 m).k 0 +
        b • gen (StrothTypeIndex.t201 m).k 1 + c • gen (StrothTypeIndex.t201 m).k 2) =
      ((-3 * a + b + c) • gen (StrothTypeIndex.t201 m).k 0 +
        (-4 * a + b + (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) * c) •
          gen (StrothTypeIndex.t201 m).k 1 +
          (-4 * a + (2 + 2 ^ (m + 1)) * b + c) • gen (StrothTypeIndex.t201 m).k 2 :
        Torus (StrothTypeIndex.t201 m).k) := by
  exact Type201.PhiUV_apply_gens (m) a b c

theorem PhiUV201_a (m : ℕ) :
    Type201.PhiUV m (gen (StrothTypeIndex.t201 m).k 1) =
      (1 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (1 : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
        (2 + 2 ^ (m + 1) : ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  change Type201.PhiUV m (gen (Type201.k m) 1) =
    (1 : ℤ) • gen (Type201.k m) 0 + (1 : ℤ) • gen (Type201.k m) 1 +
        (2 + 2 ^ (m + 1) : ℤ) • gen (Type201.k m) 2
  conv_lhs => rw [show gen (Type201.k m) 1 =
    (0:ℤ) • gen (Type201.k m) 0 +
      (1:ℤ) • gen (Type201.k m) 1 +
        (0:ℤ) • gen (Type201.k m) 2 by simp]
  rw [Type201.PhiUV_apply_gens m 0 1 0]
  refine gens_eq_of_coord ?_ ?_ ?_ <;> congr 1 <;> ring

theorem PhiUV201_b (m : ℕ) :
    Type201.PhiUV m (gen (StrothTypeIndex.t201 m).k 2) =
      (1 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2 : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
        (1 : ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  change Type201.PhiUV m (gen (Type201.k m) 2) =
    (1 : ℤ) • gen (Type201.k m) 0 + (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2 : ℤ) • gen (Type201.k m) 1 +
        (1 : ℤ) • gen (Type201.k m) 2
  conv_lhs => rw [show gen (Type201.k m) 2 =
    (0:ℤ) • gen (Type201.k m) 0 +
      (0:ℤ) • gen (Type201.k m) 1 +
        (1:ℤ) • gen (Type201.k m) 2 by simp]
  rw [Type201.PhiUV_apply_gens m 0 0 1]
  refine gens_eq_of_coord ?_ ?_ ?_ <;> congr 1 <;> ring

theorem PhiT201_a (m : ℕ) :
    Type201.PhiT m (gen (StrothTypeIndex.t201 m).k 1) =
      (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (-1 + 2 ^ (m + 1) : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
        (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  change Type201.PhiT m (gen (Type201.k m) 1) =
    (0 : ℤ) • gen (Type201.k m) 0 + (-1 + 2 ^ (m + 1) : ℤ) • gen (Type201.k m) 1 +
        (0 : ℤ) • gen (Type201.k m) 2
  conv_lhs => rw [show gen (Type201.k m) 1 =
    (0:ℤ) • gen (Type201.k m) 0 +
      (1:ℤ) • gen (Type201.k m) 1 +
        (0:ℤ) • gen (Type201.k m) 2 by simp]
  rw [Type201.PhiT_apply_gens m 0 1 0]
  refine gens_eq_of_coord ?_ ?_ ?_ <;> congr 1 <;> ring

theorem PhiT201_b (m : ℕ) :
    Type201.PhiT m (gen (StrothTypeIndex.t201 m).k 2) =
      (-(2 * 2 ^ m + 1) : ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (-(2 * 2 ^ m + 2) : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
        (-(2 * 2 ^ m + 1) : ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  change Type201.PhiT m (gen (Type201.k m) 2) =
    (-(2 * 2 ^ m + 1) : ℤ) • gen (Type201.k m) 0 + (-(2 * 2 ^ m + 2) : ℤ) • gen (Type201.k m) 1 +
        (-(2 * 2 ^ m + 1) : ℤ) • gen (Type201.k m) 2
  conv_lhs => rw [show gen (Type201.k m) 2 =
    (0:ℤ) • gen (Type201.k m) 0 +
      (0:ℤ) • gen (Type201.k m) 1 +
        (1:ℤ) • gen (Type201.k m) 2 by simp]
  rw [Type201.PhiT_apply_gens m 0 0 1]
  refine gens_eq_of_coord ?_ ?_ ?_ <;> congr 1 <;> ring

theorem PhiU201_a (m : ℕ) :
    Type201.PhiU m (gen (StrothTypeIndex.t201 m).k 1) = (0:ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (0:ℤ) • gen (StrothTypeIndex.t201 m).k 1 + (1:ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  change Type201.PhiU m (gen (Type201.k m) 1) = (0:ℤ) • gen (Type201.k m) 0 + (0:ℤ) • gen (Type201.k m) 1 + (1:ℤ) • gen (Type201.k m) 2
  rw [show gen (Type201.k m) 1 =
    (0:ℤ) • gen (Type201.k m) 0 +
      (1:ℤ) • gen (Type201.k m) 1 +
        (0:ℤ) • gen (Type201.k m) 2 by simp]
  rw [Type201.PhiU_apply_gens m 0 1 0]
  norm_num

theorem PhiU201_b (m : ℕ) :
    Type201.PhiU m (gen (StrothTypeIndex.t201 m).k 2) = (0:ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (1:ℤ) • gen (StrothTypeIndex.t201 m).k 1 + (0:ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  change Type201.PhiU m (gen (Type201.k m) 2) = (0:ℤ) • gen (Type201.k m) 0 + (1:ℤ) • gen (Type201.k m) 1 + (0:ℤ) • gen (Type201.k m) 2
  rw [show gen (Type201.k m) 2 =
    (0:ℤ) • gen (Type201.k m) 0 +
      (0:ℤ) • gen (Type201.k m) 1 +
        (1:ℤ) • gen (Type201.k m) 2 by simp]
  rw [Type201.PhiU_apply_gens m 0 0 1]
  norm_num

theorem PhiR201_a (m : ℕ) :
    Type201.PhiR m (gen (StrothTypeIndex.t201 m).k 1) = (0:ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (0:ℤ) • gen (StrothTypeIndex.t201 m).k 1 + (1:ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  change Type201.PhiR m (gen (Type201.k m) 1) = (0:ℤ) • gen (Type201.k m) 0 + (0:ℤ) • gen (Type201.k m) 1 + (1:ℤ) • gen (Type201.k m) 2
  rw [show gen (Type201.k m) 1 =
    (0:ℤ) • gen (Type201.k m) 0 +
      (1:ℤ) • gen (Type201.k m) 1 +
        (0:ℤ) • gen (Type201.k m) 2 by simp]
  rw [Type201.PhiR_apply_gens m 0 1 0]
  norm_num

theorem PhiR201_b (m : ℕ) :
    Type201.PhiR m (gen (StrothTypeIndex.t201 m).k 2) = (-1:ℤ) • gen (StrothTypeIndex.t201 m).k 0 + (-1:ℤ) • gen (StrothTypeIndex.t201 m).k 1 + (-1:ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  change Type201.PhiR m (gen (Type201.k m) 2) = (-1:ℤ) • gen (Type201.k m) 0 + (-1:ℤ) • gen (Type201.k m) 1 + (-1:ℤ) • gen (Type201.k m) 2
  rw [show gen (Type201.k m) 2 =
    (0:ℤ) • gen (Type201.k m) 0 +
      (0:ℤ) • gen (Type201.k m) 1 +
        (1:ℤ) • gen (Type201.k m) 2 by simp]
  rw [Type201.PhiR_apply_gens m 0 0 1]
  norm_num

noncomputable def bU'201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (r θ η : ℕ) : B :=
  zAdj201 D r θ η * bU201 D hBC hrel hdC hdB hL * conjBy D.u_mem (zAdj201 D r θ η)

noncomputable def bT'201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (r θ η : ℕ) : B :=
  zAdj201 D r θ η * bT201 D hBC hrel hdC hdB hL * conjBy D.t_mem (zAdj201 D r θ η)

noncomputable def bR'201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (r θ η : ℕ) : B :=
  zAdj201 D r θ η * bR201 D hBC hrel hdC hdB hL * conjBy D.ρ_mem (zAdj201 D r θ η)

noncomputable def bUV'201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (r θ η : ℕ) : B :=
  zAdj201 D r θ η * bUV201 D hBC hrel hdC hdB hL * conjBy D.uv_mem (zAdj201 D r θ η)

theorem ec_bU'201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hm : 1 ≤ m) (r θ η ε δ : ℕ) (hδε : δ = η)
    (hX : xU201 D hBC hrel hdC hdB hL =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type201.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2) :
    D.ec (bU'201 D hBC hrel hdC hdB hL r θ η) =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t201 m).k 0 +
        (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
          (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  rw [xU201] at hX
  have hX' : D.ec (bU201 D hBC hrel hdC hdB hL) =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t201 m).k 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 2 := by
    exact hX
  rw [bU'201, D.ec_mul, D.ec_mul, StrothTypeData.ec_conj_u_t201, ec_zAdj201,
    PhiU201_apply_tau, hX', gens_add, gens_add]
  refine gens_eq_of_mul (t0 := (r : ℤ)) (t1 := (δ : ℤ) + (θ : ℤ))
    (t2 := (δ : ℤ) + (θ : ℤ)) ?_ ?_ ?_
  · rw [show (StrothTypeIndex.t201 m).k 0 = m from k201_zero m]
    rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    ring_nf
  · rw [show (StrothTypeIndex.t201 m).k 1 = m + 2 from k201_one m, hδε]
    try rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) from by rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring]
    ring_nf
  · rw [show (StrothTypeIndex.t201 m).k 2 = m + 2 from k201_two m, hδε]
    try rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) from by rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring]
    ring_nf


theorem ec_bT'201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hm : 1 ≤ m) (r θ η α q : ℕ) (hαr : α = r)
    (hY : yT201 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type201.k m) 0 +
      ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((q : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2) :
    D.ec (bT'201 D hBC hrel hdC hdB hL r θ η) =
      (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 +
        (2 : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
          ((q : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 2 := by
  rw [yT201] at hY
  have hY' : D.ec (bT201 D hBC hrel hdC hdB hL) = (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 +
      ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 1 +
        ((q : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 2 := by
    exact hY
  rw [bT'201, D.ec_mul, D.ec_mul, StrothTypeData.ec_conj_t_t201, ec_zAdj201,
    PhiT201_apply_tau, hY', gens_add, gens_add]
  have hp2 : (2 : ℤ) ^ (m + 2) = 8 * 2 ^ (m - 1) := by
    rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring
  have hp1 : (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) := two_pow_succ_eq_four hm
  have hp0 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := (two_pow_succ_int hm).symm
  refine gens_eq_of_mul
    (t0 := (r : ℤ) - 2 * (η : ℤ) - 2 * (θ : ℤ) - 8 * 2 ^ (m - 1) * ((η : ℤ) + (θ : ℤ)))
    (t1 := (r : ℤ) - (η : ℤ) - (θ : ℤ) - 2 * 2 ^ (m - 1) * (η : ℤ))
    (t2 := -2 * 2 ^ (m - 1) * ((η : ℤ) + (θ : ℤ))) ?_ ?_ ?_ <;>
    simp only [show (StrothTypeIndex.t201 m).k 0 = m from k201_zero m,
      show (StrothTypeIndex.t201 m).k 1 = m + 2 from k201_one m,
      show (StrothTypeIndex.t201 m).k 2 = m + 2 from k201_two m, hp2, hp1, hp0, hαr] <;>
    ring

theorem ec_bR'201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hm : 1 ≤ m) (r θ η : ℕ)
    (hZ : zR201 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type201.k m) 0 +
      ((η : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2) :
    D.ec (bR'201 D hBC hrel hdC hdB hL r θ η) =
      (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 +
        (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
          (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  rw [zR201] at hZ
  have hZ' : D.ec (bR201 D hBC hrel hdC hdB hL) = (0 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 +
      ((η : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 2 := by
    exact hZ
  rw [bR'201, D.ec_mul, D.ec_mul, StrothTypeData.ec_conj_ρ_t201, ec_zAdj201,
    PhiR201_apply_tau, hZ', gens_add, gens_add]
  refine gens_eq_of_mul (t0 := (r : ℤ) - 2 * (η : ℤ) - 2 * (θ : ℤ))
    (t1 := 0) (t2 := (θ : ℤ)) ?_ ?_ ?_
  · rw [show (StrothTypeIndex.t201 m).k 0 = m from k201_zero m]
    rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m from (two_mul_two_pow_int m).symm]
    rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    ring
  · rw [show (StrothTypeIndex.t201 m).k 1 = m + 2 from k201_one m]
    ring
  · rw [show (StrothTypeIndex.t201 m).k 2 = m + 2 from k201_two m]
    try rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) from by rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring]
    ring

theorem ec_bUV'201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hm : 1 ≤ m) (r θ η p q : ℕ)
    (hpe : Even ((p : ℤ) - (r : ℤ) - (q : ℤ)))
    (hW : wUV201 D hBC hrel hdC hdB hL = (-2 : ℤ) • gen (Type201.k m) 0 +
      ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2) :
    D.ec (bUV'201 D hBC hrel hdC hdB hL r θ η) =
      (-2 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 +
        ((-2 : ℤ) + (q : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 1 +
          (-2 : ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
  obtain ⟨s, hs⟩ := hpe
  rw [wUV201] at hW
  have hW' : D.ec (bUV201 D hBC hrel hdC hdB hL) = (-2 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 +
      ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t201 m).k 2 := by
    exact hW
  rw [bUV'201, D.ec_mul, D.ec_mul, StrothTypeData.ec_conj_uv_t201, ec_zAdj201,
    PhiUV201_apply_tau, hW', gens_add, gens_add]
  have hp2 : (2 : ℤ) ^ (m + 2) = 8 * 2 ^ (m - 1) := by
    rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring
  have hp1 : (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) := two_pow_succ_eq_four hm
  have hp0 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := (two_pow_succ_int hm).symm
  refine gens_eq_of_mul (t0 := -(r : ℤ) + 2 * (η : ℤ) + 4 * (θ : ℤ))
    (t1 := s + (η : ℤ) + 2 * (θ : ℤ) + 8 * (2 ^ (m - 1)) ^ 2 * ((η : ℤ) + (θ : ℤ)) +
      6 * 2 ^ (m - 1) * ((η : ℤ) + (θ : ℤ)))
    (t2 := (η : ℤ) + 2 * (θ : ℤ) + 2 * 2 ^ (m - 1) * (θ : ℤ)) ?_ ?_ ?_ <;>
    simp only [show (StrothTypeIndex.t201 m).k 0 = m from k201_zero m,
      show (StrothTypeIndex.t201 m).k 1 = m + 2 from k201_one m,
      show (StrothTypeIndex.t201 m).k 2 = m + 2 from k201_two m, hp2, hp1, hp0]
  · ring
  · linear_combination 4 * (2 : ℤ) ^ (m - 1) * hs
  · ring


section CubicBasis

variable (D : StrothTypeData B (StrothTypeIndex.t201 m))

theorem m_t201 (m : ℕ) : (StrothTypeIndex.t201 m).m = m := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t201 m)) 0
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons] at h
  rw [show (StrothTypeIndex.t201 m).k 0 = m from k201_zero m] at h
  exact h.symm

theorem n_t201 (m : ℕ) : (StrothTypeIndex.t201 m).n = m + 2 := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t201 m)) 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons] at h
  rw [show (StrothTypeIndex.t201 m).k 1 = m + 2 from k201_one m] at h
  exact h.symm

structure CubicBasisEquiv201 (hBC : B ≤ C) (d : S) (hdC : d ∈ C) (k : Fin 3 → ℕ) where
  e : Additive C ≃+ Torus k
  e_d : e (Additive.ofMul ⟨d, hdC⟩) = gen k 0
  e_a : e (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k 1
  e_b : e (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k 2

noncomputable def addEquivOfSq201 (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (k : Fin 3 → ℕ) (hk0 : k 0 = m + 1) (hk1 : k 1 = m + 2) (hk2 : k 2 = m + 2) :
    CubicBasisEquiv201 D hBC d hdC k := by
  letI : CommGroup C := { mul_comm := comm_of_le_centralizer_of_type D hBC hC hrel }
  let dC : C := ⟨d, hdC⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  let bC : C := ⟨D.b, hBC D.b.2⟩
  let x : (i : Fin 3) → Additive C := ![Additive.ofMul dC, Additive.ofMul aC, Additive.ofMul bC]
  have hd2C : dC ^ 2 = ⟨D.c, hBC D.c.2⟩ := by
    apply Subtype.ext
    simp [dC, pow_two, hd2]
  have hcOrder : orderOf (⟨D.c, hBC D.c.2⟩ : C) = 2 ^ m := by
    rw [show (⟨D.c, hBC D.c.2⟩ : C) = Subgroup.inclusion hBC D.c from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.c,
      D.orderOf_c]
    rw [m_t201]
  have hcC : (⟨D.c, hBC D.c.2⟩ : C) ^ (2 ^ m) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hcOrder]
  have hdN : dC ^ (2 ^ (m + 1)) = 1 := by
    rw [show 2 ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ'], pow_mul, hd2C, hcC]
  have haOrder : orderOf aC = 2 ^ (k 1) := by
    rw [show aC = Subgroup.inclusion hBC D.a from rfl]
    rw [orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.a]
    rw [D.orderOf_a, n_t201, hk1]
  have hbOrder : orderOf bC = 2 ^ (k 2) := by
    rw [show bC = Subgroup.inclusion hBC D.b from rfl]
    rw [orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.b]
    rw [D.orderOf_b, n_t201, hk2]
  have haN : aC ^ (2 ^ k 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, haOrder]
  have hbN : bC ^ (2 ^ k 2) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hbOrder]
  have hx : ∀ i, (2 ^ k i) • x i = 0 := by
    intro i
    fin_cases i
    · change (2 ^ k 0) • Additive.ofMul dC = 0
      rw [hk0, ← ofMul_pow, hdN]
      simp
    · change (2 ^ k 1) • Additive.ofMul aC = 0
      rw [← ofMul_pow, haN]
      simp
    · change (2 ^ k 2) • Additive.ofMul bC = 0
      rw [← ofMul_pow, hbN]
      simp
  let f : Torus k →+ Additive C := torusHomOfGens k x hx
  have hfgen : ∀ i : Fin 3, f (gen k i) = x i := fun i => torusHomOfGens_gen x hx i
  have hsurj : Function.Surjective f := by
    have hK : f.range.toSubgroup' = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro z
      have hle : Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S) ≤
          f.range.toSubgroup'.map C.subtype := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · refine Subgroup.mem_map.mpr ⟨dC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx0 : x 0 = Additive.ofMul dC := rfl
          rw [← hx0, ← hfgen 0]
          exact ⟨gen k 0, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨aC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx1 : x 1 = Additive.ofMul aC := rfl
          rw [← hx1, ← hfgen 1]
          exact ⟨gen k 1, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨bC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx2 : x 2 = Additive.ofMul bC := rfl
          rw [← hx2, ← hfgen 2]
          exact ⟨gen k 2, rfl⟩
      have hC' : C ≤ f.range.toSubgroup'.map C.subtype :=
        calc C = Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S) :=
              (closure_eq_of_sq_of_type D hBC hrel hdC hdB hd2).symm
          _ ≤ f.range.toSubgroup'.map C.subtype := hle
      have hz : (z : S) ∈ f.range.toSubgroup'.map C.subtype := hC' z.2
      rcases Subgroup.mem_map.mp hz with ⟨k', hk', hks⟩
      have hkz : k' = z := Subtype.ext hks
      simpa [hkz] using hk'
    have hrange : f.range = ⊤ := by
      apply AddSubgroup.toSubgroup'.injective
      simpa using hK
    exact AddMonoidHom.range_eq_top.mp hrange
  have hcardT : Nat.card (Torus k) = 2 ^ (k 0 + k 1 + k 2) := natCard_torus k
  have hcardC : Nat.card C = 2 ^ (k 0 + k 1 + k 2) := by
    rw [hrel, D.card]
    have hBk : (StrothTypeIndex.t201 m).k 0 + (StrothTypeIndex.t201 m).k 1 +
        (StrothTypeIndex.t201 m).k 2 = m + (m + 2) + (m + 2) := by
      rw [show (StrothTypeIndex.t201 m).k 0 = m from k201_zero m,
        show (StrothTypeIndex.t201 m).k 1 = m + 2 from k201_one m,
        show (StrothTypeIndex.t201 m).k 2 = m + 2 from k201_two m]
    rw [hBk, hk0, hk1, hk2]
    rw [show 2 * 2 ^ (m + (m + 2) + (m + 2)) = 2 ^ ((m + 1) + (m + 2) + (m + 2)) by
      rw [show (m + 1) + (m + 2) + (m + 2) = (m + (m + 2) + (m + 2)) + 1 by ring, pow_succ]
      ring]
  have heq : Nat.card (Torus k) = Nat.card (Additive C) := by
    rw [hcardT, ← Nat.card_congr Additive.ofMul, hcardC]
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (le_of_eq heq)
  let e : Additive C ≃+ Torus k := (AddEquiv.ofBijective f hbij).symm
  have ed : e (Additive.ofMul ⟨d, hdC⟩) = gen k 0 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨d, hdC⟩) = gen k 0
    rw [show Additive.ofMul ⟨d, hdC⟩ = x 0 from rfl, ← hfgen 0]
    exact AddEquiv.symm_apply_apply _ _
  have ea : e (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k 1 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k 1
    rw [show Additive.ofMul ⟨D.a, hBC D.a.2⟩ = x 1 from rfl, ← hfgen 1]
    exact AddEquiv.symm_apply_apply _ _
  have eb : e (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k 2 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k 2
    rw [show Additive.ofMul ⟨D.b, hBC D.b.2⟩ = x 2 from rfl, ← hfgen 2]
    exact AddEquiv.symm_apply_apply _ _
  exact ⟨e, ed, ea, eb⟩


@[expose]
def basisElems201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (hBC : B ≤ C) {d : S}
    (hdC : d ∈ C) : Fin 3 → C :=
  ![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩]

theorem eq_c_zpow_mul_a_b201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) {β : B} {i j l : ℤ}
    (h : D.ec β = i • gen (StrothTypeIndex.t201 m).k 0 +
      j • gen (StrothTypeIndex.t201 m).k 1 + l • gen (StrothTypeIndex.t201 m).k 2) :
    β = D.c ^ i * D.a ^ j * D.b ^ l := by
  apply D.ec_injective
  rw [h, D.ec_mul, D.ec_mul, D.ec_zpow, D.ec_zpow, D.ec_zpow, D.ec_c, D.ec_a, D.ec_b]

theorem E_e_inclusion201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S))
    {k : Fin 3 → ℕ} (E : CubicBasisEquiv201 D hBC d hdC k) (β : B) {i j l : ℤ}
    (hβ : D.ec β = i • gen (StrothTypeIndex.t201 m).k 0 +
      j • gen (StrothTypeIndex.t201 m).k 1 + l • gen (StrothTypeIndex.t201 m).k 2) :
    E.e (Additive.ofMul (⟨β, hBC β.2⟩ : C)) =
      (2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  have hβ' : β = D.c ^ i * D.a ^ j * D.b ^ l := eq_c_zpow_mul_a_b201 D hβ
  have hdc : (⟨D.c, hBC D.c.2⟩ : C) = (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ :=
    (dC_sq_of_type D hBC hdC hd2).symm
  have hcimg : E.e (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = (2 : ℤ) • gen k 0 := by
    rw [hdc, ofMul_mul, map_add, E.e_d]
    rw [two_zsmul]
  have hci : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.c ^ n, hBC (D.c ^ n).2⟩ : C)) =
      n • ((2 : ℤ) • gen k 0) := by
    intro n
    have hsub : (⟨D.c ^ n, hBC (D.c ^ n).2⟩ : C) = ⟨D.c, hBC D.c.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, hcimg]
  have hai : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.a ^ n, hBC (D.a ^ n).2⟩ : C)) =
      n • gen k 1 := by
    intro n
    have hsub : (⟨D.a ^ n, hBC (D.a ^ n).2⟩ : C) = ⟨D.a, hBC D.a.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, E.e_a]
  have hbi : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.b ^ n, hBC (D.b ^ n).2⟩ : C)) =
      n • gen k 2 := by
    intro n
    have hsub : (⟨D.b ^ n, hBC (D.b ^ n).2⟩ : C) = ⟨D.b, hBC D.b.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, E.e_b]
  have hprod : (⟨β, hBC β.2⟩ : C) = ⟨D.c ^ i, hBC (D.c ^ i).2⟩ *
      ⟨D.a ^ j, hBC (D.a ^ j).2⟩ * ⟨D.b ^ l, hBC (D.b ^ l).2⟩ := by
    apply Subtype.ext
    simp [hβ']
  rw [hprod]
  rw [show Additive.ofMul (⟨D.c ^ i, hBC (D.c ^ i).2⟩ * ⟨D.a ^ j, hBC (D.a ^ j).2⟩ *
      ⟨D.b ^ l, hBC (D.b ^ l).2⟩ : C) =
      Additive.ofMul ⟨D.c ^ i, hBC (D.c ^ i).2⟩ + Additive.ofMul ⟨D.a ^ j, hBC (D.a ^ j).2⟩ +
        Additive.ofMul ⟨D.b ^ l, hBC (D.b ^ l).2⟩ by rw [ofMul_mul, ofMul_mul]]
  rw [map_add, map_add, hci, hai, hbi, smul_smul]
  module

end CubicBasis

end CocycleAdj201
section Images

variable (D : StrothTypeData B (StrothTypeIndex.t201 m))

theorem E_image_d201 (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) {k : Fin 3 → ℕ}
    (E : CubicBasisEquiv201 D hBC d hdC k) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {b : B} (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    {i j l : ℤ} (h : D.ec b = i • gen (StrothTypeIndex.t201 m).k 0 +
      j • gen (StrothTypeIndex.t201 m).k 1 + l • gen (StrothTypeIndex.t201 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨d, hdC⟩ : C))) =
      (1 + 2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  rw [hb, ofMul_mul, map_add, E.e_d]
  have hsub : Additive.ofMul ((Subgroup.inclusion hBC) b) = Additive.ofMul (⟨b, hBC b.2⟩ : C) :=
    congrArg Additive.ofMul rfl
  rw [hsub, E_e_inclusion201 D hBC hdC hd2 E b h]
  module

theorem E_image_a201 (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) {k : Fin 3 → ℕ}
    (E : CubicBasisEquiv201 D hBC d hdC k) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {i j l : ℤ} (h : D.ec (conjBy hgB D.a) = i • gen (StrothTypeIndex.t201 m).k 0 +
      j • gen (StrothTypeIndex.t201 m).k 1 + l • gen (StrothTypeIndex.t201 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨D.a, hBC D.a.2⟩ : C))) =
      (2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  have hsub : conjBy hgC (⟨D.a, hBC D.a.2⟩ : C) =
      (⟨conjBy hgB D.a, hBC (conjBy hgB D.a).2⟩ : C) := Subtype.ext rfl
  rw [hsub]
  exact E_e_inclusion201 D hBC hdC hd2 E _ h

theorem E_image_b201 (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) {k : Fin 3 → ℕ}
    (E : CubicBasisEquiv201 D hBC d hdC k) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {i j l : ℤ} (h : D.ec (conjBy hgB D.b) = i • gen (StrothTypeIndex.t201 m).k 0 +
      j • gen (StrothTypeIndex.t201 m).k 1 + l • gen (StrothTypeIndex.t201 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨D.b, hBC D.b.2⟩ : C))) =
      (2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  have hsub : conjBy hgC (⟨D.b, hBC D.b.2⟩ : C) =
      (⟨conjBy hgB D.b, hBC (conjBy hgB D.b).2⟩ : C) := Subtype.ext rfl
  rw [hsub]
  exact E_e_inclusion201 D hBC hdC hd2 E _ h

end Images


section Assembly

variable (D : StrothTypeData B (StrothTypeIndex.t201 m))

theorem hasStrothTypeOver_t101_of_generator_images201
    (hBC : B ≤ C) (_hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (_hdB : d ∉ B)
    (_hd2 : d * d = (D.c : S))
    (E : CubicBasisEquiv201 D hBC d hdC (Type101.k m))
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems201 D hBC hdC j))) =
      (Type101.action m).φuv (gen (Type101.k m) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems201 D hBC hdC j))) =
      (Type101.action m).φt (gen (Type101.k m) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems201 D hBC hdC j))) =
      (Type101.action m).φu (gen (Type101.k m) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems201 D hBC hdC j))) =
      (Type101.action m).φρ (gen (Type101.k m) j)) :
    HasStrothTypeOver D C (StrothTypeIndex.t101 m) := by
  let xd : C := ⟨d, hdC⟩
  let xa : C := ⟨D.a, hBC D.a.2⟩
  let xb : C := ⟨D.b, hBC D.b.2⟩
  have hxd : E.e (Additive.ofMul xd) = gen (Type101.k m) 0 := E.e_d
  have hxa : E.e (Additive.ofMul xa) = gen (Type101.k m) 1 := E.e_a
  have hxb : E.e (Additive.ofMul xb) = gen (Type101.k m) 2 := E.e_b
  refine ⟨⟨E.e, D.uv, D.t, D.u, D.ρ, D.uv_sq, D.t_sq, D.uv_comm_t, D.rho_cube, D.u_sq,
    D.u_rho, D.uv_rho, D.t_rho, D.uv_comm_u, D.t_u, hL D.uv_mem_L, hL D.t_mem_L,
    hL D.u_mem_L, hL D.ρ_mem_L,
    conj_eq_of_generator_images (hL D.uv_mem_L) E.e
      (Type101.action m).φuv hxd hxa hxb (huv 0) (huv 1) (huv 2),
    conj_eq_of_generator_images (hL D.t_mem_L) E.e
      (Type101.action m).φt hxd hxa hxb (ht 0) (ht 1) (ht 2),
    conj_eq_of_generator_images (hL D.u_mem_L) E.e
      (Type101.action m).φu hxd hxa hxb (hu 0) (hu 1) (hu 2),
    conj_eq_of_generator_images (hL D.ρ_mem_L) E.e
      (Type101.action m).φρ hxd hxa hxb (hρ 0) (hρ 1) (hρ 2)⟩, rfl, rfl, rfl, rfl⟩

theorem hasStrothType_t101_of_generator_images201
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S))
    (E : CubicBasisEquiv201 D hBC d hdC (Type101.k m))
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems201 D hBC hdC j))) =
      (Type101.action m).φuv (gen (Type101.k m) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems201 D hBC hdC j))) =
      (Type101.action m).φt (gen (Type101.k m) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems201 D hBC hdC j))) =
      (Type101.action m).φu (gen (Type101.k m) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems201 D hBC hdC j))) =
      (Type101.action m).φρ (gen (Type101.k m) j)) :
    HasStrothType C (StrothTypeIndex.t101 m) :=
  (hasStrothTypeOver_t101_of_generator_images201 D hBC hrel hL hdC hdB hd2 E huv ht hu hρ)
    |>.hasStrothType

theorem hasStrothTypeOver_t111_of_generator_images201
    (hBC : B ≤ C) (_hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (_hdB : d ∉ B)
    (_hd2 : d * d = (D.c : S))
    (E : CubicBasisEquiv201 D hBC d hdC (Type111.k (m - 1)))
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems201 D hBC hdC j))) =
      (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems201 D hBC hdC j))) =
      (Type111.action (m - 1)).φt (gen (Type111.k (m - 1)) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems201 D hBC hdC j))) =
      (Type111.action (m - 1)).φu (gen (Type111.k (m - 1)) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems201 D hBC hdC j))) =
      (Type111.action (m - 1)).φρ (gen (Type111.k (m - 1)) j)) :
    HasStrothTypeOver D C (StrothTypeIndex.t111 (m - 1)) := by
  let xd : C := ⟨d, hdC⟩
  let xa : C := ⟨D.a, hBC D.a.2⟩
  let xb : C := ⟨D.b, hBC D.b.2⟩
  have hxd : E.e (Additive.ofMul xd) = gen (Type111.k (m - 1)) 0 := E.e_d
  have hxa : E.e (Additive.ofMul xa) = gen (Type111.k (m - 1)) 1 := E.e_a
  have hxb : E.e (Additive.ofMul xb) = gen (Type111.k (m - 1)) 2 := E.e_b
  refine ⟨⟨E.e, D.uv, D.t, D.u, D.ρ, D.uv_sq, D.t_sq, D.uv_comm_t, D.rho_cube, D.u_sq,
    D.u_rho, D.uv_rho, D.t_rho, D.uv_comm_u, D.t_u, hL D.uv_mem_L, hL D.t_mem_L,
    hL D.u_mem_L, hL D.ρ_mem_L,
    conj_eq_of_generator_images (hL D.uv_mem_L) E.e
      (Type111.action (m - 1)).φuv hxd hxa hxb (huv 0) (huv 1) (huv 2),
    conj_eq_of_generator_images (hL D.t_mem_L) E.e
      (Type111.action (m - 1)).φt hxd hxa hxb (ht 0) (ht 1) (ht 2),
    conj_eq_of_generator_images (hL D.u_mem_L) E.e
      (Type111.action (m - 1)).φu hxd hxa hxb (hu 0) (hu 1) (hu 2),
    conj_eq_of_generator_images (hL D.ρ_mem_L) E.e
      (Type111.action (m - 1)).φρ hxd hxa hxb (hρ 0) (hρ 1) (hρ 2)⟩, rfl, rfl, rfl, rfl⟩

theorem hasStrothType_t111_of_generator_images201
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S))
    (E : CubicBasisEquiv201 D hBC d hdC (Type111.k (m - 1)))
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems201 D hBC hdC j))) =
      (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems201 D hBC hdC j))) =
      (Type111.action (m - 1)).φt (gen (Type111.k (m - 1)) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems201 D hBC hdC j))) =
      (Type111.action (m - 1)).φu (gen (Type111.k (m - 1)) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems201 D hBC hdC j))) =
      (Type111.action (m - 1)).φρ (gen (Type111.k (m - 1)) j)) :
    HasStrothType C (StrothTypeIndex.t111 (m - 1)) :=
  (hasStrothTypeOver_t111_of_generator_images201 D hBC hrel hL hdC hdB hd2 E huv ht hu hρ)
    |>.hasStrothType

end Assembly

theorem Type111_uv_gen_two (hm : 1 ≤ m) :
    (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) 2) =
      (2 : ℤ) • gen (Type111.k (m - 1)) 0 +
        (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2 : ℤ) • gen (Type111.k (m - 1)) 1 +
        (1 : ℤ) • gen (Type111.k (m - 1)) 2 := by
  rw [show (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) 2) =
      (2 - 16 * 2 ^ (m - 1) : ℤ) • gen (Type111.k (m - 1)) 0 +
        (16 * (2 ^ (m - 1)) ^ 2 + 4 * 2 ^ (m - 1) + 2 : ℤ) • gen (Type111.k (m - 1)) 1 +
          (1 - 8 * 2 ^ (m - 1) : ℤ) • gen (Type111.k (m - 1)) 2 from
    Type111.uv_b (m - 1)]
  have hp0 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := (two_pow_succ_int hm).symm
  refine gens_eq_of_mul (t0 := -4) (t1 := -1) (t2 := -1) ?_ ?_ ?_
  · rw [show (Type111.k (m - 1)) 0 = m + 1 from by simp [Type111.k]; omega]
    rw [show (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) from two_pow_succ_eq_four hm]
    ring
  · rw [show (Type111.k (m - 1)) 1 = m + 2 from by simp [Type111.k]; omega]
    rw [show (2 : ℤ) ^ (m + 2) = 8 * 2 ^ (m - 1) from by
      rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring, hp0]
    ring
  · rw [show (Type111.k (m - 1)) 2 = m + 2 from by simp [Type111.k]; omega]
    rw [show (2 : ℤ) ^ (m + 2) = 8 * 2 ^ (m - 1) from by
      rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring]
    ring

end Adjust


section Final

theorem hasStrothTypeOver_t101_or_t111_of_noInvolutionsCentralizing
    {B C S' : Subgroup S} {m : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t201 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothTypeOver D C (StrothTypeIndex.t101 m) ∨
    HasStrothTypeOver D C (StrothTypeIndex.t111 (m - 1)) := by
  classical
  have hm : 1 ≤ m := one_le_of_noInvolutionsCentralizing_t201_of_data D hBC hC hrel hL hH hcS hne
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_of_data_t201 D hBC hC hrel hL hH hcS hne
  obtain ⟨ε, δ, hε1, hδ1, hX⟩ :=
    form_xU201 D hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨α, q, hα1, hq1, hY⟩ :=
    form_yT201 D hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨θ, η, hη1, hθ1, hZ⟩ :=
    form_zR201 D hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨p, r, hp1, hr1, hW⟩ :=
    form_wUV201 D hBC hC hrel hdC hdB hd2 hL hm
  have hεp : ε = (p + r) % 2 :=
    bit_eps_201 (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL) (hm := hm) (ε := ε) (δ := δ) (p := p) (r := r) hε1 hδ1 hp1 hr1 hX hW
  have hαq : α = r ∧ q = (p + r) % 2 :=
    bit_alpha_q_201 (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL) (hm := hm) (ε := ε) (δ := δ) (α := α) (q := q) (p := p) (r := r)
      hα1 hq1 hp1 hr1 hY hZ hW
  have hδη : δ = η :=
    bit_delta_201 (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL) (hm := hm) (ε := ε) (δ := δ) (p := p) (r := r) (η := η) (θ := θ)
      hε1 hδ1 hη1 hθ1 hX hZ
  have hqε : q = ε := by rw [hαq.2, hεp]
  have hpe : Even ((p : ℤ) - (r : ℤ) - (q : ℤ)) := by
    rw [hαq.2]
    interval_cases p <;> interval_cases r <;> norm_num
  let d' : S := dAdj201 D d r θ η
  have hd'C : d' ∈ C := dAdj201_mem D hBC hdC r θ η
  have hd'B : d' ∉ B := dAdj201_notMem D hm hdB r θ η
  have hd'2 : d' * d' = (D.c : S) :=
    dAdj201_sq D hBC hC hrel hdC hd2 hm r θ η
  rcases (by omega : q = 0 ∨ q = 1) with hq0 | hq1'
  ·
    subst hq0
    have hε0 : ε = 0 := by omega
    left
    let E : CubicBasisEquiv201 D hBC d' hd'C (Type101.k m) :=
      addEquivOfSq201 D hBC hC hrel hd'C hd'B hd'2 (Type101.k m)
        (by simp [Type101.k]) (by simp [Type101.k]) (by simp [Type101.k])
    refine hasStrothTypeOver_t101_of_generator_images201 D hBC hrel hL hd'C hd'B hd'2 E ?_ ?_ ?_ ?_
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type101.action m).φuv (gen (Type101.k m) 0)
        rw [E_image_d201 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (conj_dAdj201 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.uv) (hgC := hL D.uv_mem_L) (hgB := D.uv_mem) (hm := hm)
            (hb := conj_eq_bUV201 D hBC hrel hdC hdB hL))
          (ec_bUV'201 D hBC hrel hdC hdB hL hm r θ η p 0 hpe hW)]
        rw [show (Type101.action m).φuv (gen (Type101.k m) 0) =
            (-3 : ℤ) • gen (Type101.k m) 0 + (-2 : ℤ) • gen (Type101.k m) 1 +
              (-2 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.uv_c m]
        simp only [Nat.cast_zero, zero_mul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type101.action m).φuv (gen (Type101.k m) 1)
        rw [E_image_a201 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (by rw [StrothTypeData.ec_conj_uv_t201, D.ec_a]
              exact PhiUV201_a m)]
        rw [show (Type101.action m).φuv (gen (Type101.k m) 1) =
            (2 : ℤ) • gen (Type101.k m) 0 + (1 : ℤ) • gen (Type101.k m) 1 +
              (2 * 2 ^ m + 2 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b] using Type101.uv_a m]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type101.action m).φuv (gen (Type101.k m) 2)
        rw [E_image_b201 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (by rw [StrothTypeData.ec_conj_uv_t201, D.ec_b]
              exact PhiUV201_b m)]
        rw [show (Type101.action m).φuv (gen (Type101.k m) 2) =
            (2 : ℤ) • gen (Type101.k m) 0 + (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2 : ℤ) • gen (Type101.k m) 1 +
              (1 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b] using Type101.uv_b m]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type101.action m).φt (gen (Type101.k m) 0)
        rw [E_image_d201 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (conj_dAdj201 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.t) (hgC := hL D.t_mem_L) (hgB := D.t_mem) (hm := hm)
            (hb := conj_eq_bT201 D hBC hrel hdC hdB hL))
          (ec_bT'201 D hBC hrel hdC hdB hL hm r θ η α 0 hαq.1 hY)]
        rw [show (Type101.action m).φt (gen (Type101.k m) 0) =
            (1 : ℤ) • gen (Type101.k m) 0 + (2 : ℤ) • gen (Type101.k m) 1 +
              (0 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.t_c m]
        simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type101.action m).φt (gen (Type101.k m) 1)
        rw [E_image_a201 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (by rw [StrothTypeData.ec_conj_t_t201, D.ec_a]
              exact PhiT201_a m)]
        rw [show (Type101.action m).φt (gen (Type101.k m) 1) =
            (0 : ℤ) • gen (Type101.k m) 0 + (2 * 2 ^ m - 1 : ℤ) • gen (Type101.k m) 1 +
              (0 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.t_a m]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type101.action m).φt (gen (Type101.k m) 2)
        rw [E_image_b201 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (by rw [StrothTypeData.ec_conj_t_t201, D.ec_b]
              exact PhiT201_b m)]
        rw [show (Type101.action m).φt (gen (Type101.k m) 2) =
            (-4 * 2 ^ m - 2 : ℤ) • gen (Type101.k m) 0 + (-2 * 2 ^ m - 2 : ℤ) • gen (Type101.k m) 1 +
              (-2 * 2 ^ m - 1 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b] using Type101.t_b m]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type101.action m).φu (gen (Type101.k m) 0)
        rw [E_image_d201 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (conj_dAdj201 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.u) (hgC := hL D.u_mem_L) (hgB := D.u_mem) (hm := hm)
            (hb := conj_eq_bU201 D hBC hrel hdC hdB hL))
          (ec_bU'201 D hBC hrel hdC hdB hL hm r θ η ε δ hδη hX)]
        rw [show (Type101.action m).φu (gen (Type101.k m) 0) =
            (1 : ℤ) • gen (Type101.k m) 0 + (0 : ℤ) • gen (Type101.k m) 1 +
              (0 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.u_c m]
        simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, hε0]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type101.action m).φu (gen (Type101.k m) 1)
        rw [E_image_a201 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (by rw [StrothTypeData.ec_conj_u_t201, D.ec_a]
              exact PhiU201_a m)]
        rw [show (Type101.action m).φu (gen (Type101.k m) 1) =
            (0 : ℤ) • gen (Type101.k m) 0 + (0 : ℤ) • gen (Type101.k m) 1 +
              (1 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.u_a m]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type101.action m).φu (gen (Type101.k m) 2)
        rw [E_image_b201 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (by rw [StrothTypeData.ec_conj_u_t201, D.ec_b]
              exact PhiU201_b m)]
        rw [show (Type101.action m).φu (gen (Type101.k m) 2) =
            (0 : ℤ) • gen (Type101.k m) 0 + (1 : ℤ) • gen (Type101.k m) 1 +
              (0 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.u_b m]
        simp only [zero_smul, add_zero]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type101.action m).φρ (gen (Type101.k m) 0)
        rw [E_image_d201 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (conj_dAdj201 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.ρ) (hgC := hL D.ρ_mem_L) (hgB := D.ρ_mem) (hm := hm)
            (hb := conj_eq_bR201 D hBC hrel hdC hdB hL))
          (ec_bR'201 D hBC hrel hdC hdB hL hm r θ η hZ)]
        rw [show (Type101.action m).φρ (gen (Type101.k m) 0) =
            (1 : ℤ) • gen (Type101.k m) 0 + (0 : ℤ) • gen (Type101.k m) 1 +
              (0 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.rho_c m]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type101.action m).φρ (gen (Type101.k m) 1)
        rw [E_image_a201 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (by rw [StrothTypeData.ec_conj_ρ_t201, D.ec_a]
              exact PhiR201_a m)]
        rw [show (Type101.action m).φρ (gen (Type101.k m) 1) =
            (0 : ℤ) • gen (Type101.k m) 0 + (0 : ℤ) • gen (Type101.k m) 1 +
              (1 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.rho_a m]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type101.action m).φρ (gen (Type101.k m) 2)
        rw [E_image_b201 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (by rw [StrothTypeData.ec_conj_ρ_t201, D.ec_b]
              exact PhiR201_b m)]
        rw [show (Type101.action m).φρ (gen (Type101.k m) 2) =
            (-2 : ℤ) • gen (Type101.k m) 0 + (-1 : ℤ) • gen (Type101.k m) 1 +
              (-1 : ℤ) • gen (Type101.k m) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type101.rho_b m]
        module
  ·
    subst hq1'
    have hε1' : ε = 1 := by omega
    right
    let E : CubicBasisEquiv201 D hBC d' hd'C (Type111.k (m - 1)) :=
      addEquivOfSq201 D hBC hC hrel hd'C hd'B hd'2 (Type111.k (m - 1))
        (by simp [Type111.k]; omega) (by simp [Type111.k]; omega) (by simp [Type111.k]; omega)
    refine hasStrothTypeOver_t111_of_generator_images201 D hBC hrel hL hd'C hd'B hd'2 E ?_ ?_ ?_ ?_
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) 0)
        rw [E_image_d201 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (conj_dAdj201 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.uv) (hgC := hL D.uv_mem_L) (hgB := D.uv_mem) (hm := hm)
            (hb := conj_eq_bUV201 D hBC hrel hdC hdB hL))
          (ec_bUV'201 D hBC hrel hdC hdB hL hm r θ η p 1 hpe hW)]
        rw [show (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) 0) =
            (-3 : ℤ) • gen (Type111.k (m - 1)) 0 +
              ((4 : ℤ) * 2 ^ (m - 1) - 2) • gen (Type111.k (m - 1)) 1 +
              (-2 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b] using Type111.uv_c (m - 1)]
        simp only [Nat.cast_one, one_mul]
        rw [show (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) from two_pow_succ_eq_four hm]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) 1)
        rw [E_image_a201 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (by rw [StrothTypeData.ec_conj_uv_t201, D.ec_a]
              exact PhiUV201_a m)]
        rw [show (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) 1) =
            (2 : ℤ) • gen (Type111.k (m - 1)) 0 + (1 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (4 * 2 ^ (m - 1) + 2 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b] using Type111.uv_a (m - 1)]
        rw [show (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) from two_pow_succ_eq_four hm]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) 2)
        rw [E_image_b201 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (by rw [StrothTypeData.ec_conj_uv_t201, D.ec_b]
              exact PhiUV201_b m)]
        rw [show (Type111.action (m - 1)).φuv (gen (Type111.k (m - 1)) 2) =
            (2 : ℤ) • gen (Type111.k (m - 1)) 0 + (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (1 : ℤ) • gen (Type111.k (m - 1)) 2 from Type111_uv_gen_two hm]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type111.action (m - 1)).φt (gen (Type111.k (m - 1)) 0)
        rw [E_image_d201 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (conj_dAdj201 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.t) (hgC := hL D.t_mem_L) (hgB := D.t_mem) (hm := hm)
            (hb := conj_eq_bT201 D hBC hrel hdC hdB hL))
          (ec_bT'201 D hBC hrel hdC hdB hL hm r θ η α 1 hαq.1 hY)]
        rw [show (Type111.action (m - 1)).φt (gen (Type111.k (m - 1)) 0) =
            (1 : ℤ) • gen (Type111.k (m - 1)) 0 + (2 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (2 ^ (m + 1) : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa [Torus.c, Torus.a, Torus.b, two_pow_succ_eq_four hm] using Type111.t_c (m - 1)]
        simp only [Nat.cast_one, one_mul]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type111.action (m - 1)).φt (gen (Type111.k (m - 1)) 1)
        rw [E_image_a201 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (by rw [StrothTypeData.ec_conj_t_t201, D.ec_a]
              exact PhiT201_a m)]
        rw [show (Type111.action (m - 1)).φt (gen (Type111.k (m - 1)) 1) =
            (0 : ℤ) • gen (Type111.k (m - 1)) 0 + (4 * 2 ^ (m - 1) - 1 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (0 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using
            Type111.t_a (m - 1)]
        simp only [zero_smul, add_zero]
        rw [show (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) from two_pow_succ_eq_four hm]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type111.action (m - 1)).φt (gen (Type111.k (m - 1)) 2)
        rw [E_image_b201 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (by rw [StrothTypeData.ec_conj_t_t201, D.ec_b]
              exact PhiT201_b m)]
        rw [show (Type111.action (m - 1)).φt (gen (Type111.k (m - 1)) 2) =
            (-8 * 2 ^ (m - 1) - 2 : ℤ) • gen (Type111.k (m - 1)) 0 + (-4 * 2 ^ (m - 1) - 2 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (-4 * 2 ^ (m - 1) - 1 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b] using Type111.t_b (m - 1)]
        rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type111.action (m - 1)).φu (gen (Type111.k (m - 1)) 0)
        rw [E_image_d201 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (conj_dAdj201 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.u) (hgC := hL D.u_mem_L) (hgB := D.u_mem) (hm := hm)
            (hb := conj_eq_bU201 D hBC hrel hdC hdB hL))
          (ec_bU'201 D hBC hrel hdC hdB hL hm r θ η ε δ hδη hX)]
        rw [show (Type111.action (m - 1)).φu (gen (Type111.k (m - 1)) 0) =
            ((1 : ℤ) + 2 ^ m) • gen (Type111.k (m - 1)) 0 + (0 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (0 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, two_pow_succ_int hm, add_comm, zero_smul, add_zero, zero_add] using Type111.u_c (m - 1)]
        simp only [Nat.cast_one, one_mul, zero_smul, add_zero,
          hε1']
        rw [two_pow_succ_int hm]
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type111.action (m - 1)).φu (gen (Type111.k (m - 1)) 1)
        rw [E_image_a201 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (by rw [StrothTypeData.ec_conj_u_t201, D.ec_a]
              exact PhiU201_a m)]
        rw [show (Type111.action (m - 1)).φu (gen (Type111.k (m - 1)) 1) =
            (0 : ℤ) • gen (Type111.k (m - 1)) 0 + (0 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (1 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type111.u_a (m - 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type111.action (m - 1)).φu (gen (Type111.k (m - 1)) 2)
        rw [E_image_b201 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (by rw [StrothTypeData.ec_conj_u_t201, D.ec_b]
              exact PhiU201_b m)]
        rw [show (Type111.action (m - 1)).φu (gen (Type111.k (m - 1)) 2) =
            (0 : ℤ) • gen (Type111.k (m - 1)) 0 + (1 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (0 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type111.u_b (m - 1)]
        simp only [zero_smul, add_zero]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type111.action (m - 1)).φρ (gen (Type111.k (m - 1)) 0)
        rw [E_image_d201 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (conj_dAdj201 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.ρ) (hgC := hL D.ρ_mem_L) (hgB := D.ρ_mem) (hm := hm)
            (hb := conj_eq_bR201 D hBC hrel hdC hdB hL))
          (ec_bR'201 D hBC hrel hdC hdB hL hm r θ η hZ)]
        rw [show (Type111.action (m - 1)).φρ (gen (Type111.k (m - 1)) 0) =
            (1 : ℤ) • gen (Type111.k (m - 1)) 0 + (0 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (0 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type111.rho_c (m - 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type111.action (m - 1)).φρ (gen (Type111.k (m - 1)) 1)
        rw [E_image_a201 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (by rw [StrothTypeData.ec_conj_ρ_t201, D.ec_a]
              exact PhiR201_a m)]
        rw [show (Type111.action (m - 1)).φρ (gen (Type111.k (m - 1)) 1) =
            (0 : ℤ) • gen (Type111.k (m - 1)) 0 + (0 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (1 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type111.rho_a (m - 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type111.action (m - 1)).φρ (gen (Type111.k (m - 1)) 2)
        rw [E_image_b201 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (by rw [StrothTypeData.ec_conj_ρ_t201, D.ec_b]
              exact PhiR201_b m)]
        rw [show (Type111.action (m - 1)).φρ (gen (Type111.k (m - 1)) 2) =
            (-2 : ℤ) • gen (Type111.k (m - 1)) 0 + (-1 : ℤ) • gen (Type111.k (m - 1)) 1 +
              (-1 : ℤ) • gen (Type111.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type111.rho_b (m - 1)]
        module

theorem hasStrothType_t101_or_t111_of_noInvolutionsCentralizing
    [Finite S] {B C S' : Subgroup S} {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t201 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothType C (StrothTypeIndex.t101 m) ∨
    HasStrothType C (StrothTypeIndex.t111 (m - 1)) :=
  (hasStrothTypeOver_t101_or_t111_of_noInvolutionsCentralizing hB.data hBC hC hrel hL hH hcS hne)
    |>.imp (·.hasStrothType) (·.hasStrothType)

end Final

end CFSG.CGT.Stroth77

end
