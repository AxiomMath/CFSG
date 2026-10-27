module

public import CFSG.CGT.Stroth77.Extension23
public import CFSG.CGT.Stroth77.Extension22Final
public import CFSG.CGT.Stroth77.ExtensionOver

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

section Adjust

variable (D : StrothTypeData B (StrothTypeIndex.t200 m))

noncomputable def zAdj200 (r θ η : ℕ) : B :=
  D.c ^ ((r : ℤ) * 2 ^ (m - 1)) * D.a ^ ((θ : ℤ) * 2 ^ (m + 1)) *
    D.b ^ (((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1))

theorem ec_zAdj200 (r θ η : ℕ) :
    D.ec (zAdj200 D r θ η) =
      ((r : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t200 m).k 0 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 1 +
          (((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 2 := by
  rw [zAdj200, D.ec_mul, D.ec_mul, D.ec_zpow, D.ec_zpow, D.ec_zpow, D.ec_c, D.ec_a, D.ec_b]

theorem zAdj200_sq (hm : 1 ≤ m) (r θ η : ℕ) :
    zAdj200 D r θ η * zAdj200 D r θ η = 1 := by
  apply D.ec_injective
  rw [D.ec_mul, ec_zAdj200, D.ec_one, gens_add]
  have h2m : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := two_pow_succ_int hm
  have h2m' : 2 * (2 : ℤ) ^ (m + 1) = 2 ^ (m + 2) := two_mul_two_pow_int (m + 1)
  have h0 : ((((r : ℤ) * 2 ^ (m - 1)) + ((r : ℤ) * 2 ^ (m - 1)) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t200 m).k 0)) = 0 := by
    rw [show (StrothTypeIndex.t200 m).k 0 = m from k200_zero m]
    have he : (((r : ℤ) * 2 ^ (m - 1)) + ((r : ℤ) * 2 ^ (m - 1)) : ℤ) =
        ((r * 2 ^ m : ℕ) : ℤ) := by
      push_cast
      linear_combination (r : ℤ) * h2m
    rw [he, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left _ _
  have h1 : ((((θ : ℤ) * 2 ^ (m + 1)) + ((θ : ℤ) * 2 ^ (m + 1)) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t200 m).k 1)) = 0 := by
    rw [show (StrothTypeIndex.t200 m).k 1 = m + 2 from k200_one m]
    have he : (((θ : ℤ) * 2 ^ (m + 1)) + ((θ : ℤ) * 2 ^ (m + 1)) : ℤ) =
        ((θ * 2 ^ (m + 2) : ℕ) : ℤ) := by
      push_cast
      linear_combination (θ : ℤ) * h2m'
    rw [he, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left _ _
  have h2 : (((((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) +
      (((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t200 m).k 2)) = 0 := by
    rw [show (StrothTypeIndex.t200 m).k 2 = m + 2 from k200_two m]
    have he : ((((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) +
        (((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 1)) : ℤ) =
        ((((η : ℤ) + (θ : ℤ)) * 2 ^ (m + 2) : ℤ)) := by
      linear_combination ((η : ℤ) + (θ : ℤ)) * h2m'
    rw [he]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨((η : ℤ) + (θ : ℤ)), ?_⟩
    push_cast
    ring_nf
  rw [show (0 : Torus (StrothTypeIndex.t200 m).k) =
    (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 1 +
      (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 2 by simp]
  refine gens_eq_of_coord ?_ ?_ ?_
  · simpa using h0
  · simpa using h1
  · simpa using h2


section Adjust'
variable (D : StrothTypeData B (StrothTypeIndex.t200 m))

noncomputable def zS200 (r θ η : ℕ) : S :=
  (zAdj200 D r θ η : S)

noncomputable def dAdj200 (d : S) (r θ η : ℕ) : S :=
  d * zS200 D r θ η

theorem zS200_mem (r θ η : ℕ) : zS200 D r θ η ∈ B :=
  (zAdj200 D r θ η).2

theorem zS200_sq (hm : 1 ≤ m) (r θ η : ℕ) :
    zS200 D r θ η * zS200 D r θ η = 1 := by
  have h := zAdj200_sq D hm r θ η
  simpa [zS200] using congrArg (Subtype.val) h

theorem dAdj200_mem (hBC : B ≤ C) {d : S} (hdC : d ∈ C) (r θ η : ℕ) :
    dAdj200 D d r θ η ∈ C :=
  C.mul_mem hdC (hBC (zAdj200 D r θ η).2)

theorem dAdj200_notMem (hm : 1 ≤ m) {d : S} (hdB : d ∉ B) (r θ η : ℕ) :
    dAdj200 D d r θ η ∉ B := by
  intro h
  apply hdB
  have hz : zS200 D r θ η * zS200 D r θ η = 1 := zS200_sq D hm r θ η
  show d ∈ B
  rw [show d = d * (zS200 D r θ η * zS200 D r θ η) by rw [hz, mul_one], ← mul_assoc]
  exact B.mul_mem h (zS200_mem D r θ η)

theorem dAdj200_sq (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) (hm : 1 ≤ m) (r θ η : ℕ) :
    dAdj200 D d r θ η * dAdj200 D d r θ η = (D.c : S) := by
  letI : CommGroup C := { mul_comm := comm_of_le_centralizer_of_type D hBC hC hrel }
  have hcomm : (⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ : C) =
      (⟨d, hdC⟩ : C) * ⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩ := rfl
  have hz : (⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩ : C) *
      ⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩ = 1 := by
    apply Subtype.ext
    exact zS200_sq D hm r θ η
  have hCeq : (⟨dAdj200 D d r θ η * dAdj200 D d r θ η,
        C.mul_mem (dAdj200_mem D hBC hdC r θ η) (dAdj200_mem D hBC hdC r θ η)⟩ : C) =
      Subgroup.inclusion hBC D.c := by
    calc (⟨dAdj200 D d r θ η * dAdj200 D d r θ η,
          C.mul_mem (dAdj200_mem D hBC hdC r θ η) (dAdj200_mem D hBC hdC r θ η)⟩ : C)
        = (⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ : C) *
            ⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ := rfl
      _ = ((⟨d, hdC⟩ : C) * ⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩) *
            ((⟨d, hdC⟩ : C) * ⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩) := by rw [hcomm]
      _ = (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ * (⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩ *
            ⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩) := by
          have h := mul_mul_mul_comm (⟨d, hdC⟩ : C) ⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩
            ⟨d, hdC⟩ ⟨zS200 D r θ η, hBC (zS200_mem D r θ η)⟩
          simpa [mul_assoc] using h
      _ = Subgroup.inclusion hBC D.c := by
          rw [show (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ = Subgroup.inclusion hBC D.c from
            dC_sq_of_type D hBC hdC hd2, hz, mul_one]
  exact congrArg (Subtype.val) hCeq

section ConjAdj
variable {D}
variable (hBC : B ≤ C) {d : S} (hdC : d ∈ C) (r θ η : ℕ)
  {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)

theorem conj_dAdj200 (hm : 1 ≤ m) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b) :
    conjBy hgC (⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ : C) =
      ⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ *
        Subgroup.inclusion hBC (zAdj200 D r θ η * b * conjBy hgB (zAdj200 D r θ η)) := by
  have hdC' : (⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ : C) =
      (⟨d, hdC⟩ : C) * Subgroup.inclusion hBC (zAdj200 D r θ η) := Subtype.ext rfl
  have hz : Subgroup.inclusion hBC (zAdj200 D r θ η) *
      Subgroup.inclusion hBC (zAdj200 D r θ η) = 1 := by
    rw [← map_mul]
    rw [show zAdj200 D r θ η * zAdj200 D r θ η = 1 from zAdj200_sq D hm r θ η, map_one]
  have hdinv : (⟨d, hdC⟩ : C) = (⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ : C) *
      Subgroup.inclusion hBC (zAdj200 D r θ η) := by
    rw [hdC', mul_assoc, hz, mul_one]
  calc conjBy hgC (⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ : C)
      = conjBy hgC ((⟨d, hdC⟩ : C) * Subgroup.inclusion hBC (zAdj200 D r θ η)) := by rw [hdC']
    _ = conjBy hgC (⟨d, hdC⟩ : C) * conjBy hgC (Subgroup.inclusion hBC (zAdj200 D r θ η)) :=
        conjBy_mul hgC _ _
    _ = (⟨d, hdC⟩ * Subgroup.inclusion hBC b) *
        Subgroup.inclusion hBC (conjBy hgB (zAdj200 D r θ η)) := by
        rw [hb, conjBy_inclusion hBC hgC hgB]
    _ = ((⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ : C) *
          Subgroup.inclusion hBC (zAdj200 D r θ η)) * Subgroup.inclusion hBC b *
        Subgroup.inclusion hBC (conjBy hgB (zAdj200 D r θ η)) := by rw [hdinv]
    _ = (⟨dAdj200 D d r θ η, dAdj200_mem D hBC hdC r θ η⟩ : C) *
          Subgroup.inclusion hBC (zAdj200 D r θ η * b * conjBy hgB (zAdj200 D r θ η)) := by
        rw [map_mul, map_mul]
        group

end ConjAdj

end Adjust'

section CocycleAdj200

variable (D : StrothTypeData B (StrothTypeIndex.t200 m))

theorem PhiU200_apply_tau (m : ℕ) {a b c : ℤ} :
    Type200.PhiU m (a • gen (StrothTypeIndex.t200 m).k 0 +
        b • gen (StrothTypeIndex.t200 m).k 1 + c • gen (StrothTypeIndex.t200 m).k 2) =
      a • gen (StrothTypeIndex.t200 m).k 0 + c • gen (StrothTypeIndex.t200 m).k 1 +
        b • gen (StrothTypeIndex.t200 m).k 2 := by
  exact Type200.PhiU_apply_gens (m) a b c

theorem PhiT200_apply_tau (m : ℕ) {a b c : ℤ} :
    Type200.PhiT m (a • gen (StrothTypeIndex.t200 m).k 0 +
        b • gen (StrothTypeIndex.t200 m).k 1 + c • gen (StrothTypeIndex.t200 m).k 2) =
      (a - c) • gen (StrothTypeIndex.t200 m).k 0 +
        (4 * a - b - 2 * c) • gen (StrothTypeIndex.t200 m).k 1 +
          (-c) • gen (StrothTypeIndex.t200 m).k 2 := by
  exact Type200.PhiT_apply_gens (m) a b c

theorem PhiR200_apply_tau (m : ℕ) {a b c : ℤ} :
    Type200.PhiR m (a • gen (StrothTypeIndex.t200 m).k 0 +
        b • gen (StrothTypeIndex.t200 m).k 1 + c • gen (StrothTypeIndex.t200 m).k 2) =
      (a - c) • gen (StrothTypeIndex.t200 m).k 0 + (-c) • gen (StrothTypeIndex.t200 m).k 1 +
        (b - c) • gen (StrothTypeIndex.t200 m).k 2 := by
  exact Type200.PhiR_apply_gens (m) a b c

theorem PhiUV200_apply_tau (m : ℕ) {a b c : ℤ} :
    Type200.PhiUV m (a • gen (StrothTypeIndex.t200 m).k 0 +
        b • gen (StrothTypeIndex.t200 m).k 1 + c • gen (StrothTypeIndex.t200 m).k 2) =
      (-3 * a + b + c) • gen (StrothTypeIndex.t200 m).k 0 +
        (-4 * a + b + 2 * c) • gen (StrothTypeIndex.t200 m).k 1 +
          (-4 * a + 2 * b + c) • gen (StrothTypeIndex.t200 m).k 2 := by
  exact Type200.PhiUV_apply_gens (m) a b c

theorem PhiUV200_a (m : ℕ) :
    Type200.PhiUV m (gen (StrothTypeIndex.t200 m).k 1) = (1:ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (1:ℤ) • gen (StrothTypeIndex.t200 m).k 1 + (2:ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  change Type200.PhiUV m (gen (Type200.k m) 1) = (1:ℤ) • gen (Type200.k m) 0 + (1:ℤ) • gen (Type200.k m) 1 + (2:ℤ) • gen (Type200.k m) 2
  rw [show gen (Type200.k m) 1 =
    (0:ℤ) • gen (Type200.k m) 0 +
      (1:ℤ) • gen (Type200.k m) 1 +
        (0:ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiUV_apply_gens m 0 1 0]
  norm_num

theorem PhiUV200_b (m : ℕ) :
    Type200.PhiUV m (gen (StrothTypeIndex.t200 m).k 2) = (1:ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (2:ℤ) • gen (StrothTypeIndex.t200 m).k 1 + (1:ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  change Type200.PhiUV m (gen (Type200.k m) 2) = (1:ℤ) • gen (Type200.k m) 0 + (2:ℤ) • gen (Type200.k m) 1 + (1:ℤ) • gen (Type200.k m) 2
  rw [show gen (Type200.k m) 2 =
    (0:ℤ) • gen (Type200.k m) 0 +
      (0:ℤ) • gen (Type200.k m) 1 +
        (1:ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiUV_apply_gens m 0 0 1]
  norm_num

theorem PhiT200_a (m : ℕ) :
    Type200.PhiT m (gen (StrothTypeIndex.t200 m).k 1) = (0:ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (-1:ℤ) • gen (StrothTypeIndex.t200 m).k 1 + (0:ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  change Type200.PhiT m (gen (Type200.k m) 1) = (0:ℤ) • gen (Type200.k m) 0 + (-1:ℤ) • gen (Type200.k m) 1 + (0:ℤ) • gen (Type200.k m) 2
  rw [show gen (Type200.k m) 1 =
    (0:ℤ) • gen (Type200.k m) 0 +
      (1:ℤ) • gen (Type200.k m) 1 +
        (0:ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiT_apply_gens m 0 1 0]
  norm_num

theorem PhiT200_b (m : ℕ) :
    Type200.PhiT m (gen (StrothTypeIndex.t200 m).k 2) = (-1:ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (-2:ℤ) • gen (StrothTypeIndex.t200 m).k 1 + (-1:ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  change Type200.PhiT m (gen (Type200.k m) 2) = (-1:ℤ) • gen (Type200.k m) 0 + (-2:ℤ) • gen (Type200.k m) 1 + (-1:ℤ) • gen (Type200.k m) 2
  rw [show gen (Type200.k m) 2 =
    (0:ℤ) • gen (Type200.k m) 0 +
      (0:ℤ) • gen (Type200.k m) 1 +
        (1:ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiT_apply_gens m 0 0 1]
  norm_num

theorem PhiU200_a (m : ℕ) :
    Type200.PhiU m (gen (StrothTypeIndex.t200 m).k 1) = (0:ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (0:ℤ) • gen (StrothTypeIndex.t200 m).k 1 + (1:ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  change Type200.PhiU m (gen (Type200.k m) 1) = (0:ℤ) • gen (Type200.k m) 0 + (0:ℤ) • gen (Type200.k m) 1 + (1:ℤ) • gen (Type200.k m) 2
  rw [show gen (Type200.k m) 1 =
    (0:ℤ) • gen (Type200.k m) 0 +
      (1:ℤ) • gen (Type200.k m) 1 +
        (0:ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiU_apply_gens m 0 1 0]
  norm_num

theorem PhiU200_b (m : ℕ) :
    Type200.PhiU m (gen (StrothTypeIndex.t200 m).k 2) = (0:ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (1:ℤ) • gen (StrothTypeIndex.t200 m).k 1 + (0:ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  change Type200.PhiU m (gen (Type200.k m) 2) = (0:ℤ) • gen (Type200.k m) 0 + (1:ℤ) • gen (Type200.k m) 1 + (0:ℤ) • gen (Type200.k m) 2
  rw [show gen (Type200.k m) 2 =
    (0:ℤ) • gen (Type200.k m) 0 +
      (0:ℤ) • gen (Type200.k m) 1 +
        (1:ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiU_apply_gens m 0 0 1]
  norm_num

theorem PhiR200_a (m : ℕ) :
    Type200.PhiR m (gen (StrothTypeIndex.t200 m).k 1) = (0:ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (0:ℤ) • gen (StrothTypeIndex.t200 m).k 1 + (1:ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  change Type200.PhiR m (gen (Type200.k m) 1) = (0:ℤ) • gen (Type200.k m) 0 + (0:ℤ) • gen (Type200.k m) 1 + (1:ℤ) • gen (Type200.k m) 2
  rw [show gen (Type200.k m) 1 =
    (0:ℤ) • gen (Type200.k m) 0 +
      (1:ℤ) • gen (Type200.k m) 1 +
        (0:ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiR_apply_gens m 0 1 0]
  norm_num

theorem PhiR200_b (m : ℕ) :
    Type200.PhiR m (gen (StrothTypeIndex.t200 m).k 2) = (-1:ℤ) • gen (StrothTypeIndex.t200 m).k 0 + (-1:ℤ) • gen (StrothTypeIndex.t200 m).k 1 + (-1:ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  change Type200.PhiR m (gen (Type200.k m) 2) = (-1:ℤ) • gen (Type200.k m) 0 + (-1:ℤ) • gen (Type200.k m) 1 + (-1:ℤ) • gen (Type200.k m) 2
  rw [show gen (Type200.k m) 2 =
    (0:ℤ) • gen (Type200.k m) 0 +
      (0:ℤ) • gen (Type200.k m) 1 +
        (1:ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiR_apply_gens m 0 0 1]
  norm_num

noncomputable def bU'200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (r θ η : ℕ) : B :=
  zAdj200 D r θ η * bU200 D hBC hrel hdC hdB hL * conjBy D.u_mem (zAdj200 D r θ η)

noncomputable def bT'200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (r θ η : ℕ) : B :=
  zAdj200 D r θ η * bT200 D hBC hrel hdC hdB hL * conjBy D.t_mem (zAdj200 D r θ η)

noncomputable def bR'200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (r θ η : ℕ) : B :=
  zAdj200 D r θ η * bR200 D hBC hrel hdC hdB hL * conjBy D.ρ_mem (zAdj200 D r θ η)

noncomputable def bUV'200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (r θ η : ℕ) : B :=
  zAdj200 D r θ η * bUV200 D hBC hrel hdC hdB hL * conjBy D.uv_mem (zAdj200 D r θ η)

theorem ec_bU'200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hm : 1 ≤ m) (r θ η ε δ : ℕ) (hδε : δ = η)
    (hX : xU200 D hBC hrel hdC hdB hL =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type200.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2) :
    D.ec (bU'200 D hBC hrel hdC hdB hL r θ η) =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t200 m).k 0 +
        (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 1 +
          (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  rw [xU200] at hX
  have hX' : D.ec (bU200 D hBC hrel hdC hdB hL) =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t200 m).k 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 2 := by
    exact hX
  rw [bU'200, D.ec_mul, D.ec_mul, StrothTypeData.ec_conj_u_t200, ec_zAdj200,
    PhiU200_apply_tau, hX', gens_add, gens_add]
  refine gens_eq_of_mul (t0 := (r : ℤ)) (t1 := (δ : ℤ) + (θ : ℤ))
    (t2 := (δ : ℤ) + (θ : ℤ)) ?_ ?_ ?_
  · rw [show (StrothTypeIndex.t200 m).k 0 = m from k200_zero m]
    rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    ring_nf
  · rw [show (StrothTypeIndex.t200 m).k 1 = m + 2 from k200_one m, hδε]
    try rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) from by rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring]
    ring_nf
  · rw [show (StrothTypeIndex.t200 m).k 2 = m + 2 from k200_two m, hδε]
    try rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) from by rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring]
    ring_nf


theorem ec_bT'200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hm : 1 ≤ m) (r θ η α q : ℕ) (hαr : α = r)
    (hY : yT200 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type200.k m) 0 +
      ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((q : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2) :
    D.ec (bT'200 D hBC hrel hdC hdB hL r θ η) =
      (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 0 +
        (2 : ℤ) • gen (StrothTypeIndex.t200 m).k 1 +
          ((q : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 2 := by
  rw [yT200] at hY
  have hY' : D.ec (bT200 D hBC hrel hdC hdB hL) = (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 0 +
      ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 1 +
        ((q : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 2 := by
    exact hY
  rw [bT'200, D.ec_mul, D.ec_mul, StrothTypeData.ec_conj_t_t200, ec_zAdj200,
    PhiT200_apply_tau, hY', gens_add, gens_add]
  refine gens_eq_of_mul (t0 := (r : ℤ) - 2 * (η : ℤ) - 2 * (θ : ℤ))
    (t1 := (r : ℤ) - (η : ℤ) - (θ : ℤ)) (t2 := 0) ?_ ?_ ?_
  · rw [show (StrothTypeIndex.t200 m).k 0 = m from k200_zero m]
    rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m from (two_mul_two_pow_int m).symm]
    rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    ring
  · rw [show (StrothTypeIndex.t200 m).k 1 = m + 2 from k200_one m]
    try rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) from by rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring]
    rw [hαr]
    ring_nf
    rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    ring
  · rw [show (StrothTypeIndex.t200 m).k 2 = m + 2 from k200_two m]
    ring

theorem ec_bR'200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hm : 1 ≤ m) (r θ η : ℕ)
    (hZ : zR200 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type200.k m) 0 +
      ((η : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2) :
    D.ec (bR'200 D hBC hrel hdC hdB hL r θ η) =
      (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 0 +
        (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 1 +
          (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  rw [zR200] at hZ
  have hZ' : D.ec (bR200 D hBC hrel hdC hdB hL) = (0 : ℤ) • gen (StrothTypeIndex.t200 m).k 0 +
      ((η : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 2 := by
    exact hZ
  rw [bR'200, D.ec_mul, D.ec_mul, StrothTypeData.ec_conj_ρ_t200, ec_zAdj200,
    PhiR200_apply_tau, hZ', gens_add, gens_add]
  refine gens_eq_of_mul (t0 := (r : ℤ) - 2 * (η : ℤ) - 2 * (θ : ℤ))
    (t1 := 0) (t2 := (θ : ℤ)) ?_ ?_ ?_
  · rw [show (StrothTypeIndex.t200 m).k 0 = m from k200_zero m]
    rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m from (two_mul_two_pow_int m).symm]
    rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    ring
  · rw [show (StrothTypeIndex.t200 m).k 1 = m + 2 from k200_one m]
    ring
  · rw [show (StrothTypeIndex.t200 m).k 2 = m + 2 from k200_two m]
    try rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) from by rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring]
    ring

theorem ec_bUV'200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hm : 1 ≤ m) (r θ η p q : ℕ)
    (hpe : Even ((p : ℤ) - (r : ℤ) - (q : ℤ)))
    (hW : wUV200 D hBC hrel hdC hdB hL = (-2 : ℤ) • gen (Type200.k m) 0 +
      ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2) :
    D.ec (bUV'200 D hBC hrel hdC hdB hL r θ η) =
      (-2 : ℤ) • gen (StrothTypeIndex.t200 m).k 0 +
        ((-2 : ℤ) + (q : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 1 +
          (-2 : ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
  obtain ⟨s, hs⟩ := hpe
  rw [wUV200] at hW
  have hW' : D.ec (bUV200 D hBC hrel hdC hdB hL) = (-2 : ℤ) • gen (StrothTypeIndex.t200 m).k 0 +
      ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (StrothTypeIndex.t200 m).k 2 := by
    exact hW
  rw [bUV'200, D.ec_mul, D.ec_mul, StrothTypeData.ec_conj_uv_t200, ec_zAdj200,
    PhiUV200_apply_tau, hW', gens_add, gens_add]
  refine gens_eq_of_mul (t0 := -(r : ℤ) + 2 * (η : ℤ) + 4 * (θ : ℤ))
    (t1 := s + (η : ℤ) + 2 * (θ : ℤ)) (t2 := (η : ℤ) + 2 * (θ : ℤ)) ?_ ?_ ?_
  · rw [show (StrothTypeIndex.t200 m).k 0 = m from k200_zero m]
    rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m from (two_mul_two_pow_int m).symm]
    rw [show (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) from (two_pow_succ_int hm).symm]
    ring
  · rw [show (StrothTypeIndex.t200 m).k 1 = m + 2 from k200_one m]
    have hp2 : (2 : ℤ) ^ (m + 2) = 8 * 2 ^ (m - 1) := by
      rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring
    rw [hp2]
    rw [show (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) from two_pow_succ_eq_four hm]
    linear_combination 4 * (2 : ℤ) ^ (m - 1) * hs
  · rw [show (StrothTypeIndex.t200 m).k 2 = m + 2 from k200_two m]
    have hp2 : (2 : ℤ) ^ (m + 2) = 8 * 2 ^ (m - 1) := by
      rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring
    rw [hp2]
    linear_combination (4 * (η : ℤ) + 8 * (θ : ℤ) + 2 * (r : ℤ)) * (two_pow_succ_int hm).symm


section CubicBasis

variable (D : StrothTypeData B (StrothTypeIndex.t200 m))

theorem m_t200 (m : ℕ) : (StrothTypeIndex.t200 m).m = m := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t200 m)) 0
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons] at h
  rw [show (StrothTypeIndex.t200 m).k 0 = m from k200_zero m] at h
  exact h.symm

theorem n_t200 (m : ℕ) : (StrothTypeIndex.t200 m).n = m + 2 := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t200 m)) 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons] at h
  rw [show (StrothTypeIndex.t200 m).k 1 = m + 2 from k200_one m] at h
  exact h.symm

structure CubicBasisEquiv (hBC : B ≤ C) (d : S) (hdC : d ∈ C) (k : Fin 3 → ℕ) where
  e : Additive C ≃+ Torus k
  e_d : e (Additive.ofMul ⟨d, hdC⟩) = gen k 0
  e_a : e (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k 1
  e_b : e (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k 2

noncomputable def addEquivOfSq200 (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (k : Fin 3 → ℕ) (hk0 : k 0 = m + 1) (hk1 : k 1 = m + 2) (hk2 : k 2 = m + 2) :
    CubicBasisEquiv D hBC d hdC k := by
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
    rw [m_t200]
  have hcC : (⟨D.c, hBC D.c.2⟩ : C) ^ (2 ^ m) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hcOrder]
  have hdN : dC ^ (2 ^ (m + 1)) = 1 := by
    rw [show 2 ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ'], pow_mul, hd2C, hcC]
  have haOrder : orderOf aC = 2 ^ (k 1) := by
    rw [show aC = Subgroup.inclusion hBC D.a from rfl]
    rw [orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.a]
    rw [D.orderOf_a, n_t200, hk1]
  have hbOrder : orderOf bC = 2 ^ (k 2) := by
    rw [show bC = Subgroup.inclusion hBC D.b from rfl]
    rw [orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.b]
    rw [D.orderOf_b, n_t200, hk2]
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
    have hBk : (StrothTypeIndex.t200 m).k 0 + (StrothTypeIndex.t200 m).k 1 +
        (StrothTypeIndex.t200 m).k 2 = m + (m + 2) + (m + 2) := by
      rw [show (StrothTypeIndex.t200 m).k 0 = m from k200_zero m,
        show (StrothTypeIndex.t200 m).k 1 = m + 2 from k200_one m,
        show (StrothTypeIndex.t200 m).k 2 = m + 2 from k200_two m]
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
def basisElems200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (hBC : B ≤ C) {d : S}
    (hdC : d ∈ C) : Fin 3 → C :=
  ![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩]

theorem eq_c_zpow_mul_a_b200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) {β : B} {i j l : ℤ}
    (h : D.ec β = i • gen (StrothTypeIndex.t200 m).k 0 +
      j • gen (StrothTypeIndex.t200 m).k 1 + l • gen (StrothTypeIndex.t200 m).k 2) :
    β = D.c ^ i * D.a ^ j * D.b ^ l := by
  apply D.ec_injective
  rw [h, D.ec_mul, D.ec_mul, D.ec_zpow, D.ec_zpow, D.ec_zpow, D.ec_c, D.ec_a, D.ec_b]

theorem E_e_inclusion200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S))
    {k : Fin 3 → ℕ} (E : CubicBasisEquiv D hBC d hdC k) (β : B) {i j l : ℤ}
    (hβ : D.ec β = i • gen (StrothTypeIndex.t200 m).k 0 +
      j • gen (StrothTypeIndex.t200 m).k 1 + l • gen (StrothTypeIndex.t200 m).k 2) :
    E.e (Additive.ofMul (⟨β, hBC β.2⟩ : C)) =
      (2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  have hβ' : β = D.c ^ i * D.a ^ j * D.b ^ l := eq_c_zpow_mul_a_b200 D hβ
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

end CocycleAdj200
section Images

variable (D : StrothTypeData B (StrothTypeIndex.t200 m))

theorem E_image_d200 (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) {k : Fin 3 → ℕ}
    (E : CubicBasisEquiv D hBC d hdC k) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {b : B} (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    {i j l : ℤ} (h : D.ec b = i • gen (StrothTypeIndex.t200 m).k 0 +
      j • gen (StrothTypeIndex.t200 m).k 1 + l • gen (StrothTypeIndex.t200 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨d, hdC⟩ : C))) =
      (1 + 2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  rw [hb, ofMul_mul, map_add, E.e_d]
  have hsub : Additive.ofMul ((Subgroup.inclusion hBC) b) = Additive.ofMul (⟨b, hBC b.2⟩ : C) :=
    congrArg Additive.ofMul rfl
  rw [hsub, E_e_inclusion200 D hBC hdC hd2 E b h]
  module

theorem E_image_a200 (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) {k : Fin 3 → ℕ}
    (E : CubicBasisEquiv D hBC d hdC k) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {i j l : ℤ} (h : D.ec (conjBy hgB D.a) = i • gen (StrothTypeIndex.t200 m).k 0 +
      j • gen (StrothTypeIndex.t200 m).k 1 + l • gen (StrothTypeIndex.t200 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨D.a, hBC D.a.2⟩ : C))) =
      (2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  have hsub : conjBy hgC (⟨D.a, hBC D.a.2⟩ : C) =
      (⟨conjBy hgB D.a, hBC (conjBy hgB D.a).2⟩ : C) := Subtype.ext rfl
  rw [hsub]
  exact E_e_inclusion200 D hBC hdC hd2 E _ h

theorem E_image_b200 (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) {k : Fin 3 → ℕ}
    (E : CubicBasisEquiv D hBC d hdC k) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {i j l : ℤ} (h : D.ec (conjBy hgB D.b) = i • gen (StrothTypeIndex.t200 m).k 0 +
      j • gen (StrothTypeIndex.t200 m).k 1 + l • gen (StrothTypeIndex.t200 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨D.b, hBC D.b.2⟩ : C))) =
      (2 * i) • gen k 0 + j • gen k 1 + l • gen k 2 := by
  have hsub : conjBy hgC (⟨D.b, hBC D.b.2⟩ : C) =
      (⟨conjBy hgB D.b, hBC (conjBy hgB D.b).2⟩ : C) := Subtype.ext rfl
  rw [hsub]
  exact E_e_inclusion200 D hBC hdC hd2 E _ h

end Images


section Assembly

variable (D : StrothTypeData B (StrothTypeIndex.t200 m))

theorem hasStrothTypeOver_t100_of_generator_images
    (hBC : B ≤ C) (_hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (_hdB : d ∉ B)
    (_hd2 : d * d = (D.c : S))
    (E : CubicBasisEquiv D hBC d hdC (Type100.k (m + 1)))
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems200 D hBC hdC j))) =
      (Type100.action (m + 1)).φuv (gen (Type100.k (m + 1)) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems200 D hBC hdC j))) =
      (Type100.action (m + 1)).φt (gen (Type100.k (m + 1)) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems200 D hBC hdC j))) =
      (Type100.action (m + 1)).φu (gen (Type100.k (m + 1)) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems200 D hBC hdC j))) =
      (Type100.action (m + 1)).φρ (gen (Type100.k (m + 1)) j)) :
    HasStrothTypeOver D C (StrothTypeIndex.t100 (m + 1)) := by
  let xd : C := ⟨d, hdC⟩
  let xa : C := ⟨D.a, hBC D.a.2⟩
  let xb : C := ⟨D.b, hBC D.b.2⟩
  have hxd : E.e (Additive.ofMul xd) = gen (Type100.k (m + 1)) 0 := E.e_d
  have hxa : E.e (Additive.ofMul xa) = gen (Type100.k (m + 1)) 1 := E.e_a
  have hxb : E.e (Additive.ofMul xb) = gen (Type100.k (m + 1)) 2 := E.e_b
  refine ⟨⟨E.e, D.uv, D.t, D.u, D.ρ, D.uv_sq, D.t_sq, D.uv_comm_t, D.rho_cube, D.u_sq,
    D.u_rho, D.uv_rho, D.t_rho, D.uv_comm_u, D.t_u, hL D.uv_mem_L, hL D.t_mem_L,
    hL D.u_mem_L, hL D.ρ_mem_L,
    conj_eq_of_generator_images (hL D.uv_mem_L) E.e
      (Type100.action (m + 1)).φuv hxd hxa hxb (huv 0) (huv 1) (huv 2),
    conj_eq_of_generator_images (hL D.t_mem_L) E.e
      (Type100.action (m + 1)).φt hxd hxa hxb (ht 0) (ht 1) (ht 2),
    conj_eq_of_generator_images (hL D.u_mem_L) E.e
      (Type100.action (m + 1)).φu hxd hxa hxb (hu 0) (hu 1) (hu 2),
    conj_eq_of_generator_images (hL D.ρ_mem_L) E.e
      (Type100.action (m + 1)).φρ hxd hxa hxb (hρ 0) (hρ 1) (hρ 2)⟩, rfl, rfl, rfl, rfl⟩

theorem hasStrothType_t100_of_generator_images
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S))
    (E : CubicBasisEquiv D hBC d hdC (Type100.k (m + 1)))
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems200 D hBC hdC j))) =
      (Type100.action (m + 1)).φuv (gen (Type100.k (m + 1)) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems200 D hBC hdC j))) =
      (Type100.action (m + 1)).φt (gen (Type100.k (m + 1)) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems200 D hBC hdC j))) =
      (Type100.action (m + 1)).φu (gen (Type100.k (m + 1)) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems200 D hBC hdC j))) =
      (Type100.action (m + 1)).φρ (gen (Type100.k (m + 1)) j)) :
    HasStrothType C (StrothTypeIndex.t100 (m + 1)) :=
  (hasStrothTypeOver_t100_of_generator_images D hBC hrel hL hdC hdB hd2 E huv ht hu hρ)
    |>.hasStrothType

theorem hasStrothTypeOver_t110_of_generator_images
    (hBC : B ≤ C) (_hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (_hdB : d ∉ B)
    (_hd2 : d * d = (D.c : S))
    (E : CubicBasisEquiv D hBC d hdC (Type110.k (m - 1)))
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems200 D hBC hdC j))) =
      (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems200 D hBC hdC j))) =
      (Type110.action (m - 1)).φt (gen (Type110.k (m - 1)) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems200 D hBC hdC j))) =
      (Type110.action (m - 1)).φu (gen (Type110.k (m - 1)) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems200 D hBC hdC j))) =
      (Type110.action (m - 1)).φρ (gen (Type110.k (m - 1)) j)) :
    HasStrothTypeOver D C (StrothTypeIndex.t110 (m - 1)) := by
  let xd : C := ⟨d, hdC⟩
  let xa : C := ⟨D.a, hBC D.a.2⟩
  let xb : C := ⟨D.b, hBC D.b.2⟩
  have hxd : E.e (Additive.ofMul xd) = gen (Type110.k (m - 1)) 0 := E.e_d
  have hxa : E.e (Additive.ofMul xa) = gen (Type110.k (m - 1)) 1 := E.e_a
  have hxb : E.e (Additive.ofMul xb) = gen (Type110.k (m - 1)) 2 := E.e_b
  refine ⟨⟨E.e, D.uv, D.t, D.u, D.ρ, D.uv_sq, D.t_sq, D.uv_comm_t, D.rho_cube, D.u_sq,
    D.u_rho, D.uv_rho, D.t_rho, D.uv_comm_u, D.t_u, hL D.uv_mem_L, hL D.t_mem_L,
    hL D.u_mem_L, hL D.ρ_mem_L,
    conj_eq_of_generator_images (hL D.uv_mem_L) E.e
      (Type110.action (m - 1)).φuv hxd hxa hxb (huv 0) (huv 1) (huv 2),
    conj_eq_of_generator_images (hL D.t_mem_L) E.e
      (Type110.action (m - 1)).φt hxd hxa hxb (ht 0) (ht 1) (ht 2),
    conj_eq_of_generator_images (hL D.u_mem_L) E.e
      (Type110.action (m - 1)).φu hxd hxa hxb (hu 0) (hu 1) (hu 2),
    conj_eq_of_generator_images (hL D.ρ_mem_L) E.e
      (Type110.action (m - 1)).φρ hxd hxa hxb (hρ 0) (hρ 1) (hρ 2)⟩, rfl, rfl, rfl, rfl⟩

theorem hasStrothType_t110_of_generator_images
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S))
    (E : CubicBasisEquiv D hBC d hdC (Type110.k (m - 1)))
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems200 D hBC hdC j))) =
      (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems200 D hBC hdC j))) =
      (Type110.action (m - 1)).φt (gen (Type110.k (m - 1)) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems200 D hBC hdC j))) =
      (Type110.action (m - 1)).φu (gen (Type110.k (m - 1)) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems200 D hBC hdC j))) =
      (Type110.action (m - 1)).φρ (gen (Type110.k (m - 1)) j)) :
    HasStrothType C (StrothTypeIndex.t110 (m - 1)) :=
  (hasStrothTypeOver_t110_of_generator_images D hBC hrel hL hdC hdB hd2 E huv ht hu hρ)
    |>.hasStrothType

end Assembly

theorem Type110_uv_gen_two (hm : 1 ≤ m) :
    (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) 2) =
      (2 : ℤ) • gen (Type110.k (m - 1)) 0 + (2 : ℤ) • gen (Type110.k (m - 1)) 1 +
        (1 : ℤ) • gen (Type110.k (m - 1)) 2 := by
  rw [show (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) 2) =
      (2 - 16 * 2 ^ (m - 1) : ℤ) • gen (Type110.k (m - 1)) 0 +
        (2 - 8 * 2 ^ (m - 1) : ℤ) • gen (Type110.k (m - 1)) 1 +
          (1 - 8 * 2 ^ (m - 1) : ℤ) • gen (Type110.k (m - 1)) 2 from
    Type110.uv_b (m - 1)]
  refine gens_eq_of_mul (t0 := -4) (t1 := -1) (t2 := -1) ?_ ?_ ?_
  · rw [show (Type110.k (m - 1)) 0 = m + 1 from by simp [Type110.k]; omega]
    rw [show (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) from two_pow_succ_eq_four hm]
    ring
  · rw [show (Type110.k (m - 1)) 1 = m + 2 from by simp [Type110.k]; omega]
    rw [show (2 : ℤ) ^ (m + 2) = 8 * 2 ^ (m - 1) from by
      rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring]
    ring
  · rw [show (Type110.k (m - 1)) 2 = m + 2 from by simp [Type110.k]; omega]
    rw [show (2 : ℤ) ^ (m + 2) = 8 * 2 ^ (m - 1) from by
      rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring]
    ring

end Adjust


section Final

theorem hasStrothTypeOver_t100_or_t110_of_noInvolutionsCentralizing
    {B C S' : Subgroup S} {m : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t200 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothTypeOver D C (StrothTypeIndex.t100 (m + 1)) ∨
    HasStrothTypeOver D C (StrothTypeIndex.t110 (m - 1)) := by
  classical
  have hm : 1 ≤ m := one_le_of_noInvolutionsCentralizing_t200_of_data D hBC hC hrel hL hH hcS hne
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_of_data_t200 D hBC hC hrel hL hH hcS hne
  obtain ⟨ε, δ, hε1, hδ1, hX⟩ :=
    form_xU200 D hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨α, q, hα1, hq1, hY⟩ :=
    form_yT200 D hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨θ, η, hη1, hθ1, hZ⟩ :=
    form_zR200 D hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨p, r, hp1, hr1, hW⟩ :=
    form_wUV200 D hBC hC hrel hdC hdB hd2 hL hm
  have hεp : ε = (p + r) % 2 :=
    bit_eps_200 (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL) (hm := hm) (ε := ε) (δ := δ) (p := p) (r := r) hε1 hδ1 hp1 hr1 hX hW
  have hαq : α = r ∧ q = (p + r) % 2 :=
    bit_alpha_q_200 (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL) (hm := hm) (ε := ε) (δ := δ) (α := α) (q := q) (p := p) (r := r)
      hα1 hq1 hp1 hr1 hY hZ hW
  have hδη : δ = η :=
    bit_delta_200 (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB)
      (hL := hL) (hm := hm) (ε := ε) (δ := δ) (p := p) (r := r) (η := η) (θ := θ)
      hε1 hδ1 hη1 hθ1 hX hZ
  have hqε : q = ε := by rw [hαq.2, hεp]
  have hpe : Even ((p : ℤ) - (r : ℤ) - (q : ℤ)) := by
    rw [hαq.2]
    interval_cases p <;> interval_cases r <;> norm_num
  let d' : S := dAdj200 D d r θ η
  have hd'C : d' ∈ C := dAdj200_mem D hBC hdC r θ η
  have hd'B : d' ∉ B := dAdj200_notMem D hm hdB r θ η
  have hd'2 : d' * d' = (D.c : S) :=
    dAdj200_sq D hBC hC hrel hdC hd2 hm r θ η
  rcases (by omega : q = 0 ∨ q = 1) with hq0 | hq1'
  ·
    subst hq0
    have hε0 : ε = 0 := by omega
    left
    let E : CubicBasisEquiv D hBC d' hd'C (Type100.k (m + 1)) :=
      addEquivOfSq200 D hBC hC hrel hd'C hd'B hd'2 (Type100.k (m + 1))
        (by simp [Type100.k]) (by simp [Type100.k]) (by simp [Type100.k])
    refine hasStrothTypeOver_t100_of_generator_images D hBC hrel hL hd'C hd'B hd'2 E ?_ ?_ ?_ ?_
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type100.action (m + 1)).φuv (gen (Type100.k (m + 1)) 0)
        rw [E_image_d200 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (conj_dAdj200 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.uv) (hgC := hL D.uv_mem_L) (hgB := D.uv_mem) (hm := hm)
            (hb := conj_eq_bUV200 D hBC hrel hdC hdB hL))
          (ec_bUV'200 D hBC hrel hdC hdB hL hm r θ η p 0 hpe hW)]
        rw [show (Type100.action (m + 1)).φuv (gen (Type100.k (m + 1)) 0) =
            (-3 : ℤ) • gen (Type100.k (m + 1)) 0 + (-2 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (-2 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.uv_c (m + 1)]
        simp only [Nat.cast_zero, zero_mul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type100.action (m + 1)).φuv (gen (Type100.k (m + 1)) 1)
        rw [E_image_a200 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (by rw [StrothTypeData.ec_conj_uv_t200, D.ec_a]
              exact PhiUV200_a m)]
        rw [show (Type100.action (m + 1)).φuv (gen (Type100.k (m + 1)) 1) =
            (2 : ℤ) • gen (Type100.k (m + 1)) 0 + (1 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (2 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.uv_a (m + 1)]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type100.action (m + 1)).φuv (gen (Type100.k (m + 1)) 2)
        rw [E_image_b200 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (by rw [StrothTypeData.ec_conj_uv_t200, D.ec_b]
              exact PhiUV200_b m)]
        rw [show (Type100.action (m + 1)).φuv (gen (Type100.k (m + 1)) 2) =
            (2 : ℤ) • gen (Type100.k (m + 1)) 0 + (2 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (1 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.uv_b (m + 1)]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type100.action (m + 1)).φt (gen (Type100.k (m + 1)) 0)
        rw [E_image_d200 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (conj_dAdj200 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.t) (hgC := hL D.t_mem_L) (hgB := D.t_mem) (hm := hm)
            (hb := conj_eq_bT200 D hBC hrel hdC hdB hL))
          (ec_bT'200 D hBC hrel hdC hdB hL hm r θ η α 0 hαq.1 hY)]
        rw [show (Type100.action (m + 1)).φt (gen (Type100.k (m + 1)) 0) =
            (1 : ℤ) • gen (Type100.k (m + 1)) 0 + (2 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (0 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.t_c (m + 1)]
        simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type100.action (m + 1)).φt (gen (Type100.k (m + 1)) 1)
        rw [E_image_a200 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (by rw [StrothTypeData.ec_conj_t_t200, D.ec_a]
              exact PhiT200_a m)]
        rw [show (Type100.action (m + 1)).φt (gen (Type100.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type100.k (m + 1)) 0 + (-1 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (0 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.t_a (m + 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type100.action (m + 1)).φt (gen (Type100.k (m + 1)) 2)
        rw [E_image_b200 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (by rw [StrothTypeData.ec_conj_t_t200, D.ec_b]
              exact PhiT200_b m)]
        rw [show (Type100.action (m + 1)).φt (gen (Type100.k (m + 1)) 2) =
            (-2 : ℤ) • gen (Type100.k (m + 1)) 0 + (-2 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (-1 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.t_b (m + 1)]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type100.action (m + 1)).φu (gen (Type100.k (m + 1)) 0)
        rw [E_image_d200 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (conj_dAdj200 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.u) (hgC := hL D.u_mem_L) (hgB := D.u_mem) (hm := hm)
            (hb := conj_eq_bU200 D hBC hrel hdC hdB hL))
          (ec_bU'200 D hBC hrel hdC hdB hL hm r θ η ε δ hδη hX)]
        rw [show (Type100.action (m + 1)).φu (gen (Type100.k (m + 1)) 0) =
            (1 : ℤ) • gen (Type100.k (m + 1)) 0 + (0 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (0 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.u_c (m + 1)]
        simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, hε0]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type100.action (m + 1)).φu (gen (Type100.k (m + 1)) 1)
        rw [E_image_a200 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (by rw [StrothTypeData.ec_conj_u_t200, D.ec_a]
              exact PhiU200_a m)]
        rw [show (Type100.action (m + 1)).φu (gen (Type100.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type100.k (m + 1)) 0 + (0 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (1 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.u_a (m + 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type100.action (m + 1)).φu (gen (Type100.k (m + 1)) 2)
        rw [E_image_b200 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (by rw [StrothTypeData.ec_conj_u_t200, D.ec_b]
              exact PhiU200_b m)]
        rw [show (Type100.action (m + 1)).φu (gen (Type100.k (m + 1)) 2) =
            (0 : ℤ) • gen (Type100.k (m + 1)) 0 + (1 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (0 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.u_b (m + 1)]
        simp only [zero_smul, add_zero]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type100.action (m + 1)).φρ (gen (Type100.k (m + 1)) 0)
        rw [E_image_d200 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (conj_dAdj200 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.ρ) (hgC := hL D.ρ_mem_L) (hgB := D.ρ_mem) (hm := hm)
            (hb := conj_eq_bR200 D hBC hrel hdC hdB hL))
          (ec_bR'200 D hBC hrel hdC hdB hL hm r θ η hZ)]
        rw [show (Type100.action (m + 1)).φρ (gen (Type100.k (m + 1)) 0) =
            (1 : ℤ) • gen (Type100.k (m + 1)) 0 + (0 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (0 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.rho_c (m + 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type100.action (m + 1)).φρ (gen (Type100.k (m + 1)) 1)
        rw [E_image_a200 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (by rw [StrothTypeData.ec_conj_ρ_t200, D.ec_a]
              exact PhiR200_a m)]
        rw [show (Type100.action (m + 1)).φρ (gen (Type100.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type100.k (m + 1)) 0 + (0 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (1 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.rho_a (m + 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type100.action (m + 1)).φρ (gen (Type100.k (m + 1)) 2)
        rw [E_image_b200 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (by rw [StrothTypeData.ec_conj_ρ_t200, D.ec_b]
              exact PhiR200_b m)]
        rw [show (Type100.action (m + 1)).φρ (gen (Type100.k (m + 1)) 2) =
            (-2 : ℤ) • gen (Type100.k (m + 1)) 0 + (-1 : ℤ) • gen (Type100.k (m + 1)) 1 +
              (-1 : ℤ) • gen (Type100.k (m + 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type100.rho_b (m + 1)]
        module
  ·
    subst hq1'
    have hε1' : ε = 1 := by omega
    right
    let E : CubicBasisEquiv D hBC d' hd'C (Type110.k (m - 1)) :=
      addEquivOfSq200 D hBC hC hrel hd'C hd'B hd'2 (Type110.k (m - 1))
        (by simp [Type110.k]; omega) (by simp [Type110.k]; omega) (by simp [Type110.k]; omega)
    refine hasStrothTypeOver_t110_of_generator_images D hBC hrel hL hd'C hd'B hd'2 E ?_ ?_ ?_ ?_
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) 0)
        rw [E_image_d200 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (conj_dAdj200 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.uv) (hgC := hL D.uv_mem_L) (hgB := D.uv_mem) (hm := hm)
            (hb := conj_eq_bUV200 D hBC hrel hdC hdB hL))
          (ec_bUV'200 D hBC hrel hdC hdB hL hm r θ η p 1 hpe hW)]
        rw [show (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) 0) =
            (-3 : ℤ) • gen (Type110.k (m - 1)) 0 +
              ((4 : ℤ) * 2 ^ (m - 1) - 2) • gen (Type110.k (m - 1)) 1 +
              (-2 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b] using Type110.uv_c (m - 1)]
        simp only [Nat.cast_one, one_mul]
        rw [show (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) from two_pow_succ_eq_four hm]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) 1)
        rw [E_image_a200 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (by rw [StrothTypeData.ec_conj_uv_t200, D.ec_a]
              exact PhiUV200_a m)]
        rw [show (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) 1) =
            (2 : ℤ) • gen (Type110.k (m - 1)) 0 + (1 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (2 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type110.uv_a (m - 1)]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) 2)
        rw [E_image_b200 D hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
          (by rw [StrothTypeData.ec_conj_uv_t200, D.ec_b]
              exact PhiUV200_b m)]
        rw [show (Type110.action (m - 1)).φuv (gen (Type110.k (m - 1)) 2) =
            (2 : ℤ) • gen (Type110.k (m - 1)) 0 + (2 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (1 : ℤ) • gen (Type110.k (m - 1)) 2 from Type110_uv_gen_two hm]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type110.action (m - 1)).φt (gen (Type110.k (m - 1)) 0)
        rw [E_image_d200 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (conj_dAdj200 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.t) (hgC := hL D.t_mem_L) (hgB := D.t_mem) (hm := hm)
            (hb := conj_eq_bT200 D hBC hrel hdC hdB hL))
          (ec_bT'200 D hBC hrel hdC hdB hL hm r θ η α 1 hαq.1 hY)]
        rw [show (Type110.action (m - 1)).φt (gen (Type110.k (m - 1)) 0) =
            (1 : ℤ) • gen (Type110.k (m - 1)) 0 + (2 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (2 ^ (m + 1) : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa [Torus.c, Torus.a, Torus.b, two_pow_succ_eq_four hm] using Type110.t_c (m - 1)]
        simp only [Nat.cast_one, one_mul]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type110.action (m - 1)).φt (gen (Type110.k (m - 1)) 1)
        rw [E_image_a200 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (by rw [StrothTypeData.ec_conj_t_t200, D.ec_a]
              exact PhiT200_a m)]
        rw [show (Type110.action (m - 1)).φt (gen (Type110.k (m - 1)) 1) =
            (0 : ℤ) • gen (Type110.k (m - 1)) 0 + (-1 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (0 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type110.t_a (m - 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type110.action (m - 1)).φt (gen (Type110.k (m - 1)) 2)
        rw [E_image_b200 D hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
          (by rw [StrothTypeData.ec_conj_t_t200, D.ec_b]
              exact PhiT200_b m)]
        rw [show (Type110.action (m - 1)).φt (gen (Type110.k (m - 1)) 2) =
            (-2 : ℤ) • gen (Type110.k (m - 1)) 0 + (-2 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (-1 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type110.t_b (m - 1)]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type110.action (m - 1)).φu (gen (Type110.k (m - 1)) 0)
        rw [E_image_d200 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (conj_dAdj200 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.u) (hgC := hL D.u_mem_L) (hgB := D.u_mem) (hm := hm)
            (hb := conj_eq_bU200 D hBC hrel hdC hdB hL))
          (ec_bU'200 D hBC hrel hdC hdB hL hm r θ η ε δ hδη hX)]
        rw [show (Type110.action (m - 1)).φu (gen (Type110.k (m - 1)) 0) =
            ((1 : ℤ) + 2 ^ m) • gen (Type110.k (m - 1)) 0 + (0 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (0 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, two_pow_succ_int hm, add_comm, zero_smul, add_zero, zero_add] using Type110.u_c (m - 1)]
        simp only [Nat.cast_one, one_mul, zero_smul, add_zero,
          hε1']
        rw [two_pow_succ_int hm]
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type110.action (m - 1)).φu (gen (Type110.k (m - 1)) 1)
        rw [E_image_a200 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (by rw [StrothTypeData.ec_conj_u_t200, D.ec_a]
              exact PhiU200_a m)]
        rw [show (Type110.action (m - 1)).φu (gen (Type110.k (m - 1)) 1) =
            (0 : ℤ) • gen (Type110.k (m - 1)) 0 + (0 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (1 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type110.u_a (m - 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type110.action (m - 1)).φu (gen (Type110.k (m - 1)) 2)
        rw [E_image_b200 D hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
          (by rw [StrothTypeData.ec_conj_u_t200, D.ec_b]
              exact PhiU200_b m)]
        rw [show (Type110.action (m - 1)).φu (gen (Type110.k (m - 1)) 2) =
            (0 : ℤ) • gen (Type110.k (m - 1)) 0 + (1 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (0 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type110.u_b (m - 1)]
        simp only [zero_smul, add_zero]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type110.action (m - 1)).φρ (gen (Type110.k (m - 1)) 0)
        rw [E_image_d200 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (conj_dAdj200 (D := D) (hBC := hBC) (d := d) (hdC := hdC) (r := r) (θ := θ) (η := η)
            (g := D.ρ) (hgC := hL D.ρ_mem_L) (hgB := D.ρ_mem) (hm := hm)
            (hb := conj_eq_bR200 D hBC hrel hdC hdB hL))
          (ec_bR'200 D hBC hrel hdC hdB hL hm r θ η hZ)]
        rw [show (Type110.action (m - 1)).φρ (gen (Type110.k (m - 1)) 0) =
            (1 : ℤ) • gen (Type110.k (m - 1)) 0 + (0 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (0 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type110.rho_c (m - 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type110.action (m - 1)).φρ (gen (Type110.k (m - 1)) 1)
        rw [E_image_a200 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (by rw [StrothTypeData.ec_conj_ρ_t200, D.ec_a]
              exact PhiR200_a m)]
        rw [show (Type110.action (m - 1)).φρ (gen (Type110.k (m - 1)) 1) =
            (0 : ℤ) • gen (Type110.k (m - 1)) 0 + (0 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (1 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type110.rho_a (m - 1)]
        simp only [zero_smul, add_zero]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type110.action (m - 1)).φρ (gen (Type110.k (m - 1)) 2)
        rw [E_image_b200 D hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
          (by rw [StrothTypeData.ec_conj_ρ_t200, D.ec_b]
              exact PhiR200_b m)]
        rw [show (Type110.action (m - 1)).φρ (gen (Type110.k (m - 1)) 2) =
            (-2 : ℤ) • gen (Type110.k (m - 1)) 0 + (-1 : ℤ) • gen (Type110.k (m - 1)) 1 +
              (-1 : ℤ) • gen (Type110.k (m - 1)) 2 from by
          simpa only [Torus.c, Torus.a, Torus.b, zero_smul, add_zero, zero_add] using Type110.rho_b (m - 1)]
        module

theorem hasStrothType_t100_or_t110_of_noInvolutionsCentralizing
    [Finite S] {B C S' : Subgroup S} {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t200 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothType C (StrothTypeIndex.t100 (m + 1)) ∨
    HasStrothType C (StrothTypeIndex.t110 (m - 1)) :=
  (hasStrothTypeOver_t100_or_t110_of_noInvolutionsCentralizing hB.data hBC hC hrel hL hH hcS hne)
    |>.imp (·.hasStrothType) (·.hasStrothType)

end Final

end CFSG.CGT.Stroth77

end
