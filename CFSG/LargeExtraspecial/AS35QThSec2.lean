module

public import CFSG.LargeExtraspecial.AS35QThSec
public import CFSG.LargeExtraspecial.AS35QThGU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem tr2_frob (c : K) : tr2 (frob c) = tr2 c :=
  toK_injective (by rw [toK_tr2, toK_tr2, frob_frob, add_comm])

structure SecData (S : Setting G) where
  ζ : S.Qt →ₗ[ZMod 2] S.Qt
  l : (Fin 3 → K) → S.Qt
  hl : HermCoords S.q ζ l
  Zh : G
  hZhM : Zh ∈ S.M
  hZh : ∀ v, S.rhoL hZhM v = ζ v

namespace SecData

variable (D : SecData S)

theorem zeta_sq (v : S.Qt) : D.ζ (D.ζ v) + D.ζ v + v = 0 := by
  obtain ⟨x, rfl⟩ := D.hl.bij.2 v
  rw [← D.hl.omega, ← D.hl.omega, ← D.hl.add, ← D.hl.add, smul_smul, omega_mul_omega,
    ← add_smul, add_comm (frob ω) ω, omega_add_frob, one_smul,
    show x + x = 0 from funext fun i => add_self_K _, D.hl.l_zero]

theorem exists_lift (a : Fin 3 → K) :
    ∃ x : G, x ∈ S.QG ∧ S.cl x = D.l a ∧ normZ D.Zh x = 1 := by
  obtain ⟨x, hx, hcl⟩ := S.exists_cl (D.l a)
  rcases normZ_eq_one_or_z D.hZhM D.hZh D.zeta_sq hx with h | h
  · exact ⟨x, hx, hcl, h⟩
  · refine ⟨x * S.z, S.QG.mul_mem hx S.z_mem_QG, by rw [S.cl_mul_z hx, hcl], ?_⟩
    have := normZ_mul_zp D.hZhM hx 1
    rw [zp_one] at this
    rw [this, h, S.z_mul_z]

@[expose] noncomputable def sHat (a : Fin 3 → K) : G := (D.exists_lift a).choose

theorem sHat_mem (a : Fin 3 → K) : D.sHat a ∈ S.QG := (D.exists_lift a).choose_spec.1

theorem cl_sHat (a : Fin 3 → K) : S.cl (D.sHat a) = D.l a := (D.exists_lift a).choose_spec.2.1

theorem normZ_sHat (a : Fin 3 → K) : normZ D.Zh (D.sHat a) = 1 :=
  (D.exists_lift a).choose_spec.2.2

theorem sHat_unique {x : G} {a : Fin 3 → K} (hx : x ∈ S.QG) (hcl : S.cl x = D.l a)
    (hn : normZ D.Zh x = 1) : x = D.sHat a := by
  rcases (S.cl_eq_cl_iff (D.sHat_mem a) hx).mp (by rw [hcl, D.cl_sHat]) with h | h
  · exact h
  · exfalso
    have h1 := normZ_mul_zp D.hZhM (D.sHat_mem a) 1
    rw [zp_one, ← h, hn, D.normZ_sHat, one_mul] at h1
    exact S.z_ne_one h1.symm

theorem sHat_mul (a b : Fin 3 → K) :
    D.sHat a * D.sHat b = zp S (beta a b) * D.sHat (a + b) := by
  have ha := D.sHat_mem a
  have hb := D.sHat_mem b
  have hab := S.QG.mul_mem ha hb
  set e := polar S.q (S.cl (D.sHat b)) (S.cl (D.sHat a)) +
    polar S.q (S.cl (D.sHat b)) (D.ζ (S.cl (D.sHat a))) with he
  have hN : normZ D.Zh (D.sHat a * D.sHat b) = zp S e := by
    rw [normZ_mul D.hZhM D.hZh D.zeta_sq ha hb, D.normZ_sHat, D.normZ_sHat, one_mul, one_mul]
  have hEq : D.sHat a * D.sHat b * zp S e = D.sHat (a + b) := by
    refine D.sHat_unique (S.QG.mul_mem hab (zp_mem_QG S e)) ?_ ?_
    · rw [S.cl_mul hab (zp_mem_QG S e), cl_zp, add_zero, S.cl_mul ha hb, D.cl_sHat, D.cl_sHat,
        D.hl.add]
    · rw [normZ_mul_zp D.hZhM hab, hN, zp_mul_self]
  have heβ : e = beta a b := by
    rw [he, D.cl_sHat, D.cl_sHat, ← D.hl.omega, D.hl.polar, D.hl.polar, ← tr2_add,
      herm_smul_right, beta]
    have h1 : herm frob b a + ω * herm frob b a = frob ω * herm frob b a := by
      rw [frob_omega]; ring
    rw [h1, herm_conj frob frob_frob a b, ← map_mul, tr2_frob]
  rw [← hEq, ← heβ]
  have hc := zp_comm S e (S.QG_le_M hab)
  calc D.sHat a * D.sHat b = D.sHat a * D.sHat b * (zp S e * zp S e) := by
        rw [zp_mul_self, mul_one]
    _ = (zp S e * (D.sHat a * D.sHat b)) * zp S e := by rw [hc]; group
    _ = zp S e * (D.sHat a * D.sHat b * zp S e) := by group

theorem conj_sHat {k : G} (hkM : k ∈ S.M) (hkZ : k * D.Zh = D.Zh * k)
    {f : (Fin 3 → K) → (Fin 3 → K)} (hf : ∀ x, S.rhoL hkM (D.l x) = D.l (f x))
    (a : Fin 3 → K) : k * D.sHat a * k⁻¹ = D.sHat (f a) := by
  have ha := D.sHat_mem a
  refine D.sHat_unique (S.conj_mem_QG hkM ha) ?_ ?_
  · rw [← S.rhoL_cl hkM ha, D.cl_sHat, hf]
  · have hconj : ∀ y : G, D.Zh * (k * y * k⁻¹) * D.Zh⁻¹ = k * (D.Zh * y * D.Zh⁻¹) * k⁻¹ := by
      intro y
      have hinv : k⁻¹ * D.Zh⁻¹ = D.Zh⁻¹ * k⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hkZ]
      calc D.Zh * (k * y * k⁻¹) * D.Zh⁻¹ = (D.Zh * k) * y * (k⁻¹ * D.Zh⁻¹) := by group
        _ = (k * D.Zh) * y * (D.Zh⁻¹ * k⁻¹) := by rw [← hkZ, hinv]
        _ = k * (D.Zh * y * D.Zh⁻¹) * k⁻¹ := by group
    have h2 : D.Zh * D.Zh * (k * D.sHat a * k⁻¹) * (D.Zh * D.Zh)⁻¹ =
        k * (D.Zh * D.Zh * D.sHat a * (D.Zh * D.Zh)⁻¹) * k⁻¹ := by
      rw [show D.Zh * D.Zh * (k * D.sHat a * k⁻¹) * (D.Zh * D.Zh)⁻¹ =
        D.Zh * (D.Zh * (k * D.sHat a * k⁻¹) * D.Zh⁻¹) * D.Zh⁻¹ by group, hconj, hconj]
      group
    rw [normZ, hconj, h2]
    have h3 : k * D.sHat a * k⁻¹ * (k * (D.Zh * D.sHat a * D.Zh⁻¹) * k⁻¹) *
        (k * (D.Zh * D.Zh * D.sHat a * (D.Zh * D.Zh)⁻¹) * k⁻¹) =
        k * normZ D.Zh (D.sHat a) * k⁻¹ := by
      rw [normZ]; group
    rw [h3, D.normZ_sHat, mul_one, mul_inv_cancel]

end SecData

end CFSG.LargeExtraspecial.AS35QTh
