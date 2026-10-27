module

public import CFSG.LargeExtraspecial.AS35QThSec2
public import CFSG.LargeExtraspecial.AS35QThGamBij

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

structure ThData (S : Setting G) extends SecData S where
  κ : GU3 →* G
  hκM : ∀ A, κ A ∈ S.M
  hκ : ∀ A x, S.rhoL (hκM A) (l x) = l (gv A x)
  hκZ : ∀ A, κ A * Zh = Zh * κ A
  hall : ∀ m (hm : m ∈ S.M), ∃ A, ∀ v, S.rhoL hm v = S.rhoL (hκM A) v

namespace ThData

variable (D : ThData S)

theorem phi_mem (x : Model) : zp S x.1 * D.sHat x.2.1 * D.κ x.2.2 ∈ S.M :=
  S.M.mul_mem (S.M.mul_mem (zp_mem_M S x.1) (S.QG_le_M (D.sHat_mem x.2.1))) (D.hκM x.2.2)

@[expose] noncomputable def phi (x : Model) : S.M :=
  ⟨zp S x.1 * D.sHat x.2.1 * D.κ x.2.2, D.phi_mem x⟩

theorem phi_mul (x y : Model) : D.phi (mulM x y) = D.phi x * D.phi y := by
  obtain ⟨ε, a, A⟩ := x
  obtain ⟨ε', a', A'⟩ := y
  apply Subtype.ext
  change zp S (ε + ε' + beta a (gv A a')) * D.sHat (a + gv A a') * D.κ (A * A') =
    zp S ε * D.sHat a * D.κ A * (zp S ε' * D.sHat a' * D.κ A')
  have hconj := D.conj_sHat (D.hκM A) (D.hκZ A) (D.hκ A) a'
  have hc : D.κ A * zp S ε' = zp S ε' * D.κ A := (zp_comm S ε' (D.hκM A)).symm
  have hc2 : D.sHat a * zp S ε' = zp S ε' * D.sHat a :=
    (zp_comm S ε' (S.QG_le_M (D.sHat_mem a))).symm
  calc zp S (ε + ε' + beta a (gv A a')) * D.sHat (a + gv A a') * D.κ (A * A') =
      zp S ε * zp S ε' * (zp S (beta a (gv A a')) * D.sHat (a + gv A a')) *
        (D.κ A * D.κ A') := by rw [zp_add, zp_add, map_mul]; group
    _ = zp S ε * zp S ε' * (D.sHat a * D.sHat (gv A a')) * (D.κ A * D.κ A') := by
        rw [D.sHat_mul]
    _ = zp S ε * zp S ε' * (D.sHat a * (D.κ A * D.sHat a' * (D.κ A)⁻¹)) *
        (D.κ A * D.κ A') := by rw [hconj]
    _ = zp S ε * (zp S ε' * D.sHat a) * D.κ A * D.sHat a' * D.κ A' := by group
    _ = zp S ε * (D.sHat a * zp S ε') * D.κ A * D.sHat a' * D.κ A' := by rw [hc2]
    _ = zp S ε * D.sHat a * (zp S ε' * D.κ A) * D.sHat a' * D.κ A' := by group
    _ = zp S ε * D.sHat a * D.κ A * (zp S ε' * D.sHat a' * D.κ A') := by rw [← hc]; group

theorem rho_phi (x : Model) :
    S.ρ (D.phi x) = S.ρ ⟨D.κ x.2.2, D.hκM x.2.2⟩ := by
  have hQ : zp S x.1 * D.sHat x.2.1 ∈ S.QG := S.QG.mul_mem (zp_mem_QG S x.1) (D.sHat_mem x.2.1)
  have e : D.phi x = ⟨zp S x.1 * D.sHat x.2.1, S.QG_le_M hQ⟩ * ⟨D.κ x.2.2, D.hκM x.2.2⟩ := rfl
  rw [e, map_mul, (S.ρ_eq_one_iff _).mpr hQ, one_mul]

theorem kappa_injective {A A' : GU3}
    (h : S.ρ ⟨D.κ A, D.hκM A⟩ = S.ρ ⟨D.κ A', D.hκM A'⟩) : A = A' := by
  refine gm_injective (Matrix.ext_of_mulVec_single fun j => ?_)
  apply D.hl.bij.1
  have h1 := D.hκ A (Pi.single j 1)
  have h2 := D.hκ A' (Pi.single j 1)
  have e : S.rhoL (D.hκM A) = S.rhoL (D.hκM A') := by
    simp only [Setting.rhoL]
    rw [h]
  rw [e] at h1
  rw [← h1, h2]

theorem phi_injective : Function.Injective D.phi := by
  rintro ⟨ε, a, A⟩ ⟨ε', a', A'⟩ h
  have hA : A = A' := D.kappa_injective (by
    have := congrArg S.ρ h
    rwa [D.rho_phi, D.rho_phi] at this)
  subst hA
  have h1 : zp S ε * D.sHat a = zp S ε' * D.sHat a' :=
    mul_right_cancel (congrArg Subtype.val h)
  have hcl : D.l a = D.l a' := by
    have := congrArg S.cl h1
    rwa [S.cl_mul (zp_mem_QG S ε) (D.sHat_mem a), S.cl_mul (zp_mem_QG S ε') (D.sHat_mem a'),
      cl_zp, cl_zp, zero_add, zero_add, D.cl_sHat, D.cl_sHat] at this
  have ha : a = a' := D.hl.bij.1 hcl
  subst ha
  have hε : ε = ε' := zp_injective S (mul_right_cancel h1)
  rw [hε]

theorem phi_surjective : Function.Surjective D.phi := by
  rintro ⟨m, hm⟩
  obtain ⟨A, hA⟩ := D.hall m hm
  have hyM : m * (D.κ A)⁻¹ ∈ S.M := S.M.mul_mem hm (S.M.inv_mem (D.hκM A))
  have hyQ : m * (D.κ A)⁻¹ ∈ S.QG := by
    have e : (⟨m * (D.κ A)⁻¹, hyM⟩ : S.M) = ⟨m, hm⟩ * (⟨D.κ A, D.hκM A⟩ : S.M)⁻¹ := rfl
    have h1 : S.ρ ⟨m * (D.κ A)⁻¹, hyM⟩ = 1 := by
      rw [e, map_mul, map_inv, mul_inv_eq_one]
      exact Subtype.ext (LinearEquiv.ext hA)
    exact (S.ρ_eq_one_iff _).mp h1
  set a := D.hl.inv (S.cl (m * (D.κ A)⁻¹))
  have hcl : S.cl (D.sHat a) = S.cl (m * (D.κ A)⁻¹) := by rw [D.cl_sHat, D.hl.l_inv]
  obtain ⟨ε, hε⟩ : ∃ ε : ZMod 2, m * (D.κ A)⁻¹ = zp S ε * D.sHat a := by
    rcases (S.cl_eq_cl_iff (D.sHat_mem a) hyQ).mp hcl with h | h
    · exact ⟨0, by rw [h, zp_zero, one_mul]⟩
    · refine ⟨1, ?_⟩
      rw [h, zp_one]
      exact S.z_comm (S.QG_le_M (D.sHat_mem a))
  refine ⟨(ε, a, A), Subtype.ext ?_⟩
  change zp S ε * D.sHat a * D.κ A = m
  rw [← hε, inv_mul_cancel_right]

theorem phi_bijective : Function.Bijective D.phi := ⟨D.phi_injective, D.phi_surjective⟩

include D in
theorem nonempty_mulEquiv :
    Nonempty (Subgroup.centralizer ({S.z} : Set G) ≃*
      Subgroup.centralizer ({tq (v₀ 3)} : Set (PG 5))) :=
  nonempty_mulEquiv_of_model D.phi psiC D.phi_bijective psiC_bijective D.phi_mul psiC_mul

end ThData

end CFSG.LargeExtraspecial.AS35QTh
