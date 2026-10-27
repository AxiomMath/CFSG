module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Gam
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4StrongOrbit

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.AGLEmbeddingD2.Wilson.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def C0 : Subgroup J := Subgroup.closure {c1j, nrm₂, qz}

theorem C0p_eq_map : C0p = C0.map (MulAut.conj gam).toMonoidHom := by
  unfold C0p C0 cA cB cZ
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem comm_self_pow {G : Type*} [Group G] (a : G) (n : ℕ) : a * a ^ n = a ^ n * a :=
  (Commute.self_pow a n).eq

section Facts

theorem nrm₂_mem_inf : nrm₂ ∈ Subgroup.normalizer (Q11 : Set J) ⊓
    Subgroup.centralizer ({jInv} : Set J) := by
  refine ⟨nrm₂_mem_normalizer, ?_⟩
  change nrm₂ ∈ Subgroup.centralizer ({jInv} : Set J)
  rw [Subgroup.mem_centralizer_singleton_iff, jInv]
  exact @comm_self_pow J (Subgroup.toGroup J) nrm₂ 20

theorem qz_mem_inf :
    qz ∈ Subgroup.centralizer ({jInv} : Set J) := by
  rw [Subgroup.mem_centralizer_singleton_iff, jInv]
  have h := @iterate_conj_pow J (Subgroup.toGroup J) nrm₂ qz nrm₂_qz 20
  have hq11 : qz ^ 11 = 1 := by
    have := pow_orderOf_eq_one qz
    rwa [orderOf_qz] at this
  have h2 : qz ^ (2 ^ 20) = qz := by
    have := pow_mod_orderOf qz (2 ^ 20)
    rw [orderOf_qz] at this
    rw [← this]
    have : 2 ^ 20 % 11 = 1 := by norm_num
    rw [this, pow_one]
  rw [h2] at h
  calc qz * nrm₂ ^ 20 = (nrm₂ ^ 20 * qz * (nrm₂ ^ 20)⁻¹) * nrm₂ ^ 20 := by rw [h]
    _ = nrm₂ ^ 20 * qz := by group

end Facts

section C0

theorem c1j_mem_inf : c1j ∈ Subgroup.normalizer (Q11 : Set J) ⊓
    Subgroup.centralizer ({jInv} : Set J) := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.le_normalizer (Q11.pow_mem qy_mem 10))
    nrm₁_mem_normalizer, ?_⟩
  change c1j ∈ Subgroup.centralizer ({jInv} : Set J)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact c1j_comm_jInv

theorem C0_le_inf : C0 ≤ Subgroup.normalizer (Q11 : Set J) ⊓
    Subgroup.centralizer ({jInv} : Set J) := by
  rw [C0, Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact c1j_mem_inf
  · exact nrm₂_mem_inf
  · exact ⟨Subgroup.le_normalizer qz_mem, qz_mem_inf⟩

theorem C0p_le_M2 : C0p ≤ CFSG.Quasithin.J4M2.M2 := by
  rw [C0p_eq_map]
  rintro _ ⟨x, hx, rfl⟩
  have hx' := (C0_le_inf hx).2
  change x ∈ Subgroup.centralizer ({jInv} : Set J) at hx'
  rw [Subgroup.mem_centralizer_singleton_iff] at hx'
  change gam * x * gam⁻¹ ∈ Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)
  rw [Subgroup.mem_centralizer_singleton_iff, ← gam_conj_jInv]
  calc gam * x * gam⁻¹ * (gam * jInv * gam⁻¹) = gam * (x * jInv) * gam⁻¹ := by group
    _ = gam * (jInv * x) * gam⁻¹ := by rw [hx']
    _ = _ := by group

end C0

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
