module

public import CFSG.ClassicalInvolution.Asc77.AscS24BHKey

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace HCtx

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : HCtx p f Ω K K' W S R R' z u)

include H in
theorem centralizer_z_le_sigma :
    Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
  have hst := H.C.hs.stand
  have hΩ := hst.hyp
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hL : conjSub c K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant c K hst.mem, z, H.C.hzK, hcz ▸ H.C.hzK.conj c⟩
  exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hst.mem
    (AscE186.mem_dstarComp_of_twin hst.odd hΩ hst.mem hL)

theorem J_mem_dstarComp : H.C.D.F.ρ₃.K ∈ dstarComp Ω K := by
  have hst := H.C.hs.stand
  have hcard : Nat.card ↥H.C.D.F.ρ₃.R = 2 * Nat.card ↥(Subgroup.zpowers H.C.D.x₃) := by
    have h := Thompson.D_card H.C.D.c.hp H.C.D.c.hq H.C.D.c.hΩ H.C.D.c.hW H.C.D.F.ρ₃.hR
    rw [← H.C.D.h₃] at h
    exact h
  have hU : Subgroup.zpowers H.C.D.x₃ ∈ USet Ω :=
    mem_USet_of_natCard H.C.D.F.ρ₃.hK H.C.D.F.ρ₃.hRK
      (Subgroup.zpowers_le.mpr H.C.x₃_mem_R₃) inferInstance hcard
  have hUN : Subgroup.zpowers H.C.D.x₃ ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (H.C.W_le_normalizer K hst.mem ⟨H.C.x₁_mem_K, H.C.D.x₁_mem⟩
      H.C.orderOf_x₁ H.C.D.x₃_mem)
  have hstar : H.C.D.F.ρ₃.K ∈ omegaStarNbr Ω K :=
    ⟨H.C.D.F.ρ₃.hK, H.C.J_ne_K, _, hU, Subgroup.zpowers_le.mpr H.C.x₃_mem_J, hUN⟩
  exact Relation.ReflTransGen.single ⟨H.C.D.F.ρ₃.hK, Or.inl hstar⟩

include H in
theorem centralizer_u_le_sigma :
    Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K := by
  have hst := H.C.hs.stand
  have hΩ := hst.hyp
  have hCz := H.centralizer_z_le_sigma
  obtain ⟨y, hy⟩ := hst.trans _ H.C.D.F.ρ₃.hK
  have hyN : y ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hst.mem (hy ▸ H.J_mem_dstarComp)
  have hj : H.C.D.F.j = y * z * y⁻¹ := H.C.hjJ.eq (hy ▸ H.C.hzK.conj y)
  have hCj : Subgroup.centralizer ({H.C.D.F.j} : Set G) ≤ sigmaStarNorm Ω K :=
    T7A.centralizer_conj_le hyN hj hCz
  have hCjz : Subgroup.centralizer ({H.C.D.F.j * z} : Set G) ≤ sigmaStarNorm Ω K :=
    T7A.centralizer_conj_le (hCz H.C.r_mem_centralizer_z) H.C.r_conj_j.symm hCj
  intro c hc
  rcases H.C.u_cases with h | h
  · exact hCj (by rw [← h]; exact hc)
  · exact hCjz (by rw [← h]; exact hc)

include H in
theorem false_of [IsSimpleGroup G] : False := by
  have hst := H.C.hs.stand
  have hN : sigmaStarNorm Ω K = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← S24.sup_centralizer_eq_top_of H.C.hs H.C.hd]
    exact sup_le H.centralizer_u_le_sigma H.centralizer_z_le_sigma
  have hall : ∀ M ∈ Ω, M ≤ Subgroup.centralizer ({H.a} : Set G) := by
    intro M hM
    obtain ⟨g, hg⟩ := hst.trans M hM
    have hgN : g ∈ sigmaStarNorm Ω K := by rw [hN]; exact Subgroup.mem_top g
    have hMS : M ∈ dstarComp Ω K := by
      rw [← hg]
      exact (mem_sigmaStarNorm_iff.mp hgN K).mp Relation.ReflTransGen.refl
    obtain ⟨h, hh, hK⟩ := H.trans M hMS
    rw [← hK]
    exact conjSub_le_centralizer H.K_le (Subgroup.mem_centralizer_singleton_iff.mp hh)
  have htop : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer ({H.a} : Set G) := iSup₂_le hall
  rw [hst.gen] at htop
  apply H.ha1
  refine T7B.eq_one_of_central (T7C.exists_not_commute_of_stand hst) fun g => ?_
  exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))

end HCtx


theorem h3_proved : H3 p f := by
  intro G _ _ _ Ω K K' W S R R' z u hs hd h8 D hK hK' hR hR' a ha2 haR haR' T₃ hT hTN hTa
  by_contra ha1
  have hz : D.F.z = z := (hs.hz.eq (hK ▸ D.F.hz)).symm
  exact (⟨⟨hs, hd, h8, D, hK, hK', hR, hR', hz⟩, a, T₃, ha2, ha1, haR, haR', hT, hTN, hTa⟩ :
    HCtx p f Ω K K' W S R R' z u).false_of

end S24B

end CFSG.ClassicalInvolution.Asc77
