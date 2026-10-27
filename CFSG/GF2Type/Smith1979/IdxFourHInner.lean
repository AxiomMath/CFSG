module

public import CFSG.GF2Type.Smith1979.IdxFourHFuse
public import CFSG.GF2Type.Smith1979.IdxFourHFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Literature.FSmith (zmod2_cases)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem inner_fusion {g : G} (H : S4.Hyp4 S g) (C : S4.Cons311 S g) {θ : S.O} (hθM : θ ∈ S.Mbar)
    (hθ3 : θ ^ 3 = 1) (hθ : ∀ v : S.Qt, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hin : InnerData S θ g t) {l : G} (hl : l ∈ S.M)
    (hll : l * l = 1) (hρ : S.ρ ⟨l, hl⟩ = t) : ∃ y ∈ S.M, y * l * y⁻¹ ∈ S.L0 g := by
  obtain ⟨hθt, -, hRsing, hmax, hcov⟩ := hin
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  obtain ⟨c, hc3, hcρ⟩ := exists_pow3_lift hθM hθ3
  have hfpf : ∀ v : S.Qt, (S.ρ c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0 := by
    rw [hcρ]
    exact hθ
  obtain ⟨s, hsρ, hcs⟩ := exists_comm_lift hc3 htM (by rw [hcρ]; exact hθt)
  have hs2 : S.ρ s * S.ρ s = 1 := by rw [hsρ]; exact htt
  have hsq := sq_eq_one_or_z_of_comm hc3 hfpf hcs hs2
  have K1 : ∀ u ∈ S.QG, S.cl u ∈ fixO S t → (s : G) * u = u * s := by
    intro u hu hfix
    have h := conj_eq_of_fixed hc3 hfpf hcs hu (by rw [hsρ]; exact mem_fixO.mp hfix)
    calc (s : G) * u = (s : G) * u * (s : G)⁻¹ * s := by group
      _ = u * s := by rw [h]
  set V : Subgroup G := S.QG ⊓ S.Qa g with hV
  set Vt : Submodule (ZMod 2) S.Qt := S.clSub V with hVt
  have hVQ : V ≤ S.QG := inf_le_left
  have hzV : S.z ∈ V := z_mem_QG_inf_Qa H
  have hVtq : ∀ p ∈ Vt, S.q p = 0 := by
    intro p hp
    obtain ⟨v, hv, hvQ, rfl⟩ := S.mem_clSub_iff.mp hp
    exact (S.q_cl_eq_zero_iff hvQ).mpr (S.QG_inf_Qa_sq H.conj_ne hv)
  obtain ⟨r₀, hr₀L, hr₀r₀, hr₀M, hr₀ρ⟩ := exists_involution_L0 H C ht ht1
  obtain ⟨u₀, hu₀Q, hr₀eq, hu₀F⟩ := exists_comm_form hsρ hsq hr₀M hr₀ρ hr₀r₀
  have H0 : S.q (S.cl u₀) = 0 ↔ (s : G) * s = 1 :=
    (mul_sq_eq_one_iff hsq hu₀Q (K1 u₀ hu₀Q hu₀F)).mp (by rw [← hr₀eq]; exact hr₀r₀)
  have hperp : ∀ p ∈ Vt ⊓ fixO S t, polar S.q (S.cl u₀) p = 0 := by
    intro p hp
    obtain ⟨v, hv, hvQ, rfl⟩ := S.mem_clSub_iff.mp hp.1
    have hvF : S.cl v ∈ fixO S t := hp.2
    have hvv : v * v = 1 := by rw [← pow_two]; exact S.QG_inf_Qa_sq H.conj_ne hv
    have hcomm : r₀ * v = v * r₀ :=
      comm_of_mem_L0 H hr₀L hr₀M hv (by rw [hr₀ρ]; exact mem_fixO.mp hvF)
    have hinv : (r₀ * v) * (r₀ * v) = 1 := by
      calc (r₀ * v) * (r₀ * v) = r₀ * (v * r₀) * v := by group
        _ = r₀ * (r₀ * v) * v := by rw [hcomm]
        _ = (r₀ * r₀) * (v * v) := by group
        _ = 1 := by rw [hr₀r₀, hvv, one_mul]
    have hwQ : u₀ * v ∈ S.QG := S.QG.mul_mem hu₀Q hvQ
    have hwF : S.cl (u₀ * v) ∈ fixO S t := by
      rw [S.cl_mul hu₀Q hvQ]
      exact (fixO S t).add_mem hu₀F hvF
    have H1 : S.q (S.cl (u₀ * v)) = 0 ↔ (s : G) * s = 1 := by
      refine (mul_sq_eq_one_iff hsq hwQ (K1 _ hwQ hwF)).mp ?_
      calc ((s : G) * (u₀ * v)) * ((s : G) * (u₀ * v))
          = ((s : G) * u₀ * v) * ((s : G) * u₀ * v) := by group
        _ = (r₀ * v) * (r₀ * v) := by rw [← hr₀eq]
        _ = 1 := hinv
    have hqv : S.q (S.cl v) = 0 := (S.q_cl_eq_zero_iff hvQ).mpr (by rw [pow_two]; exact hvv)
    have hadd : S.q (S.cl (u₀ * v)) = S.q (S.cl u₀) + S.q (S.cl v) + polar S.q (S.cl u₀) (S.cl v) := by
      rw [S.cl_mul hu₀Q hvQ]
      exact map_add_eq S.q _ _
    rw [hqv, add_zero] at hadd
    rw [hadd] at H1
    rcases zmod2_cases (S.q (S.cl u₀)) with ha | ha <;>
      rcases zmod2_cases (polar S.q (S.cl u₀) (S.cl v)) with hb | hb
    · exact hb
    · exfalso
      rw [ha] at H0
      rw [ha, hb] at H1
      have h1 := H0.mp rfl
      have h2 := H1.mpr h1
      revert h2
      decide
    · exact hb
    · exfalso
      rw [ha] at H0
      rw [ha, hb] at H1
      have h1 := H1.mp (by decide)
      have h2 := H0.mpr h1
      revert h2
      decide
  obtain ⟨p₀, hp₀, ρ₀, hρ₀, hcl₀⟩ := hmax (S.cl u₀) hu₀F hperp
  have hq0 : S.q (S.cl u₀) = 0 := by
    have hpol : polar S.q p₀ ρ₀ = 0 := by
      have hp : p₀ ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin (commO S t) := by
        rw [← fixO_eq_orthogonal htt]
        exact hp₀.2
      have := LinearMap.BilinForm.mem_orthogonal_iff.mp hp ρ₀ hρ₀
      rw [polar_comm]
      simpa [LinearMap.BilinForm.IsOrtho, polarBilin_apply_apply] using this
    rw [hcl₀, map_add_eq, hVtq p₀ hp₀.1, hRsing ρ₀ hρ₀, hpol, zero_add, zero_add]
  have hss1 : (s : G) * s = 1 := H0.mp hq0
  obtain ⟨u, huQ, hleq, huF⟩ := exists_comm_form hsρ hsq hl hρ hll
  have huq : S.q (S.cl u) = 0 :=
    ((mul_sq_eq_one_iff hsq huQ (K1 u huQ huF)).mp (by rw [← hleq]; exact hll)).mpr hss1
  obtain ⟨i, u₁, hu₁, ρ₁, hρ₁, hcleq⟩ := hcov (S.cl u) huF huq
  set θi : S.O := θ ^ i with hθi
  have hθct : Commute θ t := hθt
  have hθit' : θi⁻¹ * t = t * θi⁻¹ := ((hθct.pow_left i).inv_left).eq
  set d : S.M := (c ^ i)⁻¹ with hd
  have hdρ : S.ρ d = θi⁻¹ := by rw [hd, map_inv, map_pow, hcρ]
  have hdcomm : (d : G) * s * (d : G)⁻¹ = s := by
    have hcc : Commute c s := hcs
    have h1 : d * s = s * d := (((hcc.pow_left i).inv_left).eq)
    have h2 : (d : G) * s = s * d := congrArg (fun x : S.M => (x : G)) h1
    calc (d : G) * s * (d : G)⁻¹ = (s : G) * d * (d : G)⁻¹ := by rw [h2]
      _ = s := by group
  set u'' : G := (d : G) * u * (d : G)⁻¹ with hu''
  have hu''Q : u'' ∈ S.QG := S.conj_mem_QG d.2 huQ
  have hcl'' : S.cl u'' = u₁ + ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁ := by
    rw [hu'', ← S.ρ_cl d huQ, hdρ, hcleq, map_add, S4.inv_apply_apply_O]
  have hr' : ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁ ∈ commO S t := apply_mem_commO hθit' hρ₁
  have hdl : (d : G) * l * (d : G)⁻¹ = r₀ * (u₀⁻¹ * u'') := by
    calc (d : G) * l * (d : G)⁻¹ = ((d : G) * s * (d : G)⁻¹) * ((d : G) * u * (d : G)⁻¹) := by
          rw [hleq]; group
      _ = (s : G) * u'' := by rw [hdcomm]
      _ = r₀ * (u₀⁻¹ * u'') := by rw [hr₀eq]; group
  have hwQ : u₀⁻¹ * u'' ∈ S.QG := S.QG.mul_mem (S.QG.inv_mem hu₀Q) hu''Q
  have hclw : S.cl (u₀⁻¹ * u'') =
      (p₀ + ρ₀) + (u₁ + ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁) := by
    rw [S.cl_mul (S.QG.inv_mem hu₀Q) hu''Q, S.cl_inv hu₀Q, hcl'', hcl₀]
  have ha₂R : ρ₀ + ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁ ∈ commO S t :=
    (commO S t).add_mem hρ₀ hr'
  obtain ⟨v₂, hv₂⟩ := mem_commO.mp ha₂R
  obtain ⟨q₂, hq₂Q, rfl⟩ := S.exists_cl v₂
  obtain ⟨w', hw'Q, hconj, hclw'⟩ := exists_conj_shift (s := ⟨r₀, hr₀M⟩) hr₀ρ htt hwQ hq₂Q
  have hclw'' : S.cl w' = p₀ + u₁ := by
    rw [hclw', hclw]
    have h3 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q₂) + S.cl q₂ =
        ρ₀ + ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁ := by
      rw [← sub_eq_add_vec (ZMod 2)]
      exact hv₂
    rw [h3]
    calc (p₀ + ρ₀) + (u₁ + ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁) +
          (ρ₀ + ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁)
        = (p₀ + u₁) + ((ρ₀ + ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁) +
          (ρ₀ + ((θi⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ρ₁)) := by abel
      _ = p₀ + u₁ := by rw [add_self_vec (ZMod 2), add_zero]
  have hw'V : w' ∈ V := by
    have : w' ∈ S.clPre Vt := ⟨hw'Q, by rw [hclw'']; exact Vt.add_mem hp₀.1 hu₁.1⟩
    rwa [hVt, S.clPre_clSub hVQ hzV] at this
  refine ⟨q₂ * d, S.M.mul_mem (S.QG_le_M hq₂Q) d.2, ?_⟩
  have hfin : (q₂ * (d : G)) * l * (q₂ * (d : G))⁻¹ = r₀ * w' := by
    calc (q₂ * (d : G)) * l * (q₂ * (d : G))⁻¹ = q₂ * ((d : G) * l * (d : G)⁻¹) * q₂⁻¹ := by
          group
      _ = q₂ * (r₀ * (u₀⁻¹ * u'')) * q₂⁻¹ := by rw [hdl]
      _ = r₀ * w' := hconj
  rw [hfin]
  exact (S.L0 g).mul_mem hr₀L (QG_inf_Qa_le_L0 hw'V)

end CFSG.GF2Type.Smith1979.IdxFour
