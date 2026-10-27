module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCT3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
namespace Core
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_of_swap (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) (hV : ExtraTrans Ω K J S z t)
    {g : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G))
    (hswap : conjSub (g⁻¹ * (z * t) * g) R = T) : g⁻¹ * (z * t) * g = z * t := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hRsyl : IsSylow2In R K := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have hzRu : IsUniqueInvolution R z := uniqueInvolution_restrict hs.hz hRK hzR
  have haa : z * t * (z * t) = 1 := Q3.Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hC hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * (z * t) * g := ⟨_, rfl⟩
  rw [← hbdef] at hb hswap ⊢
  have hbb : b * b = 1 := by
    rw [hbdef]
    calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * ((z * t) * (z * t)) * g := by group
      _ = 1 := by rw [haa]; group
  have hbK : conjSub b K = J :=
    hΩ.eq_of_le_of_le (hcl b K hK) hJΩ hTsyl.2.1 (by omega) (hswap ▸ conjSub_mono hRK) hTJ
  have hbJ : conjSub b J = K := by
    have := congrArg (conjSub b) hbK
    rw [← conjSub_mul, hbb, conjSub_one] at this
    exact this.symm
  have hbz : b * z * b⁻¹ = t := (hs.ht.eq (hbK ▸ hs.hz.conj b)).symm
  have hRT : Commutes R T :=
    l6_7_proved G Ω hΩ S R hRΩ T hTΩ hRS hTS (R_ne_T hs)
  have hTmem : ∀ r ∈ R, b * r * b⁻¹ ∈ T := fun r hr => by
    rw [← hswap]
    exact conj_mem_conjSub hr
  have hcomm : ∀ r ∈ R, ∀ s ∈ R, s * (b * r * b⁻¹) = (b * r * b⁻¹) * s := fun r hr s hs' =>
    hRT s hs' _ (hTmem r hr)
  let φ : ↥R →* G := MonoidHom.mk' (fun r => (r : G) * (b * (r : G) * b⁻¹)) (by
    intro r s
    simp only [Subgroup.coe_mul]
    calc (r : G) * (s : G) * (b * ((r : G) * (s : G)) * b⁻¹)
        = (r : G) * ((s : G) * (b * (r : G) * b⁻¹)) * (b * (s : G) * b⁻¹) := by group
      _ = (r : G) * ((b * (r : G) * b⁻¹) * (s : G)) * (b * (s : G) * b⁻¹) := by
        rw [hcomm r r.2 s s.2]
      _ = ((r : G) * (b * (r : G) * b⁻¹)) * ((s : G) * (b * (s : G) * b⁻¹)) := by group)
  have hφ : ∀ r : ↥R, φ r = (r : G) * (b * (r : G) * b⁻¹) := fun r => rfl
  have hQS : φ.range ≤ (S : Subgroup G) := by
    rintro _ ⟨r, rfl⟩
    rw [hφ]
    exact S.mul_mem (hRS r.2)
      (S.mul_mem (S.mul_mem hb (hRS r.2)) (S.inv_mem hb))
  have hQ2 : IsPGroup 2 ↥φ.range := S.isPGroup'.to_le hQS
  have hQb : ∀ y ∈ φ.range, y * b = b * y := by
    rintro _ ⟨r, rfl⟩
    rw [hφ]
    have h1 : b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹ = (r : G) * (b * (r : G) * b⁻¹) := by
      calc b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹
          = (b * (r : G) * b⁻¹) * ((b * b) * (r : G) * (b * b)⁻¹) := by group
        _ = (b * (r : G) * b⁻¹) * (r : G) := by rw [hbb]; group
        _ = (r : G) * (b * (r : G) * b⁻¹) := (hcomm r r.2 r r.2).symm
    calc (r : G) * (b * (r : G) * b⁻¹) * b
        = (b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹) * b := by rw [h1]
      _ = b * ((r : G) * (b * (r : G) * b⁻¹)) := by group
  have hbn : g⁻¹ * (z * t) * (g⁻¹)⁻¹ = b := by rw [hbdef, inv_inv]
  obtain ⟨n', hn'b, hQn'⟩ := exists_conj_sylow_of_le_centralizer S haS (n := g⁻¹) hQ2
    (fun y hy => by rw [hbn]; exact hQb y hy)
  rw [hbn] at hn'b
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  have haSm : z * t ∈ (S : Subgroup G) := S.mul_mem (hRS hzR) (hTS htT)
  let Nsub : Subgroup ↥R := (Subgroup.normalizer ((conjSub n' R : Subgroup G) : Set G)).comap φ
  let N : Subgroup G := Nsub.map R.subtype
  have hNR : N ≤ R := Subgroup.map_subtype_le _
  have hmemN : ∀ r : ↥R, (r : G) ∈ N ↔ conjSub (φ r) (conjSub n' R) = conjSub n' R := by
    intro r
    constructor
    · intro h
      obtain ⟨r', hr', hrr'⟩ := Subgroup.mem_map.mp h
      have : r' = r := Subtype.ext hrr'
      subst this
      exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_comap.mp hr')
    · intro h
      exact Subgroup.mem_map.mpr
        ⟨r, Subgroup.mem_comap.mpr (mem_normalizer_iff_conjSub_eq.mpr h), rfl⟩
  have hperm : ∀ r : ↥R, ¬ (conjSub (φ r) (conjSub n' R) = conjSub n' R) →
      conjSub (φ r) (conjSub n' R) = conjSub n' T ∧
        conjSub (φ r) (conjSub n' T) = conjSub n' R := by
    intro r hr
    rcases frame_conj_perm hs hC (hQn' ⟨r, rfl⟩) with h | h
    · exact absurd h.1 hr
    · exact h
  have hprod : ∀ x ∈ R, ∀ y ∈ R, x ∉ N → y ∉ N → x * y ∈ N := by
    intro x hx y hy hxN hyN
    have hx' := hperm ⟨x, hx⟩ (fun h => hxN ((hmemN ⟨x, hx⟩).mpr h))
    have hy' := hperm ⟨y, hy⟩ (fun h => hyN ((hmemN ⟨y, hy⟩).mpr h))
    have : ((⟨x, hx⟩ * ⟨y, hy⟩ : ↥R) : G) ∈ N := by
      rw [hmemN, map_mul, conjSub_mul, hy'.1, hx'.2]
    exact this
  obtain ⟨r₁, hr₁N, hr₁o⟩ := exists_orderOf_four_of_swap hzRu hRsyl.2.1 h8R N hNR hprod
  have hr₁R : r₁ ∈ R := hNR hr₁N
  have hr₁sq : r₁ * r₁ = z := by
    have hr4 : (r₁ * r₁) * (r₁ * r₁) = 1 := by
      have h4 : r₁ ^ 4 = (r₁ * r₁) * (r₁ * r₁) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [← h4, ← hr₁o]
      exact pow_orderOf_eq_one r₁
    rcases hzRu.unique _ (R.mul_mem hr₁R hr₁R) hr4 with h | h
    · exfalso
      have h2 : r₁ ^ 2 = 1 := by rw [pow_two]; exact h
      have h4 : orderOf r₁ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hr₁o] at h4
      omega
    · exact h
  have hqsq : φ ⟨r₁, hr₁R⟩ * φ ⟨r₁, hr₁R⟩ = z * t := by
    have h1 : (⟨r₁, hr₁R⟩ : ↥R) * ⟨r₁, hr₁R⟩ = ⟨z, hzR⟩ := Subtype.ext hr₁sq
    calc φ ⟨r₁, hr₁R⟩ * φ ⟨r₁, hr₁R⟩ = φ (⟨r₁, hr₁R⟩ * ⟨r₁, hr₁R⟩) := (map_mul φ _ _).symm
      _ = φ ⟨z, hzR⟩ := by rw [h1]
      _ = z * t := by
        rw [hφ]
        show z * (b * z * b⁻¹) = z * t
        rw [hbz]
  have hqN : conjSub (φ ⟨r₁, hr₁R⟩) (conjSub n' R) = conjSub n' R :=
    (hmemN ⟨r₁, hr₁R⟩).mp hr₁N
  have hqS' : φ ⟨r₁, hr₁R⟩ ∈ conjSub n' (S : Subgroup G) := hQn' ⟨_, rfl⟩
  have hK'Ω : conjSub n' K ∈ Ω := hcl n' K hK
  have hz' : IsUniqueInvolution (conjSub n' K) (n' * z * n'⁻¹) := hs.hz.conj n'
  have hqK' : conjSub (φ ⟨r₁, hr₁R⟩) (conjSub n' K) = conjSub n' K :=
    Q3.Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK'Ω (RSet.conj hcl hRΩ n') (conjSub_mono hRK) hqN
  have hq2 : IsPGroup 2 (Subgroup.zpowers (φ ⟨r₁, hr₁R⟩)) :=
    (isPGroup_conjSub n' S.isPGroup').to_le (Subgroup.zpowers_le.mpr hqS')
  obtain ⟨x₂, hx₂K', hx₂o, hx₂c⟩ := Q3.Q3CL.T8.exists_orderFour_centralizes_sq hΩ hK'Ω hz' hq2 hqK'
  rw [hqsq] at hx₂c
  have hxK : n'⁻¹ * x₂ * n' ∈ K := mem_conjSub_iff.mp hx₂K'
  have hxo : orderOf (n'⁻¹ * x₂ * n') = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n'⁻¹) x₂
    rw [MulAut.conj_apply, hx₂o] at this
    simpa using this
  have hxc : (n'⁻¹ * x₂ * n') * (n'⁻¹ * (z * t) * (n'⁻¹)⁻¹) =
      (n'⁻¹ * (z * t) * (n'⁻¹)⁻¹) * (n'⁻¹ * x₂ * n') := by
    rw [inv_inv]
    calc n'⁻¹ * x₂ * n' * (n'⁻¹ * (z * t) * n') = n'⁻¹ * (x₂ * (z * t)) * n' := by group
      _ = n'⁻¹ * ((z * t) * x₂) * n' := by rw [hx₂c]
      _ = n'⁻¹ * (z * t) * n' * (n'⁻¹ * x₂ * n') := by group
  obtain ⟨O, hO, hw⟩ := conj_zt_mul_inv_mem_of_orderFour hs hC hV (n := n'⁻¹) hxK hxo hxc
  have hwb : n'⁻¹ * ((z * t) * b⁻¹) * n' = n'⁻¹ * (z * t) * (n'⁻¹)⁻¹ * (z * t)⁻¹ := by
    rw [← hn'b]
    group
  exact (eq_of_conj_mul_inv_mem_odd S.isPGroup' haSm hb hO n' (hwb ▸ hw)).symm
end Cert
end Core
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
    CFSG.ClassicalInvolution.Asc77.T8
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
namespace Core
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem extraTrans (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) : ExtraTrans Ω K J S z t := by
  intro M hM h4 hMK hMJ
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hP := T8.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  have hc := Hat2A7P1.T8.ctxOf hP hW
  obtain ⟨η, hηG, hWη⟩ := id hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV : V ≤ W).trans hWS
  have hU : M ⊓ W ∈ η := by
    have := l6_11_proved G Ω hΩ S η hηG hηS M hM (by omega)
    rwa [← hWη] at this
  obtain ⟨S₀, hη, -⟩ := id hηG
  have hUU : M ⊓ W ∈ USet Ω := (hη.1 hU).1
  obtain ⟨RM, hRMD, hRMsyl⟩ := Q3.Q3CL.Thompson.exists_sylow_mem_DSet hΩ hW hWS hM hUU inf_le_left
    (inf_le_right.trans hWS)
  obtain ⟨ρK, hρK, hρKR⟩ : ∃ ρ : Rep Ω W, ρ.K = K ∧ ρ.R = R := ⟨T8.stdRepK hs, rfl, rfl⟩
  obtain ⟨ρJ, hρJ, -⟩ : ∃ ρ : Rep Ω W, ρ.K = J ∧ ρ.R = T := ⟨T8.stdRepJ hs, rfl, rfl⟩
  obtain ⟨ρM, hρM, -⟩ : ∃ ρ : Rep Ω W, ρ.K = M ∧ ρ.R = RM :=
    ⟨Hat2A7P1.T8.mkRep hP hW hM hRMD hRMsyl, rfl, rfl⟩
  obtain ⟨zM, hzM⟩ := hΩ.exists_uniqueInvolution hM
  have hMnK : M ∉ omegaNbr Ω K := not_mem_omegaNbr_of_four_le hs hC hM h4 hMJ
  have hMnJ : M ∉ omegaNbr Ω J :=
    not_mem_omegaNbr_of_four_le (Std8.symm' hs) hC hM h4 hMK
  have hKnM : K ∉ omegaNbr Ω M := fun h =>
    hMnK (Q3.Q3CL.T3.omegaNbr_symm (l6_2) hΩ hM hK h)
  have hJnM : J ∉ omegaNbr Ω M := fun h =>
    hMnJ (Q3.Q3CL.T3.omegaNbr_symm (l6_2) hΩ hM hJΩ h)
  have hzK : IsUniqueInvolution ρK.K z := by rw [hρK]; exact hs.hz
  have htJ : IsUniqueInvolution ρJ.K t := by rw [hρJ]; exact hs.ht
  have hzMρ : IsUniqueInvolution ρM.K zM := by rw [hρM]; exact hzM
  have hsz : ρM.r * z * ρM.r⁻¹ = zM * z :=
    hc.conj_involution ρM ρK (by rw [hρK, hρM]; exact hMK) (by rw [hρK, hρM]; exact hKnM) hzMρ hzK
  have hst : ρM.r * t * ρM.r⁻¹ = zM * t :=
    hc.conj_involution ρM ρJ (by rw [hρJ, hρM]; exact hMJ) (by rw [hρJ, hρM]; exact hJnM) hzMρ htJ
  have hzW : z ∈ W := (Q3.Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW ρK.hK ρK.hR ρK.hRK hzK).2
  have hzMW : zM ∈ W := (Q3.Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW ρM.hK ρM.hR ρM.hRK hzMρ).2
  have hzzM : zM * z = z * zM := hc.comm_W zM hzMW z hzW
  have hrC : ρK.r ∈ Subgroup.centralizer ({z * t} : Set G) :=
    T8.le_centralizer_mul hs (hρKR ▸ ρK.hr)
  have hrN : ρK.r ∈ Subgroup.normalizer (W : Set G) := ρK.r_mem_normalizer
  have hsN : ρM.r ∈ Subgroup.normalizer (W : Set G) := ρM.r_mem_normalizer
  have hr2 : ρK.r * ρK.r ∈ W := Q3.Q3CL.Thompson.D_sq_mem hΩ hW ρK.hR ρK.hr
  have hs2 : ρM.r * ρM.r ∈ W := Q3.Q3CL.Thompson.D_sq_mem hΩ hW ρM.hR ρM.hr
  have hne : ρK.K ≠ ρM.K := by rw [hρK, hρM]; exact Ne.symm hMK
  have hnot : ρM.K ∉ omegaNbr Ω ρK.K := by rw [hρK, hρM]; exact hMnK
  have hcube : (piG W ρK.r * piG W ρM.r) ^ 3 = 1 := by
    rcases Hat2A7P1.thompsonCube hP W hW ρK.R ρK.hR ρM.R ρM.hR ρK.r ρK.hr ρM.r ρM.hr ρK.hrW ρM.hrW with
      h | h
    · exact absurd ((piG_comm_iff hrN hsN).mpr h) (hc.noncomm ρK ρM hne hnot)
    · exact (piG_cube_iff hrN hsN).mpr h
  obtain ⟨c, hcC, hcK⟩ := CFSG.ClassicalInvolution.Asc77.T8R.extraTrans_core hcl ρK ρM hzM.sq hsz hst hzzM hrC hr2 hs2 hcube
    (fun ρ' h => hc.K_eq_of_img_eq ρ' ρM h)
  exact ⟨c, hcC, Or.inl (by rw [← hρK, ← hρM]; exact hcK)⟩
end Cert
end Core
end T8R
end Asc77

end

end CFSG.ClassicalInvolution.Hat2A7S8
