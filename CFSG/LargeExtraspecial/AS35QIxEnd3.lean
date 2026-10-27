module

public import CFSG.LargeExtraspecial.AS35QIxEnd2
public import CFSG.LargeExtraspecial.AS35QIxBad2
public import CFSG.LargeExtraspecial.AS35QIxEnd1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxSetup

variable (T : IxSetup S)

theorem l_ne_l {x y : Fin 3 → K} (i : Fin 3) (h : x i ≠ y i) : T.l x ≠ T.l y :=
  fun e => h (congrFun (T.l_injective e) i)

theorem q_l_110 : S.q (T.l ![1, 1, 0]) = 0 := by
  rw [q_l, herm_self]
  simp [add_self_K, AS35QTh.tr2_zero]

theorem polar_l_110_011 : polar S.q (T.l ![1, 1, 0]) (T.l ![0, 1, 1]) = 0 := by
  rw [T.hl.polar, herm_def, Fin.sum_univ_three]
  simp [AS35QTh.tr2_one]

theorem F_l_110 : (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![1, 1, 0]) = T.l ![1, 1, 0] := by
  rw [F_l]
  congr 1
  funext i
  fin_cases i <;> simp

theorem omega_ne_frob : ω ≠ frob ω := by
  intro h
  have h1 := omega_add_frob
  rw [← h, add_self_K] at h1
  exact zero_ne_one h1

theorem eq_of_F_fix_of_mem_commSpace {v : S.Qt}
    (hv : v ∈ commSpace (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt)) (hv0 : v ≠ 0)
    (hF : (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = T.l ![0, 1, 1] := by
  obtain ⟨d, rfl⟩ := (T.mem_commSpace_tb_iff).mp hv
  rw [F_l] at hF
  have h1 : frob d = d := congrFun (T.l_injective hF) 1
  rcases AS35QTh.K_cases d with rfl | rfl | rfl | rfl
  · exfalso
    apply hv0
    convert T.l_zero
    funext i
    fin_cases i <;> rfl
  · rfl
  · exact absurd h1.symm omega_ne_frob
  · rw [frob_frob] at h1
    exact absurd h1 omega_ne_frob

end IxSetup

namespace IxBad

variable (T : IxBad S)

theorem not_propP (hS : S.SixHyp) {a : G} (ha : a ∈ S.M) (haa : a * a = 1)
    (hat : a * T.t = T.t * a) (hax : a * T.xh = T.xh * a) (haρ : S.ρ ⟨a, ha⟩ = T.F)
    (hg : T.g⁻¹ * a * T.g ∈ S.M) (hgζ : S.ρ ⟨_, hg⟩ * T.ζ ≠ T.ζ * S.ρ ⟨_, hg⟩) :
    ¬ PropP a := by
  intro hP
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hFinv : S.ρ ⟨a, ha⟩ * T.ζ * (S.ρ ⟨a, ha⟩)⁻¹ = T.ζ⁻¹ := by rw [haρ]; exact T.F_inv_zeta
  have hrhoa : S.rhoL ha = (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) := by rw [Setting.rhoL, haρ]
  obtain ⟨e, heQ, hecl⟩ := S.exists_cl (T.l ![1, 1, 0])
  have hea : a * e * a⁻¹ = e := T.conj_eq_of_singular ha haa hFinv heQ
    (by rw [hrhoa, hecl, T.F_l_110]) (by rw [hecl, T.q_l_110])
  have hee : e * e = 1 := by
    rw [← pow_two]
    exact (S.q_cl_eq_zero_iff heQ).mp (by rw [hecl, T.q_l_110])
  have he'Q : T.xh * e * T.xh⁻¹ ∈ S.QG := S.conj_mem_QG T.hxhM heQ
  have he'cl : S.cl (T.xh * e * T.xh⁻¹) = T.l ![0, 1, 1] := by
    rw [← S.rhoL_cl T.hxhM heQ, Setting.rhoL, T.hxhρ, hecl, T.hlβ]
    simp
  have hcomm : e * (T.xh * e * T.xh⁻¹) = (T.xh * e * T.xh⁻¹) * e :=
    (S.polar_cl_eq_zero_iff heQ he'Q).mp (by rw [hecl, he'cl]; exact T.polar_l_110_011)
  have he'e' : (T.xh * e * T.xh⁻¹) * (T.xh * e * T.xh⁻¹) = 1 :=
    IxSetup.conj_mul_self_of T.xh e hee
  set f := e * T.xh * e⁻¹ * T.xh⁻¹ with hfdef
  have hfe : f = e * (T.xh * e * T.xh⁻¹)⁻¹ := by rw [hfdef]; group
  have hfQ : f ∈ S.QG := by rw [hfe]; exact S.QG.mul_mem heQ (S.QG.inv_mem he'Q)
  have hfcl : S.cl f = T.l ![1, 0, 1] := by
    rw [hfe, S.cl_mul heQ (S.QG.inv_mem he'Q), S.cl_inv he'Q, hecl, he'cl, ← T.l_add]
    congr 1
    funext i
    fin_cases i <;> simp [add_self_K]
  have hft : f * T.t ≠ T.t * f := by
    intro h
    have h1 : T.t * f * T.t⁻¹ = f := by rw [← h]; group
    have h2 := congrArg S.cl h1
    rw [← S.rhoL_cl T.t_mem_M hfQ, hfcl] at h2
    change (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![1, 0, 1]) = T.l ![1, 0, 1] at h2
    rw [T.tb_l] at h2
    exact T.l_ne_l 1 (by simp) h2
  have hff : f * f = 1 := by
    rw [hfe, inv_eq_of_mul_eq_one_right he'e']
    exact IxSetup.mul_mul_self_of_comm hee he'e' hcomm
  have hfa : a * f * a⁻¹ = f := by
    rw [hfdef]
    have hxinv : a * T.xh⁻¹ * a⁻¹ = T.xh⁻¹ := by
      rw [show a * T.xh⁻¹ * a⁻¹ = (a * T.xh * a⁻¹)⁻¹ by group, hax]; group
    have hx : a * T.xh * a⁻¹ = T.xh := by rw [hax]; group
    have heinv : a * e⁻¹ * a⁻¹ = e⁻¹ := by
      rw [show a * e⁻¹ * a⁻¹ = (a * e * a⁻¹)⁻¹ by group, hea]
    calc a * (e * T.xh * e⁻¹ * T.xh⁻¹) * a⁻¹ =
        (a * e * a⁻¹) * (a * T.xh * a⁻¹) * (a * e⁻¹ * a⁻¹) * (a * T.xh⁻¹ * a⁻¹) := by group
      _ = e * T.xh * e⁻¹ * T.xh⁻¹ := by rw [hea, hx, heinv, hxinv]
  have hcc : (T.g⁻¹ * a * T.g) * (T.g⁻¹ * a * T.g) = 1 := by
    rw [show T.g⁻¹ * a * T.g * (T.g⁻¹ * a * T.g) = T.g⁻¹ * (a * a) * T.g by group, haa]
    group
  have hcinv := T.conj_inv_of_not_comm (⟨_, rfl⟩ : S.ρ ⟨_, hg⟩ ∈ S.Mbar) hgζ
  obtain ⟨v, hvfix, hvq, hvt⟩ := exists_singular_fix_not_fix S.q_nondegenerate T.finrank_Qt
    T.hζ2 T.qζ (S.rhoL_mem hg) (S.rhoL_mul_self hg hcc) (T.rhoL_inv_zeta hg hcinv)
    T.tb_mem_O (coe_mul_self T.tb_mul_self) (T.apply_comm_of_comm T.tb_comm_zeta)
    (coe_ne_one T.tb_ne_one)
  obtain ⟨u, huQ, rfl⟩ := S.exists_cl v
  have huc : (T.g⁻¹ * a * T.g) * u * (T.g⁻¹ * a * T.g)⁻¹ = u :=
    T.conj_eq_of_singular hg hcc hcinv huQ hvfix hvq
  have huu : u * u = 1 := by
    rw [← pow_two]
    exact (S.q_cl_eq_zero_iff huQ).mp hvq
  have hut : u * T.t ≠ T.t * u := by
    intro h
    apply hvt
    rw [show (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.rhoL T.t_mem_M from rfl, S.rhoL_cl T.t_mem_M huQ]
    congr 1
    rw [← h]
    group
  set b := T.g * u * T.g⁻¹ with hbdef
  have hbQt : b ∈ S.Qa T.g := by
    rw [S.mem_Qa_iff_inv_conj_mem, hbdef, show T.g⁻¹ * (T.g * u * T.g⁻¹) * T.g = u by group]
    exact huQ
  have hbb : b * b = 1 := by rw [hbdef]; exact IxSetup.conj_mul_self_of T.g u huu
  have hba : b * a = a * b := by
    have e1 : a = T.g * (T.g⁻¹ * a * T.g) * T.g⁻¹ := by group
    have huc' : u * (T.g⁻¹ * a * T.g) = (T.g⁻¹ * a * T.g) * u := by
      calc u * (T.g⁻¹ * a * T.g) = (T.g⁻¹ * a * T.g) * u * (T.g⁻¹ * a * T.g)⁻¹ *
          (T.g⁻¹ * a * T.g) := by rw [huc]
        _ = (T.g⁻¹ * a * T.g) * u := by group
    rw [hbdef, e1]
    calc T.g * u * T.g⁻¹ * (T.g * (T.g⁻¹ * a * T.g) * T.g⁻¹) =
        T.g * (u * (T.g⁻¹ * a * T.g)) * T.g⁻¹ := by group
      _ = T.g * ((T.g⁻¹ * a * T.g) * u) * T.g⁻¹ := by rw [huc']
      _ = T.g * (T.g⁻¹ * a * T.g) * T.g⁻¹ * (T.g * u * T.g⁻¹) := by group
  have hbt : b * T.t = T.t * b := Setting.AS35T.commute_of_mem_Qa S hbQt
  have hbz : b * S.z ≠ S.z * b := by
    intro h
    apply hut
    have e1 : S.z = T.g * T.t * T.g⁻¹ := T.g_t.symm
    have h1 : T.g * (u * T.t) * T.g⁻¹ = T.g * (T.t * u) * T.g⁻¹ := by
      calc T.g * (u * T.t) * T.g⁻¹ = b * (T.g * T.t * T.g⁻¹) := by rw [hbdef]; group
        _ = (T.g * T.t * T.g⁻¹) * b := by rw [← e1, h, e1]
        _ = T.g * (T.t * u) * T.g⁻¹ := by rw [hbdef]; group
    have h2 := congrArg (fun y => T.g⁻¹ * y * T.g) h1
    rwa [show T.g⁻¹ * (T.g * (u * T.t) * T.g⁻¹) * T.g = u * T.t by group,
      show T.g⁻¹ * (T.g * (T.t * u) * T.g⁻¹) * T.g = T.t * u by group] at h2
  have hfH : f ∈ S.HAt T.g := le_sup_left (b := S.Qa T.g) hfQ
  have hbH : b ∈ S.HAt T.g := le_sup_right (a := S.QG) hbQt
  have hpΩ : f * T.t * f⁻¹ ∈ S.zConj (S.HAt T.g) :=
    Asc77.conj_mem_conjIn_of_mem hfH T.t_mem_zConj
  have hp'Ω : b * S.z * b⁻¹ ∈ S.zConj (S.HAt T.g) :=
    Asc77.conj_mem_conjIn_of_mem hbH T.z_mem_zConj
  have hpz : f * T.t * f⁻¹ ≠ S.z := by
    intro h
    apply T.t_ne_z
    calc T.t = f⁻¹ * (f * T.t * f⁻¹) * f := by group
      _ = S.z := by rw [h]; rw [S.z_comm (S.QG_le_M (S.QG.inv_mem hfQ))]; group
  have hp'z : b * S.z * b⁻¹ ≠ S.z := by
    intro h
    apply hbz
    calc b * S.z = b * S.z * b⁻¹ * b := by group
      _ = S.z * b := by rw [h]
  obtain ⟨hpQ, hpcl⟩ := S.mul_mem_QG_of_mem_zConj hS T.t_mem_DSet T.g_z T.t_mem_M hpΩ hpz
  obtain ⟨hp'Q, hp'cl⟩ :=
    S.mul_mem_QG_of_mem_zConj hS T.t_mem_DSet T.g_z T.t_mem_M hp'Ω hp'z
  have hpa : a * (f * T.t * f⁻¹ * T.t) * a⁻¹ = f * T.t * f⁻¹ * T.t := by
    calc a * (f * T.t * f⁻¹ * T.t) * a⁻¹ =
        (a * f * a⁻¹) * (a * T.t * a⁻¹) * (a * f * a⁻¹)⁻¹ * (a * T.t * a⁻¹) := by group
      _ = f * T.t * f⁻¹ * T.t := by rw [hfa, show a * T.t * a⁻¹ = T.t by rw [hat]; group]
  have hp'a : a * (b * S.z * b⁻¹ * T.t) * a⁻¹ = b * S.z * b⁻¹ * T.t := by
    have hbia : a * b * a⁻¹ = b := by rw [← hba]; group
    calc a * (b * S.z * b⁻¹ * T.t) * a⁻¹ =
        (a * b * a⁻¹) * (a * S.z * a⁻¹) * (a * b * a⁻¹)⁻¹ * (a * T.t * a⁻¹) := by group
      _ = b * S.z * b⁻¹ * T.t := by
          rw [hbia, show a * S.z * a⁻¹ = S.z by rw [S.z_comm ha]; group,
            show a * T.t * a⁻¹ = T.t by rw [hat]; group]
  have hFfix : ∀ {w : G}, w ∈ S.QG → a * w * a⁻¹ = w →
      (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl w) = S.cl w := by
    intro w hw haw
    rw [← hrhoa, S.rhoL_cl ha hw, haw]
  have hne0 : ∀ {w : G}, w ∈ S.zConj (S.HAt T.g) → w ≠ T.t → w * T.t ∈ S.QG →
      S.cl (w * T.t) ≠ 0 := by
    intro w hwΩ hwt hwtQ h0
    rcases (S.cl_eq_zero_iff hwtQ).mp h0 with h | h
    · apply hwt
      calc w = w * T.t * T.t := by rw [mul_assoc, T.t_mul_self, mul_one]
        _ = T.t := by rw [h, one_mul]
    · apply T.not_isConj_zt
      obtain ⟨k, -, hk⟩ := hwΩ
      have hw : w = S.z * T.t := by
        calc w = w * T.t * T.t := by rw [mul_assoc, T.t_mul_self, mul_one]
          _ = S.z * T.t := by rw [h]
      exact isConj_iff.mpr ⟨k, by rw [hk, hw]⟩
  have hpt : f * T.t * f⁻¹ ≠ T.t := by
    intro h
    apply hft
    calc f * T.t = f * T.t * f⁻¹ * f := by group
      _ = T.t * f := by rw [h]
  have hp't : b * S.z * b⁻¹ ≠ T.t := by
    intro h
    apply T.t_ne_z
    calc T.t = b⁻¹ * (b * T.t) := by group
      _ = b⁻¹ * (T.t * b) := by rw [hbt]
      _ = b⁻¹ * (b * S.z * b⁻¹) * b := by rw [h]; group
      _ = S.z := by group
  have hpcl' : S.cl (f * T.t * f⁻¹ * T.t) = T.l ![0, 1, 1] :=
    T.eq_of_F_fix_of_mem_commSpace hpcl (hne0 hpΩ hpt hpQ) (hFfix hpQ hpa)
  have hp'cl' : S.cl (b * S.z * b⁻¹ * T.t) = T.l ![0, 1, 1] :=
    T.eq_of_F_fix_of_mem_commSpace hp'cl (hne0 hp'Ω hp't hp'Q) (hFfix hp'Q hp'a)
  have hfM : f ∈ S.M := S.QG_le_M hfQ
  have hfz : f * S.z * f⁻¹ = S.z := by rw [S.z_comm hfM, mul_inv_cancel_right]
  have heq : b * S.z * b⁻¹ = f * T.t * f⁻¹ := by
    rcases (S.cl_eq_cl_iff hpQ hp'Q).mp (hpcl'.trans hp'cl'.symm) with h | h
    · exact mul_right_cancel h
    · exfalso
      apply T.not_isConj_zt
      have h1 : b * S.z * b⁻¹ = f * T.t * f⁻¹ * S.z := by
        calc b * S.z * b⁻¹ = b * S.z * b⁻¹ * T.t * T.t := by
              rw [mul_assoc _ T.t, T.t_mul_self, mul_one]
          _ = f * T.t * f⁻¹ * T.t * S.z * T.t := by rw [h]
          _ = f * T.t * f⁻¹ * (T.t * S.z * T.t) := by group
          _ = f * T.t * f⁻¹ * S.z := by
              rw [T.t_comm_z, mul_assoc S.z, T.t_mul_self, mul_one]
      have h2 : f * T.t * f⁻¹ * S.z = f * (T.t * S.z) * f⁻¹ := by
        calc f * T.t * f⁻¹ * S.z = f * T.t * f⁻¹ * (f * S.z * f⁻¹) := by rw [hfz]
          _ = f * (T.t * S.z) * f⁻¹ := by group
      refine (isConj_iff.mpr ⟨b, rfl⟩).trans ?_
      rw [h1, h2, T.t_comm_z]
      exact isConj_iff.mpr ⟨f⁻¹, by group⟩
  have hyz : (f * b) * S.z * (f * b)⁻¹ = T.t := by
    calc (f * b) * S.z * (f * b)⁻¹ = f * (b * S.z * b⁻¹) * f⁻¹ := by group
      _ = (f * f) * T.t * (f * f)⁻¹ := by rw [heq]; group
      _ = T.t := by rw [hff]; group
  have hyt : (f * b) * T.t * (f * b)⁻¹ = f * T.t * f⁻¹ := by
    calc (f * b) * T.t * (f * b)⁻¹ = f * (b * T.t * b⁻¹) * f⁻¹ := by group
      _ = f * T.t * f⁻¹ := by rw [show b * T.t * b⁻¹ = T.t by rw [hbt]; group]
  have hyp : (f * b) * (f * T.t * f⁻¹) * (f * b)⁻¹ = S.z := by
    calc (f * b) * (f * T.t * f⁻¹) * (f * b)⁻¹ = f * (b * (b * S.z * b⁻¹) * b⁻¹) * f⁻¹ := by
          rw [heq]; group
      _ = f * ((b * b) * S.z * (b * b)⁻¹) * f⁻¹ := by group
      _ = f * S.z * f⁻¹ := by rw [hbb, one_mul, inv_one, mul_one]
      _ = S.z := hfz
  have h3 : (f * b) ^ 3 * S.z = S.z * (f * b) ^ 3 := by
    have e : (f * b) ^ 3 * S.z * ((f * b) ^ 3)⁻¹ = S.z := by
      calc (f * b) ^ 3 * S.z * ((f * b) ^ 3)⁻¹ =
          (f * b) * ((f * b) * ((f * b) * S.z * (f * b)⁻¹) * (f * b)⁻¹) * (f * b)⁻¹ := by
            rw [pow_three]; group
        _ = S.z := by rw [hyz, hyt, hyp]
    calc (f * b) ^ 3 * S.z = (f * b) ^ 3 * S.z * ((f * b) ^ 3)⁻¹ * (f * b) ^ 3 := by group
      _ = S.z * (f * b) ^ 3 := by rw [e]
  have h1 : (f * b) * S.z ≠ S.z * (f * b) := by
    intro h
    apply T.t_ne_z
    rw [← hyz, h]
    group
  obtain ⟨n, hn⟩ := hP e T.xh b
    (by calc e * a = (a * e * a⁻¹) * a := by rw [hea]
          _ = a * e := by group)
    hax.symm hba hee T.hxh3 hcomm
  exact not_two_element hff hbb h3 h1 n hn

end IxBad

end CFSG.LargeExtraspecial.AS35QIx
