module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Thompson
public import CFSG.LargeExtraspecial.S4Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Swap

open CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement
open Thompson

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g x : G} {K Y : Subgroup S.O}

namespace Thompson

theorem exists_swap (T : ThompsonInput S g x K Y) (H : Hyp4 S g) :
    ∃ w ∈ centralizer ({x} : Set G),
      w * S.z * w⁻¹ = g * S.z * g⁻¹ ∧ w * (g * S.z * g⁻¹) * w⁻¹ = S.z := by
  set a : G := g * S.z * g⁻¹ with ha
  have haQ : a ∈ S.QG := H.conj_mem
  have hane : a ≠ S.z := H.conj_ne
  have ha1 : a ≠ 1 := S4.conj_z_ne_one S g
  have hx1 : x ≠ 1 := by
    intro h
    have ho := T.orderOf_eq
    rw [h, orderOf_one] at ho
    omega
  have hxa : x ≠ a := fun h => T.cl_ne (by rw [h])
  have hxaz : x ≠ a * S.z := fun h => T.cl_ne (by
    rw [h, S.cl_mul haQ S.z_mem_QG, S.cl_z, add_zero])
  obtain ⟨u, huQ, hux, hua⟩ :=
    S.exists_conj_eq_mul_z_of_commute haQ T.mem_QG ha1 hane hxa hxaz
  have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa H.conj_mem H.conj_ne
  have hza : S.z ≠ a := hane.symm
  have haz : a * S.z = S.z * a := S.z_comm (S.QG_le_M haQ)
  have hxza : x ≠ S.z * a := by
    rw [← haz]
    exact hxaz
  let T' : Setting G := S.conjBy g
  have hT'z : T'.z = a := rfl
  obtain ⟨y', hy'Qa, hy'x, hy'z⟩ :=
    T'.exists_conj_eq_mul_z_of_commute (t := S.z) (e := x) hzQa T.mem_Qa
      S.z_ne_one (by rw [hT'z]; exact hza) T.ne_z (by rw [hT'z]; exact hxza)
  have hy'z' : y' * S.z * y'⁻¹ = S.z * a := by
    have := hy'z
    rwa [hT'z] at this
  have hy'a : y' * a = a * y' := T'.z_comm_QG hy'Qa
  have hu_z : u * S.z = S.z * u := S.z_comm (S.QG_le_M huQ)
  have ha2 : a * a = 1 := by
    calc a * a = g * (S.z * S.z) * g⁻¹ := by rw [ha]; group
      _ = 1 := by rw [S.z_mul_z]; group
  let w : G := y' * u * y'
  have hwx : w * x = x * w := by
    dsimp only [w]
    calc y' * u * y' * x = y' * u * (y' * x) := by group
      _ = y' * u * (x * y') := by rw [hy'x]
      _ = y' * (u * x) * y' := by group
      _ = y' * (x * u) * y' := by rw [hux]
      _ = (y' * x) * u * y' := by group
      _ = (x * y') * u * y' := by rw [hy'x]
      _ = x * (y' * u * y') := by group
  have hu_z_inv : S.z * u⁻¹ = u⁻¹ * S.z :=
    ((show Commute u S.z from hu_z).symm.inv_right).eq
  have huas : u * (a * S.z) * u⁻¹ = (u * a * u⁻¹) * S.z := by
    calc u * (a * S.z) * u⁻¹ = u * a * (S.z * u⁻¹) := by group
      _ = u * a * (u⁻¹ * S.z) := by rw [hu_z_inv]
      _ = (u * a * u⁻¹) * S.z := by group
  have hzw : w * S.z * w⁻¹ = a := by
    dsimp only [w]
    calc (y' * u * y') * S.z * (y' * u * y')⁻¹
        = y' * u * y' * S.z * y'⁻¹ * u⁻¹ * y'⁻¹ := by group
      _ = y' * u * (y' * S.z * y'⁻¹) * u⁻¹ * y'⁻¹ := by group
      _ = y' * u * (S.z * a) * u⁻¹ * y'⁻¹ := by rw [hy'z']
      _ = y' * u * (a * S.z) * u⁻¹ * y'⁻¹ := by rw [← haz]
      _ = y' * (u * (a * S.z) * u⁻¹) * y'⁻¹ := by group
      _ = y' * ((u * a * u⁻¹) * S.z) * y'⁻¹ := by rw [huas]
      _ = y' * (a * S.z) * S.z * y'⁻¹ := by rw [hua]; group
      _ = y' * a * (S.z * S.z) * y'⁻¹ := by group
      _ = y' * a * y'⁻¹ := by rw [S.z_mul_z]; group
      _ = a := by rw [hy'a]; group
  have hwa : w * a * w⁻¹ = S.z := by
    dsimp only [w]
    calc (y' * u * y') * a * (y' * u * y')⁻¹
        = y' * u * y' * a * y'⁻¹ * u⁻¹ * y'⁻¹ := by group
      _ = y' * u * (y' * a * y'⁻¹) * u⁻¹ * y'⁻¹ := by group
      _ = y' * u * a * u⁻¹ * y'⁻¹ := by rw [hy'a]; group
      _ = y' * (u * a * u⁻¹) * y'⁻¹ := by group
      _ = y' * (a * S.z) * y'⁻¹ := by rw [hua]
      _ = (y' * a * y'⁻¹) * (y' * S.z * y'⁻¹) := by group
      _ = a * (S.z * a) := by rw [hy'a, hy'z']; group
      _ = S.z := by
        rw [show a * (S.z * a) = S.z * (a * a) by
          calc a * (S.z * a) = (a * S.z) * a := by group
            _ = (S.z * a) * a := by rw [haz]
            _ = S.z * (a * a) := by group]
        rw [ha2]; group
  exact ⟨w, mem_centralizer_singleton_iff.mpr hwx, by rw [ha]; exact hzw, by rw [ha]; exact hwa⟩


theorem clSub_inf_le (hchar : IsCharTwoType G) (T : ThompsonInput S g x K Y)
    (H : Hyp4 S g) (hw : S.width = 4) :
    S.clSub (Thompson.UCore S x) ⊓
        LinearMap.ker (S.q.polarBilin (S.cl (g * S.z * g⁻¹))) ≤
      S.clSub (S.QG ⊓ S.Qa g) := by
  set a : G := g * S.z * g⁻¹ with ha
  have haQ : a ∈ S.QG := H.conj_mem
  have hane : a ≠ S.z := H.conj_ne
  have ha1 : a ≠ 1 := S4.conj_z_ne_one S g
  obtain ⟨w, hwC, hwz, hwa⟩ := exists_swap T H
  have hQaw : S.Qa w = S.Qa g := S.Qa_eq_of_conj_eq hwz
  have hQmap : S.QG.map (MulAut.conj w).toMonoidHom = S.Qa g := by
    rw [← S.Qa_eq_map w, hQaw]
  have hconjwg : (w * g) * S.z * (w * g)⁻¹ = S.z := by
    calc (w * g) * S.z * (w * g)⁻¹ = w * a * w⁻¹ := by rw [ha]; group
      _ = S.z := hwa
  have hQamap : (S.Qa g).map (MulAut.conj w).toMonoidHom = S.QG := by
    have h := S.Qa_mul g w
    rw [S.Qa_eq_of_conj_eq (g := w * g) (h := 1) (by simpa using hconjwg), S.Qa_one] at h
    exact h.symm
  have hwainv : w⁻¹ * a * w = S.z := by
    dsimp [a]
    calc w⁻¹ * (g * S.z * g⁻¹) * w = w⁻¹ * (w * S.z * w⁻¹) * w := by rw [← hwz]
      _ = S.z := by group
  intro v hv
  obtain ⟨u, huU, huQ, hcl⟩ := S.mem_clSub_iff.mp hv.1
  have hphi : S.q.polarBilin (S.cl a) v = 0 := LinearMap.mem_ker.mp hv.2
  have hphi' : polar S.q v (S.cl a) = 0 := by
    rwa [QuadraticMap.polarBilin_apply_apply, polar_comm] at hphi
  have hpol : polar S.q (S.cl u) (S.cl a) = 0 := by
    rw [hcl]
    exact hphi'
  have hcomm_ua : u * a = a * u := (S.polar_cl_eq_zero_iff huQ haQ).mp hpol
  let u' : G := w⁻¹ * u * w
  have hwH : w ∈ centralizer ({x} : Set G) := hwC
  have hwnorm : w ∈ normalizer (Thompson.UCore S x : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hwH
  have hwinvn : w⁻¹ ∈ normalizer (Thompson.UCore S x : Set G) := inv_mem hwnorm
  have hu'U : u' ∈ Thompson.UCore S x := by
    have := (Subgroup.mem_normalizer_iff.mp hwinvn u).mp huU
    simpa [u'] using this
  have hu'z : u' * S.z * u'⁻¹ = S.z := by
    dsimp only [u']
    calc w⁻¹ * u * w * S.z * (w⁻¹ * u * w)⁻¹
        = w⁻¹ * u * (w * S.z * w⁻¹) * u⁻¹ * w := by group
      _ = w⁻¹ * u * a * u⁻¹ * w := by rw [hwz]
      _ = w⁻¹ * (u * a * u⁻¹) * w := by group
      _ = w⁻¹ * a * w := by rw [hcomm_ua]; group
      _ = S.z := hwainv
  have hu'M : u' ∈ S.M := by
    rw [S.mem_M_iff]
    calc u' * S.z = (u' * S.z * u'⁻¹) * u' := by group
      _ = S.z * u' := by rw [hu'z]
  have huMap : u ∈ (S.Qa g).map (MulAut.conj w).toMonoidHom := by
    rwa [hQamap]
  obtain ⟨q, hqQa, hqeq⟩ := Subgroup.mem_map.mp huMap
  have hu'eq : u' = q := by
    dsimp [u']
    rw [← hqeq]
    change w⁻¹ * (w * q * w⁻¹) * w = q
    group
  have hu'Qa : u' ∈ S.Qa g := by rw [hu'eq]; exact hqQa
  have hlL : S.ρ ⟨u', hu'M⟩ ∈ S.Lbar g :=
    Subgroup.mem_map.mpr ⟨⟨u', hu'M⟩, Subgroup.mem_subgroupOf.mpr ⟨hu'Qa, hu'M⟩, rfl⟩
  have hlW : S.ρ ⟨u', hu'M⟩ ∈ Thompson.Wbar S x :=
    Subgroup.mem_map.mpr ⟨⟨u', hu'M⟩,
      Subgroup.mem_subgroupOf.mpr ⟨hu'U, hu'M⟩, rfl⟩
  have hlcomm : ∀ k ∈ K, S.ρ ⟨u', hu'M⟩ * k = k * S.ρ ⟨u', hu'M⟩ :=
    fun k hk => Thompson.commute_Wbar_K T u' ⟨hu'U, hu'M⟩ k hk
  have hl1 : S.ρ ⟨u', hu'M⟩ = 1 := T.eq_one _ hlL hlcomm
  have hu'Q : u' ∈ S.QG := (S.ρ_eq_one_iff ⟨u', hu'M⟩).mp hl1
  have hu_eq : u = w * u' * w⁻¹ := by
    dsimp [u']
    group
  have huQa : u ∈ S.Qa g := by
    rw [← hQmap]
    exact Subgroup.mem_map.mpr ⟨u', hu'Q, hu_eq.symm⟩
  rw [← hcl]
  exact S.cl_mem_clSub ⟨huQ, huQa⟩ huQ



end Thompson

theorem false_of_thompsonInput {G : Type} [Group G] [Finite G] (hchar : IsCharTwoType G)
    {S : Setting G} {g : G} (H : S4.Hyp4 S g) (C : S4.Cons311 S g) (hw : S.width = 4)
    {x : G} {K Y : Subgroup S.O} (T : ThompsonInput S g x K Y) : False := by
  set a : G := g * S.z * g⁻¹ with ha
  have haQ : a ∈ S.QG := H.conj_mem
  have hane : a ≠ S.z := H.conj_ne
  have ha1 : a ≠ 1 := S4.conj_z_ne_one S g
  have hcla0 : S.cl a ≠ 0 := by
    intro h
    rcases (S.cl_eq_zero_iff haQ).mp h with h1 | h1
    · exact ha1 h1
    · exact hane h1
  have hφne : S.q.polarBilin (S.cl a) ≠ 0 := by
    intro h0
    apply hcla0
    refine S.q_nondegenerate.1 (S.cl a) fun v => ?_
    have hv := congrArg (fun f : S.Qt →ₗ[ZMod 2] ZMod 2 => f v) h0
    simpa [QuadraticMap.polarBilin_apply_apply] using hv
  have hdim8 : finrank (ZMod 2) S.Qt = 8 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hker : finrank (ZMod 2) (LinearMap.ker (S.q.polarBilin (S.cl a))) = 7 := by
    have hrange_ne : (S.q.polarBilin (S.cl a)).range ≠ ⊥ := by
      intro h
      exact hφne (LinearMap.range_eq_bot.mp h)
    have hrange_pos : 0 < finrank (ZMod 2) (S.q.polarBilin (S.cl a)).range :=
      (Submodule.one_le_finrank_iff).mpr hrange_ne
    have hrange_le : finrank (ZMod 2) (S.q.polarBilin (S.cl a)).range ≤ 1 := by
      have h := Submodule.finrank_le (S.q.polarBilin (S.cl a)).range
      simpa using h
    have hr : finrank (ZMod 2) (S.q.polarBilin (S.cl a)).range = 1 := by omega
    have hsum := LinearMap.finrank_range_add_finrank_ker (S.q.polarBilin (S.cl a))
    rw [hdim8] at hsum
    omega
  have h6 : 6 ≤ finrank (ZMod 2) (S.clSub (Thompson.UCore S x)) :=
    Thompson.six_le_finrank_clSub hchar T hw
  have hle : S.clSub (Thompson.UCore S x) ⊓
      LinearMap.ker (S.q.polarBilin (S.cl a)) ≤ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [ha]
    exact clSub_inf_le hchar T H hw
  have hsup : finrank (ZMod 2) ↥(S.clSub (Thompson.UCore S x) ⊔
      LinearMap.ker (S.q.polarBilin (S.cl a))) ≤ 8 := by
    rw [← hdim8]
    exact Submodule.finrank_le _
  have hA5 : 5 ≤ finrank (ZMod 2) ↥(S.clSub (Thompson.UCore S x) ⊓
      LinearMap.ker (S.q.polarBilin (S.cl a))) := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (S.clSub (Thompson.UCore S x)) (LinearMap.ker (S.q.polarBilin (S.cl a)))
    rw [hker] at hsum
    omega
  have hD4 : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = 4 := by
    have h := S4.finrank_clSub_QG_inf_Qa (S := S) (g := g) H.conj_mem H.conj_ne C.card_QG_inf_Qa
    simpa [hw] using h
  have hAle : finrank (ZMod 2) ↥(S.clSub (Thompson.UCore S x) ⊓
      LinearMap.ker (S.q.polarBilin (S.cl a))) ≤
      finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) :=
    Submodule.finrank_mono hle
  omega


end CFSG.GF2Type.Smith1979.W4Swap
