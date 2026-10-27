module

public import CFSG.Quasithin.H13.A5V1367d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem exists_normalizer_thompsonJ_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {x : MulAut ↥S.Uv}
    (hxG : x ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hxN : x ∈ Subgroup.normalizer ((autOn S.Tv S.Uv ⊓ S.JGv : Subgroup (MulAut ↥S.Uv)) :
      Set (MulAut ↥S.Uv))) :
    ∃ (y : G) (hy : y ∈ Subgroup.centralizer ({S.v12} : Set G)),
      y ∈ Subgroup.normalizer (thompsonJ S.Tv : Set G) ∧
      ∃ r ∈ autOn S.Tv S.Uv ⊓ S.JGv, conjAct S.Uv ⟨y, S.Gv_le_normalizer_Uv hy⟩ = r * x := by
  set Q : Subgroup (MulAut ↥S.Uv) := autOn S.Tv S.Uv ⊓ S.JGv with hQ
  set Y := S.preGv (Subgroup.normalizer (Q : Set (MulAut ↥S.Uv))) with hY
  set X := S.preGv Q with hX
  have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
  have hGU := S.Gv_le_normalizer_Uv
  have hXY : X ≤ Y := fun g hg => by
    obtain ⟨hg, hq⟩ := S.mem_preGv.1 hg
    exact S.mem_preGv.2 ⟨hg, Subgroup.le_normalizer hq⟩
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    have key : ∀ k ∈ Y, ∀ g ∈ X, k * g * k⁻¹ ∈ X := by
      intro k hk g hg
      obtain ⟨hkG, hkq⟩ := S.mem_preGv.1 hk
      obtain ⟨hgG, hgq⟩ := S.mem_preGv.1 hg
      have hm : k * g * k⁻¹ ∈ Subgroup.centralizer ({S.v12} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hkG hgG) (Subgroup.inv_mem _ hkG)
      refine S.mem_preGv.2 ⟨hm, ?_⟩
      rw [show (⟨k * g * k⁻¹, hGU hm⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) =
        ⟨k, hGU hkG⟩ * ⟨g, hGU hgG⟩ * (⟨k, hGU hkG⟩)⁻¹ from rfl, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hkq _).mp hgq
    intro y hy
    refine B6.mem_normalizer_of_forall_mem (key y hy) fun g hg => ?_
    have := key y⁻¹ (Y.inv_mem hy) g hg
    rwa [inv_inv] at this
  have hTY : S.Tv ≤ Y := by
    intro t ht
    have htG := S.Tv_le_Gv ht
    refine S.mem_preGv.2 ⟨htG, ?_⟩
    have hts : conjAct S.Uv ⟨t, hGU htG⟩ ∈ autOn S.Tv S.Uv :=
      Setup.mem_autOn_iff.2 ⟨⟨t, hGU htG⟩, ht, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hQ, Subgroup.mem_inf, Subgroup.mem_inf,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hts) q),
      (Subgroup.mem_normalizer_iff.mp (S.GvS_le_normalizer_JGv (S.autOn_le_GvS S.Tv_le_Gv hts))
        q)]
  have hTY' : IsSylowTwoOf S.Tv Y := B6.isSylowTwoOf_mono hsyl hTY inf_le_right
  have hJX : thompsonJ S.Tv ≤ X := by
    intro j hj
    have hjT : j ∈ S.Tv := B6.thompsonJ_le S.Tv hj
    have hjG := S.Tv_le_Gv hjT
    refine S.mem_preGv.2 ⟨hjG, ?_, ?_⟩
    · exact Setup.mem_autOn_iff.2 ⟨⟨j, hGU hjG⟩, hjT, rfl⟩
    · exact S.autOn_thompsonJ_le_JGv (Setup.mem_autOn_iff.2 ⟨⟨j, hGU hjG⟩, hj, rfl⟩)
  have hTX : IsSylowTwoOf (S.Tv ⊓ X) X := B6.isSylowTwoOf_inf_normal hTY' hXY hYX
  obtain ⟨⟨g, hgN⟩, hgG, rfl⟩ := Setup.mem_autOn_iff.1 hxG
  have hgY : g ∈ Y := S.mem_preGv.2 ⟨hgG, hxN⟩
  obtain ⟨n, hnX, k, ⟨hkY, hkN⟩, hgnk⟩ := exists_mul_normalizer_of_sylow hXY hYX hTX hgY
  have hJ : thompsonJ (S.Tv ⊓ X) = thompsonJ S.Tv :=
    B6.thompsonJ_eq_of_le (le_inf (B6.thompsonJ_le S.Tv) hJX) inf_le_left
  have hkJ : k ∈ Subgroup.normalizer (thompsonJ S.Tv : Set G) := by
    rw [← hJ]
    exact normalizer_le_normalizer_thompsonJ _ hkN
  obtain ⟨hkG, -⟩ := S.mem_preGv.1 hkY
  obtain ⟨hnG, hnq⟩ := S.mem_preGv.1 hnX
  refine ⟨k, hkG, hkJ, (conjAct S.Uv ⟨n, hGU hnG⟩)⁻¹, Q.inv_mem hnq, ?_⟩
  have e : (⟨k, hGU hkG⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) =
      (⟨n, hGU hnG⟩)⁻¹ * ⟨g, hgN⟩ := Subtype.ext (by
    show k = n⁻¹ * g
    rw [hgnk, inv_mul_cancel_left])
  rw [e, map_mul, map_inv]

theorem exists_normalizer_baum_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {y : G} (hyG : y ∈ Subgroup.centralizer ({S.v12} : Set G))
    (hyJ : y ∈ Subgroup.normalizer (thompsonJ S.Tv : Set G)) :
    ∃ c ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ S.Tv) : Set G),
      ∃ k ∈ Subgroup.centralizer ({S.v12} : Set G) ⊓ Subgroup.normalizer (baum S.Tv : Set G),
        y = c * k := by
  set E := omegaOneCenterOf (thompsonJ S.Tv) with hE
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  set H := Gv ⊓ Subgroup.normalizer (E : Set G) with hH
  set N := Gv ⊓ Subgroup.centralizer (E : Set G) with hN
  have hNH : N ≤ H := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    have key : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N := by
      intro h hh x hx
      refine Subgroup.mem_inf.mpr
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh.1 hx.1) (Subgroup.inv_mem _ hh.1), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : h⁻¹ * e * h ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh.2) e).mp he
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ he'
      calc e * (h * x * h⁻¹) = h * ((h⁻¹ * e * h) * x) * h⁻¹ := by group
        _ = h * (x * (h⁻¹ * e * h)) * h⁻¹ := by rw [hc]
        _ = h * x * h⁻¹ * e := by group
    intro h hh
    refine B6.mem_normalizer_of_forall_mem (key h hh) fun x hx => ?_
    have := key h⁻¹ (H.inv_mem hh) x hx
    rwa [inv_inv] at this
  have hTH : S.Tv ≤ H := le_inf S.Tv_le_Gv
    ((B6.le_normalizer_thompsonJ S.Tv).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _))
  have hTH' : IsSylowTwoOf S.Tv H :=
    B6.isSylowTwoOf_mono (S.isSylowTwoOf_Tv_F4 h1222 h517) hTH inf_le_left
  have hTN := B6.isSylowTwoOf_inf_normal hTH' hNH hHN
  have hyH : y ∈ H := ⟨hyG, A4.normalizer_le_normalizer_omegaOneCenterOf _ hyJ⟩
  obtain ⟨c, hcN, k, ⟨hkH, hkS⟩, rfl⟩ := exists_mul_normalizer_of_sylow hNH hHN hTN hyH
  have hTv : S.Tv ⊓ N = baum S.Tv := by
    rw [hN, baum, ← inf_assoc, inf_eq_left.mpr S.Tv_le_Gv]
  rw [hTv] at hkS
  exact ⟨c, hcN.2, k, ⟨hkH.1, hkS⟩, rfl⟩

end Setting

end CFSG.Quasithin.H13.A5
