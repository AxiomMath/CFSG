module

public import CFSG.LargeExtraspecial.S6EightD
public import CFSG.LargeExtraspecial.S10EightM

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Hyp10.exists_point_of_mem_clSub (X : Hyp10 S g t) {kd : S.M} {u : G}
    (hPa : S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hne : S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹))
    (hv : S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa u)) :
    ∃ c ∈ (S.QG ⊓ S.Qa g) ⊓ S.Qa u, (∃ w : G, c = w * S.z * w⁻¹) ∧
      S.cl c ≠ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨c, hc, hcQ, hcl⟩ := S.mem_clSub_iff.mp hv
  have hcg : c ∈ S.Qa g := X.mem_Qa_of_mem_clSub hcQ (hcl ▸ hPa)
  refine ⟨c, ⟨⟨hcQ, hcg⟩, hc.2⟩, ?_, by rw [hcl]; exact hne⟩
  have hkQ := conj_mem_QG' S kd.2 X.haQ
  rcases (S.cl_eq_cl_iff hkQ hcQ).mp hcl.symm with h | h
  · exact ⟨(kd : G) * g, h⟩
  · have hk1 : (kd : G) * g * S.z * ((kd : G) * g)⁻¹ ≠ 1 := conj_z_ne_one S _
    have hkz : (kd : G) * g * S.z * ((kd : G) * g)⁻¹ ≠ S.z := conj_ne_z' S kd.2 X.H.conj_ne
    obtain ⟨q, -, hq⟩ := S.exists_conj_eq_mul_z hkQ hk1 hkz
    refine ⟨q * ((kd : G) * g), ?_⟩
    rw [h, ← hq]
    group

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem mem_clSub_of_linCase (hF : S6.FusionCtl S g) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (hτ1 : τ ≠ 1) (hL : LinCase S g hτ.1) {τ' : S.M}
    (hτ' : S.ρ τ' = τ) {u : G} (hτu : (τ' : G) = u * S.z * u⁻¹)
    (haQt : g * S.z * g⁻¹ ∈ S.Qa u) {kd : S.M} (hkd : S.ρ kd ∈ ⁅Yb, Yb⁆) :
    S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa u) := by
  have h68 := timmesfeld_6_8 X.H X.hNo X.C hF hτ1 hL hτ' hτu haQt
  have hkdR := D.Yb_le_Rbar hτ ((D.dec.mem_commutator_iff).mp hkd).1
  have hmem := apply_mem_Vt_of_mem_Rbar X.haQ hkdR (cl_a_mem_Vt hτ.1)
  rw [ρ_cl_conj_z S kd X.haQ] at hmem
  exact h68 hmem

end Dec108

end CFSG.LargeExtraspecial.S10
