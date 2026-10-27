module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBTriv
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBCover
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBElem
public section
namespace CFSG.Quasithin.H13.GM22
open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin
variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
namespace BCtx_F4
variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)
include c in
theorem E_conj {t e : G} (ht : t ∈ T) (he : e ∈ Subgroup.centralizer (D : Set G) ⊓ CHU T L V) :
    t * e * t⁻¹ ∈ Subgroup.centralizer (D : Set G) ⊓ CHU T L V := by
  obtain ⟨heD, heC⟩ := Subgroup.mem_inf.mp he
  have htH : t ∈ HH T := T_le_HH T ht
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun d hd => ?_, ?_⟩
  · have hd' : t⁻¹ * d * t ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp
        (c.hk.kData.H_le_normalizer_D ((HH T).inv_mem htH)) d).mp hd
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp heD _ hd'
    calc d * (t * e * t⁻¹) = t * ((t⁻¹ * d * t) * e) * t⁻¹ := by group
      _ = t * (e * (t⁻¹ * d * t)) * t⁻¹ := by rw [h1]
      _ = (t * e * t⁻¹) * d := by group
  · exact (Subgroup.mem_normalizer_iff.mp (HH_le_normalizer_CHU c.h c.hZ htH) e).mp heC
include c in
theorem E_inf_V {x : G} (hx : x ∈ Subgroup.centralizer (D : Set G) ⊓ CHU T L V) (hxV : x ∈ V) :
    x ∈ quasithinOmegaOneCenter T := by
  obtain ⟨hxC, hxCHU⟩ := Subgroup.mem_inf.mp hx
  have hxD : x ∈ D := c.hk.kData.V0_le_D ⟨hxV, hxCHU⟩
  rw [← c.hk.kData.center_eq]
  exact ⟨hxD, hxC⟩
include c in
theorem caseB_one : IsElemAbelian 2 (Subgroup.centralizer (V : Set G)) ∧
    V.relIndex (Subgroup.centralizer (V : Set G)) ≤ 2 := by
  refine ⟨c.isElemAbelian_Q, relIndex_le_two_of_E (D := D)
    (E := Subgroup.centralizer (D : Set G) ⊓ CHU T L V) (Z := quasithinOmegaOneCenter T)
    (fun x hx y hy => c.Q_comm hx hy) c.hk.E_le_centralizer c.hk.centralizer_eq_mul
    (Z_le_V c.h c.hZ) (fun x hx hxV => c.E_inf_V hx hxV) c.hZ
    (fun t ht e he => c.E_conj ht he) (fun t ht q hq => c.N_comm_Q t (c.T_le_N ht) q hq)
    (fun p hp e he => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp he).1 p hp)
    (fun e he hc => ?_) (c.ρ.exists_cover c.h.sylow.1 c.T_le_N c.D_le_T
      (by rw [c.card_D, c.card_D_inf_Q]))⟩
  have heQ := c.hk.E_le_centralizer he
  have he2 : e ^ 2 = 1 := c.isElemAbelian_Q.2 e heQ
  exact Subgroup.subset_closure ⟨⟨c.Q_le_T heQ, Subgroup.mem_centralizer_iff.mpr hc⟩, he2⟩
end BCtx_F4
theorem m22CaseBOne_holds_F4 : M22CaseBOne_F4 := by
  intro G _ _ T M L V g D hl h hk
  obtain ⟨c⟩ := nonempty_bCtx_F4 hl h hk
  exact c.caseB_one
end CFSG.Quasithin.H13.GM22
