module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NCx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NMH

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

private theorem conjSub_inv_le_centralizer {G : Type} [Group G] {a t x : G}
    (ha : a * t * a⁻¹ = x) {E : Subgroup G} (hE : IsElemAbelian 2 E) (hxE : x ∈ E) :
    conjSub a⁻¹ E ≤ centralizer ({t} : Set G) := by
  intro z hz
  rw [mem_conjSub_iff'] at hz
  obtain ⟨e, heE, rfl⟩ := hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [inv_inv]
  haveI : IsMulCommutative ↥E := hE.1
  have hcomm : Commute e x := by
    exact congrArg Subtype.val (mul_comm' (⟨e, heE⟩ : E) (⟨x, hxE⟩ : E))
  have hconj : Commute (a⁻¹ * e * a) (a⁻¹ * x * a) := by
    simpa only [inv_inv] using hcomm.conj a⁻¹
  have hxa : a⁻¹ * x * a = t := by rw [← ha]; group
  rw [hxa] at hconj
  exact hconj.eq

theorem sec7nt3_of (hB : Sec3Inputs) : Sec7NT3 := by
  intro G _ _ L hS hL c h5 h7 hRT L1 P1 P0 hcfg _hsyl x hx hxP0
  obtain ⟨a, ha⟩ := isConj_iff.mp hx
  have ht2 : c.s.t ^ 2 = 1 := by
    rw [← c.s.t_order]
    exact pow_orderOf_eq_one _
  have hx2 : x ^ 2 = 1 := by
    rw [← ha, pow_two]
    calc (a * c.s.t * a⁻¹) * (a * c.s.t * a⁻¹)
        = a * (c.s.t * c.s.t) * a⁻¹ := by group
      _ = 1 := by rw [← pow_two, ht2]; simp
  obtain ⟨E, hEP0, hEea, hE64, hxE⟩ :=
    y7n_elemCover_P0 hB hS hL c h5 h7 hRT hcfg x hxP0 hx2
  have hle : conjSub a⁻¹ E ≤ centralizer ({c.s.t} : Set G) :=
    conjSub_inv_le_centralizer ha hEea hxE
  have hE'ea : IsElemAbelian 2 (conjSub a⁻¹ E) := hEea.map _
  have hcard : Nat.card (conjSub a⁻¹ E) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) (f := (MulAut.conj a⁻¹).toMonoidHom)
      (MulAut.conj a⁻¹).injective
  have h32 := y7n_mH_le (s := c.s) (e := c.e) (f33hyp_of hB hS hL c.s c.e).hDef hRT
    (conjSub a⁻¹ E) hle hE'ea
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
