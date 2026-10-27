module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddTI
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem isTISetUnder_top_of_Mp_F4 (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first_F4)
    (hMp : IsTISetUnder (quasithinOmegaOneCenter T ⊓ V)
      (Subgroup.normalizer (oTwoUpper H : Set G))) :
    IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤ := by
  set Z₁ := quasithinOmegaOneCenter T ⊓ V with hZ₁
  have hCz := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.2
  intro g _ hgN
  by_contra hne
  have hne' : Z₁ ⊓ conjSub g⁻¹ Z₁ ≠ ⊥ := hne
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz₀ : g * z * g⁻¹ ∈ Z₁ := by
    have := mem_conjSub.mp hz.2
    simpa using this
  have hz₀1 : g * z * g⁻¹ ≠ 1 := fun h => hz1' (by
    have e : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [e, h]
    group)
  obtain ⟨d, hdD, hd⟩ := s.exists_conj_eq_of_mem_Z₁ hI hF hz₀ hz₀1 hz.1 hz1'

  have hdg : d * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc d * g * z = (d * (g * z * g⁻¹) * d⁻¹) * (d * g) := by group
      _ = z * (d * g) := by rw [hd]
  have hdgM := hCz z hz.1.1 hz1' hdg

  have hdgN : d * g ∈ Subgroup.normalizer (Z₁ : Set G) := by
    by_contra hn
    have hbot := hMp (d * g) hdgM hn
    have hmem : z ∈ Z₁ ⊓ CFSG.conjugate Z₁ (d * g) := by
      refine ⟨hz.1, ?_⟩
      show z ∈ conjSub (d * g)⁻¹ Z₁
      rw [mem_conjSub, inv_inv]
      have hc : d * g * z * (d * g)⁻¹ = z := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hdg, mul_inv_cancel_right]
      rw [hc]
      exact hz.1
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hz1' hmem
  apply hgN
  have hdN : d ∈ Subgroup.normalizer (Z₁ : Set G) := s.D_le_normalizer_Z₁ hI hdD
  have e : g = d⁻¹ * (d * g) := by group
  rw [e]
  exact Subgroup.mul_mem _ (inv_mem hdN) hdgN

end Setup5_1_17Odd

end CFSG.Quasithin.H13
