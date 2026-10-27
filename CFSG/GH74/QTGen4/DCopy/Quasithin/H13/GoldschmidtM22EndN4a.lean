module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN3a

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in

theorem normalizer_eq_sup_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1_F4)
    (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) :
    Subgroup.normalizer (V : Set G) = L ⊔ T := by
  refine le_antisymm ?_ (sup_le h.toHyp611.L_le_normalizer h.toHyp611.T_le_normalizer)
  intro n hn
  obtain ⟨z, hzZ, hz1, hZz⟩ := exists_gen_Z hZ
  have hzV : z ∈ V := Z_le_V h hZ hzZ
  have hnM : n ∈ M := (h621 G T M L V h).2 hn
  have hnzV : n * z * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hn z).mp hzV
  have hnz1 : n * z * n⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have := congrArg (fun y => n⁻¹ * y * n) h1
    simpa [mul_assoc] using this
  obtain ⟨l, hlL, hl⟩ := h.natural.exists_conj_eq hzV hnzV hz1 hnz1
  have hcomm : (l⁻¹ * n) * z = z * (l⁻¹ * n) := by
    have e : l⁻¹ * (n * z * n⁻¹) * l = z := by rw [← hl]; group
    calc (l⁻¹ * n) * z = (l⁻¹ * (n * z * n⁻¹) * l) * (l⁻¹ * n) := by group
      _ = z * (l⁻¹ * n) := by rw [e]
  have ht : l⁻¹ * n ∈ HH T := by
    rw [HH_eq_centralizer_of_gen hZz, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have htM : l⁻¹ * n ∈ M := M.mul_mem (M.inv_mem (h.L_le hlL)) hnM
  have htT : l⁻¹ * n ∈ T := by
    have : l⁻¹ * n ∈ HH T ⊓ M := ⟨ht, htM⟩
    rwa [P.HH_inf_M_eq_T_F4 h hZ h629 h6210 h6212] at this
  have e : n = l * (l⁻¹ * n) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hlL htT

include P h in

theorem centralizer_le_T_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1_F4)
    (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) :
    Subgroup.centralizer (V : Set G) ≤ T := by
  intro x hx
  have hxH : x ∈ HH T := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact Subgroup.mem_centralizer_iff.mp hx z (Z_le_V h hZ hz)
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hx
  have : x ∈ HH T ⊓ M := ⟨hxH, (h621 G T M L V h).2 hxN⟩
  rwa [P.HH_inf_M_eq_T_F4 h hZ h629 h6210 h6212] at this

end PsiData

end CFSG.Quasithin.H13.GM22
