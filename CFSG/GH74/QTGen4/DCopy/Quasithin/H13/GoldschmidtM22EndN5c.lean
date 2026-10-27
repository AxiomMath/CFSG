module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN5c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN5a

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in

theorem card_CHU_of_caseA_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9_F4)
    (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) (hT : Nat.card ↥T = 128) :
    Nat.card ↥(CHU T L V) = 64 := by
  have := P.card_T_F4 h hZ h629 h6210 h6212
  omega

end PsiData

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (P : PsiData T L V 3)

include hk P h in

theorem index_K_of_caseA_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9_F4)
    (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) (hT : Nat.card ↥T = 128) :
    ((V ⊔ conjSubgroup V g).subgroupOf (HH T)).index = 2 := by
  have hCHU := P.card_CHU_of_caseA_F4 h hZ h629 h6210 h6212 hT
  have h1 := Subgroup.relIndex_mul_card (H := V ⊔ conjSubgroup V g) (K := HH T)
  rw [inf_eq_left.mpr hk.K_le_HH, hk.card_K, Subgroup.relIndex, P.card_HH, hCHU] at h1
  omega

include hk P h in

theorem exists_hom_S3_Z2_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9_F4)
    (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) (hT : Nat.card ↥T = 128) :
    ∃ φ : ↥(HH T) →* Equiv.Perm (Fin 3) × Multiplicative (ZMod 2), Function.Surjective φ ∧
      φ.ker = D.subgroupOf (HH T) := by
  obtain ⟨l, hl⟩ := exists_hom_zmod_two _ (hk.index_K_of_caseA_F4 h P hZ h629 h6210 h6212 hT)
  have hker : (P.ψ.prod l).ker = D.subgroupOf (HH T) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Prod.ext_iff]
    simp only [MonoidHom.prod_apply, Prod.fst_one, Prod.snd_one]
    have h1 : P.ψ x = 1 ↔ (x : G) ∈ CHU T L V := P.ker x
    have h2 : l x = 1 ↔ (x : G) ∈ V ⊔ conjSubgroup V g := by
      rw [← MonoidHom.mem_ker, hl, Subgroup.mem_subgroupOf]
    rw [h1, h2, hk.D_eq, Subgroup.mem_inf, and_comm]
  refine ⟨P.ψ.prod l, ?_, hker⟩
  have hD32 : Nat.card ↥D = 32 := by
    rw [hk.extra.2.1]
    norm_num
  have hCHU := P.card_CHU_of_caseA_F4 h hZ h629 h6210 h6212 hT
  have hcard : Nat.card ↥(P.ψ.prod l).range =
      Nat.card (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) := by
    have h1 := Subgroup.card_ker_mul_card_range (P.ψ.prod l)
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hk.D_le_HH).toEquiv, hD32, P.card_HH,
      hCHU] at h1
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [Nat.card_prod, card_perm_fin_three, h2]
    omega
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ hcard)

end KData

end CFSG.Quasithin.H13.GM22
