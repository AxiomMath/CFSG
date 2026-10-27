module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN2b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN2c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN3a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN4c

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (P : PsiData T L V 3) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

include hk P h hZ in

theorem exists_a_noncomm_F4 (h6210 : Stmt6_2_10_F4) :
    ∃ a : ↥(HH T), (a : G) ∈ V ∧ (a : G) ∉ CHU T L V ∧
      P.ψ ⟨g, hk.g_mem⟩ * P.ψ a ≠ P.ψ a * P.ψ ⟨g, hk.g_mem⟩ := by
  obtain ⟨a, haV, haC⟩ := PsiData.exists_a_F4 h hZ h6210
  exact ⟨a, haV, haC, fun hc => hk.g_not_mem (((P.swap_norm a haV haC).2 ⟨g, hk.g_mem⟩).mpr hc)⟩

include hk P h hZ in

theorem conj_inf_normalizer_le_CHU_F4 (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) :
    conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤ CHU T L V := by
  obtain ⟨a, haV, haC, hg⟩ := exists_a_noncomm_F4 hk h P hZ h6210
  obtain ⟨hτ, hNa⟩ := P.swap_norm a haV haC
  have hτ2 : (P.ψ a).support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hτ
  intro x hx
  obtain ⟨hxVg, hxN⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ HH T := hk.K_le_HH (Subgroup.mem_sup_right hxVg)
  have hv : g * x * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp hxVg
  have hvH : g * x * g⁻¹ ∈ HH T := V_le_HH h hZ hv
  have hxx : (⟨x, hxH⟩ : ↥(HH T)) = (⟨g, hk.g_mem⟩ : ↥(HH T))⁻¹ * ⟨g * x * g⁻¹, hvH⟩ *
      ⟨g, hk.g_mem⟩ := by
    apply Subtype.ext
    simp [mul_assoc]
  have hψ : P.ψ ⟨x, hxH⟩ = (P.ψ ⟨g, hk.g_mem⟩)⁻¹ * P.ψ ⟨g * x * g⁻¹, hvH⟩ * P.ψ ⟨g, hk.g_mem⟩ := by
    rw [hxx, map_mul, map_mul, map_inv]
  rcases P.mem_V_F4 h h6211 a ⟨g * x * g⁻¹, hvH⟩ haV haC hv with h1 | h1
  · have : P.ψ ⟨x, hxH⟩ = 1 := by rw [hψ, h1]; group
    exact (P.ker _).mp this
  · exfalso
    have hcomm : P.ψ ⟨x, hxH⟩ * P.ψ a = P.ψ a * P.ψ ⟨x, hxH⟩ := (hNa ⟨x, hxH⟩).mp hxN
    rw [hψ, h1] at hcomm
    exact (perm3_noncomm_conj _ _ hτ2 hg).1 hcomm

include hk P h hZ in

theorem conj_inf_normalizer_eq_F4 (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) :
    conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) = conjSubgroup V g ⊓ CHU T L V :=
  le_antisymm (le_inf inf_le_left (conj_inf_normalizer_le_CHU_F4 hk h P hZ h6210 h6211))
    (inf_le_inf_left _ (CHU_le_normalizer_V_F4 h h6210))

include hk P h hZ in

theorem V1_inf_centralizer_F4 (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) :
    conjSubgroup V g ⊓ CHU T L V ⊓ Subgroup.centralizer (V : Set G) =
      quasithinOmegaOneCenter T := by
  have hA := conj_inf_normalizer_eq_F4 hk h P hZ h6210 h6211
  have h4 := hk.case2.relIndex_four
  rw [hA] at h4
  have h1 := Subgroup.relIndex_mul_card
    (H := conjSubgroup V g ⊓ CHU T L V ⊓ Subgroup.centralizer (V : Set G))
    (K := conjSubgroup V g ⊓ CHU T L V)
  rw [inf_eq_left.mpr (inf_le_left : conjSubgroup V g ⊓ CHU T L V ⊓
    Subgroup.centralizer (V : Set G) ≤ conjSubgroup V g ⊓ CHU T L V), h4,
    hk.card_V1_F4 h hZ h6211] at h1
  have hc : Nat.card ↥(conjSubgroup V g ⊓ CHU T L V ⊓ Subgroup.centralizer (V : Set G)) = 2 := by
    omega
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (V : Set G) :=
    fun z hz => Subgroup.mem_centralizer_iff.mpr fun v hv =>
      B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hv (Z_le_V h hZ hz)
  refine (Subgroup.eq_of_le_of_card_ge (le_inf ?_ hZC) (by rw [hc, hZ])).symm
  exact (hk.V0_inf_V1 h hZ).symm.le.trans inf_le_right

include hk P h hZ in

theorem D_inf_centralizer_le_F4 (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) :
    D ⊓ Subgroup.centralizer (V : Set G) ≤ V ⊓ CHU T L V := by
  intro d hd
  obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
  obtain ⟨u, hu, w, hw, rfl⟩ := hk.exists_mul_V0_V1_F4 h hZ h6211 d hdD
  have huC : u ∈ Subgroup.centralizer (V : Set G) :=
    V_le_centralizer_V h (Subgroup.mem_inf.mp hu).1
  have hwC : w ∈ Subgroup.centralizer (V : Set G) := by
    have := (Subgroup.centralizer (V : Set G)).mul_mem
      ((Subgroup.centralizer (V : Set G)).inv_mem huC) hdC
    simpa using this
  have hwZ : w ∈ quasithinOmegaOneCenter T := by
    rw [← V1_inf_centralizer_F4 hk h P hZ h6210 h6211]
    exact ⟨hw, hwC⟩
  exact (V ⊓ CHU T L V).mul_mem hu (hk.Z_le_V0 h hZ hwZ)

include hk h hZ in

theorem exists_conj_V1_F4 (h621 : Stmt6_2_1_F4) : ∃ k ∈ V ⊔ conjSubgroup V g,
    conjSubgroup V g ⊓ CHU T L V = conjSubgroup (V ⊓ CHU T L V) k := by
  obtain ⟨k, hkK, c, hc, hgkc⟩ := hk.H_eq g hk.g_mem
  have hkH : k ∈ HH T := hk.K_le_HH hkK
  refine ⟨k, hkK, ?_⟩
  have h1 : conjSubgroup V g = conjSubgroup V k := by
    rw [hgkc, ← conjSubgroup_conjSubgroup]
    exact conjSubgroup_eq_iff_mem_normalizer.mpr (CHU_le_normalizer_conj_V_F4 h hZ h621 hkH hc)
  rw [h1, CFSG.QuasithinUnique.C5.conjSubgroup_inf,
    conjSubgroup_eq_iff_mem_normalizer.mpr (HH_le_normalizer_CHU h hZ hkH)]

end KData

end CFSG.Quasithin.H13.GM22
