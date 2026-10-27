module

public import CFSG.Quasithin.H13.A6S1322
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1342
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting134

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting134 G T L V)
include S

theorem lemma13_2_2_five_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) {v w : G} (hv : v ∈ V)
    (hw : w ∈ V) {g : G} (hg : g⁻¹ * v * g = w) : ∃ h ∈ L ⊔ T, h⁻¹ * v * h = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hv1 : v = 1
  · subst hv1
    refine ⟨1, (L ⊔ T).one_mem, ?_⟩
    rw [← hg]
    group
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hv1
    have : v = g * 1 * g⁻¹ := by rw [← hg]; group
    rw [this]
    group
  obtain ⟨l₁, hl₁L, hl₁⟩ := S.exists_conj_mem_V1 hv hv1
  obtain ⟨l₂, hl₂L, hl₂⟩ := S.exists_conj_mem_V1 hw hw1

  let P : Sylow 2 G := IsPGroup.toSylow S.h13.sylow.1 S.h13.sylow.2
  have hPT : (P : Subgroup G) = T := rfl
  have hv' : l₁ * v * l₁⁻¹ ∈ Subgroup.centralizer (P : Set G) := (V1_le_center _ hl₁).2
  have hw' : l₂ * w * l₂⁻¹ ∈ Subgroup.centralizer (P : Set G) := (V1_le_center _ hl₂).2
  have hk : (l₁ * g * l₂⁻¹)⁻¹ * (l₁ * v * l₁⁻¹) * (l₁ * g * l₂⁻¹) = l₂ * w * l₂⁻¹ := by
    rw [← hg]
    group
  obtain ⟨n, hn, hn'⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P (l₁ * v * l₁⁻¹)
    (l₁ * g * l₂⁻¹) hv' (by rw [hk]; exact hw')
  rw [hk] at hn'

  have hnM : n ∈ Subgroup.normalizer (V : Set G) := by
    have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) :=
      (h331 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow).1 _ L S.uniqueM.1.1
        S.T_le_NL S.maximal Subgroup.le_normalizer S.fsu.quasisimple
    exact S.normalizer_L_le_F4 h1222 (hNT hn)
  obtain ⟨h, hh, hhv⟩ := S.exists_act_eq ⟨n⁻¹, (Subgroup.normalizer (V : Set G)).inv_mem hnM⟩
  have hv'V : l₁ * v * l₁⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl₁L) v).mp hv
  have h1 := hhv _ hv'V
  simp only [inv_inv] at h1
  refine ⟨l₁⁻¹ * h⁻¹ * l₂, ?_, ?_⟩
  · exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem (le_sup_left (a := L) hl₁L))
      ((L ⊔ T).inv_mem hh)) (le_sup_left (a := L) hl₂L)
  · have h2 : h * (l₁ * v * l₁⁻¹) * h⁻¹ = l₂ * w * l₂⁻¹ := by rw [← h1, hn']
    calc (l₁⁻¹ * h⁻¹ * l₂)⁻¹ * v * (l₁⁻¹ * h⁻¹ * l₂) =
        l₂⁻¹ * (h * (l₁ * v * l₁⁻¹) * h⁻¹) * l₂ := by group
      _ = l₂⁻¹ * (l₂ * w * l₂⁻¹) * l₂ := by rw [h2]
      _ = w := by group

end Setting134

end CFSG.Quasithin.H13.A6
