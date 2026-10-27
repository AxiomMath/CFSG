module

public import CFSG.Quasithin.H13.NQS1342
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1322

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem lemma13_4_2_three_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V)
    {v g₁ g₂ : G} (h₁ : v ∈ V.map (MulAut.conj g₁).toMonoidHom)
    (h₂ : v ∈ V.map (MulAut.conj g₂).toMonoidHom) :
    ∃ c ∈ centralizer ({v} : Set G),
      (V.map (MulAut.conj g₂).toMonoidHom).map (MulAut.conj c).toMonoidHom =
        V.map (MulAut.conj g₁).toMonoidHom := by
  obtain ⟨w₁, hw₁, rfl⟩ := h₁
  obtain ⟨w₂, hw₂, he⟩ := h₂
  have he' : g₂ * w₂ * g₂⁻¹ = g₁ * w₁ * g₁⁻¹ := he
  have hg : (g₁⁻¹ * g₂)⁻¹ * w₁ * (g₁⁻¹ * g₂) = w₂ := by
    calc (g₁⁻¹ * g₂)⁻¹ * w₁ * (g₁⁻¹ * g₂) = g₂⁻¹ * (g₁ * w₁ * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * w₂ * g₂⁻¹) * g₂ := by rw [he']
      _ = w₂ := by group
  obtain ⟨h, hh, hhw⟩ := S.lemma13_2_2_five_F4 h331 h1222 hw₁ hw₂ hg
  have hhV : h ∈ normalizer (V : Set G) := (sup_le S.frame.L_le S.frame.T_le) hh
  refine ⟨g₁ * h * g₂⁻¹, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    show g₁ * h * g₂⁻¹ * (MulAut.conj g₁ w₁) = (MulAut.conj g₁ w₁) * (g₁ * h * g₂⁻¹)
    rw [MulAut.conj_apply]
    have h3 : h * w₂ * h⁻¹ = w₁ := by rw [← hhw]; group
    calc g₁ * h * g₂⁻¹ * (g₁ * w₁ * g₁⁻¹) = g₁ * h * g₂⁻¹ * (g₂ * w₂ * g₂⁻¹) := by rw [he']
      _ = g₁ * (h * w₂ * h⁻¹) * h * g₂⁻¹ := by group
      _ = g₁ * w₁ * g₁⁻¹ * (g₁ * h * g₂⁻¹) := by rw [h3]; group
  · rw [map_conj_map_conj, show g₁ * h * g₂⁻¹ * g₂ = g₁ * h by group, ← map_conj_map_conj,
      map_conj_eq_of_mem hhV]

theorem centralizer_zV_le_F4 (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V) :
    centralizer ({S.zV} : Set G) ≤ normalizer (V : Set G) := by
  intro c hc
  refine S.normalizer_L_le_F4 h1222 (S.centralizer_ZV_le ?_)
  rw [mem_centralizer_iff]
  intro x hx
  rcases S.mem_ZV_iff.1 hx with rfl | rfl
  · simp
  · exact mem_centralizer_iff.mp hc _ (Set.mem_singleton _)

theorem eq_of_zV_mem_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V)
    {g : G} (hg : S.zV ∈ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  have h1 : S.zV ∈ V.map (MulAut.conj (1 : G)).toMonoidHom := by
    rw [map_conj_one]
    exact S.zV_mem_V
  obtain ⟨c, hc, hce⟩ := lemma13_4_2_three_F4 h331 h1222 S h1 hg
  have hcV := centralizer_zV_le_F4 h1222 S hc
  calc V.map (MulAut.conj g).toMonoidHom
      = ((V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom).map
          (MulAut.conj c⁻¹).toMonoidHom := by
        rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, one_mul]
    _ = V := by
        rw [hce, map_conj_one, map_conj_eq_of_mem (inv_mem hcV)]

end CFSG.Quasithin.H13.NQS134
