module

public import CFSG.GH74.GLS.LU.Local.FiveL66n
public import CFSG.GH74.GLS.LU.Local.FiveL66h
public import CFSG.GH74.GLS.LU.Local.FiveL66k
public import CFSG.GH74.GLS.LU.Local.FiveL83

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section TNormL

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

theorem FiveCtx.t_normL (c : FiveCtx G p f z S K₁ K₂ t u) :
    ∀ g : G, g * z * g⁻¹ = u →
      cjL t (cjL g K₁) = cjL g K₁ ∧ cjL t (cjL g K₂) = cjL g K₂ := by
  intro g hg
  have hh₀ : g⁻¹⁻¹ * z * g⁻¹ = u := by simpa using hg
  have hcu := comps_u c.toLUCtx hh₀
  have ht1 := t_norm_L c.toLUCtx hh₀
  have htC : t ∈ Cz u := Subgroup.mem_centralizer_singleton_iff.mpr c.hs.ut.symm
  have e₁ : cj K₁ g⁻¹ = cjL g K₁ := by simp only [cj, inv_inv]
  have e₂ : cj K₂ g⁻¹ = cjL g K₂ := by simp only [cj, inv_inv]
  rw [e₁] at ht1 hcu
  rw [e₂] at hcu
  have hn1 : cjL t (cjL g K₁) = cjL g K₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp ht1
  refine ⟨hn1, ?_⟩
  rcases hcu.perm htC with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd (hn1.symm.trans h1) hcu.ne

end TNormL

section Leaves

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

theorem leaf66_of_model
    (hB : FiveModelBaseLeaf) (hM : FiveModelLeaf) : Leaf66 := by
  intro G _ _ p f z S K₁ K₂ t u c
  obtain ⟨Gs, _, z', S', K₁', K₂', t', u', ψ, pic⟩ := exists_model_pic hB hM c
  obtain ⟨H, w₁, b66⟩ := pic.five66W c.hs.zt_comm c.hs.ut c.t_normL
  obtain ⟨X₁, b82⟩ := pic.exists_five82W c b66
  obtain ⟨Y, b83⟩ := exists_Y83W c b66 b82
  obtain ⟨x, hxz, hxu⟩ := c.exists_x
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hNH := pic.N_normH c b66 b82 b83
  obtain ⟨hn, φ⟩ := pic.N_quot c b66 hNH hxz hxu
  obtain ⟨φ⟩ := φ
  have hord := pic.N_ord c b66 hxz hxu φ
  have htrans := N_trans_of hz2 hu2 hzu (x_mem_NN hz2 hu2 hzu hxz hxu) hxz hxu
  exact ⟨H, w₁, Five66.ofWN b66 ⟨hNH, ⟨hn, ⟨φ⟩⟩, htrans, hord⟩⟩

theorem leaf82_of_model (hB : FiveModelBaseLeaf) (hM : FiveModelLeaf) : Leaf82 := by
  intro G _ _ p f z S K₁ K₂ t u c H w₁ b66
  obtain ⟨Gs, _, z', S', K₁', K₂', t', u', ψ, pic⟩ := exists_model_pic hB hM c
  obtain ⟨X₁, b82⟩ := pic.exists_five82W c b66.toW
  obtain ⟨x, hxz, hxu⟩ := c.exists_x
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hno := pic.no_inv_sub c b66.toW (x_mem_NN hz2 hu2 hzu hxz hxu) hxz hxu b66.N_normH
  exact ⟨X₁, Five82.ofWN b82 ⟨hno⟩⟩

end Leaves

end CFSG.GH74.GLS.LU.Local.Five
