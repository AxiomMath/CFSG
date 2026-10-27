module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Final
public import CFSG.GH74.GLS.Stage1.Main.BrPairStd4
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.GLS.Stage1.Main.BrFusedModel
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81AB
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Abs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81AbsCfg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81ModelCfg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Num
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Rig
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Top

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm3.Sec8 Fin81

open CFSG.GH74.GLS.Stage1.Main in
theorem final81b_thm (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h44 : II4_44) : Final81b := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7 hC E₁ E₂ hE hSg
  have hfused := hs.fused
  obtain ⟨F, hFf, hFfin, p, f, hp, hp2, hf0, hpf, hmod, h5, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    hs.exists_numbers hII hq hrec h44 hP8 hS7
  obtain ⟨eM⟩ := hs.stageA_equiv hII hq hrec hP8 hS7 hSg
  obtain ⟨Gs, iG, fG, hL, S₀, ⟨eM'⟩⟩ := exists_model_sylow_M128 hp hp2 hf0 hmod h5
  refine ⟨Gs, iG, fG, p, f, hp, hp2, hL, ⟨S₀, ⟨eM.symm.trans eM'⟩⟩, ?_⟩
  intro z' S' hz'ci S'' ⟨eS⟩ hSS'
  have hoddF : Odd (Nat.card F) := by rw [hpf]; exact (hp.odd_of_ne_two hp2).pow
  have hmodF : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by rw [hpf]; exact hmod
  have h5F : 5 ≤ Nat.card F := by rw [hpf]; exact h5
  have hbarcfg := hs.fusedCfg_bar hII hq hrec h44 hP8 hS7
    (e₁.trans (specialLinearGroupEquivStatedSL 2 F).symm)
    (e₂.trans (specialLinearGroupEquivStatedSL 2 F).symm) hoddF hmodF
  have hres : layerSBar z S = imgBar z K₁ ⊔ imgBar z K₂ ⊔ imgBar z S := by
    show layer (CentralizerBar z) ⊔ imgBar z S = _
    rw [layer_eq_imgBar_of_hQ hII hfused.std hfused.hQ]
  obtain ⟨eSbar⟩ := hfused.nonempty_equiv_imgBar hII
  have hz'ord : orderOf z' = 2 := hz'ci.1
  have hz'C : z' ∈ centralizer ({z'} : Set Gs) := mem_centralizer_singleton_iff.2 rfl
  have hcen : (⟨z', hz'C⟩ : ↥(centralizer ({z'} : Set Gs))) ∈
      Subgroup.center ↥(centralizer ({z'} : Set Gs)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hzS' : (⟨z', hz'C⟩ : ↥(centralizer ({z'} : Set Gs))) ∈ (S' : Subgroup ↥(centralizer ({z'} : Set Gs))) :=
    central_mem_sylow S' hcen ((Subgroup.orderOf_coe _).symm.trans hz'ord)
  have hz'S'' : z' ∈ (S'' : Subgroup Gs) := by
    rw [hSS']
    exact ⟨⟨z', hz'C⟩, hzS', rfl⟩
  have hS''C : ∀ x ∈ (S'' : Subgroup Gs), z' * x = x * z' := by
    intro x hx
    rw [hSS'] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact (mem_centralizer_singleton_iff.1 y.2).symm
  have hz1 : z' ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz'ord; omega
  have hcenS'' := central_eq_of_equiv_M128 (eM.trans eS) (z := (⟨z', hz'S''⟩ : ↥(S'' : Subgroup Gs)))
    (fun h1 => hz1 (congrArg Subtype.val h1)) (fun s => Subtype.ext (hS''C s s.2).symm)
  have hz'c : (center ↥(S'' : Subgroup Gs)).map (S'' : Subgroup Gs).subtype = zpowers z' := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      rcases hcenS'' y (fun s => (Subgroup.mem_center_iff.1 hy) s) with h1 | h1
      · rw [h1]; exact (zpowers z').one_mem
      · rw [h1]; exact Subgroup.mem_zpowers z'
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨z', hz'S''⟩, ?_, rfl⟩
      show _ ∈ Subgroup.center ↥(S'' : Subgroup Gs)
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (hS''C s s.2).symm
  have hpkg : ∃ (E₁' E₂' : Subgroup Gs) (t' u' n' : Gs) (ε : ℤ), FusedPkg Gs (p ^ f) ε z' S'' E₁' E₂' t' u' n' := by
    rcases hL with ⟨h8, hLie⟩ | ⟨h8, -, hLie⟩
    · obtain ⟨E₁', E₂', t', u', n', hk⟩ := (fusedModelLeaf Gs p f hp hp2 h5 S'' z' hz'c).1 ⟨h8, hLie⟩
      exact ⟨E₁', E₂', t', u', n', 1, hk⟩
    · obtain ⟨E₁', E₂', t', u', n', hk⟩ := (fusedModelLeaf Gs p f hp hp2 h5 S'' z' hz'c).2 ⟨h8, hLie⟩
      exact ⟨E₁', E₂', t', u', n', -1, hk⟩
  obtain ⟨E₁', E₂', t', u', n', ε, hpk⟩ := hpkg
  have hlie : (p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ LieModel Gs .PSU 4 p f) := by
    rcases hL with ⟨h8, hLie⟩ | ⟨h8, -, hLie⟩
    · exact Or.inl ⟨h8, hLie⟩
    · exact Or.inr ⟨h8, hLie⟩
  have hmcfg := fusedCfg_of_fusedPkg hpk hmod h5 F hpf
  obtain ⟨eC⟩ := model_c1_equiv hpk hp hp2 h5 hlie
  obtain ⟨Ψ⟩ := rigidity hoddF h5F hmodF hbarcfg hmcfg (eM.trans eSbar) (eSbar.symm.trans eS)
  have hcl : CFSG.GH74.GLS.Stage2.Final.IsClassicalModel Gs p f := by
    refine ⟨hp, hp2, by omega, ?_⟩
    rcases hlie with ⟨h8, hL'⟩ | ⟨h8, hU⟩
    · exact Or.inr (Or.inl ⟨by omega, hL'⟩)
    · exact Or.inr (Or.inr ⟨by omega, hU⟩)
  obtain ⟨-, himg⟩ := CFSG.GH74.GLS.Stage2.Final.modelLayerBar Gs p f S'' z' hcl
    (hlie.imp (fun h => h.2) (fun h => h.2)) hpk.data.syl.z_inv hpk.data.syl.z_cen
  have hS''Cen : (S'' : Subgroup Gs) ≤ CFSG.GH74.GLS.Stage2.Local.Cen z' := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hS''C x hx).symm
  have hmres : oPrimeResidual 2 (CentralizerBar z') = layerSBar z' (S'' : Subgroup Gs) := by
    apply le_antisymm
    · rw [← himg, CFSG.GH74.GLS.Stage2.Final.LayerFD.barOf_layerTimesSylow hS''Cen]
      exact sup_le_sup_right (CFSG.GH74.GLS.Stage2.Final.LayerFD.barOf_layer_le z') _
    · exact sup_le (CFSG.GH74.GLS.Stage2.Final.LayerFD.layer_le_oPrimeResidual _)
        (CFSG.GH74.GLS.Stage2.Final.barOf_le_oPrimeResidual S''.isPGroup')
  refine ⟨(((MulEquiv.subgroupCongr hres).trans Ψ).trans eC).trans (MulEquiv.subgroupCongr hmres)⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1
