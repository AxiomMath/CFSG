module

public import CFSG.Quasithin.H13.U3S1349A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1342

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_normalizer_le_sup_F4 (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) :
    normalizer (L : Set G) ≤ L ⊔ normalizer (L : Set G) ⊓ centralizer ({z} : Set G) := by
  intro m hm
  have hmN : m ∈ normalizer (V : Set G) := A6.Setting134.normalizer_L_le_F4 S h1222 hm
  obtain ⟨hzV, hzW⟩ := S.mem_V1_iff.1 hz

  have hψz : (S.frame.ψ ⟨z, hzV⟩ : A6.P6) = A6.e0123 ∨
      (S.frame.ψ ⟨z, hzV⟩ : A6.P6) = A6.e45 := by
    rcases A6.W1_cases _ (S.frame.ψ ⟨z, hzV⟩).2 hzW with h | h | h | h
    · exfalso
      apply hzL
      have : (⟨z, hzV⟩ : ↥V) = 1 := S.frame.ψ.injective (Subtype.ext (by rw [h, map_one]; rfl))
      rw [show z = 1 from congrArg Subtype.val this]
      exact one_mem _
    · exfalso
      apply hzL
      have : (⟨z, hzV⟩ : ↥V) = ⟨S.zV, S.zV_mem_V⟩ :=
        S.frame.ψ.injective (Subtype.ext (by rw [h, S.psi_zV]))
      exact (S.mem_centralizer_L_iff ⟨z, hzV⟩).2 (Or.inr this)
    · exact Or.inl h
    · exact Or.inr h

  obtain ⟨σ, hσA, hσ⟩ : ∃ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧
      G6.permAct 6 σ (S.frame.ψ ⟨z, hzV⟩) = G6.permAct 6 (S.frame.ρ ⟨m, hmN⟩)
        (S.frame.ψ ⟨z, hzV⟩) := by
    rcases hψz with h | h
    · obtain ⟨σ, hs, he⟩ := (alt_transitive (S.frame.ρ ⟨m, hmN⟩)).1
      exact ⟨σ, Perm.mem_alternatingGroup.2 hs, by rw [h]; exact he⟩
    · obtain ⟨σ, hs, he⟩ := (alt_transitive (S.frame.ρ ⟨m, hmN⟩)).2
      exact ⟨σ, Perm.mem_alternatingGroup.2 hs, by rw [h]; exact he⟩
  obtain ⟨⟨l, hlN⟩, hlL, hlσ⟩ := (S.frame.image_L σ).2 hσA

  have hc : l⁻¹ * m ∈ centralizer ({z} : Set G) := by
    have hfix := (S.conj_eq_iff (⟨l, hlN⟩⁻¹ * ⟨m, hmN⟩) ⟨z, hzV⟩).2 (by
      apply Subtype.ext
      rw [G6.coreAct_coe, map_mul, map_inv, hlσ, map_mul, MulAut.mul_apply, ← hσ,
        ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
    rw [mem_centralizer_singleton_iff]
    simp only [coe_mul, InvMemClass.coe_inv] at hfix
    calc l⁻¹ * m * z = l⁻¹ * m * z * (l⁻¹ * m)⁻¹ * (l⁻¹ * m) := by group
      _ = z * (l⁻¹ * m) := by rw [hfix]
  have hlM : l ∈ normalizer (L : Set G) := le_normalizer hlL
  have : m = l * (l⁻¹ * m) := by group
  rw [this]
  exact mul_mem (mem_sup_left hlL)
    (mem_sup_right (mem_inf.2 ⟨mul_mem (inv_mem hlM) hm, hc⟩))

theorem s134_CMV_le_T_F4 (S : A6.Setting134 G T L V)
    (hp : IsPGroup 2 ↥(normalizer (L : Set G) ⊓ centralizer (V : Set G))) (h1222 : Stmt12_2_2_F4) :
    normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ T := by
  have hTsyl : IsSylowTwoOf T (normalizer (L : Set G)) :=
    A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
  have hn : ((normalizer (L : Set G) ⊓ centralizer (V : Set G)).subgroupOf
      (normalizer (L : Set G))).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun m hm => ?_
    have hmV : m ∈ normalizer (V : Set G) := A6.Setting134.normalizer_L_le_F4 S h1222 hm
    refine mem_normalizer_inf (le_normalizer hm) ?_
    rw [mem_normalizer_iff]
    intro c
    have key : ∀ g ∈ normalizer (V : Set G), ∀ c ∈ centralizer (V : Set G),
        g * c * g⁻¹ ∈ centralizer (V : Set G) := by
      intro g hg c hc
      rw [mem_centralizer_iff] at hc ⊢
      intro v hv
      have hv' : g⁻¹ * v * g ∈ V := by
        have := (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
        simpa using this
      have h1 := hc _ hv'
      calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * v := by group
    refine ⟨fun hc => key m hmV c hc, fun hc => ?_⟩
    have := key m⁻¹ (inv_mem hmV) _ hc
    simpa [mul_assoc] using this
  exact (CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
    inf_le_left hn hp).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)

theorem s134_quot_M_F4 (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V)
    (hp : IsPGroup 2 ↥(normalizer (L : Set G) ⊓ centralizer (V : Set G))) :
    quasithinO2QuotientIso (normalizer (L : Set G)) ↥(alternatingGroup (Fin 6)) ∨
      quasithinO2QuotientIso (normalizer (L : Set G)) (Perm (Fin 6)) := by
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) :=
    A6.Setting134.normalizer_L_le_F4 S h1222
  set ρ' : ↥(normalizer (L : Set G)) →* Perm (Fin 6) :=
    S.frame.ρ.comp (inclusion hMV) with hρ'

  have hker : ρ'.ker = CFSG.Open.pCore 2 ↥(normalizer (L : Set G)) := by
    ext x
    rw [MonoidHom.mem_ker, ← CFSG.pCore_eq_open, ← coe_mem_pCoreOf_iff]
    have h1 : ρ' x = 1 ↔ (x : G) ∈ centralizer (V : Set G) := by
      rw [hρ', MonoidHom.comp_apply]
      exact s134_rho_eq_one_iff S _
    rw [h1]
    constructor
    · intro hx
      refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2
        (normalizer (L : Set G) ⊓ centralizer (V : Set G)) _ inf_le_left ?_ hp
        (mem_inf.2 ⟨x.2, hx⟩)
      refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun m hm => ?_
      have hmV : m ∈ normalizer (V : Set G) := hMV hm
      refine mem_normalizer_inf (le_normalizer hm) ?_
      rw [mem_normalizer_iff]
      intro c
      have key : ∀ g ∈ normalizer (V : Set G), ∀ c ∈ centralizer (V : Set G),
          g * c * g⁻¹ ∈ centralizer (V : Set G) := by
        intro g hg c hc
        rw [mem_centralizer_iff] at hc ⊢
        intro v hv
        have hv' : g⁻¹ * v * g ∈ V := by
          have := (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
          simpa using this
        have h1 := hc _ hv'
        calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
          _ = g * c * g⁻¹ * v := by group
      refine ⟨fun hc => key m hmV c hc, fun hc => ?_⟩
      have := key m⁻¹ (inv_mem hmV) _ hc
      simpa [mul_assoc] using this
    · intro hx
      exact s134_pCoreOf_M_le S hx

  have hA : alternatingGroup (Fin 6) ≤ ρ'.range := by
    intro σ hσ
    obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L σ).2 hσ
    refine ⟨⟨g, le_normalizer hgL⟩, ?_⟩
    rw [hρ', MonoidHom.comp_apply]
    rw [show inclusion hMV ⟨(g : G), le_normalizer hgL⟩ = g from Subtype.ext rfl]
    exact hgσ
  rcases eq_alt_or_top hA with h | h
  · left
    refine ⟨ρ'.codRestrict _ (fun x => h ▸ ⟨x, rfl⟩), ?_, ?_⟩
    · rintro ⟨σ, hσ⟩
      rw [← h] at hσ
      obtain ⟨x, hx⟩ := hσ
      exact ⟨x, Subtype.ext hx⟩
    · rw [← hker]
      ext x
      simp only [MonoidHom.mem_ker]
      constructor
      · intro hx
        exact congrArg Subtype.val hx
      · intro hx
        exact Subtype.ext hx
  · right
    refine ⟨ρ', fun σ => ?_, hker⟩
    have : σ ∈ ρ'.range := by rw [h]; exact mem_top σ
    exact this

theorem s134_overgroups_M_F4 (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V)
    (hp : IsPGroup 2 ↥(normalizer (L : Set G) ⊓ centralizer (V : Set G))) :
    ∀ Y : Subgroup G, T ≤ Y → Y ≤ normalizer (L : Set G) →
      Y = T ∨ Y = L₁Of L (fsuV1 T V) ⊔ T ∨ Y = l2Of S ⊔ T ∨ Y = normalizer (L : Set G) := by
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set M := normalizer (L : Set G) with hM
  have hTsyl : IsSylowTwoOf T M := A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1N : L₁ ≤ normalizer (fsuV1 T V : Set G) := (oTwoRes_le _).trans inf_le_right

  obtain ⟨A₁, A₂, hT₁, hT₂, h₁M, h₂M, h₁₂, h₂₁, hA₁, hA₂, hcls⟩ :
      ∃ A₁ A₂ : Subgroup G, T ≤ A₁ ∧ T ≤ A₂ ∧ A₁ ≤ M ∧ A₂ ≤ M ∧ ¬ A₁ ≤ A₂ ∧ ¬ A₂ ≤ A₁ ∧
        A₁ ≠ M ∧ A₂ ≠ M ∧
        ∀ Y : Subgroup G, T ≤ Y → Y ≤ M → Y = T ∨ Y = A₁ ∨ Y = A₂ ∨ Y = M := by
    rcases s134_quot_M_F4 h1222 S hp with h | h
    · obtain ⟨P₀, X₁, X₂, hP, hP', hc, h1, h2, h12, h21⟩ := A6.modelData_A6.exists_data
      exact A6.overgroups_transport h hTsyl hP hP' hc h1 h2 h12 h21
    · obtain ⟨P₀, X₁, X₂, hP, hP', hc, h1, h2, h12, h21⟩ := A6.modelData_S6.exists_data
      exact A6.overgroups_transport h hTsyl hP hP' hc h1 h2 h12 h21

  obtain ⟨y, hyL1, hyN, hyρ⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  have hP1 : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ L₁ ⊔ T → S.frame.ρ x ∈ A6.P1sub :=
    s134_rho_mem_sup S (hL1L.trans S.frame.L_le) (fun σ hσ => (A6.D6sub_le hσ).1)
      (fun x hx => inP1_of_pres45 _ (s134_pres45 S x (hL1N hx)))
  have hP2 : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ l2Of S ⊔ T → S.frame.ρ x ∈ A6.P2sub :=
    s134_rho_mem_sup S ((s134_L2_le_L S).trans S.frame.L_le) (fun σ hσ => (A6.D6sub_le hσ).2)
      (fun x hx => (s134_normalizer_V2_iff S x.2).1 (s134_L2_le_normalizer_V2 S hx))
  have hyM : y ∈ M := le_normalizer (hL1L hyL1)
  have hcM : c ∈ M := le_normalizer (s134_L2_le_L S hcL2)
  have hy1 : y ∈ L₁ ⊔ T := le_sup_left (b := T) hyL1
  have hc2 : c ∈ l2Of S ⊔ T := le_sup_left (b := T) hcL2
  have hyT : y ∉ T := fun h => gens_not_mem.2.2.1 (by
    have := S.frame.T_D ⟨y, hyN⟩ h; rwa [hyρ] at this)
  have hcT : c ∉ T := fun h => gens_not_mem.2.2.2 (by
    have := S.frame.T_D ⟨c, hcN⟩ h; rwa [hcρ] at this)
  have hy2 : y ∉ l2Of S ⊔ T := fun h => gens_not_mem.1 (by
    have := hP2 ⟨y, hyN⟩ h; rwa [hyρ] at this)
  have hc1 : c ∉ L₁ ⊔ T := fun h => gens_not_mem.2.1 (by
    have := hP1 ⟨c, hcN⟩ h; rwa [hcρ] at this)
  have hL1T_M : L₁ ⊔ T ≤ M := sup_le (hL1L.trans le_normalizer) S.T_le_NL
  have hL2T_M : l2Of S ⊔ T ≤ M := sup_le ((s134_L2_le_L S).trans le_normalizer) S.T_le_NL
  have hcase1 := hcls _ le_sup_right hL1T_M
  have hcase2 := hcls _ le_sup_right hL2T_M
  have hne1T : L₁ ⊔ T ≠ T := fun h => hyT (h ▸ hy1)
  have hne1M : L₁ ⊔ T ≠ M := fun h => hc1 (h ▸ hcM)
  have hne2T : l2Of S ⊔ T ≠ T := fun h => hcT (h ▸ hc2)
  have hne2M : l2Of S ⊔ T ≠ M := fun h => hy2 (h ▸ hyM)
  have hne12 : L₁ ⊔ T ≠ l2Of S ⊔ T := fun h => hy2 (h ▸ hy1)
  intro Y hTY hYM
  rcases hcls Y hTY hYM with h | h | h | h
  · exact Or.inl h
  · right
    rcases hcase1 with e | e | e | e
    · exact absurd e hne1T
    · exact Or.inl (h.trans e.symm)
    · rcases hcase2 with f | f | f | f
      · exact absurd f hne2T
      · exact Or.inr (Or.inl (h.trans f.symm))
      · exact absurd (e.trans f.symm) hne12
      · exact absurd f hne2M
    · exact absurd e hne1M
  · right
    rcases hcase1 with e | e | e | e
    · exact absurd e hne1T
    · rcases hcase2 with f | f | f | f
      · exact absurd f hne2T
      · exact absurd (e.trans f.symm) hne12
      · exact Or.inr (Or.inl (h.trans f.symm))
      · exact absurd f hne2M
    · exact Or.inl (h.trans e.symm)
    · exact absurd e hne1M
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Quasithin.H13.U3
