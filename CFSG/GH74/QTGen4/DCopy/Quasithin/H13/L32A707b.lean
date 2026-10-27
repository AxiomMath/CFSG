module

public import CFSG.Quasithin.H13.L32A707b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting147

variable {T L V H : Subgroup G}

theorem hypF918_of_quasisimple_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K))
    (S' : Setting147 G T L V (conjClosure K T ⊔ (l1 T L V ⊔ T))) :
    HypF918 T V L (fsuV1 T V) V (conjClosure K T ⊔ (l1 T L V ⊔ T)) K := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hTH : T ≤ H := Setting147.TH' S
  have hK₀H : conjClosure K T ≤ H := conjClosure_le fun t ht k hk =>
    H.mul_mem (H.mul_mem (hTH ht) (le_of_mem_cComp hK hk)) (H.inv_mem (hTH ht))
  have hH₀H : conjClosure K T ⊔ (l1 T L V ⊔ T) ≤ H := sup_le hK₀H S.hz.1.1
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hH₀ : conjClosure K T ⊔ (l1 T L V ⊔ T) =
      conjClosure K T ⊔ ((L ⊔ T) ⊓ (conjClosure K T ⊔ (l1 T L V ⊔ T))) :=
    le_antisymm
      (sup_le_sup_left (le_inf (sup_le_sup_right hl1L T) le_sup_right) _)
      (sup_le le_sup_left inf_le_right)
  exact ⟨L1286.hypF98_of_abelian_F4 h1222 h37 h38 h39
      (S'.hyp.hyp1281One_F4 (stmt13_3_2_two_of_F4 h1332) hMod) (S'.hyp.isTSub_V1_F4 hMod)
      S'.hyp.abelian S'.hz,
    cComp_mem_of_le hK ((le_conjClosure K T).trans le_sup_left) hH₀H, hq, hH₀,
    hH₀H.trans (C.le_normalizer_conjClosure_T h37 h38 S hK)⟩

theorem exists_c_cube_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : ∃ c ∈ l1 T L V, c ^ 3 = 1 ∧ c ∉ pCoreOf 2 (l1 T L V) := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  obtain ⟨x, hx, hx3, -, hxa, -⟩ := exists_x_cube_F4 S14 hz hz1 ha haV hb hbV
  refine ⟨x, hl1eq ▸ hx, hx3, fun h => ?_⟩
  have h1 := (S14.pCoreOf_L1_le_F4 (hl1eq ▸ h)).2.2 a (S14.hV2.2.1 ha)
  rw [hxa] at h1
  apply hbV
  rw [show b = b * a⁻¹ * a by group]
  exact mul_mem (S14.hV2.1 h1) ha

theorem false_of_sz_comp_F4
    (h519 : Lemma14_5_19_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h310 : D310) (h391 : D391)
    (hI4 : Insp4) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (hSzE : A6.SzEnd) (S : Setting147 G T L V H)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) {K : Subgroup G} (hK : K ∈ cComp H)
    {n : ℕ} (hSz : IsSz n (↥K ⧸ CFSG.pCore 2 ↥K))
    (hcomm : ∀ c ∈ l1 T L V, ∀ k ∈ conjClosure K T, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    False := by
  set H₀ := conjClosure K T ⊔ (l1 T L V ⊔ T) with hH₀
  have S' : Setting147 G T L V H₀ := (h519 G T L V H S K hK).2
  have hTH : T ≤ H := Setting147.TH' S
  have hK₀H : conjClosure K T ≤ H := conjClosure_le fun t ht k hk =>
    H.mul_mem (H.mul_mem (hTH ht) (le_of_mem_cComp hK hk)) (H.inv_mem (hTH ht))
  have hH₀H : H₀ ≤ H := sup_le hK₀H S.hz.1.1

  have hn3 : 3 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hSz
    omega
  have hq₀ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    isQuasisimple_of_psl2_or_sz hn3 (Or.inr hSz)
  have hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (pCoreOf_subgroupOf' K)).symm hq₀
  have hF := hypF918_of_quasisimple_F4 h1222 h1332 h1334 h37 h38 h39 S hK hq S'
  have hHq : SQTKGroup ↥H₀ := sqtkGroup_of_pCoreOf_ne_bot S'.hyp.fsu.qtke S'.hyp.fsu.simple
    S'.hyp.fsu.nonabelian S'.hz.1.2

  obtain ⟨c, hc, hc3, hcO⟩ := exists_c_cube_F4 S h1222 h1332 h1334
  have hcH₀ : c ∈ H₀ := Subgroup.mem_sup_right (Subgroup.mem_sup_left hc)
  have hHL₀ : H₀ ≤ Subgroup.normalizer (l1 T L V : Set G) := hH₀H.trans hHL
  have hfix : ∀ a ∈ conjClosure V H₀, (c * a * c⁻¹)⁻¹ * a ∈ fsuV1 T V → a ∈ fsuV1 T V := by
    intro a ha hca
    have hcaU : c * a * c⁻¹ ∈ conjClosure V H₀ :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H₀ hcH₀) a).mp ha
    have e1 : c * a * c⁻¹ * a⁻¹ = a⁻¹ * (c * a * c⁻¹) :=
      Setting147.UH_comm S' _ hcaU _ (inv_mem ha)
    have e2 : a⁻¹ * (c * a * c⁻¹) = ((c * a * c⁻¹)⁻¹ * a)⁻¹ := by group
    refine Setting147.mem_V1_of_fix_F4 S' h1222 h1332 h1334 hHL₀ hc hcO ha ?_
    rw [e1, e2]
    exact inv_mem hca
  have hcomm₀ : ∀ k ∈ conjClosure K T, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 H₀ := by
    intro k hk
    have hkH₀ : k ∈ H₀ := Subgroup.mem_sup_left hk
    refine inf_pCoreOf_le hH₀H ⟨hcomm c hc k hk, ?_⟩
    exact H₀.mul_mem (H₀.mul_mem (H₀.mul_mem hcH₀ hkH₀) (H₀.inv_mem hcH₀)) (H₀.inv_mem hkH₀)
  exact false_of_sz_of_hypF918 hF hHq h37 h38 h310 h391 hI4 hD36 hD37 hD321 hI5 hSzE hcH₀ hc3
    hfix hcomm₀ hSz

end Setting147

end CFSG.Quasithin.H13.L32A
