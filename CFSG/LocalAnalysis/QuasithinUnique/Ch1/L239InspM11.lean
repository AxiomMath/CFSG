module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM11Check
public import Certificates.Certificate110
public import CFSG.Sporadic.Schreier.J4SOddCheck
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open Equiv CFSG.QuasithinUnique.Unc25G2

namespace M11Insp

local notation "𝓜" => CFSG.Blueprint.NativeSporadic.M11

theorem ev_genT_mem (l : List ℕ) : ev genT l ∈ 𝓜 := by
  unfold ev
  rw [genT_eq]
  exact CFSG.Sporadic.Bridge.M11.nativeWord_mem _

@[expose] def elt (l : List ℕ) : ↥𝓜 := ⟨ev genT l, ev_genT_mem l⟩

@[expose] def cElt (j : ℕ) : ↥𝓜 := elt (cWordsCode.getD j [])

theorem coe_cElt
    (j : ℕ) : ((cElt j : ↥𝓜) : Perm (Fin 11)) = cPerm j :=
  (CFSG.Sporadic.Schreier.tab_eq _).symm

theorem pA_ne_one : pA ≠ 1 := by
  decide +kernel

theorem gA_ne_one
    : gA ≠ 1 := fun h => pA_ne_one (congrArg Subtype.val h)

theorem cElt_comm
    {j : ℕ} (hj : j < 4) : cElt j * gA = gA * cElt j := by
  have h := of_decide_eq_true (List.all_eq_true.mp comm_check j (List.mem_range.2 hj))
  apply Subtype.ext
  show (cElt j : Perm (Fin 11)) * pA = pA * (cElt j : Perm (Fin 11))
  rw [coe_cElt]
  exact h

theorem entry_spec {e : List ℕ × List ℕ × List ℕ} (he : e ∈ tblCode) :
    code (ev genT e.2.1 * pA * (ev genT e.2.1)⁻¹) = e.1 ∧
      code (ev (alph (ev genT e.2.1)) e.2.2) = code pB := by
  have h := List.all_eq_true.mp cert_check e he
  simpa [certOK, CFSG.Sporadic.Schreier.tab_eq] using h

theorem exists_entry
    {g : Perm (Fin 11)} (hg : g ∈ 𝓜) (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (hgA : g ≠ pA) : ∃ e ∈ tblCode, e.1 = code g := by
  obtain ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, hgeq⟩ := level0 hg
  rw [← wordPermsT_eq] at ht₀ ht₁ ht₂ ht₃
  have h := List.all_eq_true.mp covered_check t₀ ht₀
  have h1 := List.all_eq_true.mp h t₁ ht₁
  have h2 := List.all_eq_true.mp h1 t₂ ht₂
  have h3 := List.all_eq_true.mp h2 t₃ ht₃
  rw [← hgeq] at h3
  simp only [covered, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true] at h3
  rcases h3 with ((h3 | h3) | h3) | ⟨e, he, h3⟩
  · exact absurd hg2 h3
  · exact absurd h3 hg1
  · exact absurd (code_injective h3) hgA
  · exact ⟨e, he, h3⟩

theorem entry_conj
    {e : List ℕ × List ℕ × List ℕ} (he : e ∈ tblCode) {t : ↥𝓜}
    (hkey : e.1 = code (t : Perm (Fin 11))) : elt e.2.1 * gA * (elt e.2.1)⁻¹ = t := by
  apply Subtype.ext
  exact code_injective ((entry_spec he).1.trans hkey)

theorem top_of_not_comm
    (Y : Subgroup ↥𝓜) (hC : ∀ c : ↥𝓜, c * gA = gA * c → c ∈ Y) {y : ↥𝓜}
    (hy : y ∈ Y) (hyn : y * gA ≠ gA * y) : Y = ⊤ := by
  have ht₁2 : (y * gA * y⁻¹) * (y * gA * y⁻¹) = 1 := by
    calc (y * gA * y⁻¹) * (y * gA * y⁻¹) = y * (gA * gA) * y⁻¹ := by group
      _ = 1 := by rw [gA_sq]; group
  have ht₁1 : y * gA * y⁻¹ ≠ 1 := by
    intro h
    apply gA_ne_one
    calc gA = y⁻¹ * (y * gA * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  have ht₁A : y * gA * y⁻¹ ≠ gA := by
    intro h
    apply hyn
    calc y * gA = (y * gA * y⁻¹) * y := by group
      _ = gA * y := by rw [h]
  obtain ⟨e, he, hkey⟩ := exists_entry (y * gA * y⁻¹).2
    (by simpa using congrArg Subtype.val ht₁2) (fun h => ht₁1 (Subtype.ext h))
    (fun h => ht₁A (Subtype.ext h))
  have hconj := entry_conj he hkey
  have hcomm : (y⁻¹ * elt e.2.1) * gA = gA * (y⁻¹ * elt e.2.1) := by
    have h1 : elt e.2.1 * gA = (y * gA * y⁻¹) * elt e.2.1 := by
      rw [← hconj]
      group
    calc y⁻¹ * elt e.2.1 * gA = y⁻¹ * (elt e.2.1 * gA) := by group
      _ = y⁻¹ * ((y * gA * y⁻¹) * elt e.2.1) := by rw [h1]
      _ = gA * (y⁻¹ * elt e.2.1) := by group
  have hyeY : elt e.2.1 ∈ Y := by
    have := Y.mul_mem hy (hC _ hcomm)
    simpa using this
  let x : ℕ → ↥𝓜 := fun i => if i < 4 then cElt i else elt e.2.1
  have hxY : ∀ i, x i ∈ Y := by
    intro i
    by_cases hi : i < 4
    · simp only [x, hi, ↓reduceIte]
      exact hC _ (cElt_comm hi)
    · simp only [x, hi, ↓reduceIte]
      exact hyeY
  have hword : CFSG.Sporadic.Bridge.wordProd x (dec e.2.2) ∈ Y :=
    CFSG.Sporadic.Bridge.wordProd_mem hxY _
  have hcoe : ((CFSG.Sporadic.Bridge.wordProd x (dec e.2.2) : ↥𝓜) : Perm (Fin 11)) =
      ev (alph (ev genT e.2.1)) e.2.2 := by
    rw [CFSG.Sporadic.Bridge.coe_wordProd]
    unfold ev
    congr 1
    funext i
    by_cases hi : i < 4
    · simp only [x, alph, hi, ↓reduceIte, coe_cElt]
    · simp only [x, alph, hi, ↓reduceIte]
      rfl
  have hgB : CFSG.Sporadic.Bridge.wordProd x (dec e.2.2) = gB := by
    apply Subtype.ext
    rw [hcoe]
    exact code_injective (entry_spec he).2
  have hgBY : gB ∈ Y := hgB ▸ hword
  have hgAY : gA ∈ Y := hC gA rfl
  rw [eq_top_iff, ← closure_gA_gB, Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | hz
  · exact hgAY
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hgBY

theorem exists_conj
    {t : ↥𝓜} (ht2 : t * t = 1) (ht1 : t ≠ 1) : ∃ g : ↥𝓜, g * gA * g⁻¹ = t := by
  by_cases h : t = gA
  · exact ⟨1, by simp [h]⟩
  · obtain ⟨e, he, hkey⟩ := exists_entry t.2 (by simpa using congrArg Subtype.val ht2)
      (fun h' => ht1 (Subtype.ext h')) (fun h' => h (Subtype.ext h'))
    exact ⟨elt e.2.1, entry_conj he hkey⟩

theorem max_of_involution
    {t : ↥𝓜} (ht2 : t * t = 1) (ht1 : t ≠ 1) (Y : Subgroup ↥𝓜)
    (hC : ∀ c : ↥𝓜, c * t = t * c → c ∈ Y) : Y = ⊤ ∨ ∀ y ∈ Y, y * t = t * y := by
  by_cases hcomm : ∀ y ∈ Y, y * t = t * y
  · exact Or.inr hcomm
  · left
    push Not at hcomm
    obtain ⟨y, hyY, hyn⟩ := hcomm
    obtain ⟨g, hg⟩ := exists_conj ht2 ht1
    let Y' : Subgroup ↥𝓜 := Y.comap (MulAut.conj g).toMonoidHom
    have hmem : ∀ x, x ∈ Y' ↔ g * x * g⁻¹ ∈ Y := fun x => Iff.rfl
    have hC' : ∀ c : ↥𝓜, c * gA = gA * c → c ∈ Y' := by
      intro c hc
      rw [hmem]
      apply hC
      rw [← hg]
      calc g * c * g⁻¹ * (g * gA * g⁻¹) = g * (c * gA) * g⁻¹ := by group
        _ = g * (gA * c) * g⁻¹ := by rw [hc]
        _ = g * gA * g⁻¹ * (g * c * g⁻¹) := by group
    have hy' : g⁻¹ * y * g ∈ Y' := by
      rw [hmem]
      have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [h1]
      exact hyY
    have hyn' : (g⁻¹ * y * g) * gA ≠ gA * (g⁻¹ * y * g) := by
      intro h
      apply hyn
      calc y * t = g * ((g⁻¹ * y * g) * gA) * g⁻¹ := by rw [← hg]; group
        _ = g * (gA * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
        _ = t * y := by rw [← hg]; group
    have htop := top_of_not_comm Y' hC' hy' hyn'
    rw [eq_top_iff]
    intro x _
    have hx : g⁻¹ * x * g ∈ Y' := by rw [htop]; trivial
    rw [hmem] at hx
    have h1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [h1] at hx

theorem max_of_equiv
    {H : Type*} [Group H] (e : H ≃* ↥𝓜) {t : H} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    {Y : Subgroup H} (hC : Subgroup.centralizer ({t} : Set H) ≤ Y) :
    Y = ⊤ ∨ Y = Subgroup.centralizer ({t} : Set H) := by
  have ht2' : e t * e t = 1 := by rw [← map_mul, ht2, map_one]
  have ht1' : e t ≠ 1 := fun h => ht1 (e.injective (by rw [h, map_one]))
  rcases max_of_involution ht2' ht1' (Y.map e.toMonoidHom) (by
      intro c hc
      refine ⟨e.symm c, hC ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hc) with htop | hcomm
  · left
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ Y.map e.toMonoidHom := by rw [htop]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← e.injective hyx]
    exact hy
  · right
    apply le_antisymm _ hC
    intro y hy
    have := hcomm (e y) ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simp only [map_mul]
    exact this

end M11Insp

theorem l239M11Overgroups : L239M11Overgroups := by
  intro G _ _ L t hL htL ht2 ht1 Y hYL hCY hYne
  obtain ⟨φ⟩ := hL
  let e : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M11 := φ
  let t' : ↥L := ⟨t, htL⟩
  have ht'2 : t' * t' = 1 := Subtype.ext (by simpa [sq] using ht2)
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hC : Subgroup.centralizer ({t'} : Set ↥L) ≤ Y.subgroupOf L := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    apply hCY
    refine ⟨c.2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)
  rcases M11Insp.max_of_equiv e ht'2 ht'1 hC with htop | hcent
  · exfalso
    apply hYne
    apply le_antisymm hYL
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ Y.subgroupOf L := by rw [htop]; trivial
    exact this
  · apply le_antisymm
    · intro x hx
      refine ⟨hYL hx, ?_⟩
      have h1 : (⟨x, hYL hx⟩ : ↥L) ∈ Y.subgroupOf L := hx
      rw [hcent, Subgroup.mem_centralizer_singleton_iff] at h1
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1)
    · exact hCY

end CFSG.QuasithinUnique.Vol2Native.L239
