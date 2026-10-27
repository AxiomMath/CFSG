module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Lift
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Loc
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Orbit

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_imH_le {H A : Subgroup G} {k : G} (hk : k ∈ H) :
    (imH H A).map
      (MulAut.conj (QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨k, hk⟩)).toMonoidHom ≤
      imH H (A.map (MulAut.conj k).toMonoidHom) := by
  rintro _ ⟨y, ⟨a, ha, rfl⟩, rfl⟩
  refine ⟨⟨k, hk⟩ * a * ⟨k, hk⟩⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr
      ⟨a, Subgroup.mem_subgroupOf.mp ha, by simp [MulAut.conj_apply]⟩
  · simp [MulAut.conj_apply]

theorem exists_localized_factors {P : Sylow 3 G} {M H R L : Subgroup G}
    (h3 : D1PhaseThree 3 P M H R) (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hB3 : StmtBlockThree)
    {T K A₀ V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hI : Sp48NInSitu T (imH H (H ⊓ M)) K A₀ V₀) :
    ∃ (V₁ V₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L₁ L₂ : Subgroup G),
      IsWeakSBlock M (pCoreOf 2 H) L₁ ∧ IsWeakSBlock M (pCoreOf 2 H) L₂ ∧
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁ ≤ H ∧
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂ ≤ H ∧
      ⁅V₁, V₁⁆ = V₁ ∧ ⁅V₂, V₂⁆ = V₂ ∧ ⁅V₁, V₂⁆ = ⊥ ∧ IsCaseTwoGroup 3 V₁ ∧
      IsCaseTwoGroup 3 V₂ ∧
      V₁ ≤ imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁) ∧
      V₂ ≤ imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂) ∧
      imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁) ≤
        Subgroup.normalizer ((V₁ ⊔ V₂ : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) 3)) ∧
      imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂) ≤
        Subgroup.normalizer ((V₁ ⊔ V₂ : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) 3)) ∧
      (L₁ ≠ L₂ →
        imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁) ≤
          Subgroup.normalizer (V₁ : Set (H ⧸ primeComplementCore (G := H) 3)) ∧
        imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂) ≤
          Subgroup.normalizer (V₂ : Set (H ⧸ primeComplementCore (G := H) 3))) := by
  classical
  set S : Subgroup G := pCoreOf 2 H with hS
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set N : Subgroup G := GLBPrimeCore 3 H with hN
  have hKS : H ⊓ M = M ⊓ Subgroup.normalizer (S : Set G) := h3.inf_eq_inf_normalizer_twoCore
  have hO2 : pCoreOf 2 M ≤ N :=
    (h3.twoCore_M_le h3.twoCore_inf).trans
      (pCoreOf_le_glbPrimeCore Nat.prime_two (by norm_num) H)
  obtain ⟨V₁, V₂, h12, hcomm, hp1, hp2, ⟨d₁, hd₁, ⟨e₁⟩⟩, ⟨d₂, hd₂, ⟨e₂⟩⟩, -, -, -⟩ := hI.factors
  have hc₁ : IsCaseTwoGroup 3 V₁ := ⟨d₁, hd₁, ⟨e₁⟩⟩
  have hc₂ : IsCaseTwoGroup 3 V₂ := ⟨d₂, hd₂, ⟨e₂⟩⟩
  have hs₁ : IsSimpleGroup V₁ := isSimpleGroup_of_isCaseTwoGroup_three hc₁
  have hs₂ : IsSimpleGroup V₂ := isSimpleGroup_of_isCaseTwoGroup_three hc₂
  have hnab : ∀ (W : Subgroup (H ⧸ primeComplementCore (G := H) 3)), IsSimpleGroup W →
      ⁅W, W⁆ = W → ∃ a b : W, a * b ≠ b * a := by
    intro W hWs hWp
    by_contra hcon
    push Not at hcon
    have : Nontrivial W := inferInstance
    have hbot : ⁅W, W⁆ ≤ ⊥ := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hcon ⟨g₁, h₁⟩ ⟨g₂, h₂⟩)
    obtain ⟨a, b, hab⟩ := exists_pair_ne W
    apply hab
    have ha : (a : H ⧸ primeComplementCore (G := H) 3) ∈ (⊥ : Subgroup _) :=
      hbot (hWp.ge a.2)
    have hb : (b : H ⧸ primeComplementCore (G := H) 3) ∈ (⊥ : Subgroup _) :=
      hbot (hWp.ge b.2)
    rw [Subgroup.mem_bot] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  have hnab₁ := hnab V₁ hs₁ hp1
  have hnab₂ := hnab V₂ hs₂ hp2
  let ι := {L' : Subgroup G // ∃ k ∈ H ⊓ M, L' = L.map (MulAut.conj k).toMonoidHom}
  have hweak : ∀ L' : ι, IsWeakSBlock M S L'.1 := by
    rintro ⟨L', k, hk, rfl⟩
    exact h3.isWeakSBlock_map_conj hL hk
  have hNle : ∀ L' : ι, Subgroup.normalizer (S : Set G) ⊓ L'.1 ≤ H ⊓ M := fun L' x hx => by
    rw [hKS]
    exact ⟨(hweak L').le hx.2, hx.1⟩
  have hNH : ∀ L' : ι, Subgroup.normalizer (S : Set G) ⊓ L'.1 ≤ H := fun L' =>
    (hNle L').trans inf_le_left
  set Pt : ι → Subgroup (H ⧸ primeComplementCore (G := H) 3) :=
    fun L' => imH H (Subgroup.normalizer (S : Set G) ⊓ L'.1) with hPt
  have hbc : ∀ L' L'' : ι, L' ≠ L'' → ∀ x ∈ Pt L', ∀ y ∈ Pt L'', x * y = y * x := by
    intro L' L'' hne x hx y hy
    have hne' : L'.1 ≠ L''.1 := fun h => hne (Subtype.ext h)
    have hc : ⁅L'.1, L''.1⁆ ≤ N :=
      ((hweak L').toIsTwoPrimeComponent.commutator_le (hweak L'').toIsTwoPrimeComponent
        hne').trans hO2
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have ha' : (a : G) ∈ L'.1 := (Subgroup.mem_subgroupOf.mp ha).2
    have hb' : (b : G) ∈ L''.1 := (Subgroup.mem_subgroupOf.mp hb).2
    have h1 : ((⁅a, b⁆ : H) : G) ∈ N := by
      have := hc (Subgroup.commutator_mem_commutator ha' hb')
      simpa [commutatorElement_def] using this
    have h2 := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) ⁅a, b⁆).mp h1
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  set D : Subgroup (H ⧸ primeComplementCore (G := H) 3) := ⨆ L' : ι, Pt L' with hD
  have hDX : D ≤ imH H (H ⊓ M) := iSup_le fun L' =>
    Subgroup.map_mono (Subgroup.subgroupOf_mono H (hNle L'))
  have hXD : imH H (H ⊓ M) ≤
      Subgroup.normalizer (D : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    refine le_normalizer_of_forall_map_conj_le fun x hx => ?_
    obtain ⟨k', hk', rfl⟩ := hx
    have hkKM : (k' : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hk'
    have hkS : (k' : G) ∈ Subgroup.normalizer (S : Set G) := (hKS ▸ hkKM).2
    rw [hD, Subgroup.map_iSup]
    refine iSup_le fun L' => ?_
    obtain ⟨k₀, hk₀, hL'⟩ := L'.2
    have hconj : (L'.1).map (MulAut.conj (k' : G)).toMonoidHom =
        L.map (MulAut.conj ((k' : G) * k₀)).toMonoidHom := by
      rw [hL', map_conj_mul_eq]
    have hmem : (L'.1).map (MulAut.conj (k' : G)).toMonoidHom ∈
        {L'' : Subgroup G | ∃ k ∈ H ⊓ M, L'' = L.map (MulAut.conj k).toMonoidHom} :=
      ⟨(k' : G) * k₀, (H ⊓ M).mul_mem hkKM hk₀, hconj⟩
    refine (map_conj_imH_le k'.2).trans ?_
    have hN' : (Subgroup.normalizer (S : Set G)).map (MulAut.conj (k' : G)).toMonoidHom =
        Subgroup.normalizer (S : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkS)
    have e : (Subgroup.normalizer (S : Set G) ⊓ L'.1).map (MulAut.conj (k' : G)).toMonoidHom =
        Subgroup.normalizer (S : Set G) ⊓ (L'.1).map (MulAut.conj (k' : G)).toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (k' : G)).injective, hN']
    rw [e]
    exact le_iSup Pt (⟨(L'.1).map (MulAut.conj (k' : G)).toMonoidHom, hmem⟩ : ι)
  have hDne : D ≠ ⊥ := by
    obtain ⟨y, ⟨hyS, hyL⟩, hy3, l, hl, hlQ⟩ := hB3 h3 hL
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hlQ (by simp)
    have hyH : y ∈ H := (hKS ▸ (⟨hL.le hyL, hyS⟩ : y ∈ M ⊓ Subgroup.normalizer (S : Set G))
      : y ∈ H ⊓ M).1
    have hyN : y ∉ N := not_mem_glbPrimeCore_of_three hy3 hy1
    intro hbot
    have hLι : L ∈ {L'' : Subgroup G | ∃ k ∈ H ⊓ M,
        L'' = L.map (MulAut.conj k).toMonoidHom} :=
      ⟨1, (H ⊓ M).one_mem, by ext x; simp⟩
    have hy : π ⟨y, hyH⟩ ∈ Pt (⟨L, hLι⟩ : ι) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hyS, hyL⟩)
    have hyD : π ⟨y, hyH⟩ ∈ D := Subgroup.mem_iSup_of_mem (⟨L, hLι⟩ : ι) hy
    rw [hbot, Subgroup.mem_bot] at hyD
    exact hyN ((mem_glbPrimeCore_iff_mk_eq_one (p := 3) ⟨y, hyH⟩).mpr hyD)
  have hV₀D : V₀ ≤ D := (hI.minimal D hDX hXD).resolve_left hDne
  have hV₀N : ∀ L' : ι, Pt L' ≤ Subgroup.normalizer (V₀ : Set _) := fun L' =>
    ((le_iSup Pt L').trans hDX).trans hI.V_normal
  have hV₁V₀ : V₁ ≤ V₀ := h12 ▸ le_sup_left
  have hV₂V₀ : V₂ ≤ V₀ := h12 ▸ le_sup_right
  have hV₁n : V₀ ≤ Subgroup.normalizer (V₁ : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [← h12]
    refine sup_le Subgroup.le_normalizer fun b hb => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this)
  have hV₂n : V₀ ≤ Subgroup.normalizer (V₂ : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [← h12]
    refine sup_le (fun a ha => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)) Subgroup.le_normalizer
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm
  have hDV : D ≤ Subgroup.normalizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3)) :=
    hDX.trans hI.V_normal
  obtain ⟨i₁, hi₁⟩ := exists_le_of_commuting_family Pt hbc hV₀D hDV hI.V_perfect hV₁V₀ hV₁n
    hp1 hs₁ hnab₁
  obtain ⟨i₂, hi₂⟩ := exists_le_of_commuting_family Pt hbc hV₀D hDV hI.V_perfect hV₂V₀ hV₂n
    hp2 hs₂ hnab₂
  have hVsup : ∀ L' : ι, Pt L' ≤ Subgroup.normalizer
      ((V₁ ⊔ V₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :
        Set (H ⧸ primeComplementCore (G := H) 3)) := fun L' => h12 ▸ hV₀N L'
  refine ⟨V₁, V₂, i₁.1, i₂.1, hweak i₁, hweak i₂, hNH i₁, hNH i₂, hp1, hp2, hcomm, hc₁, hc₂,
    hi₁, hi₂, hVsup i₁, hVsup i₂, fun hne => ?_⟩
  have hne' : i₁ ≠ i₂ := fun h => hne (congrArg Subtype.val h)
  have hVc : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb => by
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  exact ⟨le_normalizer_of_commute_blocks (hbc i₁ i₂ hne') hi₁ hi₂ hVc (hVsup i₁) hs₂ hnab₂,
    le_normalizer_of_commute_blocks (hbc i₂ i₁ hne'.symm) hi₂ hi₁
      (fun b hb a ha => (hVc a ha b hb).symm) (by rw [sup_comm]; exact hVsup i₂) hs₁ hnab₁⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
