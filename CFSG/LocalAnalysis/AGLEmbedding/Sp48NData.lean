module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NPiece
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Data

public section


namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

theorem stmtSp48NData_of (hSoc : StmtChevTwoSocle) (hSurv : StmtSp48Surv)
    (hKN : KFactSp48NonsolvLocal) : StmtSp48NData := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq hcent d hd e hns
  obtain ⟨hZ, -, ⟨eK⟩, hsoc⟩ :=
    hSoc G 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inr (Or.inl ⟨rfl, hd⟩)) e
  have hC := hcfg.centralizer_eq_bot hK huniq hcent hZ
  obtain ⟨hS, hZU⟩ := hSurv hd ⟨eK⟩ hsoc
  obtain ⟨A₀, V₀, hI⟩ := hKN _ K d hd (normal_of_forall_isComponentOf_eq hK huniq) ⟨eK⟩ hC
    Rbar _ hcfg.red.three_le_pRank hcfg.red.weakCore_le hcfg.red.ne_top hns
  rw [hcfg.rbar] at hI
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hRH : R ≤ H := hcfg.ext.le_H
  have hR3 : IsPGroup 3 R := hcfg.ext.isPGroup
  have hNM : GLBPrimeCore 3 H ≤ M := hcfg.ext.primeCore_le
  set T := (R.subgroupOf H).map π with hT
  set U := d1LiftX 3 H R K with hUdef
  have hUR : U ≤ R := d1LiftX_le 3 H R K
  have hUmap : (U.subgroupOf H).map π = T ⊓ K := map_d1LiftX 3 H R K
  have hZmap : ((centerOf R).subgroupOf H).map π = centerOf T := map_inf_centralizer_eq hRH hR3
  set A := R ⊓ (A₀.comap π).map H.subtype with hAdef
  have hAR : A ≤ R := inf_le_left
  have hAmap : (A.subgroupOf H).map π = A₀ := map_inf_preimage hI.A_le
  have hcard : ∀ Z : Subgroup G, Z ≤ R → Nat.card Z = Nat.card ((Z.subgroupOf H).map π) :=
    fun Z hZR => by
      have hZp : IsPGroup 3 (Z.subgroupOf H) := (hR3.to_le hZR).comap_subtype
      rw [hπ, card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hZp,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZR.trans hRH)).toEquiv]
  have hXelem : IsElemAbelian 3 (centerOf R) := by
    refine isElemAbelian_of_map hRH hR3 inf_le_left ?_ ?_
    · rw [hZmap]
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
    · rw [hZmap]
      exact hI.center_pow
  have hAelem : IsElemAbelian 3 A := by
    refine isElemAbelian_of_map hRH hR3 hAR ?_ ?_
    · rw [hAmap]
      exact hI.A_comm
    · rw [hAmap]
      exact hI.A_pow
  have hXA : centerOf R ≤ A := le_of_map_le_of_isPGroup hRH hR3 inf_le_left hAR
    (by rw [hZmap, hAmap]; exact hI.center_le_A)
  obtain ⟨V, hVmap, hpiece⟩ := exists_sp48NPiece hI
  have hVK : V ≤ H ⊓ M := hpiece.2.1
  have hVH : V ≤ H := hVK.trans inf_le_left
  have hfac := sp48NFactors_of hI hRH rfl hVK hVmap
  have hUV : U ≤ V ⊔ GLBPrimeCore 3 H :=
    le_sup_glbPrimeCore_of_map_le (hUR.trans hRH) (by rw [hUmap, hVmap]; exact hI.TK_le_V)
  have hsyl : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
      ¬ Y ≤ GLBPrimeCore 3 H → R ⊓ Y = U ∨ R ⊓ Y = R := by
    intro Y hYK hYN hYnN
    have hYH : Y ≤ H := hYK.trans inf_le_left
    have hYb : (Y.subgroupOf H).map π ≤ ((H ⊓ M).subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.comap_mono hYK)
    have hYn := map_mk_le_normalizer_map_mk (H := H) (p := 3) hYN
    have hVY : V₀ ≤ (Y.subgroupOf H).map π := by
      rcases hI.minimal _ hYb hYn with h1 | h1
      · exact absurd (le_glbPrimeCore_of_map_eq_bot hYH h1) hYnN
      · exact h1
    have hW := hI.sylow_normal _ hYb hYn hVY
    rw [← map_inf_eq_of_normal hNM hR3 hYN] at hW
    have hinj : ∀ Z : Subgroup G, Z ≤ R → ((R ⊓ Y).subgroupOf H).map π = (Z.subgroupOf H).map π →
        R ⊓ Y = Z := fun Z hZR he =>
      le_antisymm (le_of_map_le_of_isPGroup hRH hR3 inf_le_left hZR he.le)
        (le_of_map_le_of_isPGroup hRH hR3 hZR inf_le_left he.ge)
    rcases hW with h1 | h1
    · exact Or.inl (hinj _ hUR (h1.trans hUmap.symm))
    · exact Or.inr (hinj _ le_rfl h1)
  have hhomo : ∃ u v : G, u ∈ U ∧ v ∈ U ∧ orderOf u = 9 ∧ orderOf v = 9 ∧ u * v = v * u ∧
      Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
    obtain ⟨ub, vb, hub, hvb, hu9, hv9, huv, hbot⟩ := hI.homocyclic
    rw [← hUmap] at hub hvb
    obtain ⟨u, hu, rfl⟩ := hub
    obtain ⟨v, hv, rfl⟩ := hvb
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hvU : (v : G) ∈ U := Subgroup.mem_subgroupOf.mp hv
    have huR := hUR huU
    have hvR := hUR hvU
    refine ⟨u, v, huU, hvU, ?_, ?_, ?_, ?_⟩
    · rw [← orderOf_mk_eq_of_isPGroup hRH hR3 huR]
      exact hu9
    · rw [← orderOf_mk_eq_of_isPGroup hRH hR3 hvR]
      exact hv9
    · refine eq_of_map_eq_of_isPGroup' hRH hR3 (R.mul_mem huR hvR) (R.mul_mem hvR huR) ?_
      have e1 : π ⟨(u : G) * v, hRH (R.mul_mem huR hvR)⟩ = π u * π v := by rw [← map_mul]; rfl
      have e2 : π ⟨(v : G) * u, hRH (R.mul_mem hvR huR)⟩ = π v * π u := by rw [← map_mul]; rfl
      rw [e1, e2, huv]
    · rw [eq_bot_iff]
      rintro x ⟨⟨n, rfl⟩, ⟨m, hm⟩⟩
      have hxR : (u : G) ^ n ∈ R := R.zpow_mem huR n
      have hx1 : π ⟨(u : G) ^ n, hRH hxR⟩ ∈ Subgroup.zpowers (π u) ⊓ Subgroup.zpowers (π v) := by
        refine ⟨⟨n, ?_⟩, ⟨m, ?_⟩⟩
        · show (π u) ^ n = π ⟨(u : G) ^ n, hRH hxR⟩
          rw [← map_zpow]
          rfl
        · have e : (⟨(u : G) ^ n, hRH hxR⟩ : H) = v ^ m := Subtype.ext (by simpa using hm.symm)
          show (π v) ^ m = π ⟨(u : G) ^ n, hRH hxR⟩
          rw [e, map_zpow]
      rw [hbot, Subgroup.mem_bot] at hx1
      have := eq_of_map_eq_of_isPGroup' hRH hR3 hxR R.one_mem (hx1.trans (map_one π).symm)
      exact Subgroup.mem_bot.mpr this
  have hnine : ∀ a ∈ A, a ∉ centerOf R → ∀ W : Fin 3 → Subgroup G,
      ∃ u ∈ U, ∀ i, (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≠ W i := by
    intro a haA haX W
    have haR := hAR haA
    have hab : π ⟨a, hRH haR⟩ ∈ A₀ :=
      hAmap ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haA)
    have habX : π ⟨a, hRH haR⟩ ∉ centerOf T := by
      intro h
      apply haX
      rw [← hZmap] at h
      obtain ⟨z, hz, hza⟩ := h
      have hzZ : (z : G) ∈ centerOf R := Subgroup.mem_subgroupOf.mp hz
      have := eq_of_map_eq_of_isPGroup' hRH hR3 hzZ.1 haR hza
      rw [← this]
      exact hzZ
    obtain ⟨ub, hub, hu⟩ := hI.orbit_nine _ hab habX
      (fun i => ((W i ⊓ R).subgroupOf H).map π)
    rw [← hUmap] at hub
    obtain ⟨u, huU', rfl⟩ := hub
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp huU'
    have huR := hUR huU
    refine ⟨u, huU, fun i hi => hu i ?_⟩
    have hWR : W i ≤ R := by
      rw [← hi]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨n, rfl⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact R.mul_mem (R.mul_mem huR (R.zpow_mem haR n)) (R.inv_mem huR)
    show _ = ((W i ⊓ R).subgroupOf H).map π
    rw [inf_eq_left.mpr hWR, ← hi, map_conj_subgroupOf (Subgroup.zpowers_le.mpr (hRH haR)) u,
      map_zpowers_subgroupOf (hRH haR)]
  exact ⟨A, V, ⟨hS, le_rfl, by rw [hcard R le_rfl]; exact hI.card_T, hXelem,
    by rw [hcard (centerOf R) inf_le_left, hZmap, hI.card_center], hUR,
    by rw [hcard _ hUR, hUmap, hI.card_TK], hAR, hAelem,
    by rw [hcard _ hAR, hAmap, hI.card_A], hXA, hZU, hhomo, hnine, hpiece, hUV, hsyl, hfac⟩⟩

end CFSG.AGLEmbedding
