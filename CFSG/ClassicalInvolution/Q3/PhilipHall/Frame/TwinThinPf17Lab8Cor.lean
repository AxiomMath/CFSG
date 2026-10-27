module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem lab8_false_of_beta_member (hF7 : F7Cent K₀ π g)
    (J : AEIdent (fam K (conjSub g (piGen π))) 8)
    {α : Finset (Fin 8)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {M : Subgroup G} (hMF : M ∈ fam K (conjSub g (piGen π)))
    (hMβ : M ∈ betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π)
    (hlabM : (M.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h (!b))
    {N : Subgroup G}
    (hNβ : N ∈ betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π)
    {γ : Finset (Fin 8)} (hγ : γ.card = 4) (hγα : Disjoint γ α) {c : Bool}
    (hlabN : (N.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
      AE.memBar γ hγ c) : False := by
  classical
  have hn : 5 ≤ 8 := by norm_num
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K₀) := S.hs.hyp
  have hPΩ : fam K (conjSub g (piGen π)) ⊆ CoreAssembly.conjClass K₀ :=
    fun L hL => S.fam_mem hL
  have hKF := S.mem_fam_self
  have hNF : N ∈ fam K (conjSub g (piGen π)) := S.beta_subset_fam hNβ
  have hαγ : α ≠ γ := by
    rintro rfl
    have := disjoint_self.mp hγα
    rw [this] at h
    simp at h
  have hKN : ∀ x ∈ K, ∀ y ∈ N, x * y = y * x := by
    have hne : K ≠ N := by
      intro e
      rw [← e] at hlabN
      exact hαγ (AE.eq_of_memBar_eq' hn (hlab.symm.trans hlabN))
    exact S.commutes_of_map_comm_gen hPΩ J hk hKF hNF hne (by
      rw [hlab, hlabN]
      exact AE.comm_memBar_of_disjoint hγα.symm b c)
  have hMN : ∀ x ∈ M, ∀ y ∈ N, x * y = y * x := by
    have hne : M ≠ N := by
      intro e
      rw [e] at hlabM
      exact hαγ (AE.eq_of_memBar_eq' hn (hlabM.symm.trans hlabN))
    exact S.commutes_of_map_comm_gen hPΩ J hk hMF hNF hne (by
      rw [hlabM, hlabN]
      exact AE.comm_memBar_of_disjoint hγα.symm (!b) c)
  obtain ⟨u, a, c₀, ha, hc₀, hac, huO, huX', huX, hu1, ⟨hu, hφu⟩, l, hl, l', hl', hul⟩ :=
    S.lab8_pairInv J hlab hMF hMβ hlabM
  have huN : ∀ y ∈ N, y * u = u * y := by
    intro y hy
    rw [hul]
    calc y * (l * l') = (y * l) * l' := by group
      _ = (l * y) * l' := by rw [hKN l hl y hy]
      _ = l * (y * l') := by group
      _ = l * (l' * y) := by rw [hMN l' hl' y hy]
      _ = (l * l') * y := by group
  have hneK : ¬ ∀ k ∈ K, k * u = u * k := by
    intro hall
    refine AE.not_comm_memBar_pairVec hn h b ha hc₀ hac fun x hx => ?_
    rw [← hlab] at hx
    rw [← hφu]
    exact lab8_map_comm J hKF hu hall hx
  obtain ⟨d, b₁, c₁, hdα, hda, hdc, hb₁, hc₁, hbc⟩ :=
    TwinThinPf17Lab8.exists_cyc (α := α) h ha hc₀
  have hdb : d ≠ b₁ := fun e => hb₁ (e ▸ hdα)
  have hdc₁ : d ≠ c₁ := fun e => hc₁ (e ▸ hdα)
  obtain ⟨t, hφt, k3, ht3⟩ := lab8_lift_cyc J hdb hbc hdc₁
  set σ := TwinThinPf17Lab8.cycFin8 d b₁ c₁
  have hσa : σ a = a := TwinThinPf17Lab8.cycFin8_apply_of_ne (fun e => hda e.symm)
    (fun e => hb₁ (e ▸ ha)) (fun e => hc₁ (e ▸ ha))
  have hσc : σ c₀ = c₀ := TwinThinPf17Lab8.cycFin8_apply_of_ne (fun e => hdc e.symm)
    (fun e => hb₁ (e ▸ hc₀)) (fun e => hc₁ (e ▸ hc₀))
  have htu' : J.φ t * J.φ ⟨u, hu⟩ = J.φ ⟨u, hu⟩ * J.φ t := by
    rw [hφt, hφu, ← map_mul, ← map_mul,
      TwinThinPf17Lab8.ofPerm_comm_ofVec σ _ (TwinThinPf17Lab8.pairVec_perm_symm σ hσa hσc)]
  have htu : (t : G) * u = u * (t : G) := congrArg Subtype.val (J.comm_of_pow_three hk ht3 htu')
  have htX' : (t : G) ∈ conjSub g (piGen π) := (SetLike.ext_iff.mp S.fam_gen (t : G)).mp t.2
  have htconj : (t : G) * u * (t : G)⁻¹ = u := by rw [htu]; group
  have hYu : centLayer (CoreAssembly.conjClass K₀) u ≤ Subgroup.centralizer ({u} : Set G) :=
    centLayer_le fun L hL => hL.2
  have hπMu : ∀ L ∈ π, L ∈ centMembers (CoreAssembly.conjClass K₀) u := fun L hL =>
    ⟨S.mem_of_mem_pi hL, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (huX x (le_piGen hL hx))⟩
  have hthMu : ∀ L ∈ π, conjSub (t : G) L ∈ centMembers (CoreAssembly.conjClass K₀) u := by
    intro L hL
    have := conjSub_mem_centMembers hΩ.conjInvariant (n := (t : G)) (hπMu L hL)
    rwa [htconj] at this
  have hNMu : N ∈ centMembers (CoreAssembly.conjClass K₀) u :=
    ⟨hNβ.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (huN y hy)⟩
  have hXtY : conjSub (t : G) (piGen π) ≤ centLayer (CoreAssembly.conjClass K₀) u := by
    rw [← piGen_conj]
    exact piGen_le (by rintro _ ⟨L, hL, rfl⟩; exact le_centLayer (hthMu L hL))
  have hKgcomm : Commutes (conjSub g (piGen π)) (conjSub g K) := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp ((S.hos.conj_le_inf_centralizer S.hπ S.hg hy).2) x hx
  have htinv_fix : conjSub (t : G)⁻¹ (conjSub g K) = conjSub g K :=
    conjSub_eq_of_mem_of_commutes ((conjSub g (piGen π)).inv_mem htX') hKgcomm
  have hconjπ : ∀ M₁ ∈ π, ∃ w' ∈ centLayer (CoreAssembly.conjClass K₀) u,
      conjSub w' (conjSub g K) = conjSub (t : G) M₁ := by
    intro M₁ hM₁
    obtain ⟨x, hx, hxM⟩ := S.trans_pi _ S.hg M₁ hM₁
    refine ⟨(t : G) * x * (t : G)⁻¹, hXtY (conj_mem_conjSub hx), ?_⟩
    calc conjSub ((t : G) * x * (t : G)⁻¹) (conjSub g K)
        = conjSub (t : G) (conjSub x (conjSub (t : G)⁻¹ (conjSub g K))) := by
          rw [conjSub_mul, conjSub_mul]
      _ = conjSub (t : G) (conjSub x (conjSub g K)) := by rw [htinv_fix]
      _ = conjSub (t : G) M₁ := by rw [hxM]
  have hno : ¬ ∃ w ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub w (conjSub g K) = N := by
    rintro ⟨w, hw, hwK⟩
    have hwu : w * u = u * w := Subgroup.mem_centralizer_singleton_iff.mp (hYu hw)
    have h1 : conjSub w '' (conjSub g '' π) ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) N := by
      rw [← hwK]
      exact isMaxOrb_conj S.hos.graph (isMaxOrb_conj S.hos.graph S.hπ g) w
    have h2 : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) N :=
      (mem_betaOf_iff S.hos.graph S.hK S.hπ).mp hNβ
    have h3 : conjSub w '' (conjSub g '' π) = π := maxOrb_unique S.hos.graph hNβ.1 h1 h2
    have h4 : piGen π = conjSub w (conjSub g (piGen π)) := by
      calc piGen π = piGen (conjSub w '' (conjSub g '' π)) := by rw [h3]
        _ = conjSub w (conjSub g (piGen π)) := by rw [piGen_conj, piGen_conj]
    have h5 : u ∈ piGen π := by
      rw [h4]
      have h6 := conj_mem_conjSub (n := w) huX'
      have h7 : w * u * w⁻¹ = u := by rw [hwu]; group
      rwa [h7] at h6
    exact hneK (fun k hk' =>
      (Subgroup.mem_centralizer_iff.mp (S.pair_le_cent.1 hk') u h5).symm)
  have hcomm : ∀ M₁ ∈ π, Commutes N (conjSub (t : G) M₁) := by
    intro M₁ hM₁
    refine hF7 u huO huX hu1 N hNMu (conjSub (t : G) M₁) (hthMu M₁ hM₁) ?_
    rintro ⟨w, hw, hwN⟩
    obtain ⟨w', hw', hw'e⟩ := hconjπ M₁ hM₁
    apply hno
    refine ⟨w⁻¹ * w', (centLayer (CoreAssembly.conjClass K₀) u).mul_mem
      ((centLayer (CoreAssembly.conjClass K₀) u).inv_mem hw) hw', ?_⟩
    rw [conjSub_mul, hw'e, ← hwN, conjSub_inv_conjSub]
  have hNtβ : conjSub (t : G)⁻¹ N ∈
      betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π := by
    refine ⟨S.hos.graph.conjMem N hNβ.1 _, fun M₁ hM₁ => ?_⟩
    refine S.nbrAdj_of_comm (S.hos.graph.conjMem N hNβ.1 _) (S.mem_of_mem_pi hM₁) ?_ ?_
    · intro e
      obtain ⟨w', hw', hw'e⟩ := hconjπ M₁ hM₁
      apply hno
      refine ⟨w', hw', ?_⟩
      rw [hw'e, e, conjSub_conjSub_inv]
    · have := (hcomm M₁ hM₁).conjSub (t : G)⁻¹
      rw [conjSub_inv_conjSub] at this
      exact this
  have hKtβ : conjSub (t : G) K ∈
      betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π := by
    rcases block_betaOf S.hos.graph S.hK S.hπ (t : G) with hc | hd
    · rw [← hc]
      exact ⟨K, S.K_mem_beta, rfl⟩
    · exfalso
      exact Set.disjoint_left.mp hd ⟨conjSub (t : G)⁻¹ N, hNtβ, conjSub_conjSub_inv _ _⟩ hNβ
  obtain ⟨c', hlabt⟩ := TwinThinPf10.conj_memBar_perm hn σ α h b
  have hlabKt : ((conjSub (t : G) K).subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
      AE.memBar (α.map σ.toEmbedding) (TwinThinPf10.card_map_perm σ h) c' := by
    rw [S.map_conj_member J t K, hlab, hφt]
    exact hlabt
  obtain ⟨δ, hδ, c'', hδ', hlabδ⟩ := S.lab8_beta_labels J hlab hMβ hlabM _ hKtβ
  have hαδ := AE.eq_of_memBar_eq' hn (hlabKt.symm.trans hlabδ)
  have hne := TwinThinPf17Lab8.map_cycFin8_ne hdα hb₁ hc₁ ha hda.symm hdb hdc₁
  rcases hδ' with rfl | rfl
  · exact hne.1 hαδ
  · exact hne.2 hαδ

theorem beta_eq_pair_eight (hF7 : F7Cent K₀ π g)
    (J : AEIdent (fam K (conjSub g (piGen π))) 8)
    {α : Finset (Fin 8)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b) :
    betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π = {K, K'} := by
  have hn : 5 ≤ 8 := by norm_num
  have hlab' := S.twinLab8_core hF7 J hlab
  have hlabs := S.lab8_beta_labels J hlab S.K'_mem_beta hlab'
  apply Set.Subset.antisymm
  · intro L hL
    obtain ⟨δ, hδ, c, hδ', hLlab⟩ := hlabs L hL
    rcases hδ' with rfl | rfl
    ·
      have hLf := S.beta_subset_fam hL
      by_cases hcb : c = b
      · subst hcb
        left
        exact S.eq_of_map_le hn J hLf S.mem_fam_self (le_of_eq (hLlab.trans hlab.symm))
      · have hcb' : c = !b := by cases b <;> cases c <;> simp_all
        subst hcb'
        right
        exact S.eq_of_map_le hn J hLf S.twin_mem_fam (le_of_eq (hLlab.trans hlab'.symm))
    ·
      exact (S.lab8_false_of_beta_member hF7 J hlab S.twin_mem_fam S.K'_mem_beta hlab' hL hδ
        disjoint_compl_left hLlab).elim
  · rintro L (rfl | rfl)
    · exact S.K_mem_beta
    · exact S.K'_mem_beta

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
