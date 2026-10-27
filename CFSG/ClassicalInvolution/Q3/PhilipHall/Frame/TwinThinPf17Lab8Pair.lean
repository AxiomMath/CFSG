module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Beta
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Blk8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf16Odd
public import CFSG.ClassicalInvolution.Q3.TL3T58

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

theorem lab8_map_comm {m : ℕ} {P : Set (Subgroup G)} (I : AEIdent P m) {L : Subgroup G}
    (hL : L ∈ P) {u : G} (hu : u ∈ pSpan P) (h : ∀ k ∈ L, k * u = u * k)
    {x : AE.AEQ m} (hx : x ∈ (L.subgroupOf (pSpan P)).map I.φ) :
    x * I.φ ⟨u, hu⟩ = I.φ ⟨u, hu⟩ * x := by
  obtain ⟨k, hk, rfl⟩ := I.exists_of_mem_map hL hx
  rw [← map_mul, ← map_mul]
  exact congrArg I.φ (Subtype.ext (h k hk))

theorem lab8_lift_cyc {P : Set (Subgroup G)} (I : AEIdent P 8) {d b₁ c₁ : Fin 8} (hdb : d ≠ b₁)
    (hbc : b₁ ≠ c₁) (hdc : d ≠ c₁) :
    ∃ y : ↥(pSpan P), I.φ y = AE.mkQ 8 (AE.Wr.ofPerm (TwinThinPf17Lab8.cycFin8 d b₁ c₁)) ∧
      ∃ k : ℕ, y ^ 3 ^ k = 1 := by
  have hmem : AE.mkQ 8 (AE.Wr.ofPerm (TwinThinPf17Lab8.cycFin8 d b₁ c₁)) ∈ I.φ.range := by
    rw [I.range_eq]
    exact ⟨AE.Wr.ofPerm _, ⟨by simp [AE.Wr.wsum, AE.Wr.ofPerm], by
      simpa [AE.Wr.ofPerm] using TwinThinPf17Lab8.sign_cycFin8 hdb hbc⟩, rfl⟩
  have hx3 : AE.mkQ 8 (AE.Wr.ofPerm (TwinThinPf17Lab8.cycFin8 d b₁ c₁)) ^ 3 = 1 := by
    rw [← map_pow, AE.ofPerm_pow, TwinThinPf17Lab8.cycFin8_pow_three d b₁ c₁ hdb hbc hdc,
      AE.ofPerm_one, map_one]
  obtain ⟨y, hy, k, hk⟩ := I.exists_lift_pow_three hmem hx3
  exact ⟨y, hy, k, hk⟩

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem lab8_fam_eq : fam K (conjSub g (piGen π)) = conjSub g '' π := by
  ext L
  constructor
  · intro hL
    exact ⟨conjSub g⁻¹ L, S.conj_inv_mem_pi hL, conjSub_conjSub_inv g L⟩
  · exact fun hL => S.fam_of_conj_pi hL

theorem lab8_beta_labels (J : AEIdent (fam K (conjSub g (piGen π))) 8)
    {α : Finset (Fin 8)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {M : Subgroup G}
    (hMβ : M ∈ betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π)
    (hlabM : (M.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h (!b)) :
    ∀ L ∈ betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π,
      ∃ (δ : Finset (Fin 8)) (hδ : δ.card = 4) (c : Bool), (δ = α ∨ δ = αᶜ) ∧
        (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar δ hδ c := by
  have hn : 5 ≤ 8 := by norm_num
  set β := betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π with hβ
  set B : Set (Subgroup (AE.AEQ 8)) :=
    {M | ∃ L ∈ β, M = (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ}
  have hinj : ∀ {L₁ L₂ : Subgroup G}, L₁ ∈ fam K (conjSub g (piGen π)) →
      L₂ ∈ fam K (conjSub g (piGen π)) →
      (L₁.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
        (L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ → L₁ = L₂ :=
    fun h₁ h₂ he => S.eq_of_map_le hn J h₁ h₂ (le_of_eq he)
  have hblock : TwinThinPf8.IsBlock B := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨L, hL, rfl⟩
      obtain ⟨β', hβ', c, hl⟩ := J.label L (S.beta_subset_fam hL)
      exact ⟨β', hβ', c, hl⟩
    · intro s hs
      have hs' : s ∈ J.φ.range := by rw [J.range_eq]; exact hs
      obtain ⟨x, rfl⟩ := hs'
      have hxX : (x : G) ∈ conjSub g (piGen π) := (SetLike.ext_iff.mp S.fam_gen (x : G)).mp x.2
      rcases block_betaOf S.hos.graph S.hK S.hπ (x : G) with hc | hc
      · left
        ext M
        constructor
        · rintro ⟨M0, ⟨L, hL, rfl⟩, rfl⟩
          have : conjSub (x : G) L ∈ β := by rw [hβ, ← hc]; exact ⟨L, hL, rfl⟩
          exact ⟨conjSub (x : G) L, this, (S.map_conj_member J x L).symm⟩
        · rintro ⟨L', hL', rfl⟩
          have : L' ∈ conjSub (x : G) '' β := by rw [hc]; exact hL'
          obtain ⟨L, hL, rfl⟩ := this
          exact ⟨_, ⟨L, hL, rfl⟩, (S.map_conj_member J x L).symm⟩
      · right
        refine Set.disjoint_left.mpr ?_
        rintro M ⟨M0, ⟨L, hL, rfl⟩, rfl⟩ ⟨L2, hL2, hM⟩
        have hLf : L ∈ fam K (conjSub g (piGen π)) := S.beta_subset_fam hL
        have h1 : conjSub (x : G) L ∈ fam K (conjSub g (piGen π)) := fam_inv L hLf (x : G) hxX
        have h2 := hinj h1 (S.beta_subset_fam hL2)
          ((S.map_conj_member J x L).trans hM)
        exact Set.disjoint_left.mp hc ⟨L, hL, rfl⟩ (h2 ▸ hL2)
  have hKB : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ∈ B :=
    ⟨K, S.K_mem_beta, rfl⟩
  have hMB : (M.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ∈ B :=
    ⟨M, hMβ, rfl⟩
  have htrue : AE.memBar α h true ∈ B ∧ AE.memBar α h false ∈ B := by
    cases b
    · rw [hlab] at hKB
      rw [hlabM] at hMB
      exact ⟨hMB, hKB⟩
    · rw [hlab] at hKB
      rw [hlabM] at hMB
      exact ⟨hKB, hMB⟩
  intro L hL
  have hLB : (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ∈ B := ⟨L, hL, rfl⟩
  rcases TwinThinPf10.aeBlocks8' α h B hblock htrue.1 htrue.2 with hB2 | hB3 | hall
  · rw [hB2] at hLB
    rcases hLB with h1 | h1
    · exact ⟨α, h, true, Or.inl rfl, h1⟩
    · exact ⟨α, h, false, Or.inl rfl, h1⟩
  · obtain ⟨δ, hδ, c, hδ', hLe⟩ := hB3 _ hLB
    exact ⟨δ, hδ, c, hδ', hLe⟩
  · exfalso
    refine S.false_of_fam_le_beta fun L hL => ?_
    obtain ⟨β', hβ', c, hl⟩ := J.label L hL
    have : (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ∈ B :=
      hall _ ⟨β', hβ', c, hl⟩
    obtain ⟨L2, hL2, hL2e⟩ := this
    have := hinj hL (S.beta_subset_fam hL2) hL2e
    rw [this]; exact hL2

theorem lab8_ker_permHom_le_pCore {m : ℕ} (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    ((TL4.AECov.permHom J).ker.map (pSpan (fam K (conjSub g (piGen π)))).subtype) ≤
      pCoreOf 2 (conjSub g (piGen π)) := by
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  set N := (TL4.AECov.permHom J).ker
  have hN2 : IsPGroup 2 ↥N := by
    intro x
    have hsq : J.φ (x : ↥(pSpan (fam K (conjSub g (piGen π))))) *
        J.φ (x : ↥(pSpan (fam K (conjSub g (piGen π))))) = 1 :=
      mul_self_of_mem_ker_permQ ((TL4.AECov.mem_ker_permHom J).mp x.2)
    have hyy : (x : ↥(pSpan (fam K (conjSub g (piGen π))))) * x ∈ J.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hsq
    obtain ⟨k, hk'⟩ := hk ⟨_, hyy⟩
    have hk'' : ((x : ↥(pSpan (fam K (conjSub g (piGen π))))) * x) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk'
      simpa using this
    refine ⟨k + 1, Subtype.ext ?_⟩
    show (x : ↥(pSpan (fam K (conjSub g (piGen π))))) ^ 2 ^ (k + 1) = 1
    rw [pow_succ', pow_mul, pow_two]
    exact hk''
  have hQ2 : IsPGroup 2 ↥(N.map (pSpan (fam K (conjSub g (piGen π)))).subtype) :=
    hN2.map _
  have hQle : N.map (pSpan (fam K (conjSub g (piGen π)))).subtype ≤
      pSpan (fam K (conjSub g (piGen π))) := Subgroup.map_subtype_le N
  have hQn : ((N.map (pSpan (fam K (conjSub g (piGen π)))).subtype).subgroupOf
      (pSpan (fam K (conjSub g (piGen π))))).Normal := by
    have : (N.map (pSpan (fam K (conjSub g (piGen π)))).subtype).subgroupOf
        (pSpan (fam K (conjSub g (piGen π)))) = N :=
      Subgroup.comap_map_eq_self_of_injective
        (pSpan (fam K (conjSub g (piGen π)))).subtype_injective N
    rw [this]
    exact MonoidHom.normal_ker _
  have := CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hQle hQn hQ2
  exact this.trans (le_of_eq (by rw [S.fam_gen]))

theorem lab8_pairInv (J : AEIdent (fam K (conjSub g (piGen π))) 8)
    {α : Finset (Fin 8)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {M : Subgroup G} (hMF : M ∈ fam K (conjSub g (piGen π)))
    (hMβ : M ∈ betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π)
    (hlabM : (M.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h (!b)) :
    ∃ (u : G) (a c : Fin 8), a ∈ α ∧ c ∈ α ∧ a ≠ c ∧
      u ∈ pCoreOf 2 (conjSub g (piGen π)) ∧ u ∈ conjSub g (piGen π) ∧
      (∀ x ∈ piGen π, x * u = u * x) ∧ u ≠ 1 ∧
      (∃ hu : u ∈ pSpan (fam K (conjSub g (piGen π))),
        J.φ ⟨u, hu⟩ = AE.mkQ 8 (AE.Wr.ofVec (TL4.pairVec a c))) ∧
      (∃ l ∈ K, ∃ l' ∈ M, u = l * l') := by
  obtain ⟨l, hl, l', hl', a, ha, c, hc, hac, hll, hI⟩ :=
    J.exists_mul_eq_pairVec S.mem_fam_self hMF hlab hlabM
  have hlX : ∀ x ∈ piGen π, x * l = l * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (S.pair_le_cent.1 hl) x hx
  have hl'X : ∀ x ∈ piGen π, x * l' = l' * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (S.hos.beta_le_centralizer hMβ hl') x hx
  refine ⟨l * l', a, c, ha, hc, hac, ?_, ?_, ?_, ?_, ⟨hll, hI⟩, ⟨l, hl, l', hl', rfl⟩⟩
  · refine S.lab8_ker_permHom_le_pCore J
      ⟨⟨l * l', hll⟩, (TL4.AECov.mem_ker_permHom J).mpr ?_, rfl⟩
    show permQ 8 (J.φ ⟨l * l', hll⟩) = 1
    rw [hI]
    rfl
  · rw [← S.fam_gen]
    exact hll
  · intro x hx
    calc x * (l * l') = (x * l) * l' := by group
      _ = (l * x) * l' := by rw [hlX x hx]
      _ = l * (x * l') := by group
      _ = l * (l' * x) := by rw [hl'X x hx]
      _ = (l * l') * x := by group
  · intro h1
    apply AE.vbar_pairVec_ne_one (by norm_num) hac
    rw [← hI]
    have : (⟨l * l', hll⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) = 1 := Subtype.ext h1
    rw [this, map_one]

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
