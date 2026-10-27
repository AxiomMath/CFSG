module

public import CFSG.ClassicalInvolution.Q3.TL3T78
public import CFSG.ClassicalInvolution.Q3.TL3T60
public import CFSG.ClassicalInvolution.Q3.TL3T72D
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Blk8
public import CFSG.ClassicalInvolution.Q3.TL3T56

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem yOf_supportedOn_three (ι : Fin 4 ↪ Fin n) : SupportedOn (yOf ι) {ι 0, ι 1, ι 2} := by
  intro x hx
  refine ⟨?_, ?_⟩
  · show embedVec ι (0 : Fin 4 → ZMod 2) x = 0
    by_cases hr : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hr
      rw [embedVec_apply]
      rfl
    · exact embedVec_of_not_mem ι _ hr
  · show embedPerm ι (Equiv.swap 0 1 * Equiv.swap 1 2) x = x
    by_cases hr : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hr
      rw [embedPerm_apply]
      fin_cases i
      · exact absurd (by simp) hx
      · exact absurd (by simp) hx
      · exact absurd (by simp) hx
      · exact congrArg ι (by decide)
    · exact embedPerm_of_not_mem ι _ hr

theorem supportedOn_ofPerm {σ : Equiv.Perm (Fin n)} {s : Set (Fin n)} (h : ∀ x ∉ s, σ x = x) :
    SupportedOn (ofPerm σ) s := fun x hx => ⟨rfl, h x hx⟩

theorem exists_perm_moving (α : Finset (Fin 8)) (hα : α.card = 4) :
    ∃ σ : Equiv.Perm (Fin 8), σ ∈ alternatingGroup (Fin 8) ∧
      yBar α hα * mkQ 8 (ofPerm σ) = mkQ 8 (ofPerm σ) * yBar α hα ∧
      α.map σ.toEmbedding ≠ α ∧ α.map σ.toEmbedding ≠ αᶜ := by
  classical
  set ι := emb α hα with hι
  have hια : ∀ i, ι i ∈ α := fun i => by
    have : ι i ∈ Set.range ι := Set.mem_range_self i
    rw [hι, range_emb] at this
    exact this
  have hcc : (αᶜ).card = 4 := by rw [Finset.card_compl, hα]; simp
  obtain ⟨b₁, hb₁, c₁, hc₁, hbc⟩ := Finset.one_lt_card.mp (by rw [hcc]; norm_num : 1 < (αᶜ).card)
  rw [Finset.mem_compl] at hb₁ hc₁
  set a := ι 3 with ha
  have haα : a ∈ α := hια 3
  have hab : a ≠ b₁ := fun e => hb₁ (e ▸ haα)
  have hac : a ≠ c₁ := fun e => hc₁ (e ▸ haα)
  set σ : Equiv.Perm (Fin 8) := Equiv.swap a b₁ * Equiv.swap b₁ c₁ with hσ
  have hσfix : ∀ x, x ≠ a → x ≠ b₁ → x ≠ c₁ → σ x = x := fun x h1 h2 h3 => by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h2 h3,
      Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hσa : σ a = b₁ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, hσ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hbc]
    decide
  · have hsupp : SupportedOn (ofPerm σ) {a, b₁, c₁} :=
      supportedOn_ofPerm fun x hx => hσfix x (fun e => hx (by simp [e]))
        (fun e => hx (by simp [e])) (fun e => hx (by simp [e]))
    have hdisj : Disjoint ({ι 0, ι 1, ι 2} : Set (Fin 8)) {a, b₁, c₁} := by
      rw [Set.disjoint_left]
      rintro x hx hx'
      have hxα : x ∈ α := by
        rcases hx with rfl | rfl | rfl <;> exact hια _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
      rcases hx' with rfl | rfl | rfl
      · rcases hx with h | h | h <;> have := ι.injective h <;> revert this <;> decide
      · exact hb₁ hxα
      · exact hc₁ hxα
    have hcomm := comm_of_disjoint (yOf_supportedOn_three ι) hsupp hdisj
    rw [yBar, ← map_mul, ← map_mul, ← hι, hcomm]
  · intro h
    have hb : b₁ ∈ α.map σ.toEmbedding := Finset.mem_map.mpr ⟨a, haα, hσa⟩
    rw [h] at hb
    exact hb₁ hb
  · intro h
    have h0 : σ (ι 0) = ι 0 := by
      refine hσfix _ (fun e => ?_) (fun e => hb₁ (e ▸ hια 0)) (fun e => hc₁ (e ▸ hια 0))
      have := ι.injective e
      revert this
      decide
    have h0m : ι 0 ∈ α.map σ.toEmbedding := Finset.mem_map.mpr ⟨ι 0, hια 0, h0⟩
    rw [h, Finset.mem_compl] at h0m
    exact h0m (hια 0)

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10 (aeBlocks8')

section Blocks

variable {G : Type} [Group G] {P : Set (Subgroup G)}

theorem AEIdent.blocks_eight (I : AEIdent P 8)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {B : Set (Subgroup G)} (hBP : B ⊆ P)
    (hblock : ∀ x ∈ pSpan P, (∃ M ∈ B, conjSub x M ∈ B) → ∀ M ∈ B, conjSub x M ∈ B)
    {K₀ K₁ : Subgroup G} (hK₀ : K₀ ∈ B) (hK₁ : K₁ ∈ B) {α : Finset (Fin 8)} (hα : α.card = 4)
    {b₀ : Bool} (hlab₀ : (K₀.subgroupOf (pSpan P)).map I.φ = memBar α hα b₀)
    (hlab₁ : (K₁.subgroupOf (pSpan P)).map I.φ = memBar α hα (!b₀)) :
    (∀ M ∈ B, M = K₀ ∨ M = K₁) ∨
      (∀ M ∈ B, ∃ (β : Finset (Fin 8)) (hβ : β.card = 4) (c : Bool), (β = α ∨ β = αᶜ) ∧
        (M.subgroupOf (pSpan P)).map I.φ = memBar β hβ c) ∨ ∀ M ∈ P, M ∈ B := by
  classical
  have hrange : ∀ w ∈ PhilipHall.Frame.TwinThinPf8.Hn 8, ∃ x : ↥(pSpan P), I.φ x = w := by
    intro w hw
    have hw' : w ∈ I.φ.range := by rw [I.range_eq]; exact hw
    exact hw'
  set lab : Subgroup G → Subgroup (AEQ 8) := fun L => (L.subgroupOf (pSpan P)).map I.φ with hlab
  have hlabc : ∀ (L : Subgroup G) (x : ↥(pSpan P)),
      lab (conjSub (x : G) L) = conjSub (I.φ x) (lab L) :=
    fun L x => TL4.AECov.map_conjSub_eq I L x
  set B' : Set (Subgroup (AEQ 8)) := lab '' B with hB'
  have hblk : PhilipHall.Frame.TwinThinPf8.IsBlock B' := by
    refine ⟨?_, fun s hs => ?_⟩
    · rintro _ ⟨L, hL, rfl⟩
      obtain ⟨β, hβ, c, h⟩ := I.label L (hBP hL)
      exact ⟨β, hβ, c, h⟩
    · obtain ⟨x, hx⟩ := hrange s hs
      by_cases hex : ∃ M ∈ B, conjSub (x : G) M ∈ B
      · left
        have hall := hblock x x.2 hex
        have hall' : ∀ M ∈ B, conjSub (x : G)⁻¹ M ∈ B := by
          obtain ⟨M₁, hM₁, hxM₁⟩ := hex
          exact hblock (x : G)⁻¹ ((pSpan P).inv_mem x.2)
            ⟨conjSub x M₁, hxM₁, by rw [conjSub_inv_conjSub]; exact hM₁⟩
        ext N
        constructor
        · rintro ⟨_, ⟨L, hL, rfl⟩, rfl⟩
          refine ⟨conjSub x L, hall L hL, ?_⟩
          show lab (conjSub (x : G) L) = conjSub s (lab L)
          rw [hlabc, hx]
        · rintro ⟨L, hL, rfl⟩
          refine ⟨_, ⟨conjSub (x : G)⁻¹ L, hall' L hL, rfl⟩, ?_⟩
          show conjSub s (lab (conjSub (x : G)⁻¹ L)) = lab L
          rw [← hx, ← hlabc, conjSub_conjSub_inv]
      · right
        rw [Set.disjoint_left]
        rintro _ ⟨_, ⟨L, hL, rfl⟩, rfl⟩ ⟨L', hL', hL'e⟩
        apply hex
        refine ⟨L, hL, ?_⟩
        have h1 : lab (conjSub (x : G) L) = lab L' := by
          rw [hlabc, hx]
          exact hL'e.symm
        rw [hinj _ (hconj L (hBP hL) x x.2) L' (hBP hL') h1]
        exact hL'
  have hT : memBar α hα true ∈ B' ∧ memBar α hα false ∈ B' := by
    cases b₀
    · exact ⟨⟨K₁, hK₁, hlab₁⟩, ⟨K₀, hK₀, hlab₀⟩⟩
    · exact ⟨⟨K₀, hK₀, hlab₀⟩, ⟨K₁, hK₁, hlab₁⟩⟩
  rcases aeBlocks8' α hα B' hblk hT.1 hT.2 with h | h | h
  · left
    intro M hM
    have hmem : lab M ∈ ({memBar α hα true, memBar α hα false} : Set (Subgroup (AEQ 8))) := by
      rw [← h]
      exact ⟨M, hM, rfl⟩
    rcases hmem with h1 | h1 <;> cases b₀
    · exact Or.inr (hinj M (hBP hM) K₁ (hBP hK₁) (h1.trans hlab₁.symm))
    · exact Or.inl (hinj M (hBP hM) K₀ (hBP hK₀) (h1.trans hlab₀.symm))
    · exact Or.inl (hinj M (hBP hM) K₀ (hBP hK₀) (h1.trans hlab₀.symm))
    · exact Or.inr (hinj M (hBP hM) K₁ (hBP hK₁) (h1.trans hlab₁.symm))
  · right
    left
    intro M hM
    exact h (lab M) ⟨M, hM, rfl⟩
  · right
    right
    intro M hM
    obtain ⟨β, hβ, c, h1⟩ := I.label M hM
    obtain ⟨M', hM', hM'e⟩ := h (lab M) ⟨β, hβ, c, h1⟩
    rw [hinj M hM M' (hBP hM') hM'e.symm]
    exact hM'

end Blocks

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

private theorem exists_exact_over_eight {P : Set (Subgroup G)} (I : AEIdent P 8)
    (hH : TL4.AECoverHyp I) {δ : Finset (Fin 8)} (hδ : δ.card = 4) :
    ∃ Γ : Finset (Fin 8), δ ⊆ Γ ∧ ∀ {x y : G} (hx : x ∈ pSpan (I.over Γ))
      (hy : y ∈ pSpan (I.over Γ)),
      I.φ ⟨x, I.pSpan_over_le Γ hx⟩ = I.φ ⟨y, I.pSpan_over_le Γ hy⟩ → x = y := by
  classical
  obtain ⟨p, hp⟩ := AE.Block4.exists_not_mem (s := δ) (by omega)
  set Γ := insert p δ with hΓ
  have hΓc : Γ.card = 5 := by rw [Finset.card_insert_of_notMem hp, hδ]
  obtain ⟨q, hq⟩ := AE.Block4.exists_not_mem (s := Γ) (by omega)
  have hodd : Odd Γ.card := by rw [hΓc]; decide
  exact ⟨Γ, Finset.subset_insert p δ, fun {x y} hx hy hxy =>
    I.eq_of_map_eq_over hH (by omega) hodd hq hx hy hxy⟩

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)
include hS

private theorem false_of_moving {g : G} {Ks : Subgroup G} {y : G} (hD : Data128 Ω K J g Ks y)
    (hy : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y) {h : G} (hhy : y * h = h * y)
    (hhJ : conjSub h J = J) (hhK : conjSub h K ∉ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J))
    {K' : Subgroup G} (hK' : K' ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J))
    (hK'y : ∀ k ∈ K', k * y = y * k) : False := by
  classical
  have hC := hS.toCHyp
  have hDh := hS.cex.toThmDHyp
  set π := orbOf (TC.nbrAdj Ω) K J with hπ
  have hF := hC.graphFam'
  have hKΩ : K ∈ Ω := hS.adj.1
  have hπΩ : π ⊆ Ω := hC.orb_subset_omega
  have hy1 : y ≠ 1 := fun e => hD.y_not_K fun k _ => by rw [e, one_mul, mul_one]
  have hlt := hS.card_pSpan_centMembers_lt hy1
  have hinvC : ∀ L ∈ centMembers Ω y, ∀ x ∈ pSpan (centMembers Ω y),
      conjSub x L ∈ centMembers Ω y := fun L hL x hx => hS.conjSub_mem_centMembers y hL hx
  have hπC : π ⊆ centMembers Ω y := fun M hM =>
    ⟨hπΩ hM, fun m hm => (hy m (le_pSpan hM hm)).symm⟩
  have hπhC : conjSub h '' π ⊆ centMembers Ω y := by
    rintro _ ⟨M, hM, rfl⟩
    exact hS.conjSub_mem_centMembers_of_comm hhy.symm (hπC hM)
  have hK'C : K' ∈ centMembers Ω y := ⟨hK'.1, hK'y⟩
  have hhJ' : conjSub h⁻¹ J = J :=
    calc conjSub h⁻¹ J = conjSub h⁻¹ (conjSub h J) := by rw [hhJ]
      _ = J := conjSub_inv_conjSub h J
  have hπh : ∀ M ∈ π, ∃ a ∈ pSpan (centMembers Ω y), conjSub a J = conjSub h M := by
    intro M hM
    obtain ⟨a, ha, haM⟩ := orbOf_subset_gen hF.graph hS.adj hM
    refine ⟨h * a * h⁻¹, ?_, ?_⟩
    · have h1 : h * a * h⁻¹ ∈ pSpan (conjSub h '' π) := by
        have := (pSpanConj h π ⟨a, ha⟩).2
        rwa [pSpanConj_apply] at this
      exact (pSpan_le fun L hL => le_pSpan (hπhC hL)) h1
    · rw [conjSub_mul (h * a) h⁻¹, hhJ', conjSub_mul h a, haM]
  by_cases hcase : ∃ w ∈ pSpan (centMembers Ω y), conjSub w J = K'
  ·
    obtain ⟨w, hw, hwJ⟩ := hcase
    have hwy : w * y = y * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (pSpan_centMembers_le (Ω := Ω) y hw)
    have h1 := isMaxOrb_conj hF hC.swap.max w
    rw [hwJ] at h1
    have h2 : conjSub w '' orbOf (TC.nbrAdj Ω) J K = π := maxOrb_unique hF hK'.1 h1 hK'.2
    have hyJ : y ∈ pSpan (orbOf (TC.nbrAdj Ω) J K) := by
      rw [← hC.orb_swap_eq hD.hg]
      exact hD.y_mem
    have hyX : y ∈ pSpan π := by
      have h3 : w * y * w⁻¹ ∈ pSpan (conjSub w '' orbOf (TC.nbrAdj Ω) J K) := by
        have := (pSpanConj w (orbOf (TC.nbrAdj Ω) J K) ⟨y, hyJ⟩).2
        rwa [pSpanConj_apply] at this
      rw [h2, show w * y * w⁻¹ = y by rw [hwy]; group] at h3
      exact h3
    have hle : pSpan π ≤ Subgroup.centralizer (K : Set G) :=
      hC.pSpan_orb_le.trans (pSpan_omegaNbr_le_centralizer hC.hyp hC.two hKΩ)
    exact hD.y_not_K fun k hk => (Subgroup.mem_centralizer_iff.mp (hle hyX) k hk).symm
  ·
    push Not at hcase
    apply hhK
    have hbadj : ∀ M₁ ∈ π, TC.nbrAdj Ω (conjSub h⁻¹ K') M₁ := by
      intro M₁ hM₁
      obtain ⟨a, ha, haM⟩ := hπh M₁ hM₁
      have hM₁C : conjSub h M₁ ∈ centMembers Ω y := hπhC ⟨M₁, hM₁, rfl⟩
      have hnc : ¬ ∃ x ∈ pSpan (centMembers Ω y), conjSub x K' = conjSub h M₁ := by
        rintro ⟨x, hx, hxK⟩
        refine hcase (x⁻¹ * a) (mul_mem (inv_mem hx) ha) ?_
        rw [conjSub_mul, haM, ← hxK, conjSub_inv_conjSub]
      have hcomm := comm_of_not_conj_span hDh hS.d1 (fun _ hM => hM.1) hlt hinvC hK'C hM₁C hnc
      have hcomm' : ∀ a ∈ conjSub h⁻¹ K', ∀ b ∈ M₁, a * b = b * a := by
        have := comm_conjSub hcomm h⁻¹
        rwa [conjSub_inv_conjSub] at this
      have hne : M₁ ≠ conjSub h⁻¹ K' := by
        intro e
        apply hnc
        refine ⟨1, (pSpan _).one_mem, ?_⟩
        rw [conjSub_one, e, conjSub_conjSub_inv]
      exact hC.nbrAdj_of_comm (hC.hyp.conjInvariant h⁻¹ K' hK'.1) (hπΩ hM₁) hne hcomm'
    have hβ' : conjSub h⁻¹ K' ∈ maxOrbSet Ω π :=
      hC.mem_maxOrbSet_of_adj (hC.hyp.conjInvariant h⁻¹ K' hK'.1) hbadj
    exact hC.conjSub_mem_maxOrbSet hβ' (by rw [conjSub_conjSub_inv]; exact hK')
      hC.mem_maxOrbSet_self

theorem maxOrbSet_eq_eight (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {g : G} {Ks : Subgroup G} {y : G} (hD : Data128 Ω K J g Ks y)
    (hy : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y)
    {α : Finset (Fin 8)} {hα : α.card = 4} {b : Bool}
    {y₀ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))} (hy₀ : I.φ y₀ = AE.yBar α hα)
    (hy₀y : (y₀ : G) = g⁻¹ * y * g)
    (hlab₀ : ((conjSub g⁻¹ K).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      AE.memBar α hα b)
    (hlab₁ : ((conjSub g⁻¹ Ks).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      AE.memBar α hα (!b)) :
    ∀ M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J), M = K ∨ M = Ks := by
  classical
  revert I hy y₀ hy₀ hy₀y hlab₀ hlab₁
  set π := orbOf (TC.nbrAdj Ω) K J with hπ
  intro I hy y₀ hy₀ hy₀y hlab₀ hlab₁
  have hC := hS.toCHyp
  have hKΩ : K ∈ Ω := hS.adj.1
  have hπΩ : π ⊆ Ω := hC.orb_subset_omega
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hC.oddCore_orb_eq_bot
  have hinj : ∀ L ∈ π, ∀ L' ∈ π, (L.subgroupOf (pSpan π)).map I.φ =
      (L'.subgroupOf (pSpan π)).map I.φ → L = L' := fun L hL L' hL' h =>
    aeIdent_eq_of_map_eq hC.hyp hC.two hπΩ (by norm_num) I hk hL hL' h
  have hconj : ∀ L ∈ π, ∀ x ∈ pSpan π, conjSub x L ∈ π := fun L hL x hx =>
    CSetting.conjSub_mem_orb hKΩ (hC.pSpan_orb_le hx) hL
  obtain ⟨hKsΩ, hKsπ, hKsX⟩ := hC.ks_comm_of_y_comm hD hy
  have horb : conjSub g '' π = orbOf (TC.nbrAdj Ω) J K := hC.orb_swap_eq hD.hg
  have hKsB : Ks ∈ maxOrbSet Ω π := by
    refine hC.mem_maxOrbSet_of_adj hKsΩ.1 fun L hL => hC.nbrAdj_of_comm hKsΩ.1 (hπΩ hL)
      (fun e => hKsπ (e ▸ hL)) fun a ha b hb => ?_
    exact (hKsX b (le_pSpan hL hb) a ha).symm
  have hKB : K ∈ maxOrbSet Ω π := hC.mem_maxOrbSet_self
  have hcc : ∀ (x : G) (M : Subgroup G),
      conjSub x (conjSub g⁻¹ M) = conjSub g⁻¹ (conjSub (g * x * g⁻¹) M) := by
    intro x M
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  set B' : Set (Subgroup G) := conjSub g⁻¹ '' maxOrbSet Ω π with hB'
  have hB'π : B' ⊆ π := by
    rintro _ ⟨M, hM, rfl⟩
    have h1 : M ∈ conjSub g '' π := horb ▸ hC.mem_orb_swap_of_mem_maxOrbSet hM
    obtain ⟨L, hL, rfl⟩ := h1
    rwa [conjSub_inv_conjSub]
  have hblock : ∀ x ∈ pSpan π, (∃ M ∈ B', conjSub x M ∈ B') → ∀ M ∈ B', conjSub x M ∈ B' := by
    rintro x - ⟨_, ⟨M₀, hM₀, rfl⟩, N₁, hN₁, hN₁e⟩ _ ⟨M, hM, rfl⟩
    rw [hcc] at hN₁e
    have hx₁ : N₁ = conjSub (g * x * g⁻¹) M₀ := conjSub_injective g⁻¹ hN₁e
    exact ⟨conjSub (g * x * g⁻¹) M, hC.conjSub_mem_maxOrbSet hM₀ (hx₁ ▸ hN₁) hM, (hcc x M).symm⟩
  rcases AEIdent.blocks_eight I hconj hinj hB'π hblock ⟨K, hKB, rfl⟩ ⟨Ks, hKsB, rfl⟩ hα hlab₀ hlab₁
    with h3 | h3 | h3
  ·
    intro M hM
    rcases h3 _ ⟨M, hM, rfl⟩ with h | h
    · exact Or.inl (conjSub_injective g⁻¹ h)
    · exact Or.inr (conjSub_injective g⁻¹ h)
  ·
    by_contra hcon
    push Not at hcon
    obtain ⟨K', hK'β, hK'K, hK'Ks⟩ := hcon
    obtain ⟨β₁, hβ₁, c₁, hβα, hlab'⟩ := h3 _ ⟨K', hK'β, rfl⟩
    have hK''π : conjSub g⁻¹ K' ∈ π := hB'π ⟨K', hK'β, rfl⟩
    have hK₀π : conjSub g⁻¹ K ∈ π := hB'π ⟨K, hKB, rfl⟩
    have hK₁π : conjSub g⁻¹ Ks ∈ π := hB'π ⟨Ks, hKsB, rfl⟩
    have hβ₁c : β₁ = αᶜ := by
      rcases hβα with h | h
      · exfalso
        subst h
        have hbb : c₁ = b ∨ c₁ = !b := by cases b <;> cases c₁ <;> simp
        rcases hbb with rfl | rfl
        · exact hK'K (conjSub_injective g⁻¹ (hinj _ hK''π _ hK₀π (hlab'.trans hlab₀.symm)))
        · exact hK'Ks (conjSub_injective g⁻¹ (hinj _ hK''π _ hK₁π (hlab'.trans hlab₁.symm)))
      · exact h
    subst hβ₁c
    obtain ⟨a₀, ha₀⟩ := hD.y_pow
    have hy₀pow : y₀ ^ 3 ^ a₀ = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, hy₀y, Subgroup.coe_one, show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by
        rw [inv_inv], conj_pow, ha₀, mul_one, mul_inv_cancel]
    have hK'y : ∀ k ∈ K', k * y = y * k := by
      intro k hkK'
      have hk' : g⁻¹ * k * g ∈ conjSub g⁻¹ K' := by
        simpa using conj_mem_conjSub (n := g⁻¹) hkK'
      have hcw : I.φ y₀ * I.φ ⟨g⁻¹ * k * g, le_pSpan hK''π hk'⟩ =
          I.φ ⟨g⁻¹ * k * g, le_pSpan hK''π hk'⟩ * I.φ y₀ := by
        rw [hy₀]
        refine AE.yBar_comm_memBar_of_disjoint (h := hα) (h' := hβ₁) disjoint_compl_right c₁ _ ?_
        rw [← hlab']
        exact I.mem_map hK''π hk'
      have e := congrArg Subtype.val (I.comm_of_pow_three hk hy₀pow hcw)
      change (y₀ : G) * (g⁻¹ * k * g) = (g⁻¹ * k * g) * y₀ at e
      rw [hy₀y] at e
      calc k * y = g * ((g⁻¹ * k * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * k * g)) * g⁻¹ := by rw [e]
        _ = y * k := by group
    obtain ⟨σ, hσA, hσcomm, hσα, hσαc⟩ := AE.exists_perm_moving α hα
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : ↥(pSpan π), I.φ h₀ = mkQ 8 (ofPerm σ) := by
      have : mkQ 8 (ofPerm σ) ∈ I.φ.range := by
        rw [I.range_eq]
        exact mem_aeModel_ofPerm hσA
      exact this
    have hh₀y : y₀ * h₀ = h₀ * y₀ :=
      I.comm_of_pow_three hk hy₀pow (by rw [hy₀, hh₀]; exact hσcomm)
    have hhy : y * (g * (h₀ : G) * g⁻¹) = (g * (h₀ : G) * g⁻¹) * y := by
      have e := congrArg Subtype.val hh₀y
      change (y₀ : G) * h₀ = h₀ * y₀ at e
      rw [hy₀y] at e
      calc y * (g * (h₀ : G) * g⁻¹) = g * ((g⁻¹ * y * g) * h₀) * g⁻¹ := by group
        _ = g * (h₀ * (g⁻¹ * y * g)) * g⁻¹ := by rw [e]
        _ = (g * (h₀ : G) * g⁻¹) * y := by group
    have hhJ : conjSub (g * (h₀ : G) * g⁻¹) J = J := by
      have hmem : g * (h₀ : G) * g⁻¹ ∈ pSpan (orbOf (TC.nbrAdj Ω) J K) := by
        rw [← horb]
        have := (pSpanConj g π h₀).2
        rwa [pSpanConj_apply] at this
      have hle : pSpan (orbOf (TC.nbrAdj Ω) J K) ≤ Subgroup.centralizer (J : Set G) :=
        hC.swap.pSpan_orb_le.trans (pSpan_omegaNbr_le_centralizer hC.hyp hC.two
          (hC.orb_subset_omega (mem_orbOf_self K J)))
      exact conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer (J : Set G) (hle hmem))
    have hhK : conjSub (g * (h₀ : G) * g⁻¹) K ∉ maxOrbSet Ω π := by
      intro hmem
      obtain ⟨β₂, hβ₂, c₂, hβ₂α, hlab₂⟩ := h3 _ ⟨_, hmem, rfl⟩
      obtain ⟨b', hb'⟩ := exists_conj_ofPerm_memBar σ α hα b
      have e1 : ((conjSub g⁻¹ (conjSub (g * (h₀ : G) * g⁻¹) K)).subgroupOf (pSpan π)).map I.φ =
          conjSub (mkQ 8 (ofPerm σ)) (memBar α hα b) := by
        rw [← hcc, TL4.AECov.map_conjSub_eq I (conjSub g⁻¹ K) h₀, hh₀, hlab₀]
      rw [e1] at hlab₂
      have h4 : memBar (α.map σ.toEmbedding) (by rw [Finset.card_map]; exact hα) b' =
          memBar β₂ hβ₂ c₂ := hb'.symm.trans hlab₂
      have h5 := AE.eq_of_memBar_eq' (by norm_num) h4
      rcases hβ₂α with h6 | h6
      · exact hσα (h5.trans h6)
      · exact hσαc (h5.trans h6)
    exact hS.false_of_moving hD hy hhy hhJ hhK hK'β hK'y
  ·
    exfalso
    have hall : ∀ M ∈ orbOf (TC.nbrAdj Ω) J K, M ∈ maxOrbSet Ω π := by
      intro M hM
      rw [← horb] at hM
      obtain ⟨L, hL, rfl⟩ := hM
      obtain ⟨N, hN, hNL⟩ := h3 L hL
      rw [← hNL, conjSub_conjSub_inv]
      exact hN
    exact hC.not_comm_orb_swap fun M hM L hL => hC.comm_of_mem_maxOrbSet (hall M hM) hL

theorem maxOrbSet_eq_eight' (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x) :
    ∀ M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J), M = K ∨ M = Ks := by
  classical
  have hC := hS.toCHyp
  have hJΩ : J ∈ Ω := hC.orb_subset_omega (mem_orbOf_self K J)
  obtain ⟨g, hg⟩ := hC.trans K hS.adj.1 J hJΩ
  obtain ⟨Ks₀, y, hD, α, h, b, y₀, hy₀, hy₀y, -, -, hlab₀, hlab₁⟩ :=
    hC.exists_data128_of (by norm_num) I hg
  have hy := hC.y_comm_of_rigid (by norm_num) I (ae3Rigid (by norm_num) (by norm_num)) hD
  have h1 := hS.maxOrbSet_eq_eight I hD hy hy₀ hy₀y hlab₀ hlab₁
  have hKsB : Ks ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J) := by
    refine hC.mem_maxOrbSet_of_adj (hC.swap.orb_subset_omega hKs) fun L hL =>
      hC.nbrAdj_of_comm (hC.swap.orb_subset_omega hKs) (hC.orb_subset_omega hL)
        (fun e => hKsπ (e ▸ hL)) fun a ha b hb => ?_
    exact (hKsX b (le_pSpan hL hb) a ha).symm
  intro M hM
  rcases h1 M hM with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rcases h1 Ks hKsB with h' | h'
    · exact absurd h' hKsK
    · rw [h, h']

theorem eq_of_comm_pSpan_eight (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {M : Subgroup G} (hM : M ∈ Ω)
    (hc : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ m ∈ M, x * m = m * x) : M = K ∨ M = Ks := by
  have hC := hS.toCHyp
  have hMπ : M ∉ orbOf (TC.nbrAdj Ω) K J := fun h =>
    hC.not_comm_self hM fun a ha b hb => hc a (le_pSpan h ha) b hb
  refine hS.maxOrbSet_eq_eight' I hKs hKsK hKsπ hz hKsX M (hC.mem_maxOrbSet_of_adj hM fun L hL =>
    hC.nbrAdj_of_comm hM (hC.orb_subset_omega hL) (fun e => hMπ (e ▸ hL)) fun a ha b hb => ?_)
  exact (hc b (le_pSpan hL hb) a ha).symm

theorem eq_of_mem_omegaNbr_eight (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) : M ∈ orbOf (TC.nbrAdj Ω) K J ∨ M = Ks := by
  have hC := hS.toCHyp
  by_cases hMπ : M ∈ orbOf (TC.nbrAdj Ω) K J
  · exact Or.inl hMπ
  right
  have hKM : TC.nbrAdj Ω K M := ⟨hS.adj.1, hM⟩
  have hadj : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, TC.nbrAdj Ω M L := by
    intro L hL
    have hKL : TC.nbrAdj Ω K L := adj_of_mem_orbOf hC.graphFam'.graph hS.adj hL
    have hML : M ∉ orbOf (TC.nbrAdj Ω) K L := by rwa [orbOf_eq_of_mem hL]
    have hLM := hC.graphFam'.graph.sep hKL hKM hML
    exact hC.graphFam'.graph.symm hLM
  rcases hS.maxOrbSet_eq_eight' I hKs hKsK hKsπ hz hKsX M (hC.mem_maxOrbSet_of_adj hM.1 hadj)
    with h | h
  · exact absurd h hM.2.1
  · exact h

private theorem mem_maxOrbSet_swap_of_z (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {M : Subgroup G} (hM : M ∈ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z z' : G, IsUniqueInvolution J z → IsUniqueInvolution M z' → z' = z) :
    M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) J K) := by
  classical
  have hC := hS.toCHyp
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hπΩ := hC.orb_subset_omega
  have hJΩ : J ∈ Ω := hπΩ hJπ
  have hMΩ : M ∈ Ω := hπΩ hM
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hC.card L hL]; norm_num
  obtain ⟨I'⟩ := hC.nonempty_aeIdent_swap I
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hC.hyp.omega1 J hJΩ
  obtain ⟨⟨zM, hzM⟩, -⟩ := hC.hyp.omega1 M hMΩ
  have hzz : zM = zJ := hz zJ zM hzJ hzM
  have hXJ : pSpan (orbOf (TC.nbrAdj Ω) J K) ≤ Subgroup.centralizer (J : Set G) :=
    hC.swap.pSpan_orb_le.trans (pSpan_omegaNbr_le_centralizer hC.hyp hC.two hJΩ)
  have hMnot : M ∉ orbOf (TC.nbrAdj Ω) J K := by
    intro hMJ'
    obtain ⟨δ, hδ, c, hlab⟩ := I'.label M hMJ'
    have hzMmem : zM ∈ pSpan (orbOf (TC.nbrAdj Ω) J K) := le_pSpan hMJ' hzM.mem
    have hcen : (⟨zM, hzMmem⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) J K))) ∈
        Subgroup.center ↥(pSpan (orbOf (TC.nbrAdj Ω) J K)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp (hXJ w.2) zJ hzJ.mem
      show (w : G) * zM = zM * w
      rw [hzz]
      exact this.symm
    have hker := I'.center_le_ker (by norm_num) hcen
    rw [MonoidHom.mem_ker] at hker
    have e := I'.map_eq_zBar (by norm_num) hMJ' (h8 M hMΩ) hlab hzM
    exact AE.zBar_ne_one (by norm_num) δ hδ (e.symm.trans hker)
  refine hC.swap.mem_maxOrbSet_of_adj hMΩ fun L hL => ?_
  have hLΩ : L ∈ Ω := hC.swap.orb_subset_omega hL
  have hLJ : L ∈ omegaNbr Ω J := hC.swap.orb_subset hL
  have hML : L ≠ M := fun e => hMnot (e ▸ hL)
  refine ⟨hMΩ, (TC.mem_omegaNbr_iff hC.hyp hC.two).mpr ⟨hLΩ, hML, ?_⟩⟩
  have hLzJ : ∀ v ∈ L, v * zM = zM * v := by
    intro v hv
    rw [hzz]
    exact (comm_of_mem_omegaNbr hC.hyp hC.two hJΩ hLJ zJ hzJ.mem v hv).symm
  have hnc : ∀ v ∈ L, (¬ ∀ w ∈ L, v * w = w * v) → v ∈ Subgroup.normalizer (M : Set G) :=
    fun v hv hvnc => hC.hyp.omega5 M hMΩ L hLΩ (Ne.symm hML) zM hzM v hv hvnc
      ((hC.two L hLΩ).to_le (Subgroup.zpowers_le.mpr hv)) (hLzJ v hv)
  intro v hv
  by_cases hvc : ∀ w ∈ L, v * w = w * v
  ·
    obtain ⟨w₀, hw₀, hw₀nc⟩ : ∃ w₀ ∈ L, ¬ ∀ w ∈ L, w₀ * w = w * w₀ := by
      by_contra hcon
      push Not at hcon
      exact hC.not_comm_self hLΩ fun a ha b hb => hcon a ha b hb
    have hnc2 : ¬ ∀ w ∈ L, (w₀⁻¹ * v) * w = w * (w₀⁻¹ * v) := by
      intro hall
      apply hw₀nc
      intro w hw
      have h1 : w₀⁻¹ * w = w * w₀⁻¹ := by
        apply mul_right_cancel (b := v)
        calc w₀⁻¹ * w * v = w₀⁻¹ * (w * v) := by group
          _ = w₀⁻¹ * (v * w) := by rw [hvc w hw]
          _ = (w₀⁻¹ * v) * w := by group
          _ = w * (w₀⁻¹ * v) := hall w hw
          _ = w * w₀⁻¹ * v := by group
      calc w₀ * w = w₀ * (w * w₀⁻¹) * w₀ := by group
        _ = w₀ * (w₀⁻¹ * w) * w₀ := by rw [h1]
        _ = w * w₀ := by group
    have h1 := hnc w₀ hw₀ hw₀nc
    have h2 := hnc _ (mul_mem (inv_mem hw₀) hv) hnc2
    have := mul_mem h1 h2
    rwa [mul_inv_cancel_left] at this
  · exact hnc v hv hvc

theorem twin_label_of_z_eight (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {δ : Finset (Fin 8)} {hδ : δ.card = 4} {b : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ b)
    {M : Subgroup G} (hM : M ∈ orbOf (TC.nbrAdj Ω) K J) (hMJ : M ≠ J)
    (hz : ∀ z z' : G, IsUniqueInvolution J z → IsUniqueInvolution M z' → z' = z) :
    (M.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ (!b) := by
  classical
  have hC := hS.toCHyp
  obtain ⟨Js, hJsπ, hJsJ, -, hzJs, hlabJs⟩ := hC.exists_twin_at_J_label (by norm_num) I hlabJ
  obtain ⟨I'⟩ := hC.nonempty_aeIdent_swap I
  obtain ⟨g₂, Ks, y, hD, -, -, hKsπ', hKsX, hzKs⟩ := hC.swap.exists_twin (by norm_num) I'
  have hKsπ : Ks ∈ orbOf (TC.nbrAdj Ω) K J := by
    have h1 := hD.Ks_mem
    rwa [hC.swap.orb_swap_eq hD.hg] at h1
  have key := hS.swap.maxOrbSet_eq_eight' I' hKsπ hD.Ks_ne hKsπ' hzKs hKsX
  rcases key M (hS.mem_maxOrbSet_swap_of_z I hM hz) with h | h
  · exact absurd h hMJ
  rcases key Js (hS.mem_maxOrbSet_swap_of_z I hJsπ hzJs) with h' | h'
  · exact absurd h' hJsJ
  rw [h, ← h']
  exact hlabJs

theorem conjSub_twin_label_eight (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {δ : Finset (Fin 8)} {hδ : δ.card = 4} {b : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ b)
    {s : G} (hs : conjSub s K = J) (hs' : conjSub s J = K) {Ks : Subgroup G}
    (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z) :
    ((conjSub s Ks).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      memBar δ hδ (!b) := by
  have hC := hS.toCHyp
  refine hS.twin_label_of_z_eight I hlabJ (hC.conjSub_twin_mem hs hs' hKs) ?_ ?_
  · intro e
    apply hKsK
    apply conjSub_injective s
    rw [e, hs]
  · intro z z' hzJ hz'
    obtain ⟨⟨zK, hzK⟩, -⟩ := hC.hyp.omega1 K hS.adj.1
    obtain ⟨⟨zKs, hzKs⟩, -⟩ := hC.hyp.omega1 Ks (hC.swap.orb_subset_omega hKs)
    have h1 : zKs = zK := hz zK zKs hzK hzKs
    have h2 : IsUniqueInvolution J (s * zK * s⁻¹) := hs ▸ hzK.conj s
    have h3 : IsUniqueInvolution (conjSub s Ks) (s * zK * s⁻¹) := by
      have := hzKs.conj s
      rwa [h1] at this
    rw [hz'.eq h3, hzJ.eq h2]

theorem exists_pairInv_eight (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 8)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {R : Subgroup G} (hRn : R.Normal) (hR : ∀ L ∈ Ω, ∀ v : G, IsUniqueInvolution L v → v ∈ R) :
    ∃ t u : G, conjSub t K = J ∧ conjSub t J = K ∧
      (∃ k ∈ K, ∃ k' ∈ Ks, u = k * k') ∧ u ∈ R ∧ u ≠ 1 ∧
      (∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * u = u * x) ∧
      (¬ ∀ k ∈ K, k * u = u * k) ∧ (¬ ∀ k ∈ Ks, k * u = u * k) ∧
      (∃ (hw : t * u * t⁻¹ ∈ pSpan (orbOf (TC.nbrAdj Ω) K J)) (a c : Fin 8), a ≠ c ∧
        I.φ ⟨t * u * t⁻¹, hw⟩ = mkQ 8 (ofVec (TL4.pairVec a c)) ∧
        ∀ (γ : Finset (Fin 8)) (hγ : γ.card = 4) (b : Bool),
          (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ b →
            a ∈ γ ∧ c ∈ γ) ∧
      (∃ (hw : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J)) (a c : Fin 8), a ≠ c ∧
        I.φ ⟨t⁻¹ * u * t, hw⟩ = mkQ 8 (ofVec (TL4.pairVec a c)) ∧
        ∀ (γ : Finset (Fin 8)) (hγ : γ.card = 4) (b : Bool),
          (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ b →
            a ∈ γ ∧ c ∈ γ) := by
  classical
  have hC := hS.toCHyp
  have hn5 : 5 ≤ 8 := by norm_num
  have hH := hC.aeCoverHyp_orb' hn5 I
  have hJπ : J ∈ (orbOf (TC.nbrAdj Ω) K J) := mem_orbOf_self K J
  obtain ⟨t, ht, ht'⟩ := hC.exists_swap
  obtain ⟨hti, hti'⟩ := CHyp.swap_inv ht ht'
  obtain ⟨δ, hδ, b, hlabJ⟩ := I.label J hJπ
  have hδmem : ∀ {x y : Fin 8}, x ∈ δ → y ∈ δ →
      ∀ (γ : Finset (Fin 8)) (hγ : γ.card = 4) (b' : Bool),
        (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ b' →
          x ∈ γ ∧ y ∈ γ := by
    intro x y hx hy γ hγ b' h
    obtain rfl := eq_of_memBar_eq' hn5 (hlabJ.symm.trans h)
    exact ⟨hx, hy⟩
  set Js := conjSub t Ks with hJs
  have hJsπ : Js ∈ (orbOf (TC.nbrAdj Ω) K J) := hC.conjSub_twin_mem ht ht' hKs
  have hlabJs := hS.conjSub_twin_label_eight I hlabJ ht ht' hKs hKsK hz
  have hJs' : conjSub t⁻¹ Ks = Js := by
    have h1 := hS.conjSub_twin_label_eight I hlabJ hti hti' hKs hKsK hz
    exact hH.label_inj _ (hC.conjSub_twin_mem hti hti' hKs) _ hJsπ (h1.trans hlabJs.symm)
  obtain ⟨j, hj, j', hj', a, ha, c, hc, hac, hjj, hI⟩ :=
    I.exists_mul_eq_pairVec hJπ hJsπ hlabJ hlabJs
  obtain ⟨u, hu⟩ : ∃ u : G, u = t⁻¹ * (j * j') * t := ⟨_, rfl⟩
  have htu : t * u * t⁻¹ = j * j' := by rw [hu]; group
  have hk : t⁻¹ * j * t ∈ K := by
    have := conj_mem_conjSub (n := t⁻¹) hj
    rwa [hti', inv_inv] at this
  have hk' : t⁻¹ * j' * t ∈ Ks := by
    have := conj_mem_conjSub (n := t⁻¹) hj'
    rwa [hJs, conjSub_inv_conjSub, inv_inv] at this
  have hufac : u = (t⁻¹ * j * t) * (t⁻¹ * j' * t) := by rw [hu]; group
  have hjjker : (⟨j * j', hjj⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))) ∈
      (TL4.AECov.permHom I).ker := by
    rw [TL4.AECov.mem_ker_permHom, hI]
    rfl
  have hzle : ∀ x ∈ TL4.AECov.zSpan (orbOf (TC.nbrAdj Ω) K J), (x : G) ∈ R := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨L, hL, hgL⟩ := hg
      exact hR L (hC.orb_subset_omega hL) _ hgL
    | one => exact R.one_mem
    | mul a b _ _ iha ihb => exact R.mul_mem iha ihb
    | inv a _ ih => exact R.inv_mem ih
  have hW := TL4.AECov.zSpan_elem fun L hL L' hL' v v' hv hv' =>
    TL4.AECov.comm_of_isUniqueInvolution I hn5 hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL'
      hv hv'
  have hjjR : j * j' ∈ R := hzle _ (TL4.AECov.ker_permHom_le_zSpan I (by omega) hH.card
    hH.conj_mem hH.label_inj hH.ker_two (TL4.AECov.zSpan_normal hH.conj_mem) hW hjjker)
  have huR : u ∈ R := by
    have := hRn.conj_mem _ hjjR t⁻¹
    rw [hu]
    rwa [inv_inv] at this
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 : j * j' = 1 := by rw [← htu, h1]; group
    apply vbar_pairVec_ne_one (by omega) hac
    rw [← hI]
    exact (congrArg I.φ (Subtype.ext h2 :
      (⟨j * j', hjj⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))) = 1)).trans (map_one I.φ)
  have hXu : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * u = u * x := by
    intro x hx
    rw [hufac]
    calc x * ((t⁻¹ * j * t) * (t⁻¹ * j' * t))
        = (x * (t⁻¹ * j * t)) * (t⁻¹ * j' * t) := by group
      _ = ((t⁻¹ * j * t) * x) * (t⁻¹ * j' * t) := by rw [hC.comm_orb_K hx hk]
      _ = (t⁻¹ * j * t) * (x * (t⁻¹ * j' * t)) := by group
      _ = (t⁻¹ * j * t) * ((t⁻¹ * j' * t) * x) := by rw [hKsX x hx _ hk']
      _ = ((t⁻¹ * j * t) * (t⁻¹ * j' * t)) * x := by group
  have hnc : ∀ {M L : Subgroup G} (_ : conjSub t M = L)
      (hL : L ∈ (orbOf (TC.nbrAdj Ω) K J)) {e : Bool}
      (_ : (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ e),
      ¬ ∀ k ∈ M, k * u = u * k := by
    intro M L hML hL e hlab hc'
    refine not_comm_memBar_pairVec hn5 hδ e ha hc hac fun x hx => ?_
    rw [← hlab] at hx
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL hx
    have hlM : t⁻¹ * l * t ∈ M := by
      have := conj_mem_conjSub (n := t⁻¹) (hML ▸ hl : l ∈ conjSub t M)
      rwa [conjSub_inv_conjSub, inv_inv] at this
    have e1 := hc' _ hlM
    have e2 : l * (j * j') = (j * j') * l := by
      calc l * (j * j') = t * ((t⁻¹ * l * t) * u) * t⁻¹ := by rw [hu]; group
        _ = t * (u * (t⁻¹ * l * t)) * t⁻¹ := by rw [e1]
        _ = (j * j') * l := by rw [hu]; group
    rw [← hI, ← map_mul, ← map_mul]
    exact congrArg I.φ (Subtype.ext e2)
  have hw1 : t * u * t⁻¹ ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := by rw [htu]; exact hjj
  have hI1 : I.φ ⟨t * u * t⁻¹, hw1⟩ = mkQ 8 (ofVec (TL4.pairVec a c)) := by
    rw [← hI]
    exact congrArg I.φ (Subtype.ext htu)
  refine ⟨t, u, ht, ht', ⟨_, hk, _, hk', hufac⟩, huR, hu1, hXu, hnc ht hJπ hlabJ,
    hnc (M := Ks) rfl hJsπ hlabJs, ⟨hw1, a, c, hac, hI1, hδmem ha hc⟩, ?_⟩
  have hnorm : t⁻¹ * t⁻¹ ∈
      Subgroup.normalizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G) :=
    hC.mem_normalizer_orb_of_conjSub (by rw [conjSub_mul, hti, hti'])
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = conjSpan hnorm ⟨j * j', hjj⟩ := ⟨_, rfl⟩
  have hx₀e : (x₀ : G) = t⁻¹ * u * t := by
    rw [hx₀, conjSpan_apply]
    show t⁻¹ * t⁻¹ * (j * j') * (t⁻¹ * t⁻¹)⁻¹ = t⁻¹ * u * t
    rw [hu]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hker := I.conj_mem_ker_permHom (by omega) hH hnorm hjjker
  rw [← hx₀, TL4.AECov.mem_ker_permHom] at hker
  have hl1 : t⁻¹ * t⁻¹ * j * (t⁻¹ * t⁻¹)⁻¹ ∈ J := by
    have := conj_mem_conjSub (n := t⁻¹ * t⁻¹) hj
    rwa [conjSub_mul, hti', hti] at this
  have hl2 : t⁻¹ * t⁻¹ * j' * (t⁻¹ * t⁻¹)⁻¹ ∈ Js := by
    have := conj_mem_conjSub (n := t⁻¹ * t⁻¹) hj'
    rwa [conjSub_mul, hJs, conjSub_inv_conjSub, hJs'] at this
  have hfac : t⁻¹ * u * t = (t⁻¹ * t⁻¹ * j * (t⁻¹ * t⁻¹)⁻¹) * (t⁻¹ * t⁻¹ * j' * (t⁻¹ * t⁻¹)⁻¹) := by
    rw [hu]
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hx₀m : (x₀ : G) ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := x₀.2
  have hx₀' : x₀ = ⟨_, mul_mem (le_pSpan hJπ hl1) (le_pSpan hJsπ hl2)⟩ :=
    Subtype.ext (hx₀e.trans hfac)
  rw [hx₀'] at hker
  obtain ⟨Γ, hδΓ, hex⟩ := exists_exact_over_eight I hH hδ
  have hJΓ : J ∈ I.over Γ := ⟨hJπ, δ, hδ, b, hδΓ, hlabJ⟩
  have hJsΓ : Js ∈ I.over Γ := ⟨hJsπ, δ, hδ, !b, hδΓ, hlabJs⟩
  have hxΓ : (t⁻¹ * t⁻¹ * j * (t⁻¹ * t⁻¹)⁻¹) * (t⁻¹ * t⁻¹ * j' * (t⁻¹ * t⁻¹)⁻¹) ∈
      pSpan (I.over Γ) := mul_mem (le_pSpan hJΓ hl1) (le_pSpan hJsΓ hl2)
  rcases I.map_mul_twins hJπ hJsπ hlabJ hlabJs hl1 hl2 hker with
    h1 | h1 | ⟨a', ha', c', hc', hac', h1⟩
  · exfalso
    have he := hex hxΓ (pSpan (I.over Γ)).one_mem (by
      rw [show (⟨1, I.pSpan_over_le Γ (pSpan (I.over Γ)).one_mem⟩ :
        ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))) = 1 from rfl, map_one]
      exact h1)
    apply hu1
    have : t⁻¹ * u * t = 1 := hfac.trans he
    calc u = t * (t⁻¹ * u * t) * t⁻¹ := by group
      _ = 1 := by rw [this]; group
  · exfalso
    obtain ⟨⟨zJ, hzJ⟩, -⟩ := hC.hyp.omega1 J (hC.orb_subset_omega hJπ)
    have hzJe := I.map_eq_zBar hn5 hJπ (hH.card J hJπ) hlabJ hzJ
    have he := hex hxΓ (le_pSpan hJΓ hzJ.mem) (h1.trans hzJe.symm)
    have hut : t⁻¹ * u * t = zJ := hfac.trans he
    have hz2 : IsUniqueInvolution J (t * t * zJ * (t * t)⁻¹) := by
      have := hzJ.conj (t * t)
      rwa [conjSub_mul, ht', ht] at this
    have hzz : t * t * zJ * (t * t)⁻¹ = zJ := hz2.eq hzJ
    have hjz : j * j' = zJ := by
      calc j * j' = t * u * t⁻¹ := htu.symm
        _ = t * t * (t⁻¹ * u * t) * (t * t)⁻¹ := by group
        _ = zJ := by rw [hut, hzz]
    apply vbar_pairVec_ne_zBar_of_mem hδ ha hc hac
    rw [← hI, ← hzJe]
    exact congrArg I.φ (Subtype.ext hjz)
  · have hw2 : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) := by rw [← hx₀e]; exact hx₀m
    refine ⟨hw2, a', c', hac', ?_, hδmem ha' hc'⟩
    rw [← h1]
    apply congrArg I.φ
    exact Subtype.ext hfac

end CSetting

end CFSG.ClassicalInvolution.Q3.TC.Thin
