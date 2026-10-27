module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Double
public import CFSG.ClassicalInvolution.WeakCT.TwistedTorus
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.LieType.CurtisTits.Exceptional
public import CFSG.Timmesfeld.RankTwo.LeviData

public noncomputable section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank CFSG.Blueprint
  MinData.Valid
open CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

theorem rootedTree_two_last :
    RootedTree (fun i j : Fin 2 => i.val + 1 = j.val) (fun _ => (1 : Fin 2))
      (fun i : Fin 2 => 1 - i.val) (1 : Fin 2) :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem rootedTree_two_first :
    RootedTree (fun i j : Fin 2 => i.val + 1 = j.val) (fun _ => (0 : Fin 2))
      (fun i : Fin 2 => i.val) (0 : Fin 2) :=
  ⟨by decide, by decide, by decide, by decide⟩

section Levis

variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

theorem exists_levi_orth_E6 {X : Type} [Group X] {U : Fin 4 → Subgroup X}
    (dat : ∀ i : Fin (twistedDatum k θ).rank, NodeData (twistedDatum k θ) X i (U i))
    {a c d : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    (hcd : (c = nd 2 ∧ d = nd 4) ∨ (c = nd 0 ∧ d = nd 5)) (hac : a ≠ c) (had : a ≠ d)
    (hc : Tag.cartan .E6 a c = 0) (hd : Tag.cartan .E6 a d = 0)
    {i j : Fin (twistedDatum k θ).rank} (hij : i ≠ j) (hi : hHatE k θ i = (hFixE θ a).range)
    (hj : hHatE k θ j = (hPairE θ c d).range) {ρ₁ : SL(2, fixedField θ) →* X}
    {ρ₂ : SL(2, k) →* X} (h1 : (dat i).IsParam (rFixed θ a ha) ρ₁)
    (h2 : (dat j).IsParam (slOrbitHom θ hθ hcd) ρ₂) (hX : ∀ A B, Commute (ρ₁ A) (ρ₂ B)) :
    ∃ (E : LeviEmbedding (twistedDatum k θ) i j) (φ : E.L →* X), ∀ i', (i' = i ∨ i' = j) →
      (∀ g : (twistedDatum k θ).rootGroup (Pi.single i' 1), φ (E.preimage g) = (dat i').ψp g) ∧
        ∀ g : (twistedDatum k θ).rootGroup (-Pi.single i' 1),
          φ (E.preimage g) = (dat i').ψm g :=
  exists_levi_orth rfl (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)) dat
    h1 h2 (rFixed_injective θ a ha) (slOrbitHom_injective θ hθ hcd)
    (fun A B => commute_rFixed_slOrbitHom θ hθ ha hcd hac had hc hd A B)
    (hZ_of_torus (hHat_iSupIndep θ) hij _ _ (rFixed_wS_sq_mem_hHat θ ha hi)
      (slOrbitHom_wS_sq_mem_hHat θ hθ hcd hj))
    hX

variable [Finite k]

theorem exists_levi_twistedE6 {X : Type} [Group X] {U : Fin 4 → Subgroup X}
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (dat : ∀ i : Fin (twistedDatum k θ).rank, NodeData (twistedDatum k θ) X i (U i))
    {ρL : Fin 2 → SL(2, fixedField θ) →* X} {ρS : Fin 2 → SL(2, k) →* X}
    (dP0 : (dat (nf 0)).IsParam (nodeHom0 θ) (ρL 0))
    (dP1 : (dat (nf 1)).IsParam (nodeHom1 θ) (ρL 1))
    (dP2 : (dat (nf 2)).IsParam (nodeHom2 θ hθ) (ρS 0))
    (dP3 : (dat (nf 3)).IsParam (nodeHom3 θ hθ) (ρS 1))
    (m0 : ∀ A, ρL 0 A ∈ U 0) (m1 : ∀ A, ρL 1 A ∈ U 1) (m2 : ∀ A, ρS 0 A ∈ U 2)
    (m3 : ∀ A, ρS 1 A ∈ U 3)
    (hL : ∃ ψ : SL(3, fixedField θ) →* X,
      ψ.comp (blk (fixedField θ) 0) = ρL 0 ∧ ψ.comp (blk (fixedField θ) 1) = ρL 1)
    (hS : ∃ ψ : SL(3, k) →* X, ψ.comp (blk k 0) = ρS 0 ∧ ψ.comp (blk k 1) = ρS 1)
    {θ₁ : unitaryGroup θ hθ →* X} (hl : ρL 1 = θ₁.comp (ulb θ hθ))
    (hs : ρS 0 = θ₁.comp (usb θ hθ)) :
    ∀ i j : Fin (twistedDatum k θ).rank, i ≤ j →
      ∃ (E : LeviEmbedding (twistedDatum k θ) i j) (φ : E.L →* X), ∀ i', (i' = i ∨ i' = j) →
        (∀ g : (twistedDatum k θ).rootGroup (Pi.single i' 1), φ (E.preimage g) = (dat i').ψp g) ∧
          ∀ g : (twistedDatum k θ).rootGroup (-Pi.single i' 1),
            φ (E.preimage g) = (dat i').ψm g := by
  have hCTG := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  have hdiv : (twistedDatum k θ).divisible = ∅ := rfl
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | (exfalso; revert hij; simp [Fin.le_def]; done) | skip
  ·
    exact exists_levi_node hdiv hCTG dat dP0 (rFixed_injective θ _ _)
  ·
    obtain ⟨emb, hinj, hb0, hb1⟩ := exists_levi01 θ
    obtain ⟨ψ, hψ0, hψ1⟩ := hL
    exact exists_levi_of_model hdiv hCTG dat dP0 dP1 emb hinj (blk (fixedField θ) 0)
      (blk (fixedField θ) 1) hb0 hb1 ψ hψ0 hψ1
  ·
    exact exists_levi_orth_E6 θ hθ dat rfl (Or.inl ⟨rfl, rfl⟩) (by decide) (by decide)
      (by decide) (by decide) (by simp [Fin.ext_iff]) rfl rfl dP0 dP2
      (fun A B => hcomm 0 2 (by decide) _ (m0 A) _ (m2 B))
  ·
    exact exists_levi_orth_E6 θ hθ dat rfl (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide)
      (by decide) (by decide) (by simp [Fin.ext_iff]) rfl rfl dP0 dP3
      (fun A B => hcomm 0 3 (by decide) _ (m0 A) _ (m3 B))
  ·
    exact exists_levi_node hdiv hCTG dat dP1 (rFixed_injective θ _ _)
  ·
    obtain ⟨emb, hinj, hb0, hb1⟩ := exists_levi12 θ hθ
    exact exists_levi_of_model hdiv hCTG dat dP1 dP2 emb hinj (ulb θ hθ) (usb θ hθ) hb0 hb1 θ₁
      hl.symm hs.symm
  ·
    exact exists_levi_orth_E6 θ hθ dat rfl (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide)
      (by decide) (by decide) (by simp [Fin.ext_iff]) rfl rfl dP1 dP3
      (fun A B => hcomm 1 3 (by decide) _ (m1 A) _ (m3 B))
  ·
    exact exists_levi_node hdiv hCTG dat dP2 (slOrbitHom_injective θ hθ _)
  ·
    obtain ⟨emb, hinj, hb0, hb1⟩ := exists_levi23 θ hθ
    obtain ⟨ψ, hψ0, hψ1⟩ := hS
    exact exists_levi_of_model hdiv hCTG dat dP2 dP3 emb hinj (blk k 0) (blk k 1) hb0 hb1 ψ
      hψ0 hψ1
  ·
    exact exists_levi_node hdiv hCTG dat dP3 (slOrbitHom_injective θ hθ _)

end Levis

section Recognition

variable {k : Type} [Field k] [Finite k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

theorem weakCT_twistedE6_of_CT {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTitsConclusion.{0} (twistedDatum k θ) t n p f)
    (hL : LeviConePresented (twistedDatum k θ)) (hF : 4 ≤ Nat.card (fixedField θ))
    {X : Type} [Group X] (U : Fin 4 → Subgroup X) (hgen : ⨆ i, U i = ⊤)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hp01 : ∃ W, LinearBlockStandardPair (fixedField θ) W (U 0) (U 1))
    (hp23 : ∃ W, LinearBlockStandardPair k W (U 2) (U 3))
    (htw : ∃ W, UnitaryB2BlockStandardPair θ hθ W (U 1) (U 2)) :
    ∃ Ψ : fixedGroup k θ →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (fixedGroup k θ)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ i, (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup i).map Ψ = U i := by
  classical
  have hk4 : 4 ≤ Nat.card k :=
    hF.trans (Nat.card_le_card_of_injective _ (fixedField θ).subtype.injective)
  obtain ⟨W, θ₁, -, -, hl, hs, hU1, hU2⟩ := htw
  let P := unitaryModel θ hθ
  have hν : ∃ t, P.nu t ≠ 1 := exists_unitaryNu_ne θ hθ hF
  have hμ : ∃ s, P.mu s ≠ 1 := exists_unitaryMu_ne θ hθ (by omega)
  have hlU : (θ₁.comp P.lb).range = U 1 := by rw [MonoidHom.range_comp]; exact hU1
  have hsU : (θ₁.comp P.sb).range = U 2 := by rw [MonoidHom.range_comp]; exact hU2
  let UL : Fin 2 → Subgroup X := fun i => U ⟨i.val, by omega⟩
  have hcommL : ∀ i j : Fin 2, i ≠ j → ¬ (i.val + 1 = j.val) → ¬ (j.val + 1 = i.val) →
      ∀ u ∈ UL i, ∀ v ∈ UL j, u * v = v * u := by
    intro i j hne h1 h2
    have h3 : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have := i.2
    have := j.2
    omega
  have hpairL : ∀ i j : Fin 2, i.val + 1 = j.val →
      ∃ W, LinearBlockStandardPair (fixedField θ) W (UL i) (UL j) := by
    intro i j hij
    have hi : i = 0 := Fin.ext (by have := j.2; simp only [Fin.val_zero]; omega)
    have hj : j = 1 := Fin.ext (by have := j.2; simp only [Fin.val_one]; omega)
    subst hi hj
    exact hp01
  have hVL : ∀ q : Fin 2, ((1 : Fin 2).val + 1 = q.val ∨ q.val + 1 = (1 : Fin 2).val) →
      ∀ x ∈ (θ₁.comp P.sb).range, ∀ y ∈ UL q, x * y = y * x := by
    intro q hq x hx y hy
    have hq0 : q = 0 := Fin.ext (by
      have := q.2
      simp only [Fin.val_zero]
      simp only [Fin.val_one] at hq
      omega)
    subst hq0
    rw [hsU] at hx
    exact (hcomm 0 2 (by decide) y hy x hx).symm
  obtain ⟨ρL, hρL₀, hρLU, hρLψ⟩ := exists_frame_of_tree_long P hν hF rootedTree_two_last
    ⟨0, Or.inr rfl⟩ hcommL hpairL hl hlU hVL
  let US : Fin 2 → Subgroup X := fun i => U ⟨i.val + 2, by omega⟩
  have hcommS : ∀ i j : Fin 2, i ≠ j → ¬ (i.val + 1 = j.val) → ¬ (j.val + 1 = i.val) →
      ∀ u ∈ US i, ∀ v ∈ US j, u * v = v * u := by
    intro i j hne h1 h2
    have h3 : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have := i.2
    have := j.2
    omega
  have hpairS : ∀ i j : Fin 2, i.val + 1 = j.val →
      ∃ W, LinearBlockStandardPair k W (US i) (US j) := by
    intro i j hij
    have hi : i = 0 := Fin.ext (by have := j.2; simp only [Fin.val_zero]; omega)
    have hj : j = 1 := Fin.ext (by have := j.2; simp only [Fin.val_one]; omega)
    subst hi hj
    exact hp23
  have hVS : ∀ q : Fin 2, ((0 : Fin 2).val + 1 = q.val ∨ q.val + 1 = (0 : Fin 2).val) →
      ∀ x ∈ (θ₁.comp P.lb).range, ∀ y ∈ US q, x * y = y * x := by
    intro q hq x hx y hy
    have hq1 : q = 1 := Fin.ext (by
      have := q.2
      simp only [Fin.val_zero] at hq
      simp only [Fin.val_one]
      omega)
    subst hq1
    rw [hlU] at hx
    exact hcomm 1 3 (by decide) x hx y hy
  have hsU' : (θ₁.comp P.sb).range = US 0 := hsU
  obtain ⟨ρS, hρS₀, hρSU, hρSψ⟩ := exists_frame_of_tree_short P hμ hk4 rootedTree_two_first
    ⟨1, Or.inl rfl⟩ hcommS hpairS hs hsU' hVS
  let dat : ∀ i : Fin (twistedDatum k θ).rank, NodeData (twistedDatum k θ) X i (U i) := fun i =>
    match i with
    | ⟨0, _⟩ => nodeDataFixed θ (nd 1) rfl (i := nf 0) rfl (ρL 0) (hρLU 0).2
    | ⟨1, _⟩ => nodeDataFixed θ (nd 3) rfl (i := nf 1) rfl (ρL 1) (hρLU 1).2
    | ⟨2, _⟩ => nodeDataOrbit θ hθ (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩) (i := nf 2) rfl
        (ρS 0) (hρSU 0).2
    | ⟨3, _⟩ => nodeDataOrbit θ hθ (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) (i := nf 3) rfl
        (ρS 1) (hρSU 1).2
    | ⟨n + 4, h⟩ => absurd h (by change ¬ n + 4 < 4; omega)
  have dP0 : (dat (nf 0)).IsParam (nodeHom0 θ) (ρL 0) :=
    nodeDataFixed_isParam θ (nd 1) rfl (i := nf 0) rfl (ρL 0) (hρLU 0).2
  have dP1 : (dat (nf 1)).IsParam (nodeHom1 θ) (ρL 1) :=
    nodeDataFixed_isParam θ (nd 3) rfl (i := nf 1) rfl (ρL 1) (hρLU 1).2
  have dP2 : (dat (nf 2)).IsParam (nodeHom2 θ hθ) (ρS 0) :=
    nodeDataOrbit_isParam θ hθ (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩) (i := nf 2) rfl
      (ρS 0) (hρSU 0).2
  have dP3 : (dat (nf 3)).IsParam (nodeHom3 θ hθ) (ρS 1) :=
    nodeDataOrbit_isParam θ hθ (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) (i := nf 3) rfl
      (ρS 1) (hρSU 1).2
  have hnt : ∃ i, ∃ g, (dat i).ψp g ≠ 1 := by
    refine ⟨nf 0, ⟨nodeHom0 θ (tv 0 1 1), dP0.r_upper 1⟩, ?_⟩
    rw [dP0.ψp_eq 1]
    intro h
    exact tv_zero_one_one_ne_one ((hρLU 0).1 (h.trans (map_one _).symm))
  have m0 : ∀ A, ρL 0 A ∈ UL 0 := fun A => (hρLU 0).2 ▸ ⟨A, rfl⟩
  have m1 : ∀ A, ρL 1 A ∈ UL 1 := fun A => (hρLU 1).2 ▸ ⟨A, rfl⟩
  have m2 : ∀ A, ρS 0 A ∈ US 0 := fun A => (hρSU 0).2 ▸ ⟨A, rfl⟩
  have m3 : ∀ A, ρS 1 A ∈ US 1 := fun A => (hρSU 1).2 ▸ ⟨A, rfl⟩
  exact weakCT_of_twisted_nodes hCT hL rfl hgen dat hnt
    (exists_levi_twistedE6 θ hθ hcomm dat dP0 dP1 dP2 dP3 m0 m1 m2 m3
      (hρLψ 0 1 rfl) (hρSψ 0 1 rfl) hρL₀ hρS₀)

end Recognition

section Main

open CFSG.LieType.Steinberg.Exceptional

theorem weakCT_twistedE6 {p f : ℕ} [Fact p.Prime]
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .twistedE6 0 p f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F)
    {X : Type} [Group X] (U : Fin 4 → Subgroup X) (hgen : ⨆ i, U i = ⊤)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hp01 : ∃ W, LinearBlockStandardPair F W (U 0) (U 1))
    (hp23 : ∃ W, LinearBlockStandardPair (GaloisField p (2 * f)) W (U 2) (U 3))
    (htw : ∃ W, UnitaryB2BlockStandardPair (frobQ p f) (frobQ_frobQ p f hadm.2.1) W (U 1) (U 2)) :
    ∃ Ψ : twistedE6Group p f →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (twistedE6Group p f)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .twistedE6 0 p f ∧
      ∀ i, (CFSG.LieType.CurtisTits.rankOne (twistedE6Datum p f).rootGroup i).map Ψ = U i := by
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨eF⟩ := nonempty_ringEquiv_fixedField_frobQ p f hf hF
  have hF4 : 4 ≤ Nat.card (fixedField (frobQ p f)) := by
    rw [card_fixedField_frobQ p f hf, ← hF]
    exact hq
  exact weakCT_twistedE6_of_CT (frobQ p f) (frobQ_frobQ p f hf)
    (CFSG.LieType.CurtisTits.curtisTitsConclusion_twistedE6.{0} p f hadm)
    (leviConePresented_twistedE6 p f hf) hF4 U hgen hcomm
    (hp01.imp fun W h => h.of_ringEquiv eF) hp23 htw

end Main

end CFSG.ClassicalInvolution.WeakCT
