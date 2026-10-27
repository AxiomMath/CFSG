module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDWeak
public import CFSG.ClassicalInvolution.Q3.Q3TWWFrameD
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.ClassicalInvolution.Models.TwistedPairs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem weakCT_spinMinus_of_frame {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p f)
    (hn : 4 ≤ n) (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) {b c : F}
    [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type} [Group X] (U : Fin (n - 1) → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (θ : spinGroup (quadMinus 3 F b c) →* X)
    (hθV : (shortBlock hirr 3 finOne).range.map θ = U ⟨n - 2, by omega⟩)
    (ρ' : Fin (n - 2) → (SL(2, F) →* X))
    (hρ'₀ : ρ' ⟨n - 2 - 1, by omega⟩ = θ.comp (minusLongBlock b c))
    (hρ'U : ∀ k : Fin (n - 2),
      Function.Injective (ρ' k) ∧ (ρ' k).range = U ⟨k.val, by omega⟩)
    (hρ'ψ : ∀ i j : Fin (n - 2), i.val + 1 = j.val →
      ∃ ψ : SL(3, F) →* X, ψ.comp (blk F 0) = ρ' i ∧ ψ.comp (blk F 1) = ρ' j) :
    ∃ Ψ : spinGroup (quadMinus n F b c) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧
      ∀ k, (CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map Ψ = U k := by
  classical
  have hn4 : 4 ≤ n := hn
  have h2 : (2 : F) ≠ 0 := by
    have hp := hadm.1
    have hf := hadm.2.1
    have hqc : (ringChar F).Prime := by
      rw [ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
      exact hp
    rw [Ne, ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hqc,
      ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
    exact hp2
  have hn3 : 3 ≤ n := by omega
  let P := spinMinusModel hirr
  let ρL : Fin (n - 1) → SL(2, F) →* X := fun k => if h : k.val < n - 2 then ρ' ⟨k.val, h⟩ else 1
  let ρS : SL(2, ShortField b c) →* X := θ.comp P.sb
  have hρL : ∀ k : Fin (n - 1), (h : k.val < n - 2) → ρL k = ρ' ⟨k.val, h⟩ := fun k h =>
    dite_eq_left h
  have hρLU : ∀ k : Fin (n - 1), k.val + 1 < n - 1 → (ρL k).range = U k := fun k hk => by
    rw [hρL k (by omega)]
    exact (hρ'U ⟨k.val, by omega⟩).2
  have hρLinj : ∀ k : Fin (n - 1), (h : k.val + 1 < n - 1) → Function.Injective (ρL k) :=
    fun k hk => by
      rw [hρL k (by omega)]
      exact (hρ'U ⟨k.val, by omega⟩).1
  have hρSU : ∀ k : Fin (n - 1), ¬ k.val + 1 < n - 1 → ρS.range = U k := fun k hk => by
    have hkb : k = ⟨n - 2, by omega⟩ := Fin.ext (by have := k.2; simp only; omega)
    rw [hkb, MonoidHom.range_comp]
    exact hθV
  have hCT : CurtisTits.CurtisTitsConclusion.{0} (minusDatum n hirr) .POmegaMinus n p f :=
    CurtisTits.curtisTitsConclusion_spinMinus hirr hadm hF
  have hCTG := minusDatum_isCTGroupDatum n hirr hn4
  have hL := leviConePresented_spinMinus hirr hn4
  have hdiv : (minusDatum n hirr).divisible = ∅ := rfl
  let nd : ∀ k, NodeData (minusDatum n hirr) X k (U k) := fun k =>
    if hk : k.val + 1 < n - 1 then nodeDataLong hirr (ρL k) (hρLU k hk) hk
    else nodeDataShort hirr h2 ρS (hρSU k hk) hk
  have ndL : ∀ (k : Fin (n - 1)) (hk : k.val + 1 < n - 1),
      (nd k).IsParam (rLong n b c hk) (ρL k) := fun k hk => by
    have e : nd k = nodeDataLong hirr (ρL k) (hρLU k hk) hk := dite_eq_left hk
    rw [e]
    exact nodeDataLong_isParam hirr _ _ hk
  have ndS : ∀ (k : Fin (n - 1)) (hk : ¬ k.val + 1 < n - 1),
      (nd k).IsParam (shortBlock hirr n k) ρS := fun k hk => by
    have e : nd k = nodeDataShort hirr h2 ρS (hρSU k hk) hk := dite_eq_right hk
    rw [e]
    exact nodeDataShort_isParam hirr h2 _ _ hk
  have hnt : ∃ k, ∃ g, (nd k).ψp g ≠ 1 := by
    let k₁ : Fin (n - 1) := ⟨0, by omega⟩
    have hk₁ : k₁.val + 1 < n - 1 := by simp only [k₁]; omega
    refine ⟨k₁, ⟨rLong n b c hk₁ (tv 0 1 1), rLong_upper hirr hk₁ 1⟩, ?_⟩
    rw [(ndL k₁ hk₁).ψp_eq 1]
    intro h
    exact tv_zero_one_one_ne_one (hρLinj k₁ hk₁ (h.trans (map_one _).symm))
  have hloc : ∀ i j : Fin (minusDatum n hirr).rank, i ≤ j →
      ∃ (E : LeviEmbedding (minusDatum n hirr) i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : (minusDatum n hirr).rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : (minusDatum n hirr).rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · by_cases hi : i.val + 1 < n - 1
      · exact exists_levi_node hdiv hCTG nd (ndL i hi) (rLong_injective hi)
      · exact exists_levi_node hdiv hCTG nd (ndS i hi) (shortBlock_injective hirr h2 n i)
    · have hlt' : i.val < j.val := hlt
      have hi2 : i.val < n - 1 := i.2
      have hj2 : j.val < n - 1 := j.2
      by_cases hadj : i.val + 1 = j.val
      · by_cases hj : j.val + 1 < n - 1
        ·
          have hi : i.val + 1 < n - 1 := by omega
          obtain ⟨emb, hinj, hemb0, hemb1⟩ := exists_sl3_minus h2 hn4 b c hadj hi hj
          obtain ⟨ψ, hψ0, hψ1⟩ := hρ'ψ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
            (by simpa [edgeUp] using hadj)
          exact exists_levi_of_model hdiv hCTG nd (ndL i hi) (ndL j hj) emb hinj (blk F 0)
            (blk F 1) hemb0 hemb1 ψ (hψ0.trans (hρL i (by omega)).symm)
            (hψ1.trans (hρL j (by omega)).symm)
        ·
          have hia : i.val + 3 = n := by omega
          have hjb : j.val + 2 = n := by omega
          have hi : i.val + 1 < n - 1 := by omega
          have hi' : ρL i = θ.comp P.lb := by
            have hk : (⟨i.val, by omega⟩ : Fin (n - 2)) = ⟨n - 2 - 1, by omega⟩ :=
              Fin.ext (by simp only; omega)
            rw [hρL i (by omega), hk, hρ'₀]
            rfl
          exact exists_levi_of_model hdiv hCTG nd (ndL i hi) (ndS j hj)
            (minusShift n hn3 b c).spinGroupMap (spinGroupMap_minusShift_injective h2 n hn3 hirr)
            (minusLongBlock b c) (shortBlock hirr 3 finOne) (minusShift_comp_longBlock hn3 hia hi)
            (minusShift_comp_shortBlock hn3 hirr hjb) θ hi'.symm rfl
      ·
        have hlt2 : i.val + 1 < j.val := by omega
        have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
        have hi : i.val + 1 < n - 1 := by omega
        have hcU : ∀ (A : SL(2, F)) (B : SL(2, F)), ∀ (hj : j.val + 1 < n - 1),
            Commute (ρL i A) (ρL j B) := fun A B hj =>
          hcomm i j hlt2 _ (hρLU i hi ▸ ⟨A, rfl⟩) _ (hρLU j hj ▸ ⟨B, rfl⟩)
        by_cases hj : j.val + 1 < n - 1
        · exact exists_levi_orth hdiv hCTG nd (ndL i hi) (ndL j hj) (rLong_injective hi)
            (rLong_injective hj) (commute_rLong_rLong hi hj hlt2)
            (hZ_of_torus (minusDatum_torus_iSupIndep n hirr) hne _ _
              (rLong_center_mem_torus hirr hi) (rLong_center_mem_torus hirr hj))
            (fun A B => hcU A B hj)
        · exact exists_levi_orth hdiv hCTG nd (ndL i hi) (ndS j hj) (rLong_injective hi)
            (shortBlock_injective hirr h2 n j) (commute_rLong_shortBlock hirr hi hlt2)
            (hZ_of_torus (minusDatum_torus_iSupIndep n hirr) hne _ _
              (rLong_center_mem_torus hirr hi) (shortBlock_center_mem_torus hirr hj))
            (fun A B => hcomm i j hlt2 _ (hρLU i hi ▸ ⟨A, rfl⟩) _ (hρSU j hj ▸ ⟨B, rfl⟩))
  obtain ⟨Ψ, hsurj, hker, -, -, -, hrk⟩ := weakCT_of_twisted_nodes hCT hL hdiv hgen nd hnt hloc
  exact ⟨Ψ, hsurj, hker, hrk⟩

section Ambient

theorem map_codRestrict_eq {G Y : Type*} [Group G] [Group Y] (f : Y →* G) (X : Subgroup G)
    (hf : ∀ y, f y ∈ X) (S : Subgroup Y) :
    S.map (f.codRestrict X hf) = (S.map f).subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le]
  · rfl
  · rintro _ ⟨y, -, rfl⟩
    exact hf y

theorem range_codRestrict_eq {G Y : Type*} [Group G] [Group Y] (f : Y →* G) (X : Subgroup G)
    (hf : ∀ y, f y ∈ X) : (f.codRestrict X hf).range = f.range.subgroupOf X := by
  rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, map_codRestrict_eq]

theorem iSup_subgroupOf_eq_top_of_eq' {G : Type*} [Group G] {ι : Type} {I : Subgroup G}
    {K : ι → Subgroup G} (hKI : ∀ i, K i ≤ I) (hgen : (⨆ i, K i) = I) :
    (⨆ i, (K i).subgroupOf I) = ⊤ := by
  apply Subgroup.map_injective I.subtype_injective
  rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
  simp_rw [Subgroup.map_subgroupOf_eq_of_le (hKI _)]
  exact hgen

theorem weakCT_minus_of_frame {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p f)
    (hn : 4 ≤ n) (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    {b c : F} [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {G : Type} [Group G] (U : Fin (n - 1) → Subgroup G)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (θ : spinGroup (quadMinus 3 F b c) →* G)
    (hθV : (shortBlock hirr 3 finOne).range.map θ = U ⟨n - 2, by omega⟩)
    (ρ' : Fin (n - 2) → (SL(2, F) →* G))
    (hρ'₀ : ρ' ⟨n - 2 - 1, by omega⟩ = θ.comp (minusLongBlock b c))
    (hρ'U : ∀ k : Fin (n - 2),
      Function.Injective (ρ' k) ∧ (ρ' k).range = U ⟨k.val, by omega⟩)
    (hρ'ψ : ∀ i j : Fin (n - 2), i.val + 1 = j.val →
      ∃ ψ : SL(3, F) →* G, ψ.comp (blk F 0) = ρ' i ∧ ψ.comp (blk F 1) = ρ' j) :
    ∃ Ψ : spinGroup (quadMinus n F b c) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      ∀ k, (CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map Ψ = U k := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    have hp := hadm.1
    have hf := hadm.2.1
    have hqc : (ringChar F).Prime := by
      rw [ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
      exact hp
    rw [Ne, ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hqc,
      ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
    exact hp2
  set X : Subgroup G := ⨆ k, U k with hX
  have hle : ∀ k, U k ≤ X := fun k => le_iSup U k
  have hlast : (minusLongBlock b c).range.map θ ≤ X := by
    rw [← MonoidHom.range_comp, ← hρ'₀]
    exact ((hρ'U ⟨n - 2 - 1, by omega⟩).2).le.trans (hle _)
  have hθX : θ.range ≤ X := by
    have htop : (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ :=
      spinMinusModel_blocks_sup_eq_top hirr h2
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup]
    exact sup_le hlast (hθV.le.trans (hle _))
  have hρX : ∀ (k : Fin (n - 2)) (g : SL(2, F)), ρ' k g ∈ X := fun k g => by
    have h : ρ' k g ∈ (ρ' k).range := ⟨g, rfl⟩
    rw [(hρ'U k).2] at h
    exact hle _ h
  let θs : spinGroup (quadMinus 3 F b c) →* X := θ.codRestrict X fun s => hθX ⟨s, rfl⟩
  let ρs : Fin (n - 2) → (SL(2, F) →* X) := fun k => (ρ' k).codRestrict X (hρX k)
  obtain ⟨Ψs, -, hker, hrk⟩ := weakCT_spinMinus_of_frame hadm hn hp2 hF hirr
    (fun k => (U k).subgroupOf X)
    (iSup_subgroupOf_eq_top_of_eq' hle rfl)
    (fun i j hij u hu v hv => Subtype.ext (hcomm i j hij u hu v hv)) θs
    (by rw [map_codRestrict_eq, hθV])
    ρs
    (MonoidHom.ext fun A => Subtype.ext (congrArg (fun g => g A) hρ'₀))
    (fun k => ⟨fun a b h => (hρ'U k).1 (congrArg Subtype.val h), by
      show (((ρ' k).codRestrict X (hρX k))).range = _
      rw [range_codRestrict_eq, (hρ'U k).2]⟩)
    (fun i j hij => by
      obtain ⟨ψ, hψ0, hψ1⟩ := hρ'ψ i j hij
      have hψX : ∀ g, ψ g ∈ X := by
        intro g
        have hg : ψ.range ≤ X := by
          rw [MonoidHom.range_eq_map, ← B12_sup_B23 (K := F), Subgroup.map_sup]
          refine sup_le ?_ ?_
          · show ((blk F 0).range).map ψ ≤ X
            rw [← MonoidHom.range_comp, hψ0, (hρ'U i).2]
            exact hle _
          · show ((blk F 1).range).map ψ ≤ X
            rw [← MonoidHom.range_comp, hψ1, (hρ'U j).2]
            exact hle _
        exact hg ⟨g, rfl⟩
      exact ⟨ψ.codRestrict X hψX,
        MonoidHom.ext fun A => Subtype.ext (congrArg (fun g => g A) hψ0),
        MonoidHom.ext fun A => Subtype.ext (congrArg (fun g => g A) hψ1)⟩)
  refine ⟨X.subtype.comp Ψs, ?_, fun k => ?_⟩
  · intro x hx
    refine hker (MonoidHom.mem_ker.2 (Subtype.ext ?_))
    exact MonoidHom.mem_ker.1 hx
  · rw [← Subgroup.map_map, hrk k, Subgroup.map_subgroupOf_eq_of_le (hle k)]

end Ambient

end CFSG.ClassicalInvolution.Q3.Q3TW
