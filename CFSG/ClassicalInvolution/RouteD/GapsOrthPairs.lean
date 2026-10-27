module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv
  IsClassicalMember centralizingMembers)
open CFSG.ClassicalInvolution.RouteD

@[expose] def ChainBound0 {KY : Type} [Group KY] (Z : Subgroup KY) (𝓕 : Set (Subgroup KY))
    (d : ℕ) : Prop :=
  ∀ r, 4 ≤ r → ∀ c, IsChain Z 𝓕 r c → 2 * (r + 1) ≤ d

@[expose] def PairBound {KY : Type} [Group KY] (Z : Subgroup KY) (𝓕 : Set (Subgroup KY))
    (d : ℕ) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, ∀ C ∈ 𝓕, ∀ D ∈ 𝓕, ModelAdj Z A B → ModelAdj Z C D → Commutes A C →
    Commutes A D → Commutes B C → Commutes B D → 12 ≤ d

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem chainBound0_model (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V) :
    ChainBound0 (scalars K V) (fundSet Q) (Module.finrank K V) := by
  intro r hr c hc
  obtain ⟨i, hi⟩ := exists_chain_inv hc
  have h1 := finrank_chainSpan hodd hdim hr hc hi r (by omega) le_rfl
  have h2 : Module.finrank K ↥(chainSpan i r) ≤ Module.finrank K V := Submodule.finrank_le _
  omega

theorem finrank_adj_sup (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {X Y : Subgroup (V ≃ₗ[K] V)} {iX iY : V ≃ₗ[K] V} (hX : IsFundamental Q X iX)
    (hY : IsFundamental Q Y iY) (h : ModelAdj (scalars K V) X Y) :
    Module.finrank K ↥(negSpace iX ⊔ negSpace iY) = 6 := by
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim hX hY h
  have pd := (lemma_6_10 hodd hX hY cm N C).1
  have := Submodule.finrank_sup_add_finrank_inf_eq (negSpace iX) (negSpace iY)
  rw [pd.finrank_U₂, finrank_negSpace hodd hX, finrank_negSpace hodd hY] at this
  omega

theorem orth_of_cross (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {X X' Y : Subgroup (V ≃ₗ[K] V)} {iX iX' iY : V ≃ₗ[K] V} (hX : IsFundamental Q X iX)
    (hX' : IsFundamental Q X' iX') (hY : IsFundamental Q Y iY) (hne : X ≠ X')
    (hnc : ¬ Commutes X X') (hinv : ModelInvComm (scalars K V) X' X) (hXY : Commutes X Y)
    (hX'Y : Commutes X' Y) : ∀ x ∈ negSpace iX, ∀ y ∈ negSpace iY, polar Q x y = 0 := by
  rcases orth_or_twin hodd hX hY hXY with h | h
  · exact h
  · exfalso
    refine ne_of_distinguish hodd hdim hX hY hX' hne.symm (fun e => hnc (e ▸ hXY)) hinv
      (modelInvComm_of_commutes hodd hX' hY hX'Y) ?_ h
    exact fun hiff => hnc (commutes_symm (hiff.mpr hX'Y))

theorem pairBound_model (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) :
    PairBound (scalars K V) (fundSet Q) (Module.finrank K V) := by
  rintro A ⟨iA, hA⟩ B ⟨iB, hB⟩ C ⟨iC, hC⟩ D ⟨iD, hD⟩ hAB hCD hAC hAD hBC hBD
  have hAB6 := finrank_adj_sup hodd hdim hA hB hAB
  have hCD6 := finrank_adj_sup hodd hdim hC hD hCD
  have hnBA : ¬ Commutes B A := fun h => hAB.2.1 (commutes_symm h)
  have oAC := orth_of_cross hodd hdim hA hB hC hAB.1 hAB.2.1 (ModelInvComm.of_adj hAB).symm' hAC hBC
  have oAD := orth_of_cross hodd hdim hA hB hD hAB.1 hAB.2.1 (ModelInvComm.of_adj hAB).symm' hAD hBD
  have oBC := orth_of_cross hodd hdim hB hA hC hAB.1.symm hnBA (ModelInvComm.of_adj hAB) hBC hAC
  have oBD := orth_of_cross hodd hdim hB hA hD hAB.1.symm hnBA (ModelInvComm.of_adj hAB) hBD hAD
  have hle : negSpace iC ⊔ negSpace iD ≤ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (negSpace iA ⊔ negSpace iB) := by
    have key : ∀ y : V, (∀ z ∈ negSpace iA, polar Q z y = 0) → (∀ z ∈ negSpace iB, polar Q z y = 0) →
        ∀ z ∈ negSpace iA ⊔ negSpace iB, polar Q z y = 0 := by
      intro y h1 h2 z hz
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
      rw [polar_add_left, h1 u hu, h2 v hv, add_zero]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      show polarBilin Q z y = 0
      rw [polarBilin_apply_apply]
      exact key y (fun z' hz' => oAC z' hz' y hy) (fun z' hz' => oBC z' hz' y hy) z hz
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      show polarBilin Q z y = 0
      rw [polarBilin_apply_apply]
      exact key y (fun z' hz' => oAD z' hz' y hy) (fun z' hz' => oBD z' hz' y hy) z hz
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hQ (negSpace iA ⊔ negSpace iB)
  omega

end Geometry

section Transfer

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem CentralQuot.chainBound0 (h : CentralQuot π 𝓕 𝓕' Z') {d : ℕ} (hb : ChainBound0 Z' 𝓕' d) :
    ChainBound0 (Subgroup.center KY) 𝓕 d := by
  intro r hr c hc
  refine hb r hr (fun a => (c a).map π) ⟨fun a ha => ?_, fun a ha => ?_, fun a b hab hb' => ?_⟩
  · exact h.map_mem _ (hc.mem a ha)
  · exact h.modelAdj (hc.mem a (by omega)) (hc.mem (a + 1) ha) (hc.adj a ha)
  · exact (h.commutes_iff (hc.mem a (by omega))).mpr (hc.comm a b hab hb')

theorem CentralQuot.pairBound (h : CentralQuot π 𝓕 𝓕' Z') {d : ℕ} (hb : PairBound Z' 𝓕' d) :
    PairBound (Subgroup.center KY) 𝓕 d := by
  intro A hA B hB C hC D hD hAB hCD hAC hAD hBC hBD
  exact hb _ (h.map_mem A hA) _ (h.map_mem B hB) _ (h.map_mem C hC) _ (h.map_mem D hD)
    (h.modelAdj hA hB hAB) (h.modelAdj hC hD hCD) ((h.commutes_iff hA).mpr hAC)
    ((h.commutes_iff hA).mpr hAD) ((h.commutes_iff hB).mpr hBC) ((h.commutes_iff hB).mpr hBD)

end Transfer

section Plus

variable {p f m : ℕ} [Fact p.Prime]

theorem chainBound0_plusDatum (hp2 : p ≠ 2) (hm : 5 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    ChainBound0 (Subgroup.center (spinGroup (quadPlus m (GaloisField p f))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) (2 * m) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hb := chainBound0_model (Q := quadPlus m (GaloisField p f)) hodd hdim
  rw [finrank_plus] at hb
  exact (centralQuot_plus hp2 (by omega) hm3 hq).chainBound0 hb

theorem pairBound_plusDatum (hp2 : p ≠ 2) (hm : 5 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    PairBound (Subgroup.center (spinGroup (quadPlus m (GaloisField p f))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) (2 * m) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hb := pairBound_model hodd (nondegenerate_polarBilin_quadPlus m (GaloisField p f)) hdim
  rw [finrank_plus] at hb
  exact (centralQuot_plus hp2 (by omega) hm3 hq).pairBound hb

theorem chainBound0_plus (hp2 : p ≠ 2) (hm : 5 ≤ m) (hq : 5 ≤ p ^ f) :
    ChainBound0 (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) (2 * m) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact chainBound0_plusDatum hp2 hm (by omega) hq

theorem pairBound_plus (hp2 : p ≠ 2) (hm : 5 ≤ m) (hq : 5 ≤ p ^ f) :
    PairBound (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) (2 * m) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact pairBound_plusDatum hp2 hm (by omega) hq

end Plus

section Witness

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {tY : StatedLieTag} {nY : ℕ} {N : Subgroup G} {x : G}

theorem chain0_config (cx : TCtx p f tY nY Ω N x) {d : ℕ}
    (hF : ChainBound0 (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d)
    {r : ℕ} (hr : 4 ≤ r) {c : ℕ → Subgroup G} {w : ℕ → G}
    (hc : ∀ a < r, c a ∈ centralizingMembers Ω {x})
    (hw : ∀ a < r, IsClassicalMember p f (c a) (w a))
    (hadj : ∀ a, a + 1 < r → c a ≠ c (a + 1) ∧ ¬ Commutes (c a) (c (a + 1)) ∧
      Commute (w a) (w (a + 1)) ∧ conjSub (w (a + 1)) (c a) = c a)
    (hcomm : ∀ a b, a + 1 < b → b < r → Commutes (c a) (c b)) : 2 * (r + 1) ≤ d := by
  classical
  have hcL : ∀ a < r, IsLayerMember cx (c a) := by
    intro a ha
    by_cases h1 : a + 1 < r
    · exact IsLayerMember.of_not_commutes cx (hc a ha) (hc (a + 1) h1) (hadj a h1).1
        (hadj a h1).2.1
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact IsLayerMember.of_not_commutes cx (hc (a' + 1) ha) (hc a' (by omega))
        (hadj a' (by omega)).1.symm (fun h => (hadj a' (by omega)).2.1 (commutes_symm h))
  have hex : ∀ a : ℕ, ∃ R : Subgroup (modelUniv tY nY p f Fact.out).K, a < r →
      R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
        locImg Ω x (c a) = R.map cx.d.ψ := by
    intro a
    by_cases h : a < r
    · obtain ⟨R, hR, hlR⟩ := (hcL a h).exists_fund
      exact ⟨R, fun _ => ⟨hR, hlR⟩⟩
    · exact ⟨⊥, fun h' => absurd h' h⟩
  choose R hR using hex
  refine hF r hr R ⟨fun a ha => (hR a ha).1, fun a ha => ?_, fun a b hab hb => ?_⟩
  · exact modelAdj_of_adj cx (hc a (by omega)) (hc (a + 1) ha) (hR a (by omega)).1
      (hR (a + 1) ha).1 (hR a (by omega)).2 (hR (a + 1) ha).2 (hw a (by omega)) (hw (a + 1) ha)
      (hadj a ha).1 (hadj a ha).2.1 (hadj a ha).2.2.1 (hadj a ha).2.2.2
  · exact (cx.commutes_iff_fund (hc a (by omega)) (hc b hb) (hR a (by omega)).1
      (hR a (by omega)).2 (hR b hb).2).mp (hcomm a b hab hb)

theorem pair_config (cx : TCtx p f tY nY Ω N x) {d : ℕ}
    (hF : PairBound (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d)
    {A B C D : Subgroup G} {wA wB wC wD : G} (hA : A ∈ centralizingMembers Ω {x})
    (hB : B ∈ centralizingMembers Ω {x}) (hC : C ∈ centralizingMembers Ω {x})
    (hD : D ∈ centralizingMembers Ω {x}) (hwA : IsClassicalMember p f A wA)
    (hwB : IsClassicalMember p f B wB) (hwC : IsClassicalMember p f C wC)
    (hwD : IsClassicalMember p f D wD) (hAB : A ≠ B) (hnAB : ¬ Commutes A B)
    (hcAB : Commute wA wB) (hnA : conjSub wB A = A) (hCD : C ≠ D) (hnCD : ¬ Commutes C D)
    (hcCD : Commute wC wD) (hnC : conjSub wD C = C) (hAC : Commutes A C) (hAD : Commutes A D)
    (hBC : Commutes B C) (hBD : Commutes B D) : 12 ≤ d := by
  classical
  have hAL : IsLayerMember cx A := IsLayerMember.of_not_commutes cx hA hB hAB hnAB
  have hBL : IsLayerMember cx B :=
    IsLayerMember.of_not_commutes cx hB hA hAB.symm (fun h => hnAB (commutes_symm h))
  have hCL : IsLayerMember cx C := IsLayerMember.of_not_commutes cx hC hD hCD hnCD
  have hDL : IsLayerMember cx D :=
    IsLayerMember.of_not_commutes cx hD hC hCD.symm (fun h => hnCD (commutes_symm h))
  obtain ⟨RA, hRA, hAR⟩ := hAL.exists_fund
  obtain ⟨RB, hRB, hBR⟩ := hBL.exists_fund
  obtain ⟨RC, hRC, hCR⟩ := hCL.exists_fund
  obtain ⟨RD, hRD, hDR⟩ := hDL.exists_fund
  exact hF RA hRA RB hRB RC hRC RD hRD
    (modelAdj_of_adj cx hA hB hRA hRB hAR hBR hwA hwB hAB hnAB hcAB hnA)
    (modelAdj_of_adj cx hC hD hRC hRD hCR hDR hwC hwD hCD hnCD hcCD hnC)
    ((cx.commutes_iff_fund hA hC hRA hAR hCR).mp hAC)
    ((cx.commutes_iff_fund hA hD hRA hAR hDR).mp hAD)
    ((cx.commutes_iff_fund hB hC hRB hBR hCR).mp hBC)
    ((cx.commutes_iff_fund hB hD hRB hBR hDR).mp hBD)

theorem chain5_false (cx : TCtx p f tY nY Ω N x) {d : ℕ}
    (hF : ChainBound0 (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d) (hd : d < 12)
    {m₀ m₁ m₂ m₃ m₄ : Subgroup G} {v₀ v₁ v₂ v₃ v₄ : G}
    (h₀ : m₀ ∈ centralizingMembers Ω {x}) (h₁ : m₁ ∈ centralizingMembers Ω {x})
    (h₂ : m₂ ∈ centralizingMembers Ω {x}) (h₃ : m₃ ∈ centralizingMembers Ω {x})
    (h₄ : m₄ ∈ centralizingMembers Ω {x}) (hw₀ : IsClassicalMember p f m₀ v₀)
    (hw₁ : IsClassicalMember p f m₁ v₁) (hw₂ : IsClassicalMember p f m₂ v₂)
    (hw₃ : IsClassicalMember p f m₃ v₃) (hw₄ : IsClassicalMember p f m₄ v₄)
    (a₀₁ : m₀ ≠ m₁ ∧ ¬ Commutes m₀ m₁ ∧ Commute v₀ v₁ ∧ conjSub v₁ m₀ = m₀)
    (a₁₂ : m₁ ≠ m₂ ∧ ¬ Commutes m₁ m₂ ∧ Commute v₁ v₂ ∧ conjSub v₂ m₁ = m₁)
    (a₂₃ : m₂ ≠ m₃ ∧ ¬ Commutes m₂ m₃ ∧ Commute v₂ v₃ ∧ conjSub v₃ m₂ = m₂)
    (a₃₄ : m₃ ≠ m₄ ∧ ¬ Commutes m₃ m₄ ∧ Commute v₃ v₄ ∧ conjSub v₄ m₃ = m₃)
    (c₀₂ : Commutes m₀ m₂) (c₀₃ : Commutes m₀ m₃) (c₀₄ : Commutes m₀ m₄)
    (c₁₃ : Commutes m₁ m₃) (c₁₄ : Commutes m₁ m₄) (c₂₄ : Commutes m₂ m₄) : False := by
  have key := chain0_config cx hF (r := 5) (by norm_num)
    (c := fun a => match a with | 0 => m₀ | 1 => m₁ | 2 => m₂ | 3 => m₃ | _ => m₄)
    (w := fun a => match a with | 0 => v₀ | 1 => v₁ | 2 => v₂ | 3 => v₃ | _ => v₄)
    (fun a ha => by interval_cases a <;> assumption)
    (fun a ha => by interval_cases a <;> assumption)
    (fun a ha => by
      have : a < 4 := by omega
      interval_cases a <;> assumption)
    (fun a b hab hb => by
      have : a < 4 := by omega
      interval_cases a <;> interval_cases b <;> omega)
  omega

end Witness

end CFSG.ClassicalInvolution.RouteD.Gaps
