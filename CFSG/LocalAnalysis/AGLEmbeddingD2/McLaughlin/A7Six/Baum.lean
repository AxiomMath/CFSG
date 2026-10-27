module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Sylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.PermData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.BaumStar

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open Equiv Equiv.Perm

@[expose] def pairVec (a b : Fin 7) : evenWeight 7 :=
  ⟨Pi.single a 1 + Pi.single b 1, by
    show ∑ k, (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) k = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    decide⟩

theorem pairVec_apply {a b : Fin 7} (hab : a ≠ b) (k : Fin 7) :
    (pairVec a b : Fin 7 → ZMod 2) k = if k = a ∨ k = b then 1 else 0 := by
  show (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) k = _
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases h1 : k = a <;> by_cases h2 : k = b
  · exact absurd (h1.symm.trans h2) hab
  · subst h1; simp [hab]
  · subst h2; simp [hab.symm]
  · simp [h1, h2]

theorem pair_of_altAct_fix {a b : Fin 7} (hab : a ≠ b) {σ : Perm (Fin 7)}
    (h : altAct σ (QuotientAddGroup.mk (pairVec a b) : altHeart 7) =
      (QuotientAddGroup.mk (pairVec a b) : altHeart 7)) :
    (σ a = a ∨ σ a = b) ∧ (σ b = a ∨ σ b = b) := by
  rw [altAct_mk] at h
  have h2 : evenWeightPerm σ (pairVec a b) = pairVec a b := by
    have h3 := QuotientAddGroup.eq.1 h
    rw [EightFive.evenWeightOnes_seven, AddSubgroup.mem_bot] at h3
    have h4 : -(evenWeightPerm σ (pairVec a b)) + pairVec a b = 0 := h3
    rw [neg_add_eq_zero] at h4
    exact h4
  have key : ∀ k, (pairVec a b : Fin 7 → ZMod 2) k = 1 →
      (pairVec a b : Fin 7 → ZMod 2) (σ k) = 1 := by
    intro k hk
    have h5 := congrArg (fun y : evenWeight 7 => (y : Fin 7 → ZMod 2) (σ k)) h2
    simp only [evenWeightPerm_apply] at h5
    rw [show σ⁻¹ (σ k) = k from by simp] at h5
    rw [← h5]
    exact hk
  have hmem : ∀ k, (pairVec a b : Fin 7 → ZMod 2) k = 1 ↔ k = a ∨ k = b := by
    intro k
    rw [pairVec_apply hab]
    split_ifs with hk
    · exact ⟨fun _ => hk, fun _ => rfl⟩
    · exact ⟨fun h0 => absurd h0 (by decide), fun h0 => absurd h0 hk⟩
  exact ⟨(hmem _).1 (key a ((hmem a).2 (Or.inl rfl))),
    (hmem _).1 (key b ((hmem b).2 (Or.inr rfl)))⟩

theorem altAct_fix_of_pair {a b : Fin 7} (hab : a ≠ b) {σ : Perm (Fin 7)}
    (ha : σ a = a ∨ σ a = b) (hb : σ b = a ∨ σ b = b) :
    altAct σ (QuotientAddGroup.mk (pairVec a b) : altHeart 7) =
      (QuotientAddGroup.mk (pairVec a b) : altHeart 7) := by
  rw [altAct_mk]
  congr 1
  apply Subtype.ext
  funext k
  rw [evenWeightPerm_apply, pairVec_apply hab, pairVec_apply hab]
  have hiff : (σ⁻¹ k = a ∨ σ⁻¹ k = b) ↔ (k = a ∨ k = b) := by
    have hsab : σ a ≠ σ b := fun h => hab (σ.injective h)
    constructor
    · rintro (h | h)
      · have hk : k = σ a := by rw [← h]; simp
        rw [hk]; exact ha
      · have hk : k = σ b := by rw [← h]; simp
        rw [hk]; exact hb
    · rintro (rfl | rfl)
      · rcases ha with h' | h'
        · left; rw [Perm.inv_eq_iff_eq]; exact h'.symm
        · right; rw [Perm.inv_eq_iff_eq]
          rcases hb with h'' | h''
          · exact h''.symm
          · exact absurd (h'.trans h''.symm) hsab
      · rcases hb with h' | h'
        · left; rw [Perm.inv_eq_iff_eq]
          rcases ha with h'' | h''
          · exact absurd (h''.trans h'.symm) hsab
          · exact h''.symm
        · right; rw [Perm.inv_eq_iff_eq]; exact h'.symm
  by_cases hk : k = a ∨ k = b
  · simp only [hk, hiff.2 hk, ite_true]
  · have hk' : ¬ (σ⁻¹ k = a ∨ σ⁻¹ k = b) := fun h => hk (hiff.1 h)
    simp only [hk, hk', ite_false]

theorem pair_of_finset {σ : Perm (Fin 7)} {a b : Fin 7}
    (ha : σ a ∈ ({a, b} : Finset (Fin 7))) (hb : σ b ∈ ({a, b} : Finset (Fin 7))) :
    (σ a = a ∨ σ a = b) ∧ (σ b = a ∨ σ b = b) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  exact ⟨ha, hb⟩

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

namespace SixCtx

variable (c : SixCtx T L) (pd : PermData)

theorem img_maxElem_le_E (hX : GNSetting X T) (hTL : T ≤ nL T L) (hD : c.img T = pd.D)
    {A : Subgroup X} (hA : IsMaxElemAbelian T A) : c.img A ≤ pd.E := by
  intro σ hσ
  have hσD : σ ∈ pd.D := hD ▸ c.img_mono hA.1 hσ
  refine pd.D_trans σ hσD (c.img_sq hTL hA σ hσ) fun i hi => ?_
  exact hD ▸ c.img_mono hA.1 (c.swap_mem_theta hX hTL hA hσ hi)

theorem theta_mem_E_of_mem_J (hX : GNSetting X T) (hTL : T ≤ nL T L) (hD : c.img T = pd.D)
    {j : X} (hj : j ∈ thompsonJ T) (hjL : j ∈ nL T L) : c.θ ⟨j, hjL⟩ ∈ pd.E := by
  have hJK : thompsonJ T ≤ (pd.E.comap c.θ).map (nL T L).subtype := by
    refine iSup₂_le fun A hA a ha => ?_
    exact ⟨⟨a, hTL (hA.1 ha)⟩,
      c.img_maxElem_le_E pd hX hTL hD hA ⟨⟨a, hTL (hA.1 ha)⟩, ha, rfl⟩, rfl⟩
  obtain ⟨⟨g, hg⟩, hgE, hgj⟩ := hJK hj
  simp only [Subgroup.coe_subtype] at hgj
  subst hgj
  exact hgE

theorem baum_fix_pair (hX : GNSetting X T) (hTL : T ≤ nL T L) (hD : c.img T = pd.D)
    {a b : Fin 7} (hab : a ≠ b)
    (hE : ∀ σ ∈ pd.E, (σ a = a ∨ σ a = b) ∧ (σ b = a ∨ σ b = b))
    {g : X} (hg : g ∈ baum T) :
    altAct (c.θ ⟨g, hTL hg.1⟩) (QuotientAddGroup.mk (pairVec a b) : altHeart 7) =
      (QuotientAddGroup.mk (pairVec a b) : altHeart 7) := by
  have hV : (gnV T).Normal := Subgroup.normalClosure_normal
  have hVe := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  have hVT := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.gnV_le T hX
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  obtain ⟨u, hu⟩ := c.hφ.2 (Multiplicative.ofAdd (QuotientAddGroup.mk (pairVec a b)))
  have hc : ∀ j ∈ thompsonJ T, j * (u : X) = (u : X) * j := by
    intro j hj
    have hjL : j ∈ nL T L := hTL (hJT hj)
    have hθj := c.theta_mem_E_of_mem_J pd hX hTL hD hj hjL
    have hv : j * (u : X) * j⁻¹ ∈ nV T L :=
      (Subgroup.mem_normalizer_iff.1 (nL_le_normalizer_nV hV hjL) u).1 u.2
    have h1 := c.hφe' ⟨j, hjL⟩ u ⟨_, hv⟩ rfl
    rw [hu, toAdd_ofAdd, altAct_fix_of_pair hab (hE _ hθj).1 (hE _ hθj).2] at h1
    have h2 : c.φ ⟨_, hv⟩ = c.φ u := by
      rw [hu]
      exact Multiplicative.toAdd.injective h1
    have h3 := congrArg Subtype.val (c.hφ.1 h2)
    simp only at h3
    calc j * (u : X) = j * (u : X) * j⁻¹ * j := by group
      _ = (u : X) * j := by rw [h3]
  have huV : (u : X) ∈ gnV T := Subgroup.commutator_le_left _ _ u.2
  have huΩ := CFSG.AGLEmbeddingD2.Tits.E23.mem_omegaOneCenterOf_thompsonJ hVe hVT huV hc
  have hgu : g * (u : X) * g⁻¹ = (u : X) := by
    have := Subgroup.mem_centralizer_iff.1 hg.2 _ huΩ
    rw [← this]; group
  have hv : g * (u : X) * g⁻¹ ∈ nV T L := by rw [hgu]; exact u.2
  have h1 := c.hφe' ⟨g, hTL hg.1⟩ u ⟨_, hv⟩ rfl
  have h4 : (⟨g * (u : X) * g⁻¹, hv⟩ : ↥(nV T L)) = u := Subtype.ext hgu
  rw [h4, hu, toAdd_ofAdd] at h1
  exact h1.symm

theorem theta_mem_E_of_mem_baum (hX : GNSetting X T) (hTL : T ≤ nL T L) (hD : c.img T = pd.D)
    {g : X} (hg : g ∈ baum T) : c.θ ⟨g, hTL hg.1⟩ ∈ pd.E := by
  have hgD : c.θ ⟨g, hTL hg.1⟩ ∈ pd.D := hD ▸ ⟨⟨g, hTL hg.1⟩, hg.1, rfl⟩
  have hE02 : ∀ σ ∈ pd.E, (σ 0 = 0 ∨ σ 0 = 2) ∧ (σ 2 = 0 ∨ σ 2 = 2) := fun σ hσ =>
    pair_of_finset (pd.E_pairs σ hσ).1 (pd.E_pairs σ hσ).2.1
  have hE13 : ∀ σ ∈ pd.E, (σ 1 = 1 ∨ σ 1 = 3) ∧ (σ 3 = 1 ∨ σ 3 = 3) := fun σ hσ =>
    pair_of_finset (pd.E_pairs σ hσ).2.2.1 (pd.E_pairs σ hσ).2.2.2.1
  have hE45 : ∀ σ ∈ pd.E, (σ 4 = 4 ∨ σ 4 = 5) ∧ (σ 5 = 4 ∨ σ 5 = 5) := fun σ hσ =>
    pair_of_finset (pd.E_pairs σ hσ).2.2.2.2.1 (pd.E_pairs σ hσ).2.2.2.2.2
  obtain ⟨h0, h2⟩ := pair_of_altAct_fix (by decide)
    (c.baum_fix_pair pd hX hTL hD (by decide) hE02 hg)
  obtain ⟨h1, h3⟩ := pair_of_altAct_fix (by decide)
    (c.baum_fix_pair pd hX hTL hD (by decide) hE13 hg)
  obtain ⟨h4, h5⟩ := pair_of_altAct_fix (by decide)
    (c.baum_fix_pair pd hX hTL hD (by decide) hE45 hg)
  refine pd.D_stab _ hgD ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] <;> assumption

end SixCtx

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
