module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBSmallModel
public import CFSG.ClassicalInvolution.RouteD.GapsFrBLast
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap

local macro "sl_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem false_of_bad_class_small {m : ℕ} (hm : m = 5 ∨ m = 7) (c : TCtx p f .POmegaOdd m Ω K z)
    {β : Subgroup G} {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f m Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {N₁ : Subgroup G} (hN₁Ω : N₁ ∈ Ω) (hN₁K : Commutes K N₁) (hN₁β : Commutes β N₁)
    (hN₁M : Commutes M N₁) (hN₁c : ∀ a (h : a < m), a + 3 < m → Commutes (nd.J ⟨a, h⟩) N₁)
    (hN₁adj : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨m - 3, by omega⟩) N₁)
    (hN₁2 : N₁ ≠ nd.J ⟨m - 2, by omega⟩) (hN₁1 : N₁ ≠ nd.J ⟨m - 1, by omega⟩)
    {α : spinGroup (quadOdd m (GaloisField p f)) ≃* spinGroup (quadOdd m (GaloisField p f))}
    {v : Fin m → ZMod 2}
    (hαθ : ∀ x, c.d.ψ (α x) = locAut c.hΩ.conjInvariant
      (partner_involution_commutes c.hp2 c.hz ht hKβ) (c.d.ψ x))
    (hlift : OddLift α v) (p₀ : Fin m) (hp₀ : p₀.val + 2 = m)
    (hreach : CharReach (CartanMatrix.C m) v (Pi.single p₀ 1)) : False := by
  classical
  have hm5 : 5 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  have hKJ : ∀ a (h : a < m), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by sl_idx)) (by sl_idx)
  have hmemz : ∀ a (h : a < m), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < m), 2 ≤ a →
      ∃ b, ∃ hb : b < m, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin m) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a ≤ m - 3
    · exact ⟨a + 1, by omega, by omega, by sl_idx⟩
    · exact ⟨m - 3, by omega, by omega, by sl_idx⟩
  have hlayer : ∀ a (h : a < m), 2 ≤ a → IsLayerMember c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaOdd m p f Fact.out).K,
      ∀ (h : a < m), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < m ∧ 2 ≤ a
    · obtain ⟨R, hR, hLR⟩ := (hlayer a hv.1 hv.2).exists_fund
      exact ⟨R, fun _ _ => ⟨hR, hLR⟩⟩
    · exact ⟨⊥, fun h ha => absurd ⟨h, ha⟩ hv⟩
  choose Rz hRz using hexRz
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  obtain ⟨N, hNz, hNM, hNc⟩ := hMN
  have hMlayer : IsLayerMember c M :=
    IsLayerMember.of_not_commutes c hMz hNz (fun h => hNM h.symm) hNc
  obtain ⟨RzM, hRzM, hMR⟩ := hMlayer.exists_fund
  have hN₁z : N₁ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₁Ω c.hz.mem (commutes_symm hN₁K)
  obtain ⟨WJ, hWJ⟩ := hN₁adj
  have hN₁layer : IsLayerMember c N₁ :=
    IsLayerMember.of_not_commutes c hN₁z (hmemz (m - 3) (by omega) (by omega))
      (fun e => ne_of_linearBlockStandardPair hWJ e.symm)
      (fun hc' => not_commutes_of_linearBlockStandardPair hWJ (commutes_symm hc'))
  obtain ⟨RN, hRN, hN₁R⟩ := hN₁layer.exists_fund
  obtain ⟨g₀, tt, hiso, hsq, hconj, hvt, hdim⟩ := hlift
  have hcount : (Finset.univ.filter fun i : Fin m => tt i.val = 0).card = 1 := by
    rw [hvt] at hreach
    have h1 := card_ones_of_charReach tt p₀ hreach
    have h2' := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i : Fin m => tt i.val = 1)
    have hs : (Finset.univ.filter fun i : Fin m => ¬ tt i.val = 1) =
        Finset.univ.filter fun i : Fin m => tt i.val = 0 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize tt i.val = x
      revert x
      decide
    rw [hs, Finset.card_univ, Fintype.card_fin] at h2'
    omega
  have hdimE : Module.finrank (GaloisField p f) ↥(Module.End.eigenspace
      (g₀ : Module.End (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f)) 1) = 3 := by
    rw [hdim, hcount]
  have cq := centralQuot_odd (m := m) (f := f) c.hp2 hm3 c.hq
  have hRf : ∀ a (h : a < m), 2 ≤ a →
      Rz a ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)) :=
    fun a h ha => (hRz a h ha).1
  have hcommz : ∀ a (ha : a < m) b (hb : b < m) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < m) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < m) b (hb : b < m) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin m) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaOdd m p f Fact.out).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    modelAdj_of_adj c (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hΩ hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _) (nd.conjSub_w h2 hab)
  have hfixmem : ∀ {X : Subgroup G} {R : Subgroup (spinGroup (quadOdd m (GaloisField p f)))},
      X ∈ centralizingMembers Ω {z} →
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)) →
      locImg Ω z X = R.map c.d.ψ → Commutes β X →
      ∀ l ∈ R.map (spinAction (quadOdd m (GaloisField p f))), g₀ * l = l * g₀ := by
    intro X R hXz hR hXR hβX
    have hσ : ∀ x ∈ locImg Ω z X, locAut hΩ.conjInvariant htz x = x :=
      (locAut_fixed_iff hΩ c.hP1 htz hXz).mp fun n hn =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hβX t ht.mem n hn).symm
    have hα := eq_of_fixed_of_perfect c.d.ψ c.d.ker_le α (locAut hΩ.conjInvariant htz) hαθ
      (cq.perf R hR) (fun r hr => hσ _ (by rw [hXR]; exact ⟨r, hr, rfl⟩))
    rintro _ ⟨r, hr, rfl⟩
    refine LinearEquiv.ext fun x => ?_
    have h := hconj r x
    have hα' : α r = r := hα r hr
    rw [hα'] at h
    exact h.symm
  have hβJ : ∀ a (h : a < m), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by sl_idx)) (by sl_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hQ : (polarBilin (quadOdd m (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2
  have hdimV : Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) =
      2 * m + 1 := by
    rw [finrank_odd]
  have hdim9 : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) := by
    rw [hdimV]
    omega
  let ρ := spinAction (quadOdd m (GaloisField p f))
  have hLM : RzM.map ρ ∈ fundSet (quadOdd m (GaloisField p f)) := cq.map_mem _ hRzM
  obtain ⟨iM, hiM⟩ := hLM
  have hDf : (Rz (m - 3)).map ρ ∈ fundSet (quadOdd m (GaloisField p f)) :=
    cq.map_mem _ (hRf (m - 3) (by omega) (by omega))
  obtain ⟨iD, hiD⟩ := hDf
  let Y : Fin 3 → Subgroup ((Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f)) :=
    ![(Rz (m - 2)).map ρ, (Rz (m - 1)).map ρ, RN.map ρ]
  have hY : ∀ k, Y k ∈ fundSet (quadOdd m (GaloisField p f)) := by
    intro k
    fin_cases k
    · exact cq.map_mem _ (hRf (m - 2) (by omega) (by omega))
    · exact cq.map_mem _ (hRf (m - 1) (by omega) (by omega))
    · exact cq.map_mem _ hRN
  choose iY hiY using hY
  have hinj : ∀ {X X' : Subgroup G} {R R' : Subgroup (spinGroup (quadOdd m (GaloisField p f)))},
      X ∈ centralizingMembers Ω {z} → X' ∈ centralizingMembers Ω {z} →
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)) →
      R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)) →
      locImg Ω z X = R.map c.d.ψ → locImg Ω z X' = R'.map c.d.ψ → R.map ρ = R'.map ρ → X = X' := by
    intro X X' R R' hX hX' hR hR' hXR hXR' he
    have := cq.map_inj hR hR' he
    exact c.eq_of_locImg_eq hX hX' (by rw [hXR, hXR', this])
  have n01 : Y 0 ≠ Y 1 := fun e => nd.ne_J hΩ (a := ⟨m - 2, by omega⟩) (b := ⟨m - 1, by omega⟩)
    (fin_ne_of_val_ne (by simp; omega))
    (hinj (hmemz (m - 2) (by omega) (by omega)) (hmemz (m - 1) (by omega) (by omega))
      (hRf (m - 2) (by omega) (by omega)) (hRf (m - 1) (by omega) (by omega))
      (hRz (m - 2) (by omega) (by omega)).2 (hRz (m - 1) (by omega) (by omega)).2 e)
  have n02 : Y 0 ≠ Y 2 := fun e => hN₁2
    (hinj (hmemz (m - 2) (by omega) (by omega)) hN₁z (hRf (m - 2) (by omega) (by omega)) hRN
      (hRz (m - 2) (by omega) (by omega)).2 hN₁R e).symm
  have n12 : Y 1 ≠ Y 2 := fun e => hN₁1
    (hinj (hmemz (m - 1) (by omega) (by omega)) hN₁z (hRf (m - 1) (by omega) (by omega)) hRN
      (hRz (m - 1) (by omega) (by omega)).2 hN₁R e).symm
  have hYinj : Function.Injective Y := by
    intro k k' h
    fin_cases k <;> fin_cases k' <;>
      first
      | rfl
      | exact absurd h n01
      | exact absurd h.symm n01
      | exact absurd h n02
      | exact absurd h.symm n02
      | exact absurd h n12
      | exact absurd h.symm n12
  have hfixM : ∀ l ∈ RzM.map ρ, g₀ * l = l * g₀ := hfixmem hMz hRzM hMR hMβ
  have hfixY : ∀ k, ∀ l ∈ Y k, g₀ * l = l * g₀ := by
    intro k
    fin_cases k
    · exact hfixmem (hmemz (m - 2) (by omega) (by omega)) (hRf (m - 2) (by omega) (by omega))
        (hRz (m - 2) (by omega) (by omega)).2 (hβJ (m - 2) (by omega) (by omega))
    · exact hfixmem (hmemz (m - 1) (by omega) (by omega)) (hRf (m - 1) (by omega) (by omega))
        (hRz (m - 1) (by omega) (by omega)).2 (hβJ (m - 1) (by omega) (by omega))
    · exact hfixmem hN₁z hRN hN₁R hN₁β
  have hYM : ∀ k, Commutes (Y k) (RzM.map ρ) := by
    intro k
    fin_cases k
    · exact (cq.commutes_iff (hRf (m - 2) (by omega) (by omega))).mpr
        (hMcomm (m - 2) (by omega) (by omega)).symm
    · exact (cq.commutes_iff (hRf (m - 1) (by omega) (by omega))).mpr
        (hMcomm (m - 1) (by omega) (by omega)).symm
    · exact (cq.commutes_iff hRN).mpr
        ((c.commutes_iff_fund hN₁z hMz hRN hN₁R hMR).mp (commutes_symm hN₁M))
  have hD : ∀ k, ModelAdj (scalars (GaloisField p f)
      (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f)) ((Rz (m - 3)).map ρ) (Y k) := by
    intro k
    fin_cases k
    · exact cq.modelAdj (hRf (m - 3) (by omega) (by omega)) (hRf (m - 2) (by omega) (by omega))
        (hadjz (m - 3) (by omega) (m - 2) (by omega) (by omega) (by omega) (by sl_idx))
    · exact cq.modelAdj (hRf (m - 3) (by omega) (by omega)) (hRf (m - 1) (by omega) (by omega))
        (hadjz (m - 3) (by omega) (m - 1) (by omega) (by omega) (by omega) (by sl_idx))
    · obtain ⟨w₁, hw₁⟩ := hΩ.classical N₁ hN₁Ω
      refine cq.modelAdj (hRf (m - 3) (by omega) (by omega)) hRN ?_
      exact modelAdj_of_adj c (hmemz (m - 3) (by omega) (by omega)) hN₁z
        (hRz (m - 3) (by omega) (by omega)).1 hRN (hRz (m - 3) (by omega) (by omega)).2 hN₁R
        (nd.cl _) hw₁ (fun e => ne_of_linearBlockStandardPair hWJ e)
        (not_commutes_of_linearBlockStandardPair hWJ)
        (standardPair_involutions_commute h2 hWJ (nd.cl _).mem hw₁.mem (nd.cl _).orderOf_eq_two
          hw₁.orderOf_eq_two)
        (conjSub_eq_of_standardPair h2 hWJ hw₁.mem hw₁.orderOf_eq_two)
  have hDM : Commutes ((Rz (m - 3)).map ρ) (RzM.map ρ) :=
    (cq.commutes_iff (hRf (m - 3) (by omega) (by omega))).mpr
      (hMcomm (m - 3) (by omega) (by omega)).symm
  have hMY : ∀ k, ∀ x ∈ negSpace iM, ∀ y ∈ negSpace (iY k),
      polar (quadOdd m (GaloisField p f)) x y = 0 := fun k =>
    polar_negSpace_of_adj_commute c.hodd hdim9 hiM (hiY k) hiD (hYM k).symm (hD k) hDM
  rcases hm with hm | hm
  ·
    refine model_contradiction_of_span c.hodd hQ hiso hsq hdimE (S := negSpace iM) ?_ ?_ hiY
      hYinj hfixY ?_
    · exact negSpace_le_eigenspace_neg_of_fixed c.hodd hiso hsq hdimE hiM hfixM
    · rw [finrank_negSpace c.hodd hiM, hdimV]
      omega
    · intro k y hy s hs
      rw [polar_comm]
      exact hMY k s hs y hy
  ·
    have hf3 : (Rz 3).map ρ ∈ fundSet (quadOdd m (GaloisField p f)) :=
      cq.map_mem _ (hRf 3 (by omega) (by omega))
    obtain ⟨i3, hi3⟩ := hf3
    have hfix3 : ∀ l ∈ (Rz 3).map ρ, g₀ * l = l * g₀ :=
      hfixmem (hmemz 3 (by omega) (by omega)) (hRf 3 (by omega) (by omega))
        (hRz 3 (by omega) (by omega)).2 (hβJ 3 (by omega) (by omega))
    have hM3 : Commutes (RzM.map ρ) ((Rz 3).map ρ) :=
      (cq.commutes_iff hRzM).mpr (hMcomm 3 (by omega) (by omega))
    have hD3 : ModelAdj (scalars (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f))
        ((Rz (m - 3)).map ρ) ((Rz 3).map ρ) := by
      have : m - 3 = 4 := by omega
      rw [this]
      exact cq.modelAdj (hRf 4 (by omega) (by omega)) (hRf 3 (by omega) (by omega))
        (hadjz 4 (by omega) 3 (by omega) (by omega) (by omega) (by sl_idx))
    have hD2 : ModelAdj (scalars (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f))
        ((Rz 2).map ρ) ((Rz 3).map ρ) :=
      cq.modelAdj (hRf 2 (by omega) (by omega)) (hRf 3 (by omega) (by omega))
        (hadjz 2 (by omega) 3 (by omega) (by omega) (by omega) (by sl_idx))
    have hf2 : (Rz 2).map ρ ∈ fundSet (quadOdd m (GaloisField p f)) :=
      cq.map_mem _ (hRf 2 (by omega) (by omega))
    obtain ⟨iD2, hiD2⟩ := hf2
    have hMJ : ∀ x ∈ negSpace iM, ∀ y ∈ negSpace i3, polar (quadOdd m (GaloisField p f)) x y = 0 :=
      polar_negSpace_of_adj_commute c.hodd hdim9 hiM hi3 hiD hM3 hD3 hDM
    have hY3 : ∀ k, Commutes (Y k) ((Rz 3).map ρ) := by
      intro k
      fin_cases k
      · exact (cq.commutes_iff (hRf (m - 2) (by omega) (by omega))).mpr
          (hcommz (m - 2) (by omega) 3 (by omega) (by omega) (by omega)
            (nd.commutes_of_not_adj (fin_ne_of_val_ne (by sl_idx)) (by sl_idx)))
      · exact (cq.commutes_iff (hRf (m - 1) (by omega) (by omega))).mpr
          (hcommz (m - 1) (by omega) 3 (by omega) (by omega) (by omega)
            (nd.commutes_of_not_adj (fin_ne_of_val_ne (by sl_idx)) (by sl_idx)))
      · exact (cq.commutes_iff hRN).mpr
          ((c.commutes_iff_fund hN₁z (hmemz 3 (by omega) (by omega)) hRN hN₁R
            (hRz 3 (by omega) (by omega)).2).mp
            (commutes_symm (hN₁c 3 (by omega) (by omega))))
    have hD2Y : ∀ k, Commutes ((Rz 2).map ρ) (Y k) := by
      intro k
      fin_cases k
      · exact (cq.commutes_iff (hRf 2 (by omega) (by omega))).mpr
          (hcommz 2 (by omega) (m - 2) (by omega) (by omega) (by omega)
            (nd.commutes_of_not_adj (fin_ne_of_val_ne (by sl_idx)) (by sl_idx)))
      · exact (cq.commutes_iff (hRf 2 (by omega) (by omega))).mpr
          (hcommz 2 (by omega) (m - 1) (by omega) (by omega) (by omega)
            (nd.commutes_of_not_adj (fin_ne_of_val_ne (by sl_idx)) (by sl_idx)))
      · exact (cq.commutes_iff (hRf 2 (by omega) (by omega))).mpr
          ((c.commutes_iff_fund (hmemz 2 (by omega) (by omega)) hN₁z (hRf 2 (by omega) (by omega))
            (hRz 2 (by omega) (by omega)).2 hN₁R).mp (hN₁c 2 (by omega) (by omega)))
    have horthY3 : ∀ k, ∀ x ∈ negSpace (iY k), ∀ y ∈ negSpace i3,
        polar (quadOdd m (GaloisField p f)) x y = 0 := fun k =>
      polar_negSpace_of_adj_commute c.hodd hdim9 (hiY k) hi3 hiD2 (hY3 k) hD2 (hD2Y k)
    have hsup := finrank_negSpace_sup c.hodd hiM hi3 hMJ
    refine model_contradiction_of_span c.hodd hQ hiso hsq hdimE (S := negSpace iM ⊔ negSpace i3)
      ?_ ?_ hiY hYinj hfixY ?_
    · exact sup_le (negSpace_le_eigenspace_neg_of_fixed c.hodd hiso hsq hdimE hiM hfixM)
        (negSpace_le_eigenspace_neg_of_fixed c.hodd hiso hsq hdimE hi3 hfix3)
    · rw [hsup, hdimV]
      omega
    · intro k y hy s hs
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hs
      rw [polar_add_right, polar_comm _ y u, hMY k u hu y hy, horthY3 k y hy w hw, add_zero]

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
