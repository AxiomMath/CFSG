module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBZSide
public import CFSG.ClassicalInvolution.RouteD.GapsFrBLift
public import CFSG.ClassicalInvolution.RouteD.GapsFrBEigen
public import CFSG.ClassicalInvolution.RouteD.GapsFrBWeight
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
open QuadraticMap
open scoped commutatorElement

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Group

variable {Kc X : Type} [Group Kc] [Group X]

theorem eq_of_fixed_of_perfect (θ : Kc →* X) (hker : θ.ker ≤ Subgroup.center Kc) (α : Kc ≃* Kc)
    (σ : X ≃* X) (hαθ : ∀ y, θ (α y) = σ (θ y)) {R : Subgroup Kc} (hR : ⁅R, R⁆ = R)
    (hfix : ∀ r ∈ R, σ (θ r) = θ r) : ∀ r ∈ R, α r = r := by
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc := fun r hr => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hfix r hr, inv_mul_cancel])
  have hle : ⁅R, R⁆ ≤ MonoidHom.eqLocus (α : Kc →* Kc) (MonoidHom.id Kc) := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    show α ⁅x, y⁆ = ⁅x, y⁆
    rw [map_commutatorElement]
    have e1 : α x = x * (x⁻¹ * α x) := by group
    have e2 : α y = y * (y⁻¹ * α y) := by group
    rw [e1, e2, CFSG.ClassicalInvolution.ModelFacts.commutatorElement_mul_central (hc x hx)
      (hc y hy)]
  intro r hr
  have := hle (hR ▸ hr)
  exact this

end Group

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem false_of_bad_class {m : ℕ} (hm : 8 ≤ m) (c : TCtx p f .POmegaOdd m Ω K z)
    {β : Subgroup G} {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f m Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {N₁ : Subgroup G} (hN₁Ω : N₁ ∈ Ω) (hN₁K : Commutes K N₁) (hN₁β : Commutes β N₁)
    (hN₁M : Commutes M N₁)
    (hN₁c : ∀ a (h : a < m), 3 ≤ a → a + 4 ≤ m → Commutes (nd.J ⟨a, h⟩) N₁)
    (hN₁adj : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨m - 3, by omega⟩) N₁)
    (hN₁2 : N₁ ≠ nd.J ⟨m - 2, by omega⟩) (hN₁1 : N₁ ≠ nd.J ⟨m - 1, by omega⟩)
    {α : spinGroup (quadOdd m (GaloisField p f)) ≃* spinGroup (quadOdd m (GaloisField p f))}
    {v : Fin m → ZMod 2}
    (hαθ : ∀ x, c.d.ψ (α x) = locAut c.hΩ.conjInvariant
      (partner_involution_commutes c.hp2 c.hz ht hKβ) (c.d.ψ x))
    (hlift : OddLift α v) (p₀ : Fin m) (hp₀ : p₀.val + 2 = m)
    (hreach : CharReach (CartanMatrix.C m) v (Pi.single p₀ 1)) : False := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKJ : ∀ a (h : a < m), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)
  have hmemz : ∀ a (h : a < m), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < m), 2 ≤ a →
      ∃ b, ∃ hb : b < m, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin m) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a ≤ m - 3
    · exact ⟨a + 1, by omega, by omega, by fr_idx⟩
    · exact ⟨m - 3, by omega, by omega, by fr_idx⟩
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
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hQ : (polarBilin (quadOdd m (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2
  have hdimV : Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) =
      2 * m + 1 := by
    rw [finrank_odd]
  let ρ := spinAction (quadOdd m (GaloisField p f))
  let c' : ℕ → Subgroup ((Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f)) := fun a => (Rz (a + 3)).map ρ
  have hchain : IsChain (scalars (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f))
      (fundSet (quadOdd m (GaloisField p f))) (m - 4) c' := by
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun a b hab hb => ?_⟩
    · exact cq.map_mem _ (hRf (a + 3) (by omega) (by omega))
    · exact cq.modelAdj (hRf (a + 3) (by omega) (by omega))
        (hRf (a + 1 + 3) (by omega) (by omega))
        (hadjz (a + 3) (by omega) (a + 1 + 3) (by omega) (by omega) (by omega) (by fr_idx))
    · exact (cq.commutes_iff (hRf (a + 3) (by omega) (by omega))).mpr
        (hcommz (a + 3) (by omega) (b + 3) (by omega) (by omega) (by omega)
          (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)))
  have hLM : RzM.map ρ ∈ fundSet (quadOdd m (GaloisField p f)) := cq.map_mem _ hRzM
  let Y : Fin 3 → Subgroup ((Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f)) :=
    ![(Rz (m - 2)).map ρ, (Rz (m - 1)).map ρ, RN.map ρ]
  have hY : ∀ k, Y k ∈ fundSet (quadOdd m (GaloisField p f)) := by
    intro k
    fin_cases k
    · exact cq.map_mem _ (hRf (m - 2) (by omega) (by omega))
    · exact cq.map_mem _ (hRf (m - 1) (by omega) (by omega))
    · exact cq.map_mem _ hRN
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
  have hfixc : ∀ a < m - 6, ∀ l ∈ c' a, g₀ * l = l * g₀ := fun a ha =>
    hfixmem (hmemz (a + 3) (by omega) (by omega)) (hRf (a + 3) (by omega) (by omega))
      (hRz (a + 3) (by omega) (by omega)).2 (hβJ (a + 3) (by omega) (by omega))
  have hfixM : ∀ l ∈ RzM.map ρ, g₀ * l = l * g₀ := hfixmem hMz hRzM hMR hMβ
  have hfixY : ∀ k, ∀ l ∈ Y k, g₀ * l = l * g₀ := by
    intro k
    fin_cases k
    · exact hfixmem (hmemz (m - 2) (by omega) (by omega)) (hRf (m - 2) (by omega) (by omega))
        (hRz (m - 2) (by omega) (by omega)).2 (hβJ (m - 2) (by omega) (by omega))
    · exact hfixmem (hmemz (m - 1) (by omega) (by omega)) (hRf (m - 1) (by omega) (by omega))
        (hRz (m - 1) (by omega) (by omega)).2 (hβJ (m - 1) (by omega) (by omega))
    · exact hfixmem hN₁z hRN hN₁R hN₁β
  have hMc : ∀ a < m - 6, Commutes (RzM.map ρ) (c' a) := fun a ha =>
    (cq.commutes_iff hRzM).mpr (hMcomm (a + 3) (by omega) (by omega))
  have hYc : ∀ k, ∀ a < m - 6, Commutes (Y k) (c' a) := by
    intro k a ha
    fin_cases k
    · exact (cq.commutes_iff (hRf (m - 2) (by omega) (by omega))).mpr
        (hcommz (m - 2) (by omega) (a + 3) (by omega) (by omega) (by omega)
          (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)))
    · exact (cq.commutes_iff (hRf (m - 1) (by omega) (by omega))).mpr
        (hcommz (m - 1) (by omega) (a + 3) (by omega) (by omega) (by omega)
          (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)))
    · exact (cq.commutes_iff hRN).mpr
        ((c.commutes_iff_fund hN₁z (hmemz (a + 3) (by omega) (by omega)) hRN hN₁R
          (hRz (a + 3) (by omega) (by omega)).2).mp
          (commutes_symm (hN₁c (a + 3) (by omega) (by omega) (by omega))))
  have hYM : ∀ k, Commutes (Y k) (RzM.map ρ) := by
    intro k
    fin_cases k
    · exact (cq.commutes_iff (hRf (m - 2) (by omega) (by omega))).mpr
        (hMcomm (m - 2) (by omega) (by omega)).symm
    · exact (cq.commutes_iff (hRf (m - 1) (by omega) (by omega))).mpr
        (hMcomm (m - 1) (by omega) (by omega)).symm
    · exact (cq.commutes_iff hRN).mpr
        ((c.commutes_iff_fund hN₁z hMz hRN hN₁R hMR).mp (commutes_symm hN₁M))
  have hDc : c' (m - 6) = (Rz (m - 3)).map ρ := by
    show (Rz (m - 6 + 3)).map ρ = _
    rw [show m - 6 + 3 = m - 3 by omega]
  have hD : ∀ k, ModelAdj (scalars (GaloisField p f)
      (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f)) (c' (m - 6)) (Y k) := by
    intro k
    rw [hDc]
    fin_cases k
    · exact cq.modelAdj (hRf (m - 3) (by omega) (by omega)) (hRf (m - 2) (by omega) (by omega))
        (hadjz (m - 3) (by omega) (m - 2) (by omega) (by omega) (by omega) (by fr_idx))
    · exact cq.modelAdj (hRf (m - 3) (by omega) (by omega)) (hRf (m - 1) (by omega) (by omega))
        (hadjz (m - 3) (by omega) (m - 1) (by omega) (by omega) (by omega) (by fr_idx))
    · obtain ⟨w₁, hw₁⟩ := hΩ.classical N₁ hN₁Ω
      refine cq.modelAdj (hRf (m - 3) (by omega) (by omega)) hRN ?_
      exact modelAdj_of_adj c (hmemz (m - 3) (by omega) (by omega)) hN₁z
        (hRz (m - 3) (by omega) (by omega)).1 hRN (hRz (m - 3) (by omega) (by omega)).2 hN₁R
        (nd.cl _) hw₁ (fun e => ne_of_linearBlockStandardPair hWJ e)
        (not_commutes_of_linearBlockStandardPair hWJ)
        (standardPair_involutions_commute h2 hWJ (nd.cl _).mem hw₁.mem (nd.cl _).orderOf_eq_two
          hw₁.orderOf_eq_two)
        (conjSub_eq_of_standardPair h2 hWJ hw₁.mem hw₁.orderOf_eq_two)
  have hDM : Commutes (c' (m - 6)) (RzM.map ρ) := by
    rw [hDc]
    exact (cq.commutes_iff (hRf (m - 3) (by omega) (by omega))).mpr
      (hMcomm (m - 3) (by omega) (by omega)).symm
  exact model_contradiction c.hodd hQ hm hdimV hiso hsq hdimE hchain hLM hY hYinj hfixc hfixM
    hfixY hMc hYc hYM hD hDM


theorem toralNormalB_lift_of_nodes {u : ℕ} (c : TCtx p f .POmegaOdd (u + 3 + 4) Ω K z)
    {β : Subgroup G} {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f (u + 3 + 4) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K)
    (h1 : nd.J ⟨1, by omega⟩ = β) :
    ∃ (α : spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)) ≃*
        spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))
      (k₀ : spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))
      (v : Fin (u + 3 + 4) → ZMod 2),
      (∀ x, c.d.ψ (α x) = locAut c.hΩ.conjInvariant
        (partner_involution_commutes c.hp2 c.hz ht hKβ) (c.d.ψ x)) ∧
      ToralPropB c (partner_involution_commutes c.hp2 c.hz ht hKβ) k₀ v ∧ OddLift α v := by
  classical
  have hm3 : 3 ≤ u + 3 + 4 := by omega
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hF := orthFacts_odd c.hp2 (by omega : 4 ≤ u + 3 + 4) c.hq
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaOdd (u + 3 + 4) p f :=
    ⟨Fact.out, hf1, by omega, c.hp2⟩
  have hKJ : ∀ a (h : a < u + 3 + 4), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)
  have hmemz : ∀ a (h : a < u + 3 + 4), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < u + 3 + 4), 2 ≤ a →
      ∃ b, ∃ hb : b < u + 3 + 4, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin (u + 3 + 4)) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a ≤ u + 4
    · exact ⟨a + 1, by omega, by omega, by fr_idx⟩
    · exact ⟨u + 4, by omega, by omega, by fr_idx⟩
  have hlayer : ∀ a (h : a < u + 3 + 4), 2 ≤ a → IsLayerMember c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaOdd (u + 3 + 4) p f Fact.out).K,
      ∀ (h : a < u + 3 + 4), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd (u + 3 + 4) p f Fact.out).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < u + 3 + 4 ∧ 2 ≤ a
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
  have hcommz : ∀ a (ha : a < u + 3 + 4) b (hb : b < u + 3 + 4) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < u + 3 + 4) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < u + 3 + 4) b (hb : b < u + 3 + 4) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin (u + 3 + 4)) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaOdd (u + 3 + 4) p f Fact.out).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    modelAdj_of_adj c (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hΩ hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _) (nd.conjSub_w h2 hab)
  have hlinz : ∀ a (ha : a < u + 3 + 4) b (hb : b < u + 3 + 4) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin (u + 3 + 4)) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact hF.lift c.d.ψ c.d.ker_le _ (hRz a ha ha2).1 _ (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < u + 3 + 4), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff hΩ c.hP1 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < u + 3 + 4), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map (locAut hΩ.conjInvariant htz).toMonoidHom =
      locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩)
      (by fr_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt (range_le_iSup_fund_odd (by omega) hadm c.hY.std c.d.ψ) k'
  let R : ℕ → Subgroup (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f))) := fun a =>
    Rz (a + 2)
  let Rtw : Subgroup (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f))) := Rz (u + 6)
  let RM : Subgroup (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f))) := RzM
  have hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaOdd
      (oddDatum (u + 3 + 4) (GaloisField p f)) := fun a ha =>
    (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 3 + 4) (GaloisField p f)) :=
    (hRz (u + 6) (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 3 + 4) (GaloisField p f)) :=
    hRzM
  have hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b) := fun a b hab hb =>
    hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hM : ∀ a ≤ u + 3, Commutes RM (R a) := fun a ha =>
    hMcomm (a + 2) (by omega) (by omega)
  have hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw :=
    hadjz (u + 2 + 2) (by omega) (u + 6) (by omega) (by omega) (by omega) (by fr_idx)
  have hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw := fun a ha =>
    hcommz (a + 2) (by omega) (u + 6) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hcommtw' : Commutes (R (u + 3)) Rtw :=
    hcommz (u + 3 + 2) (by omega) (u + 6) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hne : Rtw ≠ R (u + 3) := by
    intro h
    have h' : Rz (u + 6) = Rz (u + 3 + 2) := h
    have h2' : nd.J ⟨u + 6, by omega⟩ = nd.J ⟨u + 3 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz (u + 6) (by omega) (by omega)).2, (hRz (u + 3 + 2) (by omega) (by omega)).2,
          h'])
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by simp)) h2'
  have hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 y hy =>
    hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)) _
      (by rw [(hRz (a + 2) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y := fun y hy =>
    hfixnode (u + 6) (by omega) (by omega) (hβJ (u + 6) (by omega) (by omega)) _
      (by rw [(hRz (u + 6) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y := fun y hy =>
    (locAut_fixed_iff hΩ c.hP1 htz hMz).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm) _
      (by rw [hMR]; exact ⟨y, hy, rfl⟩)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := by
    intro y hy
    have hL : locImg Ω z (nd.J ⟨2, by omega⟩) = (R 0).map θ := (hRz (0 + 2) (by omega) (by omega)).2
    rw [← hL, ← hstab2]
    refine ⟨θ y, ?_, rfl⟩
    rw [hL]
    exact ⟨y, hy, rfl⟩
  obtain ⟨α, k₀, v, hαθ, hk₀, hl⟩ := toralNormal_odd_of_chain_long_lift c.hp2 c.hq θ c.d.ker_le σ
    hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hadjtw hcommtw hcommtw' hne hfix hfixtw hfixM hnorm0
  exact ⟨α, k₀, v, hαθ, hk₀, hl⟩

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
