module

public import CFSG.ClassicalInvolution.RouteD.GapsFrPattern
public import CFSG.ClassicalInvolution.RouteD.GapsToralDSmall
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

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups IsClassicalMember
  centralizingMembers modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Geometry

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem not_three_orth_fours {U₁ U₂ U₃ : Submodule K V} (hV : Module.finrank K V < 12)
    (f₁ : Module.finrank K U₁ = 4) (f₂ : Module.finrank K U₂ = 4) (f₃ : Module.finrank K U₃ = 4)
    (n₁ : PolarNondegOn Q U₁) (n₃ : PolarNondegOn Q U₃)
    (o12 : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0) (o13 : ∀ x ∈ U₁, ∀ y ∈ U₃, polar Q x y = 0)
    (o23 : ∀ x ∈ U₂, ∀ y ∈ U₃, polar Q x y = 0) : False := by
  have hdis : Disjoint U₁ U₂ := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    refine n₁ x hx1 fun y hy => ?_
    rw [polar_comm]
    exact o12 y hy x hx2
  have h12 := Frame.finrank_sup_of_disjoint hdis
  have hdis' : Disjoint (U₁ ⊔ U₂) U₃ := by
    rw [Submodule.disjoint_def]
    intro x hx hx3
    refine n₃ x hx3 fun y hy => ?_
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, o13 u hu y hy, o23 u' hu' y hy, add_zero]
  have h123 := Frame.finrank_sup_of_disjoint hdis'
  have hle : Module.finrank K ↥(U₁ ⊔ U₂ ⊔ U₃) ≤ Module.finrank K V := Submodule.finrank_le _
  omega

omit [FiniteDimensional K V] in
theorem polarNondegOn_negSpace [Finite K] (hodd : Odd (Nat.card K)) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) : PolarNondegOn Q (negSpace i) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  rw [negSpace_La_neg_one h2]
  exact F.polarNondegOn_span

end Geometry

section Five

variable {p f : ℕ} [Fact p.Prime]

theorem chain_twin_five (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R0 R1 Rtw RM : Subgroup (spinGroup (quadPlus 5 (GaloisField p f)))}
    (hR0 : R0 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by omega)))
    (hR1 : R1 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by omega)))
    (hRtw : Rtw ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by omega)))
    (hRM : RM ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by omega)))
    (hadj1 : ModelAdj (Subgroup.center _) R0 R1) (hadj2 : ModelAdj (Subgroup.center _) R0 Rtw)
    (hc12 : Commutes R1 Rtw) (hM0 : Commutes RM R0) (hM1 : Commutes RM R1)
    (hM2 : Commutes RM Rtw) :
    ∀ i j, IsFundamental (quadPlus 5 (GaloisField p f))
        (R1.map (spinAction (quadPlus 5 (GaloisField p f)))) i →
      IsFundamental (quadPlus 5 (GaloisField p f))
        (Rtw.map (spinAction (quadPlus 5 (GaloisField p f)))) j → i = j := by
  classical
  have hm3 : 3 ≤ 5 := by omega
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hfr : Module.finrank (GaloisField p f) (Fin 5 ⊕ Fin 5 → GaloisField p f) = 10 := by
    rw [finrank_plus]
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin 5 ⊕ Fin 5 → GaloisField p f) := by
    omega
  have cq := centralQuot_plus hp2 (by omega : 4 ≤ 5) hm3 hq
  obtain ⟨i0, hi0⟩ := cq.map_mem _ hR0
  obtain ⟨i1, hi1⟩ := cq.map_mem _ hR1
  obtain ⟨i2, hi2⟩ := cq.map_mem _ hRtw
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRM
  intro i j hi hj
  have e1 : i1 = i := IsFundamental.involution_unique hodd hi1 hi
  have e2 : i2 = j := IsFundamental.involution_unique hodd hi2 hj
  rw [← e1, ← e2]
  by_contra hne
  have hadj1V := cq.modelAdj hR0 hR1 hadj1
  have hadj2V := cq.modelAdj hR0 hRtw hadj2
  have c12 : Commutes (R1.map (spinAction (quadPlus 5 (GaloisField p f))))
      (Rtw.map (spinAction (quadPlus 5 (GaloisField p f)))) := (cq.commutes_iff hR1).mpr hc12
  have cM0 : Commutes (RM.map (spinAction (quadPlus 5 (GaloisField p f))))
      (R0.map (spinAction (quadPlus 5 (GaloisField p f)))) := (cq.commutes_iff hRM).mpr hM0
  have cM1 : Commutes (R1.map (spinAction (quadPlus 5 (GaloisField p f))))
      (RM.map (spinAction (quadPlus 5 (GaloisField p f)))) :=
    (cq.commutes_iff hR1).mpr (commutes_symm hM1)
  have cM2 : Commutes (Rtw.map (spinAction (quadPlus 5 (GaloisField p f))))
      (RM.map (spinAction (quadPlus 5 (GaloisField p f)))) :=
    (cq.commutes_iff hRtw).mpr (commutes_symm hM2)
  have o12 : ∀ x ∈ negSpace i1, ∀ y ∈ negSpace i2,
      polar (quadPlus 5 (GaloisField p f)) x y = 0 := by
    rcases orth_or_twin hodd hi1 hi2 c12 with h | h
    · exact h
    · exact absurd h.symm hne
  have oM : ∀ {L : Subgroup ((Fin 5 ⊕ Fin 5 → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 5 ⊕ Fin 5 → GaloisField p f))} {il : (Fin 5 ⊕ Fin 5 → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 5 ⊕ Fin 5 → GaloisField p f)},
      IsFundamental (quadPlus 5 (GaloisField p f)) L il →
      ModelAdj (scalars (GaloisField p f) (Fin 5 ⊕ Fin 5 → GaloisField p f))
        (R0.map (spinAction (quadPlus 5 (GaloisField p f)))) L →
      Commutes L (RM.map (spinAction (quadPlus 5 (GaloisField p f)))) →
      ∀ x ∈ negSpace il, ∀ y ∈ negSpace iM, polar (quadPlus 5 (GaloisField p f)) x y = 0 := by
    intro L il hl hadj hcomm
    rcases orth_or_twin hodd hl hiM hcomm with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, C⟩ := adj_data hodd hdim hi0 hl hadj
      apply C
      rw [← h]
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => (cM0 iM hiM.mem g hg).symm
  exact not_three_orth_fours (Q := quadPlus 5 (GaloisField p f)) (U₁ := negSpace i1)
    (U₂ := negSpace i2) (U₃ := negSpace iM) (by omega) (finrank_negSpace hodd hi1)
    (finrank_negSpace hodd hi2) (finrank_negSpace hodd hiM) (polarNondegOn_negSpace hodd hi1)
    (polarNondegOn_negSpace hodd hiM) o12 (oM hi1 hadj1V cM1) (oM hi2 hadj2V cM2)

theorem toralNormal_of_chain_five (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (θ : spinGroup (quadPlus 5 (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus 5 (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadPlus 5 (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus 5 (GaloisField p f)))}
    (hRf : ∀ a ≤ 1, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 5 (GaloisField p f) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by omega)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by omega)))
    (hadj : ModelAdj (Subgroup.center _) (R 0) (R 1))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R 0) (R 1))
    (hM : ∀ a ≤ 1, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R 0) Rtw) (hcommtw : Commutes (R 1) Rtw)
    (hMtw : Commutes RM Rtw) (hne : Rtw ≠ R 1)
    (hfix : ∀ y ∈ R 1, σ (θ y) = θ y) (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y)
    (hfixM : ∀ y ∈ RM, σ (θ y) = θ y) (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (k₀ : spinGroup (quadPlus 5 (GaloisField p f))) (v : Fin 5 → ZMod 2),
      ∀ γ : Fin 5 → ℤ, γ ∈ (plusDatum 5 (GaloisField p f) (by omega)).roots →
        ((((plusDatum 5 (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum 5 (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum 5 (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum 5 (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum 5 (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum 5 (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) :=
  toralNormal_of_chain (s := 1) hp2 hq (by omega) θ hker σ hσ2 hσr hRf hRtwf hRMf
    (fun a ha => by
      obtain rfl : a = 0 := by omega
      exact hadj)
    (fun a ha => by
      obtain rfl : a = 0 := by omega
      exact hlin)
    (fun a b hab hb => absurd hb (by omega)) hM
    (fun a b hab hb => absurd hb (by omega)) hne
    (chain_twin_five hp2 hq (hRf 0 (by omega)) (hRf 1 le_rfl) hRtwf hRMf hadj hadjtw hcommtw
      (hM 0 (by omega)) (hM 1 le_rfl) hMtw)
    (fun a ha1 ha2 => by
      obtain rfl : a = 1 := by omega
      exact hfix)
    hfixtw hfixM hnorm0

theorem toralNormalD_of_nodes_five {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {z : G} (c : TCtx p f .POmegaPlus 5 Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f 5 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β) :
    ToralNormalD c (partner_involution_commutes c.hp2 c.hz ht hKβ) := by
  classical
  have hm3 : 3 ≤ 5 := by omega
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hF := orthFacts_plus c.hp2 (le_refl 5) c.hq
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := p) (f := f) hm3
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaPlus 5 p f :=
    ⟨Fact.out, hf1, by show 4 ≤ 5; omega⟩
  have hKJ : ∀ a (h : a < 5), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)
  have hmemz : ∀ a (h : a < 5), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 5), 2 ≤ a →
      ∃ b, ∃ hb : b < 5, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin 5) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a = 2
    · exact ⟨3, by omega, by omega, by fr_idx⟩
    · exact ⟨2, by omega, by omega, by fr_idx⟩
  have hlayer : ∀ a (h : a < 5), 2 ≤ a → IsLayerMember c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaPlus 5 p f Fact.out).K,
      ∀ (h : a < 5), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 5 p f Fact.out).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < 5 ∧ 2 ≤ a
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
  have hcommz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 5) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin 5) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaPlus 5 p f Fact.out).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    modelAdj_of_adj c (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hΩ hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _) (nd.conjSub_w h2 hab)
  have hlinz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin 5) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact hF.lift c.d.ψ c.d.ker_le _ (hRz a ha ha2).1 _ (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < 5), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff hΩ c.hP1 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < 5), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
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
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by fr_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadPlus 5 (GaloisField p f)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  let σ := locAut hΩ.conjInvariant htz
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus 5 (GaloisField p f))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := by
    intro k'
    obtain ⟨x, hx⟩ := locAut_mem_range c htz h2t hKt (range_le_iSup_fund_plus (by omega) hadm c.d.ψ)
      (ι k')
    exact ⟨ι.symm x, by simpa [θ] using hx⟩
  let R : ℕ → Subgroup (spinGroup (quadPlus 5 (GaloisField p f))) := fun a =>
    (Rz (a + 2)).map ι.symm.toMonoidHom
  let Rtw : Subgroup (spinGroup (quadPlus 5 (GaloisField p f))) :=
    (Rz 4).map ι.symm.toMonoidHom
  let RM : Subgroup (spinGroup (quadPlus 5 (GaloisField p f))) :=
    RzM.map ι.symm.toMonoidHom
  have hRf : ∀ a ≤ 1, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 5 (GaloisField p f) (by omega)) := fun a ha =>
    map_symm_mem_fund_iso hm3 hcι (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 5 (GaloisField p f) (by omega)) :=
    map_symm_mem_fund_iso hm3 hcι (hRz 4 (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 5 (GaloisField p f) (by omega)) :=
    map_symm_mem_fund_iso hm3 hcι hRzM
  have hadj : ModelAdj (Subgroup.center _) (R 0) (R 1) :=
    ModelAdj.map_equiv ι.symm (hadjz 2 (by omega) 3 (by omega) (by omega) (by omega) (by fr_idx))
  have hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R 0) (R 1) := by
    obtain ⟨W₁, hW₁⟩ := hlinz 2 (by omega) 3 (by omega) (by omega) (by omega) (by fr_idx)
    exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  have hM : ∀ a ≤ 1, Commutes RM (R a) := fun a ha =>
    (commutes_map_equiv ι.symm).mpr (hMcomm (a + 2) (by omega) (by omega))
  have hadjtw : ModelAdj (Subgroup.center _) (R 0) Rtw :=
    ModelAdj.map_equiv ι.symm (hadjz 2 (by omega) 4 (by omega) (by omega) (by omega) (by fr_idx))
  have hcommtw : Commutes (R 1) Rtw :=
    (commutes_map_equiv ι.symm).mpr (hcommz 3 (by omega) 4 (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx)))
  have hMtw : Commutes RM Rtw :=
    (commutes_map_equiv ι.symm).mpr (hMcomm 4 (by omega) (by omega))
  have hne : Rtw ≠ R 1 := by
    intro h
    have h1' : Rz 4 = Rz (1 + 2) := Subgroup.map_injective ι.symm.injective h
    have h2' : nd.J ⟨4, by omega⟩ = nd.J ⟨1 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz 4 (by omega) (by omega)).2, (hRz (1 + 2) (by omega) (by omega)).2, h1'])
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by fr_idx)) h2'
  have hfix : ∀ y ∈ R 1, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ (hRz (1 + 2) (by omega) (by omega)).2
      (hfixnode (1 + 2) (by omega) (by omega) (hβJ (1 + 2) (by omega) (by omega)))
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ (hRz 4 (by omega) (by omega)).2
      (hfixnode 4 (by omega) (by omega) (hβJ 4 (by omega) (by omega)))
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ hMR
      ((locAut_fixed_iff hΩ c.hP1 htz hMz).mp fun n hn =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := fun y hy =>
    norm_of_map_symm ι c.d.ψ σ (hRz (0 + 2) (by omega) (by omega)).2 hstab2 y hy
  obtain ⟨k₀, v, hk₀⟩ := toralNormal_of_chain_five c.hp2 c.hq θ hker σ hσ2 hσr hRf hRtwf hRMf hadj
    hlin hM hadjtw hcommtw hMtw hne hfix hfixtw hfixM hnorm0
  exact toralNormalD_of_toral hm3 c htz hcι ⟨k₀, v, hk₀⟩

theorem toralNormalD_of_fixed_member_five {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {z : G} (c : TCtx p f .POmegaPlus 5 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus 5 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    ToralNormalD c (partner_involution_commutes c.hp2 c.hz ht hKβ) := by
  obtain ⟨M, hMΩ, hKM, hβM, hMN⟩ := hfixM
  have hMN' : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra h
    exact hMN fun N hN hNM => by_contra fun hc => h ⟨N, hN, hNM, hc⟩
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair (le_refl 5) c hsingle hshape hβ ht hKβ hMΩ hKM hβM
  exact toralNormalD_of_nodes_five c ht hKβ hMΩ hMN' nd h0 h1

theorem PartnerPatternD.of_fixed_member_five {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus 5 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus 5 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    PartnerPatternD p f 5 Ω K β t :=
  PartnerPatternD.of_toral_normal_of_adapted (le_refl 5) hMFZ
    (orthFacts_plus c.hp2 (le_refl 5) c.hq) c hsingle hshape hβ ht hKβ hfixM
    (toralNormalD_of_fixed_member_five c hsingle hshape hβ ht hKβ hfixM)
    fun nd {_ _} hβ' ht' hKβ' {_} hfix hmov hnorm =>
      adapted_pattern_D5 (orthFacts_plus c.hp2 (le_refl 5) c.hq) c hsingle hshape nd hβ' ht' hKβ'
        hfix hmov hnorm

end Five


end CFSG.ClassicalInvolution.RouteD.Gaps
