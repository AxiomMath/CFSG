module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBLast
public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen
public import CFSG.ClassicalInvolution.RouteD.TWEB6Star
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open QuadraticMap

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


section Model

theorem toral_lift_six (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (θ : spinGroup (quadOdd 6 (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd 6 (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadOdd 6 (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadOdd 6 (GaloisField p f)))}
    (hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaOdd (oddDatum 6 (GaloisField p f)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaOdd (oddDatum 6 (GaloisField p f)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaOdd (oddDatum 6 (GaloisField p f)))
    (hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b))
    (hM : ∀ a ≤ 2, Commutes RM (R a))
    (hdist : ∀ i j, IsFundamental (quadOdd 6 (GaloisField p f))
      ((R 0).map (spinAction (quadOdd 6 (GaloisField p f)))) i →
      IsFundamental (quadOdd 6 (GaloisField p f))
        ((R 2).map (spinAction (quadOdd 6 (GaloisField p f)))) j → i ≠ j)
    (hne : Rtw ≠ R 2)
    (htwin : ∀ i j, IsFundamental (quadOdd 6 (GaloisField p f))
      ((R 2).map (spinAction (quadOdd 6 (GaloisField p f)))) i →
      IsFundamental (quadOdd 6 (GaloisField p f))
        (Rtw.map (spinAction (quadOdd 6 (GaloisField p f)))) j → i = j)
    (hfix : ∀ a, 1 ≤ a → a ≤ 2 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (x : spinGroup (quadOdd 6 (GaloisField p f))) (t : Bool)
      (α : spinGroup (quadOdd 6 (GaloisField p f)) ≃* spinGroup (quadOdd 6 (GaloisField p f)))
      (k₀ : spinGroup (quadOdd 6 (GaloisField p f))) (v : Fin 6 → ZMod 2),
      (∀ a (ha : a ≤ 2), R a = ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame 2 3 (by omega) (by omega)
        (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      RM = ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame 4 5 (by omega) (by omega)
        (by omega) true t).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, θ (α y) = σ (θ y)) ∧ OddToralProp θ σ k₀ v ∧ OddLift α v := by
  have hm3 : 3 ≤ 6 := by norm_num
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := centralQuot_odd (m := 6) hp2 hm3 hq
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hQ : (quadOdd 6 (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadOdd 6 (GaloisField p f) h2)
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen hp2 hq hQ (s := 2) (by omega)
    (oddFrame 6 (GaloisField p f)).toHypFrame hdim cq hRf hRtwf hRMf hadj hlin hcomm hM
    (fun a b hab hb i j hi hj => by
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
      exact hdist i j hi hj) hne htwin
  obtain ⟨α, k₀, v, hαθ, hk₀, hl⟩ := toralNormal_odd_of_frame_chain_lift hp2 hq (s := 2) (by omega)
    θ hker σ hσ2 hσr x t hxR hxtw hxM hfix hfixtw hfixM hnorm0
  exact ⟨x, t, α, k₀, v, hxR, hxtw, hxM, hαθ, hk₀, hl⟩

end Model

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

local macro "b6_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem recognition_six (c : TCtx p f .POmegaOdd 6 Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f 6 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {N : Subgroup G} (hNΩ : N ∈ Ω) (hNc : ∀ a : Fin 6, a.val < 4 → Commutes N (nd.J a))
    (hN4 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨4, by omega⟩) N)
    (hN5 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨5, by omega⟩) N) :
    ∃ (Rz : ℕ → Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K)
      (RzM : Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K)
      (x : spinGroup (quadOdd 6 (GaloisField p f))) (tM : Bool)
      (α : spinGroup (quadOdd 6 (GaloisField p f)) ≃* spinGroup (quadOdd 6 (GaloisField p f)))
      (g₀ : (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f)),
      (∀ a (h : a < 6), 2 ≤ a →
        Rz a ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 6 p f Fact.out).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = (Rz a).map c.d.ψ) ∧
      (RzM ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 6 p f Fact.out).D ∧
        locImg Ω z M = RzM.map c.d.ψ) ∧
      (∀ a (ha : a ≤ 2), Rz (a + 2) = ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame a
        (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      RzM = ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame 4 5 (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 6 (GaloisField p f)) ∧ g₀ * g₀ = 1 ∧
      (∀ y v, spinAction (quadOdd 6 (GaloisField p f)) (α y) (g₀ v) =
        g₀ (spinAction (quadOdd 6 (GaloisField p f)) y v)) := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hF := orthFacts_odd c.hp2 (by norm_num : 4 ≤ 6) c.hq
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaOdd 6 p f := ⟨Fact.out, hf1, by norm_num, c.hp2⟩
  have hKJ : ∀ a (h : a < 6), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by b6_idx)) (by b6_idx)
  have hmemz : ∀ a (h : a < 6), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 6), 2 ≤ a →
      ∃ b, ∃ hb : b < 6, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin 6) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h3 : a = 3
    · exact ⟨4, by omega, by omega, by subst h3; b6_idx⟩
    · exact ⟨3, by omega, by omega, by b6_idx⟩
  have hlayer : ∀ a (h : a < 6), 2 ≤ a → IsLayerMember c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K,
      ∀ (h : a < 6), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 6 p f Fact.out).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < 6 ∧ 2 ≤ a
    · obtain ⟨R, hR, hLR⟩ := (hlayer a hv.1 hv.2).exists_fund
      exact ⟨R, fun _ _ => ⟨hR, hLR⟩⟩
    · exact ⟨⊥, fun h ha => absurd ⟨h, ha⟩ hv⟩
  choose Rz hRz using hexRz
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  obtain ⟨N₀, hN₀z, hN₀M, hN₀c⟩ := hMN
  have hMlayer : IsLayerMember c M :=
    IsLayerMember.of_not_commutes c hMz hN₀z (fun h => hN₀M h.symm) hN₀c
  obtain ⟨RzM, hRzM, hMR⟩ := hMlayer.exists_fund
  have hNz : N ∈ centralizingMembers Ω {z} := by
    have := hNc ⟨0, by omega⟩ (by norm_num)
    rw [h0] at this
    exact mem_centralizingMembers_of_commutes hNΩ c.hz.mem this
  obtain ⟨W4, hW4⟩ := hN4
  obtain ⟨W5, hW5⟩ := hN5
  have hn4N : ¬ Commutes N (nd.J ⟨4, by omega⟩) := fun h =>
    not_commutes_of_linearBlockStandardPair hW4 (commutes_symm h)
  have hn5N : ¬ Commutes N (nd.J ⟨5, by omega⟩) := fun h =>
    not_commutes_of_linearBlockStandardPair hW5 (commutes_symm h)
  have hN4ne : N ≠ nd.J ⟨4, by omega⟩ := fun h => ne_of_linearBlockStandardPair hW4 h.symm
  have hNlayer : IsLayerMember c N :=
    IsLayerMember.of_not_commutes c hNz (hmemz 4 (by omega) (by omega)) hN4ne hn4N
  obtain ⟨RN, hRN, hNR⟩ := hNlayer.exists_fund
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNΩ
  have hcommz : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaOdd 6 p f Fact.out).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    modelAdj_of_adj c (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hΩ hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _) (nd.conjSub_w h2 hab)
  have hlinz : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact hF.lift c.d.ψ c.d.ker_le _ (hRz a ha ha2).1 _ (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < 6), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff hΩ c.hP1 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < 6), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by b6_idx)) (by b6_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map
      (locAut hΩ.conjInvariant htz).toMonoidHom = locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by b6_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadOdd 6 (GaloisField p f)) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt (range_le_iSup_fund_odd (by omega) hadm c.hY.std c.d.ψ) k'
  let R : ℕ → Subgroup (spinGroup (quadOdd 6 (GaloisField p f))) := fun a => Rz (a + 2)
  let Rtw : Subgroup (spinGroup (quadOdd 6 (GaloisField p f))) := Rz 5
  let RM : Subgroup (spinGroup (quadOdd 6 (GaloisField p f))) := RzM
  have hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaOdd
      (oddDatum 6 (GaloisField p f)) := fun a ha => (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaOdd (oddDatum 6 (GaloisField p f)) :=
    (hRz 5 (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaOdd (oddDatum 6 (GaloisField p f)) := hRzM
  have hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by b6_idx)
  have hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by b6_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b) := fun a b hab hb =>
    hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by b6_idx)) (by b6_idx))
  have hM : ∀ a ≤ 2, Commutes RM (R a) := fun a ha => hMcomm (a + 2) (by omega) (by omega)
  have hne : Rtw ≠ R 2 := by
    intro h
    have h' : Rz 5 = Rz (2 + 2) := h
    have h2' : nd.J ⟨5, by omega⟩ = nd.J ⟨2 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz 5 (by omega) (by omega)).2, (hRz (2 + 2) (by omega) (by omega)).2, h'])
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by simp)) h2'
  have hfix : ∀ a, 1 ≤ a → a ≤ 2 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 y hy =>
    hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)) _
      (by rw [(hRz (a + 2) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y := fun y hy =>
    hfixnode 5 (by omega) (by omega) (hβJ 5 (by omega) (by omega)) _
      (by rw [(hRz 5 (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y := fun y hy =>
    (locAut_fixed_iff hΩ c.hP1 htz hMz).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm) _
      (by rw [hMR]; exact ⟨y, hy, rfl⟩)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := by
    intro y hy
    have hL : locImg Ω z (nd.J ⟨2, by omega⟩) = (R 0).map θ :=
      (hRz (0 + 2) (by omega) (by omega)).2
    rw [← hL, ← hstab2]
    refine ⟨θ y, ?_, rfl⟩
    rw [hL]
    exact ⟨y, hy, rfl⟩
  have hodd : Odd (Nat.card (GaloisField p f)) := c.hodd
  have cq := centralQuot_odd (m := 6) c.hp2 (by norm_num : 3 ≤ 6) c.hq
  have hdimV : 9 ≤ Module.finrank (GaloisField p f) (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hstar : ∃ i₁ i₂ i₃, IsFundamental (quadOdd 6 (GaloisField p f))
      ((Rz 2).map (spinAction (quadOdd 6 (GaloisField p f)))) i₁ ∧
      IsFundamental (quadOdd 6 (GaloisField p f))
        ((Rz 4).map (spinAction (quadOdd 6 (GaloisField p f)))) i₂ ∧
      IsFundamental (quadOdd 6 (GaloisField p f))
        ((Rz 5).map (spinAction (quadOdd 6 (GaloisField p f)))) i₃ ∧
      i₂ ≠ i₁ ∧ i₃ ≠ i₁ ∧ i₃ = i₂ := by
    obtain ⟨ic, hic⟩ := cq.map_mem _ (hRz 3 (by omega) (by omega)).1
    obtain ⟨i₁, hi₁⟩ := cq.map_mem _ (hRz 2 (by omega) (by omega)).1
    obtain ⟨i₂, hi₂⟩ := cq.map_mem _ (hRz 4 (by omega) (by omega)).1
    obtain ⟨i₃, hi₃⟩ := cq.map_mem _ (hRz 5 (by omega) (by omega)).1
    obtain ⟨iS, hiS⟩ := cq.map_mem _ hRN
    have hRf' : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Rz a ∈ fundamentalSubgroups .POmegaOdd
        (oddDatum 6 (GaloisField p f)) := fun a ha ha2 => (hRz a ha ha2).1
    have cm : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
        a ≠ b → ¬ DNodes.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        Commutes ((Rz a).map (spinAction (quadOdd 6 (GaloisField p f))))
          ((Rz b).map (spinAction (quadOdd 6 (GaloisField p f)))) := fun a ha b hb ha2 hb2 hab hn =>
      (cq.commutes_iff (hRf' a ha ha2)).mpr (hcommz a ha b hb ha2 hb2
        (nd.commutes_of_not_adj (fin_ne_of_val_ne hab) hn))
    have ad : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
        DNodes.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        ModelAdj (scalars (GaloisField p f) (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f))
          ((Rz a).map (spinAction (quadOdd 6 (GaloisField p f))))
          ((Rz b).map (spinAction (quadOdd 6 (GaloisField p f)))) := fun a ha b hb ha2 hb2 hab =>
      cq.modelAdj (hRf' a ha ha2) (hRf' b hb hb2) (hadjz a ha b hb ha2 hb2 hab)
    have hNne : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), N ≠ nd.J ⟨a, ha⟩ → 
        (RN.map (spinAction (quadOdd 6 (GaloisField p f)))) ≠
          ((Rz a).map (spinAction (quadOdd 6 (GaloisField p f)))) := fun a ha ha2 hne e =>
      hne (c.eq_of_locImg_eq hNz (hmemz a ha ha2) (by
        rw [hNR, (hRz a ha ha2).2, cq.map_inj hRN (hRf' a ha ha2) e]))
    have hnc : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), (hcn : ¬ Commutes N (nd.J ⟨a, ha⟩)) →
        ¬ Commutes (RN.map (spinAction (quadOdd 6 (GaloisField p f))))
          ((Rz a).map (spinAction (quadOdd 6 (GaloisField p f)))) := fun a ha ha2 hcn h =>
      hcn ((c.commutes_iff_fund hNz (hmemz a ha ha2) hRN hNR (hRz a ha ha2).2).mpr
        ((cq.commutes_iff hRN).mp h))
    have hcN2 : Commutes (RN.map (spinAction (quadOdd 6 (GaloisField p f))))
        ((Rz 2).map (spinAction (quadOdd 6 (GaloisField p f)))) :=
      (cq.commutes_iff hRN).mpr ((c.commutes_iff_fund hNz (hmemz 2 (by omega) (by omega)) hRN hNR
        (hRz 2 (by omega) (by omega)).2).mp (hNc ⟨2, by omega⟩ (by norm_num)))
    have hI : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Commute wN (nd.w ⟨a, ha⟩) →
        ModelInvComm (scalars (GaloisField p f) (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f))
          (RN.map (spinAction (quadOdd 6 (GaloisField p f))))
          ((Rz a).map (spinAction (quadOdd 6 (GaloisField p f)))) := fun a ha ha2 hc =>
      cq.modelInvComm hRN (hRf' a ha ha2)
        (modelInvComm_of_members c hNz (hmemz a ha ha2) hRN (hRf' a ha ha2) hNR
          (hRz a ha ha2).2 hwN (nd.cl _) hc)
    have hcw2 : Commute wN (nd.w ⟨2, by omega⟩) := hNc ⟨2, by omega⟩ (by norm_num) _ hwN.mem _
      (nd.cl _).mem
    have hcw4 : Commute wN (nd.w ⟨4, by omega⟩) :=
      (standardPair_involutions_commute h2 hW4 (nd.cl _).mem hwN.mem (nd.cl _).orderOf_eq_two
        hwN.orderOf_eq_two).symm
    have hcw5 : Commute wN (nd.w ⟨5, by omega⟩) :=
      (standardPair_involutions_commute h2 hW5 (nd.cl _).mem hwN.mem (nd.cl _).orderOf_eq_two
        hwN.orderOf_eq_two).symm
    have hN2ne : N ≠ nd.J ⟨2, by omega⟩ := fun h => not_commutes_self_of_mem hΩ hNΩ
      (h ▸ hNc ⟨2, by omega⟩ (by norm_num))
    have hN5ne : N ≠ nd.J ⟨5, by omega⟩ := fun h => ne_of_linearBlockStandardPair hW5 h.symm
    refine ⟨i₁, i₂, i₃, hi₁, hi₂, hi₃, ?_⟩
    exact star_twin_of_distinguish hodd hdimV hic hi₁ hi₂ hi₃ hiS
      (ad 3 (by omega) 2 (by omega) (by omega) (by omega) (by b6_idx))
      (ad 3 (by omega) 4 (by omega) (by omega) (by omega) (by b6_idx))
      (ad 3 (by omega) 5 (by omega) (by omega) (by omega) (by b6_idx))
      (cm 2 (by omega) 4 (by omega) (by omega) (by omega) (by omega) (by b6_idx))
      (cm 2 (by omega) 5 (by omega) (by omega) (by omega) (by omega) (by b6_idx))
      (cm 4 (by omega) 5 (by omega) (by omega) (by omega) (by omega) (by b6_idx))
      (hNne 2 (by omega) (by omega) hN2ne) (hNne 4 (by omega) (by omega) hN4ne)
      (hNne 5 (by omega) (by omega) hN5ne) (hI 2 (by omega) (by omega) hcw2)
      (hI 4 (by omega) (by omega) hcw4) (hI 5 (by omega) (by omega) hcw5) hcN2
      (hnc 4 (by omega) (by omega) hn4N) (hnc 5 (by omega) (by omega) hn5N)
  obtain ⟨i₁, i₂, i₃, hi₁, hi₂, hi₃, hn21, hn31, h32⟩ := hstar
  have hdist : ∀ i j, IsFundamental (quadOdd 6 (GaloisField p f))
      ((R 0).map (spinAction (quadOdd 6 (GaloisField p f)))) i →
      IsFundamental (quadOdd 6 (GaloisField p f))
        ((R 2).map (spinAction (quadOdd 6 (GaloisField p f)))) j → i ≠ j := fun i j hi hj => by
    have e1 := IsFundamental.involution_unique hodd hi hi₁
    have e2 := IsFundamental.involution_unique hodd hj hi₂
    rw [e1, e2]
    exact hn21.symm
  have htwin : ∀ i j, IsFundamental (quadOdd 6 (GaloisField p f))
      ((R 2).map (spinAction (quadOdd 6 (GaloisField p f)))) i →
      IsFundamental (quadOdd 6 (GaloisField p f))
        (Rtw.map (spinAction (quadOdd 6 (GaloisField p f)))) j → i = j := fun i j hi hj => by
    have e1 := IsFundamental.involution_unique hodd hi hi₂
    have e2 := IsFundamental.involution_unique hodd hj hi₃
    rw [e1, e2, h32]
  obtain ⟨x, tM, α, k₀, v, hxR, hxtw, hxM, hαθ, hk₀, hl⟩ := toral_lift_six c.hp2 c.hq θ c.d.ker_le
    σ hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hdist hne htwin hfix hfixtw hfixM hnorm0
  obtain ⟨g₀, t', hg₀O, hg₀2, hconj, -, -⟩ := hl
  exact ⟨Rz, RzM, x, tM, α, g₀, fun a h ha => hRz a h ha, ⟨hRzM, hMR⟩, hxR, hxM, hαθ, hg₀O, hg₀2,
    hconj⟩

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.B6
