module

public import CFSG.ClassicalInvolution.RouteD.TWED6Lift
public import CFSG.ClassicalInvolution.RouteD.TWED6Bridge
public import CFSG.ClassicalInvolution.RouteD.TWEB6Star
public import CFSG.ClassicalInvolution.RouteD.GapsToralD
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.D6

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open QuadraticMap

set_option linter.unusedSectionVars false

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem star_twin_of_distinguish' (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {c l₁ l₂ l₃ S : Subgroup (V ≃ₗ[K] V)} {ic i₁ i₂ i₃ iS : V ≃ₗ[K] V}
    (hc : IsFundamental Q c ic) (h₁ : IsFundamental Q l₁ i₁) (h₂ : IsFundamental Q l₂ i₂)
    (h₃ : IsFundamental Q l₃ i₃) (hS : IsFundamental Q S iS)
    (a₁ : ModelAdj (scalars K V) c l₁) (a₂ : ModelAdj (scalars K V) c l₂)
    (a₃ : ModelAdj (scalars K V) c l₃) (k12 : Commutes l₁ l₂) (k13 : Commutes l₁ l₃)
    (k23 : Commutes l₂ l₃) (hS1 : S ≠ l₁) (hS2 : S ≠ l₂) (hS3 : S ≠ l₃) (c1 : Commutes S l₁)
    (n2 : ¬ Commutes S l₂) (n3 : ¬ Commutes S l₃) : i₂ ≠ i₁ ∧ i₃ ≠ i₁ ∧ i₃ = i₂ := by
  have hl12 : l₁ ≠ l₂ := fun h => n2 (h ▸ c1)
  have hl13 : l₁ ≠ l₃ := fun h => n3 (h ▸ c1)
  have hS' : S ∈ fundSet Q := ⟨iS, hS⟩
  have hI₁ : ModelInvComm (scalars K V) S l₁ := modelInvComm_of_commutes hodd hS h₁ c1
  have hiS : iS * i₁ = i₁ * iS := c1 iS hS.mem i₁ h₁.mem
  have e2 : i₂ ≠ i₁ := fun h => by
    have hind := indist_of_eq hodd hdim h₁ h₂ hl12 h
    have hI₂ : ModelInvComm (scalars K V) S l₂ := by
      refine ⟨iS, i₂, ⟨hS.mem, hS.orderOf_eq_two hodd⟩, ⟨h₂.mem, h₂.orderOf_eq_two hodd⟩, ?_⟩
      have : iS * i₂ = i₂ * iS := by rw [h]; exact hiS
      rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
      exact (scalars K V).one_mem
    exact n2 ((hind.2 S hS' hS1 hS2 hI₁ hI₂).mp c1)
  have e3 : i₃ ≠ i₁ := fun h => by
    have hind := indist_of_eq hodd hdim h₁ h₃ hl13 h
    have hI₃ : ModelInvComm (scalars K V) S l₃ := by
      refine ⟨iS, i₃, ⟨hS.mem, hS.orderOf_eq_two hodd⟩, ⟨h₃.mem, h₃.orderOf_eq_two hodd⟩, ?_⟩
      have : iS * i₃ = i₃ * iS := by rw [h]; exact hiS
      rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
      exact (scalars K V).one_mem
    exact n3 ((hind.2 S hS' hS1 hS3 hI₁ hI₃).mp c1)
  rcases star_twin hodd hdim hc h₁ h₂ h₃ a₁ a₂ a₃ k12 k13 k23 with h | h | h
  · exact absurd h e2
  · exact absurd h e3
  · exact ⟨e2, e3, h⟩

end Model

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


local macro "d6_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem recognition_plus_six (c : TCtx p f .POmegaPlus 6 Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f 6 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {N : Subgroup G} (hNΩ : N ∈ Ω) (hNc : ∀ a : Fin 6, a.val < 3 → Commutes N (nd.J a))
    (hN4 : ¬ Commutes N (nd.J ⟨4, by omega⟩)) (hN5 : ¬ Commutes N (nd.J ⟨5, by omega⟩)) :
    ∃ (Rz : ℕ → Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K)
      (RzM : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K)
      (RN : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K)
      (x : spinGroup (quadPlus 6 (GaloisField p f))) (tM : Bool)
      (α : spinGroup (quadPlus 6 (GaloisField p f)) ≃* spinGroup (quadPlus 6 (GaloisField p f)))
      (g₀ : (Fin 6 ⊕ Fin 6 → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 6 ⊕ Fin 6 → GaloisField p f)),
      (∀ a (h : a < 6), 2 ≤ a →
        Rz a ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = (Rz a).map c.d.ψ) ∧
      (RzM ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D ∧
        locImg Ω z M = RzM.map c.d.ψ) ∧
      (RN ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D ∧
        locImg Ω z N = RN.map c.d.ψ) ∧
      (∀ a (ha : a ≤ 2), Rz (a + 2) = ((rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) a
        (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      RzM = ((rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 4 5 (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField p f)) ∧ g₀ * g₀ = 1 ∧
      (∀ y v, spinAction (quadPlus 6 (GaloisField p f)) (α y) (g₀ v) =
        g₀ (spinAction (quadPlus 6 (GaloisField p f)) y v)) ∧
      (∀ a : Fin 6, 1 ≤ a.val → a.val ≤ 3 → ∀ s,
        g₀ (spinAction (quadPlus 6 (GaloisField p f)) x
          ((plusFrame 6 (GaloisField p f) (by norm_num)).vec a s)) =
        spinAction (quadPlus 6 (GaloisField p f)) x
          ((plusFrame 6 (GaloisField p f) (by norm_num)).vec a s)) := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hF := orthFacts_plus c.hp2 (by norm_num : 5 ≤ 6) c.hq
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaPlus 6 p f := ⟨Fact.out, hf1, by show 4 ≤ 6; omega⟩
  have hKJ : ∀ a (h : a < 6), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by d6_idx)) (by d6_idx)
  have hmemz : ∀ a (h : a < 6), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 6), 2 ≤ a →
      ∃ b, ∃ hb : b < 6, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin 6) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h3 : a = 3
    · exact ⟨4, by omega, by omega, by subst h3; d6_idx⟩
    · exact ⟨3, by omega, by omega, by d6_idx⟩
  have hlayer : ∀ a (h : a < 6), 2 ≤ a → IsLayerMember c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K,
      ∀ (h : a < 6), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D ∧
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
  have hn45 : Commutes (nd.J ⟨4, by omega⟩) (nd.J ⟨5, by omega⟩) :=
    nd.commutes_of_not_adj (fin_ne_of_val_ne (by d6_idx)) (by d6_idx)
  have hN4ne : N ≠ nd.J ⟨4, by omega⟩ := fun h => hN5 (h ▸ hn45)
  have hNlayer : IsLayerMember c N :=
    IsLayerMember.of_not_commutes c hNz (hmemz 4 (by omega) (by omega)) hN4ne hN4
  obtain ⟨RN, hRN, hNR⟩ := hNlayer.exists_fund
  have hcommz : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K)
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
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by d6_idx)) (by d6_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map
      (locAut hΩ.conjInvariant htz).toMonoidHom = locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by d6_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadPlus 6 (GaloisField p f)) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt (range_le_iSup_fund_plus (by omega) hadm c.d.ψ) k'
  let R : ℕ → Subgroup (spinGroup (quadPlus 6 (GaloisField p f))) := fun a => Rz (a + 2)
  let Rtw : Subgroup (spinGroup (quadPlus 6 (GaloisField p f))) := Rz 5
  let RM : Subgroup (spinGroup (quadPlus 6 (GaloisField p f))) := RzM
  have hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) (by norm_num)) := fun a ha =>
    (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) (by norm_num)) := (hRz 5 (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) (by norm_num)) := hRzM
  have hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by d6_idx)
  have hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by d6_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b) := fun a b hab hb =>
    hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by d6_idx)) (by d6_idx))
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
  have cq := centralQuot_plus (m := 6) c.hp2 (by norm_num : 4 ≤ 6) (by norm_num : 3 ≤ 6) c.hq
  have hdimV : 9 ≤ Module.finrank (GaloisField p f) (Fin 6 ⊕ Fin 6 → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hstar : ∃ i₁ i₂ i₃, IsFundamental (quadPlus 6 (GaloisField p f))
      ((Rz 2).map (spinAction (quadPlus 6 (GaloisField p f)))) i₁ ∧
      IsFundamental (quadPlus 6 (GaloisField p f))
        ((Rz 4).map (spinAction (quadPlus 6 (GaloisField p f)))) i₂ ∧
      IsFundamental (quadPlus 6 (GaloisField p f))
        ((Rz 5).map (spinAction (quadPlus 6 (GaloisField p f)))) i₃ ∧
      i₂ ≠ i₁ ∧ i₃ ≠ i₁ ∧ i₃ = i₂ := by
    obtain ⟨ic, hic⟩ := cq.map_mem _ (hRz 3 (by omega) (by omega)).1
    obtain ⟨i₁, hi₁⟩ := cq.map_mem _ (hRz 2 (by omega) (by omega)).1
    obtain ⟨i₂, hi₂⟩ := cq.map_mem _ (hRz 4 (by omega) (by omega)).1
    obtain ⟨i₃, hi₃⟩ := cq.map_mem _ (hRz 5 (by omega) (by omega)).1
    obtain ⟨iS, hiS⟩ := cq.map_mem _ hRN
    have hRf' : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Rz a ∈ fundamentalSubgroups .POmegaPlus
        (plusDatum 6 (GaloisField p f) (by norm_num)) := fun a ha ha2 => (hRz a ha ha2).1
    have cm : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
        a ≠ b → ¬ DNodes.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        Commutes ((Rz a).map (spinAction (quadPlus 6 (GaloisField p f))))
          ((Rz b).map (spinAction (quadPlus 6 (GaloisField p f)))) :=
      fun a ha b hb ha2 hb2 hab hn =>
      (cq.commutes_iff (hRf' a ha ha2)).mpr (hcommz a ha b hb ha2 hb2
        (nd.commutes_of_not_adj (fin_ne_of_val_ne hab) hn))
    have ad : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
        DNodes.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        ModelAdj (scalars (GaloisField p f) (Fin 6 ⊕ Fin 6 → GaloisField p f))
          ((Rz a).map (spinAction (quadPlus 6 (GaloisField p f))))
          ((Rz b).map (spinAction (quadPlus 6 (GaloisField p f)))) := fun a ha b hb ha2 hb2 hab =>
      cq.modelAdj (hRf' a ha ha2) (hRf' b hb hb2) (hadjz a ha b hb ha2 hb2 hab)
    have hNne : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), N ≠ nd.J ⟨a, ha⟩ →
        (RN.map (spinAction (quadPlus 6 (GaloisField p f)))) ≠
          ((Rz a).map (spinAction (quadPlus 6 (GaloisField p f)))) := fun a ha ha2 hne e =>
      hne (c.eq_of_locImg_eq hNz (hmemz a ha ha2) (by
        rw [hNR, (hRz a ha ha2).2, cq.map_inj hRN (hRf' a ha ha2) e]))
    have hnc : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), (hcn : ¬ Commutes N (nd.J ⟨a, ha⟩)) →
        ¬ Commutes (RN.map (spinAction (quadPlus 6 (GaloisField p f))))
          ((Rz a).map (spinAction (quadPlus 6 (GaloisField p f)))) := fun a ha ha2 hcn h =>
      hcn ((c.commutes_iff_fund hNz (hmemz a ha ha2) hRN hNR (hRz a ha ha2).2).mpr
        ((cq.commutes_iff hRN).mp h))
    have hcN2 : Commutes (RN.map (spinAction (quadPlus 6 (GaloisField p f))))
        ((Rz 2).map (spinAction (quadPlus 6 (GaloisField p f)))) :=
      (cq.commutes_iff hRN).mpr ((c.commutes_iff_fund hNz (hmemz 2 (by omega) (by omega)) hRN hNR
        (hRz 2 (by omega) (by omega)).2).mp (hNc ⟨2, by omega⟩ (by norm_num)))
    have hN2ne : N ≠ nd.J ⟨2, by omega⟩ := fun h => not_commutes_self_of_mem hΩ hNΩ
      (h ▸ hNc ⟨2, by omega⟩ (by norm_num))
    have hN5ne : N ≠ nd.J ⟨5, by omega⟩ := fun h => hN4 (h ▸ commutes_symm hn45)
    refine ⟨i₁, i₂, i₃, hi₁, hi₂, hi₃, ?_⟩
    exact star_twin_of_distinguish' hodd hdimV hic hi₁ hi₂ hi₃ hiS
      (ad 3 (by omega) 2 (by omega) (by omega) (by omega) (by d6_idx))
      (ad 3 (by omega) 4 (by omega) (by omega) (by omega) (by d6_idx))
      (ad 3 (by omega) 5 (by omega) (by omega) (by omega) (by d6_idx))
      (cm 2 (by omega) 4 (by omega) (by omega) (by omega) (by omega) (by d6_idx))
      (cm 2 (by omega) 5 (by omega) (by omega) (by omega) (by omega) (by d6_idx))
      (cm 4 (by omega) 5 (by omega) (by omega) (by omega) (by omega) (by d6_idx))
      (hNne 2 (by omega) (by omega) hN2ne) (hNne 4 (by omega) (by omega) hN4ne)
      (hNne 5 (by omega) (by omega) hN5ne) hcN2
      (hnc 4 (by omega) (by omega) hN4) (hnc 5 (by omega) (by omega) hN5)
  obtain ⟨i₁, i₂, i₃, hi₁, hi₂, hi₃, hn21, hn31, h32⟩ := hstar
  have hdist : ∀ i j, IsFundamental (quadPlus 6 (GaloisField p f))
      ((R 0).map (spinAction (quadPlus 6 (GaloisField p f)))) i →
      IsFundamental (quadPlus 6 (GaloisField p f))
        ((R 2).map (spinAction (quadPlus 6 (GaloisField p f)))) j → i ≠ j := fun i j hi hj => by
    have e1 := IsFundamental.involution_unique hodd hi hi₁
    have e2 := IsFundamental.involution_unique hodd hj hi₂
    rw [e1, e2]
    exact hn21.symm
  have htwin : ∀ i j, IsFundamental (quadPlus 6 (GaloisField p f))
      ((R 2).map (spinAction (quadPlus 6 (GaloisField p f)))) i →
      IsFundamental (quadPlus 6 (GaloisField p f))
        (Rtw.map (spinAction (quadPlus 6 (GaloisField p f)))) j → i = j := fun i j hi hj => by
    have e1 := IsFundamental.involution_unique hodd hi hi₂
    have e2 := IsFundamental.involution_unique hodd hj hi₃
    rw [e1, e2, h32]
  obtain ⟨x, tM, α, g₀, hxR, hxtw, hxM, hαθ, hg₀O, hg₀2, hconj, hfixv⟩ := toral_lift_plus_six
    c.hp2 c.hq θ c.d.ker_le σ hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hdist hne htwin hfix hfixtw
    hfixM hnorm0
  exact ⟨Rz, RzM, RN, x, tM, α, g₀, fun a h ha => hRz a h ha, ⟨hRzM, hMR⟩, ⟨hRN, hNR⟩, hxR, hxM,
    hαθ, hg₀O, hg₀2, hconj, hfixv⟩

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.D6
