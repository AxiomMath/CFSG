module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallTwin
public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen
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

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Star

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {KY : Type} [Group KY]
  {𝓕 : Set (Subgroup KY)} {π : KY →* (V ≃ₗ[F] V)}

theorem star_twin (hodd : Odd (Nat.card F)) (hdim : 9 ≤ Module.finrank F V)
    (cq : CentralQuot π 𝓕 (fundSet Q) (scalars F V)) {R₀ R₁ R₂ Rt : Subgroup KY}
    (hR₀ : R₀ ∈ 𝓕) (hR₁ : R₁ ∈ 𝓕) (hR₂ : R₂ ∈ 𝓕) (hRt : Rt ∈ 𝓕)
    (hadj01 : ModelAdj (Subgroup.center KY) R₀ R₁) (hadj12 : ModelAdj (Subgroup.center KY) R₁ R₂)
    (hadj1t : ModelAdj (Subgroup.center KY) R₁ Rt) (hc02 : Commutes R₀ R₂)
    (hc0t : Commutes R₀ Rt) (hc2t : Commutes R₂ Rt)
    (hn02 : ∀ i j, IsFundamental Q (R₀.map π) i → IsFundamental Q (R₂.map π) j → i ≠ j)
    (hn0t : ∀ i j, IsFundamental Q (R₀.map π) i → IsFundamental Q (Rt.map π) j → i ≠ j) :
    ∀ i j, IsFundamental Q (R₂.map π) i → IsFundamental Q (Rt.map π) j → i = j := by
  classical
  obtain ⟨i0, hi0⟩ := cq.map_mem _ hR₀
  obtain ⟨i1, hi1⟩ := cq.map_mem _ hR₁
  obtain ⟨i2, hi2⟩ := cq.map_mem _ hR₂
  obtain ⟨it, hit⟩ := cq.map_mem _ hRt
  intro i j hi hj
  have e1 : i2 = i := IsFundamental.involution_unique hodd hi2 hi
  have e2 : it = j := IsFundamental.involution_unique hodd hit hj
  rw [← e1, ← e2]
  by_contra hne
  have hne' : i2 ≠ it := hne
  have o02 : ∀ x ∈ negSpace i0, ∀ y ∈ negSpace i2, polar Q x y = 0 := by
    rcases orth_or_twin hodd hi0 hi2 ((cq.commutes_iff hR₀).mpr hc02) with h | h
    · exact h
    · exact absurd h.symm (hn02 i0 i2 hi0 hi2)
  have o0t : ∀ x ∈ negSpace i0, ∀ y ∈ negSpace it, polar Q x y = 0 := by
    rcases orth_or_twin hodd hi0 hit ((cq.commutes_iff hR₀).mpr hc0t) with h | h
    · exact h
    · exact absurd h.symm (hn0t i0 it hi0 hit)
  have o2t : ∀ x ∈ negSpace i2, ∀ y ∈ negSpace it, polar Q x y = 0 := by
    rcases orth_or_twin hodd hi2 hit ((cq.commutes_iff hR₂).mpr hc2t) with h | h
    · exact h
    · exact absurd h.symm hne'
  obtain ⟨cm1, N1, C1⟩ := adj_data hodd hdim hi0 hi1 (cq.modelAdj hR₀ hR₁ hadj01)
  obtain ⟨cm2, N2, C2⟩ := adj_data hodd hdim hi1 hi2 (cq.modelAdj hR₁ hR₂ hadj12)
  obtain ⟨cm3, N3, C3⟩ := adj_data hodd hdim hi1 hit (cq.modelAdj hR₁ hRt hadj1t)
  have pd1 := (lemma_6_10 hodd hi0 hi1 cm1 N1 C1).1
  have pd2 := (lemma_6_10 hodd hi1 hi2 cm2 N2 C2).1
  have pd3 := (lemma_6_10 hodd hi1 hit cm3 N3 C3).1
  refine not_three_orth_planes (Q := Q) (W := negSpace i1)
    (P₁ := negSpace i0 ⊓ negSpace i1) (P₂ := negSpace i1 ⊓ negSpace i2)
    (P₃ := negSpace i1 ⊓ negSpace it) (finrank_negSpace hodd hi1)
    inf_le_right inf_le_left inf_le_left pd1.finrank_U₂ pd2.finrank_U₂ pd3.finrank_U₂
    pd1.nondeg₂ pd3.nondeg₂ ?_ ?_ ?_
  · exact fun x hx y hy => o02 x (Submodule.mem_inf.mp hx).1 y (Submodule.mem_inf.mp hy).2
  · exact fun x hx y hy => o0t x (Submodule.mem_inf.mp hx).1 y (Submodule.mem_inf.mp hy).2
  · exact fun x hx y hy => o2t x (Submodule.mem_inf.mp hx).2 y (Submodule.mem_inf.mp hy).2

end Star

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem chain_twin_data_seven (c : TCtx p f .POmegaMinus 7 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus 7 Ω z) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (nd : DNodes p f (7 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K)
    {R₂ R₃ R₄ R₅ : Subgroup (SpinM p f 7)}
    (hR₂ : R₂ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)))
    (hR₃ : R₃ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)))
    (hR₄ : R₄ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)))
    (hR₅ : R₅ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)))
    (hi₂ : locImg Ω z (nd.J ⟨2, by omega⟩) = R₂.map c.d.ψ)
    (hi₃ : locImg Ω z (nd.J ⟨3, by omega⟩) = R₃.map c.d.ψ)
    (hi₄ : locImg Ω z (nd.J ⟨4, by omega⟩) = R₄.map c.d.ψ)
    (hi₅ : locImg Ω z (nd.J ⟨5, by omega⟩) = R₅.map c.d.ψ) :
    (∀ i j, IsFundamental (QM p f 7) (R₂.map (spinAction (QM p f 7))) i →
      IsFundamental (QM p f 7) (R₄.map (spinAction (QM p f 7))) j → i ≠ j) ∧
    (∀ i j, IsFundamental (QM p f 7) (R₄.map (spinAction (QM p f 7))) i →
      IsFundamental (QM p f 7) (R₅.map (spinAction (QM p f 7))) j → i = j) := by
  classical
  have hΩ := c.hΩ
  have hm4 : 4 ≤ 7 := by norm_num
  have cq := ctx_centralQuot c hm4
  have hodd := c.hodd
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hdim : 13 ≤ Module.finrank (GaloisField p f) (Vm 7 (GaloisField p f)) := by
    rw [finrank_minus p f 7 (by omega)]
    omega
  have hKJ : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < 7 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have a23 : DNodes.Adj (⟨2, by omega⟩ : Fin (7 - 1)) ⟨3, by omega⟩ := by fr_idx
  have a34 : DNodes.Adj (⟨3, by omega⟩ : Fin (7 - 1)) ⟨4, by omega⟩ := by fr_idx
  have a35 : DNodes.Adj (⟨3, by omega⟩ : Fin (7 - 1)) ⟨5, by omega⟩ := by fr_idx
  have hadj23 : ModelAdj (Subgroup.center (SpinM p f 7)) R₂ R₃ :=
    modelAdj_of_adj c (hmemz 2 _ le_rfl) (hmemz 3 _ (by omega)) hR₂ hR₃ hi₂ hi₃ (nd.cl _)
      (nd.cl _) (nd.ne_J hΩ a23.ne) (nd.not_commutes_of_adj a23) (nd.commute_w h2 _ _)
      (nd.conjSub_w h2 a23)
  have hadj34 : ModelAdj (Subgroup.center (SpinM p f 7)) R₃ R₄ :=
    modelAdj_of_adj c (hmemz 3 _ (by omega)) (hmemz 4 _ (by omega)) hR₃ hR₄ hi₃ hi₄ (nd.cl _)
      (nd.cl _) (nd.ne_J hΩ a34.ne) (nd.not_commutes_of_adj a34) (nd.commute_w h2 _ _)
      (nd.conjSub_w h2 a34)
  have hadj35 : ModelAdj (Subgroup.center (SpinM p f 7)) R₃ R₅ :=
    modelAdj_of_adj c (hmemz 3 _ (by omega)) (hmemz 5 _ (by omega)) hR₃ hR₅ hi₃ hi₅ (nd.cl _)
      (nd.cl _) (nd.ne_J hΩ a35.ne) (nd.not_commutes_of_adj a35) (nd.commute_w h2 _ _)
      (nd.conjSub_w h2 a35)
  have hc24 : Commutes R₂ R₄ :=
    (c.commutes_iff_fund (hmemz 2 _ le_rfl) (hmemz 4 _ (by omega)) hR₂ hi₂ hi₄).mp
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp)) (by fr_idx))
  have hc25 : Commutes R₂ R₅ :=
    (c.commutes_iff_fund (hmemz 2 _ le_rfl) (hmemz 5 _ (by omega)) hR₂ hi₂ hi₅).mp
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp)) (by fr_idx))
  have hc45 : Commutes R₄ R₅ :=
    (c.commutes_iff_fund (hmemz 4 _ (by omega)) (hmemz 5 _ (by omega)) hR₄ hi₄ hi₅).mp
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp)) (by fr_idx))
  obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
  obtain ⟨cM⟩ := exists_ctx_member c hsingle hshape hMΩ hxM
  have hmemM : ∀ a : Fin (7 - 1), nd.J a ∈ centralizingMembers Ω {xM} := fun a =>
    mem_centralizingMembers_of_commutes (nd.mem a) hxM.mem (commutes_symm (nd.commK a))
  have hnb : ∀ a : Fin (7 - 1), ∃ b : Fin (7 - 1), DNodes.Adj a b := by
    rintro ⟨a, ha⟩
    have : a < 6 := ha
    interval_cases a
    · exact ⟨⟨1, by omega⟩, by fr_idx⟩
    · exact ⟨⟨0, by omega⟩, by fr_idx⟩
    · exact ⟨⟨1, by omega⟩, by fr_idx⟩
    · exact ⟨⟨2, by omega⟩, by fr_idx⟩
    · exact ⟨⟨3, by omega⟩, by fr_idx⟩
    · exact ⟨⟨3, by omega⟩, by fr_idx⟩
  have hlayerM : ∀ a : Fin (7 - 1), IsLayerMember cM (nd.J a) := fun a => by
    obtain ⟨b, hab⟩ := hnb a
    exact IsLayerMember.of_not_commutes cM (hmemM a) (hmemM b) (nd.ne_J hΩ hab.ne)
      (nd.not_commutes_of_adj hab)
  obtain ⟨Rm, hRm⟩ : ∃ Rm : Fin (7 - 1) → Subgroup (SpinM p f 7), ∀ a,
      Rm a ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) ∧
        locImg Ω xM (nd.J a) = (Rm a).map cM.d.ψ :=
    ⟨fun a => (hlayerM a).exists_fund.choose, fun a => (hlayerM a).exists_fund.choose_spec⟩
  have hadjM : ∀ a b : Fin (7 - 1), DNodes.Adj a b →
      ModelAdj (Subgroup.center (SpinM p f 7)) (Rm a) (Rm b) := fun a b hab =>
    modelAdj_of_adj cM (hmemM a) (hmemM b) (hRm a).1 (hRm b).1 (hRm a).2 (hRm b).2 (nd.cl _)
      (nd.cl _) (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _)
      (nd.conjSub_w h2 hab)
  have hcommM : ∀ a b : Fin (7 - 1), a ≠ b → ¬ DNodes.Adj a b → Commutes (Rm a) (Rm b) :=
    fun a b hab hna =>
      (cM.commutes_iff_fund (hmemM a) (hmemM b) (hRm a).1 (hRm a).2 (hRm b).2).mp
        (nd.commutes_of_not_adj hab hna)
  let R' : ℕ → Subgroup (SpinM p f 7) := fun a => if h : a < 7 - 1 then Rm ⟨a, h⟩ else ⊥
  have hR'eq : ∀ a (h : a < 7 - 1), R' a = Rm ⟨a, h⟩ := fun a h => by simp [R', h]
  have hdim9 : 9 ≤ Module.finrank (GaloisField p f) (Vm 7 (GaloisField p f)) := by omega
  obtain ⟨hdistM, htwinM⟩ := chain_distinct_twin_gen (u := 1) (R := R') (Rtw := Rm ⟨5, by omega⟩)
    c.hp2 c.hq hdim9 cq
    (fun a ha => by rw [hR'eq a (by omega)]; exact (hRm _).1)
    (hRm _).1
    (fun a ha => by
      rw [hR'eq a (by omega), hR'eq (a + 1) (by omega)]
      exact hadjM _ _ (by fr_idx))
    (fun a b hab hb => by
      rw [hR'eq a (by omega), hR'eq b (by omega)]
      exact hcommM _ _ (fin_ne_of_val_ne (by simp; omega)) (by fr_idx))
    (by
      rw [hR'eq (1 + 2) (by omega)]
      exact hadjM _ _ (by fr_idx))
    (fun a ha => by
      rw [hR'eq a (by omega)]
      exact hcommM _ _ (fin_ne_of_val_ne (by simp; omega)) (by fr_idx))
    (by
      rw [hR'eq (1 + 3) (by omega)]
      exact hcommM _ _ (fin_ne_of_val_ne (by simp)) (by fr_idx))
  have hframe : ∀ a : Fin (7 - 1), ∃ F : OPFrame (QM p f 7),
      (Rm a).map (spinAction (QM p f 7)) = F.La.range := fun a => by
    obtain ⟨i, F, hF, -⟩ := cq.map_mem _ (hRm a).1
    exact ⟨F, hF⟩
  choose Fm hFm using hframe
  have hisoM : ∀ a : Fin (7 - 1), IsFundamental (QM p f 7) ((Rm a).map (spinAction (QM p f 7)))
      ((Fm a).La (-1)) := fun a => ⟨Fm a, hFm a, rfl⟩
  have hFne : ∀ a b : Fin (7 - 1), a.val + 1 < b.val → b.val ≤ 4 →
      (Fm a).La (-1) ≠ (Fm b).La (-1) := by
    intro a b hab hb
    refine hdistM a.val b.val hab hb _ _ ?_ ?_
    · rw [hR'eq a.val a.isLt]
      exact hisoM a
    · rw [hR'eq b.val b.isLt]
      exact hisoM b
  have hFtw : (Fm ⟨4, by omega⟩).La (-1) = (Fm ⟨5, by omega⟩).La (-1) :=
    htwinM _ _ (by rw [hR'eq 4 (by omega)]; exact hisoM _) (hisoM _)
  have hspan : ∀ a b : Fin (7 - 1), a ≠ b → ¬ DNodes.Adj a b → (Fm a).La (-1) ≠ (Fm b).La (-1) →
      ∀ x ∈ (Fm a).span, ∀ y ∈ (Fm b).span, polar (QM p f 7) x y = 0 := by
    intro a b hab hna hne
    refine span_orth_of_commutes_ne hodd ?_ hne
    rw [← hFm a, ← hFm b]
    exact (cq.commutes_iff (hRm a).1).mpr (hcommM a b hab hna)
  have hKxM : K ∈ centralizingMembers Ω {xM} := h0 ▸ hmemM ⟨0, by omega⟩
  have hKimg : locImg Ω xM K = (Rm ⟨0, by omega⟩).map cM.d.ψ := h0 ▸ (hRm _).2
  have hsame : ∀ {R R' : Subgroup (SpinM p f 7)} {i j : _ ≃ₗ[GaloisField p f] _}, i = j →
      IsFundamental (QM p f 7) (R.map (spinAction (QM p f 7))) i →
      IsFundamental (QM p f 7) (R'.map (spinAction (QM p f 7))) j →
      ∀ i' j', IsFundamental (QM p f 7) (R.map (spinAction (QM p f 7))) i' →
        IsFundamental (QM p f 7) (R'.map (spinAction (QM p f 7))) j' → i' = j' := by
    intro R R' i j hij hi hj i' j' hi' hj'
    rw [IsFundamental.involution_unique hodd hi' hi, IsFundamental.involution_unique hodd hj' hj,
      hij]
  have hn02 : ∀ i j, IsFundamental (QM p f 7) (R₂.map (spinAction (QM p f 7))) i →
      IsFundamental (QM p f 7) (R₄.map (spinAction (QM p f 7))) j → i ≠ j := by
    intro i j hi hj hij
    exact false_of_twins_other_layer c cM le_rfl hKxM (hmemz 2 _ le_rfl) (hmemz 4 _ (by omega))
      (hmemM ⟨2, by omega⟩) (hmemM ⟨4, by omega⟩) (nd.cl _) (nd.cl _) hR₂ hR₄ hi₂ hi₄
      (hsame hij hi hj) (hRm ⟨2, by omega⟩).1 (hRm ⟨4, by omega⟩).1 hKimg (hRm _).2 (hRm _).2
      (Fm ⟨0, by omega⟩) (Fm ⟨2, by omega⟩) (Fm ⟨4, by omega⟩) (hFm _) (hFm _) (hFm _)
      (hspan _ _ (fin_ne_of_val_ne (by simp)) (by fr_idx) (hFne _ _ (by simp) (by simp)))
      (hspan _ _ (fin_ne_of_val_ne (by simp)) (by fr_idx) (hFne _ _ (by simp) (by simp)))
      (hspan _ _ (fin_ne_of_val_ne (by simp)) (by fr_idx) (hFne _ _ (by simp) (by simp)))
  have hn05 : ∀ i j, IsFundamental (QM p f 7) (R₂.map (spinAction (QM p f 7))) i →
      IsFundamental (QM p f 7) (R₅.map (spinAction (QM p f 7))) j → i ≠ j := by
    intro i j hi hj hij
    have hne05 : (Fm ⟨0, by omega⟩).La (-1) ≠ (Fm ⟨5, by omega⟩).La (-1) := by
      rw [← hFtw]
      exact hFne _ _ (by simp) (by simp)
    have hne25 : (Fm ⟨2, by omega⟩).La (-1) ≠ (Fm ⟨5, by omega⟩).La (-1) := by
      rw [← hFtw]
      exact hFne _ _ (by simp) (by simp)
    exact false_of_twins_other_layer c cM le_rfl hKxM (hmemz 2 _ le_rfl) (hmemz 5 _ (by omega))
      (hmemM ⟨2, by omega⟩) (hmemM ⟨5, by omega⟩) (nd.cl _) (nd.cl _) hR₂ hR₅ hi₂ hi₅
      (hsame hij hi hj) (hRm ⟨2, by omega⟩).1 (hRm ⟨5, by omega⟩).1 hKimg (hRm _).2 (hRm _).2
      (Fm ⟨0, by omega⟩) (Fm ⟨2, by omega⟩) (Fm ⟨5, by omega⟩) (hFm _) (hFm _) (hFm _)
      (hspan _ _ (fin_ne_of_val_ne (by simp)) (by fr_idx) (hFne _ _ (by simp) (by simp)))
      (hspan _ _ (fin_ne_of_val_ne (by simp)) (by fr_idx) hne05)
      (hspan _ _ (fin_ne_of_val_ne (by simp)) (by fr_idx) hne25)
  exact ⟨hn02, star_twin hodd (by omega) cq hR₂ hR₃ hR₄ hR₅ hadj23 hadj34 hadj35 hc24 hc25 hc45
    hn02 hn05⟩

end Main

end CFSG.ClassicalInvolution.RouteD.TwinSmall
