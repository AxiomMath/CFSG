module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Frame
public import CFSG.ClassicalInvolution.Q3.Q3TD3Orth
public import CFSG.ClassicalInvolution.RouteD.GapsFrZSide
public import CFSG.ClassicalInvolution.RouteD.GapsToralD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


local macro "fr_idx3" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Defs

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem partner_involution_commutes_z3 {β : Subgroup G} {t : G} (hz : IsClassicalMember3 K z)
    (ht : IsClassicalMember3 β t) (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) :
    t * z * t⁻¹ = z := by
  obtain ⟨W, hW⟩ := hKβ
  have hzt : Commute z t := standardPair_involutions_commute two_ne_zero_gf3 hW hz.mem ht.mem
    hz.orderOf_eq_two ht.orderOf_eq_two
  rw [mul_inv_eq_iff_eq_mul]
  exact hzt.symm.eq

@[expose] def ToralNormalD3 {m : ℕ} (c : TCtx3 .POmegaPlus m Ω K z) {t : G}
    (ht : t * z * t⁻¹ = z) : Prop :=
  ∃ (k₀ : (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K)
    (v : Fin (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rank → ZMod 2),
    ∀ γ ∈ (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.roots,
      ((conjSub k₀ ((modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup (-γ))).map c.d.ψ).map
          (locAut c.hΩ.conjInvariant ht).toMonoidHom =
        (conjSub k₀ ((modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup (-γ))).map c.d.ψ ∧
      ((∀ x ∈ (conjSub k₀ ((modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup (-γ))).map c.d.ψ,
        locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)

omit [Finite G] in
theorem toralNormalD3_of_toral {m : ℕ} (hm3 : 3 ≤ m) (c : TCtx3 .POmegaPlus m Ω K z) {t : G}
    (htz : t * z * t⁻¹ = z)
    {e : Fin (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rank ≃ Fin m}
    {ι : spinGroup (quadPlus m (GaloisField 3 1)) ≃*
      (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K}
    (hc : IsoCompatPlus hm3 e ι)
    (h : ∃ (k₀ : spinGroup (quadPlus m (GaloisField 3 1))) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (plusDatum m (GaloisField 3 1) hm3).roots →
        ((((plusDatum m (GaloisField 3 1) hm3).rootGroup γ ⊔
              (plusDatum m (GaloisField 3 1) hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map (c.d.ψ.comp ι.toMonoidHom)).map
              (locAut c.hΩ.conjInvariant htz).toMonoidHom =
          (((plusDatum m (GaloisField 3 1) hm3).rootGroup γ ⊔
              (plusDatum m (GaloisField 3 1) hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map (c.d.ψ.comp ι.toMonoidHom) ∧
        ((∀ y ∈ (((plusDatum m (GaloisField 3 1) hm3).rootGroup γ ⊔
              (plusDatum m (GaloisField 3 1) hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map (c.d.ψ.comp ι.toMonoidHom),
              locAut c.hΩ.conjInvariant htz y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0)) :
    ToralNormalD3 c htz := by
  classical
  obtain ⟨k₀, v', hk₀⟩ := h
  refine ⟨ι k₀, v' ∘ e, fun γ hγ => ?_⟩
  have hγ' : γ ∘ e.symm ∈ (plusDatum m (GaloisField 3 1) hm3).roots := (hc γ).1.mp hγ
  obtain ⟨hnorm, hfix⟩ := hk₀ (γ ∘ e.symm) hγ'
  have hG₁ : (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup γ =
      ((plusDatum m (GaloisField 3 1) hm3).rootGroup (γ ∘ e.symm)).map ι.toMonoidHom :=
    (hc γ).2
  have hG₂ : (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup (-γ) =
      ((plusDatum m (GaloisField 3 1) hm3).rootGroup (-(γ ∘ e.symm))).map ι.toMonoidHom :=
    (hc (-γ)).2
  have hRG : conjSub (ι k₀) ((modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup γ ⊔
      (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup (-γ)) =
      (((plusDatum m (GaloisField 3 1) hm3).rootGroup (γ ∘ e.symm) ⊔
        (plusDatum m (GaloisField 3 1) hm3).rootGroup (-(γ ∘ e.symm))).map
          (MulAut.conj k₀).toMonoidHom).map ι.toMonoidHom := by
    rw [hG₁, hG₂, ← Subgroup.map_sup]
    exact conjSub_map_equiv ι k₀ _
  have himg : (conjSub (ι k₀) ((modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup γ ⊔
      (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup (-γ))).map c.d.ψ =
      (((plusDatum m (GaloisField 3 1) hm3).rootGroup (γ ∘ e.symm) ⊔
        (plusDatum m (GaloisField 3 1) hm3).rootGroup (-(γ ∘ e.symm))).map
          (MulAut.conj k₀).toMonoidHom).map (c.d.ψ.comp ι.toMonoidHom) := by
    rw [hRG, Subgroup.map_map]
  rw [himg]
  refine ⟨hnorm, hfix.trans ?_⟩
  rw [charOf_comp_equiv]

end Defs

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem toralNormalD3_of_nodes {u : ℕ} (c : TCtx3 .POmegaPlus (u + 3 + 4) Ω K z)
    {β : Subgroup G} {t : G} (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes3 (u + 3 + 4) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K)
    (h1 : nd.J ⟨1, by omega⟩ = β) :
    ToralNormalD3 c (partner_involution_commutes_z3 c.hz ht hKβ) := by
  classical
  have hm3 : 3 ≤ u + 3 + 4 := by omega
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have htz := partner_involution_commutes_z3 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hF := orthFacts3_plus (by omega : 5 ≤ u + 3 + 4)
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  have hadm : StatedLieAdmissible .POmegaPlus (u + 3 + 4) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ u + 3 + 4; omega⟩
  have hKJ : ∀ a (h : a < u + 3 + 4), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx3))
      (by fr_idx3)
  have hmemz : ∀ a (h : a < u + 3 + 4), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < u + 3 + 4), 2 ≤ a →
      ∃ b, ∃ hb : b < u + 3 + 4, 2 ≤ b ∧ DNodes3.Adj (⟨a, h⟩ : Fin (u + 3 + 4)) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a ≤ u + 4
    · exact ⟨a + 1, by omega, by omega, by fr_idx3⟩
    · exact ⟨u + 4, by omega, by omega, by fr_idx3⟩
  have hlayer : ∀ a (h : a < u + 3 + 4), 2 ≤ a → IsLayerMember3 c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember3.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaPlus (u + 3 + 4) 3 1 Nat.prime_three).K,
      ∀ (h : a < u + 3 + 4), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaPlus
            (modelUniv .POmegaPlus (u + 3 + 4) 3 1 Nat.prime_three).D ∧
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
  have hMlayer : IsLayerMember3 c M :=
    IsLayerMember3.of_not_commutes c hMz hNz (fun h => hNM h.symm) hNc
  obtain ⟨RzM, hRzM, hMR⟩ := hMlayer.exists_fund
  have hcommz : ∀ a (ha : a < u + 3 + 4) b (hb : b < u + 3 + 4) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < u + 3 + 4) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < u + 3 + 4) b (hb : b < u + 3 + 4) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin (u + 3 + 4)) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaPlus (u + 3 + 4) 3 1 Nat.prime_three).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    c.modelAdj_of_adj3 (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w _ _) (nd.conjSub_w hab)
  have hlinz : ∀ a (ha : a < u + 3 + 4) b (hb : b < u + 3 + 4) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin (u + 3 + 4)) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact hF.lift c.d.ψ c.d.ker_le _ (hRz a ha ha2).1 _ (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < u + 3 + 4), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < u + 3 + 4), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx3))
      (by fr_idx3)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map (locAut hΩ.conjInvariant htz).toMonoidHom =
      locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩)
      (by simp [DNodes3.adj_def])
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1)) →* locQuot Ω z :=
    c.d.ψ.comp ι.toMonoidHom
  let σ := locAut hΩ.conjInvariant htz
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := by
    intro k'
    obtain ⟨x, hx⟩ := c.locAut_mem_range htz h2t hKt
      (range_le_iSup_fund_plus (p := 3) (f := 1) (by omega) hadm c.d.ψ) (ι k')
    exact ⟨ι.symm x, by simpa [θ] using hx⟩
  let R : ℕ → Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1))) := fun a =>
    (Rz (a + 2)).map ι.symm.toMonoidHom
  let Rtw : Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1))) :=
    (Rz (u + 6)).map ι.symm.toMonoidHom
  let RM : Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1))) :=
    RzM.map ι.symm.toMonoidHom
  have hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)) := fun a ha =>
    map_symm_mem_fund_iso hm3 hcι (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)) :=
    map_symm_mem_fund_iso hm3 hcι (hRz (u + 6) (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)) :=
    map_symm_mem_fund_iso hm3 hcι hRzM
  have hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    ModelAdj.map_equiv ι.symm (hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega)
      (by fr_idx3))
  have hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)) :=
    fun a ha => by
      obtain ⟨W₁, hW₁⟩ := hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega)
        (by fr_idx3)
      exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  have hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b) := fun a b hab hb =>
    (commutes_map_equiv ι.symm).mpr (hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx3))
        (by fr_idx3)))
  have hM : ∀ a ≤ u + 3, Commutes RM (R a) := fun a ha =>
    (commutes_map_equiv ι.symm).mpr (hMcomm (a + 2) (by omega) (by omega))
  have hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw :=
    ModelAdj.map_equiv ι.symm (hadjz (u + 2 + 2) (by omega) (u + 6) (by omega) (by omega)
      (by omega) (by fr_idx3))
  have hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw := fun a ha =>
    (commutes_map_equiv ι.symm).mpr (hcommz (a + 2) (by omega) (u + 6) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx3))
        (by fr_idx3)))
  have hcommtw' : Commutes (R (u + 3)) Rtw :=
    (commutes_map_equiv ι.symm).mpr (hcommz (u + 3 + 2) (by omega) (u + 6) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx3))
        (by fr_idx3)))
  have hne : Rtw ≠ R (u + 3) := by
    intro h
    have h1' : Rz (u + 6) = Rz (u + 3 + 2) := Subgroup.map_injective ι.symm.injective h
    have h2' : nd.J ⟨u + 6, by omega⟩ = nd.J ⟨u + 3 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz (u + 6) (by omega) (by omega)).2, (hRz (u + 3 + 2) (by omega) (by omega)).2,
          h1'])
    exact nd.ne_J (Gaps.fin_ne_of_val_ne (by simp)) h2'
  have hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 =>
    fixed_of_map_symm ι c.d.ψ σ (hRz (a + 2) (by omega) (by omega)).2
      (hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)))
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ (hRz (u + 6) (by omega) (by omega)).2
      (hfixnode (u + 6) (by omega) (by omega) (hβJ (u + 6) (by omega) (by omega)))
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ hMR
      ((locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hMz).mp fun n hn =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := fun y hy =>
    norm_of_map_symm ι c.d.ψ σ (hRz (0 + 2) (by omega) (by omega)).2 hstab2 y hy
  obtain ⟨k₀, v, hk₀⟩ := toralNormal_of_chain_long3 θ hker σ hσ2 hσr hRf hRtwf hRMf hadj
    hlin hcomm hM hadjtw hcommtw hcommtw' hne hfix hfixtw hfixM hnorm0
  exact toralNormalD3_of_toral hm3 c htz hcι ⟨k₀, v, hk₀⟩

end Main

end CFSG.ClassicalInvolution.Q3.Q3TD
