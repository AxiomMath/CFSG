module

public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes
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
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutDiagC

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits CFSG.Timmesfeld

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Pullback

variable {A B X : Type} [Group A] [Group B] [Group X]

theorem fixed_of_map_symm (ι : A ≃* B) (ψ : B →* X) (σ : X ≃* X) {R : Subgroup B}
    {L : Subgroup X} (hL : L = R.map ψ) (h : ∀ a ∈ L, σ a = a) :
    ∀ y ∈ R.map ι.symm.toMonoidHom, σ ((ψ.comp ι.toMonoidHom) y) = (ψ.comp ι.toMonoidHom) y := by
  rintro _ ⟨r, hr, rfl⟩
  have e : (ψ.comp ι.toMonoidHom) (ι.symm.toMonoidHom r) = ψ r := by simp
  rw [e]
  exact h _ (hL ▸ ⟨r, hr, rfl⟩)

theorem norm_of_map_symm (ι : A ≃* B) (ψ : B →* X) (σ : X ≃* X) {R : Subgroup B}
    {L : Subgroup X} (hL : L = R.map ψ) (h : L.map σ.toMonoidHom = L) :
    ∀ y ∈ R.map ι.symm.toMonoidHom,
      σ ((ψ.comp ι.toMonoidHom) y) ∈ (R.map ι.symm.toMonoidHom).map (ψ.comp ι.toMonoidHom) := by
  have e : (R.map ι.symm.toMonoidHom).map (ψ.comp ι.toMonoidHom) = L := by
    rw [hL, Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [e]
  rintro _ ⟨r, hr, rfl⟩
  have e2 : (ψ.comp ι.toMonoidHom) (ι.symm.toMonoidHom r) = ψ r := by simp
  rw [e2]
  have hr' : ψ r ∈ L := hL ▸ ⟨r, hr, rfl⟩
  have : σ (ψ r) ∈ L.map σ.toMonoidHom := ⟨ψ r, hr', rfl⟩
  rwa [h] at this

theorem map_map_symm (ι : A ≃* B) (ψ : B →* X) (R : Subgroup B) :
    (R.map ι.symm.toMonoidHom).map (ψ.comp ι.toMonoidHom) = R.map ψ := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp

end Pullback

section Convert

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

omit [Finite G] in
theorem toralNormalD_of_toral {m : ℕ} (hm3 : 3 ≤ m) (c : TCtx p f .POmegaPlus m Ω K z) {t : G}
    (htz : t * z * t⁻¹ = z)
    {e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m}
    {ι : spinGroup (quadPlus m (GaloisField p f)) ≃* (modelUniv .POmegaPlus m p f Fact.out).K}
    (hc : IsoCompatPlus hm3 e ι)
    (h : ∃ (k₀ : spinGroup (quadPlus m (GaloisField p f))) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (plusDatum m (GaloisField p f) hm3).roots →
        ((((plusDatum m (GaloisField p f) hm3).rootGroup γ ⊔
              (plusDatum m (GaloisField p f) hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map (c.d.ψ.comp ι.toMonoidHom)).map
              (locAut c.hΩ.conjInvariant htz).toMonoidHom =
          (((plusDatum m (GaloisField p f) hm3).rootGroup γ ⊔
              (plusDatum m (GaloisField p f) hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map (c.d.ψ.comp ι.toMonoidHom) ∧
        ((∀ y ∈ (((plusDatum m (GaloisField p f) hm3).rootGroup γ ⊔
              (plusDatum m (GaloisField p f) hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map (c.d.ψ.comp ι.toMonoidHom),
              locAut c.hΩ.conjInvariant htz y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0)) :
    ToralNormalD c htz := by
  classical
  obtain ⟨k₀, v', hk₀⟩ := h
  refine ⟨ι k₀, v' ∘ e, fun γ hγ => ?_⟩
  have hγ' : γ ∘ e.symm ∈ (plusDatum m (GaloisField p f) hm3).roots := (hc γ).1.mp hγ
  obtain ⟨hnorm, hfix⟩ := hk₀ (γ ∘ e.symm) hγ'
  have hG₁ : (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ =
      ((plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm)).map ι.toMonoidHom :=
    (hc γ).2
  have hG₂ : (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ) =
      ((plusDatum m (GaloisField p f) hm3).rootGroup (-(γ ∘ e.symm))).map ι.toMonoidHom :=
    (hc (-γ)).2
  have hRG : conjSub (ι k₀) ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
      (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ)) =
      (((plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm) ⊔
        (plusDatum m (GaloisField p f) hm3).rootGroup (-(γ ∘ e.symm))).map
          (MulAut.conj k₀).toMonoidHom).map ι.toMonoidHom := by
    rw [hG₁, hG₂, ← Subgroup.map_sup]
    exact conjSub_map_equiv ι k₀ _
  have himg : (conjSub (ι k₀) ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
      (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ =
      (((plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm) ⊔
        (plusDatum m (GaloisField p f) hm3).rootGroup (-(γ ∘ e.symm))).map
          (MulAut.conj k₀).toMonoidHom).map (c.d.ψ.comp ι.toMonoidHom) := by
    rw [hRG, Subgroup.map_map]
  rw [himg]
  refine ⟨hnorm, hfix.trans ?_⟩
  rw [charOf_comp_equiv]

end Convert

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem toralNormalD_of_nodes {u : ℕ} (c : TCtx p f .POmegaPlus (u + 3 + 4) Ω K z)
    {β : Subgroup G} {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f (u + 3 + 4) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K)
    (h1 : nd.J ⟨1, by omega⟩ = β) :
    ToralNormalD c (partner_involution_commutes c.hp2 c.hz ht hKβ) := by
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
  have hF := orthFacts_plus c.hp2 (by omega : 5 ≤ u + 3 + 4) c.hq
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := p) (f := f) hm3
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaPlus (u + 3 + 4) p f :=
    ⟨Fact.out, hf1, by show 4 ≤ u + 3 + 4; omega⟩
  have hKJ : ∀ a (h : a < u + 3 + 4), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx))
      (by fr_idx)
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
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaPlus (u + 3 + 4) p f Fact.out).K,
      ∀ (h : a < u + 3 + 4), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus (u + 3 + 4) p f Fact.out).D ∧
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
        ModelAdj (Subgroup.center (modelUniv .POmegaPlus (u + 3 + 4) p f Fact.out).K)
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
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx))
      (by fr_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map (locAut hΩ.conjInvariant htz).toMonoidHom =
      locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩)
      (by simp [DNodes.adj_def])
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadPlus (u + 3 + 4) (GaloisField p f)) →* locQuot Ω z :=
    c.d.ψ.comp ι.toMonoidHom
  let σ := locAut hΩ.conjInvariant htz
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := by
    intro k'
    obtain ⟨x, hx⟩ := locAut_mem_range c htz h2t hKt (range_le_iSup_fund_plus (by omega) hadm c.d.ψ)
      (ι k')
    exact ⟨ι.symm x, by simpa [θ] using hx⟩
  let R : ℕ → Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f))) := fun a =>
    (Rz (a + 2)).map ι.symm.toMonoidHom
  let Rtw : Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f))) :=
    (Rz (u + 6)).map ι.symm.toMonoidHom
  let RM : Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f))) :=
    RzM.map ι.symm.toMonoidHom
  have hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)) := fun a ha =>
    map_symm_mem_fund_iso hm3 hcι (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)) :=
    map_symm_mem_fund_iso hm3 hcι (hRz (u + 6) (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)) :=
    map_symm_mem_fund_iso hm3 hcι hRzM
  have hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    ModelAdj.map_equiv ι.symm (hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega)
      (by fr_idx))
  have hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)) :=
    fun a ha => by
      obtain ⟨W₁, hW₁⟩ := hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega)
        (by fr_idx)
      exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  have hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b) := fun a b hab hb =>
    (commutes_map_equiv ι.symm).mpr (hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx))
        (by fr_idx)))
  have hM : ∀ a ≤ u + 3, Commutes RM (R a) := fun a ha =>
    (commutes_map_equiv ι.symm).mpr (hMcomm (a + 2) (by omega) (by omega))
  have hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw :=
    ModelAdj.map_equiv ι.symm (hadjz (u + 2 + 2) (by omega) (u + 6) (by omega) (by omega)
      (by omega) (by fr_idx))
  have hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw := fun a ha =>
    (commutes_map_equiv ι.symm).mpr (hcommz (a + 2) (by omega) (u + 6) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx))
        (by fr_idx)))
  have hcommtw' : Commutes (R (u + 3)) Rtw :=
    (commutes_map_equiv ι.symm).mpr (hcommz (u + 3 + 2) (by omega) (u + 6) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx))
        (by fr_idx)))
  have hne : Rtw ≠ R (u + 3) := by
    intro h
    have h1' : Rz (u + 6) = Rz (u + 3 + 2) := Subgroup.map_injective ι.symm.injective h
    have h2' : nd.J ⟨u + 6, by omega⟩ = nd.J ⟨u + 3 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz (u + 6) (by omega) (by omega)).2, (hRz (u + 3 + 2) (by omega) (by omega)).2,
          h1'])
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by simp)) h2'
  have hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 =>
    fixed_of_map_symm ι c.d.ψ σ (hRz (a + 2) (by omega) (by omega)).2
      (hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)))
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ (hRz (u + 6) (by omega) (by omega)).2
      (hfixnode (u + 6) (by omega) (by omega) (hβJ (u + 6) (by omega) (by omega)))
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ hMR
      ((locAut_fixed_iff hΩ c.hP1 htz hMz).mp fun n hn =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := fun y hy =>
    norm_of_map_symm ι c.d.ψ σ (hRz (0 + 2) (by omega) (by omega)).2 hstab2 y hy
  obtain ⟨k₀, v, hk₀⟩ := toralNormal_of_chain_long c.hp2 c.hq θ hker σ hσ2 hσr hRf hRtwf hRMf hadj
    hlin hcomm hM hadjtw hcommtw hcommtw' hne hfix hfixtw hfixM hnorm0
  exact toralNormalD_of_toral hm3 c htz hcι ⟨k₀, v, hk₀⟩

end Main


end CFSG.ClassicalInvolution.RouteD.Gaps
