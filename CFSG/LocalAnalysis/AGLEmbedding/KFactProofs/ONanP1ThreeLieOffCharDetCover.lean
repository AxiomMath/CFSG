module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOutTower
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharNonNormal

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP

@[expose] def DetCoverAt (K : Type*) [Group K] (p : ℕ) : Prop :=
  ∃ D : Subgroup (MulAut K), (∀ α β : MulAut K, α * β * α⁻¹ * β⁻¹ ∈ D) ∧
    (∃ γ₀ : MulAut K, ∀ α : MulAut K, α ^ p = 1 → ∃ i : ℤ, α * γ₀ ^ i ∈ D) ∧
    (∀ δ ∈ D, δ ^ p = 1 → δ ∈ (MulAut.conj : K →* MulAut K).range) ∧
    ∀ P : Subgroup K, IsPGroup p P → ∀ δ ∈ D, ∃ k : K, ∀ x ∈ P, δ x = k * x * k⁻¹

theorem DetCoverAt.of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) {p : ℕ}
    (h : DetCoverAt L p) : DetCoverAt K p := by
  obtain ⟨D, hab, ⟨γ₀, hγ⟩, hDp, hcov⟩ := h
  refine ⟨D.comap (MulAut.congr e).toMonoidHom, fun α β => ?_,
    ⟨(MulAut.congr e).symm γ₀, fun α hα => ?_⟩, fun δ hδ hδp => ?_, fun P hP δ hδ => ?_⟩
  · change MulAut.congr e (α * β * α⁻¹ * β⁻¹) ∈ D
    simpa only [map_mul, map_inv] using hab (MulAut.congr e α) (MulAut.congr e β)
  · have hα' : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hα, map_one]
    obtain ⟨i, hi⟩ := hγ _ hα'
    refine ⟨i, ?_⟩
    change MulAut.congr e (α * ((MulAut.congr e).symm γ₀) ^ i) ∈ D
    rwa [map_mul, map_zpow, MulEquiv.apply_symm_apply]
  · have hδ' : (MulAut.congr e δ) ^ p = 1 := by rw [← map_pow, hδp, map_one]
    obtain ⟨g, hg⟩ := hDp _ hδ hδ'
    exact ⟨e.symm g, (eq_conj_of_congr_eq_conj e hg.symm).symm⟩
  · obtain ⟨l, hl⟩ := hcov (P.map e.toMonoidHom) (hP.map _) (MulAut.congr e δ) hδ
    refine ⟨e.symm l, fun x hx => ?_⟩
    have h1 := hl (e x) ⟨x, hx, rfl⟩
    have h3 : (MulAut.congr e δ) (e x) = e (δ x) := by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [h3] at h1
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

namespace ReducedNongeneration

theorem exists_cube_le {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X}
    {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀) :
    ∃ E ≤ (R : Subgroup X), IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨A, hAR, hA, hAcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p h.prime (R : Subgroup X)
  obtain ⟨C, hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 3)
    (hAcard ▸ pow_dvd_pow p h.three_le_pRank)
  have : IsMulCommutative A := hA.1
  have hC' : IsElemAbelian p C := ⟨inferInstance, fun x _ => Subtype.ext (hA.2 x x.property)⟩
  refine ⟨C.map A.subtype, (Subgroup.map_subtype_le C).trans hAR,
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hC' A.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hC]

theorem false_of_detCover {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X}
    {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀) {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (hKX : K ≤ X₀) (hT : DetCoverAt K p) :
    False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp : p.Prime := h.prime
  obtain ⟨D, hab, ⟨γ₀, hγ⟩, hDp, hcov⟩ := hT
  have hinj := conjNormal_injective (K := K) hC
  set ρ : X →* MulAut K := MulAut.conjNormal with hρ
  have hDn : D.Normal := ⟨fun δ hδ α => by
    have e : α * δ * α⁻¹ = (α * δ * α⁻¹ * δ⁻¹) * δ := by group
    rw [e]
    exact D.mul_mem (hab α δ) hδ⟩
  obtain ⟨E, hER, hEa, hEc⟩ := h.exists_cube_le
  set π := QuotientGroup.mk' D with hπ
  set ψ : E →* MulAut K ⧸ D := π.comp (ρ.comp E.subtype) with hψ
  have hρp : ∀ x ∈ E, (ρ x) ^ p = 1 := fun x hx => by rw [← map_pow, hEa.2 x hx, map_one]
  have hrange : ψ.range ≤ Subgroup.zpowers (π γ₀) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := hγ (ρ x) (hρp x x.2)
    have h1 : π (ρ x) * π γ₀ ^ i = 1 := by
      rw [← map_zpow, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).2 hi
    refine ⟨-i, ?_⟩
    change (π γ₀) ^ (-i) = π (ρ x)
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  have hcardr : Nat.card ψ.range ≤ p := by
    have : IsCyclic ψ.range := Subgroup.isCyclic_of_le hrange
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    refine Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one ?_)
    obtain ⟨x, hx⟩ := g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hx, ← map_pow]
    have : x ^ p = 1 := Subtype.ext (hEa.2 x x.2)
    rw [this, map_one]
    rfl
  have hker : ∀ x : E, ψ x = 1 → (x : X) ∈ K := by
    intro x hx
    have hxD : ρ x ∈ D := (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨k, hk⟩ := hDp _ hxD (hρp x x.2)
    have hρk : ρ (k : X) = MulAut.conj k := by
      ext y
      rw [hρ, MulAut.conjNormal_apply, MulAut.conj_apply]
      rfl
    have hxk : (k : X) = x := hinj (hρk.trans hk)
    rw [← hxk]
    exact k.2
  have hEK : p ^ 2 ≤ Nat.card (E ⊓ K : Subgroup X) := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card ψ.ker ≤ Nat.card (E ⊓ K : Subgroup X) := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨((x : E) : X), (x : E).2, hker x x.2⟩) fun a b hab' => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : (E ⊓ K : Subgroup X) => (z : X)) hab'
    have h3 : p ^ 2 * p ≤ Nat.card ψ.ker * p := by
      calc p ^ 2 * p = Nat.card E := by rw [hEc]; ring
        _ = Nat.card ψ.ker * Nat.card ψ.range := h1.symm
        _ ≤ Nat.card ψ.ker * p := Nat.mul_le_mul_left _ hcardr
    exact (Nat.le_of_mul_le_mul_right h3 hp.pos).trans h2
  set F := E ⊓ K with hF
  have hFa : IsElemAbelian p F := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hEa.2 x hx.1⟩
    have h1 := congrArg Subtype.val (hEa.1.is_comm.comm (⟨a, a.2.1⟩ : E) ⟨b, b.2.1⟩)
    exact h1
  have hEC : E ≤ Subgroup.centralizer (F : Set X) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun f hf =>
      congrArg Subtype.val (hEa.1.is_comm.comm (⟨f, hf.1⟩ : E) ⟨e, he⟩)
  have hNF : Subgroup.normalizer (F : Set X) ≤ X₀ := by
    refine le_trans ?_ h.weakCore_le
    refine CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p (inf_le_left.trans hER)
      (le_pRank_of_isElemAbelian_of_pow_le_card hp hFa le_rfl hEK) ?_
    exact le_pRank_of_isElemAbelian_of_pow_le_card hp hEa
      (le_sup_of_le_right (le_inf hER hEC)) (n := 3) (by rw [hEc])
  have hXD : D.comap ρ ≤ X₀ := by
    intro y hy
    have hPp : IsPGroup p (F.subgroupOf K) := fun g => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (Subtype.ext (hEa.2 _ (Subgroup.mem_subgroupOf.1 g.2).1))⟩
    obtain ⟨k, hk⟩ := hcov (F.subgroupOf K) hPp (ρ y) hy
    have hc : (k : X)⁻¹ * y ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 := congrArg Subtype.val (hk ⟨f, hf.2⟩ (Subgroup.mem_subgroupOf.2 hf))
      rw [hρ, MulAut.conjNormal_apply] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc f * ((k : X)⁻¹ * y) = (k : X)⁻¹ * (k * f * (k : X)⁻¹) * y := by group
        _ = (k : X)⁻¹ * (y * f * y⁻¹) * y := by rw [← h1]
        _ = (k : X)⁻¹ * y * f := by group
    have hy' : y = (k : X) * ((k : X)⁻¹ * y) := by group
    rw [hy']
    exact X₀.mul_mem (hKX k.2) (hNF (Subgroup.centralizer_le_normalizer _ hc))
  set M := D.comap ρ ⊔ (R : Subgroup X) with hM
  have hMn : M.Normal := ⟨fun m hm y => by
    have e : y * m * y⁻¹ = (y * m * y⁻¹ * m⁻¹) * m := by group
    rw [e]
    refine M.mul_mem (Subgroup.mem_sup_left ?_) hm
    change ρ (y * m * y⁻¹ * m⁻¹) ∈ D
    simpa only [map_mul, map_inv] using hab (ρ y) (ρ m)⟩
  have hMX : M ≤ X₀ := sup_le hXD
    ((CFSG.PreuniquenessRankFour.Helpers.subgroup_le_weakCore_of_rank p hp _
      h.three_le_pRank).trans h.weakCore_le)
  refine not_le_of_weakCore_le hp R h.weakCore_le h.ne_top ?_ hMX
  rw [inf_eq_left.2 (le_sup_right : (R : Subgroup X) ≤ M)]
  exact h.three_le_pRank

end ReducedNongeneration

theorem not_exists_cube_of_mulEquiv {Y : Type*} [Group Y] {K : Subgroup Y} {G : Type*} [Group G]
    (e : K ≃* G) {p : ℕ}
    (hnoK : ¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3) :
    ¬ ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  rintro ⟨E', hE', hc'⟩
  refine hnoK ⟨(E'.map e.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _,
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE' _) _, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective e.symm.injective, hc']

theorem p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover {d : TauCeti.ValidLieTypeIndex}
    (h : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ d.1.characteristic →
      (¬ ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E ∧
        Nat.card E = p ^ 3) →
      OutTowerAt (TauCeti.CFSGIndex.lie d).Group p ∨
        DetCoverAt (TauCeti.CFSGIndex.lie d).Group p) :
    P1OffCharAlmostSimpleNonNormalAt d := by
  intro p _ Y _ _ Rb Y₀ hR _ K hK huniq _ hC hnoK hKY hN hd hpd
  exfalso
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨e⟩ := nonempty_mulEquiv_of_centralizer_eq_bot hC (Classical.choice hd)
  rcases h p hR.ne_two hpd (not_exists_cube_of_mulEquiv e hnoK) with hT | hT
  · apply hN
    have := sup_sylow_normal_of_outTower hC (hT.of_mulEquiv e) Rb
    rw [Subgroup.normalCore_eq_self]
    exact le_sup_right
  · exact hR.false_of_detCover hC hKY (hT.of_mulEquiv e)

end CFSG.AGLEmbedding
