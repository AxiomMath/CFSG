module

public import CFSG.ClassicalInvolution.RouteD.GapsPatternDFinal
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}

omit [Finite G] in
theorem conjSub_conjSub_self {t : G} (h2t : t * t = 1) (L : Subgroup G) :
    conjSub t (conjSub t L) = L := by
  rw [← conjSub_mul, h2t, conjSub_one]

omit [Finite G] in
theorem conjSub_mem_centralizingMembers (hΩ : ConjInvariant Ω) {t : G} (htz : t * z * t⁻¹ = z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) :
    conjSub t L ∈ centralizingMembers Ω {z} := by
  have := centralizingMembers_conj hΩ t z
  rw [htz] at this
  rw [this]
  exact ⟨L, hL, rfl⟩

theorem conjSub_twin_eq (c : TCtx p f tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K) {T : Subgroup G}
    (hT : T ∈ centralizingMembers Ω {z}) (hTQ : locImg Ω z T ≤ c.d.Q₁) : conjSub t T = T := by
  by_contra hne
  have hΩ := c.hΩ.conjInvariant
  have hN₀z : conjSub t T ∈ centralizingMembers Ω {z} :=
    conjSub_mem_centralizingMembers hΩ htz hT
  have hTK : T ≠ K := by
    rintro rfl
    have h1 : Commutes (locImg Ω z T) (locImg Ω z T) :=
      fun a ha b hb => c.d.comm₀₁ a (c.hQ₀ ha) b (hTQ hb)
    exact not_commutes_self_of_mem c.hΩ hT.1 ((commutes_iff_locImg c.hΩ c.hP1 hT hT).mpr h1)
  have hN₀K : conjSub t T ≠ K := fun h => hTK (by
    have := congrArg (conjSub t) h
    rwa [conjSub_conjSub_self h2t, hKt] at this)
  have hall : ∀ L ∈ centralizingMembers Ω {z}, L ≠ conjSub t T → Commutes (conjSub t T) L := by
    intro L hL hLN
    have hL' : conjSub t L ∈ centralizingMembers Ω {z} :=
      conjSub_mem_centralizingMembers hΩ htz hL
    have hne' : conjSub t L ≠ T := fun h => hLN (by
      rw [← conjSub_conjSub_self h2t L, h])
    have h1 := (c.commutes_T_of_ne hT hTQ hL' hne').conjSub t
    rwa [conjSub_conjSub_self h2t] at h1
  have hN₀Q : ¬ locImg Ω z (conjSub t T) ≤ c.d.Q₁ := fun h =>
    hne (c.eq_of_locImg_le_Q₁ hN₀z hT h hTQ)
  obtain ⟨R₀, hR₀, hR₀eq⟩ := c.exists_fund_of_ne hN₀z hN₀K hN₀Q
  obtain ⟨R', hR', W, hW⟩ := c.hY.std R₀ hR₀
  obtain ⟨N', hN'z, -, -, hN'eq⟩ := c.exists_member_of_fund hR'
  have hnc : ¬ Commutes (conjSub t T) N' := fun h =>
    not_commutes_of_linearBlockStandardPair hW
      ((c.commutes_iff_fund hN₀z hN'z hR₀ hR₀eq hN'eq).mp h)
  have hN'N₀ : N' ≠ conjSub t T := fun h => ne_of_linearBlockStandardPair hW
    (eq_of_map_eq_of_perfect c.d.ψ c.d.ker_le (c.hY.perfR R₀ hR₀) (c.hY.perfR R' hR')
      (by rw [← hR₀eq, ← hN'eq, h]))
  exact hnc (hall N' hN'z hN'N₀)

theorem conjSub_layer_member (c : TCtx p f tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNQ : ¬ locImg Ω z N ≤ c.d.Q₁) :
    conjSub t N ∈ centralizingMembers Ω {z} ∧ conjSub t N ≠ K ∧
      ¬ locImg Ω z (conjSub t N) ≤ c.d.Q₁ := by
  have hΩ := c.hΩ.conjInvariant
  have hNz := conjSub_mem_centralizingMembers hΩ htz hN
  refine ⟨hNz, fun h => hNK ?_, fun h => ?_⟩
  · have := congrArg (conjSub t) h
    rwa [conjSub_conjSub_self h2t, hKt] at this
  · obtain ⟨T, hT, hTeq⟩ := c.exists_twin
    have hconj := conjSub_twin_eq c htz h2t hKt hT hTeq.le
    have h1 := c.eq_of_locImg_le_Q₁ hNz hT h hTeq.le
    apply hNQ
    have : N = T := by rw [← conjSub_conjSub_self h2t N, h1, hconj]
    rw [this, hTeq]

theorem locAut_mem_range (c : TCtx p f tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K)
    (hgen : c.d.ψ.range ≤ ⨆ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      R.map c.d.ψ) (k : (modelUniv tY nY p f Fact.out).K) :
    locAut c.hΩ.conjInvariant htz (c.d.ψ k) ∈ c.d.ψ.range := by
  have hS : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      (R.map c.d.ψ).map (locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    intro R hR
    obtain ⟨N, hNz, hNK, hNQ, hNeq⟩ := c.exists_member_of_fund hR
    obtain ⟨hN'z, hN'K, hN'Q⟩ := conjSub_layer_member c htz h2t hKt hNz hNK hNQ
    obtain ⟨R', -, hR'eq⟩ := c.exists_fund_of_ne hN'z hN'K hN'Q
    rw [← hNeq, locAut_locImg c.hΩ.conjInvariant htz, hR'eq]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hmap : c.d.ψ.range.map (locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hR => hS R hR
  exact hmap ⟨_, ⟨k, rfl⟩, rfl⟩

theorem range_le_iSup_fund_plus {m : ℕ} (hm : 4 ≤ m)
    (hadm : StatedLieAdmissible .POmegaPlus m p f) {X : Type} [Group X]
    (ψ : (modelUniv .POmegaPlus m p f Fact.out).K →* X) :
    ψ.range ≤ ⨆ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D,
      R.map ψ := by
  have hm3 : 3 ≤ m := by omega
  have hlong : ∀ γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots,
      IsLongestRoot (modelUniv .POmegaPlus m p f Fact.out).D γ := by
    rw [RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
    intro γ hγ
    exact RouteD.isLongestRoot_of_mem_roots_plusDatum hm3 hγ
  rw [← Balance.iSup_rankOneImage_eq_range .POmegaPlus m p f Fact.out trivial hadm ψ 1]
  refine iSup₂_le fun γ hγ => ?_
  exact le_iSup₂_of_le (Balance.rankOneRoot (modelUniv .POmegaPlus m p f Fact.out).D 1 γ)
    ⟨1, γ, Or.inl (hlong γ hγ), rfl⟩ le_rfl

section Wiring

omit [Finite G] in
theorem conjSub_map_equiv {A B : Type} [Group A] [Group B] (ι : A ≃* B) (k : A) (S : Subgroup A) :
    conjSub (ι k) (S.map ι.toMonoidHom) = (S.map (MulAut.conj k).toMonoidHom).map ι.toMonoidHom := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem charOf_comp_equiv {r m : ℕ} (e : Fin r ≃ Fin m) (v : Fin m → ZMod 2) (γ : Fin r → ℤ) :
    charOf (v ∘ e) γ = ∑ i, ((γ ∘ e.symm) i : ZMod 2) * v i := by
  unfold charOf
  rw [← Equiv.sum_comp e (fun j : Fin m => ((γ ∘ e.symm) j : ZMod 2) * v j)]
  simp

@[expose] def IsoCompatPlus {m : ℕ} (hm3 : 3 ≤ m)
    (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
    (ι : spinGroup (quadPlus m (GaloisField p f)) ≃*
      (modelUniv .POmegaPlus m p f Fact.out).K) : Prop :=
  ∀ γ : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → ℤ,
    (γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots ↔
      (γ ∘ e.symm) ∈ (plusDatum m (GaloisField p f) hm3).roots) ∧
    (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ =
      ((plusDatum m (GaloisField p f) hm3).rootGroup (γ ∘ e.symm)).map ι.toMonoidHom

theorem exists_isoCompatPlus {m : ℕ} (hm3 : 3 ≤ m) :
    ∃ (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
      (ι : spinGroup (quadPlus m (GaloisField p f)) ≃*
        (modelUniv .POmegaPlus m p f Fact.out).K), IsoCompatPlus hm3 e ι := by
  unfold IsoCompatPlus
  rw [RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
  exact ⟨Equiv.refl _, MulEquiv.refl _, fun γ => ⟨Iff.rfl, (Subgroup.map_id _).symm⟩⟩

@[expose] def TorusFixedD {m : ℕ} (hm3 : 3 ≤ m) (c : TCtx p f .POmegaPlus m Ω K z) {t : G}
    (htz : t * z * t⁻¹ = z) : Prop :=
  ∃ (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
    (ι : spinGroup (quadPlus m (GaloisField p f)) ≃* (modelUniv .POmegaPlus m p f Fact.out).K),
    IsoCompatPlus hm3 e ι ∧
    ∃ (i₀ i₁ : Fin m) (_ : i₀ ≠ i₁) (γ₀ : Fin m → ℤ) (s₀ t₀ : Bool)
      (_ : toStdD m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
      (k : spinGroup (quadPlus m (GaloisField p f)))
      (T : Subgroup (spinGroup (quadPlus m (GaloisField p f)))),
      (∀ y ∈ (((plusDatum m (GaloisField p f) hm3).rootGroup γ₀ ⊔
          (plusDatum m (GaloisField p f) hm3).rootGroup (-γ₀)).map (MulAut.conj k).toMonoidHom),
        locAut c.hΩ.conjInvariant htz (c.d.ψ (ι y)) = c.d.ψ (ι y)) ∧
      (∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ u : (GaloisField p f)ˣ,
        (plusFrame m (GaloisField p f) hm3).longTorus hij true false u ∈ T) ∧
      (∀ x ∈ T, locAut c.hΩ.conjInvariant htz (c.d.ψ (ι (k * x * k⁻¹))) =
        c.d.ψ (ι (k * x * k⁻¹)))

theorem toralNormalD_of_torusFixed {m : ℕ} (hm : 5 ≤ m) (hm3 : 3 ≤ m)
    (c : TCtx p f .POmegaPlus m Ω K z) {t : G} (htz : t * z * t⁻¹ = z) (h2t : t * t = 1)
    (hKt : conjSub t K = K) (hT : TorusFixedD hm3 c htz) : ToralNormalD c htz := by
  classical
  obtain ⟨e, ι, hc, i₀, i₁, h01, γ₀, s₀, t₀, hγ₀, k, T, H1, hTT, H2⟩ := hT
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hF : Nat.card (GaloisField p f) = p ^ f := c.card_eq
  have hq : 5 ≤ Nat.card (GaloisField p f) := by rw [hF]; exact c.hq
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf1, by show 4 ≤ m; omega⟩
  let θ : spinGroup (quadPlus m (GaloisField p f)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m (GaloisField p f))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have hσ2 : ∀ y, locAut c.hΩ.conjInvariant htz (locAut c.hΩ.conjInvariant htz y) = y :=
    locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr : ∀ k', locAut c.hΩ.conjInvariant htz (θ k') ∈ θ.range := by
    intro k'
    obtain ⟨x, hx⟩ := locAut_mem_range c htz h2t hKt (range_le_iSup_fund_plus (by omega) hadm c.d.ψ)
      (ι k')
    exact ⟨ι.symm x, by simpa [θ] using hx⟩
  obtain ⟨k₀, v', hk₀⟩ := ModelFacts.OrthAut.toralNormal_plus_of_subgroups c.hp2 hf1 hF hq hm hm3
    θ hker (locAut c.hΩ.conjInvariant htz) hσ2 hσr h01 hγ₀ k H1 T hTT H2
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
          (MulAut.conj k₀).toMonoidHom).map θ := by
    rw [hRG, Subgroup.map_map]
  rw [himg]
  refine ⟨hnorm, hfix.trans ?_⟩
  rw [charOf_comp_equiv]

theorem PartnerPatternD.of_torusFixed {m : ℕ} (hm : 7 ≤ m) (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : TorusFixedD (by omega : 3 ≤ m) c (partner_involution_commutes c.hp2 c.hz ht hKβ)) :
    PartnerPatternD p f m Ω K β t := by
  obtain ⟨W, hW⟩ := hKβ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact PartnerPatternD.of_toral_normal_plus hm hMFZ c hsingle hshape hβ ht ⟨W, hW⟩ hfixM
    (toralNormalD_of_torusFixed (by omega) (by omega) c _ h2t hKt hT)

end Wiring

end CFSG.ClassicalInvolution.RouteD.Gaps
