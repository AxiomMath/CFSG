module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Defs
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.Q3.TL4VtxDich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTSetup

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.ClassicalInvolution.Disconnected.AschTight

section Vocab

variable {Y : Type} [Group Y]

@[expose] def lOrbit (L M : Subgroup Y) : Set (Subgroup Y) :=
  {N | ∃ l ∈ L, conjSub l M = N}

structure OrbitHyp (H : Type) [Group H] (M : Subgroup H) (z : H) : Prop where
  odd : classicalInvolutionOddCore H = ⊥
  two : NoNormalTwo H
  fstar : FStarSimple H
  cent : Subgroup.centralizer (genFittingFStar H : Set H) = ⊥
  hyp : TypeRHyp (CoreAssembly.conjClass M)
  gen : omegaGen (CoreAssembly.conjClass M) = ⊤
  aEmpty : AEmpty (CoreAssembly.conjClass M) M
  inv : IsUniqueInvolution M z

end Vocab

section Outcomes

@[expose] def OrbitLie (H : Type) [Group H] (M : Subgroup H) (z : H) : Prop :=
  ∃ (c : CompData) (_ : c.Valid) (_ : c ≠ CompData.sl23) (φ : c.G →* H),
    Function.Surjective φ ∧ φ.ker ≤ Subgroup.center c.G ∧
    ∃ F ∈ c.fund, M ≤ F.map φ ∧ Nat.card (F.map φ) = 24 ∧ IsClassicalMember3 (F.map φ) z

@[expose] def OrbitIdent (H : Type) [Group H] (M : Subgroup H) (z : H) : Prop :=
  OrbitLie H M z ∨
    (TightEdgeless M ∧ ¬ TightActs3 M z ∧ TL4.Thm6Exit H ∧
      (M.subgroupOf (Subgroup.centralizer ({z} : Set H))).Normal) ∨
    (TightEdgeless M ∧ Nonempty (H ≃* CFSG.Blueprint.NativeSporadic.Carrier .M12) ∧
      (M.subgroupOf (Subgroup.centralizer ({z} : Set H))).Normal) ∨
    ((CFSG.Blueprint.LieModel H .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel H .POmegaPlus 4 2 1) ∧
      ∃ M' ∈ twinSet (CoreAssembly.conjClass M) M, M' ≠ M)

end Outcomes

theorem lOrbit_stable {Y : Type} [Group Y] {L M N : Subgroup Y} (hL : L.Normal)
    (hN : N ∈ lOrbit L M) {n : Y} (hn : n ∈ N) {N' : Subgroup Y} (hN' : N' ∈ lOrbit L M) :
    conjSub n N' ∈ lOrbit L M := by
  obtain ⟨l, hl, rfl⟩ := hN
  obtain ⟨l', hl', rfl⟩ := hN'
  have hm : l⁻¹ * n * l ∈ M := (mem_conjSub_iff).mp hn
  refine ⟨l * ((l⁻¹ * n * l) * (l⁻¹ * l') * (l⁻¹ * n * l)⁻¹),
    L.mul_mem hl (hL.conj_mem _ (L.mul_mem (L.inv_mem hl) hl') _), ?_⟩
  have hx : l * ((l⁻¹ * n * l) * (l⁻¹ * l') * (l⁻¹ * n * l)⁻¹) * (l⁻¹ * n * l) = n * l' := by
    group
  calc conjSub (l * ((l⁻¹ * n * l) * (l⁻¹ * l') * (l⁻¹ * n * l)⁻¹)) M
      = conjSub (l * ((l⁻¹ * n * l) * (l⁻¹ * l') * (l⁻¹ * n * l)⁻¹))
          (conjSub (l⁻¹ * n * l) M) := by
        rw [conjSub_eq_self_of_mem hm]
    _ = conjSub (n * l') M := by rw [← conjSub_mul, hx]
    _ = conjSub n (conjSub l' M) := conjSub_mul _ _ _

section Group

variable {H : Type} [Group H] {M : Subgroup H} {z : H}

theorem normal_of_twinFree (h : OrbitHyp H M z)
    (htf : ∀ M' ∈ twinSet (CoreAssembly.conjClass M) M, M' = M) :
    (M.subgroupOf (Subgroup.centralizer ({z} : Set H))).Normal := by
  have hle : M ≤ Subgroup.centralizer ({z} : Set H) := le_centralizer_of_isUniqueInvolution h.inv
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc => ?_
  rw [mem_normalizer_iff_conjSub_eq]
  have hcz : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]; group
  have hU := h.inv.conj c
  rw [hcz] at hU
  exact htf _ ⟨⟨c, rfl⟩, z, h.inv, hU⟩

theorem center_eq_bot [Finite H] (h : OrbitHyp H M z) : Subgroup.center H = ⊥ :=
  h.two _ inferInstance (TL4.Vtx.isPGroup_two_of_le_center h.odd le_rfl)

end Group

section Ident

variable {H : Type} [Group H] [Finite H] {M : Subgroup H} {z : H}

theorem orbitLie_of_lieSystem (h : OrbitHyp H M z) {Λ : Subgroup H} (hMΛ : M ≤ Λ)
    (hΛ : IsClassicalMember3 Λ z) (hL : LieSystemMod3 (CoreAssembly.conjClass Λ)) :
    OrbitLie H M z := by
  classical
  obtain ⟨ι, _, ⟨D₀⟩⟩ := hL
  set L := genFittingFStar H with hLdef
  haveI : IsSimpleGroup ↥L := h.fstar.1
  haveI hLn : L.Normal := CFSG.ClassicalInvolution.genFittingFStar_normal H
  have hle : ∀ N : Subgroup H, N.Normal → N ≠ ⊥ → L ≤ N := by
    intro N hN hN1
    haveI := hN
    rcases (inferInstance : (N.subgroupOf L).Normal).eq_bot_or_eq_top with hb | ht
    · exfalso
      apply hN1
      rw [eq_bot_iff, ← h.cent]
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hc : n * l * n⁻¹ * l⁻¹ ∈ N ⊓ L := by
        refine ⟨?_, ?_⟩
        · have := hN.conj_mem n⁻¹ (N.inv_mem hn) l
          simpa [mul_assoc] using N.mul_mem hn (by simpa [mul_assoc] using this)
        · have := hLn.conj_mem l hl n
          exact L.mul_mem this (L.inv_mem hl)
      have hc' : (⟨_, hc.2⟩ : L) ∈ N.subgroupOf L := hc.1
      rw [hb, Subgroup.mem_bot] at hc'
      have h1 : n * l * n⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hc'
      have h2 : n * l = l * n := by
        calc n * l = (n * l * n⁻¹ * l⁻¹) * l * n := by group
          _ = l * n := by rw [h1, one_mul]
      exact h2.symm
    · intro l hl
      have : (⟨l, hl⟩ : L) ∈ N.subgroupOf L := by rw [ht]; trivial
      exact this
  let e : H ⧸ classicalInvolutionOddCore H ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq h.odd).trans QuotientGroup.quotientBot
  let D := D₀.congr e
  have hid : ∀ x : H, e (QuotientGroup.mk' (classicalInvolutionOddCore H) x) = x := fun x => rfl
  have hΛmem :
      Λ ∈ Subgroup.map e.toMonoidHom '' oddQuotientFamily (CoreAssembly.conjClass Λ) := by
    refine ⟨Λ.map (QuotientGroup.mk' _), ⟨Λ, CoreAssembly.mem_conjClass_self Λ, rfl⟩, ?_⟩
    rw [Subgroup.map_map]
    ext x
    simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, hid]
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨i₀, F, hF, hΛF⟩ := D.fundamental Λ hΛmem
  have h24 : Nat.card Λ = 24 := D.card_eq Λ hΛmem
  have hrange : ∀ i, L ≤ (D.hom i).range := by
    intro i
    refine hle _ (Q3W.range_normal3 D i) fun hb => ?_
    obtain ⟨R, -, hRm⟩ := D.meets i
    have h24' := D.card_eq _ hRm
    have hRb : R.map (D.hom i) = ⊥ := by
      rw [eq_bot_iff, ← hb]; exact Subgroup.map_le_range _ _
    rw [hRb, Subgroup.card_bot] at h24'
    norm_num at h24'
  have hone : ∀ i, i = i₀ := by
    intro i
    by_contra hne
    obtain ⟨a, b, hab⟩ := h.fstar.2
    apply hab
    have := Q3W.commutes_range3 D hne _ (hrange i a.2) _ (hrange i₀ b.2)
    exact Subtype.ext this
  have hsurj : Function.Surjective (D.hom i₀) :=
    MonoidHom.range_eq_top.mp (Q3CP.range_eq_top_of_forall_eq D hone)
  refine ⟨D.kind i₀, D.valid i₀, ?_, D.hom i₀, hsurj, D.ker_le_center i₀, F, hF, ?_, ?_, ?_⟩
  · intro hsl
    have hsol := isSolvable_range_of_sl23 hsl (D.hom i₀)
    rw [MonoidHom.range_eq_top.mpr hsurj] at hsol
    obtain ⟨a, b, hab⟩ := h.fstar.2
    have : Group.IsSolvable ↥L := by
      have : Group.IsSolvable H :=
        Group.isSolvable_of_surjective (f := (⊤ : Subgroup H).subtype)
          (fun x => ⟨⟨x, trivial⟩, rfl⟩)
      infer_instance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)
  · rw [← hΛF]; exact hMΛ
  · rw [← hΛF]; exact h24
  · rw [← hΛF]; exact hΛ

theorem orbitIdent_of_pkg {n : ℕ} (hA : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hH : Nat.card H < n) (h : OrbitHyp H M z) : OrbitIdent H M z := by
  classical
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥M))
  have hMΦ : M ∈ CoreAssembly.conjClass M := CoreAssembly.mem_conjClass_self M
  have hcore : tightCore M = M := tightCore_eq_self_of_typeRHyp h.hyp hMΦ
  have hq : Nonempty (↥(S : Subgroup M) ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := h.hyp.sylow M hMΦ _ (isSylow2In_map_subtype M S)
    exact ⟨((S : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective).trans e⟩
  have hd : QuaternionBridge.Q8TwinDatum M S z :=
    { quat := ⟨3, le_rfl, hq⟩
      mem := T3.mem_of_isPGroup h.inv (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
        (le_trans (by norm_num) (Sec6Gen.eight_le_of_mem_RSet h.hyp.hyp
          (mem_RSet_of_isSylow2In hMΦ (isSylow2In_map_subtype M S))))
      order := orderOf_eq_prime (by rw [pow_two]; exact h.inv.sq) h.inv.ne_one
      cent := le_centralizer_of_isUniqueInvolution h.inv
      twoGroup := h.hyp.twoGroup M hMΦ }
  have hsg : TightSelfGen M := by
    show (⨆ g : H, conjSub g (tightCore M)) = ⊤
    rw [hcore, eq_top_iff, ← h.gen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨g, rfl⟩ := hL
    exact le_iSup (fun g : H => conjSub g M) g
  have hcls : TightCls H M S z := ⟨hq, hsg, h.odd⟩
  have hnz : ¬ TightInO2 z := by
    rintro ⟨P, hPn, hP2, hzP⟩
    have hbot := h.two P hPn hP2
    rw [hbot, Subgroup.mem_bot] at hzP
    exact h.inv.ne_one hzP
  have hZ := center_eq_bot h
  by_cases htw : ∃ M' ∈ twinSet (CoreAssembly.conjClass (tightCore M)) (tightCore M),
      M' ≠ tightCore M
  ·
    have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore M)) := by
      rw [hcore]; exact h.hyp.hyp
    have hAE : AEmpty (CoreAssembly.conjClass (tightCore M)) (tightCore M) := by
      rw [hcore]; exact h.aEmpty
    rcases hP.twin rfl H hH M S z hd hq hsg h.odd hΩ hAE htw with h1 | h1 | h1
    · exact absurd h1 hnz
    · obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h1
      have hker : f.ker = ⊥ := h.two _ inferInstance hf2
      have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
      let e : H ≃* Q := MulEquiv.ofBijective f ⟨hinj, hfs⟩
      refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
      · rcases hQ with hQ | hQ
        · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hQ)
        · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hQ)
      · rw [hcore] at htw
        exact htw
    · obtain ⟨Λ, hMΛ, hΛ⟩ := PhilipHall.Frame.LongFundSetE3.hasLift h1 htw
      have hIn := TL4.inClass3_conjClass_of_lift hcls hMΛ hΛ
      exact Or.inl (orbitLie_of_lieSystem h (hcore ▸ hMΛ) hΛ (hA H hH _ hIn))
  ·
    have htf : ∀ M' ∈ twinSet (CoreAssembly.conjClass M) M, M' = M := by
      intro M' hM'
      by_contra hne
      exact htw ⟨M', hcore.symm ▸ hM', hcore.symm ▸ hne⟩
    have hn := normal_of_twinFree h htf
    have hdT : TightDatum M S z := hd.toTightDatum hn
    rcases TL4.secIdentDatum3_of hP hA H hH M S z hdT hcls with
      h1 | ⟨he, h3, hx | htwst⟩ | ⟨he, ⟨e⟩⟩ | ⟨hz, -⟩ | ⟨Λ, hMΛ, hΛ, -, hL⟩
    · exact absurd h1 hnz
    · exact Or.inr (Or.inl ⟨he, h3, hx, hn⟩)
    · exfalso
      obtain ⟨L, -, -, -, -, -, hFc, hFL⟩ := htwst
      rw [hZ] at hFc
      exact hFL (hFc.trans bot_le)
    · refine Or.inr (Or.inr (Or.inl ⟨he, ⟨?_⟩, hn⟩))
      exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
    · exact absurd hZ hz
    · exact Or.inl (orbitLie_of_lieSystem h (hcore ▸ hMΛ) hΛ hL)

theorem orbitIdent_of_stepIH {m : ℕ} (ih : StepIH m) (hH : Nat.card H ≤ m)
    (h : OrbitHyp H M z) : OrbitIdent H M z :=
  orbitIdent_of_pkg ih.cit ih.pkg (Nat.lt_succ_of_le hH) h

end Ident

section TwoOrbit

@[expose] def TwoOrbitModelS7 (G : Type) [Group G] : Prop :=
  (∃ (N : Subgroup G) (_ : N.Normal), N.index = 2 ∧ CFSG.Blueprint.LieModel ↥N .PSU 3 3 1 ∧
      Subgroup.centralizer (N : Set G) = ⊥) ∨
    CFSG.Blueprint.NativeSporadic.IsSporadic G .M12

end TwoOrbit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
