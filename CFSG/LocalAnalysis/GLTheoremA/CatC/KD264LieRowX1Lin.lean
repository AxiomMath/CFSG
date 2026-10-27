module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Parts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.LieTwo
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def KD264X1LinCore : Prop :=
  ∀ (N : ℕ), 5 ≤ N → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ E : Subgroup (projectiveSL N K), IsElemAbelian 3 E →
      (∀ E' : Subgroup (projectiveSL N K), IsElemAbelian 3 E' →
        CFSG.Open.pRank 3 E' ≤ CFSG.Open.pRank 3 E) →
      ∃ F : Subgroup (projectiveSL N K), F ≤ E ∧ IsElemAbelian 3 F ∧
        Nat.card E = 3 * Nat.card F ∧
        ∃ L : Subgroup (projectiveSL N K),
          CFSG.Open.IsSubnormal L (Subgroup.centralizer (F : Set (projectiveSL N K))) ∧
          CFSG.Open.IsQuasisimple ↥L ∧ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem pRank_eq_of_card {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    {k : ℕ} (hk : Nat.card E = p ^ k) : CFSG.Open.pRank p E = k := by
  unfold CFSG.Open.pRank
  have hbdd : ∀ j ∈ {k : ℕ | ∃ E' : Subgroup G, E' ≤ E ∧ IsElemAbelian p E' ∧
      Nat.card E' = p ^ k}, j ≤ k := by
    rintro j ⟨E', hE'le, -, hcard⟩
    have hle : Nat.card E' ≤ Nat.card E := Subgroup.card_le_of_le hE'le
    rw [hcard, hk] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  apply le_antisymm
  · exact csSup_le' (fun j hj => hbdd j hj)
  · exact le_csSup ⟨k, fun j hj => hbdd j hj⟩ ⟨E, le_rfl, hE, hk⟩

theorem pRank_le_of_le {p : ℕ} (hp : p.Prime) {E H : Subgroup G} (h : E ≤ H) :
    CFSG.Open.pRank p E ≤ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  have hbdd : BddAbove {k : ℕ | ∃ E' : Subgroup G, E' ≤ H ∧ IsElemAbelian p E' ∧
      Nat.card E' = p ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro j ⟨E', -, -, hcard⟩
    have hlt : j < p ^ j := Nat.lt_pow_self hp.one_lt
    have hle : p ^ j ≤ Nat.card G := by
      rw [← hcard]
      exact Subgroup.card_le_card_group E'
    omega
  refine csSup_le' (fun j hj => ?_)
  obtain ⟨E', hE'le, hE', hcard⟩ := hj
  exact le_csSup hbdd ⟨E', hE'le.trans h, hE', hcard⟩

theorem exists_card_eq_pow {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E) :
    ∃ k : ℕ, Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    exact hE.2 g.1 g.2
  exact hP.exists_card_eq

theorem isElemAbelian_of_le {p : ℕ} {E E' : Subgroup G} (h : E' ≤ E) (hE : IsElemAbelian p E) :
    IsElemAbelian p E' := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hexp x (h hx)⟩
  have hc : a.1 * b.1 = b.1 * a.1 :=
    congrArg Subtype.val (hcomm.is_comm.comm (⟨a.1, h a.2⟩ : E) ⟨b.1, h b.2⟩)
  exact Subtype.ext hc

theorem center_eq_bot_of_simple_nonabelian {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) : Subgroup.center H = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center H := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha) b).symm

theorem centralizer_map_mulEquiv {H : Type*} [Group H] (e : G ≃* H) (F : Subgroup G) :
    (Subgroup.centralizer (F : Set G)).map (e : G →* H) =
      Subgroup.centralizer ((F.map (e : G →* H) : Subgroup H) : Set H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have := hx z hz
    simp only [← map_mul, this]
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := hy (e z) ⟨z, hz, rfl⟩
    apply e.injective
    simp only [map_mul]
    simpa using h1

theorem card_quotient_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (K : Subgroup A) :
    Nat.card (↥K ⧸ Subgroup.center ↥K) =
      Nat.card (↥(K.map (e : A →* B)) ⧸ Subgroup.center ↥(K.map (e : A →* B))) := by
  have hc := Subgroup.map_center_eq (MulEquiv.subgroupMap e K)
  exact Nat.card_congr (QuotientGroup.congr _ _ (MulEquiv.subgroupMap e K) hc).toEquiv

theorem isElemAbelian_of_map_injective {H : Type*} [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) {E : Subgroup G} (h : IsElemAbelian p (E.map f)) :
    IsElemAbelian p E := by
  obtain ⟨hcomm, hexp⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    have hc : f a.1 * f b.1 = f b.1 * f a.1 := by
      have := hcomm.is_comm.comm (⟨f a.1, Subgroup.mem_map_of_mem f a.2⟩ :
        ↥(E.map f)) ⟨f b.1, Subgroup.mem_map_of_mem f b.2⟩
      exact congrArg Subtype.val this
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hc
  · apply hf
    rw [map_pow, map_one]
    exact hexp (f x) (Subgroup.mem_map_of_mem f hx)

end Generic

theorem mulAut_pow_apply {S : Type*} [Group S] (f : MulAut S) (n : ℕ) (x : S) :
    (f ^ n) x = (⇑f)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

theorem linear_good_of_core (hcore : KD264X1LinCore) {S : Type} [Group S] [Finite S] {N : ℕ}
    (hN : 5 ≤ N) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (ψ : S ≃* projectiveSL N K) (hinner : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AutThreePowInner S)
    (A : Subgroup (MulAut S)) (hA : IsElemAbelian 3 A)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ CFSG.Open.pRank 3 A) :
    ∃ F' : Subgroup (MulAut S), F' ≤ A ∧ IsElemAbelian 3 F' ∧
      min 2 (CFSG.Open.pRank 3 A - 1) ≤ CFSG.Open.pRank 3 F' ∧ IsGood 3 F' := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI hsimp : IsSimpleGroup (projectiveSL N K) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isSimpleGroup_projectiveSL (by omega)
  have hZG : Subgroup.center (projectiveSL N K) = ⊥ :=
    center_eq_bot_of_simple_nonabelian
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_noncomm_projectiveSL (by omega))
  have hZS : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : ψ x ∈ Subgroup.center (projectiveSL N K) := by
      rw [← Subgroup.map_center_eq ψ]
      exact Subgroup.mem_map_of_mem (ψ : S →* projectiveSL N K) hx
    rw [hZG, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact ψ.injective (by rw [hx', map_one])
  let ρ : S →* MulAut S := MulAut.conj
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hc : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut S => φ g) hs
      simp only [ρ, MulAut.conj_apply, MulAut.one_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [hZS, Subgroup.mem_bot] at hc
    exact hc
  have hsurj : ∀ f ∈ A, ∃ s : S, ρ s = f := by
    intro f hf
    have hf3 : f ^ 3 = 1 := hA.2 f hf
    obtain ⟨a, ha⟩ := hinner f 1 (fun x => by
      have h1 := congrArg (fun φ : MulAut S => φ x) hf3
      simp only [MulAut.one_apply] at h1
      rw [mulAut_pow_apply] at h1
      exact h1)
    refine ⟨a, MulEquiv.ext fun x => ?_⟩
    show MulAut.conj a x = f x
    rw [MulAut.conj_apply]
    exact (ha x).symm
  let E : Subgroup S := A.comap ρ
  have hEmap : E.map ρ = A := by
    ext f
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_comap.1 hs
    · intro hf
      obtain ⟨s, rfl⟩ := hsurj f hf
      exact ⟨s, Subgroup.mem_comap.2 hf, rfl⟩
  have hEel : IsElemAbelian 3 E := isElemAbelian_of_map_injective ρ hρinj (by rw [hEmap]; exact hA)
  have hEcard : Nat.card E = Nat.card A := by
    have h1 := Subgroup.card_map_of_injective (K := E) hρinj
    rw [hEmap] at h1
    exact h1.symm
  obtain ⟨kA, hkA⟩ := exists_card_eq_pow hp hA
  have hpA : CFSG.Open.pRank 3 A = kA := pRank_eq_of_card hp hA hkA
  have hEGel : IsElemAbelian 3 (E.map (ψ : S →* projectiveSL N K)) :=
    isElemAbelian_of_map 3 ψ hEel
  have hEGcard : Nat.card (E.map (ψ : S →* projectiveSL N K)) = 3 ^ kA := by
    rw [Subgroup.card_map_of_injective ψ.injective, hEcard, hkA]
  have hpEG : CFSG.Open.pRank 3 (E.map (ψ : S →* projectiveSL N K)) = kA :=
    pRank_eq_of_card hp hEGel hEGcard
  have hmax : ∀ E' : Subgroup (projectiveSL N K), IsElemAbelian 3 E' →
      CFSG.Open.pRank 3 E' ≤ CFSG.Open.pRank 3 (E.map (ψ : S →* projectiveSL N K)) := by
    intro E' _
    have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL N K)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
      rw [← pRank_map_mulEquiv 3 ψ (⊤ : Subgroup S)]
      congr 1
      exact (Subgroup.map_top_of_surjective (ψ : S →* projectiveSL N K) ψ.surjective).symm
    calc CFSG.Open.pRank 3 E'
        ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL N K)) := pRank_le_of_le hp le_top
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup S) := htop
      _ ≤ CFSG.Open.pRank 3 A := hrank
      _ = kA := hpA
      _ = CFSG.Open.pRank 3 (E.map (ψ : S →* projectiveSL N K)) := hpEG.symm
  obtain ⟨FG, hFGle, hFGel, hFGcard, LG, hLsub, hLq, hLdvd⟩ :=
    hcore N hN K hK (E.map (ψ : S →* projectiveSL N K)) hEGel hmax
  have hψ'inj : Function.Injective (ψ.symm : projectiveSL N K →* S) := ψ.symm.injective
  have hFt_le : FG.map (ψ.symm : projectiveSL N K →* S) ≤ E := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hFGle hy)
    have h1 : ψ.symm y = z := by
      rw [← hzy]
      exact ψ.symm_apply_apply z
    show ψ.symm y ∈ E
    rw [h1]
    exact hz
  have hFt_card : Nat.card (FG.map (ψ.symm : projectiveSL N K →* S)) = Nat.card FG :=
    Subgroup.card_map_of_injective hψ'inj
  have hFA_le : (FG.map (ψ.symm : projectiveSL N K →* S)).map (MulAut.conj : S →* MulAut S) ≤ A := by
    calc (FG.map (ψ.symm : projectiveSL N K →* S)).map (MulAut.conj : S →* MulAut S)
        ≤ E.map (MulAut.conj : S →* MulAut S) := Subgroup.map_mono hFt_le
      _ = A := hEmap
  have hFA_el : IsElemAbelian 3
      ((FG.map (ψ.symm : projectiveSL N K →* S)).map (MulAut.conj : S →* MulAut S)) :=
    isElemAbelian_mono hA hFA_le
  have hFA_card : Nat.card ((FG.map (ψ.symm : projectiveSL N K →* S)).map
      (MulAut.conj : S →* MulAut S)) = Nat.card FG := by
    rw [Subgroup.card_map_of_injective hρinj, hFt_card]
  have hEG_card : Nat.card (E.map (ψ : S →* projectiveSL N K)) = Nat.card E :=
    Subgroup.card_map_of_injective ψ.injective
  have hcardA : Nat.card A = 3 * Nat.card FG := by
    rw [← hEcard, ← hEG_card, hFGcard]
  obtain ⟨k', rfl⟩ : ∃ k', kA = k' + 1 := by
    rcases kA with _ | k'
    · exfalso
      have h0 : Nat.card A = 1 := by rw [hkA]; rfl
      omega
    · exact ⟨k', rfl⟩
  have hFG_pow : Nat.card FG = 3 ^ k' := by
    have h3 : 3 * Nat.card FG = 3 * 3 ^ k' := by
      rw [← hcardA, hkA, pow_succ, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
  have hFA_pRank : CFSG.Open.pRank 3
      ((FG.map (ψ.symm : projectiveSL N K →* S)).map (MulAut.conj : S →* MulAut S)) = k' :=
    pRank_eq_of_card hp hFA_el (by rw [hFA_card, hFG_pow])
  have hLS_sub : CFSG.Open.IsSubnormal (LG.map (ψ.symm : projectiveSL N K →* S))
      ((Subgroup.centralizer (FG : Set (projectiveSL N K))).map
        (ψ.symm : projectiveSL N K →* S)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map ψ.symm hLsub
  rw [centralizer_map_mulEquiv ψ.symm FG, ← iInf_fixSubgroup_conj] at hLS_sub
  have hLS_q : CFSG.Open.IsQuasisimple ↥(LG.map (ψ.symm : projectiveSL N K →* S)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupMap ψ.symm LG) hLq
  have hLS_d : 3 ∣ Nat.card (↥(LG.map (ψ.symm : projectiveSL N K →* S)) ⧸
      Subgroup.center ↥(LG.map (ψ.symm : projectiveSL N K →* S))) := by
    rw [← card_quotient_center_mulEquiv ψ.symm LG]
    exact hLdvd
  have hgood : IsGood 3 ((FG.map (ψ.symm : projectiveSL N K →* S)).map
      (MulAut.conj : S →* MulAut S)) :=
    isGood_of_subnormal_quasisimple hp hLS_sub hLS_q hLS_d
  refine ⟨_, hFA_le, hFA_el, ?_, hgood⟩
  rw [hpA, hFA_pRank, Nat.add_sub_cancel]
  exact min_le_right _ _

theorem kd264X1LinPart_of_core (hcore : KD264X1LinCore) : KD264X1LinPart := by
  intro d n q hd inst
  obtain ⟨dd, hv⟩ := d
  dsimp only at hd
  subst hd
  unfold KD264X1At
  intro h1 h2 h3 h4 h5 h6
  unfold KD264X1Concl
  intro A hA hrank
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize] using h4
  have hn4 : 4 ≤ n := by
    have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hv
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
    have hdup := hvalid.2
    simp only [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    have hn1 : n ≠ 1 := fun h => by
      have := hr.2 h
      omega
    omega
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hFcard : Nat.card (GaloisField q.p q.exponent) = 2 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
    exact hq
  have hinner := CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeA_two hv hq
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group)
  let ψ := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      (n + 1) (GaloisField q.p q.exponent))
  exact linear_good_of_core hcore (N := n + 1) (by omega) hFcard ψ hinner A hA hrank

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end