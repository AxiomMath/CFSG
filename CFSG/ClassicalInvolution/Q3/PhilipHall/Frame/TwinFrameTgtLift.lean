module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecCent
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx

section Pullback

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]

theorem exists_classicalMember_of_oddQuot' (hNodd : Odd (Nat.card ↥N)) {t : H}
    (ht2 : t * t = 1) {L : Subgroup (H ⧸ N)}
    (hL : IsClassicalMember3 L (QuotientGroup.mk' N t)) {A : Subgroup H}
    (hAt : A ≤ Subgroup.centralizer ({t} : Set H)) (hAL : A.map (QuotientGroup.mk' N) ≤ L) :
    ∃ K : Subgroup H, IsClassicalMember3 K t ∧ A ≤ K := by
  classical
  set π : H →* H ⧸ N := QuotientGroup.mk' N with hπ
  set C : Subgroup H := Subgroup.centralizer ({t} : Set H) with hC
  set P : Subgroup H := L.comap π with hP
  set K : Subgroup H := P ⊓ C with hK
  have htP : t ∈ P := Subgroup.mem_comap.mpr hL.mem
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htK : t ∈ K := ⟨htP, htC⟩
  have hLC : L ≤ Subgroup.centralizer ({π t} : Set (H ⧸ N)) := isSubnormal_le' hL.subnormal
  have hCbar : Subgroup.centralizer ({π t} : Set (H ⧸ N)) = C.map π :=
    OddQ.centralizer_mk_eq hNodd ht2
  have hKL : ∀ k : K, π (k : H) ∈ L := fun k => Subgroup.mem_comap.mp k.2.1
  set f : ↥K →* ↥L := (π.comp K.subtype).codRestrict L hKL with hf
  have hfs : Function.Surjective f := by
    intro x
    have hx := hLC x.2
    rw [hCbar] at hx
    obtain ⟨c, hcC, hcx⟩ := hx
    have hcP : c ∈ P := Subgroup.mem_comap.mpr (by rw [hcx]; exact x.2)
    exact ⟨⟨c, hcP, hcC⟩, Subtype.ext hcx⟩
  have hfk : Odd (Nat.card f.ker) := by
    have hker : f.ker = N.subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
    rw [hker]
    have h1 : Nat.card (N.subgroupOf K) = Nat.card (N ⊓ K : Subgroup H) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]
    rw [h1]
    exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have ht2' : orderOf t = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact ht2) ?_
    intro h1
    have := hL.orderOf_eq_two
    rw [hπ, QuotientGroup.mk'_apply, h1, QuotientGroup.mk_one, orderOf_one] at this
    omega
  refine ⟨K, ⟨ht2', htK, ?_, ?_⟩, ?_⟩
  · have h1 := isSubnormal_comap' π hL.subnormal
    rw [hCbar] at h1
    have h2 := isSubnormal_inf h1 C
    have h3 : (C.map π).comap π ⊓ C = C := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact inf_eq_right.mpr le_sup_left
    rw [h3] at h2
    exact h2
  · obtain ⟨e⟩ := hL.nonempty_equiv
    exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv f hfs hfk).trans e⟩
  · intro a ha
    exact ⟨Subgroup.mem_comap.mpr (hAL (Subgroup.mem_map_of_mem _ ha)), hAt ha⟩

end Pullback

section Section

variable {Y : Type} [Group Y] [Finite Y] {C : Subgroup Y}

theorem exists_sectionMember_of_oddQuot' {H : Subgroup ↥C} (hH : IsSubnormal H ⊤) {t : ↥C}
    (ht : t ∈ H) (ht2 : t * t = 1) {L : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H)}
    (hL : IsClassicalMember3 L (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨t, ht⟩))
    {A : Subgroup ↥H} (hAt : A ≤ Subgroup.centralizer ({(⟨t, ht⟩ : ↥H)} : Set ↥H))
    (hAL : A.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) ≤ L) :
    ∃ K : Subgroup Y, Q3NL.IsSectionMember3 C K (t : Y) ∧
      (A.map H.subtype).map C.subtype ≤ K := by
  obtain ⟨K, hK, hAK⟩ := exists_classicalMember_of_oddQuot'
    (CFSG.ComponentClassification.OddCore.odd_card ↥H) (t := (⟨t, ht⟩ : H))
    (Subtype.ext ht2) hL hAt hAL
  have hKC := isClassicalMember3_map_subnormal hH hK
  exact ⟨_, TL4.isSectionMember3_map hKC,
    Subgroup.map_mono (Subgroup.map_mono hAK)⟩

end Section

section Dichotomy

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
@[expose] def Quiet (c t : Y) (htc : t ∈ Subgroup.centralizer ({c} : Set Y)) : Prop :=
  ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
    ∀ y ∈ L, oddQuotMk c ⟨t, htc⟩ * y = y * oddQuotMk c ⟨t, htc⟩

omit [Finite Y] in
@[expose] noncomputable def coreAt (R : Subgroup Y) (c : Y) : Subgroup Y :=
  (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).map
    (Subgroup.centralizer ({c} : Set Y)).subtype

omit [Finite Y] in
@[expose] def LiftedAt (R : Subgroup Y) (c t : Y) : Prop :=
  ∃ K : Subgroup Y, Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set Y)) K t ∧
    coreAt R c ≤ K

omit [Finite Y] in
theorem LiftedAt.classicalOrQuiet {R : Subgroup Y} {c t : Y} (h : LiftedAt R c t)
    (htc : t ∈ Subgroup.centralizer ({c} : Set Y)) : TL4.ClassicalOrQuiet c t htc :=
  Or.inl (by obtain ⟨K, hK, -⟩ := h; exact ⟨K, hK⟩)

omit [Finite Y] in
theorem Quiet.classicalOrQuiet {c t : Y} {htc : t ∈ Subgroup.centralizer ({c} : Set Y)}
    (h : Quiet c t htc) : TL4.ClassicalOrQuiet c t htc := Or.inr h

omit [Finite Y] in
theorem map_tightCore_le {X Z : Type} [Group X] [Group Z] (f : X →* Z) (R : Subgroup X) :
    (tightCore R).map f ≤ tightCore (R.map f) := by
  unfold tightCore
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxR, hx2⟩, rfl⟩
  refine ⟨⟨x, hxR, rfl⟩, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hx2.map _

variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem classicalOrQuiet_or_of_cent' {n : ℕ} (h : TwinCoreHyp n Y R S t)
    (hRc : tightCore R = R) (hZ : Subgroup.center Y = ⊥) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    (W : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c → Prop)
    (hex : ∀ (ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c)
      (Sb : Sylow 2 ↥(tightCore (secR R c))),
      (TightEx (SecQ R c) (tightCore (secR R c)) Sb
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) ⟨⟨t, htc⟩, ht⟩) ∨
        TwinE4 (SecQ R c)) →
      TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)) ∨ W ht)
    (hA : ∀ (ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c),
      AEmpty (CoreAssembly.conjClass (tightCore (secR R c))) (tightCore (secR R c)) ∨
        TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)) ∨ W ht) :
    Quiet c t htc ∨ LiftedAt R c t ∨ ∃ ht, W ht := by
  classical
  have hd := h.datum
  have hB2 : IsPGroup 2 ↥(Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hBR : Subgroup.zpowers c ≤ centralizerModOdd ⊤ R := Subgroup.zpowers_le.mpr hcm
  obtain ⟨S', hS'⟩ := exists_sylow_le_centralizer hd hB2 hBR
  have hdS := ofSylow hd S'
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({c} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := restrict hdS hS'u
  have hq8 : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) ≃*
      QuaternionGroup 2) :=
    ⟨e₁.trans ((Sylow.equiv S' S).trans h.q8.some)⟩
  obtain ⟨ht', S'', hdH, hgenH, hq8H⟩ := exists_sec hd₁ hq8
  set H := subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
    with hH
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hdq := oddQuot hdH hHodd
  have hgenq := oddQuot_selfGen (N := classicalInvolutionOddCore ↥H) hgenH
  obtain ⟨e⟩ := hq8H
  have hq8q := (sylowEquiv hdH hHodd).symm.trans e
  have hOq : TightOddFree (SecQ R c) := CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot
  obtain ⟨S₀, hdc, ⟨e₀⟩⟩ := toCore hdq
  have hidem := tightCore_idem (secR R c)
  have hgenc : TightSelfGen (tightCore (secR R c)) := by
    unfold TightSelfGen
    rw [hidem]
    exact hgenq
  have hq8c : Nonempty (↥(S₀ : Subgroup ↥(tightCore (secR R c))) ≃* QuaternionGroup 2) :=
    ⟨e₀.trans hq8q⟩
  have hΩ' := twinSecHyp_cent hd hRc h.hyp hc2 hc1 hcm
  rw [← hidem] at hΩ'
  have hlt : Nat.card (SecQ R c) < n := by
    have h1 : Nat.card (SecQ R c) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card ↥H ≤ Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) :=
      Subgroup.card_le_card_group H
    have h3 := card_centralizer_lt_of_center hZ hc1
    rw [← h.card]
    omega
  have hquiet : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨⟨t, htc⟩, ht'⟩ : H)) → Quiet c t htc ∨ LiftedAt R c t ∨ ∃ ht, W ht :=
    fun h2 => Or.inl (TL4.quiet_of_inO2_sub (isSubnormal_subnormalClosure _) ht' h2)
  have hlift : TightHasLift (tightCore (secR R c))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨⟨t, htc⟩, ht'⟩ : H)) →
        Quiet c t htc ∨ LiftedAt R c t ∨ ∃ ht, W ht := by
    rintro ⟨L, hLle, hL⟩
    rw [hidem] at hLle
    set Kc : Subgroup ↥(Subgroup.centralizer ({c} : Set Y)) :=
      tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) with hKc
    have hKcH : Kc ≤ H := le_subnormalClosure _
    set A : Subgroup ↥H := Kc.subgroupOf H with hAdef
    have hAt : A ≤ Subgroup.centralizer ({(⟨⟨t, htc⟩, ht'⟩ : ↥H)} : Set ↥H) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      have haK : (a : ↥(Subgroup.centralizer ({c} : Set Y))) ∈ Kc := ha
      have haR : ((a : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) ∈ R :=
        Subgroup.mem_subgroupOf.mp (tightCore_le _ haK)
      have := Subgroup.mem_centralizer_singleton_iff.mp (hd.cent haR)
      apply Subtype.ext
      apply Subtype.ext
      exact this
    have hAL : A.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) ≤ L := by
      refine le_trans ?_ hLle
      have h1 : tightCore ((R.subgroupOf (Subgroup.centralizer ({c} : Set Y))).subgroupOf H) =
          A := CFSG.ClassicalInvolution.Q3.tightCore_subgroupOf hKcH
      rw [← h1]
      exact map_tightCore_le _ _
    obtain ⟨K, hK, hAK⟩ := exists_sectionMember_of_oddQuot' (isSubnormal_subnormalClosure _) ht'
      (Subtype.ext (TwinEdge.t_mul_t hd)) hL hAt hAL
    refine Or.inr (Or.inl ⟨K, hK, ?_⟩)
    have h2 : A.map H.subtype = Kc := Subgroup.map_subgroupOf_eq_of_le hKcH
    rw [h2] at hAK
    exact hAK
  have hboth : (TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨⟨t, htc⟩, ht'⟩ : H)) ∨ W ht') → Quiet c t htc ∨ LiftedAt R c t ∨ ∃ ht, W ht :=
    fun h2 => h2.elim hquiet (fun h3 => Or.inr (Or.inr ⟨ht', h3⟩))
  rcases hA ht' with hAE | hA2
  swap
  · exact hboth hA2
  have hAE' := hAE
  rw [← hidem] at hAE'
  have hout := datumLift_of_IH h.twinBelow h.tbelow hlt hdc hq8c hgenc hOq hidem hΩ' hAE'
  by_cases htw : HasTwin (tightCore (secR R c))
  · rcases hout.1 htw with h2 | h2 | h2
    · exact hquiet h2
    · exact hboth (hex ht' S₀ (Or.inr h2))
    · exact hlift h2
  · rcases hout.2 htw with h2 | h2
    · exact hboth (hex ht' S₀ (Or.inl h2))
    · exact hlift h2

end Dichotomy

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
