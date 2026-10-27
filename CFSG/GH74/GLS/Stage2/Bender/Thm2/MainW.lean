module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs11d
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.KInftyFacts3
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Lemma111b
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IG512Proof
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Final
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P112CenU
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4W51
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Remark10Iw : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → ∀ H R : Subgroup G, T ≤ H → HOK k T U H → Fs H = Op p H →
      MaxIn {R' : Subgroup G | R0 k p T U H R'} R →
      H ≤ normalizer ((kInfty R : Subgroup G) : Set G) ∨
        (k = Kind.ly ∧ p = 3 ∧ IsDoubleCoverOfAlt ↥(layer (HBar H)) 11)

theorem remark_10I_C2_w (h51 : Signalizer.Ivk8.Prop5_1w') : Remark10I_C2 := by
  intro G _ _ z k S M p Q T U t g ctx hTO H R hTH hHOK hF hmax
  have hT5 : T5A z k S T (Iof U ⊔ T) := ctx.T5A hTO
  have hTI := ctx.T_le_normalizer_Iof hTO
  have hT2 := ctx.T_isPGroup
  have hkey : ∀ Q' : Subgroup G, T ≤ normalizer (Q' : Set G) →
      (Covers (H ⊓ normalizer (Q' : Set G)) (Iof U) (pPrimeCoreOf 2 (Iof U)) ↔
        Covers (H ⊓ normalizer (Q' : Set G)) (Iof U ⊔ T) (pPrimeCoreOf 2 (Iof U ⊔ T))) :=
    fun Q' hTQ => covers_iff_covers_sup hT2 hTI (le_inf hTH hTQ)
  obtain ⟨hRne, hRp, hRH, hTR, hRcov⟩ := hmax.1
  have hctx51 : Ctx51 k z S T (Iof U ⊔ T) p H R :=
    ⟨hT5, ctx.ctx9.prime, ctx.ctx9.odd, hTH, hF,
      ⟨⟨hRH, hRp, hTR, (hkey R hTR).mp (hRcov hTO)⟩, fun Q' hQ' hRQ' => ?_⟩⟩
  · rcases h51 G z k S ctx.ctx9.ctx T (Iof U ⊔ T) p H R hctx51 with h | ⟨hk, -, -⟩
    · exact h
    · exfalso
      have hcl := Stage2Ctx.isClassicalKind_of_not_typeOneCase ctx.ctx9.ctx hTO
      rcases hcl with hc | ⟨ε, hc⟩ <;> simp [hc] at hk
  · have hne : Q' ≠ ⊥ := fun hb => hRne (le_bot_iff.mp (hb ▸ hRQ'))
    have hQ'0 : R0 k p T U H Q' :=
      ⟨hne, hQ'.2.1, hQ'.1, hQ'.2.2.1, fun _ => (hkey Q' hQ'.2.2.1).mpr hQ'.2.2.2⟩
    exact hmax.2 Q' hQ'0 hRQ'

theorem remark_10I_w (h51 : Signalizer.Ivk8.Prop5_1w') : Remark10Iw := by
  intro G _ _ z k S M p Q T U t g ctx H R hTH hHOK hF hmax
  by_cases hTO : TypeOneCase G k
  · have hTS : T = S := (ctx.choice.T_one hTO).1
    have hcov : ∀ Q' : Subgroup G, T ≤ normalizer (Q' : Set G) →
        Covers (H ⊓ normalizer (Q' : Set G)) T (pPrimeCoreOf 2 T) := fun Q' hTQ =>
      le_sup_of_le_left (le_inf (le_inf hTH hTQ) le_rfl)
    have hctx51 : Ctx51 k z S T T p H R :=
      ⟨Or.inl ⟨hTO, hTS, hTS⟩, ctx.ctx9.prime, ctx.ctx9.odd, hTH, hF,
        ⟨⟨hmax.1.2.2.1, hmax.1.2.1, hmax.1.2.2.2.1, hcov R hmax.1.2.2.2.1⟩, fun Q' hQ' hRQ' => ?_⟩⟩
    · rcases h51 G z k S ctx.ctx9.ctx T T p H R hctx51 with h | ⟨hk, hp, hH⟩
      · exact Or.inl h
      · exact Or.inr ⟨hk, hp, hH⟩
    · have hne : Q' ≠ ⊥ := fun hb => hmax.1.1 (le_bot_iff.mp (hb ▸ hRQ'))
      have hQ'0 : R0 k p T U H Q' :=
        ⟨hne, hQ'.2.1, hQ'.1, hQ'.2.2.1, fun hn => absurd hTO hn⟩
      exact hmax.2 Q' hQ'0 hRQ'
  · exact Or.inl (remark_10I_C2_w h51 G z k S M p Q T U t g ctx hTO H R hTH hHOK hF hmax)

section Triple

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {Q T U : Subgroup G} {t g : G}

theorem prop_10_3_w (hk : KInfty_facts) (h101 : Prop10_1) (h102 : Lemma10_2) (h10I : Remark10Iw) :
    Prop10_3 := by
  intro G _ _ z k S M p Q T U t g ctx
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hall, hnLy⟩ := hcon
  have hex : ∃ R, Rp z k p T U Q M R ∧ ¬ normalizer ((kInfty R : Subgroup G) : Set G) ≤ M := by
    by_contra hne
    exact hall (fun R hR => by by_contra hc; exact hne ⟨R, hR, hc⟩)
  obtain ⟨R₁, hR₁, hnot₁⟩ := hex
  have hp := ctx.ctx9.prime
  let 𝒯 : Set (Subgroup G × Subgroup G × Subgroup G) := {τ |
    Rp z k p T U Q M τ.1 ∧ ¬ normalizer ((kInfty τ.1 : Subgroup G) : Set G) ≤ M ∧ IsCoatom τ.2.1 ∧
    normalizer ((kInfty τ.1 : Subgroup G) : Set G) ≤ τ.2.1 ∧
    MaxIn {V' : Subgroup G | R0 k p T U (M ⊓ τ.2.1) V'} τ.2.2 ∧
    τ.1 ⊔ (Op p M ⊓ normalizer ((kInfty τ.1 : Subgroup G) : Set G)) ≤ τ.2.2 ∧ Rp z k p T U Q M τ.2.2}
  obtain ⟨N₁, V₁, hN₁, hN₁le, hV₁max, hRsV₁, hV₁Rp⟩ := exists_NV hk ctx hR₁
  have h𝒯ne : (R₁, N₁, V₁) ∈ 𝒯 := ⟨hR₁, hnot₁, hN₁, hN₁le, hV₁max, hRsV₁, hV₁Rp⟩
  obtain ⟨τ₁, hτ₁, hmax₁⟩ := Set.exists_max_image 𝒯 (fun τ => Nat.card ↥τ.2.2) 𝒯.toFinite ⟨_, h𝒯ne⟩
  obtain ⟨⟨R, N, V⟩, ⟨hτ, hτcard⟩, hmax₂⟩ := Set.exists_max_image
    {τ : Subgroup G × Subgroup G × Subgroup G | τ ∈ 𝒯 ∧ Nat.card ↥τ.2.2 = Nat.card ↥τ₁.2.2}
    (fun τ => Nat.card ↥τ.1) (Set.toFinite _) ⟨τ₁, hτ₁, rfl⟩
  obtain ⟨hR, hnot, hN, hNle, hVmax, hRsV, hVRp⟩ := hτ
  have hA : ∀ τ' ∈ 𝒯, Nat.card ↥τ'.2.2 ≤ Nat.card ↥V := fun τ' h' => (hmax₁ τ' h').trans hτcard.ge
  have hB : ∀ τ' ∈ 𝒯, Nat.card ↥τ'.2.2 = Nat.card ↥V → Nat.card ↥τ'.1 ≤ Nat.card ↥R :=
    fun τ' h' heq => hmax₂ τ' ⟨h', heq.trans hτcard⟩
  have hRp : IsPGroup p ↥R := hR.1.2.1
  have hRM : R ≤ M := hR.1.2.2.1
  have hTR : T ≤ normalizer (R : Set G) := hR.1.2.2.2.1
  have hNR : normalizer (R : Set G) ≤ normalizer ((kInfty R : Subgroup G) : Set G) := normalizer_le_kInfty R
  have hTN : T ≤ N := fun x hx => hNle (hNR (hTR hx))
  have hNRN : normalizer (R : Set G) ≤ N := hNR.trans hNle
  have hRV : R ≤ V := le_sup_left.trans hRsV
  have hMne : M ≠ ⊤ := ctx.ctx9.coatom.1
  have hR₀ne : kInfty R ≠ ⊥ := kInfty_ne_bot hk hp hRp hR.1.1
  have hR₀R : kInfty R ≤ R := (hk G p hp R hRp).1
  have hNtop : normalizer ((kInfty R : Subgroup G) : Set G) ≠ ⊤ :=
    normalizer_ne_top ctx.ctx9.simple hMne (hR₀R.trans hRM) hR₀ne
  have hHOKM : HOK k T U M := ⟨fun x hx => Subgroup.le_normalizer (ctx.T_le_M hx), Cov10.mono inf_le_left hR.1.2.2.2.2⟩
  have hHOKMN : HOK k T U (M ⊓ N) :=
    ⟨fun x hx => mem_normalizer_inf (Subgroup.le_normalizer (ctx.T_le_M hx)) (Subgroup.le_normalizer (hTN hx)),
      Cov10.mono inf_le_left hVmax.1.2.2.2.2⟩
  have hHOKN : HOK k T U N :=
    ⟨fun x hx => Subgroup.le_normalizer (hTN hx), Cov10.mono (inf_le_left.trans inf_le_right) hVmax.1.2.2.2.2⟩
  have hMtop' : M ≠ ⊤ := hMne
  have hNne : N ≠ ⊤ := hN.1
  rcases eq_or_lt_of_le hRV with hRVeq | hRVlt
  ·
    have hRmax : MaxIn {V' : Subgroup G | R0 k p T U (M ⊓ N) V'} R := by
      rw [hRVeq]
      exact hVmax
    have hb1 := ((h102 G z k S M p Q T U t g ctx (M ⊓ N) (M ⊓ N) (fun h => hNne (top_le_iff.mp (h ▸ inf_le_right)))
      (fun h => hNne (top_le_iff.mp (h ▸ inf_le_right))) hHOKMN hHOKMN).2.1 R hRmax.1).2.mp hRmax
    have heq : (M ⊓ N) ⊓ normalizer (R : Set G) = M ⊓ normalizer (R : Set G) := by
      rw [inf_assoc, inf_eq_right.mpr hNRN]
    rw [heq] at hb1
    have hMmax := ((h102 G z k S M p Q T U t g ctx M M hMne hMne hHOKM hHOKM).2.1 R hR.1).2.mpr hb1
    rcases h10I G z k S M p Q T U t g ctx M R ctx.T_le_M hHOKM ctx.ctx9.fstar hMmax with hn | ⟨hky, hp3, -⟩
    · by_cases hEq : M = normalizer ((kInfty R : Subgroup G) : Set G)
      · exact hnot hEq.ge
      · exact hNtop (ctx.ctx9.coatom.2 _ (lt_of_le_of_ne hn hEq))
    · exact hnLy ⟨hp3, hky⟩
  ·
    have hVp : IsPGroup p ↥V := hVRp.1.2.1
    have hVM : normalizer ((kInfty V : Subgroup G) : Set G) ≤ M := by
      by_contra hnotV
      obtain ⟨N', V', hN', hN'le, hV'max, hVsV', hV'Rp⟩ := exists_NV hk ctx hVRp
      have hτ' : (V, N', V') ∈ 𝒯 := ⟨hVRp, hnotV, hN', hN'le, hV'max, hVsV', hV'Rp⟩
      have h1 := hA _ hτ'
      have h2 : Nat.card ↥V ≤ Nat.card ↥V' := Subgroup.card_le_of_le (le_sup_left.trans hVsV')
      have h3 := hB _ hτ' (le_antisymm h1 h2)
      exact absurd (Subgroup.eq_of_le_of_card_ge hRV h3) hRVlt.ne
    have hNVM : normalizer (V : Set G) ≤ M := (normalizer_le_kInfty V).trans hVM
    have hVN : R0 k p T U N V := R0_mono inf_le_right hVmax.1
    have hFN : Fs N = Op p N := by
      refine h101 G z k S M p Q T U t g ctx R N hR.1.1 hRp hRM hTR ?_ hN (inf_le_right.trans hNRN) hTN
      intro hle
      apply hR.2
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hle.trans (cen_le_centralizer_zpowers z)
    have hb1 := ((h102 G z k S M p Q T U t g ctx (M ⊓ N) (M ⊓ N) (fun h => hNne (top_le_iff.mp (h ▸ inf_le_right)))
      (fun h => hNne (top_le_iff.mp (h ▸ inf_le_right))) hHOKMN hHOKMN).2.1 V hVmax.1).2.mp hVmax
    have heq2 : (M ⊓ N) ⊓ normalizer (V : Set G) = N ⊓ normalizer (V : Set G) :=
      le_antisymm (inf_le_inf_right _ inf_le_right)
        (le_inf (le_inf (inf_le_right.trans hNVM) inf_le_left) inf_le_right)
    rw [heq2] at hb1
    have hNmax := ((h102 G z k S M p Q T U t g ctx N N hNne hNne hHOKN hHOKN).2.1 V hVN).2.mpr hb1
    rcases h10I G z k S M p Q T U t g ctx N V hTN hHOKN hFN hNmax with hn | ⟨hky, hp3, -⟩
    · exact hnot (hNle.trans (hn.trans hVM))
    · exact hnLy ⟨hp3, hky⟩

theorem prop_10_4_w (h103 : Prop10_3) (h102 : Lemma10_2) (h10I : Remark10Iw) :
    Prop10_4 := by
  intro G _ _ z k S M p Q T U t g ctx N R₁ hN hR₁ hR₁N hTN hR₁N0 hFN hnQ₁
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnM, hnLy⟩ := hcon
  have hp := ctx.ctx9.prime
  have hall : ∀ R : Subgroup G, Rp z k p T U Q M R → normalizer ((kInfty R : Subgroup G) : Set G) ≤ M := by
    rcases h103 G z k S M p Q T U t g ctx with h | h
    · exact h
    · exact absurd h hnLy
  have hNne : N ≠ ⊤ := hN.1
  let 𝒞 : Set (Subgroup G) := {R | Rp z k p T U Q M R ∧ R ≤ N ∧ R0 k p T U N R ∧ ¬ Q ⊓ R ≤ Cen z}
  obtain ⟨R, hR, hmax⟩ := Set.exists_max_image 𝒞 (fun R => Nat.card ↥R) (Set.toFinite _)
    ⟨R₁, hR₁, hR₁N, hR₁N0, hnQ₁⟩
  obtain ⟨hRp, hRN, hRN0, hnQ⟩ := hR
  have hRpg : IsPGroup p ↥R := hRp.1.2.1
  have hHOKN : HOK k T U N := ⟨fun x hx => Subgroup.le_normalizer (hTN hx), Cov10.mono (inf_le_left) hRN0.2.2.2.2⟩
  have hNRle : normalizer (R : Set G) ≤ M := (normalizer_le_kInfty R).trans (hall R hRp)
  have hHOKNR : HOK k T U (N ⊓ normalizer (R : Set G)) :=
    ⟨fun x hx => mem_normalizer_inf (Subgroup.le_normalizer (hTN hx)) (Subgroup.le_normalizer (hRN0.2.2.2.1 hx)),
      by simpa [inf_assoc] using hRN0.2.2.2.2⟩
  have hR1 := ((h102 G z k S M p Q T U t g ctx N N hNne hNne hHOKN hHOKN).2.1 R hRN0).1
  obtain ⟨V, hVmax, hRV⟩ := exists_maxIn_above
    (𝒮 := {V' : Subgroup G | R0 k p T U (N ⊓ normalizer (R : Set G)) V'}) hR1
  have hVN0 : R0 k p T U N V := R0_mono inf_le_left hVmax.1
  have hVM0 : R0 k p T U M V := R0_mono (inf_le_right.trans hNRle) hVmax.1
  · have hQR : Q ⊓ R ≤ Q ⊓ normalizer (V : Set G) := inf_le_inf_left Q (hRV.trans Subgroup.le_normalizer)
    have hVRp : Rp z k p T U Q M V := by
      refine ⟨hVM0, fun hb => hnQ ?_⟩
      have h1 : ⁅Q ⊓ R, zpowers z⁆ ≤ ⁅Q ⊓ normalizer (V : Set G), zpowers z⁆ := Subgroup.commutator_mono hQR le_rfl
      rw [hb, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
      exact h1.trans (centralizer_zpowers_le z)
    have hVC : V ∈ 𝒞 := ⟨hVRp, hVN0.2.2.1, hVN0, fun hle => hnQ (inf_le_inf_left Q hRV |>.trans hle)⟩
    have hVR : V = R := (Subgroup.eq_of_le_of_card_ge hRV (hmax V hVC)).symm
    rw [hVR] at hVmax
    have hRmaxN := ((h102 G z k S M p Q T U t g ctx N N hNne hNne hHOKN hHOKN).2.1 R hRN0).2.mpr hVmax
    rcases h10I G z k S M p Q T U t g ctx N R hTN hHOKN hFN hRmaxN with hn | ⟨hky, hp3, -⟩
    · have hle : N ≤ M := hn.trans (hall R hRp)
      by_cases hEq : N = M
      · exact hnM hEq
      · exact ctx.ctx9.coatom.1 (hN.2 M (lt_of_le_of_ne hle hEq))
    · exact hnLy ⟨hp3, hky⟩

end Triple

theorem thm2_false_core_w
    (hqp : QP_exists) (hch : Choice10_exists) (h111 : Prop11_1) (h112 : Prop11_2)
    (h48 : L48.Lemma4_8w) (hOdd : Gap56.OddCoreThreeLy) :
    Thm2False := by
  intro G _ _ z k S ctx hodd hpp
  have hyp := hyp9A_of_odd ctx hodd hpp
  obtain ⟨M, hM⟩ := exists_mem_maximalOverCentralizer ctx
  obtain ⟨p, hp, hp2, hF⟩ := hyp M hM
  have ctx9 : Ctx9 G z k S M p := ⟨ctx, hyp, hM, hp, hp2, hF⟩
  obtain ⟨Q, hQ⟩ := hqp G z p (Op p M) hp hp2 ctx.orderOf_z (op_isPGroup M)
    (le_normalizer_Op' p M ctx9.z_mem) (not_Op_le_Cen ctx ctx9.z_mem hp hp2 hF)
  obtain ⟨T, U, t, g, hchoice⟩ := hch G z k S M p ctx9
  have ctx10 : Ctx10 G z k S M p Q T U t g := ⟨ctx9, hQ, hchoice⟩
  have hone : TypeOneCase G k := by
    by_contra hn
    apply h111 G z k S M p Q T U t g ctx10
    rw [(hchoice.T_two hn).1]
    exact inf_le_right
  obtain ⟨-, hp3, hky⟩ := h112 G z k S M p Q T U t g ctx10 hone
  exact Gap56.prop_12_3_of_oddCoreThree h48 hOdd G z k S M p Q T U t g ctx10 ⟨hky, hp3⟩

theorem thm2_false_w
    (hqp : QP_exists) (h47 : Prop4_7cS) (h51 : Signalizer.Ivk8.Prop5_1w') (h48 : L48.Lemma4_8w)
    (h34 : Leaf_Prop34) (h915 : Lemma9_15) (hOdd : Gap56.OddCoreThreeLy) :
    Thm2False := by
  have h101 := prop_10_1 (prop_9_14c_of h915) (prop_9_27 ig_5_12_thm) h47
  have h102 := lemma_10_2 lemma10_2b_C2_thm
  have h10I := remark_10I_w h51
  have h103 := prop_10_3_w kInfty_facts_thm h101 h102 h10I
  have h104 := prop_10_4_w h103 h102 h10I
  exact thm2_false_core_w hqp (choice10_exists_of h34) (prop_11_1 h104 lemma11_1_star_thm)
    (prop_11_2 h103 h48) h48 hOdd

end CFSG.GH74.GLS.Stage2.Bender.Thm2
