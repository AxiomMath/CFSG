module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigW

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

theorem exists_isKleinFour_mem {X : Subgroup G} (hX : 2 ≤ CFSG.Open.pRank 2 X) {b : G}
    (hbX : b ∈ X) (hb2 : orderOf b = 2) : ∃ F : Subgroup G, F ≤ X ∧ IsKleinFour F ∧ b ∈ F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hBX, hB, hB4, hbB⟩ := exists_elemAbelian_of_involution hX hbX hb2
  obtain ⟨a, haB, ha1, hab⟩ : ∃ a ∈ B, a ≠ 1 ∧ a ≠ b := by
    by_contra h
    push Not at h
    have hsub : (B : Set G) ⊆ {1, b} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have h2 : (B : Set G).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    have h3 : Nat.card B = (B : Set G).ncard := Nat.card_coe_set_eq _
    omega
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hB.2 a haB) ha1
  have hcomm : b * a = a * b :=
    congrArg Subtype.val (hB.1.is_comm.comm (⟨b, hbB⟩ : B) ⟨a, haB⟩)
  refine ⟨closure {b, a}, ?_, ?_, subset_closure (Set.mem_insert b _)⟩
  · rw [closure_le]
    rintro x (rfl | rfl)
    · exact hBX hbB
    · exact hBX haB
  · exact UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hb2 ha2 hcomm (Ne.symm hab)

theorem two_le_pRank_inf_centralizer (hK' : K' ∈ kStarComponents N) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hSQ : S ≤ coreActionKernel K') :
    2 ≤ CFSG.Open.pRank 2 (K' ⊓ centralizer (S : Set G)) :=
  (two_le_pRank_of_mem_solomonKStar hK'.2).trans
    (pRank_le_of_sup_oddCoreIn inf_le_left (inf_centralizer_sup_oddCoreIn_eq hS hSQ))

theorem oddCoreIn_le_centralizer_of_separated (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {e : G} (heK : e ∈ K) (he2 : orderOf e = 2) {F : Subgroup G}
    (hF : IsKleinFour F) (hFK' : F ≤ K') (hFe : F ≤ centralizer ({e} : Set G))
    (hsep : ∀ f ∈ F, f ≠ 1 →
      oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥)
    {v : G} (hv : v ∈ F) :
    oddCoreIn (centralizer ({e} : Set G)) ≤ centralizer ({v} : Set G) := by
  set Oe := oddCoreIn (centralizer ({e} : Set G)) with hOe
  by_cases hv1 : v = 1
  · rw [hv1, centralizer_singleton_one]
    exact le_top
  have hFOe : F ≤ normalizer (Oe : Set G) := hFe.trans (le_normalizer_oddCoreIn _)
  have hgen := le_iSup_inf_centralizer_of_isKleinFour hF hFOe (coprime_card_oddCoreIn _)
  refine hgen.trans (iSup₂_le fun f hf => iSup_le fun hf1 => ?_)
  set Cf := centralizer ({f} : Set G) with hCf
  set Y := Oe ⊓ Cf with hY
  have hFc := comm_of_isKleinFour hF
  have hf2 : orderOf f = 2 := orderOf_eq_two_of_isKleinFour hF hf hf1
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hF hv hv1
  have hzv : zpowers v ≤ F := zpowers_le.mpr hv
  have hzvf : zpowers v ≤ Cf :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hFc v hv f hf))
  have hzvY : zpowers v ≤ normalizer (Y : Set G) := by
    intro w hw
    rw [mem_normalizer_iff]
    intro y
    rw [hY, mem_inf, mem_inf, mem_normalizer_iff.mp (hFOe (hzv hw)),
      mem_normalizer_iff.mp (le_normalizer (hzvf hw))]
  have hYcop : Nat.Coprime 2 (Nat.card Y) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn _)
  have hYodd : Odd (Nat.card Y) := Nat.coprime_two_left.mp hYcop
  have hzv2 : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hYY : ⁅⁅Y, zpowers v⁆, zpowers v⁆ = ⁅Y, zpowers v⁆ :=
    CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hzv2 hYodd hzvY
  have hYV : ⁅Y, zpowers v⁆ ≤ Y :=
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y (zpowers v) hzvY
  have hfe : f * e = e * f := mem_centralizer_singleton_iff.mp (hFe hf)
  have hO : ⁅Y, zpowers v⁆ ≤ oddCoreIn Cf :=
    le_oddCoreIn_of_pump h32 hG hN hK hK' hne (hFK' hf) hf2 heK he2 hfe (hzv.trans hFK') hzvf
      (le_inf (hYV.trans inf_le_left) (hYV.trans inf_le_right)) (le_normalizer_commutator hzvY)
      hYY
  have hbot : ⁅Y, zpowers v⁆ = ⊥ := by
    rw [eq_bot_iff, ← hsep f hf hf1]
    intro x hx
    exact ⟨(hYV hx).1, hO hx⟩
  have hYc := commutator_eq_bot_iff_le_centralizer.mp hbot
  rwa [centralizer_zpowers_eq] at hYc

@[expose] def OddCoreSeparatedFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    ∀ e ∈ K, orderOf e = 2 → ∀ f ∈ K', orderOf f = 2 → f * e = e * f →
      oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥

theorem lemma315bInputFor_of_separated (h32 : Lemma32FullFor 𝒜)
    (hsep : OddCoreSeparatedFor 𝒜) : Lemma315bInputFor 𝒜 := by
  refine lemma315bInputFor_of_theta ?_
  intro G _ _ hG N hN K hK K' hK' hne B hBK hB _ V hV hVe hV1 e heB he1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he2 : orderOf e = 2 := orderOf_eq_prime (hB.2 e heB) he1
  have heK : e ∈ K := hBK heB
  have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
  have hBQ : B ≤ coreActionKernel K' := hBK.trans (le_coreActionKernel_of_ne hK' hK hne.symm)
  set C' := K' ⊓ centralizer (B : Set G) with hC'
  have hVC' : V ≤ C' := hV.trans (map_subtype_le _)
  have hC'e : C' ≤ centralizer ({e} : Set G) :=
    inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr heB))
  have hC'2 : 2 ≤ CFSG.Open.pRank 2 C' := two_le_pRank_inf_centralizer hK' hB2 hBQ
  have hsepe : ∀ f ∈ C', orderOf f = 2 →
      oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥ :=
    fun f hf hf2 => hsep G hG N hN K hK K' hK' hne e heK he2 f hf.1 hf2
      (mem_centralizer_singleton_iff.mp (hC'e hf))
  rw [theta_eq_bot_iff]
  constructor
  ·
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1, one_mul, mul_one]
    have hv2 : orderOf v = 2 := orderOf_eq_prime (hVe.2 v hv) hv1
    obtain ⟨F, hFC', hF, hvF⟩ := exists_isKleinFour_mem hC'2 (hVC' hv) hv2
    have h := oddCoreIn_le_centralizer_of_separated h32 hG hN hK hK' hne heK he2 hF
      (hFC'.trans inf_le_left) (hFC'.trans hC'e)
      (fun f hf hf1 => hsepe f (hFC' hf) (orderOf_eq_two_of_isKleinFour hF hf hf1)) hvF hx
    exact (mem_centralizer_singleton_iff.mp h).symm
  ·
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
      by_contra h
      push Not at h
      exact hV1 (eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h x hx))
    have hv2 : orderOf v = 2 := orderOf_eq_prime (hVe.2 v hv) hv1
    have hvK' : v ∈ K' := (hVC' hv).1
    have hVv : V ≤ centralizer ({v} : Set G) := fun w hw => mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hVe.1.is_comm.comm (⟨w, hw⟩ : V) ⟨v, hv⟩))
    have hzev : zpowers e ≤ centralizer ({v} : Set G) := zpowers_le.mpr
      (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hC'e (hVC' hv))).symm)
    have h := inf_inf_le_oddCoreIn h32 hG hN hK hK' hne hvK' hv2
      (zpowers_ne_bot_of_orderOf_eq_two he2)
      (isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two he2)) (zpowers_le.mpr heK) hzev hV1 hVe
      ((hVC'.trans inf_le_left).trans (le_coreActionKernel_of_ne hK hK' hne)) hVv
    rw [centralizer_zpowers_eq] at h
    rw [eq_bot_iff, ← hsepe v (hVC' hv) hv2]
    intro x hx
    have hxV : x ∈ centralizer (V : Set G) := map_subtype_le _ hx.2
    exact ⟨hx.1, h ⟨hx, centralizer_le (Set.singleton_subset_iff.mpr hv) hxV⟩⟩

end CFSG.ComponentClassification.Sol76.Sig
