module

public import CFSG.Goldschmidt75.Sig3Four
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoprime
public import CFSG.Goldschmidt75.Sig32Core
public import CFSG.Goldschmidt75.Sig3Trans

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_commutator_left (H A : Subgroup G) :
    H ≤ normalizer ((⁅H, A⁆ : Subgroup G) : Set G) := by
  have key : ∀ h ∈ H, ∀ n ∈ ⁅H, A⁆, h * n * h⁻¹ ∈ ⁅H, A⁆ := by
    intro h hh n hn
    have hle : ⁅H, A⁆ ≤ ⁅H, A⁆.comap (MulAut.conj h).toMonoidHom := by
      rw [commutator_le]
      intro h₀ hh₀ a ha
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : h * ⁅h₀, a⁆ * h⁻¹ = ⁅h * h₀, a⁆ * ⁅h, a⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (commutator_mem_commutator (mul_mem hh hh₀) ha)
        (inv_mem (commutator_mem_commutator hh ha))
    exact hle hn
  intro h hh
  rw [mem_normalizer_iff]
  intro n
  refine ⟨key h hh n, fun hn => ?_⟩
  have h1 := key h⁻¹ (inv_mem hh) _ hn
  have e : h⁻¹ * (h * n * h⁻¹) * h⁻¹⁻¹ = n := by group
  rwa [e] at h1

theorem le_normalizer_sup {N A B : Subgroup G} (hA : N ≤ normalizer (A : Set G))
    (hB : N ≤ normalizer (B : Set G)) : N ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hA hg),
    mem_normalizer_iff_map_conj_eq.mp (hB hg)]

theorem le_normalizer_inf_of_le {N A B : Subgroup G} (hA : N ≤ normalizer (A : Set G))
    (hB : N ≤ normalizer (B : Set G)) : N ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_inf (hA hg) (hB hg)

variable [Finite G] {S₁ S₂ V₁ V₂ : Subgroup G}

theorem commutator_le_oddCent_32 (hp : FourPair S₁ S₂ V₁ V₂) (hsep : CoreSep S₁ S₂) {t v : G}
    (ht : t ∈ V₁ ⊔ V₂) (ht1 : t ≠ 1) (hv : v ∈ V₁) (hv1 : v ≠ 1) :
    ⁅⁅oddCent t, V₁⁆ ⊓ centralizer ({v} : Set G), V₁⁆ ≤ oddCent v := by
  set L := centralizer ({v} : Set G) with hL
  have hvE : v ∈ V₁ ⊔ V₂ := mem_sup_left hv
  have hEL : V₁ ⊔ V₂ ≤ L := hp.le_centralizer_of_mem hvE
  have hV₁L : V₁ ≤ L := le_sup_left.trans hEL
  have hV₂L : V₂ ≤ L := le_sup_right.trans hEL
  have htL : t ∈ L := hEL ht
  have hV₁t : V₁ ≤ centralizer ({t} : Set G) := le_sup_left.trans (hp.le_centralizer_of_mem ht)
  have hV₁N : V₁ ≤ normalizer ((oddCent t : Subgroup G) : Set G) :=
    hV₁t.trans (centralizer_le_normalizer_oddCent t)
  have hcop : Nat.Coprime 2 (Nat.card (oddCent t)) :=
    Nat.coprime_two_left.mpr (Balance.odd_card_oddCoreOf _)
  have hX₁V : ⁅⁅oddCent t, V₁⁆, V₁⁆ = ⁅oddCent t, V₁⁆ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 2 Nat.prime_two V₁
      (oddCent t) hp.isPGroup_left hV₁N hcop
  set X₁ := ⁅oddCent t, V₁⁆ with hX₁
  set Y := X₁ ⊓ L with hY
  have hYN : V₁ ≤ normalizer (Y : Set G) := le_normalizer_inf_of_le
    (le_normalizer_commutator hV₁N le_normalizer) (hV₁L.trans le_normalizer)
  have hYcop : Nat.Coprime 2 (Nat.card Y) := Nat.coprime_two_left.mpr
    (Odd.of_dvd_nat (Balance.odd_card_oddCoreOf _)
      (card_dvd_of_le (inf_le_left.trans (commutator_oddCent_le hV₁t))))
  have hXV : ⁅⁅Y, V₁⁆, V₁⁆ = ⁅Y, V₁⁆ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 2 Nat.prime_two V₁
      Y hp.isPGroup_left hYN hYcop
  set X := ⁅Y, V₁⁆ with hX
  have hXL : X ≤ L := (commutator_mono inf_le_right hV₁L).trans (commutator_le_self L)
  have hXt : X ≤ oddCent t :=
    (commutator_mono inf_le_left le_rfl).trans (hX₁V.le.trans (commutator_oddCent_le hV₁t))
  show X ≤ oddCoreOf L
  rw [← G37.barOf_eq_bot_iff hXL]
  obtain ⟨u₁, hu₁, u₂, hu₂, htu⟩ := hp.exists_mul ht
  have hord : orderOf t = 2 := hp.orderOf_eq_two ht ht1
  refine eq_bot_of_coreSep_32 (L := L ⧸ goldschmidtOddCore L) oddCore_quotient_eq_bot
    (V₁ := barOf L V₁) (V₂ := barOf L V₂)
    (u₁ := QuotientGroup.mk' (goldschmidtOddCore L) ⟨u₁, hV₁L hu₁⟩)
    (u₂ := QuotientGroup.mk' (goldschmidtOddCore L) ⟨u₂, hV₂L hu₂⟩)
    ?_ (orderOf_mk_eq_two htL hord) (barOf_le_oddCent htL hord hXt) ?_ (mk_mem_center v)
    ⟨⟨u₂, hV₂L hu₂⟩, hu₂, rfl⟩ ?_ ?_ ?_ ?_
  · intro K hK
    rcases hsep v (mem_sup_left (hp.le_left hv)) (hp.orderOf_eq_two hvE hv1) K hK with h | h
    · exact Or.inl ((G37.barOf_mono hp.le_left).trans h)
    · exact Or.inr ((G37.barOf_mono hp.le_right).trans h)
  · rw [← G37.barOf_commutator hXL hV₁L, hXV]
  · rw [← map_mul]
    exact congrArg _ (Subtype.ext htu)
  · rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hp.commute hu₁ hu₂))
  · rw [← map_mul, ← map_one (QuotientGroup.mk' (goldschmidtOddCore L))]
    exact congrArg _ (Subtype.ext (mul_self_of_isKleinFour hp.four_right hu₂))
  · rcases mem_or_le_sup_of_isKleinFour hp.four_left hv hv1 hu₁ with h | h
    · left
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      refine mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← map_zpow]
      exact congrArg _ (Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk))
    · right
      have e : barOf L (zpowers v ⊔ zpowers u₁) =
          zpowers (QuotientGroup.mk' (goldschmidtOddCore L) ⟨v, hV₁L hv⟩) ⊔
            zpowers (QuotientGroup.mk' (goldschmidtOddCore L) ⟨u₁, hV₁L hu₁⟩) := by
        rw [G37.barOf_sup (zpowers_le.mpr (hV₁L hv)) (zpowers_le.mpr (hV₁L hu₁)),
          G37.barOf_zpowers (hV₁L hv), G37.barOf_zpowers (hV₁L hu₁)]
      exact (G37.barOf_mono h).trans e.le

theorem thetaOne_inf_le (hp : FourPair S₁ S₂ V₁ V₂) (hsep : CoreSep S₁ S₂) {t : G}
    (ht : t ∈ V₁ ⊔ V₂) (ht1 : t ≠ 1) :
    thetaOne V₁ t ⊓ centralizer (V₁ : Set G) ≤ oddCentSub V₁ := by
  have hV₁t : V₁ ≤ centralizer ({t} : Set G) := le_sup_left.trans (hp.le_centralizer_of_mem ht)
  have hV₁N : V₁ ≤ normalizer ((oddCent t : Subgroup G) : Set G) :=
    hV₁t.trans (centralizer_le_normalizer_oddCent t)
  have hcop : Nat.Coprime 2 (Nat.card (oddCent t)) :=
    Nat.coprime_two_left.mpr (Balance.odd_card_oddCoreOf _)
  have hX₁V : ⁅⁅oddCent t, V₁⁆, V₁⁆ = ⁅oddCent t, V₁⁆ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 2 Nat.prime_two V₁
      (oddCent t) hp.isPGroup_left hV₁N hcop
  set X₁ := ⁅oddCent t, V₁⁆ with hX₁
  have hX₁O : X₁ ≤ oddCent t := commutator_oddCent_le hV₁t
  have hX₁odd : Odd (Nat.card X₁) :=
    Odd.of_dvd_nat (Balance.odd_card_oddCoreOf _) (card_dvd_of_le hX₁O)
  have hX₁N : V₁ ≤ normalizer (X₁ : Set G) := le_normalizer_commutator hV₁N le_normalizer
  have hmain : X₁ ⊓ centralizer (V₁ : Set G) ≤ oddCentSub V₁ := by
    rw [CFSG.ComponentClassification.FooteLit.inf_centralizer_eq_iSup_of_isKleinFour
      hp.four_left hX₁N hX₁odd hX₁V]
    refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
    exact (inf_le_inf_right _ (commutator_le_oddCent_32 hp hsep ht ht1 hv hv1)).trans
      (oddCent_inf_le_oddCentSub hv)
  intro x hx
  obtain ⟨hxθ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hZN : oddCentSub V₁ ⊓ oddCent t ≤ normalizer (X₁ : Set G) :=
    inf_le_right.trans (le_normalizer_commutator_left _ _)
  have hx' : x ∈ ((X₁ ⊔ (oddCentSub V₁ ⊓ oddCent t) : Subgroup G) : Set G) := hxθ
  rw [coe_mul_of_right_le_normalizer_left _ _ hZN] at hx'
  obtain ⟨a, ha, z, hz, rfl⟩ := hx'
  have hzC : z ∈ centralizer (V₁ : Set G) := oddCentSub_le_centralizer V₁ hz.1
  have haC : a ∈ centralizer (V₁ : Set G) := by
    have h1 := mul_mem hxC (inv_mem hzC)
    rwa [mul_inv_cancel_right] at h1
  exact mul_mem (hmain ⟨ha, haC⟩) hz.1

theorem thetaOne_inf_le_right (hp : FourPair S₁ S₂ V₁ V₂) (hsep : CoreSep S₁ S₂) {t : G}
    (ht : t ∈ V₁ ⊔ V₂) (ht1 : t ≠ 1) :
    thetaOne V₂ t ⊓ centralizer (V₂ : Set G) ≤ oddCentSub V₂ :=
  thetaOne_inf_le hp.symm (coreSep_symm hsep) (by rwa [sup_comm]) ht1

end CFSG.Goldschmidt75
