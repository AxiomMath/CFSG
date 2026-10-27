module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefInputs
public import CFSG.Quasithin.Background.B4HypCore
import CFSG.Quasithin.Background.SmithB42SL3Nat
import CFSG.Quasithin.Background.SmithB42Sp4Nat
import CFSG.Quasithin.MS93.S38OffHatMod
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W]

private theorem inf_centSec_eq_bot_of_realizes {V : Type} [CommGroup V] {D : FFModel}
    (hD : D.Faithful) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : H ⊓ centSec U Z = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxH, hxZ⟩
  obtain ⟨hπs, hZU, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  obtain ⟨hxU, hxZU⟩ := mem_centSec.1 hxZ
  obtain ⟨γ, hγ⟩ := hπs ⟨x, hxH⟩
  have hγx : ((π γ : ↥H) : MulAut V) = x := congrArg Subtype.val hγ
  have hγ1 : γ = 1 := by
    apply hD
    intro m hm
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
    have hmem : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := by
      rw [hγx]
      exact (hxU (u : V)).2 u.2
    have h1 := hβe γ u ⟨m, hm⟩ hmem (hsec γ m hm) hu
    have hz : β ⟨x (u : V) * (u : V)⁻¹, hZU (hxZU (u : V) u.2)⟩ = 1 :=
      (hβk _).2 (hxZU (u : V) u.2)
    have hsub : (⟨((π γ : ↥H) : MulAut V) (u : V), hmem⟩ : ↥U) =
        u * ⟨x (u : V) * (u : V)⁻¹, hZU (hxZU (u : V) u.2)⟩ := by
      ext
      change ((π γ : ↥H) : MulAut V) (u : V) =
        (u : V) * (x (u : V) * (u : V)⁻¹)
      rw [hγx, mul_comm (u : V) (x (u : V) * (u : V)⁻¹), mul_assoc, inv_mul_cancel,
        mul_one]
    have h2 : β u = QuotientGroup.mk (⟨D.act γ m, hsec γ m hm⟩ : ↥D.sec) := by
      rw [← h1, hsub, map_mul, hz, mul_one]
    have h3 := QuotientGroup.eq.mp (hu.symm.trans h2)
    rw [mul_comm]
    exact h3
  rw [← hγx, hγ1, map_one]
  rfl

private theorem realizes_autSec_of_realizes {V : Type} [CommGroup V] [Finite V]
    {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : D.Realizes H U Z) (hfaith : H ⊓ centSec U Z = ⊥) :
    D.Realizes (autSec H U Z) ⊤ ⊥ := by
  obtain ⟨π, hπ⟩ := h
  have hπ' := hπ
  obtain ⟨-, hZU, -, hHU, hHZ, -⟩ := hπ'
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_realizes_autSec_of_realizes hZU
    (B1.le_stabSub_of_invariant fun a ha u hu => hHU ⟨a, ha⟩ u hu)
    (B1.le_stabSub_of_invariant fun a ha z hz => hHZ ⟨a, ha⟩ z hz) hfaith ⟨π, hπ⟩

theorem IsGomiNatural.inf_centSec_eq_bot {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : IsGomiNatural L I Z) : L ⊓ centSec I Z = ⊥ := by
  rcases h with ⟨a, ha, K, hKf, hKfin, hK, hreal⟩ | ⟨a, ha, K, hKf, hKfin, hK, hreal⟩ |
    halt | hhat
  · obtain ⟨π, hπ⟩ := hreal
    exact inf_centSec_eq_bot_of_realizes (FFModel.nat_faithful (StatedSL 3 K)) hπ
  · obtain ⟨π, hπ⟩ := hreal
    exact inf_centSec_eq_bot_of_realizes (FFModel.nat_faithful (StatedSp 2 K)) hπ
  · obtain ⟨π, hπ⟩ := halt
    exact inf_centSec_eq_bot_of_realizes (FFC.altDn_faithful (by norm_num : 5 ≤ 6)) hπ
  · obtain ⟨K, hKf, hKfin, Γ₀, hK, -, -, -, hreal⟩ := hhat
    obtain ⟨π, hπ⟩ := hreal
    exact inf_centSec_eq_bot_of_realizes (FFModel.nat_faithful Γ₀) hπ

theorem IsGomiNatural.autSec [Finite W] {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : IsGomiNatural L I Z) : IsGomiNatural (autSec L I Z) ⊤ ⊥ := by
  have hfaith : L ⊓ centSec I Z = ⊥ := IsGomiNatural.inf_centSec_eq_bot h
  rcases h with ⟨a, ha, K, hKf, hKfin, hK, hreal⟩ | ⟨a, ha, K, hKf, hKfin, hK, hreal⟩ |
    halt | hhat
  · exact Or.inl ⟨a, ha, K, hKf, hKfin, hK, realizes_autSec_of_realizes hreal hfaith⟩
  · exact Or.inr (Or.inl ⟨a, ha, K, hKf, hKfin, hK,
      realizes_autSec_of_realizes hreal hfaith⟩)
  · exact Or.inr (Or.inr (Or.inl (realizes_autSec_of_realizes halt hfaith)))
  · obtain ⟨K, hKf, hKfin, Γ₀, hK, hdet, hhat, hscal, hreal⟩ := hhat
    exact Or.inr (Or.inr (Or.inr ⟨K, hKf, hKfin, Γ₀, hK, hdet, hhat, hscal,
      realizes_autSec_of_realizes hreal hfaith⟩))

private theorem card_mul_card_fixV_sq_le_of_binaryNaturalSL {V : Type} [CommGroup V]
    [Finite V] {L E : Subgroup (MulAut V)} {a : ℕ} (hnat : BinaryNaturalSL L ⊤ ⊥ 3 a)
    (hEL : E ≤ L) (hE : IsElemAbelian2 E) (hE1 : E ≠ ⊥) :
    Nat.card E * Nat.card ↥(fixV E) ^ 2 ≤ Nat.card V ^ 2 := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  have : CharP K 2 := B5.charP_two_of_card_eq hKcard
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia (StatedSL 3 K) hπ
  set c : B5.NatSec L ⊤ ⊥ K := B42SL3.natSecOf π hπ.1 e he with hc
  have hVcard : Nat.card V = Nat.card K ^ 3 := by
    rw [Nat.card_congr e.toEquiv, card_stdMod, Fintype.card_fin]
  have hfix : Nat.card ↥(fixV E) = Nat.card (B5.fixK (c.pre E)) := by
    rw [← c.card_inf_fixV (fun _ _ _ => Iff.rfl) hEL, top_inf_eq]
  have hcardE : Nat.card E = Nat.card (c.pre E) := (c.card_pre hEL).symm
  rw [hcardE, hfix, hVcard]
  calc Nat.card (c.pre E) * Nat.card (B5.fixK (c.pre E)) ^ 2 ≤ Nat.card K ^ 6 :=
        B5.card_mul_card_fixK_sq_le (c.pre_ne_bot hEL hE1) (c.pre_sq hE) (c.pre_comm hE)
    _ = (Nat.card K ^ 3) ^ 2 := by ring

private theorem cube_le_of_two_thirds_le_rAV {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)} (hE : IsElemAbelian2 E)
    (hE1 : E ≠ ⊥) (h : (2 / 3 : ℚ) ≤ rAV E) :
    Nat.card E ^ 2 * Nat.card ↥(fixV E) ^ 3 ≤ Nat.card V ^ 3 := by
  have hBc := B1.card_elemAbelian hE
  have hCc := card_eq_two_pow hV (fixV E)
  have hVc := card_eq_two_pow_rk hV
  have hpos : 0 < rk ↥E := hE.rk_pos hE1
  have hrkpos : (0 : ℚ) < (rk ↥E : ℚ) := by exact_mod_cast hpos
  have h1 : (2 / 3 : ℚ) * (rk ↥E : ℚ) ≤ (rkIdx (fixV E) : ℚ) := by
    rw [rAV] at h
    exact (le_div_iff₀ hrkpos).mp h
  have h2 : (rk ↥E : ℚ) * 2 ≤ (rkIdx (fixV E) : ℚ) * 3 := by linarith
  have h3 : rk ↥E * 2 ≤ rkIdx (fixV E) * 3 := by exact_mod_cast h2
  rw [hBc, hCc, hVc, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have hsum := rk_add_rkIdx (fixV E)
  omega

private theorem mul_sq_le_of_sq_mul_cube {e c v : ℕ} (h : e ^ 2 * c ^ 3 ≤ v ^ 3) (hc : c ≤ v) :
    e * c ^ 2 ≤ v ^ 2 := by
  have h1 : (e * c ^ 2) ^ 2 ≤ (v ^ 2) ^ 2 := by
    calc (e * c ^ 2) ^ 2 = e ^ 2 * c ^ 4 := by ring
      _ = (e ^ 2 * c ^ 3) * c := by ring
      _ ≤ v ^ 3 * v := Nat.mul_le_mul h hc
      _ = (v ^ 2) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

private theorem cube_le_of_binaryNaturalSp4 {V : Type} [CommGroup V] [Finite V]
    {L E : Subgroup (MulAut V)} {a : ℕ} (hnat : BinaryNaturalSp4 L ⊤ ⊥ a) (ha : 2 ≤ a)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE : IsElemAbelian2 E)
    (hff : Nat.card V ≤ Nat.card E * Nat.card ↥(fixV E)) :
    Nat.card E ^ 2 * Nat.card ↥(fixV E) ^ 3 ≤ Nat.card V ^ 3 := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  have : CharP K 2 := B5.charP_two_of_card_eq hKcard
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia (StatedSp 2 K) hπ
  have hLe : L.map (congrHom e) = natImage (StatedSp 2 K) :=
    map_congrHom_eq_natImage (StatedSp 2 K) hπ.1 e he
  have hEN' : E.map (congrHom e) ≤ natNorm (StatedSp 2 K) := by
    have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((L.map (congrHom e) :
          Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))) :
          Set (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))) :=
      Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
    rw [natNorm, ← hLe, ← h1]
    exact Subgroup.map_mono hEN
  have hEel : IsElemAbelian2 (E.map (congrHom e)) :=
    (isElemAbelian2_map_congrHom e).2 hE
  have hcardV : Nat.card V = Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) :=
    Nat.card_congr e.toEquiv
  have hoff : Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) ≤
      Nat.card (E.map (congrHom e)) * Nat.card ↥(fixV (E.map (congrHom e))) := by
    rw [card_map_congrHom, fixV_map_congrHom, Subgroup.card_map_of_injective e.injective,
      ← hcardV]
    exact hff
  have hmem : E.map (congrHom e) ≤ natImage (StatedSp 2 K) := by
    by_contra hnot
    have hlt := FFC.Sp4Off.card_mul_card_fixV_lt ha hKcard hEN' hEel hnot
    rw [card_map_congrHom, fixV_map_congrHom, Subgroup.card_map_of_injective e.injective,
      ← hcardV] at hlt
    omega
  have h := B42Sp4.natImage_card_sq_mul_card_fixV_cube_le hmem hEel
  rw [card_map_congrHom, fixV_map_congrHom, Subgroup.card_map_of_injective e.injective,
    ← hcardV] at h
  exact h

private theorem cube_le_of_alternatingNatural {V : Type} [CommGroup V] [Finite V]
    {L E : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hnat : AlternatingNatural L ⊤ ⊥ 6) (hB4 : B4HypCore (L ⊔ E) L)
    (hE : IsElemAbelian2 E) (hE1 : E ≠ ⊥) :
    Nat.card E ^ 2 * Nat.card ↥(fixV E) ^ 3 ≤ Nat.card V ^ 3 := by
  obtain ⟨π, hπ⟩ := hnat
  have hD : (FFModel.altDn 6).Faithful := FFC.altDn_faithful (by norm_num : 5 ≤ 6)
  have hinj : Function.Injective π := FFC.injective_of_faithful_sec hD hπ
  have hcardV : Nat.card V = 16 := by
    obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
    have hβi : Function.Injective β := by
      rw [injective_iff_map_eq_one]
      intro u hu
      exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
    rw [← Subgroup.card_top (G := V), Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)]
    have h := CFSG.Quasithin.Explicit.card_dn_sec (n := 6) (by norm_num) .alternating
    rw [ite_eq_left (show Even 6 from ⟨3, rfl⟩)] at h
    norm_num at h
    exact h
  have e : ↥L ≃* ↥(alternatingGroup (Fin 6)) :=
    (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
  have hcenter : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_center_iff] at hz
    have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hz w]
    have h4 : 4 ≤ Nat.card (Fin 6) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    rw [alternatingGroup.center_eq_bot (α := Fin 6) h4] at hz'
    rw [Subgroup.mem_bot] at hz' ⊢
    exact e.injective (by rw [hz', map_one])
  have hT : B42TypeAlt6 ↥L :=
    ⟨hcenter, ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot.trans e)⟩⟩
  have C := B42Alt6.ctx_of_b4Hyp_core (G := L ⊔ E) hB4 hT
  exact cube_le_of_two_thirds_le_rAV hV hE hE1
    (B42Alt6.two_thirds_le_rAV C hB4.2.2 hcardV le_sup_right hE1 hE)

private theorem hatA6_bounds {V : Type} [CommGroup V] [Finite V]
    {L E : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1) (hnat : TripleA6Six L ⊤ ⊥)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE : IsElemAbelian2 E)
    (hE1 : E ≠ ⊥) (hff : Nat.card V ≤ Nat.card E * Nat.card ↥(fixV E)) :
    Nat.card E * Nat.card ↥(fixV E) ^ 2 ≤ Nat.card V ^ 2 ∧
      Nat.card E ^ 2 * Nat.card ↥(fixV E) ^ 3 ≤ Nat.card V ^ 3 := by
  have hhat := CFSG.Quasithin.MS93.S38H.HatMod.of_tripleA6Six hV hnat
  obtain ⟨-, hE4, hfix, -⟩ := hhat.offender hEN hE hE1 hff
  have hV6 := hhat.card
  constructor
  · rw [hE4, hfix, hV6]
    norm_num
  · rw [hE4, hfix, hV6]
    norm_num

theorem gomiHomog_le_of_binaryNaturalSL {V : Type} [CommGroup V] [Finite V]
    {L E : Subgroup (MulAut V)} {a : ℕ} (hnat : BinaryNaturalSL L ⊤ ⊥ 3 a)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE : IsElemAbelian2 E)
    (hff : Nat.card V ≤ Nat.card E * Nat.card ↥(fixV E)) : E ≤ L := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  have : CharP K 2 := B5.charP_two_of_card_eq hKcard
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia (StatedSL 3 K) hπ
  have hLe : L.map (congrHom e) = natImage (StatedSL 3 K) :=
    map_congrHom_eq_natImage (StatedSL 3 K) hπ.1 e he
  have hEN' : E.map (congrHom e) ≤ natNorm (StatedSL 3 K) := by
    have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((L.map (congrHom e) :
          Subgroup (MulAut (StdMod (Fin 3) K))) : Set (MulAut (StdMod (Fin 3) K))) :=
      Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
    rw [natNorm, ← hLe, ← h1]
    exact Subgroup.map_mono hEN
  have hEel : IsElemAbelian2 (E.map (congrHom e)) :=
    (isElemAbelian2_map_congrHom e).2 hE
  have hoff : Nat.card (StdMod (Fin 3) K) ≤
      Nat.card (E.map (congrHom e)) * Nat.card ↥(fixV (E.map (congrHom e))) := by
    rw [card_map_congrHom, fixV_map_congrHom, Subgroup.card_map_of_injective e.injective,
      ← Nat.card_congr e.toEquiv]
    exact hff
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0, pow_zero] at hKcard
      have := Finite.one_lt_card (α := K)
      omega
    · exact hpos
  have hmem := B42SL3.le_natImage_of_offender ha hKcard hEN' hEel hoff
  rw [← hLe] at hmem
  exact (map_congrHom_le_iff e).1 hmem

theorem gomiHomog_bound {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L E : Subgroup (MulAut V)} (hB4 : B4HypCore (L ⊔ E) L) (hnat : IsGomiNatural L ⊤ ⊥)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE : IsElemAbelian2 E) (hE1 : E ≠ ⊥)
    (hff : Nat.card V ≤ Nat.card E * Nat.card ↥(fixV E)) :
    Nat.card E * Nat.card ↥(fixV E) ^ 2 ≤ Nat.card V ^ 2 ∧
      ((∃ a : ℕ, 1 ≤ a ∧ BinaryNaturalSL L ⊤ ⊥ 3 a) ∨
        Nat.card E ^ 2 * Nat.card ↥(fixV E) ^ 3 ≤ Nat.card V ^ 3) := by
  have hc := Subgroup.card_le_card_group (fixV E)
  rcases hnat with hSL | hSp | hAlt | hHat
  · obtain ⟨a, ha, hnatSL⟩ := hSL
    have hEL := gomiHomog_le_of_binaryNaturalSL hnatSL hEN hE hff
    exact ⟨card_mul_card_fixV_sq_le_of_binaryNaturalSL hnatSL hEL hE hE1,
      Or.inl ⟨a, ha, hnatSL⟩⟩
  · obtain ⟨a, ha, hnatSp⟩ := hSp
    have hcube := cube_le_of_binaryNaturalSp4 hnatSp ha hEN hE hff
    exact ⟨mul_sq_le_of_sq_mul_cube hcube hc, Or.inr hcube⟩
  · have hcube := cube_le_of_alternatingNatural hV hAlt hB4 hE hE1
    exact ⟨mul_sq_le_of_sq_mul_cube hcube hc, Or.inr hcube⟩
  · obtain ⟨hb1, hb2⟩ := hatA6_bounds hV hHat hEN hE hE1 hff
    exact ⟨hb1, Or.inr hb2⟩

end CFSG.GroupTheory
