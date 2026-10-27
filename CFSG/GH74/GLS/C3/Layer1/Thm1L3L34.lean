module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Fine
public import CFSG.GH74.GLS.C3.Layer1.Back91
public import CFSG.GH74.GLS.C3.Layer1.St1PumpClass
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.C3.Layer1.St1RigGen

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L34

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid

variable {G : Type} [Group G] [Finite G]

theorem ordA_one_strictMono : StrictMono (fun k : ℕ => 2 * k * (k + 1) * (2 * k + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  show 2 * n * (n + 1) * (2 * n + 1) < 2 * (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)
  nlinarith [Nat.zero_le n, sq_nonneg n]

theorem ordA_one_inj {q q' : ℕ} (hq : Odd q) (hq' : Odd q') (h : Open.ordA 1 q = Open.ordA 1 q') :
    q = q' := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨k', rfl⟩ := hq'
  rw [PumpClass.ordA_one_odd, PumpClass.ordA_one_odd] at h
  have := ordA_one_strictMono.injective h
  omega

theorem ordA_one_ne_2520 {q : ℕ} (hq : Odd q) : Open.ordA 1 q ≠ 2520 := by
  obtain ⟨k, rfl⟩ := hq
  rw [PumpClass.ordA_one_odd]
  intro h
  have hk : k ≤ 10 := by
    by_contra hk
    have : 2 * 11 * (11 + 1) * (2 * 11 + 1) ≤ 2 * k * (k + 1) * (2 * k + 1) := by
      gcongr <;> omega
    omega
  interval_cases k <;> omega

omit [Finite G] in
theorem card_kBar_of_hasL2Model {K : Subgroup G} {m : ℕ}
    (h : HasL2Model (kBar K) (fun q => q = m)) : Nat.card (kBar K) = Open.ordA 1 m := by
  obtain ⟨p, f, -, -, hq, hL⟩ := h
  have := GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
  rw [hq] at this
  exact this

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

omit [Finite G] in
theorem card_kBar_of_alt7 {K : Subgroup G} (h : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    Nat.card (kBar K) = 2520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_alt7]

theorem ordA_one_25 : Open.ordA 1 25 = 7800 := by decide

omit [Finite G] in
theorem hatCard_eq' (K : Subgroup G) : hatCard K = Nat.card (kBar K) := rfl

omit [Finite G] in
theorem hatCard_of_hasL2Model {K : Subgroup G} {m : ℕ}
    (h : HasL2Model (kBar K) (fun q => q = m)) : hatCard K = Open.ordA 1 m := by
  rw [hatCard_eq']
  exact card_kBar_of_hasL2Model h

omit [Finite G] in
theorem hatCard_of_alt7 {K : Subgroup G} (h : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    hatCard K = 2520 := by
  rw [hatCard_eq']
  exact card_kBar_of_alt7 h

omit [Finite G] in
theorem not_isFM9_sq {r : ℕ} (hr : 5 ≤ r) : ¬ IsFM9 (r ^ 2) := by
  rintro (h | ⟨hp, -⟩)
  · nlinarith
  · rcases hp.eq_one_or_self_of_dvd r (Dvd.intro_left r (sq r).symm) with h1 | h2
    · omega
    · nlinarith

theorem sup_eq_of_hasL2Model {I J : Subgroup G} (hIJ : I ≤ J) {r : ℕ}
    (hI : HasL2Model (kBar I) (fun q => q = r)) (hJ : HasL2Model (kBar J) (fun q => q = r)) :
    I ⊔ pPrimeCoreOf 2 J = J := by
  have hcard : Nat.card (kBar I) = Nat.card (kBar J) := by
    rw [card_kBar_of_hasL2Model hI, card_kBar_of_hasL2Model hJ]
  set φ := hatMap hIJ with hφ
  have hker : φ.ker ≤ pPrimeCore 2 ↥I :=
    le_sSup ⟨MonoidHom.normal_ker _, Nat.coprime_two_left.mpr (odd_card_ker_hatMap hIJ)⟩
  have hmap : φ.ker ≤ (pPrimeCore 2 ↥I).comap (MonoidHom.id ↥I) := by
    simpa using hker
  have hsurj : Function.Surjective
      (QuotientGroup.map φ.ker (pPrimeCore 2 ↥I) (MonoidHom.id ↥I) hmap) := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk a, rfl⟩
  have hle : Nat.card (kBar I) ≤ Nat.card φ.range := by
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    have h2 : Nat.card (↥I ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [h2] at h1
    exact h1
  have hrange : φ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) ?_)
    rw [← hcard]
    exact hle
  have hsurj' : Function.Surjective φ := MonoidHom.range_eq_top.mp hrange
  apply le_antisymm
  · exact sup_le hIJ (Thm1.pPrimeCoreOf_le_self J)
  · intro k hk
    obtain ⟨c, hc⟩ := hsurj' (QuotientGroup.mk' (pPrimeCore 2 ↥J) ⟨k, hk⟩)
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥J) (Subgroup.inclusion hIJ c) =
        QuotientGroup.mk' (pPrimeCore 2 ↥J) ⟨k, hk⟩ := hc
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have hn : ((c : G))⁻¹ * k ∈ pPrimeCoreOf 2 J :=
      ⟨(Subgroup.inclusion hIJ c)⁻¹ * ⟨k, hk⟩, h1, by simp⟩
    have hk' : k = (c : G) * (((c : G))⁻¹ * k) := by group
    rw [hk']
    exact Subgroup.mul_mem_sup c.2 hn

theorem isSimple_of_inU2
    {K : Type} [Group K] (hU : InU2 K)
    (hno : ¬ (IsL34Quotient K ∧ CFSG.IsElementaryAbelian 2 ↥(center K) ∧
      Nat.card ↥(center K) ≤ 4)) : IsSimpleGroup K := by
  obtain ⟨-, h⟩ := hU
  rcases h with h | h | h
  · exact Back.isSimpleGroup_of_hasL2Model h
  · exact Back.isSimpleGroup_of_alt7 h
  · exact absurd h hno

theorem J_class
    (hG : C3Hyp G) (hC2 : C2Facts) (hL34 : B_gen4_noL34_elem) {f : G} {J : Subgroup G}
    (hf2 : orderOf f = 2) (hJc : IsPCompIn 2 (centralizer ({f} : Set G)) J) {r : ℕ}
    (hrodd : Odd r) (hr5 : 5 ≤ r)
    (hshape : HasL2Model (kBar J) (fun q => q = r ^ 2) ∨
      Nonempty (kBar J ≃* alternatingGroup (Fin 7))) :
    InU2 (kBar J) ∧ ¬ InC2 (kBar J) ∧ IsSimpleGroup (kBar J) := by
  have hq : CFSG.IsQuasisimple (kBar J) := isQuasisimple_hat hJc
  have hU : InU2 (kBar J) := by
    refine ⟨hq, ?_⟩
    rcases hshape with h | h
    · exact Or.inl (Back.hasL2Model_mono (fun q hq => by subst hq; exact hrodd.pow) h)
    · exact Or.inr (Or.inl h)
  have hs : IsSimpleGroup (kBar J) := by
    rcases hshape with h | h
    · exact Back.isSimpleGroup_of_hasL2Model h
    · exact Back.isSimpleGroup_of_alt7 h
  refine ⟨hU, ?_, hs⟩
  intro hC
  have hcen : center (kBar J) = ⊥ := center_eq_bot_of_isSimple hs hq
  have hno : ¬ IsL34Quotient (kBar J) := fun hl =>
    hL34 G hG.gen4 f J hf2 hJc
      ⟨hl, by rw [hcen]; exact isElementaryAbelian_bot, by rw [hcen, Subgroup.card_bot]; norm_num⟩
  obtain ⟨e⟩ := kBar_equiv_bar hJc
  have hP : Gen4Comp ↥(bar f J) := gen4Comp_of_gen4Cen (gen4Cen_barQ hG.gen4 hf2) _
  have hFM' := hC2.fm9 _ hP (GH74.E2.inC2_of_mulEquiv e hC) (inU2_of_mulEquiv e hU)
    (fun h => hno (isL34Quotient_of_mulEquiv e.symm h))
  obtain ⟨p, f', hp, hf', hfm, hL⟩ := hasL2Model_of_mulEquiv e.symm hFM'
  have hodd : Odd (p ^ f') := isFM9_odd hfm
  have hcard := GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
  rcases hshape with h | h
  · have heq : p ^ f' = r ^ 2 := ordA_one_inj hodd hrodd.pow (hcard.symm.trans
      (card_kBar_of_hasL2Model h))
    rw [heq] at hfm
    exact not_isFM9_sq hr5 hfm
  · exact ordA_one_ne_2520 hodd (hcard.symm.trans (card_kBar_of_alt7 h))

end CFSG.GH74.GLS.C3.Layer1.Thm1L34
