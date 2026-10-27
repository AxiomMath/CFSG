module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoPartner
public import CFSG.LocalAnalysis.OddStandard.AltStdWeakTwoSec
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two.Exact

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

section Cent

theorem oddY_eq_bot_of_cent (d : Cyc L Q z)
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) = ⊥ := by
  obtain ⟨hle, -, -, hdisj, -⟩ :=
    oddPart_spec (cyc_le_inf_cent d) d.pgroup (cyc_odd_relIndex_inf d) d.cyclic
  rw [eq_bot_iff, ← hdisj]
  intro y hy
  refine ⟨hy, ?_⟩
  rw [← hC]
  exact hle hy

theorem exactShape_of_cent (B : Base G L Q n z)
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) : ExactShape z L n :=
  ⟨B.cyc.order, B.iso, le_cent_single B.std B.cyc, cent_le_normalizer B.std B.cyc, by
    rw [hC, eq_zpowers_of_card_eq_two_of_cyc B.cyc B.card]⟩

theorem eq_swapIota_or_of_cent (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) :
    x = (swapIota T θ (permOf T.toBase θ hx) : G) ∨
      x = z * (swapIota T θ (permOf T.toBase θ hx) : G) := by
  obtain ⟨y, hy, h⟩ := exists_oddY_mul_swapIota T θ hx
  rw [oddY_eq_bot_of_cent T.cyc hC, mem_bot] at hy
  subst hy
  simpa only [one_mul] using h

theorem centralizer_eq_of_cent (T : Shape G L Q n z u)
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) :
    centralizer ({z} : Set G) = zpowers z ⊔ (L ⊔ zpowers u) := by
  rw [centralizer_eq_sup_oddY T, oddY_eq_bot_of_cent T.cyc hC, bot_sup_eq]

theorem card_centralizer_eq_of_cent (T : Shape G L Q n z u)
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) :
    Nat.card (centralizer ({z} : Set G)) = 2 * n.factorial := by
  rw [card_centralizer_eq T, oddY_eq_bot_of_cent T.cyc hC, Subgroup.card_bot, one_mul]

theorem commutator_centralizer_le_of_cent (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) :
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤ L := by
  have h := commutator_centralizer_le_sup B.std θ B.hn B.cyc B.card
  rwa [oddY_eq_bot_of_cent B.cyc hC, sup_bot_eq] at h

omit [Finite G] in
theorem commutator_centralizer_conj_le
    (hcz : ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤ L) (g : G) :
    ⁅centralizer ({g⁻¹ * z * g} : Set G), centralizer ({g⁻¹ * z * g} : Set G)⁆ ≤
      CFSG.conjugate L g := by
  have h1 : centralizer ({g⁻¹ * z * g} : Set G) =
      (centralizer ({z} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
    have := SwapData.centralizer_conj g⁻¹ z
    rwa [inv_inv] at this
  rw [h1, ← Subgroup.map_commutator]
  exact Subgroup.map_mono hcz

theorem caseII_of_caseIIW (d : Cyc L Q z)
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    {θ : L ≃* alternatingGroup (Fin n)} {hn : 8 ≤ n} {S : Subgroup G} (h : CaseIIW θ hn S z) :
    CaseII θ hn S z := by
  intro a
  rw [h a, oddY_eq_bot_of_cent d hC]
  constructor
  · rintro ⟨y, hy, s, hs, hsw, rfl⟩
    rw [mem_bot] at hy
    subst hy
    rw [one_mul, inv_one, mul_one]
    exact ⟨hs, hsw⟩
  · rintro ⟨hs, hsw⟩
    exact ⟨1, one_mem _, a, hs, hsw, by group⟩

theorem swapIota_mem_of_even (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {σ : Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    ∃ hw : (swapIota T θ σ : G) ∈ L,
      ((θ ⟨swapIota T θ σ, hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = σ := by
  set l : L := θ.symm ⟨σ, hσ⟩ with hl
  have hlS : (l : G) ∈ L ⊔ zpowers u := mem_sup_left l.2
  have hperm : rhoSwap T θ ⟨l, hlS⟩ = σ := by
    rw [rhoSwap_apply, permOf_of_mem T.toBase θ _ l.2]
    simp [hl]
  have hι : (swapIota T θ σ : G) = l := by
    have h1 := swapIota_rhoSwap T θ ⟨l, hlS⟩
    rw [hperm] at h1
    exact congrArg Subtype.val h1
  refine ⟨hι ▸ l.2, ?_⟩
  have : (⟨swapIota T θ σ, hι ▸ l.2⟩ : L) = l := Subtype.ext hι
  rw [this, hl, MulEquiv.apply_symm_apply]

end Cent

section Map

theorem exactShape_map {X : Type} [Group X] {t : X} {A : Subgroup X} {m : ℕ}
    (h : ExactShape t A m) (φ : X ≃* X) : ExactShape (φ t) (A.map φ.toMonoidHom) m where
  order := by rw [MulEquiv.orderOf_eq]; exact h.order
  iso := ⟨(A.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans h.iso.some⟩
  le_cent := by
    rw [Solomon75.centralizer_singleton_map_mulEquiv]
    exact Subgroup.map_mono h.le_cent
  cent_le_norm := by
    rw [Solomon75.centralizer_singleton_map_mulEquiv, Solomon75.normalizer_map_equiv]
    exact Subgroup.map_mono h.cent_le_norm
  cent_cent := by
    rw [Solomon75.centralizer_map_equiv, Solomon75.centralizer_singleton_map_mulEquiv,
      ← Subgroup.map_inf _ _ _ φ.injective, h.cent_cent, MonoidHom.map_zpowers]
    rfl

end Map

section Four

theorem oddCore_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.oddCore A = ⊥) : CFSG.oddCore B = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le fun N hN' => ?_
  obtain ⟨hN, hodd⟩ := hN'
  have h1 : N.map e.symm.toMonoidHom ≤ CFSG.oddCore A :=
    le_sSup ⟨hN.map _ e.symm.surjective,
      by rwa [Subgroup.card_map_of_injective e.symm.injective]⟩
  rw [h] at h1
  intro x hx
  have hx1 : e.symm x ∈ (⊥ : Subgroup A) := h1 ⟨x, hx, rfl⟩
  rw [mem_bot, MulEquiv.symm_apply_eq, map_one] at hx1
  rw [mem_bot]
  exact hx1

theorem oddCore_centralizer_conj_eq_bot {θ : L ≃* alternatingGroup (Fin n)}
    (hbal : FourPointBalance L θ) {w : G} (hw : w ∈ L)
    (hct : ((θ ⟨w, hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2}) (g : G) :
    CFSG.oddCore (centralizer ({g * w * g⁻¹} : Set G)) = ⊥ := by
  have hord : orderOf (⟨w, hw⟩ : L) = 2 := by
    rw [← MulEquiv.orderOf_eq θ, ← Subgroup.orderOf_coe, ← Perm.lcm_cycleType, hct]
    rfl
  have hsupp : ((θ ⟨w, hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 4 := by
    rw [← Perm.sum_cycleType, hct]
    rfl
  have h0 : CFSG.oddCore (centralizer ({w} : Set G)) = ⊥ := hbal ⟨w, hw⟩ hord hsupp
  exact oddCore_eq_bot_of_mulEquiv ((Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (SwapData.centralizer_conj g w).symm)) h0

theorem oddCore_twoSec_eq_bot_of (x : G) (hx : orderOf x = 2)
    (h : CFSG.oddCore (centralizer ({x} : Set G)) = ⊥) : CFSG.oddCore (TwoSec x) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine QuasiDihedralFusion.oddCore_quotient_eq_bot_of_le_center h _
    (zpowers_le.2 (selfC_mem_center x)) ?_
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers]
  unfold selfC
  rw [Subgroup.orderOf_mk, hx, pow_one]

theorem centralizer_ne_top_of_exists_ne_one (hS : StandardSetting G L) {R : Subgroup G}
    (hR : ∃ r ∈ R, r ≠ 1) : centralizer (R : Set G) ≠ ⊤ := by
  obtain ⟨r, hr, hr1⟩ := hR
  intro htop
  apply centralizer_singleton_ne_top_of_simple hS.simple hS.nonab hr1
  rw [eq_top_iff, ← htop]
  exact centralizer_le (Set.singleton_subset_iff.2 hr)

theorem isKGroupCat_twoSec_of_std (hS : StandardSetting G L) {x : G} (hx1 : x ≠ 1) :
    CFSG.SectionRank.IsKGroupCat (TwoSec x) :=
  (isKGroupCat_of_kProper hS.kProper _
    (centralizer_singleton_ne_top_of_simple hS.simple hS.nonab hx1)).quotient _

end Four

end CFSG.OddStandard.AltStdCycTwo.Two.Exact
