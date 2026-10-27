module

public import CFSG.Sporadic.Co1Block.TwoCCent
public import Certificates.Certificate15094
public import CFSG.Sporadic.Co1Block.TwoACent
import CFSG.Sporadic.Co1Patterson.GraphNative
public import CFSG.Sporadic.Co1Block.TwoBCentBase2

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1.InvNative

theorem gtOK_validRows {Gs : Array (Array ℕ)} {T : GTree} (h : gtOK Gs T = true) {i : ℕ}
    (hi : i < T.pts.size) : validRows T.pts[i]! = true := by
  unfold gtOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hall⟩, -⟩, -⟩ := h
  have hp := CFSG.Sporadic.Th.allIn_eq_true.1 hall i (Nat.zero_le _) hi
  simp only [gtPointOK, Bool.and_eq_true] at hp
  exact hp.1

theorem mem_cent_GL {x y : GL24} : x ∈ centralizer ({y} : Set GL24) ↔ x * y = y * x := by
  rw [mem_centralizer_singleton_iff]

@[expose, irreducible] noncomputable def holtFreePG : GL24 :=
  (strongDagG cG twoCD1 twoCBray twoCD2).getD Data.pIdx.1 1 *
    (strongDagG cG twoCD1 twoCBray twoCD2).getD Data.pIdx.2 1

theorem holtFreePG_def : holtFreePG = (strongDagG cG twoCD1 twoCBray twoCD2).getD Data.pIdx.1 1 *
    (strongDagG cG twoCD1 twoCBray twoCD2).getD Data.pIdx.2 1 := by
  unfold holtFreePG
  rfl

theorem twoCDagRows_eq : twoCDagRows = strongRows iotaCRows twoCD1 twoCBray twoCD2 := by
  unfold twoCDagRows strongRows
  rfl

theorem rep_twoCDag
    (k : ℕ) :
    MRep (twoCDagRows.getD k Native.one) ((strongDagG cG twoCD1 twoCBray twoCD2).getD k 1) := by
  rw [twoCDagRows_eq]
  exact getD_rep (rep_strongDag rep_iotaC twoC_cent_check) MRep.one k

theorem rep_holtFreeP :
    MRep holtFreePRows holtFreePG := by
  unfold holtFreePRows
  rw [holtFreePG_def]
  exact (rep_twoCDag _).mul (rep_twoCDag _)

theorem holtFreePG_mem :
    holtFreePG ∈ GA ⊓ centralizer {cG} := by
  rw [holtFreePG_def]
  exact mul_mem (twoCE_le (getD_mem_of_forall strongDag_mem _))
    (twoCE_le (getD_mem_of_forall strongDag_mem _))

theorem holtFree_order_parts :
    Native.pow holtFreePRows 11 = Native.one ∧ holtFreePRows ≠ Native.one ∧
      CFSG.Sporadic.Co1.InvNative.validRows holtFreePRows = true := by
  have h := Certificates.certificate15094.1
  simp only [holtFreeOrderCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem holtFreePG_pow :
    holtFreePG ^ 11 = 1 :=
  MRep.eq_of_eq (rep_holtFreeP.pow 11) MRep.one holtFree_order_parts.1

theorem orderOf_holtFreePG :
    orderOf holtFreePG = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine orderOf_eq_prime holtFreePG_pow fun h1 => holtFree_order_parts.2.1 ?_
  have h := rep_holtFreeP
  rw [h1] at h
  exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid holtFree_order_parts.2.2
    validRows_one (h.trans MRep.one.symm)

theorem holtFreePG_inv :
    holtFreePG⁻¹ = holtFreePG ^ 10 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ']
  exact holtFreePG_pow

theorem holtFreePG_fix
    {q : GL24} (hq : q ∈ twoCQ) (hpq : holtFreePG * q = q * holtFreePG) : q = 1 ∨ q = cG := by
  have hgt := (qCheck_parts twoC_q_check).1
  obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq valHom valHom_injective hgt twoCQg
    (qRep_arr qRep_twoC)
  have hq' : q ∈ (Subgroup.closure (twoCQg '' {l | l < twoCQRows.toArray.size}) : Set GL24) := by
    rw [← qSub_eq]
    exact hq
  rw [heq] at hq'
  obtain ⟨i, hi, rfl⟩ := hq'
  set T := gtBFS twoCQRows.toArray 2048 with hT
  have hrep : MRep T.pts[i]! (f i) := (hf i hi).symm
  have hvalid : validRows T.pts[i]! = true := gtOK_validRows hgt hi
  have hrows : Native.mul holtFreePRows T.pts[i]! = Native.mul T.pts[i]! holtFreePRows := by
    refine CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid
      (CFSG.Sporadic.Co1Patterson.validRows_mul holtFree_order_parts.2.2 hvalid)
      (CFSG.Sporadic.Co1Patterson.validRows_mul hvalid holtFree_order_parts.2.2) ?_
    rw [rep_holtFreeP.mul hrep, hpq, ← hrep.mul rep_holtFreeP]
  have hfix := Certificates.certificate15094.2.1
  rw [holtFreeFixCheck, Array.all_eq_true] at hfix
  have hfi := hfix i hi
  rw [← getElem!_pos T.pts i hi, hrows, beq_self_eq_true, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hfi
  rcases hfi with h | h
  · left
    rw [h] at hrep
    exact hrep.eq MRep.one
  · right
    rw [h] at hrep
    exact hrep.eq rep_iotaC

@[expose] noncomputable def holtFreeWG (q : GL24) : GL24 := q * (holtFreePG * q * holtFreePG⁻¹)

theorem rep_holtFreeW
    {R : Native.Rows} {q : GL24} (hq : MRep R q) : MRep (holtFreeWRows R) (holtFreeWG q) := by
  unfold holtFreeWRows holtFreeWG
  rw [holtFreePG_inv]
  exact hq.mul ((rep_holtFreeP.mul hq).mul (rep_holtFreeP.pow 10))

theorem ncard_xFix_one : (xFix (1 : GL24)).ncard = 98280 := by
  have h : xFix (1 : GL24) = certX := by
    ext x
    simp [xFix]
  rw [h, ncard_certX]

theorem isConj_of_ncard_fix
    {x : GA} (hx : (x : GL24) * x = 1) :
    ((xFix (x : GL24)).ncard = 2280 → IsConj x aC) ∧
      ((xFix (x : GL24)).ncard = 264 → IsConj x cC) := by
  have hx1 : (xFix (x : GL24)).ncard = 2280 ∨ (xFix (x : GL24)).ncard = 264 → x ≠ 1 := by
    rintro h rfl
    rw [Subgroup.coe_one, ncard_xFix_one] at h
    omega
  have hx2 : (xFix (x : GL24)).ncard = 2280 ∨ (xFix (x : GL24)).ncard = 264 → orderOf x = 2 :=
    fun h => orderOf_eq_prime (by rw [sq]; exact Subtype.ext hx) (hx1 h)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases involution_classes.1 x (hx2 (Or.inl h)) with hc | hc | hc
    · exact hc
    · rw [← ncard_fix_isConj hc, ncard_fix_cC] at h
      omega
    · rw [← ncard_fix_isConj hc, ncard_fix_a₁] at h
      omega
  · rcases involution_classes.1 x (hx2 (Or.inr h)) with hc | hc | hc
    · rw [← ncard_fix_isConj hc, ncard_fix_aC] at h
      omega
    · exact hc
    · rw [← ncard_fix_isConj hc, ncard_fix_a₁] at h
      omega

theorem isConj_aC_of_two_pow
    {y : GA} (hy : orderOf y = 2) (h2 : 2 ^ 21 ∣ Nat.card (centralizer ({y} : Set GA))) :
    IsConj y aC := by
  have hcard : ∀ {x w : GA}, IsConj x w →
      Nat.card (centralizer ({x} : Set GA)) = Nat.card (centralizer ({w} : Set GA)) := by
    intro x w hxw
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxw
    exact card_centralizer_equiv (MulAut.conj c) x
  rcases involution_classes.1 y hy with hc | hc | hc
  · exact hc
  · rw [hcard hc, card_centralizer_GA, coe_cC, card_cent_cG] at h2
    norm_num at h2
  · rw [hcard hc, card_cent_a₁] at h2
    norm_num at h2

theorem transport_twoC {G₀ H₀ : Type*} [Group G₀] [Group H₀] (Φ : G₀ ≃* H₀)
    {c p qa qb qf a₀ : G₀} {Q : Subgroup G₀}
    (hcQ : c ∈ Q) (hQ2 : ∀ x ∈ Q, x * x = 1) (hQc : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQcard : Nat.card Q = 2048) (hQn : ∀ g : G₀, g * c = c * g → ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (hpc : p * c = c * p) (hp11 : orderOf p = 11)
    (hpfix : ∀ x ∈ Q, p * x = x * p → x = 1 ∨ x = c)
    (hqa : qa ∈ Q) (hqb : qb ∈ Q) (hqf : qf ∈ Q)
    (ha : IsConj (qa * (p * qa * p⁻¹)) a₀) (hf : IsConj (qf * (p * qf * p⁻¹)) a₀)
    (haf : IsConj (qa * (p * qa * p⁻¹) * (qf * (p * qf * p⁻¹))) a₀)
    (hb : ¬ IsConj (qb * (p * qb * p⁻¹)) a₀) (hbc : ¬ IsConj (qb * (p * qb * p⁻¹) * c) a₀)
    (hb1 : qb * (p * qb * p⁻¹) ≠ 1)
    (h2A : ∀ y : G₀, orderOf y = 2 → 2 ^ 21 ∣ Nat.card (centralizer ({y} : Set G₀)) →
      IsConj y a₀)
    (hcard : 2 ^ 21 ∣ Nat.card G₀) :
    ∃ (E : Subgroup H₀) (p' ea eb ef : H₀),
      Φ c ∈ E ∧ (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      Nat.card E = 2048 ∧
      (∀ g : H₀, g * Φ c = Φ c * g → ∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧
      p' * Φ c = Φ c * p' ∧ orderOf p' = 11 ∧ (∀ x ∈ E, p' * x = x * p' → x = 1 ∨ x = Φ c) ∧
      ea ∈ E ∧ eb ∈ E ∧ ef ∈ E ∧ eb * (p' * eb * p'⁻¹) ≠ 1 ∧
      ∀ y : H₀, orderOf y = 2 → ¬ 2 ∣ (centralizer ({y} : Set H₀)).index →
        IsConj (ea * (p' * ea * p'⁻¹)) y ∧ IsConj (ef * (p' * ef * p'⁻¹)) y ∧
        IsConj (ea * (p' * ea * p'⁻¹) * (ef * (p' * ef * p'⁻¹))) y ∧
        ¬ IsConj (eb * (p' * eb * p'⁻¹)) y ∧ ¬ IsConj (eb * (p' * eb * p'⁻¹) * Φ c) y := by
  have hconj : ∀ {x y : G₀}, IsConj x y ↔ IsConj (Φ x) (Φ y) := by
    intro x y
    simp only [isConj_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨Φ g, by simp [map_mul, map_inv]⟩
    · rintro ⟨g, hg⟩
      refine ⟨Φ.symm g, Φ.injective ?_⟩
      simpa [map_mul, map_inv] using hg
  have hw : ∀ q : G₀, Φ (q * (p * q * p⁻¹)) = Φ q * (Φ p * Φ q * (Φ p)⁻¹) := fun q => by
    simp [map_mul, map_inv]
  have hmem : ∀ x : H₀, x ∈ Q.map Φ.toMonoidHom ↔ Φ.symm x ∈ Q := fun x => mem_map_equiv
  have hy : ∀ y : H₀, orderOf y = 2 → ¬ 2 ∣ (centralizer ({y} : Set H₀)).index →
      IsConj (Φ a₀) y := by
    intro y hy2 hyi
    have hcy : Nat.card (centralizer ({Φ.symm y} : Set G₀)) =
        Nat.card (centralizer ({y} : Set H₀)) := by
      rw [card_centralizer_equiv Φ (Φ.symm y), MulEquiv.apply_symm_apply]
    have hdvd : 2 ^ 21 ∣ Nat.card (centralizer ({Φ.symm y} : Set G₀)) := by
      rw [hcy]
      have h1 := (centralizer ({y} : Set H₀)).card_mul_index
      have hG : Nat.card H₀ = Nat.card G₀ := (Nat.card_congr Φ.toEquiv).symm
      rw [hG] at h1
      have h2 : 2 ^ 21 ∣ Nat.card (centralizer ({y} : Set H₀)) *
          (centralizer ({y} : Set H₀)).index := h1 ▸ hcard
      exact (Nat.Coprime.pow_left 21
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hyi)).dvd_of_dvd_mul_right h2
    have h := h2A (Φ.symm y) (by rw [MulEquiv.orderOf_eq, hy2]) hdvd
    rw [hconj, MulEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨Q.map Φ.toMonoidHom, Φ p, Φ qa, Φ qb, Φ qf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact (hmem _).mpr (by simpa using hcQ)
  · intro x hx
    rw [hmem] at hx
    have := congrArg Φ (hQ2 _ hx)
    simpa using this
  · intro x hx y hy'
    rw [hmem] at hx hy'
    have := congrArg Φ (hQc _ hx _ hy')
    simpa using this
  · rw [card_map_of_injective Φ.injective, hQcard]
  · intro g hg x hx
    rw [hmem] at hx ⊢
    have hg' : Φ.symm g * c = c * Φ.symm g := Φ.injective (by simpa using hg)
    simpa using hQn _ hg' _ hx
  · rw [← map_mul, ← map_mul, hpc]
  · rw [MulEquiv.orderOf_eq, hp11]
  · intro x hx hpx
    rw [hmem] at hx
    have h1 : p * Φ.symm x = Φ.symm x * p := Φ.injective (by simpa using hpx)
    rcases hpfix _ hx h1 with h | h
    · left
      simpa using congrArg Φ h
    · right
      simpa using congrArg Φ h
  · exact (hmem _).mpr (by simpa using hqa)
  · exact (hmem _).mpr (by simpa using hqb)
  · exact (hmem _).mpr (by simpa using hqf)
  · rw [← hw]
    exact fun h => hb1 (Φ.injective (by rw [h, map_one]))
  · intro y hy2 hyi
    have hya := hy y hy2 hyi
    refine ⟨?_, ?_, ?_, fun h => hb ?_, fun h => hbc ?_⟩
    · rw [← hw]
      exact (hconj.mp ha).trans hya
    · rw [← hw]
      exact (hconj.mp hf).trans hya
    · rw [← hw, ← hw, ← map_mul]
      exact (hconj.mp haf).trans hya
    · rw [hconj, hw]
      exact h.trans hya.symm
    · rw [hconj, map_mul, hw]
      exact h.trans hya.symm

theorem co1_twoC_data
    {v : Blueprint.NativeSporadic.Co1} (hv : orderOf v = 2)
    (hcv : Nat.card (centralizer ({v} : Set Blueprint.NativeSporadic.Co1)) = 389283840) :
    ∃ (E : Subgroup Blueprint.NativeSporadic.Co1) (p ea eb ef : Blueprint.NativeSporadic.Co1),
      v ∈ E ∧ (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      Nat.card E = 2048 ∧
      (∀ g : Blueprint.NativeSporadic.Co1, g * v = v * g → ∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧
      p * v = v * p ∧ orderOf p = 11 ∧ (∀ x ∈ E, p * x = x * p → x = 1 ∨ x = v) ∧
      ea ∈ E ∧ eb ∈ E ∧ ef ∈ E ∧ eb * (p * eb * p⁻¹) ≠ 1 ∧
      ∀ y : Blueprint.NativeSporadic.Co1, orderOf y = 2 →
        ¬ 2 ∣ (centralizer ({y} : Set Blueprint.NativeSporadic.Co1)).index →
        IsConj (ea * (p * ea * p⁻¹)) y ∧ IsConj (ef * (p * ef * p⁻¹)) y ∧
        IsConj (ea * (p * ea * p⁻¹) * (ef * (p * ef * p⁻¹))) y ∧
        ¬ IsConj (eb * (p * eb * p⁻¹)) y ∧ ¬ IsConj (eb * (p * eb * p⁻¹) * v) y := by
  have hcardC : ∀ {x w : GA}, IsConj x w →
      Nat.card (centralizer ({x} : Set GA)) = Nat.card (centralizer ({w} : Set GA)) := by
    intro x w hxw
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxw
    exact card_centralizer_equiv (MulAut.conj c) x
  have hvG : IsConj cC (co1MatEquiv v) := by
    have h2 : orderOf (co1MatEquiv v) = 2 := by rw [orderOf_co1MatEquiv, hv]
    have hc : Nat.card (centralizer ({co1MatEquiv v} : Set GA)) = 389283840 := by
      rw [← card_centralizer_co1, hcv]
    rcases involution_classes.1 _ h2 with h | h | h
    · rw [hcardC h, card_centralizer_GA, coe_aC, card_cent_aG] at hc
      norm_num at hc
    · exact h.symm
    · rw [hcardC h, card_cent_a₁] at hc
      norm_num at hc
  obtain ⟨γ, hγ⟩ := isConj_iff.mp hvG
  have hQGA : twoCQ ≤ GA := fun q hq => (mem_inf.mp (twoCQ_le hq)).1
  have hmemQ : ∀ x : GA, x ∈ twoCQ.subgroupOf GA ↔ (x : GL24) ∈ twoCQ := fun x => mem_subgroupOf
  have hcQ : cG ∈ twoCQ := twoC_selfCentralizing cG (mem_inf.mpr ⟨iotaC_mem_GA,
    mem_cent_GL.2 rfl⟩) fun q hq =>
      (mem_cent_GL.1 (mem_inf.mp (twoCQ_le hq)).2).symm
  have hpGA : holtFreePG ∈ GA := (mem_inf.mp holtFreePG_mem).1
  have hpC : holtFreePG * cG = cG * holtFreePG := mem_cent_GL.1 (mem_inf.mp holtFreePG_mem).2
  have hq : ∀ l < 11, twoCQg l ∈ twoCQ := fun l hl => by
    rw [twoCQ_eq]
    exact subset_closure ⟨l, hl, rfl⟩
  have hrepq : ∀ l < 11, MRep (twoCQRows.getD l Native.one) (twoCQg l) := fun l hl =>
    qRep_twoC l (by rw [twoCQRows_length]; exact hl)
  have hwQ : ∀ {q : GL24}, q ∈ twoCQ → holtFreeWG q ∈ twoCQ := fun hq' =>
    twoCQ.mul_mem hq' (twoCQ_normal _ holtFreePG_mem _ hq')
  obtain ⟨pA, hpA⟩ : ∃ pA : GA, (pA : GL24) = holtFreePG := ⟨⟨holtFreePG, hpGA⟩, rfl⟩
  have hw : ∀ (q : GA), ((q * (pA * q * pA⁻¹) : GA) : GL24) = holtFreeWG q := fun q => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hpA]
    rfl
  obtain ⟨qa, hqa⟩ : ∃ q : GA, (q : GL24) = twoCQg Data.aIdx :=
    ⟨⟨_, hQGA (hq _ (by decide))⟩, rfl⟩
  obtain ⟨qb, hqb⟩ : ∃ q : GA, (q : GL24) = twoCQg Data.bIdx :=
    ⟨⟨_, hQGA (hq _ (by decide))⟩, rfl⟩
  obtain ⟨qf, hqf⟩ : ∃ q : GA, (q : GL24) = twoCQg Data.fIdx :=
    ⟨⟨_, hQGA (hq _ (by decide))⟩, rfl⟩
  have hcls := fun (x : GA) (hx : (x : GL24) ∈ twoCQ) => isConj_of_ncard_fix (x := x)
    (twoCQ_sq hx)
  have hrA : MRep holtFreeA (holtFreeWG (twoCQg Data.aIdx)) := by
    unfold holtFreeA
    exact rep_holtFreeW (hrepq _ (by decide))
  have hrB : MRep holtFreeB (holtFreeWG (twoCQg Data.bIdx)) := by
    unfold holtFreeB
    exact rep_holtFreeW (hrepq _ (by decide))
  have hrF : MRep holtFreeF (holtFreeWG (twoCQg Data.fIdx)) := by
    unfold holtFreeF
    exact rep_holtFreeW (hrepq _ (by decide))
  obtain ⟨hc1, -, hc2, hc3, hc4, hc5, hc6⟩ := Certificates.certificate15094
  have hfa : (xFix (holtFreeWG (twoCQg Data.aIdx))).ncard = 2280 := by
    rw [ncard_fix_certX hrA]
    exact hc2
  have hfb : (xFix (holtFreeWG (twoCQg Data.bIdx))).ncard = 264 := by
    rw [ncard_fix_certX hrB]
    exact hc3
  have hfbc : (xFix (holtFreeWG (twoCQg Data.bIdx) * cG)).ncard = 264 := by
    rw [ncard_fix_certX (hrB.mul rep_iotaC)]
    exact hc4
  have hff : (xFix (holtFreeWG (twoCQg Data.fIdx))).ncard = 2280 := by
    rw [ncard_fix_certX hrF]
    exact hc5
  have hfaf : (xFix (holtFreeWG (twoCQg Data.aIdx) * holtFreeWG (twoCQg Data.fIdx))).ncard =
      2280 := by
    rw [ncard_fix_certX (hrA.mul hrF)]
    exact hc6
  have hnac : ¬ IsConj aC cC := involution_classes.2.1
  have hcardGA : 2 ^ 21 ∣ Nat.card GA := by
    rw [← Nat.card_congr co1MatEquiv.toEquiv, CFSG.Sporadic.Co1.card_Co1]
    norm_num
  have key := @transport_twoC GA Blueprint.NativeSporadic.Co1 (inferInstance : Group GA)
    (inferInstance : Group Blueprint.NativeSporadic.Co1)
    ((MulAut.conj γ).trans co1MatEquiv.symm) cC pA qa qb qf aC (twoCQ.subgroupOf GA)
    ((hmemQ _).mpr (by rw [coe_cC]; exact hcQ))
    (fun x hx => Subtype.ext (twoCQ_sq ((hmemQ x).mp hx)))
    (fun x hx y hy => Subtype.ext (twoCQ_comm ((hmemQ x).mp hx) ((hmemQ y).mp hy)))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hQGA).toEquiv, card_twoCQ])
    (fun g hg x hx => (hmemQ _).mpr (twoCQ_normal _ (mem_inf.mpr ⟨g.2,
      mem_cent_GL.2 (by
        have h := congrArg Subtype.val hg
        rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_cC] at h)⟩) _ ((hmemQ x).mp hx)))
    (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hpA, coe_cC]; exact hpC))
    (by rw [← Subgroup.orderOf_coe, hpA, orderOf_holtFreePG])
    (fun x hx hpx => by
      have hpx' : holtFreePG * (x : GL24) = (x : GL24) * holtFreePG := by
        have := congrArg Subtype.val hpx
        rwa [Subgroup.coe_mul, Subgroup.coe_mul, hpA] at this
      rcases holtFreePG_fix ((hmemQ x).mp hx) hpx' with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (by rw [coe_cC]; exact h)))
    ((hmemQ _).mpr (hqa ▸ hq _ (by decide))) ((hmemQ _).mpr (hqb ▸ hq _ (by decide)))
    ((hmemQ _).mpr (hqf ▸ hq _ (by decide)))
    ((hcls _ (by rw [hw, hqa]; exact hwQ (hq _ (by decide)))).1 (by rw [hw, hqa]; exact hfa))
    ((hcls _ (by rw [hw, hqf]; exact hwQ (hq _ (by decide)))).1 (by rw [hw, hqf]; exact hff))
    ((hcls _ (by
        rw [Subgroup.coe_mul, hw, hw, hqa, hqf]
        exact twoCQ.mul_mem (hwQ (hq _ (by decide))) (hwQ (hq _ (by decide))))).1
      (by rw [Subgroup.coe_mul, hw, hw, hqa, hqf]; exact hfaf))
    (fun h => hnac (h.symm.trans ((hcls _ (by rw [hw, hqb]; exact hwQ (hq _ (by decide)))).2
      (by rw [hw, hqb]; exact hfb))))
    (fun h => hnac (h.symm.trans ((hcls _ (by
        rw [Subgroup.coe_mul, hw, hqb, coe_cC]
        exact twoCQ.mul_mem (hwQ (hq _ (by decide))) hcQ)).2
      (by rw [Subgroup.coe_mul, hw, hqb, coe_cC]; exact hfbc))))
    (fun h1 => by
      have h2 := hfb
      rw [← hqb, ← hw, h1, Subgroup.coe_one, ncard_xFix_one] at h2
      omega)
    (fun y hy h2 => isConj_aC_of_two_pow hy h2) hcardGA
  have hΦc : ((MulAut.conj γ).trans co1MatEquiv.symm) cC = v := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, hγ, MulEquiv.symm_apply_apply]
  rw [hΦc] at key
  exact key

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
