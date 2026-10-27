module

public import CFSG.ClassicalInvolution.AschTight.Hall196Main
public import CFSG.ClassicalInvolution.AschTight.Hall196Wr

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem isSylow2In_sup_of_normalizes {W Y P : Subgroup G} (hP : IsSylow2In P Y)
    (hW2 : IsPGroup 2 W) (hWY : W ≤ Subgroup.normalizer (Y : Set G))
    (hWP : W ≤ Subgroup.normalizer (P : Set G)) (hWYP : W ⊓ Y ≤ P) :
    IsSylow2In (P ⊔ W) (W ⊔ Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨sup_le (hP.1.trans le_sup_right) le_sup_left,
    IsPGroup.to_sup_of_normal_left' hP.2.1 hW2 hWP, fun T hT hT2 hle => ?_⟩
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) :=
    hT.trans (sup_le hWY Subgroup.le_normalizer)
  have h1 := card_sup_mul_card_inf' (A := Y) (C := T) hTY
  have h2 := card_sup_mul_card_inf' (A := Y) (C := W) hWY
  have h3 := card_sup_mul_card_inf' (A := P) (C := W) hWP
  have h4 : Nat.card ↥(Y ⊔ T) ≤ Nat.card ↥(Y ⊔ W) :=
    Subgroup.card_le_of_le (sup_le le_sup_left (sup_comm W Y ▸ hT))
  have h5 : Nat.card ↥(Y ⊓ T) ≤ Nat.card P :=
    hP.natCard_le (hT2.to_le inf_le_right) inf_le_left
  have h6 : Y ⊓ W = P ⊓ W := by
    refine le_antisymm (fun x hx => ⟨hWYP ⟨hx.2, hx.1⟩, hx.2⟩) (fun x hx => ⟨hP.1 hx.1, hx.2⟩)
  rw [h6] at h2
  have hd : 0 < Nat.card ↥(P ⊓ W) := Nat.card_pos
  have hY : 0 < Nat.card Y := Nat.card_pos
  have key : Nat.card Y * Nat.card ↥(P ⊓ W) * Nat.card T ≤
      Nat.card Y * Nat.card ↥(P ⊓ W) * Nat.card ↥(P ⊔ W) := by
    calc Nat.card Y * Nat.card ↥(P ⊓ W) * Nat.card T
        = (Nat.card Y * Nat.card T) * Nat.card ↥(P ⊓ W) := by ring
      _ = Nat.card ↥(Y ⊔ T) * Nat.card ↥(Y ⊓ T) * Nat.card ↥(P ⊓ W) := by rw [h1]
      _ ≤ Nat.card ↥(Y ⊔ W) * Nat.card P * Nat.card ↥(P ⊓ W) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul h4 h5)
      _ = (Nat.card ↥(Y ⊔ W) * Nat.card ↥(P ⊓ W)) * Nat.card P := by ring
      _ = Nat.card Y * (Nat.card P * Nat.card W) := by rw [h2]; ring
      _ = Nat.card Y * (Nat.card ↥(P ⊔ W) * Nat.card ↥(P ⊓ W)) := by rw [h3]
      _ = Nat.card Y * Nat.card ↥(P ⊓ W) * Nat.card ↥(P ⊔ W) := by ring
  have hcard := Nat.le_of_mul_le_mul_left key (Nat.mul_pos hY hd)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

omit [Finite G] in
theorem le_normalizer_inf {S Y W : Subgroup G} (hWS : W ≤ S)
    (hWY : W ≤ Subgroup.normalizer (Y : Set G)) :
    W ≤ Subgroup.normalizer ((S ⊓ Y : Subgroup G) : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hwS := hWS hw
  have hwY := Subgroup.mem_normalizer_iff.mp (hWY hw) x
  constructor
  · rintro ⟨hxS, hxY⟩
    exact ⟨S.mul_mem (S.mul_mem hwS hxS) (S.inv_mem hwS), hwY.mp hxY⟩
  · rintro ⟨hxS, hxY⟩
    refine ⟨?_, hwY.mpr hxY⟩
    have e : x = w⁻¹ * (w * x * w⁻¹) * w := by group
    rw [e]
    exact S.mul_mem (S.mul_mem (S.inv_mem hwS) hxS) hwS

theorem c19_6_cases_aux [IsSimpleGroup G] (hstar : C19_11aTmp p f)
    {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data p f K z S W)
    (hnd : ¬ IsDihedralSub ((S : Subgroup G) ⊓ sec19Y K z)) :
    (W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W ∧
        (S : Subgroup G) ⊓ sec19Y K z = W ⊓ sec19Y K z) ∨
      (IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z) ∧
        Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = 2 * Nat.card ↥(W ⊓ sec19Y K z) ∧
        Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = Nat.card ↥((S : Subgroup G) ⊓ K) ∧
        ∀ Q : Subgroup G, IsSylow2In Q (W ⊔ sec19Y K z) → IsWreathed Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, t, V, hDT⟩ := exists_sec19DataT hd
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  have hSY : (S : Subgroup G) ≤ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G) :=
    hd.hSz.trans (centralizer_le_normalizer_sec19Y hd.tight)
  have hP := isSylow2In_inf_of_le_normalizer S hSY
  obtain ⟨-, -, -, hVcyc, -⟩ := hDT.memV
  have hcomm : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, ∀ w ∈ W,
      x * w * x⁻¹ * w⁻¹ ∈ W ⊓ sec19Y K z := by
    intro x hx w hw
    refine ⟨W.mul_mem ((Subgroup.mem_normalizer_iff.mp (ef.normalizes hx) w).mp hw)
      (W.inv_mem hw), ?_⟩
    have hw' : w * x⁻¹ * w⁻¹ ∈ sec19Y K z := by
      rw [← conjSub_sec19Y hd.tight (hd.hSz (hd.hWS hw))]
      exact conj_mem_conjSub (Subgroup.inv_mem _ hx.2)
    have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx.2 hw'
  have hstar' := fun x hx hxt => mem_inf_of_commute hstar hDT ef (x := x) hx hxt
  have hCP : W ⊓ sec19Y K z ≤ (S : Subgroup G) ⊓ sec19Y K z := inf_le_inf_right _ hd.hWS
  have hC4 : 4 ≤ Nat.card ↥(W ⊓ sec19Y K z) := ef.card ▸ ef.four
  have hC2 : IsPGroup 2 ↥(W ⊓ sec19Y K z) := S.isPGroup'.to_le (inf_le_left.trans hd.hWS)
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hDT.leW.trans hd.hWS)
  by_cases hPC : (S : Subgroup G) ⊓ sec19Y K z ≤ W ⊓ sec19Y K z
  · left
    have hPeq := le_antisymm hPC hCP
    refine ⟨sup_eq_oddCoreOf_sup_of_isCyclic hP (hPeq ▸ ef.cyclic) (hPC.trans inf_le_left),
      hPeq⟩
  right
  obtain ⟨q, hqP, hqC, zc, hzcC, hzc1, hzc2, -, hqt, hqinv, -, hq2, hcoset, hcardP, hsurj⟩ :=
    exists_swap_of_not_le ef.comm hDT.leW inf_le_left ef.cyclic hVcyc ef.card.symm hC4 hC2 hV2
      hDT.memT hDT.invL.ne_one hDT.invL.sq hCP ef.normalizes hcomm hstar' hPC
  have hqk := isQuaternionSub_of_swap ef.cyclic hC4 hC2 hCP hqP hzcC hzc1 hzc2 hqinv hcoset
    hcardP
  have hq2' : q * q = zc := hq2.resolve_left fun h => hnd (hqk.2 h)
  have hcardSK : Nat.card ↥((S : Subgroup G) ⊓ K) = 2 * Nat.card ↥(W ⊓ sec19Y K z) := by
    rw [S1911.card_inf_eq hd, S1911.card_inf_eq_card hDT, ← ef.card]
  refine ⟨hqk.1 hq2', hcardP, hcardP.trans hcardSK.symm, fun Q hQ => ?_⟩
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  have hWY : W ≤ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G) := hd.hWS.trans hSY
  have hWP := le_normalizer_inf hd.hWS hWY
  have hsyl := isSylow2In_sup_of_normalizes hP hW2 hWY hWP hCP
  refine IsWreathed.of_isSylow2In hsyl ?_ hQ
  obtain ⟨v₀, hv₀⟩ := hVcyc.exists_generator
  have hVv : V = Subgroup.zpowers (v₀ : G) := eq_zpowers_of_generator hv₀
  have hvo : orderOf (v₀ : G) = Nat.card V := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hv₀]
  have htW : t ∈ W := hDT.leW hDT.memT
  have hzcW : zc ∈ W := hzcC.1
  have hqN := ef.normalizes hqP
  have hbW : ∀ w ∈ W, (t * q) * w * (t * q)⁻¹ = q * w * q⁻¹ := by
    intro w hw
    have hqw : q * w * q⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hqN w).mp hw
    have h1 := ef.comm t htW _ hqw
    calc (t * q) * w * (t * q)⁻¹ = t * (q * w * q⁻¹) * t⁻¹ := by group
      _ = q * w * q⁻¹ * t * t⁻¹ := by rw [h1]
      _ = q * w * q⁻¹ := by group
  have hb2 : (t * q) * (t * q) = 1 := by
    have h1 : q * t = zc * t * q := by
      calc q * t = q * t * q⁻¹ * q := by group
        _ = zc * t * q := by rw [hqt]
    have h2 := ef.comm t htW zc hzcW
    calc (t * q) * (t * q) = t * (q * t) * q := by group
      _ = t * (zc * t * q) * q := by rw [h1]
      _ = (t * zc) * t * (q * q) := by group
      _ = (zc * t) * t * (q * q) := by rw [h2]
      _ = zc * (t * t) * zc := by rw [hq2']; group
      _ = 1 := by rw [hDT.invL.sq, mul_one, hzc2]
  have hbP : t * q ∈ (S : Subgroup G) ⊓ sec19Y K z ⊔ W :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right htW) (Subgroup.mem_sup_left hqP)
  have hv₀W : (v₀ : G) ∈ W := hDT.leW v₀.2
  have hcW : (t * q) * v₀ * (t * q)⁻¹ ∈ W := by
    rw [hbW _ hv₀W]
    exact (Subgroup.mem_normalizer_iff.mp hqN _).mp hv₀W
  have hCV : W ⊓ sec19Y K z ≤ Subgroup.normalizer (V : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have key : ∀ y ∈ W, c * y * c⁻¹ = y := fun y hy => by
      rw [ef.comm c hc.1 y hy]
      group
    constructor
    · intro hv
      rw [key v (hDT.leW hv)]
      exact hv
    · intro hv
      have hv' : v ∈ W := by
        have e : v = c⁻¹ * (c * v * c⁻¹) * c := by group
        rw [e]
        exact W.mul_mem (W.mul_mem (W.inv_mem hc.1) (hDT.leW hv)) hc.1
      rwa [key v hv'] at hv
  have hWcard : Nat.card W = Nat.card V * Nat.card ↥(W ⊓ sec19Y K z) := by
    have h := card_sup_mul_card_inf' hCV
    have hbot : V ⊓ (W ⊓ sec19Y K z) = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_left V inf_le_right).trans ef.disj.le)
    rw [← ef.sup_eq, hbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hPW : (S : Subgroup G) ⊓ sec19Y K z ⊓ W = W ⊓ sec19Y K z := by
    ext x
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hd.hWS h.1, h.2⟩, h.1⟩⟩
  have hTcard : Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z ⊔ W) = 2 * orderOf (v₀ : G) ^ 2 := by
    have h := card_sup_mul_card_inf' hWP
    rw [hPW, hcardP, hWcard, ef.card] at h
    have hpos : 0 < Nat.card V := Nat.card_pos
    rw [hvo, _root_.sq]
    have h' : Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z ⊔ W) * Nat.card V =
        (2 * (Nat.card V * Nat.card V)) * Nat.card V := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  refine ⟨v₀, (t * q) * v₀ * (t * q)⁻¹, t * q, by rw [hvo]; exact ef.four, ?_,
    ef.comm _ hv₀W _ hcW, hTcard, hb2, rfl, ?_, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  · calc (t * q) * ((t * q) * v₀ * (t * q)⁻¹) * (t * q)⁻¹ =
        ((t * q) * (t * q)) * v₀ * ((t * q) * (t * q))⁻¹ := by group
      _ = v₀ := by rw [hb2]; group
  ·
    set cl := Subgroup.closure {(v₀ : G), (t * q) * v₀ * (t * q)⁻¹, t * q} with hcl
    have hv₀cl : (v₀ : G) ∈ cl := Subgroup.subset_closure (Set.mem_insert _ _)
    have hbcl : t * q ∈ cl :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    have hVcl : V ≤ cl := hVv ▸ Subgroup.zpowers_le.mpr hv₀cl
    have hCcl : W ⊓ sec19Y K z ≤ cl := by
      intro c hc
      obtain ⟨v, hv, hvc⟩ := hsurj c hc
      rw [← hvc, ← hbW v (hDT.leW hv)]
      exact cl.mul_mem (cl.inv_mem (hVcl hv))
        (cl.mul_mem (cl.mul_mem hbcl (hVcl hv)) (cl.inv_mem hbcl))
    have hqcl : q ∈ cl := by
      have e : q = t⁻¹ * (t * q) := by group
      rw [e]
      exact cl.mul_mem (cl.inv_mem (hVcl hDT.memT)) hbcl
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) (sup_le (fun x hx => ?_) ?_)
    · rintro y (rfl | rfl | rfl)
      · exact Subgroup.mem_sup_right hv₀W
      · exact Subgroup.mem_sup_right hcW
      · exact hbP
    · by_cases hxC : x ∈ W ⊓ sec19Y K z
      · exact hCcl hxC
      · have h1 := hcoset x hx hxC
        have e : x = q * (q⁻¹ * x) := by group
        rw [e]
        exact cl.mul_mem hqcl (hCcl h1)
    · rw [ef.sup_eq]
      exact sup_le hVcl hCcl

variable (p f) in
theorem c19_6_cases [IsSimpleGroup G] (hstar : C19_11aTmp p f) (hdih : C19_6DihTmp p f)
    {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data p f K z S W) :
    (W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W ∧
        (S : Subgroup G) ⊓ sec19Y K z = W ⊓ sec19Y K z) ∨
      (IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z) ∧
        Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = 2 * Nat.card ↥(W ⊓ sec19Y K z) ∧
        Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = Nat.card ↥((S : Subgroup G) ⊓ K) ∧
        ∀ Q : Subgroup G, IsSylow2In Q (W ⊔ sec19Y K z) → IsWreathed Q) :=
  c19_6_cases_aux hstar hd (hdih G K z S W hd)

omit [Finite G] in
theorem not_isDihedralSub_of_isQuaternionSub {P : Subgroup G} (hQ : IsQuaternionSub P) :
    ¬ IsDihedralSub P := by
  rintro ⟨a, b, ha4, -, hb2, hbab, hcl⟩
  have haP : a ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  have hbP : b ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have ha1 : a ≠ a⁻¹ := by
    intro h
    have h2 : a ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel a
    have := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h2)
    omega
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply ha1
    simpa using hbab
  have hba2 : b * a * (b * a) = 1 := by
    calc b * a * (b * a) = (b * a * b⁻¹) * a := by rw [hbinv]; group
      _ = 1 := by rw [hbab]; group
  have hba1 : b * a ≠ 1 := by
    intro h
    have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_left h
    apply ha1
    rw [← hbab, hb]
    group
  have hne : b ≠ b * a := by
    intro h
    apply ha1
    have : a = 1 := by simpa using h.symm
    rw [this, inv_one]
  exact hne (IsQuaternionSub.eq_of_mul_self_eq_one hQ hbP (P.mul_mem hbP haP) hb2 hba2 hb1 hba1)

variable (p f) in
theorem c19_6_cases_of_quat [IsSimpleGroup G] (hstar : C19_11aTmp p f) {K : Subgroup G} {z : G}
    {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data p f K z S W)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) :
    Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = 2 * Nat.card ↥(W ⊓ sec19Y K z) ∧
      Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = Nat.card ↥((S : Subgroup G) ⊓ K) ∧
      ∀ Q : Subgroup G, IsSylow2In Q (W ⊔ sec19Y K z) → IsWreathed Q := by
  rcases c19_6_cases_aux hstar hd (not_isDihedralSub_of_isQuaternionSub hQ) with
    ⟨-, hPC⟩ | ⟨-, h1, h2, h3⟩
  · exfalso
    obtain ⟨L, t, V, hDT⟩ := exists_sec19DataT hd
    have ef := S1911.etaYForm p f G K z S W L t V hDT
    obtain ⟨a, b, ha4, -, -, hbab, hcl⟩ := hQ
    have haP : a ∈ (S : Subgroup G) ⊓ sec19Y K z := hcl ▸ Subgroup.subset_closure (by simp)
    have hbP : b ∈ (S : Subgroup G) ⊓ sec19Y K z := hcl ▸ Subgroup.subset_closure (by simp)
    rw [hPC] at haP hbP
    have hab := ef.comm a haP.1 b hbP.1
    have h2 : a ^ 2 = 1 := by
      have e : a⁻¹ = a := by
        rw [← hbab]
        calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [hab]
          _ = a := by group
      rw [sq]
      nth_rewrite 2 [← e]
      exact mul_inv_cancel a
    have := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h2)
    omega
  · exact ⟨h1, h2, h3⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
