module

public import Certificates.Data.Kernel.S1277KVl
public import CFSG.Certificates.Kernel.S1277KFrSound
public import CFSG.Certificates.Kernel.S1277KSvSound

public section

namespace CFSG.KS.S1277Vl

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Cand CFSG.KC.S1277Gm
  CFSG.KC.S1277Sv CFSG.KC.S1277Fr CFSG.KC.S1277Vl CFSG.KC.Enum CFSG.KS.S1277Lat CFSG.KS.S1277Mod
  CFSG.KS.S1277Sig CFSG.KS.S1277Gm CFSG.KS.S1277Cand CFSG.KS.S1277Fr CFSG.KS.S1277Sv
  CFSG.Quasithin.H13.I1277 Certificates.Data.S1277Surv Certificates.Data.S1277Sig
open CFSG.Open
open scoped commutatorElement

theorem testBit_two_or {a b x : ℕ} (h : (1 <<< a ||| 1 <<< b).testBit x = true) : x = a ∨ x = b := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow,
    Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem testBit_two_or_right (a b : ℕ) : (1 <<< a ||| 1 <<< b).testBit b = true := by
  simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self]

section E

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem e_sound (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e0 : ℕ}
    (hN : nodeChk M kg m gs ts e0 = true) (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {p TP d : ℕ} {pg pr pt ws : List ℕ}
    (hfr : frChk M m gs ts p pg pr pt TP d ws = true) {zc : ℕ} (he : eChk M gs ts p zc = true)
    {z : G} (hzK : z ∈ K) (hzc : κ z = zc) :
    z ∈ Phi' Q ∧ (∀ r ∈ Phi' Q, r = 1 ∨ r = z) ∧ z ≠ 1 ∧
      (∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x = 1 ∨ x = z) ∧
      ∃ a ∈ Q, ∃ b ∈ Q, a * b * a⁻¹ * b⁻¹ = z := by
  obtain ⟨-, -, -, -, f5, -, -, -⟩ := fr_sound hκ hN hQK hQN hfr
  rw [eChk] at he
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
  obtain ⟨⟨⟨hp, hz1⟩, hcen⟩, hcomm⟩ := he
  have hp' := Nat.eq_of_beq_eq_true hp
  have hPK : Phi' Q ≤ K := (Phi'_le Q).trans hQK
  have hΦ : ∀ r ∈ Phi' Q, r = 1 ∨ r = z := by
    intro r hr
    have hb : p.testBit (κ r) = true := (f5 _).2 ⟨r, hr, rfl⟩
    rw [hp'] at hb
    rcases testBit_two_or hb with h | h
    · exact Or.inl (hκ.inj _ (hPK hr) _ K.one_mem (h.trans hκ.one.symm))
    · exact Or.inr (hκ.inj _ (hPK hr) _ hzK (h.trans hzc.symm))
  have hzΦ : z ∈ Phi' Q := by
    have hb : p.testBit zc = true := by rw [hp']; exact testBit_two_or_right _ _
    obtain ⟨r, hr, hrz⟩ := (f5 _).1 hb
    rw [← hκ.inj _ (hPK hr) _ hzK (hrz.trans hzc.symm)]
    exact hr
  have hzne : z ≠ 1 := by
    intro h
    rw [h, hκ.one] at hzc
    rw [hzc] at hz1
    exact absurd hz1 (by simp)
  refine ⟨hzΦ, hΦ, hzne, fun x hx hxc => ?_, ?_⟩
  · have hxl := mem_nodeL hN ((hQN _).1 ⟨x, hx, rfl⟩)
    have h := (allL_iff.1 hcen) _ hxl
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨r, hr, hrx⟩ := (f5 _).1 h
      rw [← hκ.inj _ (hPK hr) _ (hQK hx) hrx]
      exact hΦ r hr
    · exfalso
      rw [Bool.not_eq_true'] at h
      have : allL gs (fun g => Nat.beq (M.mul (κ x) g) (M.mul g (κ x))) = true := by
        refine allL_iff.2 fun g hg => ?_
        obtain ⟨y, hy, rfl⟩ := (hQN g).2 (node_gens hN hg)
        rw [← hκ.mul _ (hQK hx) _ (hQK hy), ← hκ.mul _ (hQK hy) _ (hQK hx), hxc y hy]
        exact Nat.beq_refl _
      rw [this] at h
      exact absurd h (by simp)
  · by_contra hno
    have hall : allL gs (fun a => allL gs fun b => !Nat.beq (mcomm M a b) zc) = true := by
      refine allL_iff.2 fun a ha => allL_iff.2 fun b hb => ?_
      obtain ⟨qa, hqa, rfl⟩ := (hQN a).2 (node_gens hN ha)
      obtain ⟨qb, hqb, rfl⟩ := (hQN b).2 (node_gens hN hb)
      have hK : qa * qb * qa⁻¹ * qb⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.mul_mem (hQK hqa) (hQK hqb)) (K.inv_mem (hQK hqa)))
          (K.inv_mem (hQK hqb))
      rw [Bool.not_eq_true', ← MCod.comm hκ (hQK hqa) (hQK hqb), ← hzc]
      cases h : Nat.beq (κ (qa * qb * qa⁻¹ * qb⁻¹)) (κ z) with
      | false => rfl
      | true =>
        exact absurd (hκ.inj _ hK _ hzK (Nat.eq_of_beq_eq_true h)) fun e =>
          hno ⟨qa, hqa, qb, hqb, e⟩
    rw [hall] at hcomm
    exact absurd hcomm (by simp)

end E

section Extra

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {d : ℕ}

theorem extraspecial_of (hQ2 : IsPGroup 2 ↥Q) (D : FrData H Q (Phi' Q) d) {z : G}
    (hzΦ : z ∈ Phi' Q) (hΦ : ∀ r ∈ Phi' Q, r = 1 ∨ r = z) (hz1 : z ≠ 1)
    (hcen : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x = 1 ∨ x = z)
    (hcm : ∃ a ∈ Q, ∃ b ∈ Q, a * b * a⁻¹ * b⁻¹ = z) (hzQ : ∀ q ∈ Q, q * z = z * q) :
    IsExtraspecialPGroup 2 ↥Q := by
  classical
  have hzQm : z ∈ Q := Phi'_le Q hzΦ
  have hzz : z * z = 1 := by
    rcases hΦ (z ^ 2) (sq_mem_Phi' hzQm) with h | h
    · rwa [pow_two] at h
    · exfalso
      apply hz1
      have : z * z = z * 1 := by rw [← pow_two, h, mul_one]
      exact mul_left_cancel this
  let zQ : ↥Q := ⟨z, hzQm⟩
  have hzQsq : zQ * zQ = 1 := Subtype.ext hzz
  have hzQ1 : zQ ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hmemZ : ∀ y : ↥Q, y ∈ Subgroup.zpowers zQ ↔ (y : G) = 1 ∨ (y : G) = z := by
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hsq : zQ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzQsq
      have hk : zQ ^ k = zQ ^ (k % 2) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
        rw [zpow_add, zpow_mul, hsq, one_zpow, mul_one]
      rw [hk]
      have h2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases h2 with h | h
      · left
        rw [h, zpow_zero]
        rfl
      · right
        rw [h, zpow_one]
    · rintro (h | h)
      · have : y = 1 := Subtype.ext h
        rw [this]
        exact Subgroup.one_mem _
      · have : y = zQ := Subtype.ext h
        rw [this]
        exact Subgroup.mem_zpowers _
  have hΦz : ∀ y : ↥Q, (y : G) ∈ Phi' Q → y ∈ Subgroup.zpowers zQ := fun y hy =>
    (hmemZ y).2 (hΦ _ hy)
  have hcenter : Subgroup.center ↥Q = Subgroup.zpowers zQ := by
    apply _root_.le_antisymm
    · intro x hx
      rw [Subgroup.mem_center_iff] at hx
      refine (hmemZ x).2 (hcen x.1 x.2 fun y hy => ?_)
      exact (congrArg Subtype.val (hx ⟨y, hy⟩)).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzQ g.1 g.2)
  have hcomm : commutator ↥Q = Subgroup.zpowers zQ := by
    apply _root_.le_antisymm
    · rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 ?_
      intro a _ b _
      apply hΦz
      have := comm_mem_Phi' a.2 b.2
      simpa [commutatorElement_def] using this
    · rw [Subgroup.zpowers_le]
      obtain ⟨a, ha, b, hb, hab⟩ := hcm
      have hz' : (⁅(⟨a, ha⟩ : ↥Q), ⟨b, hb⟩⁆ : ↥Q) = zQ := Subtype.ext (by
        simpa [commutatorElement_def] using hab)
      rw [← hz', _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hfratt : frattini ↥Q = Subgroup.zpowers zQ := by
    apply _root_.le_antisymm
    · intro x hx
      exact hΦz x (D.frattini_le hx)
    · rw [Subgroup.zpowers_le]
      exact Phi'_frattini hQ2 z hzΦ
  have hcard : Nat.card (Subgroup.center ↥Q) = 2 := by
    rw [hcenter, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzQsq) hzQ1
  exact ⟨hQ2, hcomm.trans hcenter.symm, hfratt.trans hcenter.symm, hcard⟩

end Extra

theorem inSp_iff {u : List ℕ} {x : ℕ} : inSp u x = true ↔ ∃ e < 8, cmb u e = x := by
  rw [inSp, Bool.not_eq_true']
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : allLt 8 (fun e => !Nat.beq (cmb u e) x) = true :=
      allLt_iff.2 fun e he => by
        rw [Bool.not_eq_true']
        cases hb : Nat.beq (cmb u e) x with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hb) (hn e he)
    rw [this] at h
    exact absurd h (by simp)
  · rintro ⟨e, he, rfl⟩
    cases hb : allLt 8 (fun e' => !Nat.beq (cmb u e') (cmb u e)) with
    | false => rfl
    | true =>
      have := (allLt_iff.1 hb) e he
      simp at this

theorem cmb_zero (u : List ℕ) : cmb u 0 = 0 := by simp [cmb]

theorem inSp_zero (u : List ℕ) : inSp u 0 = true := inSp_iff.2 ⟨0, by norm_num, cmb_zero u⟩

theorem cmb_lt {u : List ℕ} (hu : indChk u = true) (e : ℕ) : cmb u e < 64 := by
  rw [indChk] at hu
  simp only [Bool.and_eq_true] at hu
  have hl := Nat.eq_of_beq_eq_true hu.1.1
  have hlt : ∀ i < 3, u.getD i 0 < 64 := fun i hi => by
    have hi' : i < u.length := by omega
    rw [List.getD_eq_getElem u 0 hi']
    have := (allL_iff.1 hu.1.2) _ (List.getElem_mem hi')
    rwa [Nat.blt_eq] at this
  have hb : ∀ c b : ℕ, c < 64 → b < 2 → c * b < 64 := fun c b hc hb => by
    interval_cases b <;> omega
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  rw [cmb, h64]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_ <;> rw [← h64] <;>
    exact hb _ _ (hlt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))

theorem vlChk_spec {a u v : List ℕ} (h : vlChk a u v = true) :
    indChk u = true ∧ indChk v = true ∧
      (∀ x y, inSp u x = true → inSp u y = true → inSp u (x ^^^ y) = true) ∧
      (∀ x y, inSp v x = true → inSp v y = true → inSp v (x ^^^ y) = true) ∧
      (∀ x, inSp u x = true → inSp v x = true → x = 0) ∧
      (∀ c < 64, ∃ x, inSp u x = true ∧ inSp v (x ^^^ c) = true) ∧
      (∀ s ∈ a, ∀ x, inSp u x = true → inSp u (appP s x) = true) ∧
      (∀ s ∈ a, ∀ x, inSp v x = true → inSp v (appP s x) = true) ∧
      (∀ s ∈ a, (∀ i < 3, appP s (u.getD i 0) = u.getD i 0) → s = oneQ) := by
  rw [vlChk] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hu, hv⟩, hcl⟩, hint⟩, hcov⟩, hinv⟩, hker⟩ := h
  refine ⟨hu, hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨e, he, rfl⟩ := inSp_iff.1 hx
    obtain ⟨e', he', rfl⟩ := inSp_iff.1 hy
    have := (allLt_iff.1 ((allLt_iff.1 hcl) e he)) e' he'
    rw [Bool.and_eq_true] at this
    exact this.1
  · intro x y hx hy
    obtain ⟨e, he, rfl⟩ := inSp_iff.1 hx
    obtain ⟨e', he', rfl⟩ := inSp_iff.1 hy
    have := (allLt_iff.1 ((allLt_iff.1 hcl) e he)) e' he'
    rw [Bool.and_eq_true] at this
    exact this.2
  · intro x hx hxv
    obtain ⟨e, he, rfl⟩ := inSp_iff.1 hx
    have := (allLt_iff.1 hint) e he
    rw [Bool.or_eq_true] at this
    rcases this with h | h
    · rw [Nat.eq_of_beq_eq_true h, cmb_zero]
    · rw [hxv] at h
      exact absurd h (by simp)
  · intro c hc
    have := (allLt_iff.1 hcov) c hc
    rw [Bool.not_eq_true'] at this
    by_contra hn
    push Not at hn
    have h2 : allLt 8 (fun e => !inSp v (cmb u e ^^^ c)) = true :=
      allLt_iff.2 fun e he => by
        rw [Bool.not_eq_true']
        cases hb : inSp v (cmb u e ^^^ c) with
        | false => rfl
        | true => exact absurd hb (hn _ (inSp_iff.2 ⟨e, he, rfl⟩))
    rw [h2] at this
    exact absurd this (by simp)
  · intro s hs x hx
    obtain ⟨e, he, rfl⟩ := inSp_iff.1 hx
    have := (allLt_iff.1 ((allL_iff.1 hinv) s hs)) e he
    rw [Bool.and_eq_true] at this
    exact this.1
  · intro s hs x hx
    obtain ⟨e, he, rfl⟩ := inSp_iff.1 hx
    have := (allLt_iff.1 ((allL_iff.1 hinv) s hs)) e he
    rw [Bool.and_eq_true] at this
    exact this.2
  · intro s hs hfix
    have := (allL_iff.1 hker) s hs
    rw [Bool.or_eq_true] at this
    rcases this with h | h
    · exact Nat.eq_of_beq_eq_true h
    · exfalso
      have h2 : allLt 3 (fun i => Nat.beq (appP s (u.getD i 0)) (u.getD i 0)) = true :=
        allLt_iff.2 fun i hi => by rw [hfix i hi]; exact Nat.beq_refl _
      rw [h2] at h
      exact absurd h (by simp)

theorem val_eq_appP {φ : ℕ → ℕ} {σ : Equiv.Perm (Fin (2 ^ 6))} (hσ : σ ∈ Sig 6 φ)
    (x : Fin (2 ^ 6)) : (σ x).1 = appP (pk σ) x.1 := by
  rw [appP_eq_app6, app6_eq, unpackC_pk]
  exact applyCols_colsOf hσ.1 x

section AB

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem card_codes (hκ : MCod K M κ) {A : Subgroup G} (hAK : A ≤ K) {l : List ℕ} (hnd : l.Nodup)
    (hA : ∀ n, (∃ a ∈ A, κ a = n) ↔ n ∈ l) : Nat.card A = l.length := by
  let f : ↥A → {n : ℕ // n ∈ l} := fun x => ⟨κ x.1, (hA _).1 ⟨x.1, x.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (hκ.inj x.1 (hAK x.2) y.1 (hAK y.2) (congrArg Subtype.val h))
    · rintro ⟨n, hn⟩
      obtain ⟨x, hx, rfl⟩ := (hA n).2 hn
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  have e2 : {n : ℕ // n ∈ l} ≃ ↥l.toFinset := Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]

theorem nodeL_spec {kg gs ts : List ℕ} {m e : ℕ} (hN : nodeChk M kg m gs ts e = true) :
    (nodeL M ts).Nodup ∧ ∀ x, m.testBit x = true ↔ x ∈ nodeL M ts := by
  rw [nodeChk] at hN
  simp only [Bool.and_eq_true] at hN
  have htree := Nat.eq_of_beq_eq_true hN.1.1.1.2
  obtain ⟨hiff, hnd, hnew⟩ := treeF_bits htree (ne_zero_of_testBit hN.1.1.1.1)
  have hid : ∀ x, (idM M).testBit x = true ↔ x = M.one * 64 := fun x =>
    ⟨testBit_idM, fun h => by rw [h, idM, Nat.one_shiftLeft, Nat.testBit_two_pow_self]⟩
  refine ⟨List.nodup_cons.2 ⟨fun h => ?_, hnd⟩, fun x => ?_⟩
  · have := (hnew _ h).1
    rw [(hid _).2 rfl] at this
    exact absurd this (by simp)
  · rw [hiff, hid, nodeL, List.mem_cons]

theorem sub_sound (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e0 : ℕ}
    (hN : nodeChk M kg m gs ts e0 = true) (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {TP : ℕ}
    (D : FrData H Q (Phi' Q) 6) (hD : ∀ x, D.wc x = rd6 TP (κ x)) {u : List ℕ}
    (hcl : ∀ x y, inSp u x = true → inSp u y = true → inSp u (x ^^^ y) = true)
    (hab : abChk M ts TP u = true)
    (hH : ∀ h ∈ H, ∀ x ∈ Q, inSp u (D.wc x) = true → inSp u (D.wc (h * x * h⁻¹)) = true) :
    ∃ A : Subgroup G, (∀ x, x ∈ A ↔ x ∈ Q ∧ inSp u (D.wc x) = true) ∧ IsElemAbelian 2 A ∧
      Nat.card A = 16 ∧ H ≤ Subgroup.normalizer (A : Set G) := by
  classical
  obtain ⟨hnd, hmem⟩ := nodeL_spec hN
  rw [abChk, Bool.and_eq_true] at hab
  obtain ⟨hc16, hel⟩ := hab
  let A : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ inSp u (D.wc x) = true}
      one_mem' := ⟨Q.one_mem, by rw [D.wc_one]; exact inSp_zero u⟩
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
        rw [D.wc_mul _ ha.1 _ hb.1]; exact hcl _ _ ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [D.wc_inv ha.1]; exact ha.2⟩ }
  have hA : ∀ x, x ∈ A ↔ x ∈ Q ∧ inSp u (D.wc x) = true := fun x => Iff.rfl
  have hAK : A ≤ K := fun x hx => hQK ((hA x).1 hx).1
  have hcodes : ∀ n, (∃ a ∈ A, κ a = n) ↔
      n ∈ (nodeL M ts).filter fun x => inSp u (rd6 TP x) := by
    intro n
    rw [List.mem_filter]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨haQ, haN⟩ := (hA a).1 ha
      refine ⟨(hmem _).1 ((hQN _).1 ⟨a, haQ, rfl⟩), ?_⟩
      rw [← hD a]
      exact haN
    · rintro ⟨hn, hc⟩
      obtain ⟨q, hq, rfl⟩ := (hQN _).2 ((hmem _).2 hn)
      refine ⟨q, (hA q).2 ⟨hq, ?_⟩, rfl⟩
      rw [hD q]
      exact hc
  have hel' : ∀ x ∈ A, x * x = 1 ∧ ∀ y ∈ A, x * y = y * x := by
    intro x hx
    have hxl := (hcodes (κ x)).1 ⟨x, hx, rfl⟩
    rw [List.mem_filter] at hxl
    have h := (allL_iff.1 hel) _ hxl.1
    rw [Bool.or_eq_true, hxl.2] at h
    rcases h with h | h
    · exact absurd h (by simp)
    rw [Bool.and_eq_true] at h
    refine ⟨?_, fun y hy => ?_⟩
    · apply hκ.inj _ (K.mul_mem (hAK hx) (hAK hx)) _ K.one_mem
      rw [hκ.mul _ (hAK hx) _ (hAK hx), hκ.one]
      exact Nat.eq_of_beq_eq_true h.1
    · have hyl := (hcodes (κ y)).1 ⟨y, hy, rfl⟩
      rw [List.mem_filter] at hyl
      have h2 := (allL_iff.1 h.2) _ hyl.1
      rw [Bool.or_eq_true, hyl.2] at h2
      rcases h2 with h2 | h2
      · exact absurd h2 (by simp)
      apply hκ.inj _ (K.mul_mem (hAK hx) (hAK hy)) _ (K.mul_mem (hAK hy) (hAK hx))
      rw [hκ.mul _ (hAK hx) _ (hAK hy), hκ.mul _ (hAK hy) _ (hAK hx)]
      exact Nat.eq_of_beq_eq_true h2
  refine ⟨A, hA, ⟨⟨⟨fun a b => Subtype.ext ((hel' a.1 a.2).2 b.1 b.2)⟩⟩, fun x hx => ?_⟩, ?_, ?_⟩
  · rw [pow_two]
    exact (hel' x hx).1
  · rw [card_codes hκ hAK (hnd.filter _) hcodes]
    exact Nat.eq_of_beq_eq_true hc16
  · intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ h ∈ H, ∀ x, x ∈ A → h * x * h⁻¹ ∈ A := by
      intro h hh x hx
      obtain ⟨hxQ, hxN⟩ := (hA x).1 hx
      exact (hA _).2 ⟨D.hQn h hh x hxQ, hH h hh x hxQ hxN⟩
    intro x
    constructor
    · exact key h hh x
    · intro hx
      have := key h⁻¹ (H.inv_mem hh) _ hx
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      rwa [e] at this

end AB

end CFSG.KS.S1277Vl

end
