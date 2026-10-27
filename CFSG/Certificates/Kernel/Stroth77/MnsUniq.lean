module

public import CFSG.Certificates.Kernel.Stroth77.MnsSmall
public import Certificates.Data.Kernel.Stroth77.MnsUniqK

public section

namespace CFSG.KC.Stroth77MN

open CFSG.CGT.Stroth77
open CFSG.KC.Stroth77SP (memB)

theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem allU_iff {n : ℕ} {f : ℕ → Bool} : allU n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    have e : allU (n + 1) f = bAnd(f n, allU n f) := rfl
    rw [e]
    cases hf : f n
    · refine ⟨fun h => absurd h Bool.false_ne_true, fun h => ?_⟩
      exact absurd (h n (by omega)) (by rw [hf]; decide)
    · change allU n f = true ↔ _
      rw [ih]
      refine ⟨fun h i hi => ?_, fun h i hi => h i (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h i hi
      · exact hf

theorem anyU_iff {n : ℕ} {f : ℕ → Bool} : anyU n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    have e : anyU (n + 1) f = bIf(f n, true, anyU n f) := rfl
    rw [e]
    cases hf : f n
    · change anyU n f = true ↔ _
      rw [ih]
      refine ⟨fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩, fun ⟨i, hi, h⟩ => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ⟨i, hi, h⟩
      · exact absurd (hf.symm.trans h) Bool.false_ne_true
    · exact ⟨fun _ => ⟨n, by omega, hf⟩, fun _ => rfl⟩

theorem strictU_eq (y : ℕ) (k : ℕ → Bool) : strictU y k = k y := by
  cases y <;> rfl

theorem bitU_eq (M c : ℕ) : bitU M c = memB M c := by
  have e : Nat.land (Nat.shiftRight M c) 1 = M / 2 ^ c % 2 := by
    change (M >>> c) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bitU memB
  change Nat.beq (Nat.land (Nat.shiftRight M c) 1) 1 = _
  rw [e, Bool.eq_iff_iff, beq_iff_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => (congrArg (Nat.beq · 1) h).trans (Nat.beq_refl 1)⟩

theorem fld_lt256 (r o : ℕ) : fld(r, o, nat_lit 255) < 256 :=
  Nat.lt_succ_of_le Nat.and_le_right

@[expose] def klE (U : UTabs) (i : ℕ) : ℕ := fld(U.KL, Nat.mul (nat_lit 8) i, nat_lit 255)

theorem inKL_iff {U : UTabs} {c : ℕ} : inKL U c = true ↔ ∃ i < 16, klE U i = c := by
  unfold inKL
  rw [anyU_iff]
  exact exists_congr fun i => and_congr Iff.rfl
    ⟨Nat.eq_of_beq_eq_true, fun h => by rw [← h]; exact Nat.beq_refl _⟩

variable {D : Tabs} {U : UTabs}

theorem red_facts (h : uRedOK D U = true) {c : ℕ} (hc : c < 256) (hm : memA D c = false) :
    ∃ s < 256, memB D.REPM (conjS D s c) = true ∧
      (inKL U (conjS D s c) = true → inKL U c = true) := by
  unfold uRedOK at h
  have h1 := allU_iff.1 h c hc
  beta_reduce at h1
  have hb : bitU D.AM c = false := by
    rw [bitU_eq]
    exact hm
  rw [hb] at h1
  change strictU _ _ = true at h1
  rw [strictU_eq] at h1
  beta_reduce at h1
  refine ⟨fld(D.RW, Nat.mul (nat_lit 8) c, nat_lit 255), fld_lt256 _ _, ?_⟩
  generalize conjS D (fld(D.RW, Nat.mul (nat_lit 8) c, nat_lit 255)) c = k at h1 ⊢
  rw [← bitU_eq]
  revert h1
  generalize bitU D.REPM k = x1
  generalize inKL U k = x2
  generalize inKL U c = x3
  cases x1 <;> cases x2 <;> cases x3 <;> decide

theorem cen_facts (h : uCenOK D U = true) {k : ℕ} (hk : k < 256) (hr : memB D.REPM k = true)
    (hn : inKL U k = false) : ∃ n : ℕ, ∃ w : ℕ → ℕ, (∀ i, w i < 256) ∧
      (∀ i, i + 1 < n → conjS D (w i) k < conjS D (w (i + 1)) k) ∧
      (n = 16 ∨ n = 8 ∧ ∃ p < 256, ∃ q < 256, commS D k p = true ∧ commS D k q = true ∧
        commS D p q = false) := by
  unfold uCenOK at h
  have h1 := allU_iff.1 h k hk
  beta_reduce at h1
  rw [bitU_eq, hr, hn] at h1
  change strictU _ (cenE D k) = true at h1
  rw [strictU_eq] at h1
  generalize fld(U.CW, Nat.mul (nat_lit 152) k,
    nat_lit 5708990770823839524233143877797980545530986495) = e at h1
  unfold cenE at h1
  beta_reduce at h1
  generalize fld(e, nat_lit 16, nat_lit 255) = n at h1
  obtain ⟨h2, h3⟩ := bAnd_true h1
  rw [allU_iff] at h3
  refine ⟨n, cwS e, fun i => fld_lt256 _ _, fun i hi => ?_, ?_⟩
  · have h4 := h3 i (by change i < n - 1; omega)
    exact Nat.le_of_ble_eq_true h4
  · have hp : fld(e, nat_lit 0, nat_lit 255) < 256 := fld_lt256 _ _
    have hq : fld(e, nat_lit 8, nat_lit 255) < 256 := fld_lt256 _ _
    generalize fld(e, nat_lit 0, nat_lit 255) = p at h2 hp
    generalize fld(e, nat_lit 8, nat_lit 255) = q at h2 hq
    have key : Nat.beq n (nat_lit 16) = true ∨ (Nat.beq n (nat_lit 8) = true ∧
        commS D k p = true ∧ commS D k q = true ∧ commS D p q = false) := by
      revert h2
      generalize Nat.beq n (nat_lit 16) = x1
      generalize Nat.beq n (nat_lit 8) = x2
      generalize commS D k p = x3
      generalize commS D k q = x4
      generalize commS D p q = x5
      cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> decide
    rcases key with h16 | ⟨h8, h3, h4, h5⟩
    · exact Or.inl (Nat.eq_of_beq_eq_true h16)
    · exact Or.inr ⟨Nat.eq_of_beq_eq_true h8, p, hp, q, hq, h3, h4, h5⟩

theorem pair_facts (h : uPairOK D U = true) :
    ∃ a b, inKL U a = true ∧ inKL U b = true ∧ commS D a b = false := by
  unfold uPairOK at h
  beta_reduce at h
  generalize fld(U.AB, nat_lit 0, nat_lit 255) = a at h
  generalize fld(U.AB, nat_lit 8, nat_lit 255) = b at h
  refine ⟨a, b, ?_⟩
  revert h
  generalize inKL U a = x1
  generalize inKL U b = x2
  generalize bitU D.AM a = x3
  generalize bitU D.AM b = x4
  generalize commS D a b = x5
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> decide

@[expose] noncomputable def codes (S : Set Mns) : Finset ℕ := by
  classical exact (Finset.range 256).filter fun m => elS m ∈ S

theorem mem_codes {S : Set Mns} {m : ℕ} : m ∈ codes S ↔ m < 256 ∧ elS m ∈ S := by
  classical
  unfold codes
  simp only [Finset.mem_filter, Finset.mem_range]

theorem ncard_eq_codes (ht : tabOK D = true) {S : Set Mns} (hS : ∀ g ∈ S, g ∈ Tg) :
    S.ncard = (codes S).card := by
  have hset : S = elS '' ↑(codes S) := by
    ext g
    constructor
    · intro hg
      obtain ⟨c, hc, rfl⟩ := (mem_Tg_iff ht).1 (hS g hg)
      exact ⟨c, mem_codes.2 ⟨hc, hg⟩, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact (mem_codes.1 hc).2
  have hinj : Set.InjOn elS ↑(codes S) := fun c hc d hd he =>
    elS_injective ht (mem_codes.1 hc).1 (mem_codes.1 hd).1 he
  calc S.ncard = (elS '' ↑(codes S)).ncard := congrArg Set.ncard hset
    _ = (codes S).card := by rw [hinj.ncard_image, Set.ncard_coe_finset]

theorem conj_eq {G : Type*} [Group G] {a b a' b' K : G} (hb : K * b = b * K)
    (hb' : K * b' = b' * K) (h : a * b = a' * b') : a * K * a⁻¹ = a' * K * a'⁻¹ := by
  have hx : a = a' * (b' * b⁻¹) := by rw [← mul_assoc, ← h, mul_inv_cancel_right]
  have hc : b' * b⁻¹ * K * (b' * b⁻¹)⁻¹ = K := by
    have hcm : K * (b' * b⁻¹) = b' * b⁻¹ * K := Commute.mul_right hb' (Commute.inv_right hb)
    rw [← hcm, mul_inv_cancel_right]
  rw [hx]
  calc a' * (b' * b⁻¹) * K * (a' * (b' * b⁻¹))⁻¹ =
      a' * (b' * b⁻¹ * K * (b' * b⁻¹)⁻¹) * a'⁻¹ := by group
    _ = a' * K * a'⁻¹ := by rw [hc]

theorem coset_bound (ht : tabOK D = true) {n k : ℕ} (s : ℕ → ℕ) (hs : ∀ i, s i < 256)
    (hinj : ∀ i < n, ∀ j < n, conjS D (s i) k = conjS D (s j) k → i = j) :
    n * ((Finset.range 256).filter fun x => commS D k x = true).card ≤ 256 := by
  have hinjOn : Set.InjOn (fun x : ℕ × ℕ => mulS D (s x.1) x.2)
      ↑(Finset.range n ×ˢ (Finset.range 256).filter fun x => commS D k x = true) := by
    rintro ⟨i, h1⟩ hx ⟨j, h2⟩ hy he
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_filter] at hx hy
    have he' : elS (s i) * elS h1 = elS (s j) * elS h2 := by
      rw [← elS_mulS ht, ← elS_mulS ht]
      exact congrArg elS he
    have hconj : elS (conjS D (s i) k) = elS (conjS D (s j) k) := by
      rw [elS_conjS ht, elS_conjS ht]
      exact conj_eq ((commS_iff ht).1 hx.2.2) ((commS_iff ht).1 hy.2.2) he'
    have hij := hinj i hx.1 j hy.1 (elS_injective ht (mulS_lt _ _) (mulS_lt _ _) hconj)
    subst hij
    rw [elS_injective ht hx.2.1 hy.2.1 (mul_left_cancel he')]
  have h := Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => mulS D (s x.1) x.2)
    (t := Finset.range 256) (fun ⦃x⦄ _ => Finset.mem_coe.2 (Finset.mem_range.2 (mulS_lt _ _)))
    hinjOn
  rwa [Finset.card_product, Finset.card_range, Finset.card_range] at h

theorem strict_inj {n : ℕ} {f : ℕ → ℕ} (hinc : ∀ i, i + 1 < n → f i < f (i + 1)) :
    ∀ i < n, ∀ j < n, f i = f j → i = j := by
  have mono : ∀ j i, i < j → j < n → f i < f j := by
    intro j
    induction j with
    | zero => exact fun i hij _ => absurd hij (Nat.not_lt_zero i)
    | succ j ih =>
      intro i hij hjn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
      · exact (ih i hij (by omega)).trans (hinc j hjn)
      · exact hinc i hjn
  intro i hi j hj he
  rcases lt_trichotomy i j with hl | hl | hl
  · exact absurd he (mono j i hl hj).ne
  · exact hl
  · exact absurd he.symm (mono i j hl hi).ne

theorem inKL_of_mem (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true)
    (hr : uRedOK D U = true) (hce : uCenOK D U = true) {B : Subgroup Mns} (hB : B ≤ Tg)
    (hBcomm : ∀ {a b : Mns}, a ∈ B → b ∈ B → a * b = b * a) (hBn : (B : Set Mns).ncard = 32)
    {m : ℕ} (hm : m < 256) (hmB : elS m ∈ B) (hmA : elS m ∉ Ag) : inKL U m = true := by
  have hmA' : memA D m = false := by
    cases h : memA D m
    · rfl
    · exact absurd ((elS_mem_Ag_iff ht hc ha hm).2 h) hmA
  obtain ⟨s, -, hrep, himp⟩ := red_facts hr hm hmA'
  by_contra hn
  have hkn : inKL U (conjS D s m) = false := by
    cases h : inKL U (conjS D s m)
    · rfl
    · exact absurd (himp h) hn
  obtain ⟨n, w, hw, hinc, hcase⟩ := cen_facts hce (mulS_lt _ _) hrep hkn
  set k := conjS D s m
  set t := elS s
  set Bt : Set Mns := (fun b => t * b * t⁻¹) '' (B : Set Mns)
  have hBtT : ∀ g ∈ Bt, g ∈ Tg := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (mul_mem (elS_mem_Tg s) (hB hb)) (inv_mem (elS_mem_Tg s))
  have hBtn : Bt.ncard = 32 := by
    rw [Set.ncard_image_of_injective _ fun x y h => mul_left_cancel (mul_right_cancel h)]
    exact hBn
  have hBtc : ∀ x ∈ Bt, ∀ y ∈ Bt, x * y = y * x := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc b, hBcomm hb hb', mul_assoc]
  have hk : elS k ∈ Bt := ⟨elS m, hmB, (elS_conjS ht s m).symm⟩
  have hsub : codes Bt ⊆ (Finset.range 256).filter fun x => commS D k x = true := by
    intro x hx
    obtain ⟨hx256, hxB⟩ := mem_codes.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hx256, (commS_iff ht).2 (hBtc _ hk _ hxB)⟩
  have hcodes : (codes Bt).card = 32 := by rw [← ncard_eq_codes ht hBtT, hBtn]
  have hbound := coset_bound ht (n := n) (k := k) w hw (strict_inj hinc)
  have hC := Finset.card_le_card hsub
  rcases hcase with rfl | ⟨rfl, p, hp, q, hq, hkp, hkq, hpq⟩
  · omega
  · have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hpB : elS p ∈ Bt := by
      have hp' : p ∈ codes Bt := by
        rw [heq]
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hp, hkp⟩
      exact (mem_codes.1 hp').2
    have hqB : elS q ∈ Bt := by
      have hq' : q ∈ codes Bt := by
        rw [heq]
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hq, hkq⟩
      exact (mem_codes.1 hq').2
    rw [(commS_iff ht).2 (hBtc _ hpB _ hqB)] at hpq
    exact Bool.noConfusion hpq

theorem Ag_unique (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true)
    (hr : uRedOK D U = true) (hce : uCenOK D U = true) (hp : uPairOK D U = true)
    (B : Subgroup Mns) (hB : B ≤ Tg) (hcomm : IsMulCommutative B) (hcard : Nat.card B = 32) :
    B = Ag := by
  classical
  by_contra hne
  have hBcomm : ∀ {a b : Mns}, a ∈ B → b ∈ B → a * b = b * a := fun {a b} ha hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBn : (B : Set Mns).ncard = 32 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hI : Nat.card (B ⊓ Ag : Subgroup Mns) ≤ 16 := by
    have hd : Nat.card (B ⊓ Ag : Subgroup Mns) ∣ 32 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne32 : Nat.card (B ⊓ Ag : Subgroup Mns) ≠ 32 := by
      intro h32
      have hle : B ≤ Ag := by
        have hBA := Subgroup.eq_of_le_of_card_ge (inf_le_left : B ⊓ Ag ≤ B) (by rw [hcard, h32])
        rw [← hBA]
        exact inf_le_right
      exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_Ag ht hc ha]))
    obtain ⟨j, hj⟩ := hd
    rcases j with _ | _ | j
    · omega
    · omega
    · nlinarith
  have hIc : ((codes B).filter fun m => elS m ∈ Ag).card = Nat.card (B ⊓ Ag : Subgroup Mns) := by
    have e : Nat.card (B ⊓ Ag : Subgroup Mns) = ((B ⊓ Ag : Subgroup Mns) : Set Mns).ncard :=
      Nat.card_coe_set_eq _
    rw [e, ncard_eq_codes ht fun g hg => hB (Subgroup.mem_inf.1 hg).1]
    congr 1
    ext m
    simp only [Finset.mem_filter, mem_codes, SetLike.mem_coe, Subgroup.mem_inf]
    tauto
  have hBc : (codes B).card = 32 := by
    rw [← ncard_eq_codes ht fun g hg => hB hg]
    exact hBn
  have hsplit := Finset.card_filter_add_card_filter_not (s := codes B) (fun m => elS m ∈ Ag)
  have hsub : ((codes B).filter fun m => ¬ elS m ∈ Ag) ⊆ (Finset.range 16).image (klE U) := by
    intro m hm
    rw [Finset.mem_filter, mem_codes] at hm
    obtain ⟨⟨hm256, hmB⟩, hmA⟩ := hm
    obtain ⟨i, hi, rfl⟩ := inKL_iff.1 (inKL_of_mem ht hc ha hr hce hB hBcomm hBn hm256 hmB hmA)
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  have hKL : ((Finset.range 16).image (klE U)).card ≤ 16 :=
    Finset.card_image_le.trans (by rw [Finset.card_range])
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : ∀ x, inKL U x = true → elS x ∈ B := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := inKL_iff.1 hx
    have hx' : klE U i ∈ (codes B).filter fun m => ¬ elS m ∈ Ag := by
      rw [heq]
      exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
    exact (mem_codes.1 (Finset.mem_filter.1 hx').1).2
  obtain ⟨a, b, hia, hib, hab⟩ := pair_facts hp
  rw [(commS_iff ht).2 (hBcomm (hmem a hia) (hmem b hib))] at hab
  exact Bool.noConfusion hab

end CFSG.KC.Stroth77MN
