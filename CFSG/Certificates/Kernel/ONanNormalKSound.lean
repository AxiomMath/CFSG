
module

public import Certificates.Data.Kernel.ONanNormalK
public import CFSG.Certificates.Kernel.ONanB2KSound

public section

namespace CFSG.OddStandard.ONanRec.NK

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.CMK CFSG.OddStandard.ONanRec.B2K

theorem ptK_lt (H : Hyp) {w : List ℕ} (hw : ∀ c ∈ w, c < 12) {x : ℕ} (hx : x < 480) :
    ptK w x < 480 := by
  rw [ptK_eq H.letters hw hx]
  exact Fin.isLt _

theorem key3_eq (H : Hyp) {u v : List ℕ} (hu : ∀ c ∈ u, c < 12) (hv : ∀ c ∈ v, c < 12)
    (h : key3 u = key3 v) : wordPerm u = wordPerm v := by
  have a0 := ptK_lt H hu (x := 0) (by norm_num)
  have a1 := ptK_lt H hu (x := 56) (by norm_num)
  have a2 := ptK_lt H hu (x := 2) (by norm_num)
  have b0 := ptK_lt H hv (x := 0) (by norm_num)
  have b1 := ptK_lt H hv (x := 56) (by norm_num)
  have b2 := ptK_lt H hv (x := 2) (by norm_num)
  unfold key3 at h
  have e0 : ptK u 0 = ptK v 0 := by omega
  have e1 : ptK u 56 = ptK v 56 := by omega
  have e2 : ptK u 2 = ptK v 2 := by omega
  refine eqB_eq H hu hv ?_
  simp only [eqB, b2Base, List.all_cons, List.all_nil, e0, e1, e2, beq_self_eq_true,
    Bool.and_true]

theorem key3_of_eq (H : Hyp) {u v : List ℕ} (hu : ∀ c ∈ u, c < 12) (hv : ∀ c ∈ v, c < 12)
    (h : wordPerm u = wordPerm v) : key3 u = key3 v := by
  unfold key3
  rw [ptK_eq H.letters hu (x := 0) (by norm_num), ptK_eq H.letters hu (x := 56) (by norm_num),
    ptK_eq H.letters hu (x := 2) (by norm_num), ptK_eq H.letters hv (x := 0) (by norm_num),
    ptK_eq H.letters hv (x := 56) (by norm_num), ptK_eq H.letters hv (x := 2) (by norm_num), h]

theorem stepK_eq (H : Hyp) {w h : List ℕ} (hw : ∀ c ∈ w, c < 12) (hh : ∀ c ∈ h, c < 12)
    {q : ℕ} (hq : q < 480) :
    stepK w h (invWord h) q =
      ((wordPerm w * (wordPerm h * (wordPerm w * (wordPerm h)⁻¹))) ⟨q, hq⟩ : ℕ) := by
  have hl := cmLettersOK_of H.letters
  have hi := invWord_lt hh
  unfold stepK
  rw [ptK_eq H.letters hi hq]
  rw [ptK_eq H.letters hw (Fin.isLt _), ptK_eq H.letters hh (Fin.isLt _),
    ptK_eq H.letters hw (Fin.isLt _), wordPerm_inv hl hh]
  simp only [Fin.eta, Equiv.Perm.mul_apply]

theorem iterK_eq {f : ℕ → ℕ} {y : Equiv.Perm (Fin 480)}
    (hf : ∀ q (hq : q < 480), f q = (y ⟨q, hq⟩ : ℕ)) :
    ∀ (n q : ℕ) (hq : q < 480), iterK f n q = ((y ^ n) ⟨q, hq⟩ : ℕ)
  | 0, q, hq => rfl
  | n + 1, q, hq => by
    have e : iterK f (n + 1) q = iterK f n (f q) := by
      change CFSG.KC.Enum.strictN (f q) (iterK f n) = _
      cases f q <;> rfl
    rw [e, hf q hq, iterK_eq hf n _ (Fin.isLt _), pow_succ, Equiv.Perm.mul_apply]

theorem not_two_of_witK (H : Hyp) {w t : List ℕ} (hw : ∀ c ∈ w, c < 12)
    (ht : witK w t = true) : ∃ h : List ℕ, (∀ c ∈ h, c < 12) ∧
      (wordPerm w * (wordPerm h * (wordPerm w * (wordPerm h)⁻¹))) ^ 512 ≠ 1 := by
  unfold witK at ht
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne] at ht
  obtain ⟨⟨⟨⟨hh, hq⟩, hv⟩, hm⟩, hv'⟩ := ht
  set h := t.drop 3
  set q := t.getD 0 0
  set m := t.getD 1 0
  set v := t.getD 2 0
  refine ⟨h, hh, fun h512 => ?_⟩
  set y := wordPerm w * (wordPerm h * (wordPerm w * (wordPerm h)⁻¹))
  have hf : ∀ p (hp : p < 480), stepK w h (invWord h) p = (y ⟨p, hp⟩ : ℕ) :=
    fun p hp => stepK_eq H hw hh hp
  have hper : ∀ n, iterK (stepK w h (invWord h)) n q = q ↔
      Function.IsPeriodicPt (⇑y) n ⟨q, hq⟩ := by
    intro n
    rw [iterK_eq hf n q hq, Function.IsPeriodicPt, Function.IsFixedPt,
      ← Equiv.Perm.coe_pow, Fin.ext_iff]
  have h1 : Function.IsPeriodicPt (⇑y) m ⟨q, hq⟩ := (hper m).1 hm
  have h2 : Function.IsPeriodicPt (⇑y) 512 ⟨q, hq⟩ := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, h512]
    rfl
  have h3 := h1.gcd h2
  rw [← hv] at h3
  exact hv' ((hper v).2 h3)

theorem allE_sound (F : ℕ → List ℕ → List ℕ → List ℕ → Bool) :
    ∀ (i0 : ℕ) (ws rs ts : List (List ℕ)), allE F i0 ws rs ts = true →
      ∀ t < ws.length, F (i0 + t) (ws.getD t []) (rs.getD t []) (ts.getD t []) = true
  | _, [], _, _, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | i0, w :: ws, [], _, h, _, _ => by simp [allE] at h
  | i0, w :: ws, r :: rs, [], h, _, _ => by simp [allE] at h
  | i0, w :: ws, r :: rs, u :: ts, h, t, ht => by
    rw [allE, Bool.and_eq_true] at h
    rcases t with _ | t
    · simpa using h.1
    · have := allE_sound F (i0 + 1) ws rs ts h.2 t (by simpa using ht)
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using this

theorem length_of_shape16 {α : Type} {T : List (List α)} (h : shape16 T = true) {k : ℕ}
    (hk : k < 16) : (T.getD k []).length = 32 := by
  simp only [shape16, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact h.2 _ (List.getElem_mem _)

theorem entK_of {gs : List (List ℕ)} {ws : List (List (List ℕ))} {ks : List (List ℕ)}
    {rs wt : List (List (List ℕ))} (hsh : shapeK gs ws rs wt = true)
    (hch : ∀ k < 16, chunkK gs ws ks rs wt k = true) {i : ℕ} (hi : i < 512) :
    entK gs ks rs i (lookC [] ws i) (lookC [] rs i) (lookC [] wt i) = true := by
  simp only [shapeK, Bool.and_eq_true] at hsh
  have hk : i / 32 < 16 := by omega
  have h := allE_sound _ _ _ _ _ (hch _ hk) (i % 32)
    (by rw [length_of_shape16 hsh.1.1.1.2 hk]; omega)
  have e : 32 * (i / 32) + i % 32 = i := Nat.div_add_mod i 32
  rw [e] at h
  exact h

theorem lt12_lookC {T : List (List (List ℕ))} {i : ℕ} {gs ks : List (List ℕ)}
    {rs : List (List (List ℕ))} {r t : List ℕ}
    (h : entK gs ks rs i (lookC [] T i) r t = true) : ∀ c ∈ lookC [] T i, c < 12 := by
  unfold entK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  exact h.1.1.1.1.1

theorem keys_lt {K : ℕ → ℕ} (h : ∀ i < 511, K i < K (i + 1)) :
    ∀ i j, i < j → j < 512 → K i < K j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | rfl
    · exact lt_trans (ih h1 (by omega)) (h j (by omega))
    · exact h i (by omega)

theorem closed_of_gens {G : Type*} [Group G] [Finite G] (L : Set G) (A : Set G)
    (hA : ∀ a ∈ A, ∀ x ∈ L, x * a ∈ L) : ∀ g ∈ Subgroup.closure A, ∀ x ∈ L, x * g ∈ L := by
  let T : Subgroup G :=
    { carrier := {g | ∀ x ∈ L, x * g ∈ L}
      one_mem' := fun x hx => by rwa [mul_one]
      mul_mem' := fun {a b} ha hb x hx => by
        rw [← mul_assoc]
        exact hb _ (ha x hx)
      inv_mem' := fun {a} ha => by
        have hp : ∀ n : ℕ, ∀ x ∈ L, x * a ^ n ∈ L := by
          intro n
          induction n with
          | zero => intro x hx; rwa [pow_zero, mul_one]
          | succ n ih =>
            intro x hx
            rw [pow_succ, ← mul_assoc]
            exact ha _ (ih x hx)
        have ho := orderOf_pos a
        have e : a ^ (orderOf a - 1) = a⁻¹ := eq_inv_of_mul_eq_one_left (by
          rw [← pow_succ, Nat.sub_add_cancel ho, pow_orderOf_eq_one])
        intro x hx
        change x * a⁻¹ ∈ L
        rw [← e]
        exact hp _ x hx }
  have hle : Subgroup.closure A ≤ T := (Subgroup.closure_le T).2 fun a ha => hA a ha
  exact fun g hg => hle hg

theorem normal2_of (H : Hyp) {gs : List (List ℕ)} {ws : List (List (List ℕ))}
    {ks : List (List ℕ)} {rs wt : List (List (List ℕ))} (hsh : shapeK gs ws rs wt = true)
    (hch : ∀ k < 16, chunkK gs ws ks rs wt k = true) (S : Subgroup (Equiv.Perm (Fin 480)))
    (hSM : S ≤ M480) (hS2 : ∀ g ∈ S, g ^ 512 = 1)
    (hSn : ∀ g ∈ S, ∀ h ∈ M480, h * g * h⁻¹ ∈ S) : Nat.card S ≤ 4 := by
  classical
  have hl := cmLettersOK_of H.letters
  have hsh' := hsh
  simp only [shapeK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq,
    Nat.ble_eq] at hsh'
  obtain ⟨⟨⟨⟨⟨hg3, hgl⟩, -⟩, -⟩, -⟩, hcnt⟩ := hsh'
  set W : ℕ → List ℕ := lookC [] ws
  set R : ℕ → List ℕ := lookC [] rs
  set T : ℕ → List ℕ := lookC [] wt
  set K : ℕ → ℕ := lookC 0 ks
  set G : ℕ → List ℕ := fun j => gs.getD j []
  have hE : ∀ i < 512, entK gs ks rs i (W i) (R i) (T i) = true := fun i hi => entK_of hsh hch hi
  have hW : ∀ i < 512, ∀ c ∈ W i, c < 12 := fun i hi => lt12_lookC (hE i hi)
  have hG : ∀ j < 3, ∀ c ∈ G j, c < 12 := by
    intro j hj
    have : G j ∈ gs := by
      change gs.getD j [] ∈ gs
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    exact hgl _ this
  have hEi : ∀ i < 512, key3 (W i) = K i ∧ (i = 511 ∨ K i < K (i + 1)) ∧
      (∀ j < 3, (R i).getD j 0 < 512 ∧ key3 (W i ++ G j) = K ((R i).getD j 0)) ∧
      (((R i).getD 3 0 = 0 ∧ eqB (W i) [] = true) ∨
        ((((R i).getD 4 0 < 512 ∧ (R i).getD 5 0 < 3) ∧
          (R ((R i).getD 4 0)).getD 3 0 + 1 = (R i).getD 3 0) ∧
          (R ((R i).getD 4 0)).getD ((R i).getD 5 0) 0 = i)) ∧
      ((T i).isEmpty = true ∨ witK (W i) (T i) = true) := by
    intro i hi
    have h := hE i hi
    unfold entK at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true,
      List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨h1, h2, h3, h4, h5⟩
  set elt : ℕ → Equiv.Perm (Fin 480) := fun i => wordPerm (W i)
  set gen : ℕ → Equiv.Perm (Fin 480) := fun j => wordPerm (G j)
  set P : Subgroup (Equiv.Perm (Fin 480)) :=
    Subgroup.closure (Set.range fun j : Fin 3 => gen j)
  have hcl : ∀ i < 512, ∀ j < 3, elt i * gen j = elt ((R i).getD j 0) := by
    intro i hi j hj
    obtain ⟨hlt, he⟩ := (hEi i hi).2.2.1 j hj
    have hk := (hEi _ hlt).1
    rw [← hk] at he
    have e := key3_eq H (lt12_append (hW i hi) (hG j hj)) (hW _ hlt) he
    rwa [wordPerm_append] at e
  have hinj : ∀ i < 512, ∀ i' < 512, elt i = elt i' → i = i' := by
    intro i hi i' hi' he
    have hk := key3_of_eq H (hW i hi) (hW i' hi') he
    rw [(hEi i hi).1, (hEi i' hi').1] at hk
    have hmono := keys_lt (K := K) fun a ha => ((hEi a (by omega)).2.1).resolve_left (by omega)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact absurd hk (ne_of_lt (hmono _ _ h1 hi'))
    · exact absurd hk (ne_of_gt (hmono _ _ h1 hi))
  have hdep : ∀ d, ∀ i < 512, (R i).getD 3 0 = d → elt i ∈ P := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      rcases (hEi i hi).2.2.2.1 with ⟨-, h1⟩ | ⟨⟨⟨-, -⟩, h3⟩, -⟩
      · have e := eqB_eq H (hW i hi) lt12_nil h1
        change wordPerm (W i) ∈ P
        rw [e, wordPerm_nil]
        exact one_mem _
      · omega
    | succ d ih =>
      intro i hi hd
      rcases (hEi i hi).2.2.2.1 with ⟨h0, -⟩ | ⟨⟨⟨hp, hj⟩, h3⟩, h4⟩
      · omega
      · have e := hcl _ hp _ hj
        rw [h4] at e
        rw [← e]
        refine mul_mem (ih _ hp (by omega)) (Subgroup.subset_closure ⟨⟨_, hj⟩, rfl⟩)
  have hmemP : ∀ i < 512, elt i ∈ P := fun i hi => hdep _ i hi rfl
  have hPL : ∀ g ∈ P, ∀ x ∈ {x | ∃ i < 512, elt i = x}, x * g ∈ {x | ∃ i < 512, elt i = x} := by
    refine closed_of_gens _ _ ?_
    rintro _ ⟨j, rfl⟩ _ ⟨i, hi, rfl⟩
    exact ⟨_, ((hEi i hi).2.2.1 j j.2).1, (hcl i hi j j.2).symm⟩
  obtain ⟨i1, hi1, e1⟩ := hPL _ (inv_mem (hmemP 0 (by norm_num))) _ ⟨0, by norm_num, rfl⟩
  rw [mul_inv_cancel] at e1
  have hP : ∀ g ∈ P, ∃ i < 512, elt i = g := by
    intro g hg
    obtain ⟨i, hi, e⟩ := hPL g hg _ ⟨i1, hi1, rfl⟩
    rw [e1, one_mul] at e
    exact ⟨i, hi, e⟩
  have hPset : (P : Set (Equiv.Perm (Fin 480))) = elt '' (↑(Finset.range 512) : Set ℕ) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro hg
      obtain ⟨i, hi, e⟩ := hP g hg
      exact ⟨i, hi, e⟩
    · rintro ⟨i, hi, rfl⟩
      exact hmemP i hi
  have hcardP : Nat.card P = 512 := by
    have h0 : Nat.card P = (P : Set (Equiv.Perm (Fin 480))).ncard := Nat.card_coe_set_eq _
    rw [h0, hPset,
      Set.InjOn.ncard_image (fun i hi i' hi' he => hinj i (by simpa using hi) i'
        (by simpa using hi') he), Set.ncard_coe_finset, Finset.card_range]
  have hPM : P ≤ M480 := (Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun j =>
    wordPerm_mem hl _ (hG j j.2))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P0 : Subgroup M480 := P.subgroupOf M480
  have hP0 : Nat.card P0 = 2 ^ 9 := by
    rw [show Nat.card P0 = Nat.card P from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hcardP]
    norm_num
  have hidx : P0.index = 315 := by
    have h1 := P0.card_mul_index
    rw [hP0, card_M480 H.bound H.model] at h1
    omega
  have hP0p : IsPGroup 2 P0 := IsPGroup.of_card hP0
  have hidx2 : ¬ 2 ∣ P0.index := by rw [hidx]; norm_num
  set S0 : Subgroup M480 := S.subgroupOf M480
  have hS0n : S0.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hSn _ hn _ g.2⟩
  have hS0p : IsPGroup 2 S0 := fun g => ⟨9, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hS2 _ g.2⟩
  have hSP : ∀ x ∈ S, x ∈ P := by
    intro x hx
    have h1 : (⟨x, hSM hx⟩ : M480) ∈ S0 := Subgroup.mem_subgroupOf.2 hx
    have h2 := hS0p.le_sylow_of_normal (hP0p.toSylow hidx2) h1
    exact Subgroup.mem_subgroupOf.1 ((hP0p.mem_toSylow hidx2).1 h2)
  have hSE : ∀ x ∈ S, ∃ i < 512, (T i).isEmpty = true ∧ elt i = x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hP x (hSP x hx)
    refine ⟨i, hi, ?_, rfl⟩
    rcases (hEi i hi).2.2.2.2 with h | h
    · exact h
    · exfalso
      obtain ⟨h, hh, hne⟩ := not_two_of_witK H (hW i hi) h
      have hhM := wordPerm_mem hl h hh
      have h1 := hSn _ hx _ hhM
      have h2 := mul_mem hx h1
      apply hne
      have e : elt i * (wordPerm h * (elt i * (wordPerm h)⁻¹)) =
          elt i * (wordPerm h * elt i * (wordPerm h)⁻¹) := by group
      rw [e]
      exact hS2 _ h2
  set E := ((List.range 512).filter fun i => (T i).isEmpty).map elt
  have hsub : (S : Set (Equiv.Perm (Fin 480))) ⊆ (E.toFinset : Set _) := by
    intro x hx
    obtain ⟨i, hi, he, rfl⟩ := hSE x hx
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, he⟩, rfl⟩
  have hlen : E.length ≤ 4 := by
    rw [List.length_map, ← List.countP_eq_length_filter]
    exact hcnt
  calc Nat.card S = (S : Set (Equiv.Perm (Fin 480))).ncard := Nat.card_coe_set_eq _
    _ ≤ (E.toFinset : Set (Equiv.Perm (Fin 480))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = E.toFinset.card := Set.ncard_coe_finset _
    _ ≤ E.length := List.toFinset_card_le _
    _ ≤ 4 := hlen

theorem normal2_CModel_of (hB : CMBound) (hM : cmModelCheck = true)
    (h : ∀ S : Subgroup (Equiv.Perm (Fin 480)), S ≤ M480 → (∀ g ∈ S, g ^ 512 = 1) →
      (∀ g ∈ S, ∀ h ∈ M480, h * g * h⁻¹ ∈ S) → Nat.card S ≤ 4) :
    ∀ S : Subgroup CModel, IsPGroup 2 S → S.Normal → Nat.card S ≤ 4 := by
  classical
  intro S hS hSn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite CModel := (card_CModel_le hB).1
  set e := equivM480 hB hM with he
  have hcard := card_CModel hB hM
  set S' : Subgroup (Equiv.Perm (Fin 480)) := (S.map e.toMonoidHom).map M480.subtype with hS'
  have hcS : Nat.card S' = Nat.card S := by
    rw [hS', Subgroup.card_map_of_injective M480.subtype_injective,
      Subgroup.card_map_of_injective e.injective]
  have hdvd : Nat.card S ∣ 512 := by
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have h2 : Nat.card S ∣ 161280 := hcard ▸ Subgroup.card_subgroup_dvd_card S
    rw [hk] at h2 ⊢
    have hk9 : k ≤ 9 := by
      by_contra hk9
      have : 2 ^ 10 ∣ 161280 := (pow_dvd_pow 2 (by omega)).trans h2
      norm_num at this
    exact pow_dvd_pow 2 hk9
  rw [← hcS]
  refine h S' ?_ ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : (⟨x, hx⟩ : S) ^ 512 = 1 := by
      obtain ⟨m, hm⟩ := hdvd
      rw [hm, pow_mul, pow_card_eq_one', one_pow]
    have : x ^ 512 = 1 := by
      have := congrArg Subtype.val hx'
      simpa using this
    change ((e x : M480) : Equiv.Perm (Fin 480)) ^ 512 = 1
    rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  · rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩ h hh
    refine ⟨⟨h, hh⟩ * e x * ⟨h, hh⟩⁻¹, ⟨e.symm ⟨h, hh⟩ * x * (e.symm ⟨h, hh⟩)⁻¹,
      hSn.conj_mem x hx _, ?_⟩, rfl⟩
    simp

end CFSG.OddStandard.ONanRec.NK
