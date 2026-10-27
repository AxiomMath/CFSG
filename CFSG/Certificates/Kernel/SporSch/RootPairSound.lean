module

public import Certificates.Data.Kernel.SporSch.RootPair
public import CFSG.Certificates.Kernel.SporSch.ClsAllSound

public section

namespace CFSG.KS.SporSch.RPair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx
open CFSG.KS.SporSch.CAll
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Certificates
open CFSG.Sporadic.Schreier

theorem digit_eq {a b x y n : Nat} (hx : x < n) (hy : y < n) (e : a * n + x = b * n + y) :
    a = b ∧ x = y := by
  have hn : 0 < n := by omega
  have h1 : (x + a * n) / n = a := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hx, Nat.zero_add]
  have h2 : (y + b * n) / n = b := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hy, Nat.zero_add]
  have hab : a = b := by
    rw [← h1, ← h2, Nat.add_comm x, Nat.add_comm y, e]
  subst hab
  exact ⟨rfl, Nat.add_left_cancel e⟩

theorem keyR_succ (n w m BP : Nat) (f : Nat → Nat) (d : Nat) :
    keyR n w m BP f (d + 1) = keyR n w m BP f d * n + f (pg w m BP d) := rfl

theorem keyR_inj {n w m BP : Nat} {f g : Nat → Nat} : ∀ d,
    (∀ t < d, f (pg w m BP t) < n) → (∀ t < d, g (pg w m BP t) < n) →
      keyR n w m BP f d = keyR n w m BP g d → ∀ t < d, f (pg w m BP t) = g (pg w m BP t) := by
  intro d
  induction d with
  | zero => intro _ _ _ t ht; omega
  | succ d ih =>
    intro hf hg e t ht
    rw [keyR_succ, keyR_succ] at e
    obtain ⟨e1, e2⟩ := digit_eq (hf d (by omega)) (hg d (by omega)) e
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | rfl
    · exact ih (fun t ht => hf t (by omega)) (fun t ht => hg t (by omega)) e1 t h
    · exact e2

theorem keyR_congr {n w m BP : Nat} {f g : Nat → Nat} : ∀ d,
    (∀ t < d, f (pg w m BP t) = g (pg w m BP t)) → keyR n w m BP f d = keyR n w m BP g d := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro h
    rw [keyR_succ, keyR_succ, ih (fun t ht => h t (by omega)), h d (by omega)]

theorem inR_iff {lo hi u : Nat} : inR lo hi u = true ↔ lo ≤ u ∧ u < hi := by
  unfold inR
  rw [CIdx.bAnd_iff', ble_iff, blt_iff]

theorem bNot_iff {b : Bool} : Bool.rec (motive := fun _ => Bool) true false b = true ↔ b = false := by
  cases b <;> simp

theorem inQ_iff {QJ : Nat → Nat} {mm j : Nat} :
    inQ QJ mm j = true ↔ ∃ k < 8, QJ (8 * mm + k) = j := by
  unfold inQ
  rw [bNot_iff, Bool.eq_false_iff, ne_eq, allN_iff]
  constructor
  · intro h
    by_contra hne
    refine h fun k hk => ?_
    have : QJ (8 * mm + k) ≠ j := fun e => hne ⟨k, hk, e⟩
    rw [bNot_iff, Bool.eq_false_iff]
    exact fun e => this (beq_iff.1 e)
  · rintro ⟨k, hk, e⟩ h
    have := h k hk
    rw [bNot_iff, Bool.eq_false_iff] at this
    exact this (beq_iff.2 e)

@[expose] def q8G {M : Type*} [Group M] (A B : M) (k : Nat) : M :=
  if k = 0 then 1 else if k = 1 then A * A else if k = 2 then A else if k = 3 then A * A * A
  else if k = 4 then B else if k = 5 then A * A * B else if k = 6 then A * B else A * A * A * B

section Q8

variable {M : Type*} [Group M]

theorem q8G_mem {A B : M} {k : Nat} (hk : k < 8) : q8G A B k ∈ Subgroup.closure {A, B} := by
  have hA : A ∈ Subgroup.closure {A, B} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : B ∈ Subgroup.closure {A, B} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hAA := Subgroup.mul_mem _ hA hA
  interval_cases k <;> simp only [q8G] <;> (try norm_num) <;>
    first
      | exact Subgroup.one_mem _
      | exact hA
      | exact hB
      | exact hAA
      | exact Subgroup.mul_mem _ hAA hA
      | exact Subgroup.mul_mem _ hAA hB
      | exact Subgroup.mul_mem _ hA hB
      | exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hAA hA) hB

theorem q8_closure {A B : M} (h4 : A * (A * (A * A)) = 1) (hB : B * B = A * A)
    (hBA : A * B * A = B) {x : M} (hx : x ∈ Subgroup.closure {A, B}) :
    ∃ k < 8, q8G A B k = x := by
  have h4' : A * A * A * A = 1 := by simpa only [mul_assoc] using h4
  have e4 : ∀ y : M, A * (A * (A * (A * y))) = y := fun y => by
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, h4', one_mul]
  have eBA : B * A = A * (A * (A * B)) := by
    have : A * (B * A) = B := by rw [← mul_assoc, hBA]
    calc B * A = A * (A * (A * (A * (B * A)))) := (e4 _).symm
      _ = A * (A * (A * B)) := by rw [this]
  have eBA' : ∀ y : M, B * (A * y) = A * (A * (A * (B * y))) := fun y => by
    rw [← mul_assoc B, eBA]
    simp only [mul_assoc]
  have eBB : ∀ y : M, B * (B * y) = A * (A * y) := fun y => by
    rw [← mul_assoc, hB, mul_assoc]
  have eAi : A⁻¹ = A * (A * A) := by
    rw [inv_eq_iff_mul_eq_one]
    exact h4
  have eB4 : B * (B * (B * B)) = 1 := by rw [eBB, hB, h4]
  have eBi : B⁻¹ = B * (B * B) := by
    rw [inv_eq_iff_mul_eq_one]
    exact eB4
  have eBA0 := eBA
  have eBB0 : B * B = A * A := hB
  have stepA : ∀ y, (∃ k < 8, q8G A B k = y) → ∃ k < 8, q8G A B k = A * y := by
    rintro _ ⟨k, hk, rfl⟩
    interval_cases k
    · exact ⟨2, by norm_num, by simp [q8G]⟩
    · exact ⟨3, by norm_num, by simp [q8G, mul_assoc]⟩
    · exact ⟨1, by norm_num, by simp [q8G]⟩
    · exact ⟨0, by norm_num, by simp [q8G, mul_assoc, h4]⟩
    · exact ⟨6, by norm_num, by simp [q8G]⟩
    · exact ⟨7, by norm_num, by simp [q8G, mul_assoc]⟩
    · exact ⟨5, by norm_num, by simp [q8G, mul_assoc]⟩
    · exact ⟨4, by norm_num, by simp [q8G, mul_assoc, e4]⟩
  have stepB : ∀ y, (∃ k < 8, q8G A B k = y) → ∃ k < 8, q8G A B k = B * y := by
    rintro _ ⟨k, hk, rfl⟩
    interval_cases k
    · exact ⟨4, by norm_num, by simp [q8G]⟩
    · exact ⟨5, by norm_num, by simp [q8G, mul_assoc, eBA', eBA0, e4]⟩
    · exact ⟨7, by norm_num, by simp [q8G, mul_assoc, eBA0]⟩
    · exact ⟨6, by norm_num, by simp [q8G, mul_assoc, eBA', eBA0, e4]⟩
    · exact ⟨1, by norm_num, by simp [q8G, eBB0]⟩
    · exact ⟨0, by norm_num, by simp [q8G, mul_assoc, eBA', eBB, eBB0, e4, h4]⟩
    · exact ⟨2, by norm_num, by simp [q8G, mul_assoc, eBA', eBB, eBB0, e4]⟩
    · exact ⟨3, by norm_num, by simp [q8G, mul_assoc, eBA', eBB, eBB0, e4]⟩
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, by norm_num, rfl⟩
  | mul_left x hx y _ ih =>
    rcases hx with rfl | hx
    · exact stepA _ ih
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact stepB _ ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with rfl | hx
    · rw [eAi, mul_assoc, mul_assoc]
      exact stepA _ (stepA _ (stepA _ ih))
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [eBi, mul_assoc, mul_assoc]
      exact stepB _ (stepB _ (stepB _ ih))

theorem q8_pair_closure [Finite M] {A B x y : M} (h4 : A * (A * (A * A)) = 1)
    (hB : B * B = A * A) (hBA : A * B * A = B) (hA1 : A * A ≠ 1)
    (hx : ∃ k < 8, q8G A B k = x) (hy : ∃ k < 8, q8G A B k = y) (hxx : x * x = A * A)
    (hxy : x * y * x = y) :
    Subgroup.closure {x, y} = Subgroup.closure {A, B} := by
  have hW : (Subgroup.closure {A, B} : Set M) ⊆ {z | ∃ k < 8, q8G A B k = z} := fun z hz =>
    q8_closure h4 hB hBA hz
  have hcardW : Nat.card (Subgroup.closure ({A, B} : Set M)) ≤ 8 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    refine (Set.ncard_le_ncard hW (Set.toFinite _)).trans ?_
    have e : {z | ∃ k < 8, q8G A B k = z} = (fun k => q8G A B k) '' {k | k < 8} := by
      ext z
      simp
    rw [e]
    refine Set.ncard_image_le (Set.toFinite _) |>.trans ?_
    rw [show {k | k < 8} = ((Finset.range 8 : Finset Nat) : Set Nat) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  have hle : Subgroup.closure {x, y} ≤ Subgroup.closure {A, B} := by
    rw [Subgroup.closure_le]
    rintro z (rfl | hz)
    · obtain ⟨k, hk, rfl⟩ := hx
      exact q8G_mem hk
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨k, hk, rfl⟩ := hy
      exact q8G_mem hk
  have hxM : x ∈ Subgroup.closure {x, y} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyM : y ∈ Subgroup.closure {x, y} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have ho : orderOf x = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow (p := 2) ?_ ?_
    · rw [pow_one, sq, hxx]
      exact hA1
    · rw [show (2 : Nat) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, sq, hxx, ← mul_assoc,
        mul_assoc A A A]
      simpa only [mul_assoc] using h4
  have hz : Subgroup.zpowers x ≤ Subgroup.closure {x, y} := by
    rw [Subgroup.zpowers_le]
    exact hxM
  have hdvd : 4 ∣ Nat.card (Subgroup.closure ({x, y} : Set M)) := by
    have := Subgroup.card_dvd_of_le hz
    rwa [Nat.card_zpowers, ho] at this
  have hne : Nat.card (Subgroup.closure ({x, y} : Set M)) ≠ 4 := by
    intro h
    have e := Subgroup.eq_of_le_of_card_ge hz (by rw [h, Nat.card_zpowers, ho]; norm_num)
    rw [← e] at hyM
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyM
    have hc : x ^ m * x = x * x ^ m := ((Commute.refl x).zpow_right m).eq.symm
    rw [mul_assoc, hc, ← mul_assoc, hxx] at hxy
    apply hA1
    simpa using hxy
  have hpos : 0 < Nat.card (Subgroup.closure ({x, y} : Set M)) := Nat.card_pos
  have h8 : 8 ≤ Nat.card (Subgroup.closure ({x, y} : Set M)) := by
    obtain ⟨c, hc⟩ := hdvd
    have hle' := Subgroup.card_le_of_le hle
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  exact Subgroup.eq_of_le_of_card_ge hle (hcardW.trans h8)

theorem five_le_conj [Finite M] {A B x y r : M} {c : Nat → M} {G' : Subgroup M}
    (hJ : Subgroup.closure {x, y} = Subgroup.closure {A, B})
    (hW : ∀ z ∈ Subgroup.closure {A, B}, ∃ k < 8, q8G A B k = z)
    (hcG : ∀ a < 5, c a ∈ G') (hc : ∀ a < 5, c a * r = r * c a)
    (hd : ∀ a < 5, ∀ b < 5, a < b → ∃ k < 8, ∀ k' < 8,
      (c b)⁻¹ * c a * q8G A B k * (c a)⁻¹ * c b ≠ q8G A B k') :
    5 ≤ Set.ncard {J' | ∃ g ∈ G', g * r = r * g ∧
      (Subgroup.closure {x, y}).map (MulAut.conj g).toMonoidHom = J'} := by
  set K := Subgroup.closure ({x, y} : Set M)
  let F : Nat → Subgroup M := fun a => K.map (MulAut.conj (c a)).toMonoidHom
  have hinj : Set.InjOn F {a | a < 5} := by
    intro a ha b hb e
    by_contra hne
    have key : ∀ a < 5, ∀ b < 5, a < b → F a ≠ F b := by
      intro a ha b hb hab e
      obtain ⟨k, hk, hk'⟩ := hd a ha b hb hab
      have hmem : c a * q8G A B k * (c a)⁻¹ ∈ F b := by
        rw [← e]
        refine Subgroup.mem_map.2 ⟨q8G A B k, ?_, rfl⟩
        rw [hJ]
        exact q8G_mem hk
      obtain ⟨z, hz, ez⟩ := Subgroup.mem_map.1 hmem
      change c b * z * (c b)⁻¹ = _ at ez
      rw [hJ] at hz
      obtain ⟨k', hk'', rfl⟩ := hW z hz
      refine hk' k' hk'' ?_
      have e2 : (c b)⁻¹ * c a * q8G A B k * (c a)⁻¹ * c b =
          (c b)⁻¹ * (c a * q8G A B k * (c a)⁻¹) * c b := by group
      rw [e2, ← ez]
      group
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a ha b hb h e
    · exact key b hb a ha h e.symm
  have hsub : F '' {a | a < 5} ⊆ {J' | ∃ g ∈ G', g * r = r * g ∧
      K.map (MulAut.conj g).toMonoidHom = J'} := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨c a, hcG a ha, hc a ha, rfl⟩
  have hfin : {J' | ∃ g ∈ G', g * r = r * g ∧
      K.map (MulAut.conj g).toMonoidHom = J'}.Finite := by
    refine (Set.finite_univ.image fun g : M => K.map (MulAut.conj g).toMonoidHom).subset ?_
    rintro _ ⟨g, -, -, rfl⟩
    exact ⟨g, Set.mem_univ _, rfl⟩
  have := Set.ncard_le_ncard hsub hfin
  rwa [hinj.ncard_image, show {a | a < 5} = ((Finset.range 5 : Finset Nat) : Set Nat) by
    ext; simp, Set.ncard_coe_finset, Finset.card_range] at this

end Q8

section Chain

variable {n w kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}
  (hQ : ChainCK n w PS PSI LR TR TRI kS kO nb BP S base D)
include hQ

theorem el_surj {g : Equiv.Perm (Fin n)} (hg : g ∈ Gen n S kO) :
    ∃ j < ordK LR nb, el n S base nb j = g := by
  by_contra hne
  have hne' : g ∉ {x | ∃ j < ordK LR nb, el n S base nb j = x} := fun ⟨j, hj, e⟩ =>
    hne ⟨j, hj, e⟩
  have hA : {x | ∃ j < ordK LR nb, el n S base nb j = x}.ncard = ordK LR nb := by
    have e : {x | ∃ j < ordK LR nb, el n S base nb j = x} =
        (fun j => el n S base nb j) '' {j | j < ordK LR nb} := by
      ext x
      simp
    have hi : Set.InjOn (fun j => el n S base nb j) {j | j < ordK LR nb} := fun a ha b hb e =>
      el_inj hQ ha hb e
    rw [e, hi.ncard_image, show {j | j < ordK LR nb} =
      ((Finset.range (ordK LR nb) : Finset Nat) : Set Nat) by ext; simp, Set.ncard_coe_finset,
      Finset.card_range]
  have hsub : insert g {x | ∃ j < ordK LR nb, el n S base nb j = x} ⊆
      (Gen n S kO : Set (Equiv.Perm (Fin n))) := by
    rintro x (rfl | ⟨j, hj, rfl⟩)
    · exact hg
    · exact el_mem hQ hj
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hne' (Set.toFinite _), hA] at hle
  have hc : (Gen n S kO : Set (Equiv.Perm (Fin n))).ncard = ordK LR nb := by
    rw [← Nat.card_coe_set_eq]
    exact J1C.card_gen hQ
  omega

theorem acts_elF (j : Nat) :
    Acts n (elF n w (mask w) (n * w) nb LR TR j) (el n S base nb j) := fun y =>
  apL_elemT hQ j y

theorem key_eq_iff {f f' : Nat → Nat} {g g' : Equiv.Perm (Fin n)} (hf : Acts n f g)
    (hf' : Acts n f' g') (hg : g ∈ Gen n S kO) (hg' : g' ∈ Gen n S kO) :
    keyK n w (mask w) BP nb f = keyK n w (mask w) BP nb f' ↔ g = g' := by
  unfold keyK
  constructor
  · intro e
    have hlt : ∀ {f : Nat → Nat} {g : Equiv.Perm (Fin n)}, Acts n f g →
        ∀ t < nb, f (pg w (mask w) BP t) < n := fun {f g} hf t ht => by
      rw [hf ⟨_, pbase_lt hQ ht⟩]
      exact (g _).isLt
    have := keyR_inj nb (hlt hf) (hlt hf') e
    refine eq_of_pbase hQ hg hg' fun t ht hb => ?_
    rw [← hf ⟨_, hb⟩, ← hf' ⟨_, hb⟩]
    exact this t ht
  · rintro rfl
    exact keyR_congr nb fun t ht => by
      rw [hf ⟨_, pbase_lt hQ ht⟩, hf' ⟨_, pbase_lt hQ ht⟩]

omit hQ in
theorem rootHdK_facts {ncl R : Nat} {E O RP RO KL : Nat → Nat}
    (h : rootHdK n w (mask w) (n * w) BP nb LR TR E O RP RO KL ncl R = true) :
    RO 0 = 0 ∧ RO ncl = R ∧ ∀ i < ncl, RO i ≤ RO (i + 1) ∧ O i ≤ RP i ∧ RP i < O (i + 1) ∧
      KL i = keyK n w (mask w) BP nb (elF n w (mask w) (n * w) nb LR TR (E (RP i))) := by
  unfold rootHdK at h
  obtain ⟨h1, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h2, h3⟩ := (CIdx.bAnd_iff' _ _).1 h
  refine ⟨beq_iff.1 h1, beq_iff.1 h2, fun i hi => ?_⟩
  obtain ⟨a1, a⟩ := (CIdx.bAnd_iff' _ _).1 ((allN_iff.1 h3) i hi)
  obtain ⟨a2, a3⟩ := (CIdx.bAnd_iff' _ _).1 a
  obtain ⟨b1, b2⟩ := inR_iff.1 a2
  exact ⟨ble_iff.1 a1, b1, b2, beq_iff.1 a3⟩

omit hQ in
theorem sqK_facts {ncl R j : Nat} {RL RC RI KL : Nat → Nat}
    (h : sqK n w (mask w) (n * w) BP nb LR TR RL RC RI KL ncl R j = true) :
    (RI j = 0 → ∀ i < ncl, keyK n w (mask w) BP nb (fun x => elF n w (mask w) (n * w) nb LR TR j
      (elF n w (mask w) (n * w) nb LR TR j x)) ≠ KL i) ∧
    (RI j ≠ 0 → RI j - 1 < R ∧ RL (RI j - 1) = j ∧
      keyK n w (mask w) BP nb (fun x => elF n w (mask w) (n * w) nb LR TR j
        (elF n w (mask w) (n * w) nb LR TR j x)) = KL (RC (RI j - 1))) := by
  unfold sqK at h
  rw [CIdx.strictB_eq, CIdx.strictB_eq] at h
  refine ⟨fun h0 i hi e => ?_, fun h0 => ?_⟩
  · rw [h0, show Nat.beq 0 0 = true from rfl] at h
    have := (allN_iff.1 h) i hi
    rw [show Nat.beq _ (KL i) = true from beq_iff.2 e] at this
    exact Bool.false_ne_true this
  · rw [show Nat.beq (RI j) 0 = false from Bool.eq_false_iff.2 fun e => h0 (beq_iff.1 e),
      CIdx.strictB_eq] at h
    obtain ⟨a1, a⟩ := (CIdx.bAnd_iff' _ _).1 h
    obtain ⟨a2, a3⟩ := (CIdx.bAnd_iff' _ _).1 a
    exact ⟨blt_iff.1 a1, beq_iff.1 a2, beq_iff.1 a3⟩

omit hQ in
theorem rootK_facts {N ncl p : Nat} {RL RC RI RO : Nat → Nat}
    (h : rootK N RL RC RI RO ncl p = true) :
    RL p < N ∧ RI (RL p) = p + 1 ∧ RC p < ncl ∧ RO (RC p) ≤ p ∧ p < RO (RC p + 1) := by
  unfold rootK at h
  rw [CIdx.strictB_eq, CIdx.strictB_eq] at h
  obtain ⟨a1, a⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨a2, a⟩ := (CIdx.bAnd_iff' _ _).1 a
  obtain ⟨a3, a4⟩ := (CIdx.bAnd_iff' _ _).1 a
  obtain ⟨b1, b2⟩ := inR_iff.1 a4
  exact ⟨blt_iff.1 a1, beq_iff.1 a2, blt_iff.1 a3, b1, b2⟩

theorem root_complete {mx N K ncl R : Nat} {E CL O RP RO KL RL RC RI : Nat → Nat}
    (hN : ordK LR nb = N) (hF : ClsFacts n S base kO nb N mx E CL O K ncl)
    (hhd : rootHdK n w (mask w) (n * w) BP nb LR TR E O RP RO KL ncl R = true)
    (hsq : ∀ j < N, sqK n w (mask w) (n * w) BP nb LR TR RL RC RI KL ncl R j = true)
    (hrt : ∀ p < R, rootK N RL RC RI RO ncl p = true)
    {i : Nat} (hi : i < ncl) {x : Equiv.Perm (Fin n)} (hx : x ∈ Gen n S kO)
    (hxx : x * x = el n S base nb (E (RP i))) :
    ∃ p < R, RC p = i ∧ el n S base nb (RL p) = x := by
  obtain ⟨-, -, hH⟩ := rootHdK_facts hhd
  obtain ⟨j, hj, rfl⟩ := el_surj hQ hx
  have hjN : j < N := hN ▸ hj
  obtain ⟨hs0, hs1⟩ := sqK_facts (hsq j hjN)
  have hsqA : Acts n (fun y => elF n w (mask w) (n * w) nb LR TR j
      (elF n w (mask w) (n * w) nb LR TR j y)) (el n S base nb j * el n S base nb j) := by
    intro y
    dsimp only
    rw [Equiv.Perm.mul_apply, acts_elF hQ j y, acts_elF hQ j]
  have hrepK : ∀ i' < ncl, E (RP i') < N ∧ RP i' < K ∧ CL (RP i') = i' := fun i' hi' => by
    obtain ⟨-, h1, h2, -⟩ := hH i' hi'
    obtain ⟨hk, hc⟩ := hF.blk_cl i' hi' (RP i') h1 h2
    exact ⟨hF.lt _ hk, hk, hc⟩
  have hrepM : ∀ i' < ncl, el n S base nb (E (RP i')) ∈ Gen n S kO := fun i' hi' =>
    el_mem' hQ hN (hrepK i' hi').1
  have hjj : el n S base nb j * el n S base nb j ∈ Gen n S kO :=
    Subgroup.mul_mem _ (el_mem hQ hj) (el_mem hQ hj)
  have hkey : ∀ i' < ncl, (keyK n w (mask w) BP nb (fun y => elF n w (mask w) (n * w) nb LR TR j
      (elF n w (mask w) (n * w) nb LR TR j y)) = KL i' ↔
      el n S base nb j * el n S base nb j = el n S base nb (E (RP i'))) := fun i' hi' => by
    rw [(hH i' hi').2.2.2]
    exact key_eq_iff hQ hsqA (acts_elF hQ _) hjj (hrepM i' hi')
  by_cases h0 : RI j = 0
  · exact absurd ((hkey i hi).2 hxx) (hs0 h0 i hi)
  · obtain ⟨hpR, hpj, hpk⟩ := hs1 h0
    obtain ⟨-, -, hc, -, -⟩ := rootK_facts (hrt _ hpR)
    have e := (hkey _ hc).1 hpk
    rw [hxx] at e
    have e1 := el_inj hQ (hN ▸ (hrepK i hi).1) (hN ▸ (hrepK _ hc).1) e
    have e2 := hF.inj _ (hrepK i hi).2.1 _ (hrepK _ hc).2.1 e1
    refine ⟨_, hpR, ?_, by rw [hpj]⟩
    rw [← (hrepK _ hc).2.2, ← e2, (hrepK i hi).2.2]

omit hQ in
theorem siftP_succ (d l : Nat) (g : Nat → Nat) :
    siftP n w (mask w) (n * w) LR TRI BP (d + 1) l g =
      Bool.rec (motive := fun _ => Option (Nat → Nat)) none
        (siftP n w (mask w) (n * w) LR TRI BP d (l + 1) (fun x => pg w (mask w)
          (TRI (roff n (n * w) (LR l) + rpos w (mask w) (n * w) (LR l) (g (pg w (mask w) BP l))))
          (g x)))
        (Nat.blt (rpos w (mask w) (n * w) (LR l) (g (pg w (mask w) BP l))) (rcnt (LR l))) :=
  rfl

theorem siftP_complete {f : Nat → Nat} {y : Equiv.Perm (Fin n)} (hf : Acts n f y)
    (hy : y ∈ Gen n S kO) : ∃ g, siftP n w (mask w) (n * w) LR TRI BP nb 0 f = some g ∧
      ∀ x : Fin n, g x = x := by
  have hbs := CFSG.KS.SporSch.CIdx.base_size hQ
  have hd' := CFSG.KS.SporSch.CIdx.hd hQ
  have hc := CFSG.KS.SporSch.CIdx.card_le hQ
  suffices key : ∀ d l, l + d = nb → ∀ (f : Nat → Nat) (y : Equiv.Perm (Fin n)), Acts n f y →
      y ∈ Fix n S kO base l → ∃ g, siftP n w (mask w) (n * w) LR TRI BP d l f = some g ∧
        ∀ x : Fin n, g x = x by
    exact key nb 0 (Nat.zero_add nb) f y hf (by rw [Fix_zero]; exact hy)
  intro d
  induction d with
  | zero =>
    intro l hl f y hf hy
    refine ⟨f, rfl, fun x => ?_⟩
    have hl' : l = base.size := by omega
    subst hl'
    rw [hf x, CFSG.KS.Raw.Orb.fix_one hd' hc hy]
    rfl
  | succ d ih =>
    intro l hl f y hf hy
    have hlb : l < nb := by omega
    have hlb' : l < base.size := by omega
    obtain ⟨A, hP⟩ := CFSG.KS.SporSch.CIdx.agree hQ hlb
    obtain ⟨k, hk, hyk⟩ := CFSG.KS.Raw.Orb.fix_surj hd' hc hlb' hy
    have hbl := hd'.base_lt l hlb'
    have hfb : f (pg w (mask w) BP l) = (CFSG.Certificates.ChainArrays.lev n S base l).pts[k]! := by
      rw [← CFSG.KS.SporSch.CIdx.base_eq hQ l hlb, ← hyk]
      exact hf ⟨_, hbl⟩
    have hz : (CFSG.Certificates.ChainArrays.lev n S base l).pts[k]! < n := by
      rw [← hyk]
      exact (y _).isLt
    have F := CFSG.KS.Raw.Orb.lev_facts hd' hlb'
    have hpk : (CFSG.Certificates.ChainArrays.lev n S base l).pos[
        (CFSG.Certificates.ChainArrays.lev n S base l).pts[k]!]! <
        (CFSG.Certificates.ChainArrays.lev n S base l).pts.size := by
      rw [F.pos_pts k hk]
      exact hk
    have hKe : rpos w (mask w) (n * w) (LR l)
        ((CFSG.Certificates.ChainArrays.lev n S base l).pts[k]!) = k := by
      rw [A.posE _ hz hpk, F.pos_pts k hk]
    have hkr : k < rcnt (LR l) := hKe ▸ (A.pos _ hz).2 hpk
    have hblt : Nat.blt k (rcnt (LR l)) = true := Nat.blt_eq.mpr hkr
    rw [siftP_succ, hfb, hKe, hblt]
    change ∃ g, siftP n w (mask w) (n * w) LR TRI BP d (l + 1)
      (fun x => pg w (mask w) (TRI (roff n (n * w) (LR l) + k)) (f x)) = some g ∧
        ∀ x : Fin n, g x = x
    have hT : permOfArr n (unpack n w (TR (roff n (n * w) (LR l) + k))) =
        CFSG.KS.Raw.Orb.trP n S base l k :=
      CFSG.KS.SporSch.CIdx.rep_unique' (A.tr k hk).1 (CFSG.KS.Raw.Orb.rep_tr hd' hlb' hk)
    have hTI := (hP k hkr).2
    rw [hT] at hTI
    have hTs := CFSG.KS.Raw.Orb.tr_spec hd' hlb' k hk
    have hTi := Subgroup.inv_mem _ hTs.1
    refine ih (l + 1) (by omega) _ ((CFSG.KS.Raw.Orb.trP n S base l k)⁻¹ * y) (fun x => ?_)
      ⟨Subgroup.mul_mem _ hTi.1 hy.1, fun t ht h => ?_⟩
    · rw [hf x]
      exact hTI (y x)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [Equiv.Perm.mul_apply, hy.2 t ht h, hTi.2 t ht h]
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
        apply Fin.ext
        rw [hTs.2]
        exact hyk

theorem cut_sound {ncl nx p : Nat} {E RP RL RC UO CU JO CJ X XI CT CP : Nat → Nat}
    {Xg : Nat → Equiv.Perm (Fin n)}
    (hX : ∀ t < nx, Orb.PRep n w (X t) (Xg t) ∧ Orb.PRep n w (XI t) (Xg t)⁻¹)
    (hcx : ∀ i < ncl, clsXK n w (mask w) (n * w) nb nx LR TR E RP X UO CU JO CJ i = true)
    (hrt : RC p < ncl)
    (hct : cutK n w (mask w) (n * w) BP nb LR TR TRI RL RC UO CU X XI CT CP p = true)
    (hCT : CT p ≠ 0) : ∃ t < nx,
      Xg t * el n S base nb (E (RP (RC p))) = el n S base nb (E (RP (RC p))) * Xg t ∧
      (Xg t)⁻¹ * el n S base nb (RL p) * Xg t ∉ Gen n S kO := by
  unfold cutK at hct
  rw [CIdx.strictB_eq, show Nat.beq (CT p) 0 = false from
    Bool.eq_false_iff.2 fun e => hCT (beq_iff.1 e)] at hct
  simp only [CIdx.strictB_eq] at hct
  obtain ⟨a1, a⟩ := (CIdx.bAnd_iff' _ _).1 hct
  obtain ⟨a2, a3⟩ := (CIdx.bAnd_iff' _ _).1 a
  have hu : UO (RC p) + (CT p - 1) < UO (RC p + 1) := blt_iff.1 a1
  have hc := hcx (RC p) hrt
  unfold clsXK at hc
  rw [CIdx.strictB_eq] at hc
  obtain ⟨-, c⟩ := (CIdx.bAnd_iff' _ _).1 hc
  obtain ⟨-, c⟩ := (CIdx.bAnd_iff' _ _).1 c
  obtain ⟨c1, -⟩ := (CIdx.bAnd_iff' _ _).1 c
  have c2 := (allN_iff.1 c1) (CT p - 1) (by
    change CT p - 1 < UO (RC p + 1) - UO (RC p)
    omega)
  rw [CIdx.strictB_eq] at c2
  obtain ⟨d1, d2⟩ := (CIdx.bAnd_iff' _ _).1 c2
  have hq : CP p < n := blt_iff.1 a2
  generalize ht : CU (UO (RC p) + (CT p - 1)) = t at d1 d2 a3
  have htx : t < nx := blt_iff.1 d1
  obtain ⟨hX1, hX2⟩ := hX t htx
  refine ⟨t, htx, ?_, fun hm => ?_⟩
  · refine Equiv.ext fun y => Fin.ext ?_
    have := beq_iff.1 ((allN_iff.1 d2) y y.isLt)
    dsimp only at this
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hX1 (el n S base nb _ y),
      ← acts_elF hQ _ y, ← acts_elF hQ _ (Xg t y), ← hX1 y]
    exact this
  · obtain ⟨g, hg, hgid⟩ := siftP_complete hQ (f := conjF w (mask w) (XI t) (X t)
      (elF n w (mask w) (n * w) nb LR TR (RL p))) (fun y => by
        unfold conjF
        rw [hX1 y, acts_elF hQ, hX2]
        rfl) hm
    rw [hg] at a3
    have e2 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (g (CP p)) (CP p)) = true :=
      a3
    have hgq : g (CP p) = CP p := hgid ⟨CP p, hq⟩
    rw [hgq, show Nat.beq (CP p) (CP p) = true from beq_iff.2 rfl] at e2
    exact Bool.false_ne_true e2

theorem pair_sound {N ncl R zc nq : Nat} {RL RC RI RO CT QC QJ : Nat → Nat}
    (hN : ordK LR nb = N) (hrt : ∀ p < R, rootK N RL RC RI RO ncl p = true)
    (hpk : ∀ p < R, pairK n w (mask w) (n * w) BP nb LR TR RL RC RO CT QC QJ zc nq p = true)
    {p q : Nat} (hp : p < R) (hq : q < R) (hcp : CT p = 0) (hcq : CT q = 0) (hc : RC q = RC p)
    (hz : RC p ≠ zc)
    (hxy : el n S base nb (RL p) * el n S base nb (RL q) * el n S base nb (RL p) =
      el n S base nb (RL q)) :
    ∃ mm < nq, QC mm = RC p ∧ (∃ k < 8, QJ (8 * mm + k) = RL p) ∧
      ∃ k < 8, QJ (8 * mm + k) = RL q := by
  obtain ⟨hpN, -, -, -, -⟩ := rootK_facts (hrt p hp)
  obtain ⟨hqN, -, -, hq1, hq2⟩ := rootK_facts (hrt q hq)
  have h := hpk p hp
  unfold pairK at h
  rw [CIdx.strictB_eq, show Nat.beq (CT p) 0 = true from beq_iff.2 hcp,
    show Nat.beq (RC p) zc = false from Bool.eq_false_iff.2 fun e => hz (beq_iff.1 e)] at h
  simp only [CIdx.strictB_eq] at h
  rw [hc] at hq1 hq2
  have h1 := (allN_iff.1 h) (q - RO (RC p)) (by
    change q - RO (RC p) < RO (RC p + 1) - RO (RC p)
    omega)
  have hq' : Nat.add (RO (RC p)) (q - RO (RC p)) = q := by
    change RO (RC p) + (q - RO (RC p)) = q
    omega
  rw [hq', hcq] at h1
  simp only [show Nat.beq 0 0 = true from rfl, CIdx.strictB_eq] at h1
  have hA : Acts n (fun x => elF n w (mask w) (n * w) nb LR TR (RL p)
      (elF n w (mask w) (n * w) nb LR TR (RL q) (elF n w (mask w) (n * w) nb LR TR (RL p) x)))
      (el n S base nb (RL p) * el n S base nb (RL q) * el n S base nb (RL p)) := by
    intro y
    dsimp only
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, acts_elF hQ (RL p) y,
      acts_elF hQ (RL q), acts_elF hQ (RL p)]
  have hpM := el_mem hQ (hN ▸ hpN)
  have hqM := el_mem hQ (hN ▸ hqN)
  have he := (eqB_iff_eq hQ hA (acts_elF hQ _) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hpM hqM)
    hpM) hqM).2 hxy
  simp only [he] at h1
  have h2 := Bool.eq_false_iff.1 (bNot_iff.1 h1)
  by_contra hne
  refine h2 (allN_iff.2 fun mm hmm => ?_)
  rw [bNot_iff, Bool.eq_false_iff]
  intro hb
  obtain ⟨b1, b⟩ := (CIdx.bAnd_iff' _ _).1 hb
  obtain ⟨b2, b3⟩ := (CIdx.bAnd_iff' _ _).1 b
  exact hne ⟨mm, hmm, beq_iff.1 b1, inQ_iff.1 b2, inQ_iff.1 b3⟩

omit hQ in
theorem clsXK_conj {nx i u : Nat} {E RP X XI UO CU JO CJ : Nat → Nat}
    {Xg : Nat → Equiv.Perm (Fin n)} {r : Equiv.Perm (Fin n)}
    (hr : Acts n (elF n w (mask w) (n * w) nb LR TR (E (RP i))) r)
    (hX : ∀ t < nx, Orb.PRep n w (X t) (Xg t) ∧ Orb.PRep n w (XI t) (Xg t)⁻¹)
    (h : clsXK n w (mask w) (n * w) nb nx LR TR E RP X UO CU JO CJ i = true)
    (hu : JO i + u < JO (i + 1)) :
    CJ (JO i + u) < nx ∧ Xg (CJ (JO i + u)) * r = r * Xg (CJ (JO i + u)) := by
  unfold clsXK at h
  rw [CIdx.strictB_eq] at h
  obtain ⟨-, c⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨-, c⟩ := (CIdx.bAnd_iff' _ _).1 c
  obtain ⟨-, c1⟩ := (CIdx.bAnd_iff' _ _).1 c
  have c2 := (allN_iff.1 c1) u (by
    change u < JO (i + 1) - JO i
    omega)
  rw [CIdx.strictB_eq] at c2
  obtain ⟨d1, d2⟩ := (CIdx.bAnd_iff' _ _).1 c2
  generalize ht : CJ (JO i + u) = t at d1 d2
  have htx : t < nx := blt_iff.1 d1
  obtain ⟨hX1, -⟩ := hX t htx
  refine ⟨htx, Equiv.ext fun y => Fin.ext ?_⟩
  have := beq_iff.1 ((allN_iff.1 d2) y y.isLt)
  dsimp only at this
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hX1 (r y), ← hr y, ← hr (Xg t y), ← hX1 y]
  exact this

omit hQ in
theorem acts_q8W {fA fB : Nat → Nat} {A B : Equiv.Perm (Fin n)} (hA : Acts n fA A)
    (hB : Acts n fB B) {k : Nat} (hk : k < 8) : Acts n (q8W fA fB k) (q8G A B k) := by
  intro y
  interval_cases k
  · rfl
  · change fA (fA y) = _
    rw [hA, hA]
    rfl
  · change fA y = _
    rw [hA]
    rfl
  · change fA (fA (fA y)) = _
    rw [hA, hA, hA]
    rfl
  · change fB y = _
    rw [hB]
    rfl
  · change fA (fA (fB y)) = _
    rw [hB, hA, hA]
    rfl
  · change fA (fB y) = _
    rw [hB, hA]
    rfl
  · change fA (fA (fA (fB y))) = _
    rw [hB, hA, hA, hA]
    rfl

theorem sub_facts {N ncl nx mm : Nat} {E RP JO CJ UO CU X XI QC QJ QW : Nat → Nat}
    {Xg : Nat → Equiv.Perm (Fin n)} (hN : ordK LR nb = N)
    (hX : ∀ t < nx, Orb.PRep n w (X t) (Xg t) ∧ Orb.PRep n w (XI t) (Xg t)⁻¹)
    (hcx : ∀ i < ncl, clsXK n w (mask w) (n * w) nb nx LR TR E RP X UO CU JO CJ i = true)
    (h : subK n w (mask w) (n * w) BP nb N ncl LR TR E RP JO CJ X XI QC QJ QW mm = true) :
    QC mm < ncl ∧ (∀ k < 8, QJ (8 * mm + k) < N) ∧ QJ (8 * mm + 1) = E (RP (QC mm)) ∧
      (∀ k < 8, el n S base nb (QJ (8 * mm + k)) =
        q8G (el n S base nb (QJ (8 * mm + 2))) (el n S base nb (QJ (8 * mm + 4))) k) ∧
      el n S base nb (QJ (8 * mm + 4)) * el n S base nb (QJ (8 * mm + 4)) =
        el n S base nb (QJ (8 * mm + 1)) ∧
      el n S base nb (QJ (8 * mm + 2)) * el n S base nb (QJ (8 * mm + 4)) *
        el n S base nb (QJ (8 * mm + 2)) = el n S base nb (QJ (8 * mm + 4)) ∧
      (∀ a < 5, CJ (JO (QC mm) + a) < nx ∧
        Xg (CJ (JO (QC mm) + a)) * el n S base nb (E (RP (QC mm))) =
          el n S base nb (E (RP (QC mm))) * Xg (CJ (JO (QC mm) + a))) ∧
      ∀ a < 5, ∀ b < 5, a < b → ∃ k < 8, ∀ k' < 8,
        (Xg (CJ (JO (QC mm) + b)))⁻¹ * Xg (CJ (JO (QC mm) + a)) * el n S base nb (QJ (8 * mm + k)) *
          (Xg (CJ (JO (QC mm) + a)))⁻¹ * Xg (CJ (JO (QC mm) + b)) ≠
            el n S base nb (QJ (8 * mm + k')) := by
  unfold subK at h
  simp only [CIdx.strictB_eq, Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨h1, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h2, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h3, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h4, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h5, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h6, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h7, h8⟩ := (CIdx.bAnd_iff' _ _).1 h
  have hi : QC mm < ncl := blt_iff.1 h1
  have hlt : ∀ k < 8, QJ (8 * mm + k) < N := fun k hk => blt_iff.1 ((allN_iff.1 h2) k hk)
  have hJO : JO (QC mm) + 5 ≤ JO (QC mm + 1) := ble_iff.1 h7
  have hM : ∀ k < 8, el n S base nb (QJ (8 * mm + k)) ∈ Gen n S kO := fun k hk =>
    el_mem' hQ hN (hlt k hk)
  have hac := fun k => acts_elF hQ (QJ (8 * mm + k))
  set A := el n S base nb (QJ (8 * mm + 2))
  set B := el n S base nb (QJ (8 * mm + 4))
  have hAM := hM 2 (by norm_num)
  have hBM := hM 4 (by norm_num)
  have hq8M : ∀ k < 8, q8G A B k ∈ Gen n S kO := by
    intro k hk
    have m := fun x y => Subgroup.mul_mem (Gen n S kO) (x := x) (y := y)
    interval_cases k <;> simp only [q8G] <;> norm_num <;>
      first
        | exact Subgroup.one_mem _
        | exact hAM
        | exact hBM
        | exact m _ _ hAM hAM
        | exact m _ _ (m _ _ hAM hAM) hAM
        | exact m _ _ (m _ _ hAM hAM) hBM
        | exact m _ _ hAM hBM
        | exact m _ _ (m _ _ (m _ _ hAM hAM) hAM) hBM
  refine ⟨hi, hlt, beq_iff.1 h3, fun k hk => ?_, ?_, ?_, fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · exact (eqB_iff_eq hQ (hac k) (acts_q8W (hac 2) (hac 4) hk) (hM k hk) (hq8M k hk)).1
      ((allN_iff.1 h4) k hk)
  · refine (eqB_iff_eq hQ (fun y => ?_) (hac 1) (Subgroup.mul_mem _ hBM hBM)
      (hM 1 (by norm_num))).1 h5
    rw [Equiv.Perm.mul_apply, hac 4 y, hac 4]
  · refine (eqB_iff_eq hQ (fun y => ?_) (hac 4) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hAM hBM)
      hAM) hBM).1 h6
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hac 2 y, hac 4, hac 2]
  · exact clsXK_conj (acts_elF hQ _) hX (hcx _ hi) (by omega)
  · obtain ⟨hta, -⟩ := clsXK_conj (acts_elF hQ _) hX (hcx _ hi) (u := a) (by omega)
    obtain ⟨htb, -⟩ := clsXK_conj (acts_elF hQ _) hX (hcx _ hi) (u := b) (by omega)
    have g1 := (allN_iff.1 ((allN_iff.1 h8) a ha)) b hb
    simp only [show Nat.blt a b = true from blt_iff.2 hab, CIdx.strictB_eq] at g1
    obtain ⟨k1, k2⟩ := (CIdx.bAnd_iff' _ _).1 g1
    generalize hta' : CJ (JO (QC mm) + a) = ta at k2 hta
    generalize htb' : CJ (JO (QC mm) + b) = tb at k2 htb
    obtain ⟨hXa, hXa'⟩ := hX ta hta
    obtain ⟨hXb, hXb'⟩ := hX tb htb
    refine ⟨_, blt_iff.1 k1, fun k' hk' e => ?_⟩
    have k3 := (allN_iff.1 k2) k' hk'
    rw [bNot_iff, Bool.eq_false_iff] at k3
    refine k3 ?_
    unfold eqAllK
    refine allN_iff.2 fun x hx => beq_iff.2 ?_
    obtain ⟨y, rfl⟩ : ∃ y : Fin n, (y : Nat) = x := ⟨⟨x, hx⟩, rfl⟩
    have e' := congrArg (fun g : Equiv.Perm (Fin n) => (g y : Nat)) e
    simp only [Equiv.Perm.mul_apply] at e'
    dsimp only
    rw [hXb y, hXa', hac, hXa, hXb', hac]
    exact e'

end Chain

end CFSG.KS.SporSch.RPair

end
