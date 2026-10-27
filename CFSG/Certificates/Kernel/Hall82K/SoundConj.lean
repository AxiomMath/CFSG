module

public import CFSG.Certificates.Kernel.Hall82K.SoundC5
public import Certificates.Data.Kernel.Hall82K.MGens
public import CFSG.Certificates.Kernel.Hall82K.SoundAff

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HeSylow
open CFSG.CGT.Hall82 CFSG.Monster.B.Co2 CFSG.RankThree.Native

@[expose] def KPres (f : Equiv.Perm (Fin 64)) : Prop :=
  (∀ v w, f (xorF v w) = xorF (f v) (f w)) ∧ ∀ v, IsOvalVec v → IsOvalVec (f v)

theorem kPres_mul {f g : Equiv.Perm (Fin 64)} (hf : KPres f) (hg : KPres g) : KPres (f * g) :=
  ⟨fun v w => by
    simp only [Equiv.Perm.mul_apply]
    rw [hg.1, hf.1], fun v hv => hf.2 _ (hg.2 _ hv)⟩

theorem kPres_one : KPres 1 := ⟨fun _ _ => rfl, fun _ hv => hv⟩

theorem kPres_pow {f : Equiv.Perm (Fin 64)} (hf : KPres f) : ∀ k : ℕ, KPres (f ^ k)
  | 0 => by
    rw [pow_zero]
    exact kPres_one
  | k + 1 => by
    rw [pow_succ]
    exact kPres_mul (kPres_pow hf k) hf

theorem kPres_inv {f : Equiv.Perm (Fin 64)} (hf : KPres f) : KPres f⁻¹ := by
  have h : f⁻¹ = f ^ (orderOf f - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos f), pow_orderOf_eq_one]
  rw [h]
  exact kPres_pow hf _

@[expose] def kPresSub : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {f | KPres f}
  mul_mem' := kPres_mul
  one_mem' := kPres_one
  inv_mem' := kPres_inv

theorem kPresK_spec (hkm : allN (fun v => beqB (memL v hallKList) (inKK v)) 64 = true) {c : ℕ}
    (h : kPresK c = true) : ∀ v, IsOvalVec v → IsOvalVec (fnL c v) := by
  intro v hv
  have h1 := allN_iff.1 h v.val v.2
  rw [bor_eq_true, bnot_eq_true] at h1
  rcases h1 with h1 | h1
  · rw [(inKK_iff hkm v).2 hv] at h1
    exact absurd h1 (by simp)
  · exact (inKK_iff hkm (fnL c v)).1 h1

theorem hexaM_kPres (hc : hexaCheck = true) (hmg : zipArrK hexaMGensK hexaMGens = true)
    (hmk : allL kPresK hexaMGensK = true)
    (hkm : allN (fun v => beqB (memL v hallKList) (inKK v)) 64 = true) :
    ∀ s ∈ hexaM, KPres s := by
  intro s hs
  refine (grpN_le (K := kPresSub) (fun a ha => ?_)) hs
  have hrep := rep_of_validA (validA_of_mem (hexaCheck_parts hc).2.1 ha)
  obtain ⟨c, hcm, hca⟩ := forall₂_mem_right (zipArrK_spec hmg) ha
  have he : ⇑(permOfArr 64 a) = fnL c := funext fun v => Fin.ext (by
    rw [← hrep v, codeArrK_getElem hca v.2]
    rfl)
  change KPres (permOfArr 64 a)
  unfold KPres
  rw [he]
  exact ⟨fnL_add c, kPresK_spec hkm (allL_iff.1 hmk c hcm)⟩

theorem c5K_lt : ∀ w ∈ c5K, w < 2 ^ 72 := by decide +kernel

theorem land_m36_lt (w : ℕ) : Nat.land w m36K < 2 ^ 36 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem shr36_lt {w : ℕ} (hw : w < 2 ^ 72) : Nat.shiftRight w 36 < 2 ^ 36 := by
  change w >>> 36 < 2 ^ 36
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hw)

theorem codeA_of_fnL {g : Fin 64 → Fin 64} {c : ℕ} (hg : g = fnL c) (hc : c < 2 ^ 36) :
    codeA g = c ∧ IsAff g := by
  subst hg
  refine ⟨?_, isAff_of_add (fnL_add c) (fnL_zero c)⟩
  unfold codeA
  rw [linPart_of_add (fnL_add c) (fnL_zero c), codeL_fnL hc, fnL_zero]
  change c ||| 0 <<< 36 = c
  rw [Nat.zero_shiftLeft, Nat.or_zero]

theorem inv_eq_fnL {s : Equiv.Perm (Fin 64)} {w : ℕ} (hs : ⇑s = fnL (Nat.land w m36K))
    (hi : compL (Nat.land w m36K) (Nat.shiftRight w 36) = idK) :
    ⇑s⁻¹ = fnL (Nat.shiftRight w 36) := by
  funext v
  have h := congrFun (fnL_compL (Nat.land w m36K) (Nat.shiftRight w 36)) v
  rw [hi, fnL_idK, ← hs] at h
  exact Equiv.Perm.inv_eq_iff_eq.2 h

section Conj

variable (hrm : zipArrK rmK hallRMArr = true)
  (hinv : allL (fun r => Nat.beq (compL r r) idK) rmK = true)
  (hs40 : zipArrK s40K hallS40Arr = true) (hc5 : c5InvK = true)

include hrm hinv hs40 hc5 in
theorem conj_of_ok {b : Fin 64} {w : ℕ} (hw : w ∈ c5K) (hok : conjOkK b.val w = true)
    {s : Equiv.Perm (Fin 64)} (hs : ⇑s = fnL (Nat.land w m36K)) :
    fnL (sigK b.val w) ∈ hallS40 ∧ ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = fnL (sigK b.val w) (xcode x) := by
  unfold conjOkK at hok
  rw [band_eq_true, memL_iff] at hok
  have hi := nbeq_iff.1 (allL_iff.1 hc5 w hw)
  have hsi := inv_eq_fnL hs hi
  obtain ⟨cs, as⟩ := codeA_of_fnL hs (land_m36_lt w)
  obtain ⟨ci, ai⟩ := codeA_of_fnL hsi (shr36_lt (c5K_lt w hw))
  refine ⟨fnL_mem_hallS40 hs40 hok.1, fun x hx => ?_⟩
  have hxa := (x1_code hrm hinv hx).1
  have hk : Nat.beq (conjXK b.val w (codeA x)) (apL (sigK b.val w) (xcodeK (codeA x))) = true :=
    allX1_code hrm hinv hok.2 hx
  have ht := isAff_transl b
  have e : conjXK b.val w (codeA x) =
      (xcode (transl b * s * x * (s⁻¹ * transl b))).val := by
    unfold conjXK
    rw [← codeA_transl b, ← cs, ← ci, compA_codeA_mul ht as,
      compA_codeA_mul (isAff_mul ht as) hxa, compA_codeA_mul ai ht,
      compA_codeA_mul (isAff_mul (isAff_mul ht as) hxa) (isAff_mul ai ht), xcodeK_codeA]
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (transl_mul_self b)]
  apply Fin.ext
  rw [← e, nbeq_iff.1 hk, xcodeK_codeA]
  rfl

include hrm hinv hs40 hc5 in
theorem xcode_conj_of (hc : hexaCheck = true) (hidx : idxBridgeK = true)
    (hkm : allN (fun v => beqB (memL v hallKList) (inKK v)) 64 = true)
    (hmg : zipArrK hexaMGensK hexaMGens = true) (hmk : allL kPresK hexaMGensK = true)
    (hsrch : c5SrchK c5LinK 6 0 = true) (hconj : ∀ b < 64, conjRowK b = true) :
    ∀ b, ∀ s ∈ hexaM, s 5 = 5 → ∃ σ ∈ hallS40, ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x) := by
  intro b s hs h5
  obtain ⟨hadd, hK⟩ := hexaM_kPres hc hmg hmk hkm s hs
  have hmem := c5SrchK_sound hidx hkm hadd hK h5 hsrch s.injective
  unfold c5LinK at hmem
  obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hmem
  have hwe' : Nat.land w m36K = codeL s := hwe
  have hs' : ⇑s = fnL (Nat.land w m36K) := by rw [hwe', fnL_codeL hadd]
  have hok : conjOkK b.val w = true := allL_iff.1 (hconj b.val b.2) w hw
  obtain ⟨hσ, hx⟩ := conj_of_ok hrm hinv hs40 hc5 hw hok hs'
  exact ⟨_, hσ, hx⟩

theorem surjRec_spec : ∀ (S W : List ℕ),
    (List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
      (fun σ _ ih W => List.rec (motive := fun _ => Bool) false
        (fun e W' _ => band (witOkK σ e) (ih W')) W) S W : Bool) = true →
    ∀ c ∈ S, ∃ e, witOkK c e = true := by
  intro S
  induction S with
  | nil => intro _ _ c hc; simp at hc
  | cons σ S ih =>
    intro W h c hc
    cases W with
    | nil => exact absurd h (by simp)
    | cons e W' =>
      change band (witOkK σ e) (List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
        (fun σ _ ih W => List.rec (motive := fun _ => Bool) false
          (fun e W' _ => band (witOkK σ e) (ih W')) W) S W') = true at h
      rw [band_eq_true] at h
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨e, h.1⟩
      · exact ih W' h.2 c hc

include hrm hinv hs40 hc5 in
theorem xcode_conj_surj_of (hc : hexaCheck = true) (hst : hexaStabCheck = true)
    (hconj : ∀ b < 64, conjRowK b = true) (hsurj : conjSurjK = true)
    (hoval : allL (fun w => ovalOkK (Nat.land w m36K)) c5K = true)
    (hfix : allL (fun w => Nat.beq (apL (Nat.land w m36K) 5) 5) c5K = true) :
    ∀ σ ∈ hallS40, ∃ b, ∃ s ∈ hexaM, s 5 = 5 ∧ ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x) := by
  rintro σ ⟨a, ha, hσa⟩
  obtain ⟨c, hcm, hca⟩ := forall₂_mem_right (zipArrK_spec hs40) ha
  have hσ : σ = fnL c := funext fun k => Fin.ext (by
    rw [hσa k, (codeArrK_spec hca).2 k.val k.2]
    rfl)
  obtain ⟨e, he⟩ := surjRec_spec s40K s40WitK hsurj c hcm
  unfold witOkK at he
  rw [band_eq_true, memL_iff, nbeq_iff] at he
  obtain ⟨hw, hsig⟩ := he
  have hi := nbeq_iff.1 (allL_iff.1 hc5 _ hw)
  have hsur : Function.Surjective (fnL (Nat.land (Nat.shiftRight e 6) m36K)) := fun v => by
    refine ⟨fnL (Nat.shiftRight (Nat.shiftRight e 6) 36) v, ?_⟩
    have h := congrFun (fnL_compL (Nat.land (Nat.shiftRight e 6) m36K)
      (Nat.shiftRight (Nat.shiftRight e 6) 36)) v
    rw [hi, fnL_idK] at h
    exact h.symm
  let s : Equiv.Perm (Fin 64) := Equiv.ofBijective _
    ⟨Finite.injective_iff_surjective.2 hsur, hsur⟩
  have hs : ⇑s = fnL (Nat.land (Nat.shiftRight e 6) m36K) := rfl
  let b : Fin 64 := ⟨Nat.land e 63, lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩
  have hm : s ∈ hexaM := by
    refine mem_hexaM_of_stab hc hst (fun v w => by rw [hs]; exact fnL_add _ v w) ?_
    have ho := allL_iff.1 hoval _ hw
    unfold ovalOkK at ho
    intro L hL
    have h1 := allLL_iff.1 ho L hL
    rw [anyLL_iff] at h1
    obtain ⟨L', hL', hall⟩ := h1
    refine ⟨L', hL', fun x hx => ?_⟩
    have h2 := allL_iff.1 hall x.val hx
    rw [memL_iff] at h2
    exact h2
  have h5 : s 5 = 5 := Fin.ext (nbeq_iff.1 (allL_iff.1 hfix _ hw))
  have hok : conjOkK b.val (Nat.shiftRight e 6) = true := allL_iff.1 (hconj b.val b.2) _ hw
  obtain ⟨-, hx⟩ := conj_of_ok hrm hinv hs40 hc5 hw hok hs
  refine ⟨b, s, hm, h5, fun x hx' => ?_⟩
  rw [hx x hx', hσ]
  change fnL (sigK (Nat.land e 63) (Nat.shiftRight e 6)) _ = _
  rw [hsig]

end Conj

end CFSG.KC.Hall82K
