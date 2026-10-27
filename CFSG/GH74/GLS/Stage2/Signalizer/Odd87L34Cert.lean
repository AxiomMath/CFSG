module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cls3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Pgl
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import Certificates.Certificate5180

public section

open Subgroup CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four CFSG.PSL3Four.Native CFSG
  CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem CC_zero : CC 0 = C₁ := rfl
theorem CC_one : CC 1 = C₂ := rfl
theorem CC_two : CC 2 = C₃ := rfl
theorem CC_three : CC 3 = C₄ := rfl

theorem wit_of_checks {i : Fin 4} {rT : Tab}
    (hr : TabRep rT (rr i)) {D Di exc : Array Tab} (hD : Enumerates (CC i) D.toList)
    (hinv : invsOK 42 D Di = true) (h3 : witOK 42 3 enumR.tabs D Di exc rT = true)
    (h5 : witOK 42 5 enumR.tabs D Di exc rT = true) (h7 : witOK 42 7 enumR.tabs D Di exc rT = true)
    (Exc : Equiv.Perm (Fin 42) → Prop)
    (hexc : ∀ (y : Equiv.Perm (Fin 42)) (t : Tab), TabRep t y → t ∈ exc.toList → Exc y) :
    ∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ y ∈ R, y ≠ 1 → y ^ p = 1 → rr i * y * rr i * y = 1 →
      Exc y ∨ (∃ d ∈ CC i, (y * (d * y * d⁻¹)) ^ p ≠ 1) ∨
        (∃ d ∈ CC i, ∃ d' ∈ CC i, (y * (d * y * d⁻¹) * (d' * y * d'⁻¹)) ^ p ≠ 1) := by
  intro p hp y hy hy1 hyp hry
  have hw : witOK 42 p enumR.tabs D Di exc rT = true := by
    rcases hp with rfl | rfl | rfl
    exacts [h3, h5, h7]
  exact witOK_spec enumerates_R hD hinv hr hw Exc hexc hy hy1 hyp hry

theorem l34Facts : ∃ z, L34Facts z := by
  have h : l34AutCheck enumS.tabs enumR.tabs = true := Certificates.certificate5180
  simp only [l34AutCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hi1, hi2, hi3, hi4,
    w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ := h
  obtain ⟨k, hk, hkz⟩ := memTab_iff.1 hz1
  obtain ⟨z, hzR, hzrep⟩ := enumerates_R.exists_elt hk
  rw [hkz] at hzrep
  have hz2n : ¬ zT = idTab 42 := by simpa using hz2
  have hz3' : z ^ 3 = 1 := ((hzrep.pow 3).beq_iff TabRep.idTab).1 hz3
  have hzi : z⁻¹ = z * z := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_three]
    exact hz3'
  have hzz : TabRep z2T (z * z) := hzrep.comp hzrep
  have hr3r3 : r₃ * r₃ = 1 := g₆_mul_g₆
  have hr3i : r₃⁻¹ = r₃ := inv_eq_of_mul_eq_one_right hr3r3
  refine ⟨z, ?_⟩
  refine
    { z_mem := hzR
      z_ne := fun h1 => hz2n ((hzrep.eq_iff TabRep.idTab).2 h1)
      z_cube := hz3'
      z_inv := ?_
      z_notS := not_mem_of_notInOK enumerates_S hz5 hzrep
      zi_notS := ?_
      rz_notS := not_mem_of_notInOK enumerates_S hz7 (tabRep_r₃.comp hzrep)
      rzi_notS := ?_
      z_comm := ?_
      cent_le := ?_
      scan := ?_
      exp27 := fun x hx h27 => expOK_spec enumerates_R hz12 hx h27
      wit := ?_ }
  · have e : r₃ * z * r₃ = z * z :=
      (((tabRep_r₃.comp hzrep).comp tabRep_r₃).beq_iff hzz).1 hz4
    rw [hr3i, hzi, e]
  · rw [hzi]
    exact not_mem_of_notInOK enumerates_S hz6 hzz
  · rw [hzi]
    exact not_mem_of_notInOK enumerates_S hz8 (tabRep_r₃.comp hzz)
  · intro d hd
    obtain ⟨a, ha, hda⟩ := enumerates_C₃.exists_pos hd
    exact ((hda.comp hzrep).beq_iff (hzrep.comp hda)).1 ((allBelow_eq_true.1 hz9) a ha)
  · intro s hs hsz
    obtain ⟨k, hk, hsk⟩ := enumerates_S.exists_pos hs
    have h1 := (allBelow_eq_true.1 hz10) k hk
    have h2 : (comp 42 enumS.tabs[k]! zT == comp 42 zT enumS.tabs[k]!) = true :=
      ((hsk.comp hzrep).beq_iff (hzrep.comp hsk)).2 hsz
    simp only [h2, Bool.not_true, Bool.false_or] at h1
    exact ((hsk.comp tabRep_r₃).beq_iff (tabRep_r₃.comp hsk)).1 h1
  · intro x hx hxc
    obtain ⟨t, ht, hrep⟩ := centScanOK_spec enumerates_R hz11 hx (fun i hi => by
      obtain ⟨a, ha, hda⟩ := enumerates_C₃.exists_elt hi
      exact ⟨a, hda, hxc a ha⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (TabRep.idTab.perm_eq hrep).symm
    · exact Or.inr (Or.inl (hzrep.perm_eq hrep).symm)
    · exact Or.inr (Or.inr (Or.inl (by rw [hzi]; exact (hzz.perm_eq hrep).symm)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (tabRep_r₃.perm_eq hrep).symm)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((hzrep.comp tabRep_r₃).perm_eq hrep).symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by rw [hzi]; exact ((hzz.comp tabRep_r₃).perm_eq hrep).symm)))))
  · have hexc3 : ∀ (y : Equiv.Perm (Fin 42)) (t : Tab), TabRep t y → t ∈ (#[zT, z2T] : Array Tab).toList →
        y = z ∨ y = z⁻¹ := by
      intro y t hty ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact Or.inl (hzrep.perm_eq hty).symm
      · exact Or.inr (by rw [hzi]; exact (hzz.perm_eq hty).symm)
    intro i p hp y hy hy1 hyp hry
    fin_cases i
    · rcases wit_of_checks (i := 0) tabRep_r₁ enumerates_C₁ hi1 w1 w2 w3 (fun _ => False) (by simp) p hp y hy
        hy1 hyp hry with h | h | h
      · exact h.elim
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases wit_of_checks (i := 1) tabRep_r₂ enumerates_C₂ hi2 w4 w5 w6 (fun _ => False) (by simp) p hp y hy
        hy1 hyp hry with h | h | h
      · exact h.elim
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases wit_of_checks (i := 2) tabRep_r₃ enumerates_C₃ hi3 w7 w8 w9 (fun y => y = z ∨ y = z⁻¹) hexc3 p hp
        y hy hy1 hyp hry with h | h | h
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases wit_of_checks (i := 3) tabRep_r₄ enumerates_C₄ hi4 w10 w11 w12 (fun _ => False) (by simp) p hp y
        hy hy1 hyp hry with h | h | h
      · exact h.elim
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

theorem exists_class_rep {α : MulAut ↥S} (h2 : α * α = 1)
    (h1 : α ≠ 1) :
    ∃ (i : Fin 4) (ψ : MulAut ↥S), MulAut.congr ψ α = Cls3.conjIso (rrR i) := by
  set Φ := Cls3.conjIso with hΦ
  set a : ↥R := Φ.symm α with ha
  have haα : Φ a = α := Φ.apply_symm_apply α
  have hord : orderOf a = 2 := by
    apply orderOf_eq_prime
    · apply Φ.injective
      rw [pow_two, map_mul, haα, h2, map_one]
    · intro h
      apply h1
      rw [← haα, h, map_one]
  have hi : ∃ i : Fin 4, IsConj (rrR i) a := by
    rcases (orderOf_eq_two_iff a).1 hord with h | h | h | h
    · exact ⟨0, isConj_comm.1 h⟩
    · exact ⟨1, isConj_comm.1 h⟩
    · exact ⟨2, isConj_comm.1 h⟩
    · exact ⟨3, isConj_comm.1 h⟩
  obtain ⟨i, hi⟩ := hi
  obtain ⟨c, hc⟩ := isConj_iff.1 hi
  refine ⟨i, (Φ c)⁻¹, ?_⟩
  have hcongr : MulAut.congr ((Φ c)⁻¹) α = (Φ c)⁻¹ * α * Φ c := by
    ext x
    rfl
  rw [hcongr, ← haα, ← hc]
  simp only [map_mul, map_inv]
  group

theorem wit_R {z : Equiv.Perm (Fin 42)} (F : L34Facts z) (i : Fin 4) (p : ℕ)
    (hp : p = 3 ∨ p = 5 ∨ p = 7) :
    ∀ y : ↥R, y ≠ 1 → y ^ p = 1 → rrR i * y * rrR i * y = 1 →
      (i = 2 ∧ (y = ⟨z, F.z_mem⟩ ∨ y = ⟨z, F.z_mem⟩⁻¹)) ∨
      (∃ d : ↥R, (d : Equiv.Perm (Fin 42)) ∈ CC i ∧ (y * (d * y * d⁻¹)) ^ p ≠ 1) ∨
      (∃ d : ↥R, (d : Equiv.Perm (Fin 42)) ∈ CC i ∧ ∃ d' : ↥R, (d' : Equiv.Perm (Fin 42)) ∈ CC i ∧
        (y * (d * y * d⁻¹) * (d' * y * d'⁻¹)) ^ p ≠ 1) := by
  intro y hy1 hyp hry
  have hy1' : (y : Equiv.Perm (Fin 42)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyp' : (y : Equiv.Perm (Fin 42)) ^ p = 1 := by
    simpa using congrArg Subtype.val hyp
  have hry' : rr i * (y : Equiv.Perm (Fin 42)) * rr i * (y : Equiv.Perm (Fin 42)) = 1 := by
    simpa [coe_rrR] using congrArg Subtype.val hry
  rcases F.wit i p hp y y.2 hy1' hyp' hry' with ⟨hi, h⟩ | ⟨d, hd, hne⟩ | ⟨d, hd, d', hd', hne⟩
  · refine Or.inl ⟨hi, ?_⟩
    rcases h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (by simpa using h))
  · refine Or.inr (Or.inl ⟨⟨d, S_le_R (mem_CC.1 hd).2⟩, hd, fun h => hne ?_⟩)
    simpa using congrArg Subtype.val h
  · refine Or.inr (Or.inr ⟨⟨d, S_le_R (mem_CC.1 hd).2⟩, hd, ⟨d', S_le_R (mem_CC.1 hd').2⟩, hd',
      fun h => hne ?_⟩)
    simpa using congrArg Subtype.val h

theorem pow_eq_one_of_orderOf {z : Equiv.Perm (Fin 42)}
    (F : L34Facts z) {p k : ℕ} (hp : p = 3 ∨ p = 5 ∨ p = 7) {x : ↥R} (hk : orderOf x = p ^ k) : x ^ p = 1 := by
  have hdvd : p ^ k ∣ 241920 := by
    have := orderOf_dvd_natCard x
    rwa [card_R, hk] at this
  rcases hp with rfl | rfl | rfl
  · have hk3 : k ≤ 3 := by
      by_contra hlt
      have h4 : 3 ^ 4 ∣ 241920 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at h4
    have h27 : x ^ 27 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hk]
      show 3 ^ k ∣ 3 ^ 3
      exact Nat.pow_dvd_pow 3 hk3
    have := F.exp27 (x : Equiv.Perm (Fin 42)) x.2 (by simpa using congrArg Subtype.val h27)
    exact Subtype.ext (by simpa using this)
  · have hk1 : k ≤ 1 := by
      by_contra hlt
      have h2 : 5 ^ 2 ∣ 241920 := (pow_dvd_pow 5 (by omega)).trans hdvd
      norm_num at h2
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    simpa using Nat.pow_dvd_pow 5 hk1
  · have hk1 : k ≤ 1 := by
      by_contra hlt
      have h2 : 7 ^ 2 ∣ 241920 := (pow_dvd_pow 7 (by omega)).trans hdvd
      norm_num at h2
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    simpa using Nat.pow_dvd_pow 7 hk1

theorem cfg_rep {z : Equiv.Perm (Fin 42)} (F : L34Facts z) (i : Fin 4) {p : ℕ}
    {X : Subgroup (MulAut ↥S)} (h : AutCfg ↥S (Cls3.conjIso (rrR i)) p X) :
    i = 2 ∧ X = zpowers (Cls3.conjIso (⟨z, F.z_mem⟩ : ↥R)) := by
  set Φ := Cls3.conjIso with hΦ
  set ζ : ↥R := ⟨z, F.z_mem⟩ with hζ
  have : Fact p.Prime := ⟨h.prime⟩
  have hord : ∀ x ∈ X, ∃ k, orderOf (Φ.symm x) = p ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h.pgroup) ⟨x, hx⟩
    refine ⟨k, ?_⟩
    rw [← hk, Subgroup.orderOf_mk x hx]
    exact orderOf_injective Φ.symm.toMonoidHom Φ.symm.injective x
  have hp357 : p = 3 ∨ p = 5 ∨ p = 7 := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h.ne_bot
    obtain ⟨k, hk⟩ := hord a a.2
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply ha1
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact Subtype.ext (by simpa using hk)
    have hdvd : p ∣ 241920 := by
      have h1 := orderOf_dvd_natCard (Φ.symm (a : MulAut ↥S))
      rw [card_R, hk] at h1
      exact (dvd_pow_self p hk0).trans h1
    have h241 : (241920 : ℕ) = 2 ^ 8 * 3 ^ 3 * 5 * 7 := by norm_num
    rw [h241] at hdvd
    rcases (Nat.Prime.dvd_mul h.prime).1 hdvd with h' | h'
    · rcases (Nat.Prime.dvd_mul h.prime).1 h' with h'' | h''
      · rcases (Nat.Prime.dvd_mul h.prime).1 h'' with h3 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1
            (h.prime.dvd_of_dvd_pow h3)) h.odd
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1
            (h.prime.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq h.prime (by norm_num)).1 h''))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq h.prime (by norm_num)).1 h'))
  set Xr : Subgroup ↥R := X.map Φ.symm.toMonoidHom with hXr
  have hmemXr : ∀ x : ↥R, x ∈ Xr ↔ Φ x ∈ X := fun x => by
    rw [hXr, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hexp : ∀ x ∈ Xr, x ^ p = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hord (Φ x) ((hmemXr x).1 hx)
    rw [MulEquiv.symm_apply_apply] at hk
    exact pow_eq_one_of_orderOf F hp357 hk
  have ha2 : rrR i * rrR i = 1 := by
    apply Φ.injective
    rw [map_mul, h.alpha_sq, map_one]
  have haN : rrR i ∈ normalizer (Xr : Set ↥R) := by
    have := Subgroup.mem_map_of_mem Φ.symm.toMonoidHom h.alpha_norm
    rw [Transport.map_normalizer] at this
    have e : Φ.symm.toMonoidHom (Φ (rrR i)) = rrR i := Φ.symm_apply_apply _
    rwa [e] at this
  have hcomm : ⁅Xr, zpowers (rrR i)⁆ = Xr := by
    have := congrArg (Subgroup.map Φ.symm.toMonoidHom) h.comm
    rw [Transport.map_commutator, Transport.map_zpowers, MulEquiv.symm_apply_apply] at this
    exact this
  set D : Set ↥R := {d | (d : Equiv.Perm (Fin 42)) ∈ CC i} with hD
  have hDnorm : ∀ d ∈ D, d ∈ normalizer (Xr : Set ↥R) := by
    intro d hd
    obtain ⟨hdc, hdS⟩ := mem_CC.1 hd
    have hΦd : Φ d = MulAut.conj (⟨d, hdS⟩ : ↥S) := MulEquiv.ext fun t => Subtype.ext rfl
    have hcomm' : Φ (rrR i) * MulAut.conj (⟨d, hdS⟩ : ↥S) =
        MulAut.conj (⟨d, hdS⟩ : ↥S) * Φ (rrR i) := by
      rw [← hΦd, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simpa [coe_rrR] using hdc
    have h1 := h.cent_norm ⟨d, hdS⟩ hcomm'
    rw [← hΦd] at h1
    have := Subgroup.mem_map_of_mem Φ.symm.toMonoidHom h1
    rw [Transport.map_normalizer] at this
    have e : Φ.symm.toMonoidHom (Φ d) = d := Φ.symm_apply_apply _
    rwa [e] at this
  set Exc : Set ↥R := {y | i = 2 ∧ (y = ζ ∨ y = ζ⁻¹)} with hExc
  have hwit : ∀ y : ↥R, y ≠ 1 → y ^ p = 1 → rrR i * y * rrR i * y = 1 → y ∈ Exc ∨
      (∃ d ∈ D, (y * (d * y * d⁻¹)) ^ p ≠ 1) ∨
      (∃ d ∈ D, ∃ d' ∈ D, (y * (d * y * d⁻¹) * (d' * y * d'⁻¹)) ^ p ≠ 1) := by
    intro y hy1 hyp hry
    rcases wit_R F i p hp357 y hy1 hyp hry with ⟨hi, hy⟩ | ⟨d, hd, hne⟩ | ⟨d, hd, d', hd', hne⟩
    · exact Or.inl ⟨hi, hy⟩
    · exact Or.inr (Or.inl ⟨d, hd, hne⟩)
    · exact Or.inr (Or.inr ⟨d, hd, d', hd', hne⟩)
  have hle : Xr ≤ closure Exc := le_closure_exc ha2 haN hcomm hexp hexp D hDnorm Exc hwit
  have hXr_ne : Xr ≠ ⊥ := fun hb =>
    h.ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ Φ.symm.injective).1 hb)
  have hi2 : i = 2 := by
    by_contra hne
    have hE : Exc = ∅ := by
      ext y
      simp [hExc, hne]
    rw [hE, Subgroup.closure_empty, le_bot_iff] at hle
    exact hXr_ne hle
  have hle2 : Xr ≤ zpowers ζ := by
    refine hle.trans ((Subgroup.closure_le _).2 ?_)
    rintro y ⟨-, hy | hy⟩
    · rw [hy]
      exact mem_zpowers ζ
    · rw [hy]
      exact inv_mem (mem_zpowers ζ)
  have hcardZ : Nat.card ↥(zpowers ζ) = 3 := Cls3.card_zpowers (ζ := ζ) F
  have hcard : Nat.card ↥Xr = 3 := by
    have hdvd : Nat.card ↥Xr ∣ 3 := hcardZ ▸ Subgroup.card_dvd_of_le hle2
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq Xr h1) hXr_ne
    · exact h3
  have hXrZ : Xr = zpowers ζ := Subgroup.eq_of_le_of_card_ge hle2 (by rw [hcard, hcardZ])
  refine ⟨hi2, ?_⟩
  have hXX : X = Xr.map Φ.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, hmemXr]
    simp
  rw [hXX, hXrZ, Transport.map_zpowers]

theorem l34AutOn_psl3Four :
    L34AutOn ↥S := by
  obtain ⟨z, F⟩ := l34Facts
  rw [l34AutOn_iff]
  intro α p X h0
  obtain ⟨i, ψ, hψ⟩ := exists_class_rep h0.alpha_sq h0.alpha_ne
  have h1 := autCfg_map ψ h0
  rw [hψ] at h1
  obtain ⟨hi, hX⟩ := cfg_rep F i h1
  subst hi
  apply l34Concl_of_mulEquiv ψ
  rw [hψ, hX]
  exact class3_concl F isPGL3Four_NN isL2_four_C₃

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
