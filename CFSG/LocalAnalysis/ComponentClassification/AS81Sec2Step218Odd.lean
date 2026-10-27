module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step212Prod
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Invol
public import Certificates.Data.A5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Sec2V4
open scoped Pointwise

namespace Sec2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mem_sup_of_inf_eq_bot {I O : Subgroup G} (hO : Odd (Nat.card O))
    (hOI : O ≤ centralizer (I : Set G)) (hIO : I ⊓ O = ⊥) {w : G} (hw : w ∈ I ⊔ O) {k : ℕ}
    (hk : w ^ 2 ^ k = 1) : w ∈ I := by
  have hON : O ≤ normalizer (I : Set G) := hOI.trans (centralizer_le_normalizer _)
  have hw' : w ∈ (I : Set G) * (O : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left I O hON]
    exact hw
  obtain ⟨i, hi, o, ho, rfl⟩ := hw'
  have hcomm : Commute i o := mem_centralizer_iff.mp (hOI ho) i hi
  have h1 : i ^ 2 ^ k * o ^ 2 ^ k = 1 := by rw [← hcomm.mul_pow]; exact hk
  have h2 : o ^ 2 ^ k ∈ I ⊓ O := by
    refine ⟨?_, O.pow_mem ho _⟩
    rw [eq_inv_of_mul_eq_one_right h1]
    exact I.inv_mem (I.pow_mem hi _)
  rw [hIO, mem_bot] at h2
  have hodd : Odd (orderOf o) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)
  have h3 : orderOf o = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))
      (orderOf_dvd_of_pow_eq_one h2)
  change i * o ∈ I
  rw [orderOf_eq_one_iff.mp h3, mul_one]
  exact hi

omit [Finite G] in
theorem odd_orderOf_of_mem {O : Subgroup G} (hO : Odd (Nat.card O)) {o : G} (ho : o ∈ O) :
    Odd (orderOf o) :=
  hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)

section Setting

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem mem_oddCoreIn_centralizer_E (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {c : G} (hc : c ∈ centralizer (E : Set G))
    (hco : Odd (orderOf c)) : c ∈ AS76b.oddCoreIn (centralizer (E : Set G)) := by
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 6) (by rw [hF.cardE]; norm_num)
  have hEC : E ≤ centralizer (E : Set G) := fun e he => mem_centralizer_iff.mpr fun e' he' =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨e', he'⟩ ⟨e, he⟩)
  refine mem_oddCoreIn_of_mem_sup_of_odd hEC hE2 ?_ hco
  rw [sup_comm, ← (centralizer_eq_sup_oddCoreIn hF hL hodd).1]
  exact hc

theorem oddCoreIn_centralizer_le_oddCoreIn_sec2K (h21 : Step21) (h211 : Step211)
    (hS : Sec2Setting G A R g E F) :
    AS76b.oddCoreIn (centralizer (sec2S A R E F : Set G)) ≤ AS76b.oddCoreIn (sec2K E) := by
  intro o ho
  have hoS : o ∈ centralizer (sec2S A R E F : Set G) := AS76b.oddCoreIn_le _ ho
  have hoodd : Odd (orderOf o) := odd_orderOf_of_mem (AS76b.odd_card_oddCoreIn _) ho
  obtain ⟨-, -, hOP, -, -, -, -, -, -, hSE⟩ := h21 G A R g E F hS
  have hoE : o ∈ centralizer (E : Set G) := centralizer_le (SetLike.coe_subset_coe.mpr hSE.1) hoS
  have hoP : o ∈ centralizer (sec2P E : Set G) :=
    hOP (mem_oddCoreIn_centralizer_E hS.frame hS.type hS.odd hoE hoodd)
  have hoK : o ∈ sec2K E :=
    subset_closure ⟨normalizer_le_normalizer_sec2P E (centralizer_le_normalizer _ hoE), hoodd⟩
  obtain ⟨hPOK, -, -, -, -, hcm, -⟩ := h211 G A R g E F hS
  have hoPO : o ∈ sec2P E ⊔ AS76b.oddCoreIn (sec2K E) := by
    rw [← hcm]
    refine ⟨hoK, centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left) hoE),
      fun p hp => ?_⟩
    have h1 : p * o = o * p := mem_centralizer_iff.mp hoP p hp
    have e : p⁻¹ * o⁻¹ * p * o = 1 := by
      calc p⁻¹ * o⁻¹ * p * o = p⁻¹ * o⁻¹ * (p * o) := by group
        _ = p⁻¹ * o⁻¹ * (o * p) := by rw [h1]
        _ = 1 := by group
    rw [e]
    exact one_mem _
  exact mem_oddCoreIn_of_mem_sup_of_odd (le_sup_left.trans hPOK) (isPGroup_sec2P E)
    (by rwa [sup_comm]) hoodd

theorem mem_centralizer_oddCoreIn_sec2K
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21)
    (h211 : Step211) (h212 : Step212) (hS : Sec2Setting G A R g E F) {k : G} (hk : k ∈ sec2K E)
    {n : ℕ} (hkn : k ^ 2 ^ n = 1) :
    k ∈ centralizer (AS76b.oddCoreIn (sec2K E) : Set G) := by
  obtain ⟨I, -, hIO, hIOK, hOI⟩ := step212Prod_of h4 h34 hE16 h21 h211 h212 hS
  have hkI : k ∈ I := mem_of_mem_sup_of_inf_eq_bot (AS76b.odd_card_oddCoreIn _) hOI hIO
    (by rw [hIOK]; exact hk) hkn
  exact mem_centralizer_iff.mpr fun o ho => (mem_centralizer_iff.mp (hOI ho) k hkI).symm

theorem oddCoreIn_centralizer_le_centralizer_sec2T
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21)
    (h211 : Step211) (h212 : Step212) (hS : Sec2Setting G A R g E F) {T₀ : Subgroup G}
    (hT₀ : IsPGroup 2 T₀) :
    AS76b.oddCoreIn (centralizer (sec2S A R E F : Set G)) ≤ centralizer (sec2T E T₀ : Set G) := by
  intro o ho
  have hoK := oddCoreIn_centralizer_le_oddCoreIn_sec2K h21 h211 hS ho
  refine mem_centralizer_iff.mpr fun τ hτ => ?_
  obtain ⟨n, hn⟩ := hT₀ ⟨τ, hτ.1⟩
  have hτn : τ ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact (mem_centralizer_iff.mp
    (mem_centralizer_oddCoreIn_sec2K h4 h34 hE16 h21 h211 h212 hS hτ.2 hτn) o hoK).symm

theorem centralizer_sec2S_eq_sup (h24 : Step24) (h26 : Step26) (hS : Sec2Setting G A R g E F) :
    centralizer (sec2S A R E F : Set G) =
      sec2Z A E F ⊔ AS76b.oddCoreIn (centralizer (sec2S A R E F : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp := special_of h24 hS
  have hsyl := (h26 G A R g E F hS).2.2.2.2.1
  have hZC : sec2Z A E F ≤ centralizer (sec2S A R E F : Set G) := fun c hc =>
    mem_centralizer_iff.mpr fun s hs => (hSp.comm_Z hc hs).symm
  refine eq_sup_oddCoreIn_of_central hsyl.isPGroup hZC (fun c hc => ?_) ?_
  · refine mem_centralizer_iff.mpr fun w hw => ?_
    exact (mem_centralizer_iff.mp hw c (hSp.le hc)).symm
  · have h1 := (isSylowOf_iff.mp hsyl).2.2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h1)

theorem mem_oddCoreIn_centralizer_S (h24 : Step24) (h26 : Step26)
    (hS : Sec2Setting G A R g E F) {c : G} (hc : c ∈ centralizer (sec2S A R E F : Set G))
    (hco : Odd (orderOf c)) : c ∈ AS76b.oddCoreIn (centralizer (sec2S A R E F : Set G)) := by
  have hSp := special_of h24 hS
  have hZ2 : IsPGroup 2 (sec2Z A E F) := IsPGroup.of_card (n := 2) (by rw [hSp.card]; norm_num)
  have hZC : sec2Z A E F ≤ centralizer (sec2S A R E F : Set G) := fun c hc =>
    mem_centralizer_iff.mpr fun s hs => (hSp.comm_Z hc hs).symm
  refine mem_oddCoreIn_of_mem_sup_of_odd hZC hZ2 ?_ hco
  rw [sup_comm, ← centralizer_sec2S_eq_sup h24 h26 hS]
  exact hc

end Setting

section Coordinates

variable {Z : Subgroup G}

omit [Finite G] in
theorem psi_one_of_add {W : Subgroup G} {ψ : G → (Fin 5 → ZMod 2)}
    (hadd : ∀ a ∈ W, ∀ b ∈ W, ψ (a * b) = ψ a + ψ b) : ψ 1 = 0 := by
  have h := hadd 1 W.one_mem 1 W.one_mem
  rw [mul_one] at h
  exact add_eq_left.mp h.symm

omit [Finite G] in
theorem psi_inv_of_add {W : Subgroup G} {ψ : G → (Fin 5 → ZMod 2)}
    (hadd : ∀ a ∈ W, ∀ b ∈ W, ψ (a * b) = ψ a + ψ b) {a : G} (ha : a ∈ W) : ψ a⁻¹ = ψ a := by
  have h := hadd a ha a⁻¹ (W.inv_mem ha)
  rw [mul_inv_cancel, psi_one_of_add hadd] at h
  have h2 : ψ a + ψ a = 0 := by
    funext k
    exact CharTwo.add_self_eq_zero _
  exact add_left_cancel (h.symm.trans h2.symm)

theorem cycle_mem_alternatingGroup :
    (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
  decide

theorem act_cycle_pair_ne : act (Equiv.swap 0 1 * Equiv.swap 1 2) (pair 0 3) + pair 0 3 ≠ 0 := by
  decide

omit [Finite G] in
theorem Coord.phi_ne_one {S Z H : Subgroup G} (C : Coord S Z H) (hS2 : IsPGroup 2 S) {y : G}
    (hyH : y ∈ H) (hy3 : orderOf y = 3) : C.φ ⟨y, hyH⟩ ≠ 1 := by
  intro h
  have hyS : y ∈ S := by
    have hker : (⟨y, hyH⟩ : ↥H) ∈ C.φ.ker := h
    rw [C.ker] at hker
    exact hker
  obtain ⟨k, hk⟩ := hS2 ⟨y, hyS⟩
  have hk' : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : 3 ∣ 2 ^ k := hy3 ▸ orderOf_dvd_of_pow_eq_one hk'
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd
  omega

omit [Finite G] in
theorem le_of_invariant_coord {W U : Subgroup G} {ψ : G → (Fin 5 → ZMod 2)} (hZU : Z ≤ U)
    (hadd : ∀ a ∈ W, ∀ b ∈ W, ψ (a * b) = ψ a + ψ b) (hker : ∀ a ∈ W, ψ a = 0 ↔ a ∈ Z)
    (heven : ∀ a ∈ W, IsEven (ψ a))
    (hconj : ∀ σ ∈ alternatingGroup (Fin 5), ∀ a ∈ W ⊓ U, ∃ b ∈ W ⊓ U, ψ b = act σ (ψ a))
    {a₀ : G} (ha₀ : a₀ ∈ W ⊓ U) (ha₀0 : ψ a₀ ≠ 0) : W ≤ U := by
  have hψ1 : ψ 1 = 0 := psi_one_of_add hadd
  have hψinv : ∀ a ∈ W, ψ a⁻¹ = ψ a := fun a ha => psi_inv_of_add hadd ha
  let N : AddSubgroup (Fin 5 → ZMod 2) :=
    { carrier := {v | ∃ a ∈ W ⊓ U, ψ a = v}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, mul_mem ha hb, hadd a ha.1 b hb.1⟩
      zero_mem' := ⟨1, one_mem _, hψ1⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨a, ha, ?_⟩
        funext k
        exact (CharTwo.neg_eq (ψ a k)).symm }
  have hN : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ N, act σ v ∈ N := by
    rintro σ hσ _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hbe⟩ := hconj σ hσ a ha
    exact ⟨b, hb, hbe⟩
  intro a ha
  have hmem : ψ a ∈ N :=
    mem_of_invariant hN (show ψ a₀ ∈ N from ⟨a₀, ha₀, rfl⟩) (heven a₀ ha₀.1) ha₀0 (heven a ha)
  obtain ⟨a', ha', hψa'⟩ := hmem
  have hZ : a * a'⁻¹ ∈ Z := by
    rw [← hker _ (W.mul_mem ha (W.inv_mem ha'.1)), hadd _ ha _ (W.inv_mem ha'.1),
      hψinv a' ha'.1, hψa']
    funext k
    exact CharTwo.add_self_eq_zero _
  have e : a = (a * a'⁻¹) * a' := by group
  rw [e]
  exact U.mul_mem (hZU hZ) ha'.2

end Coordinates

section Setting

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

omit [Finite G] in
theorem le_centralizer_sec2Z (E F A : Subgroup G) :
    E ≤ centralizer (sec2Z A E F : Set G) := fun e he =>
  mem_centralizer_iff.mpr fun _ hc => (mem_centralizer_iff.mp hc.2.2 e (mem_sup_left he)).symm

omit [Finite G] in
theorem normalizer_le_normalizer_sec2Z (hSp : Special (sec2S A R E F) (sec2Z A E F)) :
    normalizer (sec2S A R E F : Set G) ≤ normalizer (sec2Z A E F : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact fun hc => conj_mem_Z_of_normS hSp hn hc
  · intro hc
    have h := conj_mem_Z_of_normS hSp (inv_mem hn) hc
    simpa [mul_assoc] using h

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer_of (Y : Subgroup G) :
    normalizer (Y : Set G) ≤ normalizer (centralizer (Y : Set G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    refine mem_centralizer_iff.mpr fun w hw => ?_
    have hw' : n⁻¹ * w * n ∈ Y := by
      have := (mem_normalizer_iff.mp (inv_mem hn) w).mp hw
      simpa using this
    have h1 := mem_centralizer_iff.mp hc _ hw'
    calc w * (n * c * n⁻¹) = n * ((n⁻¹ * w * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * w * n)) * n⁻¹ := by rw [h1]
      _ = n * c * n⁻¹ * w := by group
  · intro hc
    refine mem_centralizer_iff.mpr fun w hw => ?_
    have hw' : n * w * n⁻¹ ∈ Y := (mem_normalizer_iff.mp hn w).mp hw
    have h1 := mem_centralizer_iff.mp hc _ hw'
    have h2 : n * (w * c) * n⁻¹ = n * (c * w) * n⁻¹ := by
      calc n * (w * c) * n⁻¹ = (n * w * n⁻¹) * (n * c * n⁻¹) := by group
        _ = (n * c * n⁻¹) * (n * w * n⁻¹) := h1
        _ = n * (c * w) * n⁻¹ := by group
    simpa using h2

omit [Finite G] in
theorem conj_mem_centralizer {Y : Subgroup G} {n c : G} (hn : n ∈ normalizer (Y : Set G))
    (hc : c ∈ centralizer (Y : Set G)) : n * c * n⁻¹ ∈ centralizer (Y : Set G) :=
  (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer_of Y hn) c).mp hc

theorem oddCoreIn_centralizer_Z_le_centralizer_A
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hS : Sec2Setting G A R g E F) :
    AS76b.oddCoreIn (centralizer (sec2Z A E F : Set G)) ≤ centralizer (A : Set G) := by
  set K' := AS76b.oddCoreIn (centralizer (sec2Z A E F : Set G)) with hK'
  by_cases hK1 : K' = ⊥
  · rw [hK1]
    exact bot_le
  have hEK' : E ≤ normalizer (K' : Set G) :=
    (le_centralizer_sec2Z E F A).trans (AS76b.le_normalizer_oddCoreIn _)
  obtain ⟨X₀, hK'X₀, hX₀⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G))
    ⟨AS76b.odd_card_oddCoreIn _, hEK'⟩
  have hX₀ne : X₀ ≠ ⊥ := fun h => hK1 (le_bot_iff.mp (h ▸ hK'X₀))
  obtain ⟨hconj, -, -, -⟩ := step17a_of_frame h4 h34 hE16 hS.frame hS.type X₀ hX₀ hX₀ne
  have h1 := hconj 1 (one_mem _)
  rw [rightConjugate_one] at h1
  exact hK'X₀.trans (h1.le.trans (AS76b.oddCoreIn_le _))

theorem oddCoreIn_centralizer_Z_le_centralizer
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h24 : Step24) (h26 : Step26)
    (h27 : Step27) (hS : Sec2Setting G A R g E F) {u y : G} (huy : Sec2UY A R E F u y) :
    AS76b.oddCoreIn (centralizer (sec2Z A E F : Set G)) ≤
      centralizer (sec2S A R E F : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := sec2S A R E F with hSdef
  set Z := sec2Z A E F with hZdef
  set H := sec2H E F with hHdef
  set K' := AS76b.oddCoreIn (centralizer (Z : Set G)) with hK'
  have hSp : Special S Z := special_of h24 hS
  obtain ⟨C⟩ := nonempty_coord h26 hS
  obtain ⟨-, hSleH, -, -, -, -, -, hHS, hSH⟩ := h26 G A R g E F hS
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 10) (by rw [C.card_S hSp]; norm_num)
  have hK'A := oddCoreIn_centralizer_Z_le_centralizer_A h4 h34 hE16 hS
  have hAK' : A ≤ centralizer (K' : Set G) := le_centralizer_iff.mp hK'A
  have hZK' : Z ≤ centralizer (K' : Set G) := inf_le_left.trans hAK'
  have hNK' : normalizer (S : Set G) ≤ normalizer (K' : Set G) := fun n hn =>
    AS76b.normalizer_le_normalizer_oddCoreIn _
      (normalizer_le_normalizer_centralizer_of Z (normalizer_le_normalizer_sec2Z hSp hn))
  have hconjC : ∀ n ∈ normalizer (S : Set G), ∀ c ∈ centralizer (K' : Set G),
      n * c * n⁻¹ ∈ centralizer (K' : Set G) := fun n hn c hc => conj_mem_centralizer (hNK' hn) hc
  obtain ⟨x, -, hux, -, -, -, hxH⟩ := (h27 G A R g E F hS).2 u y huy
  obtain ⟨⟨huA, huS⟩, -, -, ⟨⟨hyH, -⟩, -⟩, hy3⟩ := huy
  have huK' : u ∈ centralizer (K' : Set G) := hAK' huA
  have huH : u ∈ normalizer (H : Set G) := hSH huS
  have hya := C.phi_ne_one hS2 hyH hy3
  have hcen : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  obtain ⟨b, hb⟩ : ∃ b, C.φ ⟨y, hyH⟩ * b ≠ b * C.φ ⟨y, hyH⟩ := by
    by_contra hcon
    apply hya
    have hmem : C.φ ⟨y, hyH⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) :=
      mem_center_iff.mpr fun c => (not_not.mp ((not_exists.mp hcon) c)).symm
    rw [hcen, mem_bot] at hmem
    exact hmem
  obtain ⟨⟨h, hhH⟩, hhb⟩ := C.surj b
  have hu'H : u⁻¹ * h⁻¹ * u ∈ H := by
    have := (mem_normalizer_iff.mp (inv_mem huH) h⁻¹).mp (H.inv_mem hhH)
    simpa using this
  have hwH : u⁻¹ * h⁻¹ * u * h ∈ H := H.mul_mem hu'H hhH
  have hwK' : u⁻¹ * h⁻¹ * u * h ∈ centralizer (K' : Set G) := by
    have h1 : h⁻¹ * u * h ∈ centralizer (K' : Set G) := by
      have := hconjC h⁻¹ (inv_mem (hHS hhH)) u huK'
      simpa using this
    have e : u⁻¹ * h⁻¹ * u * h = u⁻¹ * (h⁻¹ * u * h) := by group
    rw [e]
    exact mul_mem (inv_mem huK') h1
  have hsS : x⁻¹ * h⁻¹ * x * h ∈ S := hxH h hhH
  have hsH : x⁻¹ * h⁻¹ * x * h ∈ H := hSleH hsS
  have hφs : C.φ ⟨x⁻¹ * h⁻¹ * x * h, hsH⟩ = 1 := by
    have : (⟨x⁻¹ * h⁻¹ * x * h, hsH⟩ : ↥H) ∈ C.φ.ker := by
      rw [C.ker]
      exact hsS
    exact this
  have hwφ : C.φ ⟨u⁻¹ * h⁻¹ * u * h, hwH⟩ ≠ 1 := by
    intro h1
    apply hb
    rcases hux with hu | hu
    · have e : (⟨u⁻¹ * h⁻¹ * u * h, hwH⟩ : ↥H) = (⟨y, hyH⟩ : ↥H)⁻¹ *
          ⟨x⁻¹ * h⁻¹ * x * h, hsH⟩ * (⟨h, hhH⟩ : ↥H)⁻¹ * ⟨y, hyH⟩ * ⟨h, hhH⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hu]
        group
      rw [e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hφs, hhb, mul_one] at h1
      calc C.φ ⟨y, hyH⟩ * b = b * C.φ ⟨y, hyH⟩ * ((C.φ ⟨y, hyH⟩)⁻¹ * b⁻¹ * C.φ ⟨y, hyH⟩ * b) := by
            group
        _ = b * C.φ ⟨y, hyH⟩ := by rw [h1, mul_one]
    · have e : (⟨u⁻¹ * h⁻¹ * u * h, hwH⟩ : ↥H) = (⟨y, hyH⟩ : ↥H) *
          ⟨x⁻¹ * h⁻¹ * x * h, hsH⟩ * (⟨h, hhH⟩ : ↥H)⁻¹ * (⟨y, hyH⟩ : ↥H)⁻¹ * ⟨h, hhH⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hu]
        group
      rw [e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hφs, hhb, mul_one] at h1
      calc C.φ ⟨y, hyH⟩ * b = b * (C.φ ⟨y, hyH⟩ * b⁻¹ * (C.φ ⟨y, hyH⟩)⁻¹ * b)⁻¹ * C.φ ⟨y, hyH⟩ := by
            group
        _ = b * C.φ ⟨y, hyH⟩ := by rw [h1, inv_one, mul_one]
  have hs5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hDn : ((centralizer (K' : Set G)).subgroupOf H).Normal := by
    refine ⟨fun c hc k => ?_⟩
    rw [mem_subgroupOf] at hc ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconjC k (hHS k.2) c hc
  have hDtop : ((centralizer (K' : Set G)).subgroupOf H).map C.φ = ⊤ := by
    rcases (hDn.map C.φ C.surj).eq_bot_or_eq_top with hbot | htop
    · exfalso
      apply hwφ
      have : C.φ ⟨u⁻¹ * h⁻¹ * u * h, hwH⟩ ∈ ((centralizer (K' : Set G)).subgroupOf H).map C.φ :=
        ⟨⟨u⁻¹ * h⁻¹ * u * h, hwH⟩, mem_subgroupOf.mpr hwK', rfl⟩
      rwa [hbot, mem_bot] at this
    · exact htop
  have hsurj : ∀ σ : alternatingGroup (Fin 5), ∃ k : ↥H, (k : G) ∈ centralizer (K' : Set G) ∧
      C.φ k = σ := by
    intro σ
    have hσ : σ ∈ ((centralizer (K' : Set G)).subgroupOf H).map C.φ := by
      rw [hDtop]
      exact mem_top σ
    obtain ⟨k, hk, hkσ⟩ := hσ
    exact ⟨k, mem_subgroupOf.mp hk, hkσ⟩
  have σ₀mem := cycle_mem_alternatingGroup
  have hpair := act_cycle_pair_ne
  have hS₂ : C.S₂ ≤ centralizer (K' : Set G) := by
    obtain ⟨a₁, ha₁, hψa₁⟩ := C.onto₂ (pair 0 3) (isEven_pair 0 3)
    obtain ⟨k, hkK', hkσ⟩ := hsurj ⟨_, σ₀mem⟩
    have hka := C.conj₂ k a₁ ha₁
    refine le_of_invariant_coord hZK' C.add₂ C.ker₂ C.even₂ ?_
      (a₀ := (k : G) * a₁ * (k : G)⁻¹ * a₁⁻¹)
      (Subgroup.mem_inf.mpr ⟨C.S₂.mul_mem hka.1 (C.S₂.inv_mem ha₁), ?_⟩) ?_
    · intro σ hσ a ha
      obtain ⟨ha₂, haK'⟩ := Subgroup.mem_inf.mp ha
      obtain ⟨k', hk'K', hk'σ⟩ := hsurj ⟨σ, hσ⟩
      have hk'a := C.conj₂ k' a ha₂
      refine ⟨(k' : G) * a * (k' : G)⁻¹,
        Subgroup.mem_inf.mpr ⟨hk'a.1, mul_mem (mul_mem hk'K' haK') (inv_mem hk'K')⟩, ?_⟩
      rw [hk'a.2, hk'σ]
    · have h1 : a₁ * (k : G)⁻¹ * a₁⁻¹ ∈ centralizer (K' : Set G) :=
        hconjC a₁ (le_normalizer (C.le₂ ha₁)) _ (inv_mem hkK')
      have e : (k : G) * a₁ * (k : G)⁻¹ * a₁⁻¹ = (k : G) * (a₁ * (k : G)⁻¹ * a₁⁻¹) := by group
      rw [e]
      exact mul_mem hkK' h1
    · rw [C.add₂ _ hka.1 _ (C.S₂.inv_mem ha₁), hka.2, hkσ, psi_inv_of_add C.add₂ ha₁, hψa₁]
      exact hpair
  have hS₃ : C.S₃ ≤ centralizer (K' : Set G) := by
    obtain ⟨a₁, ha₁, hψa₁⟩ := C.onto₃ (pair 0 3) (isEven_pair 0 3)
    obtain ⟨k, hkK', hkσ⟩ := hsurj ⟨_, σ₀mem⟩
    have hka := C.conj₃ k a₁ ha₁
    refine le_of_invariant_coord hZK' C.add₃ C.ker₃ C.even₃ ?_
      (a₀ := (k : G) * a₁ * (k : G)⁻¹ * a₁⁻¹)
      (Subgroup.mem_inf.mpr ⟨C.S₃.mul_mem hka.1 (C.S₃.inv_mem ha₁), ?_⟩) ?_
    · intro σ hσ a ha
      obtain ⟨ha₂, haK'⟩ := Subgroup.mem_inf.mp ha
      obtain ⟨k', hk'K', hk'σ⟩ := hsurj ⟨σ, hσ⟩
      have hk'a := C.conj₃ k' a ha₂
      refine ⟨(k' : G) * a * (k' : G)⁻¹,
        Subgroup.mem_inf.mpr ⟨hk'a.1, mul_mem (mul_mem hk'K' haK') (inv_mem hk'K')⟩, ?_⟩
      rw [hk'a.2, hk'σ]
    · have h1 : a₁ * (k : G)⁻¹ * a₁⁻¹ ∈ centralizer (K' : Set G) :=
        hconjC a₁ (le_normalizer (C.le₃ ha₁)) _ (inv_mem hkK')
      have e : (k : G) * a₁ * (k : G)⁻¹ * a₁⁻¹ = (k : G) * (a₁ * (k : G)⁻¹ * a₁⁻¹) := by group
      rw [e]
      exact mul_mem hkK' h1
    · rw [C.add₃ _ hka.1 _ (C.S₃.inv_mem ha₁), hka.2, hkσ, psi_inv_of_add C.add₃ ha₁, hψa₁]
      exact hpair
  have hSK' : sec2S A R E F ≤ centralizer (K' : Set G) := by
    rw [← C.sup]
    exact sup_le hS₂ hS₃
  exact le_centralizer_iff.mp hSK'

end Setting

end Sec2

end CFSG.ComponentClassification.AS81
