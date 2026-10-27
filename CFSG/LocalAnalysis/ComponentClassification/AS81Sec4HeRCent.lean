module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HePres
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeTransport
public import Certificates.Certificate15087

public section

namespace CFSG.ComponentClassification.AS81.HePres

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.ComponentClassification.AS81.HePres.Native
open CFSG.Sporadic.HeldB (heP heGenPerm heABArrs rep_heAB rep_wordA_evalSignedWord fixCard
  fixCard_eq_countP card_heP_cent0 infCentralizerConjEquiv)
open CFSG.Sporadic.Schreier (conjClass centralizerIn)
open scoped commutatorElement

section Group

variable {M : Type*} [Group M]

theorem mul_mul_self_eq_one {a b : M} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = a * a * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem mem_closure_pair_of_comm {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : M} (hx : x ∈ closure {a, b}) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e1 : b * a = a * b := hab.symm
  have e2 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e3 : b * (a * b) = a := by rw [← mul_assoc, e1, mul_assoc, hb, mul_one]
  have e4 : a * b * a = b := by rw [mul_assoc, e1, ← mul_assoc, ha, one_mul]
  have e5 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e6 : a * b * (a * b) = 1 := mul_mul_self_eq_one ha hb hab
  let H : Subgroup M :=
    { carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
          (rw [hx, hy]
           show _ = 1 ∨ _ = a ∨ _ = b ∨ _ = a * b
           simp only [one_mul, mul_one, ha, hb, e1, e2, e3, e4, e5, e6, true_or, or_true])
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx | hx | hx <;> rw [hx] <;> show _ = 1 ∨ _ = a ∨ _ = b ∨ _ = a * b
        · exact Or.inl inv_one
        · exact Or.inr (Or.inl hai)
        · exact Or.inr (Or.inr (Or.inl hbi))
        · exact Or.inr (Or.inr (Or.inr (by rw [mul_inv_rev, hai, hbi, e1]))) }
  have hle : closure {a, b} ≤ H := by
    rw [closure_le]
    intro y hy
    rcases hy with hy | hy <;> rw [hy]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  exact hle hx

theorem inf_centralizer_map_conj {H : Subgroup M} {d : M} (hd : d ∈ H) (K : Subgroup M) :
    H ⊓ centralizer (K.map (MulAut.conj d).toMonoidHom : Set M) =
      (H ⊓ centralizer (K : Set M)).map (MulAut.conj d).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_centralizer_iff, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨d⁻¹ * x * d, ⟨H.mul_mem (H.mul_mem (H.inv_mem hd) hx) hd, fun m hm => ?_⟩, by group⟩
    have := hc m hm
    calc m * (d⁻¹ * x * d) = d⁻¹ * ((d * m * d⁻¹) * x) * d := by group
      _ = d⁻¹ * (x * (d * m * d⁻¹)) * d := by rw [this]
      _ = d⁻¹ * x * d * m := by group
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hd hy) (H.inv_mem hd), fun m hm => ?_⟩
    calc d * m * d⁻¹ * (d * y * d⁻¹) = d * (m * y) * d⁻¹ := by group
      _ = d * (y * m) * d⁻¹ := by rw [hc m hm]
      _ = d * y * d⁻¹ * (d * m * d⁻¹) := by group

end Group

theorem heSeedArrs_eq : heSeedArrs = heABArrs := rfl

theorem rep_heGenArrs8
    (i : Fin 8) :
    Rep 8330 (heGenArrs8.getD i.val #[])
      (hePiEquivP (PresentedGroup.of i) : Equiv.Perm (Fin 8330)) := by
  have e : heGenArrs8.getD i.val #[] =
      wordA 8330 heSeedArrs (heSeedArrs.map (invCand 8330)) (hePiHeWords.getD i.val []) := by
    simp [heGenArrs8, Array.getD_eq_getD_getElem?, i.2]
  rw [e, hePiEquivP_of, heSeedArrs_eq]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heAB h hh).1) (fun h hh => (rep_heAB h hh).2)
    (lettersOK_getD hePiHeWords_lettersOK i.val)

theorem hePiEquivP_mk
    (x : FreeGroup (Fin 8)) :
    (hePiEquivP (PresentedGroup.mk _ x) : Equiv.Perm (Fin 8330)) =
      FreeGroup.lift (fun i => (hePiEquivP (PresentedGroup.of i) : Equiv.Perm (Fin 8330))) x := by
  have h : heP.subtype.comp (hePiEquivP.toMonoidHom.comp (PresentedGroup.mk _)) =
      FreeGroup.lift fun i => (hePiEquivP (PresentedGroup.of i) : Equiv.Perm (Fin 8330)) :=
    FreeGroup.ext_hom _ _ fun a => by
      rw [FreeGroup.lift_apply_of]
      rfl
  exact DFunLike.congr_fun h x

theorem rep_heWordArr
    (w : List ℕ) :
    Rep 8330 (heWordArr w)
      (hePiEquivP (PresentedGroup.mk _ (FreeGroup.mk (ofCodes w))) : Equiv.Perm (Fin 8330)) := by
  have h8 := Certificates.certificate15087.1
  simp only [heGenArrsOK, List.all_eq_true, List.mem_range] at h8
  rw [hePiEquivP_mk]
  exact rep_wordArrW (fun i => rep_heGenArrs8 i)
    (fun i => rep_inv_of_isInvA (rep_heGenArrs8 i) (h8 i.val i.2)) _

@[expose] def heRPi (k : ℕ) : HePi :=
  PresentedGroup.mk _ (FreeGroup.mk (ofCodes (heRWords.getD k [])))

@[expose] noncomputable def heRP :
    Subgroup (Equiv.Perm (Fin 8330)) :=
  closure {(hePiEquivP (heRPi 0) : Equiv.Perm (Fin 8330)),
    (hePiEquivP (heRPi 1) : Equiv.Perm (Fin 8330))}

theorem heR_facts :
    let r₁ := (hePiEquivP (heRPi 0) : Equiv.Perm (Fin 8330))
    let r₂ := (hePiEquivP (heRPi 1) : Equiv.Perm (Fin 8330))
    r₁ * r₁ = 1 ∧ r₂ * r₂ = 1 ∧ r₁ * r₂ = r₂ * r₁ ∧ r₁ ≠ 1 ∧ r₂ ≠ 1 ∧ r₁ * r₂ ≠ 1 ∧
      fixCard r₁ = 346 ∧ fixCard r₂ = 346 ∧ fixCard (r₁ * r₂) = 346 := by
  intro r₁ r₂
  have h := Certificates.certificate15087.2.1
  simp only [heRInvolOK, commutesA, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h11, h22⟩, h12⟩, h1⟩, h2⟩, h3⟩, f1⟩, f2⟩, f3⟩ := h
  have e1 : Rep 8330 (heWordArr (heRWords.getD 0 [])) r₁ := rep_heWordArr _
  have e2 : Rep 8330 (heWordArr (heRWords.getD 1 [])) r₂ := rep_heWordArr _
  refine ⟨eq_of_eqA (rep_compA e1 e1) rep_idA h11, eq_of_eqA (rep_compA e2 e2) rep_idA h22,
    eq_of_eqA (rep_compA e1 e2) (rep_compA e2 e1) h12, fun h => ?_, fun h => ?_, fun h => ?_,
    (fixCard_eq_countP e1).trans f1, (fixCard_eq_countP e2).trans f2,
    (fixCard_eq_countP (rep_compA e1 e2)).trans f3⟩
  · rw [(eqA_iff e1 rep_idA).2 h] at h1
    exact Bool.noConfusion h1
  · rw [(eqA_iff e2 rep_idA).2 h] at h2
    exact Bool.noConfusion h2
  · rw [(eqA_iff (rep_compA e1 e2) rep_idA).2 h] at h3
    exact Bool.noConfusion h3

theorem heRP_class :
    ∀ x ∈ heRP, x ≠ 1 → x ∈ conjClass heP (heGenPerm 0) := by
  intro x hx hx1
  obtain ⟨h11, h22, h12, h1, h2, h3, f1, f2, f3⟩ := heR_facts
  have m1 := (hePiEquivP (heRPi 0)).2
  have m2 := (hePiEquivP (heRPi 1)).2
  rcases mem_closure_pair_of_comm h11 h22 h12 hx with rfl | rfl | rfl | rfl
  · exact absurd rfl hx1
  · exact AS81.HeEnd.mem_conjClass_heA0_of_fixCard m1
      (orderOf_eq_prime (by rw [sq]; exact h11) h1) f1
  · exact AS81.HeEnd.mem_conjClass_heA0_of_fixCard m2
      (orderOf_eq_prime (by rw [sq]; exact h22) h2) f2
  · exact AS81.HeEnd.mem_conjClass_heA0_of_fixCard (heP.mul_mem m1 m2)
      (orderOf_eq_prime (by rw [sq]; exact mul_mul_self_eq_one h11 h22 h12) h3) f3

theorem mem_inf_centralizer_heRP
    {x : Equiv.Perm (Fin 8330)} :
    x ∈ heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))) ↔ x ∈ heP ∧
      (hePiEquivP (heRPi 0) : Equiv.Perm (Fin 8330)) * x =
        x * (hePiEquivP (heRPi 0) : Equiv.Perm (Fin 8330)) ∧
      (hePiEquivP (heRPi 1) : Equiv.Perm (Fin 8330)) * x =
        x * (hePiEquivP (heRPi 1) : Equiv.Perm (Fin 8330)) := by
  rw [heRP, mem_inf, centralizer_closure, mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem card_heRC_le :
    Nat.card ↥(heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330)))) ≤ 80640 := by
  set r₁ := (hePiEquivP (heRPi 0) : Equiv.Perm (Fin 8330)) with hr₁
  set r₂ := (hePiEquivP (heRPi 1) : Equiv.Perm (Fin 8330)) with hr₂
  obtain ⟨-, -, -, h1, -⟩ := heR_facts
  obtain ⟨c, hc, hce⟩ := heRP_class r₁ (subset_closure (Set.mem_insert _ _)) h1
  have hcard : Nat.card (centralizerIn heP r₁) = 161280 := by
    rw [centralizerIn, hce, Nat.card_congr (infCentralizerConjEquiv hc (heGenPerm 0)).toEquiv]
    exact card_heP_cent0
  have hle : heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))) ≤ centralizerIn heP r₁ := by
    intro x hx
    obtain ⟨hxP, hx1, -⟩ := mem_inf_centralizer_heRP.1 hx
    exact mem_inf.2 ⟨hxP, mem_centralizer_singleton_iff.2 hx1.symm⟩
  have hw := Certificates.certificate15087.2.2.1
  simp only [heRWitOK, commutesA, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
  obtain ⟨hw1, hw2⟩ := hw
  set y := (hePiEquivP (PresentedGroup.mk _ (FreeGroup.mk (ofCodes heRWitWord))) :
    Equiv.Perm (Fin 8330))
  have ey : Rep 8330 (heWordArr heRWitWord) y := rep_heWordArr _
  have e1 : Rep 8330 (heWordArr (heRWords.getD 0 [])) r₁ := rep_heWordArr _
  have e2 : Rep 8330 (heWordArr (heRWords.getD 1 [])) r₂ := rep_heWordArr _
  have hy1 : y * r₁ = r₁ * y := eq_of_eqA (rep_compA ey e1) (rep_compA e1 ey) hw1
  have hy2 : y * r₂ ≠ r₂ * y := fun h => by
    rw [(eqA_iff (rep_compA ey e2) (rep_compA e2 ey)).2 h] at hw2
    exact Bool.noConfusion hw2
  have hyC : y ∈ centralizerIn heP r₁ :=
    mem_inf.2 ⟨(hePiEquivP _).2, mem_centralizer_singleton_iff.2 hy1⟩
  have hlt : heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))) < centralizerIn heP r₁ :=
    lt_of_le_of_ne hle fun h => hy2 (by
      rw [← h] at hyC
      exact ((mem_inf_centralizer_heRP.1 hyC).2.2).symm)
  have h₁ := card_lt_of_lt hlt
  obtain ⟨m, hm⟩ := card_dvd_of_le hle
  rw [hcard] at h₁ hm
  rcases m with _ | _ | m
  · omega
  · omega
  · have h2 : Nat.card ↥(heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330)))) * 2 ≤
        Nat.card ↥(heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330)))) * (m + 1 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem rep_commArr {n : ℕ} {a b : Array ℕ} {A B : Equiv.Perm (Fin n)} (ha : Rep n a A)
    (hb : Rep n b B) (ha' : isInvA n a (invCand n a) = true)
    (hb' : isInvA n b (invCand n b) = true) : Rep n (commArr n a b) ⁅A, B⁆ := by
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  exact rep_compA ha (rep_compA hb (rep_compA (rep_inv_of_isInvA ha ha')
    (rep_inv_of_isInvA hb hb')))

theorem heRCent_mem
    {w : List ℕ} (hw : w ∈ heRCentWords) :
    (hePiEquivP (PresentedGroup.mk _ (FreeGroup.mk (ofCodes w))) : Equiv.Perm (Fin 8330)) ∈
        heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))) ∧
      isInvA 8330 (heWordArr w) (invCand 8330 (heWordArr w)) = true := by
  have h := Certificates.certificate15087.2.2.2.1
  simp only [heRCentOK, commutesA, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hinv, hc1⟩, hc2⟩ := h.2 w hw
  have eu := rep_heWordArr w
  have e1 : Rep 8330 (heWordArr (heRWords.getD 0 []))
      (hePiEquivP (heRPi 0) : Equiv.Perm (Fin 8330)) := rep_heWordArr _
  have e2 : Rep 8330 (heWordArr (heRWords.getD 1 []))
      (hePiEquivP (heRPi 1) : Equiv.Perm (Fin 8330)) := rep_heWordArr _
  refine ⟨mem_inf_centralizer_heRP.2 ⟨(hePiEquivP _).2, ?_, ?_⟩, hinv⟩
  · exact (eq_of_eqA (rep_compA eu e1) (rep_compA e1 eu) hc1).symm
  · exact (eq_of_eqA (rep_compA eu e2) (rep_compA e2 eu) hc2).symm

noncomputable def heRCentElt
    (k : ℕ) :
    Equiv.Perm (Fin 8330) :=
  hePiEquivP (PresentedGroup.mk _ (FreeGroup.mk (ofCodes (heRCentWords.getD k []))))

theorem card_closure_heRComm :
    Nat.card (closure {⁅heRCentElt 0, heRCentElt 1⁆, ⁅heRCentElt 2, heRCentElt 3⁆}) = 80640 := by
  obtain ⟨-, -, -, -, hc, hord, hsize, horig⟩ := Certificates.certificate15087
  simp only [Bool.and_eq_true] at horig
  obtain ⟨o0, o1⟩ := horig
  rw [heRChainOrig, CFSG.Sporadic.HeldB.arr2_get0] at o0
  rw [heRChainOrig, CFSG.Sporadic.HeldB.arr2_get1] at o1
  have hk : 2 ≤ heRStrong.size := by rw [hsize]; norm_num
  have hb : heRChainBase.Nodup := by decide
  have hA : ChainArrays (RawSchreierDatum.ofArrays 8330 (by norm_num) heRStrong 2 hk heRChainBase hb
      heRChainWords) (heRStrong.extract 0 2) heRStrong heRChainBaseArr heRChainWords :=
    chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  have hinv := (chainCheckFacts hc).strong_inv
  have hrep : ∀ j < heRStrong.size, Rep 8330 heRStrong[j]! (permOfArr 8330 heRStrong[j]!) :=
    fun j hj => (rep_permOfArr (hinv j hj)).1
  have hU : ∀ k < 4, Rep 8330 (heWordArr (heRCentWords.getD k [])) (heRCentElt k) ∧
      isInvA 8330 (heWordArr (heRCentWords.getD k []))
        (invCand 8330 (heWordArr (heRCentWords.getD k []))) = true := by
    intro k hk4
    refine ⟨rep_heWordArr _, (heRCent_mem ?_).2⟩
    interval_cases k <;> decide
  have g0 : permOfArr 8330 heRStrong[0]! = ⁅heRCentElt 0, heRCentElt 1⁆ :=
    eq_of_eqA (hrep 0 (by omega))
      (rep_commArr (hU 0 (by norm_num)).1 (hU 1 (by norm_num)).1 (hU 0 (by norm_num)).2
        (hU 1 (by norm_num)).2) o0
  have g1 : permOfArr 8330 heRStrong[1]! = ⁅heRCentElt 2, heRCentElt 3⁆ :=
    eq_of_eqA (hrep 1 (by omega))
      (rep_commArr (hU 2 (by norm_num)).1 (hU 3 (by norm_num)).1 (hU 2 (by norm_num)).2
        (hU 3 (by norm_num)).2) o1
  have horig' : (RawSchreierDatum.ofArrays 8330 (by norm_num) heRStrong 2 hk heRChainBase hb
      heRChainWords).originalSubgroup =
      closure {⁅heRCentElt 0, heRCentElt 1⁆, ⁅heRCentElt 2, heRCentElt 3⁆} := by
    rw [RawSchreierDatum.originalSubgroup]
    congr 1
    ext g
    simp only [Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · exact Or.inl g0
      · exact Or.inr g1
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, g0⟩
      · exact ⟨1, by norm_num, g1⟩
  rw [← horig', card_originalSubgroup_of_chainOK hA (by norm_num) hc, hord]

theorem heRP_cent :
    ⁅heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))),
        heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330)))⁆ =
      heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))) ∧
    Nat.card ↥(heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330)))) = 80640 := by
  set C := heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))) with hC
  have hu : ∀ k < 4, heRCentElt k ∈ C := by
    intro k hk
    refine (heRCent_mem ?_).1
    interval_cases k <;> decide
  have hK : closure {⁅heRCentElt 0, heRCentElt 1⁆, ⁅heRCentElt 2, heRCentElt 3⁆} ≤ ⁅C, C⁆ := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact commutator_mem_commutator (hu 0 (by norm_num)) (hu 1 (by norm_num))
    · exact commutator_mem_commutator (hu 2 (by norm_num)) (hu 3 (by norm_num))
  have hCC : ⁅C, C⁆ ≤ C := commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem h₁ h₂) (C.inv_mem h₁)) (C.inv_mem h₂)
  have hKC := eq_of_le_of_card_ge (hK.trans hCC)
    (by rw [card_closure_heRComm]; exact card_heRC_le)
  refine ⟨le_antisymm hCC (hKC ▸ hK), ?_⟩
  rw [← hKC]
  exact card_closure_heRComm

theorem heRP_perfect :
    ⁅heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))),
        heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330)))⁆ =
      heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330))) :=
  heRP_cent.1

theorem heRP_card :
    Nat.card ↥(heP ⊓ centralizer (heRP : Set (Equiv.Perm (Fin 8330)))) = 80640 :=
  heRP_cent.2

theorem heRP_class_conj
    {d : Equiv.Perm (Fin 8330)} (hd : d ∈ heP) :
    ∀ x ∈ heRP.map (MulAut.conj d).toMonoidHom, x ≠ 1 → x ∈ conjClass heP (heGenPerm 0) := by
  rintro _ ⟨y, hy, rfl⟩ hx1
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hx1 (map_one _)
  obtain ⟨c, hc, hce⟩ := heRP_class y hy hy1
  refine ⟨d * c, heP.mul_mem hd hc, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hce]
  group

theorem heRP_perfect_conj
    {d : Equiv.Perm (Fin 8330)} (hd : d ∈ heP) :
    ⁅heP ⊓ centralizer (heRP.map (MulAut.conj d).toMonoidHom : Set (Equiv.Perm (Fin 8330))),
        heP ⊓ centralizer (heRP.map (MulAut.conj d).toMonoidHom : Set (Equiv.Perm (Fin 8330)))⁆ =
      heP ⊓ centralizer (heRP.map (MulAut.conj d).toMonoidHom : Set (Equiv.Perm (Fin 8330))) := by
  rw [inf_centralizer_map_conj hd, ← map_commutator, heRP_perfect]

theorem heRP_card_conj
    {d : Equiv.Perm (Fin 8330)} (hd : d ∈ heP) :
    Nat.card ↥(heP ⊓
      centralizer (heRP.map (MulAut.conj d).toMonoidHom : Set (Equiv.Perm (Fin 8330)))) =
      80640 := by
  rw [inf_centralizer_map_conj hd, card_map_of_injective (MulAut.conj d).injective, heRP_card]

end CFSG.ComponentClassification.AS81.HePres
