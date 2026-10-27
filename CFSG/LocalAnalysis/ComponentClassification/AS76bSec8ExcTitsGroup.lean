module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTitsTests
public import CFSG.Sporadic.Schreier.TitsComponent

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.TitsSec8

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits CFSG.Certificates
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped commutatorElement

theorem rep_mcommA {x y : Array ℕ} {g h : Equiv.Perm (Fin 1755)} (hx : Rep 1755 x g)
    (hy : Rep 1755 y h) (hxi : invOK x = true) (hyi : invOK y = true) :
    Rep 1755 (mcommA x y) ⁅g, h⁆ := by
  rw [commutatorElement_def]
  exact rep_compA (rep_compA (rep_compA hx hy) (rep_inv_of_isInvA hx hxi))
    (rep_inv_of_isInvA hy hyi)

abbrev wP (L : List (List ℤ)) (i : ℕ) : Equiv.Perm (Fin 1755) := wordIn 13 titsT (wordAt L i)

theorem rep_wP
    {L : List (List ℤ)} {i : ℕ} (h : lettersOK 13 (wordAt L i) = true) :
    Rep 1755 (wA (wordAt L i)) (wP L i) :=
  rep_wordArr_titsT h

theorem all_wordAt {L : List (List ℤ)} {p : List ℤ → Bool} (h : L.all p = true) {i : ℕ}
    (hi : i < L.length) : p (wordAt L i) = true := by
  refine List.all_eq_true.1 h _ ?_
  rw [wordAt, List.getD_eq_getElem L [] hi]
  exact List.getElem_mem hi

theorem z_witness
    (hc : titsSec8Check = true) :
    (∀ i < 4, wP titsSec8ZWords i ∈ titsH) ∧
      ⁅wP titsSec8ZWords 0, wP titsSec8ZWords 1⁆ ∈ titsJ ∧
      ⁅wP titsSec8ZWords 2, wP titsSec8ZWords 3⁆ ∈ titsJ ∧
      ⁅⁅wP titsSec8ZWords 0, wP titsSec8ZWords 1⁆,
        ⁅wP titsSec8ZWords 2, wP titsSec8ZWords 3⁆⁆ = titsZ := by
  simp only [titsSec8Check, titsSec8ZCheck, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hall⟩, hu⟩, hv⟩, huJ⟩, hvJ⟩, hz⟩, -⟩, -⟩ := hc
  have hlen : titsSec8ZWords.length = 4 := rfl
  have hw : ∀ i < 4, lettersOK 13 (wordAt titsSec8ZWords i) = true ∧
      invOK (wA (wordAt titsSec8ZWords i)) = true ∧ inH (wA (wordAt titsSec8ZWords i)) = true := by
    intro i hi
    have := all_wordAt hall (by rw [hlen]; exact hi)
    simpa only [Bool.and_eq_true, and_assoc] using this
  have hr : ∀ i < 4, Rep 1755 (wA (wordAt titsSec8ZWords i)) (wP titsSec8ZWords i) :=
    fun i hi => rep_wP (hw i hi).1
  have hru := rep_mcommA (hr 0 (by norm_num)) (hr 1 (by norm_num)) (hw 0 (by norm_num)).2.1
    (hw 1 (by norm_num)).2.1
  have hrv := rep_mcommA (hr 2 (by norm_num)) (hr 3 (by norm_num)) (hw 2 (by norm_num)).2.1
    (hw 3 (by norm_num)).2.1
  refine ⟨fun i hi => mem_titsH_of_sift (hr i hi) (hw i hi).2.2, mem_titsJ_of_sift hru huJ,
    mem_titsJ_of_sift hrv hvJ, eq_of_eqA (rep_mcommA hru hrv hu hv) titsZ_rep hz⟩

theorem t_witness
    (hc : titsSec8Check = true) :
    (∀ i < 4, wP titsSec8TWords i ∈ titsCt) ∧
      ⁅wP titsSec8TWords 0, wP titsSec8TWords 1⁆ ∈ titsQ ∧
      ⁅wP titsSec8TWords 2, wP titsSec8TWords 3⁆ ∈ titsQ ∧
      ⁅⁅wP titsSec8TWords 0, wP titsSec8TWords 1⁆,
        ⁅wP titsSec8TWords 2, wP titsSec8TWords 3⁆⁆ = titsTInv := by
  simp only [titsSec8Check, titsSec8TCheck, Bool.and_eq_true] at hc
  obtain ⟨⟨-, ⟨⟨⟨⟨⟨⟨-, hall⟩, hu⟩, hv⟩, huK⟩, hvK⟩, ht⟩⟩, -⟩ := hc
  have hlen : titsSec8TWords.length = 4 := rfl
  have hw : ∀ i < 4, lettersOK 13 (wordAt titsSec8TWords i) = true ∧
      invOK (wA (wordAt titsSec8TWords i)) = true ∧ inN (wA (wordAt titsSec8TWords i)) = true ∧
      commA (wA (wordAt titsSec8TWords i)) titsTArr = true := by
    intro i hi
    have := all_wordAt hall (by rw [hlen]; exact hi)
    simpa only [Bool.and_eq_true, and_assoc] using this
  have hr : ∀ i < 4, Rep 1755 (wA (wordAt titsSec8TWords i)) (wP titsSec8TWords i) :=
    fun i hi => rep_wP (hw i hi).1
  have hC : ∀ i < 4, wP titsSec8TWords i ∈ titsCt := fun i hi =>
    mem_inf.2 ⟨mem_titsN_of_sift (hr i hi) (hw i hi).2.2.1,
      mem_centralizer_singleton_iff.2 ((commA_iff (hr i hi) titsTInv_rep).1 (hw i hi).2.2.2)⟩
  have hru := rep_mcommA (hr 0 (by norm_num)) (hr 1 (by norm_num)) (hw 0 (by norm_num)).2.1
    (hw 1 (by norm_num)).2.1
  have hrv := rep_mcommA (hr 2 (by norm_num)) (hr 3 (by norm_num)) (hw 2 (by norm_num)).2.1
    (hw 3 (by norm_num)).2.1
  have hcomm : ∀ {i j : ℕ}, i < 4 → j < 4 → ⁅wP titsSec8TWords i, wP titsSec8TWords j⁆ ∈ titsCt :=
    fun hi hj => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hC _ hi) (hC _ hj)) (inv_mem (hC _ hi))) (inv_mem (hC _ hj))
  refine ⟨hC, mem_inf.2 ⟨hcomm (by norm_num) (by norm_num), (mem_titsK_iff_sift hru).1 huK⟩,
    mem_inf.2 ⟨hcomm (by norm_num) (by norm_num), (mem_titsK_iff_sift hrv).1 hvK⟩,
    eq_of_eqA (rep_mcommA hru hrv hu hv) titsTInv_rep ht⟩

theorem eq_or_eq_of_card_two {G : Type*} [Group G] {S : Subgroup G} (h2 : Nat.card S = 2)
    {a b x : G} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ S) : x = a ∨ x = b := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, Set.ncard_eq_two] at h2
  obtain ⟨p, q, -, hpq⟩ := h2
  have ha' : a ∈ ({p, q} : Set G) := hpq ▸ ha
  have hb' : b ∈ ({p, q} : Set G) := hpq ▸ hb
  have hx' : x ∈ ({p, q} : Set G) := hpq ▸ hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb' hx'
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> rcases hx' with rfl | rfl <;>
    simp_all

theorem eq_one_or_eq_z
    {w : Equiv.Perm (Fin 1755)} (hw : w ∈ titsH)
    (hcomm : ∀ c ∈ titsH, w * c = c * w) : w = 1 ∨ w = titsZ := by
  obtain ⟨-, -, hHz, hcard, -, -, -⟩ := AT_Tits_local_center_and_centralizer_checks
  have hzH : titsZ ∈ titsH := by
    rw [← titsD_centralizer_z]
    exact mem_inf.2 ⟨titsZ_mem_titsD, mem_centralizer_singleton_iff.2 rfl⟩
  have hmem : ∀ y ∈ titsH, (∀ c ∈ titsH, y * c = c * y) →
      y ∈ titsH ⊓ centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) := fun y hy hyc =>
    mem_inf.2 ⟨hy, mem_centralizer_iff.2 fun j hj => (hyc j (titsJ_le_titsH hj)).symm⟩
  have h1 := hmem 1 (one_mem _) (fun c _ => by rw [one_mul, mul_one])
  have hz := hmem titsZ hzH (fun c hc => (mem_centralizer_singleton_iff.1 (hHz hc)).symm)
  rcases eq_or_eq_of_card_two hcard h1 hz titsZ_ne_one.symm (hmem w hw hcomm) with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem eq_one_or_eq_t
    (hc : titsSec8Check = true) {w : Equiv.Perm (Fin 1755)} (hw : w ∈ titsCt)
    (hcomm : ∀ c ∈ titsCt, w * c = c * w) (hw2 : w * w = 1) : w = 1 ∨ w = titsTInv := by
  simp only [titsSec8Check, Bool.and_eq_true] at hc
  have hcen := hc.2
  have hwQ : w ∈ ((titsCt ⊓ centralizer (titsQ : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) :=
    mem_inf.2 ⟨hw, mem_centralizer_iff.2 fun q hq =>
      (hcomm q ((show titsQ ≤ titsCt from inf_le_left) hq)).symm⟩
  rw [titsCCQ_eq] at hwQ
  obtain ⟨c, hcQ, rfl⟩ := List.mem_map.1 hwQ
  have hcN : c ∈ titsCNt := List.mem_of_mem_filter hcQ
  have hrc := (rep_permOfArr (titsCNt_facts hcN).1).1
  have hall : (titsCNt.all fun x => commA c x) = true := by
    refine List.all_eq_true.2 fun x hx => ?_
    have hrx := (rep_permOfArr (titsCNt_facts hx).1).1
    have hxC : permOfArr 1755 x ∈ titsCt := by
      have : permOfArr 1755 x ∈ ((titsCt : Subgroup (Equiv.Perm (Fin 1755))) :
          Set (Equiv.Perm (Fin 1755))) := by
        rw [titsCt_eq]
        exact List.mem_map.2 ⟨x, hx, rfl⟩
      exact this
    exact (commA_iff hrc hrx).2 (hcomm _ hxC)
  have h := List.all_eq_true.1 hcen c hcQ
  simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · exact Or.inl (eq_of_eqA hrc rep_idA h)
  · exact Or.inr (eq_of_eqA hrc titsTInv_rep h)
  · have : eqA 1755 (compA 1755 c c) (idA 1755) = true :=
      (eqA_iff (rep_compA hrc hrc) rep_idA).2 hw2
    rw [h] at this
    exact absurd this (by decide)

abbrev cD (x : titsD) : Subgroup titsD := centralizer {x}

@[expose] def HasCommWitness (x : titsD) : Prop :=
  ∃ P : Subgroup titsD, IsPGroup 2 P ∧ P ≤ ⁅cD x, cD x⁆ ∧ x ∈ ⁅P, P⁆

@[expose] def HasCentreInv (x : titsD) : Prop :=
  ∀ w ∈ cD x, (∀ c ∈ cD x, w * c = c * w) → w * w = 1 → w = 1 ∨ w = x

theorem hasCommWitness_of_conj {x y : titsD} (h : IsConj y x) (hy : HasCommWitness y) :
    HasCommWitness x := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  obtain ⟨P, hP2, hPC, hyP⟩ := hy
  have hmap : (cD y).map (MulAut.conj g).toMonoidHom = cD x := by
    rw [map_conj_centralizer, hg]
  refine ⟨P.map (MulAut.conj g).toMonoidHom, hP2.map _, ?_, ?_⟩
  · rw [← hmap, ← map_commutator]
    exact map_mono hPC
  · rw [← map_commutator, ← hg]
    exact ⟨y, hyP, by simp⟩

theorem hasCentreInv_of_conj {x y : titsD} (h : IsConj y x) (hy : HasCentreInv y) :
    HasCentreInv x := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  intro w hw hcomm hw2
  have hmap : (cD y).map (MulAut.conj g).toMonoidHom = cD x := by
    rw [map_conj_centralizer, hg]
  have hw' : g⁻¹ * w * g ∈ cD y := by
    rw [← hmap] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    simpa [mul_assoc] using hv
  have hcomm' : ∀ c ∈ cD y, g⁻¹ * w * g * c = c * (g⁻¹ * w * g) := by
    intro c hc
    have hc' : g * c * g⁻¹ ∈ cD x := by
      rw [← hmap]
      exact ⟨c, hc, rfl⟩
    have := hcomm _ hc'
    calc g⁻¹ * w * g * c = g⁻¹ * (w * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * w) * g := by rw [this]
      _ = c * (g⁻¹ * w * g) := by group
  have hw2' : g⁻¹ * w * g * (g⁻¹ * w * g) = 1 := by
    calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hw2]; group
  rcases hy _ hw' hcomm' hw2' with h1 | h1
  · left
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = x := by rw [h1, hg]

theorem map_cD_z
    : (cD titsZD).map titsD.subtype = titsH := by
  rw [map_subtype_centralizer]
  exact titsD_centralizer_z

theorem map_cD_t
    : (cD titsTD).map titsD.subtype = titsCt := by
  rw [map_subtype_centralizer]
  exact titsD_centralizer_t.1.symm

theorem mem_cD_iff {x w : titsD} {X : Subgroup (Equiv.Perm (Fin 1755))}
    (hX : (cD x).map titsD.subtype = X) : w ∈ cD x ↔ (w : Equiv.Perm (Fin 1755)) ∈ X := by
  rw [← hX]
  constructor
  · exact fun h => ⟨w, h, rfl⟩
  · rintro ⟨v, hv, hvw⟩
    rwa [Subtype.ext hvw] at hv

theorem hasCommWitness_of_words {x : titsD} {X Y : Subgroup (Equiv.Perm (Fin 1755))}
    (hX : (cD x).map titsD.subtype = X) (hY : IsPGroup 2 Y) {L : List (List ℤ)}
    (hL : ∀ i < 4, wP L i ∈ X) (hu : ⁅wP L 0, wP L 1⁆ ∈ Y) (hv : ⁅wP L 2, wP L 3⁆ ∈ Y)
    (hx : ⁅⁅wP L 0, wP L 1⁆, ⁅wP L 2, wP L 3⁆⁆ = x) : HasCommWitness x := by
  have hXD : X ≤ titsD := by
    rw [← hX]
    exact map_subtype_le _
  let e : ℕ → titsD := fun i => if h : i < 4 then ⟨wP L i, hXD (hL i h)⟩ else 1
  have he : ∀ i < 4, (e i : Equiv.Perm (Fin 1755)) = wP L i := fun i hi => by simp [e, hi]
  have heC : ∀ i < 4, e i ∈ cD x := fun i hi => (mem_cD_iff hX).2 (by rw [he i hi]; exact hL i hi)
  let u : titsD := ⁅e 0, e 1⁆
  let v : titsD := ⁅e 2, e 3⁆
  have hu' : (u : Equiv.Perm (Fin 1755)) = ⁅wP L 0, wP L 1⁆ := by
    simp only [u, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
      he 0 (by norm_num), he 1 (by norm_num)]
  have hv' : (v : Equiv.Perm (Fin 1755)) = ⁅wP L 2, wP L 3⁆ := by
    simp only [v, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
      he 2 (by norm_num), he 3 (by norm_num)]
  let P : Subgroup titsD := closure {u, v}
  have hPY : P ≤ Y.comap titsD.subtype := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact show (u : Equiv.Perm (Fin 1755)) ∈ Y by rw [hu']; exact hu
    · exact show (v : Equiv.Perm (Fin 1755)) ∈ Y by rw [hv']; exact hv
  refine ⟨P, (hY.comap_of_injective _ titsD.subtype_injective).to_le hPY, ?_, ?_⟩
  · rw [closure_le]
    rintro _ (rfl | rfl)
    · exact commutator_mem_commutator (heC 0 (by norm_num)) (heC 1 (by norm_num))
    · exact commutator_mem_commutator (heC 2 (by norm_num)) (heC 3 (by norm_num))
  · have hxuv : x = ⁅u, v⁆ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hu', hv', ← commutatorElement_def, hx]
    rw [hxuv]
    exact commutator_mem_commutator (subset_closure (by simp)) (subset_closure (by simp))

theorem hasCommWitness_z
    (hc : titsSec8Check = true) : HasCommWitness titsZD := by
  obtain ⟨hL, hu, hv, hz⟩ := z_witness hc
  have hJ : IsPGroup 2 titsJ := IsPGroup.of_card (n := 9) (by rw [titsQJ_facts.2.2.2]; norm_num)
  exact hasCommWitness_of_words map_cD_z hJ hL hu hv hz

theorem hasCommWitness_t
    (hc : titsSec8Check = true) : HasCommWitness titsTD := by
  obtain ⟨hL, hu, hv, ht⟩ := t_witness hc
  have hQ : IsPGroup 2 titsQ := IsPGroup.of_card (n := 8) (by rw [card_titsQ]; norm_num)
  exact hasCommWitness_of_words map_cD_t hQ hL hu hv ht

theorem hasCentreInv_z
    : HasCentreInv titsZD := by
  intro w hw hcomm _
  have hw' := (mem_cD_iff map_cD_z).1 hw
  have hc : ∀ c ∈ titsH, (w : Equiv.Perm (Fin 1755)) * c = c * w := by
    intro c hc
    rw [← map_cD_z] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact congrArg Subtype.val (hcomm c' hc')
  rcases eq_one_or_eq_z hw' hc with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem hasCentreInv_t
    (hc : titsSec8Check = true) : HasCentreInv titsTD := by
  intro w hw hcomm hw2
  have hw' := (mem_cD_iff map_cD_t).1 hw
  have hcomm' : ∀ c ∈ titsCt, (w : Equiv.Perm (Fin 1755)) * c = c * w := by
    intro c hc
    rw [← map_cD_t] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact congrArg Subtype.val (hcomm c' hc')
  rcases eq_one_or_eq_t hc hw' hcomm' (congrArg Subtype.val hw2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem tits_involution_centralizer
    (hc : titsSec8Check = true) {x : titsD} (hx : orderOf x = 2) :
    HasCommWitness x ∧ HasCentreInv x ∧ HasTwoCore (cD x) := by
  have hz : HasTwoCore (cD titsZD) :=
    hasTwoCore_centralizer_of_map_eq titsD_centralizer_z hasTwoCore_titsH
  have ht : HasTwoCore (cD titsTD) :=
    hasTwoCore_centralizer_of_map_eq titsD_centralizer_t.1.symm hasTwoCore_titsCt
  rcases titsD_involution_conj x hx with h | h
  · exact ⟨hasCommWitness_of_conj h (hasCommWitness_z hc), hasCentreInv_of_conj h hasCentreInv_z,
      hasTwoCore_centralizer_of_conj h hz⟩
  · exact ⟨hasCommWitness_of_conj h (hasCommWitness_t hc),
      hasCentreInv_of_conj h (hasCentreInv_t hc), hasTwoCore_centralizer_of_conj h ht⟩

end CFSG.ComponentClassification.RankTwoExceptional.TitsSec8
