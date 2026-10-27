module

public import CFSG.Certificates.Kernel.Misc.O62SoundPl
public import CFSG.Certificates.Kernel.Misc.O62SoundGrp

public section

namespace CFSG.KC.Misc.O62

open CFSG.KC.Ord CFSG.KC.Misc
open CFSG.KC.LQT.P (letB impB allN anyN allL anyL)
open CFSG.LargeExtraspecial.O62

theorem levelK_zero (S C : ℕ) : levelK 0 S C = allN (plCnt C) fun i => letB (plAt C i) fun x =>
    letB (spanAdd S x) fun S' => Nat.beq (plCnt (plFilterFrom C i fun y =>
      andB (commK x y) (notB (plMem S' y)))) 0 := rfl

theorem levelK_succ (d S C : ℕ) : levelK (d + 1) S C = allN (plCnt C) fun i =>
    letB (plAt C i) fun x => letB (spanAdd S x) fun S' =>
      letB (plFilterFrom C i fun y => andB (commK x y) (notB (plMem S' y))) fun C' =>
        levelK d S' C' := rfl

theorem plLanes_spanAdd_pure {S x : ℕ} (hS : 2 * plCnt S < 256)
    (hp : ∀ a ∈ plLanes S, a < 2 ^ 36) :
    plLanes (spanAdd S x) = ((plLanes S).map fun s => Code.mul s x).reverse ++ plLanes S := by
  rw [plLanes_spanAdd hS]
  congr 2
  unfold plLanes
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < plCnt S := List.mem_range.1 hi
  show Code.mul (plAt S i) x = Code.mul (plLane S i) x
  rw [plAt_of_lt (hp _ (lane_mem hi'))]

theorem plMem_pure {p y : ℕ} (hp : ∀ a ∈ plLanes p, a < 2 ^ 36) :
    plMem p y = true ↔ y ∈ plLanes p := by
  rw [plMem_iff, mem_plLanes]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rw [← plAt_of_lt (hp _ (lane_mem hi))]; exact h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rw [plAt_of_lt (hp _ (lane_mem hi))]; exact h⟩

theorem search_step {E : List ℕ} (hE : ElAb E) (hEn : E.Nodup) (hEl : E.length ≤ 256)
    {S C : ℕ} (hS : SubG E (plLanes S)) (hsz : plCnt S * 2 < E.length)
    (hCE : ∀ e ∈ E, e ∉ plLanes S → e ∈ plLanes C) (hCp : ∀ a ∈ plLanes C, a < 2 ^ 36) :
    ∃ i < plCnt C, SubG E (plLanes (spanAdd S (plAt C i))) ∧
      plCnt (spanAdd S (plAt C i)) = 2 * plCnt S ∧
      ∀ e ∈ E, e ∉ plLanes (spanAdd S (plAt C i)) →
        e ∈ plLanes (plFilterFrom C i fun y =>
          andB (commK (plAt C i) y) (notB (plMem (spanAdd S (plAt C i)) y))) := by
  classical
  have hSlen : (plLanes S).length = plCnt S := length_plLanes S
  obtain ⟨e₀, he₀E, he₀S⟩ := exists_not_mem hEn (by rw [hSlen]; omega)
  have hex : ∃ j, j < plCnt C ∧ plLane C j ∈ E ∧ plLane C j ∉ plLanes S := by
    obtain ⟨j, hj, hjl⟩ := mem_plLanes.1 (hCE e₀ he₀E he₀S)
    exact ⟨j, hj, hjl ▸ he₀E, hjl ▸ he₀S⟩
  have hi := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex →
      ¬ (j < plCnt C ∧ plLane C j ∈ E ∧ plLane C j ∉ plLanes S) := fun j hj => Nat.find_min hex hj
  generalize Nat.find hex = i at hi hmin
  refine ⟨i, hi.1, ?_⟩
  have hxl : plAt C i = plLane C i := plAt_of_lt (hCp _ (lane_mem hi.1))
  have hxE : plAt C i ∈ E := hxl ▸ hi.2.1
  have hxS : plAt C i ∉ plLanes S := hxl ▸ hi.2.2
  have hS2 : 2 * plCnt S < 256 := by omega
  have hpure : ∀ a ∈ plLanes S, a < 2 ^ 36 := fun a ha => hE.lt a (hS.sub a ha)
  have hspan := plLanes_spanAdd_pure (x := plAt C i) hS2 hpure
  have hSG : SubG E (plLanes (spanAdd S (plAt C i))) := by
    rw [hspan]; exact subG_step hE hS hxE hxS
  refine ⟨hSG, plCnt_spanAdd hS2, ?_⟩
  intro e heE heS'
  have heS : e ∉ plLanes S := fun h => heS' (by rw [hspan]; exact List.mem_append_right _ h)
  obtain ⟨j, hj, hjl⟩ := mem_plLanes.1 (hCE e heE heS)
  have hij : i ≤ j := by
    by_contra hlt
    exact hmin j (not_le.1 hlt) ⟨hj, hjl ▸ heE, hjl ▸ heS⟩
  have hne : j ≠ i := by
    rintro rfl
    apply heS'
    rw [← hjl, ← hxl, hspan]
    refine List.mem_append_left _ (List.mem_reverse.2 (List.mem_map.2 ⟨Code.one,
      hS.elAb.one_mem, one_cmul (hE.lt _ hxE)⟩))
  rw [mem_plLanes_filterFrom]
  refine ⟨j, hj, lt_of_le_of_ne hij (Ne.symm hne), ?_, hjl⟩
  have hpure' : ∀ a ∈ plLanes (spanAdd S (plAt C i)), a < 2 ^ 36 :=
    fun a ha => hE.lt a (hSG.sub a ha)
  have hej : plAt C j = e := by rw [plAt_of_lt (hCp _ (lane_mem hj)), hjl]
  rw [hej, andB_eq, notB_eq, commK_eq, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · simp only [Check.comm, beq_iff_eq]
    exact hE.comm _ hxE e heE
  · cases h : plMem (spanAdd S (plAt C i)) e
    · rfl
    · exact absurd ((plMem_pure hpure').1 h) heS'

theorem levelK_false {E : List ℕ} (hE : ElAb E) (hEn : E.Nodup) (hEl : E.length ≤ 256) :
    ∀ (d S C : ℕ), SubG E (plLanes S) → plCnt S * 2 ^ (d + 1) < E.length →
      (∀ e ∈ E, e ∉ plLanes S → e ∈ plLanes C) → (∀ a ∈ plLanes C, a < 2 ^ 36) →
      levelK d S C = true → False := by
  intro d
  induction d with
  | zero =>
    intro S C hS hsz hCE hCp hlev
    rw [levelK_zero, allN_iff] at hlev
    have hsz' : plCnt S * 2 < E.length := by simpa using hsz
    obtain ⟨i, hi, hSG, hcnt, hCE'⟩ := search_step hE hEn hEl hS hsz' hCE hCp
    have h0 := hlev i hi
    simp only [letB_eq, Nat.beq_eq] at h0
    obtain ⟨e, heE, heS'⟩ := exists_not_mem hEn (by rw [length_plLanes, hcnt]; omega)
    have hmem := hCE' e heE heS'
    have hlen := length_plLanes (plFilterFrom C i fun y =>
      andB (commK (plAt C i) y) (notB (plMem (spanAdd S (plAt C i)) y)))
    rw [h0] at hlen
    exact List.ne_nil_of_mem hmem (List.length_eq_zero_iff.1 hlen)
  | succ d ih =>
    intro S C hS hsz hCE hCp hlev
    rw [levelK_succ, allN_iff] at hlev
    have h2 : 2 ≤ 2 ^ (d + 1 + 1) :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsz' : plCnt S * 2 < E.length :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ h2) hsz
    obtain ⟨i, hi, hSG, hcnt, hCE'⟩ := search_step hE hEn hEl hS hsz' hCE hCp
    have h1 := hlev i hi
    simp only [letB_eq] at h1
    refine ih _ _ hSG ?_ hCE' ?_ h1
    · rw [hcnt]
      calc 2 * plCnt S * 2 ^ (d + 1) = plCnt S * 2 ^ (d + 1 + 1) := by ring
        _ < E.length := hsz
    · intro a ha
      obtain ⟨j, hj, -, -, rfl⟩ := mem_plLanes_filterFrom.1 ha
      exact hCp _ (lane_mem hj)

theorem plLanes_one : plLanes (plPush 0 oneK) = [Code.one] ∧ plCnt (plPush 0 oneK) = 1 := by
  have h0 : plCnt 0 < 255 := by rw [plCnt_eq]; norm_num
  have h1 : oneK < 2 ^ 37 := by
    rw [oneK_eq]; exact lt_trans Code.one_lt (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [plLanes_push h0 h1, plLanes_zero, oneK_eq]
  · rw [plCnt_push h0, plCnt_eq]

theorem rank_core {IP : ℕ} {IL E : List ℕ} (hE : ElAb E) (hEn : E.Nodup)
    (hE32 : E.length = 32) (hIL : plLanes IP = IL.reverse) (hlt : ∀ a ∈ IL, a < 2 ^ 36)
    (hEIL : ∀ a ∈ E, a ≠ Code.one → a ∈ IL) (hx : ∀ i < plCnt IP, rankX IP i = true) :
    False := by
  obtain ⟨hS0, hc0⟩ := plLanes_one
  have hSG0 : SubG E (plLanes (plPush 0 oneK)) := by
    rw [hS0]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro a ha
      rw [List.mem_singleton.1 ha]; exact Code.one_lt
    · exact List.mem_singleton_self _
    · intro a ha b hb
      rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb, cmul_one Code.one_lt]
      exact List.mem_singleton_self _
    · intro a ha b hb
      rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]
    · intro a ha
      rw [List.mem_singleton.1 ha, cmul_one Code.one_lt]
    · intro a ha
      rw [List.mem_singleton.1 ha]; exact hE.one_mem
    · exact List.nodup_singleton _
  have hpure : ∀ a ∈ plLanes IP, a < 2 ^ 36 := by
    intro a ha
    rw [hIL, List.mem_reverse] at ha
    exact hlt a ha
  obtain ⟨i, hi, hSG, hcnt, hCE'⟩ := search_step hE hEn (by omega) hSG0
    (by rw [hc0]; omega) (fun e heE heS => by
      rw [hS0, List.mem_singleton] at heS
      rw [hIL, List.mem_reverse]
      exact hEIL e heE heS) hpure
  have hrank := hx i hi
  simp only [rankX, letB_eq] at hrank
  refine levelK_false hE hEn (by omega) 2 _ _ hSG (by rw [hcnt, hc0]; omega) hCE' ?_ hrank
  intro a ha
  obtain ⟨j, hj, -, -, rfl⟩ := mem_plLanes_filterFrom.1 ha
  exact hpure _ (lane_mem hj)

theorem invsK_eq (CS : List ℕ) : invsK CS = CS.filter Check.isInv := by
  induction CS with
  | nil => rfl
  | cons x t ih =>
    have e : invsK (x :: t) = Bool.rec (motive := fun _ => List ℕ) (invsK t)
        (List.cons x (invsK t)) (isInvK x) := rfl
    rw [e, ih, isInvK_eq, List.filter_cons]
    cases h : Check.isInv x <;> simp

theorem rankPre_facts {m : ℕ} {Tw : List (List ℕ)} {CS IL : List ℕ} {IP : ℕ}
    (hs : sylowK m Tw CS = true) (hp : rankPre CS IL IP = true) :
    IL = (Tw.map wordC).filter Check.isInv ∧
      (∀ a ∈ IL, a < 2 ^ 36 ∧ Code.mul a a = Code.one ∧ a ≠ Code.one) ∧
      plLanes IP = IL.reverse ∧
      ∀ a ∈ IL, ∀ b ∈ IL, a ≠ b → Code.mul a b = Code.mul b a → Code.mul a b ∈ IL := by
  unfold sylowK at hs
  simp only [andB_eq, Bool.and_eq_true, eqLN_iff, codesK_eq] at hs
  have hcs : CS = Tw.map wordC := by
    rw [← hs.1]; congr 1; funext w; exact wordCK_eq w
  subst hcs
  unfold rankPre at hp
  simp only [andB_eq, Bool.and_eq_true, eqLN_iff, Nat.blt_eq, Nat.beq_eq, lenN_eq, allL_eq,
    List.all_eq_true, impB_eq, notB_eq, commK_eq, memN_eq, mulK_eq, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq] at hp
  obtain ⟨hIL, hlen, hIP, hcl⟩ := hp
  have hIL' : IL = (Tw.map wordC).filter Check.isInv := by rw [← hIL, invsK_eq]
  have hILp : ∀ a ∈ IL, a < 2 ^ 36 ∧ Code.mul a a = Code.one ∧ a ≠ Code.one := by
    intro a ha
    rw [hIL', List.mem_filter, List.mem_map] at ha
    obtain ⟨⟨w, _, rfl⟩, hinv⟩ := ha
    simp only [Check.isInv, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hinv
    exact ⟨wordC_lt w, hinv.1, hinv.2⟩
  refine ⟨hIL', hILp, ?_, ?_⟩
  · rw [← hIP]
    exact plLanes_plOf hlen (fun x hx => lt_trans (hILp x hx).1 (by norm_num))
  · intro a ha b hb hne hcomm
    rcases hcl a ha b hb with h | h
    · exfalso
      have h1 : a.beq b = false := by
        cases h2 : a.beq b
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h2) hne
      have h3 : Check.comm a b = true := by simp [Check.comm, hcomm]
      simp [h1, h3] at h
    · exact h

end CFSG.KC.Misc.O62

end
