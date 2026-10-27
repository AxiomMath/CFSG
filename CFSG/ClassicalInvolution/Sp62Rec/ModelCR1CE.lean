module

public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1NA
public import CFSG.ClassicalInvolution.Sp62Rec.Pkg
public import Certificates.Certificate550823

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open
open scoped commutatorElement

section Checks


theorem ceEnumCheck_holds : ceEnumCheck () = true := Certificates.certificate550823.1

theorem v0Check_holds : v0Check () = true := Certificates.certificate550823.2.1

theorem centE0Check_holds : centE0Check () = true := Certificates.certificate550823.2.2.1

theorem e64Check_holds : e64Check () = true := Certificates.certificate550823.2.2.2.1

theorem a6Check_holds : a6Check () = true := Certificates.certificate550823.2.2.2.2.1

theorem commCheck_holds : commCheck () = true := Certificates.certificate550823.2.2.2.2.2

theorem ceEnumCheck_spec :
    enumOK (enumE ()) (gE ()) = true ∧ (enumE ()).elems.size = 11520 ∧
      enumOK (enumV0 ()) (gV0 ()) = true ∧ (enumV0 ()).elems.size = 32 := by
  have h := ceEnumCheck_holds
  simp only [ceEnumCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem v0Check_spec :
    (∀ j < (gV0 ()).size, ((enumE ()).lookup (gV0 ())[j]!).isSome = true) ∧
      (∀ i < (enumV0 ()).elems.size,
        compA (enumV0 ()).elems[i]! (enumV0 ()).elems[i]! = idA ()) ∧
      ∀ s ∈ idxHhat, ∀ j < (gV0 ()).size,
        ((enumV0 ()).lookup (compA (compA (genA ())[s]! (gV0 ())[j]!) (genA ())[s]!)).isSome =
          true := by
  have h := v0Check_holds
  simp only [v0Check, Bool.and_eq_true, allLt_iff, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end Checks

theorem commutator_mem_of_index_two {G : Type*} [Group G] {K : Subgroup G} (hK : K.index = 2)
    (a b : G) : ⁅a, b⁆ ∈ K := by
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hK,
    Subgroup.mul_mem_iff_of_index_two hK, Subgroup.mul_mem_iff_of_index_two hK,
    Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  tauto

theorem card_le_length_of_code_mem {B : Subgroup (StatedSp 3 (ZMod 2))} {M : List (Array ℕ)}
    (h : ∀ y ∈ B, code y ∈ M) : Nat.card B ≤ M.length := by
  classical
  calc Nat.card B = (B : Set (StatedSp 3 (ZMod 2))).ncard := Nat.card_coe_set_eq _
    _ = (code '' (B : Set (StatedSp 3 (ZMod 2)))).ncard :=
        (Set.ncard_image_of_injective _ code_injective).symm
    _ ≤ ({t | t ∈ M} : Set (Array ℕ)).ncard :=
        Set.ncard_le_ncard (by rintro _ ⟨y, hy, rfl⟩; exact h y hy) (List.finite_toSet M)
    _ = M.toFinset.card := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext
        simp
    _ ≤ M.length := List.toFinset_card_le M

section Gens


@[expose] def e0Gen (j : ℕ) : StatedSp 3 (ZMod 2) := yword (e0Words.getD j [])

@[expose] def v0Gen (j : ℕ) : StatedSp 3 (ZMod 2) := ysp (v0Idx.getD j 0)

theorem size_gE : (gE ()).size = 2 := size_wordsA _ _

theorem size_gV0 : (gV0 ()).size = 5 := by
  simp only [gV0, Array.size_ofFn]

theorem e0Words_letters : ∀ w ∈ e0Words, ∀ i ∈ w, i ∈ idxHhat := by
  decide

theorem gE_get : ∀ j < (gE ()).size, (gE ())[j]! = code (e0Gen j) := by
  intro j hj
  rw [size_gE] at hj
  rw [gE]
  exact code_yword_getD (fun _ hi => (idxHhat_spec hi).1) e0Words_letters
    (by rw [show e0Words.length = 2 from rfl]; exact hj)

theorem gV0_get : ∀ j < (gV0 ()).size, (gV0 ())[j]! = code (v0Gen j) := by
  intro j hj
  rw [size_gV0] at hj
  have hlt : v0Idx.getD j 0 < 12 := by
    interval_cases j <;> decide
  rw [v0Gen, code_ysp hlt]
  simp only [gV0]
  rw [getElem!_ofFn_nat _ hj]

theorem ysp_mem_Hhat {i : ℕ} (hi : i ∈ idxHhat) : ysp i ∈ Hhat := by
  have h := yword_mem_Hhat (w := [i]) (by simpa using hi)
  rwa [yword_cons, yword_nil, mul_one] at h

theorem yword_comm (a b : ℕ) : yword [a, b, a, b] = ⁅ysp a, ysp b⁆ := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right (ysp_mul_self a),
    inv_eq_of_mul_eq_one_right (ysp_mul_self b)]
  simp only [yword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc]

theorem E0_le_Hhat : E0 ≤ Hhat := by
  rw [E0, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact Hhat.mul_mem (Hhat.mul_mem (Hhat.mul_mem h₁ h₂) (Hhat.inv_mem h₁)) (Hhat.inv_mem h₂)

theorem e0Gen_mem_E0 (j : ℕ) : e0Gen j ∈ E0 := by
  have hc : ∀ a b : ℕ, a ∈ idxHhat → b ∈ idxHhat → yword [a, b, a, b] ∈ E0 := by
    intro a b ha hb
    rw [yword_comm, E0]
    exact Subgroup.commutator_mem_commutator (ysp_mem_Hhat ha) (ysp_mem_Hhat hb)
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj
  · rw [e0Gen, show e0Words.getD 0 [] = [2, 10, 2, 10] ++ [2, 10, 2, 10] from rfl, yword_append]
    exact E0.mul_mem (hc 2 10 (by decide) (by decide)) (hc 2 10 (by decide) (by decide))
  · rw [e0Gen, show e0Words.getD 1 [] = [8, 11, 8, 11] ++ [0, 2, 0, 2] from rfl, yword_append]
    exact E0.mul_mem (hc 8 11 (by decide) (by decide)) (hc 0 2 (by decide) (by decide))
  · rw [e0Gen, List.getD_eq_default _ _ (by rw [show e0Words.length = 2 from rfl]; exact hj),
      yword_nil]
    exact E0.one_mem

theorem V0_eq_closure : V0 = Subgroup.closure (v0Gen '' Set.Iio (gV0 ()).size) := by
  rw [size_gV0]
  have h1 : ∀ n < 12, (n ≤ 1 ∨ (3 ≤ n ∧ n ≤ 5)) → ∃ j < 5, v0Idx.getD j 0 = n := by
    decide
  have h2 : ∀ j < 5, v0Idx.getD j 0 < 12 ∧
      (v0Idx.getD j 0 ≤ 1 ∨ (3 ≤ v0Idx.getD j 0 ∧ v0Idx.getD j 0 ≤ 5)) := by
    decide
  apply le_antisymm
  · rw [V0, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hji⟩ := h1 i.val i.2 hi
    exact Subgroup.subset_closure ⟨j, hj, by rw [v0Gen, hji, ysp_eq]⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨hlt, hj'⟩ := h2 j hj
    rw [SetLike.mem_coe, v0Gen, ysp, dif_pos hlt]
    exact yamakiSp_mem_V0 hj'

end Gens

section E0Enum


theorem E0_eq_closure : E0 = Subgroup.closure (e0Gen '' Set.Iio (gE ()).size) := by
  have hKE : Subgroup.closure (e0Gen '' Set.Iio (gE ()).size) ≤ E0 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact e0Gen_mem_E0 j
  refine le_antisymm ?_ hKE
  have hKH := hKE.trans E0_le_Hhat
  have hcard : Nat.card (Subgroup.closure (e0Gen '' Set.Iio (gE ()).size)) = 11520 := by
    rw [card_closure_eq gE_get ceEnumCheck_spec.1, ceEnumCheck_spec.2.1]
  have hidx : ((Subgroup.closure (e0Gen '' Set.Iio (gE ()).size)).subgroupOf Hhat).index = 2 := by
    have h := Subgroup.card_mul_index
      ((Subgroup.closure (e0Gen '' Set.Iio (gE ()).size)).subgroupOf Hhat)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv, hcard, card_Hhat] at h
    omega
  rw [E0, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  have h := commutator_mem_of_index_two hidx ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
  rw [Subgroup.mem_subgroupOf, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv] at h
  rw [commutatorElement_def]
  exact h

theorem mem_E0_iff_isSome (x : StatedSp 3 (ZMod 2)) :
    x ∈ E0 ↔ ((enumE ()).lookup (code x)).isSome := by
  rw [E0_eq_closure]
  exact mem_closure_iff_isSome gE_get ceEnumCheck_spec.1 x

theorem card_E0 : Nat.card E0 = 11520 := by
  rw [E0_eq_closure, card_closure_eq gE_get ceEnumCheck_spec.1, ceEnumCheck_spec.2.1]

end E0Enum

section V0Enum


theorem mem_V0_iff_isSome (x : StatedSp 3 (ZMod 2)) :
    x ∈ V0 ↔ ((enumV0 ()).lookup (code x)).isSome := by
  rw [V0_eq_closure]
  exact mem_closure_iff_isSome gV0_get ceEnumCheck_spec.2.2.1 x

theorem card_V0 : Nat.card V0 = 32 := by
  rw [V0_eq_closure, card_closure_eq gV0_get ceEnumCheck_spec.2.2.1, ceEnumCheck_spec.2.2.2]

theorem V0_mul_self : ∀ v ∈ V0, v * v = 1 := by
  intro v hv
  obtain ⟨i, hi, hie⟩ := exists_lt_of_lookup ((mem_V0_iff_isSome v).mp hv)
  apply code_injective
  rw [code_mul, ← hie, code_one]
  exact v0Check_spec.2.1 i hi

theorem V0_comm {v w : StatedSp 3 (ZMod 2)} (hv : v ∈ V0) (hw : w ∈ V0) : v * w = w * v := by
  have h1 := V0_mul_self _ (V0.mul_mem hv hw)
  have h2 : v⁻¹ = v := inv_eq_of_mul_eq_one_right (V0_mul_self v hv)
  have h3 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (V0_mul_self w hw)
  calc v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = w * v := by rw [mul_inv_rev, h2, h3]

theorem conj_mem_V0 {i : Fin 12} (hi : i.val ∈ idxHhat) {v : StatedSp 3 (ZMod 2)} (hv : v ∈ V0) :
    yamakiSp i * v * (yamakiSp i)⁻¹ ∈ V0 := by
  rw [V0_eq_closure] at hv
  induction hv using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    rw [mem_V0_iff_isSome, code_mul, code_mul, yamakiSp_inv, code_yamakiSp, ← gV0_get j hj]
    exact v0Check_spec.2.2 i.val hi j hj
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact V0.one_mem
  | mul a b _ _ iha ihb =>
    rw [show yamakiSp i * (a * b) * (yamakiSp i)⁻¹ =
      yamakiSp i * a * (yamakiSp i)⁻¹ * (yamakiSp i * b * (yamakiSp i)⁻¹) by group]
    exact V0.mul_mem iha ihb
  | inv a _ ih =>
    rw [show yamakiSp i * a⁻¹ * (yamakiSp i)⁻¹ = (yamakiSp i * a * (yamakiSp i)⁻¹)⁻¹ by group]
    exact V0.inv_mem ih

theorem V0_normal_Hhat : ∀ x ∈ Hhat, ∀ v ∈ V0, x * v * x⁻¹ ∈ V0 := by
  intro x hx
  rw [Hhat] at hx
  induction hx using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    exact fun v hv => conj_mem_V0 (mem_idxHhat hi) hv
  | inv_mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    rw [yamakiSp_inv]
    exact fun v hv => conj_mem_V0 (mem_idxHhat hi) hv
  | one =>
    intro v hv
    rwa [one_mul, inv_one, mul_one]
  | mul a b _ _ ha hb =>
    intro v hv
    rw [show a * b * v * (a * b)⁻¹ = a * (b * v * b⁻¹) * a⁻¹ by group]
    exact ha _ (hb v hv)

end V0Enum

section V0E0


theorem V0_le_E0 : V0 ≤ E0 := by
  rw [V0_eq_closure, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, mem_E0_iff_isSome, ← gV0_get j hj]
  exact v0Check_spec.1 j hj

theorem V0_normal : ∀ x ∈ E0, ∀ v ∈ V0, x * v * x⁻¹ ∈ V0 :=
  fun x hx => V0_normal_Hhat x (E0_le_Hhat hx)

instance V0_subgroupOf_E0_normal : (V0.subgroupOf E0).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact V0_normal g g.2 n hn⟩

theorem eq_of_commute_E0 : ∀ x ∈ Hhat, (∀ y ∈ E0, x * y = y * x) → x = 1 ∨ x = alpha := by
  intro x hxH hx
  obtain ⟨i, hi, hie⟩ := exists_lt_of_lookup ((mem_Hhat_iff_isSome x).mp hxH)
  have h := centE0Check_holds
  simp only [centE0Check, allLt_iff, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  have hc : commOK (gE ()) (code x) = true := by
    simp only [commOK, allLt_iff, decide_eq_true_eq]
    intro j hj
    rw [gE_get j hj, ← code_mul, ← code_mul, hx _ (e0Gen_mem_E0 j)]
  rcases h i hi with (h1 | h1) | h1
  · rw [hie, hc] at h1
    cases h1
  · left
    apply code_injective
    rw [code_one, ← hie, h1]
  · right
    apply code_injective
    rw [code_alpha, ← hie, h1]

end V0E0

section E64


theorem code_mem_e64Cands {x b : StatedSp 3 (ZMod 2)} (hx : x ∈ S0) (hxx : x * x = 1)
    (hxb : x * b = b * x) : code x ∈ e64Cands (enumS0 ()).elems (code b) := by
  obtain ⟨k, hk, hke⟩ := exists_lt_of_mem_S0 hx
  simp only [e64Cands, List.mem_filter, List.mem_map, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨k, hk, hke⟩, ?_, ?_⟩
  · rw [← code_mul, hxx, code_one]
  · rw [← code_mul, ← code_mul, hxb]

theorem eq_A0_of_isE64 :
    ∀ A' : Subgroup (StatedSp 3 (ZMod 2)), A' ≤ S0 → IsE64 A' → A' = A0 := by
  intro B hBS hB
  obtain ⟨hcomm, hsq, hcard⟩ := hB
  suffices hle : B ≤ A0 from Subgroup.eq_of_le_of_card_ge hle (by rw [card_A0, hcard])
  rw [SetLike.le_def]
  by_contra hnot
  push Not at hnot
  obtain ⟨b, hbB, hbA⟩ := hnot
  obtain ⟨i, hi, hie⟩ := exists_lt_of_mem_S0 (hBS hbB)
  have h := e64Check_holds
  simp only [e64Check, allLt_iff, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  rcases h i hi with (h1 | h1) | h1
  · rw [hie] at h1
    exact hbA ((mem_A0_iff_isSome b).mpr h1)
  · apply h1
    rw [hie, ← code_mul, hsq b hbB, code_one]
  · rw [hie] at h1
    have hmem : ∀ x ∈ B, code x ∈ e64Core (enumS0 ()).elems (code b) := by
      intro x hx
      simp only [e64Core, List.mem_filter, decide_eq_true_eq]
      refine ⟨code_mem_e64Cands (hBS hx) (hsq x hx) (hcomm x hx b hbB), ?_⟩
      rw [← hcard]
      apply card_le_length_of_code_mem
      intro y hy
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨code_mem_e64Cands (hBS hy) (hsq y hy) (hcomm y hy b hbB),
        by rw [← code_mul, ← code_mul, hcomm x hx y hy]⟩
    have := card_le_length_of_code_mem hmem
    omega

end E64

section HomTable

variable {E : Enum} {gs : Array (Array ℕ)} {s : ℕ → StatedSp 3 (ZMod 2)}

theorem exists_hom_of_homOK {Q : Type} [Group Q] [DecidableEq Q] [Inhabited Q] {hs F : Array Q}
    {L : Subgroup (StatedSp 3 (ZMod 2))} (hL : L = Subgroup.closure (s '' Set.Iio gs.size))
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (henum : enumOK E gs = true)
    (hok : homOK E gs hs F = true) :
    ∃ φ : ↥L →* Q, (∀ x : ↥L, φ x = F[(E.lookup (code (x : StatedSp 3 (ZMod 2)))).getD 0]!) ∧
      ∀ j < gs.size, ∀ hj : s j ∈ L, φ ⟨s j, hj⟩ = hs[j]! := by
  subst hL
  have hnodup : nodupOK E = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.2
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.1.1
  have h0 : E.elems[0]? = some (idA ()) := by
    simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
    exact htree.1
  simp only [homOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at hok
  obtain ⟨⟨-, hF0⟩, hcrit⟩ := hok
  set f : StatedSp 3 (ZMod 2) → Q := fun x => F[(E.lookup (code x)).getD 0]! with hfdef
  have hl1 : E.lookup (code 1) = some 0 := by
    have := (allLt_iff.mp hnodup) 0 (size_pos_of_getElem? h0)
    rw [decide_eq_true_eq, getElem!_eq_of_getElem? h0] at this
    rw [code_one, this]
  have hf1 : f 1 = 1 := by
    simp only [hfdef, hl1, Option.getD_some]
    exact hF0
  have hstep : ∀ x ∈ Subgroup.closure (s '' Set.Iio gs.size), ∀ j < gs.size,
      f (x * s j) = f x * hs[j]! := by
    intro x hx j hj
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hgs henum hx)
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    have hc := hcrit k hks j hj
    rw [hke, hgs j hj, ← code_mul] at hc
    simp only [hfdef, hk, Option.getD_some]
    split at hc
    · rename_i k' hk'
      rw [hk', Option.getD_some]
      exact of_decide_eq_true hc
    · cases hc
  have hgen : ∀ j < gs.size, f (s j) = hs[j]! := by
    intro j hj
    have := hstep 1 (Subgroup.one_mem _) j hj
    rwa [one_mul, hf1, one_mul] at this
  have hmul := map_mul_of_forall_mem hf1 (S := s '' Set.Iio gs.size) (by
    rintro x hx _ ⟨j, hj, rfl⟩
    rw [hstep x hx j hj, hgen j hj])
  refine ⟨{ toFun := fun x => f x
            map_one' := hf1
            map_mul' := fun x y => hmul y y.2 x x.2 }, fun x => rfl, fun j hj _ => hgen j hj⟩

end HomTable

section A6


theorem a6Check_spec :
    homOK (enumE ()) (gE ()) a6Imgs (a6Table ()) = true ∧
      (∀ i < (enumE ()).elems.size,
        (decide ((a6Table ())[i]! = 1) == ((enumV0 ()).lookup (enumE ()).elems[i]!).isSome) =
          true) ∧
      Equiv.Perm.sign a6Sigma1 = 1 ∧ Equiv.Perm.sign a6Sigma2 = 1 := by
  have h := a6Check_holds
  simp only [a6Check, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem exists_a6Hom : ∃ φ : ↥E0 →* Equiv.Perm (Fin 6),
    (∀ x : ↥E0, φ x = (a6Table ())[((enumE ()).lookup (code (x : StatedSp 3 (ZMod 2)))).getD 0]!) ∧
      ∀ x : ↥E0, φ x ∈ alternatingGroup (Fin 6) := by
  obtain ⟨φ, hφ, hgen⟩ := exists_hom_of_homOK E0_eq_closure gE_get ceEnumCheck_spec.1
    a6Check_spec.1
  refine ⟨φ, hφ, fun x => ?_⟩
  obtain ⟨x, hx⟩ := x
  have hx' := hx
  rw [E0_eq_closure] at hx'
  induction hx' using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    have hj2 : j < 2 := by
      have := Set.mem_Iio.mp hj
      rwa [size_gE] at this
    rw [hgen j (by rw [size_gE]; exact hj2) hx]
    interval_cases j
    · exact a6Check_spec.2.2.1
    · exact a6Check_spec.2.2.2
  | one =>
    rw [show (⟨1, hx⟩ : ↥E0) = 1 from rfl, map_one]
    exact Subgroup.one_mem _
  | mul a b ha' hb' iha ihb =>
    have hma : a ∈ E0 := by rw [E0_eq_closure]; exact ha'
    have hmb : b ∈ E0 := by rw [E0_eq_closure]; exact hb'
    rw [show (⟨a * b, hx⟩ : ↥E0) = ⟨a, hma⟩ * ⟨b, hmb⟩ from rfl, map_mul]
    exact Subgroup.mul_mem _ (iha hma) (ihb hmb)
  | inv a ha' iha =>
    have hma : a ∈ E0 := by rw [E0_eq_closure]; exact ha'
    rw [show (⟨a⁻¹, hx⟩ : ↥E0) = (⟨a, hma⟩ : ↥E0)⁻¹ from rfl, map_inv]
    exact Subgroup.inv_mem _ (iha hma)

theorem exists_a6Hom_surjective : ∃ ψ : ↥E0 →* alternatingGroup (Fin 6),
    Function.Surjective ψ ∧ ψ.ker = V0.subgroupOf E0 := by
  obtain ⟨φ, hφ, hA⟩ := exists_a6Hom
  let ψ : ↥E0 →* alternatingGroup (Fin 6) := φ.codRestrict (alternatingGroup (Fin 6)) hA
  have hker : ψ.ker = V0.subgroupOf E0 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hψ : ψ x = 1 ↔ φ x = 1 := by
      rw [← Subtype.coe_inj]
      rfl
    rw [hψ, hφ]
    obtain ⟨i, hi, hie⟩ := exists_lt_of_lookup ((mem_E0_iff_isSome _).mp x.2)
    have hk := a6Check_spec.2.1 i hi
    have hl : (enumE ()).lookup (code (x : StatedSp 3 (ZMod 2))) = some i := by
      have hnd : nodupOK (enumE ()) = true := by
        have := ceEnumCheck_spec.1
        simp only [enumOK, Bool.and_eq_true] at this
        exact this.2
      have := (allLt_iff.mp hnd) i hi
      rwa [decide_eq_true_eq, hie] at this
    rw [hl, Option.getD_some, mem_V0_iff_isSome, ← hie]
    rw [← beq_iff_eq.mp hk]
    exact decide_eq_true_iff.symm
  refine ⟨ψ, ?_, hker⟩
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, hker, nat_card_alternatingGroup, Nat.card_fin]
  have h1 : Nat.card (V0.subgroupOf E0) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe V0_le_E0).toEquiv, card_V0]
  have h2 := Subgroup.card_mul_index (V0.subgroupOf E0)
  rw [h1, card_E0] at h2
  rw [show (6 : ℕ).factorial / 2 = 360 by decide]
  omega

theorem nonempty_quotient_V0 : Nonempty (↥E0 ⧸ V0.subgroupOf E0 ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨ψ, hψ, hker⟩ := exists_a6Hom_surjective
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem pCore_E0 : CFSG.pCore 2 ↥E0 = V0.subgroupOf E0 := by
  obtain ⟨ψ, hψ, hker⟩ := exists_a6Hom_surjective
  unfold CFSG.pCore
  apply le_antisymm
  · apply sSup_le
    rintro K ⟨hKn, hKp⟩
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    haveI : (K.map ψ).Normal := hKn.map ψ hψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map ψ) with h | h
    · rw [← hker]
      intro k hk
      rw [MonoidHom.mem_ker]
      have : ψ k ∈ K.map ψ := Subgroup.mem_map_of_mem ψ hk
      rwa [h, Subgroup.mem_bot] at this
    · exfalso
      have hp : IsPGroup 2 ↥(K.map ψ) := hKp.map ψ
      rw [h] at hp
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
      rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin,
        show (6 : ℕ).factorial / 2 = 360 by decide] at hn
      have hn9 : n < 9 := by
        by_contra h9
        push Not at h9
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h9
        omega
      interval_cases n <;> omega
  · apply le_sSup
    refine ⟨inferInstance, IsPGroup.of_card (n := 5) ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe V0_le_E0).toEquiv, card_V0]
    norm_num

end A6

section CommData


theorem commMemCheck_spec :
    (∀ w ∈ commFixers ++ commConjs ++ commTriple,
      ((enumE ()).lookup (wordA (genA ()) w)).isSome = true) ∧
      ∀ k < (commGk ()).size, ((enumV0 ()).lookup (commGk ())[k]!).isSome = true := by
  have h := commCheck_holds
  simp only [commCheck, Bool.and_eq_true] at h
  have h1 := h.1.1.1
  simp only [commMemCheck, Bool.and_eq_true, List.all_eq_true, allLt_iff] at h1
  exact ⟨h1.1.2, h1.2⟩

theorem commExprCheck_spec : ∀ i ∈ List.range 5, (∀ k ∈ commExpr.getD i [], k < 5) ∧
    wordA (commGk ()) (commExpr.getD i []) = (genA ())[v0Idx.getD i 0]! := by
  have h := commCheck_holds
  simp only [commCheck, Bool.and_eq_true] at h
  have h1 := h.2
  simp only [commExprCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h1
  exact h1

end CommData

section Commutant


theorem commWords_letters :
    ∀ w ∈ commV1 :: commFixers ++ commConjs ++ commTriple, ∀ i ∈ w, i ∈ idxHhat := by
  decide

theorem commGWords_letters : ∀ w ∈ commGWords, ∀ i ∈ w, i ∈ idxHhat := by
  decide

theorem commWords_lt {w : List ℕ} (hw : w ∈ commFixers ++ commConjs ++ commTriple) :
    ∀ i ∈ w, i < 12 := fun i hi =>
  (idxHhat_spec (commWords_letters w (List.mem_append_right [commV1] hw) i hi)).1

@[expose] def commG (k : ℕ) : StatedSp 3 (ZMod 2) := yword (commGWords.getD k [])

theorem size_commGk : (commGk ()).size = 5 := by
  rw [commGk, size_wordsA]
  rfl

theorem commGk_get : ∀ k < (commGk ()).size, (commGk ())[k]! = code (commG k) := by
  intro k hk
  rw [size_commGk] at hk
  rw [commGk]
  exact code_yword_getD (fun _ hi => (idxHhat_spec hi).1) commGWords_letters
    (by rw [show commGWords.length = 5 from rfl]; exact hk)

theorem commG_eq {k : ℕ} (hk : k < 5) :
    commG k = yword (commConjs.getD k []) * pi12 * (yword (commConjs.getD k []))⁻¹ := by
  have h : commGWords.getD k [] = conjWord (commConjs.getD k []) commV1 := by
    interval_cases k <;> rfl
  rw [commG, h, yword_conjWord, show commV1 = [4] from rfl, yword_pi12]


theorem commWords_E0 {w : List ℕ} (hw : w ∈ commFixers ++ commConjs ++ commTriple) :
    yword w ∈ E0 := by
  rw [mem_E0_iff_isSome, code_yword (commWords_lt hw)]
  exact commMemCheck_spec.1 w hw

theorem commConj_mem_E0 {k : ℕ} (hk : k < 5) : yword (commConjs.getD k []) ∈ E0 := by
  have hmem : commConjs.getD k [] ∈ commConjs :=
    getD_mem (by rw [show commConjs.length = 5 from rfl]; exact hk)
  exact commWords_E0 (List.mem_append_left _ (List.mem_append_right _ hmem))

theorem commTriple_mem_E0 {k : ℕ} (hk : k < 3) : yword (commTriple.getD k []) ∈ E0 := by
  have hmem : commTriple.getD k [] ∈ commTriple :=
    getD_mem (by rw [show commTriple.length = 3 from rfl]; exact hk)
  exact commWords_E0 (List.mem_append_right _ hmem)

theorem closure_commG_le_V0 : Subgroup.closure (commG '' Set.Iio 5) ≤ V0 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk5 : k < 5 := Set.mem_Iio.mp hk
  rw [SetLike.mem_coe, mem_V0_iff_isSome, ← commGk_get k (by rw [size_commGk]; exact hk5)]
  exact commMemCheck_spec.2 k (by rw [size_commGk]; exact hk5)

theorem V0_le_closure_commG : V0 ≤ Subgroup.closure (commG '' Set.Iio 5) := by
  rw [V0_eq_closure, Subgroup.closure_le, size_gV0]
  rintro _ ⟨j, hj, rfl⟩
  have hj5 : j < 5 := Set.mem_Iio.mp hj
  obtain ⟨hks, hprod⟩ := commExprCheck_spec j (List.mem_range.mpr hj5)
  have hlt : v0Idx.getD j 0 < 12 := by
    interval_cases j <;> decide
  have hcode : code ((commExpr.getD j []).map commG).prod = code (v0Gen j) := by
    rw [code_prod_map (gs := commGk ()) _ fun k hk => commGk_get k (by
      rw [size_commGk]; exact hks k hk), hprod, v0Gen, code_ysp hlt]
  rw [SetLike.mem_coe, ← code_injective hcode]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
  exact Subgroup.subset_closure ⟨k, hks k hk, rfl⟩


theorem commutant_V0 : ∀ f : MulAut ↥(V0.subgroupOf E0),
    (∀ (x : ↥E0) (v : ↥(V0.subgroupOf E0)),
      f (MulAut.conjNormal x v) = MulAut.conjNormal x (f v)) → f = 1 := by
  intro f hf
  let el : (v : StatedSp 3 (ZMod 2)) → v ∈ V0 → ↥(V0.subgroupOf E0) :=
    fun v hv => ⟨⟨v, V0_le_E0 hv⟩, Subgroup.mem_subgroupOf.mpr hv⟩
  let fv : (v : StatedSp 3 (ZMod 2)) → v ∈ V0 → StatedSp 3 (ZMod 2) :=
    fun v hv => ((f (el v hv) : ↥E0) : StatedSp 3 (ZMod 2))
  have hfvV : ∀ v hv, fv v hv ∈ V0 := fun v hv => Subgroup.mem_subgroupOf.mp (f (el v hv)).2
  have hfv_congr : ∀ v v' (hv : v ∈ V0) (hv' : v' ∈ V0), v = v' → fv v hv = fv v' hv' := by
    rintro v _ hv hv' rfl
    rfl
  have hfv_conj : ∀ c (hc : c ∈ E0) v (hv : v ∈ V0),
      fv (c * v * c⁻¹) (V0_normal c hc v hv) = c * fv v hv * c⁻¹ := by
    intro c hc v hv
    have h1 := hf ⟨c, hc⟩ (el v hv)
    have h2 : MulAut.conjNormal (⟨c, hc⟩ : ↥E0) (el v hv) =
        el (c * v * c⁻¹) (V0_normal c hc v hv) := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, el, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2] at h1
    have h3 := congrArg (fun u : ↥(V0.subgroupOf E0) => ((u : ↥E0) : StatedSp 3 (ZMod 2))) h1
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
    exact h3
  have hfv_mul : ∀ v w (hv : v ∈ V0) (hw : w ∈ V0),
      fv (v * w) (V0.mul_mem hv hw) = fv v hv * fv w hw := by
    intro v w hv hw
    have he : el (v * w) (V0.mul_mem hv hw) = el v hv * el w hw :=
      Subtype.ext (Subtype.ext (by simp only [el, Subgroup.coe_mul]))
    simp only [fv, he, map_mul, Subgroup.coe_mul]
  have hfv_one : fv 1 V0.one_mem = 1 := by
    have he : el 1 V0.one_mem = 1 :=
      Subtype.ext (Subtype.ext (by simp only [el, OneMemClass.coe_one]))
    simp only [fv, he, map_one, OneMemClass.coe_one]
  have hfv_inv : ∀ v (hv : v ∈ V0), fv v⁻¹ (V0.inv_mem hv) = (fv v hv)⁻¹ := by
    intro v hv
    have he : el v⁻¹ (V0.inv_mem hv) = (el v hv)⁻¹ :=
      Subtype.ext (Subtype.ext (by simp only [el, Subgroup.coe_inv]))
    simp only [fv, he, map_inv, Subgroup.coe_inv]
  have hfv_inj : ∀ v w (hv : v ∈ V0) (hw : w ∈ V0), fv v hv = fv w hw → v = w := by
    intro v w hv hw h
    have h1 : f (el v hv) = f (el w hw) := Subtype.ext (Subtype.ext h)
    have h2 := f.injective h1
    exact congrArg (fun u : ↥(V0.subgroupOf E0) => ((u : ↥E0) : StatedSp 3 (ZMod 2))) h2
  have hαc : ∀ c ∈ E0, c * alpha * c⁻¹ = alpha := by
    intro c hc
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (Hhat_le_centralizer_alpha (E0_le_Hhat hc))
    rw [this, mul_inv_cancel_right]
  have hαp : pi12 * alpha = alpha * pi12 :=
    Subgroup.mem_centralizer_singleton_iff.mp (Hhat_le_centralizer_alpha (S0_le_Hhat pi12_mem_S0))
  have h := commCheck_holds
  simp only [commCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, hfix⟩, htrip⟩, -⟩ := h
  simp only [commFixCheck, Bool.and_eq_true, allLt_iff, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hfix
  simp only [commTripleCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at htrip
  obtain ⟨⟨⟨hv1, hα1⟩, hxv⟩, hxyz⟩ := htrip
  obtain ⟨hdv, hfixV⟩ := hfix
  have hcv : code pi12 = wordA (genA ()) commV1 := by
    rw [← yword_pi12, code_yword (by decide)]
    rfl
  have hds : ∀ d ∈ commFixers, yword d ∈ E0 ∧ yword d * pi12 = pi12 * yword d := by
    intro d hd
    have hd' : d ∈ commFixers ++ commConjs ++ commTriple :=
      List.mem_append_left _ (List.mem_append_left _ hd)
    refine ⟨commWords_E0 hd', ?_⟩
    simp only [fixedBy, List.all_eq_true, List.mem_map, decide_eq_true_eq] at hdv
    have := hdv _ ⟨d, hd, rfl⟩
    apply code_injective
    rw [code_mul, code_mul, code_yword (commWords_lt hd'), hcv]
    exact this
  have hp12 : pi12 ∈ V0 := pi12_mem_V0
  obtain ⟨w, hwd⟩ : ∃ w, fv pi12 hp12 = w := ⟨_, rfl⟩
  have hwV : w ∈ V0 := hwd ▸ hfvV pi12 hp12
  have hwfix : ∀ d ∈ commFixers, yword d * w = w * yword d := by
    intro d hd
    obtain ⟨hdE, hdc⟩ := hds d hd
    have h1 := hfv_conj (yword d) hdE pi12 hp12
    have h2 : yword d * pi12 * (yword d)⁻¹ = pi12 := by
      rw [hdc, mul_inv_cancel_right]
    rw [hfv_congr _ _ (V0_normal _ hdE pi12 hp12) hp12 h2, hwd] at h1
    calc yword d * w = yword d * w * (yword d)⁻¹ * yword d := by group
      _ = w * yword d := by rw [← h1]
  have hw4 : w = 1 ∨ w = pi12 ∨ w = alpha ∨ w = pi12 * alpha := by
    obtain ⟨i, hi, hie⟩ := exists_lt_of_lookup ((mem_V0_iff_isSome w).mp hwV)
    have hfb : fixedBy (commFixers.map (wordA (genA ()))) (enumV0 ()).elems[i]! = true := by
      simp only [fixedBy, List.all_eq_true, List.mem_map, decide_eq_true_eq]
      rintro _ ⟨d, hd, rfl⟩
      have hd' : d ∈ commFixers ++ commConjs ++ commTriple :=
        List.mem_append_left _ (List.mem_append_left _ hd)
      rw [hie, ← code_yword (commWords_lt hd'), ← code_mul, ← code_mul, hwfix d hd]
    rcases hfixV i hi with h1 | (((h1 | h1) | h1) | h1)
    · rw [hfb] at h1
      cases h1
    · exact Or.inl (code_injective (by rw [← hie, h1, code_one]))
    · exact Or.inr (Or.inl (code_injective (by rw [← hie, h1, hcv])))
    · exact Or.inr (Or.inr (Or.inl (code_injective (by rw [← hie, h1, code_alpha]))))
    · exact Or.inr (Or.inr (Or.inr
        (code_injective (by rw [← hie, h1, code_mul, hcv, code_alpha]))))
  have hct : ∀ k < 3, code (yword (commTriple.getD k []) * pi12 *
      (yword (commTriple.getD k []))⁻¹) =
        wordA (genA ()) (conjWord (commTriple.getD k []) commV1) := by
    intro k hk
    have hmem : commTriple.getD k [] ∈ commTriple :=
      getD_mem (by rw [show commTriple.length = 3 from rfl]; exact hk)
    rw [← yword_pi12, show [4] = commV1 from rfl, ← yword_conjWord,
      code_yword (lt_of_mem_conjWord (commWords_lt (List.mem_append_right _ hmem)) (by decide))]
  obtain ⟨c0, hc0⟩ : ∃ c, yword (commTriple.getD 0 []) = c := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, yword (commTriple.getD 2 []) = c := ⟨_, rfl⟩
  have hc0E : c0 ∈ E0 := hc0 ▸ commTriple_mem_E0 (by decide)
  have hc2E : c2 ∈ E0 := hc2 ▸ commTriple_mem_E0 (by decide)
  have hct0 := hct 0 (by decide)
  have hct1 := hct 1 (by decide)
  have hct2 := hct 2 (by decide)
  rw [hc0] at hct0
  rw [hc2] at hct2
  rw [show yword (commTriple.getD 1 []) = 1 by
    rw [show commTriple.getD 1 [] = [] from rfl, yword_nil], one_mul, inv_one, mul_one] at hct1
  have hxv' : c0 * pi12 * c0⁻¹ ≠ pi12 := fun h => hxv (by rw [← hct0, h, hcv])
  have hxyz' : c0 * pi12 * c0⁻¹ * pi12 = c2 * pi12 * c2⁻¹ :=
    code_injective (by rw [code_mul, hct0, hct1, hct2]; exact hxyz)
  have hx0V : c0 * pi12 * c0⁻¹ ∈ V0 := V0_normal c0 hc0E pi12 hp12
  have hz0V : c2 * pi12 * c2⁻¹ ∈ V0 := V0_normal c2 hc2E pi12 hp12
  rcases hw4 with rfl | rfl | rfl | rfl
  ·
    exfalso
    apply hv1
    rw [← hcv, hfv_inj pi12 1 hp12 V0.one_mem (hwd.trans hfv_one.symm), code_one]
  ·
    have hfg : ∀ k < 5, ∀ hk : commG k ∈ V0, fv (commG k) hk = commG k := by
      intro k hk5 hk
      have hE := commConj_mem_E0 hk5
      have h1 := hfv_conj _ hE pi12 hp12
      rw [hwd] at h1
      rw [hfv_congr _ _ hk (V0_normal _ hE pi12 hp12) (commG_eq hk5), h1, commG_eq hk5]
    have key : ∀ u ∈ Subgroup.closure (commG '' Set.Iio 5), ∀ hu : u ∈ V0, fv u hu = u := by
      intro u hu'
      induction hu' using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨k, hk, rfl⟩ := ha
        exact fun hu => hfg k (Set.mem_Iio.mp hk) hu
      | one => exact fun _ => hfv_one
      | mul a b ha' hb' iha ihb =>
        intro hab
        have haV : a ∈ V0 := closure_commG_le_V0 ha'
        have hbV : b ∈ V0 := closure_commG_le_V0 hb'
        rw [hfv_congr _ _ hab (V0.mul_mem haV hbV) rfl, hfv_mul a b haV hbV, iha haV, ihb hbV]
      | inv a ha' iha =>
        intro hai
        have haV : a ∈ V0 := closure_commG_le_V0 ha'
        rw [hfv_congr _ _ hai (V0.inv_mem haV) rfl, hfv_inv a haV, iha haV]
    apply MulEquiv.ext
    intro u
    have hu : ((u : ↥E0) : StatedSp 3 (ZMod 2)) ∈ V0 := Subgroup.mem_subgroupOf.mp u.2
    have hel : el _ hu = u := Subtype.ext (Subtype.ext rfl)
    have h1 := key _ (V0_le_closure_commG hu) hu
    change ((f (el _ hu) : ↥E0) : StatedSp 3 (ZMod 2)) = _ at h1
    rw [hel] at h1
    rw [MulAut.one_apply]
    exact Subtype.ext (Subtype.ext h1)
  ·
    exfalso
    apply hxv'
    have h1 := hfv_conj c0 hc0E pi12 hp12
    rw [hwd, hαc c0 hc0E] at h1
    exact hfv_inj _ _ hx0V hp12 (h1.trans hwd.symm)
  ·
    exfalso
    apply hα1
    have hfx : fv (c0 * pi12 * c0⁻¹) hx0V = c0 * pi12 * c0⁻¹ * alpha := by
      rw [hfv_conj c0 hc0E pi12 hp12, hwd, show c0 * (pi12 * alpha) * c0⁻¹ =
        c0 * pi12 * c0⁻¹ * (c0 * alpha * c0⁻¹) by group, hαc c0 hc0E]
    have hfz : fv (c2 * pi12 * c2⁻¹) hz0V = c2 * pi12 * c2⁻¹ * alpha := by
      rw [hfv_conj c2 hc2E pi12 hp12, hwd, show c2 * (pi12 * alpha) * c2⁻¹ =
        c2 * pi12 * c2⁻¹ * (c2 * alpha * c2⁻¹) by group, hαc c2 hc2E]
    have hz : fv (c2 * pi12 * c2⁻¹) hz0V = fv (c0 * pi12 * c0⁻¹) hx0V * fv pi12 hp12 := by
      rw [hfv_congr _ _ hz0V (V0.mul_mem hx0V hp12) hxyz'.symm, hfv_mul _ _ hx0V hp12]
    rw [hfz, hfx, hwd] at hz
    have key : c2 * pi12 * c2⁻¹ * alpha = c2 * pi12 * c2⁻¹ * alpha * alpha := by
      calc c2 * pi12 * c2⁻¹ * alpha
          = c0 * pi12 * c0⁻¹ * alpha * (pi12 * alpha) := hz
        _ = c0 * pi12 * c0⁻¹ * (alpha * pi12) * alpha := by group
        _ = c0 * pi12 * c0⁻¹ * (pi12 * alpha) * alpha := by rw [hαp]
        _ = c0 * pi12 * c0⁻¹ * pi12 * alpha * alpha := by group
        _ = c2 * pi12 * c2⁻¹ * alpha * alpha := by rw [hxyz']
    have hα : alpha = 1 := (left_eq_mul.mp key)
    rw [← code_alpha, hα, code_one]

end Commutant

end CFSG.ClassicalInvolution.Sp62Rec
