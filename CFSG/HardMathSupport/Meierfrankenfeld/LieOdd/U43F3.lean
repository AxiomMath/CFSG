
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43F3Base

public import Certificates.Certificate13005
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem outFacts : OutFacts := by
  have h := Certificates.certificate13005
  simp only [u43OutCheck, Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hpos, hinv⟩, hdist⟩, hcl⟩, hwit⟩, hpairs⟩ := h
  refine ⟨hpos, hinv, hdist, hcl, hwit, ?_⟩
  intro k₁ hk₁ k₂ hk₂ hi₁ hm₁ hi₂ hm₂
  exact hpairs k₁ ⟨hk₁, by simp [memNA] at hm₁ ⊢; simp_all⟩ k₂ ⟨hk₂, by simp [memNA] at hm₂ ⊢; simp_all⟩

theorem rep_tTab
    (hf : AutFacts) (k : ℕ) : Rep 820 (tTab k) (tElt k) := by
  have ho := outFacts
  have hnl : 0 < 2 * tGensG.length := by have := ho.pos; rw [tGens_length] at this; omega
  unfold tTab tElt
  rw [tGens_length]
  exact rep_treeP rep_idA hnl (fun t g l hl h => rep_mulStepP tGens_length (rep_tGens hf)
    (fun j hj => ho.inv j (by rw [tGens_length]; exact hj)) t g l hl h) tPar tLab fuel k

theorem tEnum
    (hf : AutFacts) :
    (∀ k, tElt k ∈ tSub) ∧ (∀ h ∈ tSub, ∃ k < 1024, tElt k = h) ∧
      (∀ i < 1024, ∀ j < 1024, tElt i = tElt j → i = j) := by
  have ho := outFacts
  exact enum_specP tGens_length (rep_tGens hf)
    (fun j hj => ho.inv j (by rw [tGens_length]; exact hj))
    (by have := ho.pos; rw [tGens_length] at this; exact this) (by norm_num) ho.closed ho.dist

theorem card_tSub
    (hf : AutFacts) : Nat.card tSub = 1024 := by
  obtain ⟨hmem, hsurj, hinj⟩ := tEnum hf
  have : Function.Bijective (fun k : Fin 1024 => (⟨tElt k, hmem k⟩ : tSub)) := by
    constructor
    · intro i j hij
      exact Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val hij))
    · intro h
      obtain ⟨k, hk, hkh⟩ := hsurj h h.2
      exact ⟨⟨k, hk⟩, Subtype.ext hkh⟩
  rw [← Nat.card_eq_of_bijective _ this]
  simp

theorem exists_conj_mem_tSub
    (hf : AutFacts)
    (r₁ r₂ : (Nrm : Subgroup Gp)) (h1 : r₁ * r₁ = 1) (h2 : r₂ * r₂ = 1)
    (hc : r₁ * r₂ = r₂ * r₁) :
    ∃ c : (Nrm : Subgroup Gp), ((c * r₁ * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) ∈ tSub ∧
      ((c * r₂ * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) ∈ tSub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Tsyl : Sylow 2 (Nrm : Subgroup Gp) := Sylow.ofCard (tSub.subgroupOf Nrm) (by
    have h : Nat.card (tSub.subgroupOf Nrm) = Nat.card tSub :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (tSub_le_Nrm hf)).toEquiv
    rw [h, card_tSub hf, card_Nrm, factorization_two_Nrm]
    norm_num)
  let E : Subgroup (Nrm : Subgroup Gp) := Subgroup.closure ({r₁, r₂} : Set (Nrm : Subgroup Gp))
  have hpair : ({r₁, r₂} : Set (Nrm : Subgroup Gp)).Pairwise Commute := by
    intro x hx y hy _
    show x * y = y * x
    rcases hx with hx | hx <;> rcases hy with hx' | hx' <;> rw [hx, hx'] <;>
      first | rfl | exact hc | exact hc.symm
  have := Subgroup.isMulCommutative_closure hpair
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · rw [hx]; exact h1
      · rw [Set.mem_singleton_iff.1 hx]; exact h2
    | one => simp
    | mul x y hx' hy' ihx ihy =>
      have hxy : x * y = y * x := setLike_mul_comm hx' hy'
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x hx' ih => rw [← mul_inv_rev, ih, inv_one]
  have hE : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hsq x.1 x.2)⟩
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (Nrm : Subgroup Gp) Tsyl Q
  have hmem : ∀ x ∈ E, h⁻¹ * x * h ∈ (Tsyl : Subgroup (Nrm : Subgroup Gp)) := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup (Nrm : Subgroup Gp)) := hQ hx
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    simpa [MulAut.conj_inv_apply] using hxQ
  have hr1E : r₁ ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have hr2E : r₂ ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨h⁻¹, ?_, ?_⟩
  · have := hmem r₁ hr1E
    exact Subgroup.mem_subgroupOf.1 (by rw [inv_inv]; exact this :
      h⁻¹ * r₁ * h⁻¹⁻¹ ∈ tSub.subgroupOf Nrm)
  · have := hmem r₂ hr2E
    exact Subgroup.mem_subgroupOf.1 (by rw [inv_inv]; exact this :
      h⁻¹ * r₂ * h⁻¹⁻¹ ∈ tSub.subgroupOf Nrm)

theorem nonSmall_spec {t : Array ℕ}
    {τ : Gp} (ht : Rep 820 t τ) (h : nonSmall t = true) :
    ∃ n ∈ Nsub, 5 < orderOf (τ * (n * τ * n⁻¹)) := by
  unfold nonSmall at h
  rw [List.any_eq_true] at h
  obtain ⟨w, hw, hall⟩ := h
  have hg : Rep 820 (wordTab w) (psi (wordElt w)) := rep_wordTab w
  have hgi : Rep 820 (invCand 820 (wordTab w)) (psi (wordElt w))⁻¹ :=
    rep_inv_of_isInvA hg (outFacts.wit w hw)
  have hu : Rep 820 (compA 820 t (conjTab (wordTab w) t))
      (τ * (psi (wordElt w) * τ * (psi (wordElt w))⁻¹)) :=
    rep_compA ht (rep_conjTab hg ht hgi)
  refine ⟨psi (wordElt w), ⟨_, rfl⟩, ?_⟩
  by_contra hle
  push Not at hle
  set u := τ * (psi (wordElt w) * τ * (psi (wordElt w))⁻¹) with hu'
  have hpos : 0 < orderOf u := orderOf_pos _
  have hk : orderOf u ∈ [1, 2, 3, 4, 5] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have h1 := List.all_eq_true.1 hall _ hk
  rw [Bool.not_eq_true', Bool.eq_false_iff] at h1
  apply h1
  rw [eqA_iff (rep_powTab_perm hu _) rep_idA]
  exact pow_orderOf_eq_one u

theorem no_small_pair_in_T
    (hf : AutFacts)
    {t₁ t₂ : Gp} (h₁ : t₁ ∈ tSub) (h₂ : t₂ ∈ tSub) (hsq₁ : t₁ * t₁ = 1) (hsq₂ : t₂ * t₂ = 1)
    (hne₁ : t₁ ≠ 1) (hne₂ : t₂ ≠ 1) (hn₁ : t₁ ∉ Nsub) (hn₂ : t₂ ∉ Nsub) (hc : t₁ * t₂ = t₂ * t₁)
    (hn₁₂ : t₁ * t₂ ∉ Nsub) (hs₁ : SmallP t₁) (hs₂ : SmallP t₂) (hs₁₂ : SmallP (t₁ * t₂)) :
    False := by
  have ho := outFacts
  obtain ⟨k₁, hk₁, hk₁e⟩ := (tEnum hf).2.1 t₁ h₁
  obtain ⟨k₂, hk₂, hk₂e⟩ := (tEnum hf).2.1 t₂ h₂
  have rep1 : Rep 820 (tTab k₁) t₁ := hk₁e ▸ rep_tTab hf k₁
  have rep2 : Rep 820 (tTab k₂) t₂ := hk₂e ▸ rep_tTab hf k₂
  have hinv1 : isInvol (tTab k₁) = true := (isInvol_iff_P rep1).2 ⟨hsq₁, hne₁⟩
  have hinv2 : isInvol (tTab k₂) = true := (isInvol_iff_P rep2).2 ⟨hsq₂, hne₂⟩
  have hmem1 : memNA (tTab k₁) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hn₁ ((memNA_iff rep1).1 h)
  have hmem2 : memNA (tTab k₂) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hn₂ ((memNA_iff rep2).1 h)
  have hpair := ho.pairs k₁ hk₁ k₂ hk₂ hinv1 hmem1 hinv2 hmem2
  have rep12 : Rep 820 (compA 820 (tTab k₁) (tTab k₂)) (t₁ * t₂) := rep_compA rep1 rep2
  have rep21 : Rep 820 (compA 820 (tTab k₂) (tTab k₁)) (t₂ * t₁) := rep_compA rep2 rep1
  unfold pairOK at hpair
  simp only [Bool.or_eq_true] at hpair
  rcases hpair with ((((hcm | hm12) | hn1) | hn2) | hn12)
  · have : eqA 820 (compA 820 (tTab k₁) (tTab k₂)) (compA 820 (tTab k₂) (tTab k₁)) = true :=
      (eqA_iff rep12 rep21).2 hc
    rw [this] at hcm
    exact Bool.false_ne_true hcm
  · exact hn₁₂ ((memNA_iff rep12).1 hm12)
  · obtain ⟨n, hn, hlt⟩ := nonSmall_spec rep1 hn1
    exact absurd (hs₁ n hn) (not_le.2 hlt)
  · obtain ⟨n, hn, hlt⟩ := nonSmall_spec rep2 hn2
    exact absurd (hs₂ n hn) (not_le.2 hlt)
  · obtain ⟨n, hn, hlt⟩ := nonSmall_spec rep12 hn12
    exact absurd (hs₁₂ n hn) (not_le.2 hlt)

theorem u43F3 :
    U43F3 X₀ := by
  intro ψ₁ ψ₂ h1 h2 hc o1 o2 o12 s1 s2 s12 _ _
  obtain ⟨e, he⟩ := autModel
  have hf := autFacts
  have hsq : ∀ ψ : MulAut X₀, orderOf ψ = 2 → ψ * ψ = 1 := by
    intro ψ h
    rw [← sq, ← h]
    exact pow_orderOf_eq_one ψ
  have hne : ∀ ψ : MulAut X₀, orderOf ψ = 2 → ψ ≠ 1 := by
    rintro ψ h rfl
    simp at h
  set r₁ : (Nrm : Subgroup Gp) := e.symm ψ₁ with hr₁
  set r₂ : (Nrm : Subgroup Gp) := e.symm ψ₂ with hr₂
  have hr1sq : r₁ * r₁ = 1 := by
    rw [hr₁, ← map_mul, hsq ψ₁ h1, map_one]
  have hr2sq : r₂ * r₂ = 1 := by
    rw [hr₂, ← map_mul, hsq ψ₂ h2, map_one]
  have hr1ne : r₁ ≠ 1 := fun h => hne ψ₁ h1 (by
    have := congrArg e h
    simpa [hr₁] using this)
  have hr2ne : r₂ ≠ 1 := fun h => hne ψ₂ h2 (by
    have := congrArg e h
    simpa [hr₂] using this)
  have hrc : r₁ * r₂ = r₂ * r₁ := by
    rw [hr₁, hr₂, ← map_mul, ← map_mul]
    exact congrArg e.symm hc.eq
  have hout1 : (r₁ : Gp) ∉ Nsub := fun h => o1 ((mem_range_conj_iff e he ψ₁).2 h)
  have hout2 : (r₂ : Gp) ∉ Nsub := fun h => o2 ((mem_range_conj_iff e he ψ₂).2 h)
  have hout12 : ((r₁ * r₂ : (Nrm : Subgroup Gp)) : Gp) ∉ Nsub := by
    intro h
    apply o12
    rw [mem_range_conj_iff e he]
    rw [map_mul] at *
    simpa [hr₁, hr₂] using h
  have hsm1 : SmallP (r₁ : Gp) := small_to_perm e he ψ₁ s1
  have hsm2 : SmallP (r₂ : Gp) := small_to_perm e he ψ₂ s2
  have hsm12 : SmallP ((r₁ * r₂ : (Nrm : Subgroup Gp)) : Gp) := by
    have := small_to_perm e he (ψ₁ * ψ₂) s12
    simpa [hr₁, hr₂] using this
  obtain ⟨c, hc1, hc2⟩ := exists_conj_mem_tSub hf r₁ r₂ hr1sq hr2sq hrc
  have hconj : ∀ r : (Nrm : Subgroup Gp), r * r = 1 → r ≠ 1 →
      ((c * r * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) * ((c * r * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) = 1 ∧
      ((c * r * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) ≠ 1 := by
    intro r hr hr1
    constructor
    · have : (c * r * c⁻¹) * (c * r * c⁻¹) = (1 : (Nrm : Subgroup Gp)) := by
        rw [show (c * r * c⁻¹) * (c * r * c⁻¹) = c * (r * r) * c⁻¹ by group, hr]
        group
      exact congrArg Subtype.val this
    · intro h
      apply hr1
      have h' : c * r * c⁻¹ = (1 : (Nrm : Subgroup Gp)) := Subtype.ext h
      have := congrArg (fun x => c⁻¹ * x * c) h'
      simpa [mul_assoc] using this
  have hout_conj : ∀ r : (Nrm : Subgroup Gp), (r : Gp) ∉ Nsub →
      ((c * r * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) ∉ Nsub := by
    intro r hr h
    apply hr
    have := conj_mem_Nsub (Nrm.inv_mem c.2) h
    simpa [mul_assoc] using this
  have e12 : ((c * r₁ * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) * ((c * r₂ * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) =
      ((c * (r₁ * r₂) * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) := by
    have : (c * r₁ * c⁻¹) * (c * r₂ * c⁻¹) = c * (r₁ * r₂) * c⁻¹ := by group
    exact congrArg Subtype.val this
  have e21 : ((c * r₂ * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) * ((c * r₁ * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) =
      ((c * (r₂ * r₁) * c⁻¹ : (Nrm : Subgroup Gp)) : Gp) := by
    have : (c * r₂ * c⁻¹) * (c * r₁ * c⁻¹) = c * (r₂ * r₁) * c⁻¹ := by group
    exact congrArg Subtype.val this
  refine no_small_pair_in_T hf hc1 hc2 (hconj r₁ hr1sq hr1ne).1 (hconj r₂ hr2sq hr2ne).1
    (hconj r₁ hr1sq hr1ne).2 (hconj r₂ hr2sq hr2ne).2 (hout_conj r₁ hout1) (hout_conj r₂ hout2)
    (by rw [e12, e21, hrc]) ?_ (smallN_conj c hsm1) (smallN_conj c hsm2) ?_
  · rw [e12]
    exact hout_conj (r₁ * r₂) hout12
  · rw [e12]
    exact smallN_conj c hsm12

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out
