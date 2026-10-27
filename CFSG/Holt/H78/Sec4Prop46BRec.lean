module

public import CFSG.Holt.H78.Sec4KnownKV
public import CFSG.Holt.H78.Lemma27Real
public import CFSG.Holt.H78.Sec4U34
public import CFSG.Holt.H78.Sec4Lemma48
public import CFSG.Holt.H78.DataPrimitive
public import CFSG.Holt.H78.Sec4Toolkit

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Coord

variable {K : Type*} [Group K] {X : Type*} [MulAction K X] (D : HoltData K X)

@[expose] def HoltData.coordDelta (i : D.ι) (c c' : D.Ψc i) : Set (D.Ψc i) :=
  {d | ∃ y ∈ (D.ρ i).range, y ∈ longInv (Equiv.Perm (D.Ψc i)) (D.Ψc i) ∧ y c = c' ∧ y d = d}

theorem HoltData.mem_coordDelta {i : D.ι} {c c' d : D.Ψc i} :
    d ∈ D.coordDelta i c c' ↔
      ∃ y ∈ (D.ρ i).range, y ∈ longInv (Equiv.Perm (D.Ψc i)) (D.Ψc i) ∧ y c = c' ∧ y d = d :=
  Iff.rfl

theorem HoltData.coord_mem_coordDelta [Finite K] {a b x : X} {u : K} (hu : u ∈ longInvSwap K X a b)
    (hux : u • x = x) (i : D.ι) : D.coord x i ∈ D.coordDelta i (D.coord a i) (D.coord b i) := by
  refine ⟨D.ρ i ⟨u, mem_jHull_of_mem_longInv hu.1⟩, ⟨_, rfl⟩, D.rho_mem_longInv hu.1 i, ?_, ?_⟩
  · rw [← D.coord_smul]
    exact congrArg (D.coord · i) hu.2
  · rw [← D.coord_smul]
    exact congrArg (D.coord · i) hux

theorem HoltData.card_pi_coordDelta_le [Finite K] [Finite X] (a b : X) :
    Nat.card (∀ i, D.coordDelta i (D.coord a i) (D.coord b i)) ≤
      Nat.card (holtDelta K X a b) := by
  classical
  have key : ∀ d : (∀ i, D.coordDelta i (D.coord a i) (D.coord b i)),
      ∃ x : holtDelta K X a b, ∀ i, D.coord (x : X) i = d i := by
    intro d
    choose y hyR hyJ hyab hyd using fun i => (D.mem_coordDelta).mp (d i).2
    obtain ⟨u, hu, hρ⟩ := D.exists_mem_longInvSwap_rho_eq y hyR hyJ hyab
    obtain ⟨x, hx, -⟩ := hu.1.2
    refine ⟨⟨x, u, hu, hx⟩, fun i => ?_⟩
    have h1 : y i (D.coord x i) = D.coord x i := by
      have := D.coord_smul u x i
      rw [hx, hρ] at this
      exact this.symm
    obtain ⟨e, -, he⟩ := (hyJ i).2
    exact (he _ h1).trans (he _ (hyd i)).symm
  choose f hf using key
  refine Nat.card_le_card_of_injective f fun d d' h => funext fun i => Subtype.ext ?_
  rw [← hf d i, ← hf d' i, h]

theorem HoltData.holtDelta_subset_coordDelta {i : D.ι} {N : Subgroup (Equiv.Perm (D.Ψc i))}
    (hN : N ≤ (D.ρ i).range) (c c' : D.Ψc i) :
    holtDelta N (D.Ψc i) c c' ⊆ D.coordDelta i c c' := by
  rintro d ⟨t, ⟨htJ, htc⟩, htd⟩
  exact ⟨t, hN t.2, mem_longInv_subgroup_perm_iff.mp htJ, htc, htd⟩

theorem HoltData.M_le_range_rho (i : D.ι) : D.M i ≤ (D.ρ i).range :=
  Subgroup.map_le_range _ _

theorem HoltData.le_ncard_coordDelta_of_isBenderAction {i : D.ι} {n j e : ℕ}
    (hA : IsBenderAction ↥(D.M i) (D.Ψc i) n j e) {c c' : D.Ψc i} (hcc' : c ≠ c') :
    2 ^ n - 1 ≤ (D.coordDelta i c c').ncard := by
  rw [← hA.ncard_holtDelta hcc']
  exact Set.ncard_le_ncard (D.holtDelta_subset_coordDelta (D.M_le_range_rho i) c c')
    (Set.toFinite _)

theorem HoltData.ncard_coordDelta_of_alternatingGroup [Finite K] {i : D.ι}
    (hA : D.M i = alternatingGroup (D.Ψc i)) {c c' : D.Ψc i} (hcc' : c ≠ c') :
    Fintype.card (D.Ψc i) - 2 ≤ (D.coordDelta i c c').ncard := by
  classical
  have hle : alternatingGroup (D.Ψc i) ≤ (D.ρ i).range := hA ▸ D.M_le_range_rho i
  have h := holtDelta_eq_compl_of_alternatingGroup_le hle (s := D.ρ i D.tHull) ⟨_, rfl⟩
    (D.rho_mem_longInv D.t_mem i) hcc'
  have hc : ({c, c'} : Set (D.Ψc i))ᶜ.ncard = Fintype.card (D.Ψc i) - 2 := by
    rw [Set.ncard_compl, Set.ncard_pair hcc', Nat.card_eq_fintype_card]
  rw [← hc, ← h]
  exact Set.ncard_le_ncard (D.holtDelta_subset_coordDelta le_rfl c c') (Set.toFinite _)

theorem HoltData.three_le_ncard_coordDelta [Finite K] {i : D.ι} {c c' : D.Ψc i} (hcc' : c ≠ c') :
    3 ≤ (D.coordDelta i c c').ncard := by
  rcases D.factor i with ⟨hA, h7⟩ | hSE
  · have := D.ncard_coordDelta_of_alternatingGroup hA hcc'
    omega
  · obtain ⟨n, j, e, hA⟩ := isNaturalSE_iff.mp hSE
    have h1 := D.le_ncard_coordDelta_of_isBenderAction hA hcc'
    have h2 := hA.four_le_q
    omega

theorem HoltData.exists_isBenderAction_of_ncard_coordDelta_le [Finite K] {i : D.ι}
    {c c' : D.Ψc i} (hcc' : c ≠ c') (h3 : (D.coordDelta i c c').ncard ≤ 3) :
    ∃ j e : ℕ, IsBenderAction ↥(D.M i) (D.Ψc i) 2 j e := by
  rcases D.factor i with ⟨hA, h7⟩ | hSE
  · have := D.ncard_coordDelta_of_alternatingGroup hA hcc'
    omega
  · obtain ⟨n, j, e, hA⟩ := isNaturalSE_iff.mp hSE
    have h1 := D.le_ncard_coordDelta_of_isBenderAction hA hcc'
    have h2 := hA.params.2.2
    have hn : n = 2 := by
      by_contra hne
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ⟨j, e, hn ▸ hA⟩

include D in
theorem HoltData.three_le_card_holtDelta_of_ne [Finite K] [Finite X] (hO : jOddCore K X = ⊥)
    (hK : IsStarGroup K X) {a b : X} (hab : a ≠ b) : 3 ≤ Nat.card (holtDelta K X a b) := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, D.coord a i ≠ D.coord b i := by
    by_contra h
    push Not at h
    exact hab ((D.coord_bijective hO).1 (funext h))
  obtain ⟨u, hu⟩ := longInvSwap_nonempty hK a b
  obtain ⟨x, hx, -⟩ := hu.1.2
  have hpos : ∀ i, 1 ≤ Nat.card (D.coordDelta i (D.coord a i) (D.coord b i)) := fun i =>
    Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr
      ⟨⟨⟨_, D.coord_mem_coordDelta hu hx i⟩⟩, inferInstance⟩)
  calc 3 ≤ (D.coordDelta i₀ (D.coord a i₀) (D.coord b i₀)).ncard := D.three_le_ncard_coordDelta hi₀
    _ = Nat.card (D.coordDelta i₀ (D.coord a i₀) (D.coord b i₀)) := (Nat.card_coe_set_eq _).symm
    _ ≤ ∏ i, Nat.card (D.coordDelta i (D.coord a i) (D.coord b i)) :=
        Finset.single_le_prod (fun i _ => hpos i) (Finset.mem_univ i₀)
    _ = Nat.card (∀ i, D.coordDelta i (D.coord a i) (D.coord b i)) := Nat.card_pi.symm
    _ ≤ Nat.card (holtDelta K X a b) := D.card_pi_coordDelta_le a b

end Coord

section FourGroup

theorem exists_notMem_finset_of_card_lt {Ψ : Type*} [Fintype Ψ] (s : Finset Ψ)
    (h : s.card < Fintype.card Ψ) : ∃ x, x ∉ s := by
  by_contra hx
  push Not at hx
  have : s = Finset.univ := Finset.eq_univ_of_forall hx
  rw [this, Finset.card_univ] at h
  exact lt_irrefl _ h

theorem exists_isPGroup_le_alternatingGroup_fix {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]
    (h5 : 5 ≤ Fintype.card Ψ) (c : Ψ) :
    ∃ T : Subgroup (Equiv.Perm Ψ), IsPGroup 2 T ∧ T ≤ alternatingGroup Ψ ∧ 4 ≤ Nat.card T ∧
      ∀ x ∈ T, x c = c := by
  obtain ⟨p₁, h₁⟩ := exists_notMem_finset_of_card_lt {c} (by simp; omega)
  obtain ⟨p₂, h₂⟩ := exists_notMem_finset_of_card_lt {c, p₁}
    ((Finset.card_le_two).trans_lt (by omega))
  obtain ⟨p₃, h₃⟩ := exists_notMem_finset_of_card_lt {c, p₁, p₂}
    ((Finset.card_le_three).trans_lt (by omega))
  obtain ⟨p₄, h₄⟩ := exists_notMem_finset_of_card_lt {c, p₁, p₂, p₃}
    ((Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h₁ h₂ h₃ h₄
  obtain ⟨h2c, h21⟩ := h₂
  obtain ⟨h3c, h31, h32⟩ := h₃
  obtain ⟨h4c, h41, h42, h43⟩ := h₄
  have hcomm : ∀ {a b c d : Ψ}, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := fun hac had hbc hbd => by
    rw [Equiv.swap_mul_eq_mul_swap, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hac had,
      Equiv.swap_apply_of_ne_of_ne hbc hbd]
  set σ₁ : Equiv.Perm Ψ := Equiv.swap p₁ p₂ * Equiv.swap p₃ p₄ with hσ₁
  set σ₂ : Equiv.Perm Ψ := Equiv.swap p₁ p₃ * Equiv.swap p₂ p₄ with hσ₂
  have hinv : ∀ {a b c d : Ψ}, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b * Equiv.swap c d) = 1 := by
      intro a b c d hac had hbc hbd
      rw [show Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b * Equiv.swap c d) =
          Equiv.swap a b * (Equiv.swap c d * Equiv.swap a b) * Equiv.swap c d by group,
        ← hcomm hac had hbc hbd, show Equiv.swap a b * (Equiv.swap a b * Equiv.swap c d) *
          Equiv.swap c d = (Equiv.swap a b * Equiv.swap a b) * (Equiv.swap c d * Equiv.swap c d)
          by group, Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]
  have e1 : σ₁ * σ₁ = 1 := hinv (Ne.symm h31) (Ne.symm h41) (Ne.symm h32) (Ne.symm h42)
  have e2 : σ₂ * σ₂ = 1 := hinv (Ne.symm h21) (Ne.symm h41) h32 (Ne.symm h43)
  have hσ₁p : σ₁ p₁ = p₂ := by
    simp only [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm h31) (Ne.symm h41),
      Equiv.swap_apply_left]
  have hσ₁p₂ : σ₁ p₂ = p₁ := by
    simp only [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm h32) (Ne.symm h42),
      Equiv.swap_apply_right]
  have hσ₁p₃ : σ₁ p₃ = p₄ := by
    simp only [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne h41 h42]
  have hσ₁p₄ : σ₁ p₄ = p₃ := by
    simp only [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne h31 h32]
  have hσ₂p : σ₂ p₁ = p₃ := by
    simp only [hσ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm h21) (Ne.symm h41),
      Equiv.swap_apply_left]
  have e12 : Commute σ₁ σ₂ := by
    show σ₁ * σ₂ = σ₂ * σ₁
    calc σ₁ * σ₂ = σ₁ * Equiv.swap p₁ p₃ * Equiv.swap p₂ p₄ := by rw [hσ₂, ← mul_assoc]
      _ = Equiv.swap p₂ p₄ * σ₁ * Equiv.swap p₂ p₄ := by
          rw [Equiv.mul_swap_eq_swap_mul σ₁ p₁ p₃, hσ₁p, hσ₁p₃]
      _ = Equiv.swap p₂ p₄ * (Equiv.swap p₁ p₃ * σ₁) := by
          rw [mul_assoc, Equiv.mul_swap_eq_swap_mul σ₁ p₂ p₄, hσ₁p₂, hσ₁p₄]
      _ = Equiv.swap p₁ p₃ * Equiv.swap p₂ p₄ * σ₁ := by
          rw [← mul_assoc, hcomm h21 (Ne.symm h32) h41 h43]
      _ = σ₂ * σ₁ := by rw [hσ₂]
  have n1 : σ₁ ≠ 1 := fun h => h21 (by rw [← hσ₁p, h, Equiv.Perm.one_apply])
  have n2 : σ₂ ≠ 1 := fun h => h31 (by rw [← hσ₂p, h, Equiv.Perm.one_apply])
  have n12 : σ₁ ≠ σ₂ := fun h => h32 (by rw [← hσ₂p, ← h, hσ₁p])
  set T := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions σ₁ σ₂ e1 e2 e12
  have hK : IsKleinFour T :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions σ₁ σ₂ e1 e2 n1 n2 n12 e12
  have hmem : ∀ x : Equiv.Perm Ψ, x ∈ T ↔ x = σ₁ * σ₂ ∨ x = σ₁ ∨ x = σ₂ ∨ x = 1 := fun x => Iff.rfl
  have hA₁ : σ₁ ∈ alternatingGroup Ψ := by
    rw [Equiv.Perm.mem_alternatingGroup, hσ₁, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Ne.symm h21), Equiv.Perm.sign_swap (Ne.symm h43)]
    rfl
  have hA₂ : σ₂ ∈ alternatingGroup Ψ := by
    rw [Equiv.Perm.mem_alternatingGroup, hσ₂, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Ne.symm h31), Equiv.Perm.sign_swap (Ne.symm h42)]
    rfl
  have hc₁ : σ₁ c = c := by
    simp only [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm h3c) (Ne.symm h4c),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h₁) (Ne.symm h2c)]
  have hc₂ : σ₂ c = c := by
    simp only [hσ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm h2c) (Ne.symm h4c),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h₁) (Ne.symm h3c)]
  refine ⟨T, IsPGroup.of_card (n := 2) (by rw [hK.card_four]; norm_num), fun x hx => ?_,
    hK.card_four.ge, fun x hx => ?_⟩
  · rcases (hmem x).mp hx with rfl | rfl | rfl | rfl
    · exact mul_mem hA₁ hA₂
    · exact hA₁
    · exact hA₂
    · exact one_mem _
  · rcases (hmem x).mp hx with rfl | rfl | rfl | rfl
    · rw [Equiv.Perm.mul_apply, hc₂, hc₁]
    · exact hc₁
    · exact hc₂
    · rfl

end FourGroup

section Lift

variable {K : Type*} [Group K] [Finite K] {X : Type*} [MulAction K X] (D : HoltData K X)

omit [Finite K] in
theorem HoltData.exists_isPGroup_le_M_fix (i : D.ι) (c : D.Ψc i) :
    ∃ T : Subgroup (Equiv.Perm (D.Ψc i)), IsPGroup 2 T ∧ T ≤ D.M i ∧ 4 ≤ Nat.card T ∧
      ∀ x ∈ T, x c = c := by
  rcases D.factor i with ⟨hA, h7⟩ | hSE
  · obtain ⟨T, hT, hTA, hT4, hTc⟩ := exists_isPGroup_le_alternatingGroup_fix (by omega) c
    exact ⟨T, hT, hTA.trans (le_of_eq hA.symm), hT4, hTc⟩
  · obtain ⟨n, j, e, hA⟩ := isNaturalSE_iff.mp hSE
    refine ⟨seRadical (D.M i) c, hSE.isPGroup_seRadical c, seRadical_le, ?_,
      fun x hx => apply_eq_of_mem_seRadical hx⟩
    rw [hA.card_seRadical c]
    exact hA.four_le_pow

theorem HoltData.exists_isPGroup_of_coord_eq (hO : jOddCore K X = ⊥) {a b : X} {i : D.ι}
    (hab : D.coord a i = D.coord b i) :
    ∃ Q : Subgroup K, IsPGroup 2 Q ∧ 4 ≤ Nat.card Q ∧ ∀ q ∈ Q, q • a = a ∧ q • b = b := by
  obtain ⟨T, hT, hTM, hT4, hTc⟩ := D.exists_isPGroup_le_M_fix i (D.coord a i)
  obtain ⟨Q, -, hQL, hQ, hQT⟩ := D.exists_isPGroup_lift hT hTM (E := ⊥) IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  have hfix : ∀ δ : X, D.coord δ i = D.coord a i → δ ∈ fixSet X (Q.map (jHull K X).subtype) :=
    fun δ hδ => (D.mem_fixSet_map_iff_of_le_L hO hQL δ).mpr (by
      rw [hQT, hδ]
      exact fun x hx => hTc x hx)
  refine ⟨Q.map (jHull K X).subtype, hQ.map _, ?_, fun q hq =>
    ⟨hfix a rfl q hq, hfix b hab.symm q hq⟩⟩
  rw [Subgroup.card_map_of_injective (jHull K X).subtype_injective]
  refine hT4.trans (Nat.card_le_card_of_surjective
    (fun q : Q => (⟨D.ρ i q, hQT ▸ Subgroup.mem_map_of_mem _ q.2⟩ : T)) ?_)
  rintro ⟨x, hx⟩
  rw [← hQT] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨⟨q, hq⟩, rfl⟩

end Lift

section Unitary

variable {X : Type} [Finite X] {L : Subgroup (Equiv.Perm X)} {n e : ℕ}

theorem IsBenderAction.apply_eq_of_unitary (hA : IsBenderAction ↥L X n 3 e)
    {x : Equiv.Perm X} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm X))) (hx2 : x * x = 1)
    {a b : X} (hab : a ≠ b) (hxa : x a = a) (hxb : x b = b)
    {j : Equiv.Perm X} (hj : j ∈ Subgroup.normalizer (L : Set (Equiv.Perm X))) (hj2 : j * j = 1)
    (hja : j a = b) {c : X} (hjc : ∀ d, j d = d → d = c) : x c = c := by
  classical
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  by_cases hx1 : x = 1
  · rw [hx1]; rfl
  have hxL : x ∉ L := fun hxL => by
    have hord : orderOf (⟨x, hxL⟩ : L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [sq, hx2]) hx1
    obtain ⟨d, -, hd⟩ := hL.existsUnique_fixed hord
    exact hab ((hd a hxa).trans (hd b hxb).symm)
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj2
  have hjb : j b = a := by
    rw [← hja, ← Equiv.Perm.mul_apply, hj2, Equiv.Perm.one_apply]
  set y := j * x * j⁻¹ with hy
  have hyN : y ∈ Subgroup.normalizer (L : Set (Equiv.Perm X)) :=
    mul_mem (mul_mem hj hx) (inv_mem hj)
  have hy2 : y * y = 1 := by
    rw [hy, show j * x * j⁻¹ * (j * x * j⁻¹) = j * (x * x) * j⁻¹ by group, hx2, mul_one,
      mul_inv_cancel]
  have hyL : y ∉ L := fun h => hxL ((Subgroup.mem_normalizer_iff.mp hj x).mpr h)
  have hya : y a = a := by
    rw [hy, hjinv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hja, hxb, hjb]
  have hyb : y b = b := by
    rw [hy, hjinv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hjb, hxa, hja]
  have hF : fixedBy X y = fixedBy X x := by
    rw [hA.fixedBy_eq_insert_image_of_unitary hyN hy2 hyL (Ne.symm hab) hya hyb,
      hA.fixedBy_eq_insert_image_of_unitary hx hx2 hxL (Ne.symm hab) hxa hxb]
  have hjF : ∀ d, j d ∈ fixedBy X x ↔ d ∈ fixedBy X x := fun d => by
    have key : ∀ d, d ∈ fixedBy X x → j d ∈ fixedBy X x := fun d hd => by
      rw [← hF, hy, ← smul_fixedBy]
      exact Set.smul_mem_smul_set hd
    refine ⟨fun h => ?_, key d⟩
    have := key _ h
    rwa [← Equiv.Perm.mul_apply, hj2, Equiv.Perm.one_apply] at this
  have hodd : Odd (Nat.card (fixedBy X x)) := by
    rw [Nat.card_coe_set_eq, hA.ncard_fixedBy_of_unitary hx hx2 hxL]
    exact (Nat.even_pow.mpr ⟨even_two, by have := hA.params; omega⟩).add_one
  obtain ⟨d, hd⟩ := exists_apply_eq_of_pow_two_pow_eq_one hodd (s := j.subtypePerm hjF) (k := 1)
    (Equiv.ext fun d => Subtype.ext (by
      simp only [pow_one, sq, Equiv.Perm.mul_apply, Equiv.Perm.subtypePerm_apply,
        Equiv.Perm.one_apply]
      rw [← Equiv.Perm.mul_apply, hj2, Equiv.Perm.one_apply]))
  have hdc : (d : X) = c := hjc _ (congrArg Subtype.val hd)
  have := d.2
  rw [hdc] at this
  exact this

end Unitary

section Recognition

theorem IsBenderAction.of_map_permCongrHom {Δ Δ' : Type*} {M : Subgroup (Equiv.Perm Δ)}
    {n i e : ℕ} (c : Δ ≃ Δ')
    (hA : IsBenderAction ↥(M.map (c.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ')) Δ' n i e) :
    IsBenderAction ↥M Δ n i e := by
  refine hA.of_equiv (c.permCongrHom.subgroupMap M).symm c.symm fun m δ => ?_
  obtain ⟨m₀, rfl⟩ := (c.permCongrHom.subgroupMap M).surjective m
  rw [MulEquiv.symm_apply_apply]
  change c.symm (((c.permCongrHom.subgroupMap M m₀ : Equiv.Perm Δ')) δ) = (m₀ : Equiv.Perm Δ) _
  rw [MulEquiv.coe_subgroupMap_apply, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
    Equiv.symm_apply_apply]

theorem eq_of_prod_le_three {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℕ}
    (hf : ∀ i, 3 ≤ f i) (h : ∏ i, f i ≤ 3) (i j : ι) : i = j := by
  by_contra hij
  have h1 : ∀ k ∈ (Finset.univ : Finset ι), k ∉ ({i, j} : Finset ι) → 1 ≤ f k :=
    fun k _ _ => (hf k).trans' (by norm_num)
  have h2 := Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ {i, j}) h1
  rw [Finset.prod_pair hij] at h2
  have := Nat.mul_le_mul (hf i) (hf j)
  omega

theorem exists_odd_pow_pow_two_pow_eq_one {G : Type*} [Group G] [Finite G] (h : G) :
    ∃ m k : ℕ, Odd m ∧ (h ^ m) ^ 2 ^ k = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  exact ⟨m, k, hm, by rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]⟩

theorem pow_smul_eq_of_forall {G X : Type*} [Group G] [MulAction G X] {S : Set X} {g : G}
    {π : Equiv.Perm S} (h : ∀ δ : S, g • (δ : X) = π δ) (n : ℕ) (δ : S) :
    g ^ n • (δ : X) = ((π ^ n) δ : X) := by
  induction n generalizing δ with
  | zero => rw [pow_zero, pow_zero, one_smul, Equiv.Perm.one_apply]
  | succ n ih => rw [pow_succ, mul_smul, h, ih, pow_succ, Equiv.Perm.mul_apply]

variable {K : Type*} [Group K] [Finite K] {X : Type*} [Finite X] [MulAction K X]
  (D : HoltData K X)

theorem HoltData.exists_isBenderAction_of_card_holtDelta_le_three (hO : jOddCore K X = ⊥)
    {a b : X} (hab : a ≠ b)
    (h2 : ∀ Q : Subgroup K, IsPGroup 2 Q → (∀ q ∈ Q, q • a = a ∧ q • b = b) → Nat.card Q ≤ 2)
    (h3 : Nat.card (holtDelta K X a b) ≤ 3) :
    ∃ i₀ : D.ι, (∀ i, i = i₀) ∧ ∃ j e : ℕ, IsBenderAction ↥(D.M i₀) (D.Ψc i₀) 2 j e := by
  classical
  have hne : ∀ i, D.coord a i ≠ D.coord b i := fun i h => by
    obtain ⟨Q, hQ, hQ4, hQab⟩ := D.exists_isPGroup_of_coord_eq hO h
    have := h2 Q hQ hQab
    omega
  have h3i : ∀ i, 3 ≤ Nat.card (D.coordDelta i (D.coord a i) (D.coord b i)) := fun i => by
    rw [Nat.card_coe_set_eq]; exact D.three_le_ncard_coordDelta (hne i)
  have hprod : ∏ i, Nat.card (D.coordDelta i (D.coord a i) (D.coord b i)) ≤ 3 :=
    (Nat.card_pi.symm.le.trans (D.card_pi_coordDelta_le a b)).trans h3
  obtain ⟨i₀⟩ : Nonempty D.ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    exact hab ((D.coord_bijective hO).1 (funext fun i => isEmptyElim i))
  have hι : ∀ i, i = i₀ := fun i => eq_of_prod_le_three h3i hprod i i₀
  refine ⟨i₀, hι, D.exists_isBenderAction_of_ncard_coordDelta_le (hne i₀) ?_⟩
  rw [← Nat.card_coe_set_eq]
  calc _ = ∏ i, Nat.card (D.coordDelta i (D.coord a i) (D.coord b i)) :=
        (Fintype.prod_eq_single i₀ fun i hi => absurd (hι i) hi).symm
    _ ≤ 3 := hprod

end Recognition

section Main

variable {X : Type} [Fintype X] [DecidableEq X] {H : Subgroup (Equiv.Perm X)}

theorem eq_top_of_exists_swap (hT : HoltStructure H X) (hO : jOddCore H X = ⊥)
    {a b : X} (hab : a ≠ b)
    (h2 : ∀ Q : Subgroup H, IsPGroup 2 Q → (∀ q ∈ Q, q • a = a ∧ q • b = b) → Nat.card Q ≤ 2)
    (h3 : Nat.card (holtDelta H X a b) ≤ 3)
    (hsw : ∃ g : H, g • a = a ∧ g • b = b ∧ ∃ δ₁ δ₂ : holtDelta H X a b, δ₁ ≠ δ₂ ∧
      ∀ δ : holtDelta H X a b, g • (δ : X) = Equiv.swap δ₁ δ₂ δ) :
    Fintype.card X = 5 ∧ H = ⊤ := by
  classical
  obtain ⟨D⟩ := hT
  obtain ⟨i₀, hι, j, e, hA⟩ :=
    D.exists_isBenderAction_of_card_holtDelta_le_three hO hab h2 h3
  have hbij : Function.Bijective fun ω => D.coord ω i₀ := by
    refine ⟨fun ω ω' h => (D.coord_bijective hO).1 (funext fun i => ?_),
      fun c => D.exists_coord_apply_eq i₀ c⟩
    rw [hι i]
    exact h
  have hM := D.map_permCongrHom_map_L (Equiv.ofBijective _ hbij) fun h ω => D.coord_smul h ω i₀
  set MX := (D.L i₀).map (MulAction.toPermHom H X) with hMX
  have hAX : IsBenderAction ↥MX X 2 j e :=
    IsBenderAction.of_map_permCongrHom (Equiv.ofBijective _ hbij) (by rw [hM]; exact hA)
  have hSE : IsNaturalSE (D.M i₀) := isNaturalSE_iff.mpr ⟨2, j, e, hA⟩
  have hLJ : D.L i₀ = jHull H X :=
    le_antisymm (D.L_le i₀) (D.jHull_le_L_of_isNaturalSE hO hι hSE)
  have hhom : MulAction.toPermHom H X = H.subtype := MonoidHom.ext fun h => Equiv.ext fun x => rfl
  have hMX' : MX = (jHull H X).map H.subtype := by rw [hMX, hLJ, hhom]
  have hMXH : MX ≤ H := by
    rw [hMX']
    exact Subgroup.map_subtype_le _
  have hsub : MX.subgroupOf H = jHull H X := by
    rw [hMX']
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hnorm : (MX.subgroupOf H).Normal := by rw [hsub]; infer_instance
  have hN : H ≤ Subgroup.normalizer (MX : Set (Equiv.Perm X)) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hMXH
  obtain ⟨g, hga, hgb, δ₁, δ₂, hδ, hgπ⟩ := hsw
  obtain ⟨m, k, hm, hmk⟩ := exists_odd_pow_pow_two_pow_eq_one g
  set x := g ^ m with hx
  have hπm : Equiv.swap δ₁ δ₂ ^ m = Equiv.swap δ₁ δ₂ := by
    obtain ⟨l, rfl⟩ := hm
    rw [pow_succ, pow_mul, sq, Equiv.swap_mul_self, one_pow, one_mul]
  have hxδ : ∀ δ : holtDelta H X a b, x • (δ : X) = Equiv.swap δ₁ δ₂ δ := fun δ => by
    rw [hx, pow_smul_eq_of_forall hgπ m δ, hπm]
  have hxa : x • a = a := mem_stabilizer_iff.mp (pow_mem (mem_stabilizer_iff.mpr hga) m)
  have hxb : x • b = b := mem_stabilizer_iff.mp (pow_mem (mem_stabilizer_iff.mpr hgb) m)
  have hx1 : x ≠ 1 := fun h => hδ (Subtype.ext (by
    have := hxδ δ₁
    rw [h, one_smul, Equiv.swap_apply_left] at this
    exact this))
  have hx2 : x * x = 1 := by
    have hc := h2 (Subgroup.zpowers x) (isPGroup_zpowers_of_pow_eq_one hmk) fun q hq => by
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      exact ⟨mem_stabilizer_iff.mp (zpow_mem (mem_stabilizer_iff.mpr hxa) z),
        mem_stabilizer_iff.mp (zpow_mem (mem_stabilizer_iff.mpr hxb) z)⟩
    rw [Nat.card_zpowers] at hc
    have hpos := orderOf_pos x
    have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    have h2' : orderOf x = 2 := by omega
    rw [← sq, ← h2', pow_orderOf_eq_one]
  have hox : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
  have hxN : (x : Equiv.Perm X) ∈ Subgroup.normalizer (MX : Set (Equiv.Perm X)) := hN x.2
  have hx2' : (x : Equiv.Perm X) * x = 1 := by rw [← Subgroup.coe_mul, hx2, Subgroup.coe_one]
  have hxa' : (x : Equiv.Perm X) a = a := hxa
  have hxb' : (x : Equiv.Perm X) b = b := hxb
  rcases hAX.benderType.cases' with ⟨rfl, -, -⟩ | ⟨rfl, -, l, -, hl⟩ | ⟨rfl, -, -⟩
  ·
    have h5 : Fintype.card X = 5 := by
      rw [← Nat.card_eq_fintype_card, hAX.card_eq]
      norm_num
    have hMSE : IsNaturalSE MX := isNaturalSE_iff.mpr ⟨2, 1, e, hAX⟩
    have hMalt : MX = alternatingGroup X := hMSE.eq_alternatingGroup_of_card_eq_five h5
    refine ⟨h5, ?_⟩
    have hxM : (x : Equiv.Perm X) ∉ MX := fun hxM => by
      have hord : orderOf (⟨x, hxM⟩ : MX) = 2 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hox]
      obtain ⟨d, -, hd⟩ := hMSE.existsUnique_fixed hord
      exact hab ((hd a hxa').trans (hd b hxb').symm)
    have hle : alternatingGroup X ≤ H := hMalt ▸ hMXH
    have : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hcardA : Nat.card (alternatingGroup X) = 60 := by
      have h := two_mul_card_alternatingGroup (α := X)
      rw [Fintype.card_perm, h5] at h
      rw [Nat.card_eq_fintype_card]
      have h120 : (5 : ℕ).factorial = 120 := rfl
      omega
    obtain ⟨k', hk'⟩ := Subgroup.card_dvd_of_le hle
    have hHle : Nat.card H ≤ 120 := by
      have h := Subgroup.card_le_card_group H
      rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := X), h5] at h
    have hk1 : k' ≠ 1 := fun h => hxM (by
      have hHA : alternatingGroup X = H :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hk', h, mul_one])
      rw [hMalt, hHA]
      exact x.2)
    have hk0 : k' ≠ 0 := fun h => by
      have : 0 < Nat.card H := Nat.card_pos
      rw [hk', h, mul_zero] at this
      omega
    have h120 : Nat.card H = 120 := by rw [hk'] at hHle ⊢; rw [hcardA] at hHle ⊢; omega
    exact Subgroup.eq_top_of_card_eq H (by
      rw [h120, Nat.card_perm, Nat.card_eq_fintype_card (α := X), h5]
      rfl)
  ·
    omega
  ·
    exfalso
    obtain ⟨t, ht, htδ⟩ := δ₁.2
    have ht2 : (t : Equiv.Perm X) * t = 1 := by
      rw [← Subgroup.coe_mul, mul_self_eq_one_of_mem_longInv ht.1, Subgroup.coe_one]
    have hfix := hAX.apply_eq_of_unitary hxN hx2' hab hxa' hxb' (j := (t : Equiv.Perm X))
      (hN t.2) ht2 ht.2 (c := (δ₁ : X)) fun d hd => by
        obtain ⟨ω, -, hω⟩ := ht.1.2
        exact (hω d hd).trans (hω _ htδ).symm
    have h' := hxδ δ₁
    rw [Equiv.swap_apply_left] at h'
    exact hδ (Subtype.ext ((show ((x : Equiv.Perm X)) δ₁ = δ₂ from h').symm.trans hfix).symm)

end Main

end CFSG.Holt.H78
