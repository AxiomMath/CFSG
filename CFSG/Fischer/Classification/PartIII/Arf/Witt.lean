module

public import CFSG.Fischer.Classification.PartIII.Symp.Transvection
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Symplectic LocalSymp
open CFSG.ClassicalGroups.Orthogonal (PolarNondegOn)

namespace Arf

variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']

section Basic

variable (Q : QuadraticForm (ZMod 2) V)

theorem polar_self_zmod2 (x : V) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, zmod2_add_self]

theorem map_smul_zmod2 (c : ZMod 2) (x : V) : Q (c • x) = c * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul]
  rcases zmod_two_cases c with rfl | rfl <;> simp

end Basic

variable (Q : QuadraticForm (ZMod 2) V) in
@[expose] def splitSub (U : Submodule (ZMod 2) V) (s s' : V) : Submodule (ZMod 2) V :=
  U ⊓ LinearMap.ker ((polarBilin Q).flip s) ⊓ LinearMap.ker ((polarBilin Q).flip s')

section Split

variable {Q : QuadraticForm (ZMod 2) V} {U : Submodule (ZMod 2) V} {s s' : V}

theorem mem_splitSub {w : V} :
    w ∈ splitSub Q U s s' ↔ w ∈ U ∧ polar Q w s = 0 ∧ polar Q w s' = 0 := by
  simp [splitSub, and_assoc]

theorem splitSub_le : splitSub Q U s s' ≤ U := fun _ hw => (mem_splitSub.1 hw).1

theorem sub_mem_splitSub (hs : s ∈ U) (hs' : s' ∈ U) (hss' : polar Q s s' = 1) {u : V}
    (hu : u ∈ U) : u - polar Q u s' • s - polar Q u s • s' ∈ splitSub Q U s s' := by
  rw [mem_splitSub]
  refine ⟨U.sub_mem (U.sub_mem hu (U.smul_mem _ hs)) (U.smul_mem _ hs'), ?_, ?_⟩
  · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_self_zmod2,
      polar_comm Q s' s, hss', smul_eq_mul, smul_eq_mul, mul_zero, mul_one, sub_zero, sub_self]
  · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_self_zmod2 Q s',
      hss', smul_eq_mul, smul_eq_mul, mul_zero, mul_one, sub_zero, sub_self]

theorem eq_smul_add_smul_add_sub (u : V) (a b : ZMod 2) :
    u = a • s + b • s' + (u - a • s - b • s') := by
  abel

theorem polar_eq_zero_of_mem_splitSub {w : V} (hw : w ∈ splitSub Q U s s') (a b : ZMod 2) :
    polar Q (a • s + b • s') w = 0 := by
  obtain ⟨-, hws, hws'⟩ := mem_splitSub.1 hw
  rw [polar_add_left, polar_smul_left, polar_smul_left, polar_comm Q s w, polar_comm Q s' w, hws,
    hws', smul_zero, smul_zero, add_zero]

theorem map_add_splitSub (hss' : polar Q s s' = 1) {w : V} (hw : w ∈ splitSub Q U s s')
    (a b : ZMod 2) : Q (a • s + b • s' + w) = a * Q s + b * Q s' + a * b + Q w := by
  rw [QuadraticMap.map_add Q, polar_eq_zero_of_mem_splitSub hw, QuadraticMap.map_add Q,
    map_smul_zmod2, map_smul_zmod2, polar_smul_left, polar_smul_right, hss', smul_eq_mul,
    smul_eq_mul, mul_one, add_zero]

theorem polarNondegOn_splitSub (hU : PolarNondegOn Q U) (hs : s ∈ U) (hs' : s' ∈ U)
    (hss' : polar Q s s' = 1) : PolarNondegOn Q (splitSub Q U s s') := by
  intro w hw hperp
  refine hU w (splitSub_le hw) fun u hu => ?_
  have hp := sub_mem_splitSub hs hs' hss' hu
  rw [eq_smul_add_smul_add_sub u (polar Q u s') (polar Q u s) (s := s) (s' := s'), polar_add_right,
    polar_comm Q w, polar_eq_zero_of_mem_splitSub hw, hperp _ hp, zero_add]

end Split

section Count

variable [Finite V] {Q : QuadraticForm (ZMod 2) V} {U : Submodule (ZMod 2) V} {s s' : V}

theorem ncard_split (hs : s ∈ U) (hs' : s' ∈ U) (hss' : polar Q s s' = 1) (R : V → Prop) :
    {x | x ∈ U ∧ R x}.ncard = {w | w ∈ splitSub Q U s s' ∧ R w}.ncard +
      {w | w ∈ splitSub Q U s s' ∧ R (s + w)}.ncard +
      {w | w ∈ splitSub Q U s s' ∧ R (s' + w)}.ncard +
      {w | w ∈ splitSub Q U s s' ∧ R (s + s' + w)}.ncard := by
  have h := ncard_eq_add_add_add (polarBilin Q) (s := s) (s' := s')
    (by rw [polarBilin_apply_apply, polar_self_zmod2])
    (by rw [polarBilin_apply_apply, polar_self_zmod2])
    (by rw [polarBilin_apply_apply, hss']) (by rw [polarBilin_apply_apply, polar_comm, hss'])
    (fun x => x ∈ U ∧ R x)
  have key : ∀ p ∈ U, {w | (p + w ∈ U ∧ R (p + w)) ∧ polarBilin Q w s = 0 ∧
      polarBilin Q w s' = 0} = {w | w ∈ splitSub Q U s s' ∧ R (p + w)} := by
    intro p hp
    ext w
    simp only [Set.mem_ofPred_eq, polarBilin_apply_apply, mem_splitSub, U.add_mem_iff_right hp]
    tauto
  have key0 := key 0 U.zero_mem
  simp only [zero_add] at key0
  rw [key0, key s hs, key s' hs', key (s + s') (U.add_mem hs hs')] at h
  exact h

theorem ncard_eq_four_mul_splitSub (hs : s ∈ U) (hs' : s' ∈ U) (hss' : polar Q s s' = 1) :
    (U : Set V).ncard = 4 * (splitSub Q U s s' : Set V).ncard := by
  have h := ncard_split hs hs' hss' fun _ => True
  simp only [and_true, SetLike.setOfPred_mem_eq] at h
  omega

theorem ncard_eq_add_ncard (S : Set V) :
    S.ncard = {w | w ∈ S ∧ Q w = 1}.ncard + {w | w ∈ S ∧ Q w = 0}.ncard := by
  rw [← Set.ncard_union_eq]
  · congr 1
    ext w
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rcases zmod_two_cases (Q w) with h | h <;> simp [h]
  · rw [Set.disjoint_left]
    rintro w ⟨-, h1⟩ ⟨-, h0⟩
    rw [h1] at h0
    exact one_ne_zero h0

theorem ncard_splitSub_hyp (hs : s ∈ U) (hs' : s' ∈ U) (hss' : polar Q s s' = 1)
    (hQs : Q s = 0) (hQs' : Q s' = 0) :
    {x | x ∈ U ∧ Q x = 1}.ncard =
      2 * {w | w ∈ splitSub Q U s s' ∧ Q w = 1}.ncard + (splitSub Q U s s' : Set V).ncard := by
  have h := ncard_split hs hs' hss' fun x => Q x = 1
  have hval : ∀ (a b : ZMod 2) {w : V}, w ∈ splitSub Q U s s' →
      Q (a • s + b • s' + w) = a * b + Q w := fun a b w hw => by
    rw [map_add_splitSub hss' hw, hQs, hQs', mul_zero, mul_zero, zero_add, zero_add]
  have e1 : {w | w ∈ splitSub Q U s s' ∧ Q (s + w) = 1} =
      {w | w ∈ splitSub Q U s s' ∧ Q w = 1} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hw => ?_
    have := hval 1 0 hw
    rw [one_smul, zero_smul, add_zero, mul_zero, zero_add] at this
    rw [this]
  have e2 : {w | w ∈ splitSub Q U s s' ∧ Q (s' + w) = 1} =
      {w | w ∈ splitSub Q U s s' ∧ Q w = 1} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hw => ?_
    have := hval 0 1 hw
    rw [one_smul, zero_smul, zero_add, zero_mul, zero_add] at this
    rw [this]
  have e3 : {w | w ∈ splitSub Q U s s' ∧ Q (s + s' + w) = 1} =
      {w | w ∈ splitSub Q U s s' ∧ Q w = 0} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hw => ?_
    have := hval 1 1 hw
    rw [one_smul, one_smul, one_mul] at this
    rw [this]
    rcases zmod_two_cases (Q w) with h0 | h0 <;> simp [h0]
  rw [e1, e2, e3] at h
  have hW := ncard_eq_add_ncard (Q := Q) (splitSub Q U s s' : Set V)
  simp only [SetLike.mem_coe] at hW
  omega

end Count

section Partner

variable {Q : QuadraticForm (ZMod 2) V} {U : Submodule (ZMod 2) V}

theorem exists_hyp_partner (hU : PolarNondegOn Q U) {e : V} (he : e ∈ U) (he0 : e ≠ 0)
    (hQe : Q e = 0) : ∃ f ∈ U, Q f = 0 ∧ polar Q e f = 1 := by
  obtain ⟨h, hhU, heh⟩ := hU.exists_polar_ne_zero he he0
  have heh1 := zmod_two_eq_one_of_ne_zero heh
  refine ⟨h + Q h • e, U.add_mem hhU (U.smul_mem _ he), ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, map_smul_zmod2, hQe, polar_smul_right, polar_comm, heh1,
      mul_zero, add_zero, smul_eq_mul, mul_one, zmod2_add_self]
  · rw [polar_add_right, polar_smul_right, polar_self_zmod2, heh1, smul_zero, add_zero]

theorem eq_bot_of_ncard_eq_one (h : (U : Set V).ncard = 1) : U = ⊥ := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
  have h0 : (0 : V) ∈ (U : Set V) := U.zero_mem
  rw [ha, Set.mem_singleton_iff] at h0
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ (U : Set V) := hx
  rw [ha, Set.mem_singleton_iff, ← h0] at this
  exact (Submodule.mem_bot _).2 this

theorem exists_aniso_plane (hU : PolarNondegOn Q U) (hne : U ≠ ⊥)
    (han : ∀ x ∈ U, Q x = 0 → x = 0) :
    ∃ a ∈ U, ∃ b ∈ U, Q a = 1 ∧ Q b = 1 ∧ polar Q a b = 1 ∧ splitSub Q U a b = ⊥ := by
  obtain ⟨a, haU, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨b, hbU, hab⟩ := hU.exists_polar_ne_zero haU ha0
  have hab1 := zmod_two_eq_one_of_ne_zero hab
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hab (polar_zero_right Q a)
  have hQa : Q a = 1 := zmod_two_eq_one_of_ne_zero fun h => ha0 (han a haU h)
  have hQb : Q b = 1 := zmod_two_eq_one_of_ne_zero fun h => hb0 (han b hbU h)
  refine ⟨a, haU, b, hbU, hQa, hQb, hab1, ?_⟩
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  by_contra hw0
  obtain ⟨hwU, hwa, hwb⟩ := mem_splitSub.1 hw
  have hQw : Q w = 1 := zmod_two_eq_one_of_ne_zero fun h => hw0 (han w hwU h)
  have hsum : a + w = 0 := han _ (U.add_mem haU hwU) (by
    rw [QuadraticMap.map_add Q, hQa, hQw, polar_comm, hwa, add_zero]
    rfl)
  rw [← zmod_two_eq_of_add_eq_zero hsum, hab1] at hwb
  exact one_ne_zero hwb

theorem ncard_of_aniso [Finite V] (hU : PolarNondegOn Q U) (hne : U ≠ ⊥)
    (han : ∀ x ∈ U, Q x = 0 → x = 0) :
    (U : Set V).ncard = 4 ∧ {x | x ∈ U ∧ Q x = 1}.ncard = 3 := by
  obtain ⟨a, ha, b, hb, -, -, hab, hW⟩ := exists_aniso_plane hU hne han
  have h4 := ncard_eq_four_mul_splitSub ha hb hab
  rw [hW, Submodule.bot_coe, Set.ncard_singleton] at h4
  refine ⟨h4, ?_⟩
  have : {x | x ∈ U ∧ Q x = 1} = (U : Set V) \ {0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h1⟩
      refine ⟨hx, ?_⟩
      rintro rfl
      rw [QuadraticMap.map_zero] at h1
      exact zero_ne_one h1
    · rintro ⟨hx, h0⟩
      exact ⟨hx, zmod_two_eq_one_of_ne_zero fun h => h0 (han x hx h)⟩
  rw [this, Set.ncard_sdiff_singleton_of_mem (SetLike.mem_coe.2 U.zero_mem), h4]

theorem ncard_of_hyp_four [Finite V] (hU : PolarNondegOn Q U) (h4 : (U : Set V).ncard = 4)
    {e : V} (he : e ∈ U) (he0 : e ≠ 0) (hQe : Q e = 0) : {x | x ∈ U ∧ Q x = 1}.ncard = 1 := by
  obtain ⟨f, hf, hQf, hef⟩ := exists_hyp_partner hU he he0 hQe
  have hW := ncard_eq_four_mul_splitSub he hf hef
  have hW1 : (splitSub Q U e f : Set V).ncard = 1 := by omega
  have hbot := eq_bot_of_ncard_eq_one hW1
  have hN := ncard_splitSub_hyp he hf hef hQe hQf
  rw [hW1, hbot] at hN
  have h0 : {w | w ∈ (⊥ : Submodule (ZMod 2) V) ∧ Q w = 1} = ∅ := by
    ext w
    simp only [Set.mem_ofPred_eq, Submodule.mem_bot, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro rfl
    rw [QuadraticMap.map_zero]
    exact zero_ne_one
  rw [h0, Set.ncard_empty] at hN
  exact hN

theorem ne_bot_of_ncard_eq [Finite V'] {U' : Submodule (ZMod 2) V'} (hne : U ≠ ⊥)
    (hcard : (U : Set V).ncard = (U' : Set V').ncard) : U' ≠ ⊥ := by
  rintro rfl
  rw [Submodule.bot_coe, Set.ncard_singleton] at hcard
  exact hne (eq_bot_of_ncard_eq_one hcard)

end Partner

section Induction

variable {Q : QuadraticForm (ZMod 2) V} {Q' : QuadraticForm (ZMod 2) V'}

theorem exists_isometryOn_hyp {U : Submodule (ZMod 2) V} {U' : Submodule (ZMod 2) V'}
    {e f : V} {e' f' : V'} (he : e ∈ U) (hf : f ∈ U) (hQe : Q e = 0) (hQf : Q f = 0)
    (hef : polar Q e f = 1) (he' : e' ∈ U') (hf' : f' ∈ U') (hQe' : Q' e' = 0)
    (hQf' : Q' f' = 0) (hef' : polar Q' e' f' = 1) (ψ : V →ₗ[ZMod 2] V')
    (hψU : ∀ x ∈ splitSub Q U e f, ψ x ∈ splitSub Q' U' e' f')
    (hψQ : ∀ x ∈ splitSub Q U e f, Q' (ψ x) = Q x) :
    ∃ ψ' : V →ₗ[ZMod 2] V', (∀ x ∈ U, ψ' x ∈ U') ∧ ∀ x ∈ U, Q' (ψ' x) = Q x := by
  let a : V →ₗ[ZMod 2] ZMod 2 := (polarBilin Q).flip f
  let b : V →ₗ[ZMod 2] ZMod 2 := (polarBilin Q).flip e
  have ha : ∀ x, a x = polar Q x f := fun x => polarBilin_apply_apply Q x f
  have hb : ∀ x, b x = polar Q x e := fun x => polarBilin_apply_apply Q x e
  let ψ' : V →ₗ[ZMod 2] V' :=
    a.smulRight e' + b.smulRight f' + ψ ∘ₗ (LinearMap.id - a.smulRight e - b.smulRight f)
  have happ : ∀ x, ψ' x =
      polar Q x f • e' + polar Q x e • f' + ψ (x - polar Q x f • e - polar Q x e • f) :=
    fun x => by
      simp only [ψ', LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
        LinearMap.sub_apply, LinearMap.id_apply, ha, hb]
  refine ⟨ψ', fun x hx => ?_, fun x hx => ?_⟩ <;> rw [happ] <;>
    have hp := sub_mem_splitSub he hf hef hx
  · exact U'.add_mem (U'.add_mem (U'.smul_mem _ he') (U'.smul_mem _ hf'))
      (splitSub_le (hψU _ hp))
  · have hx' : Q x = polar Q x f * Q e + polar Q x e * Q f + polar Q x f * polar Q x e +
        Q (x - polar Q x f • e - polar Q x e • f) := by
      conv_lhs => rw [eq_smul_add_smul_add_sub x (polar Q x f) (polar Q x e) (s := e) (s' := f)]
      exact map_add_splitSub hef hp _ _
    rw [map_add_splitSub hef' (hψU _ hp), hψQ _ hp, hQe', hQf', hx', hQe, hQf]

theorem exists_isometryOn_aniso {U : Submodule (ZMod 2) V} {U' : Submodule (ZMod 2) V'}
    (hU : PolarNondegOn Q U) (hU' : PolarNondegOn Q' U') (hne : U ≠ ⊥) (hne' : U' ≠ ⊥)
    (han : ∀ x ∈ U, Q x = 0 → x = 0) (han' : ∀ x ∈ U', Q' x = 0 → x = 0) :
    ∃ ψ : V →ₗ[ZMod 2] V', (∀ x ∈ U, ψ x ∈ U') ∧ ∀ x ∈ U, Q' (ψ x) = Q x := by
  obtain ⟨a, ha, b, hb, hQa, hQb, hab, hW⟩ := exists_aniso_plane hU hne han
  obtain ⟨a', ha', b', hb', hQa', hQb', hab', hW'⟩ := exists_aniso_plane hU' hne' han'
  let α : V →ₗ[ZMod 2] ZMod 2 := (polarBilin Q).flip b
  let β : V →ₗ[ZMod 2] ZMod 2 := (polarBilin Q).flip a
  let ψ : V →ₗ[ZMod 2] V' := α.smulRight a' + β.smulRight b'
  have happ : ∀ x, ψ x = polar Q x b • a' + polar Q x a • b' := fun x => by
    simp only [ψ, LinearMap.add_apply, LinearMap.smulRight_apply, α, β, LinearMap.flip_apply,
      polarBilin_apply_apply]
  refine ⟨ψ, fun x _ => ?_, fun x hx => ?_⟩ <;> rw [happ]
  · exact U'.add_mem (U'.smul_mem _ ha') (U'.smul_mem _ hb')
  · have hp := sub_mem_splitSub ha hb hab hx
    have hp0 : x - polar Q x b • a - polar Q x a • b = 0 := (Submodule.mem_bot _).1 (hW ▸ hp)
    have hx' : Q x = polar Q x b * Q a + polar Q x a * Q b + polar Q x b * polar Q x a := by
      conv_lhs => rw [eq_smul_add_smul_add_sub x (polar Q x b) (polar Q x a) (s := a) (s' := b)]
      rw [map_add_splitSub hab hp, hp0, QuadraticMap.map_zero, add_zero]
    have h0' : (0 : V') ∈ splitSub Q' U' a' b' := zero_mem _
    rw [← add_zero (polar Q x b • a' + polar Q x a • b'), map_add_splitSub hab' h0',
      QuadraticMap.map_zero, add_zero, hx', hQa, hQb, hQa', hQb']

theorem exists_isometryOn [Finite V] [Finite V'] (n : ℕ) :
    ∀ (U : Submodule (ZMod 2) V) (U' : Submodule (ZMod 2) V'), (U : Set V).ncard ≤ n →
      PolarNondegOn Q U → PolarNondegOn Q' U' → (U : Set V).ncard = (U' : Set V').ncard →
      {x | x ∈ U ∧ Q x = 1}.ncard = {x | x ∈ U' ∧ Q' x = 1}.ncard →
      ∃ ψ : V →ₗ[ZMod 2] V', (∀ x ∈ U, ψ x ∈ U') ∧ ∀ x ∈ U, Q' (ψ x) = Q x := by
  induction n with
  | zero =>
    intro U U' hn
    have := (Set.ncard_pos (Set.toFinite (U : Set V))).2 ⟨0, U.zero_mem⟩
    omega
  | succ n ih =>
    intro U U' hn hU hU' hcard hN
    by_cases hbot : U = ⊥
    · refine ⟨0, fun x _ => ?_, fun x hx => ?_⟩
      · rw [LinearMap.zero_apply]
        exact U'.zero_mem
      · rw [hbot, Submodule.mem_bot] at hx
        rw [hx, map_zero, QuadraticMap.map_zero, QuadraticMap.map_zero]
    have hbot' := ne_bot_of_ncard_eq hbot hcard
    by_cases hsing : ∃ e ∈ U, e ≠ 0 ∧ Q e = 0 <;>
      by_cases hsing' : ∃ e ∈ U', e ≠ 0 ∧ Q' e = 0
    · obtain ⟨e, he, he0, hQe⟩ := hsing
      obtain ⟨e', he', he0', hQe'⟩ := hsing'
      obtain ⟨f, hf, hQf, hef⟩ := exists_hyp_partner hU he he0 hQe
      obtain ⟨f', hf', hQf', hef'⟩ := exists_hyp_partner hU' he' he0' hQe'
      have h4 := ncard_eq_four_mul_splitSub he hf hef
      have h4' := ncard_eq_four_mul_splitSub he' hf' hef'
      have hN1 := ncard_splitSub_hyp he hf hef hQe hQf
      have hN1' := ncard_splitSub_hyp he' hf' hef' hQe' hQf'
      obtain ⟨ψ, hψU, hψQ⟩ := ih (splitSub Q U e f) (splitSub Q' U' e' f') (by omega)
        (polarNondegOn_splitSub hU he hf hef) (polarNondegOn_splitSub hU' he' hf' hef')
        (by omega) (by omega)
      exact exists_isometryOn_hyp he hf hQe hQf hef he' hf' hQe' hQf' hef' ψ hψU hψQ
    · push Not at hsing'
      obtain ⟨e, he, he0, hQe⟩ := hsing
      obtain ⟨h4', h3'⟩ := ncard_of_aniso hU' hbot' fun x hx h => by_contra fun h0 =>
        hsing' x hx h0 h
      have h1 := ncard_of_hyp_four hU (hcard.trans h4') he he0 hQe
      omega
    · push Not at hsing
      obtain ⟨e', he', he0', hQe'⟩ := hsing'
      obtain ⟨h4, h3⟩ := ncard_of_aniso hU hbot fun x hx h => by_contra fun h0 =>
        hsing x hx h0 h
      have h1 := ncard_of_hyp_four hU' (hcard.symm.trans h4) he' he0' hQe'
      omega
    · push Not at hsing hsing'
      exact exists_isometryOn_aniso hU hU' hbot hbot'
        (fun x hx h => by_contra fun h0 => hsing x hx h0 h)
        (fun x hx h => by_contra fun h0 => hsing' x hx h0 h)

end Induction

end Arf

open Arf

variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']

theorem exists_linearEquiv_of_ncard_eq [Finite V] [Finite V'] (Q : QuadraticForm (ZMod 2) V)
    (Q' : QuadraticForm (ZMod 2) V') (hQ : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hQ' : ∀ x, (∀ y, polar Q' x y = 0) → x = 0) (hcard : Nat.card V = Nat.card V')
    (hN : {v | Q v = 1}.ncard = {v | Q' v = 1}.ncard) :
    ∃ L : V ≃ₗ[ZMod 2] V', ∀ v, Q' (L v) = Q v := by
  obtain ⟨ψ, -, hψ⟩ := exists_isometryOn (Q := Q) (Q' := Q') (Nat.card V) ⊤ ⊤
    (by rw [Submodule.top_coe, Set.ncard_univ])
    (fun x _ hx => hQ x fun y => hx y trivial) (fun x _ hx => hQ' x fun y => hx y trivial)
    (by rw [Submodule.top_coe, Submodule.top_coe, Set.ncard_univ, Set.ncard_univ, hcard])
    (by simpa only [Submodule.mem_top, true_and] using hN)
  have hψ' : ∀ x, Q' (ψ x) = Q x := fun x => hψ x trivial
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    refine hQ x fun y => ?_
    rw [polar, ← hψ' (x + y), ← hψ' x, ← hψ' y, map_add, hx, zero_add, QuadraticMap.map_zero,
      sub_zero, sub_self]
  exact ⟨LinearEquiv.ofBijective ψ (hinj.bijective_of_nat_card_le hcard.ge), fun v => hψ' v⟩

theorem exists_linearEquiv_fin_of_ncard_eq {m : ℕ}
    (Q Q' : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hQ : ∀ x, (∀ y, polar Q x y = 0) → x = 0) (hQ' : ∀ x, (∀ y, polar Q' x y = 0) → x = 0)
    (hN : {v | Q v = 1}.ncard = {v | Q' v = 1}.ncard) :
    ∃ L : (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2), ∀ v, Q' (L v) = Q v :=
  exists_linearEquiv_of_ncard_eq Q Q' hQ hQ' rfl hN

end CFSG.Fischer.Classification
