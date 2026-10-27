module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF3
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF4Iso

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect map_perfectCore)

section General

variable {E C X : Type*} [Group E] [Group C] [Group X]

theorem forall_normal_isPGroup_eq_bot_of_mulEquiv_symm {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {p : ℕ} (h : ∀ N : Subgroup B, N.Normal → IsPGroup p N → N = ⊥) :
    ∀ N : Subgroup A, N.Normal → IsPGroup p N → N = ⊥ := by
  intro N hN hp
  have h1 := h (N.map e.toMonoidHom) (hN.map _ e.surjective) (hp.map _)
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ N.map e.toMonoidHom := mem_map_of_mem e.toMonoidHom hx
  rw [h1, mem_bot] at hx'
  rw [mem_bot]
  simpa using hx'

theorem center_le_ker_of_surjective_of_center_eq_bot {f : E →* X} (hf : Function.Surjective f)
    (hX : center X = ⊥) : center E ≤ f.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hfz : f z ∈ center X := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz x]
  rw [hX, mem_bot] at hfz
  exact hfz

theorem isPGroup_map_comap {p : ℕ} {π : E →* C} {κ : E →* X} (hπκ : π.ker ≤ κ.ker)
    {R : Subgroup C} (hR : IsPGroup p R) : IsPGroup p ((R.comap π).map κ) := by
  rintro ⟨y, x, hx, rfl⟩
  obtain ⟨m, hm⟩ := hR ⟨π x, hx⟩
  refine ⟨m, Subtype.ext ?_⟩
  have h1 : π (x ^ p ^ m) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hm
  have h2 : κ (x ^ p ^ m) = 1 := hπκ h1
  rw [map_pow] at h2
  simpa using h2

theorem map_le_normalizer_map_comap {π : E →* C} {κ : E →* X} {Γ : Subgroup E}
    {R : Subgroup C} (hΓ : Γ.map π ≤ normalizer (R : Set C)) :
    Γ.map κ ≤ normalizer (((R.comap π).map κ : Subgroup X) : Set X) := by
  have h : Γ ≤ normalizer ((R.comap π : Subgroup E) : Set E) := by
    intro γ hγ
    rw [mem_normalizer_iff]
    intro x
    have hn := mem_normalizer_iff.1 (hΓ (mem_map_of_mem π hγ)) (π x)
    simp only [mem_comap, map_mul, map_inv]
    exact hn
  exact (map_mono h).trans (le_normalizer_map κ)

theorem map_comap_ne_bot {p : ℕ} [Fact p.Prime] {π : E →* C} {κ : E →* X}
    (hκ : κ.ker ≤ center E) {m : ℕ} (hm : Nat.Coprime p m) (hz : ∀ z ∈ center E, z ^ m = 1)
    {R : Subgroup C} (hRπ : R ≤ π.range) (hR : IsPGroup p R) (hne : R ≠ ⊥) :
    (R.comap π).map κ ≠ ⊥ := by
  intro hbot
  apply hne
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨x, rfl⟩ := hRπ hr
  have hx : κ x = 1 := by
    have : κ x ∈ (R.comap π).map κ := mem_map_of_mem κ (show x ∈ R.comap π from hr)
    rw [hbot, mem_bot] at this
    exact this
  have hxm : x ^ m = 1 := hz x (hκ hx)
  obtain ⟨k, hk⟩ := hR ⟨π x, hr⟩
  have h1 : (π x) ^ p ^ k = 1 := congrArg Subtype.val hk
  have h2 : (π x) ^ m = 1 := by rw [← map_pow, hxm, map_one]
  rw [mem_bot]
  have hc : Nat.Coprime (orderOf (π x)) (orderOf (π x)) :=
    ((Nat.Coprime.pow_left k hm).coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.coprime_self] at hc
  exact orderOf_eq_one_iff.1 hc

theorem card_mul_card_le_card_sup_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (h : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card (A ⊔ B : Subgroup G) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x => ⟨(x.1 : G) * x.2, mul_mem (mem_sup_left x.1.2) (mem_sup_right x.2.2)⟩) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have e : (a : G) * b = a' * b' := congrArg Subtype.val hab
  have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B := by
    refine mem_inf.2 ⟨mul_mem (inv_mem a'.2) a.2, ?_⟩
    have e' : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    rw [e']
    exact mul_mem b'.2 (inv_mem b.2)
  rw [h, mem_bot, inv_mul_eq_one] at hmem
  have ha : a = a' := Subtype.ext hmem.symm
  subst ha
  have hb : (b : G) = b' := mul_left_cancel e
  exact Prod.ext rfl (Subtype.ext hb)

theorem card_le_card_of_isPGroup_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {U H : Subgroup G} (hU : ¬ p ∣ U.index) (hH : IsPGroup p H) :
    Nat.card H ≤ Nat.card U := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hdvd : Nat.card H ∣ Nat.card U * U.index := by
    rw [Subgroup.card_mul_index]
    exact Subgroup.card_subgroup_dvd_card H
  have hcop : Nat.Coprime (Nat.card H) U.index := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hU)
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)

end General

section Parabolic

theorem exists_conj_mem_parabolicSubgroup_of_normalizes {τ : Tag} {K : Type} [Field K] [Finite K]
    {r : ℕ} [Fact r.Prime] [CharP K r] {S : Subgroup (adjointGroup τ K)} (hS : S ≠ ⊥)
    (hSr : IsPGroup r S) :
    ∃ (J : Set (Fin τ.rank)) (g : adjointGroup τ K), J ≠ Set.univ ∧
      ∀ x ∈ normalizer (S : Set (adjointGroup τ K)),
        ((g⁻¹ * x * g : adjointGroup τ K) : ModGL τ K) ∈ parabolicSubgroup τ K J := by
  classical
  have hfin : Finite (ModGL τ K) := finite_modGL
  obtain ⟨S₂, P, hPtop, hNS, -, -, hS₂⟩ :=
    CFSG.LieType.Chevalley.holds_adjointGroup_tag τ K r S hS hSr
  have hUsyl := isPGroup_and_not_dvd_index r (posUnipotent_le_adjointGroup (τ := τ) (K := K))
    (card_posUnipotent (τ := τ) (K := K))
  set SU : Sylow r (adjointGroup τ K) := hUsyl.1.toSylow hUsyl.2 with hSU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup τ K) SU S₂
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBN : borelGroup τ K ≤ normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    (normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1
  have hmem : ∀ z : adjointGroup τ K, z ∈ (S₂ : Subgroup (adjointGroup τ K)) ↔
      g⁻¹ * z * g ∈ (SU : Subgroup (adjointGroup τ K)) := by
    intro z
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_symm_apply]
  have hSUmem : ∀ z : adjointGroup τ K, z ∈ (SU : Subgroup (adjointGroup τ K)) ↔
      (z : ModGL τ K) ∈ posUnipotent τ K := fun z => Iff.rfl
  have hBP : ∀ b : adjointGroup τ K, (b : ModGL τ K) ∈ borelGroup τ K → g * b * g⁻¹ ∈ P := by
    intro b hb
    apply hS₂
    rw [mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    have e : g⁻¹ * (g * b * g⁻¹ * y * (g * b * g⁻¹)⁻¹) * g = b * (g⁻¹ * y * g) * b⁻¹ := by
      group
    rw [e, hSUmem, hSUmem]
    have := mem_normalizer_iff.1 (hBN hb) ((g⁻¹ * y * g : adjointGroup τ K) : ModGL τ K)
    simpa using this
  set P' : Subgroup (adjointGroup τ K) := P.comap (MulAut.conj g).toMonoidHom with hP'
  have hP'mem : ∀ y, y ∈ P' ↔ g * y * g⁻¹ ∈ P := fun y => by
    simp [hP', MulAut.conj_apply]
  have hP'top : P' ≠ ⊤ := by
    intro h
    apply hPtop
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : g⁻¹ * y * g ∈ P' := h ▸ mem_top _
    rw [hP'mem] at h1
    simpa [mul_assoc] using h1
  set A : Subgroup (ModGL τ K) := P'.map (adjointGroup τ K).subtype with hA
  have hBA : borelGroup τ K ≤ A := fun b hb =>
    ⟨⟨b, borelGroup_le_adjointGroup' hb⟩, (hP'mem _).2 (hBP _ hb), rfl⟩
  have hAC : A ≤ adjointGroup τ K := map_subtype_le _
  have hAJ := (borel_overgroup_classification τ K).1 A hBA hAC
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ A} with hJ
  have hJne : J ≠ Set.univ := by
    intro hJu
    apply hP'top
    have hAeq : A = adjointGroup τ K := by
      rw [hAJ, hJu]
      refine le_antisymm (parabolicSubgroup_le_adjointGroup τ K _) ?_
      rw [(borel_weyl_generation τ K).1]
      unfold parabolicSubgroup
      refine sup_le_sup_left (Subgroup.closure_mono ?_) _
      rintro _ ⟨i, rfl⟩
      exact ⟨i, Set.mem_univ i, rfl⟩
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : (y : ModGL τ K) ∈ A := by
      rw [hAeq]
      exact y.2
    obtain ⟨y', hy', hyy'⟩ := h1
    have h2 : y' = y := Subtype.ext hyy'
    rwa [← h2]
  refine ⟨J, g, hJne, fun x hx => ?_⟩
  have hx'P' : g⁻¹ * x * g ∈ P' := by
    rw [hP'mem]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hNS hx
  rw [← hAJ]
  exact ⟨_, hx'P', rfl⟩

end Parabolic

section Centre

variable {K : Type} [Field K]

theorem endo_pow_e6 (g : e6Data_valid.minGroup K) (n : ℕ) :
    e6Data_valid.endo K (g ^ n) = e6Data_valid.endo K g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MinData.Valid.endo_one]
  | succ n ih => rw [pow_succ, MinData.Valid.endo_mul, ih, pow_succ]

theorem diagOp_pow_e6 {d : ℕ} (f : Fin d → K) (n : ℕ) : diagOp f ^ n = diagOp (f ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, diagOp_one]
  | succ n ih => rw [pow_succ, ih, diagOp_mul, pow_succ]

theorem pow_card_sub_one_eq_one_of_mem_iSup_torus_e6 [Finite K] {z : e6Data_valid.minGroup K}
    (hz : z ∈ ⨆ i, e6Data_valid.torus K i) : z ^ (Nat.card K - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have key : ∃ f : Fin e6Data.d → K, (∀ a, f a ^ (Nat.card K - 1) = 1) ∧
      e6Data_valid.endo K z = diagOp f := by
    refine Subgroup.iSup_induction _ (C := fun x => ∃ f : Fin e6Data.d → K,
      (∀ a, f a ^ (Nat.card K - 1) = 1) ∧ e6Data_valid.endo K x = diagOp f) hz
      (fun i y hy => ?_) ⟨1, fun a => one_pow _, by rw [MinData.Valid.endo_one, diagOp_one]⟩ ?_
    · obtain ⟨t, rfl⟩ := (e6Data_valid.mem_torus K).1 hy
      refine ⟨fun a => ((t ^ e6Data.wt a i : Kˣ) : K), fun a => ?_, ?_⟩
      · rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero _)
      · rw [MinData.Valid.endo_hm]
        rfl
    · rintro x y ⟨f, hf, hx⟩ ⟨g, hg, hy⟩
      exact ⟨f * g, fun a => by rw [Pi.mul_apply, mul_pow, hf, hg, one_mul],
        by rw [MinData.Valid.endo_mul, hx, hy, diagOp_mul]⟩
  obtain ⟨f, hf, hzf⟩ := key
  apply e6Data_valid.endo_injective K
  rw [endo_pow_e6, hzf, diagOp_pow_e6, MinData.Valid.endo_one]
  have hf1 : f ^ (Nat.card K - 1) = 1 := funext fun a => by rw [Pi.pow_apply, hf a, Pi.one_apply]
  rw [hf1, diagOp_one]

theorem pow_card_sub_one_eq_one_of_mem_center_e6 [Finite K] {z : e6Data_valid.minGroup K}
    (hz : z ∈ center (e6Data_valid.minGroup K)) : z ^ (Nat.card K - 1) = 1 := by
  have hct := e6Datum_isCTGroupDatum K
  have h1 := (CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hct
    (e6Datum_steinbergExtras K) (e6Datum_bruhatExtras K)) ▸ hz
  exact pow_card_sub_one_eq_one_of_mem_iSup_torus_e6
    (CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hct (e6Datum_bruhatExtras K) h1)

end Centre

theorem coprime_two_card_sub_one {K : Type} [Field K] [Finite K] [CharP K 2] :
    Nat.Coprime 2 (Nat.card K - 1) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn, Nat.coprime_two_left]
  have h2 : Even (2 ^ (n : ℕ)) := (Nat.even_pow' n.ne_zero).2 even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one

theorem ncard_posRoots_e6 :
    {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α}.ncard = 36 := by
  have h : {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α} =
      ↑((rootFinset TwistTag.E6.tag).filter fun α => 0 < height α) := by
    ext α
    simp [mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem sixteen_le_card_filter_e6 :
    ∀ i : Fin TwistTag.E6.tag.rank,
      16 ≤ ((rootFinset TwistTag.E6.tag).filter fun α => 0 < height α ∧ α i ≠ 0).card := by
  decide +kernel

theorem sixteen_le_ncard_parabolicRadicalRoots_e6
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : J ≠ Set.univ) :
    16 ≤ (parabolicRadicalRoots TwistTag.E6.tag J).ncard := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have hsub : (↑((rootFinset TwistTag.E6.tag).filter fun α => 0 < height α ∧ α i ≠ 0) :
      Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ parabolicRadicalRoots TwistTag.E6.tag J := by
    intro α hα
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_rootFinset] at hα
    exact mem_parabolicRadicalRoots_iff.2 ⟨hα.1, hα.2.1, i, hi, hα.2.2⟩
  have hfin : (parabolicRadicalRoots TwistTag.E6.tag J).Finite :=
    (rootFinset TwistTag.E6.tag).finite_toSet.subset fun α hα => mem_rootFinset.2 hα.1.1
  calc 16 ≤ _ := sixteen_le_card_filter_e6 i
    _ = _ := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

section Fd

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem forall_normal_isPGroup_eq_bot_adjointGroup_f4 :
    ∀ N : Subgroup (adjointGroup .F4 K), N.Normal → IsPGroup 2 N → N = ⊥ :=
  forall_normal_isPGroup_eq_bot_of_mulEquiv_symm (uF4Equiv K).symm forall_normal_isPGroup_eq_bot_uF4

theorem card_posUnipotent_subgroupOf_f4 :
    Nat.card ((posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K)) = Nat.card K ^ 24 := by
  rw [card_subgroupOf_of_le posUnipotent_le_adjointGroup, card_posUnipotent, ncard_f4_posRoots]

theorem false_of_mulEquiv_f4_of_le_parabolicSubgroup {J : Set (Fin TwistTag.E6.tag.rank)}
    (hJ : J ≠ Set.univ) {H : Subgroup (adjointGroup TwistTag.E6.tag K)}
    (e : adjointGroup .F4 K ≃* H)
    (hHP : ∀ x ∈ H, (x : ModGL TwistTag.E6.tag K) ∈ parabolicSubgroup TwistTag.E6.tag K J) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Q : Subgroup (adjointGroup TwistTag.E6.tag K) := (parabolicRadical TwistTag.E6.tag K J).subgroupOf (adjointGroup TwistTag.E6.tag K) with hQ
  have hQC : parabolicRadical TwistTag.E6.tag K J ≤ adjointGroup TwistTag.E6.tag K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  obtain ⟨hQcard', hQp', -⟩ :=
    (parabolic_root_radical_Levi_factors TwistTag.E6.tag K J).2.2.2.2.2.2.2.2.2.2.2.2 2
  have hQp : IsPGroup 2 Q := F4Pilot.isPGroup_subgroupOf_of_le hQC hQp'
  have hQcard : Nat.card Q = Nat.card K ^ (parabolicRadicalRoots TwistTag.E6.tag J).ncard := by
    rw [hQ, card_subgroupOf_of_le hQC, hQcard']
  have hHN : H ≤ normalizer (Q : Set (adjointGroup TwistTag.E6.tag K)) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    have hn := mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical J (hHP x hx)) (y : ModGL _ K)
    simp only [hQ, mem_subgroupOf, coe_mul, coe_inv]
    exact hn
  have hO2 : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N = ⊥ :=
    forall_normal_isPGroup_eq_bot_of_mulEquiv_symm e.symm forall_normal_isPGroup_eq_bot_adjointGroup_f4
  have hHQ : H ⊓ Q = ⊥ := by
    have hN : (Q.subgroupOf H).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simpa using (mem_normalizer_iff.1 (hHN g.2) n).1 hn⟩
    have hbot := hO2 _ hN hQp.comap_subtype
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, (mem_inf.1 hx).1⟩ : H) ∈ Q.subgroupOf H := mem_subgroupOf.2 (mem_inf.1 hx).2
    rw [hbot, mem_bot] at hx'
    exact mem_bot.2 (congrArg Subtype.val hx')
  set S : Subgroup (adjointGroup TwistTag.E6.tag K) := ((posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K)).map
    (H.subtype.comp e.toMonoidHom) with hS
  have hinj : Function.Injective (H.subtype.comp e.toMonoidHom) :=
    H.subtype_injective.comp e.injective
  have hScard : Nat.card S = Nat.card K ^ 24 := by
    rw [hS, card_map_of_injective hinj, card_posUnipotent_subgroupOf_f4]
  have hSH : S ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  have hSp : IsPGroup 2 S := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact IsPGroup.of_card (n := (n : ℕ) * 24)
      (by rw [hScard, Nat.card_eq_fintype_card, hn, ← pow_mul])
  have hSQ : S ⊓ Q = ⊥ := eq_bot_iff.2 ((inf_le_inf_right _ hSH).trans hHQ.le)
  have hSQp : IsPGroup 2 (S ⊔ Q : Subgroup (adjointGroup TwistTag.E6.tag K)) := hSp.to_sup_of_normal_right' hQp (hSH.trans hHN)
  obtain ⟨-, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := TwistTag.E6.tag) (K := K))
    (card_posUnipotent (τ := TwistTag.E6.tag) (K := K))
  have hUcard : Nat.card ((posUnipotent TwistTag.E6.tag K).subgroupOf (adjointGroup TwistTag.E6.tag K)) = Nat.card K ^ 36 := by
    rw [card_subgroupOf_of_le posUnipotent_le_adjointGroup, card_posUnipotent, ncard_posRoots_e6]
  have hle := card_le_card_of_isPGroup_of_not_dvd_index hUi hSQp
  have hge := card_mul_card_le_card_sup_of_inf_eq_bot hSQ
  rw [hScard, hQcard, hUcard] at *
  have h16 := sixteen_le_ncard_parabolicRadicalRoots_e6 hJ
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h40 : Nat.card K ^ 40 ≤ Nat.card K ^ 36 :=
    calc Nat.card K ^ 40 = Nat.card K ^ 24 * Nat.card K ^ 16 := by rw [← pow_add]
      _ ≤ Nat.card K ^ 24 * Nat.card K ^ (parabolicRadicalRoots TwistTag.E6.tag J).ncard :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h16)
      _ ≤ _ := hge.trans hle
  have := (Nat.pow_le_pow_iff_right hq).1 h40
  omega

theorem eq_bot_of_le_normalizer_of_mulEquiv_f4 {H : Subgroup (adjointGroup TwistTag.E6.tag K)}
    (e : adjointGroup .F4 K ≃* H) {R : Subgroup (adjointGroup TwistTag.E6.tag K)}
    (hR : IsPGroup 2 R) (hHR : H ≤ normalizer (R : Set (adjointGroup TwistTag.E6.tag K))) :
    R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨J, g, hJ, hP⟩ := exists_conj_mem_parabolicSubgroup_of_normalizes hne hR
  refine false_of_mulEquiv_f4_of_le_parabolicSubgroup hJ
    (H := H.map (MulAut.conj g⁻¹).toMonoidHom) (e.trans ((MulAut.conj g⁻¹).subgroupMap H)) ?_
  rintro _ ⟨h, hh, rfl⟩
  have e1 : (MulAut.conj g⁻¹).toMonoidHom h = g⁻¹ * h * g := by
    simp
  rw [e1]
  exact hP h (hHR hh)

noncomputable abbrev e6F4Image (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (adjointGroup TwistTag.E6.tag K) :=
  (uF4SC K).map (e6IsogenyT K)

noncomputable def uF4SCEquivImage : uF4SC K ≃* e6F4Image K :=
  MulEquiv.ofBijective (((e6IsogenyT K).comp (uF4SC K).subtype).codRestrict (e6F4Image K)
      fun g => mem_map_of_mem (e6IsogenyT K) g.2)
    ⟨fun g h e => Subtype.ext (e6IsogenyT_injOn_uF4SC g.2 h.2 (congrArg Subtype.val e)), by
      rintro ⟨x, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩⟩

noncomputable def f4EquivE6F4Image : adjointGroup .F4 K ≃* e6F4Image K :=
  (uF4ASEquiv K).symm.trans ((uF4SCEquivAS K).symm.trans uF4SCEquivImage)

theorem eq_bot_of_le_e6Levi_of_uF4AS_le_normalizer {R : Subgroup (adjointGroup .E7 K)}
    (hRN : R ≤ e6Levi K) (hR : IsPGroup 2 R)
    (hF : uF4AS K ≤ normalizer (R : Set (adjointGroup .E7 K))) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hπκ : (e6ToE7 K).ker ≤ (e6IsogenyT K).ker :=
    (ker_e6ToE7_le_center (K := K)).trans
      (center_le_ker_of_surjective_of_center_eq_bot (f := e6IsogenyT K) e6IsogenyT_surjective
        center_adjointGroup_eq_bot)
  have hR' := isPGroup_map_comap (κ := e6IsogenyT K) hπκ hR
  have hne' : (R.comap (e6ToE7 K)).map (e6IsogenyT K) ≠ ⊥ :=
    map_comap_ne_bot (ker_e6IsogenyT_le_center K) coprime_two_card_sub_one
      (fun z hz => pow_card_sub_one_eq_one_of_mem_center_e6 hz)
      (hRN.trans (range_e6ToE7 (K := K)).ge) hR hne
  have hN : e6F4Image K ≤ normalizer (((R.comap (e6ToE7 K)).map (e6IsogenyT K) :
      Subgroup (adjointGroup TwistTag.E6.tag K)) : Set (adjointGroup TwistTag.E6.tag K)) :=
    map_le_normalizer_map_comap (by rw [map_e6ToE7_uF4SC]; exact hF)
  exact hne' (eq_bot_of_le_normalizer_of_mulEquiv_f4 f4EquivE6F4Image hR' hN)

theorem parabolicLevi_le_rootSpan_parabolicRoots_sup_torusGroup {τ : Tag}
    (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J ≤ rootSpan τ K (parabolicRoots τ J) ⊔ torusGroup τ K := by
  refine sup_le le_sup_right ((closure_le _).2 ?_)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, ← pinnedX_single]
    refine mem_sup_left (pinnedX_mem_rootSpan (S := parabolicRoots τ J)
      ⟨isRoot_single τ j, fun i hi => ?_⟩ c)
    exact Pi.single_eq_of_ne (by rintro rfl; exact hi hj) _
  · rw [SetLike.mem_coe, ← pinnedX_neg_single]
    refine mem_sup_left (pinnedX_mem_rootSpan (S := parabolicRoots τ J)
      ⟨isRoot_neg_single τ j, fun i hi => ?_⟩ c)
    rw [Pi.neg_apply, Pi.single_eq_of_ne (by rintro rfl; exact hi hj), neg_zero]

theorem perfectCore_torusGroup_eq_bot_of_tag {τ : Tag} : perfectCore (torusGroup τ K) = ⊥ := by
  refine eq_bot_iff.2 ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans (le_of_eq ?_))
  rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero,
    commutator_eq_bot_iff_le_centralizer]
  intro h hh
  rw [mem_centralizer_iff]
  intro k hk
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hk)
    (torusGroup_le_diagonalGroup hh)

theorem parabolicRoots_uNodes : parabolicRoots .E7 uNodes = e6LeviRoots := by
  ext α
  simp only [parabolicRoots, e6LeviRoots, uNodes, Set.mem_ofPred_eq, not_not]
  constructor
  · rintro ⟨hα, h⟩
    exact ⟨hα, h _ rfl⟩
  · rintro ⟨hα, h⟩
    refine ⟨hα, fun i hi => ?_⟩
    rw [hi]
    exact h

theorem perfectCore_parabolicLevi_subgroupOf_le_e6Levi :
    perfectCore ((parabolicLevi .E7 K uNodes).subgroupOf (adjointGroup .E7 K)) ≤ e6Levi K := by
  have : Finite (ModGL .E7 K) := finite_modGL
  have hM : parabolicLevi .E7 K uNodes ≤ adjointGroup .E7 K :=
    parabolicLevi_le_adjointGroup .E7 K uNodes
  have key : perfectCore (parabolicLevi .E7 K uNodes) ≤ rootSpan .E7 K e6LeviRoots := by
    calc perfectCore (parabolicLevi .E7 K uNodes)
        ≤ perfectCore (rootSpan .E7 K (parabolicRoots .E7 uNodes) ⊔ torusGroup .E7 K) :=
          perfectCore_mono (parabolicLevi_le_rootSpan_parabolicRoots_sup_torusGroup uNodes)
      _ ≤ rootSpan .E7 K (parabolicRoots .E7 uNodes) ⊔ perfectCore (torusGroup .E7 K) :=
          E6Pilot.perfectCore_sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
      _ = rootSpan .E7 K e6LeviRoots := by
          rw [perfectCore_torusGroup_eq_bot_of_tag, sup_bot_eq, parabolicRoots_uNodes]
  intro x hx
  rw [e6Levi, mem_subgroupOf]
  refine key ?_
  have hmap := map_perfectCore (adjointGroup .E7 K).subtype
    ((parabolicLevi .E7 K uNodes).subgroupOf (adjointGroup .E7 K))
  rw [subgroupOf_map_subtype, inf_of_le_left hM] at hmap
  rw [← hmap]
  exact mem_map_of_mem _ hx

variable (K) in
@[expose] noncomputable def e6LeviU : Subgroup (adjointGroup .E7 K) :=
  (e6Levi K).map (MulAut.conj (e7RepConj K 3)).toMonoidHom

theorem uLevi_le_e6LeviU : uLevi K ≤ e6LeviU K := by
  have : Finite (ModGL .E7 K) := finite_modGL
  refine (perfectCore_mono inf_le_left).trans ?_
  rw [leviU, ← map_perfectCore]
  exact map_mono perfectCore_parabolicLevi_subgroupOf_le_e6Levi

theorem eq_bot_of_le_e6LeviU_of_uF4_le_normalizer {R : Subgroup (adjointGroup .E7 K)}
    (hRN : R ≤ e6LeviU K) (hR : IsPGroup 2 R)
    (hF : uF4 K ≤ normalizer (R : Set (adjointGroup .E7 K))) : R = ⊥ := by
  set c := MulAut.conj (e7RepConj K 3) with hc
  have h0 : R.map c.symm.toMonoidHom = ⊥ := by
    refine eq_bot_of_le_e6Levi_of_uF4AS_le_normalizer ?_ (hR.map _) ?_
    · rintro _ ⟨r, hr, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hRN hr
      have e : c.symm.toMonoidHom ((MulAut.conj (e7RepConj K 3)).toMonoidHom x) = x :=
        c.symm_apply_apply x
      rw [e]
      exact hx
    · intro f hf
      have hf' : c f ∈ uF4 K := ⟨f, hf, rfl⟩
      have hn := hF hf'
      rw [← map_equiv_normalizer_eq _ c.symm]
      refine ⟨c f, hn, ?_⟩
      simp
  rw [eq_bot_iff]
  intro r hr
  have : c.symm r ∈ R.map c.symm.toMonoidHom := mem_map_of_mem _ hr
  rw [h0, mem_bot] at this
  rw [mem_bot]
  simpa using this

theorem forall_normal_isPGroup_eq_bot_uLevi :
    ∀ N : Subgroup (uLevi K), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hp
  have h0 : N.map (uLevi K).subtype = ⊥ := by
    refine eq_bot_of_le_e6LeviU_of_uF4_le_normalizer
      ((map_subtype_le N).trans uLevi_le_e6LeviU) (hp.map _) ?_
    intro f hf
    have hfL : f ∈ uLevi K := uF4_le_uLevi hf
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨f, hfL⟩ * n * ⟨f, hfL⟩⁻¹, hN.conj_mem n hn _, ?_⟩
      simp
    · rintro ⟨n, hn, hny⟩
      refine ⟨⟨f, hfL⟩⁻¹ * n * ⟨f, hfL⟩, ?_, ?_⟩
      · simpa using hN.conj_mem n hn ⟨f, hfL⟩⁻¹
      · have hny' : (n : adjointGroup .E7 K) = f * y * f⁻¹ := hny
        show ((⟨f, hfL⟩⁻¹ * n * ⟨f, hfL⟩ : uLevi K) : adjointGroup .E7 K) = y
        rw [coe_mul, coe_mul, coe_inv, hny']
        group
  rw [eq_bot_iff]
  intro x hx
  have : (x : adjointGroup .E7 K) ∈ N.map (uLevi K).subtype := mem_map_of_mem _ hx
  rw [h0, mem_bot] at this
  exact mem_bot.2 (Subtype.ext this)

end Fd

end CFSG.SeitzReduction.E7Pilot
