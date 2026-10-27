module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SylowGlue
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitIso
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitOffender

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour
  Matrix
open scoped Pointwise

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem endo_pow {τ : Tag} {D : MinData τ} (hV : D.Valid) (g : hV.minGroup K) (n : ℕ) :
    hV.endo K (g ^ n) = (hV.endo K g) ^ n := by
  induction n with
  | zero => exact hV.endo_one K
  | succ n ih => rw [pow_succ, hV.endo_mul, ih, pow_succ]

theorem exists_pow_two_eq_one_of_isUni {d : ℕ} (dg : Fin d → ℤ) {f : Module.End K (Fin d →₀ K)}
    (hf : IsUni dg f) : ∃ s : ℕ, f ^ (2 ^ s) = 1 := by
  set N : Module.End K (Fin d →₀ K) := f - 1 with hN
  have hNt : ∀ (t : ℕ) (m : ℤ) (w : Fin d →₀ K), w ∈ filt dg m → (N ^ t) w ∈ filt dg (m + t) := by
    intro t
    induction t with
    | zero => intro m w hw; simpa using hw
    | succ t ih =>
      intro m w hw
      have h1 : N w ∈ filt dg (m + 1) := by
        have := hf m w hw
        rwa [hN, LinearMap.sub_apply, Module.End.one_apply]
      have := ih (m + 1) _ h1
      rw [pow_succ, Module.End.mul_apply]
      simpa [add_assoc, add_comm 1 (t : ℤ)] using this
  set S : ℕ := ∑ a, (dg a).natAbs with hS
  have hle : ∀ a, (dg a).natAbs ≤ S := fun a =>
    Finset.single_le_sum (f := fun a => (dg a).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hNT : N ^ (2 * S + 1) = 0 := by
    refine ext_single fun a => ?_
    have h0 := hNt (2 * S + 1) (dg a) (Finsupp.single a 1) (single_mem_filt le_rfl)
    refine Finsupp.ext fun b => ?_
    have hb := apply_eq_zero_of_mem_filt h0 (b := b) (by
      have h1 := hle a
      have h2 := hle b
      push_cast
      omega)
    rw [hb]; rfl
  obtain ⟨s, hs⟩ : ∃ s : ℕ, 2 * S + 1 ≤ 2 ^ s := ⟨2 * S + 1, (Nat.lt_two_pow_self).le⟩
  have hNs : N ^ (2 ^ s) = 0 := by
    have : N ^ (2 ^ s) = N ^ (2 * S + 1) * N ^ (2 ^ s - (2 * S + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [this, hNT, zero_mul]
  have h2 : (2 : Module.End K (Fin d →₀ K)) = 0 := by
    rw [← one_add_one_eq_two]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply, ← two_smul K v,
      CharTwo.two_eq_zero, zero_smul]
  have hsq : ∀ M : Module.End K (Fin d →₀ K), (1 + M) ^ 2 = 1 + M ^ 2 := fun M => by
    have : (1 + M) ^ 2 = 1 + 2 * M + M ^ 2 := by noncomm_ring
    rw [this, h2, zero_mul, add_zero]
  have key : ∀ s : ℕ, (1 + N) ^ (2 ^ s) = 1 + N ^ (2 ^ s) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ, pow_mul, ih, hsq, ← pow_mul, ← pow_succ]
  refine ⟨s, ?_⟩
  have hf1 : f = 1 + N := by rw [hN]; abel
  rw [hf1, key, hNs, add_zero]

@[expose] def posU6 : Subgroup (e6Data_valid.minGroup K) :=
  ⨆ γ ∈ {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ 0 < (1 : ℤ) * ht γ},
    e6Data_valid.rootGroup K γ

theorem isPGroup_posU6 : IsPGroup 2 (posU6 K) := by
  intro g
  have hg : (g : e6Data_valid.minGroup K) ∈ ⨆ γ ∈ {γ : Fin Tag.E6.rank → ℤ |
      IsRoot Tag.E6 γ ∧ 0 < (1 : ℤ) * ht γ}, e6Data_valid.rootGroup K γ := g.2
  obtain ⟨s, hs⟩ := exists_pow_two_eq_one_of_isUni K _ (e6Data_valid.isUni_of_mem K (η := 1) hg)
  refine ⟨s, Subtype.ext (e6Data_valid.endo_injective K ?_)⟩
  change e6Data_valid.endo K ((g : e6Data_valid.minGroup K) ^ 2 ^ s) = e6Data_valid.endo K 1
  rw [endo_pow, hs, e6Data_valid.endo_one K]

theorem rootGroup_le_posU6 {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hpos : 0 < height γ) : e6Data_valid.rootGroup K γ ≤ posU6 K :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin Tag.E6.rank → ℤ |
    IsRoot Tag.E6 γ ∧ 0 < (1 : ℤ) * ht γ}) => e6Data_valid.rootGroup K γ) γ
    ⟨hγ, by rw [one_mul]; exact hpos⟩ le_rfl

theorem Uad_le_map_posU6 : Uad K Tag.E6 ≤ (posU6 K).map (e6Isogeny K) := by
  intro g hg
  have hg' : g.1 ∈ CFSG.Blueprint.Chevalley.posUnipotent Tag.E6 K := hg
  suffices h : ∀ x ∈ CFSG.Blueprint.Chevalley.posUnipotent Tag.E6 K, ∃ y : adjointGroup Tag.E6 K, y.1 = x ∧
      y ∈ (posU6 K).map (e6Isogeny K) by
    obtain ⟨y, hy1, hy⟩ := h _ hg'
    have : y = g := Subtype.ext hy1
    rwa [this] at hy
  intro x hx
  unfold CFSG.Blueprint.Chevalley.posUnipotent CFSG.Blueprint.Chevalley.rootSpan at hx
  refine Subgroup.iSup_induction _ (C := fun x => ∃ y : adjointGroup Tag.E6 K, y.1 = x ∧
    y ∈ (posU6 K).map (e6Isogeny K)) hx (fun α x hx => ?_) ⟨1, rfl, one_mem _⟩
    (fun x y ⟨a, ha1, ha⟩ ⟨b, hb1, hb⟩ => ⟨a * b, by rw [Subgroup.coe_mul, ha1, hb1], mul_mem ha hb⟩)
  refine Subgroup.iSup_induction _ (C := fun x => ∃ y : adjointGroup Tag.E6 K, y.1 = x ∧
    y ∈ (posU6 K).map (e6Isogeny K)) hx (fun hα z hz => ?_) ⟨1, rfl, one_mem _⟩
    (fun x y ⟨a, ha1, ha⟩ ⟨b, hb1, hb⟩ => ⟨a * b, by rw [Subgroup.coe_mul, ha1, hb1], mul_mem ha hb⟩)
  obtain ⟨hroot, hpos⟩ := hα
  have hz' : (⟨z, rootSubgroup_le_adjointGroup α hz⟩ : adjointGroup Tag.E6 K) ∈
      (CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 K α).subgroupOf (adjointGroup Tag.E6 K) := hz
  rw [(rootOperatorFamily Tag.E6).subgroupOf_rootSubgroup_eq K ⟨α, hroot⟩] at hz'
  obtain ⟨c, hc⟩ := (rootOperatorFamily Tag.E6).mem_rootSubgroup.1 hz'
  refine ⟨⟨z, rootSubgroup_le_adjointGroup α hz⟩, rfl, ?_⟩
  refine ⟨e6Data_valid.xm K α ((relSignOr (rootOperatorFamily Tag.E6) CFSG.LieType.Steinberg.Adjoint.e6AdjData_valid α : K) * c),
    rootGroup_le_posU6 K hroot hpos (e6Data_valid.xm_mem_rootGroup K α _), ?_⟩
  rw [e6Isogeny_xm K hroot]
  unfold yPar
  rw [← mul_assoc, relSignOr_mul_self, one_mul, CFSG.LieType.Steinberg.Adjoint.xPar_of_isRoot hroot]
  exact hc

theorem finite_minGroup6 : Finite (e6Data_valid.minGroup K) := finite_minGroup' (K := K) e6Data_valid

theorem two_group_inf_ker (P : Subgroup (e6Data_valid.minGroup K)) (hP : IsPGroup 2 P)
    {z : e6Data_valid.minGroup K} (hzP : z ∈ P) (hz : e6Isogeny K z = 1) : z = 1 := by
  have hker : z ∈ Subgroup.center (e6Data_valid.minGroup K) := by
    rw [← e6Isogeny_ker_eq_center]; exact hz
  obtain ⟨k, hk⟩ := hP ⟨z, hzP⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcard := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := K)).1
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.center (e6Data_valid.minGroup K)) := by
    rw [hcard]
    intro h
    have : 2 ∣ 3 := h.trans (Nat.gcd_dvd_left 3 _)
    omega
  have hz2 : z ^ Nat.card (Subgroup.center (e6Data_valid.minGroup K)) = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center (e6Data_valid.minGroup K)) (x := ⟨z, hker⟩)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center (e6Data_valid.minGroup K))) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have := orderOf_dvd_of_pow_eq_one hk'
  have h2 := orderOf_dvd_of_pow_eq_one hz2
  have : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop ‹orderOf z ∣ 2 ^ k› h2
  exact orderOf_eq_one_iff.1 this

theorem card_map_le_of_surj {G H : Type*} [Group G] [Group H] (S : Subgroup G) [Finite S]
    (f : G →* H) :
    Nat.card (S.map f) ≤ Nat.card S := by
  have hs : Function.Surjective (fun x : S => (⟨f x, ⟨x, x.2, rfl⟩⟩ : S.map f)) := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact Nat.card_le_card_of_surjective _ hs

theorem e6_posU6_sylow : ∃ P : Sylow 2 (e6Data_valid.minGroup K), (P : Subgroup _) = posU6 K := by
  have := finite_minGroup6 K
  obtain ⟨P, hP⟩ := (isPGroup_posU6 K).exists_le_sylow
  refine ⟨P, ?_⟩
  symm
  have hPp : IsPGroup 2 (P : Subgroup (e6Data_valid.minGroup K)) := P.isPGroup'
  set π := e6Isogeny K with hπ
  have hfin : Finite (adjointGroup Tag.E6 K) := by
    have := finite_modGL (τ := Tag.E6) (K := K)
    infer_instance
  have hinj : Function.Injective (fun x : (P : Subgroup (e6Data_valid.minGroup K)) =>
      (⟨π x, ⟨x, x.2, rfl⟩⟩ : (P : Subgroup (e6Data_valid.minGroup K)).map π)) := by
    intro x y hxy
    have h1 : π (x : e6Data_valid.minGroup K) = π y := congrArg Subtype.val hxy
    have h2 : (x : e6Data_valid.minGroup K)⁻¹ * y = 1 :=
      two_group_inf_ker K P hPp (P.mul_mem (P.inv_mem x.2) y.2) (by
        rw [map_mul, map_inv, h1, inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have hcardP : Nat.card (P : Subgroup (e6Data_valid.minGroup K)) =
      Nat.card ((P : Subgroup (e6Data_valid.minGroup K)).map π) := by
    refine Nat.card_congr (Equiv.ofBijective _ ⟨hinj, ?_⟩)
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨g, hg⟩ := adjoint_conj_into_U K Tag.E6 _ (hPp.map π)
  have hc1 : Nat.card (((P : Subgroup (e6Data_valid.minGroup K)).map π).map
      (MulAut.conj g).toMonoidHom) = Nat.card ((P : Subgroup (e6Data_valid.minGroup K)).map π) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv).symm
  have hUcard : Nat.card (Uad K Tag.E6) = Nat.card K ^
      {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α ∧ 0 < height α}.ncard := by
    rw [card_subgroupOf_of_le posUnipotent_le_adjointGroup, card_posUnipotent]
  have h2 := Subgroup.card_le_of_le (Uad_le_map_posU6 K)
  have h3 := card_map_le_of_surj (posU6 K) π
  have h4 := Subgroup.card_le_of_le hg
  have h5 : Nat.card (posU6 K) ≤ Nat.card (P : Subgroup (e6Data_valid.minGroup K)) :=
    Subgroup.card_le_of_le hP
  have hcard : Nat.card (P : Subgroup (e6Data_valid.minGroup K)) ≤ Nat.card (posU6 K) := by
    rw [hcardP, ← hc1]
    exact h4.trans (h2.trans h3)
  exact Subgroup.eq_of_le_of_card_ge hP hcard

theorem e6_conj_into_posU6 (A : Subgroup (e6Data_valid.minGroup K)) (hA : IsPGroup 2 A) :
    ∃ g : e6Data_valid.minGroup K, A.map (MulAut.conj g).toMonoidHom ≤ posU6 K := by
  have := finite_minGroup6 K
  obtain ⟨P, hP⟩ := e6_posU6_sylow K
  obtain ⟨g, hg⟩ := exists_conj_le_sylow P A hA
  exact ⟨g, hP ▸ hg⟩

theorem isPGroup_of_sq {G : Type*} [Group G] (A : Subgroup G) (hA : ∀ a ∈ A, a ^ 2 = 1) :
    IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hA a a.2)⟩

theorem offender_transfer_posU6
    (H : ∀ A : Subgroup (e6Data_valid.minGroup K), A ≤ posU6 K → A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card (fixSub e6Data_valid A) ≤ Nat.card K ^ 26 ∧
        Nat.card A ^ 2 * Nat.card (fixSub e6Data_valid A) ≤ Nat.card K ^ 42)
    {A : Subgroup (e6Data_valid.minGroup K)} (hA : A ≤ F4in27 e6Data_valid K) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card ↥(fixSub e6Data_valid A ⊓ M26 e6Data_valid K) ≤ Nat.card K ^ 25 ∧
      Nat.card A ^ 2 * Nat.card ↥(fixSub e6Data_valid A ⊓ M26 e6Data_valid K) ≤ Nat.card K ^ 41 :=
  have := finite_minGroup6 K
  offender_transfer_of_conj e6Data_valid (posU6 K)
    (fun B hB => e6_conj_into_posU6 K B (isPGroup_of_sq B hB)) H hA hne hel

theorem f4_26_offender_bound_posU6
    (H : ∀ A : Subgroup (e6Data_valid.minGroup K), A ≤ posU6 K → A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card (fixSub e6Data_valid A) ≤ Nat.card K ^ 26 ∧
        Nat.card A ^ 2 * Nat.card (fixSub e6Data_valid A) ≤ Nat.card K ^ 42)
    (θ : adjointGroup Tag.F4 K ≃* adjointGroup Tag.F4 K) {A : Subgroup (adjointGroup Tag.F4 K)}
    (hne : A ≠ ⊥) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card ↥(fixSub e6Data_valid (A.map (f4Embed K θ)) ⊓ M26 e6Data_valid K) ≤
        Nat.card K ^ 25 ∧
      Nat.card A ^ 2 *
        Nat.card ↥(fixSub e6Data_valid (A.map (f4Embed K θ)) ⊓ M26 e6Data_valid K) ≤
        Nat.card K ^ 41 := by
  have hcard : Nat.card (A.map (f4Embed K θ)) = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ (f4Embed_injective K θ)).toEquiv).symm
  have hle : A.map (f4Embed K θ) ≤ F4in27 e6Data_valid K := by
    rintro _ ⟨a, -, rfl⟩
    exact f4Embed_mem K θ a
  have hne' : A.map (f4Embed K θ) ≠ ⊥ := fun h => hne (by
    rwa [Subgroup.map_eq_bot_iff_of_injective _ (f4Embed_injective K θ)] at h)
  have hel' : ∀ b ∈ A.map (f4Embed K θ), b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hel a ha, map_one]
  have := offender_transfer_posU6 K H hle hne' hel'
  rwa [hcard] at this

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
