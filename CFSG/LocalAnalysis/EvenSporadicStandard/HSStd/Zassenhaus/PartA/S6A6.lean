module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

theorem s6_A6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem s6_A6_nonab : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  have hs := s6_A6_simple
  let _ : CommGroup (alternatingGroup (Fin 6)) :=
    { (inferInstance : Group (alternatingGroup (Fin 6))) with mul_comm := fun a b => hno a b }
  have hp := hs.prime_card
  rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hp
  simp [Nat.factorial] at hp
  norm_num at hp

theorem s6_comm_mulAut :
    commutator (MulAut (alternatingGroup (Fin 6))) =
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  apply le_antisymm
  · have hN : (MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6))).range.Normal :=
      ⟨by
        rintro _ ⟨b, rfl⟩ g
        exact ⟨g b, (mul_conj_mul_inv g b).symm⟩⟩
    have hcard : Nat.card (MulAut (alternatingGroup (Fin 6)) ⧸ (MulAut.conj :
        alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range) = 2 ^ 2 := by
      rw [← Subgroup.index_eq_card, CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6]
      norm_num
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := (MulAut.conj :
      alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range)).1 hcomm
  · have hperf : commutator (alternatingGroup (Fin 6)) = ⊤ := by
      have := s6_A6_simple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 6)))
        with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := s6_A6_nonab
        apply hab
        have hmem : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 6)) :=
          Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_def] at hmem
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [hmem, one_mul]
      · exact h
    rw [MonoidHom.range_eq_map, ← hperf, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top


section J

variable {G : Type*} [Group G]

theorem s6_conj_injective :
    Function.Injective (MulAut.conj :
      alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) :=
  have := s6_A6_simple
  conj_injective_of_simple s6_A6_nonab

theorem s6_orderOf_conj (x : alternatingGroup (Fin 6)) :
    orderOf (MulAut.conj x : MulAut (alternatingGroup (Fin 6))) = orderOf x :=
  orderOf_injective (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6)))
    s6_conj_injective x

theorem s6_mem_J_iff (Abar : Subgroup G) (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6))) {x : G} :
    x ∈ derivedIn Abar ↔ ∃ h : x ∈ Abar, e ⟨x, h⟩ ∈
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  have hmap : (commutator ↥Abar).map e.toMonoidHom = commutator (MulAut (alternatingGroup (Fin 6))) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective, ← _root_.commutator_def]
  have hiff : ∀ y : ↥Abar, y ∈ commutator ↥Abar ↔ e y ∈ commutator (MulAut (alternatingGroup (Fin 6))) := by
    intro y
    rw [← hmap]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  rw [← s6_comm_mulAut]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (hiff y).1 hy⟩
  · rintro ⟨h, h2⟩
    exact ⟨⟨x, h⟩, (hiff _).2 h2, rfl⟩

theorem s6_orderOf_of_mem_J {Abar : Subgroup G} (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6)))
    {x : G} (hx : x ∈ Abar) {z : alternatingGroup (Fin 6)} (hz : e ⟨x, hx⟩ = MulAut.conj z) :
    orderOf x = orderOf z := by
  calc orderOf x = orderOf (⟨x, hx⟩ : ↥Abar) := (Subgroup.orderOf_mk x hx).symm
    _ = orderOf (e ⟨x, hx⟩) := (MulEquiv.orderOf_eq e _).symm
    _ = orderOf (MulAut.conj z : MulAut (alternatingGroup (Fin 6))) := by rw [hz]
    _ = orderOf z := s6_orderOf_conj z

theorem s6_exists_conj {Abar : Subgroup G} (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6)))
    {y a : G} (hy : y ∈ derivedIn Abar) (hy3 : orderOf y = 3) (ha : a ∈ derivedIn Abar)
    (ha3 : orderOf a = 3) : ∃ g ∈ Abar, g * y * g⁻¹ = a := by
  obtain ⟨hyA, x, hx⟩ := (s6_mem_J_iff Abar e).1 hy
  obtain ⟨haA, x', hx'⟩ := (s6_mem_J_iff Abar e).1 ha
  have hxo : orderOf x = 3 := by rw [← s6_orderOf_of_mem_J e hyA hx.symm, hy3]
  have hxo' : orderOf x' = 3 := by rw [← s6_orderOf_of_mem_J e haA hx'.symm, ha3]
  obtain ⟨φ, hφ⟩ := exists_mulAut_apply_eq_of_orderOf_eq_three hxo hxo'
  refine ⟨(e.symm φ).1, (e.symm φ).2, ?_⟩
  have h : e.symm φ * ⟨y, hyA⟩ * (e.symm φ)⁻¹ = ⟨a, haA⟩ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hx, mul_conj_mul_inv, hφ, hx']
  exact congrArg Subtype.val h

theorem s6_exists_sylow {Abar : Subgroup G} (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6)))
    {y : G} (hy : y ∈ derivedIn Abar) (hy3 : orderOf y = 3) :
    ∃ A : Subgroup G, A ≤ derivedIn Abar ∧ y ∈ A ∧ Nat.card A = 3 ^ 2 ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ 3 = 1 := by
  obtain ⟨hyA, x, hx⟩ := (s6_mem_J_iff Abar e).1 hy
  have hxo : orderOf x = 3 := by rw [← s6_orderOf_of_mem_J e hyA hx.symm, hy3]
  set A0 : Subgroup (alternatingGroup (Fin 6)) := centralizer ({x} : Set (alternatingGroup (Fin 6)))
    with hA0
  let B : Subgroup ↥Abar := (A0.map (MulAut.conj : alternatingGroup (Fin 6) →*
    MulAut (alternatingGroup (Fin 6)))).comap
    (e : ↥Abar →* MulAut (alternatingGroup (Fin 6)))
  have hB : ∀ b : ↥Abar, b ∈ B ↔ ∃ z ∈ A0, MulAut.conj z = e b := by
    intro b
    exact Iff.rfl
  refine ⟨B.map Abar.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨z, -, hz⟩ := (hB b).1 hb
    exact (s6_mem_J_iff Abar e).2 ⟨b.2, z, hz⟩
  · refine ⟨⟨y, hyA⟩, (hB _).2 ⟨x, mem_centralizer_singleton_iff.2 rfl, hx⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective Abar.subtype_injective]
    have h1 : Nat.card B = Nat.card (A0.map (MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6)))) := by
      show Nat.card (Subgroup.comap (e : ↥Abar →* MulAut (alternatingGroup (Fin 6))) _) = _
      rw [Subgroup.comap_equiv_eq_map_symm]
      exact Subgroup.card_map_of_injective
        (f := (e.symm : MulAut (alternatingGroup (Fin 6)) →* ↥Abar)) e.symm.injective
    rw [h1, Subgroup.card_map_of_injective s6_conj_injective,
      card_centralizer_of_orderOf_eq_three hxo]
    norm_num
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨z, hz, hza⟩ := (hB a).1 ha
    obtain ⟨z', hz', hzb⟩ := (hB b).1 hb
    have hcomm : z * z' = z' * z := centralizer_commute_of_orderOf_eq_three hxo z hz z' hz'
    have : a * b = b * a := by
      apply e.injective
      rw [map_mul, map_mul, ← hza, ← hzb, ← map_mul, ← map_mul, hcomm]
    exact congrArg Subtype.val this
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨z, hz, hza⟩ := (hB a).1 ha
    have : a ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, ← hza, ← map_pow, pow_three_of_mem_centralizer hxo z hz, map_one, map_one]
    exact congrArg Subtype.val this

theorem s6_gen_J {Abar : Subgroup G} (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6)))
    {y : G} (hy : y ∈ derivedIn Abar) (hy3 : orderOf y = 3) (H : Subgroup G)
    (hH : ∀ a ∈ derivedIn Abar, orderOf a = 3 → a ∈ H) : derivedIn Abar ≤ H := by
  obtain ⟨hyA, x, hx⟩ := (s6_mem_J_iff Abar e).1 hy
  have hxo : orderOf x = 3 := by rw [← s6_orderOf_of_mem_J e hyA hx.symm, hy3]
  have hsimple := s6_A6_simple
  set K : Subgroup (alternatingGroup (Fin 6)) :=
    Subgroup.closure {w : alternatingGroup (Fin 6) | orderOf w = 3} with hK
  have hKn : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : K ≤ K.comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).2 (fun w hw => ?_)
      apply Subgroup.subset_closure
      show orderOf (g * w * g⁻¹) = 3
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective w
      have hw' : orderOf w = 3 := hw
      exact (by simpa [MulAut.conj_apply] using this : orderOf (g * w * g⁻¹) = orderOf w).trans hw'
    exact hle hn
  have hKx : x ∈ K := Subgroup.subset_closure hxo
  have hKtop : K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at hKx
      rw [hKx, orderOf_one] at hxo
      omega
    · exact h
  let f : alternatingGroup (Fin 6) →* G :=
    Abar.subtype.comp (e.symm.toMonoidHom.comp MulAut.conj)
  have hf : ∀ z, e ⟨f z, (e.symm (MulAut.conj z)).2⟩ = MulAut.conj z := fun z => by
    have : (⟨f z, (e.symm (MulAut.conj z)).2⟩ : ↥Abar) = e.symm (MulAut.conj z) := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have key : ∀ z ∈ K, f z ∈ H := by
    intro z hz
    refine Subgroup.closure_induction (p := fun z _ => f z ∈ H) ?_ ?_ ?_ ?_ hz
    · intro w hw
      have hJ : f w ∈ derivedIn Abar :=
        (s6_mem_J_iff Abar e).2 ⟨(e.symm (MulAut.conj w)).2, w, (hf w).symm⟩
      exact hH _ hJ (by rw [s6_orderOf_of_mem_J e _ (hf w)]; exact hw)
    · simp [H.one_mem]
    · intro a b _ _ ha hb
      rw [map_mul]
      exact H.mul_mem ha hb
    · intro a _ ha
      rw [map_inv]
      exact H.inv_mem ha
  intro j hj
  obtain ⟨hjA, z, hz⟩ := (s6_mem_J_iff Abar e).1 hj
  have hzj : f z = j := by
    have : e.symm (MulAut.conj z) = ⟨j, hjA⟩ := by rw [hz]; simp
    exact congrArg Subtype.val this
  rw [← hzj]
  exact key z (hKtop ▸ Subgroup.mem_top z)

end J

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
