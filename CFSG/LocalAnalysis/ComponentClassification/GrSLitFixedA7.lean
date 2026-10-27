module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL2

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem two_mul_card_le_of_not_mem {X : Type*} [Group X] [Finite X] {H K : Subgroup X}
    (hHK : H ≤ K) {x : X} (hxK : x ∈ K) (hxH : x ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHK
  have hK : 0 < Nat.card K := Nat.card_pos
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    interval_cases m
    · rw [mul_zero] at hm
      omega
    · rw [mul_one] at hm
      exact hxH (by rw [Subgroup.eq_of_le_of_card_ge hHK hm.le]; exact hxK)
  calc 2 * Nat.card H ≤ m * Nat.card H := Nat.mul_le_mul_right _ hm2
    _ = Nat.card K := by rw [hm, mul_comm]

theorem fix_or_swap_of_commute {g : Perm (Fin 7)} (hg : g * swap 0 1 = swap 0 1 * g) :
    (g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 1 ∧ g 1 = 0) := by
  have h1 : g 1 = swap 0 1 (g 0) := by
    have := congrArg (fun f : Perm (Fin 7) => f 0) hg
    simpa only [Perm.mul_apply, swap_apply_left] using this
  by_cases h0 : g 0 = 0
  · exact Or.inl ⟨h0, by rw [h1, h0, swap_apply_left]⟩
  · by_cases h0' : g 0 = 1
    · exact Or.inr ⟨h0', by rw [h1, h0', swap_apply_right]⟩
    · exfalso
      rw [swap_apply_of_ne_of_ne h0 h0'] at h1
      exact absurd (g.injective h1) (by decide)

theorem commutator_apply_zero {g h : Perm (Fin 7)} (hg : g * swap 0 1 = swap 0 1 * g)
    (hh : h * swap 0 1 = swap 0 1 * h) : (g * h * g⁻¹ * h⁻¹) 0 = 0 := by
  have hi : ∀ (f : Perm (Fin 7)) (a b : Fin 7), f a = b → f⁻¹ b = a := fun f a b hf => by
    rw [Perm.inv_eq_iff_eq, hf]
  rw [Perm.mul_apply, Perm.mul_apply, Perm.mul_apply]
  rcases fix_or_swap_of_commute hg with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;>
    rcases fix_or_swap_of_commute hh with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [hi h 0 0 h0, hi g 0 0 g0, h0, g0]
  · rw [hi h 1 0 h1, hi g 1 1 g1, h1, g0]
  · rw [hi h 0 0 h0, hi g 1 0 g1, h1, g1]
  · rw [hi h 1 0 h1, hi g 0 1 g0, h0, g1]

theorem cycleType_swap_zero_one : (swap (0 : Fin 7) 1).cycleType = {2} := by
  rw [(Perm.isCycle_swap (by decide : (0 : Fin 7) ≠ 1)).cycleType,
    Perm.card_support_swap (by decide : (0 : Fin 7) ≠ 1)]

theorem card_le_sixty_of_isPerfect {Q : Subgroup (Perm (Fin 7))} [Group.IsPerfect Q]
    (hQ : Q ≤ centralizer {swap (0 : Fin 7) 1} ⊓ alternatingGroup (Fin 7)) :
    Nat.card Q ≤ 60 := by
  have hcomm : ∀ g ∈ centralizer ({swap (0 : Fin 7) 1} : Set (Perm (Fin 7))),
      g * swap 0 1 = swap 0 1 * g := fun g hg => mem_centralizer_singleton_iff.mp hg
  have hQN : Q ≤ (centralizer {swap (0 : Fin 7) 1} ⊓ alternatingGroup (Fin 7)) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) := by
    intro x hx
    refine mem_inf.mpr ⟨hQ hx, ?_⟩
    have hx' : x ∈ ⁅Q, Q⁆ := by rw [Subgroup.commutator_eq_self]; exact hx
    have hle : ⁅Q, Q⁆ ≤ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) := by
      rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      rw [MulAction.mem_stabilizer_iff, Perm.smul_def, commutatorElement_def]
      exact commutator_apply_zero (hcomm _ (mem_inf.mp (hQ h₁)).1)
        (hcomm _ (mem_inf.mp (hQ h₂)).1)
    exact hle hx'
  have hC : Nat.card (centralizer ({swap (0 : Fin 7) 1} : Set (Perm (Fin 7)))) = 240 := by
    rw [Perm.nat_card_centralizer, cycleType_swap_zero_one]
    decide
  have hsw : swap (0 : Fin 7) 1 ∈ centralizer ({swap (0 : Fin 7) 1} : Set (Perm (Fin 7))) :=
    mem_centralizer_singleton_iff.mpr rfl
  have hswA : swap (0 : Fin 7) 1 ∉ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_swap (by decide)]
    decide
  have h1 := two_mul_card_le_of_not_mem
    (inf_le_left : centralizer {swap (0 : Fin 7) 1} ⊓ alternatingGroup (Fin 7) ≤ _) hsw
    (fun h => hswA (mem_inf.mp h).2)
  have htF : swap (0 : Fin 7) 1 * swap 2 3 ∈
      centralizer {swap (0 : Fin 7) 1} ⊓ alternatingGroup (Fin 7) := by
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (by decide), ?_⟩
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  have htN : swap (0 : Fin 7) 1 * swap 2 3 ∉
      MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) := by
    rw [MulAction.mem_stabilizer_iff, Perm.smul_def]
    decide
  have h2 := two_mul_card_le_of_not_mem inf_le_left htF (fun h => htN (mem_inf.mp h).2)
  have h3 := Subgroup.card_le_of_le hQN
  omega

theorem simpleFixedComponents_a7 : SimpleFixedComponents IsA7Type (IsL2Type 5) := by
  intro S _ _ hS hnab hτ σ hσ P hPF hP hPne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ⟩ := hτ
  obtain ⟨hs, -, h60, hdvd⟩ := fusionZStar_quotient_of_isPComponent hPF hP
  have hPle : Nat.card (P ⧸ Open.fusionZStar P) ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos hdvd
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  set σ' : MulAut (alternatingGroup (Fin 7)) := MulAut.congr θ σ with hσ'def
  obtain ⟨π, hπ⟩ := hbij.2 σ'
  have hπapp : ∀ g : alternatingGroup (Fin 7),
      ((σ' g : alternatingGroup (Fin 7)) : Perm (Fin 7)) = π * g * π⁻¹ := by
    intro g
    rw [← hπ]
    exact MulAut.conjNormal_apply π g
  have hσ'2 : σ' * σ' = 1 := by
    refine MulEquiv.ext fun t => ?_
    show σ' (σ' t) = t
    rw [hσ'def, Sporadic.HeldB.congr_apply', Sporadic.HeldB.congr_apply',
      MulEquiv.symm_apply_apply, hσ, MulEquiv.apply_symm_apply]
  have hπ2 : π * π = 1 := hbij.1 (by rw [map_mul, hπ, hσ'2, map_one])
  have hPι : P.map ((alternatingGroup (Fin 7)).subtype.comp θ.toMonoidHom) ≤
      centralizer {π} ⊓ alternatingGroup (Fin 7) := by
    rintro _ ⟨x, hx, rfl⟩
    have hfix : σ x = x := hPF hx
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, (θ x).2⟩
    have h1 : σ' (θ x) = θ x := by
      rw [hσ'def, Sporadic.HeldB.congr_apply', MulEquiv.symm_apply_apply, hfix]
    have h2 := hπapp (θ x)
    rw [h1] at h2
    change (θ x : Perm (Fin 7)) * π = π * θ x
    calc (θ x : Perm (Fin 7)) * π = π * θ x * π⁻¹ * π := by rw [← h2]
      _ = π * θ x := by group
  have hcardP : Nat.card (P.map ((alternatingGroup (Fin 7)).subtype.comp θ.toMonoidHom)) =
      Nat.card P :=
    Subgroup.card_map_of_injective ((alternatingGroup (Fin 7)).subtype_injective.comp θ.injective)
  by_cases hπ1 : π = 1
  ·
    exfalso
    have hσ'1 : σ' = 1 := by rw [← hπ, hπ1, map_one]
    have hσ1 : σ = 1 := (MulAut.congr θ).injective (by rw [← hσ'def, hσ'1, map_one])
    have hFtop : fixedSubgroup σ = ⊤ := by
      rw [hσ1, eq_top_iff]
      intro x _
      rfl
    have : IsSimpleGroup (fixedSubgroup σ) :=
      ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
    have h := eq_top_of_isPComponent_of_isSimpleGroup hP
    apply hPne
    rw [eq_top_iff]
    intro x _
    have hx : (⟨x, hFtop ▸ mem_top x⟩ : fixedSubgroup σ) ∈ P.subgroupOf (fixedSubgroup σ) :=
      h ▸ mem_top _
    exact hx
  · have hord : orderOf π = 2 := orderOf_eq_prime (by rw [pow_two]; exact hπ2) hπ1
    obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (by rw [hord]; exact Nat.prime_two)
    rw [hord] at hn
    have hsum := Perm.sum_cycleType_le π
    rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
    have hn2 : n ≤ 2 := by omega
    have hmain : Nat.card P ≤ 60 := by
      have hC := Subgroup.card_le_of_le (hPι.trans inf_le_left)
      rw [hcardP, Perm.nat_card_centralizer, hn] at hC
      interval_cases n
      ·
        have hct : (swap (0 : Fin 7) 1).cycleType = π.cycleType := by
          rw [cycleType_swap_zero_one, hn]
          rfl
        obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct)
        have hcN : c ∈ normalizer
            ((alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
          rw [normalizer_eq_top]
          exact mem_top c
        have hQ : (P.map ((alternatingGroup (Fin 7)).subtype.comp θ.toMonoidHom)).map
            (MulAut.conj c⁻¹).toMonoidHom ≤
            centralizer {swap (0 : Fin 7) 1} ⊓ alternatingGroup (Fin 7) := by
          rw [← map_conj_centralizer_inf hcN (swap 0 1), hc]
          exact map_mono hPι
        have : Group.IsPerfect (P.subgroupOf (fixedSubgroup σ)) :=
          CatalogueBHeldSmallCore.pComponent_perfect 2 _ hP
        have : Group.IsPerfect P := Group.IsPerfect.ofSurjective
          (f := (subgroupOfEquivOfLe hPF).toMonoidHom) (subgroupOfEquivOfLe hPF).surjective
        have : Group.IsPerfect
            (P.map ((alternatingGroup (Fin 7)).subtype.comp θ.toMonoidHom)) :=
          Group.IsPerfect.map _
        have : Group.IsPerfect ((P.map ((alternatingGroup (Fin 7)).subtype.comp
            θ.toMonoidHom)).map (MulAut.conj c⁻¹).toMonoidHom) := Group.IsPerfect.map _
        have h := card_le_sixty_of_isPerfect hQ
        rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hcardP] at h
        exact h
      · exact hC.trans (by decide)
      · exact hC.trans (by decide)
    have h60' : Nat.card (P ⧸ Open.fusionZStar P) = 60 := by omega
    exact Or.inl ⟨by decide,
      LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five _
        (QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60')⟩

theorem a7FixedInput : A7FixedInput :=
  properFixedComponents_of_simple (fun _ _ _ _ e h => h.map fun f => e.trans f)
    (fun _ _ _ _ e h => LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
    simpleFixedComponents_a7

end CFSG.ComponentClassification.GrSLit
