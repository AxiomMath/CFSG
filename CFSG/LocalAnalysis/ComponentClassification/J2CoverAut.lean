module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def permU : Equiv.Perm (Fin 315) := perm outerArr

theorem rep_permU : Rep 315 outerArr permU :=
  (rep_permOfArr (isInvA_of_invoList inv_check.1)).1

theorem permU_inv : permU⁻¹ = permU :=
  ((rep_permOfArr (isInvA_of_invoList inv_check.1)).2).unique rep_permU

theorem permU_mul_self : permU * permU = 1 := by
  rw [← mul_inv_cancel permU, permU_inv]

theorem permU_sq : permU ^ 2 = 1 := by
  rw [sq, permU_mul_self]

theorem permU_ne_one : permU ≠ 1 := by
  intro h
  have h1 := eqA_idA_of_movesList inv_check.2.1
  rw [(eqA_iff rep_permU rep_idA).2 h] at h1
  exact Bool.noConfusion h1

theorem permU_not_mem : permU ∉ P := by
  intro h
  have h1 := outer_check.1
  rw [(mem_P_iff rep_permU).2 h] at h1
  exact Bool.noConfusion h1

theorem conj_a_mem : permU * permA * permU⁻¹ ∈ P := by
  rw [permU_inv, mul_assoc]
  exact (mem_P_iff (rep_compA rep_permU (rep_compA (rep_strong (j := 0) (by norm_num))
    rep_permU))).1 outer_check.2.1

theorem conj_b_mem : permU * permB * permU⁻¹ ∈ P := by
  rw [permU_inv, mul_assoc]
  exact (mem_P_iff (rep_compA rep_permU (rep_compA (rep_strong (j := 1) (by norm_num))
    rep_permU))).1 outer_check.2.2

theorem permU_conj_mem : ∀ h ∈ P, permU * h * permU⁻¹ ∈ P :=
  conj_mem_of_closure rfl fun s hs => by
    rcases hs with rfl | rfl
    · exact conj_a_mem
    · exact conj_b_mem

theorem permU_conj_mem' : ∀ h ∈ P, permU⁻¹ * h * permU ∈ P := by
  intro h hh
  have := permU_conj_mem h hh
  rw [permU_inv] at this ⊢
  exact this

theorem map_conj_permU : P.map (MulAut.conj permU).toMonoidHom = P := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    exact permU_conj_mem h hh
  · intro h hh
    refine ⟨permU⁻¹ * h * permU, permU_conj_mem' h hh, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem strong_mem {j : ℕ} (hj : j < 7) : perm autStrong[j]! ∈ P := by
  have h := RawSchreierDatum.strong_get_mem_originalSubgroup
    (RawSchreierDatum.ofArrays 315 (by norm_num) autStrong 2 (by decide) [0, 4, 3] (by decide)
      autWords) autChain_valid
    ⟨j, by rw [RawSchreierDatum.ofArrays_strongCount, autStrong_size]; exact hj⟩
  rw [RawSchreierDatum.ofArrays_strong_get] at h
  rw [← autChain_originalSubgroup]
  exact h

theorem centralizer_P : Subgroup.centralizer (P : Set (Equiv.Perm (Fin 315))) = ⊥ := by
  obtain ⟨h2, h3, h4, hall⟩ := stab_check
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_centralizer_iff] at hv
  have hfix : ∀ j : ℕ, j < 7 → (autStrong[j]!)[0]! = 0 →
      ((autStrong[j]!)[((v 0 : Fin 315) : ℕ)]!) = ((v 0 : Fin 315) : ℕ) := by
    intro j hj h0
    have hc := hv _ (strong_mem hj)
    have e1 := (rep_strong hj) (v 0)
    have e0 := (rep_strong hj) 0
    have h0' : (perm autStrong[j]!) 0 = 0 := by
      apply Fin.ext
      rw [← e0, Fin.val_zero]
      exact h0
    rw [e1]
    have : (perm autStrong[j]! * v) 0 = (v * perm autStrong[j]!) 0 := by rw [hc]
    simp only [Equiv.Perm.mul_apply] at this
    rw [this, h0']
  have hv0 : v 0 = 0 := by
    have := List.all_eq_true.1 hall _ (List.mem_range.2 (v 0).isLt)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    rcases this with ((h | h) | h) | h
    · exact Fin.ext h
    · exact absurd (hfix 2 (by norm_num) h2) h
    · exact absurd (hfix 3 (by norm_num) h3) h
    · exact absurd (hfix 4 (by norm_num) h4) h
  rw [Subgroup.mem_bot]
  ext x
  obtain ⟨g, hg, rfl⟩ := P_transitive x
  have hc := hv g hg
  have : (g * v) 0 = (v * g) 0 := by rw [hc]
  simp only [Equiv.Perm.mul_apply, hv0] at this
  rw [Equiv.Perm.one_apply, ← this]

@[expose] noncomputable def R : Subgroup (Equiv.Perm (Fin 315)) :=
  Subgroup.closure {permA, permB, permU}

theorem P_le_R : P ≤ R := by
  rw [P, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem permU_mem_R : permU ∈ R :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem mem_R_iff (g : Equiv.Perm (Fin 315)) : g ∈ R ↔ g ∈ P ∨ g * permU ∈ P := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact Or.inl permA_mem
      · exact Or.inl permB_mem
      · exact Or.inr (by rw [permU_mul_self]; exact P.one_mem)
    | one => exact Or.inl P.one_mem
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (P.mul_mem hx hy)
      · exact Or.inr (by rw [mul_assoc]; exact P.mul_mem hx hy)
      · refine Or.inr ?_
        have e : x * y * permU = x * permU * (permU⁻¹ * y * permU) := by group
        rw [e]
        exact P.mul_mem hx (permU_conj_mem' y hy)
      · refine Or.inl ?_
        have e : x * y = x * permU * (permU * (y * permU) * permU⁻¹) := by
          rw [show x * permU * (permU * (y * permU) * permU⁻¹) =
            x * (permU * permU) * y * (permU * permU⁻¹) by group, permU_mul_self]
          group
        rw [e]
        exact P.mul_mem hx (permU_conj_mem _ hy)
    | inv x _ hx =>
      rcases hx with hx | hx
      · exact Or.inl (P.inv_mem hx)
      · refine Or.inr ?_
        have e : x⁻¹ * permU = (permU⁻¹ * (x * permU) * permU)⁻¹ := by
          rw [show permU⁻¹ * (x * permU) * permU = permU⁻¹ * x * (permU * permU) by group,
            permU_mul_self]
          group
        rw [e]
        exact P.inv_mem (permU_conj_mem' _ hx)
  · rintro (h | h)
    · exact P_le_R h
    · have e : g = g * permU * permU⁻¹ := by group
      rw [e]
      exact R.mul_mem (P_le_R h) (R.inv_mem permU_mem_R)

theorem card_R : Nat.card R = 1209600 := by
  set K := P.subgroupOf R
  have hidx : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨permU, permU_mem_R⟩, fun g => ?_⟩
    simp only [K, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases (mem_R_iff g).1 g.2 with h | h
    · have hn : (g : Equiv.Perm (Fin 315)) * permU ∉ P := fun h' => permU_not_mem (by
        have e : permU = (g : Equiv.Perm (Fin 315))⁻¹ * (g * permU) := by group
        rw [e]
        exact P.mul_mem (P.inv_mem h) h')
      exact Or.inr ⟨h, hn⟩
    · have hn : (g : Equiv.Perm (Fin 315)) ∉ P := fun h' => permU_not_mem (by
        have e : permU = (g : Equiv.Perm (Fin 315))⁻¹ * (g * permU) := by group
        rw [e]
        exact P.mul_mem (P.inv_mem h') h)
      exact Or.inl ⟨h, hn⟩
  have hK : Nat.card K = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_R).toEquiv
  rw [← K.card_mul_index, hidx, hK, card_P]

theorem R_le_normalizer : R ≤ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 315))) := by
  rw [R, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact Subgroup.le_normalizer permA_mem
  · exact Subgroup.le_normalizer permB_mem
  · intro h
    refine ⟨fun hh => permU_conj_mem h hh, fun hh => ?_⟩
    have := permU_conj_mem' _ hh
    rwa [show permU⁻¹ * (permU * h * permU⁻¹) * permU = h by group] at this

@[expose] noncomputable def rConj : R →* MulAut P :=
  (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion R_le_normalizer)

theorem rConj_apply (r : R) (g : P) :
    (rConj r g : Equiv.Perm (Fin 315)) = r * g * (r : Equiv.Perm (Fin 315))⁻¹ := rfl

theorem rConj_injective : Function.Injective rConj := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro r hr
  have hc : (r : Equiv.Perm (Fin 315)) ∈ Subgroup.centralizer (P : Set (Equiv.Perm (Fin 315))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg (fun α : MulAut P => ((α ⟨h, hh⟩ : P) : Equiv.Perm (Fin 315)))
      (MonoidHom.mem_ker.1 hr)
    simp only [rConj_apply, MulAut.one_apply] at h1
    calc h * r = r * h * (r : Equiv.Perm (Fin 315))⁻¹ * r := by rw [h1]
      _ = r * h := by group
  rw [centralizer_P, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem map_rConj_P : (P.subgroupOf R).map rConj = inner P := by
  ext α
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr
    refine ⟨⟨r, hr⟩, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [rConj_apply, MulAut.conj_apply]
    rfl
  · rintro ⟨p, rfl⟩
    refine ⟨⟨p, P_le_R p.2⟩, by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact p.2, ?_⟩
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [rConj_apply, MulAut.conj_apply]
    rfl

theorem ctuc_j2_normalizing_involution_permutation_model :
    permU ^ 2 = 1 ∧ permU ≠ 1 ∧ permU ∉ P ∧ P.map (MulAut.conj permU).toMonoidHom = P ∧
      Subgroup.centralizer (P : Set (Equiv.Perm (Fin 315))) = ⊥ ∧ P ≤ R ∧ permU ∈ R ∧
      (∀ g, g ∈ R ↔ g ∈ P ∨ g * permU ∈ P) ∧ Nat.card R = 1209600 ∧
      Function.Injective rConj ∧ (P.subgroupOf R).map rConj = inner P :=
  ⟨permU_sq, permU_ne_one, permU_not_mem, map_conj_permU, centralizer_P, P_le_R, permU_mem_R,
    mem_R_iff, card_R, rConj_injective, map_rConj_P⟩

theorem pa_pb_ne : pa * pb ≠ pb * pa :=
  mul_ne_mul_of_orderOf_commutator at_j2_image_pair_count.2.2.2.1 (by norm_num)

theorem center_P : Subgroup.center P = ⊥ :=
  center_eq_bot_of_simple isSimpleGroup_P pa_pb_ne

theorem finite_mulAut_P : Finite (MulAut P) :=
  Finite.of_injective (fun α : MulAut P => (α : P → P)) DFunLike.coe_injective

theorem card_mulAut_P_eq : Nat.card (MulAut P) = Nat.card (Outer P) * Nat.card P := by
  have h := (inner P).card_eq_card_quotient_mul_card_subgroup
  rw [card_inner_of_center_eq_bot center_P] at h
  exact h

theorem rConj_bijective : Function.Bijective rConj := by
  have := finite_mulAut_P
  refine rConj_injective.bijective_of_nat_card_le ?_
  rw [card_mulAut_P_eq, card_R, card_P]
  exact (Nat.mul_le_mul_right 604800 outer_P.1).trans (by norm_num)

@[expose] noncomputable def rAutEquiv : R ≃* MulAut P := MulEquiv.ofBijective rConj rConj_bijective

theorem rAutEquiv_apply (r : R) : rAutEquiv r = rConj r := rfl

theorem card_mulAut_P : Nat.card (MulAut P) = 1209600 := by
  rw [← Nat.card_congr rAutEquiv.toEquiv, card_R]

theorem card_outer_P : Nat.card (Outer P) = 2 := by
  have h := card_mulAut_P_eq
  rw [card_mulAut_P, card_P] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 604800) (h.symm.trans (by norm_num))

theorem card_multiplicative_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem ctuc_j2_full_automorphism_permutation_model :
    Function.Bijective rConj ∧ (P.subgroupOf R).map rConj = inner P ∧
      Nat.card (MulAut P) = 1209600 ∧ Nonempty (Outer P ≃* Multiplicative (ZMod 2)) ∧
      Nat.card (MulAut NativeSporadic.J2) = 1209600 ∧
      Nonempty (Outer NativeSporadic.J2 ≃* Multiplicative (ZMod 2)) := by
  have e : Outer P ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (p := 2) card_outer_P card_multiplicative_zmod_two
  refine ⟨rConj_bijective, map_rConj_P, card_mulAut_P, ⟨e⟩, ?_, ⟨outerEquivP.trans e⟩⟩
  rw [Nat.card_congr mulAutEquivP, card_mulAut_P]

end CFSG.ComponentClassification.J2Cover
