module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalAFrame

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem omegaOne_eq_self {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    AschbacherTheorem3.omegaOne E = E :=
  le_antisymm (AschbacherTheorem3.omegaOne_le E) (AschbacherTheorem3.le_omegaOne hE.2)

theorem one_lt_pRank_U (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T) :
    1 < CFSG.Open.pRank 2 (AschbacherTheorem3.omegaOne d.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU4 := four_le_card_U hloc hC d
  obtain ⟨k, hk⟩ := (d.sylowT.isPGroup.to_le EndHyp.U_le_T).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have := CFSG.SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_omegaOne hT) hk
  omega

theorem sup_inf_A_eq (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G)) :
    (AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) ⊓
        aschbacherThm5Preimage D (Abar a) =
      AschbacherTheorem3.omegaOne (d.S ⊓
        Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) := by
  apply le_antisymm
  · intro x ⟨hx, hxA⟩
    have hxS : x ∈ d.S := by
      set U := AschbacherTheorem3.omegaOne d.T
      set V := AschbacherTheorem3.omegaOne (d.S ⊓
        Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      have hcomm := UV_comm hC d hT hW
      have hUN : U ≤ Subgroup.normalizer (V : Set G) := by
        intro u hu
        refine Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
        exact congrArg Subtype.val (hcomm.is_comm.comm ⟨v, Subgroup.mem_sup_right hv⟩
          ⟨u, Subgroup.mem_sup_left hu⟩)
      have hx' : x ∈ ((U ⊔ V : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right U V hUN] at hx'
      obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
      have hvS : v ∈ d.S := (AschbacherTheorem3.omegaOne_le _ hv).1
      have huA : u ∈ U ⊓ aschbacherThm5Preimage D (Abar a) := by
        refine ⟨hu, ?_⟩
        have : u = (u * v) * v⁻¹ := by group
        rw [this]
        exact (aschbacherThm5Preimage D (Abar a)).mul_mem hxA
          ((aschbacherThm5Preimage D (Abar a)).inv_mem (d.sylowS.le hvS))
      rw [EndHyp.U_inf_A hC, Subgroup.mem_bot] at huA
      rw [huA, one_mul]
      exact hvS
    exact mem_omegaOne_W_of_mem_sup hC d hT hW hx hxS
  · exact le_inf le_sup_right ((AschbacherTheorem3.omegaOne_le _).trans
      (inf_le_left.trans d.sylowS.le))

theorem exists_root_conj (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g)
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hnot : ∃ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T ∧
      ¬ rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) :
    ∃ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T ∧
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        Subgroup.normalizer ((AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne
          (d.S ⊓ Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) : Subgroup G) :
              Set G) ∧
      ¬ rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ∧
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g = ⊥ ∧
      ∀ x ∈ rightConjugate (AschbacherTheorem3.omegaOne d.T) c,
        ∀ v ∈ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)), x * v = v * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) d.g with hHgdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set W := d.S ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) with hWdef
  set V := AschbacherTheorem3.omegaOne W with hVdef
  obtain ⟨b, hbS, hbH, hbU⟩ := exists_conj_of_not_le d hSH
  have hUV : U ⊔ V = U ⊔ rightConjugate U b := sup_conj_eq hloc hC d hT hW hcard hbS hbH hbU
  have h45 := hyp45_U hloc hC d hT hW hcard hUZ hbS hbH hbU
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hUel : IsElemAbelian 2 U := isElemAbelian_omegaOne hT
  have hP2 : IsPGroup 2 (d.S ⊔ U : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hU2 d.sylowS.isPGroup EndHyp.U_le_normalizer_S
  have hbFam : conjFamily d (rightConjugate U b) := by
    refine ⟨b, d.sylowS.le hbS, rfl, ?_⟩
    rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_left hbS : b ∈ d.S ⊔ U)]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right b
  have hUFam : conjFamily d U := ⟨1, A.one_mem, by rw [rightConjugate_one], le_sup_right⟩
  have hex : ∃ X, conjFamily d X ∧ X ≤ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) ∧
      ¬ X ≤ U ⊔ V := by
    by_contra hne
    push Not at hne
    obtain ⟨c, hc, hcle, hcnot⟩ := hnot
    exact hcnot (le_of_le_normalizer (conjFamily d) hP2 (fun X hX => hX.choose_spec.2.2)
      (fun X hX p hp => conjFamily_rightConjugate d hX hp) hUV hUFam hbFam hne _
      ⟨c, hc, rfl, hcle⟩)
  obtain ⟨X, ⟨c, hc, rfl, hcle⟩, hXN, hXK⟩ := hex
  have hΩU : AschbacherTheorem3.omegaOne U = U := omegaOne_eq_self hUel
  have hVS : rightConjugate (AschbacherTheorem3.omegaOne U) c ≤ (d.S ⊔ U) ⊓
      Subgroup.normalizer ((U ⊔ rightConjugate U b : Subgroup G) : Set G) := by
    rw [hΩU, ← hUV]
    exact le_inf hcle hXN
  have hVW : ¬ rightConjugate (AschbacherTheorem3.omegaOne U) c ≤ U ⊔ rightConjugate U b := by
    rw [hΩU, ← hUV]
    exact hXK
  obtain ⟨hH4, -⟩ := AschbacherTheorem3.lemma_4_5_five h45 (one_lt_pRank_U hloc hC d hT) hc hVS
    hVW
  rw [hΩU] at hH4
  have h4 := AschbacherTheorem3.lemma_4_5_four h45
  rw [← hUV, sup_inf_A_eq hC d hT hW] at h4
  refine ⟨c, hc, hcle, hXN, hXK, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x ⟨hxX, hxH⟩
    have hxSU : x ∈ (d.S ⊔ U) ⊓ Hg := ⟨hcle hxX, hxH⟩
    have hUHg : U ≤ Hg := EndHyp.U_le_L.trans (conj_factor_le a d.g)
    rw [sup_inf_eq_of_le EndHyp.U_le_normalizer_S hUHg] at hxSU
    have hxH4 : x ∈ (A ⊓ Hg) ⊔ U :=
      sup_le_sup_right (inf_le_inf_right Hg d.sylowS.le) U hxSU
    have : x ∈ rightConjugate U c ⊓ ((A ⊓ Hg) ⊔ U) := ⟨hxX, hxH4⟩
    rwa [hH4] at this
  · intro x hx v hv
    have hxΩ : x ∈ AschbacherTheorem3.omegaOne ((d.S ⊔ U) ⊓
        Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G)) := by
      refine AschbacherTheorem3.omegaOne_mono (le_inf hcle hXN) ?_
      rw [omegaOne_eq_self (isElemAbelian_rightConjugate hUel c)]
      exact hx
    have hv' : v ∈ AschbacherTheorem3.omegaOne V := by
      rw [omegaOne_eq_self (isElemAbelian_omegaOne hW)]
      exact hv
    have h5 := (h4 hv').2
    exact Subgroup.mem_centralizer_iff.mp h5 x hxΩ
