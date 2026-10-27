module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.Asc77.AscT3XCore
public import CFSG.ClassicalInvolution.Uniform.UMember

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3CII.T3R CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



open CFSG.ClassicalInvolution.Uniform

abbrev crossIn (K : Subgroup G) (a : G) :
    Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
  (K ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (Subgroup.centralizer ({a} : Set G))

theorem Std20.t9_fix [IsSimpleGroup G] (d : Std20 3 2 K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) :
    Nonempty (↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ⧸
      classicalInvolutionOddCore ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ≃*
        SL(2, GaloisField 3 1)) := by
  obtain ⟨hbN, -, e₀, eK, g, σ, hfe, hσ2, hσ1, -, hg⟩ := d.x_fieldData c9 h8 hb
  have he₀ : e₀ = 1 := by omega
  subst he₀
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hφ : ∀ x, semilinHom g σ (semilinHom g σ x) = x := by
    intro x
    have h2 : phiG K eK b * phiG K eK b = 1 := by
      rw [← phiG_mul hbN hbN, hb.sq, phiG_one]
    have := congrArg (fun φ : MulAut SL(2, GaloisField 3 2) => φ x) h2
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [← hg x, ← hg (phiG K eK b x)]
    exact this
  obtain ⟨φ⟩ := factF0 3 1 hp2 one_pos σ hσ1 hσ2 g hφ
  have hfix : slFix eK ⟨b, hbN⟩ = MonoidHom.eqLocus (semilinHom g σ)
      (MonoidHom.id SL(2, GaloisField 3 2)) := by
    ext x
    change slAut K eK ⟨b, hbN⟩ x = x ↔ _ = x
    have h1 : slAut K eK ⟨b, hbN⟩ x = phiG K eK b x := by
      rw [phiG_of_mem hbN]
      rfl
    rw [h1, hg x]
  let φ' : ↥(slFix eK ⟨b, hbN⟩) ≃* SL(2, GaloisField 3 1) :=
    (MulEquiv.subgroupCongr hfix).trans φ
  have hO : classicalInvolutionOddCore ↥(slFix eK ⟨b, hbN⟩) = ⊥ := by
    have h3 : Nat.card (GaloisField 3 1) = 3 := by
      rw [GaloisField.card 3 1 (by norm_num)]
      norm_num
    obtain ⟨e'⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three h3
    exact CFSG.ClassicalInvolution.Q3.oddCore_eq_bot_of_equiv (φ'.trans e')
      CFSG.ClassicalInvolution.Q3.componentOddCore_sl2Three
  let π : ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) →* ↥(slFix eK ⟨b, hbN⟩) :=
    ((slProj K eK).comp (Subgroup.inclusion inf_le_left)).codRestrict _ fun c => by
      change slAut K eK ⟨b, hbN⟩ (slProj K eK (Subgroup.inclusion inf_le_left c)) =
        slProj K eK (Subgroup.inclusion inf_le_left c)
      rw [slAut_slProj]
      congr 1
      apply Subtype.ext
      rw [normalizerConj_apply_coe]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
      change b * c * b⁻¹ = c
      rw [← hc]
      group
  have hπ : ∀ y, ((π y : ↥(slFix eK ⟨b, hbN⟩)) : SL(2, GaloisField 3 2)) =
      slProj K eK (Subgroup.inclusion inf_le_left y) := fun y => rfl
  have hsurj : Function.Surjective π := by
    rintro ⟨c, hc⟩
    obtain ⟨y, hyb, hyc⟩ := exists_mem_centralizer_of_slAut_eq eK hbN hb.sq hc
    exact ⟨⟨y, y.2, hyb⟩, Subtype.ext hyc⟩
  have hker : Odd (Nat.card π.ker) := by
    have hle : π.ker.map (K ⊓ Subgroup.centralizer ({b} : Set G)).subtype ≤ oddCoreOf K := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π x = 1 := hx
      have h1 := congrArg Subtype.val hx'
      rw [hπ] at h1
      exact (slProj_eq_one_iff eK _).mp h1
    have hcard : Nat.card (π.ker.map (K ⊓ Subgroup.centralizer ({b} : Set G)).subtype) =
        Nat.card π.ker :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv).symm
    rw [← hcard]
    exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  obtain ⟨ψ⟩ := nonempty_quotEquiv_of_surjective_of_odd _ hsurj hker hO
  exact ⟨ψ.trans φ'⟩


theorem t9_le_normalizer {a c : G} (hcK : c ∈ Subgroup.normalizer (K : Set G))
    (hca : c ∈ Subgroup.centralizer ({a} : Set G)) :
    c ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
  have hcA : c ∈ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) :
      Set G) := Subgroup.le_normalizer hca
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective]
  change conjSub c K ⊓ conjSub c (Subgroup.centralizer ({a} : Set G)) = _
  rw [conjSub_eq_of_mem_normalizer hcK, conjSub_eq_of_mem_normalizer hcA]

theorem Std20.t9_isClassicalMember [IsSimpleGroup G] (d : Std20 3 2 K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) (hzA : z ∈ Subgroup.centralizer ({b} : Set G)) :
    IsClassicalMemberU (.sl2 3 1) (crossIn K b) ⟨z, hzA⟩ := by
  obtain ⟨hiso⟩ := d.t9_fix c9 h8 hb
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set Ka := K ⊓ C with hKa
  have hI := d.viol.hzK
  have hKaA : Ka ≤ C := inf_le_right
  have hKaK : Ka ≤ K := inf_le_left
  have hzKa : z ∈ Ka := ⟨hI.mem, hzA⟩
  have e₁ : Ka.subgroupOf C ≃* Ka := Subgroup.subgroupOfEquivOfLe hKaA
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := fun k hk =>
    d.r10a_X_le_C (le_sec20X_left hk)
  refine ⟨⟨Nat.prime_three, by norm_num, by norm_num⟩, ?_, Subgroup.mem_subgroupOf.mpr hzKa, ?_, ?_,
    fun h => absurd (by norm_num : (3 : ℕ) ^ 1 = 3) h⟩
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one
  · set M := Subgroup.centralizer ({(⟨z, hzA⟩ : ↥C)} : Set ↥C) with hM
    set M₁ : Subgroup ↥C := M ⊓ (Subgroup.normalizer (K : Set G)).comap C.subtype with hM₁
    have hmemM : ∀ y : ↥C, y ∈ M ↔ (y : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      intro y
      rw [hM, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hle₁ : Ka.subgroupOf C ≤ M₁ := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      refine ⟨(hmemM x).mpr (hKz (hKaK hx)), ?_⟩
      exact Subgroup.le_normalizer (hKaK hx)
    have hle₂ : M₁ ≤ M := inf_le_left
    refine IsSubnormal.step hle₁ ?_ (IsSubnormal.step hle₂ ?_ (IsSubnormal.refl M))
    · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle₁).mpr fun y hy => ?_
      have hyK : (y : G) ∈ Subgroup.normalizer (K : Set G) := hy.2
      have hyN := t9_le_normalizer (a := b) hyK y.2
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp hyN x)
    · have hstep : ∀ y ∈ M, ∀ x ∈ M₁, y * x * y⁻¹ ∈ M₁ := by
        intro y hy x hx
        refine ⟨(M.mul_mem (M.mul_mem hy hx.1) (M.inv_mem hy)), ?_⟩
        have hxK : conjSub (x : G) K = K := mem_normalizer_iff_conjSub_eq.mp hx.2
        have := d.x_conj_normalizer ((hmemM y).mp hy) ((hmemM x).mp hx.1) hxK
        exact mem_normalizer_iff_conjSub_eq.mpr this
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle₂).mpr fun y hy => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hstep y hy x hx
      · intro hx
        have h1 := hstep y⁻¹ (M.inv_mem hy) _ hx
        have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
        rwa [e] at h1
  · exact ⟨inferInstance, ⟨(QuotientGroup.congr _ _ e₁
      (CFSG.ComponentClassification.OddCore.equiv_invariant e₁)).trans hiso⟩⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
