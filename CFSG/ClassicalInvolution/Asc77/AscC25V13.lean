module

public import CFSG.ClassicalInvolution.Asc77.AscC25V9
public import CFSG.ClassicalInvolution.AschTight.S1911F0c
public import CFSG.ClassicalInvolution.AschTight.S1911FusE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Gen

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem fs_fix_equiv (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      Nonempty (↥(slFix e ⟨b, hbN⟩) ≃* SL(2, GaloisField p e₀)) := by
  have hf : f ≠ 0 := (gf_facts hp hq).1
  have hσ2 : fieldChar hp hq e ⟨b, hbN⟩ * fieldChar hp hq e ⟨b, hbN⟩ = 1 := by
    have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set G)) * ⟨b, hbN⟩ = 1 := Subtype.ext hb2
    rw [← map_mul, h1, map_one]
  obtain ⟨e₀, hfe, hfrob⟩ := eq_frobenius_of_sq_eq_one hf hσ2 hσ1
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      rw [hfe] at hq
      simp at hq
    · exact h
  have h5 : 5 ≤ p ^ e₀ := by
    have h9' : p ^ (2 * e₀) ≠ 9 := hfe ▸ h9
    exact five_le_pow_of_ne_nine hp he₀ h9'
  refine ⟨e₀, hfe, h5, ?_⟩
  obtain ⟨g, hg⟩ := exists_semilinHom_of_mem e (gf_facts hp hq).2.1 (gf_facts hp hq).2.2.1
    (gf_facts hp hq).2.2.2 ⟨b, hbN⟩
  have hg' : ∀ x, slAut K e ⟨b, hbN⟩ x = semilinHom g (fieldChar hp hq e ⟨b, hbN⟩) x := hg
  have hφ : ∀ x, semilinHom g (fieldChar hp hq e ⟨b, hbN⟩)
      (semilinHom g (fieldChar hp hq e ⟨b, hbN⟩) x) = x := by
    intro x
    have h1 := slAut_slAut_of_mul_self e ⟨b, hbN⟩ hb2 x
    rw [← hg' x, ← hg' (slAut K e ⟨b, hbN⟩ x)]
    exact h1
  have hfix : ∀ x, slAut K e ⟨b, hbN⟩ x = x ↔
      semilinHom g (fieldChar hp hq e ⟨b, hbN⟩) x = x := fun x => by
    rw [hg' x]
  subst hfe
  obtain ⟨φ⟩ := factF0 p e₀ hp he₀ (fieldChar hp hq e ⟨b, hbN⟩) hσ1 hσ2 g hφ
  have hfixeq : slFix e ⟨b, hbN⟩ = MonoidHom.eqLocus
      (semilinHom g (fieldChar hp hq e ⟨b, hbN⟩))
      (MonoidHom.id SL(2, GaloisField p (2 * e₀))) := by
    ext x
    exact hfix x
  exact ⟨(MulEquiv.subgroupCongr hfixeq).trans φ⟩

theorem fs_exists_quotEquiv (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
        classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)))
          ≃* SL(2, GaloisField p e₀)) := by
  obtain ⟨e₀, hfe, h5, ⟨φ'⟩⟩ := fs_fix_equiv hp hq h9 e hbN hb2 hσ1
  refine ⟨e₀, hfe, h5, ?_⟩
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      simp at h5
    · exact h
  have hcardm : Nat.card (GaloisField p e₀) = p ^ e₀ := GaloisField.card p e₀ he₀.ne'
  have : Fintype (GaloisField p e₀) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField p e₀), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField p e₀))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardm]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect SL(2, GaloisField p e₀) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField p e₀) (n := 2) le_rfl (Or.inr h4)
  have hperf : Group.IsPerfect ↥(slFix e ⟨b, hbN⟩) :=
    Group.IsPerfect.ofSurjective (f := φ'.symm.toMonoidHom) φ'.symm.surjective
  have h2ne : (2 : GaloisField p e₀) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p e₀) p]; exact hp)
  have hO : classicalInvolutionOddCore ↥(slFix e ⟨b, hbN⟩) = ⊥ := by
    have h1 : (classicalInvolutionOddCore SL(2, GaloisField p e₀)).map φ'.symm.toMonoidHom =
        classicalInvolutionOddCore ↥(slFix e ⟨b, hbN⟩) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant φ'.symm
    rw [ModelFacts.LinearAut.oddCore_sl2_eq_bot h2ne (by rw [hcardm]; omega),
      Subgroup.map_bot] at h1
    exact h1.symm
  obtain ⟨ψ⟩ := nonempty_quotEquiv_perfectResidualOf e hbN hb2 hperf hO
  exact ⟨ψ.trans φ'⟩

theorem fs_mem_perfectCore {K : Subgroup G} {z : G} (hI : IsUniqueInvolution K z) {a : G}
    {e₀ : ℕ} (hp2 : p ≠ 2)
    (hiso : Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
        ≃* SL(2, GaloisField p e₀))) :
    z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨ψ⟩ := hiso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2ne : (2 : GaloisField p e₀) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p e₀) p]; exact hp2)
  have hneg : orderOf (-1 : SL(2, GaloisField p e₀)) = 2 := by
    apply orderOf_eq_prime
    · rw [sq, neg_one_mul, neg_neg]
    · intro h
      have h1 := congrArg
        (fun b : SL(2, GaloisField p e₀) =>
          (↑b : Matrix (Fin 2) (Fin 2) (GaloisField p e₀)) 0 0) h
      simp at h1
      apply h2ne
      linear_combination -h1
  have h2SL : 2 ∣ Nat.card SL(2, GaloisField p e₀) := by
    have := orderOf_dvd_natCard (-1 : SL(2, GaloisField p e₀))
    rwa [hneg] at this
  have h2Q : 2 ∣ Nat.card (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
      classicalInvolutionOddCore
        ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))) := by
    rw [Nat.card_congr ψ.toEquiv]
    exact h2SL
  have h2 : 2 ∣ Nat.card ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :=
    h2Q.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxK : (x : G) ∈ K := (perfectResidualOf_le _ x.2).1
  have hx2 : (x : G) * x = 1 := by
    have h1 := pow_orderOf_eq_one x
    rw [hx, sq] at h1
    exact congrArg Subtype.val h1
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  rcases hI.unique _ hxK hx2 with h | h
  · exact absurd h hx1
  · rw [← h]
    exact x.2

theorem fs_le_normalizer {K : Subgroup G} {a c : G} (hcK : c ∈ Subgroup.normalizer (K : Set G))
    (hca : c ∈ Subgroup.centralizer ({a} : Set G)) :
    c ∈ Subgroup.normalizer
      ((perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G) := by
  refine perfectResidualOf_normalizer_contains _ ?_
  have hcA : c ∈ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) :
      Set G) := Subgroup.le_normalizer hca
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective]
  change conjSub c K ⊓ conjSub c (Subgroup.centralizer ({a} : Set G)) = _
  rw [conjSub_eq_of_mem_normalizer hcK, conjSub_eq_of_mem_normalizer hcA]

theorem fs_isClassicalMember {K : Subgroup G} {z : G} (hI : IsUniqueInvolution K z)
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hconj : ∀ y x : G, y ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ Subgroup.centralizer ({z} : Set G) → conjSub x K = K → conjSub (y * x * y⁻¹) K = K)
    {b : G} {e₀ : ℕ} (hp2 : p ≠ 2) (hzA : z ∈ Subgroup.centralizer ({b} : Set G))
    (hiso : Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)))
        ≃* SL(2, GaloisField p e₀))) :
    IsClassicalMember p e₀ ((perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))).subgroupOf
      (Subgroup.centralizer ({b} : Set G))) ⟨z, hzA⟩ := by
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set Ka := perfectResidualOf (K ⊓ C) with hKa
  have hKaA : Ka ≤ C := (perfectResidualOf_le _).trans inf_le_right
  have hKaK : Ka ≤ K := (perfectResidualOf_le _).trans inf_le_left
  have hzKa : z ∈ Ka := fs_mem_perfectCore hI hp2 hiso
  have e₁ : Ka.subgroupOf C ≃* Ka := Subgroup.subgroupOfEquivOfLe hKaA
  refine ⟨?_, Subgroup.mem_subgroupOf.mpr hzKa, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one
  · have := finite_perfectResidualOf_isPerfect (K ⊓ C)
    exact Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
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
      have hyN := fs_le_normalizer (a := b) hyK y.2
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp hyN x)
    · have hstep : ∀ y ∈ M, ∀ x ∈ M₁, y * x * y⁻¹ ∈ M₁ := by
        intro y hy x hx
        refine ⟨(M.mul_mem (M.mul_mem hy hx.1) (M.inv_mem hy)), ?_⟩
        have hxK : conjSub (x : G) K = K := mem_normalizer_iff_conjSub_eq.mp hx.2
        have := hconj (y : G) (x : G) ((hmemM y).mp hy) ((hmemM x).mp hx.1) hxK
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
  · obtain ⟨ψ⟩ := hiso
    exact ⟨(QuotientGroup.congr _ _ e₁
      (CFSG.ComponentClassification.OddCore.equiv_invariant e₁)).trans ψ⟩

theorem fs_card_centralizer_lt [IsSimpleGroup G] (hnc : ∃ x y : G, x * y ≠ y * x)
    {b : G} (hb1 : b ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G)) < Nat.card G := by
  have hne : Subgroup.centralizer ({b} : Set G) ≠ ⊤ := by
    intro htop
    have hb : b ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Subgroup.centralizer ({b} : Set G) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hb
      exact hb1 hb
    · obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hx : x ∈ Subgroup.center G := h ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({b} : Set G))
  have hidx : (Subgroup.centralizer ({b} : Set G)).index ≠ 1 := fun h1 =>
    hne (Subgroup.index_eq_one.mp h1)
  have hpos : 0 < Nat.card (Subgroup.centralizer ({b} : Set G)) := Nat.card_pos
  have hidx0 : (Subgroup.centralizer ({b} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : 2 ≤ (Subgroup.centralizer ({b} : Set G)).index := by omega
  nlinarith

end Gen

end CFSG.ClassicalInvolution.Asc77.C25V
