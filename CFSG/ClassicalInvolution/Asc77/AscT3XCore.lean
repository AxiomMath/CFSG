module

public import CFSG.ClassicalInvolution.Asc77.AscT3XFld
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC7
public import CFSG.ClassicalInvolution.Asc77.AscT3R10aMain
public import CFSG.ClassicalInvolution.AschTight.S1911F0c
public import CFSG.ClassicalInvolution.AschTight.S1911FusE
public import CFSG.ClassicalInvolution.AschTight.S1911SecA

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


theorem Std20.x_exists_quotEquiv_perfectCore (d : Std20 p f K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) (h9 : p ^ f ≠ 9) {b : G}
    (hb : FieldInv20 S K K' W z t b) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
        classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)))
          ≃* SL(2, GaloisField p e₀)) := by
  obtain ⟨hbN, -, e₀, eK, g, σ, hfe, hσ2, hσ1, -, hg⟩ := d.x_fieldData c9 h8 hb
  have hp2 : p ≠ 2 := d.branch.odd
  have hq := d.branch.five
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      rw [hfe] at hq
      simp at hq
    · exact h
  have h5 : 5 ≤ p ^ e₀ := by
    have h9' : p ^ (2 * e₀) ≠ 9 := hfe ▸ h9
    exact five_le_pow_of_ne_nine hp2 he₀ h9'
  refine ⟨e₀, hfe, h5, ?_⟩
  subst hfe
  have hφ : ∀ x, semilinHom g σ (semilinHom g σ x) = x := by
    intro x
    have h2 : phiG K eK b * phiG K eK b = 1 := by
      rw [← phiG_mul hbN hbN, hb.sq, phiG_one]
    have := congrArg (fun φ : MulAut SL(2, GaloisField p (2 * e₀)) => φ x) h2
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [← hg x, ← hg (phiG K eK b x)]
    exact this
  obtain ⟨φ⟩ := factF0 p e₀ hp2 he₀ σ hσ1 hσ2 g hφ
  have hfix : slFix eK ⟨b, hbN⟩ = MonoidHom.eqLocus (semilinHom g σ)
      (MonoidHom.id SL(2, GaloisField p (2 * e₀))) := by
    ext x
    change slAut K eK ⟨b, hbN⟩ x = x ↔ _ = x
    have h1 : slAut K eK ⟨b, hbN⟩ x = phiG K eK b x := by
      rw [phiG_of_mem hbN]
      rfl
    rw [h1, hg x]
  let φ' : ↥(slFix eK ⟨b, hbN⟩) ≃* SL(2, GaloisField p e₀) :=
    (MulEquiv.subgroupCongr hfix).trans φ
  have hcardm : Nat.card (GaloisField p e₀) = p ^ e₀ := GaloisField.card p e₀ he₀.ne'
  have : Fintype (GaloisField p e₀) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField p e₀), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField p e₀))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardm]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect SL(2, GaloisField p e₀) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField p e₀) (n := 2) le_rfl (Or.inr h4)
  have hperf : Group.IsPerfect ↥(slFix eK ⟨b, hbN⟩) :=
    Group.IsPerfect.ofSurjective (f := φ'.symm.toMonoidHom) φ'.symm.surjective
  have h2ne : (2 : GaloisField p e₀) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p e₀) p]; exact hp2)
  have hO : classicalInvolutionOddCore ↥(slFix eK ⟨b, hbN⟩) = ⊥ := by
    have h1 : (classicalInvolutionOddCore SL(2, GaloisField p e₀)).map φ'.symm.toMonoidHom =
        classicalInvolutionOddCore ↥(slFix eK ⟨b, hbN⟩) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant φ'.symm
    rw [ModelFacts.LinearAut.oddCore_sl2_eq_bot h2ne (by rw [hcardm]; omega),
      Subgroup.map_bot] at h1
    exact h1.symm
  obtain ⟨ψ⟩ := nonempty_quotEquiv_perfectResidualOf eK hbN hb.sq hperf hO
  exact ⟨ψ.trans φ'⟩

theorem x_mem_perfectCore_of_iso (hI : IsUniqueInvolution K z) {a : G} {e₀ : ℕ}
    (hp2 : p ≠ 2)
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
        (fun b : SL(2, GaloisField p e₀) => (↑b : Matrix (Fin 2) (Fin 2) (GaloisField p e₀)) 0 0) h
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

theorem Std20.x_conj_normalizer (d : Std20 p f K K' J S R R' W V z t) {y x : G}
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (hx : x ∈ Subgroup.centralizer ({z} : Set G))
    (hxK : conjSub x K = K) : conjSub (y * x * y⁻¹) K = K := by
  have hyi : y⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hy
  have hxK' : conjSub x K' = K' := (d.late_conj_iff hx).mp hxK
  have e1 : conjSub (y * x * y⁻¹) K = conjSub y (conjSub x (conjSub y⁻¹ K)) := by
    rw [conjSub_mul, conjSub_mul]
  rcases d.late_conj_K hyi with h | h
  · rw [e1, h, hxK]
    have h1 := congrArg (conjSub y) h
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
    exact h1.symm
  · rw [e1, h, hxK']
    have h1 := congrArg (conjSub y) h
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
    exact h1.symm

theorem x_le_normalizer_perfectCore {a c : G} (hcK : c ∈ Subgroup.normalizer (K : Set G))
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

theorem Std20.x_isClassicalMember_perfectCore (d : Std20 p f K K' J S R R' W V z t) {b : G}
    {e₀ : ℕ} (hp2 : p ≠ 2) (hzA : z ∈ Subgroup.centralizer ({b} : Set G))
    (hiso : Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)))
        ≃* SL(2, GaloisField p e₀))) :
    IsClassicalMember p e₀ ((perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))).subgroupOf
      (Subgroup.centralizer ({b} : Set G))) ⟨z, hzA⟩ := by
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set Ka := perfectResidualOf (K ⊓ C) with hKa
  have hI := d.viol.hzK
  have hKaA : Ka ≤ C := (perfectResidualOf_le _).trans inf_le_right
  have hKaK : Ka ≤ K := (perfectResidualOf_le _).trans inf_le_left
  have hzKa : z ∈ Ka := x_mem_perfectCore_of_iso hI hp2 hiso
  have e₁ : Ka.subgroupOf C ≃* Ka := Subgroup.subgroupOfEquivOfLe hKaA
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := fun k hk =>
    d.r10a_X_le_C (le_sec20X_left hk)
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
      have hyN := x_le_normalizer_perfectCore (a := b) hyK y.2
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
  · obtain ⟨ψ⟩ := hiso
    exact ⟨(QuotientGroup.congr _ _ e₁
      (CFSG.ComponentClassification.OddCore.equiv_invariant e₁)).trans ψ⟩

theorem Std20.x_nonabelian (d : Std20 p f K K' J S R R' W V z t) :
    ∃ x y : G, x * y ≠ y * x := by
  obtain ⟨b, -, hbK⟩ := d.late_exists_swap
  by_contra hcon
  push Not at hcon
  apply d.ne
  have h3 : conjSub b K = K := by
    ext x
    rw [mem_conjSub_iff]
    have : b⁻¹ * x * b = x := by
      rw [mul_assoc, hcon x b, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
  exact hbK.symm.trans h3

theorem Std20.x_card_centralizer_lt [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    {b : G} (hbX : b ∉ sec20X (CoreAssembly.conjClass K) z K K') :
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
      exact hbX (hb ▸ Subgroup.one_mem _)
    · obtain ⟨x, y, hxy⟩ := d.x_nonabelian
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

theorem Std20.x_sectionData [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) (h9 : p ^ f ≠ 9) {b : G}
    (hb : FieldInv20 S K K' W z t b) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({b} : Set G),
      IsClassicalMember p e₀ (perfectCoreIn K b) ⟨z, hzA⟩ ∧
      Nat.card ↥(Subgroup.centralizer ({b} : Set G)) < Nat.card G ∧
      CITBelowU p e₀ (Nat.card G) := by
  obtain ⟨e₀, hfe, h5, hiso⟩ := d.x_exists_quotEquiv_perfectCore c9 h8 h9 hb
  have hzA : z ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hb.mem)).symm
  exact ⟨e₀, hfe, h5, hzA, d.x_isClassicalMember_perfectCore d.branch.odd hzA hiso,
    d.x_card_centralizer_lt hb.not_mem_X, d.below e₀ h5⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
