module

public import CFSG.ClassicalInvolution.AschTight.S1911FusF
public import CFSG.ClassicalInvolution.AschTight.S1911FusE

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

omit [IsSimpleGroup G] in
theorem mem_perfectCore (hd : Sec19Data p f K z S W) {a : G} {e₀ : ℕ} (hp2 : p ≠ 2)
    (hiso : Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
        ≃* SL(2, GaloisField p e₀))) :
    z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨ψ⟩ := hiso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
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

omit [IsSimpleGroup G] in
theorem inf_centralizer_le_normalizer_perfectCore (hd : Sec19Data p f K z S W) (a : G) :
    Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer
        ((perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G) := by
  have hNC := normalizer_eq_centralizer_of_tight hd.tight.toTightBranch
  refine le_trans ?_ (perfectResidualOf_normalizer_contains _)
  rintro c ⟨hcz, hca⟩
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := hNC ▸ hcz
  have hcA : c ∈ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) :
      Set G) := Subgroup.le_normalizer hca
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective]
  change conjSub c K ⊓ conjSub c (Subgroup.centralizer ({a} : Set G)) = _
  rw [conjSub_eq_of_mem_normalizer hcK, conjSub_eq_of_mem_normalizer hcA]

omit [IsSimpleGroup G] in
theorem isClassicalMember_perfectCore (hd : Sec19Data p f K z S W) {a : G} {e₀ : ℕ}
    (hp2 : p ≠ 2) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hiso : Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
        ≃* SL(2, GaloisField p e₀))) :
    IsClassicalMember p e₀ ((perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))).subgroupOf
      (Subgroup.centralizer ({a} : Set G))) ⟨z, hzA⟩ := by
  set Ka := perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) with hKa
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hKaA : Ka ≤ Subgroup.centralizer ({a} : Set G) := (perfectResidualOf_le _).trans inf_le_right
  have hKaK : Ka ≤ K := (perfectResidualOf_le _).trans inf_le_left
  have hzKa : z ∈ Ka := mem_perfectCore hd hp2 hiso
  have e₁ : Ka.subgroupOf (Subgroup.centralizer ({a} : Set G)) ≃* Ka :=
    Subgroup.subgroupOfEquivOfLe hKaA
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) :=
    le_centralizer_of_tight hd.tight.toTightBranch
  refine ⟨?_, Subgroup.mem_subgroupOf.mpr hzKa, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one
  · have := finite_perfectResidualOf_isPerfect (K ⊓ Subgroup.centralizer ({a} : Set G))
    exact Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  · set M := Subgroup.centralizer ({(⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G)))} :
      Set ↥(Subgroup.centralizer ({a} : Set G))) with hM
    have hle : Ka.subgroupOf (Subgroup.centralizer ({a} : Set G)) ≤ M := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [hM, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKz (hKaK hx)))
    refine IsSubnormal.step hle ?_ (IsSubnormal.refl M)
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun y hy => ?_
    have hyz : (y : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    have hyN := inf_centralizer_le_normalizer_perfectCore hd a ⟨hyz, y.2⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hyN x)
  · obtain ⟨ψ⟩ := hiso
    exact ⟨(QuotientGroup.congr _ _ e₁
      (CFSG.ComponentClassification.OddCore.equiv_invariant e₁)).trans ψ⟩

omit [IsSimpleGroup G] in
theorem card_centralizer_lt (hd : Sec19Data p f K z S W) {a : G}
    (haS : a ∈ (S : Subgroup G)) (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G)) < Nat.card G := by
  have hNC := normalizer_eq_centralizer_of_tight hd.tight.toTightBranch
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hNC ▸ hd.hSz haS
  have hne : Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
    intro htop
    apply haX
    refine Subgroup.mem_sup_right ⟨Subgroup.mem_top a, haN,
      mem_normalizer_oddCoreOf_of_mem_normalizer haN, fun l _ => ?_⟩
    have hl : l ∈ Subgroup.centralizer ({a} : Set G) := htop ▸ Subgroup.mem_top l
    have hla := Subgroup.mem_centralizer_singleton_iff.mp hl
    have h1 : ⁅a, l⁆ = 1 := by
      rw [commutatorElement_def, ← hla]
      group
    rw [h1]
    exact Subgroup.one_mem _
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({a} : Set G))
  have hidx : (Subgroup.centralizer ({a} : Set G)).index ≠ 1 := fun h1 =>
    hne (Subgroup.index_eq_one.mp h1)
  have hpos : 0 < Nat.card (Subgroup.centralizer ({a} : Set G)) := Nat.card_pos
  have hidx0 : (Subgroup.centralizer ({a} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : 2 ≤ (Subgroup.centralizer ({a} : Set G)).index := by omega
  nlinarith

theorem lieSystemMod_fieldInvolution (hF0 : FactF0) (hd : Sec19Data p f K z S W)
    (h9 : p ^ f ≠ 9) {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
      IsClassicalMember p e₀
        ((perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))).subgroupOf
          (Subgroup.centralizer ({a} : Set G))) ⟨z, hzA⟩ ∧
      LieSystemMod p e₀ (restrictFamily
        (conjFamily ((perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))).subgroupOf
          (Subgroup.centralizer ({a} : Set G))))
        (conjGen ((perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))).subgroupOf
          (Subgroup.centralizer ({a} : Set G))))) := by
  obtain ⟨e₀, hf, h5, hiso⟩ := exists_quotEquiv_perfectCore hF0 hd h9 haS ha2 haX
  have hzA : z ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz haS)).symm
  have hmem := isClassicalMember_perfectCore hd hd.tight.branch.odd hzA hiso
  exact ⟨e₀, hf, h5, hzA, hmem, lieSystemMod_restrict_conjugates hmem
    (card_centralizer_lt hd haS haX) (hd.ih e₀ h5)⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
