module

public import CFSG.ClassicalInvolution.Q3.Q3T6XCore
public import CFSG.ClassicalInvolution.Q3.Q3T6YFinal
public import CFSG.ClassicalInvolution.Q3.Q3T6LinMember
public import CFSG.ClassicalInvolution.Q3.TL3C6
public import CFSG.ClassicalInvolution.SolvableCase.Tight
public import CFSG.ClassicalInvolution.Q3.TL4SepDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
  CFSG.ClassicalInvolution.Q3.Q3T6X CFSG.ClassicalInvolution.Q3.TL4
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

section OmegaFamily

theorem omega4_of_mem3 {K J : Subgroup X} {z₁ z₂ : X} (h₁ : Mem3 K z₁) (h₂ : Mem3 J z₂)
    (hne : K ≠ J) :
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J) := by
  by_cases h2 : 2 ∣ Nat.card ↥(K ⊓ J)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hu' : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    have hu1 : (u : X) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hu'
      omega
    have huu : (u : X) * u = 1 := by rw [← sq, ← hu', pow_orderOf_eq_one]
    have ha := (h₁.isUniqueInvolution.unique u (Subgroup.mem_inf.mp u.2).1 huu).resolve_left hu1
    have hb := (h₂.isUniqueInvolution.unique u (Subgroup.mem_inf.mp u.2).2 huu).resolve_left hu1
    have h₂' : Mem3 J z₁ := by rw [← ha, hb]; exact h₂
    obtain ⟨-, -, hcomm⟩ := h₁.twin_facts h₂' hne
    exact ⟨padicValNat_card_inf_le_one_of_commutator (hcomm.trans inf_le_left)
      h₁.member.natCard_center_eq_two, fun _ => hcomm⟩
  · rw [padicValNat.eq_zero_of_not_dvd h2]
    exact ⟨Nat.zero_le _, fun h => absurd h (by norm_num)⟩

end OmegaFamily

section Omega5

theorem omega5_of_mem3 {K J : Subgroup X} {z t : X} (hK : Mem3 K z) (hJ : Mem3 J t)
    {v : X} (hvJ : v ∈ J) (hvnc : ¬ ∀ w ∈ J, v * w = w * v)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * z = z * v) :
    v ∈ Subgroup.normalizer (K : Set X) := by
  have h := fusion3MinOn_of_min (Set.univ : Set X) (Q3T6Y.fusion3Min_all X)
  have hS : ∀ x ∈ (Set.univ : Set X), ∀ g : X, g * x * g⁻¹ ∈ (Set.univ : Set X) :=
    fun _ _ _ => Set.mem_univ _
  have hv4 : v ^ 4 = 1 := hJ.pow_four_of_isPGroup hvJ hv2
  have hdvd : orderOf v ∣ 4 := orderOf_dvd_of_pow_eq_one hv4
  have hcases : orderOf v = 1 ∨ orderOf v = 2 ∨ orderOf v = 4 := by
    obtain ⟨i, hi, hi'⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf v ∣ 2 ^ 2 by simpa using hdvd)
    interval_cases i
    · left; simpa using hi'
    · right; left; simpa using hi'
    · right; right; simpa using hi'
  rcases hcases with h1 | h2 | h4
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · exfalso
    have hsq : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [h2, pow_two] at this
    apply hvnc
    intro w hw
    rcases hJ.isUniqueInvolution.unique v hvJ hsq with h' | h'
    · rw [h']; simp
    · rw [h']; exact (hJ.mul_comm_of_mem hw).symm
  · have hv4' : orderOf v = 4 := h4
    have htK : t ∈ Subgroup.normalizer (K : Set X) :=
      bstar_of_min h.diagNorm hJ hK (Set.mem_univ _) (Set.mem_univ _) hvJ hv4' hvz
    exact mem_normalizer_of_core_min hS h hJ hK (Set.mem_univ _) (Set.mem_univ _) htK hvJ hv2 hvz

end Omega5

section OmegaFam

theorem hypOmegaModU_of_mem3Family {Λ : Set (Subgroup X)} (hc : ConjInvariant Λ)
    (hm : ∀ M ∈ Λ, ∃ z, Mem3 M z) : HypOmegaModU (.sl2 3 1) Λ where
  conjInvariant := hc
  classical := fun L hL => by
    obtain ⟨z, h⟩ := hm L hL
    exact ⟨z, h.member⟩
  omega4 := fun K hK J hJ hne => by
    obtain ⟨z₁, h₁⟩ := hm K hK
    obtain ⟨z₂, h₂⟩ := hm J hJ
    exact omega4_of_mem3 h₁ h₂ hne
  omega5 := fun K hK J hJ _ z hz v hvJ hvnc hv2 hvz => by
    obtain ⟨z₁, h₁⟩ := hm K hK
    obtain ⟨z₂, h₂⟩ := hm J hJ
    have hzz : z₁ = z := h₁.isUniqueInvolution.eq hz
    subst hzz
    exact omega5_of_mem3 h₁ h₂ hvJ hvnc hv2 hvz

end OmegaFam

theorem natCard_quaternionGroup_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem eight_dvd_natCard_of_not_isMulCommutative {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (h : ¬ IsMulCommutative P) : 8 ∣ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  by_contra h8
  have hk2 : k < 3 := by
    by_contra hk3
    exact h8 (hk ▸ (pow_dvd_pow 2 (by omega) : 2 ^ 3 ∣ 2 ^ k))
  interval_cases k
  · have hu : Subsingleton P := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    exact h ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Fact (Nat.Prime (Nat.card P)) := ⟨by rw [hk]; exact Nat.prime_two⟩
    have := isCyclic_of_prime_card (α := P) (p := Nat.card P) rfl
    exact h inferInstance
  · exact h (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hk))

section Lift

structure IsLiftOf (J L : Subgroup X) (u : X) : Prop where
  inv : IsUniqueInvolution J u
  le : J ≤ L
  member : IsClassicalMember3 L u

@[expose] def HasLifts (Δ : Set (Subgroup X)) : Prop :=
  ∀ J ∈ Δ, ∃ (L : Subgroup X) (u : X), IsLiftOf J L u

@[expose] def liftFam (Δ : Set (Subgroup X)) : Set (Subgroup X) :=
  {M | ∃ J ∈ Δ, ∃ (L : Subgroup X) (u : X), IsLiftOf J L u ∧ M = satU (.sl2 3 1) L u}

variable {Δ : Set (Subgroup X)} {J L : Subgroup X} {u : X}

theorem IsLiftOf.conj (h : IsLiftOf J L u) (g : X) :
    IsLiftOf (conjSub g J) (conjSub g L) (g * u * g⁻¹) :=
  ⟨h.inv.conj g, conjSub_mono h.le, h.member.conj g⟩

theorem IsLiftOf.mem3 (h : IsLiftOf J L u) : Mem3 (satU (.sl2 3 1) L u) u :=
  ⟨(IsClassicalMemberU.ofQ3 h.member).satU_member, isIntrinsicU_satU _ _ _⟩

theorem IsLiftOf.le_sat (h : IsLiftOf J L u) : J ≤ satU (.sl2 3 1) L u :=
  h.le.trans le_satU

theorem IsLiftOf.member_sat (h : IsLiftOf J L u) : IsClassicalMember3 (satU (.sl2 3 1) L u) u :=
  h.mem3.member.toQ3 (by norm_num)

theorem satU_mem_liftFam (hJ : J ∈ Δ) (h : IsLiftOf J L u) :
    satU (.sl2 3 1) L u ∈ liftFam Δ := ⟨J, hJ, L, u, h, rfl⟩

theorem liftFam_mem3 {M : Subgroup X} (hM : M ∈ liftFam Δ) : ∃ z, Mem3 M z := by
  obtain ⟨J, -, L, u, h, rfl⟩ := hM
  exact ⟨u, h.mem3⟩

theorem conjInvariant_liftFam (hΔ : ConjInvariant Δ) : ConjInvariant (liftFam Δ) := by
  rintro n _ ⟨J, hJ, L, u, h, rfl⟩
  refine ⟨conjSub n J, hΔ n J hJ, conjSub n L, n * u * n⁻¹, h.conj n, ?_⟩
  rw [satU_conj]

end Lift

section LiftOmega

variable {Δ : Set (Subgroup X)}

theorem hypOmegaModU_liftFam (hΔ : ConjInvariant Δ) :
    HypOmegaModU (.sl2 3 1) (liftFam Δ) :=
  hypOmegaModU_of_mem3Family (conjInvariant_liftFam hΔ) fun _ hM => liftFam_mem3 hM

end LiftOmega

section LiftUnique

variable {Δ : Set (Subgroup X)} {J M M' : Subgroup X}

theorem exists_eight_dvd_of_mem (hΩ : HypOmegaGen Δ) (hJ : J ∈ Δ) :
    ∃ P : Subgroup X, P ≤ J ∧ IsPGroup 2 P ∧ 8 ∣ Nat.card P := by
  obtain ⟨P, hP, hnc⟩ := (hΩ.omega1 J hJ).2
  exact ⟨P, hP.1, hP.2.1, eight_dvd_natCard_of_not_isMulCommutative hP.2.1 hnc⟩

theorem liftFam_eq_of_le (hΩ : HypOmegaGen Δ) (hM : M ∈ liftFam Δ) (hM' : M' ∈ liftFam Δ)
    (hJ : J ∈ Δ) (h : J ≤ M) (h' : J ≤ M') : M = M' := by
  by_contra hne
  obtain ⟨z₁, h₁⟩ := liftFam_mem3 hM
  obtain ⟨z₂, h₂⟩ := liftFam_mem3 hM'
  have h4 := (omega4_of_mem3 h₁ h₂ hne).1
  obtain ⟨P, hPJ, -, h8⟩ := exists_eight_dvd_of_mem hΩ hJ
  have hdvd : 8 ∣ Nat.card ↥(M ⊓ M') :=
    h8.trans (Subgroup.card_dvd_of_le (le_inf (hPJ.trans h) (hPJ.trans h')))
  have hpos : Nat.card ↥(M ⊓ M') ≠ 0 := Nat.card_pos.ne'
  have := (padicValNat_dvd_iff_le (p := 2) (n := 3) hpos).mp (by simpa using hdvd)
  omega

theorem normalizer_le_of_le_liftFam (hΩ : HypOmegaGen Δ) (hM : M ∈ liftFam Δ) (hJ : J ∈ Δ)
    (h : J ≤ M) : Subgroup.normalizer (J : Set X) ≤ Subgroup.normalizer (M : Set X) := by
  intro n hn
  apply mem_normalizer_of_conjSub_eq
  have hMn : conjSub n M ∈ liftFam Δ := conjInvariant_liftFam hΩ.conjInvariant n M hM
  have hJn : conjSub n J = J := conjSub_eq_of_mem_normalizer hn
  exact liftFam_eq_of_le hΩ hMn hM hJ (hJn ▸ conjSub_mono h) h

theorem natCard_of_isSylow2In_classicalMember3 {z : X} (h : IsClassicalMember3 M z)
    {Q : Subgroup X} (hQ : IsSylow2In Q M) : Nat.card Q = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  obtain ⟨e⟩ := Q3T6.quaternion_sylow_of_isClassicalMember3 h P
  rw [hQ.natCard_eq (isSylow2In_map_subtype M P), Subgroup.card_map_of_injective M.subtype_injective,
    Nat.card_congr e.toEquiv, natCard_quaternionGroup_two]

theorem isSylow2In_of_le_liftFam (hΩ : HypOmegaGen Δ) (hJ : J ∈ Δ) (hJ2 : IsPGroup 2 J)
    (hM : M ∈ liftFam Δ) (h : J ≤ M) : IsSylow2In J M := by
  obtain ⟨z, hz⟩ := liftFam_mem3 hM
  have hm : IsClassicalMember3 M z := hz.member.toQ3 (by norm_num)
  obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge hJ2 h
  have h1 := natCard_of_isSylow2In_classicalMember3 hm hQ
  obtain ⟨P, hPJ, -, h8⟩ := exists_eight_dvd_of_mem hΩ hJ
  have : 8 ≤ Nat.card J :=
    (Nat.le_of_dvd Nat.card_pos h8).trans (Subgroup.card_le_of_le hPJ)
  exact hQ.of_natCard_le hJ2 h (by omega)

end LiftUnique

section LiftClass

variable {Δ : Set (Subgroup X)}

theorem inClass3_liftFam (hΔ : ConjInvariant Δ) (hne : Δ.Nonempty) (hl : HasLifts Δ)
    (hgen : (⨆ J ∈ Δ, J) = ⊤) : InClass3 (liftFam Δ) where
  nonempty := by
    obtain ⟨J, hJ⟩ := hne
    obtain ⟨L, u, h⟩ := hl J hJ
    exact ⟨_, satU_mem_liftFam hJ h⟩
  conjInvariant := conjInvariant_liftFam hΔ
  generated := by
    refine eq_top_iff.mpr (hgen.symm.le.trans (iSup₂_le fun J hJ => ?_))
    obtain ⟨L, u, h⟩ := hl J hJ
    exact h.le_sat.trans (le_iSup₂ (f := fun (M : Subgroup X) (_ : M ∈ liftFam Δ) => M) _
      (satU_mem_liftFam hJ h))
  classical := by
    rintro M ⟨J, -, L, u, h, rfl⟩
    exact ⟨u, h.member_sat⟩

end LiftClass

section Exact

variable {Δ : Set (Subgroup X)} {J J' M M' : Subgroup X}

@[expose] def ExactSylow (Δ : Set (Subgroup X)) : Prop :=
  ∀ M ∈ liftFam Δ, ∀ P Q : Subgroup X, IsSylow2In P M → IsSylow2In Q M → P = Q

theorem exists_core_of_mem_liftFam (hM : M ∈ liftFam Δ) : ∃ J ∈ Δ, J ≤ M := by
  obtain ⟨J, hJ, L, u, h, rfl⟩ := hM
  exact ⟨J, hJ, h.le_sat⟩

theorem ExactSylow.core_unique (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hex : ExactSylow Δ) (hM : M ∈ liftFam Δ) (hJ : J ∈ Δ) (hJ' : J' ∈ Δ) (h : J ≤ M)
    (h' : J' ≤ M) : J = J' :=
  hex M hM J J' (isSylow2In_of_le_liftFam hΩ hJ (h2 J hJ) hM h)
    (isSylow2In_of_le_liftFam hΩ hJ' (h2 J' hJ') hM h')

theorem ExactSylow.le_core (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hex : ExactSylow Δ) (hM : M ∈ liftFam Δ) (hJ : J ∈ Δ) (h : J ≤ M) {V : Subgroup X}
    (hV : IsPGroup 2 V) (hVM : V ≤ M) : V ≤ J := by
  obtain ⟨Q, hQ, hVQ⟩ := IsSylow2In.exists_ge hV hVM
  rw [hex M hM J Q (isSylow2In_of_le_liftFam hΩ hJ (h2 J hJ) hM h) hQ]
  exact hVQ

theorem ExactSylow.normalizer_eq (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hex : ExactSylow Δ) (hM : M ∈ liftFam Δ) (hJ : J ∈ Δ) (h : J ≤ M) :
    Subgroup.normalizer (M : Set X) = Subgroup.normalizer (J : Set X) := by
  refine le_antisymm (fun n hn => ?_) (normalizer_le_of_le_liftFam hΩ hM hJ h)
  apply mem_normalizer_of_conjSub_eq
  have hs : IsSylow2In (conjSub n J) M := by
    have := (isSylow2In_of_le_liftFam hΩ hJ (h2 J hJ) hM h).conj n
    rwa [conjSub_eq_of_mem_normalizer hn] at this
  exact hex M hM _ _ hs (isSylow2In_of_le_liftFam hΩ hJ (h2 J hJ) hM h)

end Exact

section Dictionary

variable {Δ : Set (Subgroup X)} {J J' M M' : Subgroup X}

theorem rSet_eq_of_isPGroup (h2 : ∀ J ∈ Δ, IsPGroup 2 J) : RSet Δ = Δ := by
  ext R
  constructor
  · intro hR
    obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
    have : J = R := hRJ.2.2 J le_rfl (h2 J hJ) hRJ.1
    rwa [← this]
  · intro hR
    exact TC.mem_RSet_of_isPGroup hR (h2 R hR)

theorem ExactSylow.rSet_liftFam (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hex : ExactSylow Δ) : RSet (liftFam Δ) = Δ := by
  ext R
  constructor
  · intro hR
    obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR
    obtain ⟨J, hJ, hJM⟩ := exists_core_of_mem_liftFam hM
    have := hex M hM R J hRM (isSylow2In_of_le_liftFam hΩ hJ (h2 J hJ) hM hJM)
    rwa [this]
  · intro hR
    obtain ⟨L, u, h⟩ := hl R hR
    exact mem_RSet_of_isSylow2In (satU_mem_liftFam hR h)
      (isSylow2In_of_le_liftFam hΩ hR (h2 R hR) (satU_mem_liftFam hR h) h.le_sat)

theorem ExactSylow.uSet_liftFam (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hex : ExactSylow Δ) : USet (liftFam Δ) = USet Δ := by
  unfold USet
  rw [hex.rSet_liftFam hΩ h2 hl, rSet_eq_of_isPGroup h2]

theorem isPGroup_of_mem_USet (h2 : ∀ J ∈ Δ, IsPGroup 2 J) {U : Subgroup X} (hU : U ∈ USet Δ) :
    IsPGroup 2 U := by
  obtain ⟨R, hR, hUR, -⟩ := hU
  rw [rSet_eq_of_isPGroup h2] at hR
  exact (h2 R hR).to_le hUR

theorem ExactSylow.mem_omegaNbr_liftFam_iff (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hex : ExactSylow Δ) (hM : M ∈ liftFam Δ) (hJ : J ∈ Δ) (hJM : J ≤ M)
    (hM' : M' ∈ liftFam Δ) (hJ' : J' ∈ Δ) (hJM' : J' ≤ M') :
    M' ∈ omegaNbr (liftFam Δ) M ↔ J' ∈ omegaNbr Δ J := by
  rw [TC.mem_omegaNbr_iff hΩ h2, omegaNbr, Set.mem_ofPred_eq,
    hex.rSet_liftFam hΩ h2 hl, hex.normalizer_eq hΩ h2 hM hJ hJM]
  constructor
  · rintro ⟨-, hne, R, hR, hRM', hRN⟩
    have hRJ' : R = J' :=
      hex.core_unique hΩ h2 hM' hR hJ' hRM' hJM'
    subst hRJ'
    refine ⟨hJ', fun h => hne ?_, hRN⟩
    subst h
    exact liftFam_eq_of_le hΩ hM' hM hJ hJM' hJM
  · rintro ⟨-, hne, hN⟩
    refine ⟨hM', fun h => hne ?_, J', hJ', hJM', hN⟩
    subst h
    exact hex.core_unique hΩ h2 hM' hJ' hJ hJM' hJM

theorem ExactSylow.mem_omegaStarNbr_liftFam_iff (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (hl : HasLifts Δ) (hex : ExactSylow Δ) (hM : M ∈ liftFam Δ)
    (hJ : J ∈ Δ) (hJM : J ≤ M) (hM' : M' ∈ liftFam Δ) (hJ' : J' ∈ Δ) (hJM' : J' ≤ M') :
    M' ∈ omegaStarNbr (liftFam Δ) M ↔ J' ∈ omegaStarNbr Δ J := by
  have hN := hex.normalizer_eq hΩ h2 hM hJ hJM
  have hUU := hex.uSet_liftFam hΩ h2 hl
  unfold omegaStarNbr
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hUU, hN]
  constructor
  · rintro ⟨-, hne, U, hU, hUM', hUN⟩
    refine ⟨hJ', fun h => hne ?_, U, hU, ?_, hUN⟩
    · subst h
      exact liftFam_eq_of_le hΩ hM' hM hJ hJM' hJM
    · exact hex.le_core hΩ h2 hM' hJ' hJM' (isPGroup_of_mem_USet h2 hU) hUM'
  · rintro ⟨-, hne, U, hU, hUJ', hUN⟩
    refine ⟨hM', fun h => hne ?_, U, hU, hUJ'.trans hJM', hUN⟩
    subst h
    exact hex.core_unique hΩ h2 hM' hJ' hJ hJM' hJM

end Dictionary

section AEmpty

variable {Δ : Set (Subgroup X)} {J J' M M' : Subgroup X}

theorem isUniqueInvolution_of_le_liftFam {u z : X}
    (hu : IsUniqueInvolution J u) (hJM : J ≤ M) (hz : IsUniqueInvolution M z) :
    IsUniqueInvolution J z := by
  have : u = z := by
    rcases hz.unique u (hJM hu.mem) hu.sq with h | h
    · exact absurd h hu.ne_one
    · exact h
  exact this ▸ hu

theorem ExactSylow.aEmpty_liftFam (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hex : ExactSylow Δ) (hA : ∀ J ∈ Δ, AEmpty Δ J) :
    ∀ M ∈ liftFam Δ, AEmpty (liftFam Δ) M := by
  intro M hM M' hM'star hM'not zK zJ hzK hzJ
  obtain ⟨J, hJ, hJM⟩ := exists_core_of_mem_liftFam hM
  obtain ⟨J', hJ', hJM'⟩ := exists_core_of_mem_liftFam hM'star.1
  have hstar := (hex.mem_omegaStarNbr_liftFam_iff hΩ h2 hl hM hJ hJM hM'star.1 hJ' hJM').mp
    hM'star
  have hnot : J' ∉ omegaNbr Δ J := fun h =>
    hM'not ((hex.mem_omegaNbr_liftFam_iff hΩ h2 hl hM hJ hJM hM'star.1 hJ' hJM').mpr h)
  obtain ⟨u, hu⟩ := (hΩ.omega1 J hJ).1
  obtain ⟨u', hu'⟩ := (hΩ.omega1 J' hJ').1
  obtain ⟨g, hg, hgJ⟩ := hA J hJ J' hstar hnot zK zJ
    (isUniqueInvolution_of_le_liftFam hu hJM hzK)
    (isUniqueInvolution_of_le_liftFam hu' hJM' hzJ)
  refine ⟨g, ?_, ?_⟩
  · exact sup_le_sup (inf_le_inf_right _ hJM) (inf_le_inf_right _ hJM') hg
  · refine liftFam_eq_of_le hΩ (conjInvariant_liftFam hΩ.conjInvariant g M hM) hM'star.1 hJ'
      ?_ hJM'
    rw [← hgJ]
    exact conjSub_mono hJM

end AEmpty

section Transfer

variable {Δ : Set (Subgroup X)} {J J' K M M' : Subgroup X}

theorem isUniqueInvolution_liftFam_of_le (hM : M ∈ liftFam Δ) {z : X} (hz : IsUniqueInvolution K z)
    (hKM : K ≤ M) : IsUniqueInvolution M z := by
  obtain ⟨z₀, h₀⟩ := liftFam_mem3 hM
  have hU := h₀.isUniqueInvolution
  have : z = z₀ := (hU.unique z (hKM hz.mem) hz.sq).resolve_left hz.ne_one
  exact this ▸ hU

theorem exists_conj_of_conj_liftFam (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hM : M ∈ liftFam Δ) (hM' : M' ∈ liftFam Δ) (hJ : J ∈ Δ) (hJ' : J' ∈ Δ) (hJM : J ≤ M)
    (hJM' : J' ≤ M') {g : X} (hg : conjSub g M = M') : ∃ x : X, conjSub x J = J' := by
  have h1 : IsSylow2In (conjSub g J) M' := by
    have := (isSylow2In_of_le_liftFam hΩ hJ (h2 J hJ) hM hJM).conj g
    rwa [hg] at this
  obtain ⟨x, -, hx⟩ := Disconnected.AschTight.Sec6Gen.exists_conjSub_eq_of_isSylow2In h1
    (isSylow2In_of_le_liftFam hΩ hJ' (h2 J' hJ') hM' hJM')
  exact ⟨x * g, by rw [conjSub_mul]; exact hx⟩

theorem mem_omegaNbr_liftFam_of_mem (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hK : K ∈ Δ) (hM : M ∈ liftFam Δ) (hKM : K ≤ M) (hM' : M' ∈ liftFam Δ) (hJM' : J ≤ M')
    (hJ : J ∈ omegaNbr Δ K) : M' ∈ omegaNbr (liftFam Δ) M := by
  obtain ⟨hJΔ, hne, hJN⟩ := (TC.mem_omegaNbr_iff hΩ h2).mp hJ
  have hKs := isSylow2In_of_le_liftFam hΩ hK (h2 K hK) hM hKM
  have hJs := isSylow2In_of_le_liftFam hΩ hJΔ (h2 J hJΔ) hM' hJM'
  refine ⟨hM', fun h => hne ?_, J, mem_RSet_of_isSylow2In hM' hJs, hJM',
    hJN.trans (normalizer_le_of_le_liftFam hΩ hM hK hKM)⟩
  have hJM : J ≤ M := h ▸ hJM'
  have hJs' := isSylow2In_of_le_liftFam hΩ hJΔ (h2 J hJΔ) hM hJM
  have hV2 : IsPGroup 2 ↥(J ⊔ K : Subgroup X) := (h2 J hJΔ).to_sup_of_normal_right' (h2 K hK) hJN
  have hVM : J ⊔ K ≤ M := sup_le hJM hKM
  have h1 : J ⊔ K = K := hKs.2.2 _ hVM hV2 le_sup_right
  have h2' : K = J := hJs'.2.2 K hKM (h2 K hK) (h1 ▸ le_sup_left)
  exact h2'.symm

end Transfer

section ExactOdd

variable {Δ : Set (Subgroup X)}

theorem eq_of_isSylow2In_of_oddCore_eq_bot {M : Subgroup X} {z : X} (h : IsClassicalMember3 M z)
    (hO : classicalInvolutionOddCore ↥M = ⊥) {P Q : Subgroup X} (hP : IsSylow2In P M)
    (hQ : IsSylow2In Q M) : P = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.nonempty_equiv_sl2 hO
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  have hS₀ := sylow_eq_pCore_of_mulEquiv_sl2Three e S₀
  have hPc : IsSylow2In ((S₀ : Subgroup M).map M.subtype) M := isSylow2In_map_subtype M S₀
  have key : ∀ V : Subgroup X, IsSylow2In V M → V = (S₀ : Subgroup M).map M.subtype := by
    intro V hV
    have hV2 : IsPGroup 2 (V.subgroupOf M) := hV.2.1.comap_subtype
    obtain ⟨S, hS⟩ := hV2.exists_le_sylow
    have hSS : (S : Subgroup M) = S₀ :=
      (sylow_eq_pCore_of_mulEquiv_sl2Three e S).trans hS₀.symm
    have hVle : V ≤ (S₀ : Subgroup M).map M.subtype := by
      have h1 : V.subgroupOf M ≤ S₀ := hSS ▸ hS
      rw [← Subgroup.map_subgroupOf_eq_of_le hV.1]
      exact Subgroup.map_mono h1
    exact (hV.2.2 _ hPc.1 hPc.2.1 hVle).symm
  exact (key P hP).trans (key Q hQ).symm

theorem ExactSylow.of_oddCoreIn_eq_bot
    (hO : ∀ J ∈ Δ, ∀ (L : Subgroup X) (u : X), IsLiftOf J L u →
      Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥) : ExactSylow Δ := by
  intro M hM P Q hP hQ
  obtain ⟨J, hJ, L, u, h, rfl⟩ := hM
  have hint := h.mem3.intrinsic solvableType_three
  have h1 := oddCoreIn_eq_of_intrinsic h.mem3.member hint
  rw [hO J hJ L u h] at h1
  have hOM : classicalInvolutionOddCore ↥(satU (.sl2 3 1) L u) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  exact eq_of_isSylow2In_of_oddCore_eq_bot h.member_sat hOM hP hQ

end ExactOdd

section Section

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}

theorem nbrAdj_of_commutes (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J) {J J' : Subgroup Y}
    (hJ : J ∈ Δ) (hJ' : J' ∈ Δ) (hne : J' ≠ J) (hc : Commutes J J') : TC.nbrAdj Δ J J' := by
  refine ⟨hJ, (TC.mem_omegaNbr_iff hΩ h2).mpr ⟨hJ', hne, fun y hy => ?_⟩⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have h1 : y * x * y⁻¹ = x := by
      rw [← hc x hx y hy, mul_inv_cancel_right]
    rw [h1]
    exact hx
  · have h1 := hc _ hx y hy
    have h2 : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹ * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h1]
        _ = y * x * y⁻¹ := by group
    rw [h2]
    exact hx

end Section

section Bridge

variable {Y : Type} [Group Y] [Finite Y]

theorem hasLifts_conjClass {K₀ L : Subgroup Y} {t : Y} (hu : IsUniqueInvolution K₀ t)
    (hle : K₀ ≤ L) (hL : IsClassicalMember3 L t) : HasLifts (CoreAssembly.conjClass K₀) := by
  rintro _ ⟨g, rfl⟩
  exact ⟨conjSub g L, g * t * g⁻¹, ⟨hu.conj g, conjSub_mono hle, hL.conj g⟩⟩

theorem liftFam_conjClass {J₀ L₀ : Subgroup Y} {u₀ : Y}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass J₀)) (h : IsLiftOf J₀ L₀ u₀) :
    liftFam (CoreAssembly.conjClass J₀) = CoreAssembly.conjClass (satU (.sl2 3 1) L₀ u₀) := by
  have hmem : ∀ g : Y, conjSub g (satU (.sl2 3 1) L₀ u₀) ∈ liftFam (CoreAssembly.conjClass J₀) := by
    intro g
    refine ⟨conjSub g J₀, ⟨g, rfl⟩, conjSub g L₀, g * u₀ * g⁻¹, h.conj g, ?_⟩
    rw [satU_conj]
  ext M
  constructor
  · intro hM
    obtain ⟨J, ⟨g, rfl⟩, L, u, hl, rfl⟩ := hM
    refine ⟨g, ?_⟩
    exact liftFam_eq_of_le hΩ (hmem g) (satU_mem_liftFam ⟨g, rfl⟩ hl) ⟨g, rfl⟩
      ((conjSub_mono h.le).trans (conjSub_mono (le_satU)))
      hl.le_sat
  · rintro ⟨g, rfl⟩
    exact hmem g

theorem eq_of_isLiftOf {Δ : Set (Subgroup Y)} (hΩ : HypOmegaGen Δ) {J L L' : Subgroup Y} {u : Y}
    (hJ : J ∈ Δ) (h : IsLiftOf J L u) (h' : IsLiftOf J L' u)
    (hi : IsIntrinsicU (.sl2 3 1) L u) (hi' : IsIntrinsicU (.sl2 3 1) L' u) : L = L' := by
  have := liftFam_eq_of_le hΩ (satU_mem_liftFam hJ h) (satU_mem_liftFam hJ h') hJ h.le_sat
    h'.le_sat
  rwa [satU_eq_of_isIntrinsicU hi, satU_eq_of_isIntrinsicU hi'] at this

end Bridge

section Thm2

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)} {J : Subgroup Y}

theorem liftFam_trans (hΩ : HypOmegaGen Δ) {M₀ : Subgroup Y} (hM₀ : M₀ ∈ liftFam Δ)
    {J₀ : Subgroup Y} (hJM₀ : J₀ ≤ M₀)
    (htr : ∀ J' ∈ Δ, ∃ g : Y, conjSub g J₀ = J') :
    ∀ M ∈ liftFam Δ, ∃ g : Y, conjSub g M₀ = M := by
  intro M hM
  obtain ⟨J', hJ', hJ'M⟩ := exists_core_of_mem_liftFam hM
  obtain ⟨g, rfl⟩ := htr J' hJ'
  exact ⟨g, liftFam_eq_of_le hΩ (conjInvariant_liftFam hΩ.conjInvariant g M₀ hM₀) hM hJ'
    (conjSub_mono hJM₀) hJ'M⟩

end Thm2

section CertTransfer

section OnX

variable {X : Type} [Group X] [Finite X] {Δ : Set (Subgroup X)} {J J' K : Subgroup X}

theorem commutes_of_thm4U {n : ℕ} (h4 : Thm4BelowU 3 1 n) (hn : Nat.card X < n)
    (hO : classicalInvolutionOddCore X = ⊥) (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hA : ∀ M ∈ liftFam Δ, AEmpty (liftFam Δ) M) (hJ : J ∈ Δ) (hJ' : J' ∈ Δ)
    (hnot : ¬ ∃ g : X, conjSub g J = J') : Commutes J J' := by
  obtain ⟨L, u, h⟩ := hl J hJ
  obtain ⟨L', u', h'⟩ := hl J' hJ'
  have hM := satU_mem_liftFam hJ h
  have hM' := satU_mem_liftFam hJ' h'
  have hnotM : ¬ ∃ g : X, conjSub g (satU (.sl2 3 1) L u) = satU (.sl2 3 1) L' u' :=
    fun ⟨g, hg⟩ => hnot (exists_conj_of_conj_liftFam hΩ h2 hM hM' hJ hJ' h.le_sat h'.le_sat hg)
  have hc := h4 (by norm_num) (by norm_num) X hn (liftFam Δ)
    (hypOmegaModU_liftFam hΩ.conjInvariant) hO hA _ hM _ hM' hnotM
  exact fun a ha b hb => hc a (h.le_sat ha) b (h'.le_sat hb)

theorem commutes_of_thm4U_exact {n : ℕ} (h4 : Thm4BelowU 3 1 n) (hn : Nat.card X < n)
    (hO : classicalInvolutionOddCore X = ⊥) (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hex : ExactSylow Δ) (hA : ∀ J ∈ Δ, AEmpty Δ J) (hJ : J ∈ Δ)
    (hJ' : J' ∈ Δ) (hnot : ¬ ∃ g : X, conjSub g J = J') : Commutes J J' :=
  commutes_of_thm4U h4 hn hO hΩ h2 hl (hex.aEmpty_liftFam hΩ h2 hl hA) hJ hJ' hnot

end OnX

end CertTransfer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
