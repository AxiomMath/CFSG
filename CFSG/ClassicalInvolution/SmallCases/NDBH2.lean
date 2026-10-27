module

public import CFSG.ClassicalInvolution.Asc77.AscT8ROutF
public import CFSG.ClassicalInvolution.SmallCases.NDBH1
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Asc77.AscT8S26Final
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UTyp
public import CFSG.ClassicalInvolution.Asc77.AscT8Y1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Asc77.T8R

namespace T8R.Loc

section Defs

variable {G : Type} [Group G] [Finite G]

structure AscStandCore (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J

structure Std8Core (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  stand : AscStandCore p f Ω K
  noTwins : ∀ K' ∈ twinSet Ω K, K' = K
  hz : IsUniqueInvolution K z
  hJ : J ∈ omegaNbr Ω K
  ht : IsUniqueInvolution J t
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hT : T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

structure Loc26 (Ω : Set (Subgroup G)) (K J : Subgroup G) (S : Sylow 2 G) (R T : Subgroup G)
    (z t : G) (Q : Subgroup G) : Prop where
  odd : Odd (Nat.card Q)
  rset : ∀ {P : Subgroup G}, P ∈ RSet Ω → P ≤ (S : Subgroup G) → P = R ∨ P = T
  four : ∀ {M : Subgroup G}, M ∈ Ω → 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G)) → M ≠ J →
    M ∉ omegaNbr Ω K
  invol : ∀ {L : Subgroup G}, L ∈ omegaNbr Ω K → ∀ {y : G}, IsUniqueInvolution L y →
    y * t⁻¹ ∈ Q
  zt : ∀ {y : G}, y ∈ Subgroup.centralizer ({z} : Set G) →
    y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ Q

end Defs

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} {Q : Subgroup G}


omit [Finite G] in
theorem natCard_conjSub' (g : G) (A : Subgroup G) : Nat.card ↥(conjSub g A) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem Std8Core.symm' (hs : Std8Core p f Ω K J S R T W z t) :
    Std8Core p f Ω J K S T R W t z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  refine ⟨⟨hp, hq, hΩ, hs.stand.aEmpty, hs.hJ.1, ?_⟩, ?_, hs.ht, ?_, hs.hz, hs.hT, hs.hR,
    hs.hW⟩
  · intro L hL
    obtain ⟨g, hg⟩ := hs.stand.trans L hL
    obtain ⟨g₀, hg₀⟩ := hs.stand.trans J hs.hJ.1
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [← hg₀, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one, hg]
  · exact fun K' hK' => T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hs.hJ.1 K' hK'
  · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hs.stand.mem hs.hJ.1 hs.hJ

theorem Std8Core.conj (hs : Std8Core p f Ω K J S R T W z t) (n : G) :
    Std8Core p f Ω (conjSub n K) (conjSub n J) (conjSylow n S) (conjSub n R) (conjSub n T)
      (conjSub n W) (n * z * n⁻¹) (n * t * n⁻¹) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hcl := hΩ.conjInvariant
  have hmem : conjSub n K ∈ Ω := hcl n K hs.stand.mem
  refine ⟨⟨hs.stand.odd, hs.stand.five, hΩ, hs.stand.aEmpty, hmem, ?_⟩, ?_, hs.hz.conj n,
    omegaNbr_conj hcl hs.hJ n, hs.ht.conj n, ?_, ?_, ?_⟩
  · intro L hL
    obtain ⟨g, hg⟩ := hs.stand.trans L hL
    refine ⟨g * n⁻¹, ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right, hg]
  · exact fun K' hK' => T8.noTwins_of_mem hcl hs.stand.trans hs.noTwins hmem K' hK'
  · obtain ⟨hR, hRK, hRS⟩ := hs.hR
    refine ⟨RSet.conj hcl hR n, conjSub_mono hRK, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hRS
  · obtain ⟨hT, hTJ, hTS⟩ := hs.hT
    refine ⟨RSet.conj hcl hT n, conjSub_mono hTJ, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hTS
  · obtain ⟨hW, hWS, hWn⟩ := hs.hW
    refine ⟨WSet.conj hcl hW n, ?_, ?_⟩
    · rw [coe_conjSylow]
      exact conjSub_mono hWS
    · intro s hs'
      rw [coe_conjSylow, mem_conjSub_iff] at hs'
      have := hWn _ hs'
      calc conjSub s (conjSub n W) = conjSub n (conjSub (n⁻¹ * s * n) W) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub n W := by rw [this]

theorem Loc26.conj (hΩ : HypOmegaMod p f Ω) (hX : Loc26 Ω K J S R T z t Q) (n : G) :
    Loc26 Ω (conjSub n K) (conjSub n J) (conjSylow n S) (conjSub n R) (conjSub n T)
      (n * z * n⁻¹) (n * t * n⁻¹) (conjSub n Q) := by
  have hcl := hΩ.conjInvariant
  have hback : ∀ {A B : Subgroup G}, conjSub n⁻¹ A = B → A = conjSub n B := fun {A B} h => by
    rw [← h, conjSub_conjSub_inv]
  refine ⟨by rw [natCard_conjSub']; exact hX.odd, fun {P} hP hPS => ?_, fun {M} hM h4 hMJ => ?_,
    fun {L} hL {y} hy => ?_, fun {y} hy => ?_⟩
  · have hPS' : conjSub n⁻¹ P ≤ (S : Subgroup G) := by
      have := conjSub_mono (n := n⁻¹) hPS
      rwa [coe_conjSylow, conjSub_inv_conjSub] at this
    rcases hX.rset (RSet.conj hcl hP n⁻¹) hPS' with h | h
    · exact Or.inl (hback h)
    · exact Or.inr (hback h)
  · intro hmem
    have h1 : conjSub n⁻¹ M ∈ omegaNbr Ω K := by
      have := omegaNbr_conj hcl hmem n⁻¹
      rwa [conjSub_inv_conjSub] at this
    refine hX.four (hcl n⁻¹ M hM) ?_ (fun e => hMJ (hback e)) h1
    have e : conjSub n (conjSub n⁻¹ M ⊓ (S : Subgroup G)) = M ⊓ (conjSylow n S : Subgroup G) := by
      rw [coe_conjSylow]
      show (conjSub n⁻¹ M ⊓ (S : Subgroup G)).map (MulAut.conj n).toMonoidHom = _
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective]
      show conjSub n (conjSub n⁻¹ M) ⊓ conjSub n (S : Subgroup G) = _
      rw [conjSub_conjSub_inv]
    have hc := natCard_conjSub' n (conjSub n⁻¹ M ⊓ (S : Subgroup G))
    rw [e] at hc
    omega
  · have h1 : conjSub n⁻¹ L ∈ omegaNbr Ω K := by
      have := omegaNbr_conj hcl hL n⁻¹
      rwa [conjSub_inv_conjSub] at this
    have h2 := hy.conj n⁻¹
    have h3 := hX.invol h1 h2
    rw [mem_conjSub_iff]
    have e : n⁻¹ * (y * (n * t * n⁻¹)⁻¹) * n = n⁻¹ * y * n⁻¹⁻¹ * t⁻¹ := by group
    rw [e]
    exact h3
  · have h1 : n⁻¹ * y * n⁻¹⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      calc n⁻¹ * y * n⁻¹⁻¹ * z = n⁻¹ * (y * (n * z * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * z * n⁻¹) * y) * n := by rw [hy]
        _ = z * (n⁻¹ * y * n⁻¹⁻¹) := by group
    have h3 := hX.zt h1
    rw [mem_conjSub_iff]
    have e : n⁻¹ * (y * (n * z * n⁻¹ * (n * t * n⁻¹)) * y⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹))⁻¹) *
        n = n⁻¹ * y * n⁻¹⁻¹ * (z * t) * (n⁻¹ * y * n⁻¹⁻¹)⁻¹ * (z * t)⁻¹ := by group
    rw [e]
    exact h3

theorem R_ne_T (hs : Std8Core p f Ω K J S R T W z t) : R ≠ T := by
  intro h
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K :=
    T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hRΩ hRK
  have h8 := hΩ.eight_le_of_mem_RSet hp hRΩ
  exact hs.hJ.2.1 (hΩ.eq_of_le_of_le hs.hJ.1 hs.stand.mem hRsyl.2.1 (by omega)
    (h ▸ hTJ) hRK)

theorem partIHyp_of_std8 (hs : Std8Core p f Ω K J S R T W z t) : PartIHyp p f Ω :=
  ⟨hs.stand.odd, hs.stand.five, hs.stand.hyp, hs.stand.aEmpty⟩

theorem mem_DSet_of_le_sylow (hs : Std8Core p f Ω K J S R T W z t) {X : Subgroup G}
    (hX : X ∈ RSet Ω) (hXS : X ≤ (S : Subgroup G)) : X ∈ DSet Ω W :=
  ⟨hX, fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 x (hXS hx))⟩

@[expose] noncomputable def stdRepK (hs : Std8Core p f Ω K J S R T W z t) : Rep Ω W :=
  mkRep (partIHyp_of_std8 hs) hs.hW.1 hs.stand.mem (mem_DSet_of_le_sylow hs hs.hR.1 hs.hR.2.2)
    (T3.isSylow2In_of_mem_RSet_of_le hs.stand.odd hs.stand.hyp hs.stand.mem hs.hR.1 hs.hR.2.1)

@[expose] noncomputable def stdRepJ (hs : Std8Core p f Ω K J S R T W z t) : Rep Ω W :=
  mkRep (partIHyp_of_std8 hs) hs.hW.1 hs.hJ.1 (mem_DSet_of_le_sylow hs hs.hT.1 hs.hT.2.2)
    (T3.isSylow2In_of_mem_RSet_of_le hs.stand.odd hs.stand.hyp hs.hJ.1 hs.hT.1 hs.hT.2.1)

theorem le_centralizer_mul {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Core p f Ω K J S R T W z t) :
    R ≤ Subgroup.centralizer ({z * t} : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRne : R ≠ T := by
    intro hRT
    have hRsyl := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hRΩ hRK
    have h8 := hΩ.eight_le_of_mem_RSet hp hRΩ
    have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
    have hzJ : z ∈ J := hTJ (hRT ▸ hzR)
    rcases hs.ht.unique z hzJ hs.hz.sq with h | h
    · exact hs.hz.ne_one h
    · have hJtw : J ∈ twinSet Ω K := ⟨hs.hJ.1, z, hs.hz, h ▸ hs.ht⟩
      exact hs.hJ.2.1 (hs.noTwins J hJtw)
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : r * z = z * r := by
    have := hs.hz.conj_eq (n := r) (conjSub_eq_self_of_mem (hRK hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [this]
  have h2 : r * t = t * r := by
    have hRsyl := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hTΩ hTJ
    have h8 := hΩ.eight_le_of_mem_RSet hp hTΩ
    have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hRsyl.2.1 (by omega)
    exact l6_7_proved p f hp hq G Ω hΩ S R hRΩ T hTΩ hRS hTS hRne r hr t htT
  calc r * (z * t) = (r * z) * t := by group
    _ = (z * r) * t := by rw [h1]
    _ = z * (r * t) := by group
    _ = z * (t * r) := by rw [h2]
    _ = (z * t) * r := by group

theorem zt_mem_sylow (hs : Std8Core p f Ω K J S R T W z t) : z * t ∈ (S : Subgroup G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hp hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  exact S.mul_mem (hRS hzR) (hTS htT)

theorem exists_not_comm [IsSimpleGroup G] (hs : Std8Core p f Ω K J S R T W z t) :
    ∃ x y : G, x * y ≠ y * x := by
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hs.stand.hyp
    hs.stand.mem hs.hz
  by_contra hcon
  push Not at hcon
  have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcon
  exact hKs inferInstance

theorem fix_or_swap (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) {s : G}
    (hsS : s ∈ (S : Subgroup G)) :
    (conjSub s R = R ∧ conjSub s T = T) ∨ (conjSub s R = T ∧ conjSub s T = R) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT := R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hsS' : ∀ P ≤ (S : Subgroup G), conjSub s P ≤ (S : Subgroup G) := by
    intro P hP
    have := conjSub_mono (n := s) hP
    rwa [conjSub_eq_self_of_mem hsS] at this
  have hR' := hX.rset (RSet.conj hcl hRΩ s) (hsS' R hRS)
  have hT' := hX.rset (RSet.conj hcl hTΩ s) (hsS' T hTS)
  rcases hR' with hR' | hR'
  · left
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)).symm hRT
    · exact hT'
  · right
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)) (Ne.symm hRT)

theorem conj_zt_of_mem_sylow (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : s * (z * t) * s⁻¹ = z * t := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have h8R := hΩ.eight_le_of_mem_RSet hp hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  rcases fix_or_swap hs hX hsS with ⟨hR', hT'⟩ | ⟨hR', hT'⟩
  · have hK' : conjSub s K = K := T8.conjSub_eq_of_conjSub_eq hp hΩ hK hRΩ hRK hR'
    have hJ' : conjSub s J = J := T8.conjSub_eq_of_conjSub_eq hp hΩ hJΩ hTΩ hTJ hT'
    have h1 := hs.hz.conj_eq hK'
    have h2 := hs.ht.conj_eq hJ'
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = z * t := by rw [h1, h2]
  · have hK' : conjSub s K = J := hΩ.eq_of_le_of_le (hcl s K hK) hJΩ hTsyl.2.1 (by omega)
      (hR' ▸ conjSub_mono (n := s) hRK) hTJ
    have hJ' : conjSub s J = K := hΩ.eq_of_le_of_le (hcl s J hJΩ) hK hRsyl.2.1 (by omega)
      (hT' ▸ conjSub_mono (n := s) hTJ) hRK
    have h1 : s * z * s⁻¹ = t := (hs.ht.eq (hK' ▸ hs.hz.conj s)).symm
    have h2 : s * t * s⁻¹ = z := (hs.hz.eq (hJ' ▸ hs.ht.conj s)).symm
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = t * z := by rw [h1, h2]
      _ = z * t := hzt.symm

end Cert

end T8R.Loc

end CFSG.ClassicalInvolution.Asc77
