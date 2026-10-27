module

public import CFSG.ClassicalInvolution.Q3.Q3CLSeven2
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} {Q Q' : Subgroup G}

namespace T8R.Loc

open CFSG.ClassicalInvolution.Asc77.T8R.Loc
  CFSG.ClassicalInvolution.Asc77.T8R
  CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

omit [Finite G] in
theorem natCard_conjSub' (g : G) (A : Subgroup G) : Nat.card ↥(conjSub g A) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

structure AscStandCore (Ω : Set (Subgroup G)) (K : Subgroup G) : Prop where
  hyp : HypOmegaGen Ω
  cls : ClassicalClause Ω
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J

structure Std8Core (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  stand : AscStandCore Ω K
  noTwins : ∀ K' ∈ twinSet Ω K, K' = K
  hz : IsUniqueInvolution K z
  hJ : J ∈ omegaNbr Ω K
  ht : IsUniqueInvolution J t
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hT : T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

theorem Std8Core.symm' (hs : Std8Core Ω K J S R T W z t) :
    Std8Core Ω J K S T R W t z := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  refine ⟨⟨hΩ, hs.stand.cls, hs.stand.aEmpty, hs.hJ.1, ?_⟩, ?_, hs.ht, ?_, hs.hz, hs.hT, hs.hR,
    hs.hW⟩
  · intro L hL
    obtain ⟨g, hg⟩ := hs.stand.trans L hL
    obtain ⟨g₀, hg₀⟩ := hs.stand.trans J hs.hJ.1
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [← hg₀, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one, hg]
  · exact fun K' hK' => T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hs.hJ.1 K' hK'
  · exact T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.stand.mem hs.hJ.1 hs.hJ

theorem Std8Core.conj (hs : Std8Core Ω K J S R T W z t) (n : G) :
    Std8Core Ω (conjSub n K) (conjSub n J) (conjSylow n S) (conjSub n R) (conjSub n T)
      (conjSub n W) (n * z * n⁻¹) (n * t * n⁻¹) := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hcl := hΩ.conjInvariant
  have hmem : conjSub n K ∈ Ω := hcl n K hs.stand.mem
  refine ⟨⟨hΩ, hs.stand.cls, hs.stand.aEmpty, hmem, ?_⟩, ?_, hs.hz.conj n,
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

theorem loc26_conj (hΩ : HypOmegaGen Ω) (hX : Loc26 Ω K J S R T z t Q) (n : G) :
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

theorem R_ne_T (hs : Std8Core Ω K J S R T W z t) : R ≠ T := by
  intro h
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K :=
    T3.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hRΩ hRK
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  exact hs.hJ.2.1 (Sec6Gen.eq_of_le_of_le hΩ hs.hJ.1 hs.stand.mem hRsyl.2.1 (by omega)
    (h ▸ hTJ) hRK)

theorem partIHyp_of_std8 (hs : Std8Core Ω K J S R T W z t) : PartIHypG Ω :=
  ⟨hs.stand.hyp, hs.stand.cls, hs.stand.aEmpty⟩

theorem mem_DSet_of_le_sylow (hs : Std8Core Ω K J S R T W z t) {X : Subgroup G}
    (hX : X ∈ RSet Ω) (hXS : X ≤ (S : Subgroup G)) : X ∈ DSet Ω W :=
  ⟨hX, fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 x (hXS hx))⟩

@[expose] noncomputable def stdRepK (hs : Std8Core Ω K J S R T W z t) : Rep Ω W :=
  T8.mkRep (partIHyp_of_std8 hs) hs.hW.1 hs.stand.mem (mem_DSet_of_le_sylow hs hs.hR.1 hs.hR.2.2)
    (T3.isSylow2In_of_mem_RSet_of_le hs.stand.hyp hs.stand.mem hs.hR.1 hs.hR.2.1)

@[expose] noncomputable def stdRepJ (hs : Std8Core Ω K J S R T W z t) : Rep Ω W :=
  T8.mkRep (partIHyp_of_std8 hs) hs.hW.1 hs.hJ.1 (mem_DSet_of_le_sylow hs hs.hT.1 hs.hT.2.2)
    (T3.isSylow2In_of_mem_RSet_of_le hs.stand.hyp hs.hJ.1 hs.hT.1 hs.hT.2.1)

theorem le_centralizer_mul {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Core Ω K J S R T W z t) :
    R ≤ Subgroup.centralizer ({z * t} : Set G) := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRne : R ≠ T := by
    intro hRT
    have hRsyl := T3.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hRΩ hRK
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
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
    have hRsyl := T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hTΩ hTJ
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hTΩ
    have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hRsyl.2.1 (by omega)
    exact Q3CP.l67Gen G Ω hΩ S R hRΩ T hTΩ hRS hTS hRne r hr t htT
  calc r * (z * t) = (r * z) * t := by group
    _ = (z * r) * t := by rw [h1]
    _ = z * (r * t) := by group
    _ = z * (t * r) := by rw [h2]
    _ = (z * t) * r := by group

theorem zt_mem_sylow (hs : Std8Core Ω K J S R T W z t) : z * t ∈ (S : Subgroup G) := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hTΩ hTJ
  have h8R := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have h8T := Sec6Gen.eight_le_of_mem_RSet hΩ hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  exact S.mul_mem (hRS hzR) (hTS htT)

theorem exists_not_comm (hs : Std8Core Ω K J S R T W z t) : ∃ x y : G, x * y ≠ y * x := by
  obtain ⟨-, P, -, hPnc⟩ := hs.stand.hyp.omega1 K hs.stand.mem
  by_contra hcon
  push Not at hcon
  exact hPnc ⟨⟨fun a b => Subtype.ext (hcon a b)⟩⟩

theorem fix_or_swap (hs : Std8Core Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) {s : G}
    (hsS : s ∈ (S : Subgroup G)) :
    (conjSub s R = R ∧ conjSub s T = T) ∨ (conjSub s R = T ∧ conjSub s T = R) := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
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

theorem conj_zt_of_mem_sylow (hs : Std8Core Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : s * (z * t) * s⁻¹ = z * t := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have h8R := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have h8T := Sec6Gen.eight_le_of_mem_RSet hΩ hTΩ
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  rcases fix_or_swap hs hX hsS with ⟨hR', hT'⟩ | ⟨hR', hT'⟩
  · have hK' : conjSub s K = K := T8.conjSub_eq_of_conjSub_eq hΩ hK hRΩ hRK hR'
    have hJ' : conjSub s J = J := T8.conjSub_eq_of_conjSub_eq hΩ hJΩ hTΩ hTJ hT'
    have h1 := hs.hz.conj_eq hK'
    have h2 := hs.ht.conj_eq hJ'
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = z * t := by rw [h1, h2]
  · have hK' : conjSub s K = J := Sec6Gen.eq_of_le_of_le hΩ (hcl s K hK) hJΩ hTsyl.2.1 (by omega)
      (hR' ▸ conjSub_mono (n := s) hRK) hTJ
    have hJ' : conjSub s J = K := Sec6Gen.eq_of_le_of_le hΩ (hcl s J hJΩ) hK hRsyl.2.1 (by omega)
      (hT' ▸ conjSub_mono (n := s) hTJ) hRK
    have h1 : s * z * s⁻¹ = t := (hs.ht.eq (hK' ▸ hs.hz.conj s)).symm
    have h2 : s * t * s⁻¹ = z := (hs.hz.eq (hJ' ▸ hs.ht.conj s)).symm
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = t * z := by rw [h1, h2]
      _ = z * t := hzt.symm

theorem _root_.CFSG.ClassicalInvolution.Asc77.T8R.Loc.AscStandCore.toGen {p f : ℕ} [Fact p.Prime]
    (h : CFSG.ClassicalInvolution.Asc77.T8R.Loc.AscStandCore p f Ω K) :
    CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc.AscStandCore Ω K := by
  have hU : CFSG.ClassicalInvolution.Uniform.HypOmegaModU
      (CFSG.ClassicalInvolution.Uniform.MemberType.sl2 p f) Ω :=
    (CFSG.ClassicalInvolution.Uniform.hypOmegaModU_iff_hypOmegaMod h.odd h.five).mpr h.hyp
  exact ⟨(partIHypG_of_modU hU h.aEmpty).hyp, (partIHypG_of_modU hU h.aEmpty).cls, h.aEmpty,
    h.mem, h.trans⟩

theorem _root_.CFSG.ClassicalInvolution.Asc77.T8R.Loc.Std8Core.toGen {p f : ℕ} [Fact p.Prime]
    (hs : CFSG.ClassicalInvolution.Asc77.T8R.Loc.Std8Core p f Ω K J S R T W z t) :
    CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc.Std8Core Ω K J S R T W z t :=
  ⟨hs.stand.toGen, hs.noTwins, hs.hz, hs.hJ, hs.ht, hs.hR, hs.hT, hs.hW⟩

end T8R.Loc


end CFSG.ClassicalInvolution.Q3.Q3CL
