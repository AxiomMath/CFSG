module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21Z01
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_commuting_gen (hΩ : HypOmegaGen Ω) {M : Subgroup G} (hM : M ∈ Ω)
    {P : Subgroup G} (hP2 : IsPGroup 2 P) (hPM : P ≤ Subgroup.normalizer (M : Set G))
    {𝒜 : Set (Subgroup G)}
    (hA : ∀ A ∈ 𝒜, A ≤ P ∧ ∃ N ∈ Ω, N ≠ M ∧ IsSylow2In A N) :
    ∃ T : Subgroup G, IsSylow2In T M ∧ (∀ p ∈ P, conjSub p T = T) ∧ IsPGroup 2 ↥(P ⊔ T) ∧
      ∀ A ∈ 𝒜, Commutes A T := by
  obtain ⟨T, hT, hfix⟩ := exists_sylow_normalized hP2 hPM
  have hTset : T ∈ RSet Ω := mem_RSet_of_isSylow2In hM hT
  have hPnT : P ≤ Subgroup.normalizer (T : Set G) := fun p hp =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix p hp)
  have hPT2 : IsPGroup 2 ↥(P ⊔ T) := hP2.to_sup_of_normal_right' hT.2.1 hPnT
  obtain ⟨S, hS⟩ := hPT2.exists_le_sylow
  refine ⟨T, hT, hfix, hPT2, fun A hA' => ?_⟩
  obtain ⟨hAP, N, hN, hNM, hAN⟩ := hA A hA'
  have hAset : A ∈ RSet Ω := mem_RSet_of_isSylow2In hN hAN
  have hAS : A ≤ (S : Subgroup G) := hAP.trans (le_sup_left.trans hS)
  have hTS : T ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hAT : A ≠ T := by
    intro h
    have h1 := Sec6Gen.card_le_two_of_le_inf hΩ hN hM hNM hAN.2.1 hAN.1 (h ▸ hT.1)
    have h2 := Sec6Gen.eight_le_of_mem_RSet hΩ hAset
    omega
  exact Q3.Q3CP.l67Gen G Ω hΩ S A hAset T hTset hAS hTS hAT

end Sylow

section FrameU

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' J W : Subgroup G}
  {z u t : G}

theorem exists_frame (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (h : Data Ω K K' z u J t W) :
    ∃ (J' R R' T T' : Subgroup G) (x y : G), J' ∈ twinSet Ω J ∧ J' ≠ J ∧
      IsUniqueInvolution J' t ∧ Q3T8.Asc77.Frame21 K K' J J' z u t R R' T T' x y := by
  have hK : K ∈ Ω := h.frame.mem
  have hz : IsUniqueInvolution K z := h.frame.hz
  have hK'tw : K' ∈ twinSet Ω K := h.frame.hK'
  have hne : K' ≠ K := h.frame.hne
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'tw
  have hJΩ : J ∈ Ω := h.frame.hJ.1
  have hJK : J ≠ K := (h.frame.hJ.2 K (mem_twinSet_self hK hz)).2.1
  have hJK' : J ≠ K' := (h.frame.hJ.2 K' hK'tw).2.1
  have hd := h.frame
  have htz : t ≠ z := hd.t_ne_z
  obtain ⟨g, hg⟩ := (htr K hK J hJΩ)
  have hzJ : IsUniqueInvolution J (g * z * g⁻¹) := by
    have := hz.conj g
    rwa [hg] at this
  have hgz : g * z * g⁻¹ = t := hzJ.eq h.frame.ht
  have hJ'Ω : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hJ't : IsUniqueInvolution (conjSub g K') t := by
    have := hzK'.conj g
    rwa [hgz] at this
  have hJ'tw : conjSub g K' ∈ twinSet Ω J := ⟨hJ'Ω, t, h.frame.ht, hJ't⟩
  have hJ'J : conjSub g K' ≠ J := by
    intro hc
    apply hne
    rw [← hg] at hc
    have := congrArg (conjSub g⁻¹) hc
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hJ'K : conjSub g K' ≠ K := fun e => htz (hz.eq (e ▸ hJ't)).symm
  have hJ'K' : conjSub g K' ≠ K' := fun e => htz (hzK'.eq (e ▸ hJ't)).symm
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, -, -, -, hc₀, hRT₀, hR'T₀⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hK hz hK'tw hne h.frame.hJ
  have h8T₀ : 8 ≤ Nat.card T₀ := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJΩ hT₀)
  have htT₀ : t ∈ T₀ := mem_of_isUniqueInvolution_of_isPGroup h.frame.ht hT₀.1 hT₀.2.1 (by omega)
  have htK : t ∈ Balance.Bootstrap.trivialOnQuot K :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₀, hR₀, fun r hr =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hRT₀ r hr t htT₀)⟩
  have htK' : t ∈ Balance.Bootstrap.trivialOnQuot K' :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'Ω ⟨R₀', hR₀', fun r hr =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hR'T₀ r hr t htT₀)⟩
  have hB := Hat2A7S.twinFrame_isElemAbelian hΩ hd
  have hA2 : IsPGroup 2 (Subgroup.closure ({z, u, t} : Set G)) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 _ hB
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hK hne hzK' hz
  have huN : u ∈ Subgroup.normalizer (K : Set G) :=
    (sup_le (Subgroup.le_normalizer) hK'N) hd.hu
  have huN' : u ∈ Subgroup.normalizer (K' : Set G) :=
    (sup_le hKN' (Subgroup.le_normalizer)) hd.hu
  have hAK : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact Subgroup.le_normalizer hz.mem
    · exact huN
    · exact htK.1
  have hAK' : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.normalizer (K' : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact Subgroup.le_normalizer hzK'.mem
    · exact huN'
    · exact htK'.1
  obtain ⟨R, hRsyl, hRfix, hBR2, -⟩ := exists_sylow_commuting_gen hΩ hK hA2 hAK (𝒜 := ∅)
    (fun A hA => absurd hA (Set.notMem_empty A))
  have hBRK' : Subgroup.closure ({z, u, t} : Set G) ⊔ R ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le hAK' (hRsyl.1.trans hKN')
  obtain ⟨R', hR'syl, hR'fix, hQ2, hcR⟩ := exists_sylow_commuting_gen hΩ hK'Ω hBR2 hBRK'
    (𝒜 := {R}) (fun A hA => by
      rw [Set.mem_singleton_iff] at hA
      subst hA
      exact ⟨le_sup_right, K, hK, hne.symm, hRsyl⟩)
  have hcomm : Commutes R R' := hcR R rfl
  have htA : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hRR' : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    Hat2A7S.T7X.isSylow2In_sup_of_twin hΩ hK hK'Ω hne hz hzK' hRsyl hR'syl hcomm
  have huRR' : u ∈ R ⊔ R' := by
    set Q : Subgroup G := (Subgroup.closure ({z, u, t} : Set G) ⊔ R) ⊔ R' with hQ
    have hle : R ⊔ R' ≤ Q ⊓ (K ⊔ K') :=
      le_inf (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
        (sup_le_sup hRsyl.1 hR'syl.1)
    have h1 : Q ⊓ (K ⊔ K') = R ⊔ R' :=
      hRR'.2.2 (Q ⊓ (K ⊔ K')) inf_le_right hQ2.to_inf_left hle
    rw [← h1]
    exact ⟨(le_sup_left.trans le_sup_left : Subgroup.closure ({z, u, t} : Set G) ≤ Q) huA,
      hd.hu⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm huRR'
  have hcent : ∀ {L R₁ : Subgroup G}, IsSylow2In R₁ L → t ∈ Balance.Bootstrap.trivialOnQuot L →
      (∀ a ∈ Subgroup.closure ({z, u, t} : Set G), conjSub a R₁ = R₁) →
        ∀ r ∈ R₁, r * t = t * r := by
    intro L R₁ hR₁ htL hfix r hr
    have h1 : t * r * t⁻¹ ∈ R₁ := by
      have := conj_mem_conjSub (n := t) hr
      rwa [hfix t htA] at this
    have h2 : t * r * t⁻¹ * r⁻¹ ∈ R₁ := R₁.mul_mem h1 (R₁.inv_mem hr)
    have h3 : t * r * t⁻¹ * r⁻¹ ∈ Balance.oddCoreIn L := by
      have := htL.2 r (hR₁.1 hr)
      rwa [commutatorElement_def] at this
    have h4 : IsPGroup 2 (Subgroup.zpowers (t * r * t⁻¹ * r⁻¹)) :=
      hR₁.2.1.to_le (Subgroup.zpowers_le.mpr h2)
    have h5 : t * r * t⁻¹ * r⁻¹ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (Balance.odd_card_oddCoreIn L) h3 h4
    have h6 : t * r * t⁻¹ = r := by
      have := congrArg (fun w => w * r) h5
      simpa using this
    calc r * t = t * r * t⁻¹ * t := by rw [h6]
      _ = t * r := by group
  have hRt : ∀ r ∈ R, r * t = t * r := hcent hRsyl htK hRfix
  have hR't : ∀ r ∈ R', r * t = t * r :=
    hcent hR'syl htK' (fun a ha => hR'fix a (Subgroup.mem_sup_left ha))
  have hu2 : u * u = 1 := hd.hu2
  have hxy2 : (x * x) * (y * y) = 1 := by
    have hc : x * y = y * x := hcomm x hx y hy
    calc (x * x) * (y * y) = x * (x * y) * y := by group
      _ = x * (y * x) * y := by rw [hc]
      _ = (x * y) * (x * y) := by group
      _ = 1 := by rw [hxy, hu2]
  have hw : x * x ∈ R ⊓ R' := by
    refine ⟨R.mul_mem hx hx, ?_⟩
    have : x * x = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left hxy2
    rw [this]
    exact R'.inv_mem (R'.mul_mem hy hy)
  have hcard : Nat.card ↥(R ⊓ R') ≤ 2 :=
    Sec6Gen.card_le_two_of_le_inf hΩ hK hK'Ω hne.symm (hRsyl.2.1.to_le inf_le_left)
      (inf_le_left.trans hRsyl.1) (inf_le_right.trans hR'syl.1)
  have hww : (x * x) * (x * x) = 1 := Q3T8.Asc77.sq_eq_one_of_natCard_le_two_frame hcard hw
  have hyy : y * y = x * x := by
    have : (y * y) = (x * x)⁻¹ := eq_inv_of_mul_eq_one_right hxy2
    rw [this]
    exact inv_eq_of_mul_eq_one_right hww
  have hxz : x * x = z := by
    rcases hz.unique (x * x) (K.mul_mem (hRsyl.1 hx) (hRsyl.1 hx)) hww with h1 | h1
    · exfalso
      have hx2 : x = 1 ∨ x = z := hz.unique x (hRsyl.1 hx) h1
      have hy2 : y = 1 ∨ y = z := hzK'.unique y (hR'syl.1 hy) (by rw [hyy, h1])
      rcases hx2 with rfl | rfl <;> rcases hy2 with rfl | rfl
      · exact hd.hu1 (by rw [← hxy, one_mul])
      · exact hd.huz (by rw [← hxy, one_mul])
      · exact hd.huz (by rw [← hxy, mul_one])
      · exact hd.hu1 (by rw [← hxy]; exact hz.sq)
    · exact h1
  have h8R : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hRsyl)
  have h8R' : 8 ≤ Nat.card R' := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK'Ω hR'syl)
  have hRc : R ≤ Subgroup.centralizer ({t} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRt r hr)
  have hR'c : R' ≤ Subgroup.centralizer ({t} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hR't r hr)
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hK hJK h.frame.ht hRsyl.1 hRsyl.2.1 (by omega) hRc
  have hR'J : R' ≤ Subgroup.normalizer (J : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hK'Ω hJK' h.frame.ht hR'syl.1 hR'syl.2.1 (by omega) hR'c
  have hRJ' : R ≤ Subgroup.normalizer ((conjSub g K' : Subgroup G) : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ'Ω hK hJ'K hJ't hRsyl.1 hRsyl.2.1 (by omega) hRc
  have hR'J' : R' ≤ Subgroup.normalizer ((conjSub g K' : Subgroup G) : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ'Ω hK'Ω hJ'K' hJ't hR'syl.1 hR'syl.2.1 (by omega) hR'c
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hQ2.to_le (sup_le (le_sup_right.trans le_sup_left)
    le_sup_right)
  obtain ⟨T, hTsyl, -, hPT2, hTc⟩ := exists_sylow_commuting_gen hΩ hJΩ hP2 (sup_le hRJ hR'J)
    (𝒜 := {R, R'}) (fun A hA => by
      rcases hA with rfl | hA
      · exact ⟨le_sup_left, K, hK, hJK.symm, hRsyl⟩
      · rw [Set.mem_singleton_iff] at hA
        subst hA
        exact ⟨le_sup_right, K', hK'Ω, hJK'.symm, hR'syl⟩)
  have hTN : T ≤ Subgroup.normalizer ((conjSub g K' : Subgroup G) : Set G) :=
    hTsyl.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hJΩ hJ'Ω hJ'J.symm h.frame.ht hJ't)
  obtain ⟨T', hT'syl, -, -, hT'c⟩ := exists_sylow_commuting_gen hΩ hJ'Ω hPT2
    (sup_le (sup_le hRJ' hR'J') hTN) (𝒜 := {R, R', T}) (fun A hA => by
      rcases hA with rfl | hA
      · exact ⟨le_sup_left.trans le_sup_left, K, hK, hJ'K.symm, hRsyl⟩
      · rcases hA with rfl | hA
        · exact ⟨le_sup_right.trans le_sup_left, K', hK'Ω, hJ'K'.symm, hR'syl⟩
        · rw [Set.mem_singleton_iff] at hA
          subst hA
          exact ⟨le_sup_right, J, hJΩ, hJ'J.symm, hTsyl⟩)
  refine ⟨conjSub g K', R, R', T, T', x, y, hJ'tw, hJ'J, hJ't, ?_⟩
  exact
    { hR := hRsyl
      hR' := hR'syl
      hT := hTsyl
      hT' := hT'syl
      cRR' := hcomm
      cRT := hTc R (by simp)
      cR'T := hTc R' (by simp)
      cRT' := hT'c R (by simp)
      cR'T' := hT'c R' (by simp)
      cTT' := hT'c T (by simp)
      Rt := hRt
      R't := hR't
      hx := hx
      hy := hy
      hx2 := hxz
      hy2 := hyy.trans hxz
      hxy := hxy }

theorem mem_tqMembers_u_J (hΩ : HypOmegaGen Ω) (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (h : Data Ω K K' z u J t W) : J ∈ tqMembers3 Ω u := by
  obtain ⟨J', R, R', T, T', x, y, -, -, -, hF⟩ := exists_frame hΩ htr h2 h
  exact ⟨h.frame.hJ.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 h.frame.hJ.1
    ⟨T, hF.hT, hF.le_centralizer_u.1⟩⟩

theorem exists_twin_mem_tqMembers_u (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (h : Data Ω K K' z u J t W) :
    ∃ J' : Subgroup G, J' ∈ twinSet Ω J ∧ J' ≠ J ∧ IsUniqueInvolution J' t ∧
      J' ∈ tqMembers3 Ω u := by
  obtain ⟨J', R, R', T, T', x, y, hJ', hne, ht', hF⟩ := exists_frame hΩ htr h2 h
  exact ⟨J', hJ', hne, ht', hJ'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ'.1
    ⟨T', hF.hT', hF.le_centralizer_u.2⟩⟩

end FrameU

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
