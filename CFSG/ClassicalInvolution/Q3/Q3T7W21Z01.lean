module

public import CFSG.ClassicalInvolution.Q3.Q3T7H4
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Sect
public import CFSG.ClassicalInvolution.Q3.Q3T7W21A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_commuting (hΩ : Q3T7M.HM Ω) {M : Subgroup G} (hM : M ∈ Ω) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPM : P ≤ Subgroup.normalizer (M : Set G)) {𝒜 : Set (Subgroup G)}
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
    have h1 := hΩ.card_le_two_of_le_inf hN hM hNM hAN.2.1 hAN.1 (h ▸ hT.1)
    have h2 := hΩ.eight_le_of_mem_RSet hAset
    omega
  exact Q3T8.Asc77.l6_7_proved G Ω hΩ S A hAset T hTset hAS hTS hAT

structure Frame21 {G : Type} [Group G] (K K' J J' : Subgroup G) (z u t : G)
    (R R' T T' : Subgroup G) (x y : G) : Prop where
  hR : IsSylow2In R K
  hR' : IsSylow2In R' K'
  hT : IsSylow2In T J
  hT' : IsSylow2In T' J'
  cRR' : Commutes R R'
  cRT : Commutes R T
  cR'T : Commutes R' T
  cRT' : Commutes R T'
  cR'T' : Commutes R' T'
  cTT' : Commutes T T'
  Rt : ∀ r ∈ R, r * t = t * r
  R't : ∀ r ∈ R', r * t = t * r
  hx : x ∈ R
  hy : y ∈ R'
  hx2 : x * x = z
  hy2 : y * y = z
  hxy : x * y = u

theorem Frame21.le_centralizer_u {K K' J J' : Subgroup G} {z u t : G} {R R' T T' : Subgroup G}
    {x y : G} (hF : Frame21 K K' J J' z u t R R' T T' x y) :
    T ≤ Subgroup.centralizer ({u} : Set G) ∧ T' ≤ Subgroup.centralizer ({u} : Set G) := by
  have key : ∀ S : Subgroup G, Commutes R S → Commutes R' S →
      S ≤ Subgroup.centralizer ({u} : Set G) := by
    intro S hRS hR'S s hs
    rw [Subgroup.mem_centralizer_singleton_iff, ← hF.hxy]
    have h1 : x * s = s * x := hRS x hF.hx s hs
    have h2 : y * s = s * y := hR'S y hF.hy s hs
    calc s * (x * y) = (s * x) * y := by group
      _ = (x * s) * y := by rw [h1]
      _ = x * (s * y) := by group
      _ = x * (y * s) := by rw [h2]
      _ = (x * y) * s := by group
  exact ⟨key T hF.cRT hF.cR'T, key T' hF.cRT' hF.cR'T'⟩

theorem sq_eq_one_of_natCard_le_two_frame {A : Subgroup G} (h : Nat.card A ≤ 2) {w : G}
    (hw : w ∈ A) : w * w = 1 :=
  CFSG.ClassicalInvolution.Asc77.sq_eq_one_of_natCard_le_two h hw

variable {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.exists_frame (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    ∃ (J' R R' T T' : Subgroup G) (x y : G), J' ∈ twinSet Ω J ∧ J' ≠ J ∧
      IsUniqueInvolution J' t ∧ Frame21 K K' J J' z u t R R' T T' x y := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hK'tw : K' ∈ twinSet Ω K := h.std.hK'
  have hne : K' ≠ K := h.std.hne
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'tw
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJK : J ≠ K := (h.hJ.2 K (mem_twinSet_self hK hz)).2.1
  have hJK' : J ≠ K' := (h.hJ.2 K' hK'tw).2.1
  have hd := h.twinFrameData
  have htz : t ≠ z := hd.t_ne_z
  obtain ⟨g, hg⟩ := h.std.stand.trans J hJΩ
  have hzJ : IsUniqueInvolution J (g * z * g⁻¹) := by
    have := hz.conj g
    rwa [hg] at this
  have hgz : g * z * g⁻¹ = t := hzJ.eq h.ht
  have hJ'Ω : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hJ't : IsUniqueInvolution (conjSub g K') t := by
    have := hzK'.conj g
    rwa [hgz] at this
  have hJ'tw : conjSub g K' ∈ twinSet Ω J := ⟨hJ'Ω, t, h.ht, hJ't⟩
  have hJ'J : conjSub g K' ≠ J := by
    intro hc
    apply hne
    rw [← hg] at hc
    have := congrArg (conjSub g⁻¹) hc
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hJ'K : conjSub g K' ≠ K := fun e => htz (hz.eq (e ▸ hJ't)).symm
  have hJ'K' : conjSub g K' ≠ K' := fun e => htz (hzK'.eq (e ▸ hJ't)).symm
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, -, -, -, hc₀, hRT₀, hR'T₀⟩ :=
    exists_twinSylow hΩ hK hz hK'tw hne h.hJ
  have h8T₀ : 8 ≤ Nat.card T₀ := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hJΩ hT₀)
  have htT₀ : t ∈ T₀ := mem_of_isUniqueInvolution_of_isPGroup h.ht hT₀.1 hT₀.2.1 (by omega)
  have htK : t ∈ Balance.Bootstrap.trivialOnQuot K :=
    mem_trivialOnQuot_of_le_centralizer3 hΩ hK hR₀ h.ht.ne_one h.ht.sq
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hRT₀ r hr t htT₀))
  have htK' : t ∈ Balance.Bootstrap.trivialOnQuot K' :=
    mem_trivialOnQuot_of_le_centralizer3 hΩ hK'Ω hR₀' h.ht.ne_one h.ht.sq
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hR'T₀ r hr t htT₀))
  have hB := twinFrame_isElemAbelian hΩ hd
  have hA2 : IsPGroup 2 (Subgroup.closure ({z, u, t} : Set G)) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 _ hB
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω hne.symm hz hzK'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK'Ω hK hne hzK' hz
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
  obtain ⟨R, hRsyl, hRfix, hBR2, -⟩ := exists_sylow_commuting hΩ hK hA2 hAK (𝒜 := ∅)
    (fun A hA => absurd hA (Set.notMem_empty A))
  have hBRK' : Subgroup.closure ({z, u, t} : Set G) ⊔ R ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le hAK' (hRsyl.1.trans hKN')
  obtain ⟨R', hR'syl, hR'fix, hQ2, hcR⟩ := exists_sylow_commuting hΩ hK'Ω hBR2 hBRK'
    (𝒜 := {R}) (fun A hA => by
      rw [Set.mem_singleton_iff] at hA
      subst hA
      exact ⟨le_sup_right, K, hK, hne.symm, hRsyl⟩)
  have hcomm : Commutes R R' := hcR R rfl
  have htA : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hRR' : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    Q3T8.Asc77.T7A.isSylow2In_sup_of_twin hΩ hK hK'Ω hne hz hzK' hRsyl hR'syl hcomm
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
    hΩ.card_le_two_of_le_inf hK hK'Ω hne.symm (hRsyl.2.1.to_le inf_le_left)
      (inf_le_left.trans hRsyl.1) (inf_le_right.trans hR'syl.1)
  have hww : (x * x) * (x * x) = 1 := sq_eq_one_of_natCard_le_two_frame hcard hw
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
  have h8R : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hK hRsyl)
  have h8R' : 8 ≤ Nat.card R' := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hK'Ω hR'syl)
  have hRc : R ≤ Subgroup.centralizer ({t} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRt r hr)
  have hR'c : R' ≤ Subgroup.centralizer ({t} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hR't r hr)
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJΩ hK hJK h.ht hRsyl.1 hRsyl.2.1 (by omega) hRc
  have hR'J : R' ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJΩ hK'Ω hJK' h.ht hR'syl.1 hR'syl.2.1 (by omega) hR'c
  have hRJ' : R ≤ Subgroup.normalizer ((conjSub g K' : Subgroup G) : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJ'Ω hK hJ'K hJ't hRsyl.1 hRsyl.2.1 (by omega) hRc
  have hR'J' : R' ≤ Subgroup.normalizer ((conjSub g K' : Subgroup G) : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJ'Ω hK'Ω hJ'K' hJ't hR'syl.1 hR'syl.2.1 (by omega) hR'c
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hQ2.to_le (sup_le (le_sup_right.trans le_sup_left)
    le_sup_right)
  obtain ⟨T, hTsyl, -, hPT2, hTc⟩ := exists_sylow_commuting hΩ hJΩ hP2 (sup_le hRJ hR'J)
    (𝒜 := {R, R'}) (fun A hA => by
      rcases hA with rfl | hA
      · exact ⟨le_sup_left, K, hK, hJK.symm, hRsyl⟩
      · rw [Set.mem_singleton_iff] at hA
        subst hA
        exact ⟨le_sup_right, K', hK'Ω, hJK'.symm, hR'syl⟩)
  have hTN : T ≤ Subgroup.normalizer ((conjSub g K' : Subgroup G) : Set G) :=
    hTsyl.1.trans (hΩ.le_normalizer_of_twin hJΩ hJ'Ω hJ'J.symm h.ht hJ't)
  obtain ⟨T', hT'syl, -, -, hT'c⟩ := exists_sylow_commuting hΩ hJ'Ω hPT2
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

theorem Hyp21.mem_tqMembers_u_J (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    J ∈ ExactLayer.tqMembers Ω u := by
  obtain ⟨J', R, R', T, T', x, y, -, -, -, hF⟩ := h.exists_frame
  exact (ExactLayer.mem_tqMembers_iff_exists_sylow h.std.stand.modU
    (ExactLayer.isPGroup_zpowers_of_sq_eq_one h.hu2)).mpr ⟨h.hJ.1, T, hF.hT, hF.le_centralizer_u.1⟩

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8
