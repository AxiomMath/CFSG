module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Ih
public import CFSG.ClassicalInvolution.Q3.Q3T7F25PW
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Q8P
abbrev _root_.CFSG.ClassicalInvolution.Q8P.Asc77.Hyp25Data :=
  @CFSG.ClassicalInvolution.Asc77.Hyp25Data
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
@[expose] def L6_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod Ω →
      ∀ S : Sylow 2 G, ∀ U ∈ USet Ω, U ≤ (S : Subgroup G) → ∀ η ∈ etaG Ω,
        (∀ V ∈ η, V ≤ (S : Subgroup G)) →
          ∃! V : Subgroup G, V ∈ η ∧ (U = V ∨ (U ⊔ V) ∈ RSet Ω)
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Std7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  ih : Q3.PhilipHall.Frame.TwinThmE.EIHAll (Nat.card G)
  quot2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
theorem l6_8 : L6_8 :=
  CFSG.ClassicalInvolution.T7F25.Asc77.l6_8
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def Hyp23 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop :=
  Std7 Ω K K' z ∧ KPerp Ω K = {K, K'}
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G]
section Mu
variable {Ω : Set (Subgroup G)}
theorem conjSub_MGrp [Finite G] (hΩ : HypOmegaMod Ω) (g : G) (W : Subgroup G) :
    conjSub g (MGrp Ω W) = MGrp Ω (conjSub g W) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.Thompson.conjSub_MGrp hΩ g W
noncomputable def muGroupConjEquiv [Finite G] (hΩ : HypOmegaMod Ω) (g : G) (W : Subgroup G) :
    ↥(muGroup Ω W) ≃* ↥(muGroup Ω (conjSub g W)) :=
  (MulEquiv.subgroupMap (nquotConj g (conjSub_sup_OCW g W)) (muGroup Ω W)).trans
    (MulEquiv.subgroupCongr (by
      ext q
      constructor
      · rintro ⟨q₀, hq₀, rfl⟩
        obtain ⟨m, hm, rfl⟩ := mem_muGroup_iff.mp hq₀
        have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
        show nquotConj g (conjSub_sup_OCW g W) (piG W m) ∈ _
        rw [nquotConj_piG g W hmN]
        refine piG_mem_muGroup ?_
        rw [← conjSub_MGrp hΩ, ← conjSub_OCW, ← Asc77.conjSub_sup]
        exact conj_mem_conjSub hm
      · intro hq
        obtain ⟨m', hm', rfl⟩ := mem_muGroup_iff.mp hq
        rw [← conjSub_MGrp hΩ, ← conjSub_OCW, ← Asc77.conjSub_sup, mem_conjSub_iff] at hm'
        refine ⟨piG W (g⁻¹ * m' * g), piG_mem_muGroup hm', ?_⟩
        have hmN : g⁻¹ * m' * g ∈ Subgroup.normalizer (W : Set G) :=
          MGrp_sup_le_normalizer Ω W hm'
        show nquotConj g (conjSub_sup_OCW g W) (piG W (g⁻¹ * m' * g)) = _
        rw [nquotConj_piG g W hmN]
        congr 1
        group))
end Mu
end Thompson
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
section Existence
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem exists_W_of_mem_omegaStarNbr (hΩ : HypOmegaMod Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaStarNbr Ω K) :
    ∃ W ∈ WSet Ω, ∃ R ∈ DSet Ω W, ∃ T ∈ DSet Ω W, IsSylow2In R K ∧ IsSylow2In T J :=
  CFSG.ClassicalInvolution.T7F25.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hK hJ
end Existence
end Thompson
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

structure Hyp25 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G) : Prop where
  std : Hyp23 Ω K K' z
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W'
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hRS : ∀ X ∈ RSet Ω, X ≤ (S : Subgroup G) → X = R ∨ X = R'
  hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s
  ht : t ∈ (S : Subgroup G) ∧ t ≠ z ∧ ∃ g : G, g * z * g⁻¹ = t
  hu₁ : u₁ ∈ R ∧ orderOf u₁ = 4 ∧ ∀ r ∈ R, r * u₁ * r⁻¹ ∈ Subgroup.zpowers u₁
  hu₂ : u₂ ∈ R' ∧ orderOf u₂ = 4 ∧ ∀ r ∈ R', r * u₂ * r⁻¹ ∈ Subgroup.zpowers u₂

@[expose] def C25_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
        Subgroup.zpowers z

@[expose] def C25_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a

@[expose] def C25_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') ∨ TwoSubgroupsFourGenerated G

@[expose] def C25_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') → TwoSubgroupsFourGenerated G

@[expose] def C25_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → (∀ W' ∈ WSet Ω, MuIsoE4 Ω W') →
      ∃ (S : Sylow 2 G) (R R' : Subgroup G) (t u₁ u₂ : G), Hyp25 Ω K K' W S R R' z t u₁ u₂

@[expose] def C25_E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → (∀ W' ∈ WSet Ω, MuIsoE4 Ω W') → TwoSubgroupsFourGenerated G

theorem c25_E4_of_steps (hsetup : C25_setup) (h19 : C25_19) (h21 : C25_21) :
    C25_E4 := by
  intro G _ _ _ Ω K K' z hs W hW hzW hE4
  obtain ⟨S, R, R', t, u₁, u₂, hyp⟩ := hsetup G Ω K K' z hs W hW hzW hE4
  rcases h19 G Ω K K' W S R R' z t u₁ u₂ hyp with h | h
  · exact h21 G Ω K K' W S R R' z t u₁ u₂ hyp h
  · exact h
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Hyp23Setting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  perp : KPerp Ω K = {K, K'}

section

theorem _root_.CFSG.ClassicalInvolution.Q8P.Asc77.Std7.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Q8P.Asc77.Std7 Ω K K' z) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Std7 Ω K K' z where
  stand := h.stand.toF
  disconnected := h.disconnected
  hz := h.hz
  hK' := h.hK'
  hne := h.hne

theorem _root_.CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23 Ω K K' z) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Hyp23 Ω K K' z :=
  ⟨h.1.toF, h.2⟩

theorem _root_.CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Hyp23Setting Ω K K' z where
  stand := h.stand.toF
  disconnected := h.disconnected
  hz := h.hz
  hK' := h.hK'
  hne := h.hne
  perp := h.perp

theorem _root_.CFSG.ClassicalInvolution.Q8P.Asc77.Hyp25.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}
    (h : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂ :=
  { h with std := h.std.toF }

end
section Basic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem Hyp23.setting (h : Hyp23 Ω K K' z) : Hyp23Setting Ω K K' z where
  stand := h.1.stand
  disconnected := h.1.disconnected
  hz := h.1.hz
  hK' := h.1.hK'
  hne := h.1.hne
  perp := h.2

theorem Hyp23Setting.twinSet_eq (h : Hyp23Setting Ω K K' z) : twinSet Ω K = {K, K'} :=
  CFSG.ClassicalInvolution.T7F25.Asc77.Hyp23Setting.twinSet_eq h.toF
end Basic
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Conversions
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z u t u₁ u₂ : G}

theorem Hyp25Data.hyp25 (h : Hyp25Data Ω K K' W S R R' z t u₁ u₂) (hs : Hyp23 Ω K K' z)
    (hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W') :
    Hyp25 Ω K K' W S R R' z t u₁ u₂ where
  std := hs
  hW := h.hW
  hzW := h.hzW
  hE4 := hE4
  hR := h.hR
  hR' := h.hR'
  hRS := h.hRS
  hzS := h.hzS
  ht := h.ht
  hu₁ := h.hu₁
  hu₂ := h.hu₂
end Conversions
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem isSylow2In_of_mem_RSet_of_le (hΩ : HypOmegaMod Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hR hRK
end T7C
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
    CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
    CFSG.LieType.CurtisTits CFSG.Blueprint
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C

theorem exists_not_commute_of_stand {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (hs : AscStand Ω K) : ∃ a b : G, a * b ≠ b * a :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7C.exists_not_commute_of_stand hs.toF

theorem exists_conj_mem_sylow_ne_core {G : Type} [Group G] [Finite G] [CoreLike G]
    (S : Sylow 2 G) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) ∧ g⁻¹ * z * g ≠ z := by
  by_contra hcon
  push Not at hcon
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hord : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hzord
  have hzZ : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hzc s s.2)
  obtain ⟨hdec, -⟩ := CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzZ hord hcon
  have hzcen : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hdec g
    rw [CoreLike.oddCore_eq_bot, Subgroup.mem_bot] at hk
    subst hk
    rw [mul_one]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc)
  rw [CoreLike.center_eq_bot, Subgroup.mem_bot] at hzcen
  exact hz1 hzcen

theorem hom_eq_one_of_sylow {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (hs : AscStand Ω K) {J R : Subgroup G} (hJ : J ∈ Ω) (hR : IsSylow2In R J)
    {A : Type*} [CommGroup A] (f : G →* A) (hf : ∀ x ∈ R, f x = 1) : f = 1 := by
  have hconj : ∀ (h : G) (x : G), x ∈ conjSub h R → f x = 1 := by
    intro h x hx
    have hx' : h⁻¹ * x * h ∈ R := mem_conjSub_iff.mp hx
    have := hf _ hx'
    simpa [map_mul, map_inv, mul_comm] using this
  have hmem : ∀ J' ∈ Ω, ∀ x ∈ J', f x = 1 := by
    intro J' hJ' 
    obtain ⟨g₁, hg₁⟩ := hs.trans J' hJ'
    obtain ⟨g₂, hg₂⟩ := hs.trans J hJ
    have hJJ : conjSub (g₁ * g₂⁻¹) J = J' := by
      rw [← hg₁, ← hg₂]
      ext y
      simp only [mem_conjSub_iff]
      constructor <;> intro h <;> convert h using 1 <;> group
    have hP : IsSylow2In (conjSub (g₁ * g₂⁻¹) R) J' := hJJ ▸ hR.conj _
    have hker : J' ≤ f.ker := by
      refine hs.gen2 J' hJ' f.ker (fun x hx hx2 => ?_)
      obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge hx2 (Subgroup.zpowers_le.mpr hx)
      obtain ⟨c, -, hc⟩ := exists_conjSub_eq_of_isSylow2In hP hV
      have hxV' : x ∈ conjSub c (conjSub (g₁ * g₂⁻¹) R) := hc ▸ hxV (Subgroup.mem_zpowers x)
      rw [mem_conjSub_iff] at hxV'
      have h1 := hconj (g₁ * g₂⁻¹) _ hxV'
      rw [MonoidHom.mem_ker]
      simpa [map_mul, map_inv, mul_comm] using h1
    exact fun x hx => MonoidHom.mem_ker.mp (hker hx)
  ext g
  have : g ∈ (⨆ J ∈ Ω, J) := hs.gen ▸ Subgroup.mem_top g
  have hle : (⨆ J ∈ Ω, J) ≤ f.ker := iSup₂_le fun J' hJ' x hx => hmem J' hJ' x hx
  simpa using hle this
end T7C
variable {G : Type} [Group G] [CoreLike G]
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2

@[expose] def C25_2_t : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∃ t' ∈ (S : Subgroup G), (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R'

@[expose] def C25_17_idx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R') ∨
        Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')
theorem c25_19_of_sylow (h2 : C25_2_t) (h17 : C25_17_idx) : C25_19 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  exact CFSG.ClassicalInvolution.T7F25.Asc77.c25_19_of_sylow_at hyp.toF
    (h2 G Ω K K' W S R R' z t u₁ u₂ hyp) (h17 G Ω K K' W S R R' z t u₁ u₂ hyp)
end Asc77
end
end CFSG.ClassicalInvolution.Q8P
