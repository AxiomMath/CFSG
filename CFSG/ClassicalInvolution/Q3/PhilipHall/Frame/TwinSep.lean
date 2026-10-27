module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMaxOrb
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExact
public import CFSG.ClassicalInvolution.SmallCases.A7Q1
public import CFSG.ClassicalInvolution.Q3.TL4SepSub

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def Thm4RTwinBelow (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Δ : Set (Subgroup X),
    HypOmegaGen Δ → (∀ J ∈ Δ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) →
    (∀ J ∈ Δ, ∀ P : Subgroup X, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))) →
    (∀ J ∈ Δ, AEmpty Δ J) → classicalInvolutionOddCore X = ⊥ →
    ∀ J ∈ Δ, ∀ L ∈ Δ, (¬ ∃ g : X, conjSub g J = L) → Commutes J L

theorem Thm4RTwinBelow.mono {r m n : ℕ} (hmn : m ≤ n) (h : Thm4RTwinBelow r n) :
    Thm4RTwinBelow r m :=
  fun X _ _ hX => h X (lt_of_lt_of_le hX hmn)

namespace TwinSep

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def perpGen (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G :=
  ⨆ M ∈ KPerp Ω K, M

omit [Finite G] in
theorem le_perpGen {K M : Subgroup G} (hM : M ∈ KPerp Ω K) : M ≤ perpGen Ω K :=
  le_iSup₂_of_le M hM le_rfl

omit [Finite G] in
theorem perpGen_le {K H : Subgroup G} (h : ∀ M ∈ KPerp Ω K, M ≤ H) :
    perpGen Ω K ≤ H :=
  iSup₂_le h

theorem commutes_of_mem_omegaNbr (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) : Commutes K J := by
  have h1 := (mem_omegaNbr_iff hΩ h2).mp hJ
  have hKJ : K ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK h1.1 hJ
  have h1' := (mem_omegaNbr_iff hΩ h2).mp hKJ
  exact commutes_of_mutual_normalizer hΩ h2 hK h1.1 (Ne.symm h1.2.1) h1'.2.2 h1.2.2

theorem perpGen_le_centralizer (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    perpGen Ω K ≤ Subgroup.centralizer ({z} : Set G) := by
  refine perpGen_le fun M hM => ?_
  rcases Set.mem_insert_iff.mp hM with rfl | hM
  · exact le_centralizer_of_unique hz
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commutes_of_mem_omegaNbr hΩ h2 hK hM z hz.mem x hx).symm

theorem centralizer_le_normalizer_perpGen (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (perpGen Ω K : Set G) := by
  have key : ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c (perpGen Ω K) ≤ perpGen Ω K := by
    intro c hc
    have hcz : c * z * c⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      rw [hc, mul_inv_cancel_right]
    have hKc : conjSub c K ∈ twinSet Ω K := by
      have h1 := hz.conj c
      rw [hcz] at h1
      exact ⟨hΩ.conjInvariant c K hK, z, hz, h1⟩
    have hperp := A7Q.Gen.kPerp_eq_of_twin hΩ hK hKc
    show (perpGen Ω K).map (MulAut.conj c).toMonoidHom ≤ perpGen Ω K
    rw [Subgroup.map_le_iff_le_comap]
    refine perpGen_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    show conjSub c M ≤ perpGen Ω K
    refine le_perpGen ?_
    rw [hperp]
    rcases Set.mem_insert_iff.mp hM with rfl | hM
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (omegaNbr_conj hΩ.conjInvariant hM c)
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key c hc (conj_mem_conjSub hh)
  · intro hh
    have hc' : c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hc
    have h1 := key c⁻¹ hc' (conj_mem_conjSub hh)
    simpa [mul_assoc] using h1

theorem le_centralizer_nbrGen (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) :
    K ≤ Subgroup.centralizer (nbrGen (nbrAdj Ω) K : Set G) := by
  have hle : nbrGen (nbrAdj Ω) K ≤ Subgroup.centralizer (K : Set G) := by
    refine nbrGen_le fun J hJ => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact commutes_of_mem_omegaNbr hΩ h2 hK hJ.2 x hx y hy
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) x hx).symm

omit [Finite G] in
theorem nbrGen_le_perpGen {K : Subgroup G} : nbrGen (nbrAdj Ω) K ≤ perpGen Ω K :=
  nbrGen_le fun _ hJ => le_perpGen (Set.mem_insert_of_mem _ hJ.2)

theorem nbrGen_normal_perpGen (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) :
    ((nbrGen (nbrAdj Ω) K).subgroupOf (perpGen Ω K)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer nbrGen_le_perpGen).mpr ?_
  refine perpGen_le fun M hM => ?_
  rcases Set.mem_insert_iff.mp hM with rfl | hM
  · exact (le_centralizer_nbrGen hΩ h2 hK).trans (Subgroup.centralizer_le_normalizer _)
  · exact (le_nbrGen (A := nbrAdj Ω) (⟨hK, hM⟩ : nbrAdj Ω K M)).trans
      (Subgroup.le_normalizer)

theorem isSubnormal_nbrGen (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    IsSubnormal (nbrGen (nbrAdj Ω) K) (Subgroup.centralizer ({z} : Set G)) := by
  refine IsSubnormal.step nbrGen_le_perpGen (nbrGen_normal_perpGen hΩ h2 hK) ?_
  refine IsSubnormal.step (perpGen_le_centralizer hΩ h2 hK hz) ?_ (IsSubnormal.refl _)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (perpGen_le_centralizer hΩ h2 hK hz)).mpr
    (centralizer_le_normalizer_perpGen hΩ hK hz)

theorem oddCore_nbrGen_eq_bot (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hθ : classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥(nbrGen (nbrAdj Ω) K) = ⊥ := by
  have hle := TwinExact.oddCoreOf_le_of_isSubnormal (isSubnormal_nbrGen hΩ h2 hK hz)
  have hbot : oddCoreOf (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
    show (classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set G))).map _ = ⊥
    rw [hθ, Subgroup.map_bot]
  rw [hbot, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hle

theorem card_nbrGen_lt (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hZ : Subgroup.center G = ⊥) : Nat.card (nbrGen (nbrAdj Ω) K) < Nat.card G := by
  have hle : nbrGen (nbrAdj Ω) K ≤ Subgroup.centralizer ({z} : Set G) :=
    nbrGen_le_perpGen.trans (perpGen_le_centralizer hΩ h2 hK hz)
  have hne : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro h
    have hc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : x ∈ Subgroup.centralizer ({z} : Set G) := by rw [h]; trivial
      exact Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [hZ, Subgroup.mem_bot] at hc
    exact hz.ne_one hc
  have hlt : nbrGen (nbrAdj Ω) K < ⊤ := lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hne)
  have := Subgroup.card_lt_of_lt hlt
  rwa [Subgroup.card_top] at this

end TwinSep

open TwinSep

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem sepHyp_of_thm4RTwin {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hn : Nat.card G ≤ n)
    (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (hq8 : ∀ J ∈ Ω, Nonempty (↥J ≃* QuaternionGroup 2)) (hA : ∀ J ∈ Ω, AEmpty Ω J)
    (hZ : Subgroup.center G = ⊥)
    (hθ : ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set G)) = ⊥) :
    SepHyp Ω := by
  intro K J J' hKJ hKJ' hnot
  have hK : K ∈ Ω := hKJ.1
  have hJΩ : J ∈ Ω := hKJ.2.1
  have hJ'Ω : J' ∈ Ω := hKJ'.2.1
  obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K hK
  set H := nbrGen (nbrAdj Ω) K with hHdef
  have hJH : J ≤ H := le_nbrGen hKJ
  have hJ'H : J' ≤ H := le_nbrGen hKJ'
  have hOH := oddCore_nbrGen_eq_bot hΩ h2 hK hz (hθ K hK z hz)
  have hHn : Nat.card H < n := lt_of_lt_of_le (card_nbrGen_lt hΩ h2 hK hz hZ) hn
  have hΩH : HypOmegaGen (restrictFamily Ω H) := hypOmegaGen_restrict hΩ H
  have h2H : ∀ M ∈ restrictFamily Ω H, IsPGroup 2 ↥M := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    exact (h2 L hL).of_equiv (Subgroup.subgroupOfEquivOfLe hLH).symm
  have htwo : ∀ M ∈ restrictFamily Ω H, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    fun M hM => (h2H M hM).to_quotient _
  have hquat : ∀ M ∈ restrictFamily Ω H, ∀ P : Subgroup ↥H, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    rintro _ ⟨L, hL, hLH, rfl⟩ P hP
    have hPeq : P = L.subgroupOf H :=
      (hP.2.2 _ le_rfl (h2H _ ⟨L, hL, hLH, rfl⟩) hP.1).symm
    subst hPeq
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLH).trans (hq8 L hL).some⟩
  have hAH : ∀ M ∈ restrictFamily Ω H, AEmpty (restrictFamily Ω H) M := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    exact aEmpty_restrictFamily hΩ h2 subset_rfl hLH (hA L hL)
  have hc := h4 ↥H hHn (restrictFamily Ω H) hΩH htwo hquat hAH hOH (J.subgroupOf H)
    ⟨J, hJΩ, hJH, rfl⟩ (J'.subgroupOf H) ⟨J', hJ'Ω, hJ'H, rfl⟩ (fun hex => by
      obtain ⟨g, hgH, hg⟩ := TL4.exists_conjSub_of_restrict hJH hJ'H hex
      exact hnot ⟨g, hgH, hg⟩)
  have hcomm : Commutes J J' := TL4.commutes_of_restrict hJH hJ'H hc
  have hne : J' ≠ J := fun h => hnot (by rw [h]; exact mem_orbOf_self K J)
  exact nbrAdj_of_commutes hΩ h2 hJΩ hJ'Ω hne hcomm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
