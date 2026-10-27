module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecEL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open scoped MatrixGroups

section Twins

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem noTwins_of_dEdgeless (hΩ : HypOmegaGen Φ) (hE : Disconnected.DEdgeless Φ) {L : Subgroup X}
    (hL : L ∈ Φ) : ∀ K' ∈ twinSet Φ L, K' = L := by
  rintro K' ⟨hK', z, hzL, hzK'⟩
  by_contra hne
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K') := inferInstance
  have hR : (Q : Subgroup K').map K'.subtype ∈ RSet Φ := ⟨K', hK', Q, rfl⟩
  have hnb : K' ∈ omegaNbr Φ L :=
    ⟨hK', hne, _, hR, Subgroup.map_subtype_le _,
      (Subgroup.map_subtype_le _).trans (Sec6Gen.le_normalizer_of_twin hΩ hK' hL hne hzK' hzL)⟩
  exact hE L hL K' hK' (Or.inl hnb)

end Twins

section Core

variable {G : Type} [Group G]

theorem not_isPGroup_sl2_three : ¬ IsPGroup 2 SL(2, ZMod 3) := by
  intro h
  obtain ⟨x, h3, hne⟩ : ∃ x : SL(2, ZMod 3), x ^ 3 = 1 ∧ x ≠ 1 := by decide
  obtain ⟨k, hk⟩ := h x
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have hord : orderOf x ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h3)
  rw [hcop] at hord
  exact hne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord))

theorem tightCore_eq_of_two {Ω : Set (Subgroup G)} [Finite G] (hΩ : HypOmegaGen Ω) {L : Subgroup G}
    (hL : L ∈ Ω) (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) : tightCore L = L := by
  rcases hΩ.omega2 L hL with h | h
  · exact h
  · obtain ⟨e⟩ := h
    exact absurd (h2.of_equiv e) not_isPGroup_sl2_three

end Core

section Datum

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem exists_datum_of_edgeless (hS : TwinDisc.Q8Section X Φ)
    (htr : ∀ K ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g K = M) (hE : Disconnected.DEdgeless Φ)
    {L : Subgroup X} (hL : L ∈ Φ) :
    ∃ (S : Sylow 2 ↥L) (z : X), IsUniqueInvolution L z ∧ TightDatum L S z ∧ TightCls X L S z ∧
      CoreAssembly.conjClass (tightCore L) = Φ := by
  have hΩ := hS.hyp
  have hcore : tightCore L = L := tightCore_eq_of_two hΩ hL (hS.two L hL)
  have hnt := noTwins_of_dEdgeless hΩ hE hL
  obtain ⟨z, hz⟩ := (hΩ.omega1 L hL).1
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hP₀ : IsSylow2In ((S : Subgroup L).map L.subtype) L := isSylow2In_map_sylow L S
  obtain ⟨e⟩ := hS.q8 L hL _ hP₀
  have eS : ↥(S : Subgroup L) ≃* QuaternionGroup 2 :=
    ((S : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).trans e
  have hcard : 8 ≤ Nat.card ↥((S : Subgroup L).map L.subtype) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcent : L ≤ Subgroup.centralizer ({z} : Set X) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hx).symm
  have hd : TightDatum L S z :=
    { quat := ⟨3, le_rfl, ⟨eS⟩⟩
      mem := T3.mem_of_isPGroup hz (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
        (le_trans (by norm_num) hcard)
      order := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
      cent := hcent
      normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hcent).mpr
        (Asc77.T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hL hnt hz)
      twoGroup := hS.two L hL }
  have hcl : CoreAssembly.conjClass (tightCore L) = Φ := by
    rw [hcore]
    ext M
    constructor
    · rintro ⟨g, rfl⟩
      exact hΩ.conjInvariant g L hL
    · intro hM
      exact htr L hL M hM
  refine ⟨S, z, hz, hd, ⟨⟨eS⟩, ?_, hS.oddFree⟩, hcl⟩
  show (⨆ g : X, conjSub g (tightCore L)) = ⊤
  rw [hcore, eq_top_iff, ← hS.gen]
  refine iSup₂_le fun M hM => ?_
  obtain ⟨g, rfl⟩ := htr L hL M hM
  exact le_iSup (fun g : X => conjSub g L) g

end Datum

theorem normalizer_le_centralizer_of_unique {X : Type} [Group X] {L : Subgroup X} {z : X}
    (hz : IsUniqueInvolution L z) :
    Subgroup.normalizer (L : Set X) ≤ Subgroup.centralizer ({z} : Set X) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hg)
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h1]

section Block

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

def sigmaStab (Φ : Set (Subgroup X)) (hΦ : ConjInvariant Φ) (K : Subgroup X) : Subgroup X where
  carrier := {g | ∀ J : Subgroup X, J ∈ dstarComp Φ K ↔ conjSub g J ∈ dstarComp Φ K}
  mul_mem' := fun {g h} hg hh J => by
    rw [hh J, hg (conjSub h J), conjSub_mul]
  one_mem' := fun J => by rw [conjSub_one]
  inv_mem' := fun {g} hg J => by
    have := hg (conjSub g⁻¹ J)
    rw [conjSub_conjSub_inv] at this
    exact this.symm

theorem normalizer_le_sigmaStab (hΦ : ConjInvariant Φ) {K : Subgroup X} (hK : K ∈ Φ) :
    Subgroup.normalizer (K : Set X) ≤ sigmaStab Φ hΦ K := by
  intro g hg J
  have hgK : conjSub g K = K := mem_normalizer_iff_conjSub_eq.mp hg
  have hgK' : conjSub g⁻¹ K = K := mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer _).inv_mem hg)
  constructor
  · intro hJ
    have := dstarComp_conj hΦ hJ g
    rwa [hgK] at this
  · intro hJ
    have := dstarComp_conj hΦ hJ g⁻¹
    rwa [hgK', conjSub_inv_conjSub] at this

theorem normalizer_le_sigmaStab_of_mem (hΦ : ConjInvariant Φ) {K J : Subgroup X} (hK : K ∈ Φ)
    (hJ : J ∈ dstarComp Φ K) : Subgroup.normalizer (J : Set X) ≤ sigmaStab Φ hΦ K := by
  have hKJ : K ∈ dstarComp Φ J := (T3.mem_dstarComp_symm hK hJ).2
  intro g hg J'
  have hgJ : conjSub g J = J := mem_normalizer_iff_conjSub_eq.mp hg
  have hgJ' : conjSub g⁻¹ J = J := mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer _).inv_mem hg)
  constructor
  · intro h
    have h1 := dstarComp_conj hΦ (hKJ.trans h) g
    rw [hgJ] at h1
    exact hJ.trans h1
  · intro h
    have h1 := dstarComp_conj hΦ (hKJ.trans h) g⁻¹
    rw [hgJ', conjSub_inv_conjSub] at h1
    exact hJ.trans h1

variable [Finite X] in
theorem omegaStarNbr_eq_empty_of_gen (hΩ : HypOmegaGen Φ) (hE : Disconnected.DEdgeless Φ)
    (htr : ∀ K ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g K = M)
    (hgen : ∀ a b : X, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → b ≠ a → a * b = b * a →
      Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) = ⊤)
    (hdisc : ¬ T3.DStarConnected Φ) : ∀ M ∈ Φ, omegaStarNbr Φ M = ∅ := by
  intro M hM
  refine Set.eq_empty_iff_forall_notMem.mpr fun J hJ => ?_
  have hJ0 := hJ
  obtain ⟨hJΦ, hne, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨zM, hzM⟩ := (hΩ.omega1 M hM).1
  obtain ⟨zJ, hzJ⟩ := (hΩ.omega1 J hJΦ).1
  have hzJU : zJ ∈ U := by
    obtain ⟨R, -, J', -, hRJ', hUR, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
    exact T3.mem_of_isPGroup hzJ hUJ (Sec6Gen.isPGroup_of_mem_USet hΩ hU) (by omega)
  have hzJN : zJ ∈ Subgroup.normalizer (M : Set X) := hUN hzJU
  have hzJC : zJ ∈ Subgroup.centralizer ({zM} : Set X) :=
    normalizer_le_centralizer_of_unique hzM hzJN
  have hcomm : zM * zJ = zJ * zM := (Subgroup.mem_centralizer_singleton_iff.mp hzJC).symm
  have hzne : zJ ≠ zM := fun h => hne (noTwins_of_dEdgeless hΩ hE hM J ⟨hJΦ, zM, hzM, h ▸ hzJ⟩)
  have hgen' := hgen zM zJ hzM.sq hzM.ne_one hzJ.sq hzJ.ne_one hzne hcomm
  have hnt : ∀ L ∈ Φ, ∀ K' ∈ twinSet Φ L, K' = L := fun L hL => noTwins_of_dEdgeless hΩ hE hL
  have hsig : J ∈ dstarComp Φ M := Relation.ReflTransGen.single ⟨hJΦ, Or.inl hJ0⟩
  have hNM := normalizer_le_sigmaStab hΩ.conjInvariant hM
  have hNJ := normalizer_le_sigmaStab_of_mem hΩ.conjInvariant hM hsig
  have hCM : Subgroup.centralizer ({zM} : Set X) ≤ sigmaStab Φ hΩ.conjInvariant M :=
    (Asc77.T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) hzM).trans hNM
  have hCJ : Subgroup.centralizer ({zJ} : Set X) ≤ sigmaStab Φ hΩ.conjInvariant M :=
    (Asc77.T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΦ (hnt J hJΦ) hzJ).trans hNJ
  have htop : sigmaStab Φ hΩ.conjInvariant M = ⊤ :=
    top_unique (hgen' ▸ sup_le hCM hCJ)
  apply hdisc
  refine T3.dstarConnected_of_pivot hM fun M' hM' => ?_
  obtain ⟨g, rfl⟩ := htr M hM M' hM'
  have hg : g ∈ sigmaStab Φ hΩ.conjInvariant M := by rw [htop]; exact Subgroup.mem_top g
  exact (hg M).mp Relation.ReflTransGen.refl

end Block

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecEL
