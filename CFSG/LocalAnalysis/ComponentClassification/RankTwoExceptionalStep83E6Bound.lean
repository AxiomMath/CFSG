module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83Pair
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverLevi
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverPullback
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.LeviA2Diag
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3007
public import Certificates.Certificate3951
public import Certificates.Certificate10005
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Step83Proof

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.EvenSmallLie.TwoE6
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Steinberg.TwistedE6
open CFSG.LieType.Steinberg.Exceptional
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

section Fibre

theorem map_snd_fibre_of_surjective
    {X : Type} [Group X] {π : X →* stdGroup}
    (hπ : Function.Surjective π) : (fibre π).map (MonoidHom.snd _ _) = ⊤ := by
  refine eq_top_iff.2 fun u _ => ?_
  obtain ⟨x, hx⟩ := hπ (isogenyStd u)
  exact ⟨(x, u), hx, rfl⟩

theorem commutator_fibre_of_sq
    {X : Type} [Group X] {π : X →* stdGroup}
    [Group.IsPerfect X] (hπ : Function.Surjective π) (h2 : ∀ z ∈ π.ker, z ^ 2 = 1) :
    ⁅fibre π, fibre π⁆ = fibre π := by
  have := isPerfect_twistedE6Group
  refine le_antisymm (commutator_self_le _) fun x hx => ?_
  have hfst : (⁅fibre π, fibre π⁆).map (MonoidHom.fst _ _) = ⊤ := by
    rw [map_commutator, map_fst_fibre, commutator_top_eq_top]
  have hsnd : (⁅fibre π, fibre π⁆).map (MonoidHom.snd _ _) = ⊤ := by
    rw [map_commutator, map_snd_fibre_of_surjective hπ, commutator_top_eq_top]
  obtain ⟨y, hy, hyx⟩ : x.2 ∈ (⁅fibre π, fibre π⁆).map (MonoidHom.snd _ _) := hsnd ▸ mem_top _
  change y.2 = x.2 at hyx
  have hyP : y ∈ fibre π := commutator_self_le _ hy
  set z := x.1 * y.1⁻¹
  have hz : z ∈ π.ker := by
    have h1 : π x.1 = isogenyStd x.2 := hx
    have h2' : π y.1 = isogenyStd y.2 := hyP
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2', hyx, mul_inv_cancel]
  obtain ⟨w, hw, hwz⟩ : z ∈ (⁅fibre π, fibre π⁆).map (MonoidHom.fst _ _) := hfst ▸ mem_top _
  change w.1 = z at hwz
  have hwP : w ∈ fibre π := commutator_self_le _ hw
  have hn : w.2 ∈ isogenyStd.ker := by
    have h : π w.1 = isogenyStd w.2 := hwP
    rw [hwz, show π z = 1 from hz] at h
    exact h.symm
  have hw3 : w ^ 3 = (z, 1) := Prod.ext (by
    rw [Prod.pow_fst, hwz]
    rw [show z ^ 3 = z * z ^ 2 by group, h2 z hz, mul_one]) (by
    rw [Prod.pow_snd, pow_three_eq_one_of_mem_ker_isogenyStd hn])
  have hx' : x = (z, 1) * y := Prod.ext (by simp [z]) (by
    change x.2 = 1 * y.2
    rw [one_mul, hyx])
  rw [hx', ← hw3]
  exact mul_mem (pow_mem hw 3) hy

theorem fibreHom_surjective_of_surjective
    {X : Type} [Group X] {π : X →* stdGroup}
    (hπ : Function.Surjective π) : Function.Surjective (fibreHom π) := by
  intro u
  obtain ⟨x, hx⟩ := hπ (isogenyStd u)
  exact ⟨⟨(x, u), hx⟩, rfl⟩

theorem ker_fibreHom_le_center_of_le
    {X : Type} [Group X] {π : X →* stdGroup}
    (hZ : π.ker ≤ center X) : (fibreHom π).ker ≤ center (fibre π) := by
  intro x hx
  have hc : (x : X × twistedE6Group 2 1) ∈ center (X × twistedE6Group 2 1) := by
    rw [Subgroup.center_prod]
    refine ⟨hZ (fst_mem_ker_of_mem_ker_fibreHom hx), ?_⟩
    rw [show (x : X × twistedE6Group 2 1).2 = 1 from hx]
    exact one_mem _
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.1 hc y)

end Fibre

theorem commutatorElement_mul_mem_center {F : Type*} [Group F] {a b c d : F}
    (hc : c ∈ center F) (hd : d ∈ center F) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' := mem_center_iff.mp hc
  have hd' := mem_center_iff.mp hd
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹ = a * (c * b) * (d * c⁻¹) * a⁻¹ * d⁻¹ * b⁻¹ := by
        group
    _ = a * (b * c) * (c⁻¹ * d) * a⁻¹ * d⁻¹ * b⁻¹ := by
        rw [(hc' b).symm, show d * c⁻¹ = c⁻¹ * d from mem_center_iff.mp (inv_mem hc) d]
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [(hd' a⁻¹).symm]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem card_ker_le_four_of_U
    {F : Type} [Group F] [Finite F] [Group.IsPerfect F] (η : F →* twistedE6Group 2 1)
    (hη : Function.Surjective η) (hC : η.ker ≤ center F) (h2 : ∀ c ∈ η.ker, c ^ 2 = 1) :
    Nat.card η.ker ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : IsPGroup 2 η.ker := fun c => ⟨1, Subtype.ext (by simpa using h2 c c.2)⟩
  have hle := ker_le_commutator_comap_levi34 η hη hC hp2
  set Q := ((twistedE6Datum 2 1).levi levi34).comap η with hQ
  set D := ⁅Q, Q⁆ with hD
  have hmap : D.map η = (twistedE6Datum 2 1).levi levi34 := map_commutator_comap_levi34 η hη
  have hDQ : D ≤ Q := commutator_self_le Q
  have hdec : ∀ x ∈ Q, ∃ d ∈ D, d⁻¹ * x ∈ η.ker := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ : η x ∈ D.map η := by rw [hmap]; exact hx
    exact ⟨d, hd, by rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]⟩
  have hDperf : ⁅D, D⁆ = D := by
    refine le_antisymm (commutator_self_le D) ?_
    conv_lhs => rw [hD]
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨d, hd, hdk⟩ := hdec x hx
    obtain ⟨e, he, hek⟩ := hdec y hy
    have h1 : ⁅x, y⁆ = ⁅d * (d⁻¹ * x), e * (e⁻¹ * y)⁆ := by
      rw [mul_inv_cancel_left, mul_inv_cancel_left]
    rw [h1, commutatorElement_mul_mem_center (hC hdk) (hC hek)]
    exact commutator_mem_commutator hd he
  have : Group.IsPerfect D := Subgroup.isPerfect_iff.2 hDperf
  have hDK : ∀ x : D, η x ∈ (twistedE6Datum 2 1).levi levi34 := fun x => hDQ x.2
  let ψ : D →* Matrix.SpecialLinearGroup (Fin 3) LieType.Chevalley.C2E6Overlap.K :=
    levi34Equiv.toMonoidHom.comp ((η.comp D.subtype).codRestrict _ hDK)
  have hψ : Function.Surjective ψ := by
    intro M
    obtain ⟨d, hd, hdM⟩ : ((levi34Equiv.symm M : (twistedE6Datum 2 1).levi levi34) :
        twistedE6Group 2 1) ∈ D.map η := by
      rw [hmap]
      exact (levi34Equiv.symm M).2
    refine ⟨⟨d, hd⟩, ?_⟩
    change levi34Equiv ⟨η d, _⟩ = M
    rw [show (⟨η d, hDK ⟨d, hd⟩⟩ : (twistedE6Datum 2 1).levi levi34) = levi34Equiv.symm M from
      Subtype.ext hdM, MulEquiv.apply_symm_apply]
  have hker : ∀ x : D, x ∈ ψ.ker ↔ (x : F) ∈ η.ker := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change levi34Equiv ⟨η x, _⟩ = 1 ↔ η x = 1
    rw [map_eq_one_iff _ levi34Equiv.injective]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hψC : ψ.ker ≤ center D := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hC ((hker x).mp hx)) y)
  have hψ2 : ∀ c ∈ ψ.ker, c ^ 2 = 1 := fun c hc =>
    Subtype.ext (by simpa using h2 c ((hker c).mp hc))
  have h4 := LieType.Multipliers.L34Upper.card_ker_le_four natCard_K ψ hψ hψC hψ2
  have heq : ψ.ker = η.ker.subgroupOf D := by
    ext x
    rw [hker, mem_subgroupOf]
  rwa [heq, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at h4

theorem card_le_four_of_le_center
    {E : Type} [Group E] [Finite E] (hperf : commutator E = ⊤)
    (hS : ChevalleyExceptionalModel (E ⧸ center E) .twistedE6 2 1) {P : Subgroup E}
    (hPZ : P ≤ center E) (hP2 : ∀ x ∈ P, x * x = 1) : Nat.card P ≤ 4 := by
  have : Group.IsPerfect E := Group.isPerfect_def.2 hperf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, _, _, σ, hL, hσ, ⟨e⟩⟩ := LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hS
  obtain ⟨e'⟩ := LieType.Chevalley.nonempty_mulEquiv_stdGroup_of_card_eq_four
    (by rw [hL]; norm_num) σ.toRingHom fun c => by simpa using hσ c
  let η₀ : E →* stdGroup := (e.trans e').toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hη₀s : Function.Surjective η₀ :=
    (e.trans e').surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ x : E, x ∈ η₀.ker ↔ x ∈ center E := by
    intro x
    rw [MonoidHom.mem_ker]
    change (e.trans e') (x : E ⧸ center E) = 1 ↔ _
    rw [map_eq_one_iff _ (e.trans e').injective, QuotientGroup.eq_one_iff]
  have hZ : η₀.ker ≤ center E := fun x hx => (hker₀ x).mp hx
  obtain ⟨hs₁, hC₁, h2₁⟩ := lift_oddPart η₀ hη₀s hZ
  have : Group.IsPerfect (E ⧸ oddPart η₀.ker hZ) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hsq₁ :=
    (LieType.Chevalley.TwistedE6FieldTwoCover.twisted_E6_field_two_central_two_kernel_elementary
      _ hs₁ hC₁ h2₁).1
  have : Finite (fibre (QuotientGroup.lift (oddPart η₀.ker hZ) η₀ oddPart_le)) := finite_fibre
  have : Group.IsPerfect (fibre (QuotientGroup.lift (oddPart η₀.ker hZ) η₀ oddPart_le)) :=
    Subgroup.isPerfect_iff.2 (commutator_fibre_of_sq hs₁ hsq₁)
  have h4 := card_ker_le_four_of_U (fibreHom _) (fibreHom_surjective_of_surjective hs₁)
    (ker_fibreHom_le_center_of_le hC₁) fun c hc => by
      have h1 := hsq₁ _ (fst_mem_ker_of_mem_ker_fibreHom hc)
      have h2 : ((c : (E ⧸ oddPart η₀.ker hZ) × twistedE6Group 2 1)).2 = 1 := hc
      refine Subtype.ext (Prod.ext ?_ ?_)
      · simpa using h1
      · simp [h2]
  rw [Nat.card_congr (kerFibreHomEquiv _)] at h4
  have hmem : ∀ p ∈ P, (p : E ⧸ oddPart η₀.ker hZ) ∈
      (QuotientGroup.lift (oddPart η₀.ker hZ) η₀ oddPart_le).ker := by
    intro p hp
    rw [MonoidHom.mem_ker, QuotientGroup.lift_mk]
    exact (hker₀ p).mpr (hPZ hp)
  let f : P → (QuotientGroup.lift (oddPart η₀.ker hZ) η₀ oddPart_le).ker :=
    fun p => ⟨(p : E), hmem p p.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have h1 : ((p : E) : E ⧸ oddPart η₀.ker hZ) = (q : E) := congrArg Subtype.val hpq
    rw [QuotientGroup.eq, mem_oddPart] at h1
    have h2 : (p : E)⁻¹ * q ∈ P := mul_mem (inv_mem p.2) q.2
    have h3 : orderOf ((p : E)⁻¹ * q) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hP2 _ h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · have h5 : (p : E)⁻¹ * q = 1 := orderOf_eq_one_iff.mp h
      exact Subtype.ext (inv_mul_eq_one.mp h5)
    · exact absurd (h ▸ h1.2) (Nat.not_odd_iff_even.mpr even_two)
  exact (Nat.card_le_card_of_injective f hf).trans h4

theorem centerElemFour_of_twistedE6
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hperf : commutator ↥A = ⊤)
    (hS : ChevalleyExceptionalModel (rankTwoQuot A) .twistedE6 2 1) : CenterElemFour A := by
  intro P hPZ hP2
  have hPA : P ≤ A := hPZ.trans inf_le_left
  have hc : P.subgroupOf A ≤ center A := by
    intro x hx
    rw [mem_subgroupOf] at hx
    exact mem_center_iff.mpr fun c => Subtype.ext (mem_centralizer_iff.mp (hPZ hx).2 c c.2)
  have h2 : ∀ x ∈ P.subgroupOf A, x * x = 1 :=
    fun x hx => Subtype.ext (hP2 _ (mem_subgroupOf.mp hx))
  have h4 := card_le_four_of_le_center hperf hS hc h2
  rwa [Nat.card_congr (subgroupOfEquivOfLe hPA).toEquiv] at h4

end CFSG.ComponentClassification.RankTwoExceptional.Step83Proof
