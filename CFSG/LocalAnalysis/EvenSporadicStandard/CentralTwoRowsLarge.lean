module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndCheck
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUnique
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRows
public import CFSG.Monster.GMS.TwoBabyUniqueOf
public import CFSG.Monster.Schur.Final
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.IndexTwo

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Monster.Schur
open scoped commutatorElement

theorem exists_index_two_of_le_center {A : Type*} [Group A] {C : Subgroup A} [Finite C]
    (hC : C ≤ center A) (heven : Even (Nat.card C)) :
    ∃ C₀ : Subgroup A, C₀ ≤ C ∧ Nat.card C = 2 * Nat.card C₀ := by
  obtain ⟨f, hf⟩ := CFSG.ComponentClassification.RankTwoSporadic.exists_surjective_zmod_two
    (H := ↥C) (fun a b => Subtype.ext (mem_center_iff.mp (hC b.2) a)) heven
  refine ⟨f.ker.map C.subtype, map_subtype_le _, ?_⟩
  rw [card_map_of_injective C.subtype_injective, card_eq_mul_card_ker f hf]
  exact congrArg (· * _) (Nat.card_zmod 2)

theorem card_ker_quotientMap {A : Type*} [Group A] [Finite A] {C C₀ : Subgroup A}
    [C₀.Normal] [C.Normal] (h₀ : C₀ ≤ C) (hcard : Nat.card C = 2 * Nat.card C₀) :
    Function.Surjective (QuotientGroup.map C₀ C (MonoidHom.id A) h₀) ∧
      Nat.card (QuotientGroup.map C₀ C (MonoidHom.id A) h₀).ker = 2 := by
  have hs : Function.Surjective (QuotientGroup.map C₀ C (MonoidHom.id A) h₀) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    exact ⟨QuotientGroup.mk' C₀ x, rfl⟩
  refine ⟨hs, ?_⟩
  have h1 := card_eq_mul_card_ker _ hs
  have h2 := C.card_eq_card_quotient_mul_card_subgroup
  have h3 := C₀.card_eq_card_quotient_mul_card_subgroup
  have hC₀ : 0 < Nat.card C₀ := Nat.card_pos
  have hq : 0 < Nat.card (A ⧸ C) := Nat.card_pos
  have h4 : Nat.card (A ⧸ C) * Nat.card C =
      Nat.card (A ⧸ C) * (Nat.card (QuotientGroup.map C₀ C (MonoidHom.id A) h₀).ker *
        Nat.card C₀) := by
    rw [← h2, h3, h1, mul_assoc]
  have h5 := Nat.eq_of_mul_eq_mul_left hq h4
  rw [hcard] at h5
  exact (Nat.eq_of_mul_eq_mul_right hC₀ h5).symm

theorem card_center_le_two_of_unique_double_cover {X : Type*} [Group X] {R : Type} [Group R]
    (hR : NoPerfectDoubleCover R)
    (hD : ∀ (D : Type) [Group D] (φ : D →* X), Function.Surjective φ → Group.IsPerfect D →
      Nat.card φ.ker = 2 → Nonempty (D ≃* R))
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hZ : IsPGroup 2 (center L)) (e : L ⧸ center L ≃* X) : Nat.card (center L) ≤ 2 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have : Group.IsPerfect L := Group.isPerfect_def.2 hq.1
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have h' : n < 2 := not_le.mp h
    interval_cases n
    · rw [pow_zero] at hn; omega
    · rw [pow_one] at hn; omega
  have heven : Even (Nat.card (center L)) := by
    rw [hn]; exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  obtain ⟨K₁, hK₁, hc₁⟩ := exists_index_two_of_le_center (le_refl (center L)) heven
  have heven₁ : Even (Nat.card K₁) := by
    have h4 : 4 ∣ Nat.card (center L) := by
      rw [hn]; exact (pow_dvd_pow 2 hn2 : 2 ^ 2 ∣ 2 ^ n)
    rw [Nat.even_iff]
    omega
  obtain ⟨K₂, hK₂, hc₂⟩ := exists_index_two_of_le_center hK₁ heven₁
  have : K₁.Normal := normal_of_le_center hK₁
  have : K₂.Normal := normal_of_le_center (hK₂.trans hK₁)
  obtain ⟨hs₁, hk₁⟩ := card_ker_quotientMap (A := L) (C := center L) (C₀ := K₁) hK₁ hc₁
  obtain ⟨hs₂, hk₂⟩ := card_ker_quotientMap (A := L) (C := K₁) (C₀ := K₂) hK₂ hc₂
  let q₁ := QuotientGroup.map K₁ (center L) (MonoidHom.id L) hK₁
  let q₂ := QuotientGroup.map K₂ K₁ (MonoidHom.id L) hK₂
  let φ : L ⧸ K₁ →* X := e.toMonoidHom.comp q₁
  have hφs : Function.Surjective φ := e.surjective.comp hs₁
  have hφk : Nat.card φ.ker = 2 := by
    have : φ.ker = q₁.ker := by
      ext x
      simp only [MonoidHom.mem_ker, φ, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    rw [this]; exact hk₁
  obtain ⟨eD⟩ := hD (L ⧸ K₁) φ hφs inferInstance hφk
  let π : L ⧸ K₂ →* R := eD.toMonoidHom.comp q₂
  have hπs : Function.Surjective π := eD.surjective.comp hs₂
  have hπk : Nat.card π.ker = 2 := by
    have : π.ker = q₂.ker := by
      ext x
      simp only [MonoidHom.mem_ker, π, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    rw [this]; exact hk₂
  exact hR (L ⧸ K₂) π hπs inferInstance hπk

theorem card_center_le_two_of_displacement {X : Type*} [Group X] {x y : X} (hy : y * y = 1)
    (hxy : x * y = y * x)
    (hD : ∀ (D : Type) [Group D] [Finite D], commutator D = ⊤ → ∀ ζ : D, orderOf ζ = 2 →
      ζ ∈ center D → ∀ π : D →* X, Function.Surjective π → π.ker = zpowers ζ →
        ∀ U V : D, π U = x → π V = y → U * V ≠ V * U)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hZ : IsPGroup 2 (center L)) (e : L ⧸ center L ≃* X) : Nat.card (center L) ≤ 2 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hperf : Group.IsPerfect L := Group.isPerfect_def.2 hq.1
  obtain ⟨m, hm⟩ := hZ.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra h
    have h' : m < 2 := not_le.mp h
    interval_cases m
    · rw [pow_zero] at hm; omega
    · rw [pow_one] at hm; omega
  let ψ : L →* X := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψk : ∀ g, ψ g = 1 ↔ g ∈ center L := fun g => by
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨u, hu⟩ := hψs x
  obtain ⟨v, hv⟩ := hψs y
  set κ : L := u * v * u⁻¹ * v⁻¹ with hκdef
  have hκZ : κ ∈ center L := by
    rw [← hψk]
    simp only [κ, map_mul, map_inv, hu, hv]
    rw [hxy]; group
  have hvvZ : v * v ∈ center L := by
    rw [← hψk, map_mul, hv, hy]
  have hκc : ∀ g, g * κ = κ * g := fun g => Subgroup.mem_center_iff.mp hκZ g
  have hvvc : ∀ g, g * (v * v) = (v * v) * g := fun g => Subgroup.mem_center_iff.mp hvvZ g
  have hκκ : κ * κ = 1 := by
    have h1 : κ * v = u * v * u⁻¹ := by simp only [κ]; group
    have key : κ * κ * (v * v) = v * v := by
      calc κ * κ * (v * v) = κ * (κ * v) * v := by simp only [mul_assoc]
        _ = κ * (v * κ) * v := by rw [hκc v]
        _ = (κ * v) * (κ * v) := by simp only [mul_assoc]
        _ = (u * v * u⁻¹) * (u * v * u⁻¹) := by rw [h1]
        _ = u * (v * v) * u⁻¹ := by group
        _ = v * v := by rw [hvvc u]; group
    exact mul_right_cancel (key.trans (one_mul _).symm)
  have hH : Nat.card (zpowers κ) ∣ 2 ^ (m - 1) := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hκκ)).trans
      (dvd_pow_self 2 (by omega))
  have hL : 2 ^ (m - 1) ∣ Nat.card (center L) := by
    rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1)
  obtain ⟨K, hKcard, hκK, hKZ⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hH hL
    (zpowers_le.2 hκZ)
  have hc2 : Nat.card (center L) = 2 * Nat.card K := by
    rw [hm, hKcard]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp [pow_succ, mul_comm]
  have : K.Normal := normal_of_le_center hKZ
  obtain ⟨hs₁, hk₁⟩ := card_ker_quotientMap (A := L) (C := center L) (C₀ := K) hKZ hc2
  let q₁ := QuotientGroup.map K (center L) (MonoidHom.id L) hKZ
  let π : L ⧸ K →* X := e.toMonoidHom.comp q₁
  have hπs : Function.Surjective π := e.surjective.comp hs₁
  have hπk : Nat.card π.ker = 2 := by
    have : π.ker = q₁.ker := by
      ext z
      simp only [MonoidHom.mem_ker, π, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    rw [this]; exact hk₁
  obtain ⟨ζ, hζK, hζ1, hζall⟩ := exists_ker_elem π hπk
  have hζ2 : ζ * ζ = 1 := by rw [← sq]; exact sq_eq_one_of_mem_ker π hπk hζK
  have hordζ : orderOf ζ = 2 := orderOf_eq_prime (by rw [sq]; exact hζ2) hζ1
  have hζc : ζ ∈ center (L ⧸ K) := mem_center_of_mem_ker π hπk hζK
  have hker : π.ker = zpowers ζ := by
    refine le_antisymm (fun k hk => ?_) (zpowers_le.2 hζK)
    rcases hζall k hk with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  have hDperf : commutator (L ⧸ K) = ⊤ := Group.isPerfect_def.1 inferInstance
  have hπmk : ∀ g : L, π (QuotientGroup.mk g) = ψ g := fun g => rfl
  have hκD : (QuotientGroup.mk κ : L ⧸ K) = 1 :=
    (QuotientGroup.eq_one_iff (N := K) κ).2 (hκK (mem_zpowers κ))
  have hcomm : (QuotientGroup.mk u : L ⧸ K) * QuotientGroup.mk v =
      QuotientGroup.mk v * QuotientGroup.mk u := by
    have h : (⁅(QuotientGroup.mk u : L ⧸ K), (QuotientGroup.mk v : L ⧸ K)⁆ : L ⧸ K) = 1 := by
      rw [commutatorElement_def]
      simpa [κ] using hκD
    exact commutatorElement_eq_one_iff_mul_comm.1 h
  exact hD (L ⧸ K) hDperf ζ hordζ hζc π hπs hker _ _ (by rw [hπmk, hu]) (by rw [hπmk, hv]) hcomm

theorem not_commute_of_square_lift {D X : Type*} [Group D] [Group X] {π : D →* X} {ζ : D}
    (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) (Q : X → Prop) (hsq : ∀ w : D, Q (π w) → w ^ 2 = ζ)
    {U V : D} (hU : Q (π U)) (hV : Q (π V)) (hUV : Q (π (U * V))) : U * V ≠ V * U := by
  intro h
  have hw : (U * V) ^ 2 = ζ := hsq _ hUV
  rw [Commute.mul_pow (show Commute U V from h), hsq U hU, hsq V hV, hζ2] at hw
  exact hζ1 hw.symm


theorem noPerfectDoubleCover_of_odd_index {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hodd : Odd H.index) (hH : Group.IsPerfect H) (hnd : NoPerfectDoubleCover H) :
    NoPerfectDoubleCover G := by
  intro E _ π hπ hE hk
  have : Finite E := finite_of_card_ker_ne_zero π (by rw [hk]; norm_num)
  obtain ⟨z, hzK, hz1, hzall⟩ := exists_ker_elem π hk
  have hz2 : z * z = 1 := by rw [← sq]; exact sq_eq_one_of_mem_ker π hk hzK
  have hordz : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hker : π.ker = zpowers z := by
    refine le_antisymm (fun k hk' => ?_) (zpowers_le.2 hzK)
    rcases hzall k hk' with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  have : (zpowers z).Normal := hker ▸ π.normal_ker
  let EH : Subgroup E := H.comap π
  have hker_le : π.ker ≤ EH := fun k hk' => by
    show π k ∈ H
    rw [MonoidHom.mem_ker.1 hk']; exact H.one_mem
  let πH : EH →* H := (π.comp EH.subtype).codRestrict H (fun x => x.2)
  have hπHs : Function.Surjective πH := by
    intro h
    obtain ⟨e, he⟩ := hπ (h : G)
    exact ⟨⟨e, by show π e ∈ H; rw [he]; exact h.2⟩, Subtype.ext he⟩
  have hker_eq : πH.ker = π.ker.subgroupOf EH := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hπHk : Nat.card πH.ker = 2 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv]; exact hk
  have hEHnp : ¬ Group.IsPerfect EH := fun hp => hnd EH πH hπHs hp hπHk
  set C₀ : Subgroup EH := commutator EH with hC₀
  have hC₀ne : C₀ ≠ ⊤ := fun h => hEHnp (Group.isPerfect_def.2 h)
  have htop : (⊤ : Subgroup EH).map πH = ⊤ := by
    rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.2 hπHs
  have hC₀map : C₀.map πH = ⊤ := by
    have h1 : C₀.map πH = commutator H := by
      rw [hC₀, commutator_def, Subgroup.map_commutator, htop, ← commutator_def]
    rw [h1]; exact Group.isPerfect_def.1 hH
  have hsup : C₀ ⊔ πH.ker = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨c, hc, hcx⟩ := (Subgroup.mem_map.1 (hC₀map ▸ (Subgroup.mem_top (πH x))))
    have hk' : c⁻¹ * x ∈ πH.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
    have : x = c * (c⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hc hk'
  have hinf : C₀ ⊓ πH.ker = ⊥ := by
    have hdvd : Nat.card ↥(C₀ ⊓ πH.ker) ∣ 2 := hπHk ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : C₀ ⊓ πH.ker = πH.ker :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hπHk])
      have hle : πH.ker ≤ C₀ := inf_eq_right.1 heq
      rw [sup_eq_left.2 hle] at hsup
      exact hC₀ne hsup
  let K : Subgroup E := C₀.map EH.subtype
  have hmapker : πH.ker.map EH.subtype = π.ker := by
    rw [hker_eq]; exact Subgroup.map_subgroupOf_eq_of_le hker_le
  have hNK : zpowers z ⊓ K = ⊥ := by
    rw [← hker, ← hmapker, ← Subgroup.map_inf_eq _ _ _ EH.subtype_injective, inf_comm, hinf,
      Subgroup.map_bot]
  have hNKsup : zpowers z ⊔ K = EH := by
    rw [← hker, ← hmapker, ← Subgroup.map_sup, sup_comm, hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcop : Nat.Coprime EH.index (Nat.card (zpowers z)) := by
    rw [Subgroup.index_comap_of_surjective H hπ, Nat.card_zpowers, hordz]
    exact Nat.coprime_two_right.2 hodd
  obtain ⟨D, hcompl, -, -⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting (zpowers z) EH K hcop hNK
      hNKsup
  have hD2 : D.index = 2 := by
    rw [hcompl.index_eq_card, Nat.card_zpowers, hordz]
  have hcomm : commutator E ≤ D := commutator_le_of_index_eq_two hD2
  rw [Group.isPerfect_def.1 hE] at hcomm
  have hDtop : D = ⊤ := eq_top_iff.2 hcomm
  rw [hDtop, Subgroup.index_top] at hD2
  exact absurd hD2 (by norm_num)

theorem mem_center_of_commutator_mem_of_perfect {E : Type*} [Group E] (hE : Group.IsPerfect E)
    {N : Subgroup E} (hN : N ≤ center E) {k : E} (hk : ∀ g : E, ⁅k, g⁆ ∈ N) : k ∈ center E := by
  have hc : ∀ n ∈ N, ∀ x : E, x * n = n * x := fun n hn x => mem_center_iff.mp (hN hn) x
  let f : E →* N :=
    { toFun := fun g => ⟨⁅k, g⁆, hk g⟩
      map_one' := by ext; simp
      map_mul' := fun g h => by
        ext
        show ⁅k, g * h⁆ = ⁅k, g⁆ * ⁅k, h⁆
        have h1 : ⁅k, g * h⁆ = ⁅k, g⁆ * (g * ⁅k, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h1, hc _ (hk h) g]
        group }
  have hker : commutator E ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subtype.ext (hc _ (f b).2 (f a : E)))
  rw [Group.isPerfect_def.1 hE] at hker
  refine mem_center_iff.2 fun g => ?_
  have h1 : f g = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top g))
  have h2 : ⁅k, g⁆ = 1 := congrArg Subtype.val h1
  exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm

theorem noPerfectDoubleCover_of_center_two {C S : Type} [Group C] [Finite C] [Group S]
    (hC : Nat.card (center C) = 2) (e : C ⧸ center C ≃* S)
    (hS : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (η : E →* S),
      Function.Surjective η → η.ker ≤ center E → IsPGroup 2 η.ker → Nat.card η.ker ≤ 2) :
    NoPerfectDoubleCover C := by
  intro E _ π hπ hE hk
  have : Finite E := finite_of_card_ker_ne_zero π (by rw [hk]; norm_num)
  have : Group.IsPerfect E := hE
  have : Finite S := Finite.of_equiv _ e.toEquiv
  let η : E →* S := e.toMonoidHom.comp ((QuotientGroup.mk' (center C)).comp π)
  have hη : Function.Surjective η := e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hπ)
  have hηk : ∀ x, η x = 1 ↔ π x ∈ center C := fun x => by
    simp only [η, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hπc : π.ker ≤ center E := fun k hk' => mem_center_of_mem_ker π hk hk'
  have hcent : η.ker ≤ center E := by
    intro k hk'
    have hπk : π k ∈ center C := (hηk k).1 hk'
    refine mem_center_of_commutator_mem_of_perfect hE hπc (fun g => MonoidHom.mem_ker.2 ?_)
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 hπk (π g)).symm
  have hη4 : Nat.card η.ker = 4 := by
    have h1 := card_eq_mul_card_ker η hη
    have h2 := card_eq_mul_card_ker π hπ
    have h3 := (center C).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr e.toEquiv, hC] at h3
    rw [hk, h3] at h2
    have hS0 : 0 < Nat.card S := Nat.card_pos
    have h4 : Nat.card S * Nat.card η.ker = Nat.card S * 4 := by
      rw [← h1, h2]; ring
    exact Nat.eq_of_mul_eq_mul_left hS0 h4
  have hp2 : IsPGroup 2 η.ker := IsPGroup.of_card (n := 2) (by rw [hη4]; norm_num)
  have := hS E η hη hcent hp2
  omega

theorem card_ker_le_two_of_hopf_multiplier {S : Type} [Group S] (hS : center S = ⊥)
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier S) = 2) {E : Type} [Group E] [Finite E]
    [hE : Group.IsPerfect E] (η : E →* S) (hη : Function.Surjective η) (hker : η.ker ≤ center E) :
    Nat.card η.ker ≤ 2 := by
  have hc : center E = η.ker := by
    refine le_antisymm (fun c hc => ?_) hker
    rw [MonoidHom.mem_ker]
    have : η c ∈ center S := by
      rw [mem_center_iff]
      intro s
      obtain ⟨e, rfl⟩ := hη s
      rw [← map_mul, ← map_mul, mem_center_iff.1 hc e]
    rw [hS] at this
    exact this
  let e' : E ⧸ center E ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientKerEquivOfSurjective η hη)
  have hd := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess (S := S) hE e'
  rw [hM, hc] at hd
  exact Nat.le_of_dvd (by norm_num) hd

theorem rowBound_M
    :
    RowBound .M :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    have : IsSimpleGroup (L ⧸ center L) := hq.2
    obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
    exact center_eq_bot_of_noPerfectDoubleCover
      (CFSG.Monster.Schur.noPerfectDoubleCover_Gmat_of_native
        CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24) hq hZ ε

section BabyMonster

open CFSG.Monster.GMS CFSG.Monster.GMS.R433Cover CFSG.YGroups
open CFSG.Blueprint.NativeSporadic (B)

theorem noPerfectDoubleCover_R433 :
    NoPerfectDoubleCover R433 := by
  intro E _ π hπ hperf hk
  obtain ⟨z, hzK, -, hzall⟩ := exists_ker_elem π hk
  have hzc : ∀ x, x * z = z * x := fun x =>
    mem_center_iff.mp (mem_center_of_mem_ker π hk hzK) x
  have hz2 : z * z = 1 := by rw [← sq]; exact sq_eq_one_of_mem_ker π hk hzK
  have hCK : R433Cover.CentralKernel π z := ⟨hzc, hz2, by simpa using hzK, hzall⟩
  obtain ⟨hY, h1⟩ := identities_of_Y432 (MonoidHom.id R433) yConj yConj_lt y432_I2 y432_I1
  obtain ⟨θ, hθ⟩ := exists_hom_R433 hCK hπ (MonoidHom.id R433)
    (fun c hc => Nat.lt_succ_of_lt (yConj_lt c hc)) hY h1
  have hsurj := surj_of_perfect hCK hθ Function.surjective_id (Group.isPerfect_def.1 hperf)
  have hπθ : ∀ r, π (θ r) = r := fun r => by
    have := congrArg (fun f => f r) hθ
    simpa using this
  have hker : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := hsurj x
    have hr : r = 1 := by rw [← hπθ r]; exact hx
    rw [hr, map_one]
    exact one_mem _
  rw [hker, card_bot] at hk
  exact absurd hk (by norm_num)

theorem nonempty_mulEquiv_R433_of_doubleCover
    {D : Type} [Group D]
    (φ : D →* B) (hφ : Function.Surjective φ) (hperf : Group.IsPerfect D)
    (hk : Nat.card φ.ker = 2) : Nonempty (D ≃* R433) := by
  have : Finite R433 := card_R433_le.1
  obtain ⟨z, hzK, -, hzall⟩ := exists_ker_elem φ hk
  have hzc : ∀ x, x * z = z * x := fun x =>
    mem_center_iff.mp (mem_center_of_mem_ker φ hk hzK) x
  have hz2 : z * z = 1 := by rw [← sq]; exact sq_eq_one_of_mem_ker φ hk hzK
  have hCK : R433Cover.CentralKernel φ z := ⟨hzc, hz2, by simpa using hzK, hzall⟩
  obtain ⟨hY, h1⟩ := identities_of_Y432 R433ToB yConj yConj_lt y432_I2 y432_I1
  have hcard : Nat.card R433 ≤ Nat.card D := by
    rw [card_eq_mul_card_ker φ hφ, hk, mul_comm]
    exact card_R433_le.2
  exact nonempty_mulEquiv_of_cover hCK hφ R433ToB_surjective
    (fun c hc => Nat.lt_succ_of_lt (yConj_lt c hc)) hY h1 (Group.isPerfect_def.1 hperf) hcard

theorem rowBound_B
    :
    RowBound .B :=
  rowBound_of_card_center_le_two rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact card_center_le_two_of_unique_double_cover noPerfectDoubleCover_R433
      (fun D _ φ hφ hperf hk => nonempty_mulEquiv_R433_of_doubleCover φ hφ hperf hk) hq hZ e

end BabyMonster

theorem isConj_klein {G : Type*} [Group G] {e₁ e₂ c₁ c₂ : G} (hcomm : e₁ * e₂ = e₂ * e₁)
    (h₁ : c₁ * e₂ = e₁ * e₂ * c₁) (h₂ : c₂ * e₁ = e₂ * e₁ * c₂) :
    IsConj e₁ (e₁ * e₂) ∧ IsConj (e₁ * e₂) e₂ := by
  refine ⟨isConj_iff.2 ⟨c₂, ?_⟩, (isConj_iff.2 ⟨c₁, ?_⟩).symm⟩
  · rw [h₂, ← hcomm]; group
  · rw [h₁]; group

open CFSG.ComponentClassification.RankTwoSporadic.Co1 in
theorem rowBound_Co1 :
    RowBound .Co1 :=
  rowBound_of_card_center_le_two rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    obtain ⟨c₁, c₂, a₀, b₀, hF⟩ := co1_swapFacts_of_check co1_endCheck
    have h₁ : CFSG.Monster.GMS.IsCo1TwoB co1E1 := isCo1TwoB_co1E1
    obtain ⟨hj₁, hj₂⟩ := isConj_klein hF.comm hF.c₁_swap hF.c₂_swap
    have h₃ : CFSG.Monster.GMS.IsCo1TwoB (co1E1 * co1E2) := isCo1TwoB_of_isConj h₁ hj₁
    have h₂ : CFSG.Monster.GMS.IsCo1TwoB co1E2 := isCo1TwoB_of_isConj h₃ hj₂
    refine card_center_le_two_of_displacement (X := Blueprint.NativeSporadic.Co1) hF.e₂_sq hF.comm
      (fun D _ _ hperf ζ hζ hζc π hπ hk U V hU hV => ?_) hq hZ e
    have hζ2 : ζ * ζ = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one ζ
      rwa [hζ] at this
    have hζ1 : ζ ≠ 1 := fun h => by rw [h, orderOf_one] at hζ; omega
    exact not_commute_of_square_lift hζ1 hζ2 CFSG.Monster.GMS.IsCo1TwoB
      (fun w hw => co1_twoB_lift D hperf ζ hζ hζc π hπ hk w hw.1 hw)
      (by rw [hU]; exact h₁) (by rw [hV]; exact h₂) (by rw [map_mul, hU, hV]; exact h₃)


open CFSG.Sporadic.LySchreier in
theorem noPerfectDoubleCover_of_equiv_Ly
    {T : Type} [Group T]
    (hT : Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.Ly)) : NoPerfectDoubleCover T := by
  obtain ⟨e⟩ := hT
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card T = 51765179004000000 := by
    rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.Ly.card_Ly
  have h2 : 2 ∣ Nat.card T := by rw [hcard]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2
  obtain ⟨hq, hZ2, ⟨φ⟩⟩ := involution_centralizers_quasisimple ⟨e⟩ t ht
  set H := Subgroup.centralizer ({t} : Set T) with hH
  have hperf : Group.IsPerfect H := hq.1
  have hnd : NoPerfectDoubleCover H := noPerfectDoubleCover_of_center_two hZ2 φ
    (fun E _ _ _ η hη hc hp =>
      CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
        (by norm_num) η hη hc hp)
  have hcardH : Nat.card H = 39916800 := by
    have h1 := (center H).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr φ.toEquiv, hZ2] at h1
    have h2 : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [h2] at h1
    omega
  have hodd : Odd H.index := by
    have h1 := H.card_mul_index
    rw [hcardH, hcard] at h1
    have : H.index = 1296826875 := by omega
    rw [this]; decide
  exact noPerfectDoubleCover_of_odd_index H hodd hperf hnd

theorem rowBound_Ly :
    RowBound .Ly :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs =>
    center_eq_bot_of_noPerfectDoubleCover
      (noPerfectDoubleCover_of_equiv_Ly (T := L ⧸ center L) hs) hq hZ (MulEquiv.refl _)

open CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.SympSix in
theorem noPerfectDoubleCover_co3M :
    NoPerfectDoubleCover ↥co3M := by
  have hLie : CFSG.Blueprint.LieModel ↥co3X36 CFSG.Assembly.LowTwoRank.StatedLieTag.PSp 3 2 1 :=
    Or.inl ⟨by decide, co3X36_classicalModel⟩
  obtain ⟨-, ⟨eM⟩⟩ := multiplier_PSp_three_two_one ↥co3X36 hLie
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier ↥co3X36) = 2 := by
    rw [Nat.card_congr eM.toEquiv]
    exact Nat.card_zmod 2
  exact noPerfectDoubleCover_of_center_two card_co3M_center co3MQuotEquiv
    (fun E _ _ _ η hη hc _ => card_ker_le_two_of_hopf_multiplier co3X36_center hM η hη hc)

open CFSG.Sporadic.Schreier.Co3 in
theorem noPerfectDoubleCover_co3P :
    NoPerfectDoubleCover ↥co3P := by
  have hle : co3M ≤ co3P := co3M_le_P
  let H : Subgroup ↥co3P := co3M.subgroupOf co3P
  let eH : ↥H ≃* ↥co3M := Subgroup.subgroupOfEquivOfLe hle
  have : Group.IsPerfect ↥co3M := co3M_isPerfect
  have hperf : Group.IsPerfect ↥H :=
    Group.IsPerfect.ofSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  have hnd : NoPerfectDoubleCover ↥H :=
    NoPerfectDoubleCover.of_mulEquiv eH.symm noPerfectDoubleCover_co3M
  have hodd : Odd H.index := by
    have h1 := H.card_mul_index
    rw [Nat.card_congr eH.toEquiv, card_co3M, card_co3P] at h1
    have : H.index = 170775 := by omega
    rw [this]; decide
  exact noPerfectDoubleCover_of_odd_index H hodd hperf hnd

open CFSG.Sporadic.Schreier.Co3 in
theorem rowBound_Co3 :
    RowBound .Co3 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact center_eq_bot_of_noPerfectDoubleCover noPerfectDoubleCover_co3P hq hZ
      (e.trans co3PermEquiv)

end CFSG.EvenSporadicStandard
