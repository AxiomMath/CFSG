module

public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase
public import CFSG.ClassicalInvolution.Q3.Q3AMXNOrb

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Edge


variable {G : Type} [Group G] [Finite G]

theorem not_commutes_self_of_isClassicalMember3 {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 L z) : ¬ Commutes L L := by
  intro hc
  have hcomm : ∀ a b : L, a * b = b * a := fun a b => Subtype.ext (hc a a.2 b b.2)
  obtain ⟨e⟩ := h.nonempty_equiv
  have hab : ∀ a b : SL(2, ZMod 3), a * b = b * a := by
    intro a b
    obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm a)
    obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm b)
    apply e.symm.injective
    rw [map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul, hcomm a' b']
  exact sl2Three_not_comm hab

theorem mem_normalizer_oddCoreOf {Y : Subgroup G} {y : G} (hy : y ∈ Y) :
    y ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_oddCoreOf_of_mem_self hy hx, fun hx => ?_⟩
  have h1 := conj_mem_oddCoreOf_of_mem_self (Y.inv_mem hy) hx
  have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem modOddIn_conjSub_oddCore {Y L : Subgroup G} {p : G} (hpO : p ∈ oddCoreOf Y) :
    modOddIn Y (conjSub p L) = modOddIn Y L := by
  obtain ⟨hpY, hpmem⟩ := mem_oddCoreOf_iff.mp hpO
  have hπp : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (⟨p, hpY⟩ : ↥Y) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hpmem
  have key : ∀ x ℓ : ↥Y, (x : G) = p * ℓ * p⁻¹ →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) x =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ℓ := by
    intro x ℓ hxe
    have hx : x = ⟨p, hpY⟩ * ℓ * ⟨p, hpY⟩⁻¹ := Subtype.ext (by simpa using hxe)
    rw [hx, map_mul, map_mul, map_inv, hπp]
    simp
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyL : p⁻¹ * (y : G) * p ∈ L := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have hℓY : p⁻¹ * (y : G) * p ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem hpY) y.2) hpY
    refine ⟨⟨p⁻¹ * y * p, hℓY⟩, Subgroup.mem_subgroupOf.mpr hyL, ?_⟩
    exact (key y ⟨p⁻¹ * y * p, hℓY⟩ (by simp [mul_assoc])).symm
  · rintro ⟨ℓ, hℓ, rfl⟩
    have hℓL : (ℓ : G) ∈ L := Subgroup.mem_subgroupOf.mp hℓ
    have hyY : p * (ℓ : G) * p⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hpY ℓ.2) (Y.inv_mem hpY)
    have hyL : p⁻¹ * (p * (ℓ : G) * p⁻¹) * p ∈ L := by
      have e : p⁻¹ * (p * (ℓ : G) * p⁻¹) * p = ℓ := by group
      rw [e]
      exact hℓL
    refine ⟨⟨p * ℓ * p⁻¹, hyY⟩, Subgroup.mem_subgroupOf.mpr (mem_conjSub_iff.mpr hyL), ?_⟩
    exact key ⟨p * ℓ * p⁻¹, hyY⟩ ℓ rfl

theorem modOddIn_mem_layerFam {Ω : Set (Subgroup G)} {M N : Subgroup G} {a : G}
    (hN : N ∈ omegaNbr Ω M) :
    modOddIn (nbrLayer Ω M a) (exactCore3 a N) ∈ layerFam Ω M a :=
  ⟨(exactCore3 a N).subgroupOf (nbrLayer Ω M a),
    ⟨exactCore3 a N, ⟨⟨N, hN, rfl⟩, exactCore3_le_centralizer a N⟩, exactCore3_le_nbrLayer hN,
      rfl⟩, rfl⟩

theorem exists_of_mem_layerFam {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G}
    {A : Subgroup (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a))}
    (hA : A ∈ layerFam Ω M a) :
    ∃ N ∈ omegaNbr Ω M, A = modOddIn (nbrLayer Ω M a) (exactCore3 a N) := by
  obtain ⟨_, ⟨L, ⟨⟨N, hN, rfl⟩, -⟩, hLY, rfl⟩, rfl⟩ := hA
  exact ⟨N, hN, rfl⟩

theorem exists_isClassicalMember3_modOddIn [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z) {N : Subgroup G}
    (hN : N ∈ omegaNbr Ω K) :
    ∃ ζ, IsClassicalMember3 (modOddIn (nbrLayer Ω K z) (exactCore3 z N)) ζ := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hBelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hstd.stand.below
  have hnab : ∃ x y : G, x * y ≠ y * x := h.nonabelian
  have hz : IsUniqueInvolution K z := hstd.hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hz.sq hz.ne_one
  obtain ⟨b, hb⟩ := hΩ.exists_uniqueInvolution hN.1
  have he := h.toEdgeSetup hint hstd.stand.mem hN hz hb
  have hNc : IsClassicalMember3 N b :=
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hN.1 hb
  have hsec := isSectionMember3_exactCore3 hNc hc2 (trivialOnQuot_of_edge he hnab hBelow)
  obtain ⟨hbY, hcl⟩ := (hsec.restrict (nbrLayer_le_centralizer Ω K z)
    (exactCore3_le_nbrLayer hN)).toIn
  exact ⟨_, hcl.map_oddQuotient⟩

theorem noTriangleAtEdge_nbr {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t) (hN : NoTriangleAtEdge Ω K J)
    {N : Subgroup G} (hN' : N ∈ omegaNbr Ω K) : NoTriangleAtEdge Ω K N := by
  intro K' hK' hK'N
  have hΩ : HypOmegaMod Ω := h.std.stand.hyp
  obtain ⟨c, hc, rfl⟩ := h.nbr_mem_orbit_of_noTriangle hN hN'
  have h1 : conjSub c⁻¹ K' ∈ omegaNbr Ω K :=
    h.conjSub_mem_omegaNbr (Subgroup.inv_mem _ hc) hK'
  have h2 := omegaNbr_conj hΩ.conjInvariant hK'N c⁻¹
  rw [conjSub_inv_conjSub] at h2
  exact hN _ h1 h2

theorem exists_nbr_of_commutes_layerFam [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : BadStd8 Ω K J S R T W z t) {N₁ N₂ : Subgroup G} (hN₁ : N₁ ∈ omegaNbr Ω K)
    (hN₂ : N₂ ∈ omegaNbr Ω K)
    (hcomm : Commutes (modOddIn (nbrLayer Ω K z) (exactCore3 z N₁))
      (modOddIn (nbrLayer Ω K z) (exactCore3 z N₂))) :
    ∃ N₃ ∈ omegaNbr Ω K, (N₃ = N₁ ∨ N₃ ∈ omegaNbr Ω N₁) ∧
      modOddIn (nbrLayer Ω K z) (exactCore3 z N₃) =
        modOddIn (nbrLayer Ω K z) (exactCore3 z N₂) := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hYC : nbrLayer Ω K z ≤ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    h.normalizer_eq_centralizer
  obtain ⟨hN₁Ω, hN₁K, T₁, hT₁R, hT₁N₁, hT₁nK⟩ := id hN₁
  obtain ⟨hN₂Ω, hN₂K, T₂, hT₂R, hT₂N₂, hT₂nK⟩ := id hN₂
  have hT₁s : IsSylow2In T₁ N₁ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hN₁Ω hT₁R hT₁N₁
  have hT₂s : IsSylow2In T₂ N₂ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hN₂Ω hT₂R hT₂N₂
  have hT₁C : T₁ ≤ exactCore3 z N₁ := le_inf hT₁N₁ (hNC ▸ hT₁nK)
  have hT₂C : T₂ ≤ exactCore3 z N₂ := le_inf hT₂N₂ (hNC ▸ hT₂nK)
  have hT₁Y : T₁ ≤ nbrLayer Ω K z := hT₁C.trans (exactCore3_le_nbrLayer hN₁)
  have hT₂Y : T₂ ≤ nbrLayer Ω K z := hT₂C.trans (exactCore3_le_nbrLayer hN₂)
  have hcomm' : ∀ a ∈ T₁, ∀ b ∈ T₂, ⁅a, b⁆ ∈ oddCoreOf (nbrLayer Ω K z) := by
    intro a ha b hb
    have haY : a ∈ nbrLayer Ω K z := hT₁Y ha
    have hbY : b ∈ nbrLayer Ω K z := hT₂Y hb
    have ha' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨a, haY⟩ ∈
        modOddIn (nbrLayer Ω K z) (exactCore3 z N₁) :=
      ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr (hT₁C ha), rfl⟩
    have hb' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨b, hbY⟩ ∈
        modOddIn (nbrLayer Ω K z) (exactCore3 z N₂) :=
      ⟨⟨b, hbY⟩, Subgroup.mem_subgroupOf.mpr (hT₂C hb), rfl⟩
    have hc := (mk_comm_eq_iff haY hbY).mp (hcomm _ ha' _ hb')
    rw [commutatorElement_def]
    exact hc
  obtain ⟨p, hpO, hp⟩ := exists_conj_commutes_of_commutator_mem hT₁s.2.1 hT₂s.2.1
    (oddCoreOf_odd_natCard _) (fun y hy => mem_normalizer_oddCoreOf (hT₁Y hy))
    (fun y hy => mem_normalizer_oddCoreOf (hT₂Y hy)) hcomm'
  have hpY : p ∈ nbrLayer Ω K z := oddCoreOf_le_self _ hpO
  have hpC : p ∈ Subgroup.centralizer ({z} : Set G) := hYC hpY
  have hN₃K : conjSub p N₂ ∈ omegaNbr Ω K := h.conjSub_mem_omegaNbr hpC hN₂
  have hcore : exactCore3 z (conjSub p N₂) = conjSub p (exactCore3 z N₂) := by
    have e := exactCore3_conjSub p z N₂
    rw [conj_eq_of_mem_centralizer_singleton hpC] at e
    exact e
  have himg : modOddIn (nbrLayer Ω K z) (exactCore3 z (conjSub p N₂)) =
      modOddIn (nbrLayer Ω K z) (exactCore3 z N₂) := by
    rw [hcore]
    exact modOddIn_conjSub_oddCore hpO
  refine ⟨conjSub p N₂, hN₃K, ?_, himg⟩
  by_cases hEq : conjSub p N₂ = N₁
  · exact Or.inl hEq
  right
  have hT₂p : conjSub p T₂ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hT₂R p
  have h4 : 4 ≤ Nat.card T₁ := by have := hΩ.eight_le_of_mem_RSet hT₁R; omega
  have hnorm : conjSub p T₂ ≤ Subgroup.normalizer (N₁ : Set G) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hN₁y : conjSub (p * b * p⁻¹) N₁ ∈ Ω := hΩ.conjInvariant _ N₁ hN₁Ω
    have hT₁y : T₁ ≤ conjSub (p * b * p⁻¹) N₁ := by
      intro x hx
      rw [mem_conjSub_iff]
      have hxy : (p * b * p⁻¹)⁻¹ * x * (p * b * p⁻¹) = x := by
        have := hp x hx b hb
        calc (p * b * p⁻¹)⁻¹ * x * (p * b * p⁻¹) = (p * b * p⁻¹)⁻¹ * (x * (p * b * p⁻¹)) := by
              rw [mul_assoc]
          _ = (p * b * p⁻¹)⁻¹ * ((p * b * p⁻¹) * x) := by rw [this]
          _ = x := by group
      rw [hxy]
      exact hT₁N₁ hx
    exact mem_normalizer_iff_conjSub_eq.mpr
      (hΩ.eq_of_le_of_le hN₁Ω hN₁y hT₁s.2.1 h4 hT₁N₁ hT₁y).symm
  exact ⟨hN₃K.1, hEq, conjSub p T₂, hT₂p, conjSub_mono hT₂N₂, hnorm⟩

theorem layerFam_noCommute [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J) :
    ∀ A ∈ layerFam Ω K z, ∀ B ∈ layerFam Ω K z, ¬ Commutes A B := by
  intro A hA B hB hAB
  obtain ⟨N₁, hN₁, rfl⟩ := exists_of_mem_layerFam hA
  obtain ⟨N₂, hN₂, rfl⟩ := exists_of_mem_layerFam hB
  by_cases hEq : modOddIn (nbrLayer Ω K z) (exactCore3 z N₁) =
      modOddIn (nbrLayer Ω K z) (exactCore3 z N₂)
  · obtain ⟨ζ, hζ⟩ := exists_isClassicalMember3_modOddIn h hint hN₁
    rw [← hEq] at hAB
    exact not_commutes_self_of_isClassicalMember3 hζ hAB
  · obtain ⟨N₃, hN₃K, hN₃, himg⟩ := exists_nbr_of_commutes_layerFam h hN₁ hN₂ hAB
    rcases hN₃ with hN₃N₁ | hN₃N₁
    · exact hEq (hN₃N₁ ▸ himg)
    · exact noTriangleAtEdge_nbr h hN hN₁ N₃ hN₃K hN₃N₁

end Edge

end CFSG.ClassicalInvolution.Q3.Q3AM
