module

public import CFSG.ClassicalInvolution.Generic.Base
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.SubnormalClosure.Basic

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]

theorem IsClassicalMember.subgroupOf {L : Subgroup G} {z : G} (h : IsClassicalMember p f L z)
    {H : Subgroup G} (hLH : L ≤ H) :
    IsClassicalMember p f (L.subgroupOf H) (⟨z, hLH h.mem⟩ : H) := by
  have e : L.subgroupOf H ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  refine ⟨?_, Subgroup.mem_subgroupOf.mpr h.mem, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  · have := h.perfect
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have h1 : IsSubnormal L (Subgroup.centralizer ({z} : Set G) ⊓ H) := by
      have := isSubnormal_inf h.subnormal H
      rwa [inf_eq_left.mpr hLH] at this
    have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ H).subgroupOf H =
        Subgroup.centralizer ({(⟨z, hLH h.mem⟩ : H)} : Set H) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h1 H
  · obtain ⟨e'⟩ := h.nonempty_equiv
    have hO : (classicalInvolutionOddCore (L.subgroupOf H)).map e.toMonoidHom =
        classicalInvolutionOddCore L :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).trans e'⟩

theorem subgroupOf_oddCore_le [Finite G] (L : Subgroup G) :
    (classicalInvolutionOddCore G).subgroupOf L ≤ classicalInvolutionOddCore L := by
  apply CFSG.ComponentClassification.OddCore.maximal
  · infer_instance
  · have hcard : Nat.card ((classicalInvolutionOddCore G).subgroupOf L) =
        Nat.card (classicalInvolutionOddCore G ⊓ L : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
    rw [hcard]
    exact (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)

theorem inf_oddCore_eq_bot [Finite G] {L : Subgroup G} (hL : classicalInvolutionOddCore L = ⊥) :
    L ⊓ classicalInvolutionOddCore G = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have h : (⟨x, hx.1⟩ : L) ∈ classicalInvolutionOddCore L :=
    subgroupOf_oddCore_le L (Subgroup.mem_subgroupOf.mpr hx.2)
  rw [hL, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h)

theorem commutes_of_commutes_oddQuotient {Y : Type} [Group Y]
    (hZ : classicalInvolutionOddCore Y ≤ Subgroup.center Y) {K L : Subgroup Y}
    (hK : Group.IsPerfect K)
    (hc : Commutes (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))) : Commutes K L := by
  intro k hk l hl
  have hcen : ∀ x ∈ K, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.center Y := by
    intro x hx
    apply hZ
    have h := hc (QuotientGroup.mk' _ x) ⟨x, hx, rfl⟩ (QuotientGroup.mk' _ l) ⟨l, hl, rfl⟩
    rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore Y)]
    change QuotientGroup.mk' (classicalInvolutionOddCore Y) (x * l * x⁻¹ * l⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h
  let φ : K →* Subgroup.center Y :=
    { toFun := fun x => ⟨x * l * x⁻¹ * l⁻¹, hcen x x.2⟩
      map_one' := by simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hy := Subgroup.mem_center_iff.mp (hcen y y.2)
        have hx := Subgroup.mem_center_iff.mp (hcen x x.2)
        have hyl : (y : Y) * l * (y : Y)⁻¹ = ((y : Y) * l * (y : Y)⁻¹ * l⁻¹) * l := by group
        calc (((x * y : K) : Y) * l * ((x * y : K) : Y)⁻¹ * l⁻¹)
            = (x : Y) * ((y : Y) * l * (y : Y)⁻¹) * (x : Y)⁻¹ * l⁻¹ := by
              simp only [Subgroup.coe_mul, mul_inv_rev]; group
          _ = (x : Y) * (((y : Y) * l * (y : Y)⁻¹ * l⁻¹) * l) * (x : Y)⁻¹ * l⁻¹ := by rw [← hyl]
          _ = ((x : Y) * ((y : Y) * l * (y : Y)⁻¹ * l⁻¹)) * l * (x : Y)⁻¹ * l⁻¹ := by group
          _ = (((y : Y) * l * (y : Y)⁻¹ * l⁻¹) * (x : Y)) * l * (x : Y)⁻¹ * l⁻¹ := by rw [hy (x : Y)]
          _ = ((y : Y) * l * (y : Y)⁻¹ * l⁻¹) * ((x : Y) * l * (x : Y)⁻¹ * l⁻¹) := by group
          _ = ((x : Y) * l * (x : Y)⁻¹ * l⁻¹) * ((y : Y) * l * (y : Y)⁻¹ * l⁻¹) :=
              hx ((y : Y) * l * (y : Y)⁻¹ * l⁻¹) }
  have hker : commutator K ≤ φ.ker := Abelianization.commutator_subset_ker φ
  have hmem : (⟨k, hk⟩ : K) ∈ φ.ker := hker (by rw [hK.1]; exact Subgroup.mem_top _)
  have h1 : k * l * k⁻¹ * l⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
  calc k * l = k * l * k⁻¹ * l⁻¹ * l * k := by group
    _ = l * k := by rw [h1]; group

variable {p f}

theorem centralizingLayer_le_centralizer (Λ : Set (Subgroup G)) (A : Set G) :
    centralizingLayer Λ A ≤ Subgroup.centralizer A :=
  iSup₂_le fun _ hL => hL.2

theorem le_centralizingLayer {Λ : Set (Subgroup G)} {A : Set G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Λ A) : L ≤ centralizingLayer Λ A :=
  le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ centralizingMembers Λ A) => L) L hL

theorem conjSub_subgroupOf (H : Subgroup G) (n : H) (L : Subgroup G) :
    conjSub n (L.subgroupOf H) = (conjSub (n : G) L).subgroupOf H := by
  ext x
  simp only [mem_conjSub_iff, Subgroup.mem_subgroupOf]
  simp [mul_assoc]

theorem inClass_local {Λ : Set (Subgroup G)} (hΛ : InClass p f Λ) (A : Set G)
    (hA : (centralizingMembers Λ A).Nonempty) :
    InClass p f (restrictFamily (centralizingMembers Λ A) (centralizingLayer Λ A)) where
  nonempty := by
    obtain ⟨L, hL⟩ := hA
    exact ⟨L.subgroupOf (centralizingLayer Λ A), L, hL, le_centralizingLayer hL, rfl⟩
  conjInvariant := by
    rintro n _ ⟨L, hL, hLH, rfl⟩
    have hn : (n : G) ∈ Subgroup.centralizer A := centralizingLayer_le_centralizer Λ A n.2
    have hmem : conjSub (n : G) L ∈ centralizingMembers Λ A := by
      refine ⟨hΛ.conjInvariant _ L hL.1, fun x hx => ?_⟩
      rw [mem_conjSub_iff] at hx
      have hx' := hL.2 hx
      have : x = (n : G) * ((n : G)⁻¹ * x * (n : G)) * (n : G)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hx') ((Subgroup.inv_mem _) hn)
    exact ⟨conjSub (n : G) L, hmem, le_centralizingLayer hmem, (conjSub_subgroupOf _ n L)⟩
  generated := by
    set S := centralizingMembers Λ A with hS
    have key := iSup_subgroupOf_self (G := G) (fun i : S => (i : Subgroup G))
    have hsup : (⨆ i : S, (i : Subgroup G)) = centralizingLayer Λ A := by
      rw [centralizingLayer, iSup_subtype']
    rw [hsup] at key
    refine eq_top_iff.mpr (key.symm.le.trans ?_)
    refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun (L' : Subgroup (centralizingLayer Λ A))
      (_ : L' ∈ restrictFamily S (centralizingLayer Λ A)) => L')
      ((i : Subgroup G).subgroupOf (centralizingLayer Λ A))
      ⟨i, i.2, le_centralizingLayer i.2, rfl⟩
  classical := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    obtain ⟨z, hz⟩ := hΛ.classical L hL.1
    exact ⟨_, hz.subgroupOf p f hLH⟩

theorem centralizingLayer_ne_top {Λ : Set (Subgroup G)} {A : Set G} (hA : ¬ A ⊆ Subgroup.center G) :
    centralizingLayer Λ A ≠ ⊤ := by
  intro h
  apply hA
  rw [← Subgroup.centralizer_eq_top_iff_subset]
  exact top_le_iff.mp (h ▸ centralizingLayer_le_centralizer Λ A)

theorem card_centralizingLayer_lt [Finite G] (Λ : Set (Subgroup G)) {A : Set G}
    (hA : ¬ A ⊆ Subgroup.center G) : Nat.card (centralizingLayer Λ A) < Nat.card G := by
  have h := Subgroup.card_mul_index (centralizingLayer Λ A)
  have hidx : (centralizingLayer Λ A).index ≠ 1 := fun h1 =>
    centralizingLayer_ne_top hA (Subgroup.index_eq_one.mp h1)
  have hpos : 0 < Nat.card (centralizingLayer Λ A) := Nat.card_pos
  have hidx0 : (centralizingLayer Λ A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : 2 ≤ (centralizingLayer Λ A).index := by omega
  nlinarith

theorem localLieSystems_of_citBelowU [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hBelow : CITBelowU p f (Nat.card G)) : LocalLieSystems p f Ω := by
  intro A hA
  by_cases hne : (centralizingMembers Ω A).Nonempty
  · exact hBelow _ (card_centralizingLayer_lt Ω hA) _ (inClass_local hΩ A hne)
  · have hrf : restrictFamily (centralizingMembers Ω A) (centralizingLayer Ω A) = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨L, hL, _⟩ => hne ⟨L, hL⟩
    have hbot : centralizingLayer Ω A = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun L hL => (hne ⟨L, hL⟩).elim)
    have hsub : Subsingleton ↥(centralizingLayer Ω A) := by rw [hbot]; infer_instance
    have hq : Subsingleton (↥(centralizingLayer Ω A) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer Ω A)) := inferInstance
    exact LieSystem.of_empty p f (by rw [hrf]; simp [oddQuotientFamily])

end CFSG.ClassicalInvolution.Generic
