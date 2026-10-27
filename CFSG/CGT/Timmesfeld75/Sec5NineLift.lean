module

public import CFSG.CGT.Timmesfeld75.Sec5OutBar
public import CFSG.CGT.Timmesfeld75.Sec5FiveFix
public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T L₁ : Subgroup G}

@[expose] def liftBar (T : Subgroup G) (Q : Subgroup (NQuot T)) : Subgroup G :=
  (Q.comap (QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G))))).map
    (Subgroup.normalizer (T : Set G)).subtype

theorem mem_liftBar {Q : Subgroup (NQuot T)} {u : G} :
    u ∈ liftBar T Q ↔ ∃ hu : u ∈ Subgroup.normalizer (T : Set G), barElt T hu ∈ Q := by
  unfold liftBar
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hu, hQ⟩
    exact ⟨⟨u, hu⟩, hQ, rfl⟩

theorem liftBar_le_normalizer (Q : Subgroup (NQuot T)) :
    liftBar T Q ≤ Subgroup.normalizer (T : Set G) := fun _ hu => (mem_liftBar.1 hu).1

theorem left_le_liftBar (Q : Subgroup (NQuot T)) : T ≤ liftBar T Q := fun t ht =>
  mem_liftBar.2 ⟨Subgroup.le_normalizer ht, by
    rw [(barElt_eq_one_iff (Subgroup.le_normalizer ht)).2 ht]
    exact Q.one_mem⟩

theorem isPGroup_liftBar {Q : Subgroup (NQuot T)} (hQ : IsPGroup 2 Q) (hT : IsPGroup 2 T) :
    IsPGroup 2 (liftBar T Q) := by
  have hker : IsPGroup 2 (QuotientGroup.mk'
      (T.subgroupOf (Subgroup.normalizer (T : Set G)))).ker := by
    rw [QuotientGroup.ker_mk']
    exact hT.comap_subtype
  exact (hQ.comap_of_ker_isPGroup _ hker).map _

theorem conj_mem_liftBar {Q : Subgroup (NQuot T)} {h u : G}
    (hh : h ∈ Subgroup.normalizer (T : Set G)) (hQ : ∀ y ∈ Q, barElt T hh * y * (barElt T hh)⁻¹ ∈ Q)
    (hu : u ∈ liftBar T Q) : h * u * h⁻¹ ∈ liftBar T Q := by
  obtain ⟨huN, huQ⟩ := mem_liftBar.1 hu
  have hconjN : h * u * h⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem ((Subgroup.normalizer (T : Set G)).mul_mem hh huN)
      ((Subgroup.normalizer (T : Set G)).inv_mem hh)
  refine mem_liftBar.2 ⟨hconjN, ?_⟩
  have e : barElt T hconjN = barElt T hh * barElt T huN * (barElt T hh)⁻¹ := rfl
  rw [e]
  exact hQ _ huQ

section HSub

theorem hSub_le_normalizer (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) :
    hSub T L₁ ≤ Subgroup.normalizer (T : Set G) :=
  sup_le Subgroup.le_normalizer (iSup₂_le fun _ hg => conjSubgroup_le_normalizer hg hL₁)

theorem le_hSub : L₁ ≤ hSub T L₁ := fun x hx =>
  Subgroup.mem_sup_right ((Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem
    (Subgroup.one_mem _) (by simpa [mem_conjSubgroup] using hx))))

theorem left_le_hSub : T ≤ hSub T L₁ := le_sup_left

theorem mul_mul_inv_mem_hSub {n y : G} (hn : n ∈ Subgroup.normalizer (T : Set G))
    (hy : y ∈ hSub T L₁) : n * y * n⁻¹ ∈ hSub T L₁ := by
  have key : hSub T L₁ ≤ (hSub T L₁).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (fun t ht => ?_) (iSup₂_le fun g hg x hx => ?_)
    · show n * t * n⁻¹ ∈ hSub T L₁
      exact Subgroup.mem_sup_left (conj_mem_of_mem_normalizer hn ht)
    · show n * x * n⁻¹ ∈ hSub T L₁
      have hx' : (n * g)⁻¹ * (n * x * n⁻¹) * (n * g) ∈ L₁ := by
        have := mem_conjSubgroup.1 hx
        simpa [mul_assoc] using this
      refine Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (n * g)
        (Subgroup.mem_iSup_of_mem ((Subgroup.normalizer (T : Set G)).mul_mem hn hg) ?_))
      exact mem_conjSubgroup.2 hx'
  exact key hy

theorem conjSubgroup_hSub {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup n (hSub T L₁) = hSub T L₁ := by
  refine le_antisymm (fun x hx => ?_) (fun y hy => ?_)
  · have h1 := mul_mul_inv_mem_hSub hn (mem_conjSubgroup.1 hx)
    simpa [mul_assoc] using h1
  · exact mem_conjSubgroup.2 (by
      simpa using mul_mul_inv_mem_hSub ((Subgroup.normalizer (T : Set G)).inv_mem hn) hy)

end HSub

@[expose] def hBar (T L₁ : Subgroup G) : Subgroup (NQuot T) :=
  Subgroup.normalClosure ((barSub T L₁ : Subgroup (NQuot T)) : Set (NQuot T))

instance hBar_normal (T L₁ : Subgroup G) : (hBar T L₁).Normal :=
  Subgroup.normalClosure_normal

theorem barSub_le_hBar : barSub T L₁ ≤ hBar T L₁ := Subgroup.le_normalClosure

theorem barSub_hSub_eq (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) :
    barSub T (hSub T L₁) = hBar T L₁ := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨u, hu, huH, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
    have hle : hSub T L₁ ≤ liftBar T (hBar T L₁) := by
      refine sup_le (left_le_liftBar _) (iSup₂_le fun g hg x hx => ?_)
      have hxL : g⁻¹ * x * g ∈ L₁ := mem_conjSubgroup.1 hx
      have hxN : x ∈ Subgroup.normalizer (T : Set G) := by
        have := (Subgroup.normalizer (T : Set G)).mul_mem
          ((Subgroup.normalizer (T : Set G)).mul_mem hg (hL₁ hxL))
          ((Subgroup.normalizer (T : Set G)).inv_mem hg)
        simpa [mul_assoc] using this
      refine mem_liftBar.2 ⟨hxN, ?_⟩
      have h1 : barElt T hxN = barElt T hg * barElt T (hL₁ hxL) * (barElt T hg)⁻¹ := by
        rw [barElt_inv, barElt_mul, barElt_mul, barElt_eq_iff]
        have e : x⁻¹ * (g * (g⁻¹ * x * g) * g⁻¹) = 1 := by group
        rw [e]
        exact T.one_mem
      rw [h1]
      exact (hBar_normal T L₁).conj_mem _ (barSub_le_hBar (barElt_mem_barSub (hL₁ hxL) hxL)) _
    obtain ⟨hu', hQ⟩ := mem_liftBar.1 (hle huH)
    exact hQ
  · have : (barSub T (hSub T L₁)).Normal := barSub_normal fun n hn => conjSubgroup_hSub hn
    refine Subgroup.normalClosure_le_normal ?_
    intro y hy
    obtain ⟨u, hu, huL, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
    exact barElt_mem_barSub hu (le_hSub huL)

theorem exists_mem_hSub_of_mem_hBar (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G))
    {x : NQuot T} (hx : x ∈ hBar T L₁) :
    ∃ (u : G) (hu : u ∈ Subgroup.normalizer (T : Set G)), u ∈ hSub T L₁ ∧ barElt T hu = x := by
  rw [← barSub_hSub_eq hL₁] at hx
  exact exists_eq_barElt_of_mem_barSub hx

theorem barElt_mem_hBar (hL₁ : L₁ ≤ Subgroup.normalizer (T : Set G)) {u : G}
    (hu : u ∈ Subgroup.normalizer (T : Set G)) (huH : u ∈ hSub T L₁) :
    barElt T hu ∈ hBar T L₁ := by
  rw [← barSub_hSub_eq hL₁]
  exact barElt_mem_barSub hu huH

section Centralizes

variable [Finite G]

theorem centralizes_of_normal_pGroup (hT : IsElemAbelian 2 T) (hT1 : T ≠ ⊥)
    (hHN : hSub T L₁ ≤ Subgroup.normalizer (T : Set G))
    (htr : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T L₁, h * x * h⁻¹ = y)
    {Q : Subgroup (NQuot T)} (hQ2 : IsPGroup 2 Q)
    (hQn : ∀ h (hh : h ∈ hSub T L₁), ∀ y ∈ Q, barElt T (hHN hh) * y * (barElt T (hHN hh))⁻¹ ∈ Q)
    {u : G} (hu : u ∈ liftBar T Q) : ∀ t ∈ T, u * t * u⁻¹ = t := by
  have hT2 : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hT
  have hU2 : IsPGroup 2 (liftBar T Q) := isPGroup_liftBar hQ2 hT2
  obtain ⟨v, hvT, hv1, hv⟩ := exists_fixed_of_isPGroup hU2 (liftBar_le_normalizer Q) hT2 hT1
  have hUH : ∀ h ∈ hSub T L₁, ∀ p ∈ liftBar T Q, h⁻¹ * p * h ∈ liftBar T Q := by
    intro h hh p hp
    have hhi : h⁻¹ ∈ hSub T L₁ := (hSub T L₁).inv_mem hh
    have := conj_mem_liftBar (hHN hhi) (hQ := hQn _ hhi) hp
    simpa using this
  intro t ht
  by_cases ht1 : t = 1
  · subst ht1
    simp
  obtain ⟨h, hh, hht⟩ := htr v hvT hv1 t ht ht1
  have h1 := hv _ (hUH h hh u hu)
  calc u * t * u⁻¹ = u * (h * v * h⁻¹) * u⁻¹ := by rw [hht]
    _ = h * ((h⁻¹ * u * h) * v * (h⁻¹ * u * h)⁻¹) * h⁻¹ := by group
    _ = h * v * h⁻¹ := by rw [h1]
    _ = t := hht

end Centralizes

end CFSG.CGT.Timmesfeld75
