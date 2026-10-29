module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusCor
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43

private lemma exists_odd_ne_one {N : Subgroup X₀} (hxN : xElt ∈ N)
    (hgen : N ≤ Subgroup.closure {a | a ∈ N ∧ Odd (orderOf a)}) (hx : orderOf xElt = 2) :
    ∃ g ∈ N, Odd (orderOf g) ∧ g ≠ 1 := by
  by_contra h
  push Not at h
  have hbot : N ≤ ⊥ := by
    refine hgen.trans ?_
    rw [Subgroup.closure_le]
    rintro a ⟨ha, hodd⟩
    rw [h a ha hodd]
    exact Subgroup.mem_bot.mpr rfl
  have hx1 : xElt = 1 := Subgroup.mem_bot.mp (hbot hxN)
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by decide)

private lemma swCen_inv {g h : X₀} (hh : h ∈ SwCen g) : h⁻¹ ∈ SwCen g :=
  ⟨SwC.inv_mem hh.1, fun o ho hodd => Commute.inv_left (hh.2 o ho hodd)⟩

private lemma swCen_mul {g h h' : X₀} (hh : h ∈ SwCen g) (hh' : h' ∈ SwCen g) :
    h * h' ∈ SwCen g :=
  ⟨SwC.mul_mem hh.1 hh'.1, fun o ho hodd =>
    Commute.mul_left (hh.2 o ho hodd) (hh'.2 o ho hodd)⟩

private lemma swCen_inv_mul {g h h' : X₀} (hh : h ∈ SwCen g) (hh' : h' ∈ SwCen g) :
    h⁻¹ * h' ∈ SwCen g :=
  swCen_mul (swCen_inv hh) hh'

private lemma odd_of_semiconj {a x y : X₀} (h : SemiconjBy a x y)
    (hx : Odd (orderOf x)) : Odd (orderOf y) := by
  rw [← SemiconjBy.orderOf_eq a h]
  exact hx

private lemma sw_decomp {N₁ N₂ : Subgroup X₀}
    (hcomm : ∀ u ∈ N₁, ∀ v ∈ N₂, u * v = v * u)
    (hcover : ∀ o ∈ SwC, Odd (orderOf o) → o ∈ N₁ ⊔ N₂) {o : X₀}
    (ho : o ∈ SwC) (hodd : Odd (orderOf o)) :
    ∃ o₁ ∈ N₁, ∃ o₂ ∈ N₂, o = o₁ * o₂ ∧ Odd (orderOf o₁) ∧ Odd (orderOf o₂) := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute N₁ N₂ hcomm).2
  have ho' : o ∈ ((N₁ ⊔ N₂ : Subgroup X₀) : Set X₀) := hcover o ho hodd
  rw [hset, Set.mem_mul] at ho'
  obtain ⟨n₁, hn₁, n₂, hn₂, hmn⟩ := ho'
  obtain ⟨r, hr₁, hr₂, heq⟩ := CFSG.OddStandard.Solomon75.exists_odd_decomp
    (hcomm n₁ hn₁ n₂ hn₂) (by rw [hmn]; exact hodd)
  refine ⟨n₁ ^ r, N₁.pow_mem hn₁ r, n₂ ^ r, N₂.pow_mem hn₂ r, ?_, hr₁, hr₂⟩
  rw [← hmn, heq]

private lemma sw_odd_mem_of_cen {N₁ N₂ : Subgroup X₀} {g₁ g₂ : X₀}
    (hcomm : ∀ u ∈ N₁, ∀ v ∈ N₂, u * v = v * u)
    (hcover : ∀ o ∈ SwC, Odd (orderOf o) → o ∈ N₁ ⊔ N₂)
    (hN₁Cen₂ : ∀ v ∈ N₁, v ∈ SwCen g₂) (hN₂Cen₁ : ∀ v ∈ N₂, v ∈ SwCen g₁)
    (hT1 : ∀ h ∈ SwCen g₁, h ∈ SwCen g₂ → h = 1 ∨ h = xElt) (hx : orderOf xElt = 2)
    {o : X₀} (ho : o ∈ SwCen g₂) (hodd : Odd (orderOf o)) : o ∈ N₁ := by
  obtain ⟨o₁, ho₁, o₂, ho₂, ho_eq, _, hodd₂⟩ := sw_decomp hcomm hcover ho.1 hodd
  have ho₁Cen₂ : o₁ ∈ SwCen g₂ := hN₁Cen₂ o₁ ho₁
  have ho₂_eq : o₂ = o₁⁻¹ * o := by rw [ho_eq]; group
  have ho₂Cen₂ : o₂ ∈ SwCen g₂ := by
    rw [ho₂_eq]
    exact swCen_inv_mul ho₁Cen₂ ho
  have ho₂Cen₁ : o₂ ∈ SwCen g₁ := hN₂Cen₁ o₂ ho₂
  rcases hT1 o₂ ho₂Cen₁ ho₂Cen₂ with h | h
  · rw [ho_eq, h, mul_one]
    exact ho₁
  · exfalso
    rw [h, hx] at hodd₂
    exact absurd hodd₂ (by decide)

theorem swFinite_of_tables (hx : orderOf xElt = 2) (T : SwTables) : SwFinite := by
  rw [SwFinite]
  intro N₁ N₂ hx₁ hx₂ hCN₁ hCN₂ hgen₁ hgen₂ hcomm hcover
  obtain ⟨g₁, hg₁N₁, hoddg₁, hneg₁⟩ := exists_odd_ne_one hx₁ hgen₁ hx
  obtain ⟨g₂, hg₂N₂, hoddg₂, hneg₂⟩ := exists_odd_ne_one hx₂ hgen₂ hx
  have hg₁C : g₁ ∈ SwC := hCN₁ hg₁N₁
  have hg₂C : g₂ ∈ SwC := hCN₂ hg₂N₂
  have hN₂Cen₁ : ∀ v ∈ N₂, v ∈ SwCen g₁ := by
    intro v hv
    refine ⟨hCN₂ hv, ?_⟩
    intro o ho hodd
    obtain ⟨o₁, ho₁, o₂, ho₂, ho_eq, _, _⟩ := sw_decomp hcomm hcover ho hodd
    have hmid : o₂ * g₁ * o₂⁻¹ = g₁ := Commute.mul_inv_cancel (hcomm g₁ hg₁N₁ o₂ ho₂).symm
    have hconv : o * g₁ * o⁻¹ = o₁ * g₁ * o₁⁻¹ := by
      rw [ho_eq]
      calc o₁ * o₂ * g₁ * (o₁ * o₂)⁻¹
          = o₁ * (o₂ * g₁ * o₂⁻¹) * o₁⁻¹ := by group
        _ = o₁ * g₁ * o₁⁻¹ := by rw [hmid]
    rw [hconv]
    exact (hcomm (o₁ * g₁ * o₁⁻¹)
      (N₁.mul_mem (N₁.mul_mem ho₁ hg₁N₁) (N₁.inv_mem ho₁)) v hv).symm
  have hN₁Cen₂ : ∀ v ∈ N₁, v ∈ SwCen g₂ := by
    intro v hv
    refine ⟨hCN₁ hv, ?_⟩
    intro o ho hodd
    obtain ⟨o₁, ho₁, o₂, ho₂, ho_eq, _, _⟩ := sw_decomp hcomm hcover ho hodd
    have ho_eq' : o = o₂ * o₁ := by rw [ho_eq, hcomm o₁ ho₁ o₂ ho₂]
    have hmid : o₁ * g₂ * o₁⁻¹ = g₂ := Commute.mul_inv_cancel (hcomm o₁ ho₁ g₂ hg₂N₂)
    have hconv : o * g₂ * o⁻¹ = o₂ * g₂ * o₂⁻¹ := by
      rw [ho_eq']
      calc o₂ * o₁ * g₂ * (o₂ * o₁)⁻¹
          = o₂ * (o₁ * g₂ * o₁⁻¹) * o₂⁻¹ := by group
        _ = o₂ * g₂ * o₂⁻¹ := by rw [hmid]
    rw [hconv]
    exact hcomm v hv (o₂ * g₂ * o₂⁻¹)
      (N₂.mul_mem (N₂.mul_mem ho₂ hg₂N₂) (N₂.inv_mem ho₂))
  have hg₁Cen₂ : g₁ ∈ SwCen g₂ := hN₁Cen₂ g₁ hg₁N₁
  have hg₂Cen₁ : g₂ ∈ SwCen g₁ := hN₂Cen₁ g₂ hg₂N₂
  obtain ⟨hT1, c, hcC, hT2a, hT2b⟩ :=
    T g₁ hg₁C g₂ hg₂C hoddg₁ hoddg₂ hneg₁ hneg₂ hg₁Cen₂ hg₂Cen₁
  have hodd₂N₁ : ∀ o ∈ SwCen g₂, Odd (orderOf o) → o ∈ N₁ :=
    fun o ho hodd => sw_odd_mem_of_cen hcomm hcover hN₁Cen₂ hN₂Cen₁ hT1 hx ho hodd
  have hodd₁N₂ : ∀ o ∈ SwCen g₁, Odd (orderOf o) → o ∈ N₂ :=
    fun o ho hodd => sw_odd_mem_of_cen (N₁ := N₂) (N₂ := N₁) (g₁ := g₂) (g₂ := g₁)
      (fun u hu v hv => (hcomm v hv u hu).symm)
      (fun o ho hodd => by rw [sup_comm]; exact hcover o ho hodd)
      hN₂Cen₁ hN₁Cen₂ (fun h hh₂ hh₁ => hT1 h hh₁ hh₂) hx ho hodd
  let f : X₀ →* X₀ := (MulAut.conj c⁻¹).toMonoidHom
  have happ : ∀ y : X₀, f y = c⁻¹ * y * c := fun y => by
    change (MulAut.conj c⁻¹) y = c⁻¹ * y * c
    rw [MulAut.conj_apply, inv_inv]
  have hconj_le : CFSG.conjugate N₁ c ≤ N₂ := by
    have hmapgen : CFSG.conjugate N₁ c ≤
        Subgroup.closure (f '' {a | a ∈ N₁ ∧ Odd (orderOf a)}) := by
      change N₁.map f ≤ Subgroup.closure (f '' {a | a ∈ N₁ ∧ Odd (orderOf a)})
      exact (Subgroup.map_mono hgen₁).trans (le_of_eq (MonoidHom.map_closure f _))
    refine hmapgen.trans ((Subgroup.closure_le (K := N₂)).mpr ?_)
    rintro y ⟨o, ⟨ho₁, hodd⟩, hy⟩
    rw [← hy, happ]
    have hoC : o ∈ SwC := hCN₁ ho₁
    have hoCen₂ : o ∈ SwCen g₂ := hN₁Cen₂ o ho₁
    have h2a := hT2a o hoC hodd hoCen₂
    have hodd' : Odd (orderOf (c⁻¹ * o * c)) :=
      odd_of_semiconj (show SemiconjBy c⁻¹ o (c⁻¹ * o * c) by
        show c⁻¹ * o = (c⁻¹ * o * c) * c⁻¹
        group) hodd
    exact hodd₁N₂ (c⁻¹ * o * c) h2a hodd'
  have hge_le : N₂ ≤ CFSG.conjugate N₁ c := by
    refine hgen₂.trans ((Subgroup.closure_le (K := CFSG.conjugate N₁ c)).mpr ?_)
    rintro o ⟨ho₂, hodd⟩
    have hoC : o ∈ SwC := hCN₂ ho₂
    have hoCen₁ : o ∈ SwCen g₁ := hN₂Cen₁ o ho₂
    have h2b := hT2b o hoC hodd hoCen₁
    have hodd' : Odd (orderOf (c * o * c⁻¹)) :=
      odd_of_semiconj (show SemiconjBy c o (c * o * c⁻¹) by
        show c * o = (c * o * c⁻¹) * c
        group) hodd
    have hmem : c * o * c⁻¹ ∈ N₁ := hodd₂N₁ (c * o * c⁻¹) h2b hodd'
    change o ∈ N₁.map f
    rw [Subgroup.mem_map]
    exact ⟨c * o * c⁻¹, hmem, by rw [happ]; group⟩
  exact ⟨c, hcC, le_antisymm hconj_le hge_le⟩

end CFSG.OddStandard.SmallF3.Omega
