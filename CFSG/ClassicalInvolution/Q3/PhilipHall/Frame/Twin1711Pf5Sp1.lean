module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Blocks
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Top

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open CFSG.Monster.B.Co2 PkG CovK CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG CFSG.Open

set_option linter.unusedSectionVars false


theorem card_conjSub' (g : ↥ySub) (R : Subgroup ↥ySub) : Nat.card (conjSub g R) = Nat.card R := by
  have e : ↥R ≃ ↥(conjSub g R) :=
    ⟨fun x => ⟨g * x * g⁻¹, conj_mem_conjSub x.2⟩, fun y => ⟨g⁻¹ * y * g, mem_conjSub_iff.1 y.2⟩,
      fun x => Subtype.ext (by show g⁻¹ * (g * (x : ↥ySub) * g⁻¹) * g = x; group),
      fun y => Subtype.ext (by show g * (g⁻¹ * (y : ↥ySub) * g) * g⁻¹ = y; group)⟩
  exact (Nat.card_congr e).symm

theorem hid_Y (R : Subgroup ↥ySub) (t : ↥ySub) (hC : CoreData (⊤ : Subgroup ↥ySub) R t) :
    ∃ g : ↥ySub, conjSub g R = RY ∧ g * t * g⁻¹ = Sp6Cover.tY := by
  obtain ⟨e⟩ := hC.q8
  obtain ⟨i, j, hiR, hjR, hii, hjj, hji, hRel⟩ := quat_data e hC.inv
  obtain ⟨g, hg⟩ := ClsK.classify_inv hC.inv.sq hC.inv.ne_one
    (fun h => hC.noncentral fun x _ => h x) ⟨i, hii⟩
  refine ⟨g, ?_, hg⟩
  refine core_eq_RY_of_data ?_ (by rw [card_conjSub', card_of_quat R e]) ?_
  · refine ⟨g * i * g⁻¹, g * j * g⁻¹, conj_mem_conjSub hiR, conj_mem_conjSub hjR, ?_, ?_, ?_, ?_⟩
    · calc g * i * g⁻¹ * (g * i * g⁻¹) = g * (i * i) * g⁻¹ := by group
        _ = Sp6Cover.tY := by rw [hii, hg]
    · calc g * j * g⁻¹ * (g * j * g⁻¹) = g * (j * j) * g⁻¹ := by group
        _ = Sp6Cover.tY := by rw [hjj, hg]
    · calc g * j * g⁻¹ * (g * i * g⁻¹) * (g * j * g⁻¹)⁻¹ = g * (j * i * j⁻¹) * g⁻¹ := by group
        _ = (g * i * g⁻¹)⁻¹ := by rw [hji]; group
    · intro r hr
      have hr' : g⁻¹ * r * g ∈ R := mem_conjSub_iff.1 hr
      obtain ⟨k, hk, hcase⟩ := hRel _ hr'
      refine ⟨k, hk, ?_⟩
      have hrr : r = g * (g⁻¹ * r * g) * g⁻¹ := by group
      rcases hcase with h | h
      · left
        rw [hrr, h, conj_pow]
      · right
        rw [hrr, h, conj_pow]
        group
  · intro s hs
    have hsc : s * Sp6Cover.tY = Sp6Cover.tY * s :=
      Subgroup.mem_centralizer_singleton_iff.1 (mem_TT_iff.1 hs)
    have hs' : g⁻¹ * s * g ∈ (⊤ : Subgroup ↥ySub) ⊓ Subgroup.centralizer ({t} : Set ↥ySub) := by
      refine ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hg] at hsc
      calc g⁻¹ * s * g * t = g⁻¹ * (s * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * s) * g := by rw [hsc]
        _ = t * (g⁻¹ * s * g) := by group
    have hsg : conjSub s (conjSub g R) = conjSub g (conjSub (g⁻¹ * s * g) R) := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [hsg]
    rcases hC.twins _ hs' with h | h
    · left
      rw [h]
    · right
      intro a ha b hb
      have ha' : g⁻¹ * a * g ∈ R := mem_conjSub_iff.1 ha
      have hb' : g⁻¹ * b * g ∈ conjSub (g⁻¹ * s * g) R := mem_conjSub_iff.1 hb
      have := h _ ha' _ hb'
      calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
        _ = b * a := by group

open Sp0Core in
theorem noSandwichIn_Y : NoSandwichIn ↥ySub := by
  intro R t B N hC hS
  obtain ⟨g, hgR, hgt⟩ := hid_Y R t hC
  let ψ : ↥ySub →* ↥ySub := (MulAut.conj g⁻¹).toMonoidHom
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹).injective
  have hr : ψ.range = ⊤ := MonoidHom.range_eq_top.2 (MulAut.conj g⁻¹).surjective
  have ht' : ψ Sp6Cover.tY = t := by
    simp only [ψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hgt]; group
  rw [← hr] at hC hS
  have hC' := hC.comap hψ ht'
  have hS' := hS.comap hC.le hψ ht'
  have hRc : R.comap ψ = RY := by
    rw [← hgR]
    ext y
    simp [ψ, mem_conjSub_iff]
  rw [hRc] at hC' hS'
  exact noSandwich_blocks tY_unique RY_norm hover_Y hfix1_Y hfix2_Y hidx1_Y hidx2_Y hS'

theorem noSandwichAt_of_equiv {H H' : Type} [Group H] [Group H'] (h : NoSandwichAt H')
    (f : H ≃* H') : NoSandwichAt H := by
  intro G _ _ X R t B N ⟨e⟩ hC hS
  exact h G X R t B N ⟨e.trans f⟩ hC hS

theorem sp1_proved : NoSandwichAt ModSp1 :=
  noSandwichAt_of_equiv (noSandwichAt_of_in noSandwichIn_Y) modSp1Equiv

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
