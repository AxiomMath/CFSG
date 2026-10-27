module

public import CFSG.CGT.PushingUpLit.CGT6X.End3Mod
public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem center_eq_bot_of_inverted (hV : ∀ v : V, v ^ 2 = 1) {G Y L : Subgroup (MulAut V)}
    (hSQ : SimpleQuot Y) (hgen : CommGen Y) (hYL : Y ≤ L)
    (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V))) {t : MulAut V} (ht2 : t ^ 2 = 1)
    (htY : ∀ y ∈ Y, t * y = y * t) (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    (hinv : ∀ z ∈ Subgroup.center ↥L, t * (z : MulAut V) * t⁻¹ = (z : MulAut V)⁻¹)
    (hirr : ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤) : Subgroup.center ↥L = ⊥ := by
  have hU : ∀ z ∈ Subgroup.center ↥L, ∀ u ∈ commV Y, (z : MulAut V) u = u := by
    intro z hz u hu
    have hdY : ∀ y ∈ Y, (z : MulAut V) * y = y * (z : MulAut V) := by
      intro y hy
      have := Subgroup.mem_center_iff.mp hz ⟨y, hYL hy⟩
      exact (congrArg Subtype.val this).symm
    have hzn : (z : MulAut V) ^ Nat.card ↥(Subgroup.center ↥L) = 1 := by
      have h1 : orderOf z ∣ Nat.card ↥(Subgroup.center ↥L) :=
        Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hz
      have h2 : z ^ Nat.card ↥(Subgroup.center ↥L) = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
      have := congrArg Subtype.val h2
      simpa using this
    exact ms_three hgen hdY (ms_odd hV hSQ htY ht2 hdY hodd hzn (hinv z hz)) u hu
  let N : Subgroup V :=
    { carrier := {v | ∀ z ∈ Subgroup.center ↥L, (z : MulAut V) v = v}
      one_mem' := fun z _ => map_one _
      mul_mem' := fun {a b} ha hb z hz => by
        show (z : MulAut V) (a * b) = a * b
        rw [map_mul, ha z hz, hb z hz]
      inv_mem' := fun {a} ha z hz => by
        show (z : MulAut V) a⁻¹ = a⁻¹
        rw [map_inv, ha z hz] }
  have hUN : commV Y ≤ N := fun u hu z hz => hU z hz u hu
  have hGinv : GInv G N := by
    intro g hg n hn z hz
    have hgN := hGL hg
    have hgi : g⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) := inv_mem hgN
    have hzL : g⁻¹ * (z : MulAut V) * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hgi (z : MulAut V)).mp z.2
      simpa using this
    have hcen : (⟨g⁻¹ * (z : MulAut V) * g, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hl' : g * (l : MulAut V) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgN _).mp l.2
      have h1 := Subgroup.mem_center_iff.mp hz ⟨g * (l : MulAut V) * g⁻¹, hl'⟩
      have h2 : g * (l : MulAut V) * g⁻¹ * (z : MulAut V) =
          (z : MulAut V) * (g * (l : MulAut V) * g⁻¹) := by
        have := congrArg Subtype.val h1
        simpa using this
      show (l : MulAut V) * (g⁻¹ * (z : MulAut V) * g) = g⁻¹ * (z : MulAut V) * g * (l : MulAut V)
      calc (l : MulAut V) * (g⁻¹ * (z : MulAut V) * g)
          = g⁻¹ * ((g * (l : MulAut V) * g⁻¹) * (z : MulAut V)) * g := by group
        _ = g⁻¹ * ((z : MulAut V) * (g * (l : MulAut V) * g⁻¹)) * g := by rw [h2]
        _ = g⁻¹ * (z : MulAut V) * g * (l : MulAut V) := by group
    have h3 := hn _ hcen
    show (z : MulAut V) (g n) = g n
    have h4 : (z : MulAut V) (g n) = g ((g⁻¹ * (z : MulAut V) * g) n) := by
      simp [MulAut.mul_apply]
    rw [h4]
    have h5 : (g⁻¹ * (z : MulAut V) * g) n = n := h3
    rw [h5]
  have hbot : commV Y ≠ ⊥ := by
    intro h
    apply hSQ.1
    rw [h]
    simp
  have hNbot : N ≠ ⊥ := fun h => hbot (le_bot_iff.mp (h ▸ hUN))
  have hNtop : N = ⊤ := (hirr N hGinv).resolve_left hNbot
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext v
  have hv : v ∈ N := by rw [hNtop]; exact Subgroup.mem_top v
  exact hv z hz

end CFSG.CGT.PushingUpLit.CGT6X.End4
