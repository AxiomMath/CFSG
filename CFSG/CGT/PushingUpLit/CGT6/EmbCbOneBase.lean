module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbApiConj
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltOT

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv
open CFSG.EvenSmallLie.OddTranspAlt (cls)

variable {V : Type} [CommGroup V] [Finite V]

structure OneCfg (G T Y : Subgroup (MulAut V)) (t : MulAut V) (m : ℕ)
    (X : Subgroup (MulAut V)) : Prop where
  cfg : EndCfg4 G T Y
  hV : ∀ v : V, v ^ 2 = 1
  hm : 7 ≤ m
  hodd : Odd m
  hY : YAlt Y m
  h2 : Alt2Rank1
  hNL : NatLiftStatement
  htG : t ∈ G
  htT : t ∈ T
  ht2 : t ^ 2 = 1
  ht1 : t ≠ 1
  hX : IsCbLift G Y t m X
  huniq : ∀ X' : Subgroup (MulAut V), IsCbLift G Y t m X' → X' = X

namespace OneCfg

variable {G T Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ} (c : OneCfg G T Y t m X)

include c in
theorem Y_le_G : Y ≤ G := fun _ hy => (c.cfg.adm.hYC hy).1

include c in
theorem X_le_G : X ≤ G := c.hX.le_G

include c in
theorem Y_le_X : Y ≤ X := c.hX.Y_le

include c in
theorem t_cent : ∀ y ∈ Y, t * y = y * t := fun _ hy =>
  Subgroup.mem_centralizer_iff.mp (c.cfg.adm.hYC hy).2 t c.htT

include c in
theorem t_mem_centralizer : t ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
  rw [Subgroup.mem_centralizer_iff]
  exact fun y hy => (c.t_cent y hy).symm

@[expose] def tG : ↥G := ⟨t, c.htG⟩

include c in
theorem orderOf_tG : orderOf c.tG = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    show t ^ 2 = 1
    exact c.ht2
  · intro h
    exact c.ht1 (congrArg Subtype.val h)

end OneCfg

theorem cbo_inv_conj_mem {A : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : ∀ a ∈ A, g⁻¹ * a * g ∈ A := by
  let φ : ↥A → ↥A := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h : g * (x : MulAut V) * g⁻¹ = g * (y : MulAut V) * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h)
  intro y hy
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hφ ⟨y, hy⟩
  have h : g * (x : MulAut V) * g⁻¹ = y := congrArg Subtype.val hx
  have h' : g⁻¹ * y * g = x := by rw [← h]; group
  rw [h']
  exact x.2

theorem cbo_map_conj_eq {A : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : A.map (MulAut.conj g).toMonoidHom = A := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact hg a ha
  · intro a ha
    exact ⟨g⁻¹ * a * g, cbo_inv_conj_mem hg a ha, by simp [MulAut.conj_apply]; group⟩

namespace OneCfg

variable {G T Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ} (c : OneCfg G T Y t m X)

include c in
theorem normalizes_Y_of_comm {g : MulAut V} (hg : g ∈ G) (hgt : g * t = t * g) :
    ∀ y ∈ Y, g * y * g⁻¹ ∈ Y :=
  c.cfg.normalizes_of_commute c.h2 c.hV c.hm c.hodd c.hY (t := c.tG) (c := ⟨g, hg⟩)
    c.orderOf_tG c.t_mem_centralizer (Subtype.ext hgt)

include c in
theorem normalizes_X_of_comm {g : MulAut V} (hg : g ∈ G) (hgt : g * t = t * g) :
    ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
  have hY := cbo_map_conj_eq (c.normalizes_Y_of_comm hg hgt)
  have hgt' : g * t * g⁻¹ = t := by rw [hgt]; group
  have h1 := c.huniq _ (c.hX.conj hg hY hgt')
  intro x hx
  rw [← h1]
  exact ⟨x, hx, rfl⟩

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
