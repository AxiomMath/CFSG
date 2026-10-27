module

public import CFSG.LargeExtraspecial.S111BO2
public import CFSG.LargeExtraspecial.S111BTIA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem Lbar_le_normalizer_EF :
    S.Lbar k ≤ normalizer ((Ebar S k k' ⊔ Ebar S k' k : Subgroup S.O) : Set S.O) :=
  le_sup_left.trans P.le_normalizer_EF

theorem comm_mem_Ebar_of_mem_O2Sub {o l : S.O} (ho : o ∈ O2Sub (S.Lbar k ⊔ S.Lbar k'))
    (hl : l ∈ S.Lbar k) : o * l * o⁻¹ * l⁻¹ ∈ Ebar S k k' := by
  rw [← P.inf_O2Sub_eq]
  refine ⟨Subgroup.mul_mem _ ((mem_normalizer_iff.mp (O2Sub_le_normalizer_Lbar P.hy.hyp4
    P.hy.cons le_sup_left (Lbar_sup_le_Mbar S k k') ho) l).mp hl) (Subgroup.inv_mem _ hl), ?_⟩
  have h1 : l * o⁻¹ * l⁻¹ ∈ O2Sub (S.Lbar k ⊔ S.Lbar k') :=
    O2Sub_normal (mem_sup_left hl) (inv_mem ho)
  rw [show o * l * o⁻¹ * l⁻¹ = o * (l * o⁻¹ * l⁻¹) by group]
  exact Subgroup.mul_mem _ ho h1

theorem map_conj_eq_of_conj_mem {x : S.O} (hx : x ∈ S.Lbar k ⊔ S.Lbar k')
    (hc : ∀ l ∈ S.Lbar k, ∀ l₂ ∈ S.Lbar k,
      x * l * x⁻¹ * l₂ * (x * l * x⁻¹)⁻¹ ∈ S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k)) :
    (S.Lbar k).map (MulAut.conj x).toMonoidHom = S.Lbar k := by
  have hXM := (Lbar_sup_le_Mbar S k k')
  have hLN2 : IsPGroup 2 (S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k) : Subgroup S.O) :=
    (isPGroup_Lbar S P.memQ).to_sup_of_normal_right' P.isPGroup_EF P.Lbar_le_normalizer_EF
  have hLx2 : IsPGroup 2 ((S.Lbar k).map (MulAut.conj x).toMonoidHom) :=
    (isPGroup_Lbar S P.memQ).map _
  have hLxX : (S.Lbar k).map (MulAut.conj x).toMonoidHom ≤ S.Lbar k ⊔ S.Lbar k' := by
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem hx (mem_sup_left hl)) (inv_mem hx)
  have key : ∀ w ∈ S.Lbar k ⊔ S.Lbar k',
      (∀ l₂ ∈ S.Lbar k, w * l₂ * w⁻¹ ∈ S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k)) →
      ∀ y ∈ S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k),
        w * y * w⁻¹ ∈ S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k) := by
    intro w hw hwl y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup P.Lbar_le_normalizer_EF hy
    rw [show w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) by group]
    exact mul_mem (hwl a ha) (mem_sup_right (P.conj_mem_EF hw hb))
  have hLxN : (S.Lbar k).map (MulAut.conj x).toMonoidHom ≤
      normalizer ((S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k) : Subgroup S.O) : Set S.O) := by
    rintro _ ⟨l, hl, rfl⟩
    have hwX : x * l * x⁻¹ ∈ S.Lbar k ⊔ S.Lbar k' :=
      mul_mem (mul_mem hx (mem_sup_left hl)) (inv_mem hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_normalizer_of_conj_mem (key _ hwX (hc l hl)) (key _ (inv_mem hwX) ?_)
    intro l₂ hl₂
    have := hc l⁻¹ (inv_mem hl) l₂ hl₂
    rwa [show x * l⁻¹ * x⁻¹ = (x * l * x⁻¹)⁻¹ by group] at this
  have h2 := hLx2.to_sup_of_normal_right' hLN2 hLxN
  have hle := S4.le_normalizer_of_weaklyClosed P.hy.cons.weaklyClosed h2
    (sup_le (hLxX.trans hXM) (sup_le (S.Lbar_le_Mbar k) ((Ebar_sup_le S k k').trans hXM)))
    (le_sup_left.trans le_sup_right)
  obtain ⟨m', hm'⟩ := MonoidHom.mem_range.mp (hXM hx)
  rw [← hm', ← Lbar_mul S m' k] at hle ⊢
  exact P.hy.cons.weaklyClosed m' m'.2 (le_sup_left.trans hle)

theorem mem_sup_EF_of_conj_mem {x : S.O} (hx : x ∈ S.Lbar k ⊔ S.Lbar k') {l : S.O}
    (hl : l ∈ S.Lbar k) (hu : x * l * x⁻¹ ∈ S.Lbar k ⊔ O2Sub (S.Lbar k ⊔ S.Lbar k')) :
    x * l * x⁻¹ ∈ S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k) := by
  refine mem_sup_of_conj_mem_of_comm le_sup_left
    (fun _ hy _ hn => P.conj_mem_EF hy hn) (isPGroup_Lbar S P.memQ)
    (fun a ha b hb => Lbar_comm S P.memQ ha hb) (fun y hy hc => P.map_conj_eq_of_conj_mem hy hc)
    hx hl fun l₂ hl₂ => ?_
  obtain ⟨a, ha, o, ho, hao⟩ := exists_mul_of_mem_sup
    ((le_sup_left : S.Lbar k ≤ S.Lbar k ⊔ S.Lbar k').trans (le_normalizer_O2Sub _)) hu
  rw [← hao]
  have h1 := P.comm_mem_Ebar_of_mem_O2Sub ho hl₂
  have h2 := P.conj_mem_EF (mem_sup_left ha :
    a ∈ S.Lbar k ⊔ S.Lbar k') (mem_sup_left h1 : o * l₂ * o⁻¹ * l₂⁻¹ ∈ Ebar S k k' ⊔ Ebar S k' k)
  have hc' : l₂ * a⁻¹ = a⁻¹ * l₂ :=
    ((Commute.inv_left (show Commute a l₂ from Lbar_comm S P.memQ ha hl₂)).eq).symm
  have e : a * o * l₂ * (a * o)⁻¹ * l₂⁻¹ = a * (o * l₂ * o⁻¹ * l₂⁻¹) * a⁻¹ := by
    calc a * o * l₂ * (a * o)⁻¹ * l₂⁻¹ =
          a * (o * l₂ * o⁻¹ * l₂⁻¹) * (l₂ * a⁻¹ * l₂⁻¹) := by group
      _ = a * (o * l₂ * o⁻¹ * l₂⁻¹) * a⁻¹ := by rw [hc', mul_inv_cancel_right]
  rw [e]
  exact h2

end Pair111

variable {m : S.M}

theorem Pair111.isTI97 (P : Pair111 S g A h k ((m : G) * k))
    (hTI : IsTIModEF S k ((m : G) * k)) :
    S9.IsTI97 S k m (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k))) := by
  intro x hx
  have hNO := P.EF_le_O2Sub
  have hO : (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k))).map (MulAut.conj x).toMonoidHom =
      O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)) :=
    map_conj_eq_of_mem_normalizer (le_normalizer_O2Sub _ hx)
  rcases hTI x hx with h1 | h1
  · left
    have e1 : S.Lbar k ⊔ O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)) =
        (S.Lbar k ⊔ (Ebar S k ((m : G) * k) ⊔ Ebar S ((m : G) * k) k)) ⊔
          O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)) := by
      rw [sup_assoc, sup_eq_right.mpr hNO]
    rw [e1, Subgroup.map_sup, h1, hO]
  · right
    rintro y ⟨hy1, hy2⟩
    obtain ⟨y₀, hy₀, rfl⟩ := hy1
    obtain ⟨l, hl, o₀, ho₀, rfl⟩ := exists_mul_of_mem_sup
      ((le_sup_left : S.Lbar k ≤ S.Lbar k ⊔ S.Lbar ((m : G) * k)).trans
        (le_normalizer_O2Sub _)) hy₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy2 ⊢
    have ho₁ : x * o₀ * x⁻¹ ∈ O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)) := O2Sub_normal hx ho₀
    have e2 : x * (l * o₀) * x⁻¹ = (x * l * x⁻¹) * (x * o₀ * x⁻¹) := by group
    rw [e2] at hy2 ⊢
    have hu : x * l * x⁻¹ ∈ S.Lbar k ⊔ O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)) := by
      have hy2' : x * l * x⁻¹ * (x * o₀ * x⁻¹) ∈
          S.Lbar k ⊔ O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)) := hy2
      have := mul_mem hy2' (inv_mem (mem_sup_right ho₁ :
        x * o₀ * x⁻¹ ∈ S.Lbar k ⊔ O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k))))
      rwa [mul_inv_cancel_right] at this
    have hu' := P.mem_sup_EF_of_conj_mem hx hl hu
    have hu'' : x * l * x⁻¹ ∈ (S.Lbar k ⊔ (Ebar S k ((m : G) * k) ⊔
        Ebar S ((m : G) * k) k)).map (MulAut.conj x).toMonoidHom := ⟨l, mem_sup_left hl, rfl⟩
    exact Subgroup.mul_mem _ (hNO (h1 ⟨hu'', hu'⟩)) ho₁

end CFSG.LargeExtraspecial.S11
