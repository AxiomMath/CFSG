module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup2

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

def KK (x : G) (V : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ centralizer (V : Set G) ∧ ∃ v ∈ V, k * x * k⁻¹ = x * v}
  one_mem' := ⟨one_mem _, 1, V.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, va, hva, hxa⟩ ⟨hb, vb, hvb, hxb⟩
    refine ⟨mul_mem ha hb, va * vb, V.mul_mem hva hvb, ?_⟩
    have hav : a * vb * a⁻¹ = vb := by
      have := mem_centralizer_iff.1 ha vb hvb
      calc a * vb * a⁻¹ = (vb * a) * a⁻¹ := by rw [this]
        _ = vb := by group
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * (x * vb) * a⁻¹ := by rw [hxb]
      _ = (a * x * a⁻¹) * (a * vb * a⁻¹) := by group
      _ = (x * va) * vb := by rw [hxa, hav]
      _ = x * (va * vb) := by group
  inv_mem' := by
    rintro a ⟨ha, va, hva, hxa⟩
    refine ⟨inv_mem ha, va⁻¹, V.inv_mem hva, ?_⟩
    have hav : a⁻¹ * va * a = va := by
      have := mem_centralizer_iff.1 ha va hva
      calc a⁻¹ * va * a = a⁻¹ * (a * va) := by rw [← this]; group
        _ = va := by group
    have h1 : a⁻¹ * x * a = x * va⁻¹ := by
      have e1 : x = a⁻¹ * (x * va) * a := by
        calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
          _ = a⁻¹ * (x * va) * a := by rw [hxa]
      have e2 : a⁻¹ * (x * va) * a = (a⁻¹ * x * a) * (a⁻¹ * va * a) := by group
      rw [hav] at e2
      rw [e2] at e1
      calc a⁻¹ * x * a = (a⁻¹ * x * a) * va * va⁻¹ := by group
        _ = x * va⁻¹ := by rw [← e1]
    simpa using h1

namespace Out12

variable {x : G} {T V : Subgroup G} (h : Out12 G x T V)
include h

theorem E_le_KK : EV x V ≤ KK x V := by
  intro e he
  refine ⟨h.E_le_C he, 1, V.one_mem, ?_⟩
  have hx := h.EV_comm he x_mem_EV
  calc e * x * e⁻¹ = (x * e) * e⁻¹ := by rw [hx]
    _ = x * 1 := by group

theorem not_sylow_E [Finite G] : ¬ Sylow2In (EV x V) (centralizer (V : Set G)) := by
  intro hsyl
  have hV4 : Nat.card V = 4 := h.V_four.2
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      exact hcon v hv
    have h1 : Nat.card V = 1 := by rw [this]; exact Subgroup.card_bot
    omega
  obtain ⟨g, hgC, hg⟩ := h.aut2 v₀ hv₀
  have key : ∀ k : ↥(KK x V), x * (k * x * k⁻¹) ∈ V := by
    rintro ⟨k, hk, v, hv, hkx⟩
    show x * (k * x * k⁻¹) ∈ V
    rw [hkx]
    have : x * (x * v) = v := by rw [← mul_assoc, h.x_sq, one_mul]
    rw [this]; exact hv
  let ψ : ↥(KK x V) →* ↥V := MonoidHom.mk' (fun k => ⟨x * (k * x * k⁻¹), key k⟩) (by
    rintro ⟨a, ha, va, hva, hxa⟩ ⟨b, hb, vb, hvb, hxb⟩
    apply Subtype.ext
    show x * (a * b * x * (a * b)⁻¹) = (x * (a * x * a⁻¹)) * (x * (b * x * b⁻¹))
    have hav : a * vb * a⁻¹ = vb := by
      have := mem_centralizer_iff.1 ha vb hvb
      calc a * vb * a⁻¹ = (vb * a) * a⁻¹ := by rw [this]
        _ = vb := by group
    have e1 : a * b * x * (a * b)⁻¹ = x * (va * vb) := by
      calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
        _ = a * (x * vb) * a⁻¹ := by rw [hxb]
        _ = (a * x * a⁻¹) * (a * vb * a⁻¹) := by group
        _ = (x * va) * vb := by rw [hxa, hav]
        _ = x * (va * vb) := by group
    rw [e1, hxa, hxb]
    have hxx : x * x = 1 := h.x_sq
    calc x * (x * (va * vb)) = (x * x) * (va * vb) := by group
      _ = va * vb := by rw [hxx, one_mul]
      _ = (x * x) * va * ((x * x) * vb) := by rw [hxx]; group
      _ = x * (x * va) * (x * (x * vb)) := by group)
  have hEker : (EV x V).subgroupOf (KK x V) ≤ ψ.ker := by
    intro e he
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show x * ((e : G) * x * (e : G)⁻¹) = 1
    have he' : (e : G) ∈ EV x V := he
    have hx := h.EV_comm he' x_mem_EV
    calc x * ((e : G) * x * (e : G)⁻¹) = x * (x * e * (e : G)⁻¹) := by rw [hx]
      _ = (x * x) := by group
      _ = 1 := h.x_sq
  have hodd : ¬ 2 ∣ (EV x V).relIndex (KK x V) := by
    intro hd
    have hEK : EV x V ≤ KK x V := h.E_le_KK
    have hKC : KK x V ≤ centralizer (V : Set G) := fun k hk => hk.1
    have hmul := relIndex_mul_relIndex _ _ _ hEK hKC
    apply hsyl.2.2
    rw [← hmul]
    exact Dvd.dvd.mul_right hd _
  have hidx : ψ.ker.index ∣ (EV x V).relIndex (KK x V) := Subgroup.index_dvd_of_le hEker
  have hidx4 : ψ.ker.index ∣ 4 := by
    rw [Subgroup.index_ker, ← hV4]
    exact Subgroup.card_subgroup_dvd_card _
  have hnd2 : ¬ 2 ∣ ψ.ker.index := fun hd => hodd (dvd_trans hd hidx)
  have h1 : ψ.ker.index = 1 := by
    have h4 : ψ.ker.index ∣ 2 ^ 2 := by simpa using hidx4
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    interval_cases i
    · simpa using hi'
    · exfalso; apply hnd2; rw [hi']; simp
    · exfalso; apply hnd2; rw [hi']; norm_num
  have hktop : ψ.ker = ⊤ := Subgroup.index_eq_one.1 h1
  have hgK : g ∈ KK x V := ⟨hgC, v₀, hv₀, hg⟩
  have hψ : ψ ⟨g, hgK⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hktop]; trivial
  have hval : x * (g * x * g⁻¹) = 1 := congrArg (fun z : ↥V => (z : G)) hψ
  rw [hg] at hval
  have : v₀ = 1 := by
    calc v₀ = (x * x) * v₀ := by rw [h.x_sq, one_mul]
      _ = x * (x * v₀) := by group
      _ = 1 := hval
  exact hv₀1 this

end Out12

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
