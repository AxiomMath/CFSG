module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64G

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64

variable (c : Cfg64 Ω K J z j u v R T)
include c

theorem oddCompl_J'_le_X {N₀K N₀J : Subgroup G}
    (hK0 : OddCompl (K ⊓ Subgroup.centralizer ({j} : Set G)) (Subgroup.zpowers u) N₀K)
    (hJ0 : OddCompl (J ⊓ Subgroup.centralizer ({z} : Set G)) (Subgroup.zpowers v) N₀J)
    {r : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    conjSub r N₀J ≤ (J ⊓ Subgroup.centralizer ({z} : Set G)) ⊔
      (K ⊓ Subgroup.centralizer ({j} : Set G)) := by
  set X' := (J ⊓ Subgroup.centralizer ({z} : Set G)) ⊔ (K ⊓ Subgroup.centralizer ({j} : Set G))
    with hX'
  have hXe : (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) = X' :=
    c.X_eq
  obtain ⟨hK1, hJ1, -⟩ := c.X_eq_oddCore_sup hK0 hJ0
  rw [hXe] at hK1 hJ1
  have hOX : oddCoreOf X' ≤ X' := oddCoreOf_le_self X'
  set A := conjSub r N₀J with hAdef
  set UV := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hUV
  set O₀ := N₀K ⊔ N₀J with hO₀
  have hO₀X : O₀ ≤ X' := (sup_le hK1 hJ1).trans hOX
  have hA : OddCompl (conjSub r J ⊓ Subgroup.centralizer ({z} : Set G))
      (conjSub r (Subgroup.zpowers v)) A := by
    rw [c.CJ'_eq_conj hr]
    exact hJ0.conj r
  have hAK : ∀ a ∈ A, a ∈ Subgroup.normalizer (K : Set G) := fun a ha =>
    c.CJ'_le_normalizer_K hr hru (hA.le ha)
  have hAJ : ∀ a ∈ A, a ∈ Subgroup.normalizer (J : Set G) := fun a ha =>
    c.CJ'_le_normalizer_J hr hru (hA.le ha)
  have hAz : ∀ a ∈ A, a ∈ Subgroup.centralizer ({z} : Set G) := fun a ha => (hA.le ha).2
  have hAj : ∀ a ∈ A, a ∈ Subgroup.centralizer ({j} : Set G) := by
    intro a ha
    have h1 := hA.le ha
    rw [c.CJ'_eq hr hru] at h1
    exact h1.2
  have hUz : Subgroup.zpowers u ≤ Subgroup.centralizer ({z} : Set G) := fun _ hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (AscL62.cyclic_comm inferInstance hx c.z_mem_U)
  have hUA : Subgroup.zpowers u ≤ Subgroup.normalizer (A : Set G) := fun g hg =>
    hA.le_normalizer (mem_normalizer_inf_centralizer (c.U_le_normalizer_J' hr hru hg) (hUz hg))
  have hVA : Subgroup.zpowers v ≤ Subgroup.normalizer (A : Set G) := fun g hg =>
    hA.le_normalizer (mem_normalizer_inf_centralizer (c.V_le_normalizer_J' hr hru hg)
      (c.symm.U_le_centralizer hg))
  have hUO : Subgroup.zpowers u ≤ Subgroup.normalizer (O₀ : Set G) := fun g hg =>
    mem_normalizer_sup (hK0.H_le_normalizer ⟨c.hUK hg, c.U_le_centralizer hg⟩)
      (hJ0.le_normalizer (mem_normalizer_inf_centralizer (c.U_le_normalizer hg) (hUz hg)))
  have hVO : Subgroup.zpowers v ≤ Subgroup.normalizer (O₀ : Set G) := fun g hg =>
    mem_normalizer_sup
      (hK0.le_normalizer (mem_normalizer_inf_centralizer (c.symm.U_le_normalizer hg)
        (c.V_le_centralizer_j hg)))
      (hJ0.H_le_normalizer ⟨c.hVJ hg, c.symm.U_le_centralizer hg⟩)
  have hUVA : UV ≤ Subgroup.normalizer (A : Set G) := sup_le hUA hVA
  have hUVO : UV ≤ Subgroup.normalizer (O₀ : Set G) := sup_le hUO hVO
  have hcomV : ∀ a ∈ A, ∀ g ∈ Subgroup.zpowers v, a⁻¹ * (g * a * g⁻¹) ∈ N₀J := by
    intro a ha g hg
    have hxA : a⁻¹ * (g * a * g⁻¹) ∈ A :=
      A.mul_mem (A.inv_mem ha) ((Subgroup.mem_normalizer_iff.mp (hVA hg) a).mp ha)
    have hxJ : a⁻¹ * (g * a * g⁻¹) ∈ J := by
      have e : a⁻¹ * (g * a * g⁻¹) = (a⁻¹ * g * a⁻¹⁻¹) * g⁻¹ := by group
      rw [e]
      exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer _).inv_mem (hAJ a ha)) g).mp (c.hVJ hg)) (J.inv_mem (c.hVJ hg))
    exact hJ0.mem_of_odd _ ⟨hxJ, hAz _ hxA⟩ (hA.odd_orderOf hxA)
  have hcomU : ∀ a ∈ A, ∀ g ∈ Subgroup.zpowers u, a⁻¹ * (g * a * g⁻¹) ∈ N₀K := by
    intro a ha g hg
    have hxA : a⁻¹ * (g * a * g⁻¹) ∈ A :=
      A.mul_mem (A.inv_mem ha) ((Subgroup.mem_normalizer_iff.mp (hUA hg) a).mp ha)
    have hxK : a⁻¹ * (g * a * g⁻¹) ∈ K := by
      have e : a⁻¹ * (g * a * g⁻¹) = (a⁻¹ * g * a⁻¹⁻¹) * g⁻¹ := by group
      rw [e]
      exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer _).inv_mem (hAK a ha)) g).mp (c.hUK hg)) (K.inv_mem (c.hUK hg))
    exact hK0.mem_of_odd _ ⟨hxK, hAj _ hxA⟩ (hA.odd_orderOf hxA)
  have hcomUV : ∀ a ∈ A, ∀ g ∈ UV, a⁻¹ * (g * a * g⁻¹) ∈ O₀ := by
    intro a ha g hg
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := exists_mul_of_mem_sup_of_commutes c.hUV hg
    have e : a⁻¹ * ((g₁ * g₂) * a * (g₁ * g₂)⁻¹) =
        (a⁻¹ * (g₁ * a * g₁⁻¹)) * (g₁ * (a⁻¹ * (g₂ * a * g₂⁻¹)) * g₁⁻¹) := by group
    rw [e]
    refine O₀.mul_mem (Subgroup.mem_sup_left (hcomU a ha g₁ hg₁)) ?_
    have h1 := hcomV a ha g₂ hg₂
    have h2 : g₁ * (a⁻¹ * (g₂ * a * g₂⁻¹)) * g₁⁻¹ ∈ N₀J :=
      (Subgroup.mem_normalizer_iff.mp
        (hJ0.le_normalizer (mem_normalizer_inf_centralizer (c.U_le_normalizer hg₁) (hUz hg₁)))
        _).mp h1
    exact Subgroup.mem_sup_right h2
  intro a ha
  set D : Subgroup G := A ⊓ O₀ with hD
  set C : Set G := {x | a⁻¹ * x ∈ D} with hC
  have hCstable : ∀ g ∈ UV, ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro g hg x hx
    show a⁻¹ * (g * x * g⁻¹) ∈ D
    have e : a⁻¹ * (g * x * g⁻¹) = (a⁻¹ * (g * a * g⁻¹)) * (g * (a⁻¹ * x) * g⁻¹) := by group
    rw [e]
    refine D.mul_mem ⟨A.mul_mem (A.inv_mem ha)
      ((Subgroup.mem_normalizer_iff.mp (hUVA hg) a).mp ha), hcomUV a ha g hg⟩ ?_
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hUVA hg) _).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hUVO hg) _).mp hx.2⟩
  have hCcard : Nat.card C = Nat.card D := by
    refine Nat.card_congr ⟨fun x => ⟨a⁻¹ * x, x.2⟩, fun d => ⟨a * d, ?_⟩, ?_, ?_⟩
    · show a⁻¹ * (a * d) ∈ D
      simp
    · intro x
      apply Subtype.ext
      show a * (a⁻¹ * x) = x
      group
    · intro d
      apply Subtype.ext
      show a⁻¹ * (a * d) = d
      group
  have hCodd : Odd (Nat.card C) := by
    rw [hCcard]
    exact hA.odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨c₀, hc₀C, hc₀fix⟩ := exists_mem_centralizer_of_odd c.UV_isPGroup hCstable hCodd
  have hc₀A : c₀ ∈ A := by
    have := A.mul_mem ha hc₀C.1
    simpa using this
  have hb : r⁻¹ * c₀ * r ∈ N₀J := by
    have := (mem_conjSub_iff).mp hc₀A
    exact this
  have hbX : r⁻¹ * c₀ * r ∈ X' := Subgroup.mem_sup_left (hJ0.le hb)
  have hc₀j : c₀ * (z * j) = (z * j) * c₀ := by
    have h1 := hc₀fix (z * j) (UV.mul_mem c.z_mem_UV c.j_mem_UV)
    calc c₀ * (z * j) = (z * j) * c₀ * (z * j)⁻¹ * (z * j) := by rw [h1]
      _ = (z * j) * c₀ := by group
  have hc₀j' : c₀ * j = j * c₀ := by
    have h1 := hc₀fix j c.j_mem_UV
    calc c₀ * j = j * c₀ * j⁻¹ * j := by rw [h1]
      _ = j * c₀ := by group
  have hrj : r * j * r⁻¹ = z * j := c.conj_j_of_not_mem hr hru
  have hbj : (r⁻¹ * c₀ * r) * j = j * (r⁻¹ * c₀ * r) := by
    have hj' : j = r⁻¹ * (z * j) * r := by rw [← hrj]; group
    calc (r⁻¹ * c₀ * r) * j = r⁻¹ * c₀ * (r * j * r⁻¹) * r := by group
      _ = r⁻¹ * (c₀ * (z * j)) * r := by rw [hrj]; group
      _ = r⁻¹ * ((z * j) * c₀) * r := by rw [hc₀j]
      _ = (r⁻¹ * (z * j) * r) * (r⁻¹ * c₀ * r) := by group
      _ = j * (r⁻¹ * c₀ * r) := by rw [← hj']
  have heK : (r⁻¹ * c₀ * r) * c₀⁻¹ ∈ K := by
    have e : (r⁻¹ * c₀ * r) * c₀⁻¹ = r⁻¹ * (c₀ * r * c₀⁻¹) := by group
    rw [e]
    exact K.mul_mem (K.inv_mem (c.hR.1 hr))
      ((Subgroup.mem_normalizer_iff.mp (hAK c₀ hc₀A) r).mp (c.hR.1 hr))
  have hej : (r⁻¹ * c₀ * r) * c₀⁻¹ ∈ Subgroup.centralizer ({j} : Set G) := by
    refine (Subgroup.centralizer _).mul_mem (Subgroup.mem_centralizer_singleton_iff.mpr hbj)
      ((Subgroup.centralizer _).inv_mem (Subgroup.mem_centralizer_singleton_iff.mpr hc₀j'))
  have heX : (r⁻¹ * c₀ * r) * c₀⁻¹ ∈ X' := Subgroup.mem_sup_right ⟨heK, hej⟩
  have hc₀X : c₀ ∈ X' := by
    have h1 := X'.mul_mem (X'.inv_mem heX) hbX
    have e : ((r⁻¹ * c₀ * r) * c₀⁻¹)⁻¹ * (r⁻¹ * c₀ * r) = c₀ := by group
    rwa [e] at h1
  have hd : a⁻¹ * c₀ ∈ X' := hO₀X hc₀C.2
  have := X'.mul_mem hc₀X (X'.inv_mem hd)
  simpa using this

theorem UV_le_X' : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤
    (J ⊓ Subgroup.centralizer ({z} : Set G)) ⊔ (K ⊓ Subgroup.centralizer ({j} : Set G)) :=
  sup_le (le_sup_of_le_right (le_inf c.hUK c.U_le_centralizer))
    (le_sup_of_le_left (le_inf c.hVJ c.symm.U_le_centralizer))

theorem conjSub_X {N₀K N₀J : Subgroup G}
    (hK0 : OddCompl (K ⊓ Subgroup.centralizer ({j} : Set G)) (Subgroup.zpowers u) N₀K)
    (hJ0 : OddCompl (J ⊓ Subgroup.centralizer ({z} : Set G)) (Subgroup.zpowers v) N₀J)
    {r : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    conjSub r ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G))) =
      (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) := by
  rw [c.X_eq]
  set X' := (J ⊓ Subgroup.centralizer ({z} : Set G)) ⊔ (K ⊓ Subgroup.centralizer ({j} : Set G))
    with hX'
  have hle : conjSub r X' ≤ X' := by
    have e : conjSub r X' = conjSub r (J ⊓ Subgroup.centralizer ({z} : Set G)) ⊔
        conjSub r (K ⊓ Subgroup.centralizer ({j} : Set G)) := Subgroup.map_sup _ _ _
    rw [e]
    refine sup_le ?_ ?_
    · rw [← c.CJ'_eq_conj hr]
      have hA : OddCompl (conjSub r J ⊓ Subgroup.centralizer ({z} : Set G))
          (conjSub r (Subgroup.zpowers v)) (conjSub r N₀J) := by
        rw [c.CJ'_eq_conj hr]
        exact hJ0.conj r
      intro h hh
      obtain ⟨n, hn, w, hw, rfl⟩ := hA.dec h hh
      exact X'.mul_mem (c.oddCompl_J'_le_X hK0 hJ0 hr hru hn) (c.UV_le_X' (c.conjSub_V_le hr hw))
    · rw [conjSub_inf, conjSub_centralizer_singleton, conjSub_eq_self_of_mem (c.hR.1 hr),
        c.conj_j_of_not_mem hr hru, c.inf_centralizer_zj]
      exact le_sup_right
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [AscL62.natCard_conjSub])

end Cfg64

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
