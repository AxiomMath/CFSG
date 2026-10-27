module

public import CFSG.GH74.Uniqueness.SU.SU13TC6C

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem commutator_mul_central {p p' m m' : G} (hpm' : p * m' = m' * p)
    (hp'm : p' * m = m * p') (hpp' : p * p' = p' * p)
    (hc : (p * p') * (m * m' * m⁻¹ * m'⁻¹) = (m * m' * m⁻¹ * m'⁻¹) * (p * p')) :
    (p * m) * (p' * m') * (p * m)⁻¹ * (p' * m')⁻¹ = m * m' * m⁻¹ * m'⁻¹ := by
  have h1 : (p * m) * (p' * m') = (p * p') * (m * m') := by
    calc (p * m) * (p' * m') = p * (m * p') * m' := by group
      _ = p * (p' * m) * m' := by rw [hp'm]
      _ = (p * p') * (m * m') := by group
  have h2 : (p' * m') * (p * m) = (p * p') * (m' * m) := by
    calc (p' * m') * (p * m) = p' * (m' * p) * m := by group
      _ = p' * (p * m') * m := by rw [hpm']
      _ = (p' * p) * (m' * m) := by group
      _ = (p * p') * (m' * m) := by rw [hpp']
  calc (p * m) * (p' * m') * (p * m)⁻¹ * (p' * m')⁻¹
      = ((p * m) * (p' * m')) * ((p' * m') * (p * m))⁻¹ := by group
    _ = ((p * p') * (m * m')) * (((p * p') * (m' * m)))⁻¹ := by rw [h1, h2]
    _ = (p * p') * (m * m' * m⁻¹ * m'⁻¹) * (p * p')⁻¹ := by group
    _ = m * m' * m⁻¹ * m'⁻¹ := by rw [hc]; group

theorem not_conj_mem_commutator {Y M : Subgroup G} {s : G}
    (hY' : ∀ n ∈ ⁅Y, Y⁆, ∀ y ∈ Y, y * n = n * y)
    (hM : ∀ a ∈ centralizer ({s} : Set G), ∀ b ∈ centralizer ({s} : Set G), a * b * a⁻¹ * b⁻¹ ∈ M)
    (hs : s ∉ M) (g : G) : g * s * g⁻¹ ∉ ⁅Y, Y⁆ := by
  intro hg
  have hYc : ∀ y ∈ Y, g⁻¹ * y * g ∈ centralizer ({s} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have h1 := hY' _ hg y hy
    calc g⁻¹ * y * g * s = g⁻¹ * (y * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * y) * g := by rw [h1]
      _ = s * (g⁻¹ * y * g) := by group
  have hmem := conj_mem_commutator (Y₂ := centralizer ({s} : Set G)) (g := g⁻¹)
    (fun y hy => by simpa using hYc y hy) hg
  have hcomm : ⁅centralizer ({s} : Set G), centralizer ({s} : Set G)⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact hM a ha b hb
  apply hs
  have : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
  rw [this] at hmem
  exact hcomm hmem

end Generic

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Ctx9

variable (X : Ctx9 G z)

abbrev VF : Subgroup G := TT (Vsub z X.L.e.s₁ X.hWc) X.L.f.F (V_invariant X.L.f X.hWc)

theorem VF_le_cent : X.VF ≤ centralizer ({X.L.e.s₁} : Set G) := by
  rintro _ ⟨v, hv, f', hf', rfl⟩
  refine mul_mem (oc_le _ hv.1) ?_
  exact F_le_centralizerF X.L.e X.L.f.toFPart hf'

theorem s₁_not_mem_VF : X.L.e.s₁ ∉ X.VF := by
  intro h
  obtain ⟨v, hv, f', hf', hvf⟩ := h
  have hs₁W : X.L.e.s₁ ∈ oc (centralizer ({X.L.e.s₁} : Set G)) :=
    zpowers_le_oc X.L.e (mem_zpowers _)
  have hf'W : f' ∈ oc (centralizer ({X.L.e.s₁} : Set G)) := by
    have : f' = v⁻¹ * X.L.e.s₁ := by rw [hvf]; group
    rw [this]
    exact (oc (centralizer ({X.L.e.s₁} : Set G))).mul_mem
      ((oc (centralizer ({X.L.e.s₁} : Set G))).inv_mem hv.1) hs₁W
  have hf'1 : f' = 1 := by
    have : f' ∈ oc (centralizer ({X.L.e.s₁} : Set G)) ⊓ X.L.f.F := mem_inf.mpr ⟨hf'W, hf'⟩
    rw [W_inf_F X.L.e X.L.f.toFPart, mem_bot] at this
    exact this
  rw [hf'1, mul_one] at hvf
  have hs₁V : X.L.e.s₁ ∈ Vsub z X.L.e.s₁ X.hWc := by
    have h0 := hv
    rwa [← hvf] at h0
  have hv1 : X.L.e.s₁ ∈ zpowers X.L.e.s₁ ⊓ Vsub z X.L.e.s₁ X.hWc :=
    mem_inf.mpr ⟨mem_zpowers _, hs₁V⟩
  rw [zpowers_inf_V X.L.f X.hWc, mem_bot] at hv1
  have := X.L.e.s₁_ord
  rw [hv1, orderOf_one] at this
  omega

theorem decomp_cent_s₁ {g : G} (hg : g ∈ centralizer ({X.L.e.s₁} : Set G)) :
    ∃ p ∈ zpowers X.L.e.s₁, ∃ m ∈ X.VF, g = p * m := by
  have hgs : g * X.L.e.s₁ = X.L.e.s₁ * g := mem_centralizer_singleton_iff.mp hg
  obtain ⟨c, k, hc, hcz, hk, hgck⟩ := X.l.a g hgs
  have hcH : c ∈ centralizer ({X.L.e.s₁} : Set G) ⊓ centralizer ({z} : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc, mem_centralizer_singleton_iff.mpr hcz⟩
  rw [X.L.f.cent] at hcH
  obtain ⟨p, hp, f', hf', hpf⟩ := SU1.mem_sup_of_commute (A := zpowers X.L.e.s₁) (B := X.L.f.F)
    (fun p hp a ha => zpowers_comm_of_mem_centralizer
      (mem_centralizer_singleton_iff.mpr (X.L.f.F_s₁ a ha)) hp) hcH
  obtain ⟨c', hc', v, hv, hkv⟩ := W_eq_sup_V X.hz X.L.f X.hWc hk
  have hfc : f' * c' = c' * f' := by
    have := zpowers_comm_of_mem_centralizer (F_le_centralizerF X.L.e X.L.f.toFPart hf') hc'
    exact this.symm
  have hv' : f' * v * f'⁻¹ ∈ Vsub z X.L.e.s₁ X.hWc := V_invariant X.L.f X.hWc f' hf' v hv
  refine ⟨p * c', mul_mem hp hc', (f' * v * f'⁻¹) * f', ⟨_, hv', f', hf', rfl⟩, ?_⟩
  rw [hgck, ← hpf, hkv]
  calc p * f' * (c' * v) = p * (f' * c') * v := by group
    _ = p * (c' * f') * v := by rw [hfc]
    _ = p * c' * (f' * v * f'⁻¹ * f') := by group

theorem comm_cent_s₁ {a b : G} (ha : a ∈ centralizer ({X.L.e.s₁} : Set G))
    (hb : b ∈ centralizer ({X.L.e.s₁} : Set G)) : a * b * a⁻¹ * b⁻¹ ∈ X.VF := by
  obtain ⟨p, hp, m, hm, rfl⟩ := X.decomp_cent_s₁ ha
  obtain ⟨p', hp', m', hm', rfl⟩ := X.decomp_cent_s₁ hb
  have hmC := X.VF_le_cent hm
  have hm'C := X.VF_le_cent hm'
  have hcomm : ∀ {q x : G}, q ∈ zpowers X.L.e.s₁ → x ∈ centralizer ({X.L.e.s₁} : Set G) →
      q * x = x * q := fun hq hx => zpowers_comm_of_mem_centralizer hx hq
  have hcc : m * m' * m⁻¹ * m'⁻¹ ∈ centralizer ({X.L.e.s₁} : Set G) :=
    mul_mem (mul_mem (mul_mem hmC hm'C) (inv_mem hmC)) (inv_mem hm'C)
  have hpp' : p * p' ∈ zpowers X.L.e.s₁ := mul_mem hp hp'
  have hp'C : p' ∈ centralizer ({X.L.e.s₁} : Set G) := by
    have h0 := hp'
    obtain ⟨k, hk⟩ := h0
    rw [← hk]
    exact mem_centralizer_singleton_iff.mpr ((Commute.refl X.L.e.s₁).zpow_left k).eq
  have hpp'c : p * p' = p' * p := hcomm hp hp'C
  rw [commutator_mul_central (hcomm hp hm'C) (hcomm hp' hmC) hpp'c (hcomm hpp' hcc)]
  exact (X.VF).mul_mem ((X.VF).mul_mem ((X.VF).mul_mem hm hm') ((X.VF).inv_mem hm)) ((X.VF).inv_mem hm')

theorem not_conj_s₁_mem (g : G) : g * X.L.e.s₁ * g⁻¹ ∉ ⁅X.Y, X.Y⁆ :=
  not_conj_mem_commutator (fun _ hn _ hy => X.Y'_comm hn hy)
    (fun _ ha _ hb => X.comm_cent_s₁ ha hb) X.s₁_not_mem_VF g

end Ctx9

end CFSG.GH74.Uniqueness.SU.SU13
