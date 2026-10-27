module

public import CFSG.GH74.GLS.C3.Layer2.L4TI
public import CFSG.GH74.Uniqueness.Statements

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.Uniqueness

variable {C : Type} [Group C]

omit [Group C] in
theorem mem_zpowers_iff_of_mul_self {C : Type} [Group C] {v a : C} (hv : v * v = 1) :
    a ∈ zpowers v ↔ a = 1 ∨ a = v := by
  constructor
  · intro ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    have h2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    have hv1 : v ^ k = v ^ (k % 2) := by
      conv_lhs => rw [hk]
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [hv1, h0, zpow_zero]
    · right; rw [hv1, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

variable {v : C} {Zs : Set C} {S E : Subgroup C} {x : C}

namespace TIData

theorem zpowers_le_normalizer (h : TIData v Zs S E x) :
    zpowers v ≤ normalizer (E : Set C) :=
  zpowers_le.2 (le_normalizer h.v_mem)

theorem zpowers_le_S (h : TIData v Zs S E x) : zpowers v ≤ S := zpowers_le.2 (h.E_le h.v_mem)

theorem zpowers_normal (h : TIData v Zs S E x) : (zpowers v).Normal := by
  refine ⟨fun a ha g => ?_⟩
  rcases (mem_zpowers_iff_of_mul_self h.v_sq).1 ha with rfl | rfl
  · simp
  · rw [h.conj_v g]; exact mem_zpowers _

end TIData

section Quotient

variable (v : C) [(zpowers v).Normal]

@[expose] def Zt (Zs : Set C) : Set (C ⧸ zpowers v) := (QuotientGroup.mk' (zpowers v)) '' Zs

@[expose] noncomputable def Mt (E : Subgroup C) : Subgroup (C ⧸ zpowers v) :=
  (normalizer (E : Set C)).map (QuotientGroup.mk' (zpowers v))

variable {v}

theorem mem_Zt_iff (h : TIData v Zs S E x) (z : C) :
    (QuotientGroup.mk z : C ⧸ zpowers v) ∈ Zt v Zs ↔ z ∈ Zs := by
  constructor
  · rintro ⟨z', hz', hzz⟩
    have hzz' : (QuotientGroup.mk z' : C ⧸ zpowers v) = QuotientGroup.mk z := hzz
    rw [QuotientGroup.eq] at hzz'
    rcases (mem_zpowers_iff_of_mul_self h.v_sq).1 hzz' with h1 | h1
    · have : z = z' := by
        have := mul_eq_one_iff_eq_inv.1 h1
        simpa using this.symm
      rw [this]; exact hz'
    · have : z = z' * v := by rw [← h1]; group
      rw [this]; exact h.Z_mul_v z' hz'
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem mem_Mt_iff (h : TIData v Zs S E x) (z : C) :
    (QuotientGroup.mk z : C ⧸ zpowers v) ∈ Mt v E ↔ z ∈ normalizer (E : Set C) := by
  constructor
  · rintro ⟨n, hn, hnz⟩
    have hnz' : (QuotientGroup.mk n : C ⧸ zpowers v) = QuotientGroup.mk z := hnz
    rw [QuotientGroup.eq] at hnz'
    have : z = n * (n⁻¹ * z) := by group
    rw [this]
    exact (normalizer (E : Set C)).mul_mem hn (h.zpowers_le_normalizer hnz')
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem isPGroup_closure_pair {X : Type} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : IsPGroup 2 (Subgroup.closure ({a, b} : Set X)) := by
  have hcomm : ∀ s ∈ ({a, b} : Set X), ∀ t ∈ ({a, b} : Set X), s * t = t * s := by
    intro s hs t ht
    rcases hs with rfl | hs <;> rcases ht with rfl | ht
    · rfl
    · rw [Set.mem_singleton_iff] at ht; rw [ht]; exact hab
    · rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hab.symm
    · rw [Set.mem_singleton_iff] at hs ht; rw [hs, ht]
  have hsq : ∀ s ∈ ({a, b} : Set X), s * s = 1 := by
    intro s hs
    rcases hs with rfl | hs
    · exact ha
    · rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hb
  have hsub : ({a, b} : Set X) ⊆ Subgroup.centralizer ({a, b} : Set X) := by
    intro s hs
    exact Subgroup.mem_centralizer_iff.2 fun t ht => hcomm t ht s hs
  have hle : Subgroup.closure ({a, b} : Set X) ≤ Subgroup.centralizer ({a, b} : Set X) :=
    (Subgroup.closure_le _).2 hsub
  have hle' : Subgroup.closure ({a, b} : Set X) ≤
      Subgroup.centralizer (Subgroup.closure ({a, b} : Set X) : Set X) := by
    rw [Subgroup.centralizer_closure]
    exact hle
  have hcl : ∀ y ∈ Subgroup.closure ({a, b} : Set X), y * y = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hsq y hy
    | one => simp
    | mul y z hy' hz' hy hz =>
      have hyz : z * y = y * z :=
        Subgroup.mem_centralizer_iff.1 (hle' hy') z hz'
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [hyz]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [hy, hz, one_mul]
    | inv y _ hy =>
      calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
        _ = 1 := by rw [hy, inv_one]
  intro g
  obtain ⟨g, hg⟩ := g
  refine ⟨1, Subtype.ext ?_⟩
  show g ^ (2 ^ 1) = 1
  rw [pow_one, sq]
  exact hcl g hg

theorem mem_S_of_mk_mem_map (h : TIData v Zs S E x) {y : C}
    (hy : (QuotientGroup.mk y : C ⧸ zpowers v) ∈ S.map (QuotientGroup.mk' (zpowers v))) :
    y ∈ S := by
  obtain ⟨s, hs, hsy⟩ := hy
  have hsy' : (QuotientGroup.mk s : C ⧸ zpowers v) = QuotientGroup.mk y := hsy
  rw [QuotientGroup.eq] at hsy'
  have : y = s * (s⁻¹ * y) := by group
  rw [this]
  exact S.mul_mem hs (h.zpowers_le_S hsy')

theorem isSylowOf_map_S [Finite C] (h : TIData v Zs S E x) :
    IsSylowOf 2 (S.map (QuotientGroup.mk' (zpowers v))) ⊤ := by
  rw [isSylowOf_iff]
  obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.1 h.sylow
  refine ⟨le_top, hp.map _, ?_⟩
  rw [Subgroup.relIndex_top_right] at hidx ⊢
  intro hdvd
  exact hidx (hdvd.trans (Subgroup.index_map_dvd S (QuotientGroup.mk'_surjective _)))

theorem isInvariantInvolutionSet_Zt (h : TIData v Zs S E x) :
    IsInvariantInvolutionSet (Zt v Zs) := by
  constructor
  · intro z hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    have hsq : (QuotientGroup.mk' (zpowers v) z0) ^ 2 = 1 := by
      rw [← map_pow, sq, h.Z_sq z0 hz0, map_one]
    have hne : (QuotientGroup.mk' (zpowers v) z0) ≠ 1 := by
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      rcases (mem_zpowers_iff_of_mul_self h.v_sq).1 h1 with h2 | h2
      · exact h.Z_ne z0 hz0 h2
      · exact h.v_nmem (h2 ▸ hz0)
    exact orderOf_eq_prime hsq hne
  · intro z hz g
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨g0⁻¹ * z0 * g0, h.Z_conj' hz0 g0, by simp [QuotientGroup.mk'_apply]⟩

theorem isProductDisconnected_Zt [Finite C] (h : TIData v Zs S E x) (hne : normalizer (E : Set C) ≠ ⊤) :
    IsProductDisconnected (Zt v Zs) (Mt v E) := by
  have hxN : x ∈ normalizer (E : Set C) := le_normalizer h.x_E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro htop
    apply hne
    rw [eq_top_iff]
    intro c _
    have : (QuotientGroup.mk c : C ⧸ zpowers v) ∈ Mt v E := by rw [htop]; trivial
    exact (mem_Mt_iff h c).1 this
  · exact ⟨QuotientGroup.mk x, (mem_Zt_iff h x).2 h.x_Z, (mem_Mt_iff h x).2 hxN⟩
  ·
    intro z hz hzM g
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g
    have hz0N : z0 ∈ normalizer (E : Set C) := (mem_Mt_iff h z0).1 hzM
    have hconj : ((QuotientGroup.mk g0 : C ⧸ zpowers v))⁻¹ * (QuotientGroup.mk' (zpowers v) z0) *
        QuotientGroup.mk g0 = QuotientGroup.mk (g0⁻¹ * z0 * g0) := by
      simp [QuotientGroup.mk'_apply]
    rw [hconj, mem_Mt_iff h, mem_Mt_iff h]
    constructor
    · intro hg
      have := h.ti_Z (g := g0⁻¹) hz0 hz0N (by simpa using hg)
      simpa using (normalizer (E : Set C)).inv_mem this
    · intro hg
      exact (normalizer (E : Set C)).mul_mem
        ((normalizer (E : Set C)).mul_mem ((normalizer (E : Set C)).inv_mem hg) hz0N) hg
  ·
    intro u hu huM
    obtain ⟨hu2, a, ha, b, hb, hab, rfl⟩ := hu
    obtain ⟨z, hz, rfl⟩ := ha
    obtain ⟨z', hz', rfl⟩ := hb
    have hzZ : z ∈ Zs := hz
    have hz'Z : z' ∈ Zs := hz'
    have hprod : (QuotientGroup.mk' (zpowers v) z) * (QuotientGroup.mk' (zpowers v) z') =
        QuotientGroup.mk (z * z') := rfl
    rw [hprod] at huM hu2 ⊢
    have huN : z * z' ∈ normalizer (E : Set C) := (mem_Mt_iff h (z * z')).1 huM
    have hnot : z * z' ∉ zpowers v := by
      intro hmem
      have : (QuotientGroup.mk (z * z') : C ⧸ zpowers v) = 1 := (QuotientGroup.eq_one_iff _).2 hmem
      rw [this, orderOf_one] at hu2
      omega
    have ha2 : (QuotientGroup.mk' (zpowers v) z) * (QuotientGroup.mk' (zpowers v) z) = 1 := by
      rw [← map_mul, h.Z_sq z hzZ, map_one]
    have hb2 : (QuotientGroup.mk' (zpowers v) z') * (QuotientGroup.mk' (zpowers v) z') = 1 := by
      rw [← map_mul, h.Z_sq z' hz'Z, map_one]
    have hP := isPGroup_closure_pair ha2 hb2 hab
    obtain ⟨k, -, hk⟩ := exists_mem_conj_le_of_isSylowOf (isSylowOf_map_S h) (le_top) hP
    obtain ⟨k0, rfl⟩ := QuotientGroup.mk_surjective k
    have hz1S : k0⁻¹ * z * k0 ∈ S := by
      apply mem_S_of_mk_mem_map h
      have := hk _ (Subgroup.subset_closure (Set.mem_insert _ _))
      simpa [QuotientGroup.mk'_apply] using this
    have hz2S : k0⁻¹ * z' * k0 ∈ S := by
      apply mem_S_of_mk_mem_map h
      have := hk _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      simpa [QuotientGroup.mk'_apply] using this
    have hz1E := ((h.Z_inter _ hz1S).1 (h.Z_conj' hzZ k0)).1
    have hz2E := ((h.Z_inter _ hz2S).1 (h.Z_conj' hz'Z k0)).1
    set e₃ := (k0⁻¹ * z * k0) * (k0⁻¹ * z' * k0) with he₃
    have he₃E : e₃ ∈ E := E.mul_mem hz1E hz2E
    have he₃eq : e₃ = k0⁻¹ * (z * z') * k0 := by rw [he₃]; group
    have he₃1 : e₃ ≠ 1 := by
      intro h1
      apply hnot
      have : z * z' = k0 * e₃ * k0⁻¹ := by rw [he₃eq]; group
      rw [this, h1]; simp
    have he₃v : e₃ ≠ v := by
      intro h1
      apply hnot
      have : z * z' = k0 * e₃ * k0⁻¹ := by rw [he₃eq]; group
      rw [this, h1, h.conj_v]; exact mem_zpowers v
    have he₃Z : e₃ ∈ Zs := h.Zmem_of_mem_E he₃E he₃1 he₃v
    have hk0N : k0 ∈ normalizer (E : Set C) := by
      apply h.ti_Z he₃Z (le_normalizer he₃E)
      have : k0 * e₃ * k0⁻¹ = z * z' := by rw [he₃eq]; group
      rw [this]; exact huN
    have hwE : z * z' ∈ E := by
      have := (mem_normalizer_iff.1 hk0N e₃).1 he₃E
      have h' : k0 * e₃ * k0⁻¹ = z * z' := by rw [he₃eq]; group
      rwa [h'] at this
    have hw1 : z * z' ≠ 1 := fun h1 => hnot (h1 ▸ one_mem _)
    have hwv : z * z' ≠ v := fun h1 => hnot (h1 ▸ mem_zpowers v)
    have hwZ : z * z' ∈ Zs := h.Zmem_of_mem_E hwE hw1 hwv
    intro y hy
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective y
    have hcomm : (QuotientGroup.mk g0 : C ⧸ zpowers v) * QuotientGroup.mk (z * z') =
        QuotientGroup.mk (z * z') * QuotientGroup.mk g0 := mem_centralizer_singleton_iff.1 hy
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
    have hconjE : g0⁻¹ * (z * z') * g0 ∈ E := by
      rcases (mem_zpowers_iff_of_mul_self h.v_sq).1 hcomm with h1 | h1
      · have : g0⁻¹ * (z * z') * g0 = z * z' := by
          have h2 : (g0 * (z * z'))⁻¹ * ((z * z') * g0) = 1 := h1
          have h3 : (z * z') * g0 = g0 * (z * z') := (inv_mul_eq_one.1 h2).symm
          calc g0⁻¹ * (z * z') * g0 = g0⁻¹ * ((z * z') * g0) := by group
            _ = z * z' := by rw [h3]; group
        rw [this]; exact hwE
      · have : g0⁻¹ * (z * z') * g0 = (z * z') * v := by
          have h2 : (g0 * (z * z'))⁻¹ * ((z * z') * g0) = v := h1
          have h3 : (z * z') * g0 = (g0 * (z * z')) * v := by
            calc (z * z') * g0 = (g0 * (z * z')) * ((g0 * (z * z'))⁻¹ * ((z * z') * g0)) := by group
              _ = (g0 * (z * z')) * v := by rw [h2]
          calc g0⁻¹ * (z * z') * g0 = g0⁻¹ * ((z * z') * g0) := by group
            _ = g0⁻¹ * ((g0 * (z * z')) * v) := by rw [h3]
            _ = (z * z') * v := by group
        rw [this]; exact E.mul_mem hwE h.v_mem
    have hg0N : g0⁻¹ ∈ normalizer (E : Set C) := by
      apply h.ti_all hwE hwZ
      simpa using hconjE
    have : g0 ∈ normalizer (E : Set C) := by simpa using (normalizer (E : Set C)).inv_mem hg0N
    exact (mem_Mt_iff h g0).2 this

end Quotient

end CFSG.GH74.GLS.C3.Layer2.L4
