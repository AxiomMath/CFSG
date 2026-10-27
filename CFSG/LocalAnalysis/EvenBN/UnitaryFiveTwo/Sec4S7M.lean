module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7K
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7J

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem Data.pull_map_conj (d : Data G) (M : Subgroup SU52) (g : SU52) :
    d.pull (M.map (MulAut.conj g).toMonoidHom) =
      (d.pull M).map (MulAut.conj (d.ι g)).toMonoidHom := by
  unfold Data.pull
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem Data.A₁_inf_map_v :
    d.A₁ ⊓ d.A₁.map (MulAut.conj d.v).toMonoidHom = d.X₃ := by
  show d.pull A₁sub ⊓ (d.pull A₁sub).map (MulAut.conj (d.ι vSU)).toMonoidHom = d.pull X₃sub
  rw [← d.pull_map_conj, ← d.pull_inf, A₁sub_inf_map_vSU]

theorem Data.X₃_map_u : d.X₃.map (MulAut.conj d.u).toMonoidHom = d.X₂ := by
  show (d.pull X₃sub).map (MulAut.conj (d.ι uSU)).toMonoidHom = d.pull X₂sub
  rw [← d.pull_map_conj, map_uSU_X₃sub]

theorem Data.A₂_sup_K₂_eq :
    d.A₂ ⊔ d.K₂ = d.A₁ ⊔ d.X₂.map (MulAut.conj d.v).toMonoidHom := by
  show d.pull A₂sub ⊔ d.pull K₂sub = d.pull A₁sub ⊔ (d.pull X₂sub).map (MulAut.conj (d.ι vSU)).toMonoidHom
  rw [← d.pull_map_conj, ← d.pull_sup, ← d.pull_sup, A₂sub_sup_K₂sub_eq]

theorem Data.u_mul_u (d : Data G) : d.u * d.u = 1 := by
  show d.ι uSU * d.ι uSU = 1
  rw [← map_mul, uSU_mul_self, map_one]

theorem Data.v_mul_v (d : Data G) : d.v * d.v = 1 := by
  show d.ι vSU * d.ι vSU = 1
  rw [← map_mul, vSU_mul_self, map_one]

theorem Data.uv_pow_four (d : Data G) : (d.u * d.v) ^ 4 = 1 := by
  show (d.ι uSU * d.ι vSU) ^ 4 = 1
  rw [← map_mul, ← map_pow, uSU_mul_vSU_pow_four, map_one]

theorem Data.u_mem_L (d : Data G) : d.u ∈ d.L := d.ι_mem _

theorem Data.v_mem_L (d : Data G) : d.v ∈ d.L := d.ι_mem _

section Gen



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

theorem Data.conj_delta (h : d.Hyp) {g : G} (hg : g ∈ d.H) (x : G) :
    (g * x * g⁻¹) * (d.t * (g * x * g⁻¹) * d.t) = g * (x * (d.t * x * d.t)) * g⁻¹ := by
  have hgt : g * d.t = d.t * g := mem_centralizer_singleton_iff.1 hg
  have h1 : d.t * g = g * d.t := hgt.symm
  have h2 : g⁻¹ * d.t = d.t * g⁻¹ := (Commute.inv_left (show Commute g d.t from hgt)).eq
  have e : d.t * (g * x * g⁻¹) * d.t = g * (d.t * x * d.t) * g⁻¹ := by
    calc d.t * (g * x * g⁻¹) * d.t = (d.t * g) * x * (g⁻¹ * d.t) := by group
      _ = (g * d.t) * x * (d.t * g⁻¹) := by rw [h1, h2]
      _ = g * (d.t * x * d.t) * g⁻¹ := by group
  rw [e]
  group

include h hKU in
theorem Data.Hyp.delta_conj (w : ↥(Data.Nn h hKU hf)) {x : G} (hx : x ∈ Data.Nn h hKU hf) :
    Data.delta h hKU hf w * x * (Data.delta h hKU hf w)⁻¹ = (w : G) * x * (w : G)⁻¹ := by
  have hc : (d.t * (w : G) * d.t) * x = x * (d.t * (w : G) * d.t) :=
    (h.comm_Nn_tcNn hKU hf hx (h.t_conj_mem_tcNn hKU hf w.2)).symm
  rw [h.delta_eq_mul hKU hf]
  calc (w : G) * (d.t * (w : G) * d.t) * x * ((w : G) * (d.t * (w : G) * d.t))⁻¹
      = (w : G) * ((d.t * (w : G) * d.t) * x) * (d.t * (w : G) * d.t)⁻¹ * (w : G)⁻¹ := by group
    _ = (w : G) * (x * (d.t * (w : G) * d.t)) * (d.t * (w : G) * d.t)⁻¹ * (w : G)⁻¹ := by
      rw [hc]
    _ = (w : G) * x * (w : G)⁻¹ := by group

include h hKU in
theorem Data.Hyp.exists_delta_eq_v : ∃ w : ↥(Data.Nn h hKU hf), Data.delta h hKU hf w = d.v := by
  have : d.v ∈ (Data.delta h hKU hf).range := by
    rw [h.range_delta_eq_A₂_sup_K₂ hKU hf]
    exact mem_sup_right Data.v_mem_K₂
  exact this

include h hKU in
theorem Data.Hyp.v_mem_normalizer_Nn : d.v ∈ normalizer (Data.Nn h hKU hf : Set G) := by
  obtain ⟨w, hw⟩ := h.exists_delta_eq_v hKU hf
  refine mem_normalizer_fintype fun x hx => ?_
  have := h.delta_conj hKU hf w hx
  rw [hw] at this
  rw [this]
  exact mul_mem (mul_mem w.2 hx) (inv_mem w.2)

include h hKU in
theorem Data.Hyp.eq_of_delta_eq {x y : G} (hx : x ∈ Data.Nn h hKU hf) (hy : y ∈ Data.Nn h hKU hf)
    (e : x * (d.t * x * d.t) = y * (d.t * y * d.t)) : x = y :=
  congrArg Subtype.val (h.delta_injective hKU hf (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) e)

include h hKU in
theorem Data.Hyp.exists_mem_B₁_of_mem_A₁ {a : G} (ha : a ∈ d.A₁) :
    ∃ b ∈ Data.B₁ h hKU hf, a = b * (d.t * b * d.t) := by
  obtain ⟨q, hq, hqa⟩ := h.exists_mem_Q_delta_eq hKU hf (d.A₁_le_S ha)
  exact ⟨q, (h.mem_B₁_iff hKU hf).2 ⟨hq.2, hqa ▸ ha⟩, hqa⟩

include h hKU in
theorem Data.Hyp.Nn_eq_gen (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    Data.Nn h hKU hf = Data.B₁ h hKU hf ⊔
      ((Data.B₁ h hKU hf ⊓ (Data.B₁ h hKU hf).map (MulAut.conj d.v).toMonoidHom).map
        (MulAut.conj d.u).toMonoidHom).map (MulAut.conj d.v).toMonoidHom := by
  have hvH : d.v ∈ d.H := h.L_le_H (Data.v_mem_L d)
  have huH : d.u ∈ d.H := h.L_le_H (Data.u_mem_L d)
  have hvN := h.v_mem_normalizer_Nn hKU hf
  have hC'N : ((Data.B₁ h hKU hf ⊓ (Data.B₁ h hKU hf).map (MulAut.conj d.v).toMonoidHom).map
        (MulAut.conj d.u).toMonoidHom).map (MulAut.conj d.v).toMonoidHom ≤ Data.Nn h hKU hf := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact (mem_normalizer_iff.1 hvN _).1 (h.B₁_le_Nn hKU hf (hBu c hc.1))
  apply le_antisymm
  ·
    set J := Data.B₁ h hKU hf ⊔
      ((Data.B₁ h hKU hf ⊓ (Data.B₁ h hKU hf).map (MulAut.conj d.v).toMonoidHom).map
        (MulAut.conj d.u).toMonoidHom).map (MulAut.conj d.v).toMonoidHom with hJ
    have hJN : J ≤ Data.Nn h hKU hf := sup_le (h.B₁_le_Nn hKU hf) hC'N
    set R : Subgroup G := (J.subgroupOf (Data.Nn h hKU hf)).map (Data.delta h hKU hf) with hR
    have hA₁R : d.A₁ ≤ R := by
      intro a ha
      obtain ⟨b, hb, hab⟩ := h.exists_mem_B₁_of_mem_A₁ hKU hf ha
      exact ⟨⟨b, h.B₁_le_Nn hKU hf hb⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hb), hab.symm⟩
    have hX₂R : d.X₂.map (MulAut.conj d.v).toMonoidHom ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← Data.X₃_map_u] at hx
      obtain ⟨x₃, hx₃, rfl⟩ := hx
      have hx₃' : x₃ ∈ d.A₁ ⊓ d.A₁.map (MulAut.conj d.v).toMonoidHom := by
        rw [Data.A₁_inf_map_v]
        exact hx₃
      obtain ⟨b₃, hb₃, hb₃e⟩ := h.exists_mem_B₁_of_mem_A₁ hKU hf hx₃'.1
      obtain ⟨a, ha, hax⟩ := hx₃'.2
      obtain ⟨b', hb', hb'e⟩ := h.exists_mem_B₁_of_mem_A₁ hKU hf ha
      have hb'N : b' ∈ Data.Nn h hKU hf := h.B₁_le_Nn hKU hf hb'
      have hvb' : d.v * b' * d.v⁻¹ ∈ Data.Nn h hKU hf := (mem_normalizer_iff.1 hvN _).1 hb'N
      have hb₃N : b₃ ∈ Data.Nn h hKU hf := h.B₁_le_Nn hKU hf hb₃
      have hb₃eq : b₃ = d.v * b' * d.v⁻¹ := by
        refine h.eq_of_delta_eq hKU hf hb₃N hvb' ?_
        rw [← hb₃e, Data.conj_delta h hvH, ← hb'e]
        show x₃ = d.v * a * d.v⁻¹
        rw [← hax]
        rfl
      have hb₃C : b₃ ∈ Data.B₁ h hKU hf ⊓ (Data.B₁ h hKU hf).map (MulAut.conj d.v).toMonoidHom :=
        ⟨hb₃, hb₃eq ▸ ⟨b', hb', rfl⟩⟩
      have hcmem : d.u * b₃ * d.u⁻¹ ∈ Data.Nn h hKU hf := h.B₁_le_Nn hKU hf (hBu b₃ hb₃)
      have hc'mem : d.v * (d.u * b₃ * d.u⁻¹) * d.v⁻¹ ∈ J :=
        Subgroup.mem_sup_right ⟨_, ⟨b₃, hb₃C, rfl⟩, rfl⟩
      refine ⟨⟨d.v * (d.u * b₃ * d.u⁻¹) * d.v⁻¹, hJN hc'mem⟩,
        Subgroup.mem_subgroupOf.2 hc'mem, ?_⟩
      rw [h.delta_eq_mul hKU hf]
      show (d.v * (d.u * b₃ * d.u⁻¹) * d.v⁻¹) *
          (d.t * (d.v * (d.u * b₃ * d.u⁻¹) * d.v⁻¹) * d.t) = _
      rw [Data.conj_delta h hvH, Data.conj_delta h huH, ← hb₃e]
      rfl
    have hrange : (Data.delta h hKU hf).range ≤ R := by
      rw [h.range_delta_eq_A₂_sup_K₂ hKU hf, Data.A₂_sup_K₂_eq]
      exact sup_le hA₁R hX₂R
    intro n hn
    have : Data.delta h hKU hf ⟨n, hn⟩ ∈ R := hrange ⟨⟨n, hn⟩, rfl⟩
    obtain ⟨j, hj, hjn⟩ := this
    have hj' : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    have hjn' : (j : G) = n := congrArg Subtype.val (h.delta_injective hKU hf hjn)
    rw [← hjn']
    exact hj'
  · exact sup_le (h.B₁_le_Nn hKU hf) hC'N

end Gen

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
