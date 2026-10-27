module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.IP
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Setting

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type*} [Group G]

theorem Hconj_top (g : G) : Hconj g (⊤ : Subgroup G) = ⊤ := by
  ext a; simp

theorem Hconj_bot (g : G) : Hconj g (⊥ : Subgroup G) = ⊥ := by
  ext a
  simp [mem_Hconj]

theorem Hconj_eq_map (g : G) (H : Subgroup G) :
    Hconj g H = H.map (MulAut.conj g⁻¹).toMonoidHom := by
  ext a
  rw [mem_Hconj, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨g * a * g⁻¹, h, ?_⟩
    show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a
    group
  · rintro ⟨y, hy, rfl⟩
    have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ H
    rw [e]
    exact hy

theorem Hconj_sup (g : G) (A B : Subgroup G) :
    Hconj g (A ⊔ B) = Hconj g A ⊔ Hconj g B := by
  rw [Hconj_eq_map, Hconj_eq_map, Hconj_eq_map, Subgroup.map_sup]

theorem hbase_conj [Finite G] {x : G} {S T P Q Rd F : Subgroup G}
    (h : HBase G x S T P Q Rd F) (g : G) :
    HBase G (g⁻¹ * x * g) (Hconj g S) (Hconj g T) (Hconj g P) (Hconj g Q) (Hconj g Rd)
      (Hconj g F) where
  simple := h.simple
  nonabelian := h.nonabelian
  x_sq := by
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [h.x_sq]; group
  x_ne_one := by
    intro hh
    apply h.x_ne_one
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [hh]; group
  S_sylow := by
    have := sylow2_conj h.S_sylow g
    rwa [Hconj_top] at this
  T_sylow := by
    have := sylow2_conj h.T_sylow g
    rwa [Hconj_centralizer] at this
  T_le_S := Hconj_le_Hconj h.T_le_S
  extremal := by
    intro s hs hsc
    rw [mem_Hconj] at hs ⊢
    apply h.extremal _ hs
    calc (g * s * g⁻¹) * x = g * (s * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * s) * g⁻¹ := by rw [hsc]
      _ = x * (g * s * g⁻¹) := by group
  rank_le := by
    intro E hE hEab
    rw [← Hconj_centralizer] at hE
    have h1 : Hconj g⁻¹ E ≤ Subgroup.centralizer ({x} : Set G) := by
      have := Hconj_le_Hconj (g := g⁻¹) hE
      rwa [Hconj_inv_Hconj] at this
    have := h.rank_le (Hconj g⁻¹ E) h1 (hEab.hconj g⁻¹)
    rwa [Hconj_card] at this
  rank_ge := by
    obtain ⟨E, hE, hEab, hE8⟩ := h.rank_ge
    refine ⟨Hconj g E, ?_, hEab.hconj g, by rw [Hconj_card]; exact hE8⟩
    rw [← Hconj_centralizer]
    exact Hconj_le_Hconj hE
  P_normal := by
    refine ⟨Hconj_le_Hconj h.P_normal.1, fun t ht n hn => ?_⟩
    rw [mem_Hconj] at ht hn ⊢
    have := h.P_normal.2 _ ht _ hn
    have e : g * (t * n * t⁻¹) * g⁻¹ = (g * t * g⁻¹) * (g * n * g⁻¹) * (g * t * g⁻¹)⁻¹ := by group
    rw [e]
    exact this
  Q_normal := by
    refine ⟨Hconj_le_Hconj h.Q_normal.1, fun t ht n hn => ?_⟩
    rw [mem_Hconj] at ht hn ⊢
    have := h.Q_normal.2 _ ht _ hn
    have e : g * (t * n * t⁻¹) * g⁻¹ = (g * t * g⁻¹) * (g * n * g⁻¹) * (g * t * g⁻¹)⁻¹ := by group
    rw [e]
    exact this
  Rd_normal := by
    refine ⟨Hconj_le_Hconj h.Rd_normal.1, fun t ht n hn => ?_⟩
    rw [mem_Hconj] at ht hn ⊢
    have := h.Rd_normal.2 _ ht _ hn
    have e : g * (t * n * t⁻¹) * g⁻¹ = (g * t * g⁻¹) * (g * n * g⁻¹) * (g * t * g⁻¹)⁻¹ := by group
    rw [e]
    exact this
  PQ_disjoint := by rw [← Hconj_inf, h.PQ_disjoint, Hconj_bot]
  PQ_comm := by
    intro p hp q hq
    rw [mem_Hconj] at hp hq
    have := h.PQ_comm _ hp _ hq
    have h2 : g * (p * q) * g⁻¹ = g * (q * p) * g⁻¹ := by
      calc g * (p * q) * g⁻¹ = (g * p * g⁻¹) * (g * q * g⁻¹) := by group
        _ = (g * q * g⁻¹) * (g * p * g⁻¹) := this
        _ = g * (q * p) * g⁻¹ := by group
    simpa using h2
  x_mem_Q := by
    rw [mem_Hconj]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact h.x_mem_Q
  R_le_Rd := by
    rw [← Hconj_sup]
    exact Hconj_le_Hconj h.R_le_Rd
  R_index_le_two := by
    rw [← Hconj_sup]
    have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
    unfold Hconj
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hsurj]
    exact h.R_index_le_two
  F_le_T := Hconj_le_Hconj h.F_le_T
  Q_le_F := Hconj_le_Hconj h.Q_le_F
  F_inf_Rd := by rw [← Hconj_inf, h.F_inf_Rd]
  nonsolv := by
    intro hsol
    apply h.nonsolv
    let ψ : ↥(Subgroup.centralizer ({x} : Set G)) →* ↥(Subgroup.centralizer ({g⁻¹ * x * g} : Set G)) :=
      { toFun := fun a => ⟨g⁻¹ * (a : G) * g, by
          rw [← Hconj_centralizer, mem_Hconj]
          have e : g * (g⁻¹ * (a : G) * g) * g⁻¹ = (a : G) := by group
          rw [e]
          exact a.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          show g⁻¹ * ((a : G) * (b : G)) * g = (g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g)
          group) }
    have hinj : Function.Injective ψ := by
      intro a b hab
      have h1 : g⁻¹ * (a : G) * g = g⁻¹ * (b : G) * g := congrArg Subtype.val hab
      exact Subtype.ext (by simpa using h1)
    exact Group.isSolvable_of_isSolvable_injective hinj

theorem ipOuter_conj {x : G} {T Rd : Subgroup G} (h : IP_outer x T Rd) (g : G) :
    IP_outer (g⁻¹ * x * g) (Hconj g T) (Hconj g Rd) := by
  intro u hu hu2 huR
  rw [mem_Hconj] at hu huR
  have hu2' : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨E, hEC, hEab, hE16⟩ := h (g * u * g⁻¹) hu hu2' huR
  refine ⟨Hconj g E, ?_, hEab.hconj g, by rw [Hconj_card]; exact hE16⟩
  rw [← Hconj_centralizer]
  exact Hconj_le_Hconj hEC

theorem ipCentFour_conj {T P Q Rd : Subgroup G} (h : IP_cent_four T P Q Rd) (g : G) :
    IP_cent_four (Hconj g T) (Hconj g P) (Hconj g Q) (Hconj g Rd) := by
  intro V hV hVf
  have hV0 : Hconj g⁻¹ V ≤ P := by
    have := Hconj_le_Hconj (g := g⁻¹) hV
    rwa [Hconj_inv_Hconj] at this
  obtain ⟨W, hWT, hWR, hWV, hWd⟩ :=
    h (Hconj g⁻¹ V) hV0 ⟨hVf.1.hconj g⁻¹, by rw [Hconj_card]; exact hVf.2⟩
  refine ⟨Hconj g W, Hconj_le_Hconj hWT, ?_, ?_, ?_⟩
  · rw [← Hconj_inf, hWR]
  · intro v hv w hw
    rw [mem_Hconj] at hw ⊢
    have hv0 : g * v * g⁻¹ ∈ Hconj g⁻¹ V := by
      rw [mem_Hconj]
      simpa [mul_assoc] using hv
    have := hWV _ hv0 _ hw
    have e : g * (v * w * v⁻¹) * g⁻¹ = (g * v * g⁻¹) * (g * w * g⁻¹) * (g * v * g⁻¹)⁻¹ := by group
    rw [e]
    exact this
  · intro d hd hdc
    rw [mem_Hconj] at hd
    have hdc0 : ∀ y ∈ Hconj g⁻¹ V, (g * d * g⁻¹) * y = y * (g * d * g⁻¹) := by
      intro y hy
      rw [mem_Hconj] at hy
      have hy' : g⁻¹ * y * g ∈ V := by simpa using hy
      have := hdc _ hy'
      calc (g * d * g⁻¹) * y = g * (d * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * d) * g⁻¹ := by rw [this]
        _ = y * (g * d * g⁻¹) := by group
    obtain ⟨v0, hv0, w0, hw0, hd0⟩ := hWd _ hd hdc0
    rw [mem_Hconj] at hv0
    refine ⟨g⁻¹ * v0 * g, by simpa using hv0, g⁻¹ * w0 * g, ?_, ?_⟩
    · rw [mem_Hconj]
      simpa [mul_assoc] using hw0
    · calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = g⁻¹ * (v0 * w0) * g := by rw [hd0]
        _ = (g⁻¹ * v0 * g) * (g⁻¹ * w0 * g) := by group

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
