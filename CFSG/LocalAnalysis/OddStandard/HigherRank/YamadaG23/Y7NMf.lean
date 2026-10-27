module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NMe

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g : G} {P U S F M : Subgroup G}

private lemma inv_mul_inv_comm {a b : G} (h : a * b = b * a) : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← mul_inv_rev, ← mul_inv_rev, h]

private lemma conj_conjSub_eq {t g v : G} (htg : t * g = g * t) :
    g * (t * v * t⁻¹) * g⁻¹ = t * (g * v * g⁻¹) * t⁻¹ := by
  calc g * (t * v * t⁻¹) * g⁻¹ = (g * t) * v * (t⁻¹ * g⁻¹) := by group
    _ = (t * g) * v * (t⁻¹ * g⁻¹) := by rw [← htg]
    _ = (t * g) * v * (g⁻¹ * t⁻¹) := by rw [inv_mul_inv_comm htg]
    _ = t * (g * v * g⁻¹) * t⁻¹ := by group

private lemma conj_conj_of_sq {t : G} (ht2 : t * t = 1) (x : G) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  rw [htinv]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [ht2]; group

private lemma conj_conjSub_inv {t g b : G} (htg : t * g = g * t) (ht2 : t * t = 1) :
    t * (g * (t * b * t⁻¹)⁻¹ * g⁻¹) * t⁻¹ = g * b⁻¹ * g⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have hgt : g⁻¹ * t⁻¹ = t⁻¹ * g⁻¹ := inv_mul_inv_comm htg.symm
  calc t * (g * (t * b * t⁻¹)⁻¹ * g⁻¹) * t⁻¹
      = (t * g) * (t * b * t⁻¹)⁻¹ * (g⁻¹ * t⁻¹) := by group
    _ = (t * g) * (t * b⁻¹ * t⁻¹) * (g⁻¹ * t⁻¹) := by
          rw [show (t * b * t⁻¹)⁻¹ = t * b⁻¹ * t⁻¹ from by group]
    _ = (g * t) * (t * b⁻¹ * t⁻¹) * (t⁻¹ * g⁻¹) := by rw [htg, hgt]
    _ = g * b⁻¹ * g⁻¹ := by
          rw [show (g * t) * (t * b⁻¹ * t⁻¹) * (t⁻¹ * g⁻¹) =
              g * (t * t) * b⁻¹ * (t⁻¹ * t⁻¹) * g⁻¹ by group,
            ht2, show t⁻¹ * t⁻¹ = 1 from by rw [htinv, ht2]]
          group

private lemma conj_mem_of_normalizes (h : Wr7 t P U) {g : G} (htg : t * g = g * t)
    (hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U) {x : G} (hx : x ∈ P) : g * x * g⁻¹ ∈ P := by
  obtain ⟨u, hu, v', hv', hxuv⟩ := h.decomp hx
  obtain ⟨v, hv, hv'eq⟩ := (mem_conjSub_iff' t U v').mp hv'
  have hEq : g * (u * (t * v * t⁻¹)) * g⁻¹ =
      (g * u * g⁻¹) * (t * (g * v * g⁻¹) * t⁻¹) := by
    calc g * (u * (t * v * t⁻¹)) * g⁻¹
        = (g * u * g⁻¹) * (g * (t * v * t⁻¹) * g⁻¹) := by group
      _ = (g * u * g⁻¹) * (t * (g * v * g⁻¹) * t⁻¹) := by rw [conj_conjSub_eq htg]
  rw [hxuv, hv'eq, hEq]
  exact h.mul_mem' (hgU u hu)
    ((mem_conjSub_iff' t U _).mpr ⟨g * v * g⁻¹, hgU v hv, rfl⟩)

private lemma proj1_eq (h : Wr7 t P U) {x u v : G} (hu : u ∈ U) (hv : v ∈ conjSub t U)
    (hx : x = u * v) (hxP : x ∈ P) : ((h.proj1 ⟨x, hxP⟩ : ↥U) : G) = u := by
  rw [show (⟨x, hxP⟩ : ↥P) = ⟨u * v, h.mul_mem' hu hv⟩ from Subtype.ext hx]
  exact (h.proj_of_mul hu hv).1

private lemma proj2_eq (h : Wr7 t P U) {x u v : G} (hu : u ∈ U) (hv : v ∈ conjSub t U)
    (hx : x = u * v) (hxP : x ∈ P) : ((h.proj2 ⟨x, hxP⟩ : ↥(conjSub t U)) : G) = v := by
  rw [show (⟨x, hxP⟩ : ↥P) = ⟨u * v, h.mul_mem' hu hv⟩ from Subtype.ext hx]
  exact (h.proj_of_mul hu hv).2

private lemma inv_decomp (h : NtTwo t g P U S F M) {p : G} (hp : p ∈ P)
    (hp2 : (p * g) ^ 2 = 1) :
    ∃ u ∈ centEl U g, ∃ v ∈ centEl U g, p = u * (t * v * t⁻¹) := by
  obtain ⟨u, hu, v', hv', hpuv⟩ := h.wr.decomp hp
  obtain ⟨v, hv, hv'eq⟩ := (mem_conjSub_iff' t U v').mp hv'
  have hFU := y7n_fuFacts h
  have hgv' : g * v' * g⁻¹ ∈ conjSub t U :=
    (mem_conjSub_iff' t U _).mpr ⟨g * v * g⁻¹, h.gU v hv, by
      rw [hv'eq]; exact conj_conjSub_eq h.tg⟩
  have hgg : g * g = 1 := by simpa [pow_two] using h.sg.g_sq
  have hii : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hgg, inv_one]
  have hp1 : p * (g * p * g⁻¹) = 1 := by
    have h1 : (p * g) * (p * g) = 1 := by simpa [pow_two] using hp2
    calc p * (g * p * g⁻¹) = (p * g) * (p * g) * (g⁻¹ * g⁻¹) := by group
      _ = 1 := by rw [h1, hii, mul_one]
  have hconj : g * p * g⁻¹ = p⁻¹ := (inv_eq_of_mul_eq_one_right hp1).symm
  have hcomm_inv : v'⁻¹ * u⁻¹ = u⁻¹ * v'⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h.wr.direct.2.2 u hu v' hv']
  have hconj' : (g * u * g⁻¹) * (g * v' * g⁻¹) = u⁻¹ * v'⁻¹ := by
    calc (g * u * g⁻¹) * (g * v' * g⁻¹) = g * (u * v') * g⁻¹ := by group
      _ = g * p * g⁻¹ := by rw [hpuv]
      _ = p⁻¹ := hconj
      _ = (u * v')⁻¹ := by rw [← hpuv]
      _ = v'⁻¹ * u⁻¹ := by rw [mul_inv_rev]
      _ = u⁻¹ * v'⁻¹ := hcomm_inv
  obtain ⟨hu_inv, hv'_inv⟩ := h.wr.unique (h.gU u hu) (U.inv_mem hu) hgv'
    ((conjSub t U).inv_mem hv') hconj'
  have hv_eq : g * v * g⁻¹ = v⁻¹ := by
    have h1 : t * (g * v * g⁻¹) * t⁻¹ = t * v⁻¹ * t⁻¹ := by
      have hh := hv'_inv
      rw [hv'eq, conj_conjSub_eq h.tg,
        show (t * v * t⁻¹)⁻¹ = t * v⁻¹ * t⁻¹ from by group] at hh
      exact hh
    calc g * v * g⁻¹ = t⁻¹ * (t * (g * v * g⁻¹) * t⁻¹) * t := by group
      _ = t⁻¹ * (t * v⁻¹ * t⁻¹) * t := by rw [h1]
      _ = v⁻¹ := by group
  exact ⟨u, hFU.inv u hu hu_inv, v, hFU.inv v hv hv_eq, by rw [hpuv, hv'eq]⟩

private lemma fu_comp (h : NtTwo t g P U S F M) {u a : G} (hu : u ∈ centEl U g) (ha : a ∈ U)
    (heq : a * u * (g * a⁻¹ * g⁻¹) = u) : a ∈ centEl U g := by
  have hFU := y7n_fuFacts h
  have hg2 : g * g = 1 := by simpa [pow_two] using h.sg.g_sq
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left (hFU.elem.mul_self_eq_one hu)
  have hgu : g * u * g⁻¹ = u := by
    have hcu : g * u = u * g := (Subgroup.mem_centralizer_singleton_iff.mp hu.2).symm
    calc g * u * g⁻¹ = u * g * g⁻¹ := by rw [hcu]
      _ = u := by group
  have h1 : u * (g * a⁻¹ * g⁻¹) = a⁻¹ * u := by
    calc u * (g * a⁻¹ * g⁻¹) = a⁻¹ * (a * u * (g * a⁻¹ * g⁻¹)) := by group
      _ = a⁻¹ * u := by rw [heq]
  have hga_inv : g * a⁻¹ * g⁻¹ = u⁻¹ * a⁻¹ * u := by
    calc g * a⁻¹ * g⁻¹ = u⁻¹ * (u * (g * a⁻¹ * g⁻¹)) := by group
      _ = u⁻¹ * (a⁻¹ * u) := by rw [h1]
      _ = u⁻¹ * a⁻¹ * u := by group
  have hga : g * a * g⁻¹ = u⁻¹ * a * u := by
    have h2 := congrArg Inv.inv hga_inv
    rw [show (g * a⁻¹ * g⁻¹)⁻¹ = g * a * g⁻¹ from by group,
      show (u⁻¹ * a⁻¹ * u)⁻¹ = u⁻¹ * a * u from by group] at h2
    exact h2
  have hgc : g * (a * u) * g⁻¹ = u⁻¹ * a := by
    calc g * (a * u) * g⁻¹ = (g * a * g⁻¹) * (g * u * g⁻¹) := by group
      _ = (u⁻¹ * a * u) * u := by rw [hga, hgu]
      _ = u⁻¹ * a := by
            rw [show (u⁻¹ * a * u) * u = (u⁻¹ * a) * (u * u) by group,
              hFU.elem.mul_self_eq_one hu, mul_one]
  have hcent : (u * g) * (a * u) * (u * g)⁻¹ = a * u := by
    calc (u * g) * (a * u) * (u * g)⁻¹ = u * (g * (a * u) * g⁻¹) * u⁻¹ := by group
      _ = u * (u⁻¹ * a) * u⁻¹ := by rw [hgc]
      _ = (u * u⁻¹) * a * u⁻¹ := by group
      _ = a * u⁻¹ := by rw [mul_inv_cancel, one_mul]
      _ = a * u := by rw [huinv]
  obtain ⟨u', hu'U, hu'g⟩ := hFU.cls u hu
  have hc'conj : (u' * g * u'⁻¹) * (a * u) * (u' * g * u'⁻¹)⁻¹ = a * u := by
    have hh := hcent
    rw [← hu'g] at hh
    exact hh
  have hc'cent : g * (u'⁻¹ * (a * u) * u') * g⁻¹ = u'⁻¹ * (a * u) * u' := by
    have h3 := congrArg (fun z => u'⁻¹ * z * u') hc'conj
    calc g * (u'⁻¹ * (a * u) * u') * g⁻¹
        = u'⁻¹ * ((u' * g * u'⁻¹) * (a * u) * (u' * g * u'⁻¹)⁻¹) * u' := by group
      _ = u'⁻¹ * (a * u) * u' := by rw [h3]
  have hc'U : u'⁻¹ * (a * u) * u' ∈ U :=
    U.mul_mem (U.mul_mem (U.inv_mem hu'U) (U.mul_mem ha hu.1)) hu'U
  have hc'C : u'⁻¹ * (a * u) * u' ∈ centEl U g := by
    refine ⟨hc'U, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hconj : g * (u'⁻¹ * (a * u) * u') = (u'⁻¹ * (a * u) * u') * g := by
      calc g * (u'⁻¹ * (a * u) * u') = g * (u'⁻¹ * (a * u) * u') * g⁻¹ * g := by group
        _ = (u'⁻¹ * (a * u) * u') * g := by rw [hc'cent]
    exact hconj.symm
  have hcu : a * u ∈ centEl U g := by
    have h4 := hFU.normal u' hu'U (u'⁻¹ * (a * u) * u') hc'C
    rwa [show u' * (u'⁻¹ * (a * u) * u') * u'⁻¹ = a * u from by group] at h4
  have h5 : (a * u) * u⁻¹ ∈ centEl U g :=
    (centEl U g).mul_mem hcu ((centEl U g).inv_mem hu)
  rwa [show (a * u) * u⁻¹ = a from by group] at h5

theorem y7n_inv_mem_M (h : NtTwo t g P U S F M) {p : G} (hp : p ∈ P)
    (hp2 : (p * g) ^ 2 = 1) : p ∈ M := by
  obtain ⟨u, hu, v, hv, hpuv⟩ := inv_decomp h hp hp2
  have hv'mem : t * v * t⁻¹ ∈ conjSub t (centEl U g) :=
    (mem_conjSub_iff' t (centEl U g) _).mpr ⟨v, hv, rfl⟩
  rw [y7n_M_eq h, hpuv]
  exact (centEl U g ⊔ conjSub t (centEl U g)).mul_mem
    (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hv'mem)

theorem y7n_cent_le_M (h : NtTwo t g P U S F M) {p y : G} (hp : p ∈ P)
    (hp2 : (p * g) ^ 2 = 1) (hy : y ∈ P) (hc : y * (p * g) = (p * g) * y) : y ∈ M := by
  obtain ⟨u, hu, v, hv, hpuv⟩ := inv_decomp h hp hp2
  obtain ⟨a, ha, b', hb', hyab⟩ := h.wr.decomp hy
  obtain ⟨b, hb, hb'eq⟩ := (mem_conjSub_iff' t U b').mp hb'
  have ht2 : t * t = 1 := by simpa [pow_two] using h.wr.t_sq
  have hv' : t * v * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨v, hv.1, rfl⟩
  have hmemgy : g * y⁻¹ * g⁻¹ ∈ P := conj_mem_of_normalizes h.wr h.tg h.gU (P.inv_mem hy)
  have hmemw : y * p * (g * y⁻¹ * g⁻¹) ∈ P := P.mul_mem (P.mul_mem hy hp) hmemgy
  have hga_in : g * a⁻¹ * g⁻¹ ∈ U := h.gU a⁻¹ (U.inv_mem ha)
  have hgb'_conj : g * b'⁻¹ * g⁻¹ ∈ conjSub t U := by
    rw [hb'eq, show (t * b * t⁻¹)⁻¹ = t * b⁻¹ * t⁻¹ from by group, conj_conjSub_eq h.tg]
    exact (mem_conjSub_iff' t U _).mpr ⟨g * b⁻¹ * g⁻¹, h.gU b⁻¹ (U.inv_mem hb), rfl⟩
  have hyinv : y⁻¹ = a⁻¹ * b'⁻¹ := by
    rw [hyab, mul_inv_rev]
    exact (inv_mul_inv_comm (h.wr.direct.2.2 a ha b' hb')).symm
  have hGy_eq : g * y⁻¹ * g⁻¹ = (g * a⁻¹ * g⁻¹) * (g * b'⁻¹ * g⁻¹) := by
    rw [hyinv]; group
  have hwp_eq : y * p * (g * y⁻¹ * g⁻¹) = p := by
    have h1 : y * p * g = p * g * y := by simpa [mul_assoc] using hc
    calc y * p * (g * y⁻¹ * g⁻¹) = (y * p * g) * (y⁻¹ * g⁻¹) := by group
      _ = (p * g * y) * (y⁻¹ * g⁻¹) := by rw [h1]
      _ = p := by group
  have hw_eq : (⟨y * p * (g * y⁻¹ * g⁻¹), hmemw⟩ : ↥P) = ⟨p, hp⟩ := Subtype.ext hwp_eq
  have hprod : (⟨y * p * (g * y⁻¹ * g⁻¹), hmemw⟩ : ↥P) =
      (⟨y, hy⟩ : ↥P) * (⟨p, hp⟩ : ↥P) * (⟨g * y⁻¹ * g⁻¹, hmemgy⟩ : ↥P) :=
    Subtype.ext rfl
  have hY1 : ((h.wr.proj1 ⟨y, hy⟩ : ↥U) : G) = a := proj1_eq h.wr ha hb' hyab hy
  have hP1 : ((h.wr.proj1 ⟨p, hp⟩ : ↥U) : G) = u := proj1_eq h.wr hu.1 hv' hpuv hp
  have hG1 : ((h.wr.proj1 ⟨g * y⁻¹ * g⁻¹, hmemgy⟩ : ↥U) : G) = g * a⁻¹ * g⁻¹ :=
    proj1_eq h.wr hga_in hgb'_conj hGy_eq hmemgy
  have hkey1 : a * u * (g * a⁻¹ * g⁻¹) = u := by
    have hproj1w : ((h.wr.proj1 ⟨y * p * (g * y⁻¹ * g⁻¹), hmemw⟩ : ↥U) : G) =
        a * u * (g * a⁻¹ * g⁻¹) := by
      rw [hprod]
      simp only [map_mul, Subgroup.coe_mul]
      rw [hY1, hP1, hG1]
    rw [← hproj1w, hw_eq, hP1]
  have hafu : a ∈ centEl U g := fu_comp h hu ha hkey1
  have hY2 : ((h.wr.proj2 ⟨y, hy⟩ : ↥(conjSub t U)) : G) = b' := proj2_eq h.wr ha hb' hyab hy
  have hP2 : ((h.wr.proj2 ⟨p, hp⟩ : ↥(conjSub t U)) : G) = t * v * t⁻¹ :=
    proj2_eq h.wr hu.1 hv' hpuv hp
  have hG2 : ((h.wr.proj2 ⟨g * y⁻¹ * g⁻¹, hmemgy⟩ : ↥(conjSub t U)) : G) = g * b'⁻¹ * g⁻¹ :=
    proj2_eq h.wr hga_in hgb'_conj hGy_eq hmemgy
  have hbv' : b' * (t * v * t⁻¹) * (g * b'⁻¹ * g⁻¹) = t * v * t⁻¹ := by
    have hproj2w : ((h.wr.proj2 ⟨y * p * (g * y⁻¹ * g⁻¹), hmemw⟩ : ↥(conjSub t U)) : G) =
        b' * (t * v * t⁻¹) * (g * b'⁻¹ * g⁻¹) := by
      rw [hprod]
      simp only [map_mul, Subgroup.coe_mul]
      rw [hY2, hP2, hG2]
    rw [← hproj2w, hw_eq, hP2]
  have hbv : b * v * (g * b⁻¹ * g⁻¹) = v := by
    have h1 : t * (b' * (t * v * t⁻¹) * (g * b'⁻¹ * g⁻¹)) * t⁻¹ =
        b * v * (g * b⁻¹ * g⁻¹) := by
      rw [hb'eq]
      calc t * ((t * b * t⁻¹) * (t * v * t⁻¹) * (g * (t * b * t⁻¹)⁻¹ * g⁻¹)) * t⁻¹
          = (t * (t * b * t⁻¹) * t⁻¹) * (t * (t * v * t⁻¹) * t⁻¹) *
              (t * (g * (t * b * t⁻¹)⁻¹ * g⁻¹) * t⁻¹) := by group
        _ = b * v * (g * b⁻¹ * g⁻¹) := by
              rw [conj_conj_of_sq ht2 b, conj_conj_of_sq ht2 v, conj_conjSub_inv h.tg ht2]
    calc b * v * (g * b⁻¹ * g⁻¹)
        = t * (b' * (t * v * t⁻¹) * (g * b'⁻¹ * g⁻¹)) * t⁻¹ := h1.symm
      _ = t * (t * v * t⁻¹) * t⁻¹ := by rw [hbv']
      _ = v := conj_conj_of_sq ht2 v
  have hbfu : b ∈ centEl U g := fu_comp h hv hb hbv
  rw [y7n_M_eq h, hyab]
  exact (centEl U g ⊔ conjSub t (centEl U g)).mul_mem (Subgroup.mem_sup_left hafu)
    (Subgroup.mem_sup_right ((mem_conjSub_iff' t (centEl U g) _).mpr ⟨b, hbfu, hb'eq⟩))

end CFSG.OddStandard.HigherRank.YamadaG23
