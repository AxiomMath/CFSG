module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Struct

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem pf_eq_one_of_commU (P : PiData L) {y : G} (hy : y ∈ normalizer (L : Set G))
    (hc : ∀ u ∈ blockU L, y * u = u * y) : P.pf y = 1 := by
  rw [P.pf_eq hy, P.hker ⟨y, hy⟩]
  intro u hu
  calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [hc u hu]
    _ = u := by group

namespace Two

variable {t x : G} (X : Two T M H S L t x)
include X

theorem decomp₁ {b : G} (hb : b ∈ baum S) :
    ∃ v ∈ conjR (blockU L) x, ∃ u ∈ blockU L, ∃ d ∈ s2I S L, b = v * u * d := by
  obtain ⟨v, hv, hq⟩ := X.C.exists_mem_V_mul_Q1 X.hx X.hVE hb
  obtain ⟨u, hu, d, hd, hud⟩ := X.C.Q1_decomp hq
  refine ⟨v, hv, u, hu, d, hd, ?_⟩
  calc b = v * (v⁻¹ * b) := by group
    _ = v * (u * d) := by rw [hud]
    _ = v * u * d := by group

theorem D₁_comm_V₁ {d v : G} (hd : d ∈ s2I S L) (hv : v ∈ conjR (blockU L) x) :
    v * d = d * v := Subgroup.mem_centralizer_iff.1 (X.D₁_le_C_V₁ hd) v hv

theorem D₁_comm_U₁ {d u : G} (hd : d ∈ s2I S L) (hu : u ∈ blockU L) : u * d = d * u :=
  Subgroup.mem_centralizer_iff.1 hd.2 u (X.C.D.blockU_le_L hu)

theorem U₁_inf_D₁ {m : G} (hmU : m ∈ blockU L) (hmD : m ∈ s2I S L) : m = 1 := by
  have hZ : m ∈ blockZ L := Subgroup.mem_inf.2 ⟨hmU, hmD.2⟩
  rw [blockZ_eq_bot_of_alt5 X.C.D.hL X.C.D.h5] at hZ
  exact Subgroup.mem_bot.1 hZ

theorem V₁_sq {v : G} (hv : v ∈ conjR (blockU L) x) : v * v = 1 := by
  have := (C5.isElemAbelian_two_iff.mp (X.C.V_elem x)).2 v hv
  rwa [pow_two] at this

theorem U₁_sq {u : G} (hu : u ∈ blockU L) : u * u = 1 := by
  have := (C5.isElemAbelian_two_iff.mp (isElemAbelian_blockU X.C.D.hL)).2 u hu
  rwa [pow_two] at this

theorem V₁_le_N {v : G} (hv : v ∈ conjR (blockU L) x) : v ∈ normalizer (L : Set G) :=
  X.C.V_le_N X.hx hv

theorem pf_vud {v u d : G} (hv : v ∈ conjR (blockU L) x) (hu : u ∈ blockU L) (hd : d ∈ s2I S L) :
    X.C.P.pf (v * u * d) = X.C.P.pf v := by
  have hvN := X.V₁_le_N hv
  have huN : u ∈ normalizer (L : Set G) := Subgroup.le_normalizer (X.C.D.blockU_le_L hu)
  have hdN : d ∈ normalizer (L : Set G) := X.C.hBN hd.1
  have hu1 : X.C.P.pf u = 1 :=
    pf_eq_one_of_commU X.C.P.toPiData huN fun w hw => blockU_comm_blockU X.C.D.hL hu hw
  have hd1 : X.C.P.pf d = 1 := pf_eq_one_of_commU X.C.P.toPiData hdN fun w hw => (X.D₁_comm_U₁ hd hw).symm
  rw [X.C.P.pf_mul ((normalizer (L : Set G)).mul_mem hvN huN) hdN, X.C.P.pf_mul hvN huN, hu1, hd1,
    mul_one, mul_one]

theorem sq_cond {v u d : G} (hv : v ∈ conjR (blockU L) x) (hu : u ∈ blockU L)
    (hd : d ∈ s2I S L) (h : (v * u * d) * (v * u * d) = 1) : v * u = u * v := by
  have hvN := X.V₁_le_N hv
  have hdv : d * v = v * d := (X.D₁_comm_V₁ hd hv).symm
  have hdu : d * u = u * d := (X.D₁_comm_U₁ hd hu).symm
  have hv2 := X.V₁_sq hv
  have hu2 := X.U₁_sq hu
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hm : v * u * v * u ∈ blockU L := by
    have h1 : v * u * v⁻¹ ∈ blockU L := PiData.conj_mem_U hvN hu
    rw [hvinv] at h1
    exact (blockU L).mul_mem h1 hu
  have hdd : d * d ∈ s2I S L := (s2I S L).mul_mem hd hd
  have e : (v * u * v * u) * (d * d) = 1 := by
    calc (v * u * v * u) * (d * d) = v * u * v * (u * d) * d := by group
      _ = v * u * v * (d * u) * d := by rw [hdu]
      _ = v * u * (v * d) * u * d := by group
      _ = v * u * (d * v) * u * d := by rw [hdv]
      _ = v * u * d * (v * u * d) := by group
      _ = 1 := h
  have hmD : v * u * v * u ∈ s2I S L := by
    have : v * u * v * u = (d * d)⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [this]; exact (s2I S L).inv_mem hdd
  have hm1 : v * u * v * u = 1 := X.U₁_inf_D₁ hm hmD
  have h1 : (v * u) * (v * u) = 1 := by
    calc (v * u) * (v * u) = v * u * v * u := by group
      _ = 1 := hm1
  have h2 : v * u = (v * u)⁻¹ := eq_inv_of_mul_eq_one_left h1
  calc v * u = (v * u)⁻¹ := h2
    _ = u⁻¹ * v⁻¹ := mul_inv_rev v u
    _ = u * v := by rw [huinv, hvinv]

theorem comm_cond {v v' u u' d d' : G} (hv : v ∈ conjR (blockU L) x)
    (hv' : v' ∈ conjR (blockU L) x) (hu : u ∈ blockU L) (hu' : u' ∈ blockU L)
    (hd : d ∈ s2I S L) (hd' : d' ∈ s2I S L)
    (h : (v * u * d) * (v' * u' * d') = (v' * u' * d') * (v * u * d)) :
    vact (X.C.P.pf v')⁻¹ (X.C.P.bf u) + X.C.P.bf u' =
      vact (X.C.P.pf v)⁻¹ (X.C.P.bf u') + X.C.P.bf u := by
  have hvN := X.V₁_le_N hv
  have hv'N := X.V₁_le_N hv'
  have hvv : v * v' = v' * v := X.C.V_comm hv hv'
  have hdv : d * v = v * d := (X.D₁_comm_V₁ hd hv).symm
  have hdv' : d * v' = v' * d := (X.D₁_comm_V₁ hd hv').symm
  have hdu : d * u = u * d := (X.D₁_comm_U₁ hd hu).symm
  have hdu' : d * u' = u' * d := (X.D₁_comm_U₁ hd hu').symm
  have hd'v : d' * v = v * d' := (X.D₁_comm_V₁ hd' hv).symm
  have hd'v' : d' * v' = v' * d' := (X.D₁_comm_V₁ hd' hv').symm
  have hd'u : d' * u = u * d' := (X.D₁_comm_U₁ hd' hu).symm
  have hd'u' : d' * u' = u' * d' := (X.D₁_comm_U₁ hd' hu').symm
  have hdY' : d * (v' * u') = (v' * u') * d := by
    calc d * (v' * u') = (d * v') * u' := by group
      _ = (v' * d) * u' := by rw [hdv']
      _ = v' * (d * u') := by group
      _ = v' * (u' * d) := by rw [hdu']
      _ = (v' * u') * d := by group
  have hd'Y : d' * (v * u) = (v * u) * d' := by
    calc d' * (v * u) = (d' * v) * u := by group
      _ = (v * d') * u := by rw [hd'v]
      _ = v * (d' * u) := by group
      _ = v * (u * d') := by rw [hd'u]
      _ = (v * u) * d' := by group
  have hL : (v * u * d) * (v' * u' * d') = ((v * u) * (v' * u')) * (d * d') := by
    calc (v * u * d) * (v' * u' * d') = (v * u) * (d * (v' * u')) * d' := by group
      _ = (v * u) * ((v' * u') * d) * d' := by rw [hdY']
      _ = ((v * u) * (v' * u')) * (d * d') := by group
  have hR : (v' * u' * d') * (v * u * d) = ((v' * u') * (v * u)) * (d' * d) := by
    calc (v' * u' * d') * (v * u * d) = (v' * u') * (d' * (v * u)) * d := by group
      _ = (v' * u') * ((v * u) * d') * d := by rw [hd'Y]
      _ = ((v' * u') * (v * u)) * (d' * d) := by group
  have e1 : (v * u) * (v' * u') = (v * v') * ((v'⁻¹ * u * v'⁻¹⁻¹) * u') := by group
  have e2 : (v' * u') * (v * u) = (v' * v) * ((v⁻¹ * u' * v⁻¹⁻¹) * u) := by group
  have hm1 : (v'⁻¹ * u * v'⁻¹⁻¹) * u' ∈ blockU L :=
    (blockU L).mul_mem (PiData.conj_mem_U ((normalizer (L : Set G)).inv_mem hv'N) hu) hu'
  have hm2 : (v⁻¹ * u' * v⁻¹⁻¹) * u ∈ blockU L :=
    (blockU L).mul_mem (PiData.conj_mem_U ((normalizer (L : Set G)).inv_mem hvN) hu') hu
  set m := (v'⁻¹ * u * v'⁻¹⁻¹) * u' with hmdef
  set m' := (v⁻¹ * u' * v⁻¹⁻¹) * u with hm'def
  have h3 : (v' * v) * (m * (d * d')) = (v' * v) * (m' * (d' * d)) := by
    calc (v' * v) * (m * (d * d')) = (v * v') * m * (d * d') := by rw [← hvv]; group
      _ = ((v * u) * (v' * u')) * (d * d') := by rw [e1]
      _ = (v * u * d) * (v' * u' * d') := hL.symm
      _ = (v' * u' * d') * (v * u * d) := h
      _ = ((v' * u') * (v * u)) * (d' * d) := hR
      _ = (v' * v) * m' * (d' * d) := by rw [e2]
      _ = (v' * v) * (m' * (d' * d)) := by group
  have h4 : m * (d * d') = m' * (d' * d) := mul_left_cancel h3
  have hz : m'⁻¹ * m = (d' * d) * (d * d')⁻¹ := by
    calc m'⁻¹ * m = m'⁻¹ * (m * (d * d')) * (d * d')⁻¹ := by group
      _ = m'⁻¹ * (m' * (d' * d)) * (d * d')⁻¹ := by rw [h4]
      _ = (d' * d) * (d * d')⁻¹ := by group
  have hzU : m'⁻¹ * m ∈ blockU L := (blockU L).mul_mem ((blockU L).inv_mem hm2) hm1
  have hzD : m'⁻¹ * m ∈ s2I S L := by
    rw [hz]
    exact (s2I S L).mul_mem ((s2I S L).mul_mem hd' hd) ((s2I S L).inv_mem ((s2I S L).mul_mem hd hd'))
  have hz1 : m'⁻¹ * m = 1 := X.U₁_inf_D₁ hzU hzD
  have hmm : m = m' := by
    have := hz1
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hYY : (v * u) * (v' * u') = (v' * u') * (v * u) := by
    rw [e1, e2, hvv, hmm]
  exact (X.C.P.toPiData.comm_vu hvN hv'N hu hu' hvv).1 hYY

end Two

end CFSG.QuasithinUnique.AppCS2
