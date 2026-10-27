module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Local

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G}

@[expose] def Csub (U : Subgroup G) (z : G) : Subgroup G :=
  Nsub U z ⊓ centralizer (U : Set G)

theorem mem_Csub {c : G} : c ∈ Csub U z ↔ c ∈ Nsub U z ∧ ∀ u ∈ U, c * u = u * c := by
  unfold Csub
  rw [mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u hu => (h2 u hu).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u hu => (h2 u hu).symm⟩

@[expose] def phiVal (z c : G) : G := z * (c⁻¹ * z * c)

variable (hS : Setting L z) (hD : LocalData L U T0)
  (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u)
include hS hD htrans

theorem conj_U_mem {n : G} (hn : n ∈ Nsub U z) {u : G} (hu : u ∈ U) : n * u * n⁻¹ ∈ U := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  obtain ⟨w, hw, hnw⟩ := (mem_Vsub_iff hS hUL).1 (conj_mem_V_of_N hn (U_le_V hu))
  rcases hnw with hnw | hnw
  · rw [hnw]; exact hw
  · exfalso
    obtain ⟨m, hm, hmw⟩ := htrans w hw
    have hu_conj : (n⁻¹ * m) * z * (n⁻¹ * m)⁻¹ = u := by
      have e : u = n⁻¹ * (n * u * n⁻¹) * n := by group
      rw [e, hnw, ← hmw]; group
    exact hS.not_isConj_z_of_mem (hUL hu) (hD.U_sq u hu) (isConj_iff.2 ⟨n⁻¹ * m, hu_conj⟩)

omit htrans in
theorem phiVal_mem {c : G} (hc : c ∈ Nsub U z) : phiVal z c ∈ U := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  obtain ⟨u, hu, hcu⟩ := conj_eq_mul_of_N hS hUL (inv_mem hc)
  have : phiVal z c = u := by
    unfold phiVal
    rw [inv_inv] at hcu
    rw [hcu]
    calc z * (z * u) = (z * z) * u := by group
      _ = u := by rw [hS.z_mul_self, one_mul]
  rw [this]; exact hu

omit hD htrans in
theorem conj_z_eq (c : G) : c⁻¹ * z * c = z * phiVal z c := by
  unfold phiVal
  calc c⁻¹ * z * c = (z * z) * (c⁻¹ * z * c) := by rw [hS.z_mul_self, one_mul]
    _ = z * (z * (c⁻¹ * z * c)) := by group

omit htrans in
theorem phiVal_mul {c c' : G} (hc : c ∈ Csub U z) (hc' : c' ∈ Csub U z) :
    phiVal z (c * c') = phiVal z c * phiVal z c' := by
  have hcN := (mem_Csub.1 hc).1
  have hcU := (mem_Csub.1 hc).2
  have hc'N := (mem_Csub.1 hc').1
  have hc'U := (mem_Csub.1 hc').2
  have hw := phiVal_mem hS hD hcN
  have hw' := phiVal_mem hS hD hc'N
  set w := phiVal z c with hwdef
  set w' := phiVal z c' with hw'def
  have h1 : c⁻¹ * z * c = z * w := conj_z_eq hS c
  have h2 : c'⁻¹ * w * c' = w := by
    have := hc'U w hw
    calc c'⁻¹ * w * c' = c'⁻¹ * (w * c') := by group
      _ = c'⁻¹ * (c' * w) := by rw [← this]
      _ = w := by group
  have h3 : c'⁻¹ * z * c' = z * w' := conj_z_eq hS c'
  calc phiVal z (c * c') = z * ((c * c')⁻¹ * z * (c * c')) := rfl
    _ = z * (c'⁻¹ * (c⁻¹ * z * c) * c') := by group
    _ = z * (c'⁻¹ * (z * w) * c') := by rw [h1]
    _ = z * ((c'⁻¹ * z * c') * (c'⁻¹ * w * c')) := by group
    _ = z * ((z * w') * w) := by rw [h3, h2]
    _ = (z * z) * w' * w := by group
    _ = w' * w := by rw [hS.z_mul_self, one_mul]
    _ = w * w' := hD.U_comm w' hw' w hw
    _ = phiVal z c * phiVal z c' := rfl

@[expose] noncomputable def phiHom : Csub U z →* G where
  toFun c := phiVal z c
  map_one' := by
    show z * ((1 : G)⁻¹ * z * 1) = 1
    rw [inv_one, one_mul, mul_one, hS.z_mul_self]
  map_mul' c c' := phiVal_mul hS hD c.2 c'.2

omit hD htrans in
theorem phiVal_eq_one_iff {c : G} : phiVal z c = 1 ↔ z * c = c * z := by
  unfold phiVal
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
  constructor
  · intro h
    have h1 : c⁻¹ * z * c = z := by
      have := eq_inv_of_mul_eq_one_right h
      rwa [hzi] at this
    calc z * c = c * (c⁻¹ * z * c) := by group
      _ = c * z := by rw [h1]
  · intro h
    calc z * (c⁻¹ * z * c) = z * (c⁻¹ * (z * c)) := by group
      _ = z * (c⁻¹ * (c * z)) := by rw [h]
      _ = z * z := by group
      _ = 1 := hS.z_mul_self

omit htrans in
theorem V_le_Csub : Vsub U z ≤ Csub U z := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  intro v hv
  refine mem_Csub.2 ⟨V_le_N hv, fun u hu => ?_⟩
  obtain ⟨w, hw, hvw⟩ := (mem_Vsub_iff hS hUL).1 hv
  rcases hvw with hvw | hvw
  · rw [hvw]; exact hD.U_comm w hw u hu
  · rw [hvw]
    calc z * w * u = z * (w * u) := by group
      _ = z * (u * w) := by rw [hD.U_comm w hw u hu]
      _ = (z * u) * w := by group
      _ = (u * z) * w := by rw [z_comm_U hS hUL hu]
      _ = u * (z * w) := by group

omit htrans in
theorem Csub_comm_mem_V {c : G} (hc : c ∈ Csub U z) (hcz : z * c = c * z) : c ∈ Vsub U z := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  obtain ⟨hcN, hcU⟩ := mem_Csub.1 hc
  obtain ⟨l, hl, hcl⟩ := exists_Hloc_of_mem_N_comm hS hUL hcN hcz
  have hlU : l ∈ U := by
    refine hD.selfCentralizing l (Hloc_le_L hl) (fun u hu => ?_)
    rcases hcl with hcl | hcl
    · rw [← hcl]; exact hcU u hu
    · have hlcz : l * z = z * l := (hS.z_comm l (Hloc_le_L hl)).symm
      have := hcU u hu
      rw [hcl] at this
      calc l * u = z * (z * l * u) := by
            calc l * u = (z * z) * l * u := by rw [hS.z_mul_self, one_mul]
              _ = z * (z * l * u) := by group
        _ = z * (l * z * u) := by rw [hlcz]
        _ = z * (u * (l * z)) := by rw [this]
        _ = z * (u * (z * l)) := by rw [hlcz]
        _ = (z * u) * z * l := by group
        _ = (u * z) * z * l := by rw [z_comm_U hS hUL hu]
        _ = u * (z * z) * l := by group
        _ = u * l := by rw [hS.z_mul_self]; group
  rcases hcl with hcl | hcl
  · rw [hcl]; exact U_le_V hlU
  · rw [hcl]
    have : l * z = z * l := (hS.z_comm l (Hloc_le_L hl)).symm
    rw [this]
    exact mul_mem z_mem_V (U_le_V hlU)

omit htrans in
theorem phiVal_conj {h c : G} (hh : h ∈ Hloc L U) (hc : c ∈ Csub U z) :
    h * c * h⁻¹ ∈ Csub U z ∧ phiVal z (h * c * h⁻¹) = h * phiVal z c * h⁻¹ := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  obtain ⟨hcN, hcU⟩ := mem_Csub.1 hc
  have hhN : h ∈ Nsub U z := Hloc_le_N hS hUL hh
  have hzh : z * h = h * z := hS.z_comm h (Hloc_le_L hh)
  refine ⟨mem_Csub.2 ⟨mul_mem (mul_mem hhN hcN) (inv_mem hhN), fun u hu => ?_⟩, ?_⟩
  · have hu' : h⁻¹ * u * h ∈ U := by
      have := Hloc_conj_mem (inv_mem hh) hu
      rwa [inv_inv] at this
    have := hcU _ hu'
    calc h * c * h⁻¹ * u = h * (c * (h⁻¹ * u * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * u * h) * c) * h⁻¹ := by rw [this]
      _ = u * (h * c * h⁻¹) := by group
  · have hzh' : h⁻¹ * z * h = z := by
      calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
        _ = h⁻¹ * (h * z) := by rw [hzh]
        _ = z := by group
    unfold phiVal
    calc z * ((h * c * h⁻¹)⁻¹ * z * (h * c * h⁻¹)) = z * (h * c⁻¹ * (h⁻¹ * z * h) * c * h⁻¹) := by
          group
      _ = z * (h * (c⁻¹ * z * c) * h⁻¹) := by rw [hzh']; group
      _ = (z * h) * (c⁻¹ * z * c) * h⁻¹ := by group
      _ = h * z * (c⁻¹ * z * c) * h⁻¹ := by rw [hzh]
      _ = h * (z * (c⁻¹ * z * c)) * h⁻¹ := by group

omit htrans in
theorem Csub_eq_V_or_card [Finite G] : Csub U z = Vsub U z ∨ Nat.card (Csub U z) = 2 ^ 23 := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  let φ := phiHom hS hD
  have hrangeU : φ.range ≤ U := by
    rintro _ ⟨c, rfl⟩
    exact phiVal_mem hS hD (mem_Csub.1 c.2).1
  have hinv : ∀ h ∈ Hloc L U, ∀ d ∈ φ.range, h * d * h⁻¹ ∈ φ.range := by
    rintro h hh _ ⟨c, rfl⟩
    obtain ⟨hc', hphi⟩ := phiVal_conj hS hD hh c.2
    exact ⟨⟨h * c * h⁻¹, hc'⟩, hphi⟩
  rcases hD.irred φ.range hrangeU hinv with hbot | htop
  · left
    apply le_antisymm
    · intro c hc
      have : φ ⟨c, hc⟩ = 1 := by
        have : φ ⟨c, hc⟩ ∈ φ.range := ⟨⟨c, hc⟩, rfl⟩
        rw [hbot] at this
        exact mem_bot.1 this
      have h1 : phiVal z c = 1 := this
      exact Csub_comm_mem_V hS hD hc ((phiVal_eq_one_iff hS).1 h1)
    · exact V_le_Csub hS hD
  · right
    have hker : Nat.card φ.ker = 2 ^ 12 := by
      have hk : φ.ker = (Vsub U z).subgroupOf (Csub U z) := by
        ext ⟨c, hc⟩
        rw [MonoidHom.mem_ker, mem_subgroupOf]
        constructor
        · intro h
          have h1 : phiVal z c = 1 := h
          exact Csub_comm_mem_V hS hD hc ((phiVal_eq_one_iff hS).1 h1)
        · intro hv
          have hv' : c ∈ Vsub U z := hv
          have hcz : z * c = c * z := by
            obtain ⟨w, hw, hvw⟩ := (mem_Vsub_iff hS hUL).1 hv'
            clear hv
            rcases hvw with hvw | hvw
            · rw [hvw]; exact z_comm_U hS hUL hw
            · rw [hvw]
              calc z * (z * w) = (z * z) * w := by group
                _ = w := by rw [hS.z_mul_self, one_mul]
                _ = (z * w) * z := by
                  calc w = (z * z) * w := by rw [hS.z_mul_self, one_mul]
                    _ = z * (z * w) := by group
                    _ = z * (w * z) := by rw [z_comm_U hS hUL hw]
                    _ = z * w * z := by group
          exact (phiVal_eq_one_iff hS).2 hcz
      rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (V_le_Csub hS hD)).toEquiv,
        card_Vsub hS hUL, hD.card_U]
      norm_num
    have := Subgroup.card_ker_mul_card_range φ
    rw [hker, htop, hD.card_U] at this
    rw [← this]
    norm_num

end CFSG.EvenSporadicStandard.J4Std
