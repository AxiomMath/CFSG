module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Matrix MatrixGroups Matrix.SpecialLinearGroup

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Data.R_inf_L (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    thompsonJ S ⊓ L = S ⊓ L := by
  have hN : L ⊔ thompsonJ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer dat.R_norm
  have h1 : IsSylowTwoOf (thompsonJ S ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal dat.R_sylow le_sup_left hN
  have hle : thompsonJ S ⊓ L ≤ S ⊓ L := inf_le_inf_right L (thompsonJ_le_self S)
  exact (h1.eq_of_le hle inf_le_right (h.S_isPGroup.to_le inf_le_left)).symm

theorem Lin2Data.P_le_R (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    S ⊓ L ≤ thompsonJ S := by
  rw [← dat.R_inf_L h]
  exact inf_le_left

omit [Finite G] in
theorem Lin2Data.U_le_Q (dat : Lin2Data T M H S L n) : blockU L ≤ pCoreOf 2 H := by
  rw [dat.Q_eq]
  exact le_sup_right

omit [Finite G] in
theorem Lin2Data.D₀_le_Q (dat : Lin2Data T M H S L n) : blockD S L ≤ pCoreOf 2 H := by
  rw [dat.Q_eq]
  exact le_sup_left

theorem Lin2Data.Q_le_R (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    pCoreOf 2 H ≤ thompsonJ S := by
  obtain ⟨x, hx, hxS⟩ := h.exists_mem_T_not_mem_S
  rw [dat.Q_eq, dat.R_eq x hx hxS]
  exact le_sup_left

theorem Lin2Data.D₀_le_R (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    blockD S L ≤ thompsonJ S :=
  dat.D₀_le_Q.trans (dat.Q_le_R h)

theorem Lin2Data.U_le_R (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    blockU L ≤ thompsonJ S :=
  dat.U_le_Q.trans (dat.Q_le_R h)

theorem Lin2Data.U_le_P (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    blockU L ≤ S ⊓ L :=
  le_inf ((dat.U_le_Q.trans h.Q_le_S)) (blockU_le L)

omit [Finite G] in
theorem Lin2Data.D₀_comm (dat : Lin2Data T M H S L n) {c ℓ : G} (hc : c ∈ blockD S L)
    (hℓ : ℓ ∈ L) : c * ℓ = ℓ * c := by
  rw [dat.D₀_eq] at hc
  exact (Subgroup.mem_centralizer_iff.1 hc.2 ℓ hℓ).symm

omit [Finite G] in
theorem Lin2Data.D₀_le_normalizer_of_le (dat : Lin2Data T M H S L n) {X : Subgroup G} (hX : X ≤ L) :
    blockD S L ≤ Subgroup.normalizer (X : Set G) :=
  le_normalizer_of_commute fun _ ha _ hb => (dat.D₀_comm hb (hX ha)).symm

theorem Lin2Data.Z_le_D₀ (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    blockZ L ≤ blockD S L := by
  rw [dat.D₀_eq]
  exact le_inf ((blockZ_le_blockU L).trans ((dat.U_le_P h).trans inf_le_left)) inf_le_right

theorem Lin2Data.D₀_inf_U (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    blockD S L ⊓ blockU L = blockZ L := by
  apply le_antisymm
  · intro u hu
    exact ⟨hu.2, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => (dat.D₀_comm hu.1 hℓ).symm⟩
  · exact le_inf (dat.Z_le_D₀ h) (blockZ_le_blockU L)

theorem Lin2Cfg.mem_blockU_of_central (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
    {z : G} (hzL : z ∈ L) (hz : ∀ ℓ ∈ L, z * ℓ = ℓ * z) : z ∈ blockU L := by
  obtain ⟨F, _, _, ⟨A⟩⟩ := h.coord
  have h2 : (2 : F) = 0 := two_eq_zero_of_card h.one_pos A.card_eq
  have hcentral : A.α ⟨z, hzL⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := A.α_surj g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz a a.2).symm
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcentral
  have hr : r = 1 := eq_one_of_sq_eq_one h2 (by simpa using hr2)
  have h1 : A.α ⟨z, hzL⟩ = 1 := by
    apply Subtype.ext
    rw [← hrA, hr]
    simp
  have : z ∈ pCoreOf 2 L := (A.mem_pCoreOf_iff ⟨z, hzL⟩).2 h1
  rwa [dat.pCore_eq] at this

theorem Lin2Data.P_inf_D₀ (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    (S ⊓ L) ⊓ blockD S L = blockZ L := by
  apply le_antisymm
  · intro p hp
    exact ⟨h.mem_blockU_of_central dat hp.1.2 fun ℓ hℓ => dat.D₀_comm hp.2 hℓ,
      Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => (dat.D₀_comm hp.2 hℓ).symm⟩
  · exact le_inf ((blockZ_le_blockU L).trans (dat.U_le_P h)) (dat.Z_le_D₀ h)

theorem Lin2Data.R_eq_sup (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    thompsonJ S = (S ⊓ L) ⊔ blockD S L := by
  have hPR := dat.P_le_R h
  have hDR := dat.D₀_le_R h
  have hle : (S ⊓ L) ⊔ blockD S L ≤ thompsonJ S := sup_le hPR hDR
  have hDn : blockD S L ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    dat.D₀_le_normalizer_of_le inf_le_right
  have hDnU : blockD S L ≤ Subgroup.normalizer (blockU L : Set G) :=
    dat.D₀_le_normalizer_of_le (blockU_le L)
  have hc1 := card_sup_mul_card_inf hDn
  have hc2 := card_sup_mul_card_inf hDnU
  rw [inf_comm (blockD S L) (S ⊓ L), dat.P_inf_D₀ h] at hc1
  rw [dat.D₀_inf_U h] at hc2
  have hQR : pCoreOf 2 H ≤ thompsonJ S := dat.Q_le_R h
  have hRcard : 2 ^ n * Nat.card (pCoreOf 2 H) = Nat.card (thompsonJ S) := by
    have := Subgroup.relIndex_mul_card (H := pCoreOf 2 H) (K := thompsonJ S)
    rw [inf_eq_left.mpr hQR, dat.RQ_index] at this
    exact this
  have hP := lin2_card_sylow h.lin2 (isSylowTwoOf_S_inf_L h.cs)
  rw [dat.pCore_eq] at hP
  have hU := lin2_card_U h.lin2
  have hapos : 0 < Nat.card (blockZ L) := Nat.card_pos
  have hQeq : Nat.card (pCoreOf 2 H) = Nat.card (blockD S L ⊔ blockU L : Subgroup G) := by
    rw [dat.Q_eq]
  have hsupcard : Nat.card (blockD S L ⊔ (S ⊓ L) : Subgroup G) = Nat.card (thompsonJ S) := by
    apply Nat.eq_of_mul_eq_mul_right hapos
    calc Nat.card (blockD S L ⊔ (S ⊓ L) : Subgroup G) * Nat.card (blockZ L)
        = Nat.card (blockD S L) * Nat.card (S ⊓ L : Subgroup G) := hc1
      _ = Nat.card (blockD S L) * (Nat.card (blockU L) * 2 ^ n) := by rw [hP]
      _ = 2 ^ n * (Nat.card (blockD S L) * Nat.card (blockU L)) := by ring
      _ = 2 ^ n * (Nat.card (blockD S L ⊔ blockU L : Subgroup G) * Nat.card (blockZ L)) := by
          rw [← hc2]
      _ = (2 ^ n * Nat.card (pCoreOf 2 H)) * Nat.card (blockZ L) := by rw [hQeq]; ring
      _ = Nat.card (thompsonJ S) * Nat.card (blockZ L) := by rw [hRcard]
  have hsupeq : blockD S L ⊔ (S ⊓ L) = thompsonJ S := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [sup_comm]; exact hle
    · exact hsupcard.ge
  exact hsupeq.symm.trans (sup_comm _ _)

theorem Lin2Data.R_mem_iff (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) {r : G} :
    r ∈ thompsonJ S ↔ ∃ p ∈ S ⊓ L, ∃ c ∈ blockD S L, r = p * c := by
  rw [dat.R_eq_sup h]
  exact mem_sup_iff_of_le_normalizer (dat.D₀_le_normalizer_of_le inf_le_right)

theorem Lin2Data.D₀_central (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) {c r : G}
    (hc : c ∈ blockD S L) (hr : r ∈ thompsonJ S) : c * r = r * c := by
  obtain ⟨p, hp, c', hc', rfl⟩ := (dat.R_mem_iff h).1 hr
  have h1 : c * p = p * c := dat.D₀_comm hc hp.2
  have h2 : c * c' = c' * c := IsElemAbelian.comm dat.D₀_elem hc hc'
  calc c * (p * c') = (c * p) * c' := by rw [mul_assoc]
    _ = p * (c * c') := by rw [h1, mul_assoc]
    _ = p * (c' * c) := by rw [h2]
    _ = p * c' * c := by rw [mul_assoc]

theorem Lin2Cfg.D_le_normalizer_P (h : Lin2Cfg G T M H S L n D) :
    D ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  have := h.norm
  rwa [inf_comm] at this

theorem Lin2Data.D_le_normalizer_R (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    D ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  refine le_normalizer_of_conj_mem fun d hd y hy => ?_
  obtain ⟨p, hp, c, hc, rfl⟩ := (dat.R_mem_iff h).1 hy
  have hdL : d ∈ L := h.D_le_L hd
  have hdc : d * c * d⁻¹ = c := by
    have h1 := dat.D₀_comm hc hdL
    calc d * c * d⁻¹ = (d * c) * d⁻¹ := rfl
      _ = (c * d) * d⁻¹ := by rw [h1]
      _ = c := by group
  have e : d * (p * c) * d⁻¹ = (d * p * d⁻¹) * c := by
    calc d * (p * c) * d⁻¹ = (d * p * d⁻¹) * (d * c * d⁻¹) := by group
      _ = (d * p * d⁻¹) * c := by rw [hdc]
  rw [e, dat.R_eq_sup h]
  exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.1 (h.D_le_normalizer_P hd) p).1 hp) hc

theorem Lin2Data.centralizer_R (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) {d r : G}
    (hd : d ∈ D) (hd1 : d ≠ 1) (hr : r ∈ thompsonJ S) (hc : d * r = r * d) :
    r ∈ blockD S L := by
  obtain ⟨p, hp, c, hc', rfl⟩ := (dat.R_mem_iff h).1 hr
  have hdL : d ∈ L := h.D_le_L hd
  have hcd : c * d = d * c := dat.D₀_comm hc' hdL
  have hpd : d * p = p * d := by
    have : d * p * c = p * d * c := by
      calc d * p * c = d * (p * c) := by rw [mul_assoc]
        _ = p * c * d := hc
        _ = p * (c * d) := by rw [mul_assoc]
        _ = p * (d * c) := by rw [hcd]
        _ = p * d * c := by rw [mul_assoc]
    exact mul_right_cancel this
  have h1 : d * p * d⁻¹ * p⁻¹ = 1 := by rw [hpd]; group
  have hpU : p ∈ pCoreOf 2 L := h.mem_pCore_of_comm hd hd1 hp (by rw [h1]; exact one_mem _)
  rw [dat.pCore_eq] at hpU
  have hpZ : p ∈ blockZ L :=
    h.mem_blockZ_of_comm hd hd1 hpU (by rw [h1]; exact one_mem _)
  exact Subgroup.mul_mem _ (dat.Z_le_D₀ h hpZ) hc'

end CFSG.QuasithinUnique.Lin2
