module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9A

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

section Conj

variable {G : Type} [Group G]

theorem mem_conjR_iff {X : Subgroup G} {g y : G} : y ∈ conjR X g ↔ g * y * g⁻¹ ∈ X := by
  unfold conjR
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : g * ((MulAut.conj g⁻¹).toMonoidHom x) * g⁻¹ = x := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hx
  · intro h
    exact ⟨g * y * g⁻¹, h, by simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulAut.conj_apply, inv_inv]; group⟩

theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {t : G}
    (h : K.map (MulAut.conj t).toMonoidHom = K) : t ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : t * x * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h2 : t * y * t⁻¹ = t * x * t⁻¹ := hyx
    have : y = x := mul_left_cancel (mul_right_cancel h2)
    rwa [← this]

theorem map_conj_self_of_mem' {X : Subgroup G} {s : G} (hs : s ∈ X) :
    X.map (MulAut.conj s).toMonoidHom = X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact X.mul_mem (X.mul_mem hs hx) (X.inv_mem hs)
  · intro hy
    refine ⟨s⁻¹ * y * s, X.mul_mem (X.mul_mem (X.inv_mem hs) hy) hs, ?_⟩
    show s * (s⁻¹ * y * s) * s⁻¹ = y
    group

end Conj

structure U9Data {G : Type} [Group G] (T M H S L : Subgroup G) (z u : G) (A V : Subgroup G) :
    Prop where
  s7 : A5Step7 T M H S L z u
  U_comm : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a
  U_sq : ∀ a ∈ blockU L, a ^ 2 = 1
  A_eq : A = pResidualOf 2 (H ⊓ centralizerElem u)
  hA : IsA4Block A V
  V_le : V ≤ blockU L
  uz_mem : u * z ∈ V
  R_eq : ∀ x ∈ T, x ∉ S → baum S = blockU L ⊔ conjR (blockU L) x
  Tu_card : Nat.card ↥(T ⊓ centralizerElem u) = 128
  U_card : Nat.card ↥(blockU L) = 16

namespace U9Data

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V K : Subgroup G}
  (D : U9Data T M H S L z u A V)

include D

omit [Finite G] in
theorem u_ne_one : u ≠ 1 := by
  intro h
  apply D.s7.u_not
  rw [h]
  exact (centerOf (borelP M L)).one_mem

omit [Finite G] in
theorem u_sq' : u * u = 1 := by
  rw [← pow_two]
  exact D.U_sq u D.s7.u_U

omit [Finite G] in
theorem z_facts : z ≠ 1 ∧ z ^ 2 = 1 :=
  z_facts_of_card_two (by rw [← D.s7.z_gen]; exact D.s7.Z_card)

omit [Finite G] in
theorem z_sq' : z * z = 1 := by
  rw [← pow_two]
  exact D.z_facts.2

omit [Finite G] in
theorem z_mem_ZR : z ∈ centerOf (baum S) := by
  rw [D.s7.ZR_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

omit [Finite G] in
theorem u_mem_R : u ∈ baum S := D.s7.u_mem.1

omit [Finite G] in
theorem uz_comm : u * z = z * u := by
  have h := Subgroup.mem_centralizer_iff.mp D.z_mem_ZR.2 u D.u_mem_R
  exact h

omit [Finite G] in
theorem u_ne_z : u ≠ z := by
  intro h
  apply D.s7.u_not_conj 1
  simp [h]

theorem A_le_Hu : A ≤ H ⊓ centralizerElem u := by
  rw [D.A_eq, pResidualOf_eq_opResidual]
  exact opResidual_le 2 _

omit [Finite G] in
theorem V_le_A : V ≤ A := D.hA.le

theorem u_not_mem_V : u ∉ V := by
  intro huV
  obtain ⟨c, hcA, -, -, hcfp, -⟩ := D.hA.exists_c
  have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp (D.A_le_Hu hcA).2
  apply hcfp u huV D.u_ne_one
  calc c * u * c⁻¹ = u * c * c⁻¹ := by rw [hcu]
    _ = u := by group

omit [Finite G] in
theorem U_le_R : blockU L ≤ baum S := by
  obtain ⟨x, hxT, hxS, -⟩ := D.s7.x_exists
  rw [D.R_eq x hxT hxS]
  exact le_sup_left

theorem not_le_conj {t : G} (ht : t ∈ T) (htS : t ∉ S) : ¬ V ≤ conjR (blockU L) t := by
  intro hVt
  have hR := D.R_eq t ht htS
  have hUt_comm : ∀ a ∈ conjR (blockU L) t, ∀ b ∈ conjR (blockU L) t, a * b = b * a := by
    intro a ha b hb
    rw [mem_conjR_iff] at ha hb
    have h := D.U_comm _ ha _ hb
    have : t * (a * b) * t⁻¹ = t * (b * a) * t⁻¹ := by
      calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
        _ = (t * b * t⁻¹) * (t * a * t⁻¹) := h
        _ = t * (b * a) * t⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  have hVc : V ≤ centerOf (baum S) := by
    intro y hy
    have hyU : y ∈ blockU L := D.V_le hy
    have hyUt : y ∈ conjR (blockU L) t := hVt hy
    refine Subgroup.mem_inf.mpr ⟨D.U_le_R hyU, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hle : blockU L ⊔ conjR (blockU L) t ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le ?_ ?_
      · intro a ha
        exact Subgroup.mem_centralizer_singleton_iff.mpr (D.U_comm a ha y hyU)
      · intro a ha
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hUt_comm a ha y hyUt)
    rw [← hR] at hle
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hr)
  rw [D.s7.ZR_eq] at hVc
  have hcomm : Commute u z := D.uz_comm
  have hzC : z ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left hcomm n).eq
  have hnorm : Subgroup.zpowers z ≤
      Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hzC).trans (Subgroup.centralizer_le_normalizer _)
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hnorm
  have hu2 : Nat.card (Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((pow_two u).trans D.u_sq') D.u_ne_one
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((pow_two z).trans D.z_sq') D.z_facts.1
  rw [hu2, hz2] at hmul
  have hpos' : 0 < Nat.card ↥(Subgroup.zpowers z ⊓ Subgroup.zpowers u) := Nat.card_pos
  have hW : Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers z) ≤ 4 := by
    rw [sup_comm]
    have h1 := Nat.le_mul_of_pos_right (Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u)) hpos'
    omega
  have hVcard : Nat.card V = 4 := D.hA.card_U
  have hVW : V = Subgroup.zpowers u ⊔ Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hVc (by rw [hVcard]; exact hW)
  apply D.u_not_mem_V
  rw [hVW]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)

theorem mem_R_of_centralizes {t : G} (htT : t ∈ T) (htu : t ∈ centralizerElem u)
    (htV : ∀ v ∈ V, t * v = v * t) : t ∈ baum S := by
  by_contra htR
  have htS : t ∉ S := by
    intro htS
    apply htR
    rw [← D.s7.Su]
    exact ⟨htS, htu⟩
  apply D.not_le_conj htT htS
  intro v hv
  rw [mem_conjR_iff]
  have : t * v * t⁻¹ = v := by
    calc t * v * t⁻¹ = (v * t) * t⁻¹ := by rw [htV v hv]
      _ = v := by group
  rw [this]
  exact D.V_le hv

omit [Finite G] in
theorem mem_M_of_commute {y : G} (h : z * y = y * z) : y ∈ M := by
  have hy : y ∈ Subgroup.centralizer (centerOf (borelP M L) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [D.s7.z_gen] at hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (show Commute z y from h) n).eq
  rwa [← D.s7.M_cent] at hy

omit [Finite G] in
theorem Tu_comm_uz {t : G} (htT : t ∈ T) (htu : t ∈ centralizerElem u) :
    t * (u * z) * t⁻¹ = u * z := by
  have hu : t * u = u * t := Subgroup.mem_centralizer_singleton_iff.mp htu
  have hzZ : z ∈ centerOf T := D.s7.Z_le (by rw [D.s7.z_gen]; exact Subgroup.mem_zpowers z)
  have hz : t * z = z * t := Subgroup.mem_centralizer_iff.mp hzZ.2 t htT
  calc t * (u * z) * t⁻¹ = (t * u) * z * t⁻¹ := by group
    _ = (u * t) * z * t⁻¹ := by rw [hu]
    _ = u * (t * z) * t⁻¹ := by group
    _ = u * (z * t) * t⁻¹ := by rw [hz]
    _ = u * z := by group

omit [Finite G] in
theorem B_le_T {K : Subgroup G} (huzK : u * z ∈ K) :
    centralizerElem u ⊓ Subgroup.centralizer (K : Set G) ≤ T := by
  rintro b ⟨hbG, hbK⟩
  have hbu : b * u = u * b := Subgroup.mem_centralizer_singleton_iff.mp hbG
  have hba : b * (u * z) = (u * z) * b :=
    (Subgroup.mem_centralizer_iff.mp hbK (u * z) huzK).symm
  have hbz : z * b = b * z := by
    have h1 : u * (b * z) = u * (z * b) := by
      calc u * (b * z) = (u * b) * z := by group
        _ = (b * u) * z := by rw [hbu]
        _ = b * (u * z) := by group
        _ = (u * z) * b := hba
        _ = u * (z * b) := by group
    exact (mul_left_cancel h1).symm
  have hbM : b ∈ M := D.mem_M_of_commute hbz
  have : b ∈ M ⊓ centralizerElem u := ⟨hbM, hbG⟩
  rw [← D.s7.Tu_eq] at this
  exact this.1

theorem Tu_le_normalizer (hK : IsComponentIn K (centralizerElem u)) (huzK : u * z ∈ K)
    (hZK : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1) :
    T ⊓ centralizerElem u ≤ Subgroup.normalizer (K : Set G) := by
  intro t ht
  have htG : t ∈ centralizerElem u := ht.2
  have hK' : IsComponentIn (K.map (MulAut.conj t).toMonoidHom) (centralizerElem u) := by
    have := BenderBranch.isComponentIn_map (MulAut.conj t) hK
    rwa [map_conj_self_of_mem' htG] at this
  rcases BenderBranch.eq_or_commute_of_isComponentIn hK hK' with h | h
  · exact mem_normalizer_of_map_conj_eq h.symm
  · exfalso
    have haK' : u * z ∈ K.map (MulAut.conj t).toMonoidHom :=
      ⟨u * z, huzK, by simpa using D.Tu_comm_uz ht.1 htG⟩
    have hKc : K ≤ Subgroup.centralizer (K.map (MulAut.conj t).toMonoidHom : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have h1 : u * z = 1 := by
      refine hZK (u * z) huzK (fun k' hk' => ?_)
      exact Subgroup.mem_centralizer_iff.mp (hKc hk') (u * z) haK'
    apply D.u_ne_z
    have : u = z⁻¹ := by
      calc u = (u * z) * z⁻¹ := by group
        _ = z⁻¹ := by rw [h1, one_mul]
    rw [this]
    exact inv_eq_of_mul_eq_one_right D.z_sq'

end U9Data

end CFSG.QuasithinUnique.A5
