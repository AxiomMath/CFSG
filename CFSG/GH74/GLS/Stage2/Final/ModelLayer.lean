module

public import CFSG.GH74.GLS.Stage2.Final.ModelOdd

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup
open scoped commutatorElement

variable {F : Type} [Field F]

theorem blkL_scalar (a : GL (Fin 2) F) (c : Fˣ)
    (hc : blkL F a = Matrix.GeneralLinearGroup.scalar (Fin 4) c) : a = 1 := by
  rw [blkL_apply, scalar4_eq] at hc
  obtain ⟨h1, h2'⟩ := diagGL_inj hc
  rw [h1, ← h2']

theorem blkR_scalar (a : GL (Fin 2) F) (c : Fˣ)
    (hc : blkR F a = Matrix.GeneralLinearGroup.scalar (Fin 4) c) : a = 1 := by
  rw [blkR_apply, scalar4_eq] at hc
  obtain ⟨h1, h2'⟩ := diagGL_inj hc
  rw [h2', ← h1]

@[expose] noncomputable def iota1 (M : ModelData F) : ↥M.H2 →* PG M :=
  blkHom M (blkL F) (fun _ ha => M.blkL_mem_K4 ha)

@[expose] noncomputable def iota2 (M : ModelData F) : ↥M.H2 →* PG M :=
  blkHom M (blkR F) (fun _ ha => M.blkR_mem_K4 ha)

theorem iota1_apply (M : ModelData F) (a : ↥M.H2) :
    iota1 M a = mkP M ⟨blkL F a, M.blkL_mem_K4 a.2⟩ := rfl

theorem iota2_apply (M : ModelData F) (a : ↥M.H2) :
    iota2 M a = mkP M ⟨blkR F a, M.blkR_mem_K4 a.2⟩ := rfl

theorem iota1_injective (M : ModelData F) : Function.Injective (iota1 M) :=
  blkHom_injective M (blkL F) (fun _ ha => M.blkL_mem_K4 ha) blkL_scalar

theorem iota2_injective (M : ModelData F) : Function.Injective (iota2 M) :=
  blkHom_injective M (blkR F) (fun _ ha => M.blkR_mem_K4 ha) blkR_scalar

noncomputable abbrev K1 (M : ModelData F) : Subgroup (PG M) := (iota1 M).range
noncomputable abbrev K2 (M : ModelData F) : Subgroup (PG M) := (iota2 M).range

abbrev Cg (M : ModelData F) : Subgroup (PG M) := Subgroup.centralizer {yP M}
abbrev C0 (M : ModelData F) : Subgroup (PG M) := (Dsub M).map (mkP M)

theorem C0_le_Cg (M : ModelData F) : C0 M ≤ Cg M := by
  show C0 M ≤ Subgroup.centralizer {yP M}
  rw [centralizer_yP]
  exact Subgroup.map_mono (Dsub_le_Nsub M)

theorem mem_Dsub_blkL (M : ModelData F) (a : ↥M.H2) :
    (⟨blkL F a, M.blkL_mem_K4 a.2⟩ : ↥M.K4) ∈ Dsub M := by
  rw [mem_Dsub]; exact Subtype.ext (ModelData.blkL_comm_yGL _)

theorem mem_Dsub_blkR (M : ModelData F) (a : ↥M.H2) :
    (⟨blkR F a, M.blkR_mem_K4 a.2⟩ : ↥M.K4) ∈ Dsub M := by
  rw [mem_Dsub]; exact Subtype.ext (ModelData.blkR_comm_yGL _)

theorem K1_le_C0 (M : ModelData F) : K1 M ≤ C0 M := by
  rintro _ ⟨a, rfl⟩
  exact ⟨_, mem_Dsub_blkL M a, rfl⟩

theorem K2_le_C0 (M : ModelData F) : K2 M ≤ C0 M := by
  rintro _ ⟨a, rfl⟩
  exact ⟨_, mem_Dsub_blkR M a, rfl⟩

theorem iota_comm (M : ModelData F) (a b : ↥M.H2) : iota1 M a * iota2 M b = iota2 M b * iota1 M a := by
  rw [iota1_apply, iota2_apply, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (blkL_mul_blkR_comm _ _)

theorem K1_K2_comm (M : ModelData F) {x y : PG M} (hx : x ∈ K1 M) (hy : y ∈ K2 M) :
    x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact iota_comm M a b

theorem C0_conj_K1 (M : ModelData F) (h2 : (2 : F) ≠ 0) {c : PG M} (hc : c ∈ C0 M) {k : PG M}
    (hk : k ∈ K1 M) : c * k * c⁻¹ ∈ K1 M := by
  obtain ⟨g, hg, rfl⟩ := hc
  obtain ⟨a, rfl⟩ := hk
  have hgc : (g : GL (Fin 4) F) * yGL F = yGL F * (g : GL (Fin 4) F) :=
    congrArg Subtype.val (mem_Dsub.1 hg)
  obtain ⟨c', hc'H, hconj⟩ := M.conj_blkL_of_comm h2 g.2 hgc a.2
  refine ⟨⟨c', hc'H⟩, ?_⟩
  have key : mkP M g * iota1 M a * (mkP M g)⁻¹ = mkP M (g * ⟨blkL F a, M.blkL_mem_K4 a.2⟩ * g⁻¹) := by
    rw [iota1_apply]
    simp only [map_mul, map_inv]
  show mkP M ⟨blkL F c', M.blkL_mem_K4 hc'H⟩ = mkP M g * iota1 M a * (mkP M g)⁻¹
  rw [key]
  congr 1
  exact Subtype.ext hconj.symm

theorem C0_conj_K2 (M : ModelData F) (h2 : (2 : F) ≠ 0) {c : PG M} (hc : c ∈ C0 M) {k : PG M}
    (hk : k ∈ K2 M) : c * k * c⁻¹ ∈ K2 M := by
  obtain ⟨g, hg, rfl⟩ := hc
  obtain ⟨a, rfl⟩ := hk
  have hgc : (g : GL (Fin 4) F) * yGL F = yGL F * (g : GL (Fin 4) F) :=
    congrArg Subtype.val (mem_Dsub.1 hg)
  obtain ⟨c', hc'H, hconj⟩ := M.conj_blkR_of_comm h2 g.2 hgc a.2
  refine ⟨⟨c', hc'H⟩, ?_⟩
  have key : mkP M g * iota2 M a * (mkP M g)⁻¹ = mkP M (g * ⟨blkR F a, M.blkR_mem_K4 a.2⟩ * g⁻¹) := by
    rw [iota2_apply]
    simp only [map_mul, map_inv]
  show mkP M ⟨blkR F c', M.blkR_mem_K4 hc'H⟩ = mkP M g * iota2 M a * (mkP M g)⁻¹
  rw [key]
  congr 1
  exact Subtype.ext hconj.symm

theorem index_C0_Cg (M : ModelData F) [Finite F] (h2 : (2 : F) ≠ 0) :
    ((C0 M).subgroupOf (Cg M)).index = 2 := by
  have h1 := Subgroup.relIndex_mul_index (C0_le_Cg M)
  rw [index_C0 M h2, show (Cg M).index = (Nsub M).index from index_C M] at h1
  have hpos : (Nsub M).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : (C0 M).relIndex (Cg M) * (Nsub M).index = 2 * (Nsub M).index := h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) this

theorem det_comm_gl2 (a a' : GL (Fin 2) F) :
    ((⁅a, a'⁆ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have h1 := ModelData.det_conj_gl2 a a'
  have h2 : ((a' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
      ((a'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.det_mul, a'.mul_inv, Matrix.det_one]
  rw [commutatorElement_def, Units.val_mul, Matrix.det_mul, h1, h2]

theorem comm_mem_E (M : ModelData F) (h2 : (2 : F) ≠ 0) {x y : PG M} (hx : x ∈ C0 M) (hy : y ∈ C0 M) :
    ⁅x, y⁆ ∈ K1 M ⊔ K2 M := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨g', hg', rfl⟩ := hy
  obtain ⟨a, b, hab, haU, hbU, -⟩ := M.exists_diagGL_of_comm h2 g.2
    (congrArg Subtype.val (mem_Dsub.1 hg))
  obtain ⟨a', b', hab', ha'U, hb'U, -⟩ := M.exists_diagGL_of_comm h2 g'.2
    (congrArg Subtype.val (mem_Dsub.1 hg'))
  have hA : ⁅a, a'⁆ ∈ M.H2 := (M.mem_H2 _).2 ⟨(M.U2.mul_mem (M.U2.mul_mem (M.U2.mul_mem haU ha'U)
    (M.U2.inv_mem haU)) (M.U2.inv_mem ha'U)), det_comm_gl2 a a'⟩
  have hB : ⁅b, b'⁆ ∈ M.H2 := (M.mem_H2 _).2 ⟨(M.U2.mul_mem (M.U2.mul_mem (M.U2.mul_mem hbU hb'U)
    (M.U2.inv_mem hbU)) (M.U2.inv_mem hb'U)), det_comm_gl2 b b'⟩
  have hprod : ⁅mkP M g, mkP M g'⁆ = iota1 M ⟨⁅a, a'⁆, hA⟩ * iota2 M ⟨⁅b, b'⁆, hB⟩ := by
    rw [iota1_apply, iota2_apply, ← map_mul, ← map_commutatorElement]
    congr 1
    apply Subtype.ext
    change ((⁅g, g'⁆ : ↥M.K4) : GL (Fin 4) F) = blkL F ⁅a, a'⁆ * blkR F ⁅b, b'⁆
    rw [← diagGL_eq_blkL_mul_blkR]
    have e1 : ((⁅g, g'⁆ : ↥M.K4) : GL (Fin 4) F) = ⁅(g : GL (Fin 4) F), (g' : GL (Fin 4) F)⁆ := rfl
    rw [e1, hab, hab']
    simp only [commutatorElement_def, diagGL_inv, diagGL_mul]
  rw [hprod]
  exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

theorem K1_le_Cg (M : ModelData F) : K1 M ≤ Cg M := (K1_le_C0 M).trans (C0_le_Cg M)
theorem K2_le_Cg (M : ModelData F) : K2 M ≤ Cg M := (K2_le_C0 M).trans (C0_le_Cg M)

theorem quasisimple_K1 (M : ModelData F) (hqs : CFSG.IsQuasisimple ↥M.H2) :
    CFSG.IsQuasisimple ↥(K1 M) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (iota1_injective M)) hqs

theorem quasisimple_K2 (M : ModelData F) (hqs : CFSG.IsQuasisimple ↥M.H2) :
    CFSG.IsQuasisimple ↥(K2 M) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (iota2_injective M)) hqs

theorem layer_map_eq [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hqs : CFSG.IsQuasisimple ↥M.H2) :
    (CFSG.layer ↥(Cg M)).map (Cg M).subtype = K1 M ⊔ K2 M := by
  have hC0n : ((C0 M).subgroupOf (Cg M)).Normal :=
    Subgroup.normal_of_index_eq_two (index_C0_Cg M h2)
  have hn1 : ((K1 M).subgroupOf (C0 M)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact C0_conj_K1 M h2 g.2 hx
  have hn2 : ((K2 M).subgroupOf (C0 M)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact C0_conj_K2 M h2 g.2 hx
  have hcomp1 := ModelGT.isComponent_subgroupOf (quasisimple_K1 M hqs) (K1_le_C0 M) (C0_le_Cg M)
    hn1 hC0n
  have hcomp2 := ModelGT.isComponent_subgroupOf (quasisimple_K2 M hqs) (K2_le_C0 M) (C0_le_Cg M)
    hn2 hC0n
  have hcomm : ⁅(C0 M).subgroupOf (Cg M), (C0 M).subgroupOf (Cg M)⁆ ≤
      (K1 M).subgroupOf (Cg M) ⊔ (K2 M).subgroupOf (Cg M) := by
    rw [← Subgroup.subgroupOf_sup (K1_le_Cg M) (K2_le_Cg M), Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf]
    exact comm_mem_E M h2 hx hy
  have hlayer := ModelGT.layer_eq_sup hcomp1 hcomp2 (index_C0_Cg M h2) hcomm
  rw [hlayer, ← Subgroup.subgroupOf_sup (K1_le_Cg M) (K2_le_Cg M),
    Subgroup.map_subgroupOf_eq_of_le (sup_le (K1_le_Cg M) (K2_le_Cg M))]

@[expose] noncomputable def iotaE (M : ModelData F) : ↥M.H2 × ↥M.H2 →* PG M :=
  (iota1 M).noncommCoprod (iota2 M) (fun a b => iota_comm M a b)

theorem iotaE_apply (M : ModelData F) (a b : ↥M.H2) : iotaE M (a, b) = iota1 M a * iota2 M b := rfl

theorem range_iotaE (M : ModelData F) : (iotaE M).range = K1 M ⊔ K2 M :=
  MonoidHom.noncommCoprod_range _ _ _

theorem mem_E_iff (M : ModelData F) {x : PG M} :
    x ∈ K1 M ⊔ K2 M ↔ ∃ a b : ↥M.H2, x = iota1 M a * iota2 M b := by
  rw [← range_iotaE]
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨(a, b), rfl⟩

theorem E_inf_R0 (M : ModelData F) (n' : ℕ) (hodd' : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) : (K1 M ⊔ K2 M) ⊓ R0 M n' hU = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxR⟩
  obtain ⟨l, rfl⟩ := hxR
  obtain ⟨a, b, hab⟩ := (mem_E_iff M).1 hxE
  rw [Subgroup.mem_bot]
  rw [theta_apply, iota1_apply, iota2_apply, ← map_mul] at hab
  obtain ⟨κ, hκ⟩ := mkP_eq_iff.1 hab
  have hu : ((thetaEl M (hU l.1 ((mem_rootsOfUnity _ _).1 l.2)) : ↥M.K4) : GL (Fin 4) F) =
      diagGL (sc2 l.1) (sc2 l.1⁻¹) := rfl
  have hv : ((⟨blkL F a, M.blkL_mem_K4 a.2⟩ * ⟨blkR F b, M.blkR_mem_K4 b.2⟩ : ↥M.K4) :
      GL (Fin 4) F) = diagGL (a : GL (Fin 2) F) (b : GL (Fin 2) F) := by
    change blkL F a * blkR F b = _
    rw [← diagGL_eq_blkL_mul_blkR]
  rw [hu, hv, diagGL_inv, diagGL_mul, scalar4_eq] at hκ
  obtain ⟨h1, h2⟩ := diagGL_inj hκ
  rw [← sc2_inv, inv_inv] at h2
  have ha : (a : GL (Fin 2) F) = sc2 (l.1 * κ) := by
    rw [← sc2_mul, ← h1]; group
  have hb : (b : GL (Fin 2) F) = sc2 (l.1⁻¹ * κ) := by
    calc (b : GL (Fin 2) F) = (sc2 l.1)⁻¹ * (sc2 l.1 * b) := by group
      _ = (sc2 l.1)⁻¹ * sc2 κ := by rw [h2]
      _ = sc2 (l.1⁻¹ * κ) := by rw [sc2_inv, sc2_mul]
  have hda : ((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := ((M.mem_H2 _).1 a.2).2
  have hdb : ((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := ((M.mem_H2 _).1 b.2).2
  rw [ha, det_sc2] at hda
  rw [hb, det_sc2] at hdb
  have hl0 : ((l.1 : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hκ0 : ((κ : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hl4 : l.1 ^ 4 = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_one] at hda hdb ⊢
    field_simp at hdb
    linear_combination hda - (↑l.1 : F) ^ 2 * hdb
  have hln : l.1 ^ n' = 1 := (mem_rootsOfUnity _ _).1 l.2
  have hord : orderOf l.1 = 1 := by
    have h4 : orderOf l.1 ∣ 4 := orderOf_dvd_of_pow_eq_one hl4
    have hn : orderOf l.1 ∣ n' := orderOf_dvd_of_pow_eq_one hln
    have hcop : Nat.Coprime 4 n' := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd')
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h4 hcop) hn
  have hl1 : l.1 = 1 := orderOf_eq_one_iff.1 hord
  have : l = 1 := Subtype.ext hl1
  rw [this, map_one]

theorem sylow_subgroupOf {G : Type*} [Group G] [Finite G] (C : Subgroup G) (hodd : Odd C.index)
    (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ C) :
    ∃ S₂ : Sylow 2 ↥C, (S₂ : Subgroup ↥C) = (S : Subgroup G).subgroupOf C := by
  have h1 : Nat.card ((S : Subgroup G).subgroupOf C) = 2 ^ (Nat.card C).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv, Sylow.card_eq_multiplicity]
    congr 1
    have hG : C.index * Nat.card C = Nat.card G := Subgroup.index_mul_card C
    rw [← hG, Nat.factorization_mul (Subgroup.index_ne_zero_of_finite) Nat.card_pos.ne']
    have : C.index.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.2 hodd |> fun h => by
        rw [even_iff_two_dvd] at h; exact h)
    simp [this]
  exact ⟨Sylow.ofCard _ h1, Sylow.coe_ofCard _ _⟩

theorem layerSylow_inf_R0 [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0) (n' : ℕ) (hodd' : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) (hqs : CFSG.IsQuasisimple ↥M.H2)
    (hdvd : n' ∣ Nat.card F - 1) {S : Subgroup (PG M)} (hS : IsPGroup 2 ↥S) (hSC : S ≤ Cg M) :
    (K1 M ⊔ K2 M ⊔ S) ⊓ R0 M n' hU = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxES, hxR⟩
  have hR0C : R0 M n' hU ≤ Cg M := (R0_le_C M n' hU).trans (C0_le_Cg M)
  have hxC : x ∈ Cg M := hR0C hxR
  have hE : (CFSG.layer ↥(Cg M)) = (K1 M ⊔ K2 M).subgroupOf (Cg M) := by
    rw [← layer_map_eq M h2 hqs]
    exact (Subgroup.comap_map_eq_self_of_injective (Cg M).subtype_injective _).symm
  have hch : (CFSG.layer ↥(Cg M)).Characteristic := CFSG.LocalCores.layer_characteristic
  have hEn : ((K1 M ⊔ K2 M).subgroupOf (Cg M)).Normal := by
    rw [← hE]; infer_instance
  have hSp : IsPGroup 2 ↥(S.subgroupOf (Cg M)) :=
    hS.of_injective (Subgroup.subgroupOfEquivOfLe hSC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSC).injective
  have hEC : K1 M ⊔ K2 M ≤ Cg M := sup_le (K1_le_Cg M) (K2_le_Cg M)
  have hmem : (⟨x, hxC⟩ : ↥(Cg M)) ∈ (K1 M ⊔ K2 M).subgroupOf (Cg M) ⊔ S.subgroupOf (Cg M) := by
    rw [← Subgroup.subgroupOf_sup hEC hSC, Subgroup.mem_subgroupOf]
    exact hxES
  have hxodd : Odd (orderOf (⟨x, hxC⟩ : ↥(Cg M))) := by
    have h1 : orderOf (⟨x, hxR⟩ : ↥(R0 M n' hU)) ∣ Nat.card ↥(R0 M n' hU) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, card_R0 M n' hodd' hU hdvd] at h1
    rw [Subgroup.orderOf_mk]
    exact Odd.of_dvd_nat hodd' h1
  have hxE' := ModelGT.mem_of_odd_orderOf_sup hSp hmem hxodd
  rw [Subgroup.mem_subgroupOf] at hxE'
  have : x ∈ (K1 M ⊔ K2 M) ⊓ R0 M n' hU := ⟨hxE', hxR⟩
  rw [E_inf_R0 M n' hodd' hU] at this
  exact this

theorem pow_decomp (M : ModelData F) {n s n' : ℕ} (hn : n = 2 ^ s * n') (hodd' : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2)
    (hdet : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1)
    {a b : GL (Fin 2) F} (ha : a ∈ M.U2) (hb : b ∈ M.U2)
    (hab : (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det = 1) :
    ∃ (u : Fˣ) (_ : u ^ n' = 1) (a'' b'' : GL (Fin 2) F), a'' ∈ M.H2 ∧ b'' ∈ M.H2 ∧
      a ^ (2 ^ s) = sc2 u * a'' ∧ b ^ (2 ^ s) = (sc2 u)⁻¹ * b'' := by
  set δ : Fˣ := Matrix.GeneralLinearGroup.det a with hδdef
  have hδ : (δ : F) = (a : Matrix (Fin 2) (Fin 2) F).det := rfl
  have hδn : δ ^ n = 1 := Units.ext (by
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [hδ]; exact hdet a ha)
  set l₁ : Fˣ := δ ^ (2 ^ s) with hl₁
  have hl₁n : l₁ ^ n' = 1 := by rw [hl₁, ← pow_mul, ← hn]; exact hδn
  obtain ⟨m, hm⟩ := hodd'
  set u : Fˣ := l₁ ^ (m + 1) with hu
  have hun : u ^ n' = 1 := by
    rw [hu, ← pow_mul, mul_comm, pow_mul, hl₁n, one_pow]
  have huu : u * u = l₁ := by
    rw [hu, ← pow_add]
    have : (m + 1) + (m + 1) = n' + 1 := by omega
    rw [this, pow_succ, hl₁n, one_mul]
  have hsc : sc2 u ∈ M.U2 := hU u hun
  have hdetU : ((sc2 u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (u : F) ^ 2 := det_sc2 u
  have hu2 : (u : F) ^ 2 = (δ : F) ^ (2 ^ s) := by
    have := congrArg (fun x : Fˣ => (x : F)) huu
    simp only [Units.val_mul, hl₁, Units.val_pow_eq_pow_val] at this
    rw [sq]; exact this
  have hδ0 : (δ : F) ≠ 0 := Units.ne_zero _
  have hu0 : (u : F) ≠ 0 := Units.ne_zero _
  have hbδ : (b : Matrix (Fin 2) (Fin 2) F).det = (δ : F)⁻¹ := by
    rw [hδ]; exact eq_inv_of_mul_eq_one_right hab
  refine ⟨u, hun, (sc2 u)⁻¹ * a ^ (2 ^ s), sc2 u * b ^ (2 ^ s), ?_, ?_, by group, by group⟩
  · refine (M.mem_H2 _).2 ⟨M.U2.mul_mem (M.U2.inv_mem hsc) (M.U2.pow_mem ha _), ?_⟩
    have ha2 : ((a ^ 2 ^ s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (a : Matrix (Fin 2) (Fin 2) F) ^ 2 ^ s := Units.val_pow_eq_pow_val _ _
    rw [Units.val_mul, Matrix.det_mul, sc2_inv, det_sc2, ha2, Matrix.det_pow,
      ← hδ, ← hu2, Units.val_inv_eq_inv_val]
    field_simp
  · refine (M.mem_H2 _).2 ⟨M.U2.mul_mem hsc (M.U2.pow_mem hb _), ?_⟩
    have hb2 : ((b ^ 2 ^ s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (b : Matrix (Fin 2) (Fin 2) F) ^ 2 ^ s := Units.val_pow_eq_pow_val _ _
    rw [Units.val_mul, Matrix.det_mul, det_sc2, hb2, Matrix.det_pow, hbδ, inv_pow, ← hu2]
    field_simp

theorem pow_mem_ER [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0) {n s n' : ℕ}
    (hn : n = 2 ^ s * n') (hs : 1 ≤ s) (hodd' : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2)
    (hdet : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1)
    {c : PG M} (hc : c ∈ Cg M) : c ^ (2 ^ s) ∈ (K1 M ⊔ K2 M) ⊔ R0 M n' hU := by
  have hcN : c ∈ (Nsub M).map (mkP M) := by
    have := hc; rw [Cg, centralizer_yP] at this; exact this
  obtain ⟨g, hgN, rfl⟩ := hcN
  rcases (mem_Nsub_iff_D M).1 hgN with hD | hD
  · obtain ⟨a, b, hab, haU, hbU, hdetab⟩ := M.exists_diagGL_of_comm h2 g.2
      (congrArg Subtype.val (mem_Dsub.1 hD))
    obtain ⟨u, hu, a'', b'', ha'', hb'', hpa, hpb⟩ := pow_decomp M hn hodd' hU hdet haU hbU hdetab
    have hsc : sc2 u ∈ M.U2 := hU u hu
    have key : g ^ (2 ^ s) = thetaEl M hsc * ⟨blkL F a'', M.blkL_mem_K4 ha''⟩ *
        ⟨blkR F b'', M.blkR_mem_K4 hb''⟩ := by
      apply Subtype.ext
      change ((g : GL (Fin 4) F)) ^ (2 ^ s) = diagGL (sc2 u) (sc2 u⁻¹) * blkL F a'' * blkR F b''
      rw [hab, diagGL_pow, hpa, hpb, mul_assoc, ← diagGL_eq_blkL_mul_blkR, diagGL_mul, sc2_inv]
    rw [← map_pow, key, map_mul, map_mul]
    have h1 : mkP M (thetaEl M hsc) ∈ R0 M n' hU := ⟨⟨u, (mem_rootsOfUnity _ _).2 hu⟩, rfl⟩
    have h2' : mkP M ⟨blkL F a'', M.blkL_mem_K4 ha''⟩ ∈ K1 M := ⟨⟨a'', ha''⟩, rfl⟩
    have h3 : mkP M ⟨blkR F b'', M.blkR_mem_K4 hb''⟩ ∈ K2 M := ⟨⟨b'', hb''⟩, rfl⟩
    have hle1 : R0 M n' hU ≤ (K1 M ⊔ K2 M) ⊔ R0 M n' hU := le_sup_right
    have hle2 : K1 M ≤ (K1 M ⊔ K2 M) ⊔ R0 M n' hU := le_sup_left.trans' le_sup_left
    have hle3 : K2 M ≤ (K1 M ⊔ K2 M) ⊔ R0 M n' hU := le_sup_left.trans' le_sup_right
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hle1 h1) (hle2 h2')) (hle3 h3)
  · obtain ⟨a, b, hab, haU, hbU, hdetab⟩ := M.exists_diagGL_of_comm h2 (M.wK * g).2
      (congrArg Subtype.val (mem_Dsub.1 hD))
    have hg' : (g : GL (Fin 4) F) = swapGL F * diagGL a b := by
      have h1 : ((M.wK * g : ↥M.K4) : GL (Fin 4) F) = swapGL F * (g : GL (Fin 4) F) := rfl
      rw [h1] at hab
      calc (g : GL (Fin 4) F) = swapGL F * (swapGL F * (g : GL (Fin 4) F)) := by
            rw [← mul_assoc, swapGL_mul_self, one_mul]
        _ = swapGL F * diagGL a b := by rw [hab]
    have hba : b * a ∈ M.H2 := (M.mem_H2 _).2 ⟨M.U2.mul_mem hbU haU, by
      rw [Units.val_mul, Matrix.det_mul, mul_comm]; exact hdetab⟩
    have hab' : a * b ∈ M.H2 := (M.mem_H2 _).2 ⟨M.U2.mul_mem haU hbU, by
      rw [Units.val_mul, Matrix.det_mul]; exact hdetab⟩
    have key : g * g = ⟨blkL F (b * a), M.blkL_mem_K4 hba⟩ *
        ⟨blkR F (a * b), M.blkR_mem_K4 hab'⟩ := by
      apply Subtype.ext
      change (g : GL (Fin 4) F) * (g : GL (Fin 4) F) = blkL F (b * a) * blkR F (a * b)
      rw [hg', ← diagGL_eq_blkL_mul_blkR]
      calc swapGL F * diagGL a b * (swapGL F * diagGL a b)
          = (swapGL F * diagGL a b * swapGL F) * diagGL a b := by group
        _ = diagGL b a * diagGL a b := by rw [swapGL_mul_diagGL_mul_swapGL]
        _ = diagGL (b * a) (a * b) := by rw [diagGL_mul]
    have hE : mkP M (g * g) ∈ K1 M ⊔ K2 M := by
      rw [key, map_mul]
      exact Subgroup.mul_mem_sup ⟨⟨b * a, hba⟩, rfl⟩ ⟨⟨a * b, hab'⟩, rfl⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hpw : mkP M g ^ (2 ^ (s' + 1)) = (mkP M (g * g)) ^ (2 ^ s') := by
      rw [map_mul, ← sq, ← pow_mul, pow_succ']
    rw [hpw]
    exact Subgroup.pow_mem _ ((le_sup_left : K1 M ⊔ K2 M ≤ (K1 M ⊔ K2 M) ⊔ R0 M n' hU) hE) _

theorem R0_le_Cg (M : ModelData F) (n' : ℕ) (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) :
    R0 M n' hU ≤ Cg M := (R0_le_C M n' hU).trans (C0_le_Cg M)

theorem R0_normal_Cg (M : ModelData F) (h2 : (2 : F) ≠ 0) (n' : ℕ)
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) : ((R0 M n' hU).subgroupOf (Cg M)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact R0_normalized M h2 n' hU g.2 hx

theorem layer_normal_Cg [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hqs : CFSG.IsQuasisimple ↥M.H2) : ((K1 M ⊔ K2 M).subgroupOf (Cg M)).Normal := by
  have hE : (CFSG.layer ↥(Cg M)) = (K1 M ⊔ K2 M).subgroupOf (Cg M) := by
    rw [← layer_map_eq M h2 hqs]
    exact (Subgroup.comap_map_eq_self_of_injective (Cg M).subtype_injective _).symm
  have hch : (CFSG.layer ↥(Cg M)).Characteristic := CFSG.LocalCores.layer_characteristic
  rw [← hE]; infer_instance

theorem sup_E_R0_eq [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0) {n s n' : ℕ}
    (hn : n = 2 ^ s * n') (hs : 1 ≤ s) (hodd' : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2)
    (hdet : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1)
    (hodd : Odd (Nsub M).index) (hqs : CFSG.IsQuasisimple ↥M.H2) (S : Sylow 2 (PG M))
    (hSC : (S : Subgroup (PG M)) ≤ Cg M) :
    (S : Subgroup (PG M)) ⊔ (K1 M ⊔ K2 M ⊔ R0 M n' hU) = Cg M := by
  have hEC : K1 M ⊔ K2 M ≤ Cg M := sup_le (K1_le_Cg M) (K2_le_Cg M)
  have hRC : R0 M n' hU ≤ Cg M := R0_le_Cg M n' hU
  have hEn := layer_normal_Cg M h2 hqs
  have hRn := R0_normal_Cg M h2 n' hU
  have hNn : (((K1 M ⊔ K2 M) ⊔ R0 M n' hU).subgroupOf (Cg M)).Normal := by
    rw [Subgroup.subgroupOf_sup hEC hRC]
    exact Subgroup.sup_normal _ _
  have hCi : (Cg M).index = (Nsub M).index := index_C M
  obtain ⟨S₂, hS₂⟩ := sylow_subgroupOf (Cg M) (by rw [hCi]; exact hodd) S hSC
  have hquot : IsPGroup 2 (↥(Cg M) ⧸ ((K1 M ⊔ K2 M) ⊔ R0 M n' hU).subgroupOf (Cg M)) := by
    intro q
    induction q using QuotientGroup.induction_on with | H c => ?_
    refine ⟨s, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact pow_mem_ER M h2 hn hs hodd' hU hdet c.2
  have htop := ModelGT.sup_eq_top_of_isPGroup_quotient S₂ _ hquot
  rw [hS₂] at htop
  have := congrArg (Subgroup.map (Cg M).subtype) htop
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSC,
    Subgroup.map_subgroupOf_eq_of_le (sup_le hEC hRC), Subgroup.map_top, Subgroup.range_subtype] at this
  exact this

theorem map_mk'_eq_top_of_sup {G : Type*} [Group G] (X N : Subgroup G) [N.Normal]
    (h : X ⊔ N = ⊤) : X.map (QuotientGroup.mk' N) = ⊤ := by
  have := congrArg (Subgroup.map (QuotientGroup.mk' N)) h
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq, ← MonoidHom.range_eq_map,
    QuotientGroup.range_mk'] at this
  exact this

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices in
theorem closure_two_elements_H2 [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hqs : CFSG.IsQuasisimple ↥M.H2) {a b : F} (hab : a ^ 2 + b ^ 2 = -1)
    (hH : ∀ g, rhoQ hab g ∈ M.H2) :
    Subgroup.closure {y : ↥M.H2 | ∃ k : ℕ, y ^ (2 ^ k) = 1} = ⊤ := by
  have hord : (⟨rhoQ hab (QuaternionGroup.a 1), hH _⟩ : ↥M.H2) ^ (2 ^ 2) = 1 := by
    apply Subtype.ext
    change (rhoQ hab (QuaternionGroup.a 1)) ^ (2 ^ 2) = 1
    rw [← map_pow]
    have : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ (2 ^ 2) = 1 := by decide
    rw [this, map_one]
  refine ModelGT.closure_two_elements_eq_top hqs _ ⟨2, hord⟩ ?_
  intro hc
  have hcomm := Subgroup.mem_center_iff.1 hc ⟨rhoQ hab (QuaternionGroup.xa 0), hH _⟩
  have hcomm' := congrArg (fun u : ↥M.H2 => ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hcomm
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rhoQ_a_one, coe_rhoQ_xa_zero] at hcomm'
  have h1 := quatI_mul_quatJ_eq_neg (K := F) a b
  rw [hcomm'] at h1
  have h3 : quatI F * quatJ a b = 0 := by
    have h4 : (2 : F) • (quatI F * quatJ a b) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h1]
      exact neg_add_cancel _
    exact (smul_eq_zero.1 h4).resolve_left h2
  have h5 := congrFun₂ h3 0 0
  have h6 := congrFun₂ h3 0 1
  simp [quatI_mul_quatJ] at h5 h6
  have : a ^ 2 + b ^ 2 = 0 := by rw [h5, h6]; ring
  rw [hab] at this
  exact one_ne_zero (neg_eq_zero.1 this)

section LayerBar

open CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem layerBar_generic [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0) {n s n' : ℕ}
    (hn : n = 2 ^ s * n') (hs : 1 ≤ s) (hodd' : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2)
    (hdet : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1)
    (hodd : Odd (Nsub M).index) (hqs : CFSG.IsQuasisimple ↥M.H2) {a b : F}
    (hab : a ^ 2 + b ^ 2 = -1) (hH : ∀ g, rhoQ hab g ∈ M.H2) (hdvd : n' ∣ Nat.card F - 1)
    (hR : CFSG.pPrimeCore 2 ↥(Cg M) = (R0 M n' hU).subgroupOf (Cg M))
    (S : Sylow 2 (PG M)) (hSC : (S : Subgroup (PG M)) ≤ Cg M) :
    layerTimesSylow (yP M) (S : Subgroup (PG M)) ⊓ OddCore (yP M) = ⊥ ∧
      barOf (yP M) (layerTimesSylow (yP M) (S : Subgroup (PG M))) =
        oPrimeResidual 2 (CentralizerBar (yP M)) := by
  have hEC : K1 M ⊔ K2 M ≤ Cg M := sup_le (K1_le_Cg M) (K2_le_Cg M)
  have hRC : R0 M n' hU ≤ Cg M := R0_le_Cg M n' hU
  have hF1 : (CFSG.layer ↥(Cg M)).map (Cg M).subtype = K1 M ⊔ K2 M := layer_map_eq M h2 hqs
  have hL : layerTimesSylow (yP M) (S : Subgroup (PG M)) = (K1 M ⊔ K2 M) ⊔ S := by
    unfold layerTimesSylow
    rw [show Subgroup.centralizer ({yP M} : Set (PG M)) = Cg M from rfl]
    rw [hF1]
  have hOdd : OddCore (yP M) = R0 M n' hU := by
    unfold OddCore pPrimeCoreOf
    show (CFSG.pPrimeCore 2 ↥(Cg M)).map (Cg M).subtype = _
    rw [hR, Subgroup.map_subgroupOf_eq_of_le hRC]
  have hSp : IsPGroup 2 ↥(S : Subgroup (PG M)) := S.isPGroup'
  refine ⟨?_, ?_⟩
  · rw [hL, hOdd]
    exact layerSylow_inf_R0 M h2 n' hodd' hU hqs hdvd hSp hSC
  · have hsup := sup_E_R0_eq M h2 hn hs hodd' hU hdet hodd hqs S hSC
    have hLC : (K1 M ⊔ K2 M) ⊔ (S : Subgroup (PG M)) ≤ Cg M := sup_le hEC hSC
    have hLR : (((K1 M ⊔ K2 M) ⊔ S).subgroupOf (Cg M)) ⊔ CFSG.pPrimeCore 2 ↥(Cg M) = ⊤ := by
      rw [hR, ← Subgroup.subgroupOf_sup hLC hRC]
      have : ((K1 M ⊔ K2 M) ⊔ (S : Subgroup (PG M))) ⊔ R0 M n' hU = Cg M := by
        rw [← hsup]
        ac_rfl
      rw [this]
      exact Subgroup.subgroupOf_self _
    have hbar : barOf (yP M) (layerTimesSylow (yP M) (S : Subgroup (PG M))) = ⊤ := by
      unfold barOf toBar
      rw [hL]
      exact map_mk'_eq_top_of_sup _ _ hLR
    have hres : oPrimeResidual 2 (CentralizerBar (yP M)) = ⊤ := by
      set A : Subgroup (CentralizerBar (yP M)) := oPrimeResidual 2 (CentralizerBar (yP M)) with hA
      have hgen : ∀ y : CentralizerBar (yP M), (∃ k : ℕ, y ^ (2 ^ k) = 1) → y ∈ A :=
        fun y hy => Subgroup.subset_closure hy
      let mk : ↥(Cg M) →* CentralizerBar (yP M) :=
        QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cg M))
      have hblk : ∀ (ι : ↥M.H2 →* PG M) (hι : ∀ h, ι h ∈ Cg M) (h : ↥M.H2),
          mk ⟨ι h, hι h⟩ ∈ A := by
        intro ι hι h
        let κ : ↥M.H2 →* CentralizerBar (yP M) := mk.comp (ι.codRestrict (Cg M) hι)
        have hle : Subgroup.closure {y : ↥M.H2 | ∃ k : ℕ, y ^ (2 ^ k) = 1} ≤ A.comap κ := by
          refine (Subgroup.closure_le _).2 (fun y hy => ?_)
          obtain ⟨k, hk⟩ := hy
          exact hgen _ ⟨k, by rw [← map_pow, hk, map_one]⟩
        rw [closure_two_elements_H2 M h2 hqs hab hH] at hle
        exact hle (Subgroup.mem_top h)
      have hK1 : ∀ y : ↥(Cg M), (y : PG M) ∈ K1 M → mk y ∈ A := by
        intro y hy
        obtain ⟨h, hh⟩ := hy
        have : y = ⟨iota1 M h, K1_le_Cg M ⟨h, rfl⟩⟩ := Subtype.ext hh.symm
        rw [this]
        exact hblk (iota1 M) (fun h => K1_le_Cg M ⟨h, rfl⟩) h
      have hK2 : ∀ y : ↥(Cg M), (y : PG M) ∈ K2 M → mk y ∈ A := by
        intro y hy
        obtain ⟨h, hh⟩ := hy
        have : y = ⟨iota2 M h, K2_le_Cg M ⟨h, rfl⟩⟩ := Subtype.ext hh.symm
        rw [this]
        exact hblk (iota2 M) (fun h => K2_le_Cg M ⟨h, rfl⟩) h
      have hS' : ∀ y : ↥(Cg M), (y : PG M) ∈ (S : Subgroup (PG M)) → mk y ∈ A := by
        intro y hy
        obtain ⟨k, hk⟩ := hSp ⟨y, hy⟩
        refine hgen _ ⟨k, ?_⟩
        rw [← map_pow]
        have : y ^ (2 ^ k) = 1 := by
          apply Subtype.ext
          have := congrArg Subtype.val hk
          simpa using this
        rw [this, map_one]
      have hLmem : ∀ l ∈ ((K1 M ⊔ K2 M) ⊔ (S : Subgroup (PG M))).subgroupOf (Cg M), mk l ∈ A := by
        intro l hl
        have hle : ((K1 M ⊔ K2 M) ⊔ (S : Subgroup (PG M))).subgroupOf (Cg M) ≤ A.comap mk := by
          rw [Subgroup.subgroupOf_sup hEC hSC, Subgroup.subgroupOf_sup (K1_le_Cg M) (K2_le_Cg M)]
          exact sup_le (sup_le (fun y hy => hK1 y hy) (fun y hy => hK2 y hy))
            (fun y hy => hS' y hy)
        exact hle hl
      rw [eq_top_iff]
      intro q _
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
      have hc : c ∈ (↑(((K1 M ⊔ K2 M) ⊔ (S : Subgroup (PG M))).subgroupOf (Cg M) ⊔
          CFSG.pPrimeCore 2 ↥(Cg M)) : Set ↥(Cg M)) := by rw [hLR]; trivial
      rw [Subgroup.mul_normal] at hc
      obtain ⟨l, hl, r, hr, rfl⟩ := Set.mem_mul.1 hc
      have hmk : (QuotientGroup.mk (l * r) : CentralizerBar (yP M)) = mk l := by
        have hr1 : QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cg M)) r = 1 :=
          (QuotientGroup.eq_one_iff r).2 hr
        show QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cg M)) (l * r) = mk l
        rw [map_mul, hr1, mul_one]
      rw [hmk]
      exact hLmem l hl
    rw [hbar, hres]

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg in
theorem det_uni_pow {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) {a : GL (Fin 2) F} (ha : a ∈ (ModelData.uni hF).U2) :
    ((a : Matrix (Fin 2) (Fin 2) F).det) ^ (p ^ f + 1) = 1 := by
  have h : conjTr (unitaryInvolution F p f) (a : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) = 1 := ha
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hc : (conjTr (unitaryInvolution F p f) (a : Matrix (Fin 2) (Fin 2) F)).det =
      (unitaryInvolution F p f) ((a : Matrix (Fin 2) (Fin 2) F).det) := by
    simp only [conjTr]
    rw [Matrix.det_transpose]
    exact (RingHom.map_det ((unitaryInvolution F p f : F ≃+* F) : F →+* F) _).symm
  rw [hc, unitaryInvolution_apply] at hdet
  rw [pow_succ]
  exact hdet

theorem det_lin_pow {F : Type} [Field F] [Finite F] (a : GL (Fin 2) F) :
    ((a : Matrix (Fin 2) (Fin 2) F).det) ^ (Nat.card F - 1) = 1 := by
  have h := pow_card_eq_one' (G := Fˣ) (x := Matrix.GeneralLinearGroup.det a)
  rw [Nat.card_units] at h
  have h' := congrArg (fun u : Fˣ => (u : F)) h
  simpa using h'

theorem layerBar_family [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0)
    (hneven : 2 ∣ n) (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 ↔ l ^ n = 1)
    (hdet : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1)
    (hdvd : n ∣ Nat.card F - 1) (hodd : Odd (Nsub M).index) (hqs : CFSG.IsQuasisimple ↥M.H2)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥M.H2)) (hev : 2 ∣ Nat.card ↥M.H2) {a b : F}
    (hab : a ^ 2 + b ^ 2 = -1) (hH : ∀ g, rhoQ hab g ∈ M.H2)
    (S : Sylow 2 (PG M)) (hSC : (S : Subgroup (PG M)) ≤ Cg M) :
    layerTimesSylow (yP M) (S : Subgroup (PG M)) ⊓ OddCore (yP M) = ⊥ ∧
      barOf (yP M) (layerTimesSylow (yP M) (S : Subgroup (PG M))) =
        oPrimeResidual 2 (CentralizerBar (yP M)) := by
  set s := n.factorization 2 with hs
  set n' := n / 2 ^ s with hn'
  have hn : n = 2 ^ s * n' := (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hodd' : Odd n' := Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hn0)
  have hs1 : 1 ≤ s := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 hneven
  have hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2 := by
    intro l hl
    rw [hU2, hn, mul_comm, pow_mul, hl, one_pow]
  have hU2' : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ n = 1 := fun l hl => (hU2 l).1 hl
  have hdvd' : n' ∣ Nat.card F - 1 := (Nat.ordCompl_dvd n 2).trans hdvd
  have hR := pPrimeCore_eq_R0 M h2 hn hs1 hodd' hU hU2' hdvd' hqs hZ hev hab hH
  exact layerBar_generic M h2 hn hs1 hodd' hU hdet hodd hqs hab hH hdvd' hR S hSC

end LayerBar

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
