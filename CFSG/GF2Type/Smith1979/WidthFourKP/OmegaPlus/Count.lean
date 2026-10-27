module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.CentT
public import CFSG.GF2Type.Smith1979.W4AsE11Surv
public import CFSG.GF2Type.Smith1979.W4AsSurvL216
public import CFSG.LargeExtraspecial.S12Elim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_Mbar_inf_normalizer_le (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9)
    (hK4 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    Nat.card (S.Mbar ⊓ normalizer (S.Lbar g : Set S.O) : Subgroup S.O) ≤ 224 := by
  let N : Subgroup S.O := S.Mbar ⊓ normalizer (S.Lbar g : Set S.O)
  letI : MulAction N (S.Lbar g) :=
    { smul := fun n x => ⟨(n : S.O) * (x : S.O) * (n : S.O)⁻¹,
        (Subgroup.mem_normalizer_iff.mp n.2.2 x).mp x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        show (1 : S.O) * (x : S.O) * (1 : S.O)⁻¹ = (x : S.O)
        group
      mul_smul := fun m n x => by
        apply Subtype.ext
        show (((m * n : N) : S.O) * (x : S.O) * ((m * n : N) : S.O)⁻¹) =
          ((m : S.O) * ((n : S.O) * (x : S.O) * (n : S.O)⁻¹) * (m : S.O)⁻¹)
        rw [Subgroup.coe_mul]
        group }
  let tL : S.Lbar g := ⟨t, ht⟩
  have horbit : MulAction.orbit N tL ⊆ {x : S.Lbar g | x ≠ 1} := by
    rintro _ ⟨n, rfl⟩
    intro h
    have h1 : (n : S.O) * t * (n : S.O)⁻¹ = 1 := congrArg Subtype.val h
    have h2 : MulAut.conj (n : S.O) t = MulAut.conj (n : S.O) 1 := by
      rw [MulAut.conj_apply, MulAut.conj_apply, h1]
      group
    exact ht1 ((MulAut.conj (n : S.O)).injective h2)
  have horbit_card : (MulAction.orbit N tL).ncard ≤ 7 := by
    have hsub := Set.ncard_le_ncard horbit
    have hset : ({x : S.Lbar g | x ≠ 1}).ncard = 7 := by
      have h := Set.ncard_diff_singleton_add_one (s := (Set.univ : Set ↥(S.Lbar g)))
        (a := 1) (Set.mem_univ _) (Set.finite_univ)
      rw [Set.ncard_univ, C.card_Lbar, hw] at h
      have hEq : ({x : ↥(S.Lbar g) | x ≠ 1}) = Set.univ \ {1} := by ext x; simp
      rw [hEq]
      omega
    rwa [hset] at hsub
  let A : Subgroup S.O := S14.Ct S t ⊓ normalizer (S.Lbar g : Set S.O)
  have hAN : A ≤ N := by
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  have hstab_eq : MulAction.stabilizer N tL = A.subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hn
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_, n.2.2⟩
      have hv : (n : S.O) * t * (n : S.O)⁻¹ = t := congrArg Subtype.val hn
      change (n : S.O) ∈ S8.CMt S t
      rw [S8.mem_CMt]
      refine ⟨n.2.1, ?_⟩
      calc (n : S.O) * t = ((n : S.O) * t * (n : S.O)⁻¹) * (n : S.O) := by group
        _ = t * (n : S.O) := by rw [hv]
    · intro hn
      rw [Subgroup.mem_subgroupOf] at hn
      apply Subtype.ext
      have hn' : (n : S.O) ∈ S8.CMt S t := hn.1
      have hcomm : (n : S.O) * t = t * (n : S.O) := (S8.mem_CMt.mp hn').2
      show (n : S.O) * t * (n : S.O)⁻¹ = t
      rw [hcomm]
      group
  have hstab_card : Nat.card (MulAction.stabilizer N tL) ≤ 32 := by
    rw [hstab_eq]
    have hcardA : Nat.card A ∣ 32 :=
      card_Ct_inf_normalizer_dvd hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9 hK4 hP3 hPn
    have hEq : Nat.card ↥(A.subgroupOf N) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
    rw [hEq]
    exact Nat.le_of_dvd (by norm_num) hcardA
  have hcardN : Nat.card N =
      Nat.card (MulAction.stabilizer N tL) * (MulAction.orbit N tL).ncard := by
    calc Nat.card N = (MulAction.stabilizer N tL).index *
          Nat.card (MulAction.stabilizer N tL) := (Subgroup.index_mul_card _).symm
      _ = (MulAction.orbit N tL).ncard * Nat.card (MulAction.stabilizer N tL) := by
          rw [MulAction.index_stabilizer]
      _ = Nat.card (MulAction.stabilizer N tL) * (MulAction.orbit N tL).ncard :=
          Nat.mul_comm _ _
  change Nat.card N ≤ 224
  rw [hcardN]
  calc Nat.card (MulAction.stabilizer N tL) * (MulAction.orbit N tL).ncard ≤ 32 * 7 :=
        Nat.mul_le_mul hstab_card horbit_card
    _ = 224 := by norm_num


theorem card_Mbar_le (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9)
    (hK4 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    Nat.card S.Mbar ≤ 30240 := by
  letI : MulAction S.Mbar S.Qt :=
    { smul := fun m v => ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
      one_smul := fun v => rfl
      mul_smul := fun m n v => rfl }
  let a : S.Qt := S.cl (g * S.z * g⁻¹)
  have ha0 : a ≠ 0 := S4.cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have horbit : MulAction.orbit S.Mbar a ⊆ {v : S.Qt | S.q v = 0} \ {0} := by
    rintro _ ⟨m, rfl⟩
    constructor
    · change S.q (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) = 0
      have hmO : ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈
          TauCeti.QuadraticMap.orthogonalGroup S.q := (m : S.O).2
      have hq := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hmO) a
      rw [hq]
      exact S4.q_cl_conj_z S H.conj_mem
    · change (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) ≠ 0
      intro h
      exact ha0 (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp h)
  have horbit_card : (MulAction.orbit S.Mbar a).ncard ≤ 135 := by
    have hsub := Set.ncard_le_ncard horbit
    have h8 : finrank (ZMod 2) S.Qt = 8 := by
      rw [S.finrank_Qt_eq_two_mul_width, hw]
    have hsing : Nat.card {v : S.Qt // S.q v = 0} = 136 :=
      W4As.card_singular_eq_136 S.q_nondegenerate h8 h4
        (fun v hv => S4.q_eq_zero_of_mem_Vt H ht1 hv)
    have hcard : ({v : S.Qt | S.q v = 0}).ncard = 136 := by
      rw [← Nat.card_coe_set_eq]
      exact hsing
    have h0 : (0 : S.Qt) ∈ {v : S.Qt | S.q v = 0} := by
      simpa using S4.q_cl_conj_z S H.conj_mem
    have h := Set.ncard_diff_singleton_add_one (s := {v : S.Qt | S.q v = 0})
      (a := 0) h0 (Set.toFinite _)
    rw [hcard] at h
    have hset : ({v : S.Qt | S.q v = 0} \ {0}).ncard = 135 := by omega
    rwa [hset] at hsub
  let N : Subgroup S.O := S.Mbar ⊓ normalizer (S.Lbar g : Set S.O)
  have hstab_eq : MulAction.stabilizer S.Mbar a = N.subgroupOf S.Mbar := by
    ext m
    rw [MulAction.mem_stabilizer_iff]
    have hfix := S.mem_normalizer_Lbar_iff_fix H.conj_mem H.conj_ne
      (by omega : 3 ≤ S.width) m.2
    constructor
    · intro h
      rw [Subgroup.mem_subgroupOf]
      exact ⟨m.2, hfix.mpr h⟩
    · intro h
      rw [Subgroup.mem_subgroupOf] at h
      exact hfix.mp h.2
  have hstab_card : Nat.card (MulAction.stabilizer S.Mbar a) ≤ 224 := by
    rw [hstab_eq]
    have hle : N ≤ S.Mbar := inf_le_left
    have hEq : Nat.card ↥(N.subgroupOf S.Mbar) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hEq]
    exact card_Mbar_inf_normalizer_le hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9
      hK4 hP3 hPn
  have hcard : Nat.card S.Mbar = Nat.card (MulAction.stabilizer S.Mbar a) *
      (MulAction.orbit S.Mbar a).ncard := by
    calc Nat.card S.Mbar = (MulAction.stabilizer S.Mbar a).index *
          Nat.card (MulAction.stabilizer S.Mbar a) := (Subgroup.index_mul_card _).symm
      _ = (MulAction.orbit S.Mbar a).ncard * Nat.card (MulAction.stabilizer S.Mbar a) := by
          rw [MulAction.index_stabilizer]
      _ = Nat.card (MulAction.stabilizer S.Mbar a) * (MulAction.orbit S.Mbar a).ncard :=
          Nat.mul_comm _ _
  rw [hcard]
  calc Nat.card (MulAction.stabilizer S.Mbar a) * (MulAction.orbit S.Mbar a).ncard ≤ 224 * 135 :=
        Nat.mul_le_mul hstab_card horbit_card
    _ = 30240 := by norm_num


theorem layer_eq_top (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9)
    (hK4 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    15120 < Nat.card (timmesfeldLayer S.Mbar) → timmesfeldLayer S.Mbar = ⊤ := by
  intro hbig
  let E : Subgroup S.Mbar := timmesfeldLayer S.Mbar
  have hM : Nat.card S.Mbar ≤ 30240 :=
    card_Mbar_le hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9 hK4 hP3 hPn
  have hbigE : 15120 < Nat.card E := hbig
  have hcard : Nat.card E * E.index = Nat.card S.Mbar := Subgroup.card_mul_index E
  have hidx : E.index = 1 := by
    have hidx0 : E.index ≠ 0 := by
      rw [Subgroup.index_eq_card]
      exact Nat.pos_iff_ne_zero.mp Nat.card_pos
    by_contra hne
    have h2 : 2 ≤ E.index := by omega
    have hle : Nat.card E * 2 ≤ Nat.card E * E.index := Nat.mul_le_mul_left _ h2
    omega
  rw [show timmesfeldLayer S.Mbar = E from rfl, ← Subgroup.index_eq_one]
  exact hidx

theorem card_layer_quot_dvd (hw : S.width = 4) (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) :
    Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∣ 348364800 := by
  have h8 : finrank (ZMod 2) S.Qt = 8 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hO : Nat.card S.O = 348364800 := by
    rw [W4As.Surv.card_orthogonalGroup_plus_eight S.q_nondegenerate h8
      ⟨Vt S g t, h4, fun v hv => S4.q_eq_zero_of_mem_Vt H ht1 hv⟩]
    norm_num
  have h1 : Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∣
      Nat.card (timmesfeldLayer S.Mbar) := Subgroup.card_quotient_dvd_card _
  have h2 : Nat.card (timmesfeldLayer S.Mbar) ∣ Nat.card S.Mbar :=
    Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card S.Mbar ∣ Nat.card S.O := Subgroup.card_subgroup_dvd_card _
  rw [hO] at h3
  exact h1.trans (h2.trans h3)

theorem card_layer_quot_le (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9)
    (hK4 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ≤ 30240 := by
  have hM : Nat.card S.Mbar ≤ 30240 :=
    card_Mbar_le hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9 hK4 hP3 hPn
  have h1 : Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∣
      Nat.card (timmesfeldLayer S.Mbar) := Subgroup.card_quotient_dvd_card _
  have h2 : Nat.card (timmesfeldLayer S.Mbar) ∣ Nat.card S.Mbar :=
    Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ≤
      Nat.card (timmesfeldLayer S.Mbar) := Nat.le_of_dvd Nat.card_pos h1
  have h4 : Nat.card (timmesfeldLayer S.Mbar) ≤ Nat.card S.Mbar :=
    Nat.le_of_dvd Nat.card_pos h2
  exact le_trans h3 (le_trans h4 hM)
end CFSG.GF2Type.Smith1979.OmegaPlus
