module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4OuterBound
public import CFSG.Milestones.ASVolI.F411.aG2Core
public import CFSG.LocalAnalysis.StandardType.GGD4AdjointOm8

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.QuasithinUnique.Setup
open scoped Pointwise

section Generic

variable {V : Type*} [Group V]

theorem exists_involution_card_le_of_not_commute [Finite V]
    {S : Subgroup (MulAut V)} (hS : IsPGroup 2 S) {x u : MulAut V}
    (hxS : x ∈ Subgroup.normalizer (S : Set (MulAut V))) (hx2 : x * x = 1) (hu : u ∈ S)
    (hxu : x * u ≠ u * x) :
    ∃ t ∈ S, t ≠ 1 ∧ t * t = 1 ∧
      Nat.card V * Nat.card {v : V // x v = v} ^ 2 ≤
        Nat.card V ^ 2 * Nat.card {v : V // t v = v} := by
  let F : MulAut V → Subgroup V := fun f => f.toMonoidHom.eqLocus (MonoidHom.id V)
  have hfix : ∀ f : MulAut V, Nat.card {v : V // f v = v} = Nat.card (F f) := fun _ => rfl
  let c : MulAut V := x⁻¹ * u⁻¹ * x * u
  have hcS : c ∈ S := by
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (S : Set (MulAut V)) :=
      Subgroup.inv_mem _ hxS
    have h1 : x⁻¹ * u⁻¹ * (x⁻¹)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hxinv u⁻¹).mp (Subgroup.inv_mem S hu)
    simpa [c] using S.mul_mem h1 hu
  have hcne : c ≠ 1 := by
    intro hc1
    apply hxu
    have h1 : u⁻¹ * x * u = x := by
      have h2 := congrArg (fun g : MulAut V => x * g) hc1
      simpa [c, mul_assoc] using h2
    calc x * u = u * (u⁻¹ * x * u) := by group
      _ = u * x := by rw [h1]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf (⟨c, hcS⟩ : S) = 2 ^ k :=
    (IsPGroup.iff_orderOf.mp hS) ⟨c, hcS⟩
  have hk' : orderOf c = 2 ^ k := by simpa using hk
  have hk0 : k ≠ 0 := by
    intro hk0
    exact hcne (orderOf_eq_one_iff.mp (by simpa [hk0] using hk'))
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  let t : MulAut V := c ^ 2 ^ (k - 1)
  have htS : t ∈ S := S.pow_mem hcS _
  have htwo : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hkpos]
  have ht2 : t * t = 1 := by
    calc t * t = c ^ 2 ^ (k - 1) * c ^ 2 ^ (k - 1) := rfl
      _ = c ^ (2 ^ (k - 1) + 2 ^ (k - 1)) := (pow_add c _ _).symm
      _ = c ^ 2 ^ k := by rw [htwo]
      _ = 1 := by rw [← hk', pow_orderOf_eq_one]
  have htne : t ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · exact pow_ne_zero _ (by norm_num)
    · rw [hk']
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_one_lt hk0)
  have hc_le_pow : ∀ n : ℕ, F c ≤ F (c ^ n) := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero]
        intro v _
        simp [F]
    | succ n ih =>
        rw [pow_succ']
        intro v hv
        have hnv : (c ^ n) v = v := ih hv
        show c ((c ^ n) v) = v
        rw [hnv]
        exact hv
  have hsub : F x ⊓ F (u⁻¹ * x * u) ≤ F c := by
    intro v hv
    rw [Subgroup.mem_inf] at hv
    obtain ⟨hxv, huv⟩ := hv
    have hxv' : x v = v := hxv
    have huv' : (u⁻¹ * x * u) v = v := huv
    have hxinv : x⁻¹ v = v := by
      rw [inv_eq_of_mul_eq_one_right hx2]
      exact hxv'
    calc c v = x⁻¹ ((u⁻¹ * x * u) v) := by simp [c, MulAut.mul_apply]
      _ = x⁻¹ v := by rw [huv']
      _ = v := hxinv
  have hle_sub : F x ⊓ F (u⁻¹ * x * u) ≤ F t :=
    le_trans hsub (hc_le_pow (2 ^ (k - 1)))
  have hcardconj : Nat.card (F (u⁻¹ * x * u)) = Nat.card (F x) := by
    rw [← hfix (u⁻¹ * x * u), ← hfix x]
    refine Nat.card_congr ?_
    refine
      { toFun := fun v => ⟨u v.1, ?_⟩
        invFun := fun w => ⟨u⁻¹ w.1, ?_⟩
        left_inv := fun v => ?_
        right_inv := fun w => ?_ }
    · have h := congrArg (fun y : V => u y) v.2
      simpa [MulAut.mul_apply] using h
    · have h := congrArg (fun y : V => u⁻¹ y) w.2
      simpa [MulAut.mul_apply] using h
    · ext
      simp
    · ext
      simp
  have hcpos : 0 < Nat.card (F x) := Finite.card_pos_iff.mpr ⟨1⟩
  have haindeq : (F (u⁻¹ * x * u)).index = (F x).index := by
    have h1 := (F (u⁻¹ * x * u)).card_mul_index
    have h2 := (F x).card_mul_index
    rw [hcardconj] at h1
    exact Nat.mul_left_cancel hcpos (h1.trans h2.symm)
  have hapos : 0 < (F x).index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := F x))
  have hle : (F t).index ≤ (F x).index * (F x).index := by
    have h1 : (F t).index ≤ (F x ⊓ F (u⁻¹ * x * u)).index :=
      Subgroup.index_antitone hle_sub
    have h2 : (F x ⊓ F (u⁻¹ * x * u)).index ≤
        (F x).index * (F (u⁻¹ * x * u)).index := Subgroup.index_inf_le
    calc (F t).index ≤ (F x ⊓ F (u⁻¹ * x * u)).index := h1
      _ ≤ (F x).index * (F (u⁻¹ * x * u)).index := h2
      _ = (F x).index * (F x).index := by rw [haindeq]
  have hca := (F x).card_mul_index
  have hct := (F t).card_mul_index
  have hb_le : (F t).index ≤ (F x).index ^ 2 := by
    simpa [pow_two] using hle
  have hmain : Nat.card V * Nat.card (F x) ^ 2 ≤ Nat.card V ^ 2 * Nat.card (F t) := by
    have hL : Nat.card V * Nat.card (F x) ^ 2 * (F x).index ^ 2 = Nat.card V ^ 3 := by
      calc Nat.card V * Nat.card (F x) ^ 2 * (F x).index ^ 2
          = Nat.card V * (Nat.card (F x) * (F x).index) ^ 2 := by ring
        _ = Nat.card V * Nat.card V ^ 2 := by rw [hca]
        _ = Nat.card V ^ 3 := by ring
    have h1 : Nat.card V ^ 3 ≤
        Nat.card V ^ 2 * (Nat.card (F t) * (F x).index ^ 2) := by
      calc Nat.card V ^ 3 = Nat.card V ^ 2 * Nat.card V := by ring
        _ = Nat.card V ^ 2 * (Nat.card (F t) * (F t).index) := by rw [hct]
        _ ≤ Nat.card V ^ 2 * (Nat.card (F t) * (F x).index ^ 2) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb_le)
    have h2 : Nat.card V ^ 2 * (Nat.card (F t) * (F x).index ^ 2) =
        Nat.card V ^ 2 * Nat.card (F t) * (F x).index ^ 2 := by ring
    have hkey : Nat.card V * Nat.card (F x) ^ 2 * (F x).index ^ 2 ≤
        Nat.card V ^ 2 * Nat.card (F t) * (F x).index ^ 2 := by
      calc Nat.card V * Nat.card (F x) ^ 2 * (F x).index ^ 2 = Nat.card V ^ 3 := hL
        _ ≤ Nat.card V ^ 2 * (Nat.card (F t) * (F x).index ^ 2) := h1
        _ = Nat.card V ^ 2 * Nat.card (F t) * (F x).index ^ 2 := h2
    exact Nat.le_of_mul_le_mul_right hkey (pow_pos hapos 2)
  refine ⟨t, htS, htne, ht2, ?_⟩
  rw [hfix x, hfix t]
  exact hmain

end Generic

section Sylow

variable {V : Type} [CommGroup V]

private theorem exists_sylow_conjAut_mem [Finite V] {L : Subgroup (MulAut V)} {x : MulAut V}
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut V))) (hx2 : x * x = 1) :
    ∃ P : Sylow 2 L, ∀ y ∈ (P : Subgroup L), X1.conjAut L hxN y ∈ (P : Subgroup L) := by
  classical
  have hxinv : x⁻¹ = x := mul_eq_one_iff_inv_eq.mp hx2
  let σ : MulAut ↥L := X1.conjAut L hxN
  have hσ2 : σ * σ = 1 := by
    refine MulEquiv.ext fun y => ?_
    apply Subtype.ext
    show x * ((X1.conjAut L hxN y : ↥L) : MulAut V) * x⁻¹ = (y : MulAut V)
    rw [X1.coe_conjAut, hxinv]
    calc x * (x * (y : MulAut V) * x) * x
        = (x * x) * (y : MulAut V) * (x * x) := by group
      _ = (y : MulAut V) := by rw [hx2, one_mul, mul_one]
  have hσp : IsPGroup 2 (Subgroup.zpowers σ) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa [pow_two] using orderOf_dvd_of_pow_eq_one hσ2
  have hnotdvd : ¬ 2 ∣ Nat.card (Sylow 2 ↥L) :=
    not_dvd_card_sylow (p := 2) (G := ↥L)
  obtain ⟨P, hP⟩ := hσp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥L) hnotdvd
  refine ⟨P, fun y hy => ?_⟩
  have hfix : (⟨σ, Subgroup.mem_zpowers σ⟩ : ↥(Subgroup.zpowers σ)) • P = P :=
    MulAction.mem_fixedPoints.mp hP ⟨σ, Subgroup.mem_zpowers σ⟩
  have hfix' : σ • P = P := by
    simpa [MulAction.compHom_smul_def] using hfix
  have hsub : σ • (P : Subgroup ↥L) = (P : Subgroup ↥L) := by
    simpa only [Sylow.pointwise_smul_def] using
      congrArg (fun Q : Sylow 2 ↥L => (Q : Subgroup ↥L)) hfix'
  have hmem : σ • y ∈ σ • (P : Subgroup ↥L) :=
    Subgroup.smul_mem_pointwise_smul y σ (P : Subgroup ↥L) hy
  rw [hsub] at hmem
  simpa [MulAut.smul_def] using hmem

end Sylow

section D4


private theorem nonempty_adjointGroup_equiv {K : Type} [Field K] [Finite K] [CharP K 2] :
    Nonempty (adjointGroup .D4 K ≃* orthElementaryGroup (quadPlus 4 K)) := by
  obtain ⟨Φ, -⟩ := CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)
  exact ⟨Φ.trans ((CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance.statedDerivedReindexEquiv
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.plusIndexEquiv 4) (quadPlus 4 K)
    (coe_quadPlus 4 K)).symm.trans
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel.plusDerivedEquiv 4 K
      (by norm_num)))⟩

private theorem not_forall_conjAut_eq_of_not_mem {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)}
    (θ : L ≃* orthElementaryGroup (quadPlus 4 K)) (hirr : X1.IsIrrOn L) {x : MulAut V}
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut V))) (hx2 : x * x = 1) (hxL : x ∉ L)
    (P : Sylow 2 L) : ¬ ∀ y ∈ (P : Subgroup L), X1.conjAut L hxN y = y := by
  classical
  intro hfix
  obtain ⟨η⟩ := nonempty_adjointGroup_equiv (K := K)
  let ψ : adjointGroup .D4 K ≃* ↥L := η.trans θ.symm
  let α : MulAut (adjointGroup .D4 K) := (ψ.trans (X1.conjAut L hxN)).trans ψ.symm
  let Q : Sylow 2 (adjointGroup .D4 K) :=
    P.comapOfInjective ψ.toMonoidHom ψ.injective (by simp)
  have hα : ∀ s ∈ (Q : Subgroup (adjointGroup .D4 K)), α s = s := by
    intro s hs
    have hsP : ψ s ∈ (P : Subgroup ↥L) := by
      simpa [Q, Sylow.coe_comapOfInjective] using hs
    have hαs : α s = ψ.symm (X1.conjAut L hxN (ψ s)) := by
      simp [α, MulEquiv.trans_apply]
    rw [hαs, hfix (ψ s) hsP]
    simp
  obtain ⟨g, hg⟩ := CFSG.ASVolI.burnsideF411a_chev_inner_of_fix_sylow .D4 K 2 α Q hα
  refine hxL (mem_of_conjAut_eq_conj hV hirr hxN hx2 (ψ g) ?_)
  intro y
  have hαy : α (ψ.symm y) = g * ψ.symm y * g⁻¹ := by
    rw [DFunLike.congr_fun hg (ψ.symm y), MulAut.conj_apply]
  calc X1.conjAut L hxN y
      = ψ (α (ψ.symm y)) := by simp [α, MulEquiv.trans_apply]
    _ = ψ (g * ψ.symm y * g⁻¹) := by rw [hαy]
    _ = ψ g * y * (ψ g)⁻¹ := by simp

theorem exists_involution_index_le_of_outer
    {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)}
    (θ : L ≃* orthElementaryGroup (quadPlus 4 K))
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) {x : MulAut V}
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut V))) (hx2 : x * x = 1) (hxL : x ∉ L) :
    ∃ t ∈ L, t ≠ 1 ∧ t * t = 1 ∧
      Nat.card V * Nat.card {v : V // x v = v} ^ 2 ≤
        Nat.card V ^ 2 * Nat.card {v : V // t v = v} := by
  classical
  have hxinv : x⁻¹ = x := mul_eq_one_iff_inv_eq.mp hx2
  obtain ⟨P, hP⟩ := exists_sylow_conjAut_mem (V := V) hxN hx2
  let S : Subgroup (MulAut V) := (P : Subgroup ↥L).map L.subtype
  have hS : IsPGroup 2 S := P.isPGroup'.map L.subtype
  have hxS : x ∈ Subgroup.normalizer (S : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · rintro ⟨y, hyP, rfl⟩
      refine Subgroup.mem_map.mpr ⟨X1.conjAut L hxN y, hP y hyP, ?_⟩
      change ((X1.conjAut L hxN y : ↥L) : MulAut V) = x * ↑y * x⁻¹
      exact X1.coe_conjAut L hxN y
    · intro hs
      obtain ⟨y, hyP, hy⟩ := Subgroup.mem_map.mp hs
      have hy' : (y : MulAut V) = x * s * x⁻¹ := hy
      refine Subgroup.mem_map.mpr ⟨X1.conjAut L hxN y, hP y hyP, ?_⟩
      change ((X1.conjAut L hxN y : ↥L) : MulAut V) = s
      rw [X1.coe_conjAut, hy', hxinv]
      calc x * (x * s * x) * x = (x * x) * s * (x * x) := by group
        _ = s := by rw [hx2, one_mul, mul_one]
  have hnot := not_forall_conjAut_eq_of_not_mem (K := K) hV θ hirr hxN hx2 hxL P
  push Not at hnot
  obtain ⟨y, hyP, hyne⟩ := hnot
  have hu : (y : MulAut V) ∈ S := Subgroup.mem_map_of_mem L.subtype hyP
  have hxu : x * (y : MulAut V) ≠ (y : MulAut V) * x := by
    intro h
    apply hyne
    apply Subtype.ext
    rw [X1.coe_conjAut, hxinv, h, mul_assoc, hx2, mul_one]
  obtain ⟨t, htS, ht1, ht2, hcard⟩ :=
    exists_involution_card_le_of_not_commute (S := S) hS hxS hx2 hu hxu
  exact ⟨t, Subgroup.map_subtype_le _ htS, ht1, ht2, hcard⟩

end D4

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
