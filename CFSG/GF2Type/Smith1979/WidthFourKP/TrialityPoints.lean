module

public import CFSG.LargeExtraspecial.S4TwoG
public import CFSG.LargeExtraspecial.S11Basic
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Tri

open CFSG CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.CGT.Timmesfeld75 CFSG.RankThree.OrthogonalInvolutions
open scoped MatrixGroups
open Subgroup Module QuadraticMap

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem isL2Pair_M0 (hw : S.width = 4) (C : Cons311 S g)
    (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3) :
    IsL2Pair (M0 S g) (LM0 S g) (2 ^ 3) := by
  have hcardL : Nat.card (LM0 S g) = 8 := by
    rw [card_LM0, C.card_Lbar, hw]
    norm_num
  have hcardM : Nat.card (M0 S g) = 504 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight h8
  have hidx : ¬ 2 ∣ (LM0 S g).index := by
    have h := (LM0 S g).card_mul_index
    rw [hcardL, hcardM] at h
    have h63 : (LM0 S g).index = 63 := by omega
    rw [h63]
    norm_num
  have hS : IsPGroup 2 (LM0 S g) := IsPGroup.of_card (n := 3) (by rw [hcardL]; norm_num)
  have hpsl : Nonempty (M0 S g ≃* PSL(2, GaloisField 2 3)) :=
    CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated 2 3 (by norm_num)
      (GaloisField.card 2 3 (by norm_num)) h8
  exact IsL2Pair.of_psl_isPGroup (f := 3) (by norm_num) hpsl hS hidx

theorem span_points_eq_top (H : Hyp4 S g) (hirr : ¬ S.IsReducible) :
    Submodule.span (ZMod 2)
      (Set.range fun m : S.M =>
        ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = ⊤ := by
  set v := S.cl (g * S.z * g⁻¹) with hv
  set W : Submodule (ZMod 2) S.Qt :=
    Submodule.span (ZMod 2) (Set.range fun m : S.M =>
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) with hW
  have hvW : v ∈ W := by
    rw [hW]
    exact Submodule.subset_span ⟨1, by simp⟩
  have hne : v ≠ 0 := cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have hW0 : W ≠ ⊥ := fun h => hne ((Submodule.mem_bot (ZMod 2)).mp (h ▸ hvW))
  by_contra htop
  refine hirr ⟨W, hW0, htop, fun m w hw => ?_⟩
  rw [hW] at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hprod := congrArg (fun x : S.O => ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
      (map_mul S.ρ m k)
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply] at hprod
    rw [← hprod]
    exact Submodule.subset_span ⟨m * k, rfl⟩
  | zero => rw [map_zero]; exact W.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact W.smul_mem a hx

theorem exists_polar_ne_zero (H : Hyp4 S g) (hirr : ¬ S.IsReducible) :
    ∃ m : S.M, polar S.q (S.cl (g * S.z * g⁻¹))
      (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) ≠ 0 := by
  by_contra h
  push Not at h
  exact hirr (isReducible_of_polar_eq_zero H h)

theorem polar_eq_one_of_points_eq (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g)
    (hirr : ¬ S.IsReducible) (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3)
    {k₁ k₂ : M0 S g}
    (hne : (((k₁ : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      (((k₂ : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) :
    polar S.q
      ((((k₁ : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
      ((((k₂ : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 1 := by
  set v := S.cl (g * S.z * g⁻¹) with hv
  set φ : M0 S g → (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    fun k => (((k : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hφ
  change polar S.q (φ k₁ v) (φ k₂ v) = 1
  change φ k₁ v ≠ φ k₂ v at hne
  have hφmem : ∀ k, (φ k : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈
      TauCeti.QuadraticMap.orthogonalGroup S.q := fun k => ((k : S.Mbar) : S.O).2
  have hiso : ∀ k x y, polar S.q (φ k x) (φ k y) = polar S.q x y := fun k x y =>
    @TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (ZMod 2) S.Qt (ZMod 2)
      inferInstance inferInstance inferInstance inferInstance Semiring.toModule S.q (φ k)
      (hφmem k) x y
  have hpt : ∀ k k' : M0 S g, conjSubgroup k (LM0 S g) = conjSubgroup k' (LM0 S g) ↔
      φ k v = φ k' v := fun k k' => conj_LM0_eq_iff H k k'
  have h2 : ConjTwoTransitive (M0 S g) (LM0 S g) := (isL2Pair_M0 hw C h8).conjTwoTransitive
  have hnonzero : ∃ k : M0 S g, polar S.q v (φ k v) ≠ 0 := by
    by_contra h
    push Not at h
    refine hirr (isReducible_of_polar_eq_zero H fun m => ?_)
    have hm : S.ρ m ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨m, rfl⟩
    obtain ⟨k, hk, hkm⟩ := exists_mem_M0_conj_eq H C ⟨S.ρ m, hm⟩
    have hkM : (((⟨k, hk⟩ : M0 S g) : S.Mbar) : S.O) ∈ S.Mbar := k.2
    have e : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
        ((((⟨k, hk⟩ : M0 S g) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      rw [hv]
      exact (map_conj_Lbar_eq_iff H hm hkM).mp hkm
    change polar S.q v (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = 0
    rw [e]
    change polar S.q v (φ ⟨k, hk⟩ v) = 0
    exact h ⟨k, hk⟩
  obtain ⟨k₀, hk₀⟩ := hnonzero
  have hk₀1 : polar S.q v (φ k₀ v) = 1 :=
    CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_one_of_ne_zero hk₀
  have hk₀' : polar S.q v (φ k₀ v) ≠ 0 := by rw [hk₀1]; decide
  have h1v : φ (1 : M0 S g) v = v := rfl
  have hne₀ : φ (1 : M0 S g) v ≠ φ k₀ v := by
    rw [h1v]
    intro h
    rw [← h] at hk₀'
    exact hk₀' (polar_self_eq_zero S.q v)
  obtain ⟨k₁', hk₁', hk₂'⟩ := h2 1 k₀ k₁ k₂ (fun h => hne₀ ((hpt 1 k₀).mp h))
    (fun h => hne ((hpt k₁ k₂).mp h))
  have e1 := (hpt (k₁' * 1) k₁).mp hk₁'
  have e2 := (hpt (k₁' * k₀) k₂).mp hk₂'
  rw [mul_one] at e1
  have hφmul : φ (k₁' * k₀) = (φ k₁' : S.Qt ≃ₗ[ZMod 2] S.Qt) * φ k₀ := rfl
  rw [← e1, ← e2]
  rw [hφmul, LinearEquiv.mul_apply]
  rw [hiso k₁' v (φ k₀ v)]
  exact hk₀1

theorem polar_eq_one_of_ne (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g)
    (hirr : ¬ S.IsReducible) (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3)
    {x y : S.O} (hx : x ∈ S.Mbar) (hy : y ∈ S.Mbar)
    (hne : ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) ≠
      ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))) :
    polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
      ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 1 := by
  set v := S.cl (g * S.z * g⁻¹) with hv
  obtain ⟨k₁, hk₁M0, hk₁⟩ := exists_mem_M0_conj_eq H C ⟨x, hx⟩
  obtain ⟨k₂, hk₂M0, hk₂⟩ := exists_mem_M0_conj_eq H C ⟨y, hy⟩
  have e1 := (map_conj_Lbar_eq_iff H hx k₁.2).mp hk₁
  have e2 := (map_conj_Lbar_eq_iff H hy k₂.2).mp hk₂
  have hne' : ((((⟨k₁, hk₁M0⟩ : M0 S g) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠
      ((((⟨k₂, hk₂M0⟩ : M0 S g) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro h
    apply hne
    rw [e1, e2]
    exact h
  have hmain := polar_eq_one_of_points_eq hw H C hirr h8
    (k₁ := ⟨k₁, hk₁M0⟩) (k₂ := ⟨k₂, hk₂M0⟩) hne'
  rw [e1, e2]
  exact hmain

theorem eq_or_eq_mul_z_of_commute (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g)
    (hirr : ¬ S.IsReducible) (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3)
    (hno : S11.NoA2All S) {b c : G} (hb : IsConj S.z b) (hc : IsConj S.z c)
    (hbQ : b ∈ S.QG) (hcQ : c ∈ S.QG) (hbz : b ≠ S.z) (hcz : c ≠ S.z)
    (hbc : b * c = c * b) : c = b ∨ c = b * S.z := by
  have hF := CFSG.LargeExtraspecial.S6.fusionCtl_of_lemma_3_13 H hno
  obtain ⟨kb, hkb⟩ := isConj_iff.mp hb
  obtain ⟨kc, hkc⟩ := isConj_iff.mp hc
  obtain ⟨m, hm, hmb⟩ := hF kb (hkb ▸ hbQ) (hkb ▸ hbz)
  obtain ⟨n, hn, hnc⟩ := hF kc (hkc ▸ hcQ) (hkc ▸ hcz)
  by_cases hcl : S.cl b = S.cl c
  · exact (S.cl_eq_cl_iff hbQ hcQ).mp hcl
  · exfalso
    have hmb' : ((S.ρ (⟨m, hm⟩ : S.M) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl (g * S.z * g⁻¹)) = S.cl b := by
      rw [S.ρ_cl_conj_z hm H.conj_mem]
      have e : m * g * S.z * (m * g)⁻¹ = m * (g * S.z * g⁻¹) * m⁻¹ := by group
      rw [e, hmb, hkb]
    have hnc' : ((S.ρ (⟨n, hn⟩ : S.M) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl (g * S.z * g⁻¹)) = S.cl c := by
      rw [S.ρ_cl_conj_z hn H.conj_mem]
      have e : n * g * S.z * (n * g)⁻¹ = n * (g * S.z * g⁻¹) * n⁻¹ := by group
      rw [e, hnc, hkc]
    have hne : ((S.ρ (⟨m, hm⟩ : S.M) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl (g * S.z * g⁻¹)) ≠
        ((S.ρ (⟨n, hn⟩ : S.M) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (S.cl (g * S.z * g⁻¹)) := by
      rw [hmb', hnc']
      exact hcl
    have hp := polar_eq_one_of_ne hw H C hirr h8
      (x := S.ρ (⟨m, hm⟩ : S.M)) (y := S.ρ (⟨n, hn⟩ : S.M))
      (MonoidHom.mem_range.mpr ⟨_, rfl⟩) (MonoidHom.mem_range.mpr ⟨_, rfl⟩) hne
    rw [hmb', hnc'] at hp
    have h0 := (S.polar_cl_eq_zero_iff hbQ hcQ).mpr hbc
    rw [hp] at h0
    exact one_ne_zero h0

theorem exists_q_ne_zero_of_ne_one (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g)
    (hirr : ¬ S.IsReducible) (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3)
    {t : S.O} (ht : t ∈ S.Mbar) (ht1 : t ≠ 1) :
    ∃ v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), S.q v ≠ 0 := by
  set v₀ := S.cl (g * S.z * g⁻¹) with hv₀
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp ht
  have hmQ : m ∉ S.Q := fun h => ht1 ((S.ρ_eq_one_iff m).mpr (by
    rw [S.mem_QG_iff]; exact ⟨m.2, h⟩))
  have hmove : ∃ k : S.M, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀) ≠
      ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀ := by
    by_contra h
    push Not at h
    have hfix : ∀ w, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
        ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
      intro w
      have hw : w ∈ Submodule.span (ZMod 2) (Set.range fun k : S.M =>
          ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀) := by
        rw [span_points_eq_top H hirr]
        trivial
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact h k
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, map_add]
      | smul a x _ hx => rw [map_smul, hx, map_smul]
    apply ht1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    simpa using hfix w
  obtain ⟨k, hk⟩ := hmove
  set p := ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀ with hp
  set p' := ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p with hp'
  have hpol : polar S.q p' p = 1 := by
    have hne : (((S.ρ m * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀) ≠
        (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀) := by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
      exact hk
    have h := polar_eq_one_of_ne hw H C hirr h8
      (x := S.ρ m * S.ρ k) (y := S.ρ k)
      (S.Mbar.mul_mem (MonoidHom.mem_range.mpr ⟨m, rfl⟩)
        (MonoidHom.mem_range.mpr ⟨k, rfl⟩))
      (MonoidHom.mem_range.mpr ⟨k, rfl⟩) hne
    rwa [Subgroup.coe_mul, LinearEquiv.mul_apply] at h
  have hq0 : S.q p = 0 := by
    rw [hp, @TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (ZMod 2) S.Qt (ZMod 2)
      inferInstance inferInstance inferInstance inferInstance Semiring.toModule S.q (S.ρ k)
      (S.ρ k).2 v₀]
    exact S.q_cl_conj_z H.conj_mem
  have hq0' : S.q p' = 0 := by
    rw [hp', hp,
      @TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (ZMod 2) S.Qt (ZMod 2)
        inferInstance inferInstance inferInstance inferInstance Semiring.toModule S.q (S.ρ m)
        (S.ρ m).2 (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀),
      @TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (ZMod 2) S.Qt (ZMod 2)
        inferInstance inferInstance inferInstance inferInstance Semiring.toModule S.q (S.ρ k)
        (S.ρ k).2 v₀]
    exact S.q_cl_conj_z H.conj_mem
  refine ⟨p' + p, ?_, ?_⟩
  · have h := sub_mem_commSpace ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p
    rw [← hp', CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec (K := ZMod 2)] at h
    exact h
  · rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq (K := ZMod 2) S.q p' p, hq0', hq0,
      hpol]
    decide

end CFSG.GF2Type.Smith1979.W4Tri
