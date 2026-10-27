module

public import CFSG.LargeExtraspecial.AS35U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35U

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem exists_smul_eq_of_mem_centralizer (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0)
    (he : herm frob e e = 0) {g : SUid frob m}
    (hg : (QuotientGroup.mk g : PG m) ∈ centralizer {tq e}) :
    ∃ μ : K, μ ≠ 0 ∧ g • e = μ • e := by
  have h1 : tq (g • e) = tq e := by
    rw [← conj_tq g he, mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hge0 : g • e ≠ 0 := (smul_ne_zero_iff_ne g).mpr he0
  have hge : herm frob (g • e) (g • e) = 0 := by rw [herm_smul_smul, he]
  obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm hge0 hge he0 he).mp h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact he0 hc
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
  calc g • e = c⁻¹ • (c • (g • e)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • e := by rw [← hc]

theorem add_two_le_width (hm : 4 ≤ m) (T : Setting (PG m)) {e : Fin m → K} (he0 : e ≠ 0)
    (he : herm frob e e = 0) (hTz : T.z = tq e) : m ≤ T.width + 2 := by
  have hm3 : 3 ≤ m := by omega
  have he' : hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  set π := QuotientGroup.mk' (center (SUid frob m)) with hπ
  obtain ⟨-, -, -, -, -, -, -, hext, -, hcard, hSU, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      hF hermB_isSymm hermB_separatingLeft hd he0 he'
  set A := axisKernel (hermB m) e
  set Ahat := A.comap (ι m)
  have hAmap : Ahat.map (ι m) = A := Subgroup.map_comap_eq_self fun y hy => by
    obtain ⟨a, ha⟩ := exists_ι_eq (hSU hy)
    exact ⟨a, ha⟩
  have hfix : ∀ a ∈ Ahat, a • e = e := fun a ha => by
    rw [← ι_apply]
    exact (mem_axisKernel.mp ha).2.1
  have hinj : ∀ x ∈ Ahat, π x = 1 → x = 1 := by
    intro x hx h1
    have hxZ : x ∈ center (SUid frob m) := (QuotientGroup.eq_one_iff _).mp h1
    rw [center_SUid hm3] at hxZ
    obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hxZ
    have hce : c • e = e := (hc e).symm.trans (hfix x hx)
    have hc1 : c = 1 := by
      have h0 : (c - 1) • e = 0 := by rw [sub_smul, one_smul, hce, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right he0)
    exact ext_smul _ fun y => by rw [hc, hc1, one_smul, one_smul]
  set r := π.comp Ahat.subtype
  have hr : Function.Injective r := (injective_iff_map_eq_one r).mpr fun x hx =>
    Subtype.ext (hinj x x.2 hx)
  have hcardbar : Nat.card (Ahat.map π) = 2 ^ (1 + 2 * (m - 2)) := by
    have hrange : r.range = Ahat.map π := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hr).toEquiv,
      ← Subgroup.card_map_of_injective (K := Ahat) (f := ι m) ι_injective, hAmap, hcard,
      Module.finrank_fin_fun]
  have hle : Ahat.map π ≤ T.M := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff, hTz]
    have h1 : a * tvU e = tvU e * a := by
      calc a * tvU e = a * tvU e * a⁻¹ * a := by group
        _ = tvU e * a := by rw [conj_tvU a he, hfix a ha]
    change π a * π (tvU e) = π (tvU e) * π a
    rw [← map_mul, ← map_mul, h1]
  have hnorm : ∀ c ∈ T.M, ∀ x ∈ Ahat.map π, c * x * c⁻¹ ∈ Ahat.map π := by
    intro c hc x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center (SUid frob m)) c
    obtain ⟨a, ha, rfl⟩ := hx
    have hgc : (QuotientGroup.mk g : PG m) ∈ centralizer {tq e} := by rw [← hTz]; exact hc
    obtain ⟨μ, hμ0, hgμ⟩ := exists_smul_eq_of_mem_centralizer hm3 he0 he hgc
    have hginv : g⁻¹ • e = μ⁻¹ • e := by
      calc g⁻¹ • e = g⁻¹ • (μ⁻¹ • (μ • e)) := by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
        _ = μ⁻¹ • e := by rw [smul_comm g⁻¹ μ⁻¹ (μ • e), ← hgμ, inv_smul_smul]
    refine ⟨g * a * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change ι m (g * a * g⁻¹) ∈ A
    refine mem_axisKernel.mpr ⟨(mem_sesqSpecialUnitaryGroup.mp (ι_mem _)).1, ?_, ?_⟩
    · rw [ι_apply, mul_smul, mul_smul, hginv, smul_comm a μ⁻¹ e, hfix a ha, smul_comm g μ⁻¹ e,
        hgμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    · intro x hx
      have hx' : herm frob e x = 0 := mem_axisPerp.mp hx
      have hy : herm frob e (g⁻¹ • x) = 0 := by
        have h := herm_smul_smul frob g e (g⁻¹ • x)
        rw [hgμ, smul_inv_smul, herm_smul_left, hx', mul_zero] at h
        exact h.symm
      have ha' := (mem_axisKernel.mp ha).2.2 (g⁻¹ • x) (mem_axisPerp.mpr hy)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha'
      rw [ι_apply] at hc
      refine Submodule.mem_span_singleton.mpr ⟨c * μ, ?_⟩
      rw [ι_apply]
      calc (c * μ) • e = g • (c • e) := by rw [smul_comm, hgμ, smul_smul]
        _ = g • (a • (g⁻¹ • x) - g⁻¹ • x) := by rw [hc]
        _ = (g * a * g⁻¹) • x - x := by rw [smul_sub, smul_inv_smul, mul_smul, mul_smul]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 (Ahat.map π) := IsPGroup.of_card hcardbar
  have hn : ((Ahat.map π).subgroupOf T.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    exact fun x k hx hk => hnorm k hk x hx
  have hP := T.le_of_normal _ hn (hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm)
  have hQle : Ahat.map π ≤ T.QG := fun x hx => ⟨⟨x, hle hx⟩, hP hx, rfl⟩
  have hc := Subgroup.card_le_of_le hQle
  rw [hcardbar, T.card_QG_eq_card_Q, T.card_Q_eq] at hc
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hc
  omega

end CFSG.LargeExtraspecial.AS35U

namespace CFSG.LargeExtraspecial.Setting

open Matrix CFSG.Open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem psu_of_case4 (hn : 1 ≤ S.width) {m : ℕ} (hm : 4 ≤ m)
    (hmodel : fischerCentralQuotientModel {g : G | IsConj S.z g}
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    Nonempty (G ≃* timmesfeldPSU (S.width + 2)) := by
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 hmodel
  set ψ := φ.trans (u2Equiv m)
  have hψd : ψ S.z ∈ DG m := by
    rw [← image_DU, ← hφ]
    exact ⟨φ S.z, ⟨S.z, IsConj.refl _, rfl⟩, rfl⟩
  obtain ⟨e, he0, he, hed⟩ := hψd
  set T := S.map ψ
  have hTz : T.z = tq e := hed.symm
  have hTw : T.width = S.width := by
    refine T.width_eq ?_
    rw [← S.card_Q_eq]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  have h1 := AS35U.width_add_two_le hm T (by omega) he0 he hTz
  have h2 := AS35U.add_two_le_width hm T he0 he hTz
  obtain rfl : m = S.width + 2 := by omega
  exact ⟨ψ.trans (AS35U.pgEquiv (by omega))⟩

end CFSG.LargeExtraspecial.Setting
