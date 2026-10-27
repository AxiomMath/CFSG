module

public import CFSG.LargeExtraspecial.S12InspPSUW4
public import CFSG.LargeExtraspecial.S12I4MLines
public import CFSG.LargeExtraspecial.S12I4MPSU
public import CFSG.LargeExtraspecial.S12I4MVec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Open
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

namespace S12I4M

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_psu_four {g : G} {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hw : S.width = 4) (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hred : ¬ S.IsReducible12)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4)
        fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (h3 : ∀ y ∈ S.Xbar12 g, y ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) →
      y ^ 3 = 1 → y ≠ 1 → ∃ x ∈ S.Xbar12 g, x ∈ S.Lbar g ∧
        x ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∧ x * y ≠ y * x) : False := by
  have hn : 3 ≤ S.width := by omega
  have hq := S.q_nondegenerate
  have hat : S.cl (g * S.z * g⁻¹) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    (S.timmesfeld_12_6 haQ hne ht htA).1
  obtain ⟨ψ, hψE, hψt⟩ := Setting.exists_psu_mulEquiv_v₀ ht htA (k := 2) (by norm_num) hmod
  obtain ⟨χ, hχ⟩ : ∃ χ : PG 4 →* S.O, χ = (S.Xbar12 g).subtype.comp ψ.symm.toMonoidHom :=
    ⟨_, rfl⟩
  have hχX : ∀ q, χ q ∈ S.Xbar12 g := fun q => by rw [hχ]; exact (ψ.symm q).2
  have hχM : ∀ q, χ q ∈ S.Mbar := fun q => Setting.Xbar12_le_Mbar (hχX q)
  have hχinj : Function.Injective χ := by
    rw [hχ]
    exact (S.Xbar12 g).subtype_injective.comp ψ.symm.injective
  have hχψ : ∀ x : S.Xbar12 g, χ (ψ x) = x := fun x => by
    rw [hχ]
    simp
  have hχt : χ (tq (v₀ 2)) = t := by rw [← hψt, hχψ]
  have hχE : ∀ q ∈ DG 4, χ q ∈ S.Ebar12 g := fun q hq => by
    have hχq : χ q = ψ.symm q := by rw [hχ]; rfl
    rw [hχq]
    exact (hψE (ψ.symm q)).2 (by rw [MulEquiv.apply_symm_apply]; exact hq)
  have hEχ : ∀ τ ∈ S.Ebar12 g, ∃ q ∈ DG 4, χ q = τ := fun τ hτ =>
    ⟨ψ ⟨τ, Setting.subset_Xbar12 hτ⟩, (hψE _).1 hτ, hχψ _⟩
  have hA : ∀ q ∈ DG 4, IsTypeA S.q (χ q : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := fun q hq =>
    Setting.isTypeA_of_mem_Ebar12 (hχE q hq)
  have hinv : ∀ v : Fin 4 → K, herm frob v v = 0 → (χ (tq v))⁻¹ = χ (tq v) := fun v hv => by
    rw [← map_inv, inv_eq_of_mul_eq_one_right (tq_mul_self hv)]
  have hv₀D : tq (v₀ 2) ∈ DG 4 := tq_mem_DG v₀_ne_zero herm_v₀_v₀
  have hK : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 →
      χ (tq (ι 2 z)) ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    intro z hz0 hz
    obtain ⟨-, horth⟩ := polar_eq_zero_of_commute hχE hEχ hred hw hv₀D (tq_ι_mem_DG hz0 hz)
      (tq_v₀_ne_ι hz0 hz) (commute_v₀_ι hz)
    rw [hχt] at horth
    exact Setting.mem_fixSub12.mpr fun w hw =>
      apply_eq_of_polar hq (hA _ (tq_ι_mem_DG hz0 hz)) fun x hx => horth w hw x hx
  have hfixa : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 →
      (χ (tq (ι 2 z)) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    fun z hz0 hz => Setting.mem_fixSub12.mp (hK z hz0 hz) _ hat
  have hnormL : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → ∀ s ∈ S.Lbar g,
      χ (tq (ι 2 z)) * s * (χ (tq (ι 2 z)))⁻¹ ∈ S.Lbar g := fun z hz0 hz s hs =>
    (mem_normalizer_iff.mp ((Setting.mem_normalizer_Lbar_iff_fix haQ hne hn (hχM _)).mpr
      (hfixa z hz0 hz)) s).mp hs
  have hk2 : 2 ≤ 2 := le_rfl
  obtain ⟨z₂, hz₂0, hz₂, hz₁₂⟩ := exists_partner_frob (isoVec_ne_zero hk2) (isoVec_isotropic hk2)
  have hz₁0 := isoVec_ne_zero hk2
  have hz₁ := isoVec_isotropic hk2
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : PG 4, y₀ = tq (ι 2 (isoVec hk2)) * tq (ι 2 z₂) := ⟨_, rfl⟩
  have hy₀3 : orderOf y₀ = 3 := by
    rw [hy₀]
    exact orderOf_tq_mul_tq_eq_three (ι_ne_zero hz₁0) (ι_ne_zero hz₂0)
      (by rw [herm_ι_ι, hz₁]) (by rw [herm_ι_ι, hz₂]) (by rw [herm_ι_ι, hz₁₂]; exact one_ne_zero)
  have hy₀t : y₀ * tq (v₀ 2) = tq (v₀ 2) * y₀ := by
    rw [hy₀, mul_assoc, ← commute_v₀_ι hz₂, ← mul_assoc, ← commute_v₀_ι hz₁, mul_assoc]
  obtain ⟨x, hxX, hxL, -, hxy⟩ := h3 (χ y₀) (hχX _)
    (by rw [hy₀, map_mul]; exact mul_mem (hK _ hz₁0 hz₁) (hK _ hz₂0 hz₂))
    (by rw [← map_pow, ← hy₀3, pow_orderOf_eq_one, map_one])
    (fun e => by
      have : y₀ = 1 := hχinj (by rw [e, map_one])
      rw [this, orderOf_one] at hy₀3
      exact absurd hy₀3 (by norm_num))
  have hEA := S.isElementaryAbelian_Lbar haQ
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (PG 4), N = (S.Lbar g).comap χ := ⟨_, rfl⟩
  have hNsq : ∀ n ∈ N, n * n = 1 := fun n hn' => hχinj (by
    rw [map_mul, map_one]
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S.Lbar g) (χ n)
      (Subgroup.mem_comap.mp (hN ▸ hn'))
    rw [← pow_two]
    simpa using this)
  have hNt : ∀ n ∈ N, n * tq (v₀ 2) = tq (v₀ 2) * n := fun n hn' => hχinj (by
    rw [map_mul, map_mul, hχt]
    exact congrArg Subtype.val (hEA.is_comm.comm ⟨χ n, Subgroup.mem_comap.mp (hN ▸ hn')⟩ ⟨t, ht⟩))
  have hNn : ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → ∀ n ∈ N,
      tq (ι 2 z) * n * tq (ι 2 z) ∈ N := fun z hz0 hz n hn' => by
    have hιz : herm frob (ι 2 z) (ι 2 z) = 0 := by rw [herm_ι_ι, hz]
    have e : χ (tq (ι 2 z) * n * tq (ι 2 z)) =
        χ (tq (ι 2 z)) * χ n * (χ (tq (ι 2 z)))⁻¹ := by
      rw [map_mul, map_mul, hinv (ι 2 z) hιz]
    rw [hN]
    refine Subgroup.mem_comap.mpr ?_
    rw [e]
    exact hnormL z hz0 hz _ (Subgroup.mem_comap.mp (hN ▸ hn'))
  have hxN : ψ ⟨x, hxX⟩ ∈ N := by
    rw [hN]
    refine Subgroup.mem_comap.mpr ?_
    rw [hχψ]
    exact hxL
  have hyχ : x * χ y₀ ≠ χ y₀ * x := hxy
  have hχx : χ (ψ ⟨x, hxX⟩) = x := hχψ ⟨x, hxX⟩
  obtain ⟨d, hd0, hdd, hρL⟩ : ∃ d : Fin 2 → K, d ≠ 0 ∧ herm frob d d = 0 ∧
      χ (tq (ω • v₀ 2 + ι 2 d) * tq (frob ω • v₀ 2 + ι 2 d)) ∈ S.Lbar g := by
    rcases eq_of_normalized hNsq hNt hNn _ hxN with h1 | h1 | ⟨d, hd0, hdd, h1 | h1⟩
    · exfalso
      have : x = 1 := by rw [← hχx, h1, map_one]
      exact hyχ (by rw [this, one_mul, mul_one])
    · exfalso
      have : x = t := by rw [← hχx, h1, hχt]
      apply hyχ
      rw [this, ← hχt, ← map_mul, ← map_mul, hy₀t]
    · refine ⟨d, hd0, hdd, ?_⟩
      rw [← h1, hχx]
      exact hxL
    · refine ⟨d, hd0, hdd, ?_⟩
      have e : tq (ω • v₀ 2 + ι 2 d) * tq (frob ω • v₀ 2 + ι 2 d) = ψ ⟨x, hxX⟩ * tq (v₀ 2) := by
        rw [h1, mul_assoc, tq_mul_self herm_v₀_v₀, mul_one]
      rw [e, map_mul, hχx, hχt]
      exact (S.Lbar g).mul_mem hxL ht
  have hD4 := tq_lin_mem_DG ω hd0 hdd
  have hD5 := tq_lin_mem_DG (frob ω) hd0 hdd
  obtain ⟨hd45, ho45⟩ := polar_eq_zero_of_commute hχE hEχ hred hw hD4 hD5
    (tq_lin_ne_lin hd0 hdd) (commute_lin_lin ω (frob ω) hdd)
  obtain ⟨hd4, ho4⟩ := polar_eq_zero_of_commute hχE hEχ hred hw hv₀D hD4
    (tq_v₀_ne_lin ω hd0 hdd) (commute_v₀_lin ω hdd)
  obtain ⟨hd5, ho5⟩ := polar_eq_zero_of_commute hχE hEχ hred hw hv₀D hD5
    (tq_v₀_ne_lin (frob ω) hd0 hdd) (commute_v₀_lin (frob ω) hdd)
  rw [hχt] at hd4 ho4 hd5 ho5
  have h4 := hA _ hD4
  have h5 := hA _ hD5
  have hle := le_sup_of_isotropic hq (by rw [S.finrank_Qt_eq_two_mul_width, hw]) h4.2.2.2.1
    h5.2.2.2.1 hd45 (fun x hx y hy => polar_eq_zero_of_isTypeA htA hx hy)
    (fun x hx y hy => polar_eq_zero_of_isTypeA h4 hx hy)
    (fun x hx y hy => polar_eq_zero_of_isTypeA h5 hx hy) ho4 ho5 ho45
  obtain ⟨u, hu0, hu, hdu⟩ := exists_partner_frob hd0 hdd
  have hιu : herm frob (ι 2 u) (ι 2 u) = 0 := by rw [herm_ι_ι, hu]
  have hρ : χ (tq (ω • v₀ 2 + ι 2 d)) * χ (tq (frob ω • v₀ 2 + ι 2 d)) ∈ S.Lbar g := by
    rw [← map_mul]
    exact hρL
  have hρ' := hnormL u hu0 hu _ hρ
  have hD' : tq (ι 2 u) * tq (ω • v₀ 2 + ι 2 d) * tq (ι 2 u) ∈ DG 4 := by
    rw [tq_mul_tq_mul_tq hιu (isotropic_lin hdd ω)]
    exact tq_mem_DG ((smul_ne_zero_iff_ne _).2 (lin_ne_zero ω hd0))
      (by rw [herm_smul_smul, isotropic_lin hdd ω])
  have he : χ (tq (ι 2 u)) * χ (tq (ω • v₀ 2 + ι 2 d)) * (χ (tq (ι 2 u)))⁻¹ =
      χ (tq (ι 2 u) * tq (ω • v₀ 2 + ι 2 d) * tq (ι 2 u)) := by
    rw [hinv _ hιu, map_mul, map_mul]
  have hopp : commSpace ((χ (tq (ι 2 u)) * χ (tq (ω • v₀ 2 + ι 2 d)) *
      (χ (tq (ι 2 u)))⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      LinearMap.BilinForm.orthogonal S.q.polarBilin
        (commSpace (χ (tq (ω • v₀ 2 + ι 2 d)) : S.Qt ≃ₗ[ZMod 2] S.Qt)) = ⊥ := by
    rw [he]
    refine (orderOf_mul_eq_three_iff_of_isTypeA hq (hA _ hD') h4).mp ?_
    rw [← Subgroup.coe_mul, ← map_mul, orderOf_submonoid, orderOf_injective χ hχinj]
    exact orderOf_conj_lin_mul_lin_eq_three hd0 hdd hu hdu
  obtain ⟨hℓE, h4E⟩ := le_clSub_and_four_le haQ hne htA hat h4 h5 hρ hρ' (hfixa u hu0 hu)
    hd45 ho45 hd4 hd5 hle hopp
  exact false_of_le_clSub haQ hne hw ht htA hℓE h4E

end S12I4M

theorem insp4FischerResidual4 : Insp4FischerResidual4 :=
  fun _ _ _ _ _ _ _ haQ hne hw _ _ ht htA _ hred _ hmod h3 =>
    (S12I4M.false_of_psu_four haQ hne hw ht htA hred hmod h3).elim

theorem insp4FischerResidual3 : Insp4FischerResidual3 :=
  insp4FischerResidual3_of_4 insp4FischerResidual4

theorem insp4FischerResidual2 : Insp4FischerResidual2 :=
  insp4FischerResidual2_of_3 insp4FischerResidual3

end CFSG.LargeExtraspecial
