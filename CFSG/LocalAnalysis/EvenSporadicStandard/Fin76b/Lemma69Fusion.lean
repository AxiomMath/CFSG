module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69Def

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem exists_involution_ne_of_dihedral {H : Type*} [Group H] (f : H ≃* DihedralGroup 4)
    (t : H) : ∃ e : H, e * e = 1 ∧ e ≠ 1 ∧ e ≠ t := by
  have hinv : ∀ d : DihedralGroup 4, d * d = 1 → d ≠ 1 →
      f.symm d * f.symm d = 1 ∧ f.symm d ≠ 1 := fun d hd hd1 =>
    ⟨by rw [← map_mul, hd, map_one], by rwa [Ne, MulEquiv.map_eq_one_iff]⟩
  by_cases h : f.symm (DihedralGroup.sr 0) = t
  · obtain ⟨h1, h2⟩ := hinv (DihedralGroup.sr 1) (DihedralGroup.sr_mul_self 1) (by decide)
    refine ⟨_, h1, h2, fun h' => ?_⟩
    rw [← h] at h'
    exact absurd (f.symm.injective h') (by decide)
  · obtain ⟨h1, h2⟩ := hinv (DihedralGroup.sr 0) (DihedralGroup.sr_mul_self 0) (by decide)
    exact ⟨_, h1, h2, h⟩

theorem mk_mem_of_mem_commutator {K : Type*} [Group K] {N : Subgroup K} [N.Normal]
    {H : Subgroup (K ⧸ N)} (hidx : H.index = 2) {d : K} (hd : d ∈ _root_.commutator K) :
    (QuotientGroup.mk d : K ⧸ N) ∈ H := by
  apply commutator_le_of_index_two hidx
  have := map_derivedSeries_le_derivedSeries (QuotientGroup.mk' N) 1
  rw [derivedSeries_one, derivedSeries_one] at this
  exact this ⟨d, hd, rfl⟩

section Wreath

variable {K : Type*} [Group K] [Finite K] {z : K} {N₁ N₂ : Subgroup (K ⧸ fusionOddCore K)}
  {D : Subgroup K}

theorem nonempty_dihedral_of_wreath (hz2 : z * z = 1) (e₁ : ↥N₁ ≃* alternatingGroup (Fin 6))
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : Disjoint N₁ N₂)
    (hidx : (N₁ ⊔ N₂).index = 2)
    (hconj : N₁.map (MulAut.conj (QuotientGroup.mk z : K ⧸ fusionOddCore K)).toMonoidHom = N₂)
    (hD8 : Nat.card D = 8) (hD2 : IsPGroup 2 D) (hDK : D ≤ _root_.commutator K)
    (hDz : ∀ x ∈ D, z * x = x * z) : Nonempty (↥D ≃* DihedralGroup 4) := by
  classical
  let q : K →* K ⧸ fusionOddCore K := QuotientGroup.mk' (fusionOddCore K)
  let σ : K ⧸ fusionOddCore K := QuotientGroup.mk z
  have hσ2 : σ * σ = 1 := by
    show (QuotientGroup.mk z : K ⧸ fusionOddCore K) * QuotientGroup.mk z = 1
    rw [← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]
  have hW : WreathData N₁ N₂ σ := wreathData_of_conj hσ2 hcomm hdisj hconj
  let P : Subgroup (K ⧸ fusionOddCore K) := D.map q
  obtain ⟨eDP⟩ := exists_equiv_map_quotient hD2
  have hPN : P ≤ N₁ ⊔ N₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_of_mem_commutator hidx (hDK hx)
  have hPσ : ∀ x ∈ P, σ * x * σ⁻¹ = x := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : z * x * z⁻¹ = x := by rw [hDz x hx]; group
    calc σ * q x * σ⁻¹ = q (z * x * z⁻¹) := by rw [map_mul, map_mul, map_inv]; rfl
      _ = q x := by rw [h1]
  let P₁ : Subgroup ↥N₁ := P.comap hW.diag
  have hmap : P₁.map hW.diag = P := by
    apply Subgroup.map_comap_eq_self
    intro x hx
    obtain ⟨a, ha⟩ := hW.mem_diag_of_comm (hPN hx) (hPσ x hx)
    exact ⟨a, ha⟩
  let e₂ : ↥P₁ ≃* ↥P :=
    (P₁.equivMapOfInjective hW.diag hW.diag_injective).trans (MulEquiv.subgroupCongr hmap)
  have hcard : Nat.card (P₁.map e₁.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e₁.injective, Nat.card_congr e₂.toEquiv,
      ← Nat.card_congr eDP.toEquiv, hD8]
  obtain ⟨f⟩ := CFSG.QuasithinUnique.DoubleA3.nonempty_dihedral_of_card_eight _ hcard
  exact ⟨eDP.trans (e₂.symm.trans ((P₁.equivMapOfInjective e₁.toMonoidHom e₁.injective).trans f))⟩

theorem exists_conj_mul_of_wreath (hz2 : z * z = 1)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : Disjoint N₁ N₂)
    (hidx : (N₁ ⊔ N₂).index = 2)
    (hzN : (QuotientGroup.mk z : K ⧸ fusionOddCore K) ∉ N₁ ⊔ N₂)
    (hconj : N₁.map (MulAut.conj (QuotientGroup.mk z : K ⧸ fusionOddCore K)).toMonoidHom = N₂)
    (hDK : D ≤ _root_.commutator K) (hDz : ∀ x ∈ D, z * x = x * z) {e : K} (he : e ∈ D)
    (hee : e * e = 1) : ∃ k : K, k * z * k⁻¹ = z * e := by
  let q : K →* K ⧸ fusionOddCore K := QuotientGroup.mk' (fusionOddCore K)
  let σ : K ⧸ fusionOddCore K := QuotientGroup.mk z
  have hqz : q z = σ := rfl
  have hσ2 : σ * σ = 1 := by
    show (QuotientGroup.mk z : K ⧸ fusionOddCore K) * QuotientGroup.mk z = 1
    rw [← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]
  have hW : WreathData N₁ N₂ σ := wreathData_of_conj hσ2 hcomm hdisj hconj
  have heN : q e ∈ N₁ ⊔ N₂ := mk_mem_of_mem_commutator hidx (hDK he)
  have hez : z * e = e * z := hDz e he
  have hσe : σ * q e * σ⁻¹ = q e := by
    have h1 : z * e * z⁻¹ = e := by rw [hez]; group
    rw [← hqz, ← map_inv, ← map_mul, ← map_mul, h1]
  obtain ⟨a, ha⟩ := hW.mem_diag_of_comm heN hσe
  have haa : (a : K ⧸ fusionOddCore K) * a = 1 := by
    have : a * a = 1 := by
      apply hW.diag_injective
      rw [map_mul, ha, map_one, ← map_mul, hee, map_one]
    exact congrArg Subtype.val this
  have hconjq : (a : K ⧸ fusionOddCore K) * q z * (a : K ⧸ fusionOddCore K)⁻¹ = q (z * e) := by
    rw [inv_eq_of_mul_eq_one_right haa, hqz]
    calc (a : K ⧸ fusionOddCore K) * σ * a = hW.diag a * σ := by
          rw [hW.diag_apply, hW.inv_eq]
          calc (a : K ⧸ fusionOddCore K) * σ * a = a * σ * a * (σ * σ) := by rw [hσ2, mul_one]
            _ = a * (σ * a * σ) * σ := by group
      _ = q (z * e) := by rw [ha, ← hqz, ← map_mul, hez]
  have hz1 : z ≠ 1 := fun h => hzN (by rw [h, QuotientGroup.mk_one]; exact one_mem _)
  have hze1 : z * e ≠ 1 := fun h => hzN (by
    rw [eq_inv_of_mul_eq_one_left h, QuotientGroup.mk_inv]
    exact inv_mem heN)
  have hzinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution z := ⟨hz1, by rw [pow_two, hz2]⟩
  have hzeinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (z * e) := by
    refine ⟨hze1, ?_⟩
    calc (z * e) ^ 2 = z * (e * z) * e := by rw [pow_two]; group
      _ = z * z * (e * e) := by rw [← hez]; group
      _ = 1 := by rw [hz2, hee, one_mul]
  exact CFSG.GorensteinWalter.involutions_conjugate_of_quotient_conjugate_odd_kernel
    (fusionOddCore K) (odd_natCard_fusionOddCore K) hzinv hzeinv ⟨a, hconjq⟩

end Wreath

theorem exists_conj_mul_of_wreathAlt {G : Type*} [Group G] [Finite G] {K E : Subgroup G}
    {z t : G} (hz : z ∈ K) (hz2 : z * z = 1) (htK : t ∈ K) (htE : t ∈ E) (hE2 : IsPGroup 2 E)
    (hEz : ∀ e ∈ E, e * z = z * e) (hD8 : Nat.card ↥(E ⊓ K) = 8)
    (hDK : (E ⊓ K).subgroupOf K ≤ _root_.commutator ↥K)
    (hwr : WreathAlt ↥K (QuotientGroup.mk ⟨z, hz⟩)) :
    ∃ e ∈ E, e * e = 1 ∧ e ≠ 1 ∧ e ≠ t ∧ ∃ g : G, g * z * g⁻¹ = z * e := by
  obtain ⟨N₁, N₂, ⟨e₁⟩, -, hc, hd, -, hidx, hzN, hconj⟩ := hwr
  let zK : ↥K := ⟨z, hz⟩
  let D : Subgroup ↥K := (E ⊓ K).subgroupOf K
  have hD2 : IsPGroup 2 D := (hE2.to_le (inf_le_left : E ⊓ K ≤ E)).comap_subtype
  have hD8' : Nat.card D = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ⊓ K ≤ K)).toEquiv).trans hD8
  have hDz : ∀ d ∈ D, zK * d = d * zK := fun d hd =>
    Subtype.ext (hEz (d : G) (mem_subgroupOf.1 hd).1).symm
  have hz2' : zK * zK = 1 := Subtype.ext hz2
  obtain ⟨f⟩ := nonempty_dihedral_of_wreath hz2' e₁ hc hd hidx hconj hD8' hD2 hDK hDz
  obtain ⟨e, hee, he1, het⟩ := exists_involution_ne_of_dihedral f
    ⟨⟨t, htK⟩, mem_subgroupOf.2 ⟨htE, htK⟩⟩
  have hee' : (e : ↥K) * e = 1 := congrArg Subtype.val hee
  obtain ⟨k, hk⟩ := exists_conj_mul_of_wreath hz2' hc hd hidx hzN hconj hDK hDz e.2 hee'
  refine ⟨((e : ↥K) : G), (mem_subgroupOf.1 e.2).1, congrArg Subtype.val hee', fun h => he1 ?_,
    fun h => het ?_, (k : G), congrArg Subtype.val hk⟩
  · exact Subtype.ext (Subtype.ext h)
  · exact Subtype.ext (Subtype.ext h)

theorem fin76bFusion69 : Fin76bFusion69 := by
  intro G _ _ L z t T₀ E Q x β B hconf _ hBD hwr
  obtain ⟨hz, hwr⟩ := hwr
  obtain ⟨hD8, hDK⟩ := hBD
  have hcfg := hconf.cfg
  have htK : t ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2
      (mem_centralizer_singleton_iff.1 (hconf.B_cent hconf.beta_mem)).symm
  exact exists_conj_mul_of_wreathAlt hz hcfg.z_sq htK hconf.econfig.t_mem
    (hcfg.T₀_pgroup.to_le hconf.econfig.le)
    (fun e he => hcfg.z_comm_of_mem_A (hconf.econfig.le.trans hcfg.T₀_le he)) hD8 hDK hwr

end CFSG.EvenSporadicStandard.Fin76b
