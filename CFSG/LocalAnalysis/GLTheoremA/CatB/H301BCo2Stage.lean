module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2Tr
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2Max
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2K0
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2Syl
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFpfA6
import CFSG.LargeExtraspecial.BridgeNat

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Stage

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.Yardstones.Md0ec50421ce4
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2I301
open CFSG.Sporadic.Co2Schreier hiding dP

theorem eq_one_or_of_mem_zpowers_of_sq {G : Type*} [Group G] {a w : G} (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) (hw : w ∈ Subgroup.zpowers a) : w = 1 ∨ w = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have ho : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  rw [← zpow_mod_orderOf, ho]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem mul_comm_of_mem_normalizer_zpowers {G : Type*} [Group G] {a g : G} (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    g * a = a * g := by
  have h := (Subgroup.mem_normalizer_iff.1 hg a).1 (Subgroup.mem_zpowers a)
  rcases eq_one_or_of_mem_zpowers_of_sq ha2 ha1 h with h1 | h1
  · exact absurd (by simpa using h1) ha1
  · calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h1]

theorem exists_zpowers_of_card_two {G : Type*} [Group G] {R0 : Subgroup G}
    (h : Nat.card R0 = 2) : ∃ a : G, a ^ 2 = 1 ∧ a ≠ 1 ∧ R0 = Subgroup.zpowers a := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : R0)).1 h
  have hyy : y * y = 1 := by
    by_contra hne
    have h1 := huniq _ hne
    exact hy (by calc y = y⁻¹ * (y * y) := by group
                  _ = y⁻¹ * y := by rw [h1]
                  _ = 1 := by group)
  refine ⟨(y : G), by rw [pow_two]; exact congrArg Subtype.val hyy,
    fun h1 => hy (Subtype.ext h1), le_antisymm (fun r hr => ?_) (Subgroup.zpowers_le.2 y.2)⟩
  by_cases hr1 : (⟨r, hr⟩ : R0) = 1
  · rw [show r = 1 from congrArg Subtype.val hr1]
    exact Subgroup.one_mem _
  · rw [show r = (y : G) from congrArg Subtype.val (huniq _ hr1)]
    exact Subgroup.mem_zpowers _

theorem map_conj_le {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P)
    {H : Subgroup (Equiv.Perm (Fin 2300))} (hH : H ≤ co2P) :
    H.map (MulAut.conj g).toMonoidHom ≤ co2P := by
  rintro _ ⟨x, hx, rfl⟩
  exact co2P.mul_mem (co2P.mul_mem hg (hH hx)) (co2P.inv_mem hg)

theorem isExtraSpec2_of_map {G H : Type} [Group G] [Group H] (ψ : G →* H)
    (hψ : Function.Injective ψ) {R : Subgroup G} (h : IsExtraSpec2 (R.map ψ)) :
    IsExtraSpec2 R :=
  (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_congr
    (Subgroup.equivMapOfInjective R ψ hψ)).2 h

theorem isExtraSpec2_locQ :
    IsExtraSpec2 locQ := by
  obtain ⟨h2, hc, hf, hz⟩ := CFSG.Monster.Existence.IsExtraspecialPGroup.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe locQ_le_C) qc_extraspecial
  exact ⟨h2, hc.trans hf.symm, hf, hz⟩

theorem k1_mul_k2_ne_one :
    k1P * k2P ≠ 1 := by
  intro h
  have h0 : (k1P * k2P) (o6P 0) = o6P 0 := by rw [h]; rfl
  rw [Equiv.Perm.mul_apply, k2P_o6P, k1P_o6P] at h0
  have h1 := o6P_injective h0
  revert h1
  decide

section Stage


private theorem dP_sq_sq : (dP ^ 2) ^ 2 = dP := by
  rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, pow_facts.1, one_mul]

theorem stage_d {B K R1 : Subgroup (Equiv.Perm (Fin 2300))} {y : Equiv.Perm (Fin 2300)}
    (h : Co2Hyp B K (Subgroup.zpowers locZ) R1 y) (hy : y = dP ∨ y = dP ^ 2)
    (hKP : K ≤ co2P) (hR1P : R1 ≤ co2P) : R1 = locQ := by
  have hKz : ∀ k ∈ K, k * locZ = locZ * k := fun k hk =>
    mul_comm_of_mem_normalizer_zpowers locZ_sq locZ_ne_one (h.norm_R0 (Subgroup.mem_sup_left hk))
  have hKd : ∀ k ∈ K, k * dP = dP * k := by
    intro k hk
    have hky : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent hk)
    rcases hy with rfl | rfl
    · exact hky
    · have h2 := (show Commute k (dP ^ 2) from hky).pow_right 2
      rw [dP_sq_sq] at h2
      exact h2
  have hdB : dP ∈ B := by
    rcases hy with rfl | rfl
    · exact h.mem_B
    · have h2 := pow_mem h.mem_B 2
      rwa [dP_sq_sq] at h2
  have hK0 : K0 ≤ K := Co2K0.K0_le_of_quotient_A6 hKP
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hKd k hk))
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hKz k hk)) h.maps_A6
  have hk1 : k1P ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hk2 : k2P ∈ K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact Co2Max.eq_locQ_of_gt_locZ R1 hR1P h.pgroup_R1 h.lt
    (h.norm_R1 (Subgroup.mem_sup_left (hK0 hk1))) (h.norm_R1 (Subgroup.mem_sup_left (hK0 hk2)))
    (h.norm_R1 (Subgroup.mem_sup_right hdB))

theorem stage_z {B K R1 : Subgroup (Equiv.Perm (Fin 2300))} {y : Equiv.Perm (Fin 2300)}
    (h : Co2Hyp B K (Subgroup.zpowers locZ) R1 y) (hBP : B ≤ co2P) (hKP : K ≤ co2P)
    (hR1P : R1 ≤ co2P) : IsExtraSpec2 R1 := by
  have hcent : ∀ g ∈ K ⊔ B, g * locZ = locZ * g := fun g hg =>
    mul_comm_of_mem_normalizer_zpowers locZ_sq locZ_ne_one (h.norm_R0 hg)
  have hCmem : ∀ g ∈ K ⊔ B, g ∈ co2P → g ∈ locC := fun g hg hgP => by
    rw [locC_eq_centralizer]
    exact Subgroup.mem_inf.2 ⟨hgP, Subgroup.mem_centralizer_singleton_iff.2 (hcent g hg)⟩
  have hKC : ∀ k ∈ K, k ∈ locC := fun k hk => hCmem k (Subgroup.mem_sup_left hk) (hKP hk)
  have hBC : ∀ b ∈ B, b ∈ locC := fun b hb => hCmem b (Subgroup.mem_sup_right hb) (hBP hb)
  have hy3 : y ^ 3 = 1 := h.elem.2 y h.mem_B
  obtain ⟨i, hi, f, hf⟩ := h.maps_A6
  have hcat : catalogIs i.Group S8.isA6 := ⟨i, hi, ⟨MulEquiv.refl _⟩⟩
  have h5K : 5 ∣ Nat.card K :=
    (I2016Sp.a6_data hcat).2.1.trans (Subgroup.card_dvd_of_surjective hf)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5 h5K
  obtain ⟨hdC, -, -, -, hk1C, hk2C⟩ := gens_mem_locC
  obtain ⟨hc5, hsix⟩ := Co2Six.six_x0_facts ⟨k1P, hk1C⟩ ⟨k2P, hk2C⟩ ⟨dP, hdC⟩ rfl rfl rfl
  have hx0 : orderOf ((⟨k1P, hk1C⟩ : locC) * ⟨k2P, hk2C⟩) = 5 :=
    orderOf_eq_prime hc5 (fun h1 => k1_mul_k2_ne_one (congrArg Subtype.val h1))
  have hd3 : (⟨dP, hdC⟩ : locC) ^ 3 = 1 := Subtype.ext (by simpa using pow_facts.1)
  have hker : (toPerm63.comp sixAction).ker = locQ.subgroupOf locC := by
    rw [← sixAction_ker]
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_eq_one_iff toPerm63 toPerm63_injective
  have h25 : ¬ 25 ∣ Nat.card locC := by
    rw [card_locC]
    norm_num
  have hx5' : orderOf (⟨(x : Equiv.Perm (Fin 2300)), hKC x x.2⟩ : locC) = 5 := by
    rw [← Subgroup.orderOf_coe (⟨(x : Equiv.Perm (Fin 2300)), hKC x x.2⟩ : locC)]
    exact (Subgroup.orderOf_coe x).trans hx5
  have hxy : Commute (⟨(x : Equiv.Perm (Fin 2300)), hKC x x.2⟩ : locC)
      (⟨y, hBC y h.mem_B⟩ : locC) :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent x.2))
  obtain ⟨c, hc⟩ := Co2Syl.exists_conj_five_three (toPerm63.comp sixAction)
    (hker ▸ isPGroup_qc) h25 hx0 hd3 hsix (Subtype.ext (by simpa using hy3))
    (fun h1 => h.ne_one (congrArg Subtype.val h1)) hx5' hxy
  set ψ : Equiv.Perm (Fin 2300) →* Equiv.Perm (Fin 2300) :=
    (MulAut.conj (c : Equiv.Perm (Fin 2300))).toMonoidHom with hψdef
  have hψ : Function.Injective ψ := (MulAut.conj (c : Equiv.Perm (Fin 2300))).injective
  have hcz : (c : Equiv.Perm (Fin 2300)) * locZ = locZ * c :=
    Subgroup.mem_centralizer_singleton_iff.1 (locC_le_centralizer c.2)
  have hψz : ψ locZ = locZ := by
    show (c : Equiv.Perm (Fin 2300)) * locZ * (c : Equiv.Perm (Fin 2300))⁻¹ = locZ
    rw [hcz]
    group
  have h' := h.map ψ hψ
  rw [MonoidHom.map_zpowers, hψz] at h'
  have hψy : ψ y = (c : Equiv.Perm (Fin 2300)) * y * (c : Equiv.Perm (Fin 2300))⁻¹ := rfl
  have hy' : ψ y = dP ∨ ψ y = dP ^ 2 := by
    rw [hψy]
    rcases hc with hc | hc
    · exact Or.inl (by simpa using congrArg (fun t : locC => (t : Equiv.Perm (Fin 2300))) hc)
    · exact Or.inr (by simpa using congrArg (fun t : locC => (t : Equiv.Perm (Fin 2300))) hc)
  have hcP : (c : Equiv.Perm (Fin 2300)) ∈ co2P := locC_le_P c.2
  have hR : R1.map ψ = locQ := stage_d h' hy' (map_conj_le hcP hKP) (map_conj_le hcP hR1P)
  refine isExtraSpec2_of_map ψ hψ ?_
  rw [hR]
  exact isExtraSpec2_locQ

end Stage

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Stage

end
