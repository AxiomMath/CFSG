module

public import CFSG.GH74.GLS.IVK.L2.Lemma13f
public import CFSG.GH74.GLS.IVK.L2.GroupAux
public import CFSG.GH74.GLS.IVK.L2.DihedralAux2
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

theorem ivk_1_2i_b : IVK_1_2i_b := by
  intro F _ _ hF K _ _ e N f hf hf2
  obtain ⟨n, hn⟩ : ∃ n, Nat.card N.P = 2 ^ n := ⟨_, card_P_eq e N⟩
  have hn3 := three_le_of_involution_mem_R hF N hf hf2 n hn
  obtain ⟨z, hzP, hz1, hzz, hzc⟩ := P_exists_central_involution hF N n hn hn3
  have hF1 := fInvNotCentPt F hF K e N f hf hf2
  have key := f_conj_t hF N n hn hf hf2 hF1 hzP hz1 hzc
  have htz := t_comm_z hF N n hn hn3 hzP hz1 hzc
  have hPT : N.P ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hPinn : N.P ≤ innAut K := inf_le_right
  have hfT : f ∈ (N.T : Subgroup (MulAut K)) := hf.1
  have hfF : f ∈ fieldAutSub e := hf.2
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, pow_two] at this
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have htt : N.t * N.t = 1 := by
    have := pow_orderOf_eq_one N.t
    rwa [N.t_order, pow_two] at this
  obtain ⟨g, hg⟩ : ∃ g : MulAut K, g = f * N.t := ⟨_, rfl⟩
  have hgT : g ∈ (N.T : Subgroup (MulAut K)) := hg ▸ Subgroup.mul_mem _ hfT N.t_mem
  have hgnorm : g ∈ normalizer (N.P : Set (MulAut K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact conj_mem_P N hgT hh
    · intro hh
      have := conj_mem_P N ((N.T : Subgroup (MulAut K)).inv_mem hgT) hh
      simpa [mul_assoc] using this
  have hg2 : g * g = z := by
    rw [hg]
    calc f * N.t * (f * N.t) = (f * N.t * f⁻¹) * N.t := by rw [hfinv]; group
      _ = N.t * z * N.t := by rw [key]
      _ = z * (N.t * N.t) := by
        have : N.t * z = z * N.t := by
          have h1 := htz
          calc N.t * z = N.t * z * N.t⁻¹ * N.t := by group
            _ = z * N.t := by rw [h1]
        calc N.t * z * N.t = z * N.t * N.t := by rw [this]
          _ = z * (N.t * N.t) := by group
      _ = z := by rw [htt, mul_one]
  have hfpt : fieldProj e N.t = 1 := (mem_innDiagSub_iff e _).mp N.t_mem_diag
  obtain ⟨σ, hσ⟩ : ∃ σ : F ≃+* F, σ = fieldProj e f := ⟨_, rfl⟩
  have hfσ : f = fieldAutHom e σ := by
    obtain ⟨τ, hτ⟩ := hfF
    rw [hσ, ← hτ, fieldProj_fieldAutHom]
  have hσ1 : σ ≠ 1 := by
    intro h
    have : f = 1 := by rw [hfσ, h, map_one]
    rw [this, orderOf_one] at hf2
    omega
  have hσ2 : σ * σ = 1 := by
    have : fieldProj e (f * f) = 1 := by rw [hff, map_one]
    rw [map_mul, ← hσ] at this
    exact this
  have hfg : fieldProj e g = σ := by rw [hg, map_mul, hfpt, mul_one, hσ]
  set S : Subgroup (MulAut K) := N.P ⊔ zpowers g with hS
  have hST : S ≤ (N.T : Subgroup (MulAut K)) :=
    sup_le hPT (Subgroup.zpowers_le.mpr hgT)
  have hS2 : IsPGroup 2 ↥S := N.T.isPGroup'.to_le hST
  have hzpow : ∀ m : ℤ, z ^ m ∈ N.P := fun m => Subgroup.zpow_mem _ hzP m
  have hg2z : g ^ 2 = z := by rw [pow_two, hg2]
  have hgpow : ∀ k : ℤ, (Even k → g ^ k ∈ N.P) ∧ (Odd k → ∃ p ∈ N.P, g ^ k = p * g) := by
    intro k
    constructor
    · rintro ⟨m, rfl⟩
      rw [← two_mul, zpow_mul]
      have : g ^ (2 : ℤ) = z := by rw [zpow_ofNat, hg2z]
      rw [this]
      exact hzpow m
    · rintro ⟨m, rfl⟩
      refine ⟨z ^ m, hzpow m, ?_⟩
      rw [zpow_add_one, zpow_mul]
      have : g ^ (2 : ℤ) = z := by rw [zpow_ofNat, hg2z]
      rw [this]
  have hfieldpow : ∀ k : ℤ, fieldProj e (g ^ k) = σ ^ k := by
    intro k; rw [map_zpow, hfg]
  have hσpow : ∀ k : ℤ, (Even k → σ ^ k = 1) ∧ (Odd k → σ ^ k = σ) := by
    intro k
    constructor
    · rintro ⟨m, rfl⟩
      rw [← two_mul, zpow_mul]
      have : σ ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two, hσ2]
      rw [this, one_zpow]
    · rintro ⟨m, rfl⟩
      rw [zpow_add_one, zpow_mul]
      have : σ ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two, hσ2]
      rw [this, one_zpow, one_mul]
  have hS1 : ∀ x ∈ S, (fieldProj e x = 1 → x ∈ N.P) ∧
      (fieldProj e x ≠ 1 → ∃ p ∈ N.P, x = p * g) := by
    intro x hx
    obtain ⟨p, hp, k, rfl⟩ := (mem_sup_zpowers_iff hgnorm).mp hx
    have hpf : fieldProj e p = 1 := (mem_innDiagSub_iff e p).mp
      (innAut_le_innDiagSub e (hPinn hp))
    have hxf : fieldProj e (p * g ^ k) = σ ^ k := by
      rw [map_mul, hpf, one_mul, hfieldpow]
    rcases Int.even_or_odd k with hk | hk
    · refine ⟨fun _ => N.P.mul_mem hp ((hgpow k).1 hk), fun h => absurd ?_ h⟩
      rw [hxf]; exact (hσpow k).1 hk
    · obtain ⟨p', hp', hgk⟩ := (hgpow k).2 hk
      refine ⟨fun h => ?_, fun _ => ⟨p * p', N.P.mul_mem hp hp', by rw [hgk]; group⟩⟩
      exfalso
      rw [hxf, (hσpow k).2 hk] at h
      exact hσ1 h
  have htP : N.t ∉ N.P := fun h => N.t_not_mem_inn (hPinn h)
  have hinvP : ∀ x ∈ S, orderOf x = 2 → x ∈ N.P := by
    intro x hxS hx2
    by_contra hxP
    have hxf : fieldProj e x ≠ 1 := fun h => hxP ((hS1 x hxS).1 h)
    obtain ⟨p, hp, hxpg⟩ := (hS1 x hxS).2 hxf
    rcases ivk_1_2i_c F hF K e N f hf hf2 x (hST hxS) hx2 with h | ⟨h, -⟩ | ⟨p', hp', hxp'⟩
    · exact hxP h
    · exact hxf ((mem_innDiagSub_iff e x).mp (Pt_le_innDiagSub N h))
    · apply htP
      have h1 : p * (f * N.t) = p' * f := by rw [← hg, ← hxpg, hxp']
      have h2 : N.t = f * (p⁻¹ * p') * f⁻¹ := by
        calc N.t = f⁻¹ * p⁻¹ * (p * (f * N.t)) := by group
          _ = f⁻¹ * p⁻¹ * (p' * f) := by rw [h1]
          _ = f * (p⁻¹ * p') * f⁻¹ := by rw [hfinv]; group
      rw [h2]
      exact conj_mem_P N hfT (N.P.mul_mem (N.P.inv_mem hp) hp')
  have hnotD : ¬ ∃ n' : ℕ, 2 ≤ n' ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ (n' - 1))) := by
    rintro ⟨n', -, ⟨φ⟩⟩
    have hSP : S ≤ N.P := DihedralAux.le_of_involutions_le S N.P φ hinvP
    have hgP : g ∈ N.P := hSP (Subgroup.mem_sup_right (mem_zpowers g))
    have : fieldProj e g = 1 :=
      (mem_innDiagSub_iff e g).mp (innAut_le_innDiagSub e (hPinn hgP))
    rw [hfg] at this
    exact hσ1 this
  obtain ⟨U, hUle, hU4, hUcent⟩ := N.four_cent
  have hUP : U ≤ N.P := hUle
  have hUinn : U ≤ innAut K := hUle.trans inf_le_right
  have hUS : U ≤ S := hUP.trans le_sup_left
  obtain ⟨hcomm, hsq⟩ := isFourSubgroup_props hU4
  have hcU := centralizer_four_inf_innDiagSub e hF U hUinn hU4
  have hcentS : ∀ x ∈ S, (∀ u ∈ U, u * x = x * u) → x ∈ U := by
    intro x hxS hxc
    obtain ⟨φ, hφ⟩ : ∃ φ : MulAut K, φ = fieldAutHom e (fieldProj e x) := ⟨_, rfl⟩
    have hφF : φ ∈ fieldAutSub e := hφ ▸ ⟨_, rfl⟩
    have hφC : ∀ u ∈ U, u * φ = φ * u := fun u hu => (hUcent φ hφF u hu).symm
    obtain ⟨y, hy⟩ : ∃ y : MulAut K, y = x * φ⁻¹ := ⟨_, rfl⟩
    have hyU : y ∈ U := by
      rw [← hcU]
      refine ⟨Subgroup.mem_centralizer_iff.mpr (fun u hu => ?_),
        (mem_innDiagSub_iff e _).mpr ?_⟩
      · have hinv : φ⁻¹ * u = u * φ⁻¹ := by
          calc φ⁻¹ * u = φ⁻¹ * (u * φ) * φ⁻¹ := by group
            _ = φ⁻¹ * (φ * u) * φ⁻¹ := by rw [hφC u hu]
            _ = u * φ⁻¹ := by group
        rw [hy]
        calc u * (x * φ⁻¹) = (u * x) * φ⁻¹ := by group
          _ = (x * u) * φ⁻¹ := by rw [hxc u hu]
          _ = x * (u * φ⁻¹) := by group
          _ = x * (φ⁻¹ * u) := by rw [hinv]
          _ = (x * φ⁻¹) * u := by group
      · rw [hy, map_mul, map_inv, hφ, fieldProj_fieldAutHom, mul_inv_cancel]
    have hφS : φ ∈ S := by
      have : φ = y⁻¹ * x := by rw [hy]; group
      rw [this]
      exact S.mul_mem (S.inv_mem (hUS hyU)) hxS
    have hφ1 : φ = 1 := by
      by_cases h1 : fieldProj e φ = 1
      · have : φ = fieldAutHom e (fieldProj e φ) := by rw [hφ, fieldProj_fieldAutHom]
        rw [this, h1, map_one]
      · exfalso
        obtain ⟨p, hp, hφpg⟩ := (hS1 φ hφS).2 h1
        have hσφ : fieldProj e φ = σ := by
          rw [hφpg, map_mul, hfg, (mem_innDiagSub_iff e p).mp
            (innAut_le_innDiagSub e (hPinn hp)), one_mul]
        have hφf : φ = f := by
          have : φ = fieldAutHom e (fieldProj e φ) := by rw [hφ, fieldProj_fieldAutHom]
          rw [this, hσφ, hfσ]
        apply htP
        have h2 : N.t = f * p⁻¹ * f⁻¹ := by
          calc N.t = f⁻¹ * p⁻¹ * (p * (f * N.t)) := by group
            _ = f⁻¹ * p⁻¹ * f := by rw [← hg, ← hφpg, hφf]
            _ = f * p⁻¹ * f⁻¹ := by rw [hfinv]
        rw [h2]
        exact conj_mem_P N hfT (N.P.inv_mem hp)
    have : x = y * φ := by rw [hy]; group
    rw [this, hφ1, mul_one]
    exact hyU
  let V : Subgroup ↥S := U.subgroupOf S
  have hVcard : Nat.card V = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv).trans hU4.2
  have hVab : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm _ a.2 _ b.2))⟩⟩
  have hVexp : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    apply Subtype.ext
    have := hsq _ hv
    simpa [pow_two] using this
  have hcentV : Subgroup.centralizer (V : Set ↥S) = V := by
    apply le_antisymm
    · intro x hx
      exact hcentS x x.2 (fun u hu => congrArg (fun a : ↥S => (a : MulAut K))
        (Subgroup.mem_centralizer_iff.mp hx ⟨u, hUS hu⟩ hu))
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (hcomm _ hy _ hx)
  have hSgoal : N.P ⊔ zpowers (f * N.t) = S := by rw [hS, hg]
  rcases CFSG.RankTwoShapes.selfCentralizing_four_shapes hS2 V hVab hVexp hVcard hcentV with
    hD | ⟨n', hn', ⟨iso⟩⟩
  · exact absurd hD hnotD
  · rw [hSgoal]
    exact ⟨n', hn', ⟨iso⟩⟩

end CFSG.GH74.GLS.IVK
