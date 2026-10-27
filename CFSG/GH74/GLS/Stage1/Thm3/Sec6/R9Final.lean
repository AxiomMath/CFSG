module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Glue3
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Count
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Three

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

@[expose] def Prop49_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F →
    Qz S z = F → (∃ n, IVK.IsQuaternionTwoGroup ↥F n) →
      ∀ U : Subgroup G, U ≤ Rz S z → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) →
        ∀ x : G, IsPGroup 3 ↥(zpowers x) →
          x ∈ normalizer ((S ⊓ centralizer (U : Set G) : Subgroup G) : Set G) →
          x ∈ normalizer (U : Set G) → x * z * x⁻¹ ≠ z →
          Nat.card ↥(Pz S z) = Nat.card ↥(Qz S z) → (Rz S z).relIndex S = 2 →
            (∃ y ∈ S, orderOf y = 2 ∧ y ∉ Rz S z ∧
              ∃ n, IVK.IsSemidihedralTwoGroup ↥(Qz S z ⊔ zpowers y) n) ∧
            ∃ q : ℕ, (q % 8 = 3 ∨ q % 8 = 5) ∧ 5 ≤ q ∧
              (∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq), Nat.card Fq = q ∧
                Nonempty (HatT K ≃* IVK.SL2 Fq)) ∧
              IVK.IsQuaternionTwoGroup ↥(Pz S z) 3 ∧ IVK.IsQuaternionTwoGroup ↥(Qz S z) 3 ∧
              HasSL2ProductOfIndexTwoStage1 (oPrimeResidual 2 (CentralizerBar z)) 3 ∧
              ∀ v ∈ Rz S z, v * v = 1 → v ≠ 1 → IsConj z v

theorem Std4r1.hThompson2 (h : Std4r1 G z S K F) {U : Subgroup G} (hUS : U ≤ S) (hU4 : R1.Four U)
    (hUn : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) {u : G} (huU : u ∈ U) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hconj : IsConj z u) :
    ∃ a b : G, a ∈ normalizer ((S ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ∧
      b ∈ normalizer ((S ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ∧
      a * z * a⁻¹ = z ∧ a * u * a⁻¹ = z * u ∧ b * u * b⁻¹ = u ∧ b * z * b⁻¹ = u * z := by
  have hsyl : ¬ 2 ∣ S.index := by
    have := h.S_top.2.2
    simpa [Subgroup.relIndex_top_right] using this
  have hHyp := CFSG.GH74.GLS.Bg.L1621.Hyp.of_cyclic h.S_pgroup h.Z_cyc hUS hUn hU4.2 hU4.1
    h.z_mem_S h.z_sq h.z_ne (fun g hg => (h.z_cent hg).symm) huU hu1 huz
  obtain ⟨a, b, ha, hb, haz, hau, hbu, hbz⟩ :=
    CFSG.GH74.GLS.Bg.L1621.exists_ab hHyp h.S_pgroup hsyl hconj
  exact ⟨a, b, ha, hb, haz, hau, hbu, hbz⟩

theorem caseB_data (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (hlift : II4_ord4_lift) (h : Std4r1 G z S K F) (hQF : Qz S z = F)
    (hquat : ∃ n, IVK.IsQuaternionTwoGroup ↥F n) (hcase : ∃ t ∈ Rz S z, t ≠ z ∧ IsConj z t) :
    ∃ U : Subgroup G, U ≤ Rz S z ∧ IVK.IsFourSubgroup U ∧
      (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) ∧
      ∃ x : G, IsPGroup 3 ↥(zpowers x) ∧
        x ∈ normalizer ((S ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ∧
        x ∈ normalizer (U : Set G) ∧ x * z * x⁻¹ ≠ z ∧ Nat.card ↥(Pz S z) = Nat.card ↥(Qz S z) ∧
        (Rz S z).relIndex S = 2 := by
  classical
  obtain ⟨U, hUR, hU4, hUn, u, huU, hu1, huz, hconj, u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq⟩ :=
    step1_std hII hq hdiag h19 hsd hsdq hqc hrn hlift h hQF hquat hcase
  have hcfg := cfg1K_Q hII hq hdiag h19 hsd hsdq hqc hrn h hQF
  have hF := h.F_eq hQF
  obtain ⟨nQ, hnQ⟩ : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n := hF ▸ hquat
  obtain ⟨nP, hnP⟩ := h.P_quat hq
  have hzQ := h.z_mem_Q hII
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have hUS : U ≤ S := hUR.trans (sup_le hcfg.P_le hcfg.Q_le)
  have hzU : z ∈ U := hcfg.toCfg1.z_mem_four hU4 hUS hUn
  have hu2 : u * u = 1 := hU4.1 u huU
  have hzu : z * u = u * z := h.z_cent (hUS huU)
  have hcases : ∀ v ∈ U, v = 1 ∨ v = z ∨ v = u ∨ v = z * u := fun v hv =>
    R1.Four.mem_cases hU4 hzU huU hz1 hu1 huz hv
  obtain ⟨a, b, ha, hb, haz, hau, hbu, hbz⟩ := h.hThompson2 hUS hU4 hUn huU hu1 huz hconj
  have haU : a ∈ normalizer (U : Set G) :=
    R1.mem_normalizer_of_four hzU huU hcases (by rw [haz]; exact hzU)
      (by rw [hau]; exact mul_mem hzU huU)
  have hbU : b ∈ normalizer (U : Set G) :=
    R1.mem_normalizer_of_four hzU huU hcases (by rw [hbz]; exact mul_mem huU hzU)
      (by rw [hbu]; exact huU)
  set Wsub : Subgroup G := S ⊓ centralizer (U : Set G) with hWdef
  set N : Subgroup G := normalizer (Wsub : Set G) ⊓ normalizer (U : Set G) with hNdef
  have haN : a ∈ N := ⟨ha, haU⟩
  have hbN : b ∈ N := ⟨hb, hbU⟩
  have hgz : (a * b) * z * (a * b)⁻¹ = u := by
    calc (a * b) * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group
      _ = a * (u * z) * a⁻¹ := by rw [hbz]
      _ = (a * u * a⁻¹) * (a * z * a⁻¹) := by group
      _ = (z * u) * z := by rw [hau, haz]
      _ = u := by rw [hzu, mul_assoc, hz2, mul_one]
  have hgu : (a * b) * u * (a * b)⁻¹ = z * u := by
    calc (a * b) * u * (a * b)⁻¹ = a * (b * u * b⁻¹) * a⁻¹ := by group
      _ = a * u * a⁻¹ := by rw [hbu]
      _ = z * u := hau
  obtain ⟨x, hxN, hx3, hxz⟩ :=
    R1.exists_three_elt (N := N) (N.mul_mem haN hbN) hzu hu2 hu1 huz hgz hgu
  have hxW : x ∈ normalizer (Wsub : Set G) := hxN.1
  have hxU : x ∈ normalizer (U : Set G) := hxN.2
  have hnormP : ∀ s ∈ S, s * u₁ * s⁻¹ = u₁ ∨ s * u₁ * s⁻¹ = u₁ * z := fun s hs =>
    (hcfg.toCfg1.conj_comp hUR hU4 hUn huU hu1 huz hu₁P hu₂Q hu hs).1
  have hnormQ : ∀ s ∈ S, s * u₂ * s⁻¹ = u₂ ∨ s * u₂ * s⁻¹ = u₂ * z := fun s hs =>
    (hcfg.toCfg1.conj_comp hUR hU4 hUn huU hu1 huz hu₁P hu₂Q hu hs).2
  obtain ⟨V₁, hV₁eq, hV₁c, hV₁i⟩ := hcfg.toCfg1.P_centr u₁ hu₁P hu₁sq hnormP
  obtain ⟨hV₂c, hV₂i⟩ := hqc G (S ⊓ cSec K) z u₂ nQ hnQ hzQ hz2 hz1 hu₂Q hu₂sq
    (fun q hq => hnormQ q hq.1)
  have hV₁P : V₁ ≤ S ⊓ K := by rw [hV₁eq]; exact inf_le_left
  have hV₁W : V₁ ≤ Wsub := by
    intro v hv
    rw [hV₁eq] at hv
    obtain ⟨hvP, hvC⟩ := hv
    refine ⟨hvP.1, Subgroup.mem_centralizer_iff.2 (fun w hw => ?_)⟩
    have hvu₁ : v * u₁ = u₁ * v := Subgroup.mem_centralizer_singleton_iff.1 hvC
    have hvu₂ : v * u₂ = u₂ * v := h.comm_PQ hvP hu₂Q
    have hvz : z * v = v * z := h.z_cent hvP.1
    have hvu : u * v = v * u := by
      calc u * v = u₁ * u₂ * v := by rw [hu]
        _ = u₁ * (u₂ * v) := by group
        _ = u₁ * (v * u₂) := by rw [hvu₂]
        _ = (u₁ * v) * u₂ := by group
        _ = (v * u₁) * u₂ := by rw [hvu₁]
        _ = v * (u₁ * u₂) := by group
        _ = v * u := by rw [hu]
    rcases hcases w hw with rfl | rfl | rfl | rfl
    · simp
    · exact hvz
    · exact hvu
    · calc (z * u) * v = z * (u * v) := by group
        _ = z * (v * u) := by rw [hvu]
        _ = (z * v) * u := by group
        _ = (v * z) * u := by rw [hvz]
        _ = v * (z * u) := by group
  have hV₂W : (S ⊓ cSec K) ⊓ centralizer ({u₂} : Set G) ≤ Wsub := by
    intro v hv
    obtain ⟨hvQ, hvC⟩ := hv
    refine ⟨hvQ.1, Subgroup.mem_centralizer_iff.2 (fun w hw => ?_)⟩
    have hvu₂ : v * u₂ = u₂ * v := Subgroup.mem_centralizer_singleton_iff.1 hvC
    have hu₁v : u₁ * v = v * u₁ := h.comm_PQ hu₁P hvQ
    have hvz : z * v = v * z := h.z_cent hvQ.1
    have hvu : u * v = v * u := by
      calc u * v = u₁ * u₂ * v := by rw [hu]
        _ = u₁ * (u₂ * v) := by group
        _ = u₁ * (v * u₂) := by rw [← hvu₂]
        _ = (u₁ * v) * u₂ := by group
        _ = (v * u₁) * u₂ := by rw [hu₁v]
        _ = v * (u₁ * u₂) := by group
        _ = v * u := by rw [hu]
    rcases hcases w hw with rfl | rfl | rfl | rfl
    · simp
    · exact hvz
    · exact hvu
    · calc (z * u) * v = z * (u * v) := by group
        _ = z * (v * u) := by rw [hvu]
        _ = (z * v) * u := by group
        _ = (v * z) * u := by rw [hvz]
        _ = v * (z * u) := by group
  have hzV₁ : z ∈ V₁ := by
    rw [hV₁eq]
    exact ⟨h.z_mem_P hII, Subgroup.mem_centralizer_singleton_iff.2 (h.z_cent hu₁P.1)⟩
  have hzV₂ : z ∈ (S ⊓ cSec K) ⊓ centralizer ({u₂} : Set G) :=
    ⟨hzQ, Subgroup.mem_centralizer_singleton_iff.2 (h.z_cent hu₂Q.1)⟩
  obtain ⟨hcard, hidx⟩ := R1.count_AB hcfg.toCfg1 hnP hnQ (V₁ := V₁)
    (V₂ := (S ⊓ cSec K) ⊓ centralizer ({u₂} : Set G)) (W := Wsub) hV₁P hV₁c hV₁i hzV₁ inf_le_left
    hV₂c hV₂i hzV₂ hV₁W hV₂W inf_le_left (x := x)
    (fun w hw => (Subgroup.mem_normalizer_iff.1 hxW w).1 hw) hxz
  refine ⟨U, ?_, ⟨isElemAbelian_of_sq_one hU4.1, hU4.2⟩, hUn, x, hx3, hxW, hxU, hxz, ?_, ?_⟩
  · rw [h.Rz_eq]; exact hUR
  · rw [h.Pz_eq, h.Qz_eq]; exact hcard
  · rw [h.Rz_eq]; exact hidx

theorem prop_4_9 (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (hZsq : Z_not_sq) (hlift : II4_ord4_lift) (hshape : Bg.B_two_maximalClass_shape)
    (hIA : IA_4_5_1) (hrest : Prop49_rest) : Prop4_9 := by
  intro G _ _ z S K F h hQF hquat
  by_cases hcase : ∃ t ∈ Rz S z, t ≠ z ∧ IsConj z t
  · obtain ⟨U, hUR, hU4, hUn, x, hx3, hxW, hxU, hxz, hcard, hidx⟩ :=
      caseB_data hII hq hdiag h19 hsd hsdq hqc hrn hlift h hQF hquat hcase
    obtain ⟨⟨y, hyS, hy2, hyR, nSD, hSDQ⟩, q, hq8, hq5, ⟨Fq, instF, instFin, hFq, hFe⟩, hP3, hQ3,
      hSL2, hRconj⟩ := hrest G z S K F h hQF hquat U hUR hU4 hUn x hx3 hxW hxU hxz hcard hidx
    have hcfg := cfg1K_Q hII hq hdiag h19 hsd hsdq hqc hrn h hQF
    have hRS : Rz S z ≤ S := by rw [h.Rz_eq]; exact sup_le inf_le_left inf_le_left
    refine ⟨q, hq8, hq5, ⟨Fq, instF, instFin, hFq, hFe⟩, hP3, hQ3, ?_⟩
    unfold G2Data
    refine ⟨?_, ?_, hSL2⟩
    · have hSy : S = Rz S z ⊔ zpowers y :=
        B.eq_sup_zpowers_of_relIndex_le_two hRS hidx.le hyS hyR
      have hnfa : ¬ InducesFAut y K := fun hfa => hyR (by
        have := h.inv_fAut y hyS hy2 hfa
        rw [← hQF] at this
        exact this)
      have hSDP := (h19 G z S K h.toStd6r1 y hyS hy2 hyR hnfa).1
      obtain ⟨Gs, instG, instGfin, p, f, hp, hp2, hpf, hLie, S', hS'⟩ :=
        hIA G z S K F h hQF hquat y hyS hy2 hyR hSy hSDP ⟨nSD, hSDQ⟩ hcard Fq instF instFin hFe
      exact ⟨Gs, instG, instGfin, p, f, hp, hp2, hFq ▸ hpf, hLie, S', hS'⟩
    · intro v hv
      have hv2 : v * v = 1 := mul_self_eq_one_of_orderOf_eq_two hv
      have hv1 : v ≠ 1 := ne_one_of_orderOf_eq_two hv
      obtain ⟨P', hP', hvP'⟩ := M.exists_syl2In_ge (M.isPGroup_zpowers_of_sq hv2 hv1)
        (le_top : zpowers v ≤ ⊤)
      obtain ⟨c, -, hc⟩ := h.S_top.exists_conj hP'
      have hv'S : c * v * c⁻¹ ∈ S := by
        have : v ∈ P' := hvP' (mem_zpowers v)
        rw [hc, M.mem_cj] at this
        exact this
      have hv'2 : (c * v * c⁻¹) * (c * v * c⁻¹) = 1 := by
        calc (c * v * c⁻¹) * (c * v * c⁻¹) = c * (v * v) * c⁻¹ := by group
          _ = 1 := by rw [hv2]; group
      have hv'1 : c * v * c⁻¹ ≠ 1 := by
        intro e
        apply hv1
        calc v = c⁻¹ * (c * v * c⁻¹) * c := by group
          _ = 1 := by rw [e]; group
      have hconj_v : IsConj (c * v * c⁻¹) v := isConj_iff.2 ⟨c⁻¹, by group⟩
      suffices hzv' : IsConj z (c * v * c⁻¹) from hzv'.trans hconj_v
      by_cases hv'R : c * v * c⁻¹ ∈ Rz S z
      · exact hRconj _ hv'R hv'2 hv'1
      · have hnormR : ∀ t ∈ S, ∀ r ∈ Rz S z, t * r * t⁻¹ ∈ Rz S z := by
          intro t ht r hr
          rw [h.Rz_eq] at hr ⊢
          exact (mem_normalizer_iff.1 (hcfg.toCfg1.S_le_normalizer_R ht) r).1 hr
        have hNS : Rz S z ≠ S := by
          intro hNS
          have := Subgroup.relIndex_eq_one.2 (le_of_eq hNS.symm : S ≤ Rz S z)
          omega
        have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Rz S z := by
          refine ⟨c * v * c⁻¹, hv'S, fun t ht => ?_⟩
          by_cases htR : t ∈ Rz S z
          · exact ⟨0, by simpa using htR⟩
          · refine ⟨1, ?_⟩
            have hcov := B.mem_or_mul_inv_mem hidx.le hv'S hv'R ht
            have h1 : t * (c * v * c⁻¹)⁻¹ ∈ Rz S z := hcov.resolve_left htR
            have h2 := hnormR (c * v * c⁻¹)⁻¹ (S.inv_mem hv'S) _ h1
            have e : (c * v * c⁻¹)⁻¹ * (t * (c * v * c⁻¹)⁻¹) * (c * v * c⁻¹)⁻¹⁻¹ =
                ((c * v * c⁻¹) ^ (1 : ℤ))⁻¹ * t := by group
            rw [← e]
            exact h2
        obtain ⟨g, hg⟩ := h.hTransfer (Rz S z) hRS hnormR hNS hcyc (c * v * c⁻¹) hv'S hv'2 hv'R
        have hg2 : (g⁻¹ * (c * v * c⁻¹) * g) * (g⁻¹ * (c * v * c⁻¹) * g) = 1 := by
          calc (g⁻¹ * (c * v * c⁻¹) * g) * (g⁻¹ * (c * v * c⁻¹) * g)
              = g⁻¹ * ((c * v * c⁻¹) * (c * v * c⁻¹)) * g := by group
            _ = 1 := by rw [hv'2]; group
        have hg1 : g⁻¹ * (c * v * c⁻¹) * g ≠ 1 := by
          intro e
          apply hv'1
          calc c * v * c⁻¹ = g * (g⁻¹ * (c * v * c⁻¹) * g) * g⁻¹ := by group
            _ = 1 := by rw [e]; group
        have hzr := hRconj _ hg hg2 hg1
        exact hzr.trans (isConj_iff.2 ⟨g, by group⟩ : IsConj (g⁻¹ * (c * v * c⁻¹) * g) (c * v * c⁻¹))
  · exfalso
    push Not at hcase
    exact caseA_std hII hq hdiag h19 hsd hsdq hqc hrn hZsq hshape h hQF hquat
      (fun t ht hconj => by
        by_contra htz
        exact hcase t ht htz hconj)

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
