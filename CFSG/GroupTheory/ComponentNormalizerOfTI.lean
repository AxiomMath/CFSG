module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSwap
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLift
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E2Comp
public import CFSG.RankThree.PartTwo.Sec11.Item116TheoremO

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

theorem le_normalizer_of_isComponent_of_centralizer_le {V K : Subgroup X}
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hV : 2 < Nat.card V)
    (hC : ∀ v ∈ V, v ≠ 1 →
      Subgroup.centralizer ({v} : Set X) ≤ Subgroup.normalizer (V : Set X))
    (hK : CFSG.IsComponent K) : V ≤ Subgroup.normalizer (K : Set X) := by
  classical
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have ha1 : a⁻¹ = a :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hV2 a ha)
    have hb1 : b⁻¹ = b :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hV2 b hb)
    have hab : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hV2 (a * b) (V.mul_mem ha hb))
    rw [mul_inv_rev, ha1, hb1] at hab
    exact hab.symm
  by_contra hnot
  have hnot' : ¬ (V : Set X) ⊆ (Subgroup.normalizer (K : Set X) : Set X) := hnot
  obtain ⟨v, hvV, hvN⟩ := Set.not_subset.mp hnot'
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hvN (Subgroup.one_mem _)
  let c : MulAut X := MulAut.conj v
  have hv2 : v * v = 1 := by simpa [pow_two] using hV2 v hvV
  have hc_sq : c * c = 1 := by
    calc c * c = MulAut.conj (v * v) := by simp [c]
      _ = MulAut.conj (1 : X) := by rw [hv2]
      _ = 1 := map_one _
  have hc_apply_sq : ∀ x : X, c (c x) = x := by
    intro x
    have hx : (c * c) x = x := by rw [hc_sq, MulAut.one_apply]
    simpa [MulAut.coe_mul] using hx
  let Kv : Subgroup X := K.map c.toMonoidHom
  have hKv : CFSG.IsComponent Kv :=
    CFSG.LocalCores.isComponent_map_mulEquiv c hK
  have hKv_ne : Kv ≠ K := by
    intro heq
    apply hvN
    exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := K) (g := v)).mpr
      (by simpa [Kv, c] using heq)
  have hKu_inv : ∀ u ∈ V,
      (K.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u).toMonoidHom = K := by
    intro u hu
    rw [Subgroup.map_conj_map_conj]
    have hu2 : u * u = 1 := by simpa [pow_two] using hV2 u hu
    rw [hu2, map_one]
    change K.map (MonoidHom.id X) = K
    exact Subgroup.map_id K
  have hcent_comp (J L : Subgroup X) (hJ : CFSG.IsComponent J) (hL : CFSG.IsComponent L)
      (hne : J ≠ L) : L ≤ Subgroup.centralizer (J : Set X) := by
    have hcomm : ⁅J, L⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hJ hL).resolve_left hne
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcomm_comp (J L : Subgroup X) (hJ : CFSG.IsComponent J) (hL : CFSG.IsComponent L)
      (hne : J ≠ L) : ∀ j ∈ J, ∀ l ∈ L, j * l = l * j := by
    intro j hj l hl
    exact Subgroup.mem_centralizer_iff.mp (hcent_comp J L hJ hL hne hl) j hj
  have hK_le_cent_Kv : K ≤ Subgroup.centralizer (Kv : Set X) :=
    hcent_comp Kv K hKv hK hKv_ne
  let φ : ↥K →* X :=
    { toFun := fun k => (k : X) * c (k : X)
      map_one' := by simp
      map_mul' := by
        intro a b
        have hav : c (a : X) ∈ Kv := Subgroup.mem_map_of_mem c.toMonoidHom a.2
        have hcomm : c (a : X) * (b : X) = (b : X) * c (a : X) :=
          Subgroup.mem_centralizer_iff.mp (hK_le_cent_Kv b.2) (c (a : X)) hav
        simp only [Subgroup.coe_mul, map_mul]
        calc (a : X) * (b : X) * (c (a : X) * c (b : X))
            = (a : X) * ((b : X) * c (a : X)) * c (b : X) := by group
          _ = (a : X) * (c (a : X) * (b : X)) * c (b : X) := by rw [← hcomm]
          _ = ((a : X) * c (a : X)) * ((b : X) * c (b : X)) := by group }
  have hphi_cent : ∀ k : ↥K, φ k ∈ Subgroup.centralizer ({v} : Set X) := by
    intro k
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have hcomm : (k : X) * c (k : X) = c (k : X) * (k : X) :=
      hcomm_comp K Kv hK hKv hKv_ne.symm (k : X) k.2 (c (k : X))
        (Subgroup.mem_map_of_mem c.toMonoidHom k.2)
    have hconj : c (φ k) = φ k := by
      calc c (φ k) = c (k : X) * c (c (k : X)) := by simp [φ]
        _ = c (k : X) * (k : X) := by rw [hc_apply_sq]
        _ = (k : X) * c (k : X) := hcomm.symm
    have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have hconj' : v * φ k * v⁻¹ = φ k := by
      simpa [c, MulAut.conj_apply, hv_inv] using hconj
    calc v * φ k = (v * φ k * v⁻¹) * v := by group
      _ = φ k * v := by rw [hconj']
  have hphiN : ∀ k : ↥K, φ k ∈ Subgroup.normalizer (V : Set X) :=
    fun k => hC v hvV hv1 (hphi_cent k)
  have key : (∀ k : ↥K, (k ^ 2 : ↥K) ∈ Subgroup.center ↥K) → False := fun h => by
    refine CFSG.GH74.GLS.Stage2.Signalizer.Odd87.not_isPGroup_quotient_center Nat.prime_two hK.1
      fun x => ⟨1, ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    rw [pow_one, ← map_pow]
    exact (QuotientGroup.eq_one_iff (y ^ 2)).mpr (h y)
  have hfactor : ∀ (w : X) (hwV : w ∈ V) (k : ↥K),
      w⁻¹ * (φ k)⁻¹ * w * (φ k) =
        ((MulAut.conj (w * v)) (k : X))⁻¹ *
          ((MulAut.conj w) (k : X))⁻¹ * (k : X) * c (k : X) := by
    intro w hwV k
    have hw2 : w * w = 1 := by simpa [pow_two] using hV2 w hwV
    have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have hD : w⁻¹ * (c (k : X))⁻¹ * w = (MulAut.conj (w * v) (k : X))⁻¹ := by
      simp only [c, MulAut.conj_apply]
      group
      simp only [zpow_neg_one]
      rw [hw_inv, hv_inv]
    have hC : w⁻¹ * (k : X)⁻¹ * w = (MulAut.conj w (k : X))⁻¹ := by
      simp only [MulAut.conj_apply]
      group
      simp only [zpow_neg_one]
      rw [hw_inv]
    calc w⁻¹ * (φ k)⁻¹ * w * (φ k)
        = (w⁻¹ * (c (k : X))⁻¹ * w) * (w⁻¹ * (k : X)⁻¹ * w) * (k : X) * c (k : X) := by
          rw [show φ k = (k : X) * c (k : X) from rfl]
          group
      _ = (MulAut.conj (w * v) (k : X))⁻¹ * (MulAut.conj w (k : X))⁻¹ * (k : X) *
            c (k : X) := by rw [hD, hC]
  by_cases hcaseA : ∃ w ∈ V, K.map (MulAut.conj w).toMonoidHom ≠ K ∧
      K.map (MulAut.conj w).toMonoidHom ≠ Kv
  ·
    obtain ⟨w, hwV, hwK, hwKv⟩ := hcaseA
    let Kw : Subgroup X := K.map (MulAut.conj w).toMonoidHom
    let Kvw : Subgroup X := K.map (MulAut.conj (w * v)).toMonoidHom
    have hKw : CFSG.IsComponent Kw :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj w) hK
    have hKvw : CFSG.IsComponent Kvw :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (w * v)) hK
    have hw2 : w * w = 1 := by simpa [pow_two] using hV2 w hwV
    have hKvw_map_v : Kvw.map (MulAut.conj v).toMonoidHom = Kw := by
      rw [show Kvw = K.map (MulAut.conj (w * v)).toMonoidHom from rfl]
      rw [Subgroup.map_conj_map_conj]
      have harg : v * (w * v) = w := by
        calc v * (w * v) = (v * w) * v := by group
          _ = (w * v) * v := by rw [hVcomm v hvV w hwV]
          _ = w := by rw [mul_assoc, hv2, mul_one]
      rw [harg]
    have hKvw_map_w : Kvw.map (MulAut.conj w).toMonoidHom = Kv := by
      rw [show Kvw = K.map (MulAut.conj (w * v)).toMonoidHom from rfl]
      rw [Subgroup.map_conj_map_conj]
      have harg : w * (w * v) = v := by
        calc w * (w * v) = (w * w) * v := by group
          _ = v := by rw [hw2, one_mul]
      rw [harg]
    have hKvw_ne_K : Kvw ≠ K := by
      intro heq
      apply hwKv
      calc Kw = Kvw.map (MulAut.conj v).toMonoidHom := hKvw_map_v.symm
        _ = K.map (MulAut.conj v).toMonoidHom := by rw [heq]
        _ = Kv := rfl
    have hKvw_ne_Kv : Kvw ≠ Kv := by
      intro heq
      apply hwK
      calc Kw = Kvw.map (MulAut.conj v).toMonoidHom := hKvw_map_v.symm
        _ = Kv.map (MulAut.conj v).toMonoidHom := by rw [heq]
        _ = K := hKu_inv v hvV
    have hKvw_ne_Kw : Kvw ≠ Kw := by
      intro heq
      apply hKv_ne
      calc Kv = Kvw.map (MulAut.conj w).toMonoidHom := hKvw_map_w.symm
        _ = Kw.map (MulAut.conj w).toMonoidHom := by rw [heq]
        _ = K := hKu_inv w hwV
    have hcomm_AK : ∀ a ∈ Kvw, ∀ b ∈ K, a * b = b * a :=
      hcomm_comp Kvw K hKvw hK hKvw_ne_K
    have hcomm_BK : ∀ a ∈ Kw, ∀ b ∈ K, a * b = b * a :=
      hcomm_comp Kw K hKw hK hwK
    have hcomm_DK : ∀ a ∈ Kv, ∀ b ∈ K, a * b = b * a :=
      hcomm_comp Kv K hKv hK hKv_ne
    have hsq_center : ∀ k : ↥K, (k ^ 2 : ↥K) ∈ Subgroup.center ↥K := by
      intro k
      let A : X := ((MulAut.conj (w * v)) (k : X))⁻¹
      let B : X := ((MulAut.conj w) (k : X))⁻¹
      let C : X := (k : X)
      let D : X := c (k : X)
      let x : X := w⁻¹ * (φ k)⁻¹ * w * (φ k)
      have hx_eq : x = A * B * C * D := by
        have h := hfactor w hwV k
        simp only [x, A, B, C, D]
        exact h
      have hxV : x ∈ V := by
        have hmem : (φ k)⁻¹ * w * (φ k) ∈ V :=
          (Subgroup.mem_normalizer_iff''.mp (hphiN k) w).mp hwV
        have hxform : x = w⁻¹ * ((φ k)⁻¹ * w * (φ k)) := by
          simp only [x]; group
        rw [hxform]
        exact V.mul_mem (V.inv_mem hwV) hmem
      have hx2 : x ^ 2 = 1 := by simpa [pow_two] using hV2 x hxV
      have hA_mem : A ∈ Kvw :=
        Kvw.inv_mem (Subgroup.mem_map_of_mem (MulAut.conj (w * v)).toMonoidHom k.2)
      have hB_mem : B ∈ Kw :=
        Kw.inv_mem (Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom k.2)
      have hC_mem : C ∈ K := k.2
      have hD_mem : D ∈ Kv := Subgroup.mem_map_of_mem c.toMonoidHom k.2
      have hAB : Commute A B :=
        hcomm_comp Kvw Kw hKvw hKw hKvw_ne_Kw A hA_mem B hB_mem
      have hAC : Commute A C :=
        hcomm_comp Kvw K hKvw hK hKvw_ne_K A hA_mem C hC_mem
      have hAD : Commute A D :=
        hcomm_comp Kvw Kv hKvw hKv hKvw_ne_Kv A hA_mem D hD_mem
      have hBC : Commute B C :=
        hcomm_comp Kw K hKw hK hwK B hB_mem C hC_mem
      have hBD : Commute B D :=
        hcomm_comp Kw Kv hKw hKv hwKv B hB_mem D hD_mem
      have hCD : Commute C D :=
        hcomm_comp K Kv hK hKv hKv_ne.symm C hC_mem D hD_mem
      have hABC_D : Commute (A * B * C) D := (hAD.mul_left hBD).mul_left hCD
      have hAB_C : Commute (A * B) C := hAC.mul_left hBC
      have hx2exp : x ^ 2 = A ^ 2 * B ^ 2 * C ^ 2 * D ^ 2 := by
        rw [hx_eq, Commute.mul_pow hABC_D, Commute.mul_pow hAB_C, Commute.mul_pow hAB]
      have hprod : A ^ 2 * B ^ 2 * C ^ 2 * D ^ 2 = 1 := by
        rw [← hx2exp]
        exact hx2
      have hD2inv : A ^ 2 * B ^ 2 * C ^ 2 = (D ^ 2)⁻¹ :=
        eq_inv_of_mul_eq_one_left hprod
      have hC2 : C ^ 2 = (A ^ 2 * B ^ 2)⁻¹ * (D ^ 2)⁻¹ := by
        calc C ^ 2 = (A ^ 2 * B ^ 2)⁻¹ * (A ^ 2 * B ^ 2 * C ^ 2) := by group
          _ = (A ^ 2 * B ^ 2)⁻¹ * (D ^ 2)⁻¹ := by rw [hD2inv]
      have hcent_Kvw_K : Kvw ≤ Subgroup.centralizer (K : Set X) :=
        hcent_comp K Kvw hK hKvw hKvw_ne_K.symm
      have hcent_Kw_K : Kw ≤ Subgroup.centralizer (K : Set X) :=
        hcent_comp K Kw hK hKw hwK.symm
      have hcent_Kv_K : Kv ≤ Subgroup.centralizer (K : Set X) :=
        hcent_comp K Kv hK hKv hKv_ne.symm
      have hA2_cent : A ^ 2 ∈ Subgroup.centralizer (K : Set X) :=
        hcent_Kvw_K (Kvw.pow_mem hA_mem 2)
      have hB2_cent : B ^ 2 ∈ Subgroup.centralizer (K : Set X) :=
        hcent_Kw_K (Kw.pow_mem hB_mem 2)
      have hD2_cent : D ^ 2 ∈ Subgroup.centralizer (K : Set X) :=
        hcent_Kv_K (Kv.pow_mem hD_mem 2)
      have hAB_cent : A ^ 2 * B ^ 2 ∈ Subgroup.centralizer (K : Set X) :=
        (Subgroup.centralizer (K : Set X)).mul_mem hA2_cent hB2_cent
      have hABinv_cent : (A ^ 2 * B ^ 2)⁻¹ ∈ Subgroup.centralizer (K : Set X) :=
        (Subgroup.centralizer (K : Set X)).inv_mem hAB_cent
      have hDinv_cent : (D ^ 2)⁻¹ ∈ Subgroup.centralizer (K : Set X) :=
        (Subgroup.centralizer (K : Set X)).inv_mem hD2_cent
      have hC2_cent : C ^ 2 ∈ Subgroup.centralizer (K : Set X) := by
        rw [hC2]
        exact (Subgroup.centralizer (K : Set X)).mul_mem hABinv_cent hDinv_cent
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simpa [C] using Subgroup.mem_centralizer_iff.mp hC2_cent (y : X) y.2
    exact key hsq_center
  ·
    have hcaseB : ∀ u ∈ V, K.map (MulAut.conj u).toMonoidHom = K ∨
        K.map (MulAut.conj u).toMonoidHom = Kv := by
      intro u hu
      by_contra hcon
      push Not at hcon
      exact hcaseA ⟨u, hu, hcon.1, hcon.2⟩
    have hexists : ∃ w ∈ V, w ∈ Subgroup.normalizer (K : Set X) ∧ w ≠ 1 := by
      have hex : ∃ u ∈ V, u ≠ 1 ∧ u ≠ v := by
        by_contra hcon
        push Not at hcon
        have hsub : V ≤ Subgroup.zpowers v := by
          intro u hu
          by_cases hu1 : u = 1
          · rw [hu1]
            exact Subgroup.one_mem _
          · rw [hcon u hu hu1]
            exact Subgroup.mem_zpowers v
        have hcard : Nat.card V ≤ 2 := by
          have hle : Nat.card V ≤ Nat.card (Subgroup.zpowers v) :=
            Subgroup.card_le_of_le hsub
          have hzv : Nat.card (Subgroup.zpowers v) ≤ 2 := by
            rw [Nat.card_zpowers]
            have hdvd : orderOf v ∣ 2 :=
              orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hv2)
            have hle2 : orderOf v ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
            omega
          omega
        omega
      obtain ⟨u, huV, hu1, hu_ne_v⟩ := hex
      rcases hcaseB u huV with huK | huKv
      · exact ⟨u, huV, by rwa [Subgroup.mem_normalizer_iff_map_conj_eq], hu1⟩
      · have hwmem : v * u ∈ Subgroup.normalizer (K : Set X) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          calc K.map (MulAut.conj (v * u)).toMonoidHom
              = (K.map (MulAut.conj u).toMonoidHom).map
                  (MulAut.conj v).toMonoidHom := by
                rw [← Subgroup.map_conj_map_conj]
            _ = Kv.map (MulAut.conj v).toMonoidHom := by rw [huKv]
            _ = K := by simpa [Kv, c] using hKu_inv v hvV
        refine ⟨v * u, V.mul_mem hvV huV, hwmem, ?_⟩
        intro hvu
        apply hu_ne_v
        calc u = u * (v * v) := by rw [hv2, mul_one]
          _ = (u * v) * v := by group
          _ = v := by rw [hVcomm u huV v hvV, hvu, one_mul]
    obtain ⟨w, hwV, hwN, hw1⟩ := hexists
    have hw2 : w * w = 1 := by simpa [pow_two] using hV2 w hwV
    have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hwK : K.map (MulAut.conj w).toMonoidHom = K :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := K) (g := w)).mp hwN
    have hwKv : Kv.map (MulAut.conj w).toMonoidHom = Kv := by
      calc Kv.map (MulAut.conj w).toMonoidHom
          = (K.map (MulAut.conj v).toMonoidHom).map (MulAut.conj w).toMonoidHom := rfl
        _ = K.map (MulAut.conj (w * v)).toMonoidHom := by
              rw [Subgroup.map_conj_map_conj]
        _ = K.map (MulAut.conj (v * w)).toMonoidHom := by
              rw [hVcomm w hwV v hvV]
        _ = (K.map (MulAut.conj w).toMonoidHom).map (MulAut.conj v).toMonoidHom := by
              rw [Subgroup.map_conj_map_conj]
        _ = K.map (MulAut.conj v).toMonoidHom := by rw [hwK]
        _ = Kv := rfl
    have hkw_mem : ∀ k : ↥K, MulAut.conj w (k : X) ∈ K := by
      intro k
      have hmem : MulAut.conj w (k : X) ∈ K.map (MulAut.conj w).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom k.2
      rwa [hwK] at hmem
    let κ : ↥K →* ↥K :=
      { toFun := fun k => ⟨MulAut.conj w (k : X), hkw_mem k⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp [map_mul] }
    have hphi_w : ∀ k : ↥K, w⁻¹ * φ k * w = φ (κ k) := by
      intro k
      have hconj_comm : MulAut.conj v * MulAut.conj w =
          MulAut.conj w * MulAut.conj v := by
        calc MulAut.conj v * MulAut.conj w = MulAut.conj (v * w) :=
              (map_mul (MulAut.conj) v w).symm
          _ = MulAut.conj (w * v) := by rw [hVcomm v hvV w hwV]
          _ = MulAut.conj w * MulAut.conj v := map_mul (MulAut.conj) w v
      have h1 : w⁻¹ * (k : X) * w = MulAut.conj w (k : X) := by
        simp [MulAut.conj_apply, hw_inv]
      have h2 : w⁻¹ * (c (k : X)) * w = c (MulAut.conj w (k : X)) := by
        calc w⁻¹ * (c (k : X)) * w =
            ((MulAut.conj w) * c) (k : X) := by
              simp [MulAut.conj_apply, hw_inv, MulAut.coe_mul]
          _ = (c * (MulAut.conj w)) (k : X) := by rw [hconj_comm.symm]
          _ = c (MulAut.conj w (k : X)) := by simp [MulAut.coe_mul]
      calc w⁻¹ * φ k * w
          = (w⁻¹ * (k : X) * w) * (w⁻¹ * (c (k : X)) * w) := by
              rw [show φ k = (k : X) * c (k : X) from rfl]
              group
        _ = MulAut.conj w (k : X) * c (MulAut.conj w (k : X)) := by rw [h1, h2]
        _ = φ (κ k) := rfl
    let N : Subgroup ↥K := V.comap φ
    have hNnormal : N.Normal := by
      refine Subgroup.Normal.mk ?_
      intro n hn g
      rw [Subgroup.mem_comap] at hn ⊢
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hphiN g) (φ n)).mp hn
    by_cases hNtop : N = ⊤
    ·
      have hsq_center : ∀ k : ↥K, (k ^ 2 : ↥K) ∈ Subgroup.center ↥K := by
        intro k
        have hφV : φ k ∈ V := by
          have hk : k ∈ N := by rw [hNtop]; exact Subgroup.mem_top k
          exact hk
        have hφ2 : (φ k) ^ 2 = 1 := by simpa [pow_two] using hV2 (φ k) hφV
        have hcomm : (k : X) * c (k : X) = c (k : X) * (k : X) :=
          hcomm_comp K Kv hK hKv hKv_ne.symm (k : X) k.2 (c (k : X))
            (Subgroup.mem_map_of_mem c.toMonoidHom k.2)
        have hEq : (k : X) ^ 2 * (c (k : X)) ^ 2 = 1 := by
          rw [← Commute.mul_pow hcomm 2]
          simpa [φ] using hφ2
        have hk2_mem : (k : X) ^ 2 ∈ Kv := by
          rw [eq_inv_of_mul_eq_one_left hEq]
          exact Kv.inv_mem (Kv.pow_mem (Subgroup.mem_map_of_mem c.toMonoidHom k.2) 2)
        have hcent_Kv_K : Kv ≤ Subgroup.centralizer (K : Set X) :=
          hcent_comp K Kv hK hKv hKv_ne.symm
        have hk2_cent : (k : X) ^ 2 ∈ Subgroup.centralizer (K : Set X) :=
          hcent_Kv_K hk2_mem
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        simpa using Subgroup.mem_centralizer_iff.mp hk2_cent (y : X) y.2
      exact key hsq_center
    ·
      have hNle : N ≤ Subgroup.center ↥K := by
        rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hNnormal with htop | hle
        · exact absurd htop hNtop
        · exact hle
      have hpsi_mem_N : ∀ k : ↥K, (κ k)⁻¹ * k ∈ N := by
        intro k
        rw [Subgroup.mem_comap]
        have hmem : (φ k)⁻¹ * w * (φ k) ∈ V :=
          (Subgroup.mem_normalizer_iff''.mp (hphiN k) w).mp hwV
        have hxform : φ ((κ k)⁻¹ * k) = w⁻¹ * ((φ k)⁻¹ * w * (φ k)) := by
          rw [map_mul, map_inv, ← hphi_w]
          group
        rw [hxform]
        exact V.mul_mem (V.inv_mem hwV) hmem
      have hpsi_center : ∀ k : ↥K, (κ k)⁻¹ * k ∈ Subgroup.center ↥K :=
        fun k => hNle (hpsi_mem_N k)
      have hcommZ : ∀ k ∈ K, ⁅k, w⁆ ∈
          CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Zsub K := by
        intro k hk
        let kK : ↥K := ⟨k, hk⟩
        have hz : (↑((κ kK)⁻¹ * kK) : X) ∈
            CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Zsub K := by
          rw [CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.mem_Zsub]
          exact ⟨((κ kK)⁻¹ * kK : ↥K).2, hpsi_center kK⟩
        have hconj := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.conj_mem_Zsub hz
          (Subgroup.le_normalizer hk)
        have hκ : ((κ kK : ↥K) : X) = w * k * w⁻¹ := by
          simp [κ, MulAut.conj_apply, kK]
        have hzval : (↑((κ kK)⁻¹ * kK) : X) = w * k⁻¹ * w * k := by
          rw [show (↑((κ kK)⁻¹ * kK) : X) = ((κ kK : ↥K) : X)⁻¹ * k from rfl, hκ]
          simp only [mul_inv_rev, inv_inv, hw_inv]
          group
        have hEq : ⁅k, w⁆ = k * (↑((κ kK)⁻¹ * kK) : X) * k⁻¹ := by
          rw [commutatorElement_def, hzval, hw_inv]
          group
        rw [hEq]
        exact hconj
      haveI : Group.IsPerfect ↥K := hK.1.1
      have hwcent : w ∈ Subgroup.centralizer (K : Set X) :=
        CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.mem_centralizer_of_comm_mem_Zsub hwN hcommZ
      have hK_cent_w : K ≤ Subgroup.centralizer ({w} : Set X) := by
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst h
        exact (Subgroup.mem_centralizer_iff.mp hwcent k hk).symm
      have hK_NV : K ≤ Subgroup.normalizer (V : Set X) :=
        hK_cent_w.trans (hC w hwV hw1)
      have hVsolv : Group.IsSolvable ↥V :=
        Group.isSolvable_of_comm fun a b => Subtype.ext (hVcomm a a.2 b b.2)
      have hcommKV : ⁅K, V⁆ = ⊥ :=
        CFSG.RankThree.PartTwo.Sec11.TheoremO.commutator_eq_bot_of_isComponent_le_normalizer
          hK hVsolv hK_NV
      have hVK : ⁅V, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm V K]
        exact hcommKV
      have hVcent : V ≤ Subgroup.centralizer (K : Set X) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := V) (H₂ := K)).mp hVK
      exact hvN (Subgroup.centralizer_le_normalizer (K : Set X) (hVcent hvV))

section

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_isComponent_inf_centralizer_eq_bot {V : Subgroup Y}
    (hO2 : CFSG.pCore 2 Y = ⊥) (hVp : IsPGroup 2 V) (hVne : V ≠ ⊥)
    (hC : ∀ v ∈ V, v ≠ 1 →
      Subgroup.centralizer ({v} : Set Y) ≤ Subgroup.normalizer (V : Set Y))
    (hO : CFSG.pPrimeCore 2 Y ≤ Subgroup.centralizer (V : Set Y)) :
    ∃ K : Subgroup Y, CFSG.IsComponent K ∧ V ⊓ Subgroup.centralizer (K : Set Y) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2' : CFSG.Open.pCoreOf 2 (⊤ : Subgroup Y) = ⊥ := by
    have h := CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := Y))
    rw [hO2, Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at h
    simp [CFSG.Open.pCoreOf, h]
  have hOdd : V ≤ Subgroup.centralizer (CFSG.oddCore Y : Set Y) := by
    rw [(CFSG.oddCore_eq_piCore Y).trans (CFSG.pPrimeCore_eq_piCore Y 2).symm]
    exact Subgroup.le_centralizer_iff.mp hO
  obtain ⟨K, hK, hKV⟩ :=
    CFSG.Quasithin.H13.Ch4.E443.exists_isComponent_commutator_ne_bot hVp hVne hO2' hOdd
  refine ⟨K, hK, eq_bot_iff.mpr fun v ⟨hvV, hvC⟩ => ?_⟩
  by_contra hv1
  have hKC : K ≤ Subgroup.centralizer ({v} : Set Y) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hvC k hk)
  have : Group.IsNilpotent V := hVp.isNilpotent
  exact hKV (CFSG.RankThree.PartTwo.Sec11.TheoremO.commutator_eq_bot_of_isComponent_le_normalizer
    hK inferInstance (hKC.trans (hC v hvV hv1)))

end

end CFSG.GroupTheory
