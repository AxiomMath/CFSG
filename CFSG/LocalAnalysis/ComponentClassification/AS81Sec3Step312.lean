module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step312W
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CentZ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.Open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding Sec3

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem omega_le_range_ρF_of (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hφ : ∃ φ : ↥(sec3F (Q₀ ⊔ Q)) →* ↥(timmesfeldOmegaPlus 4), Function.Surjective φ ∧
      φ.ker = ((Q₀ ⊔ Q) ⊔ AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓
        centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G))).subgroupOf (sec3F (Q₀ ⊔ Q))) :
    omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρF.range := by
  obtain ⟨φ, hφs, hφk⟩ := hφ
  have hk : H.ρF.ker = φ.ker := by rw [H.ker_ρF hQF, hφk]
  have h1 := Subgroup.card_ker_mul_card_range H.ρF
  have h2 := Subgroup.card_ker_mul_card_range φ
  rw [MonoidHom.range_eq_top.mpr hφs, card_top, ← hk] at h2
  have h3 : Nat.card H.ρF.range = Nat.card (timmesfeldOmegaPlus 4) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S14.nonempty_omegaGroup_equiv_omegaPlus
    H.xsub.q_nondegenerate (m := 4) (by rw [H.finrank_Qt]) (by norm_num) H.isPlusType
  have h4 : Nat.card (omegaGroup H.xsub.q H.xsub.q_nondegenerate) =
      Nat.card (timmesfeldOmegaPlus 4) := Nat.card_congr e.toEquiv
  have hle : H.ρF.range ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
    rintro _ ⟨f, rfl⟩
    exact H.ρF_mem_omega f
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, h4])).ge

theorem exists_conj_of_involution
    (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρF.range) {a s : G}
    (haQ : a ∈ Q₀ ⊔ Q) (hsQ : s ∈ Q₀ ⊔ Q) (ha : a * a = 1) (hs : s * s = 1)
    (haz : a ∉ zpowers z) (hsz : s ∉ zpowers z) :
    ∃ f ∈ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G), (f * a * f⁻¹)⁻¹ * s ∈ zpowers z := by
  have hva : H.xsub.cl a ≠ 0 := fun h => haz ((H.xsub.cl_eq_zero_iff haQ).mp h)
  have hvs : H.xsub.cl s ≠ 0 := fun h => hsz ((H.xsub.cl_eq_zero_iff hsQ).mp h)
  have hqa : H.xsub.q (H.xsub.cl a) = 0 :=
    (H.xsub.q_cl_eq_zero_iff haQ).mpr (by rw [_root_.sq]; exact ha)
  have hqs : H.xsub.q (H.xsub.cl s) = 0 :=
    (H.xsub.q_cl_eq_zero_iff hsQ).mpr (by rw [_root_.sq]; exact hs)
  obtain ⟨ω, hω, hωa⟩ := CFSG.LargeExtraspecial.O62.exists_mem_omegaGroup_apply_eq
    H.xsub.q_nondegenerate (by rw [H.finrank_Qt]; norm_num) hva hvs (hqa.trans hqs.symm)
  obtain ⟨f, hf⟩ := hΩ hω
  have hfN : (f : G) ∈ H.xsub.N := H.F_le_N f.2
  refine ⟨(f : G), hfN, ?_⟩
  have h1 : H.xsub.cl ((f : G) * a * (f : G)⁻¹) = H.xsub.cl s := by
    rw [← hωa, ← hf]
    exact (H.ρG_cl ⟨f, hfN⟩ haQ).symm
  exact (H.xsub.cl_eq_cl_iff (H.xsub.conj_mem hfN haQ) hsQ).mp h1

theorem step312_concl (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρF.range)
    (hZsQ : Zs ≤ Q)
    (hZC : centralizer (Zs : Set G) ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) :
    (∀ h ∈ centralizer ({z} : Set G),
        1 < Open.pRank 2 ((Q₀ ⊔ Q) ⊓ rightConjugate (Q₀ ⊔ Q) h) →
          rightConjugate (Q₀ ⊔ Q) h = Q₀ ⊔ Q) ∧
      ∃ T' : Subgroup G, IsSylowOf 2 T' (centralizer ({z} : Set G)) ∧
        Q₀ ⊔ Q ≤ T' ∧ ∀ h ∈ centralizer ({z} : Set G), rightConjugate (Q₀ ⊔ Q) h ≤ T' →
          rightConjugate (Q₀ ⊔ Q) h = Q₀ ⊔ Q := by
  have hS := H.q0.dData.suz
  have hFr := hS.setting.frame
  let D := H.xsub
  have hDQ : D.Q₁ = Q₀ ⊔ Q := rfl
  have hDz : D.z = z := rfl
  have hZQ₁ : Zs ≤ Q₀ ⊔ Q := hZsQ.trans le_sup_right
  have hzZ : z ∈ Zs := hS.z_mem
  have hZE : Zs ≤ E := by
    intro w hw
    rw [hS.Zs_eq] at hw
    have h2 : w ∈ centerIn (E ⊔ F) := (mem_inf.mp hw).2
    rw [← hFr.inf_eq_center] at h2
    exact (mem_inf.mp h2).1
  obtain ⟨s, hsZ, hsz⟩ : ∃ s ∈ Zs, s ∉ zpowers z := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show Zs ≤ zpowers z from hcon)
    rw [hS.Zs_card, show Nat.card (zpowers z) = 2 from D.card_zpowers_z] at h1
    omega
  have hs2 : s * s = 1 := by rw [← _root_.sq]; exact hFr.elemE.2 s (hZE hsZ)
  have hsQ : s ∈ Q₀ ⊔ Q := hZQ₁ hsZ
  have hZ2 : ∀ w ∈ Zs, w ∈ zpowers z ∨ s⁻¹ * w ∈ zpowers z := by
    have hfin : finrank (ZMod 2) (D.clSub Zs) = 1 :=
      D.finrank_clSub hZQ₁ hzZ (by rw [hS.Zs_card]; norm_num)
    have hvs : D.cl s ≠ 0 := fun h => hsz ((D.cl_eq_zero_iff hsQ).mp h)
    have hspan : Submodule.span (ZMod 2) {D.cl s} = D.clSub Zs :=
      Submodule.eq_of_le_of_finrank_eq
        ((Submodule.span_singleton_le_iff_mem _ _).mpr (D.cl_mem_clSub hsZ hsQ))
        (by rw [finrank_span_singleton hvs, hfin])
    intro w hw
    have hwQ : w ∈ Q₀ ⊔ Q := hZQ₁ hw
    have hcw : D.cl w ∈ Submodule.span (ZMod 2) {D.cl s} := by
      rw [hspan]
      exact D.cl_mem_clSub hw hwQ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hcw
    rcases Sec312.zmod2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul] at hc
      exact Or.inl ((D.cl_eq_zero_iff hwQ).mp hc.symm)
    · rw [one_smul] at hc
      exact Or.inr ((D.cl_eq_cl_iff hsQ hwQ).mp hc)
  have hsC : s ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr (D.z_comm hsQ)
  have hCZ : ∀ m ∈ centralizer ({z} : Set G), m * s = s * m →
      m ∈ centralizer (Zs : Set G) := by
    intro m hm hms
    rw [mem_centralizer_iff]
    intro w hw
    rcases hZ2 w hw with h | h
    · exact (D.comm_of_mem_zpowers hm h).symm
    · have hc := D.comm_of_mem_zpowers hm h
      rw [show w = s * (s⁻¹ * w) by group]
      calc s * (s⁻¹ * w) * m = s * ((s⁻¹ * w) * m) := by group
        _ = s * (m * (s⁻¹ * w)) := by rw [hc]
        _ = (s * m) * (s⁻¹ * w) := by group
        _ = m * (s * (s⁻¹ * w)) := by rw [← hms]; group
  have hNs : ∀ n ∈ centralizer ({D.z} : Set G), n * s * n⁻¹ * s⁻¹ ∈ zpowers D.z → n ∈ D.N := by
    intro n hn hns
    rcases D.mem_zpowers_z_iff.mp hns with h1 | h1
    · have hms : n * s = s * n := by
        calc n * s = n * s * n⁻¹ * s⁻¹ * (s * n) := by group
          _ = s * n := by rw [h1, one_mul]
      exact hZC (hCZ n hn hms)
    ·
      have hsc : s ∉ zpowers D.z := hsz
      rw [← D.mem_center_iff_mem_zpowers hsQ] at hsc
      push Not at hsc
      obtain ⟨j, hjQ, hj⟩ := hsc
      have hjs : j * s * j⁻¹ * s⁻¹ ∈ zpowers D.z := by
        have hjsj : j * s * j⁻¹ ∈ D.Q₁ := mul_mem (mul_mem hjQ hsQ) (inv_mem hjQ)
        have hQ' : j * s * j⁻¹ * s⁻¹ ∈ D.Q₁ := mul_mem hjsj (inv_mem hsQ)
        rw [← D.cl_eq_zero_iff hQ', D.cl_mul hjsj (inv_mem hsQ),
          D.cl_mul (mul_mem hjQ hsQ) (inv_mem hjQ), D.cl_mul hjQ hsQ, D.cl_inv hjQ, D.cl_inv hsQ]
        rw [add_assoc (D.cl j + D.cl s), ZModModule.add_self]
      have hjz : j * s * j⁻¹ * s⁻¹ = D.z := by
        rcases D.mem_zpowers_z_iff.mp hjs with h | h
        · exfalso
          apply hj
          calc s * j = (j * s * j⁻¹ * s⁻¹)⁻¹ * (j * s) := by group
            _ = j * s := by rw [h, inv_one, one_mul]
        · exact h
      have hjC : j ∈ centralizer ({D.z} : Set G) :=
        mem_centralizer_singleton_iff.mpr (D.z_comm hjQ)
      have hzs : D.z * s = s * D.z := (D.z_comm hsQ).symm
      have hjn : (j * n) * s = s * (j * n) := by
        have e1 : n * s * n⁻¹ = D.z * s := by
          calc n * s * n⁻¹ = n * s * n⁻¹ * s⁻¹ * s := by group
            _ = D.z * s := by rw [h1]
        have e2 : j * s * j⁻¹ = D.z * s := by
          calc j * s * j⁻¹ = j * s * j⁻¹ * s⁻¹ * s := by group
            _ = D.z * s := by rw [hjz]
        have hjz' : j * D.z = D.z * j := (D.z_comm hjQ)
        calc (j * n) * s = j * (n * s * n⁻¹) * n := by group
          _ = j * (D.z * s) * n := by rw [e1]
          _ = D.z * (j * s * j⁻¹) * j * n := by
              rw [show j * (D.z * s) * n = (j * D.z) * s * n by group, hjz']; group
          _ = D.z * (D.z * s) * j * n := by rw [e2]
          _ = s * (j * n) := by
              rw [show D.z * (D.z * s) * j * n = (D.z * D.z) * s * (j * n) by group,
                D.z_mul_z, one_mul]
      have hjnN : j * n ∈ D.N := hZC (hCZ (j * n) (mul_mem hjC hn) hjn)
      rw [show n = j⁻¹ * (j * n) by group]
      exact mul_mem (inv_mem (D.le_N hjQ)) hjnN
  have hi : ∀ h ∈ centralizer ({D.z} : Set G),
      1 < Open.pRank 2 (D.Q₁ ⊓ rightConjugate D.Q₁ h) → rightConjugate D.Q₁ h = D.Q₁ :=
    fun h hh hr => D.eq_of_one_lt_pRank
      (fun a haQ ha haz => H.exists_conj_of_involution hΩ haQ hsQ ha hs2 haz hsz) hNs hsQ hh hr
  exact ⟨hi, D.exists_isSylowOf_weaklyClosed
    (fun S hS2 hSC => H.le_zpowers_of_le_centralizer hS2 hSC) H.card hi⟩

end Sec38Hyp


theorem step312_of_centralizer
    (h17 : Step17G24Odd) {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G}
    {E F : Subgroup G} {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G}
    {D J U V₀ V Q₀ : Subgroup G} (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
    (hZC : centralizer (Zs : Set G) ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) :
    (∀ h ∈ centralizer ({z} : Set G),
        1 < Open.pRank 2 ((Q₀ ⊔ Q) ⊓ rightConjugate (Q₀ ⊔ Q) h) →
          rightConjugate (Q₀ ⊔ Q) h = Q₀ ⊔ Q) ∧
      ∃ T' : Subgroup G, IsSylowOf 2 T' (centralizer ({z} : Set G)) ∧ Q₀ ⊔ Q ≤ T' ∧
        ∀ h ∈ centralizer ({z} : Set G), rightConjugate (Q₀ ⊔ Q) h ≤ T' →
          rightConjugate (Q₀ ⊔ Q) h = Q₀ ⊔ Q := by
  have hS := hQ.dData.suz
  obtain ⟨hT, hext, hcard, hsyl, hB₀⟩ :=
    step37_of h17 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  obtain ⟨hQB₀, hB₀N, φ, hφs, hφk⟩ := sec3B0_proof G A A₁ R g E F x Zs P T Q B₀ z y hS
  have hB₀card : Nat.card B₀ = 25920 * Nat.card Q := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hφk, Nat.card_congr (subgroupOfEquivOfLe hQB₀).toEquiv, MonoidHom.range_eq_top.mpr hφs,
      card_top, (SuzB0.omega_facts SuzB0.b0_parts.2.2.2.2.2.2).1] at h
    rw [← h, mul_comm]
  let H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ :=
    { q0 := hQ
      T_le := hT
      ext := hext
      card := hcard
      sylow := hsyl
      B₀_le := hB₀
      x_not := (sec3Q0_facts hQ).2
      B₀_perf := (perfect_B₀_and_T_le hS).1
      B₀_simple := fun _ hNB hBN hNQ => eq_of_normal_of_not_le hS hNB hBN hNQ
      B₀_quot := ⟨hQB₀, hB₀N⟩
      B₀_card := hB₀card }
  obtain ⟨hQF, hφ38, -⟩ := step38_of h17 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  have hΩ := H.omega_le_range_ρF_of hQF hφ38
  have hTx : T ≤ centralizer ({x} : Set G) :=
    hS.T_le.trans (map_subtype_le _ : sec3B A₁ x ≤ centralizer ({x} : Set G))
  have hTC : Nat.card ↥(T ⊓ centralizer (Q : Set G)) ≤ 2 :=
    card_le_two_of_le_centralizer_Q hS (hS.T_two.to_le inf_le_left) inf_le_right
      (inf_le_left.trans hTx)
  obtain ⟨τ, v₀, hτ, hV⟩ := exists_tau_sec38V hQ (T_le_normalizer_V hQ) hTC
  exact H.step312_concl hΩ (H.Zs_le_Q hV.T_V hV.Zs_eq hV.card_TC) hZC

theorem step312_of
    (h17 : Step17G24Odd) (hFG : Sec3CentZNormalizes) : Step312 := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  exact step312_of_centralizer h17 hQ (hFG G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ)

end CFSG.ComponentClassification.AS81
