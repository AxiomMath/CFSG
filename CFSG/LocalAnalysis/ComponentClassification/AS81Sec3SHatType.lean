module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHat
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatTypeCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.LargeExtraspecial (pointRadical)
open CFSG.LargeExtraspecial.S2 (perp mem_perp)
open scoped commutatorElement Pointwise

namespace Sec3SHat

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {e c : G} (he : e * e = 1)
    (hc : c ∈ zpowers e) : c = 1 ∨ c = e := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
  have hk' : k = k % 2 + 2 * (k / 2) := by omega
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [hk', hk, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [hk', hk, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

end Sec3SHat

namespace SuzB0

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore

theorem rep_wordTab_foldl :
    ∀ w : List ℕ, (∀ k ∈ w, k < 10) → ∀ (a : Array ℕ) (g : Equiv.Perm (Fin 1782)),
      Rep 1782 a g → g ∈ invE 1 →
        ∃ g' ∈ invE 1, Rep 1782 (w.foldl (fun r k => compA 1782 r (cTab k)) a) g'
  | [], _, _, g, h, hg => ⟨g, hg, h⟩
  | k :: w, hw, a, g, h, hg => by
    obtain ⟨c, hc, hrep⟩ := rep_gen (hw k List.mem_cons_self)
    have hcE : c ∈ invE 1 := subset_closure hc
    simp only [List.foldl_cons]
    exact rep_wordTab_foldl w (fun j hj => hw j (List.mem_cons_of_mem k hj)) _ (g * c)
      (rep_compA h hrep) (mul_mem hg hcE)

theorem exists_rep_wordTab (w : List ℕ) (hw : ∀ k ∈ w, k < 10) :
    ∃ g ∈ invE 1, Rep 1782 (wordTab w) g :=
  rep_wordTab_foldl w hw _ 1 rep_idTab (one_mem _)

theorem commIs_iff {g h c : Array ℕ} {G Hp C : Equiv.Perm (Fin 1782)} (hg : Rep 1782 g G)
    (hh : Rep 1782 h Hp) (hc : Rep 1782 c C) : commIs g h c = true ↔ G * Hp = C * (Hp * G) :=
  eqA_iff (rep_compA hg hh) (rep_compA hc (rep_compA hh hg))

theorem polarBit_lt (v w : ℕ) : polarBit v w < 2 := Nat.mod_lt _ (by norm_num)

theorem type_facts :
    ∃ y ∈ invE 1, ∃ y' ∈ invE 1, y * y = 1 ∧ y' * y' = 1 ∧
      y * qVec 1 = qVec 1 * y ∧ y' * qVec 1 = qVec 1 * y' ∧
      (∀ u < 64, polarBit u 1 = 0 →
        y * qVec u = qVec u * y ∨ y * qVec u = qVec 1 * (qVec u * y)) ∧
      (∀ u < 64, polarBit u 1 = 0 →
        y' * qVec u = qVec u * y' ∨ y' * qVec u = qVec 1 * (qVec u * y')) ∧
      y * y' = qVec 1 * suzInv 1 * (y' * y) := by
  have h := shatType_check
  simp only [shatTypeCheck, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq] at h
  obtain ⟨h, -⟩ := h
  obtain ⟨h, hyy'⟩ := h
  obtain ⟨h, hy'Q⟩ := h
  obtain ⟨h, hyQ⟩ := h
  obtain ⟨h, hy'q⟩ := h
  obtain ⟨h, hyq⟩ := h
  obtain ⟨h, hy'2⟩ := h
  obtain ⟨h, hy2⟩ := h
  obtain ⟨h, hy'w⟩ := h
  obtain ⟨-, hyw⟩ := h
  obtain ⟨y, hyE, hy⟩ := exists_rep_wordTab typeYWord (by simpa using hyw)
  obtain ⟨y', hy'E, hy'⟩ := exists_rep_wordTab typeY'Word (by simpa using hy'w)
  have hqa : Rep 1782 qProds[typeA0]! (qVec 1) := rep_qProds (by decide)
  have hcQ : ∀ {g : Equiv.Perm (Fin 1782)} {t : Array ℕ}, Rep 1782 t g → commQOK t = true →
      ∀ u < 64, polarBit u 1 = 0 →
        g * qVec u = qVec u * g ∨ g * qVec u = qVec 1 * (qVec u * g) := by
    intro g t ht hQ u hu hpu
    simp only [commQOK, allBelow_eq_true, Bool.or_eq_true, beq_iff_eq] at hQ
    have hqu : Rep 1782 qProds[u]! (qVec u) := rep_qProds hu
    rcases hQ u hu with (h1 | h1) | h1
    · exact absurd h1 (by rw [show typeA0 = 1 from rfl, hpu]; decide)
    · left
      have h2 := (commIs_iff ht hqu rep_idTab).mp h1
      rwa [one_mul] at h2
    · exact Or.inr ((commIs_iff ht hqu hqa).mp h1)
  refine ⟨y, hyE, y', hy'E, ?_, ?_, ?_, ?_, hcQ hy hyQ, hcQ hy' hy'Q, ?_⟩
  · exact eq_of_eqA (rep_compA hy hy) rep_idTab hy2
  · exact eq_of_eqA (rep_compA hy' hy') rep_idTab hy'2
  · exact (commutesA_iff hy hqa).mp hyq
  · exact (commutesA_iff hy' hqa).mp hy'q
  · exact (commIs_iff hy hy' (rep_compA hqa rep_tTab)).mp hyy'

theorem trans_facts
    {v : ℕ} (hv : v < 64) (hv0 : v ≠ 0) (hvs : qMinusBit v = 0) :
    ∃ c ∈ invE 1, c * qVec 1 = qVec v * c ∨ c * qVec 1 = qVec v * suzInv 1 * c := by
  have h := shatType_check
  simp only [shatTypeCheck, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq] at h
  have h1 := h.2 v hv
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  have hqa : Rep 1782 qProds[typeA0]! (qVec 1) := rep_qProds (by decide)
  rcases h1 with (h1 | h1) | h1
  · exact absurd h1 hv0
  · rw [hvs] at h1
    exact absurd h1 (by decide)
  cases hl : typeTrans.lookup v with
  | none =>
    rw [hl] at h1
    exact absurd h1 Bool.false_ne_true
  | some w =>
    rw [hl] at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨hw, htr⟩ := h1
    obtain ⟨c, hcE, hc⟩ := exists_rep_wordTab w (by simpa using hw)
    refine ⟨c, hcE, ?_⟩
    simp only [transOK, Bool.or_eq_true] at htr
    rcases htr with h2 | h2
    · exact Or.inl (eq_of_eqA (rep_compA hc hqa) (rep_compA (rep_qProds hv) hc) h2)
    · exact Or.inr (eq_of_eqA (rep_compA hc hqa)
        (rep_compA (rep_compA (rep_qProds hv) rep_tTab) hc) h2)

end SuzB0

namespace Sec38Hyp

open CFSG.Sporadic.SuzOddCore (invE card_invE suzInv)

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem mem_Zs_cases (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) {s : G}
    (hs : s ∈ Zs) : s = 1 ∨ s = z ∨ s = z₂ ∨ s = z₂ * z := by
  have hs' := hs
  rw [H.Zs_eq_clPre hZQ hz₂ hz₂z] at hs'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs'.2
  have hz₂Q : z₂ ∈ H.xsub.Q₁ := H.Q_le (hZQ hz₂)
  rcases CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, eq_comm, H.xsub.cl_eq_zero_iff hs'.1] at hc
    rcases H.xsub.mem_zpowers_z_iff.mp hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [one_smul] at hc
    have h1 := (H.xsub.cl_eq_cl_iff hz₂Q hs'.1).mp hc
    rcases H.xsub.mem_zpowers_z_iff.mp h1 with h | h
    · refine Or.inr (Or.inr (Or.inl ?_))
      calc s = z₂ * (z₂⁻¹ * s) := by group
        _ = z₂ := by rw [h, mul_one]
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc s = z₂ * (z₂⁻¹ * s) := by group
        _ = z₂ * z := by rw [show z₂⁻¹ * s = z from h]

theorem exists_mul_of_mem_U (hZQ : Zs ≤ Q) {u : G}
    (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) :
    ∃ u₀ ∈ Q₀, ∃ u₁ ∈ Q ⊓ centralizer (Zs : Set G), u = u₀ * u₁ := by
  have hQ₀Q : Q₀ ≤ normalizer (Q : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => (H.comm_Q₀_Q ha hb).symm)
  have hmem : u ∈ ((Q₀ ⊔ Q : Subgroup G) : Set G) := hu.1
  rw [coe_mul_of_left_le_normalizer_right _ _ hQ₀Q, Set.mem_mul] at hmem
  obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := hmem
  have hu₀Z : u₀ ∈ centralizer (Zs : Set G) :=
    mem_centralizer_iff.mpr fun s hs => (H.comm_Q₀_Q hu₀ (hZQ hs)).symm
  refine ⟨u₀, hu₀, u₁, mem_inf.mpr ⟨hu₁, ?_⟩, rfl⟩
  have e : u₁ = u₀⁻¹ * (u₀ * u₁) := by group
  rw [e]
  exact mul_mem (inv_mem hu₀Z) hu.2

theorem mem_SHat_of_mem_pointRadical (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) {e : G}
    (he : e = z₂ ∨ e = z₂ * z) {s : G} (hsF : s ∈ sec3F (Q₀ ⊔ Q))
    (hsZ : s ∈ centralizer (Zs : Set G)) (hs2 : s * s = 1)
    (hsU : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s * u * s⁻¹ * u⁻¹ ∈ zpowers e) :
    s ∈ sec3SHat (Q₀ ⊔ Q) Zs := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := H.xsub.cl z₂ with ha
  have hz₂Q : z₂ ∈ H.xsub.Q₁ := H.Q_le (hZQ hz₂)
  have hsN := H.F_le_N hsF
  have hzQ₁ : z ∈ H.xsub.Q₁ := H.Q_le H.z_mem_Q
  have hzc : z₂ * z = z * z₂ := H.xsub.z_comm hz₂Q
  have hzz : z * z = 1 := H.xsub.z_mul_z
  have hclz : H.xsub.cl z = 0 := H.xsub.cl_z
  have hee : e * e = 1 := by
    have hz₂2 := H.sq_eq_one_of_mem_Zs hz₂
    rw [pow_two] at hz₂2
    rcases he with rfl | rfl
    · exact hz₂2
    · calc z₂ * z * (z₂ * z) = z₂ * (z * z₂) * z := by group
        _ = z₂ * (z₂ * z) * z := by rw [← hzc]
        _ = 1 := by rw [← mul_assoc, hz₂2, one_mul, hzz]
  have hcle : H.xsub.cl e = a := by
    rcases he with rfl | rfl
    · exact ha.symm
    · rw [H.xsub.cl_mul hz₂Q hzQ₁, hclz, add_zero]
  have hρa : H.ρF ⟨s, hsF⟩ a = a := H.ρG_cl_z₂ hZQ hz₂ hsZ
  have hρ : H.ρF ⟨s, hsF⟩ ∈ pointRadical H.xsub.q a := by
    have hO : H.ρF ⟨s, hsF⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q := (H.xsub.ρ _).2
    refine ⟨hO, hρa, fun v hv => ?_, fun v => ?_⟩
    · obtain ⟨u, huQ, rfl⟩ := H.xsub.exists_cl v
      have huU : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
        rw [H.centralizer_Zs_eq_clPre hZQ hz₂ hz₂z]
        refine ⟨huQ, mem_perp.mpr fun w hw => ?_⟩
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [polar_smul_left, hv, smul_zero]
      have hsu : s * u * s⁻¹ ∈ H.xsub.Q₁ := H.xsub.conj_mem hsN huQ
      have e1 : H.ρF ⟨s, hsF⟩ (H.xsub.cl u) - H.xsub.cl u = H.xsub.cl (s * u * s⁻¹ * u⁻¹) := by
        rw [H.xsub.cl_mul hsu (inv_mem huQ), H.xsub.cl_inv huQ,
          show H.ρF ⟨s, hsF⟩ (H.xsub.cl u) = H.xsub.cl (s * u * s⁻¹) from H.ρG_cl _ huQ,
          sub_eq_add_neg, ZModModule.neg_eq_self]
      rw [e1]
      rcases Sec3SHat.eq_one_or_eq_of_mem_zpowers hee (hsU u huU) with h | h
      · rw [h, XSub.cl_one]
        exact Submodule.zero_mem _
      · rw [h, hcle]
        exact Submodule.mem_span_singleton_self a
    · rw [polar_sub_right, ← hρa,
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO, hρa, sub_self]
  have hSC := CFSG.LieType.BorelTits.pCoreOf_le 2 (sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G))
  have hS2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G))
  obtain ⟨t, htS, hts⟩ := H.exists_mem_SHat_of_mem_pointRadical hΩ hQF hRc hZQ hz₂ hz₂z hρ
  have h1 : H.ρF (⟨s, hsF⟩ * t⁻¹) = 1 := by rw [map_mul, map_inv, hts, mul_inv_cancel]
  have hcZ : ((⟨s, hsF⟩ * t⁻¹ : ↥(sec3F (Q₀ ⊔ Q))) : G) ∈ centralizer (Zs : Set G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem hsZ (inv_mem (hSC htS).2)
  obtain ⟨u, hu, r, hr, hur⟩ := H.exists_mul_of_ρF_eq_one hQF hZQ hcZ h1
  have hur' : s * (t : G)⁻¹ = u * r := by
    rw [← hur, Subgroup.coe_mul, Subgroup.coe_inv]
  have hrF : ∀ f ∈ sec3F (Q₀ ⊔ Q), f * r = r * f := fun f hf =>
    mem_centralizer_iff.mp (hRc hr) f hf
  set w := u * (t : G) with hw
  have hwS : w ∈ sec3SHat (Q₀ ⊔ Q) Zs := mul_mem (H.U_le_SHat hQF hu) htS
  have hwF : w ∈ sec3F (Q₀ ⊔ Q) := (hSC hwS).1
  have hsw : s = r * w := by
    calc s = s * (t : G)⁻¹ * t := by group
      _ = u * r * t := by rw [hur']
      _ = r * (u * t) := by rw [hrF u (hQF hu.1)]; group
  have hr2 : r * r = 1 := by
    have h2 : r * r * (w * w) = 1 := by
      calc r * r * (w * w) = r * (r * w) * w := by group
        _ = r * (w * r) * w := by rw [← hrF w hwF]
        _ = r * w * (r * w) := by group
        _ = 1 := by rw [← hsw, hs2]
    have h3 : r * r = (w * w)⁻¹ := eq_inv_of_mul_eq_one_left h2
    have h4 : r * r ∈ AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓
        centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ⊓ sec3SHat (Q₀ ⊔ Q) Zs :=
      mem_inf.mpr ⟨mul_mem hr hr, by rw [h3]; exact inv_mem (mul_mem hwS hwS)⟩
    have h5 : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ⊓
        sec3SHat (Q₀ ⊔ Q) Zs = ⊥ := AS76b.oddCoreIn_inf_eq_bot hS2
    rw [h5, mem_bot] at h4
    exact h4
  have hr1 : r = 1 := by
    have hodd : Odd (orderOf r) :=
      (AS76b.odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hr)
    have h2 : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hr2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [hsw, hr1, one_mul]
  exact hwS

theorem exists_SHat_comm
    (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) :
    ∃ e ∈ Zs, e ∉ zpowers z ∧ ∃ s₁ ∈ sec3SHat (Q₀ ⊔ Q) Zs, ∃ s₂ ∈ sec3SHat (Q₀ ⊔ Q) Zs,
      (∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s₁ * u * s₁⁻¹ * u⁻¹ ∈ zpowers e) ∧
      (∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s₂ * u * s₂⁻¹ * u⁻¹ ∈ zpowers e) ∧
      s₁ * s₂ * s₁⁻¹ * s₂⁻¹ = z * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := H.q0.dData.suz
  set K := sec3B A₁ x ⊓ centralizer ({z} : Set G) with hK
  obtain ⟨e₀⟩ := hS.B_suz
  obtain ⟨-, -, π, hπs, hπk, -⟩ := Sec3.exists_hom_invE hS e₀
  have hQ₁8 : IsQ8Cube (SuzB0.coord_qVec.Q.subgroupOf (invE 1)) := by
    rw [← Sec3.isQ8Cube_map_iff (invE 1).subtype (invE 1).subtype_injective,
      subgroupOf_map_subtype, inf_eq_left.mpr SuzB0.Q_le_invE]
    exact SuzB0.coord_qVec.isQ8Cube SuzB0.b0_parts.2.2.2.2.2.2
  have hQ₁n : (SuzB0.coord_qVec.Q.subgroupOf (invE 1)).Normal :=
    ⟨fun a ha w => mem_subgroupOf.mpr
      ((mem_normalizer_iff.mp (SuzB0.invE_le w.2).1 a).mp (mem_subgroupOf.mp ha))⟩
  have hCcard : Nat.card ↥(invE 1) = 3317760 := by
    rw [card_invE (by norm_num)]
    rfl
  obtain ⟨L, -, -, hLQ, -, hLmap⟩ := Sec3.exists_lift_eq_Q hS hQ₁8 hQ₁n hCcard rfl hπs hπk
  have hzc : ∀ q ∈ Q, q * z = z * q := fun q hq =>
    mem_centralizer_iff.mp H.z_mem_centerIn_Q.2 q hq
  have hQK : Q ≤ K := fun q hq => mem_inf.mpr ⟨hS.T_le (hS.Q_le hq),
    mem_centralizer_singleton_iff.mpr (hzc q hq)⟩
  have hπQ : ∀ q (hq : q ∈ Q), ((π ⟨q, hQK hq⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈
      SuzB0.coord_qVec.Q := by
    intro q hq
    have h1 : q ∈ L.map K.subtype := by rw [hLmap]; exact hq
    obtain ⟨l, hl, hlq⟩ := h1
    have hl' : l = ⟨q, hQK hq⟩ := Subtype.ext hlq
    rw [← hl']
    exact mem_subgroupOf.mp (hLQ l hl)
  have hQ2 : IsPGroup 2 Q := hS.q8.1.1
  have hQx : ∀ q ∈ Q, q ∈ zpowers x → q = 1 := by
    intro q hq hqx
    have h3 : orderOf q ∣ 3 := hS.setting.order_x ▸ orderOf_dvd_of_mem_zpowers hqx
    obtain ⟨n, hn⟩ := hQ2 ⟨q, hq⟩
    have h2 : orderOf q ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hn)
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h2))
  have hker : ∀ (k : ↥K), (k : G) ∈ Q → π k = 1 → (k : G) = 1 := fun k hk h1 =>
    hQx k hk ((hπk k).mp h1)
  have hinj : ∀ a (ha : a ∈ Q) b (hb : b ∈ Q), π ⟨a, hQK ha⟩ = π ⟨b, hQK hb⟩ → a = b := by
    intro a ha b hb h
    have h1 : π (⟨a, hQK ha⟩ * ⟨b, hQK hb⟩⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 := hker _ (mul_mem ha (inv_mem hb)) h1
    exact mul_inv_eq_one.mp h2
  set t := suzInv 1 with htdef
  have htE : t ∈ invE 1 := SuzB0.suzInv_mem_invE
  have htc : ∀ m ∈ invE 1, m * t = t * m := fun m hm =>
    mem_centralizer_singleton_iff.mp (SuzB0.invE_le hm).2
  have hlift : ∀ (k : ↥K) (q : G) (hq : q ∈ Q), (k : G) ∈ normalizer (Q : Set G) →
      ((π k : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * (π ⟨q, hQK hq⟩ : Equiv.Perm (Fin 1782)) =
        (π ⟨q, hQK hq⟩ : Equiv.Perm (Fin 1782)) * (π k : Equiv.Perm (Fin 1782)) →
      (k : G) * q = q * k := by
    intro k q hq hkN h
    have hc : (k : G) * q * (k : G)⁻¹ * q⁻¹ ∈ Q :=
      mul_mem ((mem_normalizer_iff.mp hkN q).mp hq) (inv_mem hq)
    have h1 : π (k * ⟨q, hQK hq⟩ * k⁻¹ * ⟨q, hQK hq⟩⁻¹) = 1 := by
      apply Subtype.ext
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [h]
      group
    have h2 : (k : G) * q * (k : G)⁻¹ * q⁻¹ = 1 := hker _ hc h1
    calc (k : G) * q = ((k : G) * q * (k : G)⁻¹ * q⁻¹) * (q * k) := by group
      _ = q * k := by rw [h2, one_mul]
  have hzQ := H.z_mem_Q
  have hπz : ((π ⟨z, hQK hzQ⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = t := by
    have h1 := hπQ z hzQ
    have h2 : ∀ m ∈ SuzB0.coord_qVec.Q,
        ((π ⟨z, hQK hzQ⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * m = m * π ⟨z, hQK hzQ⟩ := by
      intro m hm
      obtain ⟨k, hk⟩ := hπs ⟨m, SuzB0.Q_le_invE hm⟩
      have hkz : (k : G) * z = z * k := mem_centralizer_singleton_iff.mp k.2.2
      have hkz' : k * ⟨z, hQK hzQ⟩ = ⟨z, hQK hzQ⟩ * k := Subtype.ext hkz
      have h3 := congrArg (fun w => ((π w : ↥(invE 1)) : Equiv.Perm (Fin 1782))) hkz'
      simp only [map_mul, Subgroup.coe_mul, hk] at h3
      exact h3.symm
    have h3 := (SuzB0.coord_qVec.forall_comm_iff h1).mp h2
    rcases Sec3SHat.eq_one_or_eq_of_mem_zpowers SuzB0.coord_qVec.t_sq h3 with h4 | h4
    · exfalso
      have h5 : π ⟨z, hQK hzQ⟩ = 1 := Subtype.ext h4
      exact H.z_ne_one (hker _ hzQ h5)
    · exact h4
  obtain ⟨z₂, hz₂, hz₂z⟩ := H.exists_z₂
  have hz₂Q := hZQ hz₂
  obtain ⟨v, hv, b, hb, hvb⟩ := SuzB0.coord_qVec.mem_Q_iff.mp (hπQ z₂ hz₂Q)
  rw [← htdef] at hvb
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [SuzB0.coord_qVec.q_zero, one_mul] at hvb
    interval_cases b
    · rw [pow_zero] at hvb
      have h : z₂ = 1 := hker _ hz₂Q (Subtype.ext hvb)
      exact hz₂z (by rw [h]; exact one_mem _)
    · rw [pow_one, ← hπz] at hvb
      have h : z₂ = z := hinj z₂ hz₂Q z hzQ (Subtype.ext hvb)
      exact hz₂z (by rw [h]; exact mem_zpowers z)
  have hvs : SuzB0.qMinusBit v = 0 := by
    have h1 : z₂ * z₂ = 1 := by
      have h := H.sq_eq_one_of_mem_Zs hz₂
      rwa [pow_two] at h
    have h2 : π (⟨z₂, hQK hz₂Q⟩ * ⟨z₂, hQK hz₂Q⟩) = 1 := by
      rw [show (⟨z₂, hQK hz₂Q⟩ * ⟨z₂, hQK hz₂Q⟩ : ↥K) = 1 from Subtype.ext h1, map_one]
    have h3 := congrArg (fun w : ↥(invE 1) => (w : Equiv.Perm (Fin 1782))) h2
    simp only [map_mul, Subgroup.coe_mul, Subgroup.coe_one, hvb] at h3
    rw [SuzB0.coord_qVec.mul_self_eq hv] at h3
    have h4 := SuzB0.qMinusBit_lt v
    interval_cases h5 : SuzB0.qMinusBit v
    · rfl
    · rw [pow_one] at h3
      exact absurd h3 SuzB0.coord_qVec.t_ne
  obtain ⟨c, hcE, hcq⟩ := SuzB0.trans_facts hv hv0 hvs
  obtain ⟨y₁, hy₁E, y₂, hy₂E, hy₁2, hy₂2, hy₁q, hy₂q, hy₁Q, hy₂Q, hy₁₂⟩ := SuzB0.type_facts
  rw [← htdef] at hcq hy₁₂
  set EM := c * SuzB0.qVec 1 * c⁻¹ with hEM
  have hEMv : EM = SuzB0.qVec v ∨ EM = SuzB0.qVec v * t := by
    rcases hcq with h | h
    · left
      rw [hEM, h, mul_inv_cancel_right]
    · right
      rw [hEM, h, mul_inv_cancel_right]
  have hz₂zQ : z₂ * z ∈ Q := mul_mem hz₂Q hzQ
  have hπz₂z : ((π ⟨z₂ * z, hQK hz₂zQ⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
      SuzB0.qVec v * t ^ b * t := by
    have h : (⟨z₂ * z, hQK hz₂zQ⟩ : ↥K) = ⟨z₂, hQK hz₂Q⟩ * ⟨z, hQK hzQ⟩ := rfl
    rw [h, map_mul, Subgroup.coe_mul, hvb, hπz]
  have htt : t * t = 1 := SuzB0.coord_qVec.t_sq
  obtain ⟨e, he, heQ, hπe⟩ : ∃ e, (e = z₂ ∨ e = z₂ * z) ∧ ∃ he : e ∈ Q,
      ((π ⟨e, hQK he⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = EM := by
    rcases hEMv with h | h <;> interval_cases b
    · exact ⟨z₂, Or.inl rfl, hz₂Q, by rw [hvb, h, pow_zero, mul_one]⟩
    · exact ⟨z₂ * z, Or.inr rfl, hz₂zQ, by rw [hπz₂z, h, pow_one, mul_assoc, htt, mul_one]⟩
    · exact ⟨z₂ * z, Or.inr rfl, hz₂zQ, by rw [hπz₂z, h, pow_zero, mul_one]⟩
    · exact ⟨z₂, Or.inl rfl, hz₂Q, by rw [hvb, h, pow_one]⟩
  have heZ : e ∈ Zs := by
    rcases he with rfl | rfl
    · exact hz₂
    · exact mul_mem hz₂ H.z_mem_Zs
  have hez : e ∉ zpowers z := by
    rcases he with rfl | rfl
    · exact hz₂z
    · intro h
      exact hz₂z (by simpa using mul_mem h (inv_mem (mem_zpowers z)))
  have hQM_q : ∀ w < 64, SuzB0.qVec w ∈ SuzB0.coord_qVec.Q := fun w hw =>
    SuzB0.coord_qVec.q_mem hw
  have hconj : ∀ y ∈ invE 1, y * SuzB0.qVec 1 = SuzB0.qVec 1 * y →
      ∀ w (hw : w ∈ Zs), (c * y * c⁻¹) * (π ⟨w, hQK (hZQ hw)⟩ : Equiv.Perm (Fin 1782)) =
        (π ⟨w, hQK (hZQ hw)⟩ : Equiv.Perm (Fin 1782)) * (c * y * c⁻¹) := by
    intro y hyE hyq w hw
    have hYE : c * y * c⁻¹ ∈ invE 1 := mul_mem (mul_mem hcE hyE) (inv_mem hcE)
    have hYt := htc _ hYE
    have hYEM : (c * y * c⁻¹) * EM = EM * (c * y * c⁻¹) := by
      rw [hEM]
      calc c * y * c⁻¹ * (c * SuzB0.qVec 1 * c⁻¹) = c * (y * SuzB0.qVec 1) * c⁻¹ := by group
        _ = c * (SuzB0.qVec 1 * y) * c⁻¹ := by rw [hyq]
        _ = c * SuzB0.qVec 1 * c⁻¹ * (c * y * c⁻¹) := by group
    have hYv : (c * y * c⁻¹) * SuzB0.qVec v = SuzB0.qVec v * (c * y * c⁻¹) := by
      rcases hEMv with h | h
      · rw [← h]
        exact hYEM
      · have h2 : SuzB0.qVec v = EM * t := by
          rw [h, mul_assoc, htt, mul_one]
        rw [h2, ← mul_assoc, hYEM, mul_assoc, hYt, ← mul_assoc]
    have hYtb : ∀ n : ℕ, (c * y * c⁻¹) * t ^ n = t ^ n * (c * y * c⁻¹) := fun n =>
      (Commute.pow_right (hYt : Commute (c * y * c⁻¹) t) n).eq
    rcases H.mem_Zs_cases hZQ hz₂ hz₂z hw with h | h | h | h
    · have e1 : (⟨w, hQK (hZQ hw)⟩ : ↥K) = 1 := Subtype.ext h
      rw [e1, map_one, Subgroup.coe_one, mul_one, one_mul]
    · have e1 : (⟨w, hQK (hZQ hw)⟩ : ↥K) = ⟨z, hQK hzQ⟩ := Subtype.ext h
      rw [e1, hπz]
      exact hYt
    · have e1 : (⟨w, hQK (hZQ hw)⟩ : ↥K) = ⟨z₂, hQK hz₂Q⟩ := Subtype.ext h
      rw [e1, hvb, ← mul_assoc, hYv, mul_assoc, hYtb, ← mul_assoc]
    · have e1 : (⟨w, hQK (hZQ hw)⟩ : ↥K) = ⟨z₂ * z, hQK hz₂zQ⟩ := Subtype.ext h
      rw [e1, hπz₂z, ← mul_assoc, ← mul_assoc, hYv, mul_assoc (SuzB0.qVec v), hYtb,
        ← mul_assoc, mul_assoc (SuzB0.qVec v * t ^ b), hYt, ← mul_assoc]
  have hx3 : x ^ 3 = 1 := by rw [← hS.setting.order_x]; exact pow_orderOf_eq_one x
  have hlift2 : ∀ Y ∈ invE 1, Y * Y = 1 → ∃ k : ↥K,
      ((π k : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = Y ∧ (k : G) * k = 1 := by
    intro Y hY hY2
    obtain ⟨k₀, hk₀⟩ := hπs ⟨Y, hY⟩
    refine ⟨k₀ ^ 3, ?_, ?_⟩
    · rw [map_pow, Subgroup.coe_pow, hk₀]
      show Y ^ 3 = Y
      rw [pow_succ, pow_two, hY2, one_mul]
    · have h1 : π (k₀ * k₀) = 1 := by
        apply Subtype.ext
        rw [map_mul, Subgroup.coe_mul, hk₀]
        exact hY2
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp ((hπk _).mp h1)
      have h3 : ((k₀ : G) * k₀) ^ 3 = 1 := by
        have e1 : ((k₀ * k₀ : ↥K) : G) = (k₀ : G) * k₀ := rfl
        rw [← e1, ← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3,
          one_zpow]
      calc ((k₀ ^ 3 : ↥K) : G) * ((k₀ ^ 3 : ↥K) : G) = ((k₀ : G) * k₀) ^ 3 := by
            rw [Subgroup.coe_pow, ← pow_two, ← pow_mul, ← pow_two, ← pow_mul]
        _ = 1 := h3
  have hprop : ∀ y ∈ invE 1, y * y = 1 → y * SuzB0.qVec 1 = SuzB0.qVec 1 * y →
      (∀ u < 64, SuzB0.polarBit u 1 = 0 → y * SuzB0.qVec u = SuzB0.qVec u * y ∨
        y * SuzB0.qVec u = SuzB0.qVec 1 * (SuzB0.qVec u * y)) →
      ∃ k : ↥K, ((π k : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = c * y * c⁻¹ ∧
        (k : G) ∈ sec3SHat (Q₀ ⊔ Q) Zs ∧
        ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G),
          (k : G) * u * (k : G)⁻¹ * u⁻¹ ∈ zpowers e := by
    intro y hyE hy2 hyq hyQ
    have hYE : c * y * c⁻¹ ∈ invE 1 := mul_mem (mul_mem hcE hyE) (inv_mem hcE)
    have hY2 : c * y * c⁻¹ * (c * y * c⁻¹) = 1 := by
      calc c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    obtain ⟨k, hk, hk2⟩ := hlift2 _ hYE hY2
    obtain ⟨b₀, hb₀, i, hbi⟩ := Sec3.exists_mem_B₀_of_mem_centralizer hS k.2
    have hkB₀ : (k : G) ∈ B₀ := by
      have hc : Commute b₀ (x ^ i) := (Commute.zpow_right (H.B₀_comm_x hb₀ : Commute b₀ x) i)
      have h1 : (k : G) = (k : G) ^ 3 := by rw [pow_succ, pow_two, hk2, one_mul]
      have h2 : (x ^ i) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
      rw [h1, hbi, hc.mul_pow, h2, mul_one]
      exact pow_mem hb₀ 3
    have hkN : (k : G) ∈ normalizer (Q : Set G) := H.B₀_quot.2 hkB₀
    have hkZ : (k : G) ∈ centralizer (Zs : Set G) := mem_centralizer_iff.mpr fun w hw =>
      (hlift k w (hZQ hw) hkN (by rw [hk]; exact hconj y hyE hyq w hw)).symm
    have hkU : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G),
        (k : G) * u * (k : G)⁻¹ * u⁻¹ ∈ zpowers e := by
      intro u hu
      obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := H.exists_mul_of_mem_U hZQ hu
      have hku₀ : (k : G) * u₀ = u₀ * k := (mem_centralizer_iff.mp (H.B₀_le hkB₀) u₀ hu₀).symm
      have hu₁Q : u₁ ∈ Q := hu₁.1
      have hcQ : (k : G) * u₁ * (k : G)⁻¹ * u₁⁻¹ ∈ Q :=
        mul_mem ((mem_normalizer_iff.mp hkN u₁).mp hu₁Q) (inv_mem hu₁Q)
      set m := ((π ⟨u₁, hQK hu₁Q⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) with hm
      have hmQ : m ∈ SuzB0.coord_qVec.Q := hπQ u₁ hu₁Q
      have hcm : c⁻¹ * m * c ∈ SuzB0.coord_qVec.Q := by
        have h := (mem_normalizer_iff.mp (SuzB0.invE_le (inv_mem hcE)).1 m).mp hmQ
        rwa [inv_inv] at h
      obtain ⟨u', hu', b', hb', hu'b'⟩ := SuzB0.coord_qVec.mem_Q_iff.mp hcm
      have hmEM : m * EM = EM * m := by
        have h1 : u₁ * e = e * u₁ := (mem_centralizer_iff.mp hu₁.2 e heZ).symm
        have h2 : (⟨u₁, hQK hu₁Q⟩ * ⟨e, hQK heQ⟩ : ↥K) = ⟨e, hQK heQ⟩ * ⟨u₁, hQK hu₁Q⟩ :=
          Subtype.ext h1
        have h3 := congrArg (fun w => ((π w : ↥(invE 1)) : Equiv.Perm (Fin 1782))) h2
        simp only [map_mul, Subgroup.coe_mul] at h3
        rwa [hπe] at h3
      have hcq1 : (c⁻¹ * m * c) * SuzB0.qVec 1 = SuzB0.qVec 1 * (c⁻¹ * m * c) := by
        have h1 : SuzB0.qVec 1 = c⁻¹ * EM * c := by rw [hEM]; group
        rw [h1]
        calc c⁻¹ * m * c * (c⁻¹ * EM * c) = c⁻¹ * (m * EM) * c := by group
          _ = c⁻¹ * (EM * m) * c := by rw [hmEM]
          _ = c⁻¹ * EM * c * (c⁻¹ * m * c) := by group
      have hpol : SuzB0.polarBit u' 1 = 0 := by
        have h3 := SuzB0.coord_qVec.commutator_eq hu' (by norm_num : 1 < 64) b' 0
        rw [← hu'b', pow_zero, mul_one, hcq1, mul_inv_cancel_right, mul_inv_cancel] at h3
        have h4 := SuzB0.polarBit_lt u' 1
        change 1 = t ^ SuzB0.polarBit u' 1 at h3
        interval_cases h5 : SuzB0.polarBit u' 1
        · rfl
        · rw [pow_one] at h3
          exact absurd h3.symm SuzB0.coord_qVec.t_ne
      have hyt : y * t ^ b' = t ^ b' * y :=
        (Commute.pow_right (htc y hyE : Commute y t) b').eq
      have hπc : ((π (k * ⟨u₁, hQK hu₁Q⟩ * k⁻¹ * ⟨u₁, hQK hu₁Q⟩⁻¹) : ↥(invE 1)) :
          Equiv.Perm (Fin 1782)) = c * (y * (c⁻¹ * m * c) * y⁻¹ * (c⁻¹ * m * c)⁻¹) * c⁻¹ := by
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hk, ← hm]
        group
      have hcm2 : y * (SuzB0.qVec u' * t ^ b') * y⁻¹ * (SuzB0.qVec u' * t ^ b')⁻¹ =
          y * SuzB0.qVec u' * y⁻¹ * (SuzB0.qVec u')⁻¹ := by
        have hqt : SuzB0.qVec u' * t ^ b' = t ^ b' * SuzB0.qVec u' :=
          SuzB0.coord_qVec.comm_pow hu' b'
        calc y * (SuzB0.qVec u' * t ^ b') * y⁻¹ * (SuzB0.qVec u' * t ^ b')⁻¹ =
            y * SuzB0.qVec u' * (t ^ b' * y⁻¹) * (t ^ b')⁻¹ * (SuzB0.qVec u')⁻¹ := by group
          _ = y * SuzB0.qVec u' * (y⁻¹ * t ^ b') * (t ^ b')⁻¹ * (SuzB0.qVec u')⁻¹ := by
            rw [show t ^ b' * y⁻¹ = y⁻¹ * t ^ b' by
              rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hyt, mul_inv_cancel_right]]
          _ = y * SuzB0.qVec u' * y⁻¹ * (SuzB0.qVec u')⁻¹ := by group
      have hcomm : (k : G) * u₁ * (k : G)⁻¹ * u₁⁻¹ = 1 ∨
          (k : G) * u₁ * (k : G)⁻¹ * u₁⁻¹ = e := by
        rcases hyQ u' hu' hpol with h5 | h5
        · left
          have h6 : y * (c⁻¹ * m * c) * y⁻¹ * (c⁻¹ * m * c)⁻¹ = 1 := by
            rw [hu'b', hcm2, h5]
            group
          rw [h6, mul_one, mul_inv_cancel] at hπc
          exact hker _ hcQ (Subtype.ext hπc)
        · right
          have h6 : y * (c⁻¹ * m * c) * y⁻¹ * (c⁻¹ * m * c)⁻¹ = SuzB0.qVec 1 := by
            rw [hu'b', hcm2, h5]
            group
          rw [h6, ← hEM, ← hπe] at hπc
          exact hinj _ hcQ e heQ (Subtype.ext hπc)
      have hc : (k : G) * u₁ * (k : G)⁻¹ * u₁⁻¹ ∈ zpowers e := by
        rcases hcomm with h | h
        · rw [h]
          exact one_mem _
        · rw [h]
          exact mem_zpowers e
      have e1 : (k : G) * (u₀ * u₁) * (k : G)⁻¹ * (u₀ * u₁)⁻¹ =
          u₀ * ((k : G) * u₁ * (k : G)⁻¹ * u₁⁻¹) * u₀⁻¹ := by
        calc (k : G) * (u₀ * u₁) * (k : G)⁻¹ * (u₀ * u₁)⁻¹ =
            ((k : G) * u₀) * u₁ * (k : G)⁻¹ * u₁⁻¹ * u₀⁻¹ := by group
          _ = u₀ * ((k : G) * u₁ * (k : G)⁻¹ * u₁⁻¹) * u₀⁻¹ := by rw [hku₀]; group
      rw [e1, H.comm_Q₀_Q hu₀ hcQ, mul_inv_cancel_right]
      exact hc
    refine ⟨k, hk, H.mem_SHat_of_mem_pointRadical hΩ hQF hRc hZQ hz₂ hz₂z he
      (H.B₀_le_F hkB₀) hkZ hk2 hkU, hkU⟩
  obtain ⟨k₁, hk₁, hk₁S, hk₁U⟩ := hprop y₁ hy₁E hy₁2 hy₁q hy₁Q
  obtain ⟨k₂, hk₂, hk₂S, hk₂U⟩ := hprop y₂ hy₂E hy₂2 hy₂q hy₂Q
  refine ⟨e, heZ, hez, k₁, hk₁S, k₂, hk₂S, hk₁U, hk₂U, ?_⟩
  have hcZ : (k₁ : G) * k₂ * (k₁ : G)⁻¹ * (k₂ : G)⁻¹ ∈ Zs := by
    have h := Subgroup.commutator_mem_commutator hk₁S hk₂S
    rw [commutatorElement_def] at h
    exact H.commutator_SHat_le hΩ hQF hZQ hz₂ hz₂z h
  have hcQ := hZQ hcZ
  have hzeQ : z * e ∈ Q := mul_mem hzQ heQ
  refine hinj _ hcQ _ hzeQ (Subtype.ext ?_)
  have e1 : (⟨(k₁ : G) * k₂ * (k₁ : G)⁻¹ * (k₂ : G)⁻¹, hQK hcQ⟩ : ↥K) = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ :=
    rfl
  have e2 : (⟨z * e, hQK hzeQ⟩ : ↥K) = ⟨z, hQK hzQ⟩ * ⟨e, hQK heQ⟩ := rfl
  rw [e1, e2]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hk₁, hk₂, hπz, hπe]
  have h1 : c * y₁ * c⁻¹ * (c * y₂ * c⁻¹) * (c * y₁ * c⁻¹)⁻¹ * (c * y₂ * c⁻¹)⁻¹ =
      c * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * c⁻¹ := by group
  have h2 : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = SuzB0.qVec 1 * t := by
    rw [hy₁₂]
    group
  have hEME : c * SuzB0.qVec 1 * c⁻¹ ∈ invE 1 :=
    mul_mem (mul_mem hcE (SuzB0.qVec_mem_invE 1)) (inv_mem hcE)
  have h3 : c * (SuzB0.qVec 1 * t) * c⁻¹ = c * SuzB0.qVec 1 * c⁻¹ * t := by
    rw [show c * (SuzB0.qVec 1 * t) * c⁻¹ = c * SuzB0.qVec 1 * (t * c⁻¹) by group,
      ← htc _ (inv_mem hcE)]
    group
  rw [h1, h2, hEM, h3]
  exact htc _ hEME

end Sec38Hyp

end CFSG.ComponentClassification.AS81
