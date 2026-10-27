module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBJ2Cert
public import Certificates.Data.Seitz77Sec27SmallJ2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.KGroups.Generic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.HarrisLit.EndB
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Th

theorem map_centralizerIn {M : Type*} [Group M] (φ : M ≃* M) (H : Subgroup M) (x : M) :
    centralizerIn (H.map φ.toMonoidHom) (φ x) = (centralizerIn H x).map φ.toMonoidHom := by
  ext y
  simp only [mem_centralizerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨h, hh, rfl⟩, hyx⟩
    refine ⟨h, ⟨hh, ?_⟩, rfl⟩
    apply φ.injective
    simpa [map_mul] using hyx
  · rintro ⟨h, ⟨hh, hhx⟩, rfl⟩
    exact ⟨⟨h, hh, rfl⟩, by simp [← map_mul, hhx]⟩

theorem card_centralizerIn_P_of_conj_a {c : Equiv.Perm (Fin 315)}
    (hc : c ∈ P) : Nat.card ↥(centralizerIn P (c * permA * c⁻¹)) = 240 := by
  rw [centralizerIn_conj P hc permA, Subgroup.card_map_of_injective (MulAut.conj c).injective,
    inner_classes.2.2.1]
  exact cent2B_facts.2.1

theorem card_centralizerIn_P_of_conj_z {c : Equiv.Perm (Fin 315)}
    (hc : c ∈ P) : Nat.card ↥(centralizerIn P (c * permTwoA * c⁻¹)) = 1920 := by
  rw [centralizerIn_conj P hc permTwoA, Subgroup.card_map_of_injective (MulAut.conj c).injective,
    inner_classes.2.2.2.2]
  exact cent2A_facts.2.1

theorem exists_conj_u_of_2B {s c : Equiv.Perm (Fin 315)}
    (hc : c ∈ P) (hs : s = c * permA * c⁻¹) : ∃ e ∈ P, permU * s * permU⁻¹ = e * s * e⁻¹ := by
  have hsP : s ∈ P := hs ▸ P.mul_mem (P.mul_mem hc permA_mem) (P.inv_mem hc)
  have hs'P : permU * s * permU⁻¹ ∈ P := permU_conj_mem s hsP
  have hords : orderOf s = 2 := by
    rw [hs, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact orderOf_permA
  have hord : orderOf (permU * s * permU⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hords
  obtain ⟨r, hr, e, he, hse⟩ := inner_classes.1 _ hs'P hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨e * c⁻¹, P.mul_mem he (P.inv_mem hc), ?_⟩
    rw [hse, hs]
    group
  · exfalso
    have h1 : Nat.card ↥(centralizerIn P (permU * s * permU⁻¹)) = 1920 := by
      rw [hse]
      exact card_centralizerIn_P_of_conj_z he
    have h2 : Nat.card ↥(centralizerIn P (permU * s * permU⁻¹)) = 240 := by
      have h := map_centralizerIn (MulAut.conj permU) P s
      rw [map_conj_permU] at h
      have e : (MulAut.conj permU) s = permU * s * permU⁻¹ := MulAut.conj_apply _ _
      rw [e] at h
      rw [h, Subgroup.card_map_of_injective (MulAut.conj permU).injective, hs]
      exact card_centralizerIn_P_of_conj_a hc
    omega

theorem conjClass_R_eq_P {s c : Equiv.Perm (Fin 315)}
    (hc : c ∈ P) (hs : s = c * permA * c⁻¹) :
    CFSG.Sporadic.Schreier.conjClass R s = CFSG.Sporadic.Schreier.conjClass P s := by
  obtain ⟨e, he, hue⟩ := exists_conj_u_of_2B hc hs
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases (mem_R_iff r).1 hr with hrP | hrU
    · exact ⟨r, hrP, rfl⟩
    · refine ⟨(r * permU) * e, P.mul_mem hrU he, ?_⟩
      have h1 : (r * permU * e) * s * (r * permU * e)⁻¹ =
          r * permU * (e * s * e⁻¹) * permU⁻¹ * r⁻¹ := by group
      have h2 : permU * (permU * s * permU) * permU = s := by
        calc permU * (permU * s * permU) * permU = (permU * permU) * s * (permU * permU) := by
              group
          _ = s := by rw [permU_mul_self]; simp
      rw [h1, ← hue, permU_inv, show r * permU * (permU * s * permU) * permU * r⁻¹ =
        r * (permU * (permU * s * permU) * permU) * r⁻¹ by group, h2]
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, P_le_R hp, rfl⟩

theorem card_centralizerIn_R_of_conj_a {s c : Equiv.Perm (Fin 315)}
    (hc : c ∈ P) (hs : s = c * permA * c⁻¹) : Nat.card ↥(centralizerIn R s) = 480 := by
  have hR := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card R s
  have hP' := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card P s
  rw [conjClass_R_eq_P hc hs, card_R] at hR
  have h240 : Nat.card ↥(centralizerIn P s) = 240 := hs ▸ card_centralizerIn_P_of_conj_a hc
  rw [h240, card_P] at hP'
  have h2520 : (CFSG.Sporadic.Schreier.conjClass P s).ncard = 2520 := by omega
  rw [h2520] at hR
  omega

theorem card_centralizerIn_R_of_outer {s : Equiv.Perm (Fin 315)}
    (hsR : s ∈ R) (hsP : s ∉ P) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    Nat.card ↥(centralizerIn R s) = 672 := by
  have hord : orderOf s = 2 := orderOf_eq_prime (by rwa [sq]) hs1
  have hsu : s * permU ∈ P := ((mem_R_iff s).1 hsR).resolve_left hsP
  have hus : permU⁻¹ * s ∈ P := by
    have h := permU_conj_mem' _ hsu
    have e : permU⁻¹ * (s * permU) * permU = permU⁻¹ * s := by
      simp [mul_assoc, permU_mul_self]
    rwa [e] at h
  obtain ⟨c, hcP, hsc⟩ := outer_classes.1 s hus hord
  have hcR : c ∈ R := P_le_R hcP
  have h1 : Nat.card ↥(centralizerIn R s) = Nat.card ↥(centralizerIn R permU) := by
    rw [hsc, centralizerIn_conj R hcR permU,
      Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hcl : CFSG.Sporadic.Schreier.conjClass R permU =
      CFSG.Sporadic.Schreier.conjClass P permU := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      rcases (mem_R_iff r).1 hr with hrP | hrU
      · exact ⟨r, hrP, rfl⟩
      · exact ⟨r * permU, hrU, by group⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, P_le_R hp, rfl⟩
  have hos := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card R permU
  rw [hcl, outer_classes.2.1, card_R] at hos
  omega

theorem two_pow_seven_dvd_R_of_conj_z {s c : Equiv.Perm (Fin 315)}
    (hc : c ∈ P) (hs : s = c * permTwoA * c⁻¹) : 2 ^ 7 ∣ Nat.card ↥(centralizerIn R s) := by
  subst hs
  have hle : centralizerIn P (c * permTwoA * c⁻¹) ≤ centralizerIn R (c * permTwoA * c⁻¹) :=
    inf_le_inf_right _ P_le_R
  have h := Subgroup.card_dvd_of_le hle
  rw [card_centralizerIn_P_of_conj_z hc] at h
  exact (by norm_num : 2 ^ 7 ∣ 1920).trans h

theorem exists_central_involution
    (h : Certificates.Seitz77Sec27.j2U0Check = true) :
    ∃ u₀ ∈ P, u₀ * u₀ = 1 ∧ u₀ ≠ 1 ∧ u₀ ≠ permA ∧
      centralizerIn P permA ≤ centralizer ({u₀} : Set (Equiv.Perm (Fin 315))) := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  unfold Certificates.Seitz77Sec27.j2U0Check at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hperm, hp0⟩, hinvo⟩, hcomm⟩, hne⟩ := h
  have rep0 := rep_tp hp0
  have hord : orderOf (tp 315 Certificates.Seitz77Sec27.j2U0) = 2 :=
    orderOf_eq_two_of_involOK hn rep0 hinvo
  have hmem : tp 315 Certificates.Seitz77Sec27.j2U0 ∈ genOf 315 c2BGens :=
    tp_wordTbl_mem hn hperm (w := [2, 2, 2]) (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp [c2BGens]) hp0
  rw [genOf_c2BGens] at hmem
  have hsq : tp 315 Certificates.Seitz77Sec27.j2U0 * tp 315 Certificates.Seitz77Sec27.j2U0 = 1 := by
    have := pow_orderOf_eq_one (tp 315 Certificates.Seitz77Sec27.j2U0)
    rwa [hord, sq] at this
  refine ⟨_, (mem_centralizerIn.1 hmem).1, hsq, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hord
    omega
  · intro hea
    have hrepa : Rep 315 (arrTable 315 autStrong[0]!) permA := rep_arrTable hn rep_permA
    have h2 := (tblEq_iff_eq rep0 hrepa).2 hea
    rw [hne] at h2
    exact Bool.false_ne_true h2
  · rw [← genOf_c2BGens, genOf, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ c2BGens := by simpa using hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact ((commTT_iff rep0 (rep_tp (hperm g hg'))).1 (hcomm g hg')).symm

theorem j2Census
    (hcheck : Certificates.Seitz77Sec27.j2U0Check = true) :
    (∀ t ∈ R, t * t = 1 → t ≠ 1 →
      5 ∣ Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 315))) ⊓ R) →
        t ∈ P ∧ 2 ^ 5 ∣ Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 315))) ⊓ R)) ∧
    (∀ t ∈ P, t * t = 1 → t ≠ 1 →
      5 ∣ Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 315))) ⊓ P) →
        2 ^ 5 ∣ Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 315))) ⊓ P) ∨
        ∃ u ∈ P, u * u = 1 ∧ u ≠ 1 ∧ u ≠ t ∧
          centralizer ({t} : Set (Equiv.Perm (Fin 315))) ⊓ P ≤
            centralizer ({u} : Set (Equiv.Perm (Fin 315)))) := by
  obtain ⟨u₀, hu₀P, hu₀2, hu₀1, hu₀a, hu₀c⟩ := exists_central_involution hcheck
  refine ⟨?_, ?_⟩
  · intro s hsR hs2 hs1 h5
    have e : centralizer ({s} : Set (Equiv.Perm (Fin 315))) ⊓ R = centralizerIn R s :=
      inf_comm _ _
    rw [e] at h5 ⊢
    by_cases hsP : s ∈ P
    · refine ⟨hsP, ?_⟩
      have hord : orderOf s = 2 := orderOf_eq_prime (by rwa [sq]) hs1
      obtain ⟨r, hr, c, hc, hsc⟩ := inner_classes.1 s hsP hord
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [card_centralizerIn_R_of_conj_a hc hsc]
        norm_num
      · exact (pow_dvd_pow 2 (by norm_num : 5 ≤ 7)).trans (two_pow_seven_dvd_R_of_conj_z hc hsc)
    · exfalso
      rw [card_centralizerIn_R_of_outer hsR hsP hs2 hs1] at h5
      revert h5
      norm_num
  · intro s hsP hs2 hs1 h5
    have hord : orderOf s = 2 := orderOf_eq_prime (by rwa [sq]) hs1
    obtain ⟨r, hr, c, hc, hsc⟩ := inner_classes.1 s hsP hord
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have e : centralizer ({s} : Set (Equiv.Perm (Fin 315))) ⊓ P = centralizerIn P s :=
      inf_comm _ _
    rcases hr with rfl | rfl
    · right
      refine ⟨c * u₀ * c⁻¹, P.mul_mem (P.mul_mem hc hu₀P) (P.inv_mem hc), ?_, ?_, ?_, ?_⟩
      · calc c * u₀ * c⁻¹ * (c * u₀ * c⁻¹) = c * (u₀ * u₀) * c⁻¹ := by group
          _ = 1 := by rw [hu₀2]; group
      · intro h
        apply hu₀1
        have h' : u₀ = c⁻¹ * (c * u₀ * c⁻¹) * c := by group
        rw [h', h]
        group
      · intro h
        apply hu₀a
        rw [hsc] at h
        calc u₀ = c⁻¹ * (c * u₀ * c⁻¹) * c := by group
          _ = c⁻¹ * (c * permA * c⁻¹) * c := by rw [h]
          _ = permA := by group
      · intro x hx
        obtain ⟨hxs, hxP⟩ := Subgroup.mem_inf.1 hx
        rw [Subgroup.mem_centralizer_singleton_iff, hsc] at hxs
        have hx' : c⁻¹ * x * c ∈ centralizerIn P permA := by
          refine mem_centralizerIn.2 ⟨P.mul_mem (P.mul_mem (P.inv_mem hc) hxP) hc, ?_⟩
          calc c⁻¹ * x * c * permA = c⁻¹ * (x * (c * permA * c⁻¹)) * c := by group
            _ = c⁻¹ * ((c * permA * c⁻¹) * x) * c := by rw [hxs]
            _ = permA * (c⁻¹ * x * c) := by group
        have h2 := Subgroup.mem_centralizer_singleton_iff.1 (hu₀c hx')
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc x * (c * u₀ * c⁻¹) = c * ((c⁻¹ * x * c) * u₀) * c⁻¹ := by group
          _ = c * (u₀ * (c⁻¹ * x * c)) * c⁻¹ := by rw [h2]
          _ = (c * u₀ * c⁻¹) * x := by group
    · left
      rw [e, hsc, card_centralizerIn_P_of_conj_z hc]
      norm_num

end CFSG.OddStandard.Seitz77
