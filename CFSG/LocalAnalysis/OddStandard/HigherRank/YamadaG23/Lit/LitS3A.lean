module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitGam
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTMem
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem lit_two_mem_of_normal [Finite Γ] {A C : Subgroup Γ} (hAC : A ≤ C)
    (hnorm : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) (hA : IsPGroup 2 A)
    (hidx : ¬ 2 ∣ A.relIndex C) {c : Γ} (hc : c ∈ C) {k : ℕ} (hk : c ^ 2 ^ k = 1) :
    c ∈ A := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let A' : Subgroup ↥C := A.subgroupOf C
  have hA' : IsPGroup 2 A' := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  haveI hA'norm : A'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hnorm (g : Γ) g.2 (n : Γ) hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h⟩
  have hidx' : ¬ 2 ∣ A'.index := by simpa [A', Subgroup.relIndex] using hidx
  let S : Sylow 2 ↥C := hA'.toSylow hidx'
  let c' : ↥C := ⟨c, hc⟩
  have hc' : c' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using hk
  have hzp : IsPGroup 2 (Subgroup.zpowers c') :=
    IsPGroup.of_card_dvd_pow (by
      rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]
      exact hc')
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hScoeeq : (S : Subgroup ↥C) = A' := IsPGroup.toSylow_coe hA' hidx'
  have hA'leQ : A' ≤ (Q : Subgroup ↥C) := IsPGroup.le_sylow_of_normal hA' Q
  have hQeq : (Q : Subgroup ↥C) = A' := by
    have h := S.is_maximal' Q.isPGroup' (by rw [hScoeeq]; exact hA'leQ)
    rwa [hScoeeq] at h
  have hcQ : c' ∈ (Q : Subgroup ↥C) := hQ (Subgroup.mem_zpowers c')
  have : c' ∈ A' := hQeq ▸ hcQ
  exact Subgroup.mem_subgroupOf.mp this

variable {Gh Zh Ah : Subgroup Γ} {t : Γ}

theorem LitGam.t_mem_A (h : LitGam Gh Zh Ah t) (x : Γ) : x ∈ Ah ↔ t * x * t⁻¹ ∈ Ah := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.ord_t] at this
    simpa [pow_two] using this
  have hfwd : ∀ y, y ∈ Ah → t * y * t⁻¹ ∈ Ah := by
    intro y hy
    have hyG : y ∈ Gh := h.A_le_G hy
    have hyT : y ∈ centralizerSection (Zh ⊔ zpowers t) Zh := (h.five_a hy).2
    have hcomm : ⁅t, y⁆ ∈ Zh := (lit_mem_T_iff h.Z_central h.Z_le_G h.t_Z hyG).mp hyT
    have heq : t * y * t⁻¹ = ⁅t, y⁆ * y := by
      simpa using (conj_eq_commutatorElement_mul (g₁ := t) (g₂ := y))
    rw [heq]
    exact Ah.mul_mem (h.Z_le_A hcomm) hy
  refine ⟨hfwd x, fun hx => ?_⟩
  have hx' := hfwd (t * x * t⁻¹) hx
  have hxx : t * (t * x * t⁻¹) * t⁻¹ = x := by
    rw [inv_eq_of_mul_eq_one_right ht2]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht2]; simp
  rwa [hxx] at hx'

theorem LitGam.t_mem_C (h : LitGam Gh Zh Ah t) (x : Γ) :
    x ∈ Gh ⊓ centralizerSection Ah Zh ↔ t * x * t⁻¹ ∈ Gh ⊓ centralizerSection Ah Zh := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.ord_t] at this
    simpa [pow_two] using this
  have htN : t ∈ normalizer (Ah : Set Γ) := Subgroup.mem_normalizer_iff.mpr (t_mem_A h)
  have key : ∀ y, y ∈ Gh ⊓ centralizerSection Ah Zh →
      t * y * t⁻¹ ∈ Gh ⊓ centralizerSection Ah Zh := by
    intro y hy
    rw [Subgroup.mem_inf] at hy ⊢
    obtain ⟨hyG, hyC⟩ := hy
    obtain ⟨hyn, hycomm⟩ := (lit_mem_C_iff h.Z_central hyG).mp hyC
    have hyG' : t * y * t⁻¹ ∈ Gh := (Subgroup.mem_normalizer_iff.mp h.t_G y).mp hyG
    refine ⟨hyG', ?_⟩
    rw [lit_mem_C_iff h.Z_central hyG']
    refine ⟨?_, ?_⟩
    · exact mul_mem (mul_mem htN hyn) (inv_mem htN)
    · intro a ha
      have htat : t⁻¹ * a * t ∈ Ah := by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem htN) a).mp ha
      have hcomm : ⁅t⁻¹ * a * t, y⁆ ∈ Zh := hycomm _ htat
      have hzh : t * ⁅t⁻¹ * a * t, y⁆ * t⁻¹ ∈ Zh :=
        (Subgroup.mem_normalizer_iff.mp h.t_Z _).mp hcomm
      have hconj : t * ⁅t⁻¹ * a * t, y⁆ * t⁻¹ = ⁅a, t * y * t⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rwa [hconj] at hzh
  refine ⟨key x, fun hx => ?_⟩
  have hx' := key (t * x * t⁻¹) hx
  have hxx : t * (t * x * t⁻¹) * t⁻¹ = x := by
    rw [inv_eq_of_mul_eq_one_right ht2]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht2]; simp
  rwa [hxx] at hx'

theorem LitGam.t_mem_N (h : LitGam Gh Zh Ah t) (x : Γ) :
    x ∈ normIn Gh Ah ↔ t * x * t⁻¹ ∈ normIn Gh Ah := by
  have htN : t ∈ normalizer (Ah : Set Γ) := Subgroup.mem_normalizer_iff.mpr (t_mem_A h)
  change x ∈ Gh ⊓ normalizer (Ah : Set Γ) ↔ t * x * t⁻¹ ∈ Gh ⊓ normalizer (Ah : Set Γ)
  constructor
  · rintro ⟨hxG, hxN⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp h.t_G x).mp hxG, ?_⟩
    exact (normalizer (Ah : Set Γ)).mul_mem
      ((normalizer (Ah : Set Γ)).mul_mem htN hxN) ((normalizer (Ah : Set Γ)).inv_mem htN)
  · rintro ⟨hyG, hyN⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp h.t_G x).mpr hyG, ?_⟩
    have hxN : t⁻¹ * (t * x * t⁻¹) * t ∈ normalizer (Ah : Set Γ) :=
      (normalizer (Ah : Set Γ)).mul_mem
        ((normalizer (Ah : Set Γ)).mul_mem ((normalizer (Ah : Set Γ)).inv_mem htN) hyN) htN
    rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at hxN

theorem lit_s3_sylow [Finite Γ] (h : LitGam Gh Zh Ah t) :
    ∃ S : Subgroup Γ, S ≤ normIn Gh Ah ∧ IsPGroup 2 S ∧ ¬ 2 ∣ S.relIndex (normIn Gh Ah) ∧
      (∀ x, x ∈ S ↔ t * x * t⁻¹ ∈ S) ∧ ∀ s ∈ S, ⁅s, t⁆ ∈ Ah := by
  classical
  obtain ⟨S, hSN, hS2, hSidx, htS⟩ :=
    lit_inv_sylow (G := Γ) (N := normIn Gh Ah) (t := t) h.ord_t (LitGam.t_mem_N h)
  refine ⟨S, hSN, hS2, hSidx, htS, ?_⟩
  intro s hs
  obtain ⟨m, hmN, c, hcC, hsmc, hmt⟩ := h.seven s (hSN hs)
  have hA_le_C : Ah ≤ Gh ⊓ centralizerSection Ah Zh := by
    intro a ha
    rw [Subgroup.mem_inf]
    refine ⟨h.A_le_G ha, ?_⟩
    rw [lit_mem_C_iff h.Z_central (h.A_le_G ha)]
    exact ⟨Subgroup.le_normalizer ha, fun b hb => h.comm_mem b hb a ha⟩
  have hnormC : ∀ c ∈ Gh ⊓ centralizerSection Ah Zh, ∀ a ∈ Ah, c * a * c⁻¹ ∈ Ah := by
    intro c hc a ha
    exact (Subgroup.mem_normalizer_iff.mp hc.2.1 a).mp ha
  set d : Γ := s⁻¹ * (t * s * t⁻¹) with hd_def
  have hdS : d ∈ S := by
    rw [hd_def]
    exact S.mul_mem (S.inv_mem hs) ((htS s).mp hs)
  have hdC : d ∈ Gh ⊓ centralizerSection Ah Zh := by
    have hdecomp : d = c⁻¹ * (m⁻¹ * (t * m * t⁻¹)) * (t * c * t⁻¹) := by
      rw [hd_def, hsmc]
      group
    rw [hdecomp]
    have hm0 : m⁻¹ * (t * m * t⁻¹) ∈ Ah := by
      have htm : ⁅t, m⁆ ∈ Ah := by
        rw [(commutatorElement_inv (g₁ := m) (g₂ := t)).symm]
        exact Ah.inv_mem hmt
      have heq : m⁻¹ * (t * m * t⁻¹) = m⁻¹ * ⁅t, m⁆ * m := by
        have hconj := conj_eq_commutatorElement_mul (g₁ := t) (g₂ := m)
        rw [MulAut.conj_apply] at hconj
        rw [hconj, ← mul_assoc]
      rw [heq]
      simpa using (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem (H := normalizer (Ah : Set Γ)) hmN.2) ⁅t, m⁆).mp htm
    exact ((Gh ⊓ centralizerSection Ah Zh).mul_mem
      ((Gh ⊓ centralizerSection Ah Zh).mul_mem
        ((Gh ⊓ centralizerSection Ah Zh).inv_mem hcC) (hA_le_C hm0))
      ((LitGam.t_mem_C h c).mp hcC))
  obtain ⟨k, hk⟩ := hS2 ⟨d, hdS⟩
  have hk' : d ^ 2 ^ k = 1 := by
    have hval := congrArg Subtype.val hk
    simpa using hval
  have hdA : d ∈ Ah :=
    lit_two_mem_of_normal hA_le_C hnormC h.sylow.2.1 h.sylow.2.2 hdC (k := k) hk'
  have hcomm_eq : ⁅s, t⁆ = s * d⁻¹ * s⁻¹ := by
    rw [hd_def, commutatorElement_def]
    group
  rw [hcomm_eq]
  exact (Subgroup.mem_normalizer_iff.mp (hSN hs).2 (d⁻¹)).mp (Ah.inv_mem hdA)

end CFSG.OddStandard.HigherRank.YamadaG23
