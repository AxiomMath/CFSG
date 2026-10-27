module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.ChainLemma
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.SylowNormalizerD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.K1Case
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.PhiMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathSplit

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private theorem THyp.mem_normalizer_Q_of_mem_T (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {Q T : Subgroup G} (hQ : QHyp L A D t Q) (hT : THyp S D Q t T) {x : G} (hx : x ∈ T) :
    x ∈ normalizer (Q : Set G) := by
  refine mem_normalizer_iff.2 fun q => ⟨?_, ?_⟩
  · intro hq
    exact THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT (Subgroup.le_normalizer hx) q hq
  · intro hq
    have h1 := THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT
      (Subgroup.le_normalizer (T.inv_mem hx)) (x * q * x⁻¹) hq
    have e : x⁻¹ * (x * q * x⁻¹) * (x⁻¹)⁻¹ = q := by group
    rwa [e] at h1

private theorem ThCyc.phiQ_b_eq_one_or_vConj_t (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {Q T : Subgroup G} (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) {e : G}
    (heNV : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) :
    phiQ hD Q b = 1 ∨ phiQ hD Q b = vConj hD t := by
  have hbNV : b ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    ThCyc.b_mem_NV W W2 hD hb hQ
  have hβH : ∀ n ∈ L ⊓ normalizer (A : Set G),
      vConj hD n * phiQ hD Q b = phiQ hD Q b * vConj hD n :=
    fun n hn => ThCyc.vConj_commute_phiQ H W W2 hD h4 hb hQ hq4 hsq heNV heK1 hn hbNV
  have htQ : t ∈ normalizer (Q : Set G) :=
    THyp.mem_normalizer_Q_of_mem_T H W W2 hD F h4 hb hQ hT hT.t_mem
  have htb : t * b * t⁻¹ = b := by
    have hcomm : t * b = b * t := H.comm_of_mem_L (W.B_le W2.b_mem)
    rw [hcomm]
    group
  have hβτ : vConj hD t * phiQ hD Q b = phiQ hD Q b * vConj hD t := by
    have h := QHyp.phiQ_conj hD hQ hq4 hsq htQ hbNV
    rw [htb] at h
    exact h.symm
  have hβA : ∀ x : VSub hD, x.val ∈ A → phiQ hD Q b x = x :=
    fun x hx => ThCyc.phiQ_b_apply H W W2 hD h4 hb hQ hq4 hsq x hx
  exact H.eq_one_or_eq_vConj_t W W2 hD h4 hβH hβτ hβA

private theorem ThCyc.tau_phiQ_e_cases (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {Q T : Subgroup G} (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {e : G} (heNV : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) :
    vConj hD t * phiQ hD Q e * vConj hD t = phiQ hD Q e ∨
      vConj hD t * phiQ hD Q e * vConj hD t = phiQ hD Q e + phiQ hD Q b := by
  have htQ : t ∈ normalizer (Q : Set G) :=
    THyp.mem_normalizer_Q_of_mem_T H W W2 hD F h4 hb hQ hT hT.t_mem
  have hteNV : t * e * t⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) :=
    QHyp.conj_mem_NV hD hQ hq4 hsq htQ heNV
  have hconj := QHyp.phiQ_conj hD hQ hq4 hsq htQ heNV
  have hττ : vConj hD t * vConj hD t = 1 := H.vConj_t_mul_self W W2 hD
  have hkey : phiQ hD Q (t * e * t⁻¹) = vConj hD t * phiQ hD Q e * vConj hD t := by
    calc phiQ hD Q (t * e * t⁻¹)
        = phiQ hD Q (t * e * t⁻¹) * 1 := (mul_one _).symm
      _ = phiQ hD Q (t * e * t⁻¹) * (vConj hD t * vConj hD t) := by rw [hττ]
      _ = (phiQ hD Q (t * e * t⁻¹) * vConj hD t) * vConj hD t := (mul_assoc _ _ _).symm
      _ = (vConj hD t * phiQ hD Q e) * vConj hD t := by rw [hconj]
      _ = vConj hD t * phiQ hD Q e * vConj hD t := rfl
  have hne := ThCyc.phiQ_ne_of_not_mem_K1 H W W2 hD h4 hb hQ hq4 hsq heNV heK1
  rcases H.phiQ_cases W W2 hD h4 hb hQ hq4 hsq heNV heK1 hteNV with h0 | hb' | he' | hsum
  · exfalso
    have hzero : vConj hD t * phiQ hD Q e * vConj hD t = 0 := by rw [← hkey, h0]
    have hw0 : phiQ hD Q e = 0 := by
      calc phiQ hD Q e
          = (vConj hD t * vConj hD t) * phiQ hD Q e *
              (vConj hD t * vConj hD t) := by rw [hττ, one_mul, mul_one]
        _ = vConj hD t * (vConj hD t * phiQ hD Q e * vConj hD t) * vConj hD t := by
              noncomm_ring
        _ = vConj hD t * 0 * vConj hD t := by rw [hzero]
        _ = 0 := by simp
    exact hne.1 hw0
  · exfalso
    have hzero : vConj hD t * phiQ hD Q e * vConj hD t = phiQ hD Q b := by
      rw [← hkey, hb']
    have hβτ : vConj hD t * phiQ hD Q b = phiQ hD Q b * vConj hD t := by
      have htb : t * b * t⁻¹ = b := by
        have hcomm : t * b = b * t := H.comm_of_mem_L (W.B_le W2.b_mem)
        rw [hcomm]
        group
      have h := QHyp.phiQ_conj hD hQ hq4 hsq htQ (ThCyc.b_mem_NV W W2 hD hb hQ)
      rw [htb] at h
      exact h.symm
    have hwβ : phiQ hD Q e = phiQ hD Q b := by
      calc phiQ hD Q e
          = (vConj hD t * vConj hD t) * phiQ hD Q e *
              (vConj hD t * vConj hD t) := by rw [hττ, one_mul, mul_one]
        _ = vConj hD t * (vConj hD t * phiQ hD Q e * vConj hD t) * vConj hD t := by
              noncomm_ring
        _ = vConj hD t * phiQ hD Q b * vConj hD t := by rw [hzero]
        _ = phiQ hD Q b := by rw [hβτ, mul_assoc, hττ, mul_one]
    exact hne.2 hwβ
  · exact Or.inl (by rw [← hkey, he'])
  · exact Or.inr (by rw [← hkey, hsum, add_comm])

private theorem ThCyc.false_of_tau_mem_phiQ (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {Q T : Subgroup G} (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {g : G} (hgT : g ∈ normalizer (T : Set G)) (hgM : g ∉ normalizer (D : Set G))
    {e : G} (heNV : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4)
    (hmem : vConj hD t = phiQ hD Q b ∨ vConj hD t = phiQ hD Q e ∨
      vConj hD t = phiQ hD Q e + phiQ hD Q b) : False := by
  have hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
    THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT hgT
  have hgNQ : g ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨hgQ q, fun hq => ?_⟩
    have h1 := THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT
      ((normalizer (T : Set G)).inv_mem hgT) (g * q * g⁻¹) hq
    have e : g⁻¹ * (g * q * g⁻¹) * (g⁻¹)⁻¹ = q := by group
    rwa [e] at h1
  have hgV : g ∈ normalizer (omega1 D hD.comm : Set G) :=
    QHyp.mem_normalizer_omega1 hD hQ hgNQ
  have hgu : g⁻¹ * t * g ∈ normalizer (D : Set G) := by
    have hmemT : g⁻¹ * t * g ∈ T := by
      simpa using (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hgT) t).1 hT.t_mem
    exact hT.le_normalizer hmemT
  let 𝒲 : Set (AddMonoid.End (VSub hD)) :=
    {f | ∃ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      f = phiQ hD Q c}
  have h𝒲g : ∀ f ∈ 𝒲, vConj hD g⁻¹ * f * vConj hD g ∈ 𝒲 := by
    rintro f ⟨c, hc, rfl⟩
    have hginv : g⁻¹ ∈ normalizer (Q : Set G) := (normalizer (Q : Set G)).inv_mem hgNQ
    have hc' : g⁻¹ * c * g ∈ normalizer (Q : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G) := by
      simpa using QHyp.conj_mem_NV hD hQ hq4 hsq hginv hc
    refine ⟨g⁻¹ * c * g, hc', ?_⟩
    have h := QHyp.phiQ_conj hD hQ hq4 hsq hginv hc
    have h' : phiQ hD Q (g⁻¹ * c * g) * vConj hD g⁻¹ = vConj hD g⁻¹ * phiQ hD Q c := by
      simpa using h
    have hinv : vConj hD g⁻¹ * vConj hD g = 1 := vConj_inv_mul hD hgV
    calc vConj hD g⁻¹ * phiQ hD Q c * vConj hD g
        = (phiQ hD Q (g⁻¹ * c * g) * vConj hD g⁻¹) * vConj hD g := by rw [h']
      _ = phiQ hD Q (g⁻¹ * c * g) * (vConj hD g⁻¹ * vConj hD g) := by rw [mul_assoc]
      _ = phiQ hD Q (g⁻¹ * c * g) := by rw [hinv, mul_one]
  have h𝒲H : ∀ f ∈ 𝒲, ∀ n ∈ L ⊓ normalizer (A : Set G),
      vConj hD n * f = f * vConj hD n := by
    rintro f ⟨c, hc, rfl⟩ n hn
    exact ThCyc.vConj_commute_phiQ H W W2 hD h4 hb hQ hq4 hsq heNV heK1 hn hc
  have hτW : vConj hD t ∈ 𝒲 := by
    have hbNV : b ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
      ThCyc.b_mem_NV W W2 hD hb hQ
    rcases hmem with h | h | h
    · exact ⟨b, hbNV, h⟩
    · exact ⟨e, heNV, h⟩
    · refine ⟨e * b, Subgroup.mul_mem _ heNV hbNV, ?_⟩
      rw [QHyp.phiQ_mul hD hQ hq4 hsq heNV hbNV]
      exact h
  exact ThCyc.false_of_vConj_t_mem H W W2 hD h4 hb hQ hgQ hgV hgu hgM h𝒲g h𝒲H hτW

private theorem ThCyc.exists_g_wComm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {Q T : Subgroup G} (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {g₀ : G} (hg₀T : g₀ ∈ normalizer (T : Set G)) (hg₀M : g₀ ∉ normalizer (D : Set G))
    {e : G} (heNV : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (heK1 : e ∉ ThCyc.K1 H W W2 hD h4) (hβ1 : phiQ hD Q b = 1)
    (hτw : vConj hD t * phiQ hD Q e * vConj hD t = phiQ hD Q e + 1) :
    ∃ g : G, g ∈ normalizer (T : Set G) ∧ g ∈ normalizer (Q : Set G) ∧
      g ∉ normalizer (D : Set G) ∧ g ∈ wComm hD (phiQ hD Q e) := by
  have hg₀Q : ∀ q ∈ Q, g₀ * q * g₀⁻¹ ∈ Q :=
    THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT hg₀T
  have hg₀NQ : g₀ ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨hg₀Q q, fun hq => ?_⟩
    have h1 := THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT
      ((normalizer (T : Set G)).inv_mem hg₀T) (g₀ * q * g₀⁻¹) hq
    have e : g₀⁻¹ * (g₀ * q * g₀⁻¹) * (g₀⁻¹)⁻¹ = q := by group
    rwa [e] at h1
  have hg₀V : g₀ ∈ normalizer (omega1 D hD.comm : Set G) :=
    QHyp.mem_normalizer_omega1 hD hQ hg₀NQ
  have hbNV : b ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    ThCyc.b_mem_NV W W2 hD hb hQ
  have hc₀NV : g₀ * e * g₀⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) :=
    QHyp.conj_mem_NV hD hQ hq4 hsq hg₀NQ heNV
  have hconj := QHyp.phiQ_conj hD hQ hq4 hsq hg₀NQ heNV
  have hcases := H.phiQ_cases W W2 hD h4 hb hQ hq4 hsq heNV heK1 hc₀NV
  have hne := ThCyc.phiQ_ne_of_not_mem_K1 H W W2 hD h4 hb hQ hq4 hsq heNV heK1
  have hw1 : phiQ hD Q e ≠ 1 := fun h => hne.2 (h.trans hβ1.symm)
  have hρgw : vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹ =
      phiQ hD Q (g₀ * e * g₀⁻¹) := by
    rw [← hconj, mul_assoc, vConj_mul_inv hD hg₀V, mul_one]
  rcases hcases with h0 | hβ | hw | hsum
  · exfalso
    have hz : vConj hD g₀ * phiQ hD Q e = 0 := by
      have h1 : vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹ = 0 := by rw [hρgw, h0]
      calc vConj hD g₀ * phiQ hD Q e
          = (vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹) * vConj hD g₀ := by
              rw [mul_assoc, vConj_inv_mul hD hg₀V, mul_one]
        _ = 0 := by rw [h1, zero_mul]
    have hzero : phiQ hD Q e = 0 := by
      calc phiQ hD Q e = (vConj hD g₀⁻¹ * vConj hD g₀) * phiQ hD Q e := by
            rw [vConj_inv_mul hD hg₀V, one_mul]
        _ = vConj hD g₀⁻¹ * (vConj hD g₀ * phiQ hD Q e) := by rw [mul_assoc]
        _ = 0 := by rw [hz, mul_zero]
    exact hne.1 hzero
  · exfalso
    have hz : vConj hD g₀ * phiQ hD Q e = vConj hD g₀ := by
      have h1 : vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹ = 1 := by
        rw [hρgw, hβ, hβ1]
      calc vConj hD g₀ * phiQ hD Q e
          = (vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹) * vConj hD g₀ := by
              rw [mul_assoc, vConj_inv_mul hD hg₀V, mul_one]
        _ = 1 * vConj hD g₀ := by rw [h1]
        _ = vConj hD g₀ := one_mul _
    have hone : phiQ hD Q e = 1 := by
      calc phiQ hD Q e = (vConj hD g₀⁻¹ * vConj hD g₀) * phiQ hD Q e := by
            rw [vConj_inv_mul hD hg₀V, one_mul]
        _ = vConj hD g₀⁻¹ * (vConj hD g₀ * phiQ hD Q e) := by rw [mul_assoc]
        _ = vConj hD g₀⁻¹ * vConj hD g₀ := by rw [hz]
        _ = 1 := vConj_inv_mul hD hg₀V
    exact hw1 hone
  · refine ⟨g₀, hg₀T, hg₀NQ, hg₀M, ⟨hg₀V, ?_⟩⟩
    have hρ : vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹ = phiQ hD Q e := by
      rw [hρgw, hw]
    calc vConj hD g₀ * phiQ hD Q e
        = vConj hD g₀ * phiQ hD Q e * 1 := (mul_one _).symm
      _ = vConj hD g₀ * phiQ hD Q e * (vConj hD g₀⁻¹ * vConj hD g₀) := by
            rw [vConj_inv_mul hD hg₀V]
      _ = (vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹) * vConj hD g₀ := by noncomm_ring
      _ = phiQ hD Q e * vConj hD g₀ := by rw [hρ]
  · refine ⟨t * g₀, Subgroup.mul_mem _ (Subgroup.le_normalizer hT.t_mem) hg₀T,
      Subgroup.mul_mem _ (THyp.mem_normalizer_Q_of_mem_T H W W2 hD F h4 hb hQ hT hT.t_mem)
        hg₀NQ, ?_, ?_⟩
    · intro h
      have htD : t ∈ normalizer (D : Set G) := H.t_mem_normalizer_D W W2 hD
      have h1 : t⁻¹ * (t * g₀) ∈ normalizer (D : Set G) :=
        (normalizer (D : Set G)).mul_mem ((normalizer (D : Set G)).inv_mem htD) h
      have e : t⁻¹ * (t * g₀) = g₀ := by group
      exact hg₀M (by rwa [e] at h1)
    · refine ⟨Subgroup.mul_mem _ (H.t_mem_normalizer_omega1 W W2 hD) hg₀V, ?_⟩
      have hρgw' : vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹ =
          phiQ hD Q e + 1 := by
        rw [hρgw, hsum, hβ1, add_comm]
      have htV : t ∈ normalizer (omega1 D hD.comm : Set G) :=
        H.t_mem_normalizer_omega1 W W2 hD
      have hρ : vConj hD (t * g₀) = vConj hD t * vConj hD g₀ := vConj_mul hD htV hg₀V
      have hρinv : vConj hD (t * g₀)⁻¹ = vConj hD g₀⁻¹ * vConj hD t := by
        have htinv : t⁻¹ = t :=
          inv_eq_of_mul_eq_one_right (by rw [← sq]; exact H.sq_t)
        have h := vConj_mul hD (n := g₀⁻¹) (m := t⁻¹)
          ((normalizer (omega1 D hD.comm : Set G)).inv_mem hg₀V)
          ((normalizer (omega1 D hD.comm : Set G)).inv_mem htV)
        rw [show g₀⁻¹ * t⁻¹ = (t * g₀)⁻¹ by group, htinv] at h
        exact h
      have hmain : vConj hD (t * g₀) * phiQ hD Q e * vConj hD (t * g₀)⁻¹ =
          phiQ hD Q e := by
        rw [hρ, hρinv]
        calc (vConj hD t * vConj hD g₀) * phiQ hD Q e * (vConj hD g₀⁻¹ * vConj hD t)
            = vConj hD t * (vConj hD g₀ * phiQ hD Q e * vConj hD g₀⁻¹) *
                vConj hD t := by noncomm_ring
          _ = vConj hD t * (phiQ hD Q e + 1) * vConj hD t := by rw [hρgw']
          _ = vConj hD t * phiQ hD Q e * vConj hD t +
                vConj hD t * 1 * vConj hD t := by noncomm_ring
          _ = (phiQ hD Q e + 1) + 1 := by rw [hτw, mul_one, H.vConj_t_mul_self W W2 hD]
          _ = phiQ hD Q e := by rw [add_assoc, VSub.add_self hD 1, add_zero]
      have htg₀V : t * g₀ ∈ normalizer (omega1 D hD.comm : Set G) :=
        (normalizer (omega1 D hD.comm : Set G)).mul_mem htV hg₀V
      calc vConj hD (t * g₀) * phiQ hD Q e
          = vConj hD (t * g₀) * phiQ hD Q e * 1 := (mul_one _).symm
        _ = vConj hD (t * g₀) * phiQ hD Q e *
              (vConj hD (t * g₀)⁻¹ * vConj hD (t * g₀)) := by rw [vConj_inv_mul hD htg₀V]
        _ = (vConj hD (t * g₀) * phiQ hD Q e * vConj hD (t * g₀)⁻¹) *
              vConj hD (t * g₀) := by noncomm_ring
        _ = phiQ hD Q e * vConj hD (t * g₀) := by rw [hmain]

theorem ThCyc.exists_wreath_or_F4 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (F : SylowFacts L S B Aa) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    ∃ (Q T : Subgroup G) (g : G) (w : AddMonoid.End (VSub hD)),
      QHyp L A D t Q ∧ THyp S D Q t T ∧ (∀ q ∈ Q, q ^ 4 = 1) ∧
      (∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) ∧
      g ∈ normalizer (T : Set G) ∧ g ∈ normalizer (Q : Set G) ∧ g ∉ normalizer (D : Set G) ∧
      g ∈ wComm hD w ∧
      (∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n) ∧
      vConj hD t * w * vConj hD t = w + 1 ∧ phiQ hD Q b = 1 ∧
      (∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
        phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1) ∧
      w ≠ 0 ∧ w ≠ 1 ∧ (w * w = w ∨ w * w = w + 1) := by
  obtain ⟨Q, hQ⟩ := H.exists_QHyp W W2 hD h4
  obtain ⟨T, hT⟩ := H.exists_THyp W W2 hD hQ
  obtain ⟨g₀, hg₀T, hg₀M⟩ := H.exists_mem_normalizer_not_mem W W2 hD F h4 hb hT
  obtain ⟨hq4, hsq, _⟩ :=
    hT.exponent_four_of_mem_normalizer H W W2 hD F h4 hb hQ hg₀T hg₀M
  have hnotK1 : ¬ (T ⊓ (normalizer (D : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G)) ≤ ThCyc.K1 H W W2 hD h4) :=
    fun hle => H.false_of_inf_K_le_K1 W W2 hD F h4 hb hQ hT hg₀T hg₀M hle
  obtain ⟨e, heTK, heK1⟩ := SetLike.not_le_iff_exists.mp hnotK1
  have heNV : e ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    ⟨THyp.mem_normalizer_Q_of_mem_T H W W2 hD F h4 hb hQ hT heTK.1, heTK.2.2⟩
  have hβcases :=
    ThCyc.phiQ_b_eq_one_or_vConj_t H W W2 hD F h4 hb hQ hT hq4 hsq heNV heK1
  have hτwcases := ThCyc.tau_phiQ_e_cases H W W2 hD F h4 hb hQ hT hq4 hsq heNV heK1
  have hw0 : phiQ hD Q e ≠ 0 :=
    (ThCyc.phiQ_ne_of_not_mem_K1 H W W2 hD h4 hb hQ hq4 hsq heNV heK1).1
  have hwβ : phiQ hD Q e ≠ phiQ hD Q b :=
    (ThCyc.phiQ_ne_of_not_mem_K1 H W W2 hD h4 hb hQ hq4 hsq heNV heK1).2
  have hwH : ∀ n ∈ L ⊓ normalizer (A : Set G),
      vConj hD n * phiQ hD Q e = phiQ hD Q e * vConj hD n :=
    fun n hn => ThCyc.vConj_commute_phiQ H W W2 hD h4 hb hQ hq4 hsq heNV heK1 hn heNV
  have hCE : ∀ f : AddMonoid.End (VSub hD),
      (f = phiQ hD Q e ∨ f = phiQ hD Q e * phiQ hD Q e + phiQ hD Q e) →
      f * vConj hD t = vConj hD t * f →
      f = 0 ∨ f = 1 ∨ f = vConj hD t + 1 ∨ f = vConj hD t := by
    intro f hf hfτ
    have hfH : ∀ n ∈ L ⊓ normalizer (A : Set G),
        vConj hD n * f = f * vConj hD n := by
      rcases hf with rfl | rfl
      · exact hwH
      · intro n hn
        have h1 := hwH n hn
        calc vConj hD n * (phiQ hD Q e * phiQ hD Q e + phiQ hD Q e)
            = vConj hD n * (phiQ hD Q e * phiQ hD Q e) +
                vConj hD n * phiQ hD Q e := by rw [mul_add]
          _ = (vConj hD n * phiQ hD Q e) * phiQ hD Q e +
                vConj hD n * phiQ hD Q e := by rw [← mul_assoc]
          _ = (phiQ hD Q e * vConj hD n) * phiQ hD Q e +
                phiQ hD Q e * vConj hD n := by rw [h1]
          _ = phiQ hD Q e * (vConj hD n * phiQ hD Q e) +
                phiQ hD Q e * vConj hD n := by rw [mul_assoc]
          _ = phiQ hD Q e * (phiQ hD Q e * vConj hD n) +
                phiQ hD Q e * vConj hD n := by rw [h1]
          _ = (phiQ hD Q e * phiQ hD Q e + phiQ hD Q e) * vConj hD n := by
                rw [add_mul, mul_assoc]
    exact H.end_cases_of_commute W W2 hD h4 hfH hfτ.symm
  have hττ : vConj hD t * vConj hD t = 1 := H.vConj_t_mul_self W W2 hD
  have htau := tau_cases_of_char_two (h2 := VSub.add_self hD) hττ hβcases hw0 hwβ hτwcases hCE
  rcases htau with hτmem | ⟨hβ1, hτw1, hwsq⟩
  · exfalso
    have hmem : vConj hD t = phiQ hD Q b ∨ vConj hD t = phiQ hD Q e ∨
        vConj hD t = phiQ hD Q e + phiQ hD Q b := by
      rcases hτmem with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact ThCyc.false_of_tau_mem_phiQ H W W2 hD F h4 hb hQ hT hq4 hsq hg₀T hg₀M
      heNV heK1 hmem
  · obtain ⟨g, hgT, hgQ, hgM, hgw⟩ :=
      ThCyc.exists_g_wComm H W W2 hD F h4 hb hQ hT hq4 hsq hg₀T hg₀M heNV heK1 hβ1 hτw1
    refine ⟨Q, T, g, phiQ hD Q e, hQ, hT, hq4, hsq, hgT, hgQ, hgM, hgw, hwH, hτw1,
      hβ1, ?_, hw0, ?_, hwsq⟩
    · intro c hc
      rcases H.phiQ_cases W W2 hD h4 hb hQ hq4 hsq heNV heK1 hc with h0 | hb' | he' | hsum
      · exact Or.inl h0
      · exact Or.inr (Or.inl (hb'.trans hβ1))
      · exact Or.inr (Or.inr (Or.inl he'))
      · exact Or.inr (Or.inr (Or.inr (by rw [hsum, hβ1, add_comm])))
    · intro h
      exact hwβ (h.trans hβ1.symm)

end CFSG.EvenSporadicStandard.ThStd

end
