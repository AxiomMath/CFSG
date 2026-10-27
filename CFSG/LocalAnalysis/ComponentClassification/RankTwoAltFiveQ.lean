module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveJ2
public import CFSG.GH74.Uniqueness.SU.SU5Facts
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ

public section

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

namespace CFSG.ComponentClassification.RankTwoAltFive

theorem j2Syl_centralizer_R : ∀ s : J2Syl, (∀ r : J2Syl, r ∈ J2Syl.R → s * r = r * s) →
    s = 1 ∨ s = J2Syl.z0 := by decide +kernel

variable {G : Type} [Group G] [Finite G]

structure QFacts (S V₀ : Subgroup G) (z : G) (Q : Subgroup G) : Prop where
  z_mem_V₀ : z ∈ V₀
  z_ne_one : z ≠ 1
  z_central : ∀ y ∈ S, z * y = y * z
  le : Q ≤ S
  normal : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q
  q8d8 : IsQ8D8 Q
  z_mem : z ∈ Q
  comm_mem : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ zpowers z
  V₀_le : V₀ ≤ Q
  conj_mem : ∀ t ∈ S, t ≠ 1 → IsConj z t → t ∈ Q
  isConj : ∀ t ∈ Q, t ≠ 1 → t * t = 1 → IsConj z t
  closed : ∀ t ∈ Q, ∀ c ∈ centralizer ({z} : Set G), c⁻¹ * t * c ∈ S → c⁻¹ * t * c ∈ Q
  centralizer_eq : ∀ s ∈ S, (∀ q ∈ Q, s * q = q * s) → s = 1 ∨ s = z

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem mem_V₀_of_mem_Zc (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) {t : G} (ht : t ∈ Zc P) :
    t ∈ V₀ := by
  obtain ⟨htP, htc⟩ := mem_Zc.mp ht
  have htV : t ∈ R ⊔ T := by
    rw [← hPC]
    exact mem_inf.mpr ⟨htP, mem_centralizer_iff.mpr fun v hv => (htc v (hVP hv)).symm⟩
  obtain ⟨y, hyP, hyV⟩ : ∃ y ∈ P, y ∉ R ⊔ T := by
    by_contra hno
    push Not at hno
    have h1 := Subgroup.card_le_of_le (show P ≤ R ⊔ T from hno)
    rw [hP64, h.loc.card] at h1
    omega
  refine h.P_fixed hP hPC hyP hyV htV ?_
  rw [← htc y hyP]
  group

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem exists_QFacts_of_eps_one (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S) :
    ∃ z : G, ∃ Q : Subgroup G, QFacts (S : Subgroup G) V₀ z Q := by
  have hV₀2 : ∀ w ∈ V₀, w * w = 1 := fun w hw => h.mul_self (h.V₀_le hw)
  obtain ⟨z', hz', hz'1, -⟩ := exists_ne_one_ne h.card_V₀ hV₀2 (one_mem V₀)
  obtain ⟨x, hz'x, hemb⟩ := h.j2Emb_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e
    hV'16 hinf hsup hV'inv S hPS hz' hz'1
  obtain ⟨f, hf, hrange, -, -⟩ := id hemb
  set z := f J2Syl.z0 with hzdef
  have hz : IsZGen (S : Subgroup G) z := hrange ▸ isZGen_f hf
  have hJ := hemb.facts hz
  have hzS : ∀ y ∈ (S : Subgroup G), z * y = y * z := (hz.2.2 z hz.1).2 (Or.inr rfl)
  have hzV₀ : z ∈ V₀ := h.center_le_V₀ hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf
    hsup hV'inv S hPS hz.1 hzS
  have hz1 : z ≠ 1 := hz.2.1
  set Q := J2Syl.R.map f with hQdef
  have hQS : Q ≤ (S : Subgroup G) := hrange ▸ Subgroup.map_le_range f _
  have hQn : ∀ s ∈ (S : Subgroup G), ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := by
    rw [← hrange]
    rintro _ ⟨m, rfl⟩ _ ⟨r, hr, rfl⟩
    exact ⟨m * r * m⁻¹, J2Syl.R_normal m r hr, by simp⟩
  have hQq : IsQ8D8 Q := (isQ8D8_map_iff hf).2 J2Syl.isQ8D8_R
  have hzQ : z ∈ Q := Subgroup.mem_map_of_mem f J2Syl.z0_mem_R
  obtain ⟨R', -, -, -, -, -, huniq, -, -, -, -, -, hinv, -, hsqz, -⟩ := hJ.RV
  have hQR' : Q = R' := huniq Q hQS hQn hQq
  obtain ⟨-, ζ, hζQ, hζ1, hcen, hsq⟩ := hQq.facts
  have hzζ : z = ζ := ((hcen z hzQ).mp fun m hm => hzS m (hQS hm)).resolve_left hz1
  rw [← hzζ] at hsq
  have hz2 : z * z = 1 := hV₀2 z hzV₀
  have hsqm : ∀ t ∈ Q, t * t ∈ zpowers z := fun t ht => by
    rcases hsq t ht with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact mem_zpowers z
  have hsqc : ∀ t ∈ Q, ∀ y ∈ Q, t * t * y = y * (t * t) := fun t ht y hy => by
    rcases hsq t ht with h1 | h1
    · rw [h1]; group
    · rw [h1]; exact hzS y (hQS hy)
  have hV₀Q : V₀ ≤ Q := fun v hv => by
    by_cases hv1 : v = 1
    · rw [hv1]; exact one_mem _
    have hvZ : v ∈ Zc P := mem_Zc.mpr ⟨hVP (h.V₀_le hv), fun y hy => (P_comm_V₀ hP hv hy).symm⟩
    rw [hQR']
    exact ((hinv v (hPS (hVP (h.V₀_le hv)))).mpr (Or.inl ⟨hvZ, hv1⟩)).1
  have hconj : ∀ t ∈ (S : Subgroup G), t ≠ 1 → IsConj z t → t ∈ Q := by
    intro t htS ht1 hzt
    have ht2 : t * t = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hzt
      rw [← hc]
      calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    by_cases htP : t ∈ P
    · exact hV₀Q (h.mem_V₀_of_isConj hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup
        hV'inv hzV₀ hz1 htP ht2 hzt)
    · rw [hQR']
      exact ((hinv t htS).mpr (Or.inr ⟨htP, by rw [sq]; exact ht2⟩)).1
  have hisConj : ∀ t ∈ Q, t ≠ 1 → t * t = 1 → IsConj z t := by
    intro t htQ ht1 ht2
    have htS := hQS htQ
    rw [hQR'] at htQ
    rcases (hinv t htS).mp ⟨htQ, ht1, by rw [sq]; exact ht2⟩ with ⟨htZ, -⟩ | ⟨htP, -⟩
    · exact h.isConj_of_mem_V₀ hzV₀ hz1
        (h.mem_V₀_of_mem_Zc hP hPC hP64 hVP htZ) ht1
    · obtain ⟨c, -, hc⟩ := hJ.conj_invol t htS htP (by rw [sq]; exact ht2)
      exact ((h.isConj_of_mem_V₀ hzV₀ hz1 hz' hz'1).trans hz'x).trans
        (isConj_iff.mpr ⟨c, hc⟩)
  refine ⟨z, Q, hzV₀, hz1, hzS, hQS, hQn, hQq, hzQ, ?_, hV₀Q, hconj, hisConj, ?_, ?_⟩
  ·
    intro a ha b hb
    have e : a * b * a⁻¹ * b⁻¹ = (a * b) * (a * b) * (a * a)⁻¹ * (b * b)⁻¹ := by
      have hc : b * (a * a)⁻¹ = (a * a)⁻¹ * b := by
        calc b * (a * a)⁻¹ = (a * a)⁻¹ * ((a * a) * b) * (a * a)⁻¹ := by group
          _ = (a * a)⁻¹ * (b * (a * a)) * (a * a)⁻¹ := by rw [hsqc a ha b hb]
          _ = (a * a)⁻¹ * b := by group
      calc a * b * a⁻¹ * b⁻¹ = a * b * a * ((a * a)⁻¹ * b) * (b * b)⁻¹ := by group
        _ = a * b * a * (b * (a * a)⁻¹) * (b * b)⁻¹ := by rw [hc]
        _ = (a * b) * (a * b) * (a * a)⁻¹ * (b * b)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hsqm _ (mul_mem ha hb)) (inv_mem (hsqm a ha))) (inv_mem (hsqm b hb))
  ·
    intro t htQ c hc hcS
    rcases hsq t htQ with h1 | h1
    · by_cases ht1 : t = 1
      · rw [ht1, mul_one, inv_mul_cancel]; exact one_mem _
      have hct1 : c⁻¹ * t * c ≠ 1 := fun he => ht1 (by
        calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
          _ = 1 := by rw [he]; group)
      exact hconj _ hcS hct1 ((hisConj t htQ ht1 h1).trans (isConj_iff.mpr ⟨c⁻¹, by group⟩))
    · rw [hQR']
      refine hsqz _ hcS ?_
      rw [mem_centralizer_singleton_iff] at hc
      calc (c⁻¹ * t * c) ^ 2 = c⁻¹ * (t * t) * c := by rw [sq]; group
        _ = c⁻¹ * (z * c) := by rw [h1, mul_assoc]
        _ = z := by rw [← hc]; group
  ·
    rw [← hrange]
    rintro _ ⟨m, rfl⟩ hc
    have hm : ∀ r : J2Syl, r ∈ J2Syl.R → m * r = r * m := fun r hr =>
      hf (by rw [map_mul, map_mul]; exact hc (f r) (Subgroup.mem_map_of_mem f hr))
    rcases j2Syl_centralizer_R m hm with h1 | h1
    · left; rw [h1, map_one]
    · right; rw [h1]

theorem centralizer_le_normalizer_of_QFacts
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} {Q : Subgroup G} (hQ : QFacts (S : Subgroup G) V₀ z Q)
    (hnc : AS81.QbarNoComponent z Q) :
    centralizer ({z} : Set G) ≤ normalizer (Q : Set G) := by
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hQ.z_central y hy).symm
  have hS := isSylowOf_of_sylow_le S hSC
  have hz2 : z ^ 2 = 1 := by rw [sq]; exact h.mul_self (h.V₀_le hQ.z_mem_V₀)
  have h1 := AS81.centralizer_le_normalizer_of_goldschmidt hGold hz2 hS hQ.le hQ.z_mem
    hQ.comm_mem hQ.closed hnc
  rwa [h.oddCoreIn_centralizer_eq_bot_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e
    hV'16 hinf hsup hV'inv S hPS hQ.z_mem_V₀ hQ.z_ne_one hQ.z_central, sup_bot_eq] at h1

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
