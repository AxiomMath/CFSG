module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10t1_eq_zpowers {H : Type} [Group H] {A : Subgroup H} (hA : Nat.card A = 5) {a : H}
    (ha : a ∈ A) (ha1 : a ≠ 1) : orderOf a = 5 ∧ A = Subgroup.zpowers a := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hdvd : orderOf a ∣ 5 := hA ▸ Subgroup.orderOf_dvd_natCard A ha
  have hord : orderOf a = 5 :=
    ((Nat.dvd_prime (by norm_num)).mp hdvd).resolve_left fun h => ha1 (orderOf_eq_one_iff.mp h)
  refine ⟨hord, (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr ha) ?_).symm⟩
  rw [Nat.card_zpowers, hord, hA]

theorem a10t1_mem_pre {G Q : Type} [Group G] [Group Q] (J : Subgroup G) (ψ : ↥J →* Q)
    (Λ : Subgroup Q) {g : G} (hg : g ∈ J) : g ∈ a10Pre J ψ Λ ↔ ψ ⟨g, hg⟩ ∈ Λ := by
  unfold a10Pre
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem a10t1_inj {G Q : Type} [Group G] [Finite G] [Group Q] {P : Sylow 5 G} {J T : Subgroup G}
    (hTP : T ≤ (P : Subgroup G)) (ψ : ↥J →* Q)
    (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J) :
    ∀ (t : G) (ht : t ∈ J), t ∈ T → ψ ⟨t, ht⟩ = 1 → t = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hTp : IsPGroup 5 (T.subgroupOf J) := (P.isPGroup'.to_le hTP).comap_subtype
  have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
  have hOcop : Nat.Coprime 5 (Nat.card (rankThreePrimeCore 5 J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J
  have hcop : ¬ 5 ∣ Nat.card ψ.ker := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hOcop
  intro t ht hT h1
  have := u3main_eq_one_of_ker ψ hcop hTp ⟨t, ht⟩ (Subgroup.mem_subgroupOf.mpr hT) h1
  exact congrArg Subtype.val this

theorem a10t1_card_inf {G Q : Type} [Group G] [Group Q] {J T : Subgroup G} (hTJ : T ≤ J)
    (ψ : ↥J →* Q) (hinj : ∀ (t : G) (ht : t ∈ J), t ∈ T → ψ ⟨t, ht⟩ = 1 → t = 1)
    {S Λ : Subgroup Q} (hS : S = (T.subgroupOf J).map ψ) :
    Nat.card ↥(T ⊓ a10Pre J ψ Λ) = Nat.card ↥(S ⊓ Λ) := by
  have hle : T ⊓ a10Pre J ψ Λ ≤ J := inf_le_left.trans hTJ
  let ρ : ↥(T ⊓ a10Pre J ψ Λ) →* Q := ψ.comp (Subgroup.inclusion hle)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hinj a.1 (hle a.2) a.2.1 ha)
  have hrange : ρ.range = S ⊓ Λ := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hS]
        exact ⟨⟨a.1, hle a.2⟩, Subgroup.mem_subgroupOf.mpr a.2.1, rfl⟩
      · exact (a10t1_mem_pre J ψ Λ (hle a.2)).mp a.2.2
    · rintro ⟨hqS, hqΛ⟩
      rw [hS] at hqS
      obtain ⟨j, hj, rfl⟩ := hqS
      have hjT : (j : G) ∈ T := hj
      exact ⟨⟨j.1, hjT, (a10t1_mem_pre J ψ Λ j.2).mpr hqΛ⟩, rfl⟩
  rw [← hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv

theorem a10t1_sup_eq {G : Type} [Group G] [Finite G] {T A B : Subgroup G} (hAT : A ≤ T)
    (hBT : B ≤ T) (hT : Nat.card T = 25) (hA : Nat.card A = 5) (hB : Nat.card B = 5)
    (hAB : A ⊓ B = ⊥) : A ⊔ B = T := by
  have hsupT : A ⊔ B ≤ T := sup_le hAT hBT
  have hd1 : Nat.card ↥(A ⊔ B) ∣ 25 := by
    have := Subgroup.card_dvd_of_le hsupT
    rwa [hT] at this
  obtain ⟨k, hk⟩ : 5 ∣ Nat.card ↥(A ⊔ B) := hA ▸ Subgroup.card_dvd_of_le le_sup_left
  rw [hk] at hd1
  have hk5 : k ∣ 5 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5) (show 5 * k ∣ 5 * 5 from hd1)
  rcases (Nat.dvd_prime (by norm_num)).mp hk5 with h1 | h5
  · exfalso
    have hAeq : A = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    have hBA : B ≤ A := hAeq ▸ le_sup_right
    have hB1 : B = ⊥ := by
      rw [← hAB, inf_comm, inf_eq_left.mpr hBA]
    rw [hB1, Subgroup.card_bot] at hB
    omega
  · exact Subgroup.eq_of_le_of_card_ge hsupT (by omega)

theorem a10t1_mem_sup_of_comm {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {d : G} (hd : d ∈ A ⊔ B) :
    ∃ u ∈ A, ∃ v ∈ B, u * v = d := by
  rw [Subgroup.sup_eq_closure] at hd
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hd
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, A.mul_mem hy₁ hy₂, z₁ * z₂, B.mul_mem hz₁ hz₂, ?_⟩
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by simp only [mul_assoc]
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [h y₂ hy₂ z₁ hz₁]
      _ = y₁ * z₁ * (y₂ * z₂) := by simp only [mul_assoc]
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, A.inv_mem hy, z⁻¹, B.inv_mem hz, ?_⟩
    calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := (mul_inv_rev z y).symm
      _ = (y * z)⁻¹ := by rw [h y hy z hz]

theorem a10t1_core {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q] {J T U : Subgroup G}
    (ψ : ↥J →* Q) (hTJ : T ≤ J) (hTcard : Nat.card T = 25)
    (hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hinj : ∀ (t : G) (ht : t ∈ J), t ∈ T → ψ ⟨t, ht⟩ = 1 → t = 1)
    {S Λ₁ Λ₂ : Subgroup Q} (hSyl : S = (T.subgroupOf J).map ψ) (hΛ : A10GammaStructAt Q S Λ₁ Λ₂)
    (hγ : ∃ (d : G) (hd : d ∈ J), d ∈ U ⊓ T ∧ ψ ⟨d, hd⟩ ≠ 1 ∧
      Nat.card (Subgroup.centralizer ({ψ ⟨d, hd⟩} : Set Q)) = 25) :
    ∃ a₁ a₂ : G, a₁ ∈ T ∧ a₂ ∈ T ∧ orderOf a₁ = 5 ∧ orderOf a₂ = 5 ∧
      a₁ * a₂ ∈ U ∧ T = Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ∧
      a₁ ∉ Subgroup.zpowers a₂ ∧
      Subgroup.zpowers a₁ = T ⊓ a10Pre J ψ Λ₁ ∧
      Subgroup.zpowers a₂ = T ⊓ a10Pre J ψ Λ₂ ∧
      (∀ A : Subgroup G, IsFiveCycleLine J T ψ A →
        A = Subgroup.zpowers a₁ ∨ A = Subgroup.zpowers a₂) := by
  obtain ⟨d, hdJ, hdUT, hψd, hcentd⟩ := hγ
  have hψS : ∀ (t : G) (ht : t ∈ J), t ∈ T → ψ ⟨t, ht⟩ ∈ S := by
    intro t ht htT
    rw [hSyl]
    exact ⟨⟨t, ht⟩, Subgroup.mem_subgroupOf.mpr htT, rfl⟩
  have hA₁card : Nat.card ↥(T ⊓ a10Pre J ψ Λ₁) = 5 :=
    (a10t1_card_inf hTJ ψ hinj hSyl).trans hΛ.S_card₁
  have hA₂card : Nat.card ↥(T ⊓ a10Pre J ψ Λ₂) = 5 :=
    (a10t1_card_inf hTJ ψ hinj hSyl).trans hΛ.S_card₂
  have hA₁₂ : (T ⊓ a10Pre J ψ Λ₁) ⊓ (T ⊓ a10Pre J ψ Λ₂) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨⟨htT, ht₁⟩, -, ht₂⟩ := ht
    have htJ : t ∈ J := hTJ htT
    have h1 : ψ ⟨t, htJ⟩ ∈ Λ₁ := (a10t1_mem_pre J ψ Λ₁ htJ).mp ht₁
    have h2 : ψ ⟨t, htJ⟩ ∈ Λ₂ := (a10t1_mem_pre J ψ Λ₂ htJ).mp ht₂
    have h12 : ψ ⟨t, htJ⟩ ∈ Λ₁ ⊓ Λ₂ := ⟨h1, h2⟩
    rw [hΛ.inf_bot, Subgroup.mem_bot] at h12
    exact Subgroup.mem_bot.mpr (hinj t htJ htT h12)
  have hsup : (T ⊓ a10Pre J ψ Λ₁) ⊔ (T ⊓ a10Pre J ψ Λ₂) = T :=
    a10t1_sup_eq inf_le_left inf_le_left hTcard hA₁card hA₂card hA₁₂
  obtain ⟨u, hu, v, hv, huv⟩ := a10t1_mem_sup_of_comm (A := T ⊓ a10Pre J ψ Λ₁)
    (B := T ⊓ a10Pre J ψ Λ₂) (fun a ha b hb => hTcomm a ha.1 b hb.1)
    (by rw [hsup]; exact hdUT.2)
  have hu1 : u ≠ 1 := by
    intro hu1
    have hdv : d = v := by rw [← huv, hu1, one_mul]
    have hd2 : ψ ⟨d, hdJ⟩ ∈ Λ₂ := (a10t1_mem_pre J ψ Λ₂ hdJ).mp (by rw [hdv]; exact hv.2)
    have := hΛ.cent₃₀₀ _ (hψS d hdJ hdUT.2) hψd (Or.inr hd2)
    omega
  have hv1 : v ≠ 1 := by
    intro hv1
    have hdu : d = u := by rw [← huv, hv1, mul_one]
    have hd1 : ψ ⟨d, hdJ⟩ ∈ Λ₁ := (a10t1_mem_pre J ψ Λ₁ hdJ).mp (by rw [hdu]; exact hu.2)
    have := hΛ.cent₃₀₀ _ (hψS d hdJ hdUT.2) hψd (Or.inl hd1)
    omega
  obtain ⟨hou, hAu⟩ := a10t1_eq_zpowers hA₁card hu hu1
  obtain ⟨hov, hAv⟩ := a10t1_eq_zpowers hA₂card hv hv1
  refine ⟨u, v, hu.1, hv.1, hou, hov, by rw [huv]; exact hdUT.1, ?_, ?_, hAu.symm, hAv.symm, ?_⟩
  · rw [← hAu, ← hAv]
    exact hsup.symm
  · rw [← hAv]
    intro huv'
    have h12 : u ∈ (T ⊓ a10Pre J ψ Λ₁) ⊓ (T ⊓ a10Pre J ψ Λ₂) := ⟨hu, huv'⟩
    rw [hA₁₂] at h12
    exact hu1 (Subgroup.mem_bot.mp h12)
  · intro A hA
    obtain ⟨hAT, hAcard, a, haJ, haA, hψa, hcenta⟩ := hA
    have ha1 : a ≠ 1 := by
      intro h
      apply hψa
      have : (⟨a, haJ⟩ : ↥J) = 1 := Subtype.ext h
      rw [this, map_one]
    have haT : a ∈ T := hAT haA
    have hmem : ψ ⟨a, haJ⟩ ∈ Λ₁ ∨ ψ ⟨a, haJ⟩ ∈ Λ₂ := by
      by_contra hcon
      push Not at hcon
      have := hΛ.cent₂₅ _ (hψS a haJ haT) hcon.1 hcon.2
      omega
    have hAeq : A = Subgroup.zpowers a := (a10t1_eq_zpowers hAcard haA ha1).2
    rcases hmem with h | h
    · left
      have haA₁ : a ∈ T ⊓ a10Pre J ψ Λ₁ := ⟨haT, (a10t1_mem_pre J ψ Λ₁ haJ).mpr h⟩
      exact hAeq.trans ((a10t1_eq_zpowers hA₁card haA₁ ha1).2.symm.trans hAu)
    · right
      have haA₂ : a ∈ T ⊓ a10Pre J ψ Λ₂ := ⟨haT, (a10t1_mem_pre J ψ Λ₂ haJ).mpr h⟩
      exact hAeq.trans ((a10t1_eq_zpowers hA₂card haA₂ ha1).2.symm.trans hAv)

theorem a10_T_lines (hX : A10Facts) (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q]
    (ψ : ↥J →* Q) (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) {S : Sylow 5 Q} (hSyl : (S : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ)
    {Λ₁ Λ₂ : Subgroup Q} (hΛ : A10GammaStructAt Q (S : Subgroup Q) Λ₁ Λ₂) {U : Subgroup G}
    (hUP : IIPlane 5 P x J U) (hγ : A10PlaneShape J (u3T P x J) ψ U) :
    ∃ a₁ a₂ : G, a₁ ∈ u3T P x J ∧ a₂ ∈ u3T P x J ∧ orderOf a₁ = 5 ∧ orderOf a₂ = 5 ∧
      a₁ * a₂ ∈ U ∧ u3T P x J = Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ∧
      a₁ ∉ Subgroup.zpowers a₂ ∧
      Subgroup.zpowers a₁ = u3T P x J ⊓ a10Pre J ψ Λ₁ ∧
      Subgroup.zpowers a₂ = u3T P x J ⊓ a10Pre J ψ Λ₂ ∧
      (∀ A : Subgroup G, IsFiveCycleLine J (u3T P x J) ψ A →
        A = Subgroup.zpowers a₁ ∨ A = Subgroup.zpowers a₂) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hTcard, hTel, -⟩ := plane_T_structure hX.sylow hc
  have hTcard' : Nat.card ↥(u3T P x J) = 25 := by rw [hTcard]; norm_num
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hTP : u3T P x J ≤ (P : Subgroup G) :=
    (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  have hTcomm : ∀ a ∈ u3T P x J, ∀ b ∈ u3T P x J, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hTel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact a10t1_core ψ hTJ hTcard' hTcomm (a10t1_inj hTP ψ hker) hSyl hΛ hγ

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
