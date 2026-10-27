module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3HF
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6plane_inf_ne_bot {P : Sylow 3 G} {M : Subgroup G} {x : G} {J : Subgroup G}
    {U : Subgroup G} (hJ : IsA6Normal M x J) (_hxJ : x ∉ J) (hR : A6Prop34 3 P J x)
    (hV : A6InV 3 P J x U) : U ⊓ J ≠ ⊥ := by
  obtain ⟨-, hΩ, -⟩ := hR
  obtain ⟨hUQ, hUel, hUcard, hxU, -⟩ := hV
  obtain ⟨y, hyU, hyx⟩ : ∃ y ∈ U, y ∉ zpowers x := by
    by_contra hno
    push Not at hno
    have h1 := Subgroup.card_le_of_le (fun u hu => hno u hu : U ≤ zpowers x)
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hUel.2 x hxU))
    rw [hUcard, Nat.card_zpowers] at h1
    omega
  have hTx : ∀ t ∈ (P : Subgroup G) ⊓ J, ∀ c ∈ zpowers x, t * c = c * t := by
    intro t ht c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    have htx : Commute t x := mem_centralizer_singleton_iff.mp (hJ.le_centralizer ht.2)
    exact (htx.zpow_right k).eq
  obtain ⟨t, ht, c, hc, rfl⟩ := u3l42_decomp hTx (hΩ y (hUQ hyU) (hUel.2 y hyU))
  have htU : t ∈ U := by
    simpa using U.mul_mem hyU (U.inv_mem (zpowers_le.mpr hxU hc))
  intro hbot
  have htUJ : t ∈ U ⊓ J := ⟨htU, ht.2⟩
  rw [hbot, mem_bot] at htUJ
  exact hyx (by simpa [htUJ] using hc)

theorem a6plane_card_inf {P : Sylow 3 G} {M : Subgroup G} {x : G} {J : Subgroup G}
    {U : Subgroup G} (hJ : IsA6Normal M x J) (hxJ : x ∉ J) (hR : A6Prop34 3 P J x)
    (hV : A6InV 3 P J x U) : Nat.card ↥(U ⊓ J) = 3 := by
  have hne := a6plane_inf_ne_bot hJ hxJ hR hV
  obtain ⟨-, -, hUcard, hxU, -⟩ := hV
  have hdvd : Nat.card ↥(U ⊓ J) ∣ 3 ^ 2 := hUcard ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases i
  · rw [pow_zero] at hci
    exact absurd (Subgroup.card_eq_one.mp hci) hne
  · rwa [pow_one] at hci
  · have heq : U ⊓ J = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hci, hUcard])
    have hx : x ∈ U ⊓ J := by
      rw [heq]
      exact hxU
    exact absurd hx.2 hxJ

theorem a6plane_wc {P : Sylow 3 G} {M : Subgroup G} {x : G} (hgen : IsGenericPoint 3 P M x)
    {J : Subgroup G} {U : Subgroup G} (hJ : IsA6Normal M x J) (hxJ : x ∉ J)
    (hR : A6Prop34 3 P J x) (hV : A6InV 3 P J x U) : LineWeaklyClosed x U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := a6plane_card_inf hJ hxJ hR hV
  obtain ⟨-, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := hgen
  obtain ⟨-, -, hfus⟩ := hR
  obtain ⟨hUQ, -, -, -, hδ⟩ := hV
  intro g hg
  rcases hfus g (hg.trans hUQ) with h | h
  · exact h
  · refine absurd (Subgroup.eq_of_le_of_card_ge (le_inf hg h) ?_) (hδ g)
    rw [hcard, Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers,
      orderOf_eq_prime hx3 hx1]

theorem a6plane_comm_of_le {Q K H : Subgroup G} (hQ : IsSylowOf 3 Q K)
    (hQab : IsMulCommutative Q) (hH : IsPGroup 3 H) (hHK : H ≤ K) :
    ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR⟩ := (hH.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, -, hk⟩ := hQ.exists_mem_conj (P' := (R : Subgroup K).map K.subtype) ⟨R, rfl⟩
  have hmem : ∀ a ∈ H, k⁻¹ * a * k ∈ Q := fun a ha =>
    (hk a).mp ⟨⟨a, hHK ha⟩, hR (mem_subgroupOf.mpr ha), rfl⟩
  intro a ha b hb
  have hcomm := congrArg Subtype.val (hQab.is_comm.comm ⟨_, hmem a ha⟩ ⟨_, hmem b hb⟩)
  have h1 : k⁻¹ * (a * b) * k = k⁻¹ * (b * a) * k := by
    calc k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by group
      _ = (k⁻¹ * b * k) * (k⁻¹ * a * k) := hcomm
      _ = k⁻¹ * (b * a) * k := by group
  exact mul_left_cancel (mul_right_cancel h1)

omit [Finite G] in
theorem a6plane_mem_centralizer {x f : G} {U : Subgroup G} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxU : x ∈ U) (hwc : LineWeaklyClosed x U) {m : ℕ} (hfm : f ^ 3 ^ m = 1)
    (hfU : f ∈ normalizer (U : Set G)) : f ∈ centralizer ({x} : Set G) := by
  have hle : (zpowers x).map (MulAut.conj f).toMonoidHom ≤ U := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact (mem_normalizer_iff.mp hfU x).mp hxU
  have hmem : f * x * f⁻¹ ∈ zpowers x := by
    rw [← hwc f hle, MonoidHom.map_zpowers]
    exact mem_zpowers _
  exact mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (p34_conj_eq_of_pow hx1 hx3 hfm hmem))

theorem a6plane_hF {P : Sylow 3 G} {M : Subgroup G} {x : G} (hgen : IsGenericPoint 3 P M x)
    {J : Subgroup G} {U : Subgroup G} (hJ : IsA6Normal M x J) (hxJ : x ∉ J)
    (hR : A6Prop34 3 P J x) (hV : A6InV 3 P J x U) :
    ∀ F : Subgroup G, IsPGroup 3 F → U ≤ F → F ≤ M → CFSG.Open.pRank 3 F ≤ 2 →
      IsMulCommutative F ∧ ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro F hFp hUF _ hFrk
  have hwc := a6plane_wc hgen hJ hxJ hR hV
  obtain ⟨-, ⟨-, hx1, hx3, -, -⟩, hsyl, -⟩ := hgen
  obtain ⟨hQab, -, -⟩ := hR
  obtain ⟨-, hUel, hUcard, hxU, -⟩ := hV
  set F₁ : Subgroup G := F ⊓ normalizer (U : Set G) with hF₁
  have hUF₁ : U ≤ F₁ := le_inf hUF le_normalizer
  have hF₁C : F₁ ≤ centralizer ({x} : Set G) := fun f hf => by
    obtain ⟨m, hm⟩ := hFp ⟨f, hf.1⟩
    exact a6plane_mem_centralizer hx1 hx3 hxU hwc (congrArg Subtype.val hm) hf.2
  have hF₁ab := a6plane_comm_of_le hsyl hQab (hFp.to_le inf_le_left) hF₁C
  have hΩ₁ : ∀ f ∈ F₁, f ^ 3 = 1 → f ∈ U := fun f hf hf3 => by
    by_contra hfU
    exact u3hf_inf_card_le hf3 hf.1 hfU (fun t ht => hF₁ab t (hUF₁ ht) f hf) hUel.2 hFrk U
      (le_inf hUF le_rfl) hUcard
  have hFN : F ≤ normalizer (U : Set G) := by
    by_contra hnot
    have : Group.IsNilpotent ↥F := hFp.isNilpotent
    have hlt : F₁.subgroupOf F < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hnot fun f hf => ?_
      have hf' : (⟨f, hf⟩ : ↥F) ∈ F₁.subgroupOf F := by
        rw [htop]
        exact mem_top _
      exact (mem_subgroupOf.mp hf').2
    obtain ⟨n, hnN, hnF₁⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have key : ∀ c ∈ normalizer ((F₁.subgroupOf F : Subgroup ↥F) : Set ↥F), ∀ u ∈ U,
        (c : G) * u * (c : G)⁻¹ ∈ U := by
      intro c hc u hu
      have h1 := (mem_normalizer_iff.mp hc ⟨u, hUF hu⟩).mp (mem_subgroupOf.mpr (hUF₁ hu))
      have h2 : (c : G) * u * (c : G)⁻¹ ∈ F₁ := mem_subgroupOf.mp h1
      refine hΩ₁ _ h2 ?_
      rw [conj_pow, hUel.2 u hu, mul_one, mul_inv_cancel]
    refine hnF₁ (mem_subgroupOf.mpr ⟨n.2, mem_normalizer_iff.mpr fun u =>
      ⟨key n hnN u, fun h => ?_⟩⟩)
    simpa [mul_assoc] using key n⁻¹ (inv_mem hnN) _ h
  refine ⟨⟨⟨fun a b => Subtype.ext (hF₁ab a ⟨a.2, hFN a.2⟩ b ⟨b.2, hFN b.2⟩)⟩⟩,
    fun g hg => hwc g fun y hy => hΩ₁ y ⟨hg hy, hFN (hg hy)⟩ ?_⟩
  obtain ⟨z, hz, rfl⟩ := hy
  rw [← map_pow, orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hz).trans
    (orderOf_dvd_of_pow_eq_one hx3)), map_one]

end CFSG.LocalAnalysis.RankThreeTheoremC
