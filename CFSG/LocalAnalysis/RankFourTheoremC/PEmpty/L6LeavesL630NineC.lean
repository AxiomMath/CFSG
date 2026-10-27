module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup

variable {G : Type} [Group G]

@[expose] def sectionSub (N X1 : Subgroup G) {Q : Type} [Group Q] (Φ : N →* Q)
    (S : Subgroup Q) : Subgroup G :=
  ((S.comap Φ) ⊓ X1.subgroupOf N).map N.subtype

theorem mem_sectionSub_iff {N X1 : Subgroup G} {Q : Type} [Group Q] {Φ : N →* Q}
    {S : Subgroup Q} {g : G} :
    g ∈ sectionSub N X1 Φ S ↔ ∃ hgN : g ∈ N, g ∈ X1 ∧ Φ ⟨g, hgN⟩ ∈ S := by
  constructor
  · intro hg
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hg
    have htS : Φ t ∈ S := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp ht).1
    have htX : (t : G) ∈ X1 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp ht).2
    have hgN : g ∈ N := by rw [← hts]; exact t.2
    refine ⟨hgN, by rw [← hts]; exact htX, ?_⟩
    have heq : (⟨g, hgN⟩ : N) = t := Subtype.ext hts.symm
    rw [heq]
    exact htS
  · rintro ⟨hgN, hgX, hgS⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hgN⟩,
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr hgS, Subgroup.mem_subgroupOf.mpr hgX⟩, rfl⟩

theorem conj_mem_sectionSub {N X1 : Subgroup G} (hX1N : X1 ≤ N)
    (hX1 : ∀ g ∈ X1, ∀ h ∈ X1, g * h * g⁻¹ ∈ X1) {Q : Type} [Group Q] {Φ : N →* Q}
    {S : Subgroup Q} [S.Normal] {g h : G} (hg : g ∈ X1) (hh : h ∈ sectionSub N X1 Φ S) :
    g * h * g⁻¹ ∈ sectionSub N X1 Φ S := by
  obtain ⟨hhN, hhX, hhS⟩ := mem_sectionSub_iff.mp hh
  have hgN : g ∈ N := hX1N hg
  rw [mem_sectionSub_iff]
  refine ⟨N.mul_mem (N.mul_mem hgN hhN) (N.inv_mem hgN), hX1 g hg h hhX, ?_⟩
  have heq : Φ ⟨g * h * g⁻¹, N.mul_mem (N.mul_mem hgN hhN) (N.inv_mem hgN)⟩ =
      Φ ⟨g, hgN⟩ * Φ ⟨h, hhN⟩ * (Φ ⟨g, hgN⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [heq]
  exact (inferInstance : S.Normal).conj_mem _ hhS _

theorem comm_inv_of_comm' {a x : G} (h : a * x = x * a) : a⁻¹ * x = x * a⁻¹ := by
  calc a⁻¹ * x = a⁻¹ * (x * a) * a⁻¹ := by group
    _ = a⁻¹ * (a * x) * a⁻¹ := by rw [h]
    _ = x * a⁻¹ := by group

theorem false_of_mem_fivePart {Q : Type} [Group Q] [Finite Q] {M : Subgroup G} [Finite G] {x z : G}
    (N : Subgroup G) (hX1N : M ⊓ centralizer ({x} : Set G) ≤ N) (Φ : N →* Q)
    (hΦ : Function.Surjective Φ) (S : Subgroup Q) [S.Normal] [IsSimpleGroup S]
    (hnab : ¬ ∀ a b : S, a * b = b * a) (h2 : 2 ∣ Nat.card S) (h5 : 5 ∣ Nat.card S)
    (hidx : S.index ∣ 2)
    (hSX : S ≤ ((M ⊓ centralizer ({x} : Set G)).subgroupOf N).map Φ)
    (hzX : z ∈ M ⊓ centralizer ({x} : Set G)) (hzΦ : Φ ⟨z, hX1N hzX⟩ ≠ 1) (hz5 : z ^ 5 = 1)
    (R T : Subgroup G) (hRn : ∀ m ∈ M, ∀ r ∈ R, m * r * m⁻¹ ∈ R)
    (hTn : ∀ m ∈ M, ∀ t ∈ T, m * t * m⁻¹ ∈ T) (hTM : T ≤ M)
    (hTcard : Nat.Coprime 5 (Nat.card T))
    (hRT : ∀ r ∈ R, ∃ n : ℕ, r ^ (5 ^ n) ∈ T) (hzR : z ∈ R) : False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set X1 : Subgroup G := M ⊓ centralizer ({x} : Set G) with hX1def
  have hX1cl : ∀ g ∈ X1, ∀ h ∈ X1, g * h * g⁻¹ ∈ X1 := by
    intro g hg h hh
    refine ⟨M.mul_mem (M.mul_mem hg.1 hh.1) (M.inv_mem hg.1), ?_⟩
    have hg' : g * x = x * g := mem_centralizer_singleton_iff.mp hg.2
    have hh' : h * x = x * h := mem_centralizer_singleton_iff.mp hh.2
    have hgi := comm_inv_of_comm' hg'
    refine mem_centralizer_singleton_iff.mpr ?_
    calc g * h * g⁻¹ * x = g * h * (g⁻¹ * x) := by group
      _ = g * h * (x * g⁻¹) := by rw [hgi]
      _ = g * (h * x) * g⁻¹ := by group
      _ = g * (x * h) * g⁻¹ := by rw [hh']
      _ = (g * x) * h * g⁻¹ := by group
      _ = (x * g) * h * g⁻¹ := by rw [hg']
      _ = x * (g * h * g⁻¹) := by group
  set H : Subgroup G := sectionSub N X1 Φ S with hHdef
  have hHmem : ∀ h ∈ H, ∃ hhN : h ∈ N, h ∈ X1 ∧ Φ ⟨h, hhN⟩ ∈ S := fun h hh =>
    mem_sectionSub_iff.mp hh
  have hHconj : ∀ g ∈ X1, ∀ h ∈ H, g * h * g⁻¹ ∈ H := fun g hg h hh =>
    conj_mem_sectionSub hX1N hX1cl hg hh
  have hHsurj : ∀ s ∈ S, ∃ h ∈ H, ∃ hhN : h ∈ N, Φ ⟨h, hhN⟩ = s := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp (hSX hs)
    have htX : (t : G) ∈ X1 := Subgroup.mem_subgroupOf.mp ht
    have htH : (t : G) ∈ H := by
      rw [hHdef, mem_sectionSub_iff]
      refine ⟨t.2, htX, ?_⟩
      show Φ t ∈ S
      rw [hts]
      exact hs
    exact ⟨t, htH, t.2, hts⟩
  set W : Subgroup G := R ⊓ H with hWdef
  have hWN : ∀ w ∈ W, w ∈ N := fun w hw => by
    obtain ⟨hwN, -, -⟩ := hHmem w (Subgroup.mem_inf.mp hw).2
    exact hwN
  have hWconj : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W := by
    intro h hh w hw
    obtain ⟨-, hhX, -⟩ := hHmem h hh
    obtain ⟨hwR, hwH⟩ := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_inf.mpr ⟨hRn h hhX.1 w hwR, hHconj h hhX w hwH⟩
  set U : Subgroup Q := (W.subgroupOf N).map Φ with hUdef
  set Y : Subgroup Q := ((T ⊓ W).subgroupOf N).map Φ with hYdef
  have hUS : U ≤ S := by
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hu
    have hnH : (n : G) ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)).2
    obtain ⟨hnN, -, hnS⟩ := hHmem (n : G) hnH
    exact hnS
  have hYU : Y ≤ U := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)).2, rfl⟩
  have hYS : Y ≤ S := hYU.trans hUS
  have hUnorm : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
    intro s hs u hu
    obtain ⟨h, hhH, hhN, hΦh⟩ := hHsurj s hs
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hu
    have hnW := Subgroup.mem_subgroupOf.mp hn
    rw [← hΦh]
    refine Subgroup.mem_map.mpr ⟨(⟨h, hhN⟩ : N) * n * (⟨h, hhN⟩ : N)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have := hWconj h hhH _ hnW
      simpa using this
    · simp only [map_mul, map_inv]
  have hYnorm : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := by
    intro s hs y hy
    obtain ⟨h, hhH, hhN, hΦh⟩ := hHsurj s hs
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    have hnTW := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨hnT, hnW⟩ := Subgroup.mem_inf.mp hnTW
    obtain ⟨-, hhX, -⟩ := hHmem h hhH
    rw [← hΦh]
    refine Subgroup.mem_map.mpr ⟨(⟨h, hhN⟩ : N) * n * (⟨h, hhN⟩ : N)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · simpa using hTn h hhX.1 _ hnT
      · simpa using hWconj h hhH _ hnW
    · simp only [map_mul, map_inv]
  have hU'n : (U.subgroupOf S).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hUnorm g.1 g.2 _ hn
    simpa using this⟩
  have hY'n : (Y.subgroupOf S).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hYnorm g.1 g.2 _ hn
    simpa using this⟩
  have hEord : ∀ n : N, n.1 ∈ T ⊓ W → orderOf (Φ n) ∣ Nat.card T := by
    intro n hn
    have h1 : orderOf (Φ n) ∣ orderOf n := orderOf_map_dvd Φ n
    have h2 : orderOf n = orderOf (n : G) := (Subgroup.orderOf_coe n).symm
    have h3 : orderOf (n : G) ∣ Nat.card T := by
      have hT' := orderOf_dvd_natCard (⟨n.1, (Subgroup.mem_inf.mp hn).1⟩ : T)
      rwa [Subgroup.orderOf_mk] at hT'
    rw [h2] at h1
    exact h1.trans h3
  have hYtriv : ∀ n : N, n.1 ∈ T ⊓ W → Φ n = 1 := by
    intro n hn
    by_contra hne
    have hYmem : Φ n ∈ Y := Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top (Y.subgroupOf S) with hbot | htop
    · have hmem : (⟨Φ n, hYS hYmem⟩ : S) ∈ Y.subgroupOf S := Subgroup.mem_subgroupOf.mpr hYmem
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hne (congrArg Subtype.val hmem)
    · obtain ⟨t, ht5⟩ := exists_prime_orderOf_dvd_card' 5 h5
      have htY' : t ∈ Y.subgroupOf S := by
        rw [htop]
        exact Subgroup.mem_top t
      obtain ⟨m, hm, hΦm⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp htY')
      have hd := hEord m (Subgroup.mem_subgroupOf.mp hm)
      rw [hΦm, Subgroup.orderOf_coe, ht5] at hd
      have := Nat.Coprime.eq_one_of_dvd hTcard hd
      norm_num at this
  have hUtriv : ∀ n : N, n.1 ∈ W → Φ n = 1 := by
    intro n hn
    by_contra hne
    have hUmem : Φ n ∈ U := Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top (U.subgroupOf S) with hbot | htop
    · have hmem : (⟨Φ n, hUS hUmem⟩ : S) ∈ U.subgroupOf S := Subgroup.mem_subgroupOf.mpr hUmem
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hne (congrArg Subtype.val hmem)
    · obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have htU' : t ∈ U.subgroupOf S := by
        rw [htop]
        exact Subgroup.mem_top t
      obtain ⟨m, hm, hΦm⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp htU')
      have hmW : (m : G) ∈ W := Subgroup.mem_subgroupOf.mp hm
      obtain ⟨k, hk⟩ := hRT (m : G) (Subgroup.mem_inf.mp hmW).1
      have hkW : ((m ^ (5 ^ k) : N) : G) ∈ T ⊓ W := by
        rw [Subgroup.coe_pow]
        exact Subgroup.mem_inf.mpr ⟨hk, W.pow_mem hmW _⟩
      have hmk : Φ (m ^ (5 ^ k)) = 1 := hYtriv _ hkW
      have ht1 : (t : Q) ^ (5 ^ k) = 1 := by
        rw [← hΦm, ← map_pow, hmk]
      have ht1' : t ^ (5 ^ k) = 1 := by
        apply Subtype.ext
        simpa using ht1
      have hdvd : orderOf t ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one ht1'
      rw [ht2] at hdvd
      have h25 : 2 ∣ 5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
      norm_num at h25
  have hzN : z ∈ N := hX1N hzX
  set zq : Q := Φ ⟨z, hzN⟩ with hzqdef
  have hzq5 : zq ^ 5 = 1 := by
    have h1 : (⟨z, hzN⟩ : N) ^ 5 = 1 := Subtype.ext (by simpa using hz5)
    rw [hzqdef, ← map_pow, h1, map_one]
  have hcomm : ∀ s ∈ S, zq * s = s * zq := by
    intro s hs
    obtain ⟨h, hhH, hhN, hΦh⟩ := hHsurj s hs
    obtain ⟨-, hhX, -⟩ := hHmem h hhH
    have hzh : z * h * z⁻¹ * h⁻¹ ∈ W := by
      have h1 : z * h * z⁻¹ ∈ H := hHconj z hzX h hhH
      have h2 : z * h * z⁻¹ * h⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem hhH)
      have h3 : z * h * z⁻¹ * h⁻¹ ∈ R := by
        have h4 : z * (h * z⁻¹ * h⁻¹) ∈ R :=
          R.mul_mem hzR (hRn h hhX.1 z⁻¹ (R.inv_mem hzR))
        simpa [mul_assoc] using h4
      exact Subgroup.mem_inf.mpr ⟨h3, h2⟩
    have key := hUtriv ((⟨z, hzN⟩ : N) * ⟨h, hhN⟩ * (⟨z, hzN⟩ : N)⁻¹ * (⟨h, hhN⟩ : N)⁻¹)
      (by simpa using hzh)
    simp only [map_mul, map_inv] at key
    rw [← hΦh]
    calc zq * Φ ⟨h, hhN⟩ = (zq * Φ ⟨h, hhN⟩ * zq⁻¹ * (Φ ⟨h, hhN⟩)⁻¹) * (Φ ⟨h, hhN⟩ * zq) := by
          group
      _ = Φ ⟨h, hhN⟩ * zq := by rw [key, one_mul]
  by_cases hzqS : zq ∈ S
  · have hc1 : (⟨zq, hzqS⟩ : S) ≠ 1 := fun h => hzΦ (congrArg Subtype.val h)
    have hcen : ∀ g : S, g * ⟨zq, hzqS⟩ = ⟨zq, hzqS⟩ * g := by
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (hcomm g.1 g.2).symm
    have hcZ : (⟨zq, hzqS⟩ : S) ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr hcen
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hcZ
      exact hc1 hcZ
    · apply hnab
      intro a b
      have ha : a ∈ Subgroup.center S := by
        rw [ht]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hmk1 : QuotientGroup.mk' S zq ≠ 1 := by
      rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact hzqS
    have hmk5 : (QuotientGroup.mk' S zq) ^ 5 = 1 := by
      rw [← map_pow, hzq5, map_one]
    have hord : orderOf (QuotientGroup.mk' S zq) = 5 := orderOf_eq_prime hmk5 hmk1
    have hdvd : 5 ∣ S.index := by
      have := orderOf_dvd_natCard (QuotientGroup.mk' S zq)
      rw [hord] at this
      exact this
    have h52 : 5 ∣ 2 := hdvd.trans hidx
    norm_num at h52

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
