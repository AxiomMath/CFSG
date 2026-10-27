module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Star
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217CentE

import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CommLift
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
  CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M Q H F : Subgroup G} {q p : ℕ} {E : Subgroup G}

private theorem mk_mem_centralizer_kStar_of_mem_centralizer_kSub
    {x : G} (hxH : x ∈ H)
    (hx : x ∈ Subgroup.centralizer (AGL81C.kSub q M H : Set G)) :
    QuotientGroup.mk' (primeComplementCore (G := ↥H) q) ⟨x, hxH⟩ ∈
      Subgroup.centralizer (AGL81C.kStar q M H : Set (AGL81C.StarGroup q H)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro y hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (k : G)
    (Subgroup.mem_subgroupOf.mp hk))

private theorem exists_mul_mem_inf_centralizer (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) {p : ℕ} (hp : p.Prime)
    (hcop : ¬ p ∣ Nat.card ↥(AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H))
    {k : G} (hk : k ∈ AGL81C.kSub q M H)
    {D : Subgroup G} (hDH : D ≤ H) (hD : IsPGroup p D)
    (hcent : ∀ (d : G) (hd : d ∈ D),
      QuotientGroup.mk' (primeComplementCore (G := ↥H) q) ⟨d, hDH hd⟩ *
        QuotientGroup.mk' (primeComplementCore (G := ↥H) q)
          ⟨k, AGL81C.kSub_le q M H hk⟩ =
      QuotientGroup.mk' (primeComplementCore (G := ↥H) q)
          ⟨k, AGL81C.kSub_le q M H hk⟩ *
        QuotientGroup.mk' (primeComplementCore (G := ↥H) q) ⟨d, hDH hd⟩) :
    ∃ n ∈ AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H,
      ∀ d ∈ D, d * (k * n) * d⁻¹ = k * n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) q
  let K : Subgroup G := AGL81C.kSub q M H
  let R : Subgroup G := CFSG.Open.relPPrimeCore q H
  let N : Subgroup G := K ⊓ R
  have hkH : k ∈ H := AGL81C.kSub_le q M H hk
  have hKnorm : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (AGL81C.kSub_le q M H)).mp
      (s.kStructure h1).1
  have hRnorm : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
        (p := q) H)).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        s.qPrime H)
  have hNnorm : H ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKnorm hx, hRnorm hx⟩
  have hmN : ∀ (d : G) (hd : d ∈ D), k⁻¹ * (d * k * d⁻¹) ∈ N := by
    intro d hd
    have hdH : d ∈ H := hDH hd
    have hmH : k⁻¹ * (d * k * d⁻¹) ∈ H :=
      H.mul_mem (H.inv_mem hkH) (H.mul_mem (H.mul_mem hdH hkH) (H.inv_mem hdH))
    have hmK : k⁻¹ * (d * k * d⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem hk) ((Subgroup.mem_normalizer_iff.mp (hKnorm hdH) k).mp hk)
    have hcomm : QuotientGroup.mk' O ⟨d, hdH⟩ * QuotientGroup.mk' O ⟨k, hkH⟩ =
        QuotientGroup.mk' O ⟨k, hkH⟩ * QuotientGroup.mk' O ⟨d, hdH⟩ := hcent d hd
    have hconj : QuotientGroup.mk' O ⟨d * k * d⁻¹,
        H.mul_mem (H.mul_mem hdH hkH) (H.inv_mem hdH)⟩ = QuotientGroup.mk' O ⟨k, hkH⟩ := by
      rw [show (⟨d * k * d⁻¹, H.mul_mem (H.mul_mem hdH hkH) (H.inv_mem hdH)⟩ : ↥H) =
          ⟨d, hdH⟩ * ⟨k, hkH⟩ * ⟨d, hdH⟩⁻¹ from Subtype.ext rfl]
      rw [map_mul, map_mul, map_inv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hm1 : QuotientGroup.mk' O ⟨k⁻¹ * (d * k * d⁻¹), hmH⟩ = 1 := by
      rw [show (⟨k⁻¹ * (d * k * d⁻¹), hmH⟩ : ↥H) =
          ⟨k, hkH⟩⁻¹ * ⟨d * k * d⁻¹,
            H.mul_mem (H.mul_mem hdH hkH) (H.inv_mem hdH)⟩ from Subtype.ext rfl]
      rw [map_mul, map_inv, hconj, inv_mul_cancel]
    exact Subgroup.mem_inf.mpr ⟨hmK,
      (CFSG.AGLEmbedding.mk'_primeComplementCore_eq_one_iff q ⟨_, hmH⟩).mp hm1⟩
  have hclosure : ∀ (d : G) (hd : d ∈ D) (g : G), k⁻¹ * g ∈ N → k⁻¹ * (d * g * d⁻¹) ∈ N := by
    intro d hd g hg
    have hgd : g = k * (k⁻¹ * g) := by group
    have hNconj : d * (k⁻¹ * g) * d⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hNnorm (hDH hd)) (k⁻¹ * g)).mp hg
    have heq : k⁻¹ * (d * g * d⁻¹) =
        (k⁻¹ * (d * k * d⁻¹)) * (d * (k⁻¹ * g) * d⁻¹) := by
      rw [hgd]
      group
    rw [heq]
    exact N.mul_mem (hmN d hd) hNconj
  obtain ⟨n, hnN, hfix⟩ := CFSG.Quasithin.Stellmacher.L3YC.exists_fixed_mem_coset
    (p := p) (D := D) (N := N) hD hcop k hclosure
  exact ⟨n, hnN, hfix⟩

theorem Hyp1417.exists_not_mem_centralizer_star (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo)
    {A : Subgroup G} (hAE : A ≤ E) (hA : Nat.card A = p)
    (hH : ¬ Subgroup.normalizer (A : Set G) ≤ M)
    (hcop : ¬ p ∣ Nat.card ↥(AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ⊓
      CFSG.Open.relPPrimeCore q (Subgroup.normalizer (A : Set G)))) :
    ∃ b : ↥(Subgroup.normalizer (A : Set G)), (b : G) ∈ E ∧ (b : G) ∉ A ∧
      orderOf (b : G) = p ∧
      QuotientGroup.mk' (primeComplementCore (G := ↥(Subgroup.normalizer (A : Set G))) q) b ∉
        Subgroup.centralizer (AGL81C.kStar q M (Subgroup.normalizer (A : Set G)) :
          Set (↥(Subgroup.normalizer (A : Set G)) ⧸
            primeComplementCore (G := ↥(Subgroup.normalizer (A : Set G))) q)) := by
  classical
  let HA : Subgroup G := Subgroup.normalizer (A : Set G)
  change ∃ b : ↥HA, (b : G) ∈ E ∧ (b : G) ∉ A ∧ orderOf (b : G) = p ∧
    QuotientGroup.mk' (primeComplementCore (G := ↥HA) q) b ∉
      Subgroup.centralizer (AGL81C.kStar q M HA :
        Set (↥HA ⧸ primeComplementCore (G := ↥HA) q))
  obtain ⟨Q, F, s⟩ := h.exists_setting hAE hA hH
  haveI : Fact p.Prime := ⟨h.hp⟩
  haveI : IsCyclic A := isCyclic_of_prime_card hA
  haveI : IsMulCommutative ↥E := h.elem.1
  have hEcentA : E ≤ Subgroup.centralizer (A : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    simpa using mul_comm' (⟨a, hAE ha⟩ : E) ⟨e, he⟩
  have hEHA : E ≤ HA :=
    hEcentA.trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have hKAc : A ≤ Subgroup.centralizer (AGL81C.kSub q M HA : Set G) :=
    s.le_centralizer_kSub h1 le_rfl
  by_contra hcon
  have hcent : ∀ b : ↥HA, (b : G) ∈ E → (b : G) ∉ A → orderOf (b : G) = p →
      QuotientGroup.mk' (primeComplementCore (G := ↥HA) q) b ∈
        Subgroup.centralizer (AGL81C.kStar q M HA : Set (AGL81C.StarGroup q HA)) := by
    intro b hbE hbA hbo
    by_contra hbC
    exact hcon ⟨b, hbE, hbA, hbo, hbC⟩
  have hcentral : ∀ (d : G) (hd : d ∈ E), QuotientGroup.mk' (primeComplementCore (G := ↥HA) q)
      ⟨d, hEHA hd⟩ ∈
        Subgroup.centralizer (AGL81C.kStar q M HA : Set (AGL81C.StarGroup q HA)) := by
    intro d hd
    by_cases hdA : d ∈ A
    · exact mk_mem_centralizer_kStar_of_mem_centralizer_kSub (hxH := hEHA hd)
        (hx := hKAc hdA)
    · have hdpG : orderOf d = p :=
        orderOf_eq_prime (by simpa using h.elem.2 d hd) (by
          intro h1
          exact hdA (h1 ▸ A.one_mem))
      have hdp : orderOf ((⟨d, hEHA hd⟩ : ↥HA) : G) = p := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_mk]
        exact hdpG
      exact hcent ⟨d, hEHA hd⟩ hd hdA hdp
  have hKAM : AGL81C.kSub q M HA ≤ M := by
    intro k hk
    obtain ⟨n, hnN, hfix⟩ := exists_mul_mem_inf_centralizer (s := s) (h1 := h1)
      (hp := h.hp) (hcop := hcop) (hk := hk) (hDH := hEHA) (hD := h.elem.isPGroup)
      (hcent := by
        intro d hd
        have hmemK : QuotientGroup.mk' (primeComplementCore (G := ↥HA) q)
            ⟨k, AGL81C.kSub_le q M HA hk⟩ ∈ AGL81C.kStar q M HA :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
        exact (Subgroup.mem_centralizer_iff.mp (hcentral d hd) _ hmemK).symm)
    have hknKA : k * n ∈ AGL81C.kSub q M HA :=
      (AGL81C.kSub q M HA).mul_mem hk hnN.1
    have hkncent : k * n ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hfixe := hfix e he
      calc e * (k * n) = (e * (k * n) * e⁻¹) * e := by group
        _ = (k * n) * e := by rw [hfixe]
    have hknM : k * n ∈ M := h.centralizer_le h1 hNT hL34 hkncent
    have hnM : n ∈ M := s.nine.relPPrimeCore_le hnN.2
    have hk_eq : k = (k * n) * n⁻¹ := by group
    rw [hk_eq]
    exact M.mul_mem hknM (M.inv_mem hnM)
  exact s.kSub_not_le h1 hKAM

private theorem dvd_card_star_inf_centralizer (h : Hyp1417 G M q p E)
    (s : Setting1417 G M Q H F q) {A : Subgroup G} (hAE : A ≤ E)
    (hHNA : Subgroup.normalizer (A : Set G) ≤ H) {b : ↥H} (hbE : (b : G) ∈ E) :
    q ∣ Nat.card ↥(AGL81C.starImg q H (H ⊓ M) ⊓
      Subgroup.centralizer
        (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := ↥H) q) b) :
          Set (AGL81C.StarGroup q H))) := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) q
  let X := AGL81C.StarGroup q H
  let X₁ : Subgroup X := AGL81C.starImg q H (H ⊓ M)
  let D : Subgroup X := Subgroup.zpowers (QuotientGroup.mk' O b)
  obtain ⟨y, hyMCE, hyo⟩ := h.exists_orderOf_eq
  have hyM : y ∈ M := hyMCE.1
  have hyCE : y ∈ Subgroup.centralizer (E : Set G) := hyMCE.2
  have hyH : y ∈ H := hHNA ((Subgroup.centralizer_le_normalizer (A : Set G))
    ((Subgroup.centralizer_le hAE) hyCE))
  let z : X := QuotientGroup.mk' O ⟨y, hyH⟩
  have hyq : y ^ q = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  have hzq : z ^ q = 1 := by
    rw [show z = QuotientGroup.mk' O ⟨y, hyH⟩ from rfl, ← map_pow,
      show (⟨y, hyH⟩ : ↥H) ^ q = 1 from Subtype.ext (by simpa using hyq), map_one]
  have hz1 : z ≠ 1 := by
    intro hz
    have hyO : (⟨y, hyH⟩ : ↥H) ∈ O := by
      have h' : QuotientGroup.mk' O (⟨y, hyH⟩ : ↥H) = 1 := hz
      rw [QuotientGroup.mk'_apply] at h'
      exact (QuotientGroup.eq_one_iff (N := O) _).mp h'
    have hq_dvd : q ∣ Nat.card O := by
      have h1' : orderOf (⟨y, hyH⟩ : ↥H) = q := by
        rw [Subgroup.orderOf_mk, hyo]
      rw [← h1']
      exact Subgroup.orderOf_dvd_natCard O hyO
    exact (Nat.Prime.coprime_iff_not_dvd s.qPrime).mp
      (primeComplementCore_coprime (G := ↥H) q) hq_dvd
  have hzd : orderOf z = q := orderOf_eq_prime hzq hz1
  have hzX₁ : z ∈ X₁ := by
    have hmem : (⟨y, hyH⟩ : ↥H) ∈ (H ⊓ M).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hyH, hyM⟩
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hmem
  have hcommby : QuotientGroup.mk' O b * z = z * QuotientGroup.mk' O b := by
    rw [show z = QuotientGroup.mk' O ⟨y, hyH⟩ from rfl, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyCE (b : G) hbE)
  have hzCD : z ∈ Subgroup.centralizer (D : Set X) := by
    rw [show D = Subgroup.zpowers (QuotientGroup.mk' O b) from rfl,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact hcommby.symm
  have hzmem : z ∈ X₁ ⊓ Subgroup.centralizer (D : Set X) :=
    Subgroup.mem_inf.mpr ⟨hzX₁, hzCD⟩
  have h1' : orderOf z ∣ Nat.card ↥(X₁ ⊓ Subgroup.centralizer (D : Set X)) :=
    Subgroup.orderOf_dvd_natCard _ hzmem
  rwa [hzd] at h1'

private theorem exists_kStar_mem_centralizer_not_le (h : Hyp1417 G M q p E)
    (s : Setting1417 G M Q H F q) (h1 : NineFourTwoSigmaGen) (hK1 : KFactThreeEightFive)
    {b : ↥H} (hbE : (b : G) ∈ E)
    (hbC : QuotientGroup.mk' (primeComplementCore (G := ↥H) q) b ∉
      Subgroup.centralizer (AGL81C.kStar q M H : Set (AGL81C.StarGroup q H)))
    (hqD : q ∣ Nat.card ↥(AGL81C.starImg q H (H ⊓ M) ⊓
      Subgroup.centralizer
        (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := ↥H) q) b) :
          Set (AGL81C.StarGroup q H)))) :
    ∃ (k : ↥H) (x : AGL81C.StarGroup q H),
      (k : G) ∈ AGL81C.kSub q M H ∧
        QuotientGroup.mk' (primeComplementCore (G := ↥H) q) k = x ∧
        x ∈ Subgroup.centralizer
          (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := ↥H) q) b) :
            Set (AGL81C.StarGroup q H)) ∧
        x ∉ AGL81C.starImg q H (H ⊓ M) := by
  classical
  haveI : Fact p.Prime := ⟨h.hp⟩
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) q
  let X := AGL81C.StarGroup q H
  let K : Subgroup X := AGL81C.kStar q M H
  let X₁ : Subgroup X := AGL81C.starImg q H (H ⊓ M)
  let D : Subgroup X := Subgroup.zpowers (QuotientGroup.mk' O b)
  have hbpow : b ^ p = 1 := by
    apply Subtype.ext
    simpa using h.elem.2 (b : G) hbE
  have hord : orderOf (QuotientGroup.mk' O b) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hbpow, map_one]
    · intro h1'
      exact hbC (h1' ▸ Subgroup.one_mem _)
  have hDcard : Nat.card D = p := by
    rw [show D = Subgroup.zpowers (QuotientGroup.mk' O b) from rfl, Nat.card_zpowers, hord]
  have hK1app := hK1 q s.qPrime s.q_ne_two X K (s.kStar_normal h1)
    (s.kStructure h1).2.2.2 (s.two_le_pRank_top_star (F := F)) X₁
    (s.isStronglyPEmbedded_starImg (F := F)) D ⟨p, h.hp, h.hp2, h.hpq, hDcard⟩ hqD
  obtain ⟨x, hx, hxX₁⟩ := SetLike.not_le_iff_exists.mp hK1app
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxK, hxD⟩ := hx
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hxK
  exact ⟨k, x, Subgroup.mem_subgroupOf.mp hk, hkx, hxD, hxX₁⟩

private theorem false_of_star_lift (h : Hyp1417 G M q p E)
    (s : Setting1417 G M Q H F q) (h1 : NineFourTwoSigmaGen) (hK1 : KFactThreeEightFive)
    (hcop : ¬ p ∣ Nat.card ↥(AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H))
    {b : ↥H} (hbE : (b : G) ∈ E) (hbo : orderOf (b : G) = p)
    (hbC : QuotientGroup.mk' (primeComplementCore (G := ↥H) q) b ∉
      Subgroup.centralizer (AGL81C.kStar q M H : Set (AGL81C.StarGroup q H)))
    (hKAM : AGL81C.kSub q M H ⊓ Subgroup.centralizer (({(b : G)} : Set G)) ≤ M)
    (hqD : q ∣ Nat.card ↥(AGL81C.starImg q H (H ⊓ M) ⊓
      Subgroup.centralizer
        (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := ↥H) q) b) :
          Set (AGL81C.StarGroup q H)))) : False := by
  classical
  haveI : Fact p.Prime := ⟨h.hp⟩
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  obtain ⟨k, x, hkA, hkx, hxD, hxX₁⟩ :=
    exists_kStar_mem_centralizer_not_le (h := h) (s := s) h1 hK1 hbE hbC hqD
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) q
  let X := AGL81C.StarGroup q H
  let X₁ : Subgroup X := AGL81C.starImg q H (H ⊓ M)
  let D : Subgroup X := Subgroup.zpowers (QuotientGroup.mk' O b)
  have hDH : Subgroup.zpowers (b : G) ≤ H := Subgroup.zpowers_le.mpr b.2
  have hDp : IsPGroup p (Subgroup.zpowers (b : G)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hbo, pow_one]
  have hkx' : QuotientGroup.mk' O ⟨(k : G), AGL81C.kSub_le q M H hkA⟩ = x := by
    rw [show (⟨(k : G), AGL81C.kSub_le q M H hkA⟩ : ↥H) = k from Subtype.ext rfl]
    exact hkx
  have hmemD : ∀ (d : G) (hd : d ∈ Subgroup.zpowers (b : G)),
      QuotientGroup.mk' O ⟨d, hDH hd⟩ ∈ D := by
    intro d hd
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hd
    rw [show D = Subgroup.zpowers (QuotientGroup.mk' O b) from rfl]
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← map_zpow, show b ^ n = ⟨d, hDH hd⟩ from Subtype.ext hn]
  rw [← hkx'] at hxD
  have hcent' : ∀ (d : G) (hd : d ∈ Subgroup.zpowers (b : G)),
      QuotientGroup.mk' O ⟨d, hDH hd⟩ *
        QuotientGroup.mk' O ⟨(k : G), AGL81C.kSub_le q M H hkA⟩ =
      QuotientGroup.mk' O ⟨(k : G), AGL81C.kSub_le q M H hkA⟩ *
        QuotientGroup.mk' O ⟨d, hDH hd⟩ := by
    intro d hd
    exact Subgroup.mem_centralizer_iff.mp hxD _ (hmemD d hd)
  obtain ⟨n, hnN, hfix⟩ := exists_mul_mem_inf_centralizer (s := s) (h1 := h1)
    (hp := h.hp) (hcop := hcop) (hk := hkA) (hDH := hDH) (hD := hDp) (hcent := hcent')
  have hknKA : (k : G) * n ∈ AGL81C.kSub q M H :=
    (AGL81C.kSub q M H).mul_mem hkA hnN.1
  have hknCb : (k : G) * n ∈ Subgroup.centralizer (({(b : G)} : Set G)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfixb := hfix b (Subgroup.mem_zpowers (b : G))
    have hb : b * ((k : G) * n) = ((k : G) * n) * b := by
      have h' := congrArg (fun t : G => t * (b : G)) hfixb
      simpa [mul_assoc] using h'
    exact hb.symm
  have hknM : (k : G) * n ∈ M :=
    hKAM (Subgroup.mem_inf.mpr ⟨hknKA, hknCb⟩)
  have hknH : (k : G) * n ∈ H := AGL81C.kSub_le q M H hknKA
  have hnH : n ∈ H := AGL81C.kSub_le q M H hnN.1
  have hn1 : QuotientGroup.mk' O ⟨n, hnH⟩ = 1 :=
    (CFSG.AGLEmbedding.mk'_primeComplementCore_eq_one_iff q ⟨n, hnH⟩).mpr hnN.2
  have hxeq : x = QuotientGroup.mk' O ⟨(k : G) * n, hknH⟩ := by
    rw [← hkx', show (⟨(k : G) * n, hknH⟩ : ↥H) =
      ⟨(k : G), AGL81C.kSub_le q M H hkA⟩ * ⟨n, hnH⟩ from Subtype.ext rfl,
      map_mul, hn1, mul_one]
  have hmemX₁ : QuotientGroup.mk' O ⟨(k : G) * n, hknH⟩ ∈ X₁ := by
    have hmem : (⟨(k : G) * n, hknH⟩ : ↥H) ∈ (H ⊓ M).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hknH, hknM⟩
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hmem
  exact hxX₁ (hxeq.symm ▸ hmemX₁)

theorem Hyp1417.false_of_coprime (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) (hK1 : KFactThreeEightFive)
    {A : Subgroup G} (hAE : A ≤ E) (hA : Nat.card A = p)
    (hH : ¬ Subgroup.normalizer (A : Set G) ≤ M)
    (hcop : ¬ p ∣ Nat.card ↥(AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ⊓
      CFSG.Open.relPPrimeCore q (Subgroup.normalizer (A : Set G)))) : False := by
  classical
  obtain ⟨Q, F, s⟩ := h.exists_setting hAE hA hH
  obtain ⟨b, hbE, hbA, hbo, hbC⟩ :=
    h.exists_not_mem_centralizer_star h1 hNT hL34 hAE hA hH hcop
  have hqD := dvd_card_star_inf_centralizer (h := h) (s := s) (A := A) hAE le_rfl
    (b := b) hbE
  have hKAM := h.kSub_inf_centralizer_le h1 hNT hL34 hAE hA hH hbE hbA
  exact false_of_star_lift (h := h) (s := s) h1 hK1 hcop hbE hbo hbC hKAM hqD

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
