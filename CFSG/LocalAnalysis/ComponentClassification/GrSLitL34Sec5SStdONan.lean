module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCoreModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCoreLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdHost
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdImage
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdPair
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSylowShear
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCentralizer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped commutatorElement

section Glue

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_of_card_sylow_eq_two {H : Subgroup G}
    (hS : ∀ S : Sylow 2 ↥H, Nat.card S = 2) :
    ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P → Nat.card P ≤ 2 := by
  intro P hPH hP
  have hPsub : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨S, hPS⟩ := hPsub.exists_le_sylow
  calc
    Nat.card P = Nat.card (P.subgroupOf H) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv).symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hPS
    _ = 2 := hS S

theorem isKGroupCat_quotient_pPrimeCore_centralizer [IsSimpleGroup G]
    (hnonab : ∃ g h : G, g * h ≠ h * g) (hK : Assembly.KProper Blueprint.Catalog G)
    {z : G} (hz : orderOf z = 2) :
    SectionRank.IsKGroupCat (↥(centralizer ({z} : Set G)) ⧸
      pPrimeCore 2 ↥(centralizer ({z} : Set G))) := by
  have hcenter : Subgroup.center G = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).2
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hne : centralizer ({z} : Set G) ≠ ⊤ := by
    intro htop
    have hzmem : z ∈ Subgroup.center G :=
      (Subgroup.centralizer_eq_top_iff_subset.mp htop) (by simp)
    rw [hcenter] at hzmem
    exact hz1 (Subgroup.mem_bot.mp hzmem)
  exact (CFSG.QuasithinUnique.isKGroupCat_of_kProper hK hne).quotient
    (pPrimeCore 2 ↥(centralizer ({z} : Set G)))

theorem centralizerCore_subgroupOf_facts {J : Subgroup G} (hst : IsStandardSubgroup J)
    {t z : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G))
    (hperf : ∀ L : Subgroup G, L ≤ centralizer ({t} : Set G) → ⁅L, L⁆ = L → L ≤ J)
    {K : Subgroup G}
    (hK : ⁅(⁅J ⊓ centralizer ({z} : Set G), J ⊓ centralizer ({z} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({z} : Set G), J ⊓ centralizer ({z} : Set G)⁆⁆ = K)
    (htC : t ∈ centralizer ({z} : Set G)) :
    K.subgroupOf (centralizer ({z} : Set G)) ≤
        centralizer ({(⟨t, htC⟩ : ↥(centralizer ({z} : Set G)))} :
          Set ↥(centralizer ({z} : Set G))) ∧
      ((K.subgroupOf (centralizer ({z} : Set G))).subgroupOf
        (centralizer ({(⟨t, htC⟩ : ↥(centralizer ({z} : Set G)))} :
          Set ↥(centralizer ({z} : Set G))))).Normal ∧
      ∀ L : Subgroup ↥(centralizer ({z} : Set G)),
        L ≤ centralizer ({(⟨t, htC⟩ : ↥(centralizer ({z} : Set G)))} :
          Set ↥(centralizer ({z} : Set G))) →
        ⁅L, L⁆ = L → L ≤ K.subgroupOf (centralizer ({z} : Set G)) := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hC
  set D : Subgroup G := J ⊓ C with hD
  set tX : ↥C := ⟨t, htC⟩ with htX
  have hKD : K ≤ D := hK ▸ (commutator_le_self ⁅D, D⁆).trans (commutator_le_self D)
  have hKJ : K ≤ J := hKD.trans inf_le_left
  have hKC : K ≤ C := hKD.trans inf_le_right
  have htJ' : ∀ k : G, k ∈ K → k * t = t * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp htJ k (hKJ hk)
  have hKcent : K.subgroupOf C ≤ centralizer ({tX} : Set ↥C) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (k : G) * t = t * (k : G)
    exact htJ' (k : G) (Subgroup.mem_subgroupOf.mp hk)
  refine ⟨hKcent, ?_, ?_⟩
  have hKlered : ∀ c : ↥C, c ∈ centralizer ({tX} : Set ↥C) →
      ∀ k : G, k ∈ K → (c : G) * k * (c : G)⁻¹ ∈ K := by
    intro c hc k hk
    have hct : (c : G) ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun x : ↥C => (x : G))
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have hnormJ : (c : G) ∈ Subgroup.normalizer (J : Set G) :=
      (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
        (CFSG.IsStandardSubgroup.assembly hst) htJ ht).1 hct
    have hcC : (c : G) ∈ C := c.2
    have hnormD : (c : G) ∈ Subgroup.normalizer (D : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hnormJ, (Subgroup.le_normalizer : C ≤ Subgroup.normalizer (C : Set G)) hcC⟩
    have hDmap : D.map (MulAut.conj (c : G)).toMonoidHom = D :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormD
    have hEmap : (⁅D, D⁆ : Subgroup G).map (MulAut.conj (c : G)).toMonoidHom = ⁅D, D⁆ := by
      rw [Subgroup.map_commutator, hDmap]
    have hKmap : K.map (MulAut.conj (c : G)).toMonoidHom = K := by
      rw [← hK, Subgroup.map_commutator, hEmap]
    have hmem : (MulAut.conj (c : G)) k ∈ K.map (MulAut.conj (c : G)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hk
    rwa [hKmap, MulAut.conj_apply] at hmem
  refine Subgroup.Normal.mk ?_
  intro n hn c
  have hnK : ((n : ↥C) : G) ∈ K :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hn)
  have hcM : (c : ↥C) ∈ centralizer ({tX} : Set ↥C) := c.2
  have hmem : ((c : ↥C) : G) * ((n : ↥C) : G) * (((c : ↥C) : G))⁻¹ ∈ K :=
    hKlered (c : ↥C) hcM _ hnK
  apply Subgroup.mem_subgroupOf.mpr
  apply Subgroup.mem_subgroupOf.mpr
  simpa using hmem
  intro L hLt hLperf
  set L' : Subgroup G := L.map C.subtype with hL'
  have hL'perf : ⁅L', L'⁆ = L' := by
    have hmap := Subgroup.map_commutator (H₁ := L) (H₂ := L) (f := C.subtype)
    rw [hLperf] at hmap
    exact hmap.symm
  have hL't : L' ≤ centralizer ({t} : Set G) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun y : ↥C => (y : G))
      (Subgroup.mem_centralizer_singleton_iff.mp (hLt hl))
  have hL'J : L' ≤ J := hperf L' hL't hL'perf
  have hL'C : L' ≤ C := Subgroup.map_subtype_le L
  have hL'D : L' ≤ D := le_inf hL'J hL'C
  have hL'E : L' ≤ ⁅D, D⁆ := hL'perf ▸ Subgroup.commutator_mono hL'D hL'D
  have hL'K : L' ≤ K := by
    have h1 : ⁅L', L'⁆ ≤ ⁅(⁅D, D⁆ : Subgroup G), ⁅D, D⁆⁆ :=
      Subgroup.commutator_mono hL'E hL'E
    rw [hL'perf] at h1
    exact hK ▸ h1
  intro l hl
  exact Subgroup.mem_subgroupOf.mpr (hL'K (Subgroup.mem_map_of_mem C.subtype hl))

theorem centralizerCore_onan
    {J : Subgroup G}
    (hF : IsSporadic (↥J ⧸ center ↥J) .ONan) (hZ : Odd (Nat.card (center ↥J)))
    {a : G} (haJ : a ∈ J) (ha : orderOf a = 2) {K : Subgroup G}
    (hK : ⁅(⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆⁆ = K) :
    (IsQuasisimple ↥K ∧ Blueprint.LieModel (↥K ⧸ center ↥K) .PSL 3 2 2) ∧
      (∃ w ∈ K, orderOf w = 4 ∧ w * w = a ∧ (∀ k ∈ K, w * k = k * w) ∧
        ∀ c ∈ K, (∀ k ∈ K, c * k = k * c) → (∃ n : ℕ, c ^ 2 ^ n = 1) → c ∈ zpowers w) ∧
      (∃ u ∈ K, orderOf u = 2 ∧ ∃ k ∈ K, u * k ≠ k * u) ∧
      ∀ y ∈ J ⊓ centralizer ({a} : Set G), (∃ n : ℕ, (y * y) ^ 2 ^ n = 1) → y * y ∈ K := by
  have hā : orderOf (QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J) = 2 :=
    orderOf_mk'_eq_two_of_odd hZ (by rw [Subgroup.orderOf_mk]; exact ha)
  have hLp := commutator_commutator_centralizer_onan hF hā
  exact ⟨isQuasisimple_centralizerCore_of_quotient hZ haJ ha rfl hLp
      (lieModel_commutator_centralizer_onan hF hā) hK,
    exists_center_centralizerCore_of_quotient hZ haJ ha rfl hLp
      (exists_center_commutator_centralizer_onan hF hā) hK,
    exists_noncentral_involution_centralizerCore_of_quotient hZ haJ ha rfl hLp
      (exists_noncentral_involution_commutator_centralizer_onan hF hā) hK,
    fun y hy hy2 => mul_self_mem_centralizerCore_of_quotient hZ haJ ha rfl hLp
      (fun _ hy' => mul_self_mem_commutator_centralizer_onan hF hā hy') hK hy hy2⟩

end Glue

theorem false_of_onan_standard_core
     (hCI : GSLit.ClassicalInvolutionInput) (hcat : L34CyclicProperFixedCatalog)
    (hGe : GSThmB.CF24cCenterGe) (hSuz6 : RankTwoL3Four.SuzMultiplierSix)
    {G : Type} [Group G] [Finite G] [hsimple : IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hUo : ¬ CFSG.ComponentClassification.OutcomeLocal.UOutcome G)
    {x : G} (hx : orderOf x = 2) {P : Subgroup G}
    (hPx : P ≤ centralizer ({x} : Set G))
    (hτ : IsSporadic (↥P ⧸ Open.fusionZStar ↥P) .ONan)
    (hst : IsStandardSubgroup P)
    (hO : oddIn P ≤ (center ↥P).map P.subtype) : False := by
  classical
  let b : G := x
  let J : Subgroup G := P
  have hb : orderOf b = 2 := hx
  have hJb : J ≤ centralizer ({b} : Set G) := hPx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hF, hZ, -⟩ := isSporadic_center_onan_of_isStandardSubgroup hst hτ hO
  have hcen : center (↥J ⧸ center ↥J) = ⊥ :=
    CFSG.EvenSporadicStandard.Solomon78.center_eq_bot_of_isSporadic_on hF
  have hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
      α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range :=
    fun _ _ hα hβ => mul_mem_range_conj_onan hF hα hβ
  have hfix : ∀ (T : Sylow 2 (↥J ⧸ center ↥J)) (α : MulAut (↥J ⧸ center ↥J)),
      (∀ x ∈ (T : Subgroup (↥J ⧸ center ↥J)), α x = x) →
        α ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range :=
    fun T _ hα => mem_range_conj_of_forall_mem_sylow_onan hF T hα
  have hZT : ∀ T : Sylow 2 (↥J ⧸ center ↥J),
      Nat.card (center (T : Subgroup (↥J ⧸ center ↥J))) = 2 :=
    card_center_sylow_onan hF
  have hcls : ∀ a b : ↥J, orderOf a = 2 → orderOf b = 2 → ∃ j : ↥J, b = j⁻¹ * a * j :=
    fun _ _ ha hb => exists_conj_of_orderOf_eq_two_onan hF hZ ha hb
  have hpow : ∀ a : ↥J, orderOf a = 2 → ∃ y : ↥J, y ^ 8 = a :=
    fun _ ha => exists_pow_eight_eq_of_orderOf_eq_two_onan hF hZ ha
  have hC2 : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → Nat.card P ≤ 2 :=
    card_le_two_of_card_sylow_eq_two
      (card_sylow_centralizer_eq_two_of_onan_of_classicalInvolution hCI hnonab hKP hUo hst hF hZ)
  have htJ : b ∈ centralizer (J : Set G) := by
    rw [mem_centralizer_iff]
    intro j hj
    exact mem_centralizer_singleton_iff.mp (hJb hj)
  obtain ⟨P, z, hzJ, hz, hzP, hzc, htP, -, hext, hZ', hzt, hzzt, hfus⟩ :=
    exists_sylow_shear_of_standard hnonab hst hZ hcen hOut hfix hZT hcls hpow hC2 hb htJ
  have hcyc : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → IsCyclic P := by
    intro Q hQ hQp
    have h2 := hC2 Q hQ hQp
    have h0 : 0 < Nat.card Q := Nat.card_pos
    exact isCyclic_of_card_dvd_prime (p := 2) (by interval_cases (Nat.card Q) <;> norm_num)
  have hperfG : ∀ L : Subgroup G, L ≤ centralizer ({b} : Set G) → ⁅L, L⁆ = L → L ≤ J :=
    fun _ hLt hL => le_of_perfect_le_centralizer hst hOut hcyc hb htJ hLt hL
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup G,
      ⁅(⁅J ⊓ centralizer ({z} : Set G), J ⊓ centralizer ({z} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({z} : Set G), J ⊓ centralizer ({z} : Set G)⁆⁆ = K := ⟨_, rfl⟩
  obtain ⟨⟨hKq, hKL⟩, ⟨w, hwK, hw, hww, hwc, hZK⟩, ⟨u, huK, hu, k₀, hk₀K, huk₀⟩, -⟩ :=
    centralizerCore_onan hF hZ hzJ hz hKdef
  have hKD : K ≤ J ⊓ centralizer ({z} : Set G) := by
    rw [← hKdef]
    exact (commutator_le_self _).trans (commutator_le_self _)
  have hKJ : K ≤ J := hKD.trans inf_le_left
  have hKC : K ≤ centralizer ({z} : Set G) := hKD.trans inf_le_right
  have htC : b ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htJ z hzJ).symm
  obtain ⟨hKXt, hKXn, hperfX⟩ :=
    centralizerCore_subgroupOf_facts hst hb htJ hperfG hKdef htC
  have hU : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({z} : Set G)))) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(centralizer ({z} : Set G))))
  let eK : ↥(K.subgroupOf (centralizer ({z} : Set G))) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have hKXq : IsQuasisimple ↥(K.subgroupOf (centralizer ({z} : Set G))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq
  have hKXL : Blueprint.LieModel (↥(K.subgroupOf (centralizer ({z} : Set G))) ⧸
      center ↥(K.subgroupOf (centralizer ({z} : Set G)))) .PSL 3 2 2 :=
    Blueprint.LieModel.of_mulEquiv
      (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv eK).symm hKL
  have hK2X : ∃ k ∈ K.subgroupOf (centralizer ({z} : Set G)), orderOf k = 2 :=
    ⟨⟨u, hKC huK⟩, Subgroup.mem_subgroupOf.mpr huK, by rw [Subgroup.orderOf_mk]; exact hu⟩
  have htXo : orderOf (⟨b, htC⟩ : ↥(centralizer ({z} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hb
  have htX2 : (⟨b, htC⟩ : ↥(centralizer ({z} : Set G))) ^ 2 = 1 := by
    rw [← htXo]; exact pow_orderOf_eq_one _
  have hwKX : (⟨w, hKC hwK⟩ : ↥(centralizer ({z} : Set G))) ∈
      K.subgroupOf (centralizer ({z} : Set G)) := Subgroup.mem_subgroupOf.mpr hwK
  have hwcX : ∀ k ∈ K.subgroupOf (centralizer ({z} : Set G)),
      (⟨w, hKC hwK⟩ : ↥(centralizer ({z} : Set G))) * k = k * ⟨w, hKC hwK⟩ := fun k hk =>
    Subtype.ext (hwc k (Subgroup.mem_subgroupOf.mp hk))
  have hwX : orderOf (⟨w, hKC hwK⟩ : ↥(centralizer ({z} : Set G))) = 4 := by
    rw [Subgroup.orderOf_mk]; exact hw
  have hZKX : ∀ c ∈ K.subgroupOf (centralizer ({z} : Set G)),
      (∀ k ∈ K.subgroupOf (centralizer ({z} : Set G)), c * k = k * c) →
      (∃ n : ℕ, c ^ 2 ^ n = 1) → c ∈ zpowers (⟨w, hKC hwK⟩ : ↥(centralizer ({z} : Set G))) := by
    intro c hc hcc hc2
    have hcK : (c : G) ∈ K := Subgroup.mem_subgroupOf.mp hc
    have hcc' : ∀ k ∈ K, (c : G) * k = k * c := fun k hk =>
      congrArg Subtype.val (hcc ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
    obtain ⟨n, hn⟩ := hc2
    have hc2' : ∃ n : ℕ, (c : G) ^ 2 ^ n = 1 := ⟨n, by simpa using congrArg Subtype.val hn⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hZK c hcK hcc' hc2')
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)⟩
  obtain ⟨hKbt, hKbcomp⟩ := isComponent_map_centralizer_quotient hU htX2 hKXt hKXq hKXn hK2X
  obtain ⟨-, hKbL, hwb, hZKb⟩ := lieModel_map_and_center_of_odd hU hKXq hKXL hwKX hwX hZKX
  have hKbar := isKGroupCat_quotient_pPrimeCore_centralizer hnonab hKP hz
  have hObar := CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥(centralizer ({z} : Set G)) 2
  have htb := orderOf_mk'_eq_two_of_odd hU htXo
  have hwbK := Subgroup.mem_map_of_mem
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G)))) hwKX
  have hwbc : ∀ d ∈ (K.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G)))),
      QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))) ⟨w, hKC hwK⟩ * d =
        d * QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))) ⟨w, hKC hwK⟩ := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hwcX k hk]
  have hwbZ : ∀ y : ↥(centralizer ({z} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({z} : Set G)),
      QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))) ⟨w, hKC hwK⟩ *
          QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))) ⟨w, hKC hwK⟩ * y =
        y * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))) ⟨w, hKC hwK⟩ *
          QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))) ⟨w, hKC hwK⟩) := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))) y
    rw [← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show w * w * (y : G) = (y : G) * (w * w)
    rw [hww]
    exact (mem_centralizer_singleton_iff.mp y.2).symm
  rcases isComponent_or_swap_of_isComponent_centralizer_l34 hcat hGe hSuz6 hKbar hObar htb hKbt
      hKbcomp hKbL hwbK hwbc hwb hwbZ hZKb with hcomp | ⟨Q, hQ, hQt, hKQ⟩
  ·
    have huJ : u ∈ J := hKJ huK
    obtain ⟨g, hg⟩ := hfus u huJ hu
    obtain ⟨Ku, hKudef⟩ : ∃ Ku : Subgroup G,
        ⁅(⁅J ⊓ centralizer ({u} : Set G), J ⊓ centralizer ({u} : Set G)⁆ : Subgroup G),
          ⁅J ⊓ centralizer ({u} : Set G), J ⊓ centralizer ({u} : Set G)⁆⁆ = Ku := ⟨_, rfl⟩
    obtain ⟨⟨hKuq, -⟩, -, -, hKusq⟩ := centralizerCore_onan hF hZ huJ hu hKudef
    have hKuD : Ku ≤ J ⊓ centralizer ({u} : Set G) := by
      rw [← hKudef]
      exact (commutator_le_self _).trans (commutator_le_self _)
    have hwu : w ∈ J ⊓ centralizer ({u} : Set G) :=
      ⟨hKJ hwK, mem_centralizer_singleton_iff.mpr (hwc u huK)⟩
    have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hzKu : z ∈ Ku := by
      rw [← hww]
      exact hKusq w hwu ⟨1, by rw [hww, pow_one]; exact hz2⟩
    have hKup : ⁅Ku, Ku⁆ = Ku := (Subgroup.isPerfect_iff (H := Ku)).mp hKuq.1
    have hclsz : ∀ a ∈ J, orderOf a = 2 → ∃ j ∈ J, a = j⁻¹ * z * j := by
      intro a haJ ha
      obtain ⟨j, hj⟩ := hcls ⟨z, hzJ⟩ ⟨a, haJ⟩ (by rw [Subgroup.orderOf_mk]; exact hz)
        (by rw [Subgroup.orderOf_mk]; exact ha)
      exact ⟨j, j.2, by simpa using congrArg Subtype.val hj⟩
    obtain ⟨x, hxC, hx⟩ := exists_mem_centralizer_conj_eq_mul_of_perfect hJb hperfG hclsz hKup
      (hKuD.trans inf_le_left) (hKuD.trans inf_le_right) hzKu hz hg
    exact false_of_isComponent_map_of_conj_eq_mul hU htX2 hKXq hK2X hKXt hperfX hcomp
      (u := ⟨u, hKC huK⟩) (x := ⟨x, hxC⟩) (Subgroup.mem_subgroupOf.mpr huK)
      ⟨⟨k₀, hKC hk₀K⟩, Subgroup.mem_subgroupOf.mpr hk₀K,
        fun h => huk₀ (congrArg Subtype.val h)⟩
      (Subtype.ext hx)
  ·
    obtain ⟨ε, hε⟩ := exists_units_hom_eq_neg_one_of_swap hU htX2 hperfX hQ hQt hKQ
    exact false_of_units_hom_of_isExtremalIn
      (fun N _ => CFSG.Quasithin.I4.index_ne_two_of_isSimpleGroup hnonab N) P hz hzP hzc hb htP
      hext hZ' hzt hzzt ε htC hε

theorem false_of_onan_standard
    (hCI : GSLit.ClassicalInvolutionInput) (hcat : L34CyclicProperFixedCatalog)
    (hGe : GSThmB.CF24cCenterGe) (hSuz6 : RankTwoL3Four.SuzMultiplierSix)
    {G : Type} [Group G] [Finite G] (hG : L34BaseSetting G) {b : G} {J : Subgroup G}
    (hb : orderOf b = 2) (hJb : J ≤ centralizer ({b} : Set G))
    (hτ : IsSporadic (↥J ⧸ Open.fusionZStar ↥J) .ONan) (hst : IsStandardSubgroup J)
    (hO : oddIn J ≤ (center ↥J).map J.subtype) : False := by
  obtain ⟨hsimple, hnonab, hKP, -, hUo, -, -, -⟩ := hG
  exact false_of_onan_standard_core (hsimple := hsimple) hCI hcat hGe hSuz6 hnonab hKP hUo
    hb hJb hτ hst hO

end CFSG.ComponentClassification.GrSLit.L34Sec5S
