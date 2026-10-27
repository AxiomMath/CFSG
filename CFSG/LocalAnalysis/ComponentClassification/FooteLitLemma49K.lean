module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412Pair
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSzEightSylow
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Conj
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndThm3
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma411

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_normalizer_footeK {t x : G} (hx : x ∈ normalizer (footeB L t : Set G)) :
    x ∈ normalizer (footeK L t : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  have h1 := GSThmB.Six.conjugate_layerIn (footeB L t) x
  rw [conjugate_eq_of_mem_normalizer hx] at h1
  exact h1

theorem exists_isSylowOf_footeK_le (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {t : G}
    (ht : FooteInCC M t) :
    ∃ R : Subgroup G, IsSylowOf 2 R (footeK L t) ∧ R ≤ coreActionKernel M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht2, htC, hCt⟩ := ht
  obtain ⟨-, -, -, -, Q, hQB, hQC, -⟩ := foote_lemma_4_9_core h h47 hST hM ht2 htC hCt
  obtain ⟨hKB, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  have hBK : footeB L t ≤ normalizer (footeK L t : Set G) := fun b hb =>
    mem_normalizer_footeK (le_normalizer hb)
  have hR := hQB.inf_of_le_normalizer hKB hBK
  exact ⟨Q ⊓ footeK L t, hR, inf_le_left.trans hQC⟩

theorem exists_omega_of_isCoverOverTwo_sz_quotient {K R : Subgroup G} (hRK : IsSylowOf 2 R K)
    (hcov : IsCoverOverTwo (K ⧸ pPrimeCore 2 K) (Open.Sz 1)) :
    ∃ A : Subgroup G, A ≤ R ∧ Nat.card A = 16 ∧ (∀ x ∈ A, x ^ 2 = 1) ∧
      ∀ x ∈ R, x ^ 2 = 1 → x ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hRK
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hρ
  set T' : Sylow 2 (K ⧸ pPrimeCore 2 K) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
    with hT'
  obtain ⟨A₀, hA₀T, hA₀16, hA₀2, hA₀inv⟩ := exists_omega_of_isCoverOverTwo_sz hcov T'
  have hQO : ∀ x ∈ (Q : Subgroup ↥K), ρ x = 1 → x = 1 := by
    intro x hxQ hx1
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x, hxQ⟩
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hk
      simpa using this)
    have h2 : orderOf x ∣ Nat.card (pPrimeCore 2 ↥K) := Subgroup.orderOf_dvd_natCard _ hx1
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 ↥K)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (odd_card_pPrimeCore_two ↥K))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  set A' := A₀.comap ρ ⊓ (Q : Subgroup ↥K) with hA'
  have hinj : Function.Injective (ρ.comp A'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [mem_bot]
    exact Subtype.ext (hQO x (mem_inf.mp x.2).2 hx)
  have hrange : (ρ.comp A'.subtype).range = A₀ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (mem_inf.mp x.2).1
    · intro y hy
      have hyT : y ∈ (Q : Subgroup ↥K).map ρ := hA₀T hy
      obtain ⟨x, hxQ, rfl⟩ := mem_map.mp hyT
      exact ⟨⟨x, mem_inf.mpr ⟨hy, hxQ⟩⟩, rfl⟩
  refine ⟨A'.map K.subtype, ?_, ?_, ?_, ?_⟩
  · rw [← hQ]
    exact map_mono inf_le_right
  · rw [card_map_of_injective K.subtype_injective, ← hA₀16, ← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : ρ (x ^ 2) = 1 := by rw [map_pow]; exact hA₀2 _ (mem_inf.mp hx).1
    have h2 := hQO (x ^ 2) (pow_mem (mem_inf.mp hx).2 2) h1
    rw [subtype_apply, ← SubgroupClass.coe_pow, h2, OneMemClass.coe_one]
  · intro x hxR hx2
    rw [← hQ] at hxR
    obtain ⟨y, hyQ, rfl⟩ := mem_map.mp hxR
    refine ⟨y, mem_inf.mpr ⟨?_, hyQ⟩, rfl⟩
    have hy2 : y ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    exact hA₀inv _ (mem_map_of_mem ρ hyQ) (by rw [← map_pow, hy2, map_one])

theorem exists_isKleinFour_of_footeInCC (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {t : G}
    (ht : FooteInCC M t) {u : G} (hu : u ^ 2 = 1) (hut : u ∈ centralizer ({t} : Set G))
    (huN : u ∈ normalizer (M : Set G)) :
    ∃ V : Subgroup G, IsKleinFour V ∧ V ≤ coreActionKernel M ⊓ centralizer ({u} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht' := ht
  obtain ⟨ht2, htC, hCt⟩ := ht'
  obtain ⟨hBN, -, hBt, -⟩ := foote_lemma_4_9_core h h47 hST hM ht2 htC hCt
  obtain ⟨hKB, hKpc, -, -, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  obtain ⟨R, hR, hRC⟩ := exists_isSylowOf_footeK_le h h47 hST hAsc h2An hM ht
  set K := footeK L t with hK
  set C := coreActionKernel M with hC
  have huK : u ∈ normalizer (K : Set G) := mem_normalizer_footeK (hBN hut)
  have huC : u ∈ normalizer (C : Set G) := normalizer_le_normalizer_coreActionKernel M huN
  set Y := K ⊓ C with hY
  have huY : u ∈ normalizer (Y : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [hY, mem_inf, mem_inf, ← mem_normalizer_iff.mp huK y, ← mem_normalizer_iff.mp huC y]
  have hRY : IsSylowOf 2 R Y := hR.of_le (le_inf hR.le hRC) inf_le_left
  set Z := Y ⊔ zpowers u with hZ
  have hZY : Z ≤ normalizer (Y : Set G) := sup_le le_normalizer (zpowers_le.mpr huY)
  by_cases hu1 : u = 1
  · obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
    obtain ⟨V, hV, hVE⟩ := exists_isKleinFour_le hE2 (by omega)
    refine ⟨V, hV, fun x hx => mem_inf.mpr ⟨hEC (hVE hx), ?_⟩⟩
    rw [hu1]
    exact mem_centralizer_singleton_iff.mpr (by rw [mul_one, one_mul])
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu hu1
  have hup : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  obtain ⟨S₀, hS₀, huS₀⟩ := exists_isSylowOf_ge_of_le (le_sup_right : zpowers u ≤ Z) hup
  set R' := S₀ ⊓ Y with hR'
  have hR'Y : IsSylowOf 2 R' Y := hS₀.inf_of_le_normalizer le_sup_left hZY
  have huR' : u ∈ normalizer (R' : Set G) := by
    have h1 : u ∈ normalizer (S₀ : Set G) := le_normalizer (huS₀ (mem_zpowers u))
    rw [mem_normalizer_iff]
    intro y
    have e1 := mem_normalizer_iff.mp h1 y
    have e2 := mem_normalizer_iff.mp huY y
    exact ⟨fun hy => mem_inf.mpr ⟨e1.mp (mem_inf.mp hy).1, e2.mp (mem_inf.mp hy).2⟩,
      fun hy => mem_inf.mpr ⟨e1.mpr (mem_inf.mp hy).1, e2.mpr (mem_inf.mp hy).2⟩⟩
  have hR'K : IsSylowOf 2 R' K := by
    apply isSylowOf_of_card (hR'Y.le.trans inf_le_left)
    rw [hR'Y.card_eq, ← hRY.card_eq, hR.card_eq]
  have hR'C : R' ≤ C := hR'Y.le.trans inf_le_right
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; omega
  have hutC : t ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hut).symm
  rcases htype with ⟨-, htK⟩ | ⟨hcov, -⟩
  ·
    have hKeven : Even (Nat.card K) := by
      have h1 := CatFactsSp4.even_card_of_isPComponent hKpc
      rwa [Nat.card_congr (subgroupOfEquivOfLe hKB).toEquiv] at h1
    have hR'even : Even (Nat.card R') := by
      rw [hR'K.card_eq]
      have h2 : 2 ∣ Nat.card K := even_iff_two_dvd.mp hKeven
      have h3 : (Nat.card K).factorization 2 ≠ 0 :=
        (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2).ne'
      exact (Nat.even_pow' h3).mpr even_two
    obtain ⟨r, hrR', hr, hru⟩ := exists_involution_commute_of_even hR'even hu huR'
    have hrK : r ∈ K := hR'K.le hrR'
    have hr2 : r ^ 2 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
    have hr1 : r ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hr; omega
    have hrt : t ≠ r := fun h1 => htK (h1 ▸ hrK)
    have hrt' : r * t = t * r := mem_centralizer_singleton_iff.mp (hBt (hKB hrK))
    refine ⟨zpowers r ⊔ zpowers t, isKleinFour_sup_zpowers hr2 ht2' hr1 ht1 hrt hrt', sup_le ?_ ?_⟩
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨hR'C hrR', mem_centralizer_singleton_iff.mpr hru⟩
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨htC, hutC⟩
  ·
    obtain ⟨A, hAR', hA16, hA2, hAinv⟩ := exists_omega_of_isCoverOverTwo_sz_quotient hR'K hcov
    have huu : u * u = 1 := by rw [← sq]; exact hu
    have huA : ∀ y ∈ A, u * y * u⁻¹ ∈ A := by
      intro y hy
      refine hAinv _ ((mem_normalizer_iff.mp huR' y).mp (hAR' hy)) ?_
      rw [show (u * y * u⁻¹) ^ 2 = u * y ^ 2 * u⁻¹ by rw [sq, sq]; group, hA2 y hy]
      group
    have hu2' : ∀ y ∈ A, u * (u * y * u⁻¹) * u⁻¹ = y := fun y _ => by
      calc u * (u * y * u⁻¹) * u⁻¹ = (u * u) * y * (u * u)⁻¹ := by group
        _ = y := by rw [huu]; group
    have hcard := card_le_sq_card_inf_centralizer_of_sq
      (fun x hx y hy => commute_of_sq_eq_one hA2 hx hy)
      (fun y hy => by rw [← sq]; exact hA2 y hy) huA hu2'
    rw [hA16] at hcard
    have h4 : 4 ≤ Nat.card ↥(A ⊓ centralizer ({u} : Set G)) := by
      by_contra h5
      push Not at h5
      have : Nat.card ↥(A ⊓ centralizer ({u} : Set G)) ^ 2 ≤ 3 ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      omega
    obtain ⟨V, hV, hVA⟩ := exists_isKleinFour_le (fun x hx => hA2 x (mem_inf.mp hx).1) h4
    exact ⟨V, hV, fun x hx => mem_inf.mpr ⟨hR'C (hAR' (mem_inf.mp (hVA hx)).1),
      (mem_inf.mp (hVA hx)).2⟩⟩

end CFSG.ComponentClassification.FooteLit
