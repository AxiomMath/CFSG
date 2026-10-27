module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413One

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_ne_one_mem_coreActionKernel_of_card_sixteen
    (h : FooteSec4 G L) (hAR : FooteAutRankThree) {M : Subgroup G} (hM : IsFooteM L M)
    {F : Subgroup G} (hF2 : ∀ x ∈ F, x ^ 2 = 1) (hF16 : Nat.card F = 16)
    (hFN : F ≤ normalizer (M : Set G)) : ∃ u ∈ F, u ≠ 1 ∧ u ∈ coreActionKernel M := by
  by_contra hno
  push Not at hno
  obtain ⟨-, ⟨ε⟩⟩ := hM.quotient h
  set N := normalizer (M : Set G) with hN
  set Φ := footeAct (M := M) ε with hΦ
  have hinj : Function.Injective (Φ.comp (F.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [mem_bot]
    by_contra hx1
    have hx1' : ((x : N) : G) ≠ 1 := fun h1 => hx1 (Subtype.ext (Subtype.ext h1))
    exact hno _ x.2 hx1' (mem_coreActionKernel_of_footeAct_eq_one ε hx)
  set F' := (F.subgroupOf N).map Φ with hF'
  have hrange : (Φ.comp (F.subgroupOf N).subtype).range = F' := by
    rw [MonoidHom.range_comp, range_subtype]
  have hF'16 : Nat.card F' = 16 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hF16]
    exact Nat.card_congr (subgroupOfEquivOfLe hFN).toEquiv
  have hF'2 : ∀ e ∈ F', e * e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x * x = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]
      exact hF2 _ hx)
    rw [← map_mul, hx2, map_one]
  have h8 := hAR _ h.footeFamilyType F' hF'2
  omega

omit [Finite G] in
theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp hA x, ← mem_normalizer_iff.mp hB x]

theorem foote_lemma_4_13_sz
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hAR : FooteAutRankThree) {M : Subgroup G}
    (hM : IsFooteM L M)
    (hH : ∀ t : G, FooteInCC M t → ∀ u ∈ footeK L t, FooteInCC M u → u = t) {t : G}
    (ht : FooteInCC M t) (htK : t ∈ footeK L t) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht' := ht
  obtain ⟨ht2, htC, hCt⟩ := ht'
  obtain ⟨hBN, -, hBt, -⟩ := foote_lemma_4_9_core h h47 hST hM ht2 htC hCt
  obtain ⟨hKB, -, -, -, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  obtain ⟨E₈, -, hE₈8, -⟩ := hM.exists_card_eight h
  obtain ⟨R₀, hR₀, hR₀C⟩ := exists_isSylowOf_footeK_le h h47 hST hAsc h2An hM ht
  obtain ⟨S₀, hS₀, hS₀N⟩ := exists_isSylowOf_centralizer_le_normalizer h h47 hST hM ht2 htC
  set K := footeK L t with hK
  set C := coreActionKernel M with hC
  set N := normalizer (M : Set G) with hN
  have hcov : IsCoverOverTwo (K ⧸ pPrimeCore 2 K) (Open.Sz 1) := by
    rcases htype with ⟨-, hnot⟩ | ⟨hc, -⟩
    · exact absurd htK hnot
    · exact hc
  have hCN : ∀ c ∈ C, c ∈ N := fun c hc => (mem_coreActionKernel.mp hc).1
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have ht2' : t ^ 2 = 1 := by rw [sq]; exact htt
  have hKt : K ≤ centralizer ({t} : Set G) := hKB.trans hBt
  set D := C ⊓ centralizer ({t} : Set G) with hD
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 D
  have hTD : T ≤ D := hT.le
  have hTC : T ≤ C := hTD.trans inf_le_left
  have hTt : T ≤ centralizer ({t} : Set G) := hTD.trans inf_le_right
  have hKCD : K ⊓ C ≤ D := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp hx).2, hKt (mem_inf.mp hx).1⟩
  have hDKC : D ≤ normalizer ((K ⊓ C : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_inf_of_mem (mem_normalizer_footeK (hBN (mem_inf.mp hd).2))
      (le_normalizer (mem_inf.mp hd).1)
  have hTKC := hT.inf_of_le_normalizer hKCD hDKC
  have hTKC' : T ⊓ (K ⊓ C) = T ⊓ K := by
    ext x
    simp only [mem_inf]
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, hTC hx.1⟩⟩
  rw [hTKC'] at hTKC
  have hR₀KC : IsSylowOf 2 R₀ (K ⊓ C) := hR₀.of_le (le_inf hR₀.le hR₀C) inf_le_left
  set R := T ⊓ K with hR
  have hRK : IsSylowOf 2 R K := by
    apply isSylowOf_of_card (hTKC.le.trans inf_le_left)
    rw [hTKC.card_eq, ← hR₀KC.card_eq, hR₀.card_eq]
  obtain ⟨A, hAR', hA16, hA2, hAinv⟩ := exists_omega_of_isCoverOverTwo_sz_quotient hRK hcov
  have hAT : A ≤ T := hAR'.trans inf_le_left
  have hAK : A ≤ K := hAR'.trans inf_le_right
  have hTA : ∀ x ∈ T, x ^ 2 = 1 → x ∈ A := by
    intro x hxT hx2
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem A
    have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have hxs : x * t = t * x := mem_centralizer_singleton_iff.mp (hTt hxT)
    rcases mem_or_mul_mem_footeK h h47 hST hAsc h2An hM ht (hTC hxT) hxs hxo with hxK | hxtK
    · exact hAinv x (mem_inf.mpr ⟨hxT, hxK⟩) hx2
    · have hxK : x ∈ K := by
        have h1 := mul_mem hxtK (inv_mem htK)
        rwa [mul_inv_cancel_right] at h1
      exact hAinv x (mem_inf.mpr ⟨hxT, hxK⟩) hx2
  have htT : t ∈ T := by
    have htN : zpowers t ≤ normalizer (T : Set G) := zpowers_le.mpr
      (mem_normalizer_of_forall_commute fun u hu => mem_centralizer_singleton_iff.mp (hTt hu))
    have hp : IsPGroup 2 ↥(T ⊔ zpowers t) :=
      hT.isPGroup.to_sup_of_normal_left' (isPGroup_two_zpowers_of_sq_eq_one ht2') htN
    have hle : T ⊔ zpowers t ≤ D :=
      sup_le hTD (zpowers_le.mpr (mem_inf.mpr ⟨htC, mem_centralizer_singleton_iff.mpr rfl⟩))
    have h1 := hT.eq_of_le le_sup_left hle hp
    rw [← h1]
    exact mem_sup_right (mem_zpowers t)
  have hNA : ∀ n ∈ N, n * t * n⁻¹ ∈ A → n * t * n⁻¹ = t := fun n hn hnA =>
    hH t ht _ (hAK hnA) (ht.conj hn)
  have hconj2 : ∀ g : G, (g * t * g⁻¹) ^ 2 = 1 := fun g => by
    rw [conj_pow, ht2', mul_one, mul_inv_cancel]
  have hGT : ∀ g : G, g * t * g⁻¹ ∈ T → g * t * g⁻¹ = t := by
    intro g hgT
    have h1 : t ∈ coreActionKernel (conjugate M g) := by
      rw [mem_coreActionKernel_conjugate_iff]
      exact hTC hgT
    obtain ⟨n, hn, c, hc, rfl⟩ := foote_cor_4_8_iii h h47 hST hM ht2 htC h1
    have hct : c * t * c⁻¹ = t := by
      rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
    have h2 : n * c * t * (n * c)⁻¹ = n * t * n⁻¹ := by
      calc n * c * t * (n * c)⁻¹ = n * (c * t * c⁻¹) * n⁻¹ := by group
        _ = n * t * n⁻¹ := by rw [hct]
    rw [h2] at hgT ⊢
    exact hNA n hn (hTA _ hgT (hconj2 n))
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_ge_of_le
    (le_inf (fun x hx => hCN x (hTC hx)) hTt : T ≤ N ⊓ centralizer ({t} : Set G)) hT.isPGroup
  have hS₀' : IsSylowOf 2 S₀ (N ⊓ centralizer ({t} : Set G)) :=
    hS₀.of_le (le_inf hS₀N hS₀.le) inf_le_right
  have hSt : IsSylowOf 2 S (centralizer ({t} : Set G)) := by
    apply isSylowOf_of_card (hS.le.trans inf_le_right)
    rw [hS.card_eq, ← hS₀'.card_eq, hS₀.card_eq]
  have hSN : S ≤ N := hS.le.trans inf_le_left
  have hSC : S ⊓ C = T :=
    hT.eq_of_le (le_inf hTS hTC)
      (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, hSt.le (mem_inf.mp hx).1⟩)
      (hS.isPGroup.to_le inf_le_left)
  obtain ⟨g₁, hg₁c, hg₁ne⟩ := exists_conj_commute_ne_of_card_eight h.simple hE₈8 ht2
  set y := g₁ * t * g₁⁻¹ with hy
  have hyt : y ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hg₁c
  have hy2 : y ^ 2 = 1 := hconj2 g₁
  obtain ⟨c₁, hc₁, hc₁y⟩ := exists_conj_le_of_isSylowOf hSt (zpowers_le.mpr hyt)
    (isPGroup_two_zpowers_of_sq_eq_one hy2)
  set g := c₁⁻¹ * g₁ with hgdef
  set t' := g * t * g⁻¹ with ht'def
  have ht'eq : t' = c₁⁻¹ * y * c₁ := by rw [ht'def, hgdef, hy]; group
  have ht'S : t' ∈ S := by rw [ht'eq]; exact hc₁y y (mem_zpowers y)
  have hc₁t : c₁ * t * c₁⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hc₁, mul_inv_cancel_right]
  have ht'ne : t' ≠ t := by
    intro h1
    apply hg₁ne
    calc y = c₁ * (c₁⁻¹ * y * c₁) * c₁⁻¹ := by group
      _ = c₁ * t * c₁⁻¹ := by rw [← ht'eq, h1]
      _ = t := hc₁t
  have ht'T : t' ∉ T := fun h1 => ht'ne (hGT g h1)
  have ht'2 : t' ^ 2 = 1 := hconj2 g
  have ht'N : t' ∈ N := hSN ht'S
  have ht'K : t' ∈ normalizer (K : Set G) := mem_normalizer_footeK (hBN (hSt.le ht'S))
  have ht'T' : t' ∈ normalizer (T : Set G) := by
    rw [← hSC]
    exact mem_normalizer_inf_of_mem (le_normalizer ht'S)
      (normalizer_le_normalizer_coreActionKernel M ht'N)
  have ht'R : t' ∈ normalizer (R : Set G) := mem_normalizer_inf_of_mem ht'T' ht'K
  have hcA : ∀ a ∈ A, t' * a * t'⁻¹ = a := fun a ha =>
    conj_eq_of_isCoverOverTwo_sz hRK hcov ht'K ht'R ht'2 (hAR' ha) (hA2 a ha)
  have hAgt : conjugate A g ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 : t' * (g * x * g⁻¹) = (g * x * g⁻¹) * t' := by
      calc t' * (g * x * g⁻¹) = t' * (g * x * g⁻¹) * t'⁻¹ * t' := by group
        _ = (g * x * g⁻¹) * t' := by rw [hcA _ hx]
    rw [mem_centralizer_singleton_iff]
    calc x * t = g⁻¹ * ((g * x * g⁻¹) * t') * g := by rw [ht'def]; group
      _ = g⁻¹ * (t' * (g * x * g⁻¹)) * g := by rw [h1]
      _ = t * x := by rw [ht'def]; group
  have hAgp : IsPGroup 2 (conjugate A g) :=
    IsPGroup.of_card (n := 4) (by rw [card_conjugate_eq_card, hA16]; norm_num)
  obtain ⟨c₂, hc₂, hc₂A⟩ := exists_conj_le_of_isSylowOf hSt hAgt hAgp
  set k := g * c₂ with hkdef
  have hAk : ∀ a ∈ A, k⁻¹ * a * k ∈ S := by
    intro a ha
    have h1 : g⁻¹ * a * g ∈ conjugate A g := by
      rw [mem_conjugate_iff, show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
      exact ha
    have h2 := hc₂A _ h1
    rwa [show c₂⁻¹ * (g⁻¹ * a * g) * c₂ = k⁻¹ * a * k by rw [hkdef]; group] at h2
  have hc₂t : c₂ * t * c₂⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hc₂, mul_inv_cancel_right]
  have ht'k : t' = k * t * k⁻¹ := by
    rw [ht'def, hkdef]
    calc g * t * g⁻¹ = g * (c₂ * t * c₂⁻¹) * g⁻¹ := by rw [hc₂t]
      _ = g * c₂ * t * (g * c₂)⁻¹ := by group
  have hkN : k ∉ N := by
    intro h1
    apply ht'T
    rw [← hSC]
    refine mem_inf.mpr ⟨ht'S, ?_⟩
    rw [ht'k]
    exact (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M h1) t).mp htC
  have htA : t ∈ A := hTA t htT ht2'
  have htkT : k⁻¹ * t * k ∉ T := by
    intro h1
    have h2 := hGT k⁻¹ (by rwa [inv_inv])
    apply ht'ne
    rw [ht'k]
    calc k * t * k⁻¹ = k * (k⁻¹ * t * k⁻¹⁻¹) * k⁻¹ := by rw [h2]
      _ = t := by group
  have hAkS : conjugate A k ≤ S := fun x hx => by
    rw [mem_conjugate_iff] at hx
    have h1 := hAk _ hx
    rwa [show k⁻¹ * (k * x * k⁻¹) * k = x by group] at h1
  obtain ⟨u, huAk, hu1, huC⟩ := exists_ne_one_mem_coreActionKernel_of_card_sixteen h hAR hM
    (sq_eq_one_of_mem_conjugate hA2 k) (by rw [card_conjugate_eq_card, hA16]) (hAkS.trans hSN)
  have huT : u ∈ T := by
    rw [← hSC]
    exact mem_inf.mpr ⟨hAkS huAk, huC⟩
  have hu2 : u ^ 2 = 1 := sq_eq_one_of_mem_conjugate hA2 k u huAk
  have huo : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have huA : k * u * k⁻¹ ∈ A := (mem_conjugate_iff.mp huAk)
  have huCC : ¬ FooteInCC M u := by
    intro hu
    have hut : u = t := hH t ht u (hAK (hTA u huT hu2)) hu
    apply htkT
    have h1 : k * t * k⁻¹ ∈ A := by rw [← hut]; exact huA
    have h2 := hGT k (hAT h1)
    rw [show k⁻¹ * t * k = t by
      calc k⁻¹ * t * k = k⁻¹ * (k * t * k⁻¹) * k := by rw [h2]
        _ = t := by group]
    exact htT
  have hCu : centralizer ({u} : Set G) ≤ N := by
    by_contra h1
    exact huCC ⟨huo, hTC huT, h1⟩
  have hu' : u ∈ coreActionKernel (conjugate M k) := by
    rw [mem_coreActionKernel_conjugate_iff]
    exact hTC (hAT huA)
  obtain ⟨n, hn, c, hc, hknc⟩ := foote_cor_4_8_iii h h47 hST hM huo (hTC huT) hu'
  exact hkN (hknc ▸ mul_mem hn (hCu hc))

end CFSG.ComponentClassification.FooteLit
