module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnM12
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Struct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12 CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec14
open scoped commutatorElement

section Transport

variable {G : Type*} [Group G] {S : Subgroup G} {a b y x : G}

theorem m12Data_top (h : Sec13.M12Data S a b y x) :
    Sec13.M12Data (⊤ : Subgroup ↥S) ⟨a, a_mem h⟩ ⟨b, b_mem h⟩ ⟨y, y_mem h⟩ ⟨x, x_mem h⟩ where
  ha := Subtype.ext (by simpa using h.ha)
  hb := Subtype.ext (by simpa using h.hb)
  hab := Subtype.ext h.hab
  hy := Subtype.ext h.hy
  hx := Subtype.ext h.hx
  hyx := Subtype.ext h.hyx
  hya := Subtype.ext h.hya
  hyb := Subtype.ext h.hyb
  hxa := Subtype.ext (by simpa using h.hxa)
  hxb := Subtype.ext (by simpa using h.hxb)
  gen := by
    apply Subgroup.map_injective S.subtype_injective
    rw [MonoidHom.map_closure]
    have : S.subtype '' ({⟨a, a_mem h⟩, ⟨b, b_mem h⟩, ⟨y, y_mem h⟩, ⟨x, x_mem h⟩} : Set ↥S) =
        {a, b, y, x} := by
      ext t
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, hu, rfl⟩
        rcases hu with rfl | rfl | rfl | rfl <;> simp
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨⟨t, a_mem h⟩, Or.inl rfl, rfl⟩
        · exact ⟨⟨t, b_mem h⟩, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨⟨t, y_mem h⟩, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
        · exact ⟨⟨t, x_mem h⟩, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
    rw [this, h.gen, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  card := by
    rw [Subgroup.card_top]
    exact h.card

end Transport

section Transport2

variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] {a b y x : Γ}

theorem m12Data_map (f : Γ →* Γ') (hf : Function.Injective f)
    (h : Sec13.M12Data (⊤ : Subgroup Γ) a b y x) :
    Sec13.M12Data f.range (f a) (f b) (f y) (f x) where
  ha := by rw [← map_pow, h.ha, map_one]
  hb := by rw [← map_pow, h.hb, map_one]
  hab := by rw [← map_mul, ← map_mul, h.hab]
  hy := by rw [← map_mul, h.hy, map_one]
  hx := by rw [← map_mul, h.hx, map_one]
  hyx := by rw [← map_mul, ← map_mul, h.hyx]
  hya := by simpa [map_mul, map_inv] using congrArg f h.hya
  hyb := by simpa [map_mul, map_inv] using congrArg f h.hyb
  hxa := by simpa [map_mul, map_inv] using congrArg f h.hxa
  hxb := by simpa [map_mul, map_inv] using congrArg f h.hxb
  gen := by
    rw [show ({f a, f b, f y, f x} : Set Γ') = f '' ({a, b, y, x} : Set Γ) by
      simp [Set.image_insert_eq], ← MonoidHom.map_closure, h.gen, ← MonoidHom.range_eq_map]
  card := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, ← Subgroup.card_top]
    exact h.card

end Transport2

section OddQuot

variable {Γ : Type*} [Group Γ]

theorem injective_of_two_group {P : Type*} [Group P] (N : Subgroup Γ) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N)) (hP : IsPGroup 2 P) (ι : P →* Γ)
    (hι : Function.Injective ι) : Function.Injective ((QuotientGroup.mk' N).comp ι) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker] at hs
  have hsN : ι s ∈ N := by
    have : QuotientGroup.mk' N (ι s) = 1 := hs
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨k, hk⟩ := hP s
  have h1 : orderOf (ι s) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hk, map_one]
  have h2 : orderOf (ι s) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hsN
  have h5 : Nat.Coprime (orderOf (ι s)) (Nat.card N) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k hN)
  have : orderOf (ι s) = 1 := Nat.Coprime.eq_one_of_dvd h5 h2
  have hs1 : ι s = 1 := orderOf_eq_one_iff.1 this
  exact (Subgroup.mem_bot.2 (hι (by rw [hs1, map_one])))

theorem involutions_conj_of_coset (N : Subgroup Γ) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N)) {u v : Γ} (hu : u * u = 1) (hv : v * v = 1)
    (huv : QuotientGroup.mk' N u = QuotientGroup.mk' N v) : ∃ n ∈ N, n * u * n⁻¹ = v := by
  classical
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.1 hN
  have hodd : Odd (Nat.card (QuotientGroup.mk' N).ker) := by
    rw [QuotientGroup.ker_mk']; exact hNodd
  have hone : ∀ w : Γ, w * w = 1 → w ∈ N → w = 1 := by
    intro w hw hwN
    have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw)
    have h3 : orderOf w ∣ Nat.card N := by
      have := Subgroup.orderOf_dvd_natCard N hwN
      simpa [Subgroup.orderOf_coe] using this
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exfalso
      rw [h] at h3
      exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h3)
  by_cases hu1 : u = 1
  · subst hu1
    have hvN : v ∈ N := by
      have : QuotientGroup.mk' N v = 1 := by rw [← huv, map_one]
      exact (QuotientGroup.eq_one_iff v).1 this
    have : v = 1 := hone v hv hvN
    exact ⟨1, one_mem _, by simp [this]⟩
  · have hv1 : v ≠ 1 := by
      intro hv1
      apply hu1
      have huN : u ∈ N := by
        have : QuotientGroup.mk' N u = 1 := by rw [huv, hv1, map_one]
        exact (QuotientGroup.eq_one_iff u).1 this
      exact hone u hu huN
    have hui : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution u := ⟨hu1, by rw [pow_two]; exact hu⟩
    have hvi : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution v := ⟨hv1, by rw [pow_two]; exact hv⟩
    obtain ⟨n, hn, hconj⟩ := CFSG.ProperTwoGeneratedCore.involutions_kernel_conjugate
      (QuotientGroup.mk' N) hodd hui hvi huv
    rw [QuotientGroup.ker_mk'] at hn
    refine ⟨n⁻¹, N.inv_mem hn, ?_⟩
    simpa [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem] using hconj

end OddQuot

section Main

theorem isSylow2In_map_of_surjective {Γ Γ' : Type*} [Group Γ] [Group Γ'] (f : Γ →* Γ')
    (hf : Function.Surjective f) {S : Subgroup Γ} (hS : IsSylow2In S ⊤) :
    IsSylow2In (S.map f) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact hS.2.1.of_surjective (f.subgroupMap S) (MonoidHom.subgroupMap_surjective f S)
  · rw [Subgroup.relIndex_top_right]
    have h1 : ¬ 2 ∣ S.index := by
      have := hS.2.2
      rwa [Subgroup.relIndex_top_right] at this
    intro hd
    exact h1 (hd.trans (Subgroup.index_map_dvd S hf))

end Main


section Bar

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {a b y x : G}

theorem lemma14_3_bar (h91 : IVK_9_1) (h : Sec13.M12Data S a b y x)
    (hKC : IsKGroupNative ↥(Cz a b)) (hS : Sec13.Sylow2In S ⊤)
    (hF1 : ∀ c ∈ S, c * c = a ^ 2 * b ^ 2 →
      ∃ g ∈ Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set G), g * c * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G) ∧
        (g * c * g⁻¹) * (g * c * g⁻¹) = a ^ 2 * b ^ 2)
    (hF2 : ∀ g ∈ Cz a b, g * x * g⁻¹ ∉ Subgroup.closure ({a * a, b * b} : Set G)) :
    ∃ (S' : Subgroup (CentralizerBar (a ^ 2 * b ^ 2))) (a' b' y' x' : CentralizerBar (a ^ 2 * b ^ 2)),
      Sec13.M12Data S' a' b' y' x' ∧ Sec13.Sylow2In S' ⊤ ∧ a' ^ 2 * b' ^ 2 = zBar (a ^ 2 * b ^ 2) ∧
      S' = (S.subgroupOf (Cz a b)).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cz a b))) ∧
      (∀ c : ↥(Cz a b), (c : G) = a → QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cz a b)) c = a') ∧
      (∀ c : ↥(Cz a b), (c : G) = b → QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cz a b)) c = b') ∧
      (∀ c : ↥(Cz a b), (c : G) = y → QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cz a b)) c = y') ∧
      (∀ c : ↥(Cz a b), (c : G) = x → QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cz a b)) c = x') ∧
      Lemma14_3Conc (CentralizerBar (a ^ 2 * b ^ 2)) (a' ^ 2 * b' ^ 2) (Rsub S' a' b')
        (R1sub a' b' y') := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥(Cz a b) := CFSG.pPrimeCore 2 ↥(Cz a b) with hN
  let π : ↥(Cz a b) →* CentralizerBar (a ^ 2 * b ^ 2) := QuotientGroup.mk' N
  let ι : ↥S →* ↥(Cz a b) := Subgroup.inclusion (S_le_Cz h)
  let f : ↥S →* CentralizerBar (a ^ 2 * b ^ 2) := π.comp ι
  have hNcop : Nat.Coprime 2 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have hSyl := sylow2In_centralizer_z h hS
  have hSp2 : IsPGroup 2 ↥S := hSyl.2.1
  have hfinj : Function.Injective f :=
    injective_of_two_group N hNcop hSp2 ι (Subgroup.inclusion_injective _)
  have h' := m12Data_map f hfinj (m12Data_top h)
  have hzS : (⟨a, a_mem h⟩ : ↥S) ^ 2 * (⟨b, b_mem h⟩ : ↥S) ^ 2 = ⟨a ^ 2 * b ^ 2, z_mem h⟩ :=
    Subtype.ext (by simp)
  have hz' : f ⟨a, a_mem h⟩ ^ 2 * f ⟨b, b_mem h⟩ ^ 2 = zBar (a ^ 2 * b ^ 2) := by
    rw [← map_pow, ← map_pow, ← map_mul, hzS]
    rfl
  have hcenter : ∀ g : CentralizerBar (a ^ 2 * b ^ 2),
      g * zBar (a ^ 2 * b ^ 2) = zBar (a ^ 2 * b ^ 2) * g := by
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    show QuotientGroup.mk (g * zElt (a ^ 2 * b ^ 2)) = QuotientGroup.mk (zElt (a ^ 2 * b ^ 2) * g)
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 g.2 (a ^ 2 * b ^ 2) (Set.mem_singleton _)).symm
  have hcen : Subgroup.centralizer ({f ⟨a, a_mem h⟩ ^ 2 * f ⟨b, b_mem h⟩ ^ 2} :
      Set (CentralizerBar (a ^ 2 * b ^ 2))) = ⊤ := by
    rw [hz']
    apply eq_top_iff.2
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact (hcenter g).symm
  have hrange : f.range = (S.subgroupOf (Cz a b)).map π := by
    ext c
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨ι s, (show (ι s : G) ∈ S from s.2), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨(c : G), hc⟩, rfl⟩
  have hSyl' : IsSylow2In f.range ⊤ := by
    rw [hrange]
    exact isSylow2In_map_of_surjective π (QuotientGroup.mk'_surjective N) (rcfg h hS).sylow
  have hKbar : IsKGroupNative (CentralizerBar (a ^ 2 * b ^ 2)) :=
    SectionRank.IsKGroupCat.quotient hKC N
  let e : ↥(Cz (f ⟨a, a_mem h⟩) (f ⟨b, b_mem h⟩)) ≃* CentralizerBar (a ^ 2 * b ^ 2) :=
    (MulEquiv.subgroupCongr hcen).trans Subgroup.topEquiv
  have hKC' : IsKGroupNative ↥(Cz (f ⟨a, a_mem h⟩) (f ⟨b, b_mem h⟩)) :=
    SectionRank.IsKGroupCat.of_mulEquiv hKbar e
  have hO' : CFSG.oddCore ↥(Cz (f ⟨a, a_mem h⟩) (f ⟨b, b_mem h⟩)) = ⊥ := by
    rw [oddCore_eq_pPrimeCore_two']
    have h1 := CFSG.pPrimeCore_map_iso 2 e
    rw [pPrimeCore_quotient_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  have f_nu : ∀ p : NF, f ⟨nu a b y x p, nu_mem h p⟩ =
      nu (f ⟨a, a_mem h⟩) (f ⟨b, b_mem h⟩) (f ⟨y, y_mem h⟩) (f ⟨x, x_mem h⟩) p := by
    intro p
    have : (⟨nu a b y x p, nu_mem h p⟩ : ↥S) = ⟨a, a_mem h⟩ ^ p.1.val * ⟨b, b_mem h⟩ ^ p.2.1.val *
        (⟨y, y_mem h⟩ ^ p.2.2.1.val * ⟨x, x_mem h⟩ ^ p.2.2.2.val) := Subtype.ext (by simp [nu])
    rw [this]
    simp only [map_mul, map_pow]
    rfl
  have hF1' : ∀ c ∈ f.range, c * c = f ⟨a, a_mem h⟩ ^ 2 * f ⟨b, b_mem h⟩ ^ 2 →
      ∃ g ∈ Subgroup.centralizer ({f ⟨a, a_mem h⟩ ^ 2 * f ⟨b, b_mem h⟩ ^ 2} :
          Set (CentralizerBar (a ^ 2 * b ^ 2))),
        g * c * g⁻¹ ∈ Subgroup.closure ({f ⟨a, a_mem h⟩, f ⟨b, b_mem h⟩} :
            Set (CentralizerBar (a ^ 2 * b ^ 2))) ∧
          (g * c * g⁻¹) * (g * c * g⁻¹) = f ⟨a, a_mem h⟩ ^ 2 * f ⟨b, b_mem h⟩ ^ 2 := by
    rintro _ ⟨s, rfl⟩ hsq
    have hss : s * s = ⟨a ^ 2 * b ^ 2, z_mem h⟩ := by
      apply hfinj
      rw [map_mul, hsq, hz']
      rfl
    have hss' : (s : G) * (s : G) = a ^ 2 * b ^ 2 := congrArg Subtype.val hss
    obtain ⟨g, hg, hgc, hgsq⟩ := hF1 (s : G) s.2 hss'
    rw [H0_eq h] at hgc
    obtain ⟨p, hp, hpe⟩ := hgc
    have e1 : π ⟨g, hg⟩ * f s * (π ⟨g, hg⟩)⁻¹ = f ⟨nu a b y x p, nu_mem h p⟩ := by
      show π ⟨g, hg⟩ * π (ι s) * (π ⟨g, hg⟩)⁻¹ = π (ι ⟨nu a b y x p, nu_mem h p⟩)
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simpa [ι] using hpe
    refine ⟨π ⟨g, hg⟩, by rw [hcen]; trivial, ?_, ?_⟩
    · rw [e1, f_nu p, H0_eq h']
      exact ⟨p, hp, rfl⟩
    · rw [e1, ← map_mul]
      have : (⟨nu a b y x p, nu_mem h p⟩ * ⟨nu a b y x p, nu_mem h p⟩ : ↥S) =
          ⟨a ^ 2 * b ^ 2, z_mem h⟩ := Subtype.ext (by simpa [hpe] using hgsq)
      rw [this, ← hzS, map_mul, map_pow, map_pow]
  have hF2' : ∀ g' ∈ Subgroup.centralizer ({f ⟨a, a_mem h⟩ ^ 2 * f ⟨b, b_mem h⟩ ^ 2} :
      Set (CentralizerBar (a ^ 2 * b ^ 2))),
      g' * f ⟨x, x_mem h⟩ * g'⁻¹ ∉ Subgroup.closure ({f ⟨a, a_mem h⟩ * f ⟨a, a_mem h⟩,
        f ⟨b, b_mem h⟩ * f ⟨b, b_mem h⟩} : Set (CentralizerBar (a ^ 2 * b ^ 2))) := by
    intro g' _ hmem
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g'
    rw [U_eq h'] at hmem
    obtain ⟨q, hq, hqe⟩ := hmem
    have huu : ι ⟨nu a b y x q, nu_mem h q⟩ * ι ⟨nu a b y x q, nu_mem h q⟩ = 1 := by
      apply Subtype.ext
      show nu a b y x q * nu a b y x q = 1
      rw [nu_mul h, pU_sq_one q hq, nu_zero]
    have hvv : g * ι ⟨x, x_mem h⟩ * g⁻¹ * (g * ι ⟨x, x_mem h⟩ * g⁻¹) = 1 := by
      have hxx : ι ⟨x, x_mem h⟩ * ι ⟨x, x_mem h⟩ = 1 := Subtype.ext h.hx
      calc g * ι ⟨x, x_mem h⟩ * g⁻¹ * (g * ι ⟨x, x_mem h⟩ * g⁻¹)
          = g * (ι ⟨x, x_mem h⟩ * ι ⟨x, x_mem h⟩) * g⁻¹ := by group
        _ = 1 := by rw [hxx]; group
    have hπ : QuotientGroup.mk' N (ι ⟨nu a b y x q, nu_mem h q⟩) =
        QuotientGroup.mk' N (g * ι ⟨x, x_mem h⟩ * g⁻¹) := by
      have e2 : QuotientGroup.mk' N (g * ι ⟨x, x_mem h⟩ * g⁻¹) =
          π g * f ⟨x, x_mem h⟩ * (π g)⁻¹ := by
        simp [π, f, ι, map_mul, map_inv]
      rw [e2, hqe]
      exact f_nu q
    obtain ⟨n, hn, hnuv⟩ := involutions_conj_of_coset N hNcop huu hvv hπ
    refine hF2 ((n⁻¹ * g : ↥(Cz a b)) : G) (n⁻¹ * g).2 ?_
    rw [U_eq h]
    refine ⟨q, hq, ?_⟩
    have e3 : (n⁻¹ * g) * ι ⟨x, x_mem h⟩ * (n⁻¹ * g)⁻¹ = ι ⟨nu a b y x q, nu_mem h q⟩ := by
      have : n⁻¹ * (g * ι ⟨x, x_mem h⟩ * g⁻¹) * n = ι ⟨nu a b y x q, nu_mem h q⟩ := by
        rw [← hnuv]; group
      calc (n⁻¹ * g) * ι ⟨x, x_mem h⟩ * (n⁻¹ * g)⁻¹
          = n⁻¹ * (g * ι ⟨x, x_mem h⟩ * g⁻¹) * n := by group
        _ = _ := this
    have := congrArg Subtype.val e3
    simpa [ι] using this
  have hpt : ∀ (t : G) (ht : t ∈ S) (c : ↥(Cz a b)), (c : G) = t → π c = f ⟨t, ht⟩ := by
    intro t ht c hc
    have : c = ι ⟨t, ht⟩ := Subtype.ext hc
    rw [this]; rfl
  refine ⟨f.range, f ⟨a, a_mem h⟩, f ⟨b, b_mem h⟩, f ⟨y, y_mem h⟩, f ⟨x, x_mem h⟩, h', hSyl', hz',
    hrange, hpt a (a_mem h), hpt b (b_mem h), hpt y (y_mem h), hpt x (x_mem h), ?_⟩
  have hnorm := normal_of_m12 h' h91 hKC' hSyl' hO' hF1' hF2'
  have hR : Rsub f.range (f ⟨a, a_mem h⟩) (f ⟨b, b_mem h⟩) =
      nfSub h' pR closed_pR := R_eq h'
  exact iv3_14_3b _ f.range _ _ _ _ h' (by rw [hcen]; exact hSyl') hO' hF1' hF2'
    (by rw [hR]; exact hnorm)

end Bar

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn
