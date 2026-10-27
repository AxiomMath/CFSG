module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenNormalizer
import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {H : Type} [Group H] [Finite H]

theorem false_of_threeTenHyp_of_thirteen {I D P Y : Subgroup H} {d : ℕ}
    (hhyp : ThreeTenHyp I D P Y 3 d)
    (hext : IsExtNotation (fun A _ => Nat.card A = 3) (fun B _ => Nat.card B = 13) ↥I) :
    False := by
  have hDNY := normalizer_D_inter_le_Y hhyp
  obtain ⟨hp, -, hd, hd2, hdp, hIdef, hD, -, hP, hYlt, -, hNP⟩ := hhyp
  have : Fact d.Prime := ⟨hd⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨N, hNn, hN13, hQ3, -⟩ := hext
  have hI39 : Nat.card I = 39 := by
    rw [← N.card_mul_index, hN13, Subgroup.index_eq_card, hQ3]
  have hInorm : I.Normal := normal_of_oPPrimeHull_eq hIdef
  set N₀ : Subgroup H := N.map I.subtype with hN₀def
  have hN₀I : N₀ ≤ I := Subgroup.map_subtype_le N
  have hN₀13 : Nat.card N₀ = 13 := by
    rw [hN₀def, Subgroup.card_map_of_injective I.subtype_injective, hN13]
  have hconj : ∀ h : H, ∀ n ∈ N₀, h * n * h⁻¹ ∈ N₀ := by
    intro h n hn
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
    let m : ↥I := ⟨h * (x : H) * h⁻¹, hInorm.conj_mem _ x.2 h⟩
    have hx13 : x ^ 13 = 1 := by
      have := pow_card_eq_one' (G := ↥N) (x := ⟨x, hx⟩)
      rw [hN13] at this
      exact congrArg Subtype.val this
    have hm13 : m ^ 13 = 1 := by
      apply Subtype.ext
      simp only [m, SubgroupClass.coe_pow, conj_pow, OneMemClass.coe_one]
      rw [show (x : H) ^ 13 = ((x ^ 13 : ↥I) : H) from rfl, hx13]
      simp
    have hmN : m ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N) m]
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes (a := 13) (b := 3) (by norm_num)
      · exact orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hm13, QuotientGroup.mk_one])
      · exact hQ3 ▸ orderOf_dvd_natCard _
    exact Subgroup.mem_map.mpr ⟨m, hmN, rfl⟩
  have hDN : D ≤ Subgroup.normalizer (N₀ : Set H) := by
    intro y _
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hconj y n
    · intro hn
      have := hconj y⁻¹ _ hn
      simpa [mul_assoc] using this
  have hDY : D ≤ Y := fun x hx =>
    hDNY ⟨Subgroup.le_normalizer hx, (le_sup_right : D ≤ I ⊔ D) hx⟩
  have hPI : P ≤ I := by
    rw [hIdef]
    exact p_sylow_le_oPPrimeHull hp hP
  have hPY : P ≤ Y := fun x hx => hNP ⟨Subgroup.le_normalizer hx, hPI hx⟩
  have hN₀Y : N₀ ≤ Y := by
    by_cases hd13 : d = 13
    · subst hd13
      have hN₀p : IsPGroup 13 N₀ := IsPGroup.of_card (n := 1) (by rw [hN₀13, pow_one])
      have hsup : IsPGroup 13 ↥(D ⊔ N₀) := hD.isPGroup.to_sup_of_normal_right' hN₀p hDN
      have heq : D ⊔ N₀ = D := hD.eq_of_le le_sup_left le_top hsup
      exact (le_sup_right.trans heq.le).trans hDY
    · have hcop : ∀ y ∈ D, Nat.Coprime (orderOf y) (13 - 1) := by
        intro y hy
        obtain ⟨k, hk⟩ := hD.isPGroup ⟨y, hy⟩
        have hdvd : orderOf y ∣ d ^ k := by
          apply orderOf_dvd_of_pow_eq_one
          exact congrArg Subtype.val hk
        have hd12 : Nat.Coprime d 12 := by
          rw [Nat.Prime.coprime_iff_not_dvd hd]
          intro h
          rcases (Nat.Prime.dvd_mul hd).mp (by simpa using h : d ∣ 2 ^ 2 * 3) with h4 | h3
          · exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h4))
          · exact hdp ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp h3)
        exact Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left k hd12)
      intro n hn
      have hnD : n ∈ Subgroup.normalizer (D : Set H) := by
        have hc : n ∈ Subgroup.centralizer (D : Set H) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (CFSG.Quasithin.EmptyFaithfulMultiple.L3213.commute_of_normalizes_of_coprime
            hN₀13 (hcop y hy) (hDN hy) n hn)
        exact Subgroup.centralizer_le_normalizer _ hc
      exact hDNY ⟨hnD, (le_sup_left : I ≤ I ⊔ D) (hN₀I hn)⟩
  have h3P : 3 ∣ Nat.card P := by
    rw [hP.card_eq]
    have h39 : 39 ∣ Nat.card (⊤ : Subgroup H) := hI39 ▸ Subgroup.card_dvd_of_le le_top
    have h3 : 3 ∣ Nat.card (⊤ : Subgroup H) := (by norm_num : 3 ∣ 39).trans h39
    exact dvd_pow_self 3 (Nat.Prime.factorization_pos_of_dvd Nat.prime_three
      Nat.card_pos.ne' h3).ne'
  have hle : N₀ ⊔ P ≤ I := sup_le hN₀I hPI
  have hcard : 39 ∣ Nat.card ↥(N₀ ⊔ P) := by
    have h13 : 13 ∣ Nat.card ↥(N₀ ⊔ P) := hN₀13 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h3 : 3 ∣ Nat.card ↥(N₀ ⊔ P) := h3P.trans (Subgroup.card_dvd_of_le le_sup_right)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h3
  have hIeq : N₀ ⊔ P = I := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hI39]
    exact Nat.le_of_dvd Nat.card_pos hcard
  have hall : I ⊔ D ≤ Y := sup_le (hIeq ▸ sup_le hN₀Y hPY) hDY
  exact lt_irrefl _ (lt_of_le_of_lt hall hYlt)

end CFSG.LocalAnalysis.AGL81I.Section3

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

@[expose] def ThreeTenCase5Sp4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (d : ℕ), ThreeTenHyp I D P Y 3 d →
    D ≤ I →
    (∃ (W : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3)))
        (N : Subgroup (↥W ⧸ CFSG.pCore 3 ↥W)) (_ : N.Normal), oPPrimeHull 3 W = W ∧
        Nonempty (↥I ≃* (↥W ⧸ CFSG.pCore 3 ↥W) ⧸ N)) →
    False

theorem threeTenCase5Sp4_of_generation
    (hgen : ∀ (W : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3))), oPPrimeHull 3 W = W →
      ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → q ≠ 3 → ∀ (D₁ : Sylow q ↥W) (P₁ : Sylow 3 ↥W),
        (D₁ : Subgroup ↥W) ≠ ⊥ →
        Subgroup.normalizer ((D₁ : Subgroup ↥W) : Set ↥W) ⊔
          Subgroup.normalizer ((P₁ : Subgroup ↥W) : Set ↥W) = ⊤) :
    ThreeTenCase5Sp4 := by
  intro H _ _ I D P Y d hhyp hDI ⟨W, N, hNn, hW, ⟨e⟩⟩
  have hDNY := normalizer_D_inter_le_Y hhyp
  obtain ⟨hp, -, hd, hd2, hdp, hIdef, hD, hDne, hP, hYlt, -, hNP⟩ := hhyp
  have : Fact d.Prime := ⟨hd⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : ↥W →* ↥I :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' N).comp (QuotientGroup.mk' (CFSG.pCore 3 ↥W)))
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective N).comp (QuotientGroup.mk'_surjective _))
  have hPI : P ≤ I := by
    rw [hIdef]
    exact p_sylow_le_oPPrimeHull hp hP
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf d D I := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hDI, hD.isPGroup, fun hdvd => ?_⟩
    apply (CFSG.ABGLocalTools.isSylowOf_iff.mp hD).2.2
    rw [← Subgroup.relIndex_mul_relIndex (H := D) (K := I) (L := ⊤) hDI le_top]
    exact dvd_mul_of_dvd_left hdvd _
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P I := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hPI, hP.isPGroup, fun hdvd => ?_⟩
    apply (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.2
    rw [← Subgroup.relIndex_mul_relIndex (H := P) (K := I) (L := ⊤) hPI le_top]
    exact dvd_mul_of_dvd_left hdvd _
  obtain ⟨SD, hSD⟩ := hDsyl.exists_sylow_eq_subgroupOf
  obtain ⟨SP, hSP⟩ := hPsyl.exists_sylow_eq_subgroupOf
  obtain ⟨D₁, hD₁⟩ := Sylow.mapSurjective_surjective hπ d SD
  obtain ⟨P₁, hP₁⟩ := Sylow.mapSurjective_surjective hπ 3 SP
  have hD₁map : (D₁ : Subgroup ↥W).map π = D.subgroupOf I := by
    rw [← hSD, ← hD₁, Sylow.coe_mapSurjective]
  have hP₁map : (P₁ : Subgroup ↥W).map π = P.subgroupOf I := by
    rw [← hSP, ← hP₁, Sylow.coe_mapSurjective]
  have hD₁ne : (D₁ : Subgroup ↥W) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.map_bot] at hD₁map
    apply hDne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hDI hx⟩ : ↥I) ∈ D.subgroupOf I := hx
    rw [← hD₁map, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hgW := hgen W hW d hd2 hdp D₁ P₁ hD₁ne
  have htop : (⊤ : Subgroup ↥I) ≤ Subgroup.normalizer ((D.subgroupOf I : Subgroup ↥I) : Set ↥I) ⊔
      Subgroup.normalizer ((P.subgroupOf I : Subgroup ↥I) : Set ↥I) := by
    rw [← Subgroup.map_top_of_surjective π hπ, ← hgW, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rw [← hD₁map]
      exact Subgroup.le_normalizer_map π
    · rw [← hP₁map]
      exact Subgroup.le_normalizer_map π
  have hle : Subgroup.normalizer ((D.subgroupOf I : Subgroup ↥I) : Set ↥I) ⊔
      Subgroup.normalizer ((P.subgroupOf I : Subgroup ↥I) : Set ↥I) ≤ Y.subgroupOf I := by
    refine sup_le ?_ ?_
    · intro y hy
      rw [← Subgroup.subgroupOf_normalizer_eq hDI, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      exact hDNY ⟨hy, (le_sup_left : I ≤ I ⊔ D) y.2⟩
    · intro y hy
      rw [← Subgroup.subgroupOf_normalizer_eq hPI, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      exact hNP ⟨hy, y.2⟩
  have hIY : I ≤ Y := fun x hx => by
    have := (htop.trans hle) (Subgroup.mem_top (⟨x, hx⟩ : ↥I))
    rwa [Subgroup.mem_subgroupOf] at this
  rw [sup_eq_left.mpr hDI] at hYlt
  exact lt_irrefl _ (lt_of_le_of_lt hIY hYlt)

theorem threeTenCase5Thirteen_holds :
    ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (d : ℕ), ThreeTenHyp I D P Y 3 d →
      IsExtNotation (fun A _ => Nat.card A = 3) (fun B _ => Nat.card B = 13) ↥I → False :=
  fun _ _ _ _ _ _ _ _ hhyp hext => false_of_threeTenHyp_of_thirteen hhyp hext

end CFSG.LocalAnalysis.AGL81I.Section3
