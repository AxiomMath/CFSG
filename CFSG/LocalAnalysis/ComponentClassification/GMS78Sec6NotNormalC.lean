module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormal
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6MainC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormalBender
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormalLocal

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G}

theorem exists_conj_centralized_by_delta
    (h3 : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    ∃ Y Q : Subgroup G, Y ≤ centralizer (K : Set G) ∧ gmsA L T ≤ Y ∧
      Q ≤ centralizer (Y : Set G) ∧ Q ≤ gmsV L T ∧ ¬ Q ≤ T ⊓ centralizer (L : Set G) ∧
      IsSimpleGroup (rankTwoQuot Y) ∧ center (rankTwoQuot Y) = ⊥ ∧
      Even (Nat.card (rankTwoQuot Y)) ∧ Odd (Nat.card (center Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h313 := h3.lemma313_of_psu3 hF hf e
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h3.hyp.standard.1.1 hf e
  obtain ⟨-, -, hAX', -, hZX, hZX', ⟨eX⟩, ⟨eX'⟩⟩ := u3K_facts h3 hf e hKL hKo hKH
  have hP := h3.isSylowOf_T₁
  obtain ⟨-, hA₁card, -⟩ := sylow_of_psu3 hZ hf e hP
  set T₁ := T ⊓ L with hT₁def
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  set A₁ := gmsA L T with hA₁def
  set X₀ := u3X₀ L K with hX₀def
  have hT₁2 : IsPGroup 2 T₁ := hP.isPGroup
  have hKH' : T₁ ⊔ K = L ⊓ normalizer (T₁ : Set G) ⊓ centralizer (A₁ : Set G) := hKH
  have hKN : K ≤ normalizer (T₁ : Set G) := fun k hk =>
    (mem_inf.mp (mem_inf.mp ((hKH' ▸ (le_sup_right : K ≤ T₁ ⊔ K)) hk)).1).2
  have hKA : K ≤ centralizer (A₁ : Set G) := fun k hk =>
    (mem_inf.mp ((hKH' ▸ (le_sup_right : K ≤ T₁ ⊔ K)) hk)).2
  have hT₀L : T₀ ≤ centralizer (L : Set G) := inf_le_right
  have hKV : K ≤ centralizer (gmsV L T : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ((Subgroup.le_centralizer_iff).mp hKA) ?_
    exact hT₀L.trans (Subgroup.centralizer_le hKL)
  have hT₀Δ : T₀ ∈ gmsDelta L T := ⟨⟨1, rightConjugate_one _⟩, le_sup_right⟩
  have hΔ : 1 < Nat.card (gmsDelta L T) := by
    rw [h313.card_eq]
    exact Nat.one_lt_two_pow (by omega)
  obtain ⟨Q, hQΔ, hQne⟩ : ∃ Q ∈ gmsDelta L T, Q ≠ T₀ := by
    have : Nontrivial (gmsDelta L T) := Finite.one_lt_card_iff_nontrivial.mp hΔ
    obtain ⟨⟨Q, hQ⟩, hne⟩ := exists_ne (⟨T₀, hT₀Δ⟩ : gmsDelta L T)
    exact ⟨Q, hQ, fun h => hne (Subtype.ext h)⟩
  obtain ⟨n, hnV, hnQ, -⟩ := h313.twoTransitive T₀ hT₀Δ Q hQΔ Q hQΔ T₀ hT₀Δ hQne.symm hQne
  have hA₁n : rightConjugate A₁ n = A₁ := Sec3.rightConjugate_gmsA_eq h313 hnV
  have hT₁n : rightConjugate T₁ n = T₁ := h3.rightConjugate_T₁_eq hF hf e hKL hKo hKH hnV
  set L' := rightConjugate L n with hL'def
  set Kn := rightConjugate K n with hKndef
  have hT₁L' : T₁ ≤ L' := by
    intro x hx
    have hx' : x ∈ rightConjugate T₁ n := by rw [hT₁n]; exact hx
    exact (mem_rightConjugate_iff L n x).mpr ((mem_rightConjugate_iff T₁ n x).mp hx').2
  have hKnL' : Kn ≤ L' := fun x hx =>
    (mem_rightConjugate_iff L n x).mpr (hKL ((mem_rightConjugate_iff K n x).mp hx))
  have hQL' : Q ≤ centralizer (L' : Set G) := by
    intro x hx
    rw [← hnQ] at hx
    rw [mem_centralizer_rightConjugate_iff]
    exact hT₀L ((mem_rightConjugate_iff T₀ n x).mp hx)
  have hKNL' : K ≤ normalizer (L' : Set G) :=
    hKV.trans (h3.centralizer_gmsV_le_normalizer_conj hF hnV)
  have hKnN : Kn ≤ normalizer (T₁ : Set G) := by
    intro x hx
    rw [← hT₁n, mem_normalizer_rightConjugate_iff]
    exact hKN ((mem_rightConjugate_iff K n x).mp hx)
  have hT₁L'syl : IsSylowOf 2 T₁ L' := by
    refine isSylowOf_of_card hT₁L' ?_
    rw [hL'def, rightConjugate_card, ← hP.card_eq]
  set N₁ := rightConjugate (T₁ ⊔ K) n with hN₁def
  have hN₁ : N₁ = T₁ ⊔ Kn := by
    have h1 := Subgroup.map_sup T₁ K (MulAut.conj n⁻¹).toMonoidHom
    change N₁ = rightConjugate T₁ n ⊔ rightConjugate K n at h1
    rw [h1, hT₁n]
  have hN₁L : ∀ x ∈ N₁, n * x * n⁻¹ ∈ T₁ ⊔ K := fun x hx =>
    (mem_rightConjugate_iff (T₁ ⊔ K) n x).mp hx
  have hN₁N : N₁ ≤ normalizer (T₁ : Set G) := by
    intro x hx
    rw [← hT₁n, mem_normalizer_rightConjugate_iff]
    exact (mem_inf.mp (mem_inf.mp (hKH' ▸ hN₁L x hx)).1).2
  have hKN₁ : K ≤ normalizer (N₁ : Set G) := by
    intro k hk
    rw [hN₁def, mem_normalizer_rightConjugate_iff, hKH']
    have hk1 : n * k * n⁻¹ ∈ normalizer (L : Set G) :=
      (mem_normalizer_rightConjugate_iff L n k).mp (hKNL' hk)
    have hk2 : n * k * n⁻¹ ∈ normalizer (T₁ : Set G) := by
      rw [← mem_normalizer_rightConjugate_iff, hT₁n]
      exact hKN hk
    have hk3 : n * k * n⁻¹ ∈ centralizer (A₁ : Set G) := by
      rw [← mem_centralizer_rightConjugate_iff, hA₁n]
      exact hKA hk
    exact mem_normalizer_inf (mem_normalizer_inf hk1 (le_normalizer hk2))
      (le_normalizer hk3)
  have hT₁N₁ : T₁ ≤ N₁ := hN₁ ▸ le_sup_left
  have hN₁L' : N₁ ≤ L' := hN₁ ▸ sup_le hT₁L' hKnL'
  have hT₁N₁syl : IsSylowOf 2 T₁ N₁ := hT₁L'syl.of_le hT₁N₁ hN₁L'
  have hKno : Odd (Nat.card Kn) := by rw [hKndef, rightConjugate_card]; exact hKo
  have hconj : ∀ k ∈ K, ∃ t ∈ T₁, Kn.map (MulAut.conj k).toMonoidHom =
      Kn.map (MulAut.conj t).toMonoidHom := by
    intro k hk
    have hkT₁ : T₁.map (MulAut.conj k).toMonoidHom = T₁ :=
      (mem_normalizer_iff_map_conj_eq.mp (hKN hk))
    have hkN₁ : N₁.map (MulAut.conj k).toMonoidHom = N₁ :=
      (mem_normalizer_iff_map_conj_eq.mp (hKN₁ hk))
    have hsup : T₁ ⊔ Kn.map (MulAut.conj k).toMonoidHom = N₁ := by
      rw [← hkT₁, ← Subgroup.map_sup, ← hN₁, hkN₁]
    have hodd : Odd (Nat.card (Kn.map (MulAut.conj k).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom)
        (MulAut.conj k).injective]
      exact hKno
    exact exists_conj_eq_of_sup_eq hT₁N₁syl hN₁N hsup hN₁.symm hodd hKno
  set D := (T₁ ⊔ K) ⊓ normalizer (Kn : Set G) with hDdef
  have hDsup : T₁ ⊔ D = T₁ ⊔ K := by
    refine le_antisymm (sup_le le_sup_left inf_le_left) (sup_le le_sup_left ?_)
    intro k hk
    obtain ⟨t, htT₁, ht⟩ := hconj k hk
    have hd : t⁻¹ * k ∈ D := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (mem_sup_left htT₁)) (mem_sup_right hk), ?_⟩
      rw [mem_normalizer_iff]
      intro y
      have h1 := SetLike.ext_iff.mp ht (k * y * k⁻¹)
      rw [mem_map_conj_iff, mem_map_conj_iff] at h1
      have e1 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      have e2 : t⁻¹ * (k * y * k⁻¹) * t = t⁻¹ * k * y * (t⁻¹ * k)⁻¹ := by group
      rw [e1, e2] at h1
      exact h1
    have hk' : k = t * (t⁻¹ * k) := by group
    rw [hk']
    exact mul_mem (mem_sup_left htT₁) (mem_sup_right hd)
  have hHN : T₁ ⊔ K ≤ normalizer (T₁ : Set G) := sup_le le_normalizer hKN
  have hT₁H : IsSylowOf 2 T₁ (T₁ ⊔ K) := hP.of_le le_sup_left (sup_le inf_le_right hKL)
  have hDN : D ≤ normalizer (T₁ : Set G) := inf_le_left.trans hHN
  have hDsyl : IsSylowOf 2 (T₁ ⊓ D) D :=
    isSylowOf_inf_of_sup_eq hT₁H hDN (by rw [sup_comm]; exact hDsup)
  have hDN' : D ≤ normalizer ((T₁ ⊓ D : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_inf (hDN hd) (le_normalizer hd)
  obtain ⟨D₀, hD₀D, hD₀o, hD₀sup⟩ := exists_odd_sup_eq hDsyl hDN'
  have hD₀H : T₁ ⊔ D₀ = T₁ ⊔ K := by
    refine le_antisymm (sup_le le_sup_left (hD₀D.trans inf_le_left)) ?_
    rw [← hDsup]
    refine sup_le le_sup_left ?_
    rw [← hD₀sup]
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  obtain ⟨g, hgT₁, hKg⟩ := exists_conj_eq_of_sup_eq hT₁H hHN rfl hD₀H hKo hD₀o
  set Kg := Kn.map (MulAut.conj g).toMonoidHom with hKgdef
  have hKKg : K ≤ normalizer (Kg : Set G) := by
    intro k hk
    rw [hKg] at hk
    obtain ⟨d, hd, rfl⟩ := hk
    have hdN : d ∈ normalizer (Kn : Set G) := (mem_inf.mp (hD₀D hd)).2
    rw [mem_normalizer_iff]
    intro y
    rw [hKgdef, mem_map_conj_iff, mem_map_conj_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e1 : g⁻¹ * (g * d * g⁻¹ * y * (g * d * g⁻¹)⁻¹) * g = d * (g⁻¹ * y * g) * d⁻¹ := by
      group
    rw [e1]
    exact mem_normalizer_iff.mp hdN _
  have hgL' : g ∈ normalizer (L' : Set G) := le_normalizer (hT₁L' hgT₁)
  set c := g * n⁻¹ with hcdef
  have hconjc : ∀ H : Subgroup G, H.map (MulAut.conj c).toMonoidHom =
      (rightConjugate H n).map (MulAut.conj g).toMonoidHom := by
    intro H
    show H.map _ = (H.map (MulAut.conj n⁻¹).toMonoidHom).map _
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [hcdef, MulAut.conj_apply, mul_assoc]
  have hLc : L.map (MulAut.conj c).toMonoidHom = L' := by
    rw [hconjc]
    exact mem_normalizer_iff_map_conj_eq.mp hgL'
  have hKc : K.map (MulAut.conj c).toMonoidHom = Kg := hconjc K
  set X := u3X₀ L' Kg with hXdef
  have hXc : X₀.map (MulAut.conj c).toMonoidHom = X := by
    rw [hX₀def, u3X₀_map_conj, hLc, hKc]
  have hKX : K ≤ normalizer (X : Set G) := by
    intro k hk
    have h1 : L'.map (MulAut.conj k).toMonoidHom = L' :=
      mem_normalizer_iff_map_conj_eq.mp (hKNL' hk)
    have h2 : Kg.map (MulAut.conj k).toMonoidHom = Kg :=
      mem_normalizer_iff_map_conj_eq.mp (hKKg hk)
    refine mem_normalizer_iff_map_conj_eq.mpr ?_
    show (u3X₀ L' Kg).map (MulAut.conj k).toMonoidHom = u3X₀ L' Kg
    rw [u3X₀_map_conj, h1, h2]
  have hgA : g ∈ centralizer (A₁ : Set G) := mem_centralizer_iff.mpr fun a ha =>
    ((mem_centralizer_iff.mp (mem_inf.mp ha).2) g hgT₁).symm
  have hA₁c : A₁.map (MulAut.conj c).toMonoidHom = A₁ := by
    rw [hconjc, hA₁n]
    exact mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hgA)
  have hX₀X₀ : ⁅X₀, X₀⁆ ≤ X₀ := commutator_le.mpr fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hA₁X₀ : A₁ ≤ X₀ := hAX'.trans hX₀X₀
  have hA₁X : A₁ ≤ X := by
    rw [← hXc, ← hA₁c]
    exact Subgroup.map_mono hA₁X₀
  have heXX : Nonempty (rankTwoQuot X ≃* Matrix.SpecialLinearGroup (Fin 2)
      (GaloisField 2 f)) := by
    rw [← hXc]
    obtain ⟨ec⟩ := nonempty_rankTwoQuot_map_conj X₀ c
    exact ⟨ec.trans eX⟩
  obtain ⟨eXX⟩ := heXX
  have hZXX : Odd (Nat.card (center X)) := by
    rw [← hXc, card_center_map_conj]
    exact hZX
  have hYK : ⁅X, X⁆ ≤ centralizer (K : Set G) :=
    commutator_le_centralizer_of_odd hf eXX hZXX hKX hKo hA₁X hA₁card hKA
  set Y := ⁅X, X⁆ with hYdef
  have hYc : (⁅X₀, X₀⁆).map (MulAut.conj c).toMonoidHom = Y := by
    rw [map_commutator, hXc]
  have hA₁Y : A₁ ≤ Y := by
    rw [← hYc, ← hA₁c]
    exact Subgroup.map_mono hAX'
  have heYY : Nonempty (rankTwoQuot Y ≃* Matrix.SpecialLinearGroup (Fin 2)
      (GaloisField 2 f)) := by
    rw [← hYc]
    obtain ⟨ec⟩ := nonempty_rankTwoQuot_map_conj (⁅X₀, X₀⁆) c
    exact ⟨ec.trans eX'⟩
  obtain ⟨eY⟩ := heYY
  have hZYY : Odd (Nat.card (center Y)) := by
    rw [← hYc, card_center_map_conj]
    exact hZX'
  have h4 : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    have hc : 4 ≤ (Finset.univ : Finset (GaloisField 2 f)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  have hYs : IsSimpleGroup (rankTwoQuot Y) := by
    have := u3_isSimpleGroup_SL2 (GaloisField 2 f) h4
    exact eY.isSimpleGroup
  have hYZ : center (rankTwoQuot Y) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eY z ∈ center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := eY.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) w]
    rw [u3_center_SL2_eq_bot, mem_bot] at h1
    rw [mem_bot]
    exact eY.injective (h1.trans (map_one eY).symm)
  have hYe : Even (Nat.card (rankTwoQuot Y)) := by
    rw [Nat.card_congr eY.toEquiv]
    exact u3_even_card_SL2 _
  have hXL' : X ≤ L' := (commutator_le.mpr fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)).trans inf_le_left
  have hYL' : Y ≤ L' := (commutator_le.mpr fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)).trans hXL'
  have hQY : Q ≤ centralizer (Y : Set G) := hQL'.trans (Subgroup.centralizer_le hYL')
  have hQT₀ : ¬ Q ≤ T₀ := fun hle => hQne (Subgroup.eq_of_le_of_card_ge hle
    (by rw [← hnQ, rightConjugate_card]))
  exact ⟨Y, Q, hYK, hA₁Y, hQY, hQΔ.2, hQT₀, hYs, hYZ, hYe, hZYY⟩

end Sec3

theorem not_normal_oddQuotImageC_of_conj {K X₀ Y A T₀ Q : Subgroup G}
    (hYK : Y ≤ centralizer (K : Set G)) (hAX₀ : A ≤ X₀) (hAY : A ≤ Y) (hA2 : IsPGroup 2 A)
    (hT₀K : T₀ ≤ centralizer (K : Set G)) (hT₀X₀ : T₀ ≤ centralizer (X₀ : Set G))
    (hQY : Q ≤ centralizer (Y : Set G)) (hT₀A : T₀ ≤ normalizer (A : Set G))
    (hQV : Q ≤ A ⊔ T₀) (hQT₀ : ¬ Q ≤ T₀)
    (hYs : IsSimpleGroup (rankTwoQuot Y)) (hYZ : center (rankTwoQuot Y) = ⊥)
    (hYe : Even (Nat.card (rankTwoQuot Y))) (hZY : Odd (Nat.card (center Y))) :
    ¬ (oddQuotImageC K X₀).Normal := by
  intro hN
  have := hYs
  set G₁ := centralizer (K : Set G) with hG₁
  set O := standardComponentOddCore G₁
  have hOo : Odd (Nat.card O) := odd_card_standardComponentOddCore'
  set π := QuotientGroup.mk' O
  set Xb := oddQuotImageC K X₀
  have hYG₁ : Y ≤ G₁ := hYK
  set ι : Y →* G₁ := Subgroup.inclusion hYG₁
  set πY := QuotientGroup.mk' (center Y)
  obtain ⟨x, hxQ, hxT₀⟩ := Set.not_subset.mp hQT₀
  have hxV : x ∈ ((A ⊔ T₀ : Subgroup G) : Set G) := hQV hxQ
  rw [coe_mul_of_right_le_normalizer_left A T₀ hT₀A] at hxV
  obtain ⟨a, haA, t, htT₀, rfl⟩ := Set.mem_mul.mp hxV
  have haY : a ∈ Y := hAY haA
  set a' : Y := ⟨a, haY⟩
  have htG₁ : t ∈ G₁ := hT₀K htT₀
  obtain ⟨k₀, hk₀⟩ := hA2 ⟨a, haA⟩
  have ha2 : a' ^ 2 ^ k₀ = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk₀)
  suffices hπa : πY a' = 1 by
    have haZ : a' ∈ center Y := by
      rw [← QuotientGroup.eq_one_iff]
      exact hπa
    have ha1 : a' = 1 := eq_one_of_pow_two_pow_of_mem_odd hZY haZ ha2
    have ha1' : a = 1 := congrArg Subtype.val ha1
    rw [ha1', one_mul] at hxT₀
    exact hxT₀ htT₀
  have hcomm₁ : ∀ m : Y, π (ι m) ∈ Xb → π (ι a') * π (ι m) = π (ι m) * π (ι a') := by
    intro m hm
    obtain ⟨w, hw, hwm⟩ := hm
    have hwX : ((w : G₁) : G) ∈ X₀ := hw
    have htw : (⟨t, htG₁⟩ : G₁) * w = w * ⟨t, htG₁⟩ := Subtype.ext
      ((mem_centralizer_iff.mp (hT₀X₀ htT₀)) _ hwX).symm
    have hxm : ι a' * ⟨t, htG₁⟩ * ι m = ι m * (ι a' * ⟨t, htG₁⟩) := Subtype.ext
      ((mem_centralizer_iff.mp (hQY hxQ)) _ m.2).symm
    have h1 : π (ι a' * ⟨t, htG₁⟩ * ι m) = π (ι m * (ι a' * ⟨t, htG₁⟩)) := by rw [hxm]
    have h2 : π (⟨t, htG₁⟩ * w) = π (w * ⟨t, htG₁⟩) := by rw [htw]
    simp only [map_mul] at h1 h2
    rw [hwm] at h2
    calc π (ι a') * π (ι m) = π (ι a') * π ⟨t, htG₁⟩ * π (ι m) * (π ⟨t, htG₁⟩)⁻¹ := by
          rw [mul_assoc (π (ι a')), h2]; group
      _ = π (ι m) * (π (ι a') * π ⟨t, htG₁⟩) * (π ⟨t, htG₁⟩)⁻¹ := by rw [h1]
      _ = π (ι m) * π (ι a') := by group
  set NY : Subgroup Y := (Xb.comap π).comap ι
  have : NY.Normal := Subgroup.Normal.comap (Subgroup.Normal.comap hN π) ι
  have haN : a' ∈ NY := by
    show π (ι a') ∈ Xb
    exact ⟨ι a', hAX₀ haA, rfl⟩
  set OY : Subgroup Y := O.comap ι
  have : OY.Normal := Subgroup.Normal.comap inferInstance ι
  have hOY : ∀ c ∈ OY, πY c = 1 := by
    have hn : (OY.map πY).Normal := Subgroup.Normal.map inferInstance _
      (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (OY.map πY) with hb | ht
    · intro c hc
      have : πY c ∈ OY.map πY := ⟨c, hc, rfl⟩
      rwa [hb, mem_bot] at this
    · exfalso
      have h1 : Nat.card (OY.map πY) ∣ Nat.card OY := OY.card_map_dvd πY
      have h2 : Nat.card OY ∣ Nat.card O := by
        have h3 := Subgroup.card_dvd_of_le (show OY.map ι ≤ O from fun _ ⟨c, hc, hce⟩ =>
          hce ▸ hc)
        rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hYG₁)] at h3
      rw [ht, Subgroup.card_top] at h1
      exact (Nat.not_even_iff_odd.mpr (hOo.of_dvd_nat (h1.trans h2))) hYe
  have hnN : (NY.map πY).Normal := Subgroup.Normal.map inferInstance _
    (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (NY.map πY) with hb | ht
  · have : πY a' ∈ NY.map πY := ⟨a', haN, rfl⟩
    rwa [hb, mem_bot] at this
  ·
    have hcen : πY a' ∈ center (rankTwoQuot Y) := by
      rw [mem_center_iff]
      intro u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center Y) u
      have hy : πY y ∈ NY.map πY := by rw [ht]; exact mem_top _
      obtain ⟨m, hm, hmy⟩ := hy
      have hz : m⁻¹ * y ∈ center Y := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have : (QuotientGroup.mk m : rankTwoQuot Y) = QuotientGroup.mk y := hmy
        rw [this, inv_mul_cancel]
      have haz : a' * (m⁻¹ * y) = (m⁻¹ * y) * a' := (mem_center_iff.mp hz) a'
      have hcm := hcomm₁ m hm
      have hcz : π (ι a') * π (ι (m⁻¹ * y)) = π (ι (m⁻¹ * y)) * π (ι a') := by
        have h3 := congrArg (fun w => π (ι w)) haz
        simpa only [map_mul] using h3
      have hcy : π (ι a') * π (ι y) = π (ι y) * π (ι a') := by
        have hy' : ι y = ι m * ι (m⁻¹ * y) := by rw [← map_mul, mul_inv_cancel_left]
        rw [hy', map_mul, ← mul_assoc, hcm, mul_assoc, hcz, ← mul_assoc]
      have hπ : π (ι (a' * y * a'⁻¹ * y⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcy]
        group
      have hO : a' * y * a'⁻¹ * y⁻¹ ∈ OY := by
        show ι (a' * y * a'⁻¹ * y⁻¹) ∈ O
        rw [← QuotientGroup.eq_one_iff]
        exact hπ
      have h1 := hOY _ hO
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : πY a' * πY y * (πY a')⁻¹ = πY y := mul_inv_eq_one.mp h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [hYZ, mem_bot] at hcen
    exact hcen

theorem gms61NotNormalC
    (hF : Foundation) : GMS61NotNormalC := by
  intro G _ _ L T K f hf he h3 hKL hKo hKH
  obtain ⟨e⟩ := he
  obtain ⟨-, -, hAX', -, -, -, -, -⟩ := u3K_facts h3 hf e hKL hKo hKH
  obtain ⟨Y, Q, hYK, hA₁Y, hQY, hQV, hQT₀, hYs, hYZ, hYe, hZY⟩ :=
    h3.exists_conj_centralized_by_delta hF hf e hKL hKo hKH
  have hX₀X₀ : ⁅u3X₀ L K, u3X₀ L K⁆ ≤ u3X₀ L K := commutator_le.mpr fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hX₀L : u3X₀ L K ≤ L := by
    show ⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆ ≤ L
    exact (commutator_le.mpr fun x hx y hy =>
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)).trans inf_le_left
  have hA₁L : gmsA L T ≤ L := inf_le_left.trans inf_le_right
  have hT₀L : T ⊓ centralizer (L : Set G) ≤ centralizer (L : Set G) := inf_le_right
  exact not_normal_oddQuotImageC_of_conj hYK (hAX'.trans hX₀X₀) hA₁Y
    (h3.isSylowOf_T₁.isPGroup.to_le inf_le_left)
    (hT₀L.trans (Subgroup.centralizer_le hKL)) (hT₀L.trans (Subgroup.centralizer_le hX₀L))
    hQY (hT₀L.trans ((Subgroup.centralizer_le hA₁L).trans (Subgroup.centralizer_le_normalizer _)))
    hQV hQT₀ hYs hYZ hYe hZY

end CFSG.ComponentClassification.GMS78
