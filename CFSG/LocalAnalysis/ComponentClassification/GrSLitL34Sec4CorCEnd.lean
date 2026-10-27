module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCEndFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCEndTools

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X]

namespace Config

variable {a : X} {J E : Subgroup X}

theorem sylow_centralizer (h : Config a J E) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hΩ : ∀ q ∈ S ⊓ coreActionKernel J, orderOf q = 2 → (∀ s ∈ S, s * q = q * s) → q = a) :
    ∃ T : Sylow 2 ↥(centralizer ({a} : Set X)),
      (T : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({a} : Set X) with hC
  set H := C ⊓ normalizer (J : Set X) with hH
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 ((P₀ : Subgroup _).map H.subtype) := P₀.isPGroup'.map _
    rwa [hP₀, map_subgroupOf_eq_of_le hSH] at h1
  have hSC : S ≤ C := hSH.trans inf_le_left
  have hSN : S ≤ normalizer (J : Set X) := hSH.trans inf_le_right
  have hS₁ : IsPGroup 2 (S.subgroupOf C) := hS2.of_equiv (subgroupOfEquivOfLe hSC).symm
  obtain ⟨T, hTle⟩ := hS₁.exists_le_sylow
  refine ⟨T, ?_⟩
  by_contra hne
  have : Group.IsNilpotent ↥(T : Subgroup ↥C) := T.isPGroup'.isNilpotent
  set U := (S.subgroupOf C).subgroupOf (T : Subgroup ↥C) with hU
  have hUtop : U < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun x hx => ?_) hTle
    have hx' : (⟨x, hx⟩ : ↥(T : Subgroup ↥C)) ∈ U := htop ▸ mem_top _
    exact hx'
  obtain ⟨u, huN, huU⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent U hUtop)
  set t : X := ((u : ↥C) : X) with ht
  have htC : t ∈ C := (u : ↥C).2
  have htS : t ∉ S := fun h' => huU h'
  have htSS : ∀ s ∈ S, t * s * t⁻¹ ∈ S := by
    intro s hs
    have hsT : (⟨s, hSC hs⟩ : ↥C) ∈ (T : Subgroup ↥C) :=
      hTle (show (⟨s, hSC hs⟩ : ↥C) ∈ S.subgroupOf C from hs)
    have hsU : (⟨⟨s, hSC hs⟩, hsT⟩ : ↥(T : Subgroup ↥C)) ∈ U := hs
    exact (mem_normalizer_iff.mp huN _).mp hsU
  have htN : t ∈ normalizer (S : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj _).injective])
    rintro _ ⟨s, hs, rfl⟩
    exact htSS s hs
  obtain ⟨k, hk⟩ := T.isPGroup' u
  have htk : t ^ 2 ^ k = 1 := by
    have h1 := congrArg (fun v : ↥(T : Subgroup ↥C) => ((v : ↥C) : X)) hk
    simpa using h1
  have htJ : t ∉ normalizer (J : Set X) := by
    intro htJ
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have htH : t ∈ H := mem_inf.mpr ⟨htC, htJ⟩
    have hwk : (⟨t, htH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using htk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hwk)
    have hw2 : IsPGroup 2 (zpowers (⟨t, htH⟩ : ↥H)) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    have hwN : (⟨t, htH⟩ : ↥H) ∈ normalizer ((P₀ : Subgroup ↥H) : Set ↥H) := by
      rw [mem_normalizer_iff]
      intro y
      show y ∈ (P₀ : Subgroup ↥H) ↔
        (⟨t, htH⟩ : ↥H) * y * (⟨t, htH⟩ : ↥H)⁻¹ ∈ (P₀ : Subgroup ↥H)
      rw [hP₀, mem_subgroupOf, mem_subgroupOf]
      exact mem_normalizer_iff.mp htN y
    have h1 := (hw2.inf_normalizer_sylow P₀).le (mem_inf.mpr ⟨mem_zpowers _, hwN⟩)
    have h2 : (⟨t, htH⟩ : ↥H) ∈ (P₀ : Subgroup ↥H) := (mem_inf.mp h1).2
    rw [hP₀, mem_subgroupOf] at h2
    exact htS h2
  have hJ'C : conjugate J t ≤ C := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h2 := mul_mem (mul_mem (inv_mem htC) (h.le_centralizer hy)) htC
    rwa [show t⁻¹ * (t * y * t⁻¹) * t = y by group] at h2
  have hJ'c : IsPComponent 2 ((conjugate J t).subgroupOf C) := by
    have h1 := isPComponent_conjugate h.isPComponent (⟨t, htC⟩ : ↥C)
    rwa [conjugate_subgroupOf_eq] at h1
  have hJne : J ≠ conjugate J t := fun he => htJ (mem_normalizer_of_conjugate_eq he.symm)
  have hJ'K : conjugate J t ≤ coreActionKernel J :=
    le_coreActionKernel_of_component_ne h.le_centralizer hJ'C h.isPComponent hJ'c hJne
  have hSJ' : S ≤ normalizer ((conjugate J t : Subgroup X) : Set X) := fun s hs =>
    mem_normalizer_iff.mpr fun y => by
      have hs' : t * s * t⁻¹ ∈ normalizer (J : Set X) := hSN (htSS s hs)
      have h1 := mem_normalizer_iff.mp hs' (t * y * t⁻¹)
      simp only [mem_conjugate_iff] at h1 ⊢
      rw [h1, show t * s * t⁻¹ * (t * y * t⁻¹) * (t * s * t⁻¹)⁻¹ = t * (s * y * s⁻¹) * t⁻¹ by
        group]
  have hDne : S ⊓ J ≠ ⊥ := fun hbot => by
    have h1 := (h.card_inf hSH hSsyl).1
    rw [hbot, card_bot] at h1
    omega
  obtain ⟨x, hxD, hx1⟩ := (S ⊓ J).bot_or_exists_ne_one.resolve_left hDne
  have hD'ne : S ⊓ conjugate J t ≠ ⊥ := by
    intro hbot
    have hmem : t⁻¹ * x * t ∈ S ⊓ conjugate J t := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h1 := (mem_normalizer_iff.mp (inv_mem htN) x).mp (mem_inf.mp hxD).1
        rwa [inv_inv] at h1
      · rw [mem_conjugate_iff, show t * (t⁻¹ * x * t) * t⁻¹ = x by group]
        exact (mem_inf.mp hxD).2
    rw [hbot, mem_bot] at hmem
    apply hx1
    calc x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      _ = 1 := by rw [hmem]; group
  obtain ⟨q, hqD', hq2, hqS⟩ := exists_involution_center_of_normal hS2 inf_le_left
    (le_normalizer_inf Subgroup.le_normalizer hSJ') hD'ne
  have hqa := hΩ q (mem_inf.mpr ⟨(mem_inf.mp hqD').1, hJ'K (mem_inf.mp hqD').2⟩) hq2 hqS
  have haJ' : a ∈ conjugate J t := hqa ▸ (mem_inf.mp hqD').2
  rw [mem_conjugate_iff] at haJ'
  have hta : t * a = a * t := mem_centralizer_singleton_iff.mp htC
  rw [hta, mul_inv_cancel_right] at haJ'
  exact h.not_mem haJ'

theorem false_of_fusion (h : Config a J E) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hES : E ≤ S) {b : X} (hbSK : b ∈ S ⊓ coreActionKernel J)
    (hbE : ¬ ∀ e ∈ E, e * b = b * e)
    (hΩ : ∀ q ∈ S ⊓ coreActionKernel J, orderOf q = 2 → (∀ s ∈ S, s * q = q * s) → q = a)
    (hfus : ∀ z ∈ S ⊓ J, orderOf z = 2 → (∀ s ∈ S, s * z = z * s) →
      ∃ g : X, g * a * g⁻¹ = a * z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 ((P₀ : Subgroup _).map
        (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)).subtype) := P₀.isPGroup'.map _
    rwa [hP₀, map_subgroupOf_eq_of_le hSH] at h1
  have hSC : S ≤ centralizer ({a} : Set X) := hSH.trans inf_le_left
  have hSN : S ≤ normalizer (J : Set X) := hSH.trans inf_le_right
  have haSK := UnbalancedCorr.mem_inf_coreActionKernel_of_sylow h.orderOf_eq h.le_centralizer hSsyl
  have haP : a ∈ S ⊓ coreActionKernel J :=
    mem_inf.mpr ⟨(mem_inf.mp haSK).1, (mem_inf.mp (mem_inf.mp haSK).2).2⟩
  obtain ⟨hD8, hZD⟩ := h.card_inf hSH hSsyl
  set P := S ⊓ coreActionKernel J with hP
  set D := S ⊓ J with hD
  have hSnK : S ≤ normalizer (coreActionKernel J : Set X) := fun s hs =>
    mem_normalizer_iff.mpr fun y =>
      ⟨fun hy => UnbalancedLayer.conj_mem_coreActionKernel (hSN hs) hy, fun hy => by
        have h1 := UnbalancedLayer.conj_mem_coreActionKernel (inv_mem (hSN hs)) hy
        rwa [show s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y by group] at h1⟩
  have hSnP : S ≤ normalizer (P : Set X) := le_normalizer_inf Subgroup.le_normalizer hSnK
  have hSnD : S ≤ normalizer (D : Set X) := le_normalizer_inf Subgroup.le_normalizer hSN
  have hDP : D ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨hxS, hxJ⟩, -, hxK⟩ := hx
    obtain ⟨k, hk⟩ := hS2 ⟨x, hxS⟩
    exact mem_bot.mpr (eq_one_of_mem_oddIn (h.mem_oddIn_of_mem_coreActionKernel hxJ hxK)
      (by simpa using congrArg Subtype.val hk))
  have hDne : D ≠ ⊥ := fun hbot => by
    rw [hbot, card_bot] at hD8
    omega
  obtain ⟨z, hzD, hz, hzS⟩ := exists_involution_center_of_normal hS2 inf_le_left hSnD hDne
  obtain ⟨g, hg⟩ := hfus z hzD hz hzS
  obtain ⟨n, hnS, hna⟩ :=
    exists_mem_normalizer_conj hSC (h.sylow_centralizer hSH hSsyl hΩ) hzS hg
  set Q := P.map (MulAut.conj n).toMonoidHom with hQ
  have hmemQ : ∀ y, y ∈ Q ↔ n⁻¹ * y * n ∈ P := fun y => by
    rw [hQ, mem_map_equiv, MulAut.conj_symm_apply]
  have hQS : Q ≤ S := fun y hy => by
    have h1 := (mem_normalizer_iff.mp hnS _).mp ((hmemQ y).mp hy).1
    rwa [show n * (n⁻¹ * y * n) * n⁻¹ = y by group] at h1
  have hSnQ : S ≤ normalizer (Q : Set X) := fun s hs => mem_normalizer_iff.mpr fun y => by
    have hs' : n⁻¹ * s * n ∈ S := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hnS) s).mp hs
      rwa [inv_inv] at h1
    have h1 := mem_normalizer_iff.mp (hSnP hs') (n⁻¹ * y * n)
    show y ∈ Q ↔ s * y * s⁻¹ ∈ Q
    rw [hmemQ, hmemQ]
    rw [show n⁻¹ * s * n * (n⁻¹ * y * n) * (n⁻¹ * s * n)⁻¹ = n⁻¹ * (s * y * s⁻¹) * n by
      group] at h1
    exact h1
  have hQP : Nat.card Q = Nat.card P := card_map_of_injective (MulAut.conj n).injective
  have hcent : ∀ q : X, (∀ s ∈ S, s * q = q * s) →
      ∀ s ∈ S, s * (n⁻¹ * q * n) = n⁻¹ * q * n * s := by
    intro q hq s hs
    have h1 := hq _ ((mem_normalizer_iff.mp hnS s).mp hs)
    calc s * (n⁻¹ * q * n) = n⁻¹ * (n * s * n⁻¹ * q) * n := by group
      _ = n⁻¹ * (q * (n * s * n⁻¹)) * n := by rw [h1]
      _ = n⁻¹ * q * n * s := by group
  have hQa : ∀ q ∈ Q, orderOf q = 2 → (∀ s ∈ S, s * q = q * s) → q = a * z := by
    intro q hq hq2 hqS
    have h2 := hΩ (n⁻¹ * q * n) ((hmemQ q).mp hq)
      ((SemiconjBy.orderOf_eq n⁻¹ (show n⁻¹ * q = n⁻¹ * q * n * n⁻¹ by group)).symm.trans hq2)
      (hcent q hqS)
    rw [← hna, ← h2]
    group
  have hPQ : P ⊓ Q = ⊥ := by
    by_contra hne
    obtain ⟨q, hq, hq2, hqS⟩ := exists_involution_center_of_normal hS2
      (inf_le_left.trans inf_le_left) (le_normalizer_inf hSnP hSnQ) hne
    have h1 := hΩ q (mem_inf.mp hq).1 hq2 hqS
    have h3 := hQa q (mem_inf.mp hq).2 hq2 hqS
    have h4 : a * z = a * 1 := by rw [mul_one, ← h3, h1]
    rw [mul_left_cancel h4, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hDQ : D ⊓ Q = ⊥ := by
    by_contra hne
    obtain ⟨q, hq, hq2, hqS⟩ := exists_involution_center_of_normal hS2
      (inf_le_left.trans inf_le_left) (le_normalizer_inf hSnD hSnQ) hne
    have h3 := hQa q (mem_inf.mp hq).2 hq2 hqS
    have h4 := mul_mem (mem_inf.mp (mem_inf.mp hq).1).2 (inv_mem (mem_inf.mp hzD).2)
    rw [h3, mul_inv_cancel_right] at h4
    exact h.not_mem h4
  have hP4 : 4 ≤ Nat.card P := by
    have hZle : zpowers a ≤ P := zpowers_le.mpr haP
    have hZ2 : Nat.card (zpowers a) = 2 := by rw [Nat.card_zpowers, h.orderOf_eq]
    have hbZ : b ∉ zpowers a := by
      intro hb'
      apply hbE
      intro e he
      have hae : a ∈ centralizer ({e} : Set X) := mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (mem_inf.mp (h.le_H he)).1).symm
      exact (mem_centralizer_singleton_iff.mp (zpowers_le.mpr hae hb')).symm
    obtain ⟨m, hm⟩ := card_dvd_of_le hZle
    rw [hZ2] at hm
    have hpos : 0 < Nat.card P := Nat.card_pos
    rcases m with _ | _ | m
    · omega
    · have hZP : zpowers a = P := eq_of_le_of_card_ge hZle (by rw [hZ2, hm])
      exact (hbZ (hZP ▸ hbSK)).elim
    · omega
  have hc := centralizes_of_count inf_le_left inf_le_left hQS
    (commute_of_inf_eq_bot (inf_le_left.trans hSnP) (inf_le_left.trans hSnD) hDP)
    (commute_of_inf_eq_bot (inf_le_left.trans hSnQ) (hQS.trans hSnD) hDQ)
    (commute_of_inf_eq_bot (inf_le_left.trans hSnQ) (hQS.trans hSnP) hPQ) hDP hPQ hQP
    (h.card_le_sixteen hS2 hSN) hD8.ge hZD.le hP4
  exact hbE fun e he => hc e (hES he) b hbSK

end Config

end CFSG.ComponentClassification.GSThmB.CorC
