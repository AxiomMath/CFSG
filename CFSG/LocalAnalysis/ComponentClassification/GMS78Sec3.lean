module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup
public import CFSG.Walter.W67.W2Cor32A

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

structure Foundation : Prop where
  lemma32 : AS76b.Lemma32
  lemma33One : AS76b.Lemma33One
  lemma33Two : AS76b.Lemma33Two
  lemma33Three : AS76b.Lemma33Three
  asc75Theorem4 : AS76b.Asc75Theorem4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB : x ∈ normalizer (B : Set G)) : x ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [mem_inf, mem_inf, hA y, hB y]

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB : x ∈ normalizer (B : Set G)) : x ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem isSylowOf_sup_of_inf {p : ℕ} [Fact p.Prime] {A B R Z : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) (hR : IsSylowOf p R A) (hZ : IsSylowOf p Z B)
    (hRZ : R ≤ normalizer (Z : Set G)) (hinf : IsSylowOf p (R ⊓ Z) (A ⊓ B)) :
    IsSylowOf p (R ⊔ Z) (A ⊔ B) := by
  have hp : p.Prime := Fact.out
  have hle : R ⊔ Z ≤ A ⊔ B := sup_le_sup hR.le hZ.le
  refine isSylowOf_iff.mpr ⟨hle, hR.isPGroup.to_sup_of_normal_right' hZ.isPGroup hRZ, ?_⟩
  have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hAB
  have h2 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hRZ
  rw [sup_comm B, inf_comm B] at h1
  rw [sup_comm Z, inf_comm Z] at h2
  have hA := relIndex_mul_card R A
  have hB := relIndex_mul_card Z B
  have hK := relIndex_mul_card (R ⊔ Z) (A ⊔ B)
  have hI := relIndex_mul_card (R ⊓ Z) (A ⊓ B)
  rw [inf_eq_left.mpr hR.le] at hA
  rw [inf_eq_left.mpr hZ.le] at hB
  rw [inf_eq_left.mpr hle] at hK
  rw [inf_eq_left.mpr hinf.le] at hI
  have hpos : 0 < Nat.card (R ⊔ Z : Subgroup G) * Nat.card (R ⊓ Z : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have key : (R ⊔ Z).relIndex (A ⊔ B) * (R ⊓ Z).relIndex (A ⊓ B) =
      R.relIndex A * Z.relIndex B := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (R ⊔ Z).relIndex (A ⊔ B) * (R ⊓ Z).relIndex (A ⊓ B) *
          (Nat.card (R ⊔ Z : Subgroup G) * Nat.card (R ⊓ Z : Subgroup G))
        = ((R ⊔ Z).relIndex (A ⊔ B) * Nat.card (R ⊔ Z : Subgroup G)) *
            ((R ⊓ Z).relIndex (A ⊓ B) * Nat.card (R ⊓ Z : Subgroup G)) := by ring
      _ = Nat.card A * Nat.card B := by rw [hK, hI, h1, mul_comm]
      _ = R.relIndex A * Z.relIndex B *
            (Nat.card (R ⊔ Z : Subgroup G) * Nat.card (R ⊓ Z : Subgroup G)) := by
          rw [h2, ← hA, ← hB]
          ring
  intro hdvd
  have : p ∣ R.relIndex A * Z.relIndex B := key ▸ hdvd.mul_right _
  rcases hp.dvd_mul.mp this with h | h
  · exact (isSylowOf_iff.mp hR).2.2 h
  · exact (isSylowOf_iff.mp hZ).2.2 h

structure Sec3 (G : Type) [Group G] [Finite G] (L T : Subgroup G) : Prop where
  hyp : BenderHyp G L
  sylow : IsSylowOf 2 T (normalizer (L : Set G))

namespace Sec3

variable {L T : Subgroup G}

theorem normalizer_le_normalizer_centralizer (h : Sec3 G L T) :
    normalizer (L : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) := by
  rw [AS76b.normalizer_centralizer_eq h.hyp.standard]

theorem centralizer_le_normalizer (h : Sec3 G L T) :
    centralizer (L : Set G) ≤ normalizer (L : Set G) := by
  rw [← AS76b.normalizer_centralizer_eq h.hyp.standard]
  exact le_normalizer

theorem isSylowOf_T₁ (h : Sec3 G L T) : IsSylowOf 2 (T ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.sylow.inf_of_le_normalizer le_normalizer le_rfl

theorem isSylowOf_T₀ (h : Sec3 G L T) : IsSylowOf 2 (T ⊓ centralizer (L : Set G))
    (centralizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.sylow.inf_of_le_normalizer h.centralizer_le_normalizer
    h.normalizer_le_normalizer_centralizer

omit [Finite G] in
theorem le_centralizer {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) :
    L ≤ centralizer ({t} : Set G) := fun x hx =>
  mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ht.2 x hx)

theorem isElemAbelian_T₀
    (h : Sec3 G L T) (hF : Foundation) : IsElemAbelian 2 (T ⊓ centralizer (L : Set G)) :=
  hF.lemma32 G L h.hyp.hyp31 _ h.isSylowOf_T₀

theorem exists_four_le (h : Sec3 G L T) :
    ∃ E : Subgroup G, E ≤ T ⊓ centralizer (L : Set G) ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 :=
  exists_elemAbelian_four_le_of_isSylowOf h.hyp.rank h.isSylowOf_T₀

theorem T₀_ne_bot (h : Sec3 G L T) : T ⊓ centralizer (L : Set G) ≠ ⊥ := by
  obtain ⟨E, hE, -, hE4⟩ := h.exists_four_le
  intro hb
  rw [hb, le_bot_iff] at hE
  rw [hE, card_bot] at hE4
  norm_num at hE4

theorem inf_sup_eq (h : Sec3 G L T) :
    T ⊓ (L ⊔ centralizer (L : Set G)) = (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G)
  have hKN := h.centralizer_le_normalizer
  have hLKN : L ⊔ K ≤ normalizer (L : Set G) := sup_le le_normalizer hKN
  have hLKn : normalizer (L : Set G) ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup hx (h.normalizer_le_normalizer_centralizer hx)
  have hS : IsSylowOf 2 (T ⊓ (L ⊔ K)) (L ⊔ K) := h.sylow.inf_of_le_normalizer hLKN hLKn
  have hLKi : L ⊓ K ≤ normalizer (L : Set G) := inf_le_left.trans le_normalizer
  have hLKin : normalizer (L : Set G) ≤ normalizer ((L ⊓ K : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf hx (h.normalizer_le_normalizer_centralizer hx)
  have hinf : IsSylowOf 2 ((T ⊓ L) ⊓ (T ⊓ K)) (L ⊓ K) := by
    have := h.sylow.inf_of_le_normalizer hLKi hLKin
    rwa [show (T ⊓ L) ⊓ (T ⊓ K) = T ⊓ (L ⊓ K) by
      ext x
      simp only [mem_inf]
      tauto]
  have hT₀N : T ⊓ L ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (le_normalizer hx.1)
      (h.normalizer_le_normalizer_centralizer (le_normalizer hx.2))
  have hP := isSylowOf_sup_of_inf (le_normalizer.trans h.normalizer_le_normalizer_centralizer)
    h.isSylowOf_T₁ h.isSylowOf_T₀ hT₀N hinf
  have hle : (T ⊓ L) ⊔ (T ⊓ K) ≤ T ⊓ (L ⊔ K) :=
    sup_le (inf_le_inf_left T le_sup_left) (inf_le_inf_left T le_sup_right)
  exact hP.eq_of_le hle hS.le hS.isPGroup

omit [Finite G] in
theorem map_conj_rightConjugate (Q : Subgroup G) (y c : G) :
    (rightConjugate Q y).map (MulAut.conj c).toMonoidHom = rightConjugate Q (y * c⁻¹) := by
  ext x
  rw [mem_map_equiv, mem_rightConjugate_iff, mem_rightConjugate_iff]
  simp only [MulAut.conj_symm_apply, mul_inv_rev, inv_inv]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem exists_conj
    (h : Sec3 G L T) (hF : Foundation) :
    ∃ g : G, g ∉ normalizer (L : Set G) ∧
      rightConjugate (T ⊓ centralizer (L : Set G)) g ≤ T ⊓ (L ⊔ centralizer (L : Set G)) ∧
      rightConjugate (T ⊓ centralizer (L : Set G)) g ⊓ centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  have hA := h.hyp.hyp31
  have htight := AS76b.tightlyEmbedded_centralizer h.hyp.standard
  have hNK := AS76b.normalizer_centralizer_eq h.hyp.standard
  have hKM := h.centralizer_le_normalizer
  obtain ⟨g, hg, T', hT'N, hT'K⟩ := hF.lemma33Three G L hA
  have hT'M : T' ≤ normalizer (L : Set G) := hT'N.le.trans inf_le_right
  obtain ⟨S, hS, hT'S⟩ := AS76b.exists_isSylowOf_le hT'M hT'K.isPGroup
  obtain ⟨m, hm, hSm⟩ := IsSylowOf.exists_map_conj h.sylow hS
  have hT'' : rightConjugate T' m ≤ T := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have h1 := hT'S hy
    rw [hSm] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    have : z = y := by
      have h2 : m * z * m⁻¹ = m * y * m⁻¹ := hzy
      simpa using h2
    rw [← this]
    exact hz
  set x := g * m with hxdef
  have hxM : x ∉ normalizer (L : Set G) := fun hx => hg (by
    have := mul_mem hx (inv_mem hm)
    rwa [hxdef, mul_inv_cancel_right] at this)
  have hT''K : IsSylowOf 2 (rightConjugate T' m) (rightConjugate K x) := by
    have := AschbacherTheorem3.isSylowOf_rightConjugate hT'K m
    rwa [rightConjugate_mul] at this
  have hT₀x := AschbacherTheorem3.isSylowOf_rightConjugate h.isSylowOf_T₀ x
  obtain ⟨c, hc, hceq⟩ := IsSylowOf.exists_map_conj hT₀x hT''K
  rw [map_conj_rightConjugate] at hceq
  set h₀ := x * c⁻¹ with hh₀def
  have hk : x * c * x⁻¹ ∈ K := (mem_rightConjugate_iff K x c).mp hc
  have hh₀M : h₀ ∉ normalizer (L : Set G) := by
    intro hh
    apply hxM
    have h1 : x = (x * c * x⁻¹) * h₀ := by rw [hh₀def]; group
    rw [h1]
    exact mul_mem (hKM hk) hh
  have hh₀K : h₀ ∉ normalizer (K : Set G) := by rwa [hNK]
  have hT₀h : rightConjugate T₀ h₀ ≤ T := hceq ▸ hT''
  have hT₀hK : IsSylowOf 2 (rightConjugate T₀ h₀) (rightConjugate K h₀) :=
    AschbacherTheorem3.isSylowOf_rightConjugate h.isSylowOf_T₀ h₀
  have hbot : rightConjugate T₀ h₀ ⊓ K = ⊥ := by
    refine two_subgroup_of_odd_eq_bot _ (K ⊓ rightConjugate K h₀) ?_ (htight.2 h₀ hh₀K) ?_
    · exact hT₀hK.isPGroup.to_inf_left
    · exact fun y hy => ⟨hy.2, hT₀hK.le hy.1⟩
  have hTM : rightConjugate T₀ h₀ ≤ normalizer (L : Set G) := hT₀h.trans h.sylow.le
  have hTKN : rightConjugate T₀ h₀ ≤ normalizer (K : Set G) := by rw [hNK]; exact hTM
  obtain ⟨S', hS', hTS'⟩ := AS76b.exists_isSylowOf_le
    (le_sup_right : rightConjugate T₀ h₀ ≤ K ⊔ rightConjugate T₀ h₀) hT₀hK.isPGroup
  have hR : IsSylowOf 2 (S' ⊓ K) K :=
    hS'.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTKN)
  have hTR : rightConjugate T₀ h₀ ≤ normalizer ((S' ⊓ K : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_inf (le_normalizer (hTS' hy)) (hTKN hy)
  have hT1 : rightConjugate T₀ h₀ ≠ ⊥ := by
    intro hb
    apply h.T₀_ne_bot
    have h1 : rightConjugate (rightConjugate T₀ h₀) h₀⁻¹ = ⊥ := by
      rw [hb]
      ext y
      simp only [mem_rightConjugate_iff, inv_inv, mem_bot]
      constructor
      · intro hy
        calc y = h₀ * (h₀⁻¹ * y * h₀) * h₀⁻¹ := by group
          _ = 1 := by rw [hy]; group
      · intro hy
        rw [hy]
        group
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
  have hTsyl : IsSylowOf 2 (rightConjugate T₀ h₀)
      (rightConjugate K h₀ ⊓ normalizer (L : Set G)) :=
    hT₀hK.of_le (le_inf hT₀hK.le hTM) inf_le_left
  have hLK := hF.lemma33Two G L hA (S' ⊓ K) hR h₀ hh₀M (rightConjugate T₀ h₀) hTsyl hT1 hTR
    hT₀hK
  exact ⟨h₀, hh₀M, le_inf hT₀h hLK, hbot⟩

end Sec3

end CFSG.ComponentClassification.GMS78
