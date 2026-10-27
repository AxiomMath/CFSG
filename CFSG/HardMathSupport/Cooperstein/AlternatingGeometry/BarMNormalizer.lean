module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding

variable {G : Type} [Group G]

theorem barM_mono {M X Y : Subgroup G} (h : X ≤ Y) : barM M X ≤ barM M Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem mem_barM {M Y : Subgroup G} (b : ↥M ⧸ CFSG.pCore 2 ↥M) :
    b ∈ barM M Y ↔ ∃ m : ↥M, (m : G) ∈ Y ∧
      (QuotientGroup.mk m : ↥M ⧸ CFSG.pCore 2 ↥M) = b := by
  unfold barM
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply]

theorem conj_mem_of_normalizes {X S : Subgroup G} (hSX : S ≤ X)
    (hO2 : ∀ x : ↥X, x ∈ CFSG.pCore 2 ↥X → (x : G) ∈ S) {x : ↥X}
    (hx : (QuotientGroup.mk x : ↥X ⧸ CFSG.pCore 2 ↥X) ∈
      Subgroup.normalizer ((barM X S : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set _))
    {s : G} (hs : s ∈ S) : (x : G) * s * (x : G)⁻¹ ∈ S := by
  have hmem : (QuotientGroup.mk (⟨s, hSX hs⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ barM X S :=
    (mem_barM _).2 ⟨⟨s, hSX hs⟩, hs, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 hx _).1 hmem
  obtain ⟨t, ht, htm⟩ := (mem_barM _).1 h1
  have h2 : (QuotientGroup.mk t : ↥X ⧸ CFSG.pCore 2 ↥X) =
      QuotientGroup.mk (x * ⟨s, hSX hs⟩ * x⁻¹) := by
    rw [htm]; simp
  rw [QuotientGroup.eq] at h2
  have h3 := hO2 _ h2
  have h4 : (t : G)⁻¹ * ((x : G) * s * (x : G)⁻¹) ∈ S := h3
  have := S.mul_mem ht h4
  simpa using this

theorem barM_normalizer_inf {X S L : Subgroup G} (hSX : S ≤ X)
    (hO2 : ∀ x : ↥X, x ∈ CFSG.pCore 2 ↥X → (x : G) ∈ S) :
    barM X (Subgroup.normalizer (S : Set G) ⊓ L) =
      Subgroup.normalizer ((barM X S : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set _) ⊓
        barM X L := by
  ext b
  rw [Subgroup.mem_inf, mem_barM, mem_barM]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_inf] at hx
    refine ⟨?_, x, hx.2, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      obtain ⟨m, hm, rfl⟩ := (mem_barM _).1 hc
      refine (mem_barM _).2 ⟨x * m * x⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.1 hx.1 _).1 hm
    · intro hc
      obtain ⟨m, hm, hmc⟩ := (mem_barM _).1 hc
      have hc' : c = QuotientGroup.mk (x⁻¹ * m * x) := by
        have e : c = (QuotientGroup.mk x : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ *
            (QuotientGroup.mk x * c * (QuotientGroup.mk x)⁻¹) * QuotientGroup.mk x := by group
        rw [e, ← hmc]
        simp
      rw [hc']
      refine (mem_barM _).2 ⟨x⁻¹ * m * x, ?_, rfl⟩
      have h' : (x : G)⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem hx.1
      have := (Subgroup.mem_normalizer_iff.1 h' _).1 hm
      simpa using this
  · rintro ⟨hN, x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, hx⟩
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      exact conj_mem_of_normalizes hSX hO2 hN hs
    · intro hs
      have hN' : (QuotientGroup.mk x⁻¹ : ↥X ⧸ CFSG.pCore 2 ↥X) ∈
          Subgroup.normalizer ((barM X S : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set _) := by
        rw [QuotientGroup.mk_inv]; exact inv_mem hN
      have := conj_mem_of_normalizes hSX hO2 hN' hs
      simpa [mul_assoc] using this

theorem barM_inf {X S L : Subgroup G} (hO2 : ∀ x : ↥X, x ∈ CFSG.pCore 2 ↥X → (x : G) ∈ S) :
    barM X (S ⊓ L) = barM X S ⊓ barM X L := by
  apply le_antisymm
  · exact le_inf (barM_mono inf_le_left) (barM_mono inf_le_right)
  · intro b hb
    obtain ⟨hbS, hbL⟩ := Subgroup.mem_inf.1 hb
    obtain ⟨s, hs, hsb⟩ := (mem_barM _).1 hbS
    obtain ⟨l, hl, hlb⟩ := (mem_barM _).1 hbL
    have h0 : (QuotientGroup.mk s : ↥X ⧸ CFSG.pCore 2 ↥X) = QuotientGroup.mk l :=
      hsb.trans hlb.symm
    rw [QuotientGroup.eq] at h0
    have h1 : ((s⁻¹ * l : ↥X) : G) ∈ S := hO2 _ h0
    have hlS : (l : G) ∈ S := by
      have := S.mul_mem hs h1
      simpa using this
    exact (mem_barM _).2 ⟨l, Subgroup.mem_inf.2 ⟨hlS, hl⟩, hlb⟩

theorem isPGroup_pCoreOf (H : Subgroup G) : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) := by
  unfold CFSG.Open.pCoreOf
  exact CFSG.pCore_isPGroup.map _

theorem le_pCoreOf_of_normalized {K A : Subgroup G} (hAK : A ≤ K)
    (hnorm : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A) (hp : IsPGroup 2 A) :
    A ≤ CFSG.Open.pCoreOf 2 K := by
  unfold CFSG.Open.pCoreOf
  intro a ha
  have hN : (A.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact hnorm g g.2 n hn
  have hP : IsPGroup 2 (A.subgroupOf K) := hp.comap_subtype
  have hle : A.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hN, hP⟩
  exact ⟨⟨a, hAK ha⟩, hle ha, rfl⟩

theorem pCore_le_of_isTwoRadicalIn [Finite G] {X S : Subgroup G}
    (h : CFSG.Quasithin.IsTwoRadicalIn X S) :
    ∀ x : ↥X, x ∈ CFSG.pCore 2 ↥X → (x : G) ∈ S := by
  obtain ⟨hSX, -, hSeq⟩ := h
  set Q : Subgroup G := (CFSG.pCore 2 ↥X).map X.subtype with hQ
  have hQX : Q ≤ X := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup.map X.subtype
  have hconj : ∀ y ∈ X, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := by
    rintro y hy _ ⟨q', hq', rfl⟩
    have := (inferInstance : (CFSG.pCore 2 ↥X).Normal).conj_mem q' hq' ⟨y, hy⟩
    exact ⟨_, this, rfl⟩
  have hSp : IsPGroup 2 S := by
    have := isPGroup_pCoreOf (X ⊓ Subgroup.normalizer (S : Set G))
    rwa [← hSeq] at this
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact fun hq => hconj y hy q hq
    · intro hq
      have := hconj y⁻¹ (inv_mem hy) _ hq
      simpa [mul_assoc] using this
  have hSQ : S ≤ Subgroup.normalizer (Q : Set G) := hSX.trans hXQ
  have hA : Q ⊓ Subgroup.normalizer (S : Set G) ≤ S := by
    have h1 : Q ⊓ Subgroup.normalizer (S : Set G) ≤
        CFSG.Open.pCoreOf 2 (X ⊓ Subgroup.normalizer (S : Set G)) :=
      le_pCoreOf_of_normalized (inf_le_inf_right _ hQX)
        (fun k hk a ha => by
          obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.1 hk
          obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.1 ha
          exact Subgroup.mem_inf.2 ⟨hconj k hk1 a ha1,
            mul_mem (mul_mem hk2 ha2) (inv_mem hk2)⟩) hQp.to_inf_left
    exact h1.trans hSeq.ge
  intro x hx
  have hxQ : (x : G) ∈ Q := ⟨x, hx, rfl⟩
  by_cases hTS : S ⊔ Q ≤ S
  · exact hTS ((le_sup_right : Q ≤ S ⊔ Q) hxQ)
  · exfalso
    set T : Subgroup G := S ⊔ Q with hT
    have hTp : IsPGroup 2 T := hSp.to_sup_of_normal_right' hQp hSQ
    have : Group.IsNilpotent ↥T := hTp.isNilpotent
    have hH : S.subgroupOf T < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact hTS
    obtain ⟨y, hyN, hyH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hH)
    have hyS : ∀ s : G, s ∈ S ↔ (y : G) * s * (y : G)⁻¹ ∈ S := by
      intro s
      have hSle : S ≤ T := le_sup_left
      constructor
      · intro hs
        have := (Subgroup.mem_normalizer_iff.1 hyN ⟨s, hSle hs⟩).1 hs
        exact this
      · intro hs
        have hsT : s ∈ T := by
          have : s = (y : G)⁻¹ * ((y : G) * s * (y : G)⁻¹) * (y : G) := by group
          rw [this]
          exact mul_mem (mul_mem (inv_mem y.2) (hSle hs)) y.2
        exact (Subgroup.mem_normalizer_iff.1 hyN ⟨s, hsT⟩).2 hs
    have hyNS : (y : G) ∈ Subgroup.normalizer (S : Set G) := by
      rw [Subgroup.mem_normalizer_iff]; exact hyS
    have hy2 : (y : G) ∈ ((S ⊔ Q : Subgroup G) : Set G) := y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S Q hSQ] at hy2
    obtain ⟨s, hs, q, hq, hsq⟩ := hy2
    have hqN : q ∈ Subgroup.normalizer (S : Set G) := by
      have : q = s⁻¹ * (y : G) := by rw [← hsq]; group
      rw [this]
      exact mul_mem (inv_mem (Subgroup.le_normalizer hs)) hyNS
    have hqS : q ∈ S := hA ⟨hq, hqN⟩
    exact hyH (by rw [Subgroup.mem_subgroupOf, ← hsq]; exact mul_mem hs hqS)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
