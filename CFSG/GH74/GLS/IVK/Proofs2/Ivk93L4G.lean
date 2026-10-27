module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OrdG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelLU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

structure Ivk93OneClassRes : Prop where
  g2 : ∀ (G : Type) [Group G] [Finite G] (z : G) (ε : Bool) (S : Subgroup G) (q : ℕ)
      (L₁ L₂ : Subgroup (CentralizerBar z)), Stage2Ctx G z (Kind.l4 ε) S →
      Stage1L4 G z S ε q L₁ L₂ → (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
      ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
        IsSimpleGroup ↥(generalizedFitting (HBar H)) →
        (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) → PerfInJ H →
        HasTwoInvolutionClasses (HBar H) →
        ∀ p f : ℕ, p ^ f = q → ¬ LieModel ↥(generalizedFitting (HBar H)) .G2 0 p f
  mismatch : ∀ (G : Type) [Group G] [Finite G] (z : G) (ε : Bool) (S : Subgroup G) (q : ℕ)
      (L₁ L₂ : Subgroup (CentralizerBar z)), Stage2Ctx G z (Kind.l4 ε) S →
      Stage1L4 G z S ε q L₁ L₂ → (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
      ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
        IsSimpleGroup ↥(generalizedFitting (HBar H)) →
        (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) → PerfInJ H →
        HasTwoInvolutionClasses (HBar H) →
        ∀ p f : ℕ, p ^ f = q →
          ¬ (if ε then LieModel ↥(generalizedFitting (HBar H)) .PSU 4 p f
              else LieModel ↥(generalizedFitting (HBar H)) .PSL 4 p f)


section L4

theorem ivk93_l4 (h93 : Ivk93Pair) (hres : Ivk93OneClassRes) {ε : Bool}
    (hctx : Stage2Ctx G z (Kind.l4 ε) S) {H : Subgroup G} (hne : H ≠ ⊤) (hCH : Cen z ≤ H)
    (hV : pCore 2 (HBar H) = ⊥) (hs : IsSimpleGroup ↥(generalizedFitting (HBar H)))
    (hn : ∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) (hPerf : PerfInJ H)
    (h2 : HasTwoInvolutionClasses (HBar H)) : C0 z (Kind.l4 ε) S H ∨ FUS H := by
  have hz2 := hctx.orderOf_z
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  obtain ⟨q, L₁, L₂, hp⟩ : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      Stage1L4 G z S ε q L₁ L₂ := by
    cases hctx.data with
    | l4 _ h => exact h
  obtain ⟨hzJ, L₁', L₂', hcfg⟩ := exists_cfg hz2 hCH hPerf hp.pair
  have hcen := isCentralInvolution_zbar hctx hCH hzJ
  have hGH := ghList_J hctx hne hs hn
  have hconcl := h93 ↥(generalizedFitting (HBar H)) hs hGH _ hcen q L₁' L₂' hcfg
  obtain ⟨T, hT⟩ := exists_sylow_barIn hctx hCH
  have hTcard : Nat.card ↥(T : Subgroup (HBar H)) = 2 ^ nuQ q * 4 := by
    rw [hT, card_barIn_S hctx hCH]
    exact card_S_l4 hctx hp
  have hq5 : 5 ≤ q := by
    obtain ⟨m, hm⟩ := hp.pair.odd
    have := hp.pair.gt3
    omega
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  have hpos : 0 < 2 ^ nuQ q := pow_pos (by norm_num) _
  have hC0 : IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q → C0 z (Kind.l4 ε) S H := by
    intro hpsp
    obtain ⟨y, b, -, -, -, hb, hbpsp, hcard⟩ :=
      jm_apply hctx hCH hzJ hp.pair.odd hq5 (Or.inl hpsp) T hT
    have hb2 : b = 2 := by
      rcases hb with h | h
      · exact h
      · exact absurd (hbpsp.2 hpsp) (by omega)
    subst hb2
    refine ⟨ε, q, L₁, L₂, rfl, hp, hp.pair.gt3, hpsp, ?_, ?_⟩
    · intro hle
      rw [← hT] at hle
      have heq : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) = (T : Subgroup (HBar H)) :=
        inf_eq_left.2 hle
      rw [heq, hTcard] at hcard
      omega
    · obtain ⟨N, hN, -, hidx⟩ := exists_index_two_of_sylow_card (J := generalizedFitting (HBar H)) T
        (by rw [hcard, hTcard]; ring)
      exact O2Of_ne_of_index_two hN hidx
  have hxz : ∀ {x : G}, TwoClassData G z S L₁ L₂ q x → ¬ IsConj z x := fun {x} hx h => hx.x_nonCentral (by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have := isCentralInvolution_of_equiv (MulAut.conj c) hctx.central
    have hx' : (MulAut.conj c) z = x := by
      show c * z * c⁻¹ = x
      exact hc
    rwa [hx'] at this)
  have hFUS : IVK.IsSp4L4U4 ↥(generalizedFitting (HBar H)) q → ¬ IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q →
      ∀ {x : G}, TwoClassData G z S L₁ L₂ q x → FUS H := by
    intro hK hnpsp x hx
    obtain ⟨y, b, hy2, hyz, hcl, hb, hbpsp, hcard⟩ := jm_apply hctx hCH hzJ hp.pair.odd hq5 hK T hT
    have hb4 : b = 4 := by
      rcases hb with h | h
      · exact absurd (hbpsp.1 h) hnpsp
      · exact h
    subst hb4
    have hTJ : (T : Subgroup (HBar H)) ≤ generalizedFitting (HBar H) := by
      have heq : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) = (T : Subgroup (HBar H)) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hTcard])
      rw [← heq]
      exact inf_le_right
    have hxH : x ∈ H := hCH (hctx.S_le_Cen hx.x_mem)
    exact fus_of_J_two_classes hzmem hxH hz2 hx.x_inv (hxz hx) hx.classes T hTJ hzJ hcl
  have hLU : ∀ {p f : ℕ}, p.Prime → p ≠ 2 → p ^ f = q →
      ((p ^ f % 8 ≠ 1 ∧ LieModel ↥(generalizedFitting (HBar H)) .PSL 4 p f) ∨
        (p ^ f % 8 ≠ 7 ∧ LieModel ↥(generalizedFitting (HBar H)) .PSU 4 p f)) →
      (T : Subgroup (HBar H)) ≤ generalizedFitting (HBar H) := by
    intro p f hp' hp2 hpf hK
    obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal T (N := generalizedFitting (HBar H))
    have hzP : (⟨mkH H ⟨z, hzmem⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) ∈
        (P : Subgroup ↥(generalizedFitting (HBar H))) := by
      rw [hP, Subgroup.mem_subgroupOf]
      exact ⟨by rw [hT]; exact zbar_mem_barIn hctx hCH, hzJ⟩
    have hzc : ∀ s ∈ (P : Subgroup ↥(generalizedFitting (HBar H))),
        s * (⟨mkH H ⟨z, hzmem⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) =
          ⟨mkH H ⟨z, hzmem⟩, hzJ⟩ * s := by
      intro s hs
      rw [hP, Subgroup.mem_subgroupOf] at hs
      exact Subtype.ext (zbar_comm_barIn hctx hCH (hT ▸ hs.1))
    have hcardP := jm_card_lu hp' hp2 (hpf ▸ hq5) hK P hzP hcen.1 hzc
    rw [hpf] at hcardP
    have hcardinf : Nat.card ↥((T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H)) =
        2 ^ nuQ q * 4 := by
      rw [← hcardP, hP]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) ≤ generalizedFitting (HBar H))).toEquiv).symm
    have heq : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) = (T : Subgroup (HBar H)) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardinf, hTcard])
    rw [← heq]
    exact inf_le_right
  have hone_false : (T : Subgroup (HBar H)) ≤ generalizedFitting (HBar H) →
      (∀ a b : ↥(generalizedFitting (HBar H)), orderOf a = 2 → orderOf b = 2 → IsConj a b) → False := by
    intro hTJ hJone
    obtain ⟨a, b, ha, hb, hab⟩ := h2
    have hodd := index_odd_of_sylow_le T hTJ
    have haJ := involution_mem_of_odd_index hodd ha
    have hbJ := involution_mem_of_odd_index hodd hb
    have := MonoidHom.map_isConj (generalizedFitting (HBar H)).subtype
      (hJone ⟨a, haJ⟩ ⟨b, hbJ⟩ (by rw [← Subgroup.orderOf_coe]; exact ha)
        (by rw [← Subgroup.orderOf_coe]; exact hb))
    exact hab this
  rcases hp.fusion with ⟨hq4one, hone⟩ | ⟨hq4two, x, hx, -, -⟩
  ·
    rcases hconcl with hPsp | ⟨p, f, hp', hp2, hf, hpf, h8, hm⟩ | ⟨p, f, hp', hp2, hf, hpf, h8, hm⟩ |
      ⟨p, f, hp', hp2, hf, hpf, hm⟩
    · exact Or.inl (hC0 hPsp)
    · exfalso
      by_cases h4 : q % 4 = 3
      · have hε : ε = false := by
          rcases ε with _ | _
          · rfl
          · simp at hq4one
            omega
        subst hε
        exact hres.mismatch G z false S q L₁ L₂ hctx hp hone H hne hCH hV hs hn hPerf h2 p f hpf
          (by simpa using hm)
      · have h58 : p ^ f % 8 = 5 := by
          obtain ⟨m, hm'⟩ := hp.pair.odd
          have : q % 8 ≠ 1 := h8
          rw [hpf]
          omega
        exact hone_false (hLU hp' hp2 hpf (Or.inl ⟨by omega, hm⟩))
          (CFSG.GH74.GLS.Stage2.Final.modelOneClass _ p f hp' hp2 (Or.inl ⟨h58, hm⟩))
    · exfalso
      by_cases h4 : q % 4 = 1
      · have hε : ε = true := by
          rcases ε with _ | _
          · simp at hq4one
            omega
          · rfl
        subst hε
        exact hres.mismatch G z true S q L₁ L₂ hctx hp hone H hne hCH hV hs hn hPerf h2 p f hpf
          (by simpa using hm)
      · have h38 : p ^ f % 8 = 3 := by
          obtain ⟨m, hm'⟩ := hp.pair.odd
          have : q % 8 ≠ 7 := h8
          rw [hpf]
          omega
        exact hone_false (hLU hp' hp2 hpf (Or.inr ⟨by omega, hm⟩))
          (CFSG.GH74.GLS.Stage2.Final.modelOneClass _ p f hp' hp2 (Or.inr ⟨h38, hm⟩))
    · exfalso
      exact hres.g2 G z ε S q L₁ L₂ hctx hp hone H hne hCH hV hs hn hPerf h2 p f hpf hm
  ·
    rcases hconcl with hPsp | ⟨p, f, hp', hp2, hf, hpf, h8, hm⟩ | ⟨p, f, hp', hp2, hf, hpf, h8, hm⟩ |
      ⟨p, f, hp', hp2, hf, hpf, hm⟩
    · exact Or.inl (hC0 hPsp)
    · have hL : IVK.IsLnEps 4 ↥(generalizedFitting (HBar H)) 1 q := hpf ▸
        CFSG.GH74.GLS.Stage2.Final.isLnEps_psl_of_lieModel hm
      by_cases h4 : q % 4 = 3
      · refine Or.inr (hFUS (Or.inr (Or.inl ⟨h4, hL⟩)) ?_ hx)
        intro hpsp
        exact (CFSG.GH74.GLS.Stage2.Final.ivk_PSp4_ne_LU _ q hpsp).1 hL
      · exfalso
        have h58 : p ^ f % 8 = 5 := by
          obtain ⟨m, hm'⟩ := hp.pair.odd
          have : q % 8 ≠ 1 := h8
          rw [hpf]
          omega
        exact false_of_J_one_class hctx hCH hPerf hp.pair hx
          (CFSG.GH74.GLS.Stage2.Final.modelOneClass _ p f hp' hp2 (Or.inl ⟨h58, hm⟩))
    · have hU : IVK.IsLnEps 4 ↥(generalizedFitting (HBar H)) (-1) q := hpf ▸
        CFSG.GH74.GLS.Stage2.Final.isLnEps_psu_of_lieModel hm
      by_cases h4 : q % 4 = 1
      · refine Or.inr (hFUS (Or.inr (Or.inr ⟨h4, hU⟩)) ?_ hx)
        intro hpsp
        exact (CFSG.GH74.GLS.Stage2.Final.ivk_PSp4_ne_LU _ q hpsp).2 hU
      · exfalso
        have h38 : p ^ f % 8 = 3 := by
          obtain ⟨m, hm'⟩ := hp.pair.odd
          have : q % 8 ≠ 7 := h8
          rw [hpf]
          omega
        exact false_of_J_one_class hctx hCH hPerf hp.pair hx
          (CFSG.GH74.GLS.Stage2.Final.modelOneClass _ p f hp' hp2 (Or.inr ⟨h38, hm⟩))
    · exfalso
      exact false_of_J_one_class hctx hCH hPerf hp.pair hx (g2_one_class hp' hp2 hm)

end L4

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
