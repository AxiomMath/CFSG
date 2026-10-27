module

public import CFSG.LocalAnalysis.GH72.Sec7Two
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectSubgroupLeTwoResidual
public import CFSG.LocalAnalysis.GH72.GWTwoExtension
public import CFSG.LocalAnalysis.GH72.Sec7Fusion

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Foote81L6.TStruct (IsFourIn)

namespace Sec7

variable {G : Type} [Group G] [Finite G]

theorem isL2OrA7_of_le_quotient {K K₀ K₀' Q : Subgroup G} {L L₂ : Type} [Group L] [Group L₂]
    (hL : IsL2OrA7 L 5) (hK₀K : K₀ ≤ K) (hK₀'n : (K₀'.subgroupOf K).Normal) (hK₀'K : K₀' ≤ K)
    (hOK : O K ≤ K₀') (hQK₀ : Q ≤ K₀) (hQK₀' : Q ≤ K₀') (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (f₁ : K₀ →* L) (hf₁ : Function.Surjective f₁) (hf₁ker : f₁.ker = (O K).subgroupOf K₀)
    (f₁' : K₀' →* L₂) (hf₁' : Function.Surjective f₁') (hf₁'ker : f₁'.ker = (O K).subgroupOf K₀')
    (hL₂ : IsL2OrA7 L₂ 5 ∨ IsKleinFour L₂) : IsL2OrA7 L₂ 5 := by
  have : IsSimpleGroup L := isSimpleGroup_of_isL2OrA7 le_rfl hL
  have : Finite L := Finite.of_surjective f₁ hf₁
  have : Finite L₂ := Finite.of_surjective f₁' hf₁'
  rcases hL₂ with h | h
  · exact h
  exfalso
  have hK₀K₀' : K₀ ≤ K₀' := by
    have hKN : K ≤ normalizer (K₀' : Set G) := (normal_subgroupOf_iff_le_normalizer hK₀'K).mp hK₀'n
    set N := K₀ ⊓ K₀' with hNdef
    have hNn : (N.subgroupOf K₀).Normal :=
      (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
        inf_normalizer_le_normalizer_inf ⟨le_normalizer hk, hKN (hK₀K hk)⟩
    have htop : (N.subgroupOf K₀).map f₁ = ⊤ := by
      have : ((N.subgroupOf K₀).map f₁).Normal := hNn.map f₁ hf₁
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf K₀).map f₁) with hb | ht
      · refine absurd (fun q hq => ?_) (not_le_O_of_isPGroup (H := K) hQ hQ1)
        have h1 : f₁ ⟨q, hQK₀ hq⟩ = 1 := by
          rw [← mem_bot, ← hb]
          exact mem_map_of_mem f₁ (show (⟨q, hQK₀ hq⟩ : K₀) ∈ N.subgroupOf K₀ from
            ⟨hQK₀ hq, hQK₀' hq⟩)
        have h2 : (⟨q, hQK₀ hq⟩ : K₀) ∈ f₁.ker := h1
        rw [hf₁ker] at h2
        exact h2
      · exact ht
    intro k hk
    obtain ⟨n, hn, hnk⟩ := (htop ▸ mem_top (f₁ ⟨k, hk⟩) : f₁ ⟨k, hk⟩ ∈ (N.subgroupOf K₀).map f₁)
    have hz : (n : G)⁻¹ * k ∈ O K := by
      have h1 : n⁻¹ * ⟨k, hk⟩ ∈ f₁.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnk, inv_mul_cancel]
      rw [hf₁ker] at h1
      exact h1
    have : k = n * ((n : G)⁻¹ * k) := by group
    rw [this]
    exact mul_mem hn.2 (hOK hz)
  set φ : K₀ →* L₂ := f₁'.comp (inclusion hK₀K₀') with hφdef
  have hφker : φ.ker = f₁.ker := by
    ext x
    rw [MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hf₁'ker, hf₁ker]
    rfl
  have e : L ≃* φ.range :=
    (QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
        (QuotientGroup.quotientKerEquivRange φ))
  have h1 : Nat.card L ≤ Nat.card L₂ := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.card_le_card_group _
  have h60 := sixty_le_card_of_isL2OrA7 le_rfl hL
  have h4 : Nat.card L₂ = 4 := IsKleinFour.card_four
  omega

theorem exists_M₁_of {S P Q A : Subgroup G} (MP M0P : Subgroup G → Subgroup G)
    (hMP : ∀ A', MP A' = centralizer ((A' ⊓ P : Subgroup G) : Set G))
    (hM0P : ∀ A', M0P A' = ⁅O2 (MP A'), O2 (MP A')⁆ ⊔ O (MP A'))
    (hP : IsDih P) (hQP : Q ≤ centralizer (P : Set G)) (hSP : S ≤ normalizer (P : Set G))
    (hAS : A ≤ S) (hA : IsE16 A) (hXq : IsKleinFour ↥(A ⊓ Q)) (hXp : A ⊓ P ≠ ⊥)
    (hconstr : ∀ V, IsFourIn P V → ∃ A', A' ≤ S ∧ IsE16 A' ∧ A' = V ⊔ (A ⊓ Q) ∧ A' ⊓ P = V ∧
      A' ⊓ Q = A ⊓ Q)
    (hnn : ∀ T : Subgroup G, T ≤ P → T ≠ ⊥ → normalizer (T : Set G) ≠ ⊤)
    (hsimpA : QuotIs (M0P A) (O (MP A)) (fun L _ => IsL2OrA7 L 5))
    (hsimp : ∀ A', A' ≤ S → IsE16 A' → A' ⊓ Q = A ⊓ Q →
      QuotIs (M0P A') (O (MP A')) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L))
    (h49 : ∀ A', A' ≤ S → IsE16 A' → A' ⊓ Q = A ⊓ Q → ∀ T : Subgroup G, T ≤ P → T ≠ ⊥ →
      ∀ K ∈ ({centralizer (T : Set G), normalizer (T : Set G)} : Set (Subgroup G)),
        (K ⊓ M0P A') ⊔ O K ≤ K ∧ (((K ⊓ M0P A') ⊔ O K).subgroupOf K).Normal ∧
          IsSylowOf 2 Q ((K ⊓ M0P A') ⊔ O K) ∧
          QuotIso ((K ⊓ M0P A') ⊔ O K) (O K) (M0P A') (O (MP A')))
    (h411 : ∀ A', A' ≤ S → IsE16 A' → A' ⊓ Q = A ⊓ Q → ∀ q ∈ A' ⊓ Q, q ≠ 1 →
      ∀ D : Subgroup G, D ≤ C q → Odd (Nat.card D) → A' ≤ normalizer (D : Set G) →
        ⁅D, A' ⊓ Q⁆ ≤ O (C q))
    (h413 : ∀ A', A' ≤ S → IsE16 A' → A' ⊓ Q = A ⊓ Q → ∀ H : Subgroup G, H ≠ ⊤ →
      Covers H (M0P A') (O (MP A')) → ∀ p ∈ A' ⊓ P, p ≠ 1 → p ∈ H → O H ⊓ C p ≤ O (C p))
    (h66 : ∀ p q : G, p ∈ P → q ∈ Q → orderOf p = 2 → orderOf q = 2 → O (C p) ⊓ O (C q) = ⊥) :
    ∃ M₁ : Subgroup G, M₁ ≤ MP A ∧ (M₁.subgroupOf (MP A)).Normal ∧ CFSG.Open.IsQuasisimple M₁ ∧
      IsSylowOf 2 Q M₁ ∧ QuotIso M₁ (O M₁) (M0P A) (O (MP A)) ∧
      ∀ T₁ : Subgroup G, T₁ ≤ P → T₁ ≠ ⊥ →
        M₁ ≤ normalizer (T₁ : Set G) ∧ (M₁.subgroupOf (normalizer (T₁ : Set G))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (P : Set G) with hKdef
  have hPne : P ≠ ⊥ := fun h => hXp (eq_bot_iff.mpr (h ▸ inf_le_right))
  have hKmem : K ∈ ({centralizer (P : Set G), normalizer (P : Set G)} : Set (Subgroup G)) :=
    Set.mem_insert _ _
  have hXqQ : A ⊓ Q ≤ Q := inf_le_right
  have hXq2 : IsPGroup 2 ↥(A ⊓ Q) :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hXq1 : A ⊓ Q ≠ ⊥ := by
    intro h
    have := IsKleinFour.card_four (G := ↥(A ⊓ Q))
    rw [h, card_bot] at this
    exact absurd this (by norm_num)
  have hAc : ∀ (B : Subgroup G), IsE16 B → ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun B hB a ha b hb =>
    congrArg Subtype.val (hB.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hord : ∀ (B : Subgroup G), IsE16 B → ∀ a ∈ B, a ≠ 1 → orderOf a = 2 := fun B hB a ha ha1 =>
    orderOf_eq_prime (hB.1.2 a ha) ha1
  have hNPK : normalizer (P : Set G) ≤ normalizer (K : Set G) := fun k hk =>
    mem_normalizer_centralizer hk
  obtain ⟨hK₀K, hK₀n, hK₀syl, hK₀iso⟩ := h49 A hAS hA rfl P le_rfl hPne K hKmem
  set K₀ := (K ⊓ M0P A) ⊔ O K with hK₀def
  obtain ⟨L, _, f₁, f₂, hf₁, hf₂, hf₁ker, hf₂ker⟩ := hK₀iso
  obtain ⟨L', _, h, hh, hhker, hL'⟩ := hsimpA
  obtain ⟨eLL'⟩ := nonempty_mulEquiv_of_ker_eq f₂ hf₂ h hh (hf₂ker.trans hhker.symm)
  have hL : IsL2OrA7 L 5 := isL2OrA7_of_mulEquiv eLL' hL'
  have : IsSimpleGroup L := isSimpleGroup_of_isL2OrA7 le_rfl hL
  have hLperf : commutator L = ⊤ := commutator_eq_top_of_isL2OrA7 le_rfl hL
  have hcov : Covers K (M0P A) (O (MP A)) :=
    covers_of_common_quotient hLperf rfl f₁ hf₁ hf₁ker f₂ hf₂ hf₂ker
  have hNP : normalizer (P : Set G) ≠ ⊤ := hnn P le_rfl hPne
  have hKNP : K ≤ normalizer (P : Set G) := fun c hc =>
    Subgroup.mem_normalizer_fintype fun t ht => by
      rw [(mem_centralizer_iff.mp hc t ht).symm, mul_inv_cancel_right]
      exact ht
  have hOKO : O K ≤ O (normalizer (P : Set G)) :=
    O_le_O_of_normal hKNP ((normal_subgroupOf_iff_le_normalizer hKNP).mpr hNPK)
  obtain ⟨⟨p, hp⟩, hp1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hXp
  have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
  have hpN : p ∈ normalizer (P : Set G) := le_normalizer hp.2
  have hOKp : O K ≤ O (C p) := by
    have h1 := h413 A hAS hA rfl _ hNP (Covers.mono hcov hKNP) p hp hp1' hpN
    refine (le_inf hOKO fun o ho => ?_).trans h1
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (O_le K ho) p hp.2).symm
  have hAK : A ≤ normalizer (O K : Set G) :=
    (hAS.trans hSP).trans (hNPK.trans (normalizer_le_normalizer_O K))
  have hOKodd : Odd (Nat.card (O K)) := card_O_odd K
  have hXqOK : A ⊓ Q ≤ centralizer (O K : Set G) := by
    refine @le_centralizer_of_forall_inf G _ _ (O K) (A ⊓ Q) hXq hOKodd
      (inf_le_left.trans hAK) fun q hq hq1 => ?_
    have hq2 := hord A hA q hq.1 hq1
    have hAD : A ≤ normalizer ((O K ⊓ C q : Subgroup G) : Set G) := fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨hAK ha, Subgroup.mem_normalizer_fintype fun c hc => by
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hc ⊢
        have hay : Commute a q := hAc A hA a ha q hq.1
        calc a * c * a⁻¹ * q = a * c * (a⁻¹ * q) := by group
          _ = a * c * (q * a⁻¹) := by rw [hay.inv_left.eq]
          _ = a * (c * q) * a⁻¹ := by group
          _ = a * (q * c) * a⁻¹ := by rw [hc]
          _ = a * q * c * a⁻¹ := by group
          _ = q * a * c * a⁻¹ := by rw [hay.eq]
          _ = q * (a * c * a⁻¹) := by group⟩
    have h1 := h411 A hAS hA rfl q hq hq1 (O K ⊓ C q) inf_le_right
      (Odd.of_dvd_nat hOKodd (card_dvd_of_le inf_le_left)) hAD
    have h2 : ⁅O K ⊓ C q, A ⊓ Q⁆ ≤ O K := by
      rw [commutator_le]
      intro d hd b hb
      rw [commutatorElement_def]
      have : b * d⁻¹ * b⁻¹ ∈ O K := (mem_normalizer_iff.mp (hAK hb.1) d⁻¹).mp (inv_mem hd.1)
      rw [show d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) by group]
      exact mul_mem hd.1 this
    have h3 : ⁅O K ⊓ C q, A ⊓ Q⁆ = ⊥ := by
      rw [eq_bot_iff, ← h66 p q hp.2 hq.2 (hord A hA p hp.1 hp1') hq2]
      exact le_inf (h2.trans hOKp) h1
    rw [commutator_eq_bot_iff_le_centralizer] at h3
    exact le_centralizer_iff.mp h3
  have hQK₀ : Q ≤ K₀ := hK₀syl.le
  obtain ⟨M₁, hM₁def⟩ : ∃ M₁ : Subgroup G,
      M₁ = ⁅K₀ ⊓ centralizer (O K : Set G), K₀ ⊓ centralizer (O K : Set G)⁆ := ⟨_, rfl⟩
  obtain ⟨hM₁K₀, hM₁c, hM₁n, hperf, hquasi, hOM₁, ⟨g, hg, hgker⟩, hodd⟩ :=
    quasisimple_commutator_of_simple (T := A ⊓ Q) hLperf hK₀K hK₀n f₁ hf₁ hf₁ker
      (hXqQ.trans hQK₀) hXqOK (not_le_O_of_isPGroup hXq2 hXq1) rfl hM₁def
  have hM₁K : M₁ ≤ K := hM₁K₀.trans hK₀K
  have hKM : K ≤ MP A := by
    rw [hMP A]
    exact centralizer_le inf_le_right
  have hM₁M : M₁ ≤ MP A := hM₁K.trans hKM
  have hK₀M₁ : K₀ ≤ normalizer (M₁ : Set G) :=
    hK₀K.trans ((normal_subgroupOf_iff_le_normalizer hM₁K).mp hM₁n)
  have hQM₁ : Q ≤ M₁ := le_of_isSylowOf_of_odd_relIndex hK₀syl hM₁K₀ hK₀M₁ hodd
  have hsyl : IsSylowOf 2 Q M₁ := hK₀syl.of_le hQM₁ hM₁K₀
  have hM₁M₀ : M₁ ≤ M0P A := by
    have h1 := CFSG.GorensteinWalter.perfect_subgroup_le_twoResidualOf (MP A) M₁ hM₁M
      (Subgroup.isPerfect_iff.2 hperf)
    rw [hM0P A]
    calc M₁ = ⁅M₁, M₁⁆ := hperf.symm
      _ ≤ ⁅O2 (MP A), O2 (MP A)⁆ := commutator_mono h1 h1
      _ ≤ _ := le_sup_left
  have hcenM₁ : O M₁ ≤ centralizer (M₁ : Set G) := by
    rw [hOM₁]
    exact inf_le_right.trans (le_centralizer_iff.mp hM₁c)
  have hiii : ∀ T₁ : Subgroup G, T₁ ≤ P → T₁ ≠ ⊥ →
      M₁ ≤ normalizer (T₁ : Set G) ∧ (M₁.subgroupOf (normalizer (T₁ : Set G))).Normal := by
    intro T₁ hT₁P hT₁
    have hM₁T₁ : M₁ ≤ normalizer (T₁ : Set G) := by
      refine hM₁K.trans ((centralizer_le hT₁P).trans fun c hc =>
        Subgroup.mem_normalizer_fintype fun t ht => ?_)
      rw [(mem_centralizer_iff.mp hc t ht).symm, mul_inv_cancel_right]
      exact ht
    refine ⟨hM₁T₁, (normal_subgroupOf_iff_le_normalizer hM₁T₁).mpr ?_⟩
    obtain ⟨T', V, hT'T₁, hT'ne, hNT, hV, hT'V⟩ := IsDih.exists_four_le hP hT₁P hT₁
    obtain ⟨Ast, hAstS, hAst, hAsteq, hAstP, hAstQ⟩ := hconstr V hV
    have hT'P : T' ≤ P := hT'T₁.trans hT₁P
    obtain ⟨hK₀K', hK₀n', hK₀syl', hK₀iso'⟩ := h49 Ast hAstS hAst hAstQ P le_rfl hPne K hKmem
    obtain ⟨L₂, _, f₁', f₂', hf₁', hf₂', hf₁'ker, hf₂'ker⟩ := hK₀iso'
    obtain ⟨L₃, _, h₃, hh₃, hh₃ker, hL₃⟩ := hsimp Ast hAstS hAst hAstQ
    obtain ⟨e₂₃⟩ := nonempty_mulEquiv_of_ker_eq f₂' hf₂' h₃ hh₃ (hf₂'ker.trans hh₃ker.symm)
    have hL₂' : IsL2OrA7 L₂ 5 ∨ IsKleinFour L₂ := by
      rcases hL₃ with h' | h'
      · exact Or.inl (isL2OrA7_of_mulEquiv e₂₃ h')
      · have := h'
        exact Or.inr (IsKleinFour.mk ((Nat.card_congr e₂₃.toEquiv).trans IsKleinFour.card_four)
          ((Monoid.exponent_eq_of_mulEquiv e₂₃).trans IsKleinFour.exponent_two))
    have hL₂ : IsL2OrA7 L₂ 5 :=
      isL2OrA7_of_le_quotient hL hK₀K hK₀n' hK₀K' le_sup_right hQK₀ hK₀syl'.le
        (IsSylowOf.isPGroup hK₀syl) (fun h' => hXq1 (eq_bot_iff.mpr (h' ▸ hXqQ))) f₁ hf₁
        hf₁ker f₁' hf₁' hf₁'ker hL₂'
    have : IsSimpleGroup L₂ := isSimpleGroup_of_isL2OrA7 le_rfl hL₂
    have hcov' : Covers K (M0P Ast) (O (MP Ast)) :=
      covers_of_common_quotient (commutator_eq_top_of_isL2OrA7 le_rfl hL₂) rfl f₁' hf₁' hf₁'ker
        f₂' hf₂' hf₂'ker
    obtain ⟨hJ₀J, hJ₀n, -, hJ₀iso⟩ := h49 A hAS hA rfl T' hT'P hT'ne (normalizer (T' : Set G))
      (Set.mem_insert_of_mem _ rfl)
    have hTM := normalizer_le_normalizer_of_four (P := P) (Q := Q) (A := A) (Ast := Ast)
      (M := MP A) hLperf hQP hT'V hT'ne hV hAst hAsteq hAstP hAstQ hXq hXqQ (hnn T' hT'P hT'ne)
      hcov' (h413 Ast hAstS hAst hAstQ) (h411 Ast hAstS hAst hAstQ) h66 rfl hJ₀J hJ₀n hJ₀iso hM₁K
      hM₁M₀ hperf (hXqQ.trans hQM₁) hcenM₁ g hg hgker f₂ hf₂ hf₂ker
    exact hNT.trans hTM
  have hMN : MP A ≤ normalizer (M₁ : Set G) := by
    have h1 := (normal_subgroupOf_iff_le_normalizer (hiii (A ⊓ P) inf_le_right hXp).1).mp
      (hiii (A ⊓ P) inf_le_right hXp).2
    refine le_trans ?_ h1
    rw [hMP A]
    intro c hc
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    rw [(mem_centralizer_iff.mp hc t ht).symm, mul_inv_cancel_right]
    exact ht
  exact ⟨M₁, hM₁M, (normal_subgroupOf_iff_le_normalizer hM₁M).mpr hMN, hquasi, hsyl,
    ⟨L, inferInstance, g, f₂, hg, hf₂, hgker, hf₂ker⟩, hiii⟩

end Sec7

end CFSG.GH72
