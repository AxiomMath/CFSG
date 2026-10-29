module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2F
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2False
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Layer
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Normal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

namespace Case2Data

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem cc_mem_zOf {z : Y} : z ∈ zOf T ↔ z ∈ T ∧ ∀ g ∈ T, g * z = z * g := by
  unfold zOf
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

private theorem cc_conj_mem_centralizer {L : Subgroup Y} {g c : Y}
    (hg : g ∈ normalizer (L : Set Y)) (hc : c ∈ centralizer (L : Set Y)) :
    g * c * g⁻¹ ∈ centralizer (L : Set Y) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hm : g⁻¹ * l * g ∈ (L : Set Y) := by
    refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * l * g)).mpr ?_
    rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
    exact hl
  have key := hc (g⁻¹ * l * g) hm
  calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * l := by group

private theorem cc_aux (h : Case2Data p P T D F x) {C : Subgroup Y} (hCle : C ≤ P)
    (hCP : ∀ q ∈ P, ∀ c ∈ C, q * c * q⁻¹ ∈ C) (hCF : ∀ f ∈ F, ∀ c ∈ C, f * c * f⁻¹ ∈ C)
    (hxC : x ∉ C) (hTC : ¬ T ≤ C) : C = ⊥ ∨ C = zOf T := by
  have hCD : C ⊓ D = ⊥ := by
    by_contra hne
    exact hxC (h.x_mem_of_ne_bot (C ⊓ D) inf_le_right hne).1
  have hTP : T ≤ P := h.pdata.T_le
  have hnorm : ∀ t ∈ T, ∀ a ∈ C ⊓ T, t * a * t⁻¹ ∈ C ⊓ T := by
    intro t ht a ha
    exact Subgroup.mem_inf.mpr ⟨hCP t (hTP ht) a (Subgroup.mem_inf.mp ha).1,
      T.mul_mem (T.mul_mem ht (Subgroup.mem_inf.mp ha).2) (T.inv_mem ht)⟩
  have hA : C ⊓ T = ⊥ ∨ C ⊓ T = zOf T := by
    by_cases hA0 : C ⊓ T = ⊥
    · exact Or.inl hA0
    · right
      haveI := h.fact
      haveI : Group.IsNilpotent (↥T) := (IsPGroup.of_card (p := p) h.pdata.T_card).isNilpotent
      haveI : ((C ⊓ T).subgroupOf T).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hnorm _ g.2 _ hn⟩
      have hAne : (C ⊓ T).subgroupOf T ≠ ⊥ := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr inf_le_right]
        exact hA0
      have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥T) hAne
      have hK : (C ⊓ T) ⊓ zOf T ≠ ⊥ := by
        intro hK0
        apply hcen
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨hzA, hzc⟩ := Subgroup.mem_inf.mp hz
        have hzY : (z : Y) ∈ (C ⊓ T) ⊓ zOf T := by
          refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hzA,
            cc_mem_zOf.mpr ⟨z.2, fun g hg => ?_⟩⟩
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨g, hg⟩)
        rw [hK0, Subgroup.mem_bot] at hzY
        rw [Subgroup.mem_bot]
        exact Subtype.ext hzY
      have hzle : zOf T ≤ C ⊓ T := by
        have hdvd : Nat.card ((C ⊓ T) ⊓ zOf T : Subgroup Y) ∣ Nat.card (zOf T) :=
          Subgroup.card_dvd_of_le inf_le_right
        rw [h.zOf_card] at hdvd
        rcases (Nat.dvd_prime h.prime).mp hdvd with h1 | h1
        · exact absurd (Subgroup.card_eq_one.mp h1) hK
        · have heq : (C ⊓ T) ⊓ zOf T = zOf T :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [h.zOf_card, h1]))
          rw [← heq]
          exact inf_le_left
      rcases h.torus.irred (C ⊓ T) inf_le_right hzle (fun f hf a ha =>
          Subgroup.mem_inf.mpr ⟨hCF f hf a (Subgroup.mem_inf.mp ha).1,
            h.torus.F_T f hf a (Subgroup.mem_inf.mp ha).2⟩) with h1 | h1
      · exact h1
      · exfalso
        apply hTC
        intro t ht
        have htC : t ∈ C ⊓ T := by
          rw [h1]
          exact ht
        exact (Subgroup.mem_inf.mp htC).1
  have hkey : ∀ t ∈ T, ∀ d ∈ D, ∀ f ∈ F,
      t⁻¹ * (f * t * f⁻¹) = (t * d)⁻¹ * (f * (t * d) * f⁻¹) := by
    intro t ht d hd f hf
    have hfd : f * d * f⁻¹ = d := h.F_D f hf d hd
    have hcomm : (t⁻¹ * (f * t * f⁻¹)) * d = d * (t⁻¹ * (f * t * f⁻¹)) :=
      h.pdata.comm _ (T.mul_mem (T.inv_mem ht) (h.torus.F_T f hf t ht)) d hd
    calc t⁻¹ * (f * t * f⁻¹) = d⁻¹ * (d * (t⁻¹ * (f * t * f⁻¹))) := by group
      _ = d⁻¹ * ((t⁻¹ * (f * t * f⁻¹)) * d) := by rw [hcomm]
      _ = (t * d)⁻¹ * (f * (t * d) * f⁻¹) := by
        rw [show f * (t * d) * f⁻¹ = (f * t * f⁻¹) * (f * d * f⁻¹) by group, hfd]
        group
  have hZ : ∀ c ∈ C, ∀ t ∈ T, ∀ d ∈ D, c = t * d → t ∈ zOf T := by
    intro c hc t ht d hd hcd
    have hw : ∀ f ∈ F, t⁻¹ * (f * t * f⁻¹) ∈ zOf T := by
      intro f hf
      have hwC : t⁻¹ * (f * t * f⁻¹) ∈ C := by
        rw [hkey t ht d hd f hf, ← hcd]
        exact C.mul_mem (C.inv_mem hc) (hCF f hf c hc)
      have hwT : t⁻¹ * (f * t * f⁻¹) ∈ T := T.mul_mem (T.inv_mem ht) (h.torus.F_T f hf t ht)
      have hwCT : t⁻¹ * (f * t * f⁻¹) ∈ C ⊓ T := Subgroup.mem_inf.mpr ⟨hwC, hwT⟩
      rcases hA with h0 | h0
      · rw [h0, Subgroup.mem_bot] at hwCT
        rw [hwCT]
        exact (zOf T).one_mem
      · rw [h0] at hwCT
        exact hwCT
    apply h.torus.fpf t ht
    intro f hf
    have hw' := hw f hf
    have hcomm : t * (t⁻¹ * (f * t * f⁻¹)) = (t⁻¹ * (f * t * f⁻¹)) * t :=
      (cc_mem_zOf.mp hw').2 t ht
    have hfix : f * t * f⁻¹ * t⁻¹ = t⁻¹ * (f * t * f⁻¹) := by
      calc f * t * f⁻¹ * t⁻¹ = t * (t⁻¹ * (f * t * f⁻¹)) * t⁻¹ := by group
        _ = (t⁻¹ * (f * t * f⁻¹)) * t * t⁻¹ := by rw [hcomm]
        _ = t⁻¹ * (f * t * f⁻¹) := by group
    rw [hfix]
    exact hw'
  rcases hA with h0 | h0
  · left
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨t, ht, d, hd, hcd⟩ := h.exists_mul c (hCle hc)
    have htZ := hZ c hc t ht d hd hcd
    have hfix : ∀ f ∈ F, f * t * f⁻¹ = t := by
      intro f hf
      have hw : t⁻¹ * (f * t * f⁻¹) ∈ C ⊓ T := by
        refine Subgroup.mem_inf.mpr ⟨?_, T.mul_mem (T.inv_mem ht) (h.torus.F_T f hf t ht)⟩
        rw [hkey t ht d hd f hf, ← hcd]
        exact C.mul_mem (C.inv_mem hc) (hCF f hf c hc)
      rw [h0, Subgroup.mem_bot] at hw
      calc f * t * f⁻¹ = t * (t⁻¹ * (f * t * f⁻¹)) := by group
        _ = t := by rw [hw, mul_one]
    have ht1 : t = 1 := h.F_fixed t htZ hfix
    have hcD : c ∈ C ⊓ D := Subgroup.mem_inf.mpr ⟨hc, by rw [hcd, ht1, one_mul]; exact hd⟩
    rw [hCD, Subgroup.mem_bot] at hcD
    exact Subgroup.mem_bot.mpr hcD
  · right
    apply le_antisymm
    · intro c hc
      obtain ⟨t, ht, d, hd, hcd⟩ := h.exists_mul c (hCle hc)
      have htZ := hZ c hc t ht d hd hcd
      have htC : t ∈ C := by
        have htCT : t ∈ C ⊓ T := by
          rw [h0]
          exact htZ
        exact (Subgroup.mem_inf.mp htCT).1
      have hdC : d ∈ C := by
        have hde : d = t⁻¹ * c := by rw [hcd, inv_mul_cancel_left]
        rw [hde]
        exact C.mul_mem (C.inv_mem htC) hc
      have hdCD : d ∈ C ⊓ D := Subgroup.mem_inf.mpr ⟨hdC, hd⟩
      rw [hCD, Subgroup.mem_bot] at hdCD
      have hct : c = t := by rw [hcd, hdCD, mul_one]
      rw [hct]
      exact htZ
    · rw [← h0]
      exact inf_le_left

theorem centralizer_cases (h : Case2Data p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hTL : ¬ T ≤ centralizer (L : Set Y)) :
    P ⊓ centralizer (L : Set Y) = ⊥ ∨ P ⊓ centralizer (L : Set Y) = zOf T := by
  have hPN : P ≤ normalizer (L : Set Y) := h.P_le_normalizer hL
  refine cc_aux (C := P ⊓ centralizer (L : Set Y)) h inf_le_left ?_ ?_ ?_ ?_
  · intro q hq c hc
    exact Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem hq (Subgroup.mem_inf.mp hc).1) (P.inv_mem hq),
      cc_conj_mem_centralizer (hPN hq) (Subgroup.mem_inf.mp hc).2⟩
  · intro f hf c hc
    exact Subgroup.mem_inf.mpr ⟨h.F_mem_normalizer_P f hf c (Subgroup.mem_inf.mp hc).1,
      cc_conj_mem_centralizer (h.F_mem_normalizer hL hf) (Subgroup.mem_inf.mp hc).2⟩
  · intro hx
    apply h.not_le_centralizer_x hL
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl).symm
  · intro hT
    exact hTL (fun t ht => (Subgroup.mem_inf.mp (hT ht)).2)

end Case2Data

theorem case2_core {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}
    (h : Case2Data p P T D F x) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (h123 : KFactWeakClosureHeis) : ∀ y : Y, ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
  have hT : T ≤ CFSG.pCore p Y := by
    by_contra hnot
    have hex : ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ ¬ T ≤ centralizer (L : Set Y) := by
      by_contra hne
      push Not at hne
      exact hnot (h.le_pCore_of_forall_le_centralizer hne)
    obtain ⟨L, hL, hTL⟩ := hex
    rcases h.centralizer_cases hL hTL with hC | hC
    · exact h.false_of_faithful h123 hL hC
    · exact h.false_of_abelian (kFactWeakClosureRank2_of hInn hWC) hL hC
  exact h.normal_of_le_pCore hT

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
