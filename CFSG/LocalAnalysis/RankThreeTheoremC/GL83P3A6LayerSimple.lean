module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerData
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerOrbit
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod CFSG.ComponentClassification

namespace XData

variable {X : Type} [Group X] [Finite X] {P : Subgroup X} {x e₂ e₃ t ρ : X} {s : ℤ}
  (hd : XData X P x e₂ e₃ t ρ s)

include hd

theorem diag_ne_one : x * e₂ * e₃ ≠ 1 := by
  have hf := hd.frame
  intro h1
  rw [← hf.qel_diag, ← Tri.qel_zero hf.toVITriple] at h1
  have := hf.qel_inj h1
  revert this
  decide

theorem diag_mem_of_component {L : Subgroup X} (hL : IsComponentOf L ⊤)
    (hQL : Qf x e₂ e₃ ⊓ L ≠ ⊥) : x * e₂ * e₃ ∈ L := by
  have hf := hd.frame
  have htL := hd.t_mem_normalizer_of_component hL hQL
  have := hf.diag_mem_of_t_invariant (W := Qf x e₂ e₃ ⊓ L) inf_le_left hQL
    (fun w hw => mem_inf.mpr ⟨hf.conj_mem_of_mem_normalizer hf.t_mem_normalizer (mem_inf.mp hw).1,
      (mem_normalizer_iff.mp htL w).mp (mem_inf.mp hw).2⟩)
  exact (mem_inf.mp this).2

theorem exists_simple :
    ∃ L : Subgroup X, L.Normal ∧ IsSimpleGroup ↥L ∧ (∃ a b : ↥L, a * b ≠ b * a) ∧
      centralizer (L : Set X) = ⊥ ∧ Qf x e₂ e₃ ≤ L ∧
      ∀ N : Subgroup X, N.Normal → N ≠ ⊥ → L ≤ N := by
  have hf := hd.frame
  have hfree := hd.free
  obtain ⟨L, hL, h3⟩ := hd.exists_component_three
  have hQL : Qf x e₂ e₃ ⊓ L ≠ ⊥ := hd.inf_ne_bot_of_three hL h3
  have htL := hd.t_mem_normalizer_of_component hL hQL
  have hz := hd.diag_mem_of_component hL hQL
  have hρN := hf.ρ_mem_normalizer
  have hρL : ρ ∈ normalizer (L : Set X) := by
    by_contra hρ
    set L' : Subgroup X := L.map (MulAut.conj ρ).toMonoidHom with hL'def
    have hL' := isComponent_map_conj hL ρ
    have hQL' : Qf x e₂ e₃ ⊓ L' ≠ ⊥ := by
      obtain ⟨q, hq, hq1⟩ := ((Qf x e₂ e₃ ⊓ L).bot_or_exists_ne_one).resolve_left hQL
      intro hb
      have hmem : ρ * q * ρ⁻¹ ∈ Qf x e₂ e₃ ⊓ L' :=
        mem_inf.mpr ⟨hf.conj_mem_of_mem_normalizer hρN (mem_inf.mp hq).1,
          ⟨q, (mem_inf.mp hq).2, rfl⟩⟩
      rw [hb, mem_bot] at hmem
      apply hq1
      have e : q = ρ⁻¹ * (ρ * q * ρ⁻¹) * ρ := by group
      rw [e, hmem]
      group
    have hz' := hd.diag_mem_of_component hL' hQL'
    have hne : L ≠ L' := fun h => hρ (mem_normalizer_iff_map_conj.mpr h.symm)
    have hbot := inf_eq_bot_of_le_centralizer hfree hL' (le_centralizer_of_ne hL hL' hne)
    have hmem : x * e₂ * e₃ ∈ L ⊓ L' := mem_inf.mpr ⟨hz, hz'⟩
    rw [hbot, mem_bot] at hmem
    exact hd.diag_ne_one hmem
  have hinv : ∀ g ∈ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X),
      g ∈ normalizer (L : Set X) → ∀ w ∈ Qf x e₂ e₃ ⊓ L, g * w * g⁻¹ ∈ Qf x e₂ e₃ ⊓ L :=
    fun g hg hgL w hw => mem_inf.mpr ⟨hf.conj_mem_of_mem_normalizer hg (mem_inf.mp hw).1,
      (mem_normalizer_iff.mp hgL w).mp (mem_inf.mp hw).2⟩
  have hQle : Qf x e₂ e₃ ≤ L := by
    rcases hf.eq_bot_or_eq_of_invariant (W := Qf x e₂ e₃ ⊓ L) inf_le_left
      (hinv t hf.t_mem_normalizer htL) (hinv ρ hρN hρL) with hb | heq
    · exact absurd hb hQL
    · rw [← heq]
      exact inf_le_right
  have hkey : ∀ g : X, L.map (MulAut.conj g).toMonoidHom = L := by
    intro g
    by_contra hne
    set L' : Subgroup X := L.map (MulAut.conj g).toMonoidHom with hL'def
    have hL' := isComponent_map_conj hL g
    have hc : L ≤ centralizer (L' : Set X) := le_centralizer_of_ne hL hL' (Ne.symm hne)
    have hbot : L ⊓ L' = ⊥ := inf_eq_bot_of_le_centralizer hfree hL' hc
    set Q' : Subgroup X := (Qf x e₂ e₃).map (MulAut.conj g).toMonoidHom with hQ'def
    have hQ'L' : Q' ≤ L' := Subgroup.map_mono hQle
    have hQQ' : Qf x e₂ e₃ ⊓ Q' = ⊥ := le_bot_iff.mp (by rw [← hbot]; exact inf_le_inf hQle hQ'L')
    have hQN : Qf x e₂ e₃ ≤ normalizer (Q' : Set X) :=
      (hQle.trans hc).trans ((Subgroup.centralizer_le hQ'L').trans
        (Subgroup.centralizer_le_normalizer _))
    have hcard := GL83P3A6Syl.card_sup_mul hQN hQQ'
    have hQ'c : Nat.card Q' = 27 := by
      rw [hQ'def, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hf.Q_card
    have hdvd : Nat.card (Qf x e₂ e₃ ⊔ Q' : Subgroup X) ∣ Nat.card X :=
      Subgroup.card_subgroup_dvd_card _
    rw [hcard, hf.Q_card, hQ'c] at hdvd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hidx : ¬ 3 ∣ P.index := by
      have h := (isSylowOf_iff.mp hd.sylow).2.2
      rwa [Subgroup.relIndex_top_right] at h
    have hX : Nat.card X = 81 * P.index := by
      rw [← hd.card]
      exact (Subgroup.card_mul_index P).symm
    rw [hX, show (27 : ℕ) * 27 = 81 * 9 by norm_num] at hdvd
    have h9 : 9 ∣ P.index := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    exact hidx (dvd_trans ⟨3, rfl⟩ h9)
  have hLn : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [← hkey g]
    exact ⟨n, hn, rfl⟩
  haveI := hLn
  refine ⟨L, hLn, RadicalFreeLayer.component_simple hfree L hL, ?_, ?_, hQle,
    fun N hN hne => hd.component_le hL N hN hne⟩
  · by_contra hcom
    push Not at hcom
    exact component_not_comm hL ⟨⟨fun a b => hcom a b⟩⟩
  · by_contra hne
    have hQC := hd.le_of_normal (centralizer (L : Set X)) inferInstance hne
    have hbot := inf_eq_bot_of_le_centralizer hfree hL (le_refl (centralizer (L : Set X)))
    exact hd.Q_ne_bot (le_bot_iff.mp (by rw [← hbot]; exact le_inf hQC hQle))

end XData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
