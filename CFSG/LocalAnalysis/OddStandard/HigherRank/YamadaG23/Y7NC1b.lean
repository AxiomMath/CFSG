module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NC1a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NXa

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g g0 : G} {P U S F M U0 P0 : Subgroup G}

theorem y7n_c1_J (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0) :
    IsElemAbelian 2 ((centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)) ∧
      Nat.card ↥((centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)) = 2 ^ 8 ∧
      (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0) ≤ P0 ⊔ zpowers t := by
  have hW : Wr7 t P0 U0 := y7n_c1_wr h h1
  obtain ⟨hJ1le, hJ1el, hJ1card⟩ := y7n_c1_J1 h h1
  have hJ1t_le : conjSub t (centEl U g ⊔ zpowers g0) ≤ conjSub t U0 := by
    simpa only [conjSub] using
      (Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hJ1le)
  have hJ1t_el : IsElemAbelian 2 (conjSub t (centEl U g ⊔ zpowers g0)) := by
    simpa only [conjSub] using hJ1el.map (MulAut.conj t).toMonoidHom
  have hJ1t_card : Nat.card ↥(conjSub t (centEl U g ⊔ zpowers g0)) = 16 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective, hJ1card]
  have hcomm : ∀ a ∈ centEl U g ⊔ zpowers g0,
      ∀ b ∈ conjSub t (centEl U g ⊔ zpowers g0), a * b = b * a :=
    fun a ha b hb => hW.direct.2.2 a (hJ1le ha) b (hJ1t_le hb)
  have hdisj : Disjoint (centEl U g ⊔ zpowers g0) (conjSub t (centEl U g ⊔ zpowers g0)) := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ U0 ⊓ conjSub t U0 := ⟨hJ1le hx.1, hJ1t_le hx.2⟩
    rw [hW.direct.2.1, Subgroup.mem_bot] at hx'
    rwa [Subgroup.mem_bot]
  have hcent : conjSub t (centEl U g ⊔ zpowers g0) ≤
      Subgroup.centralizer ((centEl U g ⊔ zpowers g0 : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a ha b hb
  have hnorm : conjSub t (centEl U g ⊔ zpowers g0) ≤
      Subgroup.normalizer ((centEl U g ⊔ zpowers g0 : Subgroup G) : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcard : Nat.card ↥((centEl U g ⊔ zpowers g0) ⊔
      conjSub t (centEl U g ⊔ zpowers g0)) = 2 ^ 8 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (centEl U g ⊔ zpowers g0) (conjSub t (centEl U g ⊔ zpowers g0)) hnorm hdisj,
      hJ1card, hJ1t_card]
    norm_num
  refine ⟨hJ1el.sup_of_commute hJ1t_el hcomm, hcard, ?_⟩
  refine sup_le ?_ ?_
  · exact hJ1le.trans (hW.le_left.1.trans le_sup_left)
  · exact hJ1t_le.trans (hW.le_left.2.trans le_sup_left)

theorem y7n_case1_rank (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0)
    {E : Subgroup G} (hE : E ≤ P0 ⊔ zpowers t) (hel : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ 8 ∧ (Nat.card E = 2 ^ 8 →
      E = (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)) := by
  have hW : Wr7 t P0 U0 := y7n_c1_wr h h1
  have hm : ∀ E' : Subgroup G, E' ≤ U0 → IsElemAbelian 2 E' → Nat.card E' ≤ 16 :=
    fun E' hE' hel' => (y7n_c1_U0_rank h h1 hE' hel').1
  by_cases hEP0 : E ≤ P0
  · obtain ⟨hle, heq⟩ := y7n_card_le_sq hW (m := 16) hm hEP0 hel
    refine ⟨?_, ?_⟩
    · calc Nat.card E ≤ 16 * 16 := hle
        _ = 2 ^ 8 := by norm_num
    · intro hcard
      have hcard' : Nat.card E = 16 * 16 := by
        rw [hcard]
        norm_num
      obtain ⟨hdecomp, hEU0card, hEtcard⟩ := heq hcard'
      have hEU0 : E ⊓ U0 = centEl U g ⊔ zpowers g0 :=
        (y7n_c1_U0_rank h h1 inf_le_right (hel.mono inf_le_left)).2 hEU0card
      have hEt : E ⊓ conjSub t U0 = conjSub t (centEl U g ⊔ zpowers g0) := by
        have hFcard : Nat.card ↥(conjSub t (E ⊓ conjSub t U0)) = 16 := by
          rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective, hEtcard]
        have hFle : conjSub t (E ⊓ conjSub t U0) ≤ U0 := by
          have hle' : conjSub t (E ⊓ conjSub t U0) ≤ conjSub t (conjSub t U0) :=
            Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) inf_le_right
          rwa [conjSub_conjSub_of_sq hW.t_sq U0] at hle'
        have hFel : IsElemAbelian 2 (conjSub t (E ⊓ conjSub t U0)) := by
          simpa only [conjSub] using
            (hel.mono inf_le_left).map (MulAut.conj t).toMonoidHom
        have hFeq : conjSub t (E ⊓ conjSub t U0) = centEl U g ⊔ zpowers g0 :=
          (y7n_c1_U0_rank h h1 hFle hFel).2 hFcard
        have hcongr := congrArg (conjSub t) hFeq
        rwa [conjSub_conjSub_of_sq hW.t_sq (E ⊓ conjSub t U0)] at hcongr
      rw [hdecomp, hEU0, hEt]
  · obtain ⟨x, hxE, hxP0⟩ : ∃ x, x ∈ E ∧ x ∉ P0 := by
      by_contra hcon
      apply hEP0
      intro x hx
      by_contra hxP0
      exact hcon ⟨x, hx, hxP0⟩
    have hxP1 : x ∈ P0 ⊔ zpowers t := hE hxE
    rcases y7n_mem_sup_zpowers hW.t_sq (fun x hx => hW.conj_mem hx) hxP1 with
      hxP0' | ⟨y, hyP0, hxyt⟩
    · exact absurd hxP0' hxP0
    · have hle_two : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ P0) :=
        y7n_card_le_two_mul (N := P0) (E := E) (y := t) hW.t_sq
          (fun n hn => hW.conj_mem hn) hE
      have hcent_le : Nat.card ↥(E ⊓ P0) ≤ 16 := by
        refine y7n_card_cent_le (Q := P0) (V := U0) (x := x) (E := E ⊓ P0) hW (m := 16)
          ?_ ?_ inf_le_right (hel.mono inf_le_left) ?_
        · intro E' hE' hel'
          exact (y7n_c1_U0_rank h h1 hE' hel').1
        · intro v hv
          have htv : t * v * t⁻¹ ∈ U0 := by
            rw [← conjSub_conjSub_of_sq hW.t_sq U0]
            exact (mem_conjSub_iff' t (conjSub t U0) _).mpr ⟨v, hv, rfl⟩
          have hnorm := y7n_Q_normalizes_V hW hyP0 htv
          have hxv : x * v * x⁻¹ = y * (t * v * t⁻¹) * y⁻¹ := by
            rw [hxyt]
            group
          rw [hxv]
          exact hnorm
        · intro e he
          exact hel.comm he.1 hxE
      have h32 : Nat.card E ≤ 32 := by
        calc Nat.card E ≤ 2 * Nat.card ↥(E ⊓ P0) := hle_two
          _ ≤ 2 * 16 := Nat.mul_le_mul_left 2 hcent_le
          _ = 32 := by norm_num
      have hlt : Nat.card E < 2 ^ 8 :=
        lt_of_le_of_lt h32 (by norm_num : (32 : ℕ) < 2 ^ 8)
      exact ⟨h32.trans (by norm_num : (32 : ℕ) ≤ 2 ^ 8),
        fun hcard => absurd hcard (ne_of_lt hlt)⟩

end CFSG.OddStandard.HigherRank.YamadaG23
