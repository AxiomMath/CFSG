module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NFa

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g : G} {P U S F M : Subgroup G}

private lemma conj_comm_zpowers {t g v : G} (htg : t * g = g * t) (hgv : g * v = v * g) :
    g * (t * v * t⁻¹) = (t * v * t⁻¹) * g := by
  have hgtinv : g * t⁻¹ = t⁻¹ * g := by
    calc g * t⁻¹ = (t⁻¹ * (t * g)) * t⁻¹ := by group
      _ = (t⁻¹ * (g * t)) * t⁻¹ := by rw [htg]
      _ = t⁻¹ * g := by group
  calc g * (t * v * t⁻¹) = (g * t) * v * t⁻¹ := by group
    _ = (t * g) * v * t⁻¹ := by rw [← htg]
    _ = t * (g * v) * t⁻¹ := by group
    _ = t * (v * g) * t⁻¹ := by rw [hgv]
    _ = t * v * (g * t⁻¹) := by group
    _ = t * v * (t⁻¹ * g) := by rw [hgtinv]
    _ = (t * v * t⁻¹) * g := by group

private lemma conjSub_centEl_le (h : NtTwo t g P U S F M) :
    conjSub t (centEl U g) ≤ conjSub t U := by
  intro b hb
  obtain ⟨w, hw, rfl⟩ := (mem_conjSub_iff' t (centEl U g) b).mp hb
  exact (mem_conjSub_iff' t U _).mpr ⟨w, (show centEl U g ≤ U from inf_le_left) hw, rfl⟩

private lemma centEl_mem_M (h : NtTwo t g P U S F M) {w : G} (hw : w ∈ centEl U g) :
    w ∈ M := by
  obtain ⟨u, hu, hwu⟩ := (y7n_fuFacts h).cls w hw
  have hweq : w = ⁅u, g⁆ := by
    rw [commutatorElement_def, hwu]
    group
  rw [hweq, ← commutatorElement_inv]
  exact M.inv_mem (h.M_comm u (h.wr.le_left.1 hu))

private lemma conjSub_centEl_mem_M (h : NtTwo t g P U S F M) {x : G}
    (hx : x ∈ conjSub t (centEl U g)) : x ∈ M := by
  obtain ⟨w, hw, rfl⟩ := (mem_conjSub_iff' t (centEl U g) x).mp hx
  obtain ⟨u, hu, hwu⟩ := (y7n_fuFacts h).cls w hw
  have htg' : t * g * t⁻¹ = g := by rw [h.tg]; group
  have hconj := conjugate_commutatorElement (g₁ := u) (g₂ := g) (g₃ := t)
  rw [htg'] at hconj
  have hv : t * u * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨u, hu, rfl⟩
  have hweq : w = ⁅u, g⁆ := by
    rw [commutatorElement_def, hwu]
    group
  rw [hweq, hconj, ← commutatorElement_inv]
  exact M.inv_mem (h.M_comm (t * u * t⁻¹) (h.wr.le_left.2 hv))

private lemma card_sup_centEl_conjSub (h : NtTwo t g P U S F M) :
    Nat.card ↥(centEl U g ⊔ conjSub t (centEl U g)) = 64 := by
  have hFU := y7n_fuFacts h
  have hdisj : Disjoint (centEl U g) (conjSub t (centEl U g)) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro a ha
    rw [Subgroup.mem_bot]
    have hmem : a ∈ U ⊓ conjSub t U :=
      ⟨(show centEl U g ≤ U from inf_le_left) ha.1, conjSub_centEl_le h ha.2⟩
    rw [h.wr.direct.2.1, Subgroup.mem_bot] at hmem
    exact hmem
  have hcentAB : conjSub t (centEl U g) ≤ Subgroup.centralizer (centEl U g : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h.wr.direct.2.2 a ((show centEl U g ≤ U from inf_le_left) ha) b (conjSub_centEl_le h hb)
  have hnorm : conjSub t (centEl U g) ≤ Subgroup.normalizer (centEl U g : Set G) :=
    hcentAB.trans (Subgroup.centralizer_le_normalizer _)
  have hcardB : Nat.card (conjSub t (centEl U g)) = 8 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective, hFU.card]
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (centEl U g) (conjSub t (centEl U g)) hnorm hdisj, hFU.card, hcardB]

theorem y7n_M_eq (h : NtTwo t g P U S F M) : M = centEl U g ⊔ conjSub t (centEl U g) := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · exact sup_le (fun w hw => centEl_mem_M h hw) (fun x hx => conjSub_centEl_mem_M h hx)
  · rw [h.M_card, card_sup_centEl_conjSub h]
    norm_num

theorem y7n_M_le_P (h : NtTwo t g P U S F M) : M ≤ P := by
  rw [y7n_M_eq h]
  refine sup_le ?_ ?_
  · exact (show centEl U g ≤ U from inf_le_left).trans h.wr.le_left.1
  · exact (conjSub_centEl_le h).trans h.wr.le_left.2

theorem y7n_g_cent_M (h : NtTwo t g P U S F M) : ∀ m ∈ M, g * m = m * g := by
  rw [y7n_M_eq h]
  have hcentA : centEl U g ≤ Subgroup.centralizer ({g} : Set G) := fun w hw => hw.2
  have hcentB : conjSub t (centEl U g) ≤ Subgroup.centralizer ({g} : Set G) := by
    intro b hb
    obtain ⟨w, hw, rfl⟩ := (mem_conjSub_iff' t (centEl U g) b).mp hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (conj_comm_zpowers h.tg (Subgroup.mem_centralizer_singleton_iff.mp hw.2).symm).symm
  intro m hm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (sup_le hcentA hcentB hm)).symm

theorem y7n_g_notin_P (h : NtTwo t g P U S F M) : g ∉ P := by
  intro hgP
  have hmem : g ∈ S := by
    rw [← h.cent]
    exact ⟨hgP, Subgroup.mem_centralizer_singleton_iff.mpr h.tg.symm⟩
  exact h.sg.g_notin hmem

theorem y7n_J2_facts (h : NtTwo t g P U S F M) :
    IsElemAbelian 2 (M ⊔ zpowers g) ∧ Nat.card ↥(M ⊔ zpowers g) = 2 ^ 7 := by
  have hFU := y7n_fuFacts h
  have hMeq := y7n_M_eq h
  have hAB : IsElemAbelian 2 (centEl U g ⊔ conjSub t (centEl U g)) :=
    hFU.elem.sup_of_commute (hFU.elem.map (MulAut.conj t).toMonoidHom)
      (fun a ha b hb =>
        h.wr.direct.2.2 a ((show centEl U g ≤ U from inf_le_left) ha) b (conjSub_centEl_le h hb))
  have hABg : centEl U g ⊔ conjSub t (centEl U g) ≤ Subgroup.centralizer ({g} : Set G) :=
    sup_le (fun w hw => hw.2)
      (fun b hb => by
        obtain ⟨w, hw, rfl⟩ := (mem_conjSub_iff' t (centEl U g) b).mp hb
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (conj_comm_zpowers h.tg (Subgroup.mem_centralizer_singleton_iff.mp hw.2).symm).symm)
  have hcommZ : ∀ a ∈ centEl U g ⊔ conjSub t (centEl U g), ∀ z ∈ zpowers g,
      a * z = z * a := by
    intro a ha z hz
    have haC : a ∈ Subgroup.centralizer (zpowers g : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hABg ha
    exact (Subgroup.mem_centralizer_iff.mp haC z hz).symm
  have hgne : g ≠ 1 := by
    intro h1
    exact h.sg.g_notin (h1 ▸ S.one_mem)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardZ : Nat.card (zpowers g) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime h.sg.g_sq hgne
  have hnotmemA : g ∉ (centEl U g ⊔ conjSub t (centEl U g)) := by
    intro hg
    exact y7n_g_notin_P h (y7n_M_le_P h (by rw [hMeq]; exact hg))
  constructor
  · rw [hMeq]
    exact hAB.sup_of_commute (isElemAbelian_zpowers h.sg.g_sq) hcommZ
  · rw [hMeq]
    have hdisj : Disjoint (centEl U g ⊔ conjSub t (centEl U g)) (zpowers g) := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      have hHbot : (centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g = ⊥ := by
        have hne : (centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g ≠ zpowers g := by
          intro hEq
          have hg : g ∈ (centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g :=
            hEq.symm ▸ Subgroup.mem_zpowers g
          exact hnotmemA hg.1
        have hle : (centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g ≤ zpowers g :=
          inf_le_right
        have hlt : Nat.card
            ↥((centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g) < 2 := by
          calc Nat.card ↥((centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g)
              < Nat.card ↥(zpowers g) :=
                Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne)
            _ = 2 := hcardZ
        haveI : Nonempty ↥((centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g) := ⟨1⟩
        have hpos : 0 < Nat.card
            ↥((centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g) := Nat.card_pos
        have hcard1 : Nat.card
            ↥((centEl U g ⊔ conjSub t (centEl U g)) ⊓ zpowers g) = 1 := by omega
        exact Subgroup.eq_bot_of_card_eq _ hcard1
      exact Subgroup.mem_bot.mp (hHbot ▸ hx)
    have hnorm : zpowers g ≤ Subgroup.normalizer
        ((centEl U g ⊔ conjSub t (centEl U g) : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      exact (Subgroup.centralizer_le_normalizer _) (by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        exact (y7n_g_cent_M h m (by rw [hMeq]; exact hm)).symm)
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (centEl U g ⊔ conjSub t (centEl U g)) (zpowers g) hnorm hdisj,
      card_sup_centEl_conjSub h, hcardZ]
    norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
