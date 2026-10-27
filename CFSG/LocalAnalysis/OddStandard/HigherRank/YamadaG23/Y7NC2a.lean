module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NXa
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NMf

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g : G} {P U S F M : Subgroup G}

private lemma inv_mul_inv_comm {a b : G} (h : a * b = b * a) : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← mul_inv_rev, ← mul_inv_rev, h]

private lemma conj_conjSub_eq_comm {t g v : G} (htg : t * g = g * t) :
    g * (t * v * t⁻¹) * g⁻¹ = t * (g * v * g⁻¹) * t⁻¹ := by
  calc g * (t * v * t⁻¹) * g⁻¹ = (g * t) * v * (t⁻¹ * g⁻¹) := by group
    _ = (t * g) * v * (t⁻¹ * g⁻¹) := by rw [← htg]
    _ = (t * g) * v * (g⁻¹ * t⁻¹) := by rw [inv_mul_inv_comm htg]
    _ = t * (g * v * g⁻¹) * t⁻¹ := by group

private lemma conjSub_eq_of_sq_conj {c : G} (hc : c ^ 2 = 1) {A : Subgroup G}
    (h : ∀ x ∈ A, c * x * c⁻¹ ∈ A) : conjSub c A = A := by
  have hc' : c * c = 1 := by simpa [pow_two] using hc
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_left hc'
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_conjSub_iff' c A x).mp hx
    exact h y hy
  · intro x hx
    rw [mem_conjSub_iff']
    refine ⟨c⁻¹ * x * c, ?_, by group⟩
    have heq : c⁻¹ * x * c = c * x * c⁻¹ := by rw [hcinv]
    rw [heq]
    exact h x hx

private lemma g_norm_P (h : NtTwo t g P U S F M) : ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
  have hgU : conjSub g U = U := conjSub_eq_of_sq_conj h.sg.g_sq h.gU
  have hgU' : conjSub g (conjSub t U) = conjSub t U := by
    apply conjSub_eq_of_sq_conj h.sg.g_sq
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (mem_conjSub_iff' t U v).mp hv
    rw [mem_conjSub_iff']
    exact ⟨g * u * g⁻¹, h.gU u hu, conj_conjSub_eq_comm h.tg⟩
  have hgP : conjSub g P = P := by
    have h1 : conjSub g (U ⊔ conjSub t U) = U ⊔ conjSub t U := by
      change (U ⊔ conjSub t U).map (MulAut.conj g).toMonoidHom = U ⊔ conjSub t U
      rw [Subgroup.map_sup,
        show U.map (MulAut.conj g).toMonoidHom = U from hgU,
        show (conjSub t U).map (MulAut.conj g).toMonoidHom = conjSub t U from hgU']
    rw [h.wr.direct.1] at h1
    exact h1
  intro x hx
  have hmem : g * x * g⁻¹ ∈ conjSub g P :=
    (mem_conjSub_iff' g P _).mpr ⟨x, hx, rfl⟩
  rwa [hgP] at hmem

private lemma P0_le_normalizer_U (h : NtTwo t g P U S F M) :
    P ⊔ zpowers g ≤ Subgroup.normalizer (U : Set G) := by
  refine sup_le ?_ ?_
  · intro q hq
    rw [Subgroup.mem_set_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact y7n_Q_normalizes_V h.wr hq hv
    · intro hv
      have hconj := y7n_Q_normalizes_V h.wr (P.inv_mem hq) hv
      rwa [show q⁻¹ * (q * v * q⁻¹) * (q⁻¹)⁻¹ = v by group] at hconj
  · rw [Subgroup.zpowers_le, Subgroup.mem_set_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact h.gU v hv
    · intro hv
      have hgg : g * g = 1 := by simpa [pow_two] using h.sg.g_sq
      have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_left hgg
      have hconj := h.gU (g * v * g⁻¹) hv
      rwa [show g * (g * v * g⁻¹) * g⁻¹ = v by
        calc g * (g * v * g⁻¹) * g⁻¹ = (g * g) * v * (g⁻¹ * g⁻¹) := by group
          _ = v := by rw [hgg, hginv, hgg]; simp] at hconj

private lemma t_norm_P0 (h : NtTwo t g P U S F M) :
    ∀ x ∈ P ⊔ zpowers g, t * x * t⁻¹ ∈ P ⊔ zpowers g := by
  have htgconj : t * g * t⁻¹ = g := by rw [h.tg]; group
  have hzg : conjSub t (zpowers g) = zpowers g := by
    rw [conjSub, MonoidHom.map_zpowers]
    exact congrArg zpowers (by
      show (MulAut.conj t) g = g
      rw [MulAut.conj_apply, htgconj])
  have hconj : conjSub t (P ⊔ zpowers g) = P ⊔ zpowers g := by
    change (P ⊔ zpowers g).map (MulAut.conj t).toMonoidHom = P ⊔ zpowers g
    rw [Subgroup.map_sup,
      show P.map (MulAut.conj t).toMonoidHom = P from h.wr.conjSub_eq,
      show (zpowers g).map (MulAut.conj t).toMonoidHom = zpowers g from hzg]
  intro x hx
  have hmem : t * x * t⁻¹ ∈ conjSub t (P ⊔ zpowers g) :=
    (mem_conjSub_iff' t (P ⊔ zpowers g) _).mpr ⟨x, hx, rfl⟩
  rwa [hconj] at hmem

theorem y7n_case2_rank (h : NtTwo t g P U S F M) {E : Subgroup G}
    (hE : E ≤ (P ⊔ zpowers g) ⊔ zpowers t) (hel : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ 7 ∧ (Nat.card E = 2 ^ 7 → E = M ⊔ zpowers g) := by
  have hRankU : RankFacts U :=
    RankFacts.of_mulEquiv h.wr.centEquiv.symm (RankFacts.of_eq h.cent.symm h.sg.rank)
  have hm8 : ∀ E' : Subgroup G, E' ≤ U → IsElemAbelian 2 E' → Nat.card E' ≤ 8 :=
    fun E' hE' hEel => hRankU.bound E' hE' hEel
  have hgP : ∀ x ∈ P, g * x * g⁻¹ ∈ P := g_norm_P h
  have hP0N : P ⊔ zpowers g ≤ Subgroup.normalizer (U : Set G) := P0_le_normalizer_U h
  have htP0 : ∀ x ∈ P ⊔ zpowers g, t * x * t⁻¹ ∈ P ⊔ zpowers g := t_norm_P0 h
  by_cases hEP0 : E ≤ P ⊔ zpowers g
  · by_cases hEP : E ≤ P
    ·
      have hsq := (y7n_card_le_sq h.wr (m := 8) hm8 hEP hel).1
      have hle64 : Nat.card E ≤ 64 := by simpa using hsq
      refine ⟨hle64.trans (by norm_num), ?_⟩
      intro hcard
      have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
      omega
    ·
      obtain ⟨x, hxE, hxP⟩ := IsConcreteLE.not_le_iff_exists.mp hEP
      have hxP0 : x ∈ P ⊔ zpowers g := hEP0 hxE
      rcases y7n_mem_sup_zpowers h.sg.g_sq hgP hxP0 with hxP' | ⟨p, hp, hxpg⟩
      · exact absurd hxP' hxP
      · have hp2 : (p * g) ^ 2 = 1 := by rw [← hxpg]; exact hel.2 x hxE
        have hpM : p ∈ M := y7n_inv_mem_M h hp hp2
        have hpgE : p * g ∈ E := hxpg ▸ hxE
        have hEinfPM : E ⊓ P ≤ M := fun y hy =>
          y7n_cent_le_M h hp hp2 hy.2 (hel.comm hy.1 hpgE)
        have hleEinfP : Nat.card ↥(E ⊓ P) ≤ 2 ^ 6 := by
          have hcardM := Subgroup.card_le_of_le hEinfPM
          rwa [h.M_card] at hcardM
        have hb2 := y7n_card_le_two_mul (N := P) (E := E) h.sg.g_sq hgP hEP0
        have hbound : Nat.card E ≤ 2 ^ 7 :=
          calc Nat.card E ≤ 2 * Nat.card ↥(E ⊓ P) := hb2
            _ ≤ 2 * 2 ^ 6 := Nat.mul_le_mul_left 2 hleEinfP
            _ = 2 ^ 7 := by norm_num
        refine ⟨hbound, ?_⟩
        intro hcard
        have hge : 2 ^ 6 ≤ Nat.card ↥(E ⊓ P) := by
          have h2 : (2 : ℕ) ^ 7 ≤ 2 * Nat.card ↥(E ⊓ P) := by rw [← hcard]; exact hb2
          have h7 : (2 : ℕ) ^ 7 = 2 * 2 ^ 6 := by norm_num
          omega
        have hcardEq : Nat.card ↥(E ⊓ P) = 2 ^ 6 := le_antisymm hleEinfP hge
        have hEinfP_eq_M : E ⊓ P = M :=
          Subgroup.eq_of_le_of_card_ge hEinfPM (by rw [hcardEq, h.M_card])
        have hMleE : M ≤ E := by rw [← hEinfP_eq_M]; exact inf_le_left
        have hgE : g ∈ E := by
          have hgpx : g = p⁻¹ * x := by rw [hxpg]; group
          rw [hgpx]
          exact E.mul_mem (hMleE (M.inv_mem hpM)) hxE
        have hJle : M ⊔ zpowers g ≤ E := sup_le hMleE (Subgroup.zpowers_le.mpr hgE)
        exact (Subgroup.eq_of_le_of_card_ge hJle (by rw [hcard, (y7n_J2_facts h).2])).symm
  ·
    obtain ⟨x, hxE, hxP0⟩ := IsConcreteLE.not_le_iff_exists.mp hEP0
    have hxsup : x ∈ (P ⊔ zpowers g) ⊔ zpowers t := hE hxE
    rcases y7n_mem_sup_zpowers h.wr.t_sq htP0 hxsup with hxP0' | ⟨q, hqP0, hxqt⟩
    · exact absurd hxP0' hxP0
    · have hxU : ∀ v ∈ conjSub t U, x * v * x⁻¹ ∈ U := by
        intro v hv
        have htv : t * v * t⁻¹ ∈ U := by
          obtain ⟨u, hu, rfl⟩ := (mem_conjSub_iff' t U v).mp hv
          have ht' : t * t = 1 := by simpa [pow_two] using h.wr.t_sq
          have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht'
          have hvv : t * (t * u * t⁻¹) * t⁻¹ = u := by
            calc t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t⁻¹ * t⁻¹) := by group
              _ = u := by rw [ht', htinv, ht']; simp
          rw [hvv]; exact hu
        have hqN : q ∈ Subgroup.normalizer (U : Set G) := hP0N hqP0
        have hxq : x * v * x⁻¹ = q * (t * v * t⁻¹) * q⁻¹ := by rw [hxqt]; group
        rw [hxq]
        exact (Subgroup.mem_set_normalizer_iff.mp hqN (t * v * t⁻¹)).mp htv
      have hel' : IsElemAbelian 2 ((E ⊓ (P ⊔ zpowers g)) ⊓ P) :=
        hel.mono (inf_le_left.trans inf_le_left)
      have hcent := y7n_card_cent_le h.wr (m := 8) hm8 hxU inf_le_right hel'
        (fun e he => hel.comm he.1.1 hxE)
      have hb_t := y7n_card_le_two_mul (N := P ⊔ zpowers g) (E := E) h.wr.t_sq htP0 hE
      have hb_g := y7n_card_le_two_mul (N := P) (E := E ⊓ (P ⊔ zpowers g))
        h.sg.g_sq hgP inf_le_right
      have hle32 : Nat.card E ≤ 32 := by
        calc Nat.card E ≤ 2 * Nat.card ↥(E ⊓ (P ⊔ zpowers g)) := hb_t
          _ ≤ 2 * (2 * Nat.card ↥((E ⊓ (P ⊔ zpowers g)) ⊓ P)) :=
              Nat.mul_le_mul_left 2 hb_g
          _ ≤ 2 * (2 * 8) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hcent)
          _ = 32 := by norm_num
      refine ⟨hle32.trans (by norm_num), ?_⟩
      intro hcard
      have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
      omega

end CFSG.OddStandard.HigherRank.YamadaG23
