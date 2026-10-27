module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWe

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t : G} {Q V : Subgroup G}

private lemma card_range_of_injective {H : Type*} [Group H] {E : Subgroup G}
    (φ : ↥E →* H) (hφ : Function.Injective φ) : Nat.card φ.range = Nat.card ↥E := by
  have h := Subgroup.card_ker_mul_card_range φ
  rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ, Subgroup.card_bot, one_mul] at h
  exact h

private lemma eq_of_le_of_mul_eq_mul {a b m : ℕ} (hm : 0 < m) (ha : a ≤ m) (hb : b ≤ m)
    (h : a * b = m * m) : a = m ∧ b = m := by
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · subst hb0; simp at h; omega
    · exact hbpos
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0; simp at h; omega
    · exact hapos
  constructor
  · by_contra hne
    have h1 : (a + 1) * b ≤ m * b :=
      Nat.mul_le_mul_right b (Nat.succ_le_of_lt (lt_of_le_of_ne ha hne))
    have h2 : m * b ≤ m * m := Nat.mul_le_mul_left m hb
    have h3 : (a + 1) * b = a * b + b := by ring
    have : a * b + b ≤ a * b := by
      calc a * b + b = (a + 1) * b := h3.symm
        _ ≤ m * b := h1
        _ ≤ m * m := h2
        _ = a * b := h.symm
    omega
  · by_contra hne
    have h1 : a * (b + 1) ≤ a * m :=
      Nat.mul_le_mul_left a (Nat.succ_le_of_lt (lt_of_le_of_ne hb hne))
    have h2 : a * m ≤ m * m := Nat.mul_le_mul_right m ha
    have h3 : a * (b + 1) = a * b + a := by ring
    have : a * b + a ≤ a * b := by
      calc a * b + a = a * (b + 1) := h3.symm
        _ ≤ a * m := h1
        _ ≤ m * m := h2
        _ = a * b := h.symm
    omega

theorem y7n_card_le_two_mul {N E : Subgroup G} {y : G} (hy2 : y ^ 2 = 1)
    (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hE : E ≤ N ⊔ zpowers y) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ N) := by
  classical
  by_cases hEN : E ≤ N
  · have hinf : E ⊓ N = E := le_antisymm inf_le_left (le_inf le_rfl hEN)
    rw [hinf]
    omega
  · obtain ⟨e0, he0E, he0N⟩ : ∃ e0 ∈ E, e0 ∉ N := by
      by_contra h
      exact hEN fun x hx => by
        by_contra hxN
        exact h ⟨x, hx, hxN⟩
    obtain ⟨z0, hz0N, he0eq⟩ : ∃ z0 ∈ N, e0 = z0 * y := by
      rcases y7n_mem_sup_zpowers hy2 hyN (hE he0E) with h | h
      · exact absurd h he0N
      · exact h
    have hmem : ∀ x : ↥E, ((x : G) ∈ N) ∨ (x : G) * e0⁻¹ ∈ N := by
      intro x
      by_cases hx : ((x : G) ∈ N)
      · exact Or.inl hx
      · right
        rcases y7n_mem_sup_zpowers hy2 hyN (hE x.2) with h | ⟨z, hz, hxz⟩
        · exact absurd h hx
        · rw [hxz, he0eq]
          have h1 : z * y * (z0 * y)⁻¹ = z * z0⁻¹ := by
            rw [mul_inv_rev]
            group
          rw [h1]
          exact N.mul_mem hz (N.inv_mem hz0N)
    let g : ↥(E ⊓ N) × Bool → ↥E := fun p =>
      if p.2 then ⟨((p.1 : G) * e0), E.mul_mem p.1.2.1 he0E⟩
      else ⟨(p.1 : G), p.1.2.1⟩
    have hg : Function.Surjective g := by
      intro x
      rcases hmem x with hx | hx
      · exact ⟨(⟨(x : G), ⟨x.2, hx⟩⟩, false), Subtype.ext rfl⟩
      · refine ⟨(⟨(x : G) * e0⁻¹, ⟨E.mul_mem x.2 (E.inv_mem he0E), hx⟩⟩, true), ?_⟩
        apply Subtype.ext
        show ((x : G) * e0⁻¹) * e0 = (x : G)
        group
    have hle := Nat.card_le_card_of_surjective g hg
    have hcard : Nat.card (↥(E ⊓ N) × Bool) = Nat.card ↥(E ⊓ N) * 2 := by
      simp [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [hcard] at hle
    calc Nat.card E ≤ Nat.card ↥(E ⊓ N) * 2 := hle
      _ = 2 * Nat.card ↥(E ⊓ N) := Nat.mul_comm _ _

theorem y7n_Q_normalizes_V (h : Wr7 t Q V) {q v : G} (hq : q ∈ Q) (hv : v ∈ V) :
    q * v * q⁻¹ ∈ V := by
  obtain ⟨u, hu, v', hv', rfl⟩ := h.decomp hq
  have hcomm : v' * v = v * v' := (h.direct.2.2 v hv v' hv').symm
  have hconj : (u * v') * v * (u * v')⁻¹ = u * v * u⁻¹ := by
    have h1 : v' * v * v'⁻¹ = v := by
      rw [hcomm]
      group
    calc (u * v') * v * (u * v')⁻¹ = u * (v' * v * v'⁻¹) * u⁻¹ := by group
      _ = u * v * u⁻¹ := by rw [h1]
  rw [hconj]
  exact V.mul_mem (V.mul_mem hu hv) (V.inv_mem hu)

private lemma ker_proj1_eq (h : Wr7 t Q V) {E : Subgroup G} (hEQ : E ≤ Q) :
    ((h.proj1.comp (Subgroup.inclusion hEQ)).ker.map E.subtype) = E ⊓ conjSub t V := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨e, he, rfl⟩ := hy
    have hproj1 : ((h.proj1 (Subgroup.inclusion hEQ e) : ↥V) : G) = 1 := by
      have := congrArg (fun z : ↥V => (z : G)) he
      simpa using this
    have hpm := h.proj_mul (Subgroup.inclusion hEQ e)
    rw [hproj1, one_mul] at hpm
    have heqv : ((h.proj2 (Subgroup.inclusion hEQ e) : ↥(conjSub t V)) : G) = (e : G) := by
      simpa using hpm
    have heC : (e : G) ∈ conjSub t V := by
      rw [← heqv]
      exact (h.proj2 _).2
    exact Subgroup.mem_inf.mpr ⟨e.2, heC⟩
  · intro hy
    obtain ⟨hyE, hyC⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_map]
    refine ⟨⟨y, hyE⟩, ?_, rfl⟩
    apply Subtype.ext
    have hprojof := h.proj_of_mul (u := (1 : G)) (v := y) (one_mem V) hyC
    have hEq : (Subgroup.inclusion hEQ ⟨y, hyE⟩ : ↥Q) =
        ⟨1 * y, h.mul_mem' (one_mem V) hyC⟩ := Subtype.ext (by simp)
    show ((h.proj1 (Subgroup.inclusion hEQ ⟨y, hyE⟩) : ↥V) : G) = 1
    rw [hEq]
    exact hprojof.1

private lemma ker_proj2_eq (h : Wr7 t Q V) {E : Subgroup G} (hEQ : E ≤ Q) :
    ((h.proj2.comp (Subgroup.inclusion hEQ)).ker.map E.subtype) = E ⊓ V := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨e, he, rfl⟩ := hy
    have hproj2 : ((h.proj2 (Subgroup.inclusion hEQ e) : ↥(conjSub t V)) : G) = 1 := by
      have := congrArg (fun z : ↥(conjSub t V) => (z : G)) he
      simpa using this
    have hpm := h.proj_mul (Subgroup.inclusion hEQ e)
    rw [hproj2, mul_one] at hpm
    have heqv : ((h.proj1 (Subgroup.inclusion hEQ e) : ↥V) : G) = (e : G) := by
      simpa using hpm
    have heV : (e : G) ∈ V := by
      rw [← heqv]
      exact (h.proj1 _).2
    exact Subgroup.mem_inf.mpr ⟨e.2, heV⟩
  · intro hy
    obtain ⟨hyE, hyV⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_map]
    refine ⟨⟨y, hyE⟩, ?_, rfl⟩
    apply Subtype.ext
    have hprojof := h.proj_of_mul (u := y) (v := (1 : G)) hyV (one_mem (conjSub t V))
    have hEq : (Subgroup.inclusion hEQ ⟨y, hyE⟩ : ↥Q) =
        ⟨y * 1, h.mul_mem' hyV (one_mem (conjSub t V))⟩ := Subtype.ext (by simp)
    show ((h.proj2 (Subgroup.inclusion hEQ ⟨y, hyE⟩) : ↥(conjSub t V)) : G) = 1
    rw [hEq]
    exact hprojof.2

private lemma isElemAbelian_range_proj1 (h : Wr7 t Q V) {E : Subgroup G} (hEQ : E ≤ Q)
    (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (((h.proj1.comp (Subgroup.inclusion hEQ)).range).map V.subtype) := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ((hE.subgroupOf Q).map h.proj1).map V.subtype

private lemma isElemAbelian_conj_range_proj2 (h : Wr7 t Q V) {E : Subgroup G} (hEQ : E ≤ Q)
    (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (conjSub t
      (((h.proj2.comp (Subgroup.inclusion hEQ)).range).map (conjSub t V).subtype)) := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  exact (((hE.subgroupOf Q).map h.proj2).map (conjSub t V).subtype).map
    (MulAut.conj t).toMonoidHom

private lemma card_range_proj1 (h : Wr7 t Q V) {E : Subgroup G} (hEQ : E ≤ Q) :
    Nat.card (((h.proj1.comp (Subgroup.inclusion hEQ)).range).map V.subtype)
      = Nat.card ((h.proj1.comp (Subgroup.inclusion hEQ)).range) :=
  Subgroup.card_subtype V _

private lemma card_range_proj2 (h : Wr7 t Q V) {E : Subgroup G} (hEQ : E ≤ Q) :
    Nat.card (conjSub t
      (((h.proj2.comp (Subgroup.inclusion hEQ)).range).map (conjSub t V).subtype))
      = Nat.card ((h.proj2.comp (Subgroup.inclusion hEQ)).range) := by
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective,
    Subgroup.card_subtype]

private lemma card_ker_proj1 (h : Wr7 t Q V) {E : Subgroup G} (hEQ : E ≤ Q) :
    Nat.card ((h.proj1.comp (Subgroup.inclusion hEQ)).ker)
      = Nat.card ↥(E ⊓ conjSub t V) := by
  calc Nat.card ((h.proj1.comp (Subgroup.inclusion hEQ)).ker)
      = Nat.card ↥(((h.proj1.comp (Subgroup.inclusion hEQ)).ker).map E.subtype) :=
        (Subgroup.card_map_of_injective E.subtype_injective).symm
    _ = Nat.card ↥(E ⊓ conjSub t V) :=
        congrArg (fun X : Subgroup G => Nat.card ↥X) (ker_proj1_eq h hEQ)

private lemma card_ker_proj2 (h : Wr7 t Q V) {E : Subgroup G} (hEQ : E ≤ Q) :
    Nat.card ((h.proj2.comp (Subgroup.inclusion hEQ)).ker)
      = Nat.card ↥(E ⊓ V) := by
  calc Nat.card ((h.proj2.comp (Subgroup.inclusion hEQ)).ker)
      = Nat.card ↥(((h.proj2.comp (Subgroup.inclusion hEQ)).ker).map E.subtype) :=
        (Subgroup.card_map_of_injective E.subtype_injective).symm
    _ = Nat.card ↥(E ⊓ V) :=
        congrArg (fun X : Subgroup G => Nat.card ↥X) (ker_proj2_eq h hEQ)

theorem y7n_card_cent_le (h : Wr7 t Q V) {m : ℕ}
    (hm : ∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → Nat.card E ≤ m) {x : G}
    (hx : ∀ v ∈ conjSub t V, x * v * x⁻¹ ∈ V) {E : Subgroup G} (hEQ : E ≤ Q)
    (hE : IsElemAbelian 2 E) (hcomm : ∀ e ∈ E, e * x = x * e) : Nat.card E ≤ m := by
  let φ : ↥E →* ↥V := h.proj1.comp (Subgroup.inclusion hEQ)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply Subtype.ext
    have hproj1 : ((h.proj1 (Subgroup.inclusion hEQ e) : ↥V) : G) = 1 := by
      have := congrArg (fun z : ↥V => (z : G)) he
      simpa [φ] using this
    have hpm := h.proj_mul (Subgroup.inclusion hEQ e)
    rw [hproj1, one_mul] at hpm
    have heC : (e : G) ∈ conjSub t V := by
      have heqv : ((h.proj2 (Subgroup.inclusion hEQ e) : ↥(conjSub t V)) : G) = (e : G) := by
        simpa using hpm
      rw [← heqv]
      exact (h.proj2 _).2
    have hxe : x * (e : G) * x⁻¹ = (e : G) := by
      calc x * (e : G) * x⁻¹ = (e : G) * x * x⁻¹ := by rw [← hcomm e e.2]
        _ = (e : G) := by group
    have heV : (e : G) ∈ V := by
      rw [← hxe]
      exact hx _ heC
    have hebot : (e : G) ∈ (⊥ : Subgroup G) := by
      rw [← h.direct.2.1]
      exact Subgroup.mem_inf.mpr ⟨heV, heC⟩
    simpa using Subgroup.mem_bot.mp hebot
  have hcard : Nat.card (φ.range.map V.subtype) = Nat.card ↥E := by
    rw [Subgroup.card_subtype, card_range_of_injective φ hφinj]
  have hEA : IsElemAbelian 2 (φ.range.map V.subtype) :=
    isElemAbelian_range_proj1 h hEQ hE
  have hle := hm (φ.range.map V.subtype) (Subgroup.map_subtype_le (H := V) _) hEA
  rwa [hcard] at hle

theorem y7n_card_le_sq (h : Wr7 t Q V) {m : ℕ}
    (hm : ∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → Nat.card E ≤ m)
    {E : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ m * m ∧
      (Nat.card E = m * m →
        E = (E ⊓ V) ⊔ (E ⊓ conjSub t V) ∧ Nat.card ↥(E ⊓ V) = m ∧
          Nat.card ↥(E ⊓ conjSub t V) = m) := by
  have hE1 : Nat.card E = Nat.card ↥(E ⊓ conjSub t V) *
      Nat.card (((h.proj1.comp (Subgroup.inclusion hEQ)).range).map V.subtype) := by
    have hcard := Subgroup.card_ker_mul_card_range (h.proj1.comp (Subgroup.inclusion hEQ))
    rw [card_ker_proj1 h hEQ, ← card_range_proj1 h hEQ] at hcard
    exact hcard.symm
  have hE2 : Nat.card E = Nat.card ↥(E ⊓ V) *
      Nat.card (conjSub t
        (((h.proj2.comp (Subgroup.inclusion hEQ)).range).map (conjSub t V).subtype)) := by
    have hcard := Subgroup.card_ker_mul_card_range (h.proj2.comp (Subgroup.inclusion hEQ))
    rw [card_ker_proj2 h hEQ, ← card_range_proj2 h hEQ] at hcard
    exact hcard.symm
  have hker1 : Nat.card ↥(E ⊓ conjSub t V) ≤ m := by
    have h1 : conjSub t (E ⊓ conjSub t V) ≤ conjSub t (conjSub t V) :=
      Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) inf_le_right
    have hconj : conjSub t (E ⊓ conjSub t V) ≤ V := by
      rwa [conjSub_conjSub_of_sq h.t_sq V] at h1
    have hEA : IsElemAbelian 2 (conjSub t (E ⊓ conjSub t V)) :=
      (hE.mono inf_le_left).map (MulAut.conj t).toMonoidHom
    have := hm _ hconj hEA
    rwa [conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective] at this
  have hrange1 : Nat.card (((h.proj1.comp (Subgroup.inclusion hEQ)).range).map V.subtype) ≤ m :=
    hm _ (Subgroup.map_subtype_le (H := V) _) (isElemAbelian_range_proj1 h hEQ hE)
  have hker2 : Nat.card ↥(E ⊓ V) ≤ m := hm _ inf_le_right (hE.mono inf_le_left)
  have hrange2 : Nat.card (conjSub t
      (((h.proj2.comp (Subgroup.inclusion hEQ)).range).map (conjSub t V).subtype)) ≤ m := by
    have h1 : conjSub t (((h.proj2.comp (Subgroup.inclusion hEQ)).range).map
        (conjSub t V).subtype) ≤ conjSub t (conjSub t V) :=
      Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom)
        (Subgroup.map_subtype_le (H := conjSub t V) _)
    have hconj : conjSub t (((h.proj2.comp (Subgroup.inclusion hEQ)).range).map
        (conjSub t V).subtype) ≤ V := by
      rwa [conjSub_conjSub_of_sq h.t_sq V] at h1
    exact hm _ hconj (isElemAbelian_conj_range_proj2 h hEQ hE)
  refine ⟨?_, ?_⟩
  · rw [hE1]
    exact Nat.mul_le_mul hker1 hrange1
  · intro hEm
    have hmpos : 0 < m := by
      have h1 : 0 < Nat.card E := Nat.card_pos
      rw [hEm] at h1
      exact Nat.pos_of_mul_pos_left h1
    obtain ⟨hker1m, -⟩ := eq_of_le_of_mul_eq_mul hmpos hker1 hrange1 (by rw [← hE1, hEm])
    obtain ⟨hker2m, -⟩ := eq_of_le_of_mul_eq_mul hmpos hker2 hrange2 (by rw [← hE2, hEm])
    have hdisj : Disjoint (E ⊓ V) (E ⊓ conjSub t V) := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have hx' : x ∈ V ⊓ conjSub t V := ⟨hx.1.2, hx.2.2⟩
      rw [h.direct.2.1] at hx'
      exact hx'
    have hcent : E ⊓ conjSub t V ≤ Subgroup.centralizer ((E ⊓ V : Subgroup G) : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact h.direct.2.2 a ha.2 b hb.2
    have hnorm : E ⊓ conjSub t V ≤ Subgroup.normalizer ((E ⊓ V : Subgroup G) : Set G) :=
      hcent.trans (Subgroup.centralizer_le_normalizer _)
    have hcardsup : Nat.card ↥((E ⊓ V) ⊔ (E ⊓ conjSub t V)) = m * m := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (E ⊓ V)
        (E ⊓ conjSub t V) hnorm hdisj, hker2m, hker1m]
    have hle : (E ⊓ V) ⊔ (E ⊓ conjSub t V) ≤ E := sup_le inf_le_left inf_le_left
    have heq : E = (E ⊓ V) ⊔ (E ⊓ conjSub t V) :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardsup, hEm])).symm
    exact ⟨heq, hker2m, hker1m⟩

end CFSG.OddStandard.HigherRank.YamadaG23
