module

public import CFSG.CGT.Timmesfeld75.L2Basic

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

@[expose] def IsL2Pair (X : Type) [Group X] (S : Subgroup X) (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (e : X ≃* SL(2, F)),
    Nat.card F = q ∧ S.map e.toMonoidHom = utri F

section Transfer

variable {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)

theorem mem_map_mulEquiv_iff {S : Subgroup X} {x : X} : e x ∈ S.map e.toMonoidHom ↔ x ∈ S :=
  Subgroup.mem_map_iff_mem e.injective

theorem map_conjSubgroup_mulEquiv (g : X) (S : Subgroup X) :
    (conjSubgroup g S).map e.toMonoidHom = conjSubgroup (e g) (S.map e.toMonoidHom) :=
  map_conjSubgroup e.toMonoidHom g S

theorem mem_normalizer_iff_mulEquiv {S : Subgroup X} {g : X} :
    g ∈ Subgroup.normalizer (S : Set X) ↔
      e g ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  rw [← Subgroup.map_normalizer_eq_of_bijective S (f := e.toMonoidHom) e.bijective]
  exact (mem_map_mulEquiv_iff e).symm

theorem IsWC.map_mulEquiv {S : Subgroup X} (hS : IsWC S) : IsWC (S.map e.toMonoidHom) := by
  have hSb := isElemAbelian_map_of_hom hS.1 e.toMonoidHom
  refine ⟨hSb, fun tb htb htb1 => ⟨fun x hx => ?_, fun gb hgb => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact elemAbelian_mul_comm hSb htb hx
  · obtain ⟨g, rfl⟩ := e.surjective gb
    obtain ⟨t, ht, rfl⟩ := htb
    have ht1 : t ≠ 1 := fun h => htb1 (by rw [h]; exact map_one e.toMonoidHom)
    have hcent : conjSubgroup g S ≤ Subgroup.centralizer ({t} : Set X) := by
      intro x hx
      have hxm : e x ∈ conjSubgroup (e g) (S.map e.toMonoidHom) := by
        rw [← map_conjSubgroup_mulEquiv]
        exact Subgroup.mem_map_of_mem _ hx
      have hxc := Subgroup.mem_centralizer_iff.1 (hgb hxm) (e t) (Set.mem_singleton _)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact e.injective (by rw [map_mul, map_mul]; exact hxc.symm)
    have hconj := (hS.2 t ht ht1).2 g hcent
    show conjSubgroup (e g) (S.map e.toMonoidHom) = S.map e.toMonoidHom
    rw [← map_conjSubgroup_mulEquiv, hconj]

theorem map_trans_conj_eq (c : Y) (T : Subgroup X) :
    T.map (e.trans (MulAut.conj c)).toMonoidHom = conjSubgroup c (T.map e.toMonoidHom) := by
  rw [conjSubgroup, Subgroup.map_map]
  rfl

theorem map_symm_map_mulEquiv (T : Subgroup Y) :
    (T.map e.symm.toMonoidHom).map e.toMonoidHom = T := by
  rw [Subgroup.map_map]
  have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y :=
    MonoidHom.ext fun y => e.apply_symm_apply y
  rw [h, Subgroup.map_id]

end Transfer

namespace IsL2Pair

variable {X : Type} [Group X] {S : Subgroup X} {q : ℕ}

theorem exists_data (h : IsL2Pair X S q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (e : X ≃* SL(2, F)),
      Nat.card F = q ∧ S.map e.toMonoidHom = utri F ∧
      S = (utri F).map e.symm.toMonoidHom ∧ (∀ x, x ∈ S ↔ e x ∈ utri F) ∧
      (∀ g, g ∈ Subgroup.normalizer (S : Set X) ↔ e g ∈ borel F) := by
  obtain ⟨F, i1, i2, i3, e, hq, hS⟩ := h
  refine ⟨F, i1, i2, i3, e, hq, hS, ?_, fun x => ?_, fun g => ?_⟩
  · ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulEquiv.symm_symm]
    rw [← hS, mem_map_mulEquiv_iff]
  · rw [← hS, mem_map_mulEquiv_iff]
  · rw [mem_normalizer_iff_mulEquiv e, hS, normalizer_utri]

theorem isElemAbelian (h : IsL2Pair X S q) : IsElemAbelian 2 S := by
  obtain ⟨F, _, _, _, e, -, -, hS', -, -⟩ := h.exists_data
  rw [hS']
  exact isElemAbelian_map_of_hom isElemAbelian_utri _

theorem card_eq (h : IsL2Pair X S q) : Nat.card S = q := by
  obtain ⟨F, _, _, _, e, hq, -, hS', -, -⟩ := h.exists_data
  rw [hS', Subgroup.card_map_of_injective e.symm.injective, card_utri, hq]

theorem exists_eq_two_pow (h : IsL2Pair X S q) : ∃ n : ℕ, 0 < n ∧ q = 2 ^ n := by
  obtain ⟨F, _, _, _, e, hq, -, -, -, -⟩ := h.exists_data
  obtain ⟨n, hn, hn'⟩ := exists_natCard_eq_two_pow (F := F)
  exact ⟨n, hn, hq ▸ hn'⟩

theorem centralizer_eq (h : IsL2Pair X S q) {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set X) = S := by
  obtain ⟨F, _, _, _, e, -, -, -, hmemS, -⟩ := h.exists_data
  obtain ⟨σ, hσ⟩ := mem_utri_iff.1 ((hmemS s).1 hs)
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hσ
    exact hs1 (e.injective (hσ.trans (map_one e).symm))
  ext x
  have hx : x * s = s * x ↔ e x * e s = e s * e x :=
    ⟨fun h => by rw [← map_mul, ← map_mul, h],
      fun h => e.injective (by rwa [map_mul, map_mul])⟩
  rw [Subgroup.mem_centralizer_singleton_iff, hmemS, hx, hσ,
    ← Subgroup.mem_centralizer_singleton_iff, centralizer_utriElt hσ0]

theorem transitive (h : IsL2Pair X S q) {x : X} (hx : x ∈ S) (hx1 : x ≠ 1) {y : X} (hy : y ∈ S)
    (hy1 : y ≠ 1) : ∃ g ∈ Subgroup.normalizer (S : Set X), g * x * g⁻¹ = y := by
  obtain ⟨F, _, _, _, e, -, -, -, hmemS, hmemN⟩ := h.exists_data
  obtain ⟨σ, hσ⟩ := mem_utri_iff.1 ((hmemS x).1 hx)
  obtain ⟨τ, hτ⟩ := mem_utri_iff.1 ((hmemS y).1 hy)
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hσ
    exact hx1 (e.injective (hσ.trans (map_one e).symm))
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hτ
    exact hy1 (e.injective (hτ.trans (map_one e).symm))
  obtain ⟨b, hb, hbst⟩ := exists_mem_borel_conj_utriElt hσ0 hτ0
  refine ⟨e.symm b, (hmemN _).2 (by rwa [e.apply_symm_apply]), e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply, hσ, hτ]
  exact hbst

theorem card_normalizer (h : IsL2Pair X S q) :
    Nat.card (Subgroup.normalizer (S : Set X)) = q * (q - 1) := by
  obtain ⟨F, _, _, _, e, hq, -, -, -, hmemN⟩ := h.exists_data
  have hN : Subgroup.normalizer (S : Set X) = (borel F).map e.symm.toMonoidHom := by
    ext g
    rw [hmemN, Subgroup.mem_map_equiv]
    simp only [MulEquiv.symm_symm]
  rw [hN, Subgroup.card_map_of_injective e.symm.injective, card_borel, hq]

theorem relIndex_normalizer (h : IsL2Pair X S q) :
    S.relIndex (Subgroup.normalizer (S : Set X)) = q - 1 := by
  have hSN : S ≤ Subgroup.normalizer (S : Set X) := Subgroup.le_normalizer
  have h1 := Subgroup.card_mul_index (S.subgroupOf (Subgroup.normalizer (S : Set X)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, h.card_eq, card_normalizer h]
    at h1
  obtain ⟨n, -, hn⟩ := h.exists_eq_two_pow
  have hq : 0 < q := by rw [hn]; positivity
  exact Nat.eq_of_mul_eq_mul_left hq h1

theorem finite (h : IsL2Pair X S q) : Finite X := by
  obtain ⟨F, _, _, _, e, -, -, -, -, -⟩ := h.exists_data
  exact Finite.of_equiv _ e.symm.toEquiv

theorem conj (h : IsL2Pair X S q) (g : X) : IsL2Pair X (conjSubgroup g S) q := by
  obtain ⟨F, i1, i2, i3, e, hq, hS⟩ := h
  refine ⟨F, i1, i2, i3, e.trans (MulAut.conj (e g)⁻¹), hq, ?_⟩
  rw [map_trans_conj_eq, map_conjSubgroup_mulEquiv, hS, conjSubgroup_conjSubgroup,
    inv_mul_cancel, conjSubgroup_one]

theorem exists_complement (h : IsL2Pair X S q) :
    ∃ H : Subgroup X, H ≤ Subgroup.normalizer (S : Set X) ∧ IsCyclic H ∧ Nat.card H = q - 1 ∧
      S ⊓ H = ⊥ ∧ S ⊔ H = Subgroup.normalizer (S : Set X) ∧
      ∀ x ∈ S, x ≠ 1 → ∀ y ∈ S, y ≠ 1 → ∃! k, k ∈ H ∧ k * x * k⁻¹ = y := by
  obtain ⟨F, _, _, _, e, hq, hS, -, hmemS, hmemN⟩ := h.exists_data
  have hH : ∀ k, k ∈ (torus F).map e.symm.toMonoidHom ↔ e k ∈ torus F := fun k => by
    rw [Subgroup.mem_map_equiv]
    simp only [MulEquiv.symm_symm]
  refine ⟨(torus F).map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact (hmemN k).2 (torus_le_borel ((hH k).1 hk))
  · have : IsCyclic (torus F) := isCyclic_torus
    exact isCyclic_of_surjective (e.symm.subgroupMap (torus F))
      (e.symm.subgroupMap (torus F)).surjective
  · rw [Subgroup.card_map_of_injective e.symm.injective, card_torus, hq]
  · rw [eq_bot_iff]
    rintro x ⟨hxS, hxH⟩
    have h1 : e x ∈ utri F ⊓ torus F := ⟨(hmemS x).1 hxS, (hH x).1 hxH⟩
    rw [inf_utri_torus, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  · apply le_antisymm
    · exact sup_le Subgroup.le_normalizer
        (fun k hk => (hmemN k).2 (torus_le_borel ((hH k).1 hk)))
    · intro g hg
      have h1 : e g ∈ utri F ⊔ torus F := by
        rw [← borel_eq_sup]
        exact (hmemN g).1 hg
      have h2 : (S ⊔ (torus F).map e.symm.toMonoidHom).map e.toMonoidHom = utri F ⊔ torus F := by
        rw [Subgroup.map_sup, hS, map_symm_map_mulEquiv]
      rw [← mem_map_mulEquiv_iff e, h2]
      exact h1
  · intro x hx hx1 y hy hy1
    obtain ⟨σ, hσ⟩ := mem_utri_iff.1 ((hmemS x).1 hx)
    obtain ⟨τ, hτ⟩ := mem_utri_iff.1 ((hmemS y).1 hy)
    have hσ0 : σ ≠ 0 := by
      rintro rfl
      rw [utriElt_zero] at hσ
      exact hx1 (e.injective (hσ.trans (map_one e).symm))
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      rw [utriElt_zero] at hτ
      exact hy1 (e.injective (hτ.trans (map_one e).symm))
    obtain ⟨a, ha⟩ := exists_torusElt_conj_utriElt hσ0 hτ0
    refine ⟨e.symm (torusElt a), ⟨(hH _).2 (by rw [e.apply_symm_apply]; exact torusElt_mem_torus a),
      e.injective ?_⟩, fun k ⟨hkH, hk⟩ => ?_⟩
    · rw [map_mul, map_mul, map_inv, e.apply_symm_apply, hσ, hτ]
      exact ha
    · obtain ⟨a', ha'⟩ := mem_torus_iff.1 ((hH k).1 hkH)
      have h1 : torusElt a' * utriElt σ * (torusElt a')⁻¹ = utriElt τ := by
        rw [← ha', ← hσ, ← hτ, ← map_inv, ← map_mul, ← map_mul, hk]
      have h2 := eq_of_torusElt_conj_eq hσ0 (h1.trans ha.symm)
      apply e.injective
      rw [ha', h2, e.apply_symm_apply]

theorem inf_conj_eq_bot (h : IsL2Pair X S q) {g : X} (hg : g ∉ Subgroup.normalizer (S : Set X)) :
    S ⊓ conjSubgroup g S = ⊥ := by
  obtain ⟨F, _, _, _, e, -, hS, -, -, hmemN⟩ := h.exists_data
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hg' : e g ∉ borel F := fun hb => hg ((hmemN g).2 hb)
  apply (Subgroup.map_eq_bot_iff_of_injective _ hinj).1
  rw [Subgroup.map_inf _ _ _ hinj, map_conjSubgroup_mulEquiv, hS]
  exact utri_inf_conj_eq_bot hg'

theorem normalizer_inf_conj_eq_bot (h : IsL2Pair X S q) {g : X}
    (hg : g ∉ Subgroup.normalizer (S : Set X)) :
    Subgroup.normalizer (S : Set X) ⊓ conjSubgroup g S = ⊥ := by
  obtain ⟨F, _, _, _, e, -, hS, -, -, hmemN⟩ := h.exists_data
  have hg' : e g ∉ borel F := fun hb => hg ((hmemN g).2 hb)
  rw [eq_bot_iff]
  rintro x ⟨hxN, hxC⟩
  have h2 : e x ∈ conjSubgroup (e g) (utri F) := by
    rw [← hS, ← map_conjSubgroup_mulEquiv, mem_map_mulEquiv_iff]
    exact hxC
  have h3 : e x ∈ borel F ⊓ conjSubgroup (e g) (utri F) := ⟨(hmemN x).1 hxN, h2⟩
  rw [inf_borel_conj_utri_eq_bot hg', Subgroup.mem_bot] at h3
  rw [Subgroup.mem_bot]
  exact e.injective (h3.trans (map_one e).symm)

theorem inf_conjSubgroup_eq_bot (h : IsL2Pair X S q) {a b : X}
    (hab : conjSubgroup a S ≠ conjSubgroup b S) : conjSubgroup a S ⊓ conjSubgroup b S = ⊥ := by
  obtain ⟨F, _, _, _, e, -, hS, -, -, -⟩ := h.exists_data
  have hinj : Function.Injective e.toMonoidHom := e.injective
  apply (Subgroup.map_eq_bot_iff_of_injective _ hinj).1
  rw [Subgroup.map_inf _ _ _ hinj, map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv,
    hS]
  refine inf_conjSubgroup_utri_eq_bot fun h' => hab ?_
  apply Subgroup.map_injective hinj
  rw [map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hS]
  exact h'

theorem conjTwoTransitive (h : IsL2Pair X S q) : ConjTwoTransitive X S := by
  obtain ⟨F, _, _, _, e, -, hS, -, -, -⟩ := h.exists_data
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have key : ∀ x y : X, conjSubgroup x S ≠ conjSubgroup y S →
      conjSubgroup (e x) (utri F) ≠ conjSubgroup (e y) (utri F) := by
    intro x y hxy hxy'
    apply hxy
    apply Subgroup.map_injective hinj
    rw [map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hS]
    exact hxy'
  intro a b c d hab hcd
  obtain ⟨g, hg1, hg2⟩ :=
    conjTwoTransitive_utri (e a) (e b) (e c) (e d) (key a b hab) (key c d hcd)
  refine ⟨e.symm g, ?_, ?_⟩
  · apply Subgroup.map_injective hinj
    rw [map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hS, map_mul, e.apply_symm_apply]
    exact hg1
  · apply Subgroup.map_injective hinj
    rw [map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hS, map_mul, e.apply_symm_apply]
    exact hg2

theorem card_eq_mul (h : IsL2Pair X S q) : Nat.card X = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, _, e, hq, -, -, -, -⟩ := h.exists_data
  rw [Nat.card_congr e.toEquiv, card_sl2, hq]

theorem exists_sylow_eq (h : IsL2Pair X S q) : ∃ P : Sylow 2 X, (P : Subgroup X) = S := by
  obtain ⟨F, _, _, _, e, -, -, hS', -, -⟩ := h.exists_data
  exact ⟨Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective (utriSylow F),
    hS'.symm⟩

theorem exists_conj_eq_sylow (h : IsL2Pair X S q) (P : Sylow 2 X) :
    ∃ g : X, conjSubgroup g S = (P : Subgroup X) := by
  have := h.finite
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq
  obtain ⟨g, hg⟩ := exists_conjSubgroup_eq_of_sylow Q P
  exact ⟨g, hQ ▸ hg⟩

theorem isConj_of_mul_self_eq_one (h : IsL2Pair X S q) {x y : X} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hy : y * y = 1) (hy1 : y ≠ 1) : IsConj x y := by
  obtain ⟨F, _, _, _, e, -, -, -, -, -⟩ := h.exists_data
  have hc := _root_.CFSG.CGT.Timmesfeld75.isConj_of_mul_self_eq_one (g := e x) (h := e y)
    (by rw [← map_mul, hx, map_one]) (fun h' => hx1 (e.injective (h'.trans (map_one e).symm)))
    (by rw [← map_mul, hy, map_one]) (fun h' => hy1 (e.injective (h'.trans (map_one e).symm)))
  have := MonoidHom.map_isConj e.symm.toMonoidHom hc
  simpa using this

theorem exists_conj_mem_of_mul_self_eq_one (h : IsL2Pair X S q) {x : X} (hx : x * x = 1) :
    ∃ g : X, x ∈ conjSubgroup g S := by
  have := h.finite
  obtain ⟨P, hP⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hx).exists_le_sylow
  obtain ⟨g, hg⟩ := h.exists_conj_eq_sylow P
  exact ⟨g, by rw [hg]; exact hP (Subgroup.mem_zpowers x)⟩

theorem centralizer_eq_conj (h : IsL2Pair X S q) {g x : X} (hx : x ∈ conjSubgroup g S)
    (hx1 : x ≠ 1) : Subgroup.centralizer ({x} : Set X) = conjSubgroup g S :=
  (h.conj g).centralizer_eq hx hx1

theorem exists_mul_orderOf_three (h : IsL2Pair X S q) {a b : X}
    (hab : conjSubgroup a S ≠ conjSubgroup b S) :
    ∃ u ∈ conjSubgroup a S, u ≠ 1 ∧ ∃ v ∈ conjSubgroup b S, v ≠ 1 ∧ orderOf (u * v) = 3 := by
  obtain ⟨F, _, _, _, e, -, hS, -, -, -⟩ := h.exists_data
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hne : conjSubgroup (e a) (utri F) ≠ conjSubgroup (e b) (utri F) := by
    intro h'
    apply hab
    apply Subgroup.map_injective hinj
    rw [map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hS]
    exact h'
  obtain ⟨u, hu, hu1, v, hv, hv1, hord⟩ := exists_mul_orderOf_three_of_conj_ne hne
  have hu' : e.symm u ∈ conjSubgroup a S := by
    rw [← mem_map_mulEquiv_iff e, e.apply_symm_apply, map_conjSubgroup_mulEquiv, hS]
    exact hu
  have hv' : e.symm v ∈ conjSubgroup b S := by
    rw [← mem_map_mulEquiv_iff e, e.apply_symm_apply, map_conjSubgroup_mulEquiv, hS]
    exact hv
  refine ⟨e.symm u, hu', fun h1 => hu1 ?_, e.symm v, hv', fun h1 => hv1 ?_, ?_⟩
  · simpa using congrArg e h1
  · simpa using congrArg e h1
  · calc orderOf (e.symm u * e.symm v) = orderOf (e (e.symm u * e.symm v)) :=
        (orderOf_injective e.toMonoidHom e.injective _).symm
      _ = orderOf (u * v) := by rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      _ = 3 := hord

theorem sup_conj_eq_top (h : IsL2Pair X S q) {a b : X}
    (hab : conjSubgroup a S ≠ conjSubgroup b S) : conjSubgroup a S ⊔ conjSubgroup b S = ⊤ := by
  obtain ⟨F, _, _, _, e, -, hS, -, -, -⟩ := h.exists_data
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hne : conjSubgroup (e a) (utri F) ≠ conjSubgroup (e b) (utri F) := by
    intro h'
    apply hab
    apply Subgroup.map_injective hinj
    rw [map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hS]
    exact h'
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_sup, map_conjSubgroup_mulEquiv, map_conjSubgroup_mulEquiv, hS,
    sup_conjSubgroup_utri_eq_top hne, Subgroup.map_top_of_surjective _ e.surjective]

theorem exists_mul_orderOf_three_of_sylow (h : IsL2Pair X S q) {P Q : Sylow 2 X} (hPQ : P ≠ Q) :
    ∃ u ∈ (P : Subgroup X), u ≠ 1 ∧ ∃ v ∈ (Q : Subgroup X), v ≠ 1 ∧ orderOf (u * v) = 3 := by
  obtain ⟨a, ha⟩ := h.exists_conj_eq_sylow P
  obtain ⟨b, hb⟩ := h.exists_conj_eq_sylow Q
  rw [← ha, ← hb]
  refine h.exists_mul_orderOf_three fun h' => hPQ (Sylow.ext ?_)
  rw [← ha, ← hb]
  exact h'

theorem sup_sylow_eq_top (h : IsL2Pair X S q) {P Q : Sylow 2 X} (hPQ : P ≠ Q) :
    (P : Subgroup X) ⊔ (Q : Subgroup X) = ⊤ := by
  obtain ⟨a, ha⟩ := h.exists_conj_eq_sylow P
  obtain ⟨b, hb⟩ := h.exists_conj_eq_sylow Q
  rw [← ha, ← hb]
  refine h.sup_conj_eq_top fun h' => hPQ (Sylow.ext ?_)
  rw [← ha, ← hb]
  exact h'

theorem eq_of_isWC (h : IsL2Pair X S q) {A : Subgroup X} (hA : A ≤ S) (hA1 : A ≠ ⊥)
    (hWC : IsWC A) : A = S := by
  obtain ⟨F, _, _, _, e, -, hS, -, -, -⟩ := h.exists_data
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hA' : A.map e.toMonoidHom ≤ utri F := by
    rw [← hS]
    exact Subgroup.map_mono hA
  have hA1' : A.map e.toMonoidHom ≠ ⊥ := fun h' =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h')
  have hAS := eq_utri_of_isWC hA' hA1' (IsWC.map_mulEquiv e hWC)
  apply Subgroup.map_injective hinj
  rw [hAS, hS]

theorem of_sylow (h : IsL2Pair X S q) (P : Sylow 2 X) : IsL2Pair X (P : Subgroup X) q := by
  obtain ⟨g, hg⟩ := h.exists_conj_eq_sylow P
  rw [← hg]
  exact h.conj g

theorem of_psl_sylow {f : ℕ} (hf : f ≠ 0) (h : Nonempty (X ≃* PSL(2, GaloisField 2 f)))
    (S : Sylow 2 X) : IsL2Pair X (S : Subgroup X) (2 ^ f) := by
  obtain ⟨e₀⟩ := h
  let e₁ : X ≃* SL(2, GaloisField 2 f) := e₀.trans pslMulEquivSL
  have : Finite X := Finite.of_equiv _ e₁.symm.toEquiv
  let P : Sylow 2 SL(2, GaloisField 2 f) :=
    Sylow.mapSurjective (f := e₁.toMonoidHom) e₁.surjective S
  obtain ⟨g, hg⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, inferInstance,
    e₁.trans (MulAut.conj g⁻¹), GaloisField.card 2 f hf, ?_⟩
  rw [map_trans_conj_eq]
  have hP : (S : Subgroup X).map e₁.toMonoidHom = conjSubgroup g (utri (GaloisField 2 f)) :=
    hg.symm
  rw [hP, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

theorem of_psl_isPGroup {f : ℕ} (hf : f ≠ 0) (h : Nonempty (X ≃* PSL(2, GaloisField 2 f)))
    (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.index) : IsL2Pair X S (2 ^ f) :=
  of_psl_sylow hf h (IsPGroup.toSylow hS hidx)

theorem of_psl_exists_sylow {f : ℕ} (hf : f ≠ 0) (h : Nonempty (X ≃* PSL(2, GaloisField 2 f)))
    (hS : ∃ P : Sylow 2 X, (P : Subgroup X) = S) : IsL2Pair X S (2 ^ f) := by
  obtain ⟨P, rfl⟩ := hS
  exact of_psl_sylow hf h P

end IsL2Pair

end CFSG.CGT.Timmesfeld75
