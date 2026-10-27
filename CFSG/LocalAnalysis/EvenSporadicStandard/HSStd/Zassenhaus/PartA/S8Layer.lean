module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Algebra

variable {Γ : Type*} [Group Γ]

theorem comm_mul_right_central {a y c : Γ} (h : Commute c y) : ⁅a * c, y⁆ = ⁅a, y⁆ := by
  have : c * y * c⁻¹ = y := h.mul_inv_cancel
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * c * y * (c⁻¹ * a⁻¹) * y⁻¹ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [this]

theorem comm_mul_left_central {a y c : Γ} (h : Commute c a) : ⁅a, y * c⁆ = ⁅a, y⁆ := by
  have : ⁅y * c, a⁆ = ⁅y, a⁆ := comm_mul_right_central h
  rw [← commutatorElement_inv, this, commutatorElement_inv]

theorem comm_mul_central {a b c c' : Γ} (h1 : Commute c b) (h2 : Commute c' a)
    (h5 : Commute c' c) : ⁅a * c, b * c'⁆ = ⁅a, b⁆ := by
  rw [comm_mul_left_central (h2.mul_right h5), comm_mul_right_central h1]

theorem comm_mul_mul {a b m m' : Γ} (h1 : Commute a m) (h2 : Commute a m') (h3 : Commute b m)
    (h4 : Commute b m') : ⁅a * m, b * m'⁆ = ⁅a, b⁆ * ⁅m, m'⁆ := by
  have c1 : m * b = b * m := h3.eq.symm
  have hu : Commute a⁻¹ (m * m' * m⁻¹) :=
    ((h1.inv_left.mul_right h2.inv_left).mul_right h1.inv_left.inv_right)
  have hv : Commute b⁻¹ (m * m' * m⁻¹ * m'⁻¹) :=
    (((h3.inv_left.mul_right h4.inv_left).mul_right h3.inv_left.inv_right).mul_right
      h4.inv_left.inv_right)
  have e1 : m * m' * m⁻¹ * a⁻¹ = a⁻¹ * (m * m' * m⁻¹) := hu.eq.symm
  have e2 : m * m' * m⁻¹ * m'⁻¹ * b⁻¹ = b⁻¹ * (m * m' * m⁻¹ * m'⁻¹) := hv.eq.symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * m * (b * m') * (m⁻¹ * a⁻¹) * (m'⁻¹ * b⁻¹)
      = a * (m * b) * (m' * m⁻¹ * a⁻¹ * m'⁻¹ * b⁻¹) := by group
    _ = a * b * (m * m' * m⁻¹ * a⁻¹ * m'⁻¹ * b⁻¹) := by rw [c1]; simp only [mul_assoc]
    _ = a * b * (a⁻¹ * (m * m' * m⁻¹) * m'⁻¹ * b⁻¹) := by rw [← e1]
    _ = a * b * a⁻¹ * (m * m' * m⁻¹ * m'⁻¹ * b⁻¹) := by group
    _ = a * b * a⁻¹ * (b⁻¹ * (m * m' * m⁻¹ * m'⁻¹)) := by rw [e2]
    _ = _ := by group

theorem exists_mul_of_mem_sup {N M : Subgroup Γ} (h : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n) {x : Γ}
    (hx : x ∈ N ⊔ M) : ∃ n ∈ N, ∃ m ∈ M, x = n * m := by
  let S : Subgroup Γ :=
    { carrier := {x | ∃ n ∈ N, ∃ m ∈ M, x = n * m}
      one_mem' := ⟨1, N.one_mem, 1, M.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, m, hm, rfl⟩ ⟨n', hn', m', hm', rfl⟩
        refine ⟨n * n', N.mul_mem hn hn', m * m', M.mul_mem hm hm', ?_⟩
        have := h n' hn' m hm
        calc n * m * (n' * m') = n * (m * n') * m' := by group
          _ = n * (n' * m) * m' := by rw [← this]
          _ = _ := by group
      inv_mem' := by
        rintro _ ⟨n, hn, m, hm, rfl⟩
        refine ⟨n⁻¹, N.inv_mem hn, m⁻¹, M.inv_mem hm, ?_⟩
        have := h n⁻¹ (N.inv_mem hn) m⁻¹ (M.inv_mem hm)
        rw [mul_inv_rev]
        exact this.symm }
  have : N ⊔ M ≤ S := sup_le (fun n hn => ⟨n, hn, 1, M.one_mem, by simp⟩)
    (fun m hm => ⟨1, N.one_mem, m, hm, by simp⟩)
  exact this hx

def prodSub (Q M J : Subgroup Γ) (h : ∀ q ∈ Q, ∀ m ∈ M, q * m = m * q) : Subgroup Γ where
  carrier := {x | x ∈ J ∧ ∃ q ∈ Q, ∃ m ∈ M, x = q * m}
  one_mem' := ⟨J.one_mem, 1, Q.one_mem, 1, M.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨hx, q, hq, m, hm, rfl⟩ ⟨hy, q', hq', m', hm', rfl⟩
    refine ⟨J.mul_mem hx hy, q * q', Q.mul_mem hq hq', m * m', M.mul_mem hm hm', ?_⟩
    have := h q' hq' m hm
    calc q * m * (q' * m') = q * (m * q') * m' := by group
      _ = q * (q' * m) * m' := by rw [← this]
      _ = _ := by group
  inv_mem' := by
    rintro _ ⟨hx, q, hq, m, hm, rfl⟩
    refine ⟨J.inv_mem hx, q⁻¹, Q.inv_mem hq, m⁻¹, M.inv_mem hm, ?_⟩
    have := h q⁻¹ (Q.inv_mem hq) m⁻¹ (M.inv_mem hm)
    rw [mul_inv_rev]
    exact this.symm

theorem commutatorElement_mem {J : Subgroup Γ} {a b : Γ} (ha : a ∈ J) (hb : b ∈ J) : ⁅a, b⁆ ∈ J := by
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)

theorem commutator_self_le (Q : Subgroup Γ) : ⁅Q, Q⁆ ≤ Q :=
  Subgroup.commutator_le.mpr fun _ ha _ hb => commutatorElement_mem ha hb

theorem perfect_le_of_central_product (t : Γ) (N M J : Subgroup Γ)
    (hNM : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n)
    (hNt : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M)
    (hJ : J ≤ N ⊔ M) (hJt : ∀ j ∈ J, j * t = t * j)
    (hJs : IsSimpleGroup J) (hJp : ⁅J, J⁆ = J)
    (hHJ : ∀ Q : Subgroup Γ, Q ≤ N → (∀ q ∈ Q, q * t = t * q) → ⁅Q, Q⁆ = Q → Q ≤ J)
    (hNJ : ¬ ∀ n ∈ N, ∀ j ∈ J, n * j = j * n) : J ≤ N := by
  let D : Subgroup Γ :=
    { carrier := {n | n ∈ N ∧ ∃ m ∈ M, n * m ∈ J}
      one_mem' := ⟨N.one_mem, 1, M.one_mem, by simpa using J.one_mem⟩
      mul_mem' := by
        rintro n n' ⟨hn, m, hm, hj⟩ ⟨hn', m', hm', hj'⟩
        refine ⟨N.mul_mem hn hn', m * m', M.mul_mem hm hm', ?_⟩
        have := hNM n' hn' m hm
        have e : (n * n') * (m * m') = (n * m) * (n' * m') := by
          calc (n * n') * (m * m') = n * (n' * m) * m' := by group
            _ = n * (m * n') * m' := by rw [this]
            _ = _ := by group
        rw [e]; exact J.mul_mem hj hj'
      inv_mem' := by
        rintro n ⟨hn, m, hm, hj⟩
        refine ⟨N.inv_mem hn, m⁻¹, M.inv_mem hm, ?_⟩
        have := hNM n⁻¹ (N.inv_mem hn) m⁻¹ (M.inv_mem hm)
        have e : n⁻¹ * m⁻¹ = (n * m)⁻¹ := by rw [mul_inv_rev]; exact this
        rw [e]; exact J.inv_mem hj }
  have hDN : D ≤ N := fun n hn => hn.1
  have hDJ : ∀ j ∈ J, ∃ d ∈ D, ∃ m ∈ M, j = d * m := by
    intro j hj
    obtain ⟨n, hn, m, hm, rfl⟩ := exists_mul_of_mem_sup hNM (hJ hj)
    exact ⟨n, ⟨hn, m, hm, hj⟩, m, hm, rfl⟩
  have hDt : ∀ d ∈ D, ∃ c, c ∈ N ∧ c ∈ M ∧ t * d * t⁻¹ = d * c := by
    rintro d ⟨hdN, m, hm, hj⟩
    have hc := hJt _ hj
    have h1 : t * d * t⁻¹ * (t * m * t⁻¹) = d * m := by
      calc t * d * t⁻¹ * (t * m * t⁻¹) = t * (d * m) * t⁻¹ := by group
        _ = d * m := by rw [← hc]; group
    refine ⟨d⁻¹ * (t * d * t⁻¹), N.mul_mem (N.inv_mem hdN) (hNt d hdN), ?_, by group⟩
    have : d⁻¹ * (t * d * t⁻¹) = m * (t * m * t⁻¹)⁻¹ := by
      calc d⁻¹ * (t * d * t⁻¹)
          = d⁻¹ * (t * d * t⁻¹ * (t * m * t⁻¹)) * (t * m * t⁻¹)⁻¹ := by group
        _ = _ := by rw [h1]; group
    rw [this]
    exact M.mul_mem hm (M.inv_mem (hMt m hm))
  set Q : Subgroup Γ := ⁅D, D⁆ with hQdef
  have hQN : Q ≤ N := by
    refine Subgroup.commutator_le.mpr fun d hd d' hd' => ?_
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hDN hd) (hDN hd')) (N.inv_mem (hDN hd)))
      (N.inv_mem (hDN hd'))
  have hQM : ∀ q ∈ Q, ∀ m ∈ M, q * m = m * q := fun q hq m hm => hNM q (hQN hq) m hm
  have hQt : ∀ q ∈ Q, q * t = t * q := by
    have : Q ≤ Subgroup.centralizer ({t} : Set Γ) := by
      refine Subgroup.commutator_le.mpr fun d hd d' hd' => ?_
      obtain ⟨c, hcN, hcM, hc⟩ := hDt d hd
      obtain ⟨c', hcN', hcM', hc'⟩ := hDt d' hd'
      have hconj : t * ⁅d, d'⁆ * t⁻¹ = ⁅d, d'⁆ := by
        have e : t * ⁅d, d'⁆ * t⁻¹ = ⁅t * d * t⁻¹, t * d' * t⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e, hc, hc']
        exact comm_mul_central (Commute.symm (hNM d' (hDN hd') c hcM))
          (Commute.symm (hNM d (hDN hd) c' hcM')) (hNM c' hcN' c hcM)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ⁅d, d'⁆ * t = (t * ⁅d, d'⁆ * t⁻¹) * t := by rw [hconj]
        _ = t * ⁅d, d'⁆ := by group
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hq)
  have hA : ∀ j ∈ J, ∃ q ∈ Q, ∃ m ∈ M, j = q * m := by
    have hle : J ≤ prodSub Q M J hQM := by
      calc J = ⁅J, J⁆ := hJp.symm
        _ ≤ _ := by
          refine Subgroup.commutator_le.mpr fun j hj j' hj' => ?_
          obtain ⟨d, hd, m, hm, rfl⟩ := hDJ j hj
          obtain ⟨d', hd', m', hm', rfl⟩ := hDJ j' hj'
          refine ⟨commutatorElement_mem hj hj', ⁅d, d'⁆, Subgroup.commutator_mem_commutator hd hd',
            ⁅m, m'⁆, ?_, ?_⟩
          · rw [commutatorElement_def]
            exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')
          · exact comm_mul_mul (hNM d (hDN hd) m hm) (hNM d (hDN hd) m' hm')
              (hNM d' (hDN hd') m hm) (hNM d' (hDN hd') m' hm')
    intro j hj
    exact (hle hj).2
  have hQQ : ⁅Q, Q⁆ ≤ Q := commutator_self_le Q
  have hQQM : ∀ q ∈ ⁅Q, Q⁆, ∀ m ∈ M, q * m = m * q := fun q hq m hm => hQM q (hQQ hq) m hm
  have hA2 : ∀ j ∈ J, ∃ q ∈ ⁅Q, Q⁆, ∃ m ∈ M, j = q * m := by
    have hle : J ≤ prodSub ⁅Q, Q⁆ M J hQQM := by
      calc J = ⁅J, J⁆ := hJp.symm
        _ ≤ _ := by
          refine Subgroup.commutator_le.mpr fun j hj j' hj' => ?_
          obtain ⟨q, hq, m, hm, rfl⟩ := hA j hj
          obtain ⟨q', hq', m', hm', rfl⟩ := hA j' hj'
          refine ⟨commutatorElement_mem hj hj', ⁅q, q'⁆, Subgroup.commutator_mem_commutator hq hq',
            ⁅m, m'⁆, ?_, ?_⟩
          · rw [commutatorElement_def]
            exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')
          · exact comm_mul_mul (hQM q hq m hm) (hQM q hq m' hm')
              (hQM q' hq' m hm) (hQM q' hq' m' hm')
    intro j hj
    exact (hle hj).2
  have hperf : ⁅Q, Q⁆ = Q := by
    refine le_antisymm hQQ ?_
    have hsplit : ∀ d ∈ D, ∃ q ∈ ⁅Q, Q⁆, ∃ c, c ∈ N ∧ c ∈ M ∧ d = q * c := by
      intro d hd
      obtain ⟨hdN, m₀, hm₀, hj⟩ := hd
      obtain ⟨q, hq, m', hm', hqm⟩ := hA2 _ hj
      refine ⟨q, hq, q⁻¹ * d, N.mul_mem (N.inv_mem (hQN (hQQ hq))) hdN, ?_, by group⟩
      have : q⁻¹ * d = m' * m₀⁻¹ := by
        calc q⁻¹ * d = q⁻¹ * (d * m₀) * m₀⁻¹ := by group
          _ = q⁻¹ * (q * m') * m₀⁻¹ := by rw [hqm]
          _ = m' * m₀⁻¹ := by group
      rw [this]
      exact M.mul_mem hm' (M.inv_mem hm₀)
    refine Subgroup.commutator_le.mpr fun d hd d' hd' => ?_
    obtain ⟨q, hq, c, hcN, hcM, rfl⟩ := hsplit d hd
    obtain ⟨q', hq', c', hcN', hcM', rfl⟩ := hsplit d' hd'
    rw [comm_mul_central (Commute.symm (hNM q' (hQN (hQQ hq')) c hcM))
      (Commute.symm (hNM q (hQN (hQQ hq)) c' hcM')) (hNM c' hcN' c hcM)]
    exact Subgroup.commutator_mem_commutator (hQQ hq) (hQQ hq')
  have hQJ : Q ≤ J := hHJ Q hQN hQt hperf
  have hnorm : (M.subgroupOf J).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨n, hn, m', hm', hg⟩ := exists_mul_of_mem_sup hNM (hJ g.2)
    have hx' : (x : Γ) ∈ M := hx
    show ((g : Γ) * x * (g : Γ)⁻¹) ∈ M
    have hy : m' * x * m'⁻¹ ∈ M := M.mul_mem (M.mul_mem hm' hx') (M.inv_mem hm')
    have e : (g : Γ) * x * (g : Γ)⁻¹ = n * (m' * x * m'⁻¹) * n⁻¹ := by rw [hg]; group
    have e2 : n * (m' * x * m'⁻¹) = (m' * x * m'⁻¹) * n := hNM n hn _ hy
    rw [e, e2]
    simpa using hy
  intro j hj
  rcases hJs.eq_bot_or_eq_top_of_normal (M.subgroupOf J) with h | h
  · obtain ⟨q, hq, m, hm, rfl⟩ := hA j hj
    have hmJ : m ∈ J := by
      have := J.mul_mem (J.inv_mem (hQJ hq)) hj
      simpa using this
    have hmem : (⟨m, hmJ⟩ : ↥J) ∈ M.subgroupOf J := hm
    rw [h, Subgroup.mem_bot] at hmem
    have : m = 1 := congrArg Subtype.val hmem
    subst this
    simpa using hQN hq
  · exfalso
    apply hNJ
    intro n hn j' hj'
    have : (⟨j', hj'⟩ : ↥J) ∈ M.subgroupOf J := by rw [h]; trivial
    exact hNM n hn j' this

end Algebra

section Components

variable {Γ : Type*} [Group Γ] [Finite Γ]

abbrev cj (t : Γ) (K : Subgroup Γ) : Subgroup Γ := K.map (MulAut.conj t).toMonoidHom

theorem mem_cj {t : Γ} (ht : t * t = 1) {K : Subgroup Γ} {x : Γ} :
    x ∈ cj t K ↔ t * x * t⁻¹ ∈ K := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : t * (t * y * t⁻¹) * t⁻¹ = y := by rw [hti]; calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [this]; exact hy
  · intro h
    refine ⟨t * x * t⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hti]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group

theorem cj_cj {t : Γ} (ht : t * t = 1) (K : Subgroup Γ) : cj t (cj t K) = K := by
  ext x
  rw [mem_cj ht, mem_cj ht]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have : t * (t * x * t⁻¹) * t⁻¹ = x := by
    rw [hti]; calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group
  rw [this]

theorem isComponent_cj (t : Γ) {K : Subgroup Γ} (hK : IsComponent K) : IsComponent (cj t K) :=
  isComponent_map_mulEquiv (MulAut.conj t) hK

theorem le_centralizer_of_ne {A B : Subgroup Γ} (hA : IsComponent A) (hB : IsComponent B)
    (h : A ≠ B) : A ≤ Subgroup.centralizer (B : Set Γ) := by
  rcases distinct_components_commute hA hB with h' | h'
  · exact absurd h' h
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h'

theorem orbit_commute {t : Γ} (ht : t * t = 1) {K K' : Subgroup Γ} (hK : IsComponent K)
    (hK' : IsComponent K') (h1 : K' ≠ K) (h2 : K' ≠ cj t K) :
    K ⊔ cj t K ≤ Subgroup.centralizer ((K' ⊔ cj t K' : Subgroup Γ) : Set Γ) := by
  have h3 : cj t K' ≠ K := fun h => h2 (by rw [← h, cj_cj ht])
  have h4 : cj t K' ≠ cj t K := fun h => h1 (by
    have := congrArg (cj t) h
    rwa [cj_cj ht, cj_cj ht] at this)
  have hcK := isComponent_cj t hK
  have hcK' := isComponent_cj t hK'
  have key : ∀ A : Subgroup Γ, IsComponent A → A ≠ K' → A ≠ cj t K' →
      A ≤ Subgroup.centralizer ((K' ⊔ cj t K' : Subgroup Γ) : Set Γ) := by
    intro A hA hA1 hA2
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (le_centralizer_of_ne hK' hA hA1.symm) (le_centralizer_of_ne hcK' hA hA2.symm)
  exact sup_le (key K hK h1.symm h3.symm) (key (cj t K) hcK h2.symm h4.symm)

theorem J_le_orbit {t : Γ} (ht : t * t = 1) {J : Subgroup Γ} (hJs : IsSimpleGroup J)
    (hJp : ⁅J, J⁆ = J) (hJE : J ≤ layer Γ) (hJt : ∀ j ∈ J, j * t = t * j)
    (hHJ : ∀ Q : Subgroup Γ, Q ≤ layer Γ → (∀ q ∈ Q, q * t = t * q) → ⁅Q, Q⁆ = Q → Q ≤ J)
    (hZ : ∀ K : Subgroup Γ, IsComponent K → ¬ ∀ k ∈ K, ∀ j ∈ J, k * j = j * k)
    {K : Subgroup Γ} (hK : IsComponent K) : J ≤ K ⊔ cj t K := by
  have hcK := isComponent_cj t hK
  set N : Subgroup Γ := K ⊔ cj t K with hN
  set M : Subgroup Γ := sSup {K' | IsComponent K' ∧ K' ≠ K ∧ K' ≠ cj t K} with hM
  have hNle : N ≤ layer Γ := sup_le (component_le_layer hK) (component_le_layer hcK)
  have hNMc : N ≤ Subgroup.centralizer (M : Set Γ) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sSup_le fun K' hK' => le_centralizer_of_ne hK'.1 hK hK'.2.1
    · rw [Subgroup.le_centralizer_iff]
      exact sSup_le fun K' hK' => le_centralizer_of_ne hK'.1 hcK hK'.2.2
  have hNM : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n := fun n hn m hm =>
    (Subgroup.mem_centralizer_iff.1 (hNMc hn) m hm).symm
  have hNt : ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    have : N ≤ N.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun k hk => ?_) (fun x hx => ?_)
      · show (MulAut.conj t).toMonoidHom k ∈ N
        exact Subgroup.mem_sup_right ⟨k, hk, rfl⟩
      · show (MulAut.conj t).toMonoidHom x ∈ N
        have := (mem_cj ht).1 hx
        simpa [MulAut.conj_apply] using Subgroup.mem_sup_left this
    intro n hn
    simpa [MulAut.conj_apply] using this hn
  have hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M := by
    have : M ≤ M.comap (MulAut.conj t).toMonoidHom := by
      refine sSup_le fun K' hK' k hk => ?_
      obtain ⟨hc, h1, h2⟩ := hK'
      show (MulAut.conj t).toMonoidHom k ∈ M
      have hcc : cj t K' ≤ M := by
        refine le_sSup ⟨isComponent_cj t hc, ?_, ?_⟩
        · intro h; exact h2 (by rw [← h, cj_cj ht])
        · intro h; exact h1 (by
            have := congrArg (cj t) h
            rwa [cj_cj ht, cj_cj ht] at this)
      exact hcc ⟨k, hk, rfl⟩
    intro m hm
    simpa [MulAut.conj_apply] using this hm
  have hJNM : J ≤ N ⊔ M := by
    refine hJE.trans (sSup_le fun K' hK' => ?_)
    by_cases h1 : K' = K
    · rw [h1]; exact le_sup_left.trans le_sup_left
    by_cases h2 : K' = cj t K
    · rw [h2]; exact le_sup_right.trans le_sup_left
    · exact (le_sSup ⟨hK', h1, h2⟩ : K' ≤ M).trans le_sup_right
  exact perfect_le_of_central_product t N M J hNM hNt hMt hJNM hJt hJs hJp
    (fun Q hQ => hHJ Q (hQ.trans hNle))
    (fun h => hZ K hK fun k hk j hj => h k ((le_sup_left : K ≤ K ⊔ cj t K) hk) j hj)

theorem single_orbit {t : Γ} (ht : t * t = 1) {J : Subgroup Γ} (hJs : IsSimpleGroup J)
    (hJp : ⁅J, J⁆ = J) (hJE : J ≤ layer Γ) (hJt : ∀ j ∈ J, j * t = t * j)
    (hHJ : ∀ Q : Subgroup Γ, Q ≤ layer Γ → (∀ q ∈ Q, q * t = t * q) → ⁅Q, Q⁆ = Q → Q ≤ J)
    (hZ : ∀ K : Subgroup Γ, IsComponent K → ¬ ∀ k ∈ K, ∀ j ∈ J, k * j = j * k) :
    ∃ K, IsComponent K ∧ ∀ K', IsComponent K' → K' = K ∨ K' = cj t K := by
  obtain ⟨j, hj1⟩ := exists_ne (1 : J)
  have hcomp : ∃ K : Subgroup Γ, IsComponent K := by
    by_contra h
    push Not at h
    have := layer_eq_bot_of_forall h
    apply hj1
    have : (j : Γ) ∈ (⊥ : Subgroup Γ) := this ▸ hJE j.2
    exact Subtype.ext (by simpa using this)
  obtain ⟨K, hK⟩ := hcomp
  refine ⟨K, hK, fun K' hK' => ?_⟩
  by_contra hne
  push Not at hne
  have hJ1 := J_le_orbit ht hJs hJp hJE hJt hHJ hZ hK
  have hJ2 := J_le_orbit ht hJs hJp hJE hJt hHJ hZ hK'
  have hab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
    intro a ha b hb
    have := orbit_commute ht hK hK' hne.1 hne.2 (hJ1 ha)
    exact (Subgroup.mem_centralizer_iff.1 this b (hJ2 hb)).symm
  apply hj1
  have : ⁅J, J⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hab a ha b hb
  have hJbot : J = ⊥ := hJp.symm.trans this
  exact Subtype.ext ((Subgroup.eq_bot_iff_forall J).1 hJbot j j.2)

end Components

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
