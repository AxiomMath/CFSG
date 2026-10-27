module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D2Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 E1 E2 : Subgroup G}

private theorem sec8d3_mem_sup_of_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [hAB a₂ ha₂ b₁ hb₁]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hAB a ha b hb]
        rw [mul_inv_rev, hc] }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by rw [mul_one]⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by rw [one_mul]⟩)
  exact hle hx

theorem sec8t84d3_E_inf_O (h : Sec8T84DCtx G t E X1 X2) :
    E ⊓ oddCoreIn (normalizer (E : Set G)) = ⊥ := by
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (oddCoreIn (normalizer (E : Set G)))) := by
    rw [h.elem.2]
    exact Nat.Coprime.pow_left 8 (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  exact disjoint_iff.mp (disjoint_of_coprime_natCard hcop)

theorem sec8t84d3_O_comm (h : Sec8T84DCtx G t E X1 X2) {o e : G}
    (ho : o ∈ oddCoreIn (normalizer (E : Set G))) (he : e ∈ E) : e * o = o * e :=
  (Subgroup.mem_centralizer_iff.mp (h.hO ho)) e he

theorem sec8t84d3_C_decomp (h : Sec8T84DCtx G t E X1 X2) {c : G}
    (hc : c ∈ centralizer (E : Set G)) :
    ∃ e ∈ E, ∃ o ∈ oddCoreIn (normalizer (E : Set G)), c = e * o := by
  have hc' : c ∈ E ⊔ oddCoreIn (normalizer (E : Set G)) := by rw [← h.hCE]; exact hc
  exact sec8d3_mem_sup_of_commute
    (fun e he o ho => sec8t84d3_O_comm h ho he) hc'

theorem sec8t84d3_E_decomp (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2)
    {e : G} (he : e ∈ E) : ∃ e1 ∈ E1, ∃ e2 ∈ E2, e = e1 * e2 := by
  have he' : e ∈ E1 ⊔ E2 := by rw [hd.sup]; exact he
  exact sec8d3_mem_sup_of_commute
    (fun a ha b hb =>
      congrArg Subtype.val ((h.elem.1.1.is_comm).comm ⟨a, hd.le1 ha⟩ ⟨b, hd.le2 hb⟩)) he'

theorem sec8t84d3_comm_E1 (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2)
    {a b : G} (ha : a ∈ X1) (hao : Odd (orderOf a)) (hb : b ∈ X2) :
    ∃ e ∈ E1, ∃ o ∈ oddCoreIn (normalizer (E : Set G)), a * b * a⁻¹ * b⁻¹ = e * o := by
  obtain ⟨e, he, o, ho, heo⟩ := sec8t84d3_C_decomp h (h.hX.comm a ha b hb)
  obtain ⟨e1, he1, e2, he2, he12⟩ := sec8t84d3_E_decomp h hd he
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((h.elem.1.1.is_comm).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hOE : ∀ o ∈ oddCoreIn (normalizer (E : Set G)), ∀ e ∈ E, o * e = e * o :=
    fun o ho e he => (sec8t84d3_O_comm h ho he).symm
  have hu1 : a * b * a⁻¹ * b⁻¹ = e1 * e2 * o := by rw [heo, he12]
  have hstep : ∀ k, a ^ (k + 1) * b * (a ^ (k + 1))⁻¹ * b⁻¹
      = (a * (a ^ k * b * (a ^ k)⁻¹ * b⁻¹) * a⁻¹) * (a * b * a⁻¹ * b⁻¹) := by
    intro k
    rw [pow_succ']
    group
  have hclaim : ∀ k, ∃ g ∈ E1, ∃ o' ∈ oddCoreIn (normalizer (E : Set G)),
      a ^ k * b * (a ^ k)⁻¹ * b⁻¹ = g * e2 ^ k * o' := by
    intro k
    induction k with
    | zero => exact ⟨1, E1.one_mem, 1, (oddCoreIn (normalizer (E : Set G))).one_mem, by simp⟩
    | succ k ih =>
        obtain ⟨g, hg, o', ho', hk⟩ := ih
        have hg' : a * g * a⁻¹ ∈ E1 := hd.inv1 a ha g hg
        have ho'' : a * o' * a⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
          conj_mem_oddCoreIn ((Subgroup.le_normalizer : normalizer (E : Set G) ≤
            normalizer ((normalizer (E : Set G)) : Set G)) (h.hX.le1 ha)) ho'
        have he2fix : a * e2 ^ k * a⁻¹ = e2 ^ k := by
          rw [← conj_pow, hd.triv1 a ha e2 he2]
        have hconj : a * (a ^ k * b * (a ^ k)⁻¹ * b⁻¹) * a⁻¹
            = (a * g * a⁻¹) * e2 ^ k * (a * o' * a⁻¹) := by
          calc a * (a ^ k * b * (a ^ k)⁻¹ * b⁻¹) * a⁻¹
              = a * (g * e2 ^ k * o') * a⁻¹ := by rw [hk]
            _ = (a * g * a⁻¹) * (a * e2 ^ k * a⁻¹) * (a * o' * a⁻¹) := by group
            _ = (a * g * a⁻¹) * e2 ^ k * (a * o' * a⁻¹) := by rw [he2fix]
        refine ⟨(a * g * a⁻¹) * e1, E1.mul_mem hg' he1,
          (a * o' * a⁻¹) * o, (oddCoreIn (normalizer (E : Set G))).mul_mem ho'' ho, ?_⟩
        rw [hstep k, hconj, hu1]
        calc
          ((a * g * a⁻¹) * e2 ^ k * (a * o' * a⁻¹)) * (e1 * e2 * o)
              = (a * g * a⁻¹) * e2 ^ k * ((a * o' * a⁻¹) * e1) * e2 * o := by group
            _ = (a * g * a⁻¹) * e2 ^ k * (e1 * (a * o' * a⁻¹)) * e2 * o := by
                  rw [hOE (a * o' * a⁻¹) ho'' e1 (hd.le1 he1)]
            _ = (a * g * a⁻¹) * e2 ^ k * e1 * ((a * o' * a⁻¹) * e2) * o := by group
            _ = (a * g * a⁻¹) * e2 ^ k * e1 * (e2 * (a * o' * a⁻¹)) * o := by
                  rw [hOE (a * o' * a⁻¹) ho'' e2 (hd.le2 he2)]
            _ = (a * g * a⁻¹) * (e2 ^ k * e1) * e2 * (a * o' * a⁻¹) * o := by group
            _ = (a * g * a⁻¹) * (e1 * e2 ^ k) * e2 * (a * o' * a⁻¹) * o := by
                  rw [hEcomm (e2 ^ k) (E.pow_mem (hd.le2 he2) k) e1 (hd.le1 he1)]
            _ = (a * g * a⁻¹) * e1 * (e2 ^ k * e2) * (a * o' * a⁻¹) * o := by group
            _ = ((a * g * a⁻¹) * e1) * e2 ^ (k + 1) * ((a * o' * a⁻¹) * o) := by
                  rw [pow_succ]; group
  set n := orderOf a with hn
  have hno : Odd n := by rw [hn]; exact hao
  obtain ⟨g, hg, o', ho', huk⟩ := hclaim n
  have han : a ^ n = 1 := by rw [hn, pow_orderOf_eq_one]
  have hun : a ^ n * b * (a ^ n)⁻¹ * b⁻¹ = 1 := by rw [han]; group
  have he2n : e2 ^ n = e2 := by
    obtain ⟨m, hm⟩ := hno
    have he2sq : e2 ^ 2 = 1 := hd.e16_2.1.2 e2 he2
    calc e2 ^ n = e2 ^ (2 * m + 1) := by rw [hm]
      _ = e2 ^ (2 * m) * e2 := by rw [pow_add, pow_one]
      _ = (e2 ^ 2) ^ m * e2 := by rw [pow_mul]
      _ = e2 := by rw [he2sq, one_pow, one_mul]
  have hun' : 1 = g * e2 * o' := by
    have hh := huk
    rw [hun, he2n] at hh
    exact hh
  have hgone : g * e2 = 1 := by
    have hgeo : g * e2 = o'⁻¹ := eq_inv_of_mul_eq_one_left hun'.symm
    have hgO : g * e2 ∈ oddCoreIn (normalizer (E : Set G)) := by
      rw [hgeo]; exact (oddCoreIn (normalizer (E : Set G))).inv_mem ho'
    have hgE : g * e2 ∈ E := E.mul_mem (hd.le1 hg) (hd.le2 he2)
    have : g * e2 ∈ (⊥ : Subgroup G) := by
      rw [← sec8t84d3_E_inf_O h]; exact ⟨hgE, hgO⟩
    exact Subgroup.mem_bot.mp this
  have he2g : e2 = g⁻¹ := eq_inv_of_mul_eq_one_right hgone
  have he2E1 : e2 ∈ E1 := by rw [he2g]; exact E1.inv_mem hg
  have he2one : e2 = 1 := by
    have hbot : e2 ∈ (⊥ : Subgroup G) := by
      rw [← hd.inf]; exact ⟨he2E1, he2⟩
    exact Subgroup.mem_bot.mp hbot
  refine ⟨e1, he1, o, ho, ?_⟩
  rw [heo, he12, he2one]
  group

theorem sec8t84d3_comm_E2 (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2)
    {a b : G} (ha : a ∈ X1) (hb : b ∈ X2) (hbo : Odd (orderOf b)) :
    ∃ e ∈ E2, ∃ o ∈ oddCoreIn (normalizer (E : Set G)), a * b * a⁻¹ * b⁻¹ = e * o := by
  obtain ⟨e, he, o, ho, heo⟩ := sec8t84d3_comm_E1 h.symm hd.symm hb hbo ha
  refine ⟨e⁻¹, E2.inv_mem he, o⁻¹, (oddCoreIn (normalizer (E : Set G))).inv_mem ho, ?_⟩
  have hcomm : e * o = o * e := sec8t84d3_O_comm h ho (hd.le2 he)
  calc a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
    _ = (e * o)⁻¹ := by rw [heo]
    _ = o⁻¹ * e⁻¹ := by rw [mul_inv_rev]
    _ = e⁻¹ * o⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcomm]

theorem sec8t84d3_comm_odd (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2)
    {a b : G} (ha : a ∈ X1) (hao : Odd (orderOf a)) (hb : b ∈ X2) (hbo : Odd (orderOf b)) :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := by
  obtain ⟨e1, he1, o1, ho1, h1⟩ := sec8t84d3_comm_E1 h hd ha hao hb
  obtain ⟨e2, he2, o2, ho2, h2⟩ := sec8t84d3_comm_E2 h hd ha hb hbo
  have heq : e1 * o1 = e2 * o2 := h1.symm.trans h2
  have hkey : e2⁻¹ * e1 = o2 * o1⁻¹ := by
    calc e2⁻¹ * e1 = e2⁻¹ * (e1 * o1) * o1⁻¹ := by group
      _ = e2⁻¹ * (e2 * o2) * o1⁻¹ := by rw [heq]
      _ = o2 * o1⁻¹ := by group
  have hmemO : e2⁻¹ * e1 ∈ oddCoreIn (normalizer (E : Set G)) := by
    rw [hkey]
    exact (oddCoreIn (normalizer (E : Set G))).mul_mem ho2
      ((oddCoreIn (normalizer (E : Set G))).inv_mem ho1)
  have hmemE : e2⁻¹ * e1 ∈ E := E.mul_mem (hd.le2 (E2.inv_mem he2)) (hd.le1 he1)
  have hbot : e2⁻¹ * e1 = 1 := by
    have : e2⁻¹ * e1 ∈ (⊥ : Subgroup G) := by
      rw [← sec8t84d3_E_inf_O h]; exact ⟨hmemE, hmemO⟩
    exact Subgroup.mem_bot.mp this
  have he1e2 : e1 = e2 := by
    have := congrArg (fun x => e2 * x) hbot
    simpa using this
  have he1one : e1 = 1 := by
    have hbot' : e1 ∈ (⊥ : Subgroup G) := by
      rw [← hd.inf]; exact ⟨he1, he1e2.symm ▸ he2⟩
    exact Subgroup.mem_bot.mp hbot'
  rw [h1, he1one, one_mul]
  exact ho1

end CFSG.OddStandard.SmallF3.Omega
