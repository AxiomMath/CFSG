module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Cent
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits

section Fixfree

variable {Y : Type*} [Group Y]

theorem a6grp_conj_inv (O : Subgroup Y) [O.Normal] [Finite O] {t : Y} (ht : t * t = 1)
    (hfix : ∀ c ∈ O, t * c = c * t → c = 1) : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let f : O → O := fun g => ⟨(g : Y)⁻¹ * (t * g * t⁻¹),
    mul_mem (inv_mem g.2) (Subgroup.Normal.conj_mem (inferInstance : O.Normal) (g : Y) g.2 t)⟩
  have hinj : Function.Injective f := by
    intro g k hgk
    have hfg : (g : Y)⁻¹ * (t * g * t⁻¹) = (k : Y)⁻¹ * (t * k * t⁻¹) := congrArg Subtype.val hgk
    have h1 : (k : Y) * (g : Y)⁻¹ * t = t * ((k : Y) * (g : Y)⁻¹) := by
      have e : (k : Y) * ((g : Y)⁻¹ * (t * g * t⁻¹)) = t * k * t⁻¹ := by
        rw [hfg]; group
      calc (k : Y) * (g : Y)⁻¹ * t
          = ((k : Y) * ((g : Y)⁻¹ * (t * g * t⁻¹))) * (t * (g : Y)⁻¹) := by group
        _ = (t * k * t⁻¹) * (t * (g : Y)⁻¹) := by rw [e]
        _ = t * ((k : Y) * (g : Y)⁻¹) := by group
    have h2 : (k : Y) * (g : Y)⁻¹ = 1 := hfix _ (mul_mem k.2 (inv_mem g.2)) h1.symm
    exact Subtype.ext (mul_inv_eq_one.mp h2).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro o ho
  obtain ⟨g, hg⟩ := hsurj ⟨o, ho⟩
  have hg' : (g : Y)⁻¹ * (t * g * t⁻¹) = o := congrArg Subtype.val hg
  rw [← hg']
  simp only [mul_inv_rev, htinv, inv_inv, mul_assoc, ht, mul_one]

theorem a6grp_comm_of_conj_inv (O : Subgroup Y) {t : Y} (hinv : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹) :
    ∀ a ∈ O, ∀ b ∈ O, a * b = b * a := by
  intro a ha b hb
  have h1 : t * (a * b) * t⁻¹ = (a * b)⁻¹ := hinv _ (mul_mem ha hb)
  have h2 : t * (a * b) * t⁻¹ = a⁻¹ * b⁻¹ := by
    calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [hinv a ha, hinv b hb]
  have h3 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by rw [← h2, h1, mul_inv_rev]
  have h4 := congrArg (fun w : Y => w⁻¹) h3
  simpa using h4.symm

end Fixfree

section NormalForms

variable {Y : Type*} [Group Y] {t u x : Y}

theorem a6grp_pow_nf (h : I21.CRel t u x) (n a i j : ℕ) :
    ∃ m : ℕ, (t ^ a * x ^ i * u ^ j) ^ n = t ^ (n * a) * x ^ m * u ^ (n * j) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + i * 2 ^ (n * j), ?_⟩
    rw [pow_succ, hm, h.nf_mul, show (n + 1) * a = n * a + a by ring,
      show (n + 1) * j = n * j + j by ring]

theorem a6grp_exists_pow_of_odd (h : I21.CRel t u x) {c : Y}
    (hc : c ∈ closure ({t, u, x} : Set Y)) {m : ℕ} (hm : Odd m) (hcm : c ^ m = 1) :
    ∃ i : ℕ, c = x ^ i := by
  obtain ⟨a, i, j, rfl⟩ := h.mem_closure_iff.mp hc
  obtain ⟨m', hm'⟩ := a6grp_pow_nf h m a i j
  rw [hm', h.nf_eq_one_iff] at hcm
  obtain ⟨ha, -, hj⟩ := hcm
  have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  have ha' : 2 ∣ a := hcop.dvd_of_dvd_mul_left ha
  have hj' : 4 ∣ j := (Nat.Coprime.pow_left 2 hcop).dvd_of_dvd_mul_left (by simpa using hj)
  refine ⟨i, ?_⟩
  have h1 : t ^ a = 1 := by
    obtain ⟨k, hk⟩ := ha'
    rw [hk, pow_mul, h.t_sq, one_pow]
  have h2 : u ^ j = 1 := by
    obtain ⟨k, hk⟩ := hj'
    rw [hk, pow_mul, h.u_four, one_pow]
  rw [h1, h2, one_mul, mul_one]

end NormalForms

section Hyp

variable {Y : Type*} [Group Y] {t u x : Y}

theorem a6grp_exists_crel (hs : SecTwoHyp Y t u) (hx : orderOf x = 5) (htx : t * x = x * t)
    (hux : u * x * u⁻¹ = x ^ 2 ∨ u * x * u⁻¹ = x ^ 3) :
    ∃ u' : Y, I21.CRel t u' x ∧ closure ({t, u', x} : Set Y) = closure ({t, u, x} : Set Y) ∧
      u' ^ 2 = u ^ 2 := by
  have h5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  rcases hux with h2 | h3
  · exact ⟨u, ⟨hs.t_sq, hs.u_pow_four, h5, hs.commute, htx, h2, hs.t_ne_one, hs.z_ne_one,
      hs.sq_ne⟩, rfl, rfl⟩
  · have hz : (u⁻¹) ^ 2 = u ^ 2 := by rw [inv_pow]; exact hs.z_inv
    have h2' : u⁻¹ * x * (u⁻¹)⁻¹ = x ^ 2 := by
      have ha3 : (u⁻¹ * x * (u⁻¹)⁻¹) ^ 3 = x := by rw [conj_pow, ← h3]; group
      have ha5 : (u⁻¹ * x * (u⁻¹)⁻¹) ^ 5 = 1 := by rw [conj_pow, h5]; group
      calc u⁻¹ * x * (u⁻¹)⁻¹ = (u⁻¹ * x * (u⁻¹)⁻¹) ^ 5 * (u⁻¹ * x * (u⁻¹)⁻¹) := by
            rw [ha5, one_mul]
        _ = (u⁻¹ * x * (u⁻¹)⁻¹) ^ 6 := (pow_succ _ 5).symm
        _ = ((u⁻¹ * x * (u⁻¹)⁻¹) ^ 3) ^ 2 := by rw [← pow_mul]
        _ = x ^ 2 := by rw [ha3]
    have hcl : closure ({t, u⁻¹, x} : Set Y) = closure ({t, u, x} : Set Y) := by
      apply le_antisymm
      · rw [closure_le]
        intro g hg
        rcases hg with h1 | h1 | h1 <;> rw [h1]
        · exact subset_closure (by simp)
        · exact inv_mem (subset_closure (by simp))
        · exact subset_closure (by simp)
      · rw [closure_le]
        intro g hg
        rcases hg with h1 | h1 | h1 <;> rw [h1]
        · exact subset_closure (by simp)
        · simpa using inv_mem (subset_closure (show u⁻¹ ∈ ({t, u⁻¹, x} : Set Y) by simp))
        · exact subset_closure (by simp)
    refine ⟨u⁻¹, ⟨hs.t_sq, ?_, h5, ?_, htx, h2', hs.t_ne_one, ?_, ?_⟩, hcl, hz⟩
    · rw [inv_pow, hs.u_pow_four, inv_one]
    · exact (show Commute t u from hs.commute).inv_right.eq
    · rw [hz]; exact hs.z_ne_one
    · rw [hz]; exact hs.sq_ne

theorem a6grp_fixfree (hc : I21.CRel t u x) (hx : orderOf x = 5)
    (hC : centralizer ({t} : Set Y) = closure ({t, u, x} : Set Y)) {O : Subgroup Y}
    (hO : Odd (Nat.card O)) (hxO : x ∉ O) : ∀ c ∈ O, t * c = c * t → c = 1 := by
  intro c hcO htc
  have hcC : c ∈ closure ({t, u, x} : Set Y) := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact htc.symm
  have hodd : Odd (orderOf c) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hcO)
  obtain ⟨i, hi⟩ := a6grp_exists_pow_of_odd hc hcC hodd (pow_orderOf_eq_one c)
  by_contra hc1
  apply hxO
  have hi5 : ¬ 5 ∣ i := by
    intro h5
    apply hc1
    rw [hi]
    obtain ⟨k, hk⟩ := h5
    rw [hk, pow_mul, hc.x_five, one_pow]
  have hcop : Nat.Coprime i (orderOf x) := by
    rw [hx]
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hi5).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, ← hi]
  exact pow_mem hcO m

theorem a6grp_oddCore_abelian [Finite Y] {h : Y} (hs : SecTwoHyp Y t u) (hx : orderOf x = 5)
    (htx : t * x = x * t) (hux : u * x * u⁻¹ = x ^ 2 ∨ u * x * u⁻¹ = x ^ 3)
    (hC : centralizer ({t} : Set Y) = closure ({t, u, x} : Set Y))
    (hh : h * t * h⁻¹ = t * u ^ 2) (hxO : x ∉ standardComponentOddCore Y) :
    (∀ o ∈ standardComponentOddCore Y, t * o * t⁻¹ = o⁻¹) ∧
      (∀ a ∈ standardComponentOddCore Y, ∀ b ∈ standardComponentOddCore Y, a * b = b * a) ∧
      ∀ o ∈ standardComponentOddCore Y, u ^ 2 * o = o * u ^ 2 := by
  obtain ⟨u', hc, hcl, -⟩ := a6grp_exists_crel hs hx htx hux
  have hC' : centralizer ({t} : Set Y) = closure ({t, u', x} : Set Y) := by rw [hcl, hC]
  have hfix := a6grp_fixfree hc hx hC' secTwo_odd_card_oddCore hxO
  have hinv := a6grp_conj_inv (standardComponentOddCore Y) hs.t_mul_t hfix
  refine ⟨hinv, a6grp_comm_of_conj_inv _ hinv, ?_⟩
  intro o ho
  have hn : (standardComponentOddCore Y).Normal := inferInstance
  have h1 : (t * u ^ 2) * o * (t * u ^ 2)⁻¹ = o⁻¹ := by
    have e1 : t * (h⁻¹ * o * h) * t⁻¹ = (h⁻¹ * o * h)⁻¹ := hinv _ (hn.conj_mem' o ho h)
    rw [← hh]
    calc h * t * h⁻¹ * o * (h * t * h⁻¹)⁻¹ = h * (t * (h⁻¹ * o * h) * t⁻¹) * h⁻¹ := by group
      _ = h * (h⁻¹ * o * h)⁻¹ * h⁻¹ := by rw [e1]
      _ = o⁻¹ := by group
  have h2 : t * o⁻¹ * t⁻¹ = o := by rw [hinv _ (inv_mem ho), inv_inv]
  have htinv : t⁻¹ = t := hs.t_inv
  have h3 : u ^ 2 * o * (u ^ 2)⁻¹ = o := by
    have e : u ^ 2 * o * (u ^ 2)⁻¹ = t⁻¹ * ((t * u ^ 2) * o * (t * u ^ 2)⁻¹) * t := by group
    rw [e, h1, htinv]
    rw [htinv] at h2
    exact h2
  calc u ^ 2 * o = u ^ 2 * o * (u ^ 2)⁻¹ * u ^ 2 := by group
    _ = o * u ^ 2 := by rw [h3]

end Hyp

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
