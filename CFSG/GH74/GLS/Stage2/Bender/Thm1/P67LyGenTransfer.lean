module

public import CFSG.Sporadic.Recognition.LyonsAS4Local
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyGen

open Subgroup Equiv Equiv.Perm CFSG.Sporadic.Recognition.LyonsSims

theorem map_centralizer_singleton {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    (centralizer ({a} : Set A)).map φ.toMonoidHom = centralizer ({φ a} : Set B) := by
  ext b
  simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hg]
  · intro hb
    refine ⟨φ.symm b, ?_, by simp⟩
    apply φ.injective
    rw [map_mul, map_mul]
    simpa using hb

theorem sup_centralizer_equiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) {a b : A}
    (h : centralizer ({a} : Set A) ⊔ centralizer ({b} : Set A) = ⊤) :
    centralizer ({φ a} : Set B) ⊔ centralizer ({φ b} : Set B) = ⊤ := by
  rw [← map_centralizer_singleton φ a, ← map_centralizer_singleton φ b, ← Subgroup.map_sup, h,
    ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 φ.surjective

theorem sup_centralizer_conj {Y : Type*} [Group Y] {a b : Y}
    (h : centralizer ({a} : Set Y) ⊔ centralizer ({b} : Set Y) = ⊤) (c : Y) :
    centralizer ({c * a * c⁻¹} : Set Y) ⊔ centralizer ({c * b * c⁻¹} : Set Y) = ⊤ := by
  have := sup_centralizer_equiv (MulAut.conj c) h
  simpa only [MulAut.conj_apply] using this

theorem cycleType_of_orderOf_twentyone {τ : Perm (Fin 11)} (h : orderOf τ = 21) :
    τ.cycleType = {7, 3} := by
  classical
  set s := τ.cycleType with hs
  have hdvd : ∀ n ∈ s, n ∣ 21 := fun n hn => h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
  have h2 : ∀ n ∈ s, 2 ≤ n := fun n hn => Equiv.Perm.two_le_of_mem_cycleType hn
  have hsum : s.sum ≤ 11 := by simpa using Equiv.Perm.sum_cycleType_le τ
  have hlcm : s.lcm = 21 := by rw [hs, Equiv.Perm.lcm_cycleType, h]
  have hmem : ∀ n ∈ s, n = 3 ∨ n = 7 := by
    intro n hn
    have hn21 := hdvd n hn
    have hn2 := h2 n hn
    have hle : n ≤ 11 := (Multiset.le_sum_of_mem hn).trans hsum
    interval_cases n <;> omega
  have h7 : 7 ∈ s := by
    by_contra hno
    have hd : s.lcm ∣ 3 := Multiset.lcm_dvd.2 fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn hno
    rw [hlcm] at hd
    omega
  have h3 : 3 ∈ s := by
    by_contra hno
    have hd : s.lcm ∣ 7 := Multiset.lcm_dvd.2 fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact absurd hn hno
      · exact dvd_rfl
    rw [hlcm] at hd
    omega
  obtain ⟨s', hs'⟩ := Multiset.exists_cons_of_mem h7
  have h3' : 3 ∈ s' := by
    have : 3 ∈ 7 ::ₘ s' := hs' ▸ h3
    rcases Multiset.mem_cons.1 this with h | h
    · omega
    · exact h
  obtain ⟨s'', hs''⟩ := Multiset.exists_cons_of_mem h3'
  have hsum' : 7 + (3 + s''.sum) ≤ 11 := by
    rw [hs', hs'', Multiset.sum_cons, Multiset.sum_cons] at hsum
    exact hsum
  have hs''0 : s'' = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := Multiset.exists_mem_of_ne_zero hne
    have hle : n ≤ s''.sum := Multiset.le_sum_of_mem hn
    have hn2 : 2 ≤ n := h2 n (by rw [hs', hs'']; simp [hn])
    omega
  rw [hs', hs'', hs''0]
  rfl

@[expose] def tauP : Perm (Fin 11) :=
  (swap 3 4 * swap 4 5 * swap 5 6 * swap 6 7 * swap 7 8 * swap 8 9) * x1p

theorem tauP_pow_twentyone : tauP ^ 21 = 1 := by decide +kernel

theorem tauP_pow_seven : tauP ^ 7 = x1p := by decide +kernel

theorem tauP_pow_three : tauP ^ 3 ≠ 1 := by decide +kernel

theorem orderOf_tauP : orderOf tauP = 21 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) tauP_pow_twentyone fun p hp hpd => ?_
  have h21 : p ∣ 3 * 7 := hpd
  rcases (Nat.Prime.dvd_mul hp).1 h21 with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    rw [tauP_pow_seven]
    decide
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    exact tauP_pow_three

theorem cycleType_pow_seven {τ : Perm (Fin 11)} (h : orderOf τ = 21) :
    (τ ^ 7).cycleType = {3} := by
  have h1 : IsConj tauP τ := Equiv.Perm.isConj_of_cycleType_eq
    ((cycleType_of_orderOf_twentyone orderOf_tauP).trans (cycleType_of_orderOf_twentyone h).symm)
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  rw [← hc, conj_pow, tauP_pow_seven, Equiv.Perm.cycleType_conj, cycleType_x1p]

theorem orderOf_rho_of_orderOf {E : Type*} [Group E] {ρ : E →* Perm (Fin 11)} {z : E}
    (hc : IsCover11 ρ z) {x : E} (hx : orderOf x = 21) : orderOf (ρ x) = 21 := by
  have h21 : ρ x ^ 21 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h21 fun p hp hpd h1 => ?_
  have hker : x ^ (21 / p) = 1 ∨ x ^ (21 / p) = z :=
    hc.mem_ker_iff.1 (by rw [map_pow]; exact h1)
  have hp' : p = 3 ∨ p = 7 := by
    have h21 : p ∣ 3 * 7 := hpd
    rcases (Nat.Prime.dvd_mul hp).1 h21 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
  rcases hker with h | h
  · have := orderOf_dvd_of_pow_eq_one h
    rw [hx] at this
    rcases hp' with rfl | rfl <;> omega
  · have h2 : x ^ (2 * (21 / p)) = 1 := by rw [mul_comm, pow_mul, h, hc.sq_eq_one]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at this
    rcases hp' with rfl | rfl <;> omega

theorem sup_eq_top_of_gen_pair {Y X : Type} [Group Y] [Group X] (e : Y ≃* X) {s u : X}
    (hs : orderOf s = 2) (hu : orderOf u = 21) (hsu : s * u = u * s)
    (hgen : centralizer ({s} : Set X) ⊔ centralizer ({u ^ 7} : Set X) = ⊤)
    {t : Y} {ρ : ↥(centralizer ({t} : Set Y)) →* Perm (Fin 11)} (D : LyData Y t ρ)
    {x₁ : ↥(centralizer ({t} : Set Y))} (hx3 : x₁ ^ 3 = 1) (hxρ : ρ x₁ = x1p) :
    centralizer ({t} : Set Y) ⊔ centralizer ({(x₁ : Y)} : Set Y) = ⊤ := by
  classical
  have hs₁ : orderOf (e.symm s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs
  obtain ⟨c, hc⟩ := isConj_iff.1 (D.one_class t (e.symm s) D.order_t hs₁)
  have hcomm : t * (c⁻¹ * e.symm u * c) = (c⁻¹ * e.symm u * c) * t := by
    have h1 : e.symm s * e.symm u = e.symm u * e.symm s := by rw [← map_mul, ← map_mul, hsu]
    rw [← hc] at h1
    calc t * (c⁻¹ * e.symm u * c) = c⁻¹ * ((c * t * c⁻¹) * e.symm u) * c := by group
      _ = c⁻¹ * (e.symm u * (c * t * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * e.symm u * c) * t := by group
  have hu'ord : orderOf (c⁻¹ * e.symm u * c) = 21 := by
    have : c⁻¹ * e.symm u * c = (MulAut.conj c⁻¹) (e.symm u) := by
      simp
    rw [this, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hu
  have hgen' : centralizer ({t} : Set Y) ⊔
      centralizer ({(c⁻¹ * e.symm u * c) ^ 7} : Set Y) = ⊤ := by
    have h1 := sup_centralizer_equiv e.symm hgen
    have h2 := sup_centralizer_conj h1 c⁻¹
    have h3 : c⁻¹ * e.symm (u ^ 7) * c⁻¹⁻¹ = (c⁻¹ * e.symm u * c) ^ 7 := by
      have := conj_pow (a := c⁻¹) (b := e.symm u) (i := 7)
      rw [map_pow]
      simpa [inv_inv] using this.symm
    have h4 : c⁻¹ * e.symm s * c⁻¹⁻¹ = t := by rw [← hc]; group
    rwa [h4, h3] at h2
  let u'' : ↥(centralizer ({t} : Set Y)) :=
    ⟨c⁻¹ * e.symm u * c, mem_centralizer_singleton_iff.2 hcomm.symm⟩
  have hu''ord : orderOf u'' = 21 := by
    rw [← hu'ord, ← Subgroup.orderOf_coe]
  have hρord : orderOf (ρ u'') = 21 := orderOf_rho_of_orderOf D.cover hu''ord
  have hct : (ρ (u'' ^ 7)).cycleType = (ρ x₁).cycleType := by
    rw [map_pow, cycleType_pow_seven hρord, hxρ, cycleType_x1p]
  have hcube : (u'' ^ 7) ^ 3 = 1 := by
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hu''ord])
  obtain ⟨h, hh⟩ := isConj_iff.1 (D.cover.isConj_of_cycleType_eq hcube hx3 hct)
  have hht : (h : Y) * t * (h : Y)⁻¹ = t := by
    have h1 : (h : Y) * t = t * (h : Y) := mem_centralizer_singleton_iff.1 h.2
    calc (h : Y) * t * (h : Y)⁻¹ = (t * (h : Y)) * (h : Y)⁻¹ := by rw [h1]
      _ = t := by group
  have hhx : (h : Y) * (c⁻¹ * e.symm u * c) ^ 7 * (h : Y)⁻¹ = (x₁ : Y) := by
    have := congrArg Subtype.val hh
    simpa [u''] using this
  have := sup_centralizer_conj hgen' (h : Y)
  rwa [hht, hhx] at this

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyGen
