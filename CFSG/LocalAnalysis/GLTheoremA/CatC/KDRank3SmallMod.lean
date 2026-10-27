module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

namespace KDRank3SmallMod

theorem pure_id {M : Type*} [AddCommGroup M] (h2 : ∀ y : M, y + y = 0) (x y z p q r s : M) :
    x = (y + p + s) + (z + r + q) + (x + y + z) + (x + p + q) + (x + r + s) := by
  have e : (y + p + s) + (z + r + q) + (x + y + z) + (x + p + q) + (x + r + s)
      = x + ((x + x) + (y + y) + (p + p) + (s + s) + (z + z) + (r + r) + (q + q)) := by
    abel
  rw [e]
  simp [h2]

abbrev commGroupOfComm {G : Type} [Group G] {U : Subgroup G}
    (h : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) : CommGroup U :=
  { (inferInstance : Group U) with mul_comm := fun x y => Subtype.ext (h x x.2 y y.2) }

section Gen

variable {G : Type} [Group G]

theorem le_normalizer_of_comm {p : ℕ} {E A B : Subgroup G} (hE : IsElemAbelian p E)
    (hA : A ≤ E) (hB : B ≤ E) : B ≤ Subgroup.normalizer (A : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  by_cases hh : h ∈ E
  · have hcomm : c * h = h * c := isElemAbelian_commute hE (hB hc) hh
    have hconj : c * h * c⁻¹ = h := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
  · constructor
    · intro hA'
      exact (hh (hA hA')).elim
    · intro hc'
      have hE' : h ∈ E := by
        have : h = c⁻¹ * (c * h * c⁻¹) * c := by group
        rw [this]
        exact E.mul_mem (E.mul_mem (E.inv_mem (hB hc)) (hA hc')) (hB hc)
      exact (hh hE').elim

theorem eq_one_of_comm {E U : Subgroup G} (hE : IsElemAbelian 3 E)
    (hnorm : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U)
    (hirr : ∀ V : Subgroup G, V ≤ U → (∀ e ∈ E, ∀ v ∈ V, e * v * e⁻¹ ∈ V) → V = ⊥ ∨ V = U)
    {k : G} (hk : k ∈ E) (hkC : k ∉ Subgroup.centralizer (U : Set G)) {u : G} (hu : u ∈ U)
    (hcomm : k * u = u * k) : u = 1 := by
  set V : Subgroup G := U ⊓ Subgroup.centralizer ({k} : Set G) with hVdef
  have hVinv : ∀ e ∈ E, ∀ v ∈ V, e * v * e⁻¹ ∈ V := by
    intro e he v hv
    have hvU : v ∈ U := hv.1
    have hvk : v * k = k * v := Subgroup.mem_centralizer_singleton_iff.1 hv.2
    refine ⟨hnorm e he v hvU, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hek : k * e = e * k := isElemAbelian_commute hE hk he
    have hek' : k * e⁻¹ = e⁻¹ * k := isElemAbelian_commute hE hk (E.inv_mem he)
    calc e * v * e⁻¹ * k = e * v * (e⁻¹ * k) := by group
      _ = e * v * (k * e⁻¹) := by rw [hek']
      _ = e * (v * k) * e⁻¹ := by group
      _ = e * (k * v) * e⁻¹ := by rw [hvk]
      _ = (e * k) * v * e⁻¹ := by group
      _ = (k * e) * v * e⁻¹ := by rw [hek]
      _ = k * (e * v * e⁻¹) := by group
  rcases hirr V inf_le_left hVinv with hV | hV
  · have huV : u ∈ V := ⟨hu, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩
    rw [hV] at huV
    exact Subgroup.mem_bot.1 huV
  · exfalso
    apply hkC
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhV : h ∈ V := by
      rw [hV]
      exact hh
    exact Subgroup.mem_centralizer_singleton_iff.1 hhV.2

theorem orbit_eq_one {E U : Subgroup G} (hE : IsElemAbelian 3 E)
    (hnorm : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U)
    (hirr : ∀ V : Subgroup G, V ≤ U → (∀ e ∈ E, ∀ v ∈ V, e * v * e⁻¹ ∈ V) → V = ⊥ ∨ V = U)
    (hcommU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    {k : G} (hk : k ∈ E) (hkC : k ∉ Subgroup.centralizer (U : Set G)) {u : G} (hu : u ∈ U) :
    u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) = 1 := by
  have hk3 : k ^ 3 = 1 := hE.2 k hk
  have hα : k * u * k⁻¹ ∈ U := hnorm k hk u hu
  have hβ : k ^ 2 * u * (k ^ 2)⁻¹ ∈ U := hnorm (k ^ 2) (E.pow_mem hk 2) u hu
  have hv : u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) ∈ U := U.mul_mem (U.mul_mem hu hα) hβ
  have hconj : k * (u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹)) * k⁻¹
      = (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) * u := by
    have h3 : k * (u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹)) * k⁻¹
        = (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) * (k ^ 3 * u * (k ^ 3)⁻¹) := by group
    rw [h3, hk3]
    group
  have hcomm3 : (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) * u
      = u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) := by
    rw [mul_assoc, hcommU _ hβ u hu, ← mul_assoc, hcommU _ hα u hu]
  have hfix : k * (u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹)) * k⁻¹
      = u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) := hconj.trans hcomm3
  have hkv : k * (u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹))
      = (u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹)) * k := by
    calc k * (u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹))
        = k * (u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹)) * k⁻¹ * k := by group
      _ = (u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹)) * k := by rw [hfix]
  exact eq_one_of_comm hE hnorm hirr hk hkC hv hkv

theorem exists_gens [Finite G] {E C : Subgroup G} (hE : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 3) (hCE : C ≤ E) (hC : Nat.card C ≤ 3) :
    ∃ a ∈ E, ∃ b ∈ E, a ∉ C ∧ b ∉ C ∧ a * b ∉ C ∧ a * b ^ 2 ∉ C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h27 : Nat.card E = 27 := by rw [hEcard]; norm_num
  have hEC : ¬ E ≤ C := fun h => by
    have := Subgroup.card_le_of_le h
    omega
  obtain ⟨a, haE, haC⟩ := SetLike.not_le_iff_exists.1 hEC
  have ha3 : a ^ 3 = 1 := hE.2 a haE
  have ha1 : a ≠ 1 := fun h => haC (h ▸ C.one_mem)
  set Z : Subgroup G := Subgroup.zpowers a with hZdef
  have hZE : Z ≤ E := Subgroup.zpowers_le.2 haE
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hCnorm : C ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_of_comm hE hZE hCE
  have hprod := card_sup_mul_card_inf_of_le_normalizer hCnorm
  have hpos : 0 < Nat.card ↥(Z ⊓ C) := Nat.card_pos
  have hZC : Nat.card ↥(Z ⊔ C) ≤ 9 := by
    rw [hZcard] at hprod
    nlinarith
  have hEZC : ¬ E ≤ Z ⊔ C := fun h => by
    have := Subgroup.card_le_of_le h
    omega
  obtain ⟨b, hbE, hbZC⟩ := SetLike.not_le_iff_exists.1 hEZC
  have hb3 : b ^ 3 = 1 := hE.2 b hbE
  have hbC : b ∉ C := fun h => hbZC (Subgroup.mem_sup_right h)
  have haZ : a ∈ Z := Subgroup.mem_zpowers a
  have haZC : a⁻¹ ∈ Z ⊔ C := Subgroup.inv_mem _ (Subgroup.mem_sup_left haZ)
  refine ⟨a, haE, b, hbE, haC, hbC, ?_, ?_⟩
  · intro h
    apply hbZC
    have : a⁻¹ * (a * b) ∈ Z ⊔ C := Subgroup.mul_mem _ haZC (Subgroup.mem_sup_right h)
    simpa using this
  · intro h
    apply hbZC
    have h1 : a⁻¹ * (a * b ^ 2) ∈ Z ⊔ C := Subgroup.mul_mem _ haZC (Subgroup.mem_sup_right h)
    have h2 : b ^ 2 ∈ Z ⊔ C := by simpa using h1
    have h4 : (b ^ 2) ^ 2 = b := by
      have : (b ^ 2) ^ 2 = b ^ 3 * b := by group
      rw [this, hb3, one_mul]
    rw [← h4]
    exact Subgroup.pow_mem _ h2 2

theorem identity_one {E U : Subgroup G} (hE : IsElemAbelian 3 E)
    (hcommU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hsqU : ∀ x ∈ U, x * x = 1)
    (hnorm : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E)
    (hfix : ∀ k ∈ E, k ∉ Subgroup.centralizer (U : Set G) → ∀ u ∈ U,
      u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) = 1)
    (hA : a ∉ Subgroup.centralizer (U : Set G)) (hB : b ∉ Subgroup.centralizer (U : Set G))
    (hAB : a * b ∉ Subgroup.centralizer (U : Set G))
    (hAB2 : a * b ^ 2 ∉ Subgroup.centralizer (U : Set G))
    {w : G} (hw : w ∈ U) : w = 1 := by
  have hb3 : b ^ 3 = 1 := hE.2 b hb
  have hcommab : Commute a b := isElemAbelian_commute hE ha hb
  have hbE2 : b ^ 2 ∈ E := E.pow_mem hb 2
  have haE2 : a ^ 2 ∈ E := E.pow_mem ha 2
  have hab_E : a * b ∈ E := E.mul_mem ha hb
  have hab2_E : a * b ^ 2 ∈ E := E.mul_mem ha hbE2
  have hsq1 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := hcommab.mul_pow 2
  have hsq2 : (a * b ^ 2) ^ 2 = a ^ 2 * b := by
    rw [(hcommab.pow_right 2).mul_pow]
    congr 1
    have : (b ^ 2) ^ 2 = b ^ 3 * b := by group
    rw [this, hb3, one_mul]
  have hPb : w * (b * w * b⁻¹) * (b ^ 2 * w * (b ^ 2)⁻¹) = 1 := hfix b hb hB w hw
  have hPab : w * (a * b * w * (a * b)⁻¹) * (a ^ 2 * b ^ 2 * w * (a ^ 2 * b ^ 2)⁻¹) = 1 := by
    have := hfix (a * b) hab_E hAB w hw
    rw [hsq1] at this
    exact this
  have hPab2 : w * (a * b ^ 2 * w * (a * b ^ 2)⁻¹) * (a ^ 2 * b * w * (a ^ 2 * b)⁻¹) = 1 := by
    have := hfix (a * b ^ 2) hab2_E hAB2 w hw
    rw [hsq2] at this
    exact this
  have hO1 : (b * w * b⁻¹) * (a * b * w * (a * b)⁻¹) * (a ^ 2 * b * w * (a ^ 2 * b)⁻¹) = 1 := by
    have := hfix a ha hA (b * w * b⁻¹) (hnorm b hb w hw)
    have e1 : a * (b * w * b⁻¹) * a⁻¹ = a * b * w * (a * b)⁻¹ := by group
    have e2 : a ^ 2 * (b * w * b⁻¹) * (a ^ 2)⁻¹ = a ^ 2 * b * w * (a ^ 2 * b)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  have hO2 : (b ^ 2 * w * (b ^ 2)⁻¹) * (a * b ^ 2 * w * (a * b ^ 2)⁻¹)
      * (a ^ 2 * b ^ 2 * w * (a ^ 2 * b ^ 2)⁻¹) = 1 := by
    have := hfix a ha hA (b ^ 2 * w * (b ^ 2)⁻¹) (hnorm (b ^ 2) hbE2 w hw)
    have e1 : a * (b ^ 2 * w * (b ^ 2)⁻¹) * a⁻¹ = a * b ^ 2 * w * (a * b ^ 2)⁻¹ := by group
    have e2 : a ^ 2 * (b ^ 2 * w * (b ^ 2)⁻¹) * (a ^ 2)⁻¹
        = a ^ 2 * b ^ 2 * w * (a ^ 2 * b ^ 2)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  let X0 : U := ⟨w, hw⟩
  let Xb : U := ⟨b * w * b⁻¹, hnorm b hb w hw⟩
  let Xb2 : U := ⟨b ^ 2 * w * (b ^ 2)⁻¹, hnorm (b ^ 2) hbE2 w hw⟩
  let Xab : U := ⟨a * b * w * (a * b)⁻¹, hnorm (a * b) hab_E w hw⟩
  let Xa2b2 : U := ⟨a ^ 2 * b ^ 2 * w * (a ^ 2 * b ^ 2)⁻¹,
    hnorm (a ^ 2 * b ^ 2) (E.mul_mem haE2 hbE2) w hw⟩
  let Xab2 : U := ⟨a * b ^ 2 * w * (a * b ^ 2)⁻¹, hnorm (a * b ^ 2) hab2_E w hw⟩
  let Xa2b : U := ⟨a ^ 2 * b * w * (a ^ 2 * b)⁻¹, hnorm (a ^ 2 * b) (E.mul_mem haE2 hb) w hw⟩
  have eP_b : X0 * Xb * Xb2 = 1 := Subtype.ext hPb
  have eP_ab : X0 * Xab * Xa2b2 = 1 := Subtype.ext hPab
  have eP_ab2 : X0 * Xab2 * Xa2b = 1 := Subtype.ext hPab2
  have eO1 : Xb * Xab * Xa2b = 1 := Subtype.ext hO1
  have eO2 : Xb2 * Xab2 * Xa2b2 = 1 := Subtype.ext hO2
  letI : CommGroup U := commGroupOfComm hcommU
  have h2 : ∀ y : Additive U, y + y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := Additive.ofMul.surjective y
    have hxx : x * x = 1 := Subtype.ext (hsqU (x : G) x.2)
    rw [← ofMul_mul, hxx, ofMul_one]
  have key := pure_id h2 (Additive.ofMul X0) (Additive.ofMul Xb) (Additive.ofMul Xb2)
    (Additive.ofMul Xab) (Additive.ofMul Xa2b2) (Additive.ofMul Xab2) (Additive.ofMul Xa2b)
  have rO1 : Additive.ofMul Xb + Additive.ofMul Xab + Additive.ofMul Xa2b = 0 := by
    rw [← ofMul_mul, ← ofMul_mul, eO1, ofMul_one]
  have rO2 : Additive.ofMul Xb2 + Additive.ofMul Xab2 + Additive.ofMul Xa2b2 = 0 := by
    rw [← ofMul_mul, ← ofMul_mul, eO2, ofMul_one]
  have rPb : Additive.ofMul X0 + Additive.ofMul Xb + Additive.ofMul Xb2 = 0 := by
    rw [← ofMul_mul, ← ofMul_mul, eP_b, ofMul_one]
  have rPab : Additive.ofMul X0 + Additive.ofMul Xab + Additive.ofMul Xa2b2 = 0 := by
    rw [← ofMul_mul, ← ofMul_mul, eP_ab, ofMul_one]
  have rPab2 : Additive.ofMul X0 + Additive.ofMul Xab2 + Additive.ofMul Xa2b = 0 := by
    rw [← ofMul_mul, ← ofMul_mul, eP_ab2, ofMul_one]
  rw [rO1, rO2, rPb, rPab, rPab2, add_zero] at key
  have hX0 : X0 = 1 := ofMul_eq_zero.1 (by rw [key]; simp)
  exact congrArg Subtype.val hX0

end Gen

theorem card_centralizer_ge_nine {G : Type} [Group G] [Finite G] {E U : Subgroup G}
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3) (hU : IsElemAbelian 2 U)
    (hUne : U ≠ ⊥) (hnorm : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U)
    (hirr : ∀ V : Subgroup G, V ≤ U → (∀ e ∈ E, ∀ v ∈ V, e * v * e⁻¹ ∈ V) → V = ⊥ ∨ V = U) :
    3 ^ 2 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (U : Set G)) := by
  by_contra hlt
  rw [not_le] at hlt
  have hcommU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    isElemAbelian_commute hU hx hy
  have hsqU : ∀ x ∈ U, x * x = 1 := fun x hx => by rw [← pow_two]; exact hU.2 x hx
  set C : Subgroup G := E ⊓ Subgroup.centralizer (U : Set G) with hCdef
  have hCE : C ≤ E := inf_le_left
  have hC3 : Nat.card C ≤ 3 := by
    have hdvd : Nat.card C ∣ 3 ^ 3 := by
      rw [← hEcard]
      exact Subgroup.card_dvd_of_le hCE
    obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rw [hkC] at hlt ⊢
    interval_cases k
    · norm_num
    · norm_num
    · norm_num at hlt
    · norm_num at hlt
  obtain ⟨a, haE, b, hbE, haC, hbC, habC, hab2C⟩ := exists_gens hE hEcard hCE hC3
  have hmemC : ∀ g ∈ E, g ∉ C → g ∉ Subgroup.centralizer (U : Set G) :=
    fun g hg hgC hcen => hgC ⟨hg, hcen⟩
  have hfix : ∀ k ∈ E, k ∉ Subgroup.centralizer (U : Set G) → ∀ u ∈ U,
      u * (k * u * k⁻¹) * (k ^ 2 * u * (k ^ 2)⁻¹) = 1 :=
    fun k hk hkc u hu => orbit_eq_one hE hnorm hirr hcommU hk hkc hu
  have hone : ∀ w ∈ U, w = 1 := fun w hw =>
    identity_one hE hcommU hsqU hnorm haE hbE hfix (hmemC a haE haC) (hmemC b hbE hbC)
      (hmemC _ (E.mul_mem haE hbE) habC) (hmemC _ (E.mul_mem haE (E.pow_mem hbE 2)) hab2C) hw
  exact hUne (eq_bot_iff.2 fun w hwU => Subgroup.mem_bot.2 (hone w hwU))

end KDRank3SmallMod

end CFSG.LocalAnalysis.GLTheoremA
