module

public import CFSG.CGT.Timmesfeld75.Sec76Transv
public import CFSG.CGT.Timmesfeld75.Sec76Stmt
public import CFSG.CGT.Timmesfeld75.Sec74
public import CFSG.CGT.Timmesfeld75.Sec7Three

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem ay_facts {a y b c : G} (ha2 : a * a = 1) (hy2 : y * y = 1) (h4 : orderOf (a * y) = 4)
    (hb : b = y * a * y) (hc : c = a * b) :
    c = (a * y) ^ 2 ∧ c ≠ 1 ∧ c * c = 1 ∧ y * (a * y * a) = c ∧ c * a = b ∧ a * c = b ∧
      y * c = c * y := by
  have F1 : c = (a * y) ^ 2 := by
    rw [hc, hb, pow_two]
    group
  have F2 : c ≠ 1 := by
    intro h
    rw [F1] at h
    have h1 : orderOf (a * y) ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [h4] at h1
    omega
  have F3 : c * c = 1 := by
    rw [F1, ← pow_add]
    have : (a * y) ^ 4 = 1 := by
      rw [← h4]
      exact pow_orderOf_eq_one _
    exact this
  have F6 : y * (a * y * a) = c := by
    have h1 : c * (y * (a * y * a)) = 1 := by
      calc c * (y * (a * y * a)) = (a * y * a) * (y * y) * (a * y * a) := by rw [hc, hb]; group
        _ = (a * y * a) * (a * y * a) := by rw [hy2, mul_one]
        _ = a * y * (a * a) * y * a := by group
        _ = a * (y * y) * a := by rw [ha2, mul_one]; group
        _ = 1 := by rw [hy2, mul_one, ha2]
    exact mul_left_cancel (h1.trans F3.symm)
  have F7 : c * a = b := by
    calc c * a = (y * (a * y * a)) * a := by rw [F6]
      _ = y * a * y * (a * a) := by group
      _ = b := by rw [ha2, mul_one, hb]
  have F8 : a * c = b := by
    rw [hc, ← mul_assoc, ha2, one_mul]
  refine ⟨F1, F2, F3, F6, F7, F8, ?_⟩
  calc y * c = y * a * y * a * y := by rw [hc, hb]; group
    _ = c * y := by rw [← F6]; group

theorem Sec3Global.sec3_of_conj {T : Subgroup G} (hG : Sec3Global T) {h g : G}
    (hne : conjSubgroup h T ≠ conjSubgroup g T)
    (hN : normIn (conjSubgroup h T) (conjSubgroup g T) ≠ ⊥) :
    Sec3 (conjSubgroup h T) (conjSubgroup g T) := by
  have hgh : conjSubgroup (g * h⁻¹) (conjSubgroup h T) = conjSubgroup g T := by
    rw [conjSubgroup_conjSubgroup, show g * h⁻¹ * h = g by group]
  have hne' : conjSubgroup (g * h⁻¹) (conjSubgroup h T) ≠ conjSubgroup h T := by
    rw [hgh]
    exact fun h' => hne h'.symm
  have hL : normIn (conjSubgroup h T) (conjSubgroup (g * h⁻¹) (conjSubgroup h T)) ≠ ⊥ := by
    rw [hgh]
    exact hN
  have hS := (hG.conj h) (g * h⁻¹) hne' hL
  rw [hgh] at hS
  exact hS

theorem Sec6Ctx.false_of_normalizes_conj (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {x y h : G} (hx : x ∈ classD T)
    (hy : y ∈ classD T) (hxN : x ∈ Subgroup.normalizer ((conjSubgroup h T : Subgroup G) : Set G))
    (hyN : y ∈ Subgroup.normalizer ((conjSubgroup h T : Subgroup G) : Set G)) {k : ℕ}
    (hk : Odd k) (hk3 : 3 ≤ k) (ho : orderOf (x * y) = 2 * k) : False := by
  have hx' : h⁻¹ * x * h ∈ normD T := ⟨classD_conj hx h, mem_normalizer_conjSubgroup_iff.1 hxN⟩
  have hy' : h⁻¹ * y * h ∈ normD T := ⟨classD_conj hy h, mem_normalizer_conjSubgroup_iff.1 hyN⟩
  have ho' : orderOf ((h⁻¹ * x * h) * (h⁻¹ * y * h)) = 2 * k := by
    have e : (h⁻¹ * x * h) * (h⁻¹ * y * h) = h⁻¹ * (x * y) * h := by group
    rw [e, orderOf_inv_mul_mul_eq]
    exact ho
  exact hc.false_of_normD_pair h1 h62 h63 hA8 hnat hx' hy' hk hk3 ho'

theorem Sec6Ctx.sec76_mem (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n)
    (hA8 : ¬ (n = 4 ∧ m = 1)) {x y a : G} (hx : x ∈ classD T) (hy : y ∈ classD T) {k : ℕ}
    (hk : Odd k) (hk3 : 3 ≤ k) (ho : orderOf (x * y) = 2 * k) (ha : a ∈ T) (ha1 : a ≠ 1)
    (hxa : a * x = x * a) : orderOf (a * y) ≠ 2 ∧ orderOf (a * y) ≠ 4 := by
  have := hc.finite
  have hP := hc.hy.pair
  have hTab := hP.wc.1
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_classD hTab hx
  have hy2 : y * y = 1 := mul_self_eq_one_of_mem_classD hTab hy
  have ha2 : a * a = 1 := elemAbelian_mul_self hTab ha
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have haD : a ∈ classD T := mem_classD_of_mem ha ha1
  have hx1 : x ≠ 1 := ne_one_of_mem_classD hx
  have hy1 : y ≠ 1 := ne_one_of_mem_classD hy
  have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
    hP.wc.centralizer_le_normalizer ha ha1 (Subgroup.mem_centralizer_singleton_iff.2 hxa.symm)
  have hxD : x ∈ normD T := ⟨hx, hxN⟩
  refine ⟨fun h2 => ?_, fun h4 => ?_⟩
  · have hcomm : a * y = y * a :=
      (orderOf_mul_dvd_two_iff_commute ha2 hy2).1 (dvd_of_eq h2)
    have hyN : y ∈ Subgroup.normalizer (T : Set G) :=
      hP.wc.centralizer_le_normalizer ha ha1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
    exact hc.false_of_normD_pair h1 h62 h63 hA8 hnat hxD ⟨hy, hyN⟩ hk hk3 ho
  · obtain ⟨b, hb⟩ : ∃ b : G, b = y * a * y := ⟨_, rfl⟩
    obtain ⟨c, hcdef⟩ : ∃ c : G, c = a * b := ⟨_, rfl⟩
    obtain ⟨F1, F2, F3, F6, F7, F8, F5⟩ := ay_facts ha2 hy2 h4 hb hcdef
    have hbD : b ∈ classD T := by
      have := classD_conj_mul haD y
      rwa [hyi, ← hb] at this
    have hcD : c ∈ classD T := by
      have := h66 G T T₁ n m hc a haD y hy h4
      rwa [← F1] at this
    have hcN : c ∈ Subgroup.normalizer (T : Set G) :=
      hP.wc.centralizer_le_normalizer ha ha1
        (Subgroup.mem_centralizer_singleton_iff.2 (F7.trans F8.symm))
    by_cases hbT : b ∈ T
    · have hcT : c ∈ T := by
        rw [hcdef]
        exact T.mul_mem ha hbT
      have hyN : y ∈ Subgroup.normalizer (T : Set G) :=
        hP.wc.centralizer_le_normalizer hcT F2 (Subgroup.mem_centralizer_singleton_iff.2 F5)
      exact hc.false_of_normD_pair h1 h62 h63 hA8 hnat hxD ⟨hy, hyN⟩ hk hk3 ho
    · have hcT : c ∉ T := by
        intro hcT
        apply hbT
        rw [← F8]
        exact T.mul_mem ha hcT
      have hc' : c ∈ normD T := ⟨hcD, hcN⟩
      have h74 := sec74_of h66 h1 h62 h63 G T T₁ n m hc hnat hn3 hA8 a haD y hy h4
      rcases h74 with ⟨h, hah, hyah⟩ | ⟨g, hyg, hayg⟩
      · exfalso
        have hne : T ⊓ conjSubgroup h T ≠ ⊥ := by
          intro hbot
          have : a ∈ T ⊓ conjSubgroup h T := ⟨ha, hah⟩
          rw [hbot, Subgroup.mem_bot] at this
          exact ha1 this
        have := hP.wc.conj_eq_of_inf_ne_bot hne
        rw [this, hyi, ← hb] at hyah
        exact hbT hyah
      · have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [hai] at hayg
        have hcg : c ∈ conjSubgroup g T := by
          rw [← F6]
          exact (conjSubgroup g T).mul_mem hyg hayg
        have hset := hc.sec65 h62 h63 hc' hcT
        have hmem : b ∈ {y' | y' ∈ classD T ∧ ∃ t ∈ T, y' = c * t} := ⟨hbD, a, ha, F7.symm⟩
        rw [hset.1, hset.2] at hmem
        obtain ⟨c', hc'mem, hbc'⟩ := hmem
        have hac : a ∈ commSub c T := by
          have : a = c' := mul_left_cancel (F7.trans hbc')
          rw [this]
          exact hc'mem
        have hx4 := hc.pow_four_mem_of_fixed h1 h63 hA8 hnat hxD hc' hcT ha ha1 hac hxa.symm
        have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right F3
        have h8 : (x * c) ^ 8 = 1 := by
          rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add]
          exact elemAbelian_mul_self hTab hx4
        have hdvd8 : orderOf (x * c) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one (by simpa using h8)
        obtain ⟨hcases, -⟩ := hc.sec73 h1 h62 h63 h66 hA8 hnat hx hcD
        have hord : orderOf (x * c) ∣ 2 ∨ orderOf (x * c) = 4 := by
          obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd8
          interval_cases i
          · left
            rw [hoi]
            norm_num
          · left
            rw [hoi]
            norm_num
          · right
            rw [hoi]
            norm_num
          · exfalso
            rcases hcases with h | h | ⟨k', hk', hk'o⟩
            · rw [hoi] at h
              norm_num at h
            · rw [hoi] at h
              obtain ⟨d, hd⟩ := h
              omega
            · rw [hoi] at hk'o
              obtain ⟨d, rfl⟩ := hk'
              omega
        have hnorm_false : x ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) →
            False := fun hxg =>
          hc.false_of_normalizes_conj h1 h62 h63 hA8 hnat hx hy hxg
            (Subgroup.le_normalizer hyg) hk hk3 ho
        rcases hord with hord2 | hord4
        · have hxc : x * c = c * x := (orderOf_mul_dvd_two_iff_commute hx2 F3).1 hord2
          exact hnorm_false ((hP.wc.conj g).centralizer_le_normalizer hcg F2
            (Subgroup.mem_centralizer_singleton_iff.2 hxc))
        · have h74' := sec74_of h66 h1 h62 h63 G T T₁ n m hc hnat hn3 hA8 x hx c hcD hord4
          have hsqc : (x * c) ^ (2 * 2) = 1 := by
            rw [show 2 * 2 = orderOf (x * c) by rw [hord4]]
            exact pow_orderOf_eq_one _
          obtain ⟨hxsq, hcsq⟩ := dihedral_center_comm hx2 F3 hsqc
          have hsq1 : (x * c) ^ 2 ≠ 1 := fun h => by
            have := orderOf_dvd_of_pow_eq_one h
            rw [hord4] at this
            omega
          have hyx : orderOf (y * x) = 2 * k := by
            rw [← dihedral_inv hx2 hy2, orderOf_inv]
            exact ho
          rcases h74' with ⟨h', hxh', hcxh'⟩ | ⟨g', hcg', hxcg'⟩
          · have hsqh' : (x * c) ^ 2 ∈ conjSubgroup h' T := by
              have e : (x * c) ^ 2 = x * (c⁻¹ * x * c) := by
                rw [hci, pow_two]
                group
              rw [e]
              exact (conjSubgroup h' T).mul_mem hxh' hcxh'
            have hcN' : c ∈ Subgroup.normalizer ((conjSubgroup h' T : Subgroup G) : Set G) :=
              (hP.wc.conj h').centralizer_le_normalizer hsqh' hsq1
                (Subgroup.mem_centralizer_singleton_iff.2 hcsq)
            by_cases hTg : conjSubgroup h' T = conjSubgroup g T
            · rw [hTg] at hxh'
              exact hnorm_false (Subgroup.le_normalizer hxh')
            · have hne : conjSubgroup g T ≠ conjSubgroup h' T := fun h => hTg h.symm
              have hN : normIn (conjSubgroup g T) (conjSubgroup h' T) ≠ ⊥ := by
                intro hbot
                have : c ∈ normIn (conjSubgroup g T) (conjSubgroup h' T) :=
                  mem_normIn.2 ⟨hcg, hcN'⟩
                rw [hbot, Subgroup.mem_bot] at this
                exact F2 this
              have hS := hc.hS.sec3_of_conj hne hN
              obtain ⟨x₀, hx₀X, hx₀⟩ := hS.conj
              have hyD' : y ∈ classDIn (conjSubgroup g T ⊔ conjSubgroup h' T)
                  (conjSubgroup g T) :=
                ⟨hy1, 1, (conjSubgroup g T ⊔ conjSubgroup h' T).one_mem, by
                  rw [conjSubgroup_one]
                  exact hyg⟩
              have hxD' : x ∈ classDIn (conjSubgroup g T ⊔ conjSubgroup h' T)
                  (conjSubgroup g T) :=
                ⟨hx1, x₀, hx₀X, by
                  rw [← hx₀]
                  exact hxh'⟩
              obtain ⟨hcs, -⟩ := hS.orderOf_mul_cases hyD' hxD'
              rw [hyx] at hcs
              obtain ⟨d, rfl⟩ := hk
              rcases hcs with h | h | ⟨e, he⟩ <;> omega
          · have hbot : conjSubgroup g T ⊓ conjSubgroup (g' * g⁻¹) (conjSubgroup g T) ≠ ⊥ := by
              intro hbot
              have e : conjSubgroup (g' * g⁻¹) (conjSubgroup g T) = conjSubgroup g' T := by
                rw [conjSubgroup_conjSubgroup, show g' * g⁻¹ * g = g' by group]
              have : c ∈ conjSubgroup g T ⊓ conjSubgroup (g' * g⁻¹) (conjSubgroup g T) :=
                ⟨hcg, by rw [e]; exact hcg'⟩
              rw [hbot, Subgroup.mem_bot] at this
              exact F2 this
            have e : conjSubgroup (g' * g⁻¹) (conjSubgroup g T) = conjSubgroup g' T := by
              rw [conjSubgroup_conjSubgroup, show g' * g⁻¹ * g = g' by group]
            have hTg := (hP.wc.conj g).conj_eq_of_inf_ne_bot hbot
            rw [e] at hTg
            rw [hTg, hxi] at hxcg'
            have hsqg : (x * c) ^ 2 ∈ conjSubgroup g T := by
              have e2 : (x * c) ^ 2 = (x * c * x) * c := by
                rw [pow_two]
                group
              rw [e2]
              exact (conjSubgroup g T).mul_mem hxcg' hcg
            exact hnorm_false ((hP.wc.conj g).centralizer_le_normalizer hsqg hsq1
              (Subgroup.mem_centralizer_singleton_iff.2 hxsq))

theorem sec76_of (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) : Sec76 := by
  intro G _ T T₁ n m hc hnat hn3 hA8 x hx y hy k hk hk3 ho a ha hxa
  obtain ⟨c, s, hsT, hs1, rfl⟩ := ha
  have hx' : c * x * c⁻¹ ∈ classD T := classD_conj_mul hx c
  have hy' : c * y * c⁻¹ ∈ classD T := classD_conj_mul hy c
  have ho' : orderOf ((c * x * c⁻¹) * (c * y * c⁻¹)) = 2 * k := by
    have e : (c * x * c⁻¹) * (c * y * c⁻¹) = c * (x * y) * c⁻¹ := by group
    rw [e, ← ho]
    exact MulEquiv.orderOf_eq (MulAut.conj c) _
  have hxa' : s * (c * x * c⁻¹) = (c * x * c⁻¹) * s := by
    calc s * (c * x * c⁻¹) = c * (c⁻¹ * s * c * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * s * c)) * c⁻¹ := by rw [hxa]
      _ = (c * x * c⁻¹) * s := by group
  have hres := hc.sec76_mem h66 h1 h62 h63 hnat hn3 hA8 hx' hy' hk hk3 ho' hsT hs1 hxa'
  have e2 : orderOf (c⁻¹ * s * c * y) = orderOf (s * (c * y * c⁻¹)) := by
    have : s * (c * y * c⁻¹) = c * (c⁻¹ * s * c * y) * c⁻¹ := by group
    rw [this]
    exact (MulEquiv.orderOf_eq (MulAut.conj c) _).symm
  rw [e2]
  exact hres

end CFSG.CGT.Timmesfeld75
