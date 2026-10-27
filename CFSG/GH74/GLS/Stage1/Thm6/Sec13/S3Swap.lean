module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3TypeA
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type} [Group G]

theorem exists_swap_basis [Finite G] {P V : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (e : ↥P ≃* Z2n2 2) (hVO : V = Om P hP 1) {y : G} (hy : y * y = 1)
    (hyP : ∀ q ∈ P, y * q * y⁻¹ ∈ P) (hV4 : Nat.card V = 4)
    (hmoved : ∃ v ∈ V, y * v * y⁻¹ ≠ v) :
    ∃ a b : G, a ∈ P ∧ b ∈ P ∧ a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * b = b * a ∧
      Subgroup.closure ({a, b} : Set G) = P ∧ y * a * y⁻¹ = b ∧ y * b * y⁻¹ = a := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  obtain ⟨v, hvV, hv⟩ := hmoved
  have hvO : v ∈ Om P hP 1 := hVO ▸ hvV
  obtain ⟨a, haO, ha2⟩ := Om_pow_surj hP e (i := 1) (by norm_num) hvO
  have haP : a ∈ P := by
    have h2 : (1 + 1 : ℕ) = 2 := rfl
    rw [h2, Om_top hP e] at haO
    exact haO
  have ha2' : a * a = v := by rw [← ha2]; simp [pow_two]
  have hv2 : v * v = 1 := by
    have := (mem_Om.1 hvO).2
    rwa [pow_one, pow_two] at this
  have hVconj : ∀ u ∈ V, y * u * y⁻¹ ∈ V := by
    intro u hu
    rw [hVO] at hu ⊢
    exact Om_conj hyP hu
  have hv'V : y * v * y⁻¹ ∈ V := hVconj v hvV
  have hv'2 : (y * v * y⁻¹) * (y * v * y⁻¹) = 1 := by
    calc (y * v * y⁻¹) * (y * v * y⁻¹) = y * (v * v) * y⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hv1 : v ≠ 1 := by
    intro h
    apply hv
    rw [h]; group
  have hv'1 : y * v * y⁻¹ ≠ 1 := by
    intro h
    apply hv1
    have : v = y⁻¹ * (y * v * y⁻¹) * y := by group
    rw [this, h]; group
  set b := y * a * y⁻¹ with hb
  have hbP : b ∈ P := hyP a haP
  have hb2 : b * b = y * v * y⁻¹ := by
    calc b * b = y * (a * a) * y⁻¹ := by rw [hb]; group
      _ = y * v * y⁻¹ := by rw [ha2']
  have ha4 : a ^ 4 = 1 := by
    calc a ^ 4 = (a * a) * (a * a) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [ha2', hv2]
  have hb4 : b ^ 4 = 1 := by
    calc b ^ 4 = (b * b) * (b * b) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [hb2, hv'2]
  have hyb : y * b * y⁻¹ = a := by
    rw [hb, hyi]
    calc y * (y * a * y) * y = (y * y) * a * (y * y) := by group
      _ = a := by rw [hy]; group
  have haV : a ∉ V := by
    intro h
    apply hv1
    rw [← ha2']
    have hh : a ∈ Om P hP 1 := hVO ▸ h
    have := (mem_Om.1 hh).2
    rwa [pow_one, pow_two] at this
  have hK : Subgroup.closure ({a, b} : Set G) = P := by
    set K := Subgroup.closure ({a, b} : Set G) with hKdef
    have haK : a ∈ K := Subgroup.subset_closure (by simp)
    have hbK : b ∈ K := Subgroup.subset_closure (by simp)
    have hKP : K ≤ P := by
      rw [hKdef, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact haP
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]; exact hbP
    have hvK : v ∈ K := by rw [← ha2']; exact K.mul_mem haK haK
    have hv'K : y * v * y⁻¹ ∈ K := by rw [← hb2]; exact K.mul_mem hbK hbK
    have hVK : V ≤ K := by
      let U : Subgroup G := Subgroup.closure ({v, y * v * y⁻¹} : Set G)
      have hUV : U ≤ V := by
        rw [Subgroup.closure_le]
        intro g hg
        rcases hg with rfl | hg
        · exact hvV
        · rw [Set.mem_singleton_iff] at hg
          rw [hg]; exact hv'V
      have hvU : v ∈ U := Subgroup.subset_closure (by simp)
      have hv'U : y * v * y⁻¹ ∈ U := Subgroup.subset_closure (by simp)
      have h3 := three_le_card U.one_mem hvU hv'U (Ne.symm hv1) (Ne.symm hv'1) (Ne.symm hv)
      have hdvd : Nat.card U ∣ 4 := by
        have := Subgroup.card_dvd_of_le hUV
        rwa [hV4] at this
      have hUcard : Nat.card U = 4 := by
        have hle : Nat.card U ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        have hne3 : Nat.card U ≠ 3 := by
          intro h
          rw [h] at hdvd
          norm_num at hdvd
        omega
      have hUeq : U = V := Subgroup.eq_of_le_of_card_ge hUV (by rw [hUcard, hV4])
      have hUK : U ≤ K := by
        rw [Subgroup.closure_le]
        intro g hg
        rcases hg with rfl | hg
        · exact hvK
        · rw [Set.mem_singleton_iff] at hg
          rw [hg]; exact hv'K
      rw [← hUeq]
      exact hUK
    have hVa : V ⊔ zpowers a ≤ K := sup_le hVK ((zpowers_le).2 haK)
    have hs : ∀ u ∈ V, a * u * a⁻¹ ∈ V := by
      intro u hu
      have h1 : a * u = u * a := by
        have hu' : u ∈ P := (mem_Om.1 (hVO ▸ hu : u ∈ Om P hP 1)).1
        exact hP a haP u hu'
      have : a * u * a⁻¹ = u := by
        calc a * u * a⁻¹ = (u * a) * a⁻¹ := by rw [h1]
          _ = u := by group
      rw [this]; exact hu
    have hsq : a * a ∈ V := by rw [ha2']; exact hvV
    have h8 : Nat.card ↥(V ⊔ zpowers a) = 8 := by
      have := card_sup_zpowers_sq hsq hs haV
      rw [hV4] at this
      exact this
    have hbna : b ∉ V ⊔ zpowers a := by
      intro hb'
      obtain ⟨u, hu, h1 | h1⟩ := (mem_sup_zpowers_sq hsq hs).1 hb'
      · have hu2 : u * u = 1 := by
          have hu' : u ∈ Om P hP 1 := hVO ▸ hu
          have := (mem_Om.1 hu').2
          rwa [pow_one, pow_two] at this
        have hbb : b * b = 1 := by rw [h1]; exact hu2
        exact hv'1 (by rw [← hb2]; exact hbb)
      · have hu' : u ∈ Om P hP 1 := hVO ▸ hu
        have hu2 : u * u = 1 := by
          have := (mem_Om.1 hu').2
          rwa [pow_one, pow_two] at this
        have hcomm : a * u = u * a := hP a haP u (mem_Om.1 hu').1
        have hbb : b * b = v := by
          rw [h1]
          calc u * a * (u * a) = u * (a * u) * a := by group
            _ = u * (u * a) * a := by rw [hcomm]
            _ = (u * u) * (a * a) := by group
            _ = v := by rw [hu2, ha2', one_mul]
        exact hv (by rw [← hb2]; exact hbb)
    have hlt : V ⊔ zpowers a < K := lt_of_le_of_ne hVa (fun h => hbna (by rw [h]; exact hbK))
    have hc1 := Subgroup.card_lt_of_lt hlt
    have hd1 := Subgroup.card_dvd_of_le hVa
    obtain ⟨m, hm⟩ := hd1
    rw [h8] at hc1 hm
    have hm2 : 2 ≤ m := by
      by_contra hlm
      have : m ≤ 1 := by omega
      have := Nat.mul_le_mul_left 8 this
      omega
    have hPc : Nat.card P = 16 := by
      have := card_Om hP e (i := 2) le_rfl
      rw [Om_top hP e] at this
      simpa using this
    have hKc : 16 ≤ Nat.card K := by
      have := Nat.mul_le_mul_left 8 hm2
      omega
    exact Subgroup.eq_of_le_of_card_ge hKP (by rw [hPc]; exact hKc)
  exact ⟨a, b, haP, hbP, ha4, hb4, by
    have := hP a haP b hbP
    exact this, hK, rfl, hyb⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
