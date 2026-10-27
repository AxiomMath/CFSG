module

public import CFSG.GH74.M12.T1Q8

public section

namespace CFSG.GH74.M12.Thm1

open Subgroup CFSG.Quasithin
open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem card_le_sixtyfour [Finite G] (hyp : Asc03Hyp G z) {S : Subgroup G} (hSH : S ≤ ascH z)
    (hS : IsPGroup 2 ↥S) : Nat.card ↥S ≤ 64 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
  have hdvd : 2 ^ k ∣ 192 := by
    rw [← hk, ← card_ascH' hyp]; exact Subgroup.card_dvd_of_le hSH
  have hk6 : k ≤ 6 := by
    by_contra h
    push Not at h
    have : 2 ^ 7 ∣ 192 := (pow_dvd_pow 2 h).trans hdvd
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
    _ = 64 := by norm_num

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] [Finite G] {P T : Subgroup G}
    (hP : IsPGroup p ↥P) (hTP : T ≤ P) (hne : T ≠ P) :
    ∃ x ∈ P, x ∉ T ∧ x ∈ normalizer (T : Set G) := by
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : T.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    apply le_antisymm hTP
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ T.subgroupOf P := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hnc := Group.normalizerCondition_of_isNilpotent (T.subgroupOf P) hlt
  obtain ⟨x, hxN, hxT⟩ := Set.exists_of_ssubset hnc
  refine ⟨x, x.2, fun h => hxT (Subgroup.mem_subgroupOf.2 h), ?_⟩
  refine mem_normalizer_of_conj fun t ht => ?_
  have h1 := (Subgroup.mem_normalizer_iff.1 hxN ⟨t, hTP ht⟩).1 (Subgroup.mem_subgroupOf.2 ht)
  exact Subgroup.mem_subgroupOf.1 h1

theorem sup_zpowers_facts [Finite G] (hyp : Asc03Hyp G z) {v : G} (hvH : v ∈ ascH z)
    (hvQ : v ∉ ascQ z) (hvo : orderOf v = 2) :
    IsPGroup 2 ↥(ascQ z ⊔ zpowers v) ∧ ascQ z ⊔ zpowers v ≤ ascH z ∧
      Nat.card ↥(ascQ z ⊔ zpowers v) = 64 := by
  have hzp : IsPGroup 2 ↥(zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hvo, pow_one])
  have hvN : zpowers v ≤ normalizer ((ascQ z : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_conj fun q hq => conj_mem_ascQ hvH hq
  have hT₀p : IsPGroup 2 ↥(ascQ z ⊔ zpowers v) := (isPGroup_ascQ hyp).to_sup_of_normal_left' hzp hvN
  have hT₀H : ascQ z ⊔ zpowers v ≤ ascH z := sup_le (ascQ_le_ascH z) ((Subgroup.zpowers_le).2 hvH)
  have hinf : Nat.card ↥(ascQ z ⊓ zpowers v) = 1 := by
    have hle : ascQ z ⊓ zpowers v ≤ zpowers v := inf_le_right
    have hdvd : Nat.card ↥(ascQ z ⊓ zpowers v) ∣ 2 := by
      rw [← hvo, ← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hle
    have hne : Nat.card ↥(ascQ z ⊓ zpowers v) ≠ 2 := by
      intro h
      have heq : ascQ z ⊓ zpowers v = zpowers v :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h, Nat.card_zpowers, hvo])
      exact hvQ (by
        have : v ∈ ascQ z ⊓ zpowers v := by rw [heq]; exact Subgroup.mem_zpowers v
        exact this.1)
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥(ascQ z ⊓ zpowers v) <;> simp_all
  have h1 := card_mul_card_le_sup (ascQ z) (zpowers v)
  rw [card_ascQ hyp, Nat.card_zpowers, hvo, hinf] at h1
  have h2 := card_le_sixtyfour hyp hT₀H hT₀p
  exact ⟨hT₀p, hT₀H, by omega⟩

theorem exists_sylow_le [Finite G] (hyp : Asc03Hyp G z) :
    ∃ P : Sylow 2 G, ascQ z ≤ (P : Subgroup G) ∧ (P : Subgroup G) ≤ ascH z ∧
      Nat.card ↥(P : Subgroup G) = 64 ∧ normalizer ((P : Subgroup G) : Set G) ≤ ascH z := by
  have hE := extraspecialAt_ascQ hyp
  obtain ⟨g, -, -, -, -, -, -, v₀, hv₀, hv₀o, hv₀Q⟩ := exists_config_of_asc03 hyp
  have hv₀H : v₀ ∈ ascH z := hv₀.1
  set T₀ := ascQ z ⊔ zpowers v₀ with hT₀
  have hzp : IsPGroup 2 ↥(zpowers v₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv₀o, pow_one])
  have hvN : zpowers v₀ ≤ normalizer ((ascQ z : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_conj fun q hq => conj_mem_ascQ hv₀H hq
  have hT₀p : IsPGroup 2 ↥T₀ := (isPGroup_ascQ hyp).to_sup_of_normal_left' hzp hvN
  have hT₀H : T₀ ≤ ascH z := sup_le (ascQ_le_ascH z) ((Subgroup.zpowers_le).2 hv₀H)
  have hinf : Nat.card ↥(ascQ z ⊓ zpowers v₀) = 1 := by
    have hle : ascQ z ⊓ zpowers v₀ ≤ zpowers v₀ := inf_le_right
    have hdvd : Nat.card ↥(ascQ z ⊓ zpowers v₀) ∣ 2 := by
      rw [← hv₀o, ← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hle
    have hne : Nat.card ↥(ascQ z ⊓ zpowers v₀) ≠ 2 := by
      intro h
      have heq : ascQ z ⊓ zpowers v₀ = zpowers v₀ :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h, Nat.card_zpowers, hv₀o])
      exact hv₀Q (by
        have : v₀ ∈ ascQ z ⊓ zpowers v₀ := by rw [heq]; exact Subgroup.mem_zpowers v₀
        exact this.1)
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥(ascQ z ⊓ zpowers v₀) <;> simp_all
  have hT₀card : Nat.card ↥T₀ = 64 := by
    have h1 := card_mul_card_le_sup (ascQ z) (zpowers v₀)
    rw [card_ascQ hyp, Nat.card_zpowers, hv₀o, hinf, ← hT₀] at h1
    have h2 := card_le_sixtyfour hyp hT₀H hT₀p
    omega
  have hcenter : ∀ c ∈ T₀, (∀ t ∈ T₀, c * t = t * c) → c = 1 ∨ c = z := by
    intro c hc hct
    exact eq_of_cent_ascQ hyp (hT₀H hc) (fun q hq => hct q (le_sup_left (a := ascQ z) hq))
  have hzT : z ∈ T₀ := le_sup_left (a := ascQ z) hE.mem
  have hnorm : ∀ x ∈ normalizer (T₀ : Set G), x ∈ ascH z := by
    intro x hx
    have hxz : x * z * x⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.1 hx z).1 hzT
    have hcent : ∀ t ∈ T₀, x * z * x⁻¹ * t = t * (x * z * x⁻¹) := by
      intro t ht
      have ht' : x⁻¹ * t * x ∈ T₀ := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) t).1 ht
        simpa using this
      have hzc : z * (x⁻¹ * t * x) = (x⁻¹ * t * x) * z :=
        (Subgroup.mem_centralizer_singleton_iff.1 (hT₀H ht')).symm
      calc x * z * x⁻¹ * t = x * (z * (x⁻¹ * t * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * t * x) * z) * x⁻¹ := by rw [hzc]
        _ = t * (x * z * x⁻¹) := by group
    rcases hcenter _ hxz hcent with h | h
    · exfalso; apply hE.ne_one
      have := congrArg (fun w => x⁻¹ * w * x) h
      simpa [mul_assoc] using this
    · rw [ascH, Subgroup.mem_centralizer_singleton_iff]
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [h]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hT₀p.exists_le_sylow
  have hPeq : T₀ = (P : Subgroup G) := by
    by_contra hne
    obtain ⟨x, hxP, hxT, hxN⟩ := exists_mem_normalizer_not_mem P.isPGroup' hP hne
    have hxH := hnorm x hxN
    have hxp : IsPGroup 2 ↥(zpowers x) :=
      P.isPGroup'.to_le ((Subgroup.zpowers_le).2 hxP)
    have hS : IsPGroup 2 ↥(T₀ ⊔ zpowers x) :=
      hT₀p.to_sup_of_normal_left' hxp ((Subgroup.zpowers_le).2 hxN)
    have hSH : T₀ ⊔ zpowers x ≤ ascH z := sup_le hT₀H ((Subgroup.zpowers_le).2 hxH)
    have hlt : T₀ < T₀ ⊔ zpowers x :=
      lt_of_le_of_ne le_sup_left fun h => hxT (h ▸ le_sup_right (a := T₀) (Subgroup.mem_zpowers x))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := card_le_sixtyfour hyp hSH hS
    omega
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · rw [← hPeq]; exact le_sup_left
  · rw [← hPeq]; exact hT₀H
  · rw [← hPeq]; exact hT₀card
  · rw [← hPeq]; exact hnorm

theorem cent_le_of_E8 [Finite G] (hyp : Asc03Hyp G z) {D : Subgroup G} (hDQ : D ≤ ascQ z)
    (hD8 : Nat.card ↥D = 8) (hDe : ∀ a ∈ D, ∀ b ∈ D, a * a = 1 ∧ a * b = b * a)
    (hzD : z ∈ D) (hDH : ∀ h ∈ ascH z, ∀ d ∈ D, h * d * h⁻¹ ∈ D) :
    ∀ c : G, (∀ d ∈ D, c * d = d * c) → c ∈ D := by
  have hE := extraspecialAt_ascQ hyp
  intro c hc
  have hcH : c ∈ ascH z := Subgroup.mem_centralizer_singleton_iff.2 (hc z hzD)
  set C : Subgroup G := ascH z ⊓ Subgroup.centralizer (D : Set G) with hCdef
  have hmemC : ∀ x : G, x ∈ C ↔ x ∈ ascH z ∧ ∀ d ∈ D, d * x = x * d := by
    intro x
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hcC : c ∈ C := (hmemC c).2 ⟨hcH, fun d hd => (hc d hd).symm⟩
  have hCH : C ≤ ascH z := fun x hx => ((hmemC x).1 hx).1
  have hnC : ∀ h ∈ ascH z, ∀ x ∈ C, h * x * h⁻¹ ∈ C := by
    intro h hh x hx
    rw [hmemC] at hx ⊢
    refine ⟨(ascH z).mul_mem ((ascH z).mul_mem hh hx.1) ((ascH z).inv_mem hh), fun d hd => ?_⟩
    have hd' : h⁻¹ * d * h ∈ D := by simpa using hDH h⁻¹ (inv_mem hh) d hd
    have := hx.2 _ hd'
    calc d * (h * x * h⁻¹) = h * ((h⁻¹ * d * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * d * h)) * h⁻¹ := by rw [this]
      _ = h * x * h⁻¹ * d := by group
  have h3 : ∀ y ∈ C, orderOf y ≠ 3 := by
    intro y hy hy3
    have hall : ∀ d ∈ D, d = 1 ∨ d = z := fun d hd =>
      cent_of_order_three hyp ((hmemC y).1 hy).1 hy3 (hDQ hd) (((hmemC y).1 hy).2 d hd)
    have := card_le_two_of_forall hall
    omega
  have hCQ : C ≤ ascQ z := le_ascQ_of_normal hCH hnC (isPGroup_of_not_three hyp hCH h3)
  have hcQ : c ∈ ascQ z := hCQ hcC
  by_contra hcD
  set B := Subgroup.closure ((D : Set G) ∪ {c}) with hB
  have hS : ∀ u ∈ (D : Set G) ∪ {c}, ∀ v ∈ (D : Set G) ∪ {c}, u * v = v * u := by
    rintro u (hu | hu) v (hv | hv)
    · exact (hDe u hu v hv).2
    · rw [Set.mem_singleton_iff.1 hv]; exact (hc u hu).symm
    · rw [Set.mem_singleton_iff.1 hu]; exact hc v hv
    · rw [Set.mem_singleton_iff.1 hu, Set.mem_singleton_iff.1 hv]
  have hcl := Subgroup.isMulCommutative_closure (k := (D : Set G) ∪ {c})
    (fun u hu v hv _ => hS u hu v hv)
  have hBab : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := by
    intro u hu v hv
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨u, hu⟩ : B) ⟨v, hv⟩)
  have hBQ : B ≤ ascQ z := (Subgroup.closure_le _).2
    (Set.union_subset (fun x hx => hDQ hx) (Set.singleton_subset_iff.2 hcQ))
  have hlt : D < B := lt_of_le_of_ne (fun x hx => Subgroup.subset_closure (Or.inl hx))
    (fun h => hcD (h ▸ Subgroup.subset_closure (Or.inr rfl)))
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := hE.card_abelian_le hBQ hBab
  omega

end CFSG.GH74.M12.Thm1
