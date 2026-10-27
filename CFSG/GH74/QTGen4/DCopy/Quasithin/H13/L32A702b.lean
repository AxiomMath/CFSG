module

public import CFSG.Quasithin.H13.L32A702b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A702
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting147

variable {T L V H : Subgroup G}

theorem lemma14_7_2_F4 (S : Setting147 G T L V H) (hThm : Thm14_5_3_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {I : Subgroup G} (hVI : fsuV1 T V ≤ I)
    (hIU : I < conjClosure V H) (hHI : H ≤ Subgroup.normalizer (I : Set G)) {Y V₂ : Subgroup G}
    (hV2 : A6.IsV2 T V V₂) (hYH : Y ≤ H) (hYo : oTwoUpper Y = Y)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hS3 : quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3))) :
    V ⊓ I = fsuV1 T V ∧
      (I.relIndex (conjClosure V₂ Y ⊔ I) = 2 ∨ I.relIndex (conjClosure V₂ Y ⊔ I) = 4) ∧
      (⁅V₂, Y⁆ ≤ I → ⁅V₂, Y⁆ = ⊥) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hinf := Setting147.inf_V_eq_F4 S h1222 h1332 h1334 hVI hIU hHI
  have hUab := S.hyp.abelian
  have hab : ∀ x ∈ fsuU T V, ∀ y ∈ fsuU T V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(fsuU T V)) ⟨y, hy⟩)
  have hHV1 : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := S.hz.2.1
  have hUHU : conjClosure V H ≤ fsuU T V := conjClosure_mono le_rfl hHV1
  have hIU' : I ≤ fsuU T V := hIU.le.trans hUHU
  have hV₂V : V₂ ≤ V := hV2.2.1
  have hV₁V₂ : fsuV1 T V ≤ V₂ := hV2.1
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := hV2.2.2.1
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hVH : V ≤ H := S14.VT_F4.trans hTH
  have hUHH : conjClosure V H ≤ H := conjClosure_le fun h hh v hv =>
    H.mul_mem (H.mul_mem hh (hVH hv)) (H.inv_mem hh)
  have hEUH : conjClosure V₂ Y ≤ conjClosure V H := conjClosure_mono hV₂V hYH
  have hEU : conjClosure V₂ Y ≤ fsuU T V := hEUH.trans hUHU
  have hEH : conjClosure V₂ Y ≤ H := hEUH.trans hUHH
  have hV₂U : V₂ ≤ fsuU T V := hV₂V.trans ((le_conjClosure V H).trans hUHU)
  have h2V₂ : (fsuV1 T V).relIndex V₂ = 2 := by
    have h := relIndex_card_mul hV₁V₂
    rw [S14.card_V1_F4, hV2.2.2.2] at h
    omega
  have hV₂I : V₂ ⊓ I = fsuV1 T V := by
    refine le_antisymm (fun v hv => ?_) (le_inf hV₁V₂ hVI)
    rw [← hinf]
    exact ⟨hV₂V hv.1, hv.2⟩

  set O : Set (Subgroup G) := {X | ∃ g ∈ Y ⊔ T, X = conjSub g V₂} with hOdef
  have hOcard : Nat.card O = ((Subgroup.normalizer (V₂ : Set G)).subgroupOf (Y ⊔ T)).index :=
    card_conjOrbit (Y ⊔ T) V₂
  have hT3 : T.relIndex (Y ⊔ T) = 3 := U3.relIndex_eq_three_of_quot hS3
    (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow le_sup_right)
  have hOdvd : Nat.card O ∣ 3 := by
    rw [hOcard, ← hT3]
    exact Subgroup.index_dvd_of_le fun t ht =>
      Subgroup.mem_subgroupOf.mpr (hTV₂ (Subgroup.mem_subgroupOf.mp ht))
  have hYTH : Y ⊔ T ≤ H := sup_le hYH hTH
  have hYTmem : ∀ g ∈ Y ⊔ T, ∃ y ∈ Y, ∃ t ∈ T, g = y * t := fun g hg =>
    (F1.mem_sup_iff_exists_mul_of_normalizes hTY).mp hg
  have hline : ∀ X ∈ O, fsuV1 T V ≤ X ∧ X ≤ conjClosure V₂ Y ∧ (fsuV1 T V).relIndex X = 2 ∧
      X ⊓ I = fsuV1 T V := by
    rintro _ ⟨g, hg, rfl⟩
    have hgH := hYTH hg
    have hg1 : conjSub g (fsuV1 T V) = fsuV1 T V := conjSub_eq_iff.mpr (hHV1 hgH)
    have hgI : conjSub g I = I := conjSub_eq_iff.mpr (hHI hgH)
    obtain ⟨y, hy, t, ht, rfl⟩ := hYTmem g hg
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hg1]
      exact Subgroup.map_mono hV₁V₂
    · rw [conjSub_mul, conjSub_eq_iff.mpr (hTV₂ ht)]
      intro x hx
      have h' := mem_conjSub.mp hx
      rw [show x = y * (y⁻¹ * x * y) * y⁻¹ by group]
      exact mem_conjClosure hy h'
    · rw [← hg1, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (y * t)).injective]
      exact h2V₂
    · rw [← hgI, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj (y * t)).injective, hV₂I]
      exact hg1
  have hV₂O : V₂ ∈ O := ⟨1, one_mem _, (conjSub_one V₂).symm⟩
  have hOfin : O.Finite := Set.toFinite O
  have hOle3 : O.ncard ≤ 3 := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.le_of_dvd (by norm_num) hOdvd
  have hEO : ∀ y ∈ Y, conjSub y V₂ ∈ O := fun y hy => ⟨y, Subgroup.mem_sup_left hy, rfl⟩

  obtain ⟨K₁, hK₁, K₂, hK₂, K₃, hK₃, hsub⟩ := exists_subset_three hOfin ⟨V₂, hV₂O⟩ hOle3
  have hEle : conjClosure V₂ Y ≤ K₁ ⊔ K₂ ⊔ K₃ := conjClosure_le fun y hy v hv => by
    have hX := hsub (hEO y hy)
    have hv' : y * v * y⁻¹ ∈ conjSub y V₂ := mem_conjSub.mpr (by simpa [mul_assoc] using hv)
    rcases hX with h | h | h
    · rw [h] at hv'
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hv')
    · rw [h] at hv'
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hv')
    · rw [h] at hv'
      exact Subgroup.mem_sup_right hv'
  have hle8 : (fsuV1 T V).relIndex (conjClosure V₂ Y) ≤ 8 := by
    obtain ⟨h1a, h1b, h1c, -⟩ := hline K₁ hK₁
    obtain ⟨h2a, h2b, h2c, -⟩ := hline K₂ hK₂
    obtain ⟨h3a, h3b, h3c, -⟩ := hline K₃ hK₃
    have h8 := relIndex_sup_three_le hab (h1b.trans hEU) (h2b.trans hEU) (h3b.trans hEU) h1a h2a
      h3a h1c.le h2c.le h3c.le
    have hEeq : conjClosure V₂ Y = K₁ ⊔ K₂ ⊔ K₃ :=
      le_antisymm hEle (sup_le (sup_le h1b h2b) h3b)
    rw [hEeq]
    exact h8
  have hE2 : IsPGroup 2 ↥(conjClosure V₂ Y) := fun x =>
    ⟨1, by
      rw [pow_one, sq]
      exact Subtype.ext (Setting147.sq_fsuU S (fun v hv => S14.mul_self_V_F4 hv) x (hEU x.2))⟩
  have hV₁E : fsuV1 T V ≤ conjClosure V₂ Y := hV₁V₂.trans (le_conjClosure V₂ Y)
  have hpow : ∃ k, (fsuV1 T V).relIndex (conjClosure V₂ Y) = 2 ^ k := by
    obtain ⟨n, hn⟩ := hE2.exists_card_eq
    have hd : (fsuV1 T V).relIndex (conjClosure V₂ Y) ∣ 2 ^ n :=
      by rw [← hn]; exact Subgroup.relIndex_dvd_card _ _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨k, hk⟩
  have hge2 : 2 ≤ (fsuV1 T V).relIndex (conjClosure V₂ Y) := by
    have hm := Subgroup.relIndex_mul_relIndex _ _ _ hV₁V₂ (le_conjClosure V₂ Y)
    rw [h2V₂] at hm
    have hpos : V₂.relIndex (conjClosure V₂ Y) ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hne8 := (hThm G T L V S.hyp Y V₂ hV2 hYo (hYH.trans S.hz.2.1) hTY hS3).2.2
  have hE24 : (fsuV1 T V).relIndex (conjClosure V₂ Y) = 2 ∨
      (fsuV1 T V).relIndex (conjClosure V₂ Y) = 4 := by
    obtain ⟨k, hk⟩ := hpow
    rw [hk] at hle8 hge2 hne8 ⊢
    have hk3 : k ≤ 3 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases k
    · norm_num at hge2
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hne8

  have hEN : conjClosure V₂ Y ≤ Subgroup.normalizer (I : Set G) := hEH.trans hHI
  have hEI : I.relIndex (conjClosure V₂ Y ⊔ I) =
      (I ⊓ conjClosure V₂ Y).relIndex (conjClosure V₂ Y) := by
    rw [A4.relIndex_sup_eq_of_le_normalizer' hEN, Subgroup.inf_relIndex_right]
  have hEIne1 : (I ⊓ conjClosure V₂ Y).relIndex (conjClosure V₂ Y) ≠ 1 := by
    intro h
    have hV₂I' : V₂ ≤ I :=
      (le_conjClosure V₂ Y).trans ((Subgroup.relIndex_eq_one.mp h).trans inf_le_left)
    have h' : V₂ ≤ fsuV1 T V := by
      rw [← hV₂I]
      exact le_inf le_rfl hV₂I'
    have h1 : (fsuV1 T V).relIndex V₂ = 1 := Subgroup.relIndex_eq_one.mpr h'
    omega
  have hEIdvd : (I ⊓ conjClosure V₂ Y).relIndex (conjClosure V₂ Y) ∣
      (fsuV1 T V).relIndex (conjClosure V₂ Y) :=
    Subgroup.relIndex_dvd_of_le_left _ (le_inf hVI hV₁E)
  have h2 : I.relIndex (conjClosure V₂ Y ⊔ I) = 2 ∨ I.relIndex (conjClosure V₂ Y ⊔ I) = 4 := by
    rw [hEI]
    rcases hE24 with h | h
    · rw [h] at hEIdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hEIdvd with h' | h'
      · exact absurd h' hEIne1
      · exact Or.inl h'
    · rw [h, show (4 : ℕ) = 2 ^ 2 by norm_num] at hEIdvd
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hEIdvd
      interval_cases i
      · exact absurd (by simpa using hi') hEIne1
      · exact Or.inl (by simpa using hi')
      · exact Or.inr (by simpa using hi')
  refine ⟨hinf, h2, fun hcomm => ?_⟩

  have hEV₂I : conjClosure V₂ Y ≤ V₂ ⊔ I := conjClosure_le fun y hy v hv => by
    have hc : v * y * v⁻¹ * y⁻¹ ∈ I := by
      simpa [commutatorElement_def] using hcomm (Subgroup.commutator_mem_commutator hv hy)
    rw [show y * v * y⁻¹ = (v * y * v⁻¹ * y⁻¹)⁻¹ * v by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (inv_mem hc)) (Subgroup.mem_sup_left hv)
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  have hO13 : Nat.card O = 1 ∨ Nat.card O = 3 := (Nat.dvd_prime Nat.prime_three).mp hOdvd
  rcases hO13 with h1 | h3
  ·
    rw [Nat.card_coe_set_eq] at h1
    obtain ⟨X, hX⟩ := Set.ncard_eq_one.mp h1
    have hYN : Y ≤ Subgroup.normalizer (V₂ : Set G) := fun y hy => by
      have h1' : conjSub y V₂ ∈ O := hEO y hy
      have h2' : V₂ ∈ O := hV₂O
      rw [hX, Set.mem_singleton_iff] at h1' h2'
      exact conjSub_eq_iff.mp (h1'.trans h2'.symm)

    have hsq : ∀ y ∈ Y, y * y ∈ Subgroup.centralizer (V₂ : Set G) := by
      intro y hy
      have hyV₁ := hHV1 (hYH hy)
      have hyV₂ := hYN hy
      have hfix1 : ∀ w ∈ fsuV1 T V, y * w * y⁻¹ = w := fun w hw => by
        have hw' : y * w * y⁻¹ ∈ fsuV1 T V := (Subgroup.mem_normalizer_iff.mp hyV₁ w).mp hw
        rcases S14.eq_of_mem_V1_F4 hz hz1 hw with h | h
        · rw [h]
          group
        · rcases S14.eq_of_mem_V1_F4 hz hz1 hw' with h' | h'
          · exfalso
            apply hz1
            rw [h] at h'
            have := congrArg (fun u => y⁻¹ * u * y) h'
            simpa [mul_assoc] using this
          · rw [h', h]
      have hya : y * a * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hyV₂ a).mp ha
      have hya1 : y * a * y⁻¹ ∉ fsuV1 T V := fun h => haV (by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyV₁) _).mp h
        simpa [mul_assoc] using this)
      have hw : a * (y * a * y⁻¹) ∈ fsuV1 T V := (S14.mem_V2_F4 ha haV hya).resolve_left hya1
      have haa : a * a = 1 := S14.mul_self_V_F4 (hV₂V ha)
      obtain ⟨w, hwV, hyw⟩ : ∃ w ∈ fsuV1 T V, y * a * y⁻¹ = a * w :=
        ⟨a * (y * a * y⁻¹), hw, by rw [← mul_assoc, haa, one_mul]⟩
      have hww : w * w = 1 := S14.mul_self_V_F4 (Subgroup.mem_inf.mp hwV).1
      have hy2a : (y * y) * a * (y * y)⁻¹ = a := by
        calc (y * y) * a * (y * y)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by group
          _ = y * (a * w) * y⁻¹ := by rw [hyw]
          _ = (y * a * y⁻¹) * (y * w * y⁻¹) := by group
          _ = a * w * w := by rw [hfix1 w hwV, hyw]
          _ = a := by rw [mul_assoc, hww, mul_one]
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv1 : ∀ w ∈ fsuV1 T V, w * (y * y) = (y * y) * w := fun w hw' => by
        have h1 := hfix1 w hw'
        have h2 := hfix1 (y * w * y⁻¹) (by rw [h1]; exact hw')
        rw [h1] at h2
        calc w * (y * y) = (y * y) * ((y * y)⁻¹ * w * (y * y)) := by group
          _ = (y * y) * w := by
            congr 1
            rw [show (y * y)⁻¹ * w * (y * y) = y⁻¹ * (y⁻¹ * w * y) * y by group]
            have h3 : y⁻¹ * w * y = w := by
              have := congrArg (fun u => y⁻¹ * u * y) h1
              simpa [mul_assoc] using this.symm
            rw [h3, h3]
      rcases S14.mem_V2_F4 ha haV hv with h | h
      · exact hv1 v h
      · have ha2 : a * (y * y) = (y * y) * a := by
          calc a * (y * y) = (y * y) * ((y * y)⁻¹ * a * (y * y)) := by group
            _ = (y * y) * a := by
              congr 1
              have := congrArg (fun u => (y * y)⁻¹ * u * (y * y)) hy2a
              simpa [mul_assoc] using this.symm
        have hv' : v = a * (a * v) := by rw [← mul_assoc, haa, one_mul]
        rw [hv', mul_assoc, hv1 _ h, ← mul_assoc, ha2, mul_assoc]
    have hYC : Y ≤ Subgroup.centralizer (V₂ : Set G) := by
      rw [← hYo]
      refine (Subgroup.closure_le _).mpr fun y hy => ?_
      have hmem := A4.mem_zpowers_pow_of_coprime (Nat.coprime_two_left.mpr hy.2)
      rw [pow_two] at hmem
      exact (Subgroup.zpowers_le.mpr (hsq y hy.1)) hmem
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYC
  ·
    exfalso
    rw [Nat.card_coe_set_eq] at h3
    obtain ⟨A, B, C, hAB, hAC, hBC, hO⟩ := Set.ncard_eq_three.mp h3
    have hmem : ∀ X, X ∈ O ↔ X = A ∨ X = B ∨ X = C := fun X => by
      rw [hO]
      simp
    obtain ⟨K₂, hK₂, K₃, hK₃, h12, h13, h23⟩ :
        ∃ K₂ ∈ O, ∃ K₃ ∈ O, V₂ ≠ K₂ ∧ V₂ ≠ K₃ ∧ K₂ ≠ K₃ := by
      rcases (hmem V₂).mp hV₂O with h | h | h
      · exact ⟨B, (hmem B).mpr (Or.inr (Or.inl rfl)), C, (hmem C).mpr (Or.inr (Or.inr rfl)),
          h ▸ hAB, h ▸ hAC, hBC⟩
      · exact ⟨A, (hmem A).mpr (Or.inl rfl), C, (hmem C).mpr (Or.inr (Or.inr rfl)),
          h ▸ hAB.symm, h ▸ hBC, hAC⟩
      · exact ⟨A, (hmem A).mpr (Or.inl rfl), B, (hmem B).mpr (Or.inr (Or.inl rfl)),
          h ▸ hAC.symm, h ▸ hBC.symm, hAB⟩
    obtain ⟨hK₂1, hK₂E, hK₂2, hK₂I⟩ := hline K₂ hK₂
    obtain ⟨hK₃1, hK₃E, hK₃2, hK₃I⟩ := hline K₃ hK₃
    have hexists : ∀ {X : Subgroup G}, (fsuV1 T V).relIndex X = 2 → ∃ e ∈ X, e ∉ fsuV1 T V := by
      intro X hX2
      by_contra h
      push Not at h
      rw [Subgroup.relIndex_eq_one.mpr h] at hX2
      norm_num at hX2
    obtain ⟨e₂, he₂, he₂V⟩ := hexists hK₂2
    obtain ⟨e₃, he₃, he₃V⟩ := hexists hK₃2
    have hIN : I ≤ Subgroup.normalizer (V₂ : Set G) := le_normalizer_of_comm' hab hV₂U hIU'

    have haI : ∀ e ∈ conjClosure V₂ Y, e ∉ I → a * e ∈ I := fun e he heI => by
      obtain ⟨v, hv, i, hi, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hIN).mp (hEV₂I he)
      rcases S14.mem_V2_F4 ha haV hv with h | h
      · exact absurd (mul_mem (hVI h) hi) heI
      · rw [← mul_assoc]
        exact mul_mem (hVI h) hi
    have he₂I : e₂ ∉ I := fun h => he₂V (hK₂I ▸ ⟨he₂, h⟩)
    have hae₂ : a * e₂ ∈ I := haI e₂ (hK₂E he₂) he₂I

    have hK₂V₂ : ¬ K₂ ≤ V₂ := fun h =>
      h12 (eq_of_relIndex_two hV₁V₂ hK₂1 h2V₂ hK₂2 (h he₂) he₂ he₂V)
    have hV₂K₂ : (fsuV1 T V).relIndex (V₂ ⊔ K₂) = 4 := by
      have hm := Subgroup.relIndex_mul_relIndex _ _ _ hV₁V₂ (le_sup_left : V₂ ≤ V₂ ⊔ K₂)
      rw [h2V₂] at hm
      have hne : V₂.relIndex (V₂ ⊔ K₂) ≠ 1 := fun h =>
        hK₂V₂ (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h))
      have hle := Subgroup.relIndex_le_of_le_right (sup_le (le_conjClosure V₂ Y) hK₂E)
        (Subgroup.index_ne_zero_of_finite : (fsuV1 T V).relIndex (conjClosure V₂ Y) ≠ 0)
      have hpos : V₂.relIndex (V₂ ⊔ K₂) ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases hE24 with h | h <;> omega
    have hEeq : V₂ ⊔ K₂ = conjClosure V₂ Y := by
      have hle : V₂ ⊔ K₂ ≤ conjClosure V₂ Y := sup_le (le_conjClosure V₂ Y) hK₂E
      have hm := Subgroup.relIndex_mul_relIndex _ _ _ (hV₁V₂.trans le_sup_left) hle
      rw [hV₂K₂] at hm
      have hpos : (V₂ ⊔ K₂).relIndex (conjClosure V₂ Y) ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1 : (V₂ ⊔ K₂).relIndex (conjClosure V₂ Y) = 1 := by rcases hE24 with h | h <;> omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
    have hK₂N : K₂ ≤ Subgroup.normalizer (V₂ : Set G) :=
      le_normalizer_of_comm' hab hV₂U (hK₂E.trans hEU)
    obtain ⟨v, hv, k, hk, he₃eq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hK₂N).mp (hEeq ▸ hK₃E he₃)
    rcases S14.mem_V2_F4 ha haV hv with hv1 | hv1 <;>
      rcases mem_or_mul_mem_of_relIndex_two hK₂2 he₂ he₂V hk with hk1 | hk1
    · exact he₃V (he₃eq ▸ mul_mem hv1 hk1)
    · exact h23 (eq_of_relIndex_two hK₂1 hK₃1 hK₂2 hK₃2 (he₃eq ▸ mul_mem (hK₂1 hv1) hk) he₃ he₃V)
    · exact h13 (eq_of_relIndex_two hV₁V₂ hK₃1 h2V₂ hK₃2 (he₃eq ▸ mul_mem hv (hV₁V₂ hk1)) he₃
        he₃V)
    · apply he₃V
      rw [← hK₃I]
      refine ⟨he₃, ?_⟩
      have haU : a ∈ fsuU T V := hV₂U ha
      have he₂U : e₂ ∈ fsuU T V := hK₂E.trans hEU he₂
      have hvU : v ∈ fsuU T V := hV₂U hv
      have hkU : k ∈ fsuU T V := hK₂E.trans hEU hk
      have hw₁U : a * v ∈ fsuU T V := mul_mem haU hvU
      have hc1 : a * v * e₂⁻¹ = e₂⁻¹ * (a * v) := hab _ hw₁U _ (inv_mem he₂U)
      have hc2 : a * e₂ = e₂ * a := hab _ haU _ he₂U
      have e : e₃ = (e₂ * a)⁻¹ * ((a * v) * (e₂ * k)) := by
        rw [he₃eq]
        calc v * k = a⁻¹ * (a * v) * (e₂⁻¹ * (e₂ * k)) := by group
          _ = a⁻¹ * (e₂⁻¹ * (a * v)) * (e₂ * k) := by rw [← hc1]; group
          _ = (e₂ * a)⁻¹ * ((a * v) * (e₂ * k)) := by group
      rw [e]
      have hae₂' : e₂ * a ∈ I := by rw [← hc2]; exact hae₂
      exact I.mul_mem (I.inv_mem hae₂') (I.mul_mem (hVI hv1) (hVI hk1))

end Setting147

theorem lemma14_7_2_of_F4 (hThm : Thm14_5_3_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : Lemma14_7_2_F4 := by
  intro G _ _ T L V H S I hVI hIU hHI Y V₂ hV2 hYH hYo hTY hS3
  exact Setting147.lemma14_7_2_F4 S hThm h1222 h1332 h1334 hVI hIU hHI hV2 hYH hYo hTY hS3

end CFSG.Quasithin.H13.L32A
