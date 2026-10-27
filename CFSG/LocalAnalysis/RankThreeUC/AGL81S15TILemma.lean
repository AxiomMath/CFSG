module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tiPair_comm {p : ℕ} {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨a, ha⟩ ⟨b, hb⟩)

omit [Finite G] in
theorem tiPair_mul_self {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) {a : G}
    (ha : a ∈ A) : a * a = 1 := by
  simpa [pow_two] using hA.2 a ha

omit [Finite G] in
theorem tiPair_mem_normalizer_of_commute {H A : Subgroup G}
    (hTI : ∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom = A ∨
      A ⊓ A.map (MulAut.conj h).toMonoidHom = ⊥)
    {h x : G} (hh : h ∈ H) (hxA : x ∈ A) (hx1 : x ≠ 1) (hc : h * x = x * h) :
    h ∈ normalizer (A : Set G) := by
  rcases hTI h hh with he | hbot
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · exfalso
    have hxmap : x ∈ A.map (MulAut.conj h).toMonoidHom :=
      ⟨x, hxA, by simp [MulAut.conj_apply, hc]⟩
    have hmem : x ∈ A ⊓ A.map (MulAut.conj h).toMonoidHom := ⟨hxA, hxmap⟩
    rw [hbot] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)

theorem tiPair_exists_ne_one_mem_center {T X : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hXT : X ≤ T) (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x ≠ 1 ∧ ∀ t ∈ T, t * x = x * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let X' : Subgroup ↥T := X.subgroupOf T
  have hX'n : X'.Normal := ⟨fun x hx t => by
    show ((t * x * t⁻¹ : ↥T) : G) ∈ X
    have : ((t * x * t⁻¹ : ↥T) : G) = (t : G) * (x : G) * (t : G)⁻¹ := rfl
    rw [this]
    exact hXn t t.2 x hx⟩
  have hX'ne : X' ≠ ⊥ := by
    intro h
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXT hx⟩ : ↥T) ∈ X' := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hX'ne
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hzX : ((z : ↥T) : G) ∈ X := (Subgroup.mem_inf.1 z.2).1
  have hzc := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2
  refine ⟨((z : ↥T) : G), hzX, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun t ht => ?_⟩
  exact congrArg Subtype.val (hzc ⟨t, ht⟩)

omit [Finite G] in
theorem tiPair_mem_sup_of_commute {U V : Subgroup G} (h : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    {x : G} (hx : x ∈ U ⊔ V) : ∃ u ∈ U, ∃ v ∈ V, u * v = x := by
  rw [sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, V.one_mem, by simp⟩
    · exact ⟨1, U.one_mem, y, hy, by simp⟩
  · exact ⟨1, U.one_mem, 1, V.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
    refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, v₁ * v₂, V.mul_mem hv₁ hv₂, ?_⟩
    calc u₁ * u₂ * (v₁ * v₂) = u₁ * (u₂ * v₁) * v₂ := by group
      _ = u₁ * (v₁ * u₂) * v₂ := by rw [h u₂ hu₂ v₁ hv₁]
      _ = u₁ * v₁ * (u₂ * v₂) := by group
  · rintro _ _ ⟨u, hu, v, hv, rfl⟩
    refine ⟨u⁻¹, U.inv_mem hu, v⁻¹, V.inv_mem hv, ?_⟩
    calc u⁻¹ * v⁻¹ = (v * u)⁻¹ := by group
      _ = (u * v)⁻¹ := by rw [h u hu v hv]

omit [Finite G] in
theorem tiPair_commutator_mem {K P Q : Subgroup G} (hPK : P ≤ K)
    (hP : CFSG.Open.IsElemAbelian 2 P) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (tiQ : ∀ h ∈ K, ∀ x ∈ Q, x ≠ 1 → h * x = x * h → h ∈ normalizer (Q : Set G))
    {v a : G} (hvQ : v ∈ Q) (hvP : v ∈ normalizer (P : Set G)) (haP : a ∈ P) :
    v⁻¹ * a * v * a⁻¹ ∈ P ⊓ normalizer (Q : Set G) := by
  have ha' : v⁻¹ * a * v ∈ P := by
    have := (mem_normalizer_iff.mp (inv_mem hvP) a).mp haP
    simpa using this
  have hwP : v⁻¹ * a * v * a⁻¹ ∈ P := P.mul_mem ha' (P.inv_mem haP)
  refine ⟨hwP, ?_⟩
  by_cases hv1 : v = 1
  · subst hv1
    have h1 : (1 : G)⁻¹ * a * 1 * a⁻¹ = 1 := by group
    rw [h1]
    exact one_mem _
  · refine tiQ _ (hPK hwP) v hvQ hv1 ?_
    have hvv : v * v = 1 := tiPair_mul_self hQ hvQ
    have haa : a * a = 1 := tiPair_mul_self hP haP
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    have hc : a * (v⁻¹ * a * v) = (v⁻¹ * a * v) * a := tiPair_comm hP haP ha'
    rw [hvi] at hc
    rw [hvi, hai]
    have e1 : (v * a * v * a) * v = a * v * a := by
      rw [← hc]
      simp only [mul_assoc, hvv, mul_one]
    have e2 : v * (v * a * v * a) = a * v * a := by
      have : v * (v * a * v * a) = (v * v) * a * v * a := by simp only [mul_assoc]
      rw [this, hvv, one_mul]
    exact e1.trans e2.symm

omit [Finite G] in
theorem tiPair_le_normalizer_sup {K P Q : Subgroup G} (hPK : P ≤ K)
    (hP : CFSG.Open.IsElemAbelian 2 P) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (tiQ : ∀ h ∈ K, ∀ x ∈ Q, x ≠ 1 → h * x = x * h → h ∈ normalizer (Q : Set G)) :
    P ≤ normalizer (((P ⊓ normalizer (Q : Set G)) ⊔ (Q ⊓ normalizer (P : Set G)) :
      Subgroup G) : Set G) := by
  refine le_normalizer_iff.mpr fun a haP k hk => ?_
  have hle : (P ⊓ normalizer (Q : Set G)) ⊔ (Q ⊓ normalizer (P : Set G)) ≤
      ((P ⊓ normalizer (Q : Set G)) ⊔ (Q ⊓ normalizer (P : Set G))).comap
        (MulAut.conj a).toMonoidHom := by
    refine sup_le (fun u hu => ?_) (fun v hv => ?_)
    · rw [mem_comap]
      have h1 : a * u * a⁻¹ = u := by
        rw [tiPair_comm hP haP hu.1, mul_inv_cancel_right]
      have h2 : (MulAut.conj a).toMonoidHom u = u := by
        simpa [MulAut.conj_apply] using h1
      rw [h2]
      exact mem_sup_left hu
    · rw [mem_comap]
      have hw := tiPair_commutator_mem hPK hP hQ tiQ hv.1 hv.2 haP
      have h1 : (MulAut.conj a).toMonoidHom v = v * (v⁻¹ * a * v * a⁻¹) := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
      rw [h1]
      exact mul_mem (mem_sup_right hv) (mem_sup_left hw)
  have := hle hk
  rw [mem_comap] at this
  simpa [MulAut.conj_apply] using this

theorem normalizer_of_TI_pair {H A B : Subgroup G} (hH : IsPGroup 2 H) (hAH : A ≤ H) (hBH : B ≤ H)
    (hA : CFSG.Open.IsElemAbelian 2 A) (hB : CFSG.Open.IsElemAbelian 2 B)
    (hTIA : ∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom = A ∨
      A ⊓ A.map (MulAut.conj h).toMonoidHom = ⊥)
    (hTIB : ∀ h ∈ H, B.map (MulAut.conj h).toMonoidHom = B ∨
      B ⊓ B.map (MulAut.conj h).toMonoidHom = ⊥)
    (hN : A ⊓ Subgroup.normalizer (B : Set G) ≠ ⊥) (hcard : Nat.card B ≤ Nat.card A) :
    A ⊔ B ≤ Subgroup.normalizer (A : Set G) := by
  have hKH : A ⊔ B ≤ H := sup_le hAH hBH
  have hK2 : IsPGroup 2 ↥(A ⊔ B) := hH.to_le hKH
  have tiA : ∀ h ∈ A ⊔ B, ∀ x ∈ A, x ≠ 1 → h * x = x * h → h ∈ normalizer (A : Set G) :=
    fun h hh x hx hx1 hc => tiPair_mem_normalizer_of_commute hTIA (hKH hh) hx hx1 hc
  have tiB : ∀ h ∈ A ⊔ B, ∀ x ∈ B, x ≠ 1 → h * x = x * h → h ∈ normalizer (B : Set G) :=
    fun h hh x hx hx1 hc => tiPair_mem_normalizer_of_commute hTIB (hKH hh) hx hx1 hc
  by_cases hBA : B ≤ normalizer (A : Set G)
  · exact sup_le le_normalizer hBA
  obtain ⟨b, hbB, hbA⟩ := SetLike.not_le_iff_exists.mp hBA
  have hAB : ∀ x ∈ A, x ∈ B → x = 1 := by
    intro x hxA hxB
    by_contra hx1
    exact hbA (tiA b (mem_sup_right hbB) x hxA hx1 (tiPair_comm hB hbB hxB))
  set U : Subgroup G := A ⊓ normalizer (B : Set G) with hU
  set V : Subgroup G := B ⊓ normalizer (A : Set G) with hV
  have hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := by
    intro u hu v hv
    have hcA : v⁻¹ * u⁻¹ * v * u ∈ A := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hv.2) u⁻¹).mp (inv_mem hu.1)
      have h2 : v⁻¹ * u⁻¹ * v ∈ A := by simpa using h1
      exact A.mul_mem h2 hu.1
    have hcB : v⁻¹ * u⁻¹ * v * u ∈ B := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hu.2) v).mp hv.1
      have h2 : u⁻¹ * v * u ∈ B := by simpa using h1
      have h3 := B.mul_mem (B.inv_mem hv.1) h2
      simpa only [mul_assoc] using h3
    have hc1 : v⁻¹ * u⁻¹ * v * u = 1 := hAB _ hcA hcB
    have h4 : v = u⁻¹ * v * u := by
      have : v⁻¹ * (u⁻¹ * v * u) = 1 := by rw [← hc1]; group
      exact inv_mul_eq_one.mp this
    calc u * v = u * (u⁻¹ * v * u) := by rw [← h4]
      _ = v * u := by group
  have hXK : U ⊔ V ≤ A ⊔ B := sup_le_sup inf_le_left inf_le_left
  have hXne : U ⊔ V ≠ ⊥ := ne_bot_of_le_ne_bot hN le_sup_left
  have hAX : A ≤ normalizer ((U ⊔ V : Subgroup G) : Set G) :=
    tiPair_le_normalizer_sup (K := A ⊔ B) le_sup_left hA hB tiB
  have hBX : B ≤ normalizer ((U ⊔ V : Subgroup G) : Set G) := by
    rw [sup_comm U V]
    exact tiPair_le_normalizer_sup (K := A ⊔ B) le_sup_right hB hA tiA
  have hKX : ∀ t ∈ A ⊔ B, ∀ x ∈ U ⊔ V, t * x * t⁻¹ ∈ U ⊔ V :=
    le_normalizer_iff.mp (sup_le hAX hBX)
  obtain ⟨z, hzX, hz1, hzc⟩ := tiPair_exists_ne_one_mem_center hK2 hXK hKX hXne
  by_cases hCV : ∃ v ∈ V, v ≠ 1 ∧ ∀ a ∈ A, a * v = v * a
  · exfalso
    obtain ⟨v, hvV, hv1, hvc⟩ := hCV
    have hAN : A ≤ normalizer (B : Set G) := fun a ha =>
      tiB a (mem_sup_left ha) v hvV.1 hv1 (hvc a ha)
    have hUA : U = A := inf_eq_left.mpr hAN
    have hVB : V < B := by
      refine lt_of_le_of_ne inf_le_left fun h => hbA ?_
      have hbV : b ∈ V := by rw [h]; exact hbB
      exact hbV.2
    let f : U → V := fun u => ⟨(u : G)⁻¹ * b * u * b⁻¹,
      tiPair_commutator_mem (K := A ⊔ B) le_sup_right hB hA tiA u.2.1 u.2.2 hbB⟩
    have hf : Function.Injective f := by
      intro u u' h
      have h1 : (u : G)⁻¹ * b * u * b⁻¹ = (u' : G)⁻¹ * b * u' * b⁻¹ := congrArg Subtype.val h
      have h2 : (u : G)⁻¹ * b * u = (u' : G)⁻¹ * b * u' := mul_right_cancel h1
      have hcomm : b * ((u : G) * (u' : G)⁻¹) = ((u : G) * (u' : G)⁻¹) * b := by
        calc b * ((u : G) * (u' : G)⁻¹) = (u : G) * ((u : G)⁻¹ * b * u) * (u' : G)⁻¹ := by group
          _ = (u : G) * ((u' : G)⁻¹ * b * u') * (u' : G)⁻¹ := by rw [h2]
          _ = ((u : G) * (u' : G)⁻¹) * b := by group
      have hcA : (u : G) * (u' : G)⁻¹ ∈ A := A.mul_mem u.2.1 (A.inv_mem u'.2.1)
      by_cases hc1 : (u : G) * (u' : G)⁻¹ = 1
      · exact Subtype.ext (mul_inv_eq_one.mp hc1)
      · exact absurd (tiA b (mem_sup_right hbB) _ hcA hc1 hcomm) hbA
    have h1 : Nat.card U ≤ Nat.card V := Nat.card_le_card_of_injective f hf
    have h2 : Nat.card V < Nat.card B := Subgroup.card_lt_of_lt hVB
    have h3 : Nat.card U = Nat.card A := by rw [hUA]
    omega
  · obtain ⟨u, hu, v, hv, rfl⟩ := tiPair_mem_sup_of_commute hUV hzX
    have hv1 : v = 1 := by
      by_contra hv1
      apply hCV
      refine ⟨v, hv, hv1, fun a ha => ?_⟩
      have hzc' : a * (u * v) = (u * v) * a := hzc a (mem_sup_left ha)
      have hua : (u : G) * a = a * u := tiPair_comm hA hu.1 ha
      calc a * v = u⁻¹ * (u * a) * v := by group
        _ = u⁻¹ * (a * u) * v := by rw [hua]
        _ = u⁻¹ * (a * (u * v)) := by group
        _ = u⁻¹ * ((u * v) * a) := by rw [hzc']
        _ = v * a := by group
    subst hv1
    have hu1 : u ≠ 1 := by simpa using hz1
    intro t ht
    exact tiA t ht u hu.1 hu1 (by simpa using hzc t ht)

end CFSG.LocalAnalysis.RankThreeUC.S15
