module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank

namespace Bridge

namespace Alt57

variable {S : Type} [CommGroup S] [Finite S] {G L A : Subgroup (MulAut S)} {m : ℕ}

omit [Finite S] in
theorem ffJ_le (G : Subgroup (MulAut S)) : ffJ G ≤ G :=
  iSup₂_le fun _ hA => hA.1

theorem sl2_card {q : ℕ} (hq : ∃ n : ℕ, q = 2 ^ n) (h : q * (q ^ 2 - 1) = 60 ∨ q * (q ^ 2 - 1) = 2520) :
    q = 4 ∧ q * (q ^ 2 - 1) = 60 := by
  obtain ⟨n, rfl⟩ := hq
  by_cases hn : n ≤ 4
  · interval_cases n <;> simp at h ⊢
  · exfalso
    push Not at hn
    have h1 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h3 : 1024 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h4 : 32 * 1023 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega

theorem sl3_card {q : ℕ} (hq : ∃ n : ℕ, q = 2 ^ n) :
    q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) ≠ 60 ∧ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) ≠ 2520 := by
  obtain ⟨n, rfl⟩ := hq
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp
  · push Not at hn
    have h1 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h3 : 64 ≤ (2 ^ n) ^ 3 := by nlinarith
    have h4 : 63 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have h5 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
    have h6 : 64 * 63 * 15 ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 h4) h5
    omega

theorem card_sl3_field (K : Type) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      Nat.card K ^ 3 * (Nat.card K ^ 3 - 1) * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_three, Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 2 := ⟨Fintype.card K - 2, by omega⟩
  rw [hr]
  have e : ((r + 2) ^ 3 - 1) * ((r + 2) ^ 3 - (r + 2)) * ((r + 2) ^ 3 - (r + 2) ^ 2) =
      ((r + 2) ^ 3 * ((r + 2) ^ 3 - 1) * ((r + 2) ^ 2 - 1)) * (r + 2 - 1) := by
    have h1 : 1 ≤ (r + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h2 : (r + 2) ≤ (r + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 : (r + 2) ^ 2 ≤ (r + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : 1 ≤ (r + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h5 : 1 ≤ r + 2 := by omega
    zify [h1, h2, h3, h4, h5]
    ring
  rw [e]
  exact Nat.mul_div_cancel _ (by omega)

section Cases

namespace Ctx

variable (C : Ctx G L m)

include C

theorem case1 (h : B42Case1 G L A) : m = 5 ∧ BinaryNaturalSL L ⊤ ⊥ 2 2 := by
  obtain ⟨-, ⟨n, hn⟩, -, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
  have hL : Nat.card ↥L = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv]
    exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
  rw [hcard] at hL
  obtain ⟨hq4, hq60⟩ := sl2_card ⟨n, rfl⟩ (by rw [← hL]; exact C.card_cases)
  have hn2 : n = 2 := by
    have : (2 : ℕ) ^ n = 2 ^ 2 := by rw [hq4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hn2
  refine ⟨?_, hn⟩
  have hc60 : Nat.card ↥L = 60 := by rw [hL]; exact hq60
  rcases C.m_cases with rfl | rfl
  · rfl
  · rw [C.card_eq, card_alt_seven] at hc60; omega

theorem case2_false (h : B42Case2 G L) : False := by
  obtain ⟨-, ⟨n, hn⟩, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
  have hL : Nat.card ↥L = Nat.card K ^ 3 * (Nat.card K ^ 3 - 1) * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv]
    exact card_sl3_field K
  rw [hcard] at hL
  obtain ⟨h1, h2⟩ := sl3_card (q := 2 ^ n) ⟨n, rfl⟩
  rcases C.card_cases with h | h
  · exact h1 (by rw [← hL]; exact h)
  · exact h2 (by rw [← hL]; exact h)

theorem case3_false (facts : Alt57ModelFacts) (hA : IsFFStarOffender G A) (h : B42Case3 G L) :
    False := by
  obtain ⟨⟨n, hn, -⟩, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSp4.exists_equiv hn
  have hLJ : L ≤ ffJ G := C.le_ffJ hA
  have hJG : ffJ G ≤ G := ffJ_le G
  have hnorm : (L.subgroupOf (ffJ G)).Normal := ⟨fun l hl g => by
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact C.normal (g : MulAut S) (hJG g.2) _ hl⟩
  have hsq : ∀ x : ↥(ffJ G), x ^ 2 ∈ L.subgroupOf (ffJ G) := fun x => by
    rw [Subgroup.mem_subgroupOf]
    exact C.hsq _ (hJG x.2)
  obtain ⟨ei⟩ := C.iso
  exact facts.sp4 K ⟨n, hcard⟩ ↥(ffJ G) e.toMonoidHom e.surjective (L.subgroupOf (ffJ G)) hnorm
    hsq m C.m_cases ⟨(Subgroup.subgroupOfEquivOfLe hLJ).trans ei⟩

theorem case4_false (facts : Alt57ModelFacts) (hA : IsFFStarOffender G A) (h : B42Case4 G L A) :
    False := by
  obtain ⟨⟨n, ⟨K, hK, hKfin, hcard, π, hπ⟩, -, -⟩, -⟩ := h
  have hLJ : L ≤ ffJ G := C.le_ffJ hA
  have hJG : ffJ G ≤ G := ffJ_le G
  have hnorm : (L.subgroupOf (ffJ G)).Normal := ⟨fun l hl g => by
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact C.normal (g : MulAut S) (hJG g.2) _ hl⟩
  have hsq : ∀ x : ↥(ffJ G), x ^ 2 ∈ L.subgroupOf (ffJ G) := fun x => by
    rw [Subgroup.mem_subgroupOf]
    exact C.hsq _ (hJG x.2)
  obtain ⟨ei⟩ := C.iso
  exact facts.g2 K ⟨n, hcard⟩ ↥(ffJ G) π hπ.1 (L.subgroupOf (ffJ G)) hnorm hsq m C.m_cases
    ⟨(Subgroup.subgroupOfEquivOfLe hLJ).trans ei⟩

theorem case6_false (h : B42Case6 G L A) : False := by
  obtain ⟨-, ⟨π, hπ⟩, -⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alt_isSimple (by norm_num)
  have := C.simple
  have : Nontrivial ↥L := C.simple.toNontrivial
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple
    (Γ := alternatingGroup (Fin 6)) (H := ↥L) π hπ.1
  have h1 := Nat.card_congr e.toEquiv
  rw [card_alt_six] at h1
  rcases C.card_cases with h | h <;> omega

theorem case7 (h : B42Case7 G L A) : m = 7 ∧ A7Four L ⊤ ⊥ ∧ Nat.card S = 2 ^ 4 := by
  obtain ⟨-, -, hA7, hcard, -, -⟩ := h
  obtain ⟨α, π, hπ⟩ := hA7
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alt_isSimple (by norm_num)
  have := C.simple
  have : Nontrivial ↥L := C.simple.toNontrivial
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple
    (Γ := alternatingGroup (Fin 7)) (H := ↥L) π hπ.1
  have h1 := Nat.card_congr e.toEquiv
  rw [card_alt_seven] at h1
  rcases C.m_cases with rfl | rfl
  · rw [C.card_eq, card_alt_five] at h1; omega
  · exact ⟨rfl, ⟨α, π, hπ⟩, hcard⟩

theorem case8_false (h : B42Case8 G L A) : False := by
  obtain ⟨-, -, -, K, hK, hKfin, Γ₀, hK4, -, hHat, -, π, hπ, -⟩ := h
  have hinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
  have hbot : Subgroup.center ↥Γ₀ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgL : π g ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ : ∃ y : ↥Γ₀, π y = x := hπ.1 x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg y]
    rw [C.center_bot, Subgroup.mem_bot] at hgL
    exact Subgroup.mem_bot.2 (hinj (by rw [hgL, map_one]))
  have h3 := hHat.2.1
  rw [hbot, Subgroup.card_bot] at h3
  omega

theorem case9_false (h : B42Case9 G L) : False := by
  obtain ⟨-, n, hn, hnat, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hnat
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have : NeZero n := ⟨by rcases hn with rfl | rfl <;> norm_num⟩
  have hL : Nat.card ↥L = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
    rw [← Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL n K).toEquiv]
    exact card_sl_two_field n K hK2
  rcases hn with rfl | rfl
  · rw [Fin.prod_univ_four] at hL
    norm_num at hL
    rcases C.card_cases with h | h <;> omega
  · rw [Fin.prod_univ_five] at hL
    norm_num at hL
    rcases C.card_cases with h | h <;> omega

theorem case10_false (h : B42Case10 G L A) : False := by
  obtain ⟨⟨π, hπ⟩, -⟩ := h
  obtain ⟨e⟩ := C.iso
  exact noAlt57Image_sl4 ↥L π hπ.1 ⊤ inferInstance (fun _ => Subgroup.mem_top _) m C.m_cases
    ⟨Subgroup.topEquiv.trans e⟩

theorem case11_false (h : B42Case11 G L A) : False := by
  obtain ⟨-, -, -, -, π, hπ, -⟩ := h
  obtain ⟨e⟩ := C.iso
  exact noAlt57Image_sl5 ↥L π hπ.1 ⊤ inferInstance (fun _ => Subgroup.mem_top _) m C.m_cases
    ⟨Subgroup.topEquiv.trans e⟩

theorem case5 (hA : IsFFStarOffender G A) (h : B42Case5 G A) : AlternatingNatural L ⊤ ⊥ m := by
  obtain ⟨⟨n, hn, π, hπ, -⟩, -⟩ := h
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> omega
  have := C.simple
  have : Nontrivial ↥L := C.simple.toNontrivial
  have hsA : IsSimpleGroup (alternatingGroup (Fin n)) := alt_isSimple hn5
  have hLJ : L ≤ ffJ G := C.le_ffJ hA
  have hJG : ffJ G ≤ G := ffJ_le G
  have hsurj : Function.Surjective π := hπ.1
  obtain ⟨-, hZU, hkerle, -, -, hsecinv, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  let H₀ : Subgroup (MulAut S) := ffJ G
  let Lr : Subgroup ↥H₀ := L.subgroupOf H₀
  have hLrN : Lr.Normal := ⟨fun l hl g => by
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact C.normal (g : MulAut S) (hJG g.2) _ hl⟩
  let P : Subgroup ↥H₀ := (alternatingGroup (Fin n)).map π
  have hPN : P.Normal := Subgroup.Normal.map inferInstance π hsurj
  have : IsSimpleGroup ↥Lr := (Subgroup.subgroupOfEquivOfLe hLJ).isSimpleGroup
  have hmemLr : ∀ l : ↥L, (⟨(l : MulAut S), hLJ l.2⟩ : ↥H₀) ∈ Lr := fun l => l.2
  obtain ⟨a₀, b₀, hab₀⟩ := C.nonab
  have hN1 : ((Lr ⊓ P).subgroupOf Lr).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨Lr.mul_mem (Lr.mul_mem g.2 hx.1) (Lr.inv_mem g.2), hPN.conj_mem _ hx.2 (g : ↥H₀)⟩⟩
  have hLrP : Lr = P := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Lr ⊓ P).subgroupOf Lr) with h0 | h0
    · exfalso
      have hLP : ∀ x ∈ Lr ⊓ P, x = 1 := by
        intro x hx
        have : (⟨x, hx.1⟩ : ↥Lr) ∈ (Lr ⊓ P).subgroupOf Lr := hx
        rw [h0, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      have hcomm : ∀ p ∈ P, ∀ l ∈ Lr, p * l = l * p := by
        intro p hp l hl
        have h1 : p * l * p⁻¹ * l⁻¹ ∈ Lr ⊓ P := by
          refine ⟨Lr.mul_mem (hLrN.conj_mem _ hl p) (Lr.inv_mem hl), ?_⟩
          have : p * (l * p⁻¹ * l⁻¹) = p * l * p⁻¹ * l⁻¹ := by group
          rw [← this]
          exact P.mul_mem hp (hPN.conj_mem _ (P.inv_mem hp) l)
        have := hLP _ h1
        calc p * l = (p * l * p⁻¹ * l⁻¹) * (l * p) := by group
          _ = l * p := by rw [this, one_mul]
      have hP1 : ∀ p ∈ P, p = 1 := by
        intro p hp
        refine Subtype.ext (C.cent_trivial (p : MulAut S) (hJG p.2) fun l hl => ?_)
        have := hcomm p hp ⟨l, hLJ hl⟩ hl
        exact congrArg Subtype.val this
      have hsign : ∀ σ : Equiv.Perm (Fin n), π σ = 1 ∨ π σ = (π (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩))⁻¹ := by
        intro σ
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
        · exact Or.inl (hP1 _ (Subgroup.mem_map.2 ⟨σ, Equiv.Perm.mem_alternatingGroup.2 h1, rfl⟩))
        · right
          have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
          have h2 : σ * Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ∈ alternatingGroup (Fin n) := by
            rw [Equiv.Perm.mem_alternatingGroup, map_mul, h1, Equiv.Perm.sign_swap hne]; rfl
          have h3 := hP1 _ (Subgroup.mem_map.2 ⟨_, h2, rfl⟩)
          rw [map_mul] at h3
          exact eq_inv_of_mul_eq_one_left h3
      have hcommH : ∀ x y : ↥H₀, x * y = y * x := by
        intro x y
        obtain ⟨σ, rfl⟩ := hsurj x
        obtain ⟨τ, rfl⟩ := hsurj y
        rcases hsign σ with h1 | h1 <;> rcases hsign τ with h2 | h2 <;> rw [h1, h2] <;> simp
      apply hab₀
      have := hcommH ⟨(a₀ : MulAut S), hLJ a₀.2⟩ ⟨(b₀ : MulAut S), hLJ b₀.2⟩
      exact Subtype.ext (congrArg (fun z : ↥H₀ => (z : MulAut S)) this)
    ·
      have hLP : Lr ≤ P := by
        intro x hx
        have : (⟨x, hx⟩ : ↥Lr) ∈ (Lr ⊓ P).subgroupOf Lr := by rw [h0]; trivial
        exact (Subgroup.mem_subgroupOf.1 this).2
      have hQN : (Lr.comap (π.comp (alternatingGroup (Fin n)).subtype)).Normal :=
        Subgroup.Normal.comap hLrN _
      refine le_antisymm hLP ?_
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Lr.comap (π.comp (alternatingGroup (Fin n)).subtype)) with hq | hq
      · exfalso
        have h1 : ∀ x ∈ Lr, x = 1 := by
          intro x hx
          obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 (hLP hx)
          have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin n))) ∈
              Lr.comap (π.comp (alternatingGroup (Fin n)).subtype) := hx
          rw [hq, Subgroup.mem_bot] at this
          have h2 : a = 1 := congrArg Subtype.val this
          rw [h2, map_one]
        apply hab₀
        have := h1 _ (hmemLr a₀)
        have h4 := h1 _ (hmemLr b₀)
        have h5 : a₀ = 1 := Subtype.ext (congrArg (fun z : ↥H₀ => (z : MulAut S)) this)
        rw [h5]; simp
      · rintro _ ⟨a, ha, rfl⟩
        have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin n))) ∈
            Lr.comap (π.comp (alternatingGroup (Fin n)).subtype) := by rw [hq]; trivial
        exact this
  let π' : ↥(alternatingGroup (Fin n)) →* ↥L :=
    (((H₀.subtype).comp π).comp (alternatingGroup (Fin n)).subtype).codRestrict L (fun a => by
      have h1 : π (a : Equiv.Perm (Fin n)) ∈ P := Subgroup.mem_map.2 ⟨a, a.2, rfl⟩
      rw [← hLrP] at h1
      exact Subgroup.mem_subgroupOf.1 h1)
  have hsurj' : Function.Surjective π' := by
    intro l
    have h1 : (⟨(l : MulAut S), hLJ l.2⟩ : ↥H₀) ∈ P := by rw [← hLrP]; exact hmemLr l
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 h1
    exact ⟨⟨a, ha⟩, Subtype.ext (congrArg (fun z : ↥H₀ => (z : MulAut S)) hax)⟩
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple π' hsurj'
  have hcard := Nat.card_congr e.toEquiv
  have hnm : n = m := by
    rcases hn with rfl | rfl <;> rcases C.m_cases with rfl | rfl
    · rfl
    · rw [card_alt_five, C.card_eq, card_alt_seven] at hcard; omega
    · rw [card_alt_seven, C.card_eq, card_alt_five] at hcard; omega
    · rfl
  subst hnm
  refine ⟨π', hsurj', hZU, hkerle, fun h u hu => trivial, fun h z hz => ?_,
    fun γ m hm => hsecinv (Subtype.val γ) m hm, fun γ m hm => hkerinv (Subtype.val γ) m hm, β, hβs,
    hβk, fun γ u m hu hm hum => hβe (Subtype.val γ) u m hu hm hum⟩
  rw [Subgroup.mem_bot.1 hz, map_one]
  exact Subgroup.one_mem _

end Ctx

end Cases

theorem classification {KP : ∀ (Y : Type) [Group Y], Prop} (h42 : AsB42With KP)
    (facts : Alt57ModelFacts) (hS : ∀ s : S, s ^ 2 = 1) (C : Ctx G L m)
    (hHyp : B4HypWith KP G L) (hA : IsFFStarOffender G A) :
    (m = 5 ∧ BinaryNaturalSL L ⊤ ⊥ 2 2) ∨ AlternatingNatural L ⊤ ⊥ m ∨
      (m = 7 ∧ A7Four L ⊤ ⊥ ∧ Nat.card S = 2 ^ 4) := by
  have hc := h42 S hS G L hHyp A hA
  unfold B42Conclusion at hc
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact Or.inl (C.case1 h1)
  · exact (C.case2_false h2).elim
  · exact (C.case3_false facts hA h3).elim
  · exact (C.case4_false facts hA h4).elim
  · exact Or.inr (Or.inl (C.case5 hA h5))
  · exact (C.case6_false h6).elim
  · exact Or.inr (Or.inr (C.case7 h7))
  · exact (C.case8_false h8).elim
  · exact (C.case9_false h9).elim
  · exact (C.case10_false h10).elim
  · exact (C.case11_false h11).elim

end Alt57

end Bridge

end CFSG.QuasithinUnique
