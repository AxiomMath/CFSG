module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGQ

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem eq_of_sq_eq_one {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  haveI := Fintype.ofFinite C
  by_contra hne
  have h := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter fun a : C => a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hx
    · exact hy
  have hcard : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hne
    · simp [hx1.symm, hy1.symm]
  have := Finset.card_le_card hsub
  convert h using 1
  omega

theorem conj_eq_of_cyclic (c : KQCfg A p Kb Sb Bb Mb z) [IsCyclic ↥Sb] {a : A} (ha : a ∈ Sb)
    (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) {b : A} (hb : b ∈ Bb) : b * a * b⁻¹ = a := by
  have hmem : b * a * b⁻¹ ∈ Sb := (mem_normalizer_iff.mp (c.B_le_S hb) a).mp ha
  have h2 : (b * a * b⁻¹) ^ 2 = 1 := by
    rw [pow_two] at ha2 ⊢
    calc b * a * b⁻¹ * (b * a * b⁻¹) = b * (a * a) * b⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have h1 : b * a * b⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have : a = b⁻¹ * (b * a * b⁻¹) * b := by group
    rw [this, h]
    group
  have := eq_of_sq_eq_one (C := ↥Sb) (x := ⟨b * a * b⁻¹, hmem⟩) (y := ⟨a, ha⟩)
    (Subtype.ext (by simpa using h2)) (Subtype.ext (by simpa using ha2))
    (fun h => h1 (congrArg Subtype.val h)) (fun h => ha1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem eq_one_of_map_eq_one (c : KQCfg A p Kb Sb Bb Mb z) {W : Type*} [Group W] (ρ : A →* W)
    (hρ : ¬ Kb ≤ ρ.ker) {x : A} (hx : x ∈ Kb ⊔ Sb) (h : ρ x = 1) : x = 1 := by
  haveI := c.simple
  have hKn : ∀ k ∈ Kb, ρ k = 1 → k = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.comp Kb.subtype).ker with hbot | htop
    · intro k hk hρk
      have : (⟨k, hk⟩ : ↥Kb) ∈ (ρ.comp Kb.subtype).ker := hρk
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      apply hρ
      intro k hk
      have : (⟨k, hk⟩ : ↥Kb) ∈ (ρ.comp Kb.subtype).ker := by rw [htop]; exact Subgroup.mem_top _
      exact this
  refine KGQ.eq_one_of_centralizes c hx fun n hn => ?_
  have hxn : x ∈ normalizer (Kb : Set A) := KGQ.sup_le_normalizer c hx
  have hmem : x * n * x⁻¹ * n⁻¹ ∈ Kb :=
    Kb.mul_mem ((mem_normalizer_iff.mp hxn n).mp hn) (Kb.inv_mem hn)
  have h1 : x * n * x⁻¹ * n⁻¹ = 1 := by
    refine hKn _ hmem ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, one_mul, inv_one, mul_one,
      mul_inv_cancel]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem mem_normalizer_zpowers_of_commute {a b : A} (h : b * a = a * b) :
    b ∈ normalizer (zpowers a : Set A) :=
  KGB.mem_normalizer_of_commute fun t ht => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_right (show Commute b a from h) i).eq

theorem normalizer_zpowers_le (c : KQCfg A p Kb Sb Bb Mb z) [IsCyclic ↥Sb] {a : A} (ha : a ∈ Sb)
    (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) : normalizer (zpowers a : Set A) ≤ Mb := by
  refine c.cover (zpowers a) (zpowers_le.mpr ha) ?_ ?_ ?_
  · intro h
    exact ha1 (zpowers_eq_bot.mp h)
  · intro s hs
    refine mem_normalizer_zpowers_of_commute ?_
    exact congrArg Subtype.val (mul_comm' (⟨s, hs⟩ : ↥Sb) ⟨a, ha⟩)
  · intro b hb
    refine mem_normalizer_zpowers_of_commute ?_
    have := conj_eq_of_cyclic c ha ha1 ha2 hb
    rwa [mul_inv_eq_iff_eq_mul] at this

theorem rankThreePrimeCore_eq_bot {Y : Subgroup A} (hY : IsSimpleGroup ↥Y) (hp : p.Prime)
    (hpY : p ∣ Nat.card ↥Y) : rankThreePrimeCore p Y = ⊥ := by
  unfold rankThreePrimeCore relPPrimeCore
  refine le_bot_iff.mp (sSup_le fun N hN => ?_)
  obtain ⟨hNY, hNn, hcop⟩ := hN
  rcases hY.eq_bot_or_eq_top_of_normal (N.subgroupOf Y) with h | h
  · intro n hn
    have : (⟨n, hNY hn⟩ : ↥Y) ∈ N.subgroupOf Y := hn
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hNY' : N = Y := by
      refine le_antisymm hNY fun y hy => ?_
      have : (⟨y, hy⟩ : ↥Y) ∈ N.subgroupOf Y := by rw [h]; exact Subgroup.mem_top _
      exact this
    rw [hNY'] at hcop
    exact hp.one_lt.ne' (hcop.eq_one_of_dvd hpY)

theorem isSimpleSection_bot {Y : Subgroup A} (hY : IsSimpleGroup ↥Y)
    (hab : ∃ x y : ↥Y, x * y ≠ y * x) : S622IsSimpleSection Y ⊥ := by
  obtain ⟨x, y, hxy⟩ := hab
  refine ⟨bot_le, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    infer_instance
  · intro h
    apply hxy
    have hx : (x : A) ∈ (⊥ : Subgroup A) := by rw [h]; exact x.2
    have hy : (y : A) ∈ (⊥ : Subgroup A) := by rw [h]; exact y.2
    rw [Subgroup.mem_bot] at hx hy
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy])
  · intro N _ hNY hN
    rcases hY.eq_bot_or_eq_top_of_normal (N.subgroupOf Y) with h | h
    · left
      refine le_antisymm (fun n hn => ?_) bot_le
      have : (⟨n, hNY hn⟩ : ↥Y) ∈ N.subgroupOf Y := hn
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · right
      refine le_antisymm hNY fun n hn => ?_
      have : (⟨n, hn⟩ : ↥Y) ∈ N.subgroupOf Y := by rw [h]; exact Subgroup.mem_top _
      exact this
  · intro hall
    apply hxy
    have := hall x x.2 y y.2
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, this])

theorem false_of_transv (hT : KGTransvCent) (h241 : KFact2401ThreeOmega)
    (c : KQCfg A p Kb Sb Bb Mb z) (hs : KQStrong A p Mb z) (hc : KGStep4Concl A Kb Sb)
    (hbot : Sb ⊓ Kb = ⊥) [IsCyclic ↥Sb] {V : Type} [CommGroup V] [Finite V]
    (hV : IsElemAbelianTwo V) (ρ : A →* MulAut V) (hρ : ¬ Kb ≤ ρ.ker) {a : A} (ha : a ∈ Sb)
    (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) (htv : IsTransvection (ρ a)) : False := by
  have hp := c.prime
  have hp5 := c.five_le
  haveI : Fact p.Prime := ⟨hp⟩
  have haK : a ∉ Kb := fun h => ha1 (by
    have : a ∈ Sb ⊓ Kb := ⟨ha, h⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this)
  have hXn : Kb ⊔ zpowers a ≤ Kb ⊔ Sb := sup_le_sup_left (zpowers_le.mpr ha) _
  have hcomm : a * z = z * a := by
    have := conj_eq_of_cyclic c ha ha1 ha2 c.z_mem_B
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  obtain ⟨ε, n, hn3, hΩ, Y, hYle, hzY, hYs, hYn, h3⟩ := hT A V hV ρ Kb a z p c.simple c.nonab
    hc.2.2 (c.S_le_K ha) ha1 ha2 haK
    (fun x hx hxc => KGQ.eq_one_of_centralizes c (hXn hx) hxc)
    (fun x hx hρx => eq_one_of_map_eq_one c ρ hρ (hXn hx) hρx) htv c.z_mem_K c.z_order hp hp5
    hcomm
  have hYK : Y ≤ Kb := hYle.trans inf_le_left
  have hYC : Y ≤ centralizer ({a} : Set A) := hYle.trans inf_le_right
  have hYM : Y ≤ Mb := fun y hy =>
    normalizer_zpowers_le c ha ha1 ha2
      (mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp (hYC hy)))
  have hpY : p ∣ Nat.card ↥Y := by
    have h1 : orderOf (⟨z, hzY⟩ : ↥Y) = p := by
      rw [Subgroup.orderOf_mk]
      exact c.z_order
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hcore : rankThreePrimeCore p Y = ⊥ := rankThreePrimeCore_eq_bot hYs hp hpY
  have hsec : S622IsSimpleSection Y (rankThreePrimeCore p Y) := by
    rw [hcore]
    exact isSimpleSection_bot hYs hYn
  have hrel : 3 ∣ (rankThreePrimeCore p Y).relIndex Y := by
    rw [hcore, Subgroup.relIndex_bot_left]
    exact h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3
  have hyY : (y' : A) ∈ Y := y'.2
  have hyo : orderOf (y' : A) = 3 := by rw [Subgroup.orderOf_coe]; exact hy'
  have hyP : IsPGroup 3 (zpowers (y' : A)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨F, hF, hyF⟩ :=
    KGB.exists_isSylowOf_ge (f := 3) (L := Kb) (zpowers_le.mpr (hYK hyY)) hyP
  have hFY : F ⊓ Y ≠ ⊥ := by
    intro h
    have hmem : (y' : A) ∈ F ⊓ Y := ⟨hyF (mem_zpowers _), hyY⟩
    rw [h, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hyo
    omega
  have hstrong : ∀ F₁ : Subgroup A, F₁ ≤ F → F₁ ≠ ⊥ → normalizer (F₁ : Set A) ≤ Mb :=
    fun F₁ h1 h2 => hs 3 Nat.prime_three (by norm_num) (by omega) Y hYM hzY hsec hrel F
      hF.isPGroup hFY F₁ h1 h2
  have hKM : Kb ≤ Mb := h241 A Kb F ε n hn3 hΩ hF Mb fun S₀ hS₀ hS₀1 =>
    inf_le_left.trans (hstrong S₀ hS₀ hS₀1)
  exact c.not_le hKM

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix
