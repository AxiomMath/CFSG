module

public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.CGT.Timmesfeld75.Config214
public import CFSG.CGT.Timmesfeld75.Dihedral
public import CFSG.CGT.Timmesfeld75.Inputs214
public import CFSG.CGT.Timmesfeld75.Lemma25

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

section Cores

theorem odd_card_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = pPrimeCore 2 X := by
    unfold fusionOddCore pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))

theorem eq_pCore_two_of_forall_eq_bot {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]
    (hN2 : IsPGroup 2 N)
    (hO2 : ∀ K : Subgroup (G ⧸ N), K.Normal → IsPGroup 2 K → K = ⊥) :
    N = CFSG.pCore 2 G := by
  refine le_antisymm (le_sSup ⟨hN, hN2⟩) (sSup_le fun K hK => ?_)
  have h := hO2 (K.map (QuotientGroup.mk' N)) (hK.1.map _ (QuotientGroup.mk'_surjective N))
    (hK.2.map _)
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h

end Cores

section Bender

theorem le_center_of_normal_isPGroup {Y : Type*} [Group Y] [Finite Y] {S : Subgroup Y}
    (hS : StrongWC S) (hnS : ¬ ∀ g : Y, conjSubgroup g S = S)
    (hK : Subgroup.normalClosure (S : Set Y) = ⊤) (N : Subgroup Y) [hN : N.Normal]
    (hN2 : IsPGroup 2 N) : N ≤ Subgroup.center Y := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro k
  exact (twoCore_le_center hS hnS N (by rw [hK]; exact le_top)
    (fun k _ n hn => hN.conj_mem n hn k) hN2 n hn k (by rw [hK]; exact Subgroup.mem_top k)).symm

theorem nonempty_mulEquiv_center_quotient {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Nonempty (Y ≃* Y ⧸ Subgroup.center Y) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm⟩

theorem models_of_isBenderGroup {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) (hS : StrongWC S) (hS0 : S ≠ ⊥)
    (hnS : ¬ ∀ g : Y, conjSubgroup g S = S) (hK : Subgroup.normalClosure (S : Set Y) = ⊤)
    (hg : ∃ g : Y, S ⊔ conjSubgroup g S = ⊤)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (Y ⧸ Subgroup.center Y)) :
    (∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ Nonempty (Y ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (Y ≃* Sz a))) := by
  have key : Subgroup.center Y = ⊥ → ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun hZ N hN hN2 => le_bot_iff.1 (hZ ▸ le_center_of_normal_isPGroup hS hnS hK N hN2)
  cases hB with
  | isPSL2 n hn e =>
    have hZ := hCen Y S hS hS0 hnS hK (Or.inl ⟨n, hn, ⟨e⟩⟩)
    obtain ⟨φ⟩ := nonempty_mulEquiv_center_quotient hZ
    exact ⟨key hZ, Or.inl ⟨n, hn, ⟨φ.trans e⟩⟩⟩
  | isSuzuki n hn e =>
    have hZ := hCen Y S hS hS0 hnS hK (Or.inr ⟨n, hn, ⟨e⟩⟩)
    obtain ⟨φ⟩ := nonempty_mulEquiv_center_quotient hZ
    exact ⟨key hZ, Or.inr ⟨n, hn, ⟨φ.trans e⟩⟩⟩
  | isPSU3 n hn e =>
    obtain ⟨g, hg⟩ := hg
    exact absurd hg (hU Y S hS hS0 hnS ⟨n, hn, ⟨e⟩⟩ g)

end Bender

section Dihedral

theorem eq_of_mk_eq_of_odd_card {Y : Type*} [Group Y] {A O : Subgroup Y} [O.Normal]
    (hA : IsElemAbelian 2 A) (hO : Odd (Nat.card O)) {x y : Y} (hx : x ∈ A) (hy : y ∈ A)
    (h : (x : Y ⧸ O) = y) : x = y := by
  have h1 : x⁻¹ * y ∈ O := QuotientGroup.eq.1 h
  exact inv_mul_eq_one.1
    (eq_one_of_mem_of_odd_card hA hO (A.mul_mem (A.inv_mem hx) hy) h1)

theorem mk_eq_of_commute_of_odd_orderOf_mul {Y : Type*} [Group Y] {O : Subgroup Y} [O.Normal]
    {a b : Y} (ha : a * a = 1) (hb : b * b = 1) (hodd : Odd (orderOf (a * b)))
    (hcomm : (a : Y ⧸ O) * b = b * a) : (a : Y ⧸ O) = b := by
  have hu : (a : Y ⧸ O) * a = 1 := by rw [← QuotientGroup.mk_mul, ha, QuotientGroup.mk_one]
  have hv : (b : Y ⧸ O) * b = 1 := by rw [← QuotientGroup.mk_mul, hb, QuotientGroup.mk_one]
  have h2 : ((a : Y ⧸ O) * b) ^ 2 = 1 := by
    calc ((a : Y ⧸ O) * b) ^ 2 = a * b * (a * b) := pow_two _
      _ = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hcomm]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [hu, hv, one_mul]
  have hdvd : orderOf ((a : Y ⧸ O) * b) ∣ orderOf (a * b) := by
    have := orderOf_map_dvd (QuotientGroup.mk' O) (a * b)
    simpa using this
  have h1 : orderOf ((a : Y ⧸ O) * b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h | h
    · exact h
    · exact absurd (Odd.of_dvd_nat hodd hdvd) (by rw [h]; decide)
  calc (a : Y ⧸ O) = a * (b * b) := by rw [hv, mul_one]
    _ = (a * b) * b := (mul_assoc _ _ _).symm
    _ = b := by rw [orderOf_eq_one_iff.1 h1, one_mul]

theorem exists_dihedral_of_zStar {Y : Type*} [Group Y] [Finite Y] {A B : Subgroup Y}
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B) (hAB : A ⊔ B = ⊤) (hZ : ZStarCase Y)
    (hA1 : A ≠ ⊥) (hBA : ¬ B ≤ A)
    (hodd : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ B, b ≠ 1 → Odd (orderOf (a * b))) :
    ∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (DihedralGroup n ≃* Y) := by
  have hOodd : Odd (Nat.card (fusionOddCore Y)) := odd_card_fusionOddCore Y
  have hcomm : ∀ y z : Y, (y : Y ⧸ fusionOddCore Y) * z = z * y := by
    intro y z
    have hy : y ∈ fusionZStar Y := by rw [hZ]; exact Subgroup.mem_top y
    exact (Subgroup.mem_center_iff.1 (Subgroup.mem_comap.1 hy) (z : Y ⧸ fusionOddCore Y)).symm
  have hπ : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      (a : Y ⧸ fusionOddCore Y) = b := fun a ha ha1 b hb hb1 =>
    mk_eq_of_commute_of_odd_orderOf_mul (elemAbelian_mul_self hA ha) (elemAbelian_mul_self hB hb)
      (hodd a ha ha1 b hb hb1) (hcomm a b)
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    obtain ⟨⟨a, ha⟩, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    exact ⟨a, ha, fun h => h1 (Subtype.ext h)⟩
  obtain ⟨b₀, hb₀, hb₀A⟩ : ∃ b ∈ B, b ∉ A := IsConcreteLE.not_le_iff_exists.1 hBA
  have hb₀1 : b₀ ≠ 1 := fun h => hb₀A (h ▸ A.one_mem)
  have hAeq : ∀ a ∈ A, a = 1 ∨ a = a₀ := by
    intro a ha
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    · refine Or.inr (eq_of_mk_eq_of_odd_card hA hOodd ha ha₀ ?_)
      rw [hπ a ha ha1 b₀ hb₀ hb₀1, hπ a₀ ha₀ ha₀1 b₀ hb₀ hb₀1]
  have hBeq : ∀ b ∈ B, b = 1 ∨ b = b₀ := by
    intro b hb
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    · refine Or.inr (eq_of_mk_eq_of_odd_card hB hOodd hb hb₀ ?_)
      rw [← hπ a₀ ha₀ ha₀1 b hb hb1, ← hπ a₀ ha₀ ha₀1 b₀ hb₀ hb₀1]
  have hgen : Subgroup.closure ({a₀, b₀} : Set Y) = ⊤ := by
    rw [eq_top_iff, ← hAB]
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rcases hAeq a ha with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
    · rcases hBeq b hb with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
  have hn : Odd (orderOf (a₀ * b₀)) := hodd a₀ ha₀ ha₀1 b₀ hb₀ hb₀1
  have hn1 : orderOf (a₀ * b₀) ≠ 1 := by
    intro h
    apply hb₀A
    rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h)]
    exact A.inv_mem ha₀
  refine ⟨orderOf (a₀ * b₀), hn, ?_, dihedral_mulEquiv_of_involutions hn
    (elemAbelian_mul_self hA ha₀) ha₀1 (elemAbelian_mul_self hB hb₀) rfl hgen⟩
  obtain ⟨k, hk⟩ := hn
  omega

theorem eq_bot_of_dihedral {Y : Type*} [Group Y] {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (e : DihedralGroup n ≃* Y) (K : Subgroup Y) [hK : K.Normal] (hK2 : IsPGroup 2 K) :
    K = ⊥ := by
  have h := dihedral_pCore_trivial hn h3 (K.comap e.toMonoidHom) (hK.comap _)
    (hK2.comap_of_injective _ e.injective)
  rw [Subgroup.eq_bot_iff_forall] at h ⊢
  intro y hy
  have h1 : e.symm y = 1 := h (e.symm y) (by simpa [Subgroup.mem_comap] using hy)
  calc y = e (e.symm y) := (e.apply_symm_apply y).symm
    _ = 1 := by rw [h1, map_one]

end Dihedral

section Quotient

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem Cfg.mk_not_mem_map_of_not_mem_normIn (c : Cfg T T₁) [(cfgM T T₁).Normal] {b : G}
    (hb : b ∈ T₁) (hbL : b ∉ normIn T₁ T) :
    QuotientGroup.mk' (cfgM T T₁) b ∉ T.map (QuotientGroup.mk' (cfgM T T₁)) := by
  rintro ⟨t, ht, hbt⟩
  obtain ⟨l, hl, y, hy, hly⟩ := c.mem_cfgM_iff.1 (QuotientGroup.eq.1 hbt)
  have e : b * y⁻¹ = t * l := by
    have : b = t * (l * y) := by rw [← hly]; group
    rw [this]; group
  have h1 : b * y⁻¹ ∈ T ⊓ T₁ :=
    ⟨e ▸ T.mul_mem ht (normIn_le _ _ hl), T₁.mul_mem hb (T₁.inv_mem (normIn_le _ _ hy))⟩
  rw [c.inf, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact hbL (h1 ▸ hy)

theorem Cfg.odd_orderOf_map_mul [Finite G] (c : Cfg T T₁) [(cfgM T T₁).Normal]
    (hX : T ⊔ T₁ = ⊤) (hconj : ∃ x : G, T₁ = conjSubgroup x T) {a b : G ⧸ cfgM T T₁}
    (ha : a ∈ T.map (QuotientGroup.mk' (cfgM T T₁))) (ha1 : a ≠ 1)
    (hb : b ∈ T₁.map (QuotientGroup.mk' (cfgM T T₁))) (hb1 : b ≠ 1) :
    Odd (orderOf (a * b)) := by
  obtain ⟨t, ht, rfl⟩ := ha
  obtain ⟨s, hs, rfl⟩ := hb
  have htL : t ∉ normIn T T₁ := fun h =>
    ha1 ((QuotientGroup.eq_one_iff t).2 (Cfg.normIn_le_cfgM_left T T₁ h))
  have hsL : s ∉ normIn T₁ T := fun h =>
    hb1 ((QuotientGroup.eq_one_iff s).2 (Cfg.normIn_le_cfgM_right T T₁ h))
  refine Odd.of_dvd_nat (c.odd_orderOf_mul hX hconj ht htL hs hsL) ?_
  rw [← map_mul]
  exact orderOf_map_dvd _ _

end Quotient

section Assembly

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem Cfg.quotient_cases (c : Cfg T T₁) [(cfgM T T₁).Normal] (hAsc : AschbacherNoPolarInput)
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) (hX : T ⊔ T₁ = ⊤)
    (hconj : ∃ x : G, T₁ = conjSubgroup x T) :
    (∀ K : Subgroup (G ⧸ cfgM T T₁), K.Normal → IsPGroup 2 K → K = ⊥) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ⧸ cfgM T T₁ ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (G ⧸ cfgM T T₁ ≃* Sz a)) ∨
        (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (G ⧸ cfgM T T₁ ≃* DihedralGroup n))) := by
  set f := QuotientGroup.mk' (cfgM T T₁)
  have hS : StrongWC (T.map f) := c.strongWC_map hX
  have hK : Subgroup.normalClosure ((T.map f : Subgroup (G ⧸ cfgM T T₁)) :
      Set (G ⧸ cfgM T T₁)) = ⊤ := c.normalClosure_map hX hconj
  have hT0 : T.map f ≠ ⊥ := c.map_ne_bot hconj
  obtain ⟨x, hx⟩ := hconj
  have hT₁ : T₁.map f = conjSubgroup (f x) (T.map f) := by
    have h := map_conjSubgroup f x T
    rwa [← hx] at h
  have hAB : T.map f ⊔ T₁.map f = ⊤ := by
    rw [← Subgroup.map_sup, hX, Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective _)]
  have hconj' : ∃ y : G, T = conjSubgroup y T₁ :=
    ⟨x⁻¹, by rw [hx, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]⟩
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (c.symm.normIn_lt hconj')
  have hbT : f b ∉ T.map f := c.mk_not_mem_map_of_not_mem_normIn hb hbL
  have hbT₁ : f b ∈ T₁.map f := ⟨b, hb, rfl⟩
  have hnT : ¬ ∀ g : G ⧸ cfgM T T₁, conjSubgroup g (T.map f) = T.map f := fun h =>
    hbT (by rw [← h (f x), ← hT₁]; exact hbT₁)
  have hg : T.map f ⊔ conjSubgroup (f x) (T.map f) = ⊤ := by rw [← hT₁]; exact hAB
  rcases lemma25_top hAsc hS hK with hZ | hB
  · obtain ⟨n, hn, h3, ⟨e⟩⟩ := exists_dihedral_of_zStar hS.1
      (hT₁ ▸ isElemAbelian_conjSubgroup hS.1 (f x)) hAB hZ hT0 (fun hle => hbT (hle hbT₁))
      fun a ha ha1 b hb hb1 => c.odd_orderOf_map_mul hX ⟨x, hx⟩ ha ha1 hb hb1
    exact ⟨fun K _ hK2 => eq_bot_of_dihedral hn h3 e K hK2, Or.inr (Or.inr ⟨n, hn, h3, ⟨e.symm⟩⟩)⟩
  · obtain ⟨hO2, hmod⟩ := models_of_isBenderGroup hCen hU hS hT0 hnT hK ⟨f x, hg⟩ hB
    exact ⟨hO2, hmod.imp id Or.inl⟩

end Assembly

theorem core214_of_inputs (hAsc : AschbacherNoPolarInput) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) : Core214 := by
  intro G _ _ T T₁ c hX hconj
  have hN : (cfgM T T₁).Normal := c.normal_cfgM hX
  obtain ⟨hO2, hcases⟩ := c.quotient_cases hAsc hCen hU hX hconj
  exact ⟨eq_pCore_two_of_forall_eq_bot _ (isPGroup_two_of_isElemAbelian c.isElemAbelian_cfgM) hO2,
    hN, hcases⟩

end CFSG.CGT.Timmesfeld75
