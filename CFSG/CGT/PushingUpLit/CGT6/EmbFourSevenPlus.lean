module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.G18Prop
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.ThompsonSchur
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.TwoSeven
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightNat
public import CFSG.RankThree.PartOne.KFCL.L4Block

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.SL2MinimalFaithful Matrix

theorem exists_complement_of_plusSection {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) {Y : Subgroup (MulAut V)}
    (hY : IsNatSectionBy (omegaPlusAct n) Y (commV Y) ⊥) :
    ∃ C : Subgroup V, (∀ y ∈ Y, ∀ c ∈ C, y c = c) ∧ C ⊓ commV Y = ⊥ ∧ C ⊔ commV Y = ⊤ := by
  classical
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hY
  let ρ : ↥Y →* MulAut V := Y.subtype
  have hAt' : ∀ g : ↥Y, ∀ a ∈ (⊥ : Subgroup V), ρ g a = a := fun g a ha => by
    rw [Subgroup.mem_bot.mp ha, map_one]
  have hVB' : ∀ (g : ↥Y) (v : V), ρ g v * v⁻¹ ∈ commV Y := fun g v =>
    Subgroup.subset_closure ⟨(g : MulAut V), g.2, v, rfl⟩
  have hB' : ∀ (g : ↥Y), ∀ b ∈ commV Y, ρ g b ∈ commV Y := fun g b hb => hinv g g.2 b hb
  have hcardF : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h2n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2n' : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hoddF : Odd (Nat.card (Fq n) - 1) := by
    rw [hcardF]
    have hpos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
    exact ⟨2 ^ (n - 1) - 1, by omega⟩
  obtain ⟨d, m, hm, hdm, hfpfL, hfpfR⟩ := exists_odd_fpf (Fq n) (by omega) hoddF
  have h4 : ∃ s : Finset (Fq n), s.card = 4 := by
    have : Fintype (Fq n) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fq n)))
      (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h2n)
    exact ⟨s, hs⟩
  have hperf := sl2_mult_trivial (Fq n) h4 (M := V)
  let e₁ : SpecialLinearGroup (Fin 2) (Fq n) →* ↥Y := θ.symm.toMonoidHom.comp (MonoidHom.inl _ _)
  let e₂ : SpecialLinearGroup (Fin 2) (Fq n) →* ↥Y := θ.symm.toMonoidHom.comp (MonoidHom.inr _ _)
  have hcomm12 : ∀ s t, e₁ s * e₂ t = e₂ t * e₁ s := by
    intro s t
    apply θ.injective
    simp [e₁, e₂]
  have hcomm21 : ∀ s t, e₂ s * e₁ t = e₁ t * e₂ s := fun s t => (hcomm12 t s).symm
  have hdec : ∀ g : ↥Y, ∃ s t, g = e₁ s * e₂ t := by
    intro g
    refine ⟨(θ g).1, (θ g).2, ?_⟩
    apply θ.injective
    simp [e₁, e₂]
  have hact : ∀ (x : ↥Y) (b : V) (hb : b ∈ commV Y), β ⟨ρ x b, hB' x b hb⟩ =
      omegaPlusAct n (θ x) (β ⟨b, hb⟩) := fun x b hb => hβe x ⟨b, hb⟩ _
  have hAmem : ∀ (b : V) (hb : b ∈ commV Y), β ⟨b, hb⟩ = 1 → b ∈ (⊥ : Subgroup V) := by
    intro b hb h1
    have : (⟨b, hb⟩ : ↥(commV Y)) ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at this
    exact this
  have hfix₁ : ∀ b ∈ commV Y, ρ (e₁ d) b = b → b ∈ (⊥ : Subgroup V) := by
    intro b hb hfix
    have h1 := hact (e₁ d) b hb
    have h2 : β ⟨ρ (e₁ d) b, hB' _ b hb⟩ = β ⟨b, hb⟩ := by
      congr 1; exact Subtype.ext hfix
    have hθ : θ (e₁ d) = (d, 1) := by simp [e₁]
    rw [h2, hθ] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    have h5 : (d : Matrix (Fin 2) (Fin 2) (Fq n)) * Multiplicative.toAdd (β ⟨b, hb⟩) =
        Multiplicative.toAdd (β ⟨b, hb⟩) := by simpa [omegaPlusAct] using h3.symm
    have h4 := hfpfL _ h5
    apply hAmem b hb
    apply Multiplicative.toAdd.injective
    simpa using h4
  have hfix₂ : ∀ b ∈ commV Y, ρ (e₂ d) b = b → b ∈ (⊥ : Subgroup V) := by
    intro b hb hfix
    have h1 := hact (e₂ d) b hb
    have h2 : β ⟨ρ (e₂ d) b, hB' _ b hb⟩ = β ⟨b, hb⟩ := by
      congr 1; exact Subtype.ext hfix
    have hθ : θ (e₂ d) = (1, d) := by simp [e₂]
    rw [h2, hθ] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    have h5 : Multiplicative.toAdd (β ⟨b, hb⟩) * (d : Matrix (Fin 2) (Fin 2) (Fq n)).transpose =
        Multiplicative.toAdd (β ⟨b, hb⟩) := by simpa [omegaPlusAct] using h3.symm
    have h4 := hfpfR _ h5
    apply hAmem b hb
    apply Multiplicative.toAdd.injective
    simpa using h4
  have hFin : ∀ K : Subgroup (MulAut V), Fintype ↥K := fun K => Fintype.ofFinite _
  obtain ⟨hodd1, hW1B, -, hBC1, hfix1, -, -⟩ := half_split hV ρ ⊥ (commV Y) hAt' hVB' e₁ e₂
    hcomm12 d hm hdm hfix₁ hperf (Subgroup.zpowers (ρ (e₁ d))) rfl
  obtain ⟨hodd2, -, -, -, hfix2, -, -⟩ := half_split hV ρ ⊥ (commV Y) hAt' hVB' e₂ e₁
    hcomm21 d hm hdm hfix₂ hperf (Subgroup.zpowers (ρ (e₂ d))) rfl
  let K₁ : Subgroup (MulAut V) := Subgroup.zpowers (ρ (e₁ d))
  let K₂ : Subgroup (MulAut V) := Subgroup.zpowers (ρ (e₂ d))
  have hK₂ : ∀ k ∈ K₂, ∃ t, k = ρ (e₂ t) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨d ^ j, by rw [map_zpow, map_zpow]⟩
  have hK₁ : ∀ k ∈ K₁, ∃ t, k = ρ (e₁ t) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨d ^ j, by rw [map_zpow, map_zpow]⟩
  have hCC : fixV K₁ ≤ fixV K₂ := by
    intro c hc k hk
    obtain ⟨t, rfl⟩ := hK₂ k hk
    exact hfix1 t c hc
  have hCC' : fixV K₂ ≤ fixV K₁ := by
    intro c hc k hk
    obtain ⟨t, rfl⟩ := hK₁ k hk
    exact hfix2 t c hc
  have hCeq : fixV K₂ = fixV K₁ := le_antisymm hCC' hCC
  have hCinv : ∀ g ∈ Y, ∀ c ∈ fixV K₁, g c = c := by
    intro g hg c hc
    obtain ⟨s, t, hst⟩ := hdec ⟨g, hg⟩
    have h1 : ρ ⟨g, hg⟩ c = ρ (e₁ s * e₂ t) c := by rw [← hst]
    rw [map_mul] at h1
    have h2 : (g : MulAut V) c = ρ (e₁ s) (ρ (e₂ t) c) := h1
    rw [h2, hfix1 t c hc]
    exact hfix2 s c (hCeq ▸ hc)
  have hsup : (normK K₁).ker ⊔ fixV K₁ = ⊤ := normK_ker_sup_fixV K₁ hodd1 hV
  refine ⟨fixV K₁, hCinv, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro b ⟨hbC, hbB⟩
    exact hBC1 b hbB hbC
  · rw [eq_top_iff, ← hsup]
    exact sup_le (hW1B.trans le_sup_right) le_sup_left

section Factor

@[expose] def rowZero (n : ℕ) : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))) where
  carrier := {m | ∀ j, (Multiplicative.toAdd m) 1 j = 0}
  one_mem' := fun j => by simp
  mul_mem' := fun {a b} ha hb j => by
    show ((Multiplicative.toAdd a) + (Multiplicative.toAdd b)) 1 j = 0
    simp [ha j, hb j]
  inv_mem' := fun {a} ha j => by
    show (-(Multiplicative.toAdd a)) 1 j = 0
    simp [ha j]

theorem mem_rowZero {n : ℕ} {m : Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))} :
    m ∈ rowZero n ↔ ∀ j, (Multiplicative.toAdd m) 1 j = 0 := Iff.rfl

variable {n : ℕ}

theorem unipotent_mul_apply_zero (x : Fq n) (M : Matrix (Fin 2) (Fin 2) (Fq n)) (j : Fin 2) :
    ((unipotent x : SpecialLinearGroup (Fin 2) (Fq n)) * M : Matrix (Fin 2) (Fin 2) (Fq n)) 0 j =
      M 0 j + x * M 1 j := by
  simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mul_apply_one (x : Fq n) (M : Matrix (Fin 2) (Fin 2) (Fq n)) (j : Fin 2) :
    ((unipotent x : SpecialLinearGroup (Fin 2) (Fq n)) * M : Matrix (Fin 2) (Fin 2) (Fq n)) 1 j =
      M 1 j := by
  simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mul_sub_mem (x : Fq n) (M : Matrix (Fin 2) (Fin 2) (Fq n)) :
    Multiplicative.ofAdd ((unipotent x : SpecialLinearGroup (Fin 2) (Fq n)) * M - M) ∈
      rowZero n := fun j => by
  simp [unipotent_mul_apply_one]

theorem unipotent_mul_eq_of_rowZero (x : Fq n) {M : Matrix (Fin 2) (Fin 2) (Fq n)}
    (hM : ∀ j, M 1 j = 0) :
    ((unipotent x : SpecialLinearGroup (Fin 2) (Fq n)) * M :
      Matrix (Fin 2) (Fin 2) (Fq n)) = M := by
  ext i j
  fin_cases i
  · simp [unipotent_mul_apply_zero, hM j]
  · simp [unipotent_mul_apply_one]

theorem exists_unipotent_mul_sub_eq {x : Fq n} (hx : x ≠ 0) {M : Matrix (Fin 2) (Fin 2) (Fq n)}
    (hM : ∀ j, M 1 j = 0) :
    ∃ M' : Matrix (Fin 2) (Fin 2) (Fq n),
      (unipotent x : SpecialLinearGroup (Fin 2) (Fq n)) * M' - M' = M := by
  refine ⟨Matrix.of ![0, fun j => x⁻¹ * M 0 j], ?_⟩
  ext i j
  fin_cases i
  · simp [unipotent_mul_apply_zero, hx]
  · simp [unipotent_mul_apply_one, hM j]

end Factor

section FirstFactor

variable {V : Type} [CommGroup V] [Finite V]

theorem plus_first_factor_centralizes (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {Y : Subgroup (MulAut V)} (hinv : ∀ y ∈ Y, ∀ p ∈ commV Y, y p ∈ commV Y)
    {C : Subgroup V} (hCfix : ∀ y ∈ Y, ∀ c ∈ C, y c = c) (hCsup : C ⊔ commV Y = ⊤)
    (θ : ↥Y ≃* SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n))
    (φ : ↥(commV Y) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)))
    (hφ : ∀ (g : ↥Y) (x : ↥(commV Y)) (hp : (g : MulAut V) x ∈ commV Y),
      φ ⟨(g : MulAut V) x, hp⟩ = omegaPlusAct n (θ g) (φ x))
    {X : Subgroup (MulAut V)} (hX : ¬ 2 ∣ Nat.card X)
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    ∀ x : Fq n, ∀ ξ ∈ X, ((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) * ξ =
      ξ * ((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) := by
  let ιh : SpecialLinearGroup (Fin 2) (Fq n) →* MulAut V :=
    Y.subtype.comp (θ.symm.toMonoidHom.comp (MonoidHom.inl _ _))
  have hι_inj : Function.Injective ιh := fun A B h => by
    have h1 : θ.symm (A, 1) = θ.symm (B, 1) := Subtype.ext h
    exact congrArg Prod.fst (θ.symm.injective h1)
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (MulAut V),
      E = (unipotentHom (F := Fq n)).range.map ιh := ⟨_, rfl⟩
  have hEmem : ∀ e, e ∈ E ↔ ∃ x : Fq n, ιh (unipotent x) = e := fun e => by
    rw [hE, Subgroup.mem_map]
    constructor
    · rintro ⟨A, ⟨t, rfl⟩, rfl⟩
      exact ⟨t.toAdd, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨unipotent x, ⟨Multiplicative.ofAdd x, rfl⟩, rfl⟩
  have hEY : E ≤ Y := by
    intro e he
    obtain ⟨x, rfl⟩ := (hEmem e).mp he
    exact (θ.symm (unipotent x, 1)).2
  have hEab : IsElemAbelian2 E := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      obtain ⟨x, rfl⟩ := (hEmem a).mp ha
      obtain ⟨y, rfl⟩ := (hEmem b).mp hb
      rw [← map_mul, ← map_mul, ← unipotent_add, ← unipotent_add, add_comm]
    · intro a ha
      obtain ⟨x, rfl⟩ := (hEmem a).mp ha
      rw [← map_pow, sq, ← unipotent_add, CharTwo.add_self_eq_zero, unipotent_zero, map_one]
  have hE4 : 4 ≤ Nat.card E := by
    have hcard : Nat.card E = 2 ^ n := by
      rw [hE, Subgroup.card_map_of_injective hι_inj,
        ← GaloisField.card 2 n (by omega)]
      exact (Nat.card_congr
        (MonoidHom.ofInjective (unipotentHom_injective (F := Fq n))).toEquiv).symm
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨W, hW⟩ : ∃ W : Subgroup V,
      W = ((rowZero n).comap φ.toMonoidHom).map (commV Y).subtype := ⟨_, rfl⟩
  have hWmem : ∀ w, w ∈ W ↔ ∃ t : ↥(commV Y), φ t ∈ rowZero n ∧ (t : V) = w := fun w => by
    rw [hW]; exact Subgroup.mem_map
  have hact : ∀ (x : Fq n) (u : ↥(commV Y))
      (hp : ((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) u ∈ commV Y),
      φ ⟨((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) u, hp⟩ =
        Multiplicative.ofAdd ((unipotent x : Matrix (Fin 2) (Fin 2) (Fq n)) *
          Multiplicative.toAdd (φ u)) := by
    intro x u hp
    rw [hφ (θ.symm (unipotent x, 1)) u hp, MulEquiv.apply_symm_apply]
    simp [omegaPlusAct]
  have hE_mem : ∀ e ∈ E, ∃ x : Fq n, e = ((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) := by
    intro e he
    obtain ⟨x, rfl⟩ := (hEmem e).mp he
    exact ⟨x, rfl⟩
  have hdecomp : ∀ v : V, ∃ (c : V) (u : ↥(commV Y)), c ∈ C ∧ v = c * u := by
    intro v
    have hv : v ∈ C ⊔ commV Y := by rw [hCsup]; exact Subgroup.mem_top v
    obtain ⟨c, hc, u, hu, h⟩ := Subgroup.mem_sup.mp hv
    exact ⟨c, ⟨u, hu⟩, hc, h.symm⟩
  have hW1 : ∀ e ∈ E, ∀ v : V, e v * v⁻¹ ∈ W := by
    intro e he v
    obtain ⟨x, rfl⟩ := hE_mem e he
    obtain ⟨c, u, hc, rfl⟩ := hdecomp v
    have hcfix : ((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) c = c :=
      hCfix _ (θ.symm (unipotent x, 1)).2 c hc
    have hp : ((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) u ∈ commV Y :=
      hinv _ (θ.symm (unipotent x, 1)).2 u u.2
    rw [aut_mul_mul_inv', hcfix, mul_inv_cancel, one_mul]
    have hφt : φ (⟨((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) u, hp⟩ * (u : ↥(commV Y))⁻¹) =
        Multiplicative.ofAdd ((unipotent x : Matrix (Fin 2) (Fin 2) (Fq n)) *
          Multiplicative.toAdd (φ u) - Multiplicative.toAdd (φ u)) := by
      rw [map_mul, map_inv, hact x u hp]
      apply Multiplicative.toAdd.injective
      simp [sub_eq_add_neg]
    exact (hWmem _).mpr ⟨_, by
      rw [hφt]
      exact unipotent_mul_sub_mem x _, rfl⟩
  have hW2 : ∀ e ∈ E, ∀ w ∈ W, e w = w := by
    intro e he w hw
    obtain ⟨x, rfl⟩ := hE_mem e he
    obtain ⟨t, ht, rfl⟩ := (hWmem w).mp hw
    have hp : ((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) t ∈ commV Y :=
      hinv _ (θ.symm (unipotent x, 1)).2 t t.2
    have h1 : φ ⟨((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) t, hp⟩ = φ t := by
      rw [hact x t hp, unipotent_mul_eq_of_rowZero x (mem_rowZero.mp ht)]
      simp
    exact congrArg Subtype.val (φ.injective h1)
  have hW3 : ∀ e ∈ E, e ≠ 1 → ∀ w ∈ W, ∃ v : V, w = e v * v⁻¹ := by
    intro e he he1 w hw
    obtain ⟨x, rfl⟩ := hE_mem e he
    obtain ⟨t, ht, rfl⟩ := (hWmem w).mp hw
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact he1 (by simp [unipotent_zero])
    obtain ⟨M', hM'⟩ := exists_unipotent_mul_sub_eq hx0 (mem_rowZero.mp ht)
    obtain ⟨u, hu⟩ := φ.surjective (Multiplicative.ofAdd M')
    have hp : ((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) u ∈ commV Y :=
      hinv _ (θ.symm (unipotent x, 1)).2 u u.2
    refine ⟨(u : V), ?_⟩
    have h1 : φ (⟨((θ.symm (unipotent x, 1) : ↥Y) : MulAut V) u, hp⟩ * (u : ↥(commV Y))⁻¹) =
        φ t := by
      rw [map_mul, map_inv, hact x u hp, hu]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
      rw [← sub_eq_add_neg]
      exact hM'
    exact (congrArg Subtype.val (φ.injective h1)).symm
  have hEc : X ≤ Subgroup.centralizer (E : Set (MulAut V)) :=
    le_centralizer_of_commonImage hV hEab hE4 hW1 hW2 hW3 hX (hEY.trans hYX)
  intro x ξ hξ
  exact Subgroup.mem_centralizer_iff.mp (hEc hξ) _ ((hEmem _).mpr ⟨x, rfl⟩)

end FirstFactor

section Plus

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem plus_equivariant_swap {n : ℕ} {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n))
    (φ : ↥(commV Y) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)))
    (hφ : ∀ (g : ↥Y) (x : ↥(commV Y)) (hp : (g : MulAut V) x ∈ commV Y),
      φ ⟨(g : MulAut V) x, hp⟩ = omegaPlusAct n (θ g) (φ x)) (g : ↥Y) (x : ↥(commV Y))
    (hp : (g : MulAut V) x ∈ commV Y) :
    (φ.trans (AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin 2) (Fin 2) (Fq n))))
        ⟨(g : MulAut V) x, hp⟩ =
      omegaPlusAct n ((θ.trans MulEquiv.prodComm) g)
        ((φ.trans
          (AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin 2) (Fin 2) (Fq n)))) x) := by
  show Multiplicative.ofAdd (Multiplicative.toAdd (φ ⟨(g : MulAut V) x, hp⟩))ᵀ = _
  rw [hφ g x hp]
  simp [omegaPlusAct, Matrix.transpose_mul, mul_assoc]

theorem omegaPlus_oddInvariant_le_centralizer (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {Y : Subgroup (MulAut V)} (hY : IsNatSectionBy (omegaPlusAct n) Y (commV Y) ⊥)
    {X : Subgroup (MulAut V)} (hX : ¬ 2 ∣ Nat.card X)
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
  obtain ⟨C, hCfix, -, hCsup⟩ := exists_complement_of_plusSection hV hn hY
  obtain ⟨hinv, θ, φ, hφ⟩ := TwoEight.natSection_equiv hY
  have h1 := plus_first_factor_centralizes hV hn hinv hCfix hCsup θ φ hφ hX hYX
  have h2 := plus_first_factor_centralizes hV hn hinv hCfix hCsup (θ.trans MulEquiv.prodComm)
    (φ.trans (AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin 2) (Fin 2) (Fq n))))
    (plus_equivariant_swap θ φ hφ) hX hYX
  have h4 : 4 ≤ Nat.card (Fq n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup (SpecialLinearGroup (Fin 2) (Fq n)) :=
    CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := Fq n) h4
  have h10 : unipotent (1 : Fq n) ≠ 1 := fun h =>
    one_ne_zero (unipotent_injective (h.trans unipotent_zero.symm))
  have := centKer_normal hYX
  exact le_centralizer_of_centKer_eq_top (normal_eq_top_of_prod θ (centKer Y X) h10
    (fun ξ hξ => h1 1 ξ hξ) h10 (fun ξ hξ => h2 1 ξ hξ))

end Plus

end CFSG.CGT.PushingUpLit.CGT6
