module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockTransferIso
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightOfData
public import CFSG.HardMathSupport.Cooperstein.Proving.TwoCoreInf
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm Subgroup

abbrev DE : Type := Fin 2 × Bool

@[expose] def embD (s : ℕ) : Perm DE →* Perm (OmegaE 2 s) :=
  (Perm.sumCongrHom DE (Fin s)).comp (MonoidHom.inl _ _)

theorem embD_apply (s : ℕ) (a : Perm DE) : embD s a = Perm.sumCongr a 1 := rfl

theorem embD_injective (s : ℕ) : Function.Injective (embD s) :=
  Perm.sumCongrHom_injective.comp (fun _ _ h => congrArg Prod.fst h)

theorem sign_embD (s : ℕ) (a : Perm DE) : sign (embD s a) = sign a := by
  rw [embD_apply, sign_sumCongr]; simp

@[expose] def TP (s : ℕ) : Subgroup (Perm (OmegaE 2 s)) := (alternatingGroup DE).map (embD s)

theorem TP_le_alt (s : ℕ) : TP s ≤ alternatingGroup (OmegaE 2 s) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_alternatingGroup, sign_embD]; exact ha

@[expose] def TA (s : ℕ) : Subgroup (AltE 2 s) := (TP s).subgroupOf (alternatingGroup (OmegaE 2 s))

@[expose] noncomputable def eA (s : ℕ) : ↥(TA s) ≃* alternatingGroup DE :=
  (Subgroup.subgroupOfEquivOfLe (TP_le_alt s)).trans
    (Subgroup.equivMapOfInjective (alternatingGroup DE) (embD s) (embD_injective s)).symm

set_option maxRecDepth 100000 in
theorem perm4_three_witness : ∀ c : Perm (Fin 4), c ≠ 1 → c ^ 3 = 1 →
    ∃ g : Perm (Fin 4), sign g = 1 ∧ (c * (g * c * g⁻¹)⁻¹) ^ 2 = 1 ∧ c * (g * c * g⁻¹)⁻¹ ≠ 1 := by
  decide

theorem a4_solvable : Group.IsSolvable (alternatingGroup (Fin 4)) :=
  ⟨⟨2, by
    change ⁅commutator (alternatingGroup (Fin 4)), commutator (alternatingGroup (Fin 4))⁆ = ⊥
    rw [← alternatingGroup.kleinFour_eq_commutator (by simp)]
    exact Subgroup.commutator_self_eq_bot_iff.mpr
      (alternatingGroup.kleinFour_isKleinFour (by simp)).isMulCommutative⟩⟩

theorem exists_order_three {H : Type*} [Group H] {r : H} (hr : r ≠ 1)
    (h3 : ∃ m : ℕ, r ^ (3 ^ m) = 1) : ∃ j : ℕ, (r ^ (3 ^ j)) ^ 3 = 1 ∧ r ^ (3 ^ j) ≠ 1 := by
  obtain ⟨m, hm⟩ := h3
  have hdvd : orderOf r ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hk'
    exact hr (orderOf_eq_one_iff.1 hk')
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨j, ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ]
    rw [← hk']; exact pow_orderOf_eq_one r
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hk'] at this
    have := Nat.le_of_dvd (by positivity) this
    have h2 : 3 ^ j < 3 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem a4_noNormalThree (R : Subgroup (alternatingGroup (Fin 4)))
    (hn : ∀ b : alternatingGroup (Fin 4), ∀ r ∈ R, b * r * b⁻¹ ∈ R)
    (h3 : ∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) : R = ⊥ := by
  by_contra hne
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  obtain ⟨j, hc3, hc1⟩ := exists_order_three hr1' (h3 r hr)
  set c : alternatingGroup (Fin 4) := r ^ (3 ^ j) with hc
  have hcR : c ∈ R := R.pow_mem hr _
  obtain ⟨g, hg, h2, h1⟩ := perm4_three_witness c.1 (fun h => hc1 (Subtype.ext (by simpa using h)))
    (by simpa using congrArg Subtype.val hc3)
  let g' : alternatingGroup (Fin 4) := ⟨g, by rw [mem_alternatingGroup]; exact hg⟩
  have hx : c * (g' * c * g'⁻¹)⁻¹ ∈ R :=
    R.mul_mem hcR (R.inv_mem (hn g' c hcR))
  obtain ⟨m, hm⟩ := h3 _ hx
  have hx2 : (c * (g' * c * g'⁻¹)⁻¹) ^ 2 = 1 := Subtype.ext (by simpa using h2)
  have hxne : c * (g' * c * g'⁻¹)⁻¹ ≠ 1 := fun h => h1 (by simpa using congrArg Subtype.val h)
  have hodd : (c * (g' * c * g'⁻¹)⁻¹) ^ (3 ^ m) = c * (g' * c * g'⁻¹)⁻¹ := by
    have hmod : 3 ^ m % 2 = 1 := by rw [Nat.pow_mod]; simp
    have hpos : 0 < 3 ^ m := by positivity
    obtain ⟨t, ht⟩ : ∃ t, 3 ^ m = 2 * t + 1 := ⟨(3 ^ m - 1) / 2, by omega⟩
    rw [ht, pow_succ, pow_mul, hx2, one_pow, one_mul]
  exact hxne (hodd ▸ hm)

theorem card_DE : Fintype.card DE = 4 := by simp [Fintype.card_prod]

theorem alt_DE_solvable : Group.IsSolvable (alternatingGroup DE) := by
  have e4 : DE ≃ Fin 4 := Fintype.equivFinOfCardEq card_DE
  have := a4_solvable
  exact Group.isSolvable_of_isSolvable_injective (f := (Equiv.altCongrHom e4).toMonoidHom)
    (Equiv.altCongrHom e4).injective

theorem solvable_TA (s : ℕ) : Group.IsSolvable ↥(TA s) := by
  have := alt_DE_solvable
  exact Group.isSolvable_of_isSolvable_injective (f := (eA s).toMonoidHom) (eA s).injective

theorem noNormalThree_of_altDE {K : Type*} [Group K] (e : K ≃* alternatingGroup DE)
    (R : Subgroup K) (hn : ∀ b : K, ∀ r ∈ R, b * r * b⁻¹ ∈ R)
    (h3 : ∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) : R = ⊥ := by
  have e4 : DE ≃ Fin 4 := Fintype.equivFinOfCardEq card_DE
  let f : K ≃* alternatingGroup (Fin 4) := e.trans (Equiv.altCongrHom e4)
  have h := a4_noNormalThree (R.map f.toMonoidHom) (by
    rintro b _ ⟨r, hr, rfl⟩
    exact ⟨f.symm b * r * (f.symm b)⁻¹, hn _ r hr, by simp⟩) (by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨m, hm⟩ := h3 r hr
    exact ⟨m, by rw [← map_pow]; simp [hm]⟩)
  rw [eq_bot_iff]
  intro r hr
  have : f r ∈ R.map f.toMonoidHom := ⟨r, hr, rfl⟩
  rw [h] at this
  have h1 : f r = 1 := Subgroup.mem_bot.1 this
  have : r = 1 := f.injective (by rw [h1, map_one])
  rw [this]; exact Subgroup.one_mem _

theorem hT3_of_equiv {M : Type*} [Group M] {T : Subgroup M} (e : ↥T ≃* alternatingGroup DE) :
    ∀ R : Subgroup M, R ≤ T → (∀ b ∈ T, ∀ r ∈ R, b * r * b⁻¹ ∈ R) →
      (∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) → R = ⊥ := by
  intro R hRT hn h3
  have h := noNormalThree_of_altDE e (R.subgroupOf T) (fun b r hr => hn b b.2 r hr) (by
    intro r hr
    obtain ⟨m, hm⟩ := h3 r hr
    exact ⟨m, Subtype.ext (by simpa using hm)⟩)
  rw [eq_bot_iff]
  intro r hr
  have : (⟨r, hRT hr⟩ : ↥T) ∈ R.subgroupOf T := hr
  rw [h] at this
  have h1 : (⟨r, hRT hr⟩ : ↥T) = 1 := Subgroup.mem_bot.1 this
  have : r = 1 := congrArg Subtype.val h1
  rw [this]; exact Subgroup.one_mem _

theorem conj_mem_TP (s : ℕ) (σ₁ : Perm DE) (σ₂ : Perm (Fin s)) {x : Perm (OmegaE 2 s)}
    (hx : x ∈ TP s) : Perm.sumCongr σ₁ σ₂ * x * (Perm.sumCongr σ₁ σ₂)⁻¹ ∈ TP s := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨σ₁ * a * σ₁⁻¹, ?_, ?_⟩
  · have ha' : sign a = 1 := mem_alternatingGroup.1 ha
    show σ₁ * a * σ₁⁻¹ ∈ alternatingGroup DE
    rw [mem_alternatingGroup]
    simp [map_mul, map_inv, ha']
  · rw [embD_apply, embD_apply, Perm.sumCongr_inv, Perm.sumCongr_mul, Perm.sumCongr_mul]
    simp

@[expose] def VK : Subgroup (Perm DE) := (alternatingGroup.kleinFour DE).map (alternatingGroup DE).subtype

theorem VK_eq_closure : VK = Subgroup.closure
    {σ : Perm DE | σ ∈ alternatingGroup DE ∧ σ.cycleType = {2, 2}} := by
  unfold VK alternatingGroup.kleinFour
  rw [MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨σ, h1⟩, h2, rfl⟩

theorem VK_le_alt : VK ≤ alternatingGroup DE := by
  rintro _ ⟨g, -, rfl⟩; exact g.2

theorem VK_conj (g : Perm DE) {x : Perm DE} (hx : x ∈ VK) : g * x * g⁻¹ ∈ VK := by
  rw [VK_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hy1, hy2⟩ := hy
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · have := mem_alternatingGroup.1 hy1
      rw [mem_alternatingGroup]
      simp [map_mul, map_inv, this]
    · rw [Equiv.Perm.cycleType_conj]
      exact hy2
  | one => simp
  | mul y z _ _ hy hz =>
    have := Subgroup.mul_mem _ hy hz
    simpa [mul_assoc] using this
  | inv y _ hy =>
    have := Subgroup.inv_mem _ hy
    convert this using 1
    group

theorem VK_sq (x : Perm DE) (hx : x ∈ VK) : x ^ 2 = 1 := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hK := alternatingGroup.kleinFour_isKleinFour (α := DE) (by rw [Nat.card_eq_fintype_card]; exact card_DE)
  have h2 := hK.exponent_two
  have : (⟨g, hg⟩ : ↥(alternatingGroup.kleinFour DE)) ^ 2 = 1 := by
    have h3 := Monoid.pow_exponent_eq_one (⟨g, hg⟩ : ↥(alternatingGroup.kleinFour DE))
    rwa [h2] at h3
  have := congrArg (fun y : ↥(alternatingGroup.kleinFour DE) => ((y : alternatingGroup DE) : Perm DE)) this
  simpa using this

theorem card_VK : Nat.card VK = 4 := by
  have hK := alternatingGroup.kleinFour_isKleinFour (α := DE) (by rw [Nat.card_eq_fintype_card]; exact card_DE)
  have : Nat.card VK = Nat.card (alternatingGroup.kleinFour DE) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (alternatingGroup DE).subtype_injective).symm.toEquiv)
  rw [this]; exact hK.card_four

set_option maxRecDepth 100000 in
theorem even_sq_mem_wStab' : ∀ σ : Perm DE, sign σ = 1 → σ ^ 2 = 1 →
    ∀ x y : DE, (σ x).1 = (σ y).1 ↔ x.1 = y.1 := by
  decide

theorem VK_le_wStab : VK ≤ wStab (Fin 2) Bool := fun x hx =>
  mem_wStab.2 (even_sq_mem_wStab' x (mem_alternatingGroup.1 (VK_le_alt hx)) (VK_sq x hx))

@[expose] def VP (s : ℕ) : Subgroup (Perm (OmegaE 2 s)) := VK.map (embD s)

theorem VP_le_TP (s : ℕ) : VP s ≤ TP s := Subgroup.map_mono (VK_le_alt)

@[expose] def VA (s : ℕ) : Subgroup (AltE 2 s) :=
  (VP s).subgroupOf (alternatingGroup (OmegaE 2 s))

theorem VA_le_TA (s : ℕ) : VA s ≤ TA s := fun _ h => VP_le_TP s h

theorem VA_isPGroup (s : ℕ) : IsPGroup 2 (VA s) := by
  intro v
  refine ⟨1, ?_⟩
  obtain ⟨a, ha, hav⟩ := v.2
  have hv : ((v : AltE 2 s) : Perm (OmegaE 2 s)) = embD s a := hav.symm
  apply Subtype.ext; apply Subtype.ext
  have h2 : (embD s a) ^ 2 = 1 := by rw [← map_pow, VK_sq a ha, map_one]
  have h3 : (((v ^ 2 ^ 1 : ↥(VA s)) : AltE 2 s) : Perm (OmegaE 2 s)) =
      (((v : AltE 2 s) : Perm (OmegaE 2 s))) ^ 2 := by simp
  show (((v ^ 2 ^ 1 : ↥(VA s)) : AltE 2 s) : Perm (OmegaE 2 s)) = 1
  rw [h3, hv, h2]

theorem card_VA (s : ℕ) : Nat.card (VA s) = 4 := by
  have h1 : Nat.card (VA s) = Nat.card (VP s) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := hx
      rw [mem_alternatingGroup, sign_embD]; exact VK_le_alt ha)).toEquiv
  have h2 : Nat.card (VP s) = Nat.card VK :=
    (Nat.card_congr (Subgroup.equivMapOfInjective VK (embD s) (embD_injective s)).symm.toEquiv)
  rw [h1, h2, card_VK]

theorem card_TA (s : ℕ) : Nat.card (TA s) = 12 := by
  have h := alternatingGroup.card_of_card_eq_four (α := DE) (by rw [Nat.card_eq_fintype_card]; exact card_DE)
  rw [Nat.card_congr (eA s).toEquiv, h]

theorem VP_conj (s : ℕ) (σ₁ : Perm DE) (σ₂ : Perm (Fin s)) {x : Perm (OmegaE 2 s)} (hx : x ∈ VP s) :
    Perm.sumCongr σ₁ σ₂ * x * (Perm.sumCongr σ₁ σ₂)⁻¹ ∈ VP s := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨σ₁ * a * σ₁⁻¹, VK_conj σ₁ ha, ?_⟩
  rw [embD_apply, embD_apply, Perm.sumCongr_inv, Perm.sumCongr_mul, Perm.sumCongr_mul]
  simp

theorem VA_le_eightN (s : ℕ) : VA s ≤ eightN 2 s := by
  intro v hv
  obtain ⟨a, ha, hav⟩ := hv
  refine ⟨(a, 1), ⟨VK_le_wStab ha, ?_⟩, ?_⟩
  · have := mem_alternatingGroup.1 (VK_le_alt ha)
    simp [this]
  · rw [Perm.sumCongrHom_apply, ← hav, embD_apply]

theorem exists_TA_not_eightN (s : ℕ) : ∃ t ∈ TA s, t ∉ eightN 2 s := by
  set d0 : DE := (0, false)
  set d1 : DE := (0, true)
  set d2 : DE := (1, false)
  set c : Perm DE := swap d0 d1 * swap d1 d2 with hc
  have hcalt : c ∈ alternatingGroup DE := by
    rw [mem_alternatingGroup, hc, map_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  have hcw : c ∉ wStab (Fin 2) Bool := by
    intro h
    have := (mem_wStab.1 h) d0 d1
    revert this
    simp [hc, d0, d1, d2, swap_apply_def]
  refine ⟨⟨embD s c, ?_⟩, ?_, ?_⟩
  · rw [mem_alternatingGroup, sign_embD]; exact mem_alternatingGroup.1 hcalt
  · exact ⟨c, hcalt, rfl⟩
  · rintro ⟨⟨a, b⟩, hp, hab⟩
    have h1 : Perm.sumCongrHom DE (Fin s) (a, b) = Perm.sumCongrHom DE (Fin s) (c, 1) :=
      hab.trans rfl
    have := Perm.sumCongrHom_injective h1
    exact hcw ((Prod.mk.inj this).1 ▸ hp.1)

open CFSG.AGLEmbedding (Asc81bHyp IsTwoPrimeComponent barM IsWeakSBlock)

variable {G : Type} [Group G]

@[expose] def TT {X L : Subgroup G} (s : ℕ) (ψ : ↥(barM X L) ≃* AltE 2 s) : Subgroup ↥(barM X L) :=
  (TA s).comap ψ.toMonoidHom

@[expose] noncomputable def ttEquiv {X L : Subgroup G} (s : ℕ) (ψ : ↥(barM X L) ≃* AltE 2 s) :
    ↥(TT s ψ) ≃* ↥(TA s) :=
  (ψ.subgroupMap (TT s ψ)).trans (MulEquiv.subgroupCongr
    (Subgroup.map_comap_eq_self_of_surjective ψ.surjective _))

theorem index_VA_TA (s : ℕ) : (((VA s).subgroupOf (TA s))).index = 3 := by
  have h := Subgroup.card_mul_index ((VA s).subgroupOf (TA s))
  have h1 : Nat.card (((VA s).subgroupOf (TA s))) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (VA_le_TA s)).toEquiv, card_VA]
  rw [h1, card_TA] at h
  omega

theorem eightTwo_false [Finite G] {X S L : Subgroup G} {s : ℕ} (hA : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hLB : SolvableSylowNormalizer X S) (D : EightBlockData X S L 2 s) : False := by
  obtain ⟨ψ, hψN, hact⟩ := D
  set T := TT s ψ with hT
  set eT := ttEquiv s ψ with heT
  have hmemT : ∀ l : ↥(barM X L), l ∈ T ↔ ψ l ∈ TA s := fun l => Iff.rfl
  have hNL : barM X (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM X L := barM_mono inf_le_right
  have hSbar : ∀ y ∈ barM X S, y ∈ barM X (Subgroup.normalizer (S : Set G) ⊓
      Subgroup.normalizer (L : Set G)) := by
    intro y hy
    obtain ⟨x, hxX, hxS, rfl⟩ := mem_barM_iff.1 hy
    exact mem_barM_iff.2 ⟨x, hxX, ⟨Subgroup.le_normalizer hxS, hSL hxS⟩, rfl⟩
  have hnorm : ∀ y ∈ barM X S, ∀ l l' : ↥(barM X L),
      (l' : ↥X ⧸ CFSG.pCore 2 ↥X) = y * l * y⁻¹ → l ∈ T → l' ∈ T := by
    intro y hy l l' hll' hl
    obtain ⟨σ₁, -, σ₂, hσ⟩ := hact y (hSbar y hy)
    have h1 := hσ l l' hll'
    have h2 : ((ψ l' : AltE 2 s) : Perm (OmegaE 2 s)) ∈ TP s := by
      rw [h1]; exact conj_mem_TP s σ₁ σ₂ hl
    exact h2
  have hsolv : Group.IsSolvable ↥T := by
    have := solvable_TA s
    exact Group.isSolvable_of_isSolvable_injective (f := eT.toMonoidHom) eT.injective
  have hodd : ¬ 2 ∣ (((barM X (S ⊓ L)).subgroupOf (barM X L)).subgroupOf T).index := by
    set VT : Subgroup ↥(barM X L) := (VA s).comap ψ.toMonoidHom with hVT
    have hVT_T : VT ≤ T := fun v hv => VA_le_TA s hv
    have hpc := Proving.barM_inf_eq_pCoreOf_barM hA hL
    have hVT_P : VT ≤ (barM X (S ⊓ L)).subgroupOf (barM X L) := by
      intro v hv
      show (v : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ barM X (S ⊓ L)
      rw [hpc]
      have hApG : IsPGroup 2 (VT.map (barM X L).subtype) :=
        ((VA_isPGroup s).comap_of_injective ψ.toMonoidHom ψ.injective).map _
      have hVN : ∀ v' ∈ VT, v' ∈ ((barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
          (barM X L)) := by
        intro v' hv'
        have h1 : ψ v' ∈ eightN 2 s := VA_le_eightN s hv'
        rw [← hψN] at h1
        obtain ⟨n, hn, hnv⟩ := h1
        have : n = v' := ψ.injective hnv
        rw [← this]; exact hn
      refine le_pCoreOf_of_normalized (A := VT.map (barM X L).subtype) ?_ ?_ hApG ⟨v, hv, rfl⟩
      · rintro _ ⟨v', hv', rfl⟩
        exact hVN v' hv'
      · rintro k hk _ ⟨v', hv', rfl⟩
        have hkL : k ∈ barM X L := hNL hk
        have hk' : (⟨k, hkL⟩ : ↥(barM X L)) ∈ ((barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
            (barM X L)) := hk
        have h1 : ψ ⟨k, hkL⟩ ∈ eightN 2 s := by
          rw [← hψN]; exact ⟨_, hk', rfl⟩
        obtain ⟨p, hp, hpk⟩ := h1
        refine ⟨⟨k, hkL⟩ * v' * ⟨k, hkL⟩⁻¹, ?_, rfl⟩
        have h2 : ψ (⟨k, hkL⟩ * v' * ⟨k, hkL⟩⁻¹) ∈ VA s := by
          have h3 : (ψ v' : AltE 2 s) ∈ VA s := hv'
          have h4 : ((ψ v' : AltE 2 s) : Perm (OmegaE 2 s)) ∈ VP s := h3
          have h5 := VP_conj s p.1 p.2 h4
          rw [map_mul, map_mul, map_inv]
          show (((ψ ⟨k, hkL⟩ : AltE 2 s) * ψ v' * (ψ ⟨k, hkL⟩ : AltE 2 s)⁻¹ : AltE 2 s) :
            Perm (OmegaE 2 s)) ∈ VP s
          have h6 : ((ψ ⟨k, hkL⟩ : AltE 2 s) : Perm (OmegaE 2 s)) = Perm.sumCongr p.1 p.2 :=
            hpk.symm
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv, h6]
          exact h5
        exact h2
    have hsub : VT.subgroupOf T ≤ ((barM X (S ⊓ L)).subgroupOf (barM X L)).subgroupOf T :=
      fun t ht => hVT_P ht
    have hdvd := Subgroup.index_dvd_of_le hsub
    have hc : ((VA s).subgroupOf (TA s)).comap eT.toMonoidHom = VT.subgroupOf T := by
      ext t
      simp only [mem_comap, mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      exact Iff.rfl
    have h3 : (VT.subgroupOf T).index = 3 := by
      rw [← hc, index_comap_of_surjective _ (by exact eT.surjective), index_VA_TA]
    rw [h3] at hdvd
    intro h2
    have := Nat.dvd_trans h2 hdvd
    omega
  have hT3 := hT3_of_equiv (eT.trans (eA s))
  have hres := blockTransfer_iso hA hSL T hnorm hsolv hodd hT3 hLB
  obtain ⟨t, htT, htN⟩ := exists_TA_not_eightN s
  have htT' : ψ.symm t ∈ T := by
    show ψ (ψ.symm t) ∈ TA s
    simpa using htT
  have hmem := hres _ htT'
  apply htN
  rw [← hψN]
  refine ⟨ψ.symm t, ?_, by simp⟩
  exact hmem

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 CFSG.QuasithinUnique

@[expose] def SolvableSylowNormalizerAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → SolvableSylowNormalizer X S

@[expose] def EightTwoExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    ∀ N : ℕ, ¬ (EightBlockData X S L 2 (N - 2 * 2) ∧ IsShort2 L ∧ IsTypeScriptL L)

theorem eightTwoExcluded_of_lemmaB (hB : SolvableSylowNormalizerAll) : EightTwoExcluded := by
  intro G _ _ X S L hX hA hL hSL N h
  exact eightTwo_false hA hL.toIsTwoPrimeComponent hSL (hB G X S hX hA) h.1

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
