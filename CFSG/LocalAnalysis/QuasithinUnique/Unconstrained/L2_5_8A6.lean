module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8A6Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.QuasithinUnique.Unc25A6

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter CFSG.QuasithinUnique.Unc25Small
  CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Unc25K1.A6Model CFSG.Sporadic.Schreier

abbrev X0 : Type := ↥A6Models.psl29

@[expose] def Dsub : Subgroup X0 := (P0 ⊓ A6Models.psl29).subgroupOf A6Models.psl29

theorem mem_Dsub (y : X0) : y ∈ Dsub ↔ code (y : P10) ∈ Core.dLit := by
  rw [← mem_D_iff, Dsub, Subgroup.mem_subgroupOf, Subgroup.mem_inf]

theorem code_X0_mem (y : X0) : code (y : P10) ∈ Core.pslLit := (mem_psl29_iff _).1 y.2

theorem exists_X0_of_code {c : List ℕ} (hc : c ∈ Core.pslLit) :
    ∃ y : X0, code (y : P10) = c := by
  obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hc
  exact ⟨⟨x, hx⟩, rfl⟩

theorem exists_Dsub_of_code {c : List ℕ} (hc : c ∈ Core.dLit) :
    ∃ y : X0, y ∈ Dsub ∧ code (y : P10) = c := by
  obtain ⟨x, hxP, hxpsl, rfl⟩ := exists_D_of_code hc
  exact ⟨⟨x, hxpsl⟩, (mem_Dsub _).2 hc, rfl⟩

theorem code_mul_X0 (x y : X0) :
    code ((x * y : X0) : P10) = Core.cmul (code (x : P10)) (code (y : P10)) := code_mul _ _

theorem code_one_X0 : code ((1 : X0) : P10) = Core.cid := code_one

theorem code_inj_X0 {x y : X0} (h : code (x : P10) = code (y : P10)) : x = y :=
  Subtype.ext (code_injective h)

theorem code_pow_X0 (x : X0) (n : ℕ) :
    code ((x ^ n : X0) : P10) = Core.cpow (code (x : P10)) n := by
  rw [Subgroup.coe_pow]
  exact code_pow _ _

theorem card_Dsub : Nat.card Dsub = 8 := by
  have h := card_eq_length (fun x : X0 => x ∈ Dsub) (fun x => code (x : P10))
    (fun x y hxy => code_inj_X0 hxy) Core.dLit d_nodup (fun c => by
      constructor
      · intro hc
        obtain ⟨y, hy, rfl⟩ := exists_Dsub_of_code hc
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact (mem_Dsub y).1 hy)
  rw [d_length] at h
  exact h

theorem isSylowTwoOf_Dsub : IsSylowTwoOf Dsub ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold IsSylowTwoOf
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_Dsub]; norm_num), ?_⟩
  have hmul := Subgroup.card_mul_index Dsub
  have hc : Nat.card X0 = 360 := card_psl29
  rw [card_Dsub, hc] at hmul
  have h45 : Dsub.index = 45 := by omega
  have hrel : (Dsub.subgroupOf ⊤).index = Dsub.index := Subgroup.relIndex_top_right Dsub
  rw [hrel, h45]
  decide

theorem shape_Dsub : Nonempty (↥Dsub ≃* DihedralGroup 4) := by
  have h := d_dihedral_check
  obtain ⟨ρc, hρc, h⟩ := List.any_eq_true.mp h
  obtain ⟨σc, hσc, hb⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range] at hb
  obtain ⟨⟨⟨⟨hσ2, hρ4⟩, hρ2⟩, hrel⟩, hall⟩ := hb
  obtain ⟨ρ, hρD, hρcode⟩ := exists_Dsub_of_code hρc
  obtain ⟨σ, hσD, hσcode⟩ := exists_Dsub_of_code hσc
  have hσ2' : σ * σ = 1 :=
    code_inj_X0 (by rw [code_mul_X0, code_one_X0, hσcode]; exact hσ2)
  have hρ4' : ρ ^ 4 = 1 :=
    code_inj_X0 (by rw [code_pow_X0, code_one_X0, hρcode]; exact hρ4)
  have hρ2' : ρ ^ 2 ≠ 1 := fun h => hρ2 (by
    have := congrArg (fun z : X0 => code (z : P10)) h
    simpa only [code_pow_X0, code_one_X0, hρcode] using this)
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2'
  have hρ3 : ρ ^ 3 = ρ⁻¹ := by
    have h1 : ρ ^ 3 * ρ = 1 := by rw [← pow_succ]; exact hρ4'
    exact (inv_eq_of_mul_eq_one_left h1).symm
  have hrel' : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    have h1 : σ * ρ * σ = ρ ^ 3 :=
      code_inj_X0 (by rw [code_mul_X0, code_mul_X0, code_pow_X0, hσcode, hρcode]; exact hrel)
    rw [hσinv, h1, hρ3]
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ↥Dsub, (ρ' : X0) = ρ := ⟨⟨ρ, hρD⟩, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ↥Dsub, (σ' : X0) = σ := ⟨⟨σ, hσD⟩, rfl⟩
  have hσ2'' : σ' ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hσ', pow_two]
    exact hσ2')
  have hrel'' : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := Subtype.ext (by
    show (σ' : X0) * (ρ' : X0) * (σ' : X0)⁻¹ = (ρ' : X0)⁻¹
    rw [hσ', hρ']
    exact hrel')
  have hρ4'' : ρ' ^ 4 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hρ']
    exact hρ4')
  have hρ2'' : ρ' ^ 2 ≠ 1 := fun h => hρ2' (by
    have := congrArg Subtype.val h
    rw [Subgroup.coe_pow, hρ'] at this
    exact this)
  have hgen : ⊤ = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    rw [eq_comm, eq_top_iff]
    intro x _
    obtain ⟨i, -, j, -, hij⟩ := hall (code ((x : X0) : P10)) ((mem_Dsub _).1 x.2)
    have hx : (x : X0) = ρ ^ i * σ ^ j :=
      code_inj_X0 (by
        rw [code_mul_X0, code_pow_X0, code_pow_X0, hρcode, hσcode]
        exact hij.symm)
    have hx' : x = ρ' ^ i * σ' ^ j := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hρ', hσ']
      exact hx)
    rw [hx']
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers ρ') i)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ') j)
  have hord : orderOf ρ' = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ρ') (by simpa using hρ2'')
      (by simpa using hρ4'')
    simpa using this
  rcases isCyclic_or_dihedral_of_generators ρ' σ' hgen hσ2'' hrel'' with hcyc | ⟨⟨e⟩⟩
  · exfalso
    have : IsCyclic ↥Dsub := hcyc
    have hcomm : ρ' * σ' = σ' * ρ' := IsMulCommutative.is_comm.comm ρ' σ'
    have h1 : σ' * ρ' * σ'⁻¹ = ρ' := by
      rw [← hcomm, mul_inv_cancel_right]
    rw [h1] at hrel''
    apply hρ2''
    have h2 : ρ' * ρ' = 1 := by
      calc ρ' * ρ' = ρ' * ρ'⁻¹ := by rw [← hrel'']
        _ = 1 := mul_inv_cancel ρ'
    rw [pow_two]
    exact h2
  · rw [hord] at e
    exact ⟨e⟩

theorem hnorm_Dsub : ∀ g : X0, (∀ p ∈ Dsub, g * p * g⁻¹ ∈ Dsub) → g ∈ Dsub := by
  intro g hg
  have h := List.all_eq_true.mp d_norm_check (code (g : P10)) (code_X0_mem g)
  have hn : normsB (code (g : P10)) Core.dLit = true := by
    unfold normsB
    rw [List.all_eq_true]
    intro d hd
    obtain ⟨p, hp, rfl⟩ := exists_Dsub_of_code hd
    rw [List.any_eq_true]
    refine ⟨code ((g * p * g⁻¹ : X0) : P10), (mem_Dsub _).1 (hg p hp), ?_⟩
    rw [beq_iff_eq, ← code_mul_X0, ← code_mul_X0, show g * p * g⁻¹ * g = g * p by group]
  rw [hn] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (mem_Dsub g).2 (List.contains_iff_mem.mp h)

theorem mem_Fl_iff {t s u : List ℕ} : u ∈ Fl t s ↔ u = Core.cid ∨ u = t ∨ u = s ∨ u = Core.cmul t s := by
  simp [Fl]

theorem lift_Fl {t s w x : X0}
    (h : ∃ u ∈ Fl (code (t : P10)) (code (s : P10)),
      Core.cmul (code (w : P10)) (code (x : P10)) = Core.cmul u (code (w : P10))) :
    ∃ u ∈ [1, t, s, t * s], w * x = u * w := by
  obtain ⟨u, hu, hue⟩ := h
  rw [mem_Fl_iff] at hu
  rcases hu with h | h | h | h
  · refine ⟨1, by simp, code_inj_X0 ?_⟩
    rw [code_mul_X0, code_mul_X0, code_one_X0]
    rw [h] at hue
    exact hue
  · refine ⟨t, by simp, code_inj_X0 ?_⟩
    rw [code_mul_X0, code_mul_X0]
    rw [h] at hue
    exact hue
  · refine ⟨s, by simp, code_inj_X0 ?_⟩
    rw [code_mul_X0, code_mul_X0]
    rw [h] at hue
    exact hue
  · refine ⟨t * s, by simp, code_inj_X0 ?_⟩
    rw [code_mul_X0, code_mul_X0, code_mul_X0]
    rw [h] at hue
    exact hue

theorem code_invsD {t : X0} (htD : t ∈ Dsub) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    code (t : P10) ∈ invsD := by
  unfold invsD
  rw [List.mem_filter]
  refine ⟨(mem_Dsub t).1 htD, ?_⟩
  have h1 : code (t : P10) ≠ Core.cid := fun h => ht1 (code_inj_X0 (by rw [h, code_one_X0]))
  have h2 : Core.cmul (code (t : P10)) (code (t : P10)) = Core.cid := by
    rw [← code_mul_X0, ht2, code_one_X0]
  simp [h1, h2]

theorem hfour_Dsub : ∀ t s : X0, t ∈ Dsub → s ∈ Dsub → t ≠ 1 → s ≠ 1 → t ≠ s → t * t = 1 →
    s * s = 1 → t * s = s * t →
    (∀ g : X0, g * t = t * g → g * s = s * g → g = 1 ∨ g = t ∨ g = s ∨ g = t * s) ∧
      ∃ w : X0, w ^ 3 = 1 ∧ w ≠ 1 ∧ (∃ u ∈ [1, t, s, t * s], w * t = u * w) ∧
        (∃ u ∈ [1, t, s, t * s], w * s = u * w) := by
  intro t s htD hsD ht1 hs1 hts ht2 hs2 hcomm
  have htI := code_invsD htD ht1 ht2
  have hsI := code_invsD hsD hs1 hs2
  have e3 : (code (t : P10) == code (s : P10)) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => hts (code_inj_X0 h)
  have e4 : (Core.cmul (code (t : P10)) (code (s : P10)) ==
      Core.cmul (code (s : P10)) (code (t : P10))) = true := by
    rw [beq_iff_eq, ← code_mul_X0, ← code_mul_X0, hcomm]
  refine ⟨?_, ?_⟩
  · intro g hgt hgs
    have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp d_cent_check
      (code (g : P10)) (code_X0_mem g)) _ htI) _ hsI
    have e1 : (Core.cmul (code (g : P10)) (code (t : P10)) ==
        Core.cmul (code (t : P10)) (code (g : P10))) = true := by
      rw [beq_iff_eq, ← code_mul_X0, ← code_mul_X0, hgt]
    have e2 : (Core.cmul (code (g : P10)) (code (s : P10)) ==
        Core.cmul (code (s : P10)) (code (g : P10))) = true := by
      rw [beq_iff_eq, ← code_mul_X0, ← code_mul_X0, hgs]
    rw [e1, e2, e3, e4] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((h | h) | h) | h
    · left
      exact code_inj_X0 (by rw [h, code_one_X0])
    · right; left
      exact code_inj_X0 h
    · right; right; left
      exact code_inj_X0 h
    · right; right; right
      exact code_inj_X0 (by rw [h, code_mul_X0])
  · have h := List.all_eq_true.mp (List.all_eq_true.mp d_three_check _ htI) _ hsI
    rw [e3, e4] at h
    simp only [Bool.false_or, Bool.not_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      List.any_eq_true] at h
    obtain ⟨wc, hwc, ⟨⟨hw3, hw1⟩, hwt⟩, hws⟩ := h
    obtain ⟨w, hw⟩ := exists_X0_of_code hwc
    refine ⟨w, ?_, ?_, lift_Fl ?_, lift_Fl ?_⟩
    · exact code_inj_X0 (by rw [code_pow_X0, code_one_X0, hw]; exact hw3)
    · intro h1
      apply hw1
      rw [← hw, h1, code_one_X0]
    · rw [hw]
      exact hwt
    · rw [hw]
      exact hws

theorem sylowFourData_Dsub : SylowFourData Dsub :=
  sylowFourData_of_checks isSylowTwoOf_Dsub (Or.inl ⟨4, le_rfl, shape_Dsub⟩) hnorm_Dsub hfour_Dsub

noncomputable def θ : MulAut X0 ≃* ↥A6Models.autA6 := thetaEquiv (MulEquiv.refl X0)

theorem θ_apply (γ : MulAut X0) (x : X0) :
    ((γ x : X0) : P10) = ((θ γ : ↥A6Models.autA6) : P10) * (x : P10) *
      ((θ γ : ↥A6Models.autA6) : P10)⁻¹ :=
  thetaEquiv_spec (MulEquiv.refl X0) γ x

theorem conj_apply (a : ↥A6Models.autA6) (x : X0) :
    ((θ.symm a x : X0) : P10) = (a : P10) * (x : P10) * (a : P10)⁻¹ := by
  have h := θ_apply (θ.symm a) x
  rwa [θ.apply_symm_apply] at h

@[expose] def toAut (g : X0) : ↥A6Models.autA6 := ⟨(g : P10), psl29_le_autA6 g.2⟩

theorem conj_toAut (g x : X0) : θ.symm (toAut g) x = g * x * g⁻¹ :=
  Subtype.ext (conj_apply (toAut g) x)

theorem normsB_iff {Q : Subgroup X0} {L : List (List ℕ)}
    (hL : ∀ c, c ∈ L ↔ ∃ y : X0, y ∈ Q ∧ code (y : P10) = c) (a : ↥A6Models.autA6) :
    normsB (code (a : P10)) L = true ↔ ∀ p ∈ Q, θ.symm a p ∈ Q := by
  constructor
  · intro h p hp
    have h1 := List.all_eq_true.mp h (code (p : P10)) ((hL _).2 ⟨p, hp, rfl⟩)
    obtain ⟨u, hu, hue⟩ := List.any_eq_true.mp h1
    rw [beq_iff_eq] at hue
    obtain ⟨y, hy, hyu⟩ := (hL u).1 hu
    have h2 : (a : P10) * (p : P10) = (y : P10) * (a : P10) := by
      apply code_injective
      rw [code_mul, code_mul, hyu]
      exact hue
    have h3 : θ.symm a p = y := by
      apply Subtype.ext
      rw [conj_apply, h2]
      group
    rw [h3]
    exact hy
  · intro h
    unfold normsB
    rw [List.all_eq_true]
    intro f hf
    obtain ⟨p, hp, rfl⟩ := (hL f).1 hf
    rw [List.any_eq_true]
    refine ⟨code ((θ.symm a p : X0) : P10), (hL _).2 ⟨_, h p hp, rfl⟩, ?_⟩
    rw [beq_iff_eq, ← code_mul, ← code_mul]
    congr 1
    rw [conj_apply]
    group

theorem mem_normalizer_iff_normsB {Q : Subgroup X0} {L : List (List ℕ)}
    (hL : ∀ c, c ∈ L ↔ ∃ y : X0, y ∈ Q ∧ code (y : P10) = c) (g : X0) :
    g ∈ Subgroup.normalizer (Q : Set X0) ↔ normsB (code (g : P10)) L = true := by
  have h := normsB_iff hL (toAut g)
  have hc : code ((toAut g : ↥A6Models.autA6) : P10) = code (g : P10) := rfl
  rw [hc] at h
  rw [h]
  constructor
  · intro hg p hp
    rw [conj_toAut]
    exact (Subgroup.mem_normalizer_iff.mp hg p).mp hp
  · intro h'
    refine mem_normalizer_of_conj_le fun f hf => ?_
    have h2 := h' f hf
    rwa [conj_toAut] at h2

theorem hL_D : ∀ c, c ∈ Core.dLit ↔ ∃ y : X0, y ∈ Dsub ∧ code (y : P10) = c := by
  intro c
  constructor
  · exact exists_Dsub_of_code
  · rintro ⟨y, hy, rfl⟩
    exact (mem_Dsub y).1 hy

theorem aut_sq_mem (a : ↥A6Models.autA6) : (a : P10) * (a : P10) ∈ A6Models.psl29 := by
  have h := List.all_eq_true.mp aut_sq_check (code (a : P10)) (code_mem_autL a.2)
  rw [mem_psl29_iff, code_mul]
  exact List.contains_iff_mem.mp h

theorem sq_inner (φ : MulAut X0) : φ ^ 2 ∈ innerAut X0 := by
  have hsq := aut_sq_mem (θ φ)
  refine ⟨⟨((θ φ : ↥A6Models.autA6) : P10) * ((θ φ : ↥A6Models.autA6) : P10), hsq⟩, ?_⟩
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  have e : ((φ ^ 2) y : X0) = φ (φ y) := by
    rw [pow_two]
    rfl
  rw [e, θ_apply φ (φ y), θ_apply φ y]
  show ((θ φ : ↥A6Models.autA6) : P10) * ((θ φ : ↥A6Models.autA6) : P10) * (y : P10) *
    (((θ φ : ↥A6Models.autA6) : P10) * ((θ φ : ↥A6Models.autA6) : P10))⁻¹ = _
  group

theorem beq_false_of_ne {t s : X0} (h : t ≠ s) : (code (t : P10) == code (s : P10)) = false := by
  rw [beq_eq_false_iff_ne]
  exact fun h' => h (code_inj_X0 h')

theorem beq_of_comm {t s : X0} (h : t * s = s * t) :
    (Core.cmul (code (t : P10)) (code (s : P10)) ==
      Core.cmul (code (s : P10)) (code (t : P10))) = true := by
  rw [beq_iff_eq, ← code_mul_X0, ← code_mul_X0, h]

theorem θ_comm {φ : MulAut X0} {x : X0} (h : φ x = x) :
    ((θ φ : ↥A6Models.autA6) : P10) * (x : P10) = (x : P10) * ((θ φ : ↥A6Models.autA6) : P10) := by
  have h1 := θ_apply φ x
  rw [h] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1.symm)

theorem fixes_Dsub : ∀ F : Subgroup X0, F ≤ Dsub → IsFourSubgroup F → ∀ φ : MulAut X0,
    (∀ f ∈ F, φ f = f) → ∀ y, φ y ∈ Dsub ↔ y ∈ Dsub := by
  intro F hFP hF φ hφ
  obtain ⟨t, s, ht, hs, hc, ht1, hs1, hts, rfl⟩ := exists_kleinFour_gens hF
  have hmem := Unc25K1.mem_kleinFourOfCommutingInvolutions_iff ht hs hc
  have htF : t ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
    (hmem t).mpr (Or.inr (Or.inl rfl))
  have hsF : s ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
    (hmem s).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have htI := code_invsD (hFP htF) ht1 ht
  have hsI := code_invsD (hFP hsF) hs1 hs
  have hn : normsB (code ((θ φ : ↥A6Models.autA6) : P10)) Core.dLit = true := by
    have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp d_fix_check
      (code ((θ φ : ↥A6Models.autA6) : P10)) (code_mem_autL (θ φ).2)) _ htI) _ hsI
    have e1 : (Core.cmul (code ((θ φ : ↥A6Models.autA6) : P10)) (code (t : P10)) ==
        Core.cmul (code (t : P10)) (code ((θ φ : ↥A6Models.autA6) : P10))) = true := by
      rw [beq_iff_eq, ← code_mul, ← code_mul, θ_comm (hφ t htF)]
    have e2 : (Core.cmul (code ((θ φ : ↥A6Models.autA6) : P10)) (code (s : P10)) ==
        Core.cmul (code (s : P10)) (code ((θ φ : ↥A6Models.autA6) : P10))) = true := by
      rw [beq_iff_eq, ← code_mul, ← code_mul, θ_comm (hφ s hsF)]
    rw [e1, e2, beq_false_of_ne hts, beq_of_comm hc.eq] at h
    simpa only [Bool.not_true, Bool.false_or, Bool.or_false] using h
  have h2 := (normsB_iff hL_D (θ φ)).1 hn
  rw [θ.symm_apply_apply] at h2
  exact mem_iff_of_map_le _ h2

theorem f1_data : t1C ∈ invsD ∧ s1C ∈ invsD ∧ t1C ≠ s1C ∧
    Core.cmul t1C s1C = Core.cmul s1C t1C := by
  have h := f1_valid
  simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem dynkinAt_Dsub : DynkinAt X0 Dsub := by
  intro B hB1 hB2 α hα hcomm
  obtain ⟨ht1I, hs1I, hne1, hcomm1⟩ := f1_data
  have ht1D : t1C ∈ Core.dLit := (List.mem_filter.mp ht1I).1
  have hs1D : s1C ∈ Core.dLit := (List.mem_filter.mp hs1I).1
  obtain ⟨t1, ht1Dsub, ht1code⟩ := exists_Dsub_of_code ht1D
  obtain ⟨s1, hs1Dsub, hs1code⟩ := exists_Dsub_of_code hs1D
  have ht1sq : t1 * t1 = 1 := by
    apply code_inj_X0
    rw [code_mul_X0, code_one_X0, ht1code]
    have h := (List.mem_filter.mp ht1I).2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    exact h.2
  have hs1sq : s1 * s1 = 1 := by
    apply code_inj_X0
    rw [code_mul_X0, code_one_X0, hs1code]
    have h := (List.mem_filter.mp hs1I).2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    exact h.2
  have hcomm1' : Commute t1 s1 := by
    show t1 * s1 = s1 * t1
    apply code_inj_X0
    rw [code_mul_X0, code_mul_X0, ht1code, hs1code]
    exact hcomm1
  obtain ⟨F1, hF1⟩ : ∃ F1 : Subgroup X0, F1 = kleinFourOfCommutingInvolutions t1 s1 ht1sq hs1sq
      hcomm1' := ⟨_, rfl⟩
  have hmemF1 : ∀ y : X0, y ∈ F1 ↔ y = t1 * s1 ∨ y = t1 ∨ y = s1 ∨ y = 1 := by
    intro y
    rw [hF1]
    exact Unc25K1.mem_kleinFourOfCommutingInvolutions_iff ht1sq hs1sq hcomm1' y
  have hL1 : ∀ c, c ∈ Fl t1C s1C ↔ ∃ y : X0, y ∈ F1 ∧ code (y : P10) = c := by
    intro c
    rw [mem_Fl_iff]
    constructor
    · rintro (h | h | h | h)
      · exact ⟨1, (hmemF1 1).2 (Or.inr (Or.inr (Or.inr rfl))), by rw [code_one_X0, h]⟩
      · exact ⟨t1, (hmemF1 t1).2 (Or.inr (Or.inl rfl)), by rw [ht1code, h]⟩
      · exact ⟨s1, (hmemF1 s1).2 (Or.inr (Or.inr (Or.inl rfl))), by rw [hs1code, h]⟩
      · exact ⟨t1 * s1, (hmemF1 _).2 (Or.inl rfl), by rw [code_mul_X0, ht1code, hs1code, h]⟩
    · rintro ⟨y, hy, rfl⟩
      rcases (hmemF1 y).1 hy with h | h | h | h
      · right; right; right
        rw [h, code_mul_X0, ht1code, hs1code]
      · right; left
        rw [h, ht1code]
      · right; right; left
        rw [h, hs1code]
      · left
        rw [h, code_one_X0]
  have hDY : Dsub ≤ Subgroup.normalizer (F1 : Set X0) := by
    intro d hd
    rw [mem_normalizer_iff_normsB hL1 d]
    exact List.all_eq_true.mp f1_dnorm (code (d : P10)) ((mem_Dsub d).1 hd)
  have hYD : Subgroup.normalizer (F1 : Set X0) ≠ Dsub := by
    intro h
    obtain ⟨wc, hwc, hw⟩ := List.any_eq_true.mp f1_ne_d
    obtain ⟨hw1, hw2⟩ := Bool.and_eq_true_iff.mp hw
    obtain ⟨w, hwcode⟩ := exists_X0_of_code hwc
    have hwY : w ∈ Subgroup.normalizer (F1 : Set X0) := by
      rw [mem_normalizer_iff_normsB hL1 w, hwcode]
      exact hw1
    rw [h] at hwY
    have hm := (mem_Dsub w).1 hwY
    rw [hwcode] at hm
    have hc : Core.dLit.contains wc = true := List.contains_iff_mem.mpr hm
    rw [hc] at hw2
    exact absurd hw2 (by decide)
  have hYtop : Subgroup.normalizer (F1 : Set X0) ≠ ⊤ := by
    intro h
    obtain ⟨gc, hgc, hg⟩ := List.any_eq_true.mp f1_ne_top
    obtain ⟨g, hgcode⟩ := exists_X0_of_code hgc
    have hgY : g ∈ Subgroup.normalizer (F1 : Set X0) := by rw [h]; exact Subgroup.mem_top g
    rw [mem_normalizer_iff_normsB hL1 g, hgcode] at hgY
    simp [hgY] at hg
  have hnot : ¬ (∀ β ∈ B, ∀ y : X0, β y ∈ Subgroup.normalizer (F1 : Set X0) ↔
      y ∈ Subgroup.normalizer (F1 : Set X0)) := fun h => by
    rcases hB2 _ hDY h with h' | h'
    · exact hYD h'
    · exact hYtop h'
  have hex : ∃ β ∈ B, ¬ (∀ f ∈ F1, β f ∈ F1) := by
    by_contra hcon
    apply hnot
    intro β hβ y
    refine normalizer_preserved β F1 (fun f hf => ?_) y
    by_contra hfF
    exact hcon ⟨β, hβ, fun h => hfF (h f hf)⟩
  obtain ⟨β, hβ, hβF⟩ := hex
  obtain ⟨b, hb⟩ : ∃ b : ↥A6Models.autA6, θ.symm b = β := ⟨θ β, θ.symm_apply_apply β⟩
  obtain ⟨a, ha⟩ : ∃ a : ↥A6Models.autA6, θ.symm a = α := ⟨θ α, θ.symm_apply_apply α⟩
  have hbD : normsB (code (b : P10)) Core.dLit = true :=
    (normsB_iff hL_D b).2 fun p hp => by
      rw [hb]
      exact (hB1 β hβ p).2 hp
  have hbF : ¬ (normsB (code (b : P10)) (Fl t1C s1C) = true) := fun h =>
    hβF fun f hf => by
      have h1 := (normsB_iff hL1 b).1 h f hf
      rwa [hb] at h1
  have haD : ∀ d ∈ Core.dLit, Core.cmul (code (a : P10)) d = Core.cmul d (code (a : P10)) := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := exists_Dsub_of_code hd
    have h0 : θ.symm a p = p := by
      rw [ha]
      exact hα p hp
    have h1 := congrArg (fun z : X0 => (z : P10)) h0
    simp only [conj_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [← code_mul, ← code_mul, h1]
  have hab' : a * b = b * a := θ.symm.injective (by
    rw [map_mul, map_mul, ha, hb]
    exact hcomm β hβ)
  have hab : Core.cmul (code (a : P10)) (code (b : P10)) =
      Core.cmul (code (b : P10)) (code (a : P10)) := by
    rw [← code_mul, ← code_mul]
    exact congrArg (fun z : ↥A6Models.autA6 => code (z : P10)) hab'
  have hdyn := List.all_eq_true.mp dyn_check (code (a : P10)) (code_mem_autL a.2)
  have hcent : (Core.dLit.all fun d => Core.cmul (code (a : P10)) d ==
      Core.cmul d (code (a : P10))) = true := by
    rw [List.all_eq_true]
    intro d hd
    rw [beq_iff_eq]
    exact haD d hd
  rw [hcent, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hdyn
  rcases hdyn with hpsl | hall
  · have ha_psl : (a : P10) ∈ A6Models.psl29 :=
      (mem_psl29_iff _).2 (List.contains_iff_mem.mp hpsl)
    refine ⟨⟨(a : P10), ha_psl⟩, ?_⟩
    rw [← ha]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [conj_apply]
    rfl
  · exfalso
    have h2 := List.all_eq_true.mp hall (code (b : P10)) (code_mem_autL b.2)
    have e2 : normsB (code (b : P10)) (Fl t1C s1C) = false := by simpa using hbF
    have e3 : (Core.cmul (code (a : P10)) (code (b : P10)) ==
        Core.cmul (code (b : P10)) (code (a : P10))) = true := beq_iff_eq.2 hab
    rw [hbD, e2, e3] at h2
    simp at h2

theorem isSimple_X0 : IsSimpleGroup X0 := by
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact ψ.isSimpleGroup

theorem smallListFacts_X0 : SmallListFacts X0 :=
  { simple := isSimple_X0
    out_two := fun φ => ⟨1, by rw [pow_one]; exact sq_inner φ⟩
    sylow_shape := sylowFourData_Dsub.sylow_shape
    sylow_normalizer := sylowFourData_Dsub.sylow_normalizer
    four_normalizer := fun _ hF => sylowFourData_Dsub.four_normalizer hF
    four_fixes := four_fixes_of_sylow isSylowTwoOf_Dsub fixes_Dsub }

theorem a6_facts (X : Type) [Group X] [Finite X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 6))) :
    SmallListFacts X ∧ A6DynkinCentral X := by
  obtain ⟨e⟩ := h
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  let φ : X ≃* X0 := e.trans ψ.symm
  refine ⟨SmallListFacts.of_mulEquiv φ smallListFacts_X0, ?_⟩
  exact a6DynkinCentral_of_dynkinAt (isSylowTwoOf_top_map' φ.symm isSylowTwoOf_Dsub)
    (dynkinAt_Dsub.map φ.symm)

end CFSG.QuasithinUnique.Unc25A6
