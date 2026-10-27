module

public import CFSG.Holt.H78.Sec4Prop49S5e

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

theorem IsNaturalSE.card_mod_four {Δ : Type*} [Fintype Δ] {M : Subgroup (Equiv.Perm Δ)}
    (hM : IsNaturalSE M) : Fintype.card Δ % 4 = 1 := by
  obtain ⟨q, e, hB⟩ := hM
  obtain ⟨-, -, he, -⟩ := hB.params
  have key : ∀ f : ℕ, 2 ≤ f → 4 ∣ 2 ^ f := fun f hf => by
    have := pow_dvd_pow 2 hf
    simpa using this
  have hq : 4 ∣ q := by
    rcases hB.model with ⟨-, f, hf, rfl, -⟩ | ⟨-, a, ha, rfl, -⟩ | ⟨-, f, hf, rfl, -⟩
    · exact key f hf
    · exact key _ (by omega)
    · exact key f hf
  have h4 : 4 ∣ q ^ e := hq.trans (dvd_pow_self q (by omega))
  rw [← Nat.card_eq_fintype_card, hB.card_eq]
  omega

namespace P49Config

section Prop53

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data)

theorem two_mul_card_rootZ_le (h : C.P95) : 2 * Nat.card C.rootZ ≤ Nat.card P.W := by
  obtain ⟨T⟩ := P.nonempty_torus h
  obtain ⟨k, hk, hkL, hX⟩ := P.exists_ne_inf_ne_bot h
  obtain ⟨n, hnα, hnN, hnL⟩ := P.exists_mem_normalizer_smul_line h hk
  have hnα' : n⁻¹ • α = α := by
    rw [inv_smul_eq_iff]
    exact (mem_stabilizer_iff.mp hnα).symm
  set X' : Subgroup G := (P.W ⊓ P.Wl k).map (MulAut.conj n⁻¹).toMonoidHom
  have hX'W : X' ≤ P.W := by
    rintro _ ⟨x, hx, rfl⟩
    have := P.conj_mem_Wl (inv_mem hnN) hx.2
    rwa [← hnL, inv_smul_smul] at this
  have hX'1 : X' ≠ ⊥ := fun h1 =>
    hX ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj n⁻¹).injective).mp h1)
  have hℓ' : n⁻¹ • C.line ∈ linesThrough G C.line α := by
    have := smul_mem_linesThrough (line_mem_linesThrough C) n⁻¹
    rwa [hnα'] at this
  have hℓ'L : n⁻¹ • C.line ≠ C.line := fun h1 => hkL (by
    rw [← hnL]
    nth_rewrite 1 [← h1]
    exact smul_inv_smul n _)
  have hX'ℓ' : X' ≤ P.Wl (n⁻¹ • C.line) := by
    rintro _ ⟨x, hx, rfl⟩
    exact P.conj_mem_Wl (inv_mem hnN) hx.1
  have hV' := Torus.V_le_Wl_of_le P h T hX'W hX'1 hℓ' hℓ'L hX'ℓ'
  set Vk : Subgroup G := T.V.map (MulAut.conj n).toMonoidHom
  have hVkW : Vk ≤ P.W := by
    rintro _ ⟨x, hx, rfl⟩
    have := P.conj_mem_Wl hnN (hV' hx)
    rwa [smul_inv_smul] at this
  have hVk : Nat.card Vk = Nat.card C.rootZ := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, T.card_V h]
  have hne : Vk ≠ P.W := by
    intro heq
    apply hX
    rw [eq_bot_iff]
    intro y hy
    have hyVk : y ∈ Vk := heq ▸ hy.1
    obtain ⟨x, hx, rfl⟩ := hyVk
    have hxW : x ∈ P.W := by
      have h1 := P.conj_mem_Wl (inv_mem hnN) hy.2
      rw [← hnL, inv_smul_smul] at h1
      have e : n⁻¹ * ((MulAut.conj n).toMonoidHom x) * n⁻¹⁻¹ = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e] at h1
      exact h1
    rw [T.eq_one_of_mem_W h hx hxW, map_one]
    exact Subgroup.one_mem _
  have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hVkW hne)
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hVkW
  rw [hVk] at ha hlt
  rw [ha] at hlt ⊢
  have ha2 : 2 ≤ a := by
    by_contra h2
    push Not at h2
    interval_cases a <;> omega
  calc 2 * Nat.card C.rootZ ≤ a * Nat.card C.rootZ := Nat.mul_le_mul_right _ ha2
    _ = Nat.card C.rootZ * a := mul_comm _ _

theorem inf_Wl_ne_bot (h : C.P95) {ℓ : Set Ω} (hℓ : ℓ ∈ linesThrough G C.line α) :
    P.W ⊓ P.Wl ℓ ≠ ⊥ := by
  have hE := P.card_E h
  have h2 := P.two_mul_card_rootZ_le h
  have hWE : P.W ≤ P.E := inf_le_left
  have hWlE : P.Wl ℓ ≤ P.E := inf_le_left
  have hrel : ∀ H : Subgroup G, H ≤ P.E → H.relIndex P.E * Nat.card H = Nat.card P.E :=
    fun H hH => by
      have := Subgroup.relIndex_mul_card H P.E
      rwa [inf_eq_left.mpr hH] at this
  have h1 := hrel _ hWE
  have h1' := hrel _ hWlE
  rw [P.card_Wl h hℓ] at h1'
  have hI := hrel (P.W ⊓ P.Wl ℓ) (inf_le_left.trans hWE)
  have hle := Subgroup.relIndex_inf_le (H := P.W) (K := P.Wl ℓ) (L := P.E)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hI
  rw [hbot] at hle
  have hq : 0 < Nat.card C.rootZ := Nat.card_pos
  have hw : 0 < Nat.card P.W := Nat.card_pos
  rw [hE] at h1 h1' hI
  have e1 : P.W.relIndex P.E = Nat.card C.rootZ :=
    Nat.eq_of_mul_eq_mul_right hw (h1.trans (mul_comm _ _))
  have e2 : (P.Wl ℓ).relIndex P.E = Nat.card C.rootZ :=
    Nat.eq_of_mul_eq_mul_right hw (h1'.trans (mul_comm _ _))
  rw [e1, e2] at hle
  rw [mul_one] at hI
  rw [hI] at hle
  nlinarith

theorem Torus.V_le_Wl (h : C.P95) (T : P.Torus) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) (hℓL : ℓ ≠ C.line) : T.V ≤ P.Wl ℓ :=
  Torus.V_le_Wl_of_le P h T inf_le_left (P.inf_Wl_ne_bot h hℓ) hℓ hℓL inf_le_right

end P95Data

end Prop53

section Lemma54

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data) {X : Subgroup G}

theorem not_isOuterFactor (h : C.P95) (hXW : X ≤ P.W) (hX1 : X ≠ ⊥)
    (D : HoltData (centralizerImage Ω X) (fixSet Ω X)) {c : D.ι}
    (hcL : ∀ y : fixSet Ω X, (y : Ω) ∈ C.line → ∀ j, j ≠ c →
      D.coord y j = D.coord ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩ j) :
    ¬ IsOuterFactor (D.M c) := by
  rintro ⟨hAlt, h4⟩
  have hS := h.setting
  have hXp := P.isPGroup_of_le_W hXW
  have h3 := P.three_le_card_fixSet_of_le_W hXW
  have hinj := D.coord_injective (P.jOddCore_eq_bot h hXW hX1)
  set αX : fixSet Ω X := ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩
  set βX : fixSet Ω X := ⟨C.β, P.line_subset_fixSet_of_le_W hXW C.β_mem_line⟩
  have hβc : D.coord βX c ≠ D.coord αX c := fun h1 => C.ne (congrArg Subtype.val (hinj (funext
    fun j => by
      rcases eq_or_ne j c with rfl | hj
      · exact h1.symm
      · exact (hcL βX C.β_mem_line j hj).symm)))
  have hsurj : ∀ ψ' : D.Ψc c, ∃ y : fixSet Ω X, (y : Ω) ∈ C.line ∧ D.coord y c = ψ' := by
    intro ψ'
    by_cases hψα : ψ' = D.coord αX c
    · exact ⟨αX, C.α_mem_line, hψα.symm⟩
    by_cases hψβ : ψ' = D.coord βX c
    · exact ⟨βX, C.β_mem_line, hψβ.symm⟩
    have hM : alternatingGroup (D.Ψc c) ≤ (D.ρ c).range := by
      rw [D.range_rho, ← hAlt]
      exact le_sup_left
    have hΔ' := holtDelta'_eq_compl_of_alternatingGroup_le hM ⟨D.tHull, rfl⟩
      (D.rho_mem_longInv D.t_mem c) (Ne.symm hβc)
    have hmem : ψ' ∈ holtDelta' (D.ρ c).range (D.Ψc c) (D.coord αX c) (D.coord βX c) := by
      rw [hΔ']
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hψα, hψβ⟩
    obtain ⟨w, hw, hwβ⟩ := hmem
    obtain ⟨t₀, ht₀⟩ := D.longInvAt_nonempty αX
    set t₀H : jHull (centralizerImage Ω X) (fixSet Ω X) := ⟨t₀, mem_jHull_of_mem_longInv ht₀.1⟩
    obtain ⟨π, hπ, hρ⟩ := D.exists_mem_longInvAt_rho_eq αX
      (Function.update (fun j => D.ρ j t₀H) c (w : Equiv.Perm (D.Ψc c))) (fun j => by
        rcases eq_or_ne j c with rfl | hj
        · rw [Function.update_self]; exact w.2
        · rw [Function.update_of_ne hj]; exact ⟨t₀H, rfl⟩) (fun j => by
        rcases eq_or_ne j c with rfl | hj
        · rw [Function.update_self]; exact mem_longInvAt_subgroup_iff.mp hw
        · rw [Function.update_of_ne hj]; exact D.rho_mem_longInvAt ht₀ j)
    obtain ⟨s, hs, -, hsπ⟩ :=
      (hS.mem_longInvAt_centralizerImage_iff hXp h3 (π : centralizerImage Ω X)).mp hπ
    refine ⟨(π : centralizerImage Ω X) • βX, ?_, ?_⟩
    · have h1 : (((π : centralizerImage Ω X) • βX : fixSet Ω X) : Ω) = s • C.β := hsπ βX
      rw [h1, ← h.smul_eq_of_mem_K (Subgroup.subset_closure hs) (line_mem_linesThrough C)]
      exact Set.smul_mem_smul_set C.β_mem_line
    · rw [D.coord_smul, hρ, Function.update_self]
      exact hwβ
  set f : C.D.Ψc C.i → D.Ψc c := fun ψ =>
    D.coord ⟨(C.lpt ψ : Ω), P.line_subset_fixSet_of_le_W hXW (C.lpt_mem_line ψ)⟩ c
  have hf : Function.Bijective f := by
    refine ⟨fun ψ ψ' hψ => C.lpt_injective (Subtype.ext ?_), fun ψ' => ?_⟩
    · have := hinj (funext fun j => by
        rcases eq_or_ne j c with rfl | hj
        · exact hψ
        · exact (hcL _ (C.lpt_mem_line ψ) j hj).trans (hcL _ (C.lpt_mem_line ψ') j hj).symm)
      exact congrArg (fun y : fixSet Ω X => (y : Ω)) this
    · obtain ⟨⟨y, hyX⟩, hyL, hyc⟩ := hsurj ψ'
      obtain ⟨ψ, rfl⟩ := hyL
      exact ⟨ψ, hyc⟩
  have hcard := Fintype.card_of_bijective hf
  have h1 := (C.isNaturalSE C.i).card_mod_four
  omega

end P95Data

theorem P95.exists_mem_fixingSubgroup_lineActs (h : C.P95) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) (hℓL : ℓ ≠ C.line) {m : Equiv.Perm (C.D.Ψc C.i)}
    (hm : m ∈ C.D.M C.i) (hma : m (C.D.coord C.a C.i) = C.D.coord C.a C.i) :
    ∃ g ∈ fixingSubgroup G ℓ, C.LineActs g m := by
  obtain ⟨P⟩ := nonempty_p95Data C
  have hS := h.setting
  set X : Subgroup G := P.W ⊓ P.Wl ℓ
  have hXW : X ≤ P.W := inf_le_left
  have hX1 : X ≠ ⊥ := P.inf_Wl_ne_bot h hℓ
  have hXℓ : X ≤ P.Wl ℓ := inf_le_right
  have hXp := P.isPGroup_of_le_W hXW
  have h3 := P.three_le_card_fixSet_of_le_W hXW
  obtain ⟨D⟩ := hS.holtData_centralizerImage hXp hX1 h3
  have hinj := D.coord_injective (P.jOddCore_eq_bot h hXW hX1)
  set αX : fixSet Ω X := ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩
  obtain ⟨c, hcL⟩ := P.exists_coord_of_le_Wl h hXW hX1 D (line_mem_linesThrough C)
    (le_of_le_of_eq hXW rfl)
  obtain ⟨c', hc'⟩ := P.exists_coord_of_le_Wl h hXW hX1 D hℓ hXℓ
  have hcc' : c ≠ c' := fun hcc => P.false_of_coord_eq h hXW hX1 D hℓ hXℓ hℓL hcL (hcc ▸ hc')
  have hXL : X ≤ fixingSubgroup G C.line := fun x hx => (hXW hx).2
  obtain ⟨g, hg, hgm⟩ := C.exists_lineActs_closure hS h.transitive hXp hXL hm
  have hg' : g ∈ Subgroup.closure
      {c | c ∈ longInv G Ω ∧ c ∈ Subgroup.centralizer (X : Set G)} := by
    refine Subgroup.closure_mono ?_ hg
    intro c hc
    exact ⟨hc.1, hc.2.1⟩
  obtain ⟨hgC, hgH⟩ := hS.centralizerImageElt_mem_jHull_of_mem_closure hXp h3 hg'
  set gH : jHull (centralizerImage Ω X) (fixSet Ω X) := ⟨_, hgH⟩
  have hgα : g • α = α := by rw [hgm.smul_α, hma, C.lpt_coord_a, C.coe_a]
  have hgαX : (gH : centralizerImage Ω X) • αX = αX := Subtype.ext hgα
  have hρ : D.ρ c gH ∈ D.M c := by
    rw [← D.range_rho_of_not_isOuterFactor (P.not_isOuterFactor h hXW hX1 D hcL)]
    exact ⟨gH, rfl⟩
  obtain ⟨hh, hhL, hhρ⟩ := D.mem_M.mp hρ
  obtain ⟨g', -, hg'h⟩ := mem_centralizerImage.mp (hh : centralizerImage Ω X).2
  refine ⟨g', ?_, fun ψ => ?_⟩
  · rw [mem_fixingSubgroup_iff]
    intro y hy
    have hyX : y ∈ fixSet Ω X := fun x hx => (P.mem_Wl.mp (hXℓ hx)).2 y hy
    set yX : fixSet Ω X := ⟨y, hyX⟩
    have hfix : (hh : centralizerImage Ω X) • yX = yX := hinj (funext fun j => by
      rw [D.coord_smul]
      rcases eq_or_ne j c with rfl | hj
      · rw [hhρ, hc' yX hy j hcc', ← D.coord_smul, hgαX]
      · rw [D.rho_eq_one_of_mem_L (Ne.symm hj) hhL, Equiv.Perm.one_apply])
    rw [← hg'h yX]
    exact congrArg Subtype.val hfix
  · have hψX : (C.lpt ψ : Ω) ∈ fixSet Ω X :=
      P.line_subset_fixSet_of_le_W hXW (C.lpt_mem_line ψ)
    set yX : fixSet Ω X := ⟨_, hψX⟩
    have heq : (hh : centralizerImage Ω X) • yX = (gH : centralizerImage Ω X) • yX :=
      hinj (funext fun j => by
        rw [D.coord_smul, D.coord_smul]
        rcases eq_or_ne j c with rfl | hj
        · rw [hhρ]
        · rw [D.rho_eq_one_of_mem_L (Ne.symm hj) hhL, Equiv.Perm.one_apply,
            hcL yX (C.lpt_mem_line ψ) j hj, ← D.coord_smul, hgαX])
    exact (hg'h yX).symm.trans ((congrArg Subtype.val heq).trans (hgm ψ))

end Lemma54

section Thm55

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

theorem LineActs.conj_mem_M (h : C.P95) {g : G} {π : Equiv.Perm (C.D.Ψc C.i)}
    (hg : C.LineActs g π) {y : Equiv.Perm (C.D.Ψc C.i)} (hy : y ∈ C.D.M C.i) :
    π * y * π⁻¹ ∈ C.D.M C.i := by
  have hS := h.setting
  have hgen : Subgroup.closure {y | y ∈ C.D.M C.i ∧ y ∈ longInv (Equiv.Perm (C.D.Ψc C.i))
      (C.D.Ψc C.i)} ≤ (C.D.M C.i).comap (MulAut.conj π).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyM, hyJ⟩
    obtain ⟨ψ₀, hψ₀, -⟩ := hyJ.2
    obtain ⟨s, hs, -, hsy⟩ := C.exists_lineActs_longInvAt hS hyM ⟨hyJ, hψ₀⟩
    have hs' := conj_mem_longInvAt hs g
    rw [hg ψ₀] at hs'
    obtain ⟨y', hy'M, -, hy'⟩ := C.exists_lineActs_of_mem_longInvAt hS h.transitive hs'
    have h1 : C.LineActs (g * s * g⁻¹) (π * y * π⁻¹) := (hg.mul hsy).mul hg.inv
    show π * y * π⁻¹ ∈ C.D.M C.i
    rw [h1.unique hy']
    exact hy'M
  exact hgen ((C.isNaturalSE C.i).le_closure_longInv hy)

theorem LineActs.mem_normalizer (h : C.P95) {g : G} {π : Equiv.Perm (C.D.Ψc C.i)}
    (hg : C.LineActs g π) :
    π ∈ Subgroup.normalizer (C.D.M C.i : Set (Equiv.Perm (C.D.Ψc C.i))) :=
  mem_normalizer_of_conj (fun _ hz => hg.conj_mem_M h hz) (fun _ hz => hg.inv.conj_mem_M h hz)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem pow_card_eq_one_of_mem {N : Subgroup G} {x : G} (hx : x ∈ N) : x ^ Nat.card N = 1 := by
  have h1 : (⟨x, hx⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
  have h2 := congrArg Subtype.val h1
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2

theorem P95.smul_eq_of_odd (h : C.P95) {ℓ : Set Ω} (hℓ : ℓ ∈ linesThrough G C.line α)
    (hℓL : ℓ ≠ C.line) {N : Subgroup G} (hN : N ≤ fixingSubgroup G ℓ)
    (hnorm : ∀ p ∈ fixingSubgroup G ℓ, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (hodd : Odd (Nat.card N))
    {n : G} (hn : n ∈ N) {y : Ω} (hy : y ∈ C.line) : n • y = y := by
  obtain ⟨P⟩ := nonempty_p95Data C
  obtain ⟨T⟩ := P.nonempty_torus h
  have hnα : n • α = α := (mem_fixingSubgroup_iff G).mp (hN hn) α hℓ.2
  have hcomm : ∀ {g : G}, g ∈ fixingSubgroup G ℓ → n * g * n⁻¹ * g⁻¹ ∈ N := fun {g} hg => by
    have e : n * g * n⁻¹ * g⁻¹ = n * (g * n⁻¹ * g⁻¹) := by group
    rw [e]
    exact N.mul_mem hn (hnorm g hg n⁻¹ (N.inv_mem hn))
  have hKΓ : ∀ k ∈ C.K, k ∈ N → ∀ γ ∈ C.Γ, k • γ = γ := by
    intro k hk hkN γ hγ
    obtain ⟨e, he, heγ⟩ := P.exists_mem_E_eqOn h hk
    have heα : e ∈ stabilizer G α := P.E_le_stabilizer he
    have hpow : ∀ j : ℕ, ∀ γ ∈ C.Γ, k ^ j • γ = e ^ j • γ := by
      intro j
      induction j with
      | zero => intro γ _; simp
      | succ j ih =>
        intro γ hγ
        have heγ' : e • γ ∈ C.Γ := by
          rw [← smul_Γ (C := C) heα]
          exact Set.smul_mem_smul_set hγ
        rw [pow_succ, pow_succ, mul_smul, mul_smul, ← heγ γ hγ, ih _ heγ']
    obtain ⟨a, ha⟩ := hodd
    have h1 := hpow (Nat.card N) γ hγ
    rw [pow_card_eq_one_of_mem hkN, one_smul, ha, pow_succ, pow_mul, sq, P.mul_self_E h he,
      one_pow, one_mul] at h1
    rw [heγ γ hγ] at h1
    exact h1.symm
  have htK : P.t ∈ C.K := Subgroup.subset_closure P.t_mem
  obtain ⟨zt, hzt, htz⟩ := h.exists_lineActs_rootZ htK
  obtain ⟨e, heV, hez⟩ := T.exists_mem_V_lineActs h hzt
  have heβ : e • C.β ≠ C.β := by
    rw [hez.smul_β, ← htz.smul_β]
    exact fun h1 => C.ne (P.t_mem.1.2.unique h1 P.t_mem.2).symm
  have heWl : ∀ A ∈ linesThrough G C.line α, A ≠ C.line → e ∈ P.Wl A := fun A hA hAL =>
    P95Data.Torus.V_le_Wl P h T hA hAL heV
  have heK : e ∈ C.K := P.E_le_K (T.V_le_E heV)
  have heℓ : e ∈ fixingSubgroup G ℓ :=
    (mem_fixingSubgroup_iff G).mpr (P.mem_Wl.mp (heWl ℓ hℓ hℓL)).2
  have hconjΓ : ∀ γ ∈ C.Γ, (n * e * n⁻¹) • γ = e • γ := fun γ hγ => by
    have heγ : e • γ ∈ C.Γ := by
      rw [← smul_Γ (C := C) (P.E_le_stabilizer (T.V_le_E heV))]
      exact Set.smul_mem_smul_set hγ
    have hcK : n * e * n⁻¹ * e⁻¹ ∈ C.K :=
      mul_mem (conj_mem_K (mem_stabilizer_iff.mpr hnα) heK) (inv_mem heK)
    have h1 := hKΓ _ hcK (hcomm heℓ) _ heγ
    rwa [mul_smul, inv_smul_smul] at h1
  have hnL : n • C.line = C.line := by
    by_contra hne
    have hA : n⁻¹ • C.line ∈ linesThrough G C.line α := by
      have := smul_mem_linesThrough (line_mem_linesThrough C) n⁻¹
      rwa [inv_smul_eq_iff.mpr hnα.symm] at this
    have hAL : n⁻¹ • C.line ≠ C.line := fun h1 => hne (by
      calc n • C.line = n • (n⁻¹ • C.line) := by rw [h1]
        _ = C.line := smul_inv_smul n _)
    have h1 : (n * e * n⁻¹) • C.β = C.β := by
      rw [mul_smul, mul_smul, (P.mem_Wl.mp (heWl _ hA hAL)).2 _
        (Set.smul_mem_smul_set C.β_mem_line), smul_inv_smul]
    rw [hconjΓ _ β_mem_Γ] at h1
    exact heβ h1
  have hπ := C.lineActs_lineHom ⟨n, hnL⟩
  set π := C.lineHom ⟨n, hnL⟩
  have hπa : π (C.D.coord C.a C.i) = C.D.coord C.a C.i := by
    refine C.lpt_injective (Subtype.ext ?_)
    rw [← hπ (C.D.coord C.a C.i), C.lpt_coord_a, C.coe_a, hnα]
  have hπN := hπ.mem_normalizer h
  have hπpow : π ^ Nat.card N = 1 := by
    have h1 := hπ.pow (Nat.card N)
    rw [pow_card_eq_one_of_mem hn] at h1
    exact h1.unique C.lineActs_one
  have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hodd
  have hR : ∀ r ∈ seRadical (C.D.M C.i) (C.D.coord C.a C.i), π * r = r * π := by
    intro r hr
    obtain ⟨hrM, hra, -⟩ := (C.isNaturalSE C.i).mem_seRadical_iff.mp hr
    obtain ⟨g, hgℓ, hgr⟩ := h.exists_mem_fixingSubgroup_lineActs hℓ hℓL hrM hra
    have hact : C.LineActs (n * g * n⁻¹ * g⁻¹) (π * r * π⁻¹ * r⁻¹) :=
      ((hπ.mul hgr).mul hπ.inv).mul hgr.inv
    have hwR : π * r * π⁻¹ * r⁻¹ ∈ seRadical (C.D.M C.i) (C.D.coord C.a C.i) :=
      mul_mem (conj_mem_seRadical hπN hπa hr) (inv_mem hr)
    have hw1 : (π * r * π⁻¹ * r⁻¹) ^ Nat.card N = 1 := by
      have h1 := hact.pow (Nat.card N)
      rw [pow_card_eq_one_of_mem (hcomm hgℓ)] at h1
      exact h1.unique C.lineActs_one
    obtain ⟨k, hk⟩ := (C.isNaturalSE C.i).isPGroup_seRadical _ ⟨_, hwR⟩
    have hk' : (π * r * π⁻¹ * r⁻¹) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hord : orderOf (π * r * π⁻¹ * r⁻¹) = 1 := by
      have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hw1)
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k hcop), Nat.dvd_one] at h1
    have hw : π * r * π⁻¹ * r⁻¹ = 1 := orderOf_eq_one_iff.mp hord
    calc π * r = (π * r * π⁻¹ * r⁻¹) * (r * π) := by group
      _ = r * π := by rw [hw, one_mul]
  have hπZ := (C.isNaturalSE C.i).mem_rootCenter_seRadical_of_commute hπN hR
  have hπ2 := (C.isNaturalSE C.i).mul_self_eq_one_of_mem_rootCenter hπZ
  have hπ1 : π = 1 := by
    obtain ⟨a, ha⟩ := hodd
    rw [ha, pow_succ, pow_mul, sq, hπ2, one_pow, one_mul] at hπpow
    exact hπpow
  obtain ⟨ψ, rfl⟩ := hy
  rw [hπ ψ, hπ1, Equiv.Perm.one_apply]

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_smul_α_eq (C : P49Config G Ω α v) {y : Ω} {A : Set Ω}
    (hA : A ∈ linesThrough G C.line y) : ∃ g : G, g • α = y ∧ g • C.line = A := by
  obtain ⟨⟨g₁, rfl⟩, hy⟩ := hA
  obtain ⟨_, ⟨ψ, rfl⟩, hψ⟩ := hy
  obtain ⟨m, hm, hma⟩ := C.exists_mem_M_apply_eq' (C.D.coord C.a C.i) ψ
  obtain ⟨c, -, hcm⟩ := C.exists_lineActs_of_mem hm
  exact ⟨g₁ * c, by rw [mul_smul, hcm.smul_α, hma]; exact hψ, by rw [mul_smul, hcm.smul_line]⟩

theorem P95.le_lineFix_of_odd (h : C.P95) {y : Ω} {L₀ : Set Ω}
    (hL₀ : L₀ ∈ linesThrough G C.line y) {N : Subgroup G} (hNP : N ≤ fixingSubgroup G L₀)
    (hPN : ∀ p ∈ fixingSubgroup G L₀, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N ≤ lineFix G C.line y := by
  intro n hn
  have hny : n • y = y := (mem_fixingSubgroup_iff G).mp (hNP hn) y hL₀.2
  refine mem_lineFix.mpr ⟨hny, fun A hA z hz => ?_⟩
  rcases eq_or_ne A L₀ with rfl | hAL₀
  · exact (mem_fixingSubgroup_iff G).mp (hNP hn) z hz
  obtain ⟨g, hgα, hgA⟩ := exists_smul_α_eq C hA
  have hℓ : g⁻¹ • L₀ ∈ linesThrough G C.line α := by
    have := smul_mem_linesThrough hL₀ g⁻¹
    rwa [← hgα, inv_smul_smul] at this
  have hℓL : g⁻¹ • L₀ ≠ C.line := fun h1 => hAL₀ (by
    rw [← hgA, ← h1, smul_inv_smul])
  set N' : Subgroup G := N.map (MulAut.conj g⁻¹).toMonoidHom
  have hN'P : N' ≤ fixingSubgroup G (g⁻¹ • L₀) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_smul, smul_inv_smul]
    rw [(mem_fixingSubgroup_iff G).mp (hNP hm) w hw]
  have hPN' : ∀ p ∈ fixingSubgroup G (g⁻¹ • L₀), ∀ m ∈ N', p * m * p⁻¹ ∈ N' := by
    rintro p hp _ ⟨m, hm, rfl⟩
    have hp' : g * p * g⁻¹ ∈ fixingSubgroup G L₀ := by
      rw [mem_fixingSubgroup_iff]
      intro w hw
      have h1 := (mem_fixingSubgroup_iff G).mp hp (g⁻¹ • w) (Set.smul_mem_smul_set hw)
      rw [mul_smul, mul_smul, h1, smul_inv_smul]
    refine ⟨g * p * g⁻¹ * m * (g * p * g⁻¹)⁻¹, hPN _ hp' m hm, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hoddN' : Odd (Nat.card N') := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hzL : g⁻¹ • z ∈ C.line := by
    rw [← hgA] at hz
    exact Set.mem_smul_set_iff_inv_smul_mem.mp hz
  have hkey := h.smul_eq_of_odd hℓ hℓL hN'P hPN' hoddN' (n := g⁻¹ * n * g⁻¹⁻¹)
    ⟨n, hn, rfl⟩ hzL
  rw [inv_inv, mul_smul, mul_smul, smul_inv_smul] at hkey
  exact smul_left_cancel _ hkey

theorem P95.lineFix_eq_bot (h : C.P95) (x : Ω) : lineFix G C.line x = ⊥ := by
  have hS := h.setting
  have hpre := hS.preprimitive
  have htr := hS.star.isPretransitive
  obtain ⟨P⟩ := nonempty_p95Data C
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G α x
  set L₀ : Set Ω := g₀ • C.line
  have hL₀ : L₀ ∈ linesThrough G C.line x :=
    ⟨⟨g₀, rfl⟩, hg₀ ▸ Set.smul_mem_smul_set C.α_mem_line⟩
  have hL₀J : IsJClosed G Ω L₀ := (C.isJClosed_line hS h.transitive).smul g₀
  have hother : ∀ {y : Ω}, y ∈ L₀ → ∃ z ∈ L₀, z ≠ y := by
    rintro _ ⟨w, -, rfl⟩
    by_cases hw : w = α
    · exact ⟨g₀ • C.β, Set.smul_mem_smul_set C.β_mem_line, fun h1 =>
        C.ne (hw ▸ (smul_left_cancel g₀ h1)).symm⟩
    · exact ⟨g₀ • α, Set.smul_mem_smul_set C.α_mem_line, fun h1 => hw (smul_left_cancel g₀ h1).symm⟩
  have hoddAt : ∀ {y : Ω}, y ∈ L₀ → Odd (Nat.card (lineFix G C.line y)) := fun {y} hy => by
    obtain ⟨z, hz, hzy⟩ := hother hy
    exact hS.odd_card_lineFix ⟨hL₀.1, hy⟩ hz hzy
  have hle : ∀ {y z : Ω}, y ∈ L₀ → z ∈ L₀ → lineFix G C.line y ≤ lineFix G C.line z :=
    fun {y z} hy hz => h.le_lineFix_of_odd ⟨hL₀.1, hz⟩
      (lineFix_le_fixingSubgroup ⟨hL₀.1, hy⟩)
      (fun p hp m hm => by
        have hpy : p • y = y := (mem_fixingSubgroup_iff G).mp hp y hy
        simpa [hpy] using conj_mem_lineFix hm p)
      (hoddAt hy)
  have hGx : stabilizer G x ≤ Subgroup.normalizer (lineFix G C.line x : Set G) := by
    intro g hg
    have hgx : g • x = x := hg
    have hgx' : g⁻¹ • x = x := mem_stabilizer_iff.mp (Subgroup.inv_mem _ hg)
    refine mem_normalizer_of_conj (fun z hz => ?_) (fun z hz => ?_)
    · have := conj_mem_lineFix hz g
      rwa [hgx] at this
    · have := conj_mem_lineFix hz g⁻¹
      rwa [hgx'] at this
  have hGL : stabilizer G L₀ ≤ Subgroup.normalizer (lineFix G C.line x : Set G) := by
    intro g hg
    have hgx : g • x ∈ L₀ := by
      rw [← mem_stabilizer_iff.mp hg]
      exact Set.smul_mem_smul_set hL₀.2
    have hgx' : g⁻¹ • x ∈ L₀ := by
      rw [← mem_stabilizer_iff.mp (Subgroup.inv_mem _ hg)]
      exact Set.smul_mem_smul_set hL₀.2
    exact mem_normalizer_of_conj (fun z hz => hle hgx hL₀.2 (conj_mem_lineFix hz g))
      (fun z hz => hle hgx' hL₀.2 (conj_mem_lineFix hz g⁻¹))
  obtain ⟨y, hy, hyx⟩ := hother hL₀.2
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq G α y
  have ht : g₁ * P.t * g₁⁻¹ ∈ longInvAt G Ω y := by
    have := conj_mem_longInvAt P.t_mem g₁
    rwa [hg₁] at this
  have htL : g₁ * P.t * g₁⁻¹ ∈ stabilizer G L₀ := hL₀J y hy _ ht
  have hlt : stabilizer G x < Subgroup.normalizer (lineFix G C.line x : Set G) := by
    refine lt_of_le_of_ne hGx fun heq => hyx ?_
    have htx : (g₁ * P.t * g₁⁻¹) • x = x := mem_stabilizer_iff.mp (heq ▸ hGL htL)
    exact ht.1.2.unique ht.2 htx
  have : Nontrivial Ω := ⟨⟨x, y, Ne.symm hyx⟩⟩
  have htop := (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G x).2 _ hlt
  exact eq_bot_of_normal_of_le_stabilizer (Subgroup.normalizer_eq_top_iff.mp htop)
    (fun z hz => (mem_lineFix.mp hz).1)

end Thm55

end P49Config

end CFSG.Holt.H78
