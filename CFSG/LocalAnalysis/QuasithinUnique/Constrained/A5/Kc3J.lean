module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L3

public section

namespace CFSG.QuasithinUnique.A5.Kc3J

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.QuasithinUnique.A5.Kc3Irr
  CFSG.QuasithinUnique.A5.Kc3L3

@[expose] def Delta5Norm {H : Type} [Group H] (V : Subgroup H)
    (β : ↥V ≃* Multiplicative ↥(evenWeight 5)) : Prop :=
  ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → ∃ l : H,
    l ∈ Subgroup.normalizer (V : Set H) ∧ ∀ v w : ↥V, (w : H) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) = Delta5.vact σ (Multiplicative.toAdd (β v))

section Conj

variable {H : Type} [Group H] {V : Subgroup H} (β : ↥V ≃* Multiplicative ↥(evenWeight 5))

theorem pt_mem (u : ↥(evenWeight 5)) : pt β u ∈ V := (β.symm (Multiplicative.ofAdd u)).2

theorem pt_vact {l : H} (hl : l ∈ Subgroup.normalizer (V : Set H)) {σ : Equiv.Perm (Fin 5)}
    (hact : ∀ v w : ↥V, (w : H) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) = Delta5.vact σ (Multiplicative.toAdd (β v)))
    (u : ↥(evenWeight 5)) : pt β (Delta5.vact σ u) = l * pt β u * l⁻¹ := by
  set v : ↥V := β.symm (Multiplicative.ofAdd u) with hv
  have hmem : l * (v : H) * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hl (v : H)).1 v.2
  let w' : ↥V := ⟨l * v * l⁻¹, hmem⟩
  have h1 := hact v w' rfl
  have h2 : β w' = Multiplicative.ofAdd (Delta5.vact σ u) := by
    rw [← ofAdd_toAdd (β w'), h1]
    simp [hv]
  have h3 : w' = β.symm (Multiplicative.ofAdd (Delta5.vact σ u)) := by
    rw [← h2]
    simp
  show ((β.symm (Multiplicative.ofAdd (Delta5.vact σ u)) : ↥V) : H) = l * (v : H) * l⁻¹
  rw [← h3]

end Conj

section Generic

variable {F : Type} [Field F] {M : Type*} [AddCommGroup M] [Module F M]

@[expose] noncomputable def PsiG (A : Fin 5 → M) : (Fin 5 → F) →ₗ[F] M :=
  ∑ i, (LinearMap.proj i : (Fin 5 → F) →ₗ[F] F).smulRight (A i)

theorem PsiG_apply (A : Fin 5 → M) (x : Fin 5 → F) : PsiG A x = ∑ i, x i • A i := by
  simp [PsiG, LinearMap.sum_apply]

end Generic

section Core

variable {F : Type} [Field F] [CharP F 2] {W : Type} [AddCommGroup W] [Module F W]
  {H : Type} [Group H] {V : Subgroup H} (β : ↥V ≃* Multiplicative ↥(evenWeight 5))
  (ρ : H →* Module.End F W)

@[expose] noncomputable def Nw (u : ↥(evenWeight 5)) : Module.End F W := ρ (pt β u) - 1

omit [CharP F 2] in
theorem Nw_apply (u : ↥(evenWeight 5)) (w : W) : Nw β ρ u w = ρ (pt β u) w - w := by
  simp [Nw]

omit [CharP F 2] in
theorem Nw_add (u u' : ↥(evenWeight 5)) :
    Nw β ρ (u + u') = Nw β ρ u + Nw β ρ u' + Nw β ρ u * Nw β ρ u' := by
  unfold Nw
  rw [pt_add, map_mul]
  noncomm_ring

omit [CharP F 2] in
theorem Nw_conj {l : H} (hl : l ∈ Subgroup.normalizer (V : Set H)) {σ : Equiv.Perm (Fin 5)}
    (hact : ∀ v w : ↥V, (w : H) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) = Delta5.vact σ (Multiplicative.toAdd (β v)))
    (u : ↥(evenWeight 5)) :
    Nw β ρ (Delta5.vact σ u) = ρ l * Nw β ρ u * ρ l⁻¹ := by
  have h : ρ l * ρ l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  unfold Nw
  rw [pt_vact β hl hact u, map_mul, map_mul, mul_sub, sub_mul, mul_one, h]

@[expose] noncomputable def Ai (i : Fin 5) : Module.End F W := Nw β ρ (gen2 i)

@[expose] noncomputable def Psi : (Fin 5 → F) →ₗ[F] Module.End F W := PsiG (Ai β ρ)

omit [CharP F 2] in
theorem Psi_apply_vec (x : Fin 5 → F) (w : W) : Psi β ρ x w = ∑ i, x i • Ai β ρ i w := by
  simp [Psi, PsiG_apply, LinearMap.sum_apply]

end Core

section Flag

variable {F : Type} [Field F] [CharP F 2] {W : Type} [AddCommGroup W] [Module F W]
  {H : Type} [Group H] {V : Subgroup H} (β : ↥V ≃* Multiplicative ↥(evenWeight 5))
  (ρ : H →* Module.End F W)

omit [CharP F 2] in
theorem mem_fix1 {R : Subgroup H} {w : W} : w ∈ fixFlag ρ R 1 ↔ ∀ g ∈ R, ρ g w = w := by
  rw [mem_fixFlag_succ]
  simp only [fixFlag_zero, Submodule.mem_bot, sub_eq_zero]

omit [CharP F 2] in
theorem fixFlag_stab {R : Subgroup H} {k : ℕ} (h : fixFlag ρ R (k + 1) = fixFlag ρ R k) :
    ∀ j, fixFlag ρ R (k + j) = fixFlag ρ R k ∧ fixFlag ρ R (k + j + 1) = fixFlag ρ R k := by
  intro j
  induction j with
  | zero => exact ⟨rfl, h⟩
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have e : fixFlag ρ R (k + j + 1 + 1) = fixFlag ρ R (k + 1) := by
      ext v
      rw [mem_fixFlag_succ, mem_fixFlag_succ, ih.2]
    exact e.trans h

theorem fixFlag_top_of_stab [Finite W] {R : Subgroup H} (hR : IsPGroup 2 R) {k : ℕ}
    (h : fixFlag ρ R (k + 1) = fixFlag ρ R k) : fixFlag ρ R k = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := exists_fixFlag_eq_top ρ 2 R hR
  rcases le_total m k with hmk | hkm
  · have := fixFlag_mono ρ R hmk
    rw [hm] at this
    exact top_le_iff.1 this
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
    rw [← (fixFlag_stab ρ h j).1]
    exact hm

omit [CharP F 2] in
theorem Nw_mem_fix1 {w : W} (hw : w ∈ fixFlag ρ V 2) (u : ↥(evenWeight 5)) :
    Nw β ρ u w ∈ fixFlag ρ V 1 := by
  rw [Nw_apply]
  exact (mem_fixFlag_succ ρ).1 hw (pt β u) (pt_mem β u)

omit [CharP F 2] in
theorem Nw_fix1 {c : W} (hc : c ∈ fixFlag ρ V 1) (u : ↥(evenWeight 5)) : Nw β ρ u c = 0 := by
  rw [Nw_apply, (mem_fix1 ρ).1 hc (pt β u) (pt_mem β u), sub_self]

omit [CharP F 2] in
theorem Nw_add_apply {u u' : ↥(evenWeight 5)} {w : W} (hw : w ∈ fixFlag ρ V 2) :
    Nw β ρ (u + u') w = Nw β ρ u w + Nw β ρ u' w := by
  have h3 : Nw β ρ u (Nw β ρ u' w) = 0 := Nw_fix1 β ρ (Nw_mem_fix1 β ρ hw u') u
  rw [Nw_add]
  simp [LinearMap.add_apply, h3, Module.End.mul_apply]

theorem Nw_eq_Psi {w : W} (hw : w ∈ fixFlag ρ V 2) (u : ↥(evenWeight 5)) :
    Nw β ρ u w = Psi β ρ (emb u) w := by
  classical
  let Tm : ↥(evenWeight 5) →+ W :=
    AddMonoidHom.mk' (fun u => Nw β ρ u w) (fun u u' => Nw_add_apply β ρ hw)
  have hsum : u = ∑ i ∈ Finset.univ.filter (fun i : Fin 5 => u.1 i = 1), gen2 i := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact decomp2 u.1 u.2
  have h1 : Nw β ρ u w =
      ∑ i ∈ Finset.univ.filter (fun i : Fin 5 => u.1 i = 1), Nw β ρ (gen2 i) w := by
    have := map_sum Tm gen2 (Finset.univ.filter (fun i : Fin 5 => u.1 i = 1))
    rw [← hsum] at this
    exact this
  rw [h1, Psi_apply_vec, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : u.1 i = 0 ∨ u.1 i = 1 := by
    generalize u.1 i = a
    revert a
    decide
  rcases hz with h | h
  · simp [emb, h]
  · simp [emb, h, Ai]

theorem Psi_conj {σ : Equiv.Perm (Fin 5)} {l : H} (hl : l ∈ Subgroup.normalizer (V : Set H))
    (hact : ∀ v w : ↥V, (w : H) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) = Delta5.vact σ (Multiplicative.toAdd (β v)))
    {x : Fin 5 → F} (hx : x ∈ (delta5 : Submodule F (Fin 5 → F))) {w : W}
    (hw : w ∈ fixFlag ρ V 2) :
    Psi β ρ (pactF σ x) w = ρ l (Psi β ρ x (ρ l⁻¹ w)) := by
  have hw' : ρ l⁻¹ w ∈ fixFlag ρ V 2 :=
    ((normalizer_le_flagStab_fixFlag ρ V) hl) 2 w hw |>.2
  have hgen : ∀ i, Psi β ρ (pactF σ (gen i)) w = ρ l (Psi β ρ (gen i) (ρ l⁻¹ w)) := by
    intro i
    rw [← emb_gen2, pactF_emb, ← Nw_eq_Psi β ρ hw, ← Nw_eq_Psi β ρ hw', Nw_conj β ρ hl hact]
    simp [Module.End.mul_apply]
  have h1 : Psi β ρ (pactF σ x) w = ∑ i, x i • Psi β ρ (pactF σ (gen i)) w := by
    conv_lhs => rw [decomp hx]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : ρ l (Psi β ρ x (ρ l⁻¹ w)) =
      ∑ i, x i • ρ l (Psi β ρ (gen i) (ρ l⁻¹ w)) := by
    conv_lhs => rw [decomp hx]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun i _ => by rw [hgen i]

@[expose] def Kset : Submodule F (Fin 5 → F) where
  carrier := {x | x ∈ (delta5 : Submodule F (Fin 5 → F)) ∧
    ∀ w ∈ fixFlag ρ V 2, Psi β ρ x w = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun w hw => by
      rw [map_add, LinearMap.add_apply, ha' w hw, hb' w hw, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun w _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨Submodule.smul_mem _ c ha, fun w hw => by
      rw [map_smul, LinearMap.smul_apply, ha' w hw, smul_zero]⟩

theorem Kset_dichotomy (hact : Delta5Norm V β) :
    Kset β ρ = ⊥ ∨ Kset β ρ = (delta5 : Submodule F (Fin 5 → F)) := by
  by_cases hK : Kset β ρ = ⊥
  · exact Or.inl hK
  · right
    refine irr_delta5 (fun x hx => hx.1) ?_ hK
    intro σ hσ x hx
    obtain ⟨l, hl, hact'⟩ := hact σ hσ
    refine ⟨pactF_mem_delta5 σ hx.1, fun w hw => ?_⟩
    have hw' : ρ l⁻¹ w ∈ fixFlag ρ V 2 :=
      ((normalizer_le_flagStab_fixFlag ρ V) hl) 2 w hw |>.2
    rw [Psi_conj β ρ hl hact' hx.1 hw, hx.2 _ hw', map_zero]

theorem Kset_ne_top [Finite W] (hVp : IsPGroup 2 ↥V) (hnt : ∀ v : ↥V, ρ v = 1 → v = 1) :
    Kset β ρ ≠ (delta5 : Submodule F (Fin 5 → F)) := by
  intro hK
  have h0 : ∀ u : ↥(evenWeight 5), ∀ w ∈ fixFlag ρ V 2, Nw β ρ u w = 0 := by
    intro u w hw
    rw [Nw_eq_Psi β ρ hw u]
    have : emb u ∈ Kset β ρ := by rw [hK]; exact emb_mem u
    exact this.2 w hw
  have hC21 : fixFlag ρ V 2 ≤ fixFlag ρ V 1 := by
    intro w hw
    rw [mem_fix1]
    intro g hg
    have := h0 (Multiplicative.toAdd (β ⟨g, hg⟩)) w hw
    rw [Nw_apply, sub_eq_zero] at this
    have hpt : pt β (Multiplicative.toAdd (β ⟨g, hg⟩)) = g := by simp [pt]
    rwa [hpt] at this
  have hstab : fixFlag ρ V (1 + 1) = fixFlag ρ V 1 := le_antisymm hC21 (fixFlag_le_succ ρ V 1)
  have htop : fixFlag ρ V 1 = ⊤ := fixFlag_top_of_stab ρ hVp hstab
  let w₀ : ↥(evenWeight 5) := ⟨Delta5.w0, Delta5.w0_mem⟩
  have h1 : ρ (pt β w₀) = 1 := by
    refine LinearMap.ext fun w => ?_
    have hw : w ∈ fixFlag ρ V 1 := by rw [htop]; trivial
    rw [Module.End.one_apply]
    exact (mem_fix1 ρ).1 hw (pt β w₀) (pt_mem β w₀)
  have h2 : (⟨pt β w₀, pt_mem β w₀⟩ : ↥V) = 1 := hnt _ h1
  exact pt_ne_one β (congrArg Subtype.val h2)

theorem partA [Finite F] [Finite W] [Module.Finite F W] (hW4 : Module.finrank F W = 4)
    (hVp : IsPGroup 2 ↥V) (hnt : ∀ v : ↥V, ρ v = 1 → v = 1) (hact : Delta5Norm V β) :
    ∃ (C : Submodule F W) (A : Fin 5 → Module.End F W), Module.finrank F C = 2 ∧
      (∀ i w, A i w ∈ C) ∧ (∀ i, ∀ c ∈ C, A i c = 0) ∧ (∀ i, ∃ g ∈ V, A i = ρ g - 1) ∧
      ∀ M : Module.End F W, (∀ w, M w ∈ C) → (∀ c ∈ C, M c = 0) →
        ∃ x : Fin 5 → F, ∀ w, M w = ∑ i, x i • A i w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hK0 : Kset β ρ = ⊥ := (Kset_dichotomy β ρ hact).resolve_right (Kset_ne_top β ρ hVp hnt)
  set C₁ := fixFlag ρ V 1 with hC₁def
  set C₂ := fixFlag ρ V 2 with hC₂def
  have hC12 : C₁ ≤ C₂ := fixFlag_le_succ ρ V 1
  obtain ⟨v₀, hv₀, hv₀fix⟩ := exists_fixed_ne_zero ρ 2 V hVp
  have ha1 : 1 ≤ Module.finrank F C₁ := by
    have hne : C₁ ≠ ⊥ := by
      intro h
      have : v₀ ∈ C₁ := (mem_fix1 ρ).2 hv₀fix
      rw [h, Submodule.mem_bot] at this
      exact hv₀ this
    exact Submodule.one_le_finrank_iff.2 hne
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl C₁
  set D₂ : Submodule F W := D ⊓ C₂ with hD₂def
  have hC₂eq : C₂ = C₁ ⊔ D₂ := by
    have h1 : (C₁ ⊔ D) ⊓ C₂ = C₁ ⊔ D ⊓ C₂ := sup_inf_assoc_of_le D hC12
    rw [hD.sup_eq_top, top_inf_eq] at h1
    exact h1
  have hdisj : Disjoint C₁ D₂ := hD.disjoint.mono_right inf_le_left
  have hc₂ : Module.finrank F C₂ = Module.finrank F C₁ + Module.finrank F D₂ := by
    have := Submodule.finrank_sup_add_finrank_inf_eq C₁ D₂
    rw [hdisj.eq_bot, finrank_bot, add_zero, ← hC₂eq] at this
    exact this
  have hc₂le : Module.finrank F C₂ ≤ 4 := hW4 ▸ Submodule.finrank_le C₂
  have hmapsD : ∀ i, ∀ d ∈ D₂, Ai β ρ i d ∈ C₁ := fun i d hd =>
    Nw_mem_fix1 β ρ hd.2 (gen2 i)
  let f : Fin 5 → (↥D₂ →ₗ[F] ↥C₁) := fun i => (Ai β ρ i).restrict (p := D₂) (q := C₁) (hmapsD i)
  let Φ : (Fin 5 → F) →ₗ[F] (↥D₂ →ₗ[F] ↥C₁) := PsiG f
  have hΦ : ∀ x d, ((Φ x d : ↥C₁) : W) = Psi β ρ x (d : W) := by
    intro x d
    simp [Φ, PsiG_apply, Psi_apply_vec, f, LinearMap.sum_apply]
  have hΦinj : ∀ x ∈ (delta5 : Submodule F (Fin 5 → F)), Φ x = 0 → x = 0 := by
    intro x hx h0
    have hxK : x ∈ Kset β ρ := by
      refine ⟨hx, fun w hw => ?_⟩
      have hw' : w ∈ C₁ ⊔ D₂ := by rw [← hC₂eq]; exact hw
      obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 hw'
      have hc0 : Psi β ρ x c = 0 := by
        rw [Psi_apply_vec]
        exact Finset.sum_eq_zero fun i _ => by rw [Ai, Nw_fix1 β ρ hc, smul_zero]
      have hd0 : Psi β ρ x d = 0 := by
        have := hΦ x ⟨d, hd⟩
        rw [h0] at this
        simpa using this.symm
      rw [map_add, hc0, hd0, add_zero]
    rw [hK0] at hxK
    exact (Submodule.mem_bot F).1 hxK
  have hinjD : Function.Injective (Φ.domRestrict (delta5 : Submodule F (Fin 5 → F))) := by
    intro x y hxy
    have h1 : Φ ((x : Fin 5 → F) - (y : Fin 5 → F)) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 hxy
    have := hΦinj _ (sub_mem x.2 y.2) h1
    exact Subtype.ext (sub_eq_zero.1 this)
  have hdim : Module.finrank F (delta5 : Submodule F (Fin 5 → F)) ≤
      Module.finrank F (↥D₂ →ₗ[F] ↥C₁) :=
    LinearMap.finrank_le_finrank_of_injective hinjD
  rw [finrank_delta5, Module.finrank_linearMap] at hdim
  have key : Module.finrank F C₁ = 2 ∧ Module.finrank F D₂ = 2 := by
    have h1 := hdim
    have h2 := hc₂
    have h3 := hc₂le
    have h4 := ha1
    generalize Module.finrank F C₁ = a at h1 h2 h3 h4 ⊢
    generalize Module.finrank F D₂ = d at h1 h2 h3 h4 ⊢
    generalize Module.finrank F C₂ = c at h1 h2 h3 h4 ⊢
    have ha4 : a ≤ 4 := by omega
    interval_cases a <;> omega
  have hC₂top : C₂ = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hc₂, key.1, key.2, hW4])
  have hsurj : Function.Surjective (Φ.domRestrict (delta5 : Submodule F (Fin 5 → F))) := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hinjD
    · rw [finrank_delta5, Module.finrank_linearMap, key.1, key.2]
  refine ⟨C₁, Ai β ρ, key.1, ?_, ?_, ?_, ?_⟩
  · intro i w
    have hw : w ∈ C₂ := by rw [hC₂top]; trivial
    exact Nw_mem_fix1 β ρ hw (gen2 i)
  · intro i c hc
    exact Nw_fix1 β ρ hc (gen2 i)
  · intro i
    exact ⟨pt β (gen2 i), pt_mem β _, rfl⟩
  · intro M hM1 hM0
    let φM : ↥D₂ →ₗ[F] ↥C₁ := (M.comp D₂.subtype).codRestrict C₁ (fun d => hM1 d)
    obtain ⟨⟨x, hx⟩, hxΦ⟩ := hsurj φM
    refine ⟨x, fun w => ?_⟩
    have hw : w ∈ C₁ ⊔ D₂ := by rw [← hC₂eq, hC₂top]; trivial
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 hw
    have hxd : Psi β ρ x d = M d := by
      have h1 := hΦ x ⟨d, hd⟩
      have h2 : Φ x ⟨d, hd⟩ = φM ⟨d, hd⟩ := by
        have := congrArg (fun ψ => ψ ⟨d, hd⟩) hxΦ
        simpa using this
      rw [h2] at h1
      exact h1.symm.trans (rfl : ((φM ⟨d, hd⟩ : ↥C₁) : W) = M d)
    rw [map_add, hM0 c hc, zero_add, ← hxd, Psi_apply_vec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, show Ai β ρ i c = 0 from Nw_fix1 β ρ hc (gen2 i), zero_add]

end Flag

section Symp

variable {F : Type} [Field F] [CharP F 2] {W : Type} [AddCommGroup W] [Module F W]

theorem no_symplectic [Module.Finite F W] (hW4 : Module.finrank F W = 4)
    (B : LinearMap.BilinForm F W) (hsymm : ∀ x y, B x y = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (C : Submodule F W) (hC : Module.finrank F C = 2) (A : Fin 5 → Module.End F W)
    (hAC : ∀ i w, A i w ∈ C) (hA0 : ∀ i, ∀ c ∈ C, A i c = 0)
    (hAsp : ∀ i x y, B (x + A i x) (y + A i y) = B x y)
    (hspan : ∀ M : Module.End F W, (∀ w, M w ∈ C) → (∀ c ∈ C, M c = 0) →
      ∃ x : Fin 5 → F, ∀ w, M w = ∑ i, x i • A i w) : False := by
  have E1 : ∀ i x y, B x (A i y) + B (A i x) y + B (A i x) (A i y) = 0 := by
    intro i x y
    have h := hAsp i x y
    simp only [map_add, LinearMap.add_apply] at h
    linear_combination h
  have hCperp : ∀ i, ∀ c ∈ C, ∀ y, B c (A i y) = 0 := by
    intro i c hc y
    have h := E1 i c y
    simpa [hA0 i c hc] using h
  have hCperpM : ∀ M : Module.End F W, (∀ w, M w ∈ C) → (∀ c ∈ C, M c = 0) →
      ∀ c ∈ C, ∀ y, B c (M y) = 0 := by
    intro M hM1 hM0 c hc y
    obtain ⟨x, hx⟩ := hspan M hM1 hM0
    rw [hx y, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hCperp i c hc y, smul_zero]
  have hlt : C < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, finrank_top, hW4] at hC
    omega
  obtain ⟨f, hf0, hCf⟩ := Submodule.exists_le_ker_of_lt_top C hlt
  obtain ⟨y₀, hy₀⟩ := DFunLike.ne_iff.1 hf0
  have hy₀' : f y₀ ≠ 0 := by simpa using hy₀
  have hiso : ∀ c₁ ∈ C, ∀ c₂ ∈ C, B c₁ c₂ = 0 := by
    intro c₁ hc₁ c₂ hc₂
    let f' : W →ₗ[F] F := (f y₀)⁻¹ • f
    have hf'y : f' y₀ = 1 := by
      simp [f', inv_mul_cancel₀ hy₀']
    have hf'C : ∀ c ∈ C, f' c = 0 := by
      intro c hc
      have : c ∈ LinearMap.ker f := hCf hc
      simp [f', LinearMap.mem_ker.1 this]
    let M : Module.End F W := f'.smulRight c₂
    have hM1 : ∀ w, M w ∈ C := fun w => Submodule.smul_mem _ _ hc₂
    have hM0 : ∀ c ∈ C, M c = 0 := fun c hc => by simp [M, hf'C c hc]
    have := hCperpM M hM1 hM0 c₁ hc₁ y₀
    simpa [M, hf'y] using this
  have hsymA : ∀ i y z, B (A i y) z = B y (A i z) := by
    intro i y z
    have h := E1 i y z
    have hz : B (A i y) (A i z) = 0 := hiso _ (hAC i y) _ (hAC i z)
    rw [hz, add_zero] at h
    have h' : B (A i y) z = - B y (A i z) := by linear_combination h
    rw [h', CharTwo.neg_eq]
  have hsymM : ∀ M : Module.End F W, (∀ w, M w ∈ C) → (∀ c ∈ C, M c = 0) →
      ∀ y z, B (M y) z = B y (M z) := by
    intro M hM1 hM0 y z
    obtain ⟨x, hx⟩ := hspan M hM1 hM0
    have h1 : B (M y) z = ∑ i, x i * B (A i y) z := by
      rw [hx y]
      simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    have h2 : B y (M z) = ∑ i, x i * B y (A i z) := by
      rw [hx z]
      simp [map_sum, map_smul]
    rw [h1, h2]
    exact Finset.sum_congr rfl fun i _ => by rw [hsymA i y z]
  have hCne : C ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hC
    omega
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCne
  have hspanle : ∃ c' ∈ C, c' ∉ Submodule.span F {c} := by
    by_contra hcon
    push Not at hcon
    have hle : C ≤ Submodule.span F {c} := hcon
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hc0] at h1
    omega
  obtain ⟨c', hc', hc'span⟩ := hspanle
  have hy : ∃ y, B c y = 1 := by
    by_contra hcon
    push Not at hcon
    apply hc0
    apply hnd c
    intro y
    by_contra hy
    apply hcon ((B c y)⁻¹ • y)
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  obtain ⟨y, hy⟩ := hy
  let M : Module.End F W := (B c').smulRight c
  have hM1 : ∀ w, M w ∈ C := fun w => Submodule.smul_mem _ _ hc
  have hM0 : ∀ z ∈ C, M z = 0 := fun z hz => by simp [M, hiso c' hc' z hz]
  have hsy := hsymM M hM1 hM0 y
  have hcomb : ∀ z, B c' z = B c' y * B c z := by
    intro z
    have h := hsy z
    simp only [M, LinearMap.smulRight_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [hsymm y c, hy, mul_one] at h
    exact h.symm
  have h0 : c' - (B c' y) • c = 0 := by
    apply hnd
    intro z
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hcomb z,
      sub_self]
  apply hc'span
  have h1 : c' = (B c' y) • c := sub_eq_zero.1 h0
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)

end Symp

theorem delta5Norm_of_d5 {G : Type} [Group G] {K L V Q : Subgroup G} (hLK : L ≤ K) (hVQ : V ≤ Q)
    (hQL : Q ≤ L) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α)
    (β : ↥V ≃* Multiplicative ↥(evenWeight 5))
    (hβ : ∀ (l : ↥L) (v w : ↥V), (w : G) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) =
        Delta5.vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          (Multiplicative.toAdd (β v))) :
    Delta5Norm (V.subgroupOf K)
      ((Subgroup.subgroupOfEquivOfLe (hVQ.trans (hQL.trans hLK))).trans β) := by
  intro σ hσ
  have hρA : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hσ
  obtain ⟨l, hl⟩ := hα ⟨σ, hρA⟩
  have hlρ : ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = σ :=
    congrArg Subtype.val hl
  have hlK : (l : G) ∈ K := hLK l.2
  refine ⟨⟨(l : G), hlK⟩, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro n
    have h := Subgroup.mem_normalizer_iff.1 (hLV l.2) ((n : ↥K) : G)
    show ((n : ↥K) : G) ∈ V ↔ ((⟨(l : G), hlK⟩ * n * ⟨(l : G), hlK⟩⁻¹ : ↥K) : G) ∈ V
    simpa using h
  · intro v w hw
    have hvG : ((v : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
    have hwG : ((w : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 w.2
    have hw' : ((w : ↥K) : G) = l * ((v : ↥K) : G) * l⁻¹ := by
      have := congrArg Subtype.val hw
      simpa using this
    have := hβ l ⟨_, hvG⟩ ⟨_, hwG⟩ hw'
    rw [hlρ] at this
    exact this

end CFSG.QuasithinUnique.A5.Kc3J
