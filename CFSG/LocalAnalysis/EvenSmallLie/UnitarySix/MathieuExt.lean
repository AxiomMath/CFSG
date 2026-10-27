module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.MathieuExtDesign
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut
public import CFSG.Monster.B.TwoA.Fischer.M22Aut

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.MathieuExt

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane CFSG.Fischer
open scoped Pointwise MatrixGroups

theorem M22_subgroupOf_normal
    : (M22.subgroupOf hexadAut).Normal :=
  Subgroup.normal_of_index_eq_two card_hexadAut.2

theorem conj_mem_M22
    {g m : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) (hm : m ∈ M22) :
    g * m * g⁻¹ ∈ M22 := by
  have := M22_subgroupOf_normal.conj_mem ⟨m, M22_le_hexadAut hm⟩
    (by rwa [Subgroup.mem_subgroupOf]) ⟨g, hg⟩
  rwa [Subgroup.mem_subgroupOf] at this

theorem eq_M22_of_le_hexadAut
    {K : Subgroup (Equiv.Perm (Fin 22))} (hK : K ≤ hexadAut)
    (hcard : Nat.card K = 443520) : K = M22 := by
  obtain ⟨hA, hM⟩ := card_hexadAut
  have hKidx : (K.subgroupOf hexadAut).index = 2 := by
    have h := Subgroup.card_mul_index (K.subgroupOf hexadAut)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv, hcard, hA] at h
    omega
  have hKn : (K.subgroupOf hexadAut).Normal := Subgroup.normal_of_index_eq_two hKidx
  have hsimple : IsSimpleGroup M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hnorm : (K.subgroupOf M22).Normal := by
    constructor
    intro k hk m
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have := hKn.conj_mem ⟨k, M22_le_hexadAut k.2⟩ (by rwa [Subgroup.mem_subgroupOf])
      ⟨m, M22_le_hexadAut m.2⟩
    rwa [Subgroup.mem_subgroupOf] at this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf M22) with h | h
  ·
    exfalso
    have hbot : K.subgroupOf hexadAut ⊓ M22.subgroupOf hexadAut = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
      have : (⟨x, hx.2⟩ : M22) ∈ K.subgroupOf M22 := by
        rw [Subgroup.mem_subgroupOf]
        exact hx.1
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      have h' : (x : Equiv.Perm (Fin 22)) = 1 := congrArg Subtype.val this
      exact Subtype.ext h'
    have hle := Subgroup.index_inf_le (H := K.subgroupOf hexadAut) (K := M22.subgroupOf hexadAut)
    rw [hbot, Subgroup.index_bot, hA, hKidx, show (M22.subgroupOf hexadAut).index = 2 from hM]
      at hle
    omega
  ·
    have hle : M22 ≤ K := fun m hm => by
      have : (⟨m, hm⟩ : M22) ∈ K.subgroupOf M22 := h ▸ Subgroup.mem_top _
      rwa [Subgroup.mem_subgroupOf] at this
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_M22'])).symm

theorem eq_one_of_commute_M22
    {g : Equiv.Perm (Fin 22)} (hg : ∀ m ∈ M22, g * m = m * g) :
    g = 1 := by
  refine Equiv.ext fun a => ?_
  by_contra hne
  change g a ≠ a at hne
  obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 22, c ≠ a ∧ c ≠ g a := by
    by_contra hc
    push Not at hc
    have hsub : (Finset.univ : Finset (Fin 22)) ⊆ {a, g a} := fun x _ => by
      by_cases hx : x = a
      · simp [hx]
      · simp [hc x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have := Finset.card_le_two (a := a) (b := g a)
    omega
  obtain ⟨h, hh, hhb⟩ := exists_mem_stabilizer_smul_eq a hne hca
  have hha : (h : Equiv.Perm (Fin 22)) a = a := hh
  have e := congrArg (fun σ : Equiv.Perm (Fin 22) => σ a) (hg h h.2)
  simp only [Equiv.Perm.mul_apply, hha] at e
  exact hcb (hhb.symm.trans e.symm)

@[expose] def conjAut
    (g : hexadAut) : MulAut M22 where
  toFun m := ⟨(g : Equiv.Perm (Fin 22)) * m * (g : Equiv.Perm (Fin 22))⁻¹, conj_mem_M22 g.2 m.2⟩
  invFun m := ⟨(g : Equiv.Perm (Fin 22))⁻¹ * m * (g : Equiv.Perm (Fin 22)), by
    simpa using conj_mem_M22 (inv_mem g.2) m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' m m' := Subtype.ext (by simp [mul_assoc])

theorem coe_conjAut_apply
    (g : hexadAut) (m : M22) :
    ((conjAut g m : M22) : Equiv.Perm (Fin 22)) =
      (g : Equiv.Perm (Fin 22)) * m * (g : Equiv.Perm (Fin 22))⁻¹ := rfl

@[expose] def conjHom :
    hexadAut →* MulAut M22 where
  toFun := conjAut
  map_one' := MulEquiv.ext fun m => Subtype.ext (by simp [coe_conjAut_apply])
  map_mul' g h := MulEquiv.ext fun m => Subtype.ext (by
    simp only [MulAut.mul_apply, coe_conjAut_apply, Subgroup.coe_mul, mul_inv_rev, mul_assoc])

theorem conjHom_injective :
    Function.Injective conjHom := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine Subtype.ext (eq_one_of_commute_M22 fun m hm => ?_)
  have := congrArg (fun φ : MulAut M22 => ((φ ⟨m, hm⟩ : M22) : Equiv.Perm (Fin 22))) hg
  change (g : Equiv.Perm (Fin 22)) * m * (g : Equiv.Perm (Fin 22))⁻¹ = m at this
  calc (g : Equiv.Perm (Fin 22)) * m
      = (g : Equiv.Perm (Fin 22)) * m * (g : Equiv.Perm (Fin 22))⁻¹ * g := by
        rw [inv_mul_cancel_right]
    _ = m * g := by rw [this]

theorem natCard_mulAut_M22
    : Nat.card (MulAut M22) = 887040 :=
  CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.1

@[expose] def hexadAutEquiv :
    hexadAut ≃* MulAut M22 :=
  have : Finite (MulAut M22) := Nat.finite_of_card_ne_zero (by rw [natCard_mulAut_M22]; norm_num)
  MulEquiv.ofBijective conjHom (conjHom_injective.bijective_of_nat_card_le
    (by rw [natCard_mulAut_M22, card_hexadAut.1]))

section Embedding

variable {N : Type*} [Group N] {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MulAction N Ω]

@[expose] def permHom (f : Ω ≃ Fin 22) : N →* Equiv.Perm (Fin 22) :=
  (Equiv.permCongrHom f).toMonoidHom.comp (MulAction.toPermHom N Ω)

omit [Fintype Ω] [DecidableEq Ω] in
theorem permHom_apply (f : Ω ≃ Fin 22) (n : N) (x : Fin 22) :
    permHom f n x = f (n • f.symm x) := rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem permHom_injective [FaithfulSMul N Ω] (f : Ω ≃ Fin 22) :
    Function.Injective (permHom (N := N) f) := by
  intro n m h
  refine eq_of_smul_eq_smul (α := Ω) fun x => ?_
  have := congrArg (fun σ : Equiv.Perm (Fin 22) => σ (f x)) h
  simpa [permHom_apply] using this

omit [Fintype Ω] in
theorem permHom_mem_hexadAut {𝓑 : Finset (Finset Ω)} {f : Ω ≃ Fin 22}
    (hf : ∀ B, B ∈ 𝓑 ↔ B.map f.toEmbedding ∈ hexads) (hinv : ∀ n : N, ∀ B ∈ 𝓑, n • B ∈ 𝓑)
    (n : N) : permHom f n ∈ hexadAut := by
  refine mem_hexadAut_of fun C hC => ?_
  have hB : C.map f.symm.toEmbedding ∈ 𝓑 := by
    rw [hf, Finset.map_map]
    simpa using hC
  have h1 := (hf _).1 (hinv n _ hB)
  convert h1 using 1
  ext y
  rw [Finset.mem_map_equiv, Finset.mem_map_equiv, ← Finset.inv_smul_mem_iff,
    Finset.mem_map_equiv, Equiv.symm_symm, ← Equiv.Perm.inv_def, ← map_inv, permHom_apply]

omit [DecidableEq Ω] in
theorem card_eq_mul_card_stabilizer [IsPretransitive N Ω] (hΩ : Fintype.card Ω = 22) (o : Ω) :
    Nat.card N = 22 * Nat.card (stabilizer N o) := by
  have h := (stabilizer N o).card_mul_index
  rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ, Nat.card_eq_fintype_card (α := Ω), hΩ]
    at h
  linarith

end Embedding

section Main

variable {N : Type*} [Group N] {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MulAction N Ω]
  [FaithfulSMul N Ω] [IsPretransitive N Ω]
  {P : Type*} [Fintype P] [DecidableEq P] {𝓛 : Finset (Finset P)} {o : Ω} {ι : P → Ω}

theorem mathieu_of_extension_abstract
    (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o)
    (hA : ∀ n : N, n • o = o → ∃ σ ∈ blockAut 𝓛, ∀ p, n • ι p = ι (σ p))
    (hB : ∀ L ∈ 𝓛, ∃ n : N, n • o = o ∧ n * n = 1 ∧ ∀ p, n • ι p = ι p ↔ p ∈ L)
    (hC : 20160 ≤ Nat.card (stabilizer N o)) :
    Nat.card N = 22 * Nat.card (stabilizer N o) ∧
    ∃ f : Ω ≃ Fin 22, (∀ L ∈ 𝓛, (insert o (L.map ⟨ι, hι⟩)).map f.toEmbedding ∈ hexads) ∧
      ((Nat.card N = 443520 ∧ (permHom (N := N) f).range = M22) ∨
        (Nat.card N = 887040 ∧ (permHom (N := N) f).range = hexadAut)) := by
  have hfin : Finite N := Finite.of_injective _ (MulAction.toPerm_injective (α := N) (β := Ω))
  obtain ⟨𝓑, h𝓑, hinv, hlines⟩ := exists_steinerTriple hΩ h𝓛 hι hιo hA hB
  obtain ⟨f, hf⟩ := steinerTriple_iso h𝓑 isSteinerTriple_hexads
  have hcardN := card_eq_mul_card_stabilizer (N := N) hΩ o
  refine ⟨hcardN, f, fun L hL => (hf _).1 (hlines L hL), ?_⟩
  have hle : (permHom (N := N) f).range ≤ hexadAut := by
    rintro _ ⟨n, rfl⟩
    exact permHom_mem_hexadAut hf hinv n
  have hrange : Nat.card (permHom (N := N) f).range = Nat.card N :=
    (Nat.card_congr (MonoidHom.ofInjective (permHom_injective (N := N) f)).toEquiv).symm
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hrange, card_hexadAut.1] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : k ≤ 2 := by nlinarith
  interval_cases k
  · omega
  · refine Or.inr ⟨by omega, Subgroup.eq_of_le_of_card_ge hle ?_⟩
    rw [hrange, card_hexadAut.1]
    omega
  · exact Or.inl ⟨by omega, eq_M22_of_le_hexadAut hle (by rw [hrange]; omega)⟩

theorem mathieu_of_extension
    (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o) {G : Subgroup (Equiv.Perm P)}
    (hG : Nat.card G = 20160)
    (hel : ∀ L ∈ 𝓛, ∃ σ ∈ G, σ * σ = 1 ∧ ∀ p, σ p = p ↔ p ∈ L)
    (hup : ∀ n : N, n • o = o → ∃ σ ∈ blockAut 𝓛, ∀ p, n • ι p = ι (σ p))
    (hlow : ∀ σ ∈ G, ∃ n : N, n • o = o ∧ ∀ p, n • ι p = ι (σ p)) :
    ∃ f : Ω ≃ Fin 22, (∀ L ∈ 𝓛, (insert o (L.map ⟨ι, hι⟩)).map f.toEmbedding ∈ hexads) ∧
      ((Nat.card (stabilizer N o) = 20160 ∧ (permHom (N := N) f).range = M22 ∧
          Nonempty (N ≃* M22) ∧ ∃ φ : stabilizer N o ≃* G,
            ∀ (n : stabilizer N o) (p : P), (n : N) • ι p = ι ((φ n : Equiv.Perm P) p)) ∨
        (Nat.card (stabilizer N o) = 40320 ∧ (permHom (N := N) f).range = hexadAut ∧
          Nonempty (N ≃* MulAut M22))) := by
  have hrng := eq_or_exists_of_card hΩ h𝓛 hι hιo
  have htriv : ∀ n : N, n • o = o → (∀ p, n • ι p = ι p) → n = 1 := fun n hno hn =>
    eq_of_smul_eq_smul (α := Ω) fun x => by
      rcases hrng x with hx | ⟨p, rfl⟩
      · rw [hx, hno, one_smul]
      · rw [hn, one_smul]
  have hB : ∀ L ∈ 𝓛, ∃ n : N, n • o = o ∧ n * n = 1 ∧ ∀ p, n • ι p = ι p ↔ p ∈ L := by
    intro L hL
    obtain ⟨σ, hσG, hσ2, hσL⟩ := hel L hL
    obtain ⟨n, hno, hn⟩ := hlow σ hσG
    refine ⟨n, hno, htriv _ (by rw [mul_smul, hno, hno]) fun p => ?_, fun p => ?_⟩
    · rw [mul_smul, hn, hn, ← Equiv.Perm.mul_apply, hσ2, Equiv.Perm.one_apply]
    · rw [hn, hι.eq_iff, hσL]
  have huniq : ∀ {n m : N} {σ : Equiv.Perm P}, n • o = o → m • o = o →
      (∀ p, n • ι p = ι (σ p)) → (∀ p, m • ι p = ι (σ p)) → n = m := by
    intro n m σ hno hmo hn hm
    have := htriv (m⁻¹ * n) (by rw [mul_smul, hno, inv_smul_eq_iff, hmo])
      (fun p => by rw [mul_smul, hn, inv_smul_eq_iff, hm])
    rw [inv_mul_eq_one] at this
    exact this.symm
  choose χ hχo hχ using hlow
  set χ' : G → stabilizer N o := fun σ => ⟨χ σ.1 σ.2, hχo σ.1 σ.2⟩
  have hχ'mul : ∀ σ τ : G, χ' (σ * τ) = χ' σ * χ' τ := fun σ τ => Subtype.ext
    (huniq (χ' (σ * τ)).2 (χ' σ * χ' τ).2 (hχ _ _) fun p => by
      change (χ σ.1 σ.2 * χ τ.1 τ.2) • ι p = ι (σ.1 (τ.1 p))
      rw [mul_smul, hχ, hχ])
  have hχ'inj : Function.Injective χ' := by
    intro σ τ h
    have h' := congrArg (fun m : stabilizer N o => (m : N)) h
    refine Subtype.ext (Equiv.ext fun p => hι ?_)
    have := congrArg (· • ι p) h'
    simp only [χ'] at this
    rwa [hχ, hχ] at this
  have hfin : Finite N := Finite.of_injective _ (MulAction.toPerm_injective (α := N) (β := Ω))
  have hC : 20160 ≤ Nat.card (stabilizer N o) := by
    rw [← hG]
    exact Nat.card_le_card_of_injective χ' hχ'inj
  obtain ⟨hcardN, f, hlines, hcase⟩ := mathieu_of_extension_abstract hΩ h𝓛 hι hιo hup hB hC
  refine ⟨f, hlines, ?_⟩
  have hequiv := MonoidHom.ofInjective (permHom_injective (N := N) f)
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hstab : Nat.card (stabilizer N o) = 20160 := by omega
    have hbij := hχ'inj.bijective_of_nat_card_le (by rw [hstab, hG])
    set e : G ≃* stabilizer N o := MulEquiv.ofBijective (MonoidHom.mk' χ' hχ'mul) hbij
    refine Or.inl ⟨hstab, h2, ⟨hequiv.trans (MulEquiv.subgroupCongr h2)⟩, e.symm,
      fun n p => ?_⟩
    have hn : ((χ' (e.symm n) : stabilizer N o) : N) = n :=
      congrArg Subtype.val (e.apply_symm_apply n)
    rw [← hn]
    exact hχ _ _ p
  · refine Or.inr ⟨by omega, h2, ⟨(hequiv.trans (MulEquiv.subgroupCongr h2)).trans
      hexadAutEquiv⟩⟩

end Main

section DavisSolomon

variable {N : Type*} [Group N] {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MulAction N Ω]
  [FaithfulSMul N Ω] [IsPretransitive N Ω]

theorem davis_solomon_transitive_extension_plane
    (hΩ : Fintype.card Ω = 22) (o : Ω)
    (ι : Fin 21 → Ω) (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o)
    (hup : ∀ n : N, n • o = o → ∃ σ ∈ lineAut, ∀ p, n • ι p = ι (σ p))
    (hlow : ∀ g : PSL(3, F4), ∃ n : N, n • o = o ∧ ∀ p, n • ι p = ι (pslPerm g p)) :
    ∃ f : Ω ≃ Fin 22,
      (∀ a : Fin 21, (insert o ((projLine a).map ⟨ι, hι⟩)).map f.toEmbedding ∈ hexads) ∧
      ((Nat.card (stabilizer N o) = 20160 ∧ (permHom (N := N) f).range = M22 ∧
          Nonempty (N ≃* M22) ∧ ∃ φ : stabilizer N o ≃* PSL(3, F4),
            ∀ (n : stabilizer N o) (p : Fin 21), (n : N) • ι p = ι (pslPerm (φ n) p)) ∨
        (Nat.card (stabilizer N o) = 40320 ∧ (permHom (N := N) f).range = hexadAut ∧
          Nonempty (N ≃* MulAut M22))) := by
  have hel : ∀ L ∈ Finset.univ.image projLine, ∃ σ ∈ pslPerm.range, σ * σ = 1 ∧
      ∀ p, σ p = p ↔ p ∈ L := by
    intro L hL
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨g, hg2, hgL⟩ := exists_elation_projLine a
    exact ⟨pslPerm g, ⟨g, rfl⟩, hg2, hgL⟩
  obtain ⟨f, hlines, hcase⟩ := mathieu_of_extension hΩ isSteinerPlane_projLine hι hιo
    card_range_pslPerm hel
    (fun n hno => by
      obtain ⟨σ, hσ, hnσ⟩ := hup n hno
      exact ⟨σ, mem_blockAut_of_mem_lineAut hσ, hnσ⟩)
    (by
      rintro _ ⟨g, rfl⟩
      exact hlow g)
  refine ⟨f, fun a => hlines _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)), ?_⟩
  rcases hcase with ⟨h1, h2, h3, φ, hφ⟩ | h
  · set ψ : PSL(3, F4) ≃* pslPerm.range := MonoidHom.ofInjective pslPerm_injective
    refine Or.inl ⟨h1, h2, h3, φ.trans ψ.symm, fun n p => ?_⟩
    rw [hφ n p]
    congr 2
    have := ψ.apply_symm_apply (φ n)
    exact (congrArg Subtype.val this).symm
  · exact Or.inr h

theorem davis_solomon_transitive_extension_of_normalizes
    (hΩ : Fintype.card Ω = 22) (o : Ω)
    (ι : Fin 21 → Ω) (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o)
    (hnorm : ∀ n : N, n • o = o → ∃ σ : Equiv.Perm (Fin 21), (∀ p, n • ι p = ι (σ p)) ∧
      ∀ τ ∈ pslPerm.range, σ * τ * σ⁻¹ ∈ pslPerm.range)
    (hlow : ∀ g : PSL(3, F4), ∃ n : N, n • o = o ∧ ∀ p, n • ι p = ι (pslPerm g p)) :
    ∃ f : Ω ≃ Fin 22,
      (∀ a : Fin 21, (insert o ((projLine a).map ⟨ι, hι⟩)).map f.toEmbedding ∈ hexads) ∧
      ((Nat.card (stabilizer N o) = 20160 ∧ (permHom (N := N) f).range = M22 ∧
          Nonempty (N ≃* M22) ∧ ∃ φ : stabilizer N o ≃* PSL(3, F4),
            ∀ (n : stabilizer N o) (p : Fin 21), (n : N) • ι p = ι (pslPerm (φ n) p)) ∨
        (Nat.card (stabilizer N o) = 40320 ∧ (permHom (N := N) f).range = hexadAut ∧
          Nonempty (N ≃* MulAut M22))) :=
  davis_solomon_transitive_extension_plane hΩ o ι hι hιo (fun n hno => by
    obtain ⟨σ, hσ, hσn⟩ := hnorm n hno
    exact ⟨σ, mem_lineAut_of_normalizes hσn, hσ⟩) hlow

end DavisSolomon

end CFSG.EvenSmallLie.UnitarySix.MathieuExt
