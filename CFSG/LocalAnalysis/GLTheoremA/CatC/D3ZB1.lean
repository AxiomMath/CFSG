module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IBound

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem sgn_cover :
    ∀ b₁ b₂ : D4Idx → Bool, b₁ 0 = b₁ 1 → b₁ 1 = b₁ 3 → b₂ 0 = b₂ 1 → b₂ 1 = b₂ 3 →
      (∃ i, b₁ i = true) → (∃ i, b₂ i = true) → b₁ ≠ b₂ →
      ∀ v ∈ d4RootsFrom 1, sgnB b₁ v = true ∨ sgnB b₂ v = true := by decide +kernel


section Four

variable {K : Type} [Field K] [Finite K]

theorem borelScalar_s_mul' {g g' g'' : ModGL Tag.D4 K} (hg : BorelScalar g) (hg' : BorelScalar g')
    (hg'' : BorelScalar g'') (h : g'' = g * g') {v : D4Vec} (hv : IsRoot Tag.D4 v ∧ 0 < height v) :
    hg''.s v = hg.s v * hg'.s v := by
  subst h
  rw [borelScalar_s_eq hg'' hv]
  have hxm : pinnedX Tag.D4 K v 1 ∈ heightSeries Tag.D4 K (height v) :=
    pinnedX_mem_heightSeries_height hv 1
  have hym : g' * pinnedX Tag.D4 K v 1 * g'⁻¹ ∈ heightSeries Tag.D4 K (height v) :=
    (Subgroup.mem_normalizer_iff.1 (hg'.1 _) _).1 hxm
  have e : g * g' * pinnedX Tag.D4 K v 1 * (g * g')⁻¹ =
      g * (g' * pinnedX Tag.D4 K v 1 * g'⁻¹) * g⁻¹ := by group
  rw [e, hg.spec.2 v hv _ hym, hg'.spec.2 v hv _ hxm, rootCoord_self hv, mul_one]

theorem sign_vector_invariant [CharP K 3] {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hr : ∀ k δ, (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1)
    {g : ↥(adjointGroup Tag.D4 K)} (hs : BorelScalar (g : ModGL Tag.D4 K)) (hαg : α g = g)
    {b : D4Idx → Bool} (hb : ∀ v ∈ d4RootsFrom 1, hs.s v = if sgnB b v then -1 else 1) :
    b 0 = b 1 ∧ b 1 = b 3 := by
  have hm : 2 * ε ∈ ({2, 4} : Finset ℕ) := by
    rcases hε with h | h <;> subst h <;> simp
  have hbinv : ∀ i, b ((d4Rho ^ (2 * ε)) i) = b i := by
    intro i
    let δi : UnitRoots Tag.D4 0 := ⟨rA i, rA_isRoot i, by rw [height_rA]; rfl⟩
    have h1 := sign_perm_invariant la hs hαg 0 δi
    have h2 : (la.r 0 δi).1 = rA ((d4Rho ^ (2 * ε)) i) := by
      rw [hr, show δi.1 = rA i from rfl]
      exact permLattice_single _ i
    rw [h2] at h1
    have hr1 : ∀ j : D4Idx, rA j ∈ d4RootsFrom 1 := fun j => by
      refine mem_d4RootsFrom.2 ⟨rA_isRoot j, ?_, ?_⟩ <;> rw [height_rA] <;> norm_num
    have h3 : σ (hs.s (rA ((d4Rho ^ (2 * ε)) i))) = hs.s (rA i) := h1
    rw [hb _ (hr1 _), hb _ (hr1 _), sgnB_rA, sgnB_rA] at h3
    cases h4 : b ((d4Rho ^ (2 * ε)) i) <;> cases h5 : b i <;> simp [h4, h5] at h3 ⊢
    · exact neg_one_ne_one_of_charThree (K := K) h3.symm
    · exact neg_one_ne_one_of_charThree (K := K) h3
  exact invariant_of_perm (2 * ε) hm b hbinv

theorem four_group_borel_c [CharP K 3] {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hr : ∀ k δ, (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1)
    {g₁ g₂ : ↥(adjointGroup Tag.D4 K)} (hg₁2 : g₁ * g₁ = 1) (hg₂2 : g₂ * g₂ = 1)
    (hcomm : g₁ * g₂ = g₂ * g₁) (hg₁1 : g₁ ≠ 1) (hg₂1 : g₂ ≠ 1) (hne : g₁ ≠ g₂)
    (hg₁U : ((posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)).map
      (MulAut.conj g₁).toMonoidHom = (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (hg₂U : ((posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)).map
      (MulAut.conj g₂).toMonoidHom = (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (hαg₁ : α g₁ = g₁) (hαg₂ : α g₂ = g₂) {A : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hAU : A ≤ (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (hfix₁ : ∀ a ∈ A, g₁ * a * g₁⁻¹ = a) (hfix₂ : ∀ a ∈ A, g₂ * a * g₂⁻¹ = a) :
    Nat.card A = 1 := by
  classical
  have hgB₁ := mem_borelGroup_of_stable g₁ hg₁U
  have hgB₂ := mem_borelGroup_of_stable g₂ hg₂U
  have hs₁ : BorelScalar (g₁ : ModGL Tag.D4 K) := borelScalar_of_mem_borelGroup hgB₁
  have hs₂ : BorelScalar (g₂ : ModGL Tag.D4 K) := borelScalar_of_mem_borelGroup hgB₂
  have hg₁2' : (g₁ : ModGL Tag.D4 K) * (g₁ : ModGL Tag.D4 K) = 1 := congrArg Subtype.val hg₁2
  have hg₂2' : (g₂ : ModGL Tag.D4 K) * (g₂ : ModGL Tag.D4 K) = 1 := congrArg Subtype.val hg₂2
  obtain ⟨b₁, hb₁⟩ := signData_table (neg_one_ne_one_of_charThree (K := K))
    (signData_of_involution hs₁ hg₁2')
  obtain ⟨b₂, hb₂⟩ := signData_table (neg_one_ne_one_of_charThree (K := K))
    (signData_of_involution hs₂ hg₂2')
  have hmemR : ∀ k (δ : UnitRoots Tag.D4 k), δ.1 ∈ d4RootsFrom 1 := fun k δ =>
    mem_d4RootsFrom.2 ⟨δ.2.1, (UnitRoots.pos Tag.D4 δ).2, by
      rw [δ.2.2]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)⟩
  have hbne : ∀ (g : ↥(adjointGroup Tag.D4 K)) (hgB : (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K)
      (hg2 : g * g = 1) (hg1 : g ≠ 1) (b : D4Idx → Bool)
      (hb : ∀ v ∈ d4RootsFrom 1, (borelScalar_of_mem_borelGroup hgB).s v = if sgnB b v then -1 else 1),
      ∃ i, b i = true := by
    intro g hgB hg2 hg1 b hb
    by_contra hcon
    push Not at hcon
    have hb0 : b = fun _ => false := funext fun i => by simpa using hcon i
    apply hg1
    refine eq_one_of_borelScalar_eq_one g hgB hg2 ?_
    intro v hv
    rw [hb v hv, hb0, sgnB_zero]
    simp
  have hbne₁ : ∃ i, b₁ i = true := hbne g₁ hgB₁ hg₁2 hg₁1 b₁ hb₁
  have hbne₂ : ∃ i, b₂ i = true := hbne g₂ hgB₂ hg₂2 hg₂1 b₂ hb₂
  obtain ⟨h01, h13⟩ := sign_vector_invariant la hε hr hs₁ hαg₁ hb₁
  obtain ⟨h01', h13'⟩ := sign_vector_invariant la hε hr hs₂ hαg₂ hb₂
  have hb12 : b₁ ≠ b₂ := by
    intro h12
    apply hne
    have hg₃B : ((g₁ * g₂ : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K :=
      mul_mem hgB₁ hgB₂
    have hg₃2 : (g₁ * g₂) * (g₁ * g₂) = 1 := by
      calc (g₁ * g₂) * (g₁ * g₂) = g₁ * (g₂ * g₁) * g₂ := by group
        _ = g₁ * (g₁ * g₂) * g₂ := by rw [← hcomm]
        _ = (g₁ * g₁) * (g₂ * g₂) := by group
        _ = 1 := by rw [hg₁2, hg₂2, mul_one]
    have h3 : g₁ * g₂ = 1 := by
      refine eq_one_of_borelScalar_eq_one (g₁ * g₂) hg₃B hg₃2 ?_
      intro v hv
      have hvv := mem_d4RootsFrom.1 hv
      rw [borelScalar_s_mul' hs₁ hs₂ (borelScalar_of_mem_borelGroup hg₃B) rfl ⟨hvv.1, hvv.2.1⟩,
        hb₁ v hv, hb₂ v hv, h12]
      cases sgnB b₂ v <;> simp
    calc g₁ = g₁ * (g₁ * g₂) := by rw [h3, mul_one]
      _ = (g₁ * g₁) * g₂ := by group
      _ = g₂ := by rw [hg₁2, one_mul]
  have hcover := sgn_cover b₁ b₂ h01 h13 h01' h13' hbne₁ hbne₂ hb12
  have hlayerG : ∀ (g : ↥(adjointGroup Tag.D4 K)) (hs : BorelScalar (g : ModGL Tag.D4 K))
      (b : D4Idx → Bool) (hb : ∀ v ∈ d4RootsFrom 1, hs.s v = if sgnB b v then -1 else 1)
      (hfix : ∀ a ∈ A, g * a * g⁻¹ = a), ∀ k, ∀ q ∈ layerImage A k,
        ∀ δ : UnitRoots Tag.D4 k, sgnB b δ.1 = true → Multiplicative.toAdd q δ = 0 := by
    intro g hs b hb hfix k q hq δ hδ
    have hβ : ∀ x : ↥(adjointGroup Tag.D4 K),
        (((MulAut.conj g) x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
          (g : ModGL Tag.D4 K) * (MonoidHom.id (ModGL Tag.D4 K)) (x : ModGL Tag.D4 K) *
            (g : ModGL Tag.D4 K)⁻¹ := fun x => rfl
    let laG : LayerAct Tag.D4 (MulAut.conj g) 1 :=
      layerAct_of_borel_monomial hs (MonoidHom.id _) id (fun _ => 1) 1 (fun γ h => h)
        (fun γ => rfl) (fun γ γ' _ _ h => h)
        (fun γ _ c => by
          change pinnedX Tag.D4 K γ c = pinnedX Tag.D4 K γ (1 * c)
          rw [one_mul]) hβ (fun _ δ => δ) (fun _ _ => rfl)
    have hfix' : ∀ a ∈ A, (MulAut.conj g) a = a := fun a ha => by
      rw [MulAut.conj_apply]; exact hfix a ha
    have h := layerImage_fixed laG hfix' k hq
    have h' := congrFun (congrArg Multiplicative.toAdd h) δ
    have hsδ : hs.s δ.1 = -1 := by rw [hb δ.1 (hmemR k δ), hδ]; simp
    change hs.s δ.1 * 1 * ((1 : K ≃+* K) (Multiplicative.toAdd q δ)) = Multiplicative.toAdd q δ at h'
    have h2 : (2 : K) * Multiplicative.toAdd q δ = 0 := by
      rw [hsδ] at h'
      have : (1 : K ≃+* K) (Multiplicative.toAdd q δ) = Multiplicative.toAdd q δ := rfl
      rw [this] at h'
      linear_combination -h'
    exact (mul_eq_zero.1 h2).resolve_left (two_ne_zero_of_charThree (K := K))
  have hsupp : ∀ k, ∀ q ∈ layerImage A k, ∀ δ : UnitRoots Tag.D4 k, Multiplicative.toAdd q δ = 0 := by
    intro k q hq δ
    rcases hcover δ.1 (hmemR k δ) with h | h
    · exact hlayerG g₁ hs₁ b₁ hb₁ hfix₁ k q hq δ h
    · exact hlayerG g₂ hs₂ b₂ hb₂ hfix₂ k q hq δ h
  set d := (maxHeight Tag.D4).toNat with hd
  have hA0 : A ≤ unitN Tag.D4 K 0 := fun x hx =>
    unitN_zero_of_mem_pos (Subgroup.mem_subgroupOf.1 (hAU hx))
  have hprod := card_le_prod_of_filtration (unitN Tag.D4 K) (unitPhi Tag.D4 K) d
    (unitN_bot Tag.D4) (unitN_chain Tag.D4) (unitPhi_eq_one_iff) A hA0
    (fun k => Nat.card (layerImage A k)) (fun k _ => le_rfl)
  have hlay : ∀ k, Nat.card (layerImage A k) ≤ 1 := by
    intro k
    haveI : Subsingleton (layerImage A k) := ⟨fun q q' => by
      apply Subtype.ext
      have h1 : ∀ r : layerImage A k, (r : UnitCoord Tag.D4 K k) = 1 := fun r => by
        apply Multiplicative.toAdd.injective
        funext δ
        exact hsupp k r.1 r.2 δ
      rw [h1 q, h1 q']⟩
    calc Nat.card (layerImage A k) ≤ Nat.card (Fin 1) :=
          Nat.card_le_card_of_injective (fun _ => (0 : Fin 1)) (fun x y _ => Subsingleton.elim x y)
      _ = 1 := by simp
  have hA1 : Nat.card A ≤ 1 := by
    calc Nat.card A ≤ ∏ k ∈ Finset.range d, Nat.card (layerImage A k) := hprod
      _ ≤ ∏ k ∈ Finset.range d, 1 := Finset.prod_le_prod' fun k _ => hlay k
      _ = 1 := Finset.prod_const_one
  exact le_antisymm hA1 Nat.card_pos

end Four

end CFSG.LocalAnalysis.GLTheoremA
