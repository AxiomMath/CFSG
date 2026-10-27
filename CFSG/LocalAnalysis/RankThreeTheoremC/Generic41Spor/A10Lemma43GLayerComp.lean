module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GDefs
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.Foundations.Basic
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem a10t1_comp_A5_card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [h120] at h2
  omega

private theorem a10t1_comp_A5_nonab : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩, ?_⟩
  decide

private theorem a10t1_comp_A5_perfect : Group.IsPerfect (alternatingGroup (Fin 5)) := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5))) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := a10t1_comp_A5_nonab
    apply hab
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ commutator (alternatingGroup (Fin 5)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  · exact h

private theorem a10t1_comp_quasisimple {H : Type} [Group H] (e : H ≃* alternatingGroup (Fin 5)) :
    CFSG.IsQuasisimple H := by
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) := a10t1_comp_A5_perfect
  haveI : IsSimpleGroup H := e.isSimpleGroup
  haveI : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hc : Subgroup.center H = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center H) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) (Group.IsPerfect.not_isMulCommutative H)
  have hsimp : IsSimpleGroup (H ⧸ Subgroup.center H) :=
    MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  haveI := hsimp
  have hnc : ∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative (H ⧸ Subgroup.center H) ⟨⟨fun a b => hcon a b⟩⟩
  unfold CFSG.IsQuasisimple
  exact ⟨inferInstance, hsimp, hnc⟩

private theorem a10t1_comp_pPrimeCore {H : Type} [Group H] [Finite H] (f : H →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (hc : ¬ 5 ∣ Nat.card f.ker) :
    CFSG.pPrimeCore 5 H = f.ker := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply le_antisymm
  · have hCn : (CFSG.pPrimeCore 5 H).Normal := CFSG.pPrimeCore_normal
    have hCc : ¬ 5 ∣ Nat.card (CFSG.pPrimeCore 5 H) :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).1 CFSG.pPrimeCore_coprime_card
    have hmn : ((CFSG.pPrimeCore 5 H).map f).Normal := hCn.map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pPrimeCore 5 H).map f) with h | h
    · rwa [Subgroup.map_eq_bot_iff] at h
    · exfalso
      have hd : Nat.card ((CFSG.pPrimeCore 5 H).map f) ∣ Nat.card (CFSG.pPrimeCore 5 H) :=
        Subgroup.card_map_dvd _ f
      rw [h, Subgroup.card_top, a10t1_comp_A5_card] at hd
      exact hCc (dvd_trans (by norm_num) hd)
  · exact le_sSup ⟨f.normal_ker, (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hc⟩

private theorem a10t1_comp_le_normalizer {S H : Subgroup G} (h : ∀ s ∈ S, ∀ a ∈ H, s * a * s⁻¹ ∈ H) :
    S ≤ Subgroup.normalizer (H : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨h s hs a, fun ha => ?_⟩
  have := h s⁻¹ (S.inv_mem hs) _ ha
  simpa [mul_assoc] using this

private theorem a10t1_comp_subnormal {W E₁ E₂ : Subgroup G} (hE₁ : E₁ ≤ W) (hE₂ : E₂ ≤ W)
    (hW : ∀ w ∈ W, ∀ e ∈ E₁ ⊔ E₂, w * e * w⁻¹ ∈ E₁ ⊔ E₂)
    (h₂ : ∀ e ∈ E₂, ∀ a ∈ E₁, e * a * e⁻¹ ∈ E₁) :
    (E₁.subgroupOf W).IsSubnormal := by
  have hsup : E₁ ⊔ E₂ ≤ W := sup_le hE₁ hE₂
  have hKn : ((E₁ ⊔ E₂).subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsup).2 (a10t1_comp_le_normalizer hW)
  have hle : E₁.subgroupOf W ≤ (E₁ ⊔ E₂).subgroupOf W := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hx))
  refine Subgroup.IsSubnormal.step _ _ hle hKn.isSubnormal ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, ← Subgroup.subgroupOf_normalizer_eq hE₁]
  intro k hk
  have hle2 : E₁ ⊔ E₂ ≤ Subgroup.normalizer (E₁ : Set G) :=
    sup_le Subgroup.le_normalizer (a10t1_comp_le_normalizer (S := E₂) h₂)
  exact hle2 (Subgroup.mem_subgroupOf.1 hk)

private theorem a10t1_comp_ker_card {E O : Subgroup G} (f : ↥E →* alternatingGroup (Fin 5))
    (hker : f.ker = O.subgroupOf E) (hOc : ¬ 5 ∣ Nat.card O) : ¬ 5 ∣ Nat.card f.ker := by
  rw [hker]
  intro h
  apply hOc
  refine dvd_trans h ?_
  let φ : ↥(O.subgroupOf E) →* ↥O :=
    { toFun := fun x => ⟨(x.1 : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Subgroup.card_dvd_of_injective φ (fun x y hxy => by
    have h' : ((φ x : ↥O) : G) = ((φ y : ↥O) : G) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h'))

private theorem a10t1_comp_residual {W E : Subgroup G} (hEW : E ≤ W)
    (hgen : Subgroup.closure {g : G | g ∈ E ∧ ∃ k : ℕ, g ^ 5 ^ k = 1} = E) :
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 5 ↥(E.subgroupOf W) = ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hE : E ≤ (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 5 ↥E).map E.subtype := by
    refine hgen.symm.le.trans ((Subgroup.closure_le _).2 ?_)
    rintro g ⟨hgE, k, hk⟩
    refine ⟨⟨g, hgE⟩, ?_, rfl⟩
    have hord : orderOf (⟨g, hgE⟩ : ↥E) ∣ 5 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hord
    have hP : IsPGroup 5 (Subgroup.zpowers (⟨g, hgE⟩ : ↥E)) :=
      IsPGroup.iff_card.mpr ⟨j, (Nat.card_zpowers _).trans hj⟩
    exact CFSG.ComponentClassification.CatalogueBPrimeJoin.pSubgroup_le_residual 5 _ hP
      (Subgroup.mem_zpowers _)
  have hEtop : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 5 ↥E = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hE x.2
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  let e : ↥(E.subgroupOf W) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEW
  have hmap := CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_map_equiv 5 e
  rw [hEtop] at hmap
  have h2 := Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 5 ↥(E.subgroupOf W))
  rw [hmap, Subgroup.comap_top] at h2
  exact h2.symm

private theorem a10t1_comp_one {W O E : Subgroup G} (hEW : E ≤ W)
    (hsub : (E.subgroupOf W).IsSubnormal) (hOc : ¬ 5 ∣ Nat.card O)
    (hgen : Subgroup.closure {g : G | g ∈ E ∧ ∃ k : ℕ, g ^ 5 ^ k = 1} = E)
    (hA : ∃ f : ↥E →* alternatingGroup (Fin 5), Function.Surjective f ∧ f.ker = O.subgroupOf E) :
    GLAPComponent 5 W E ∧
      Nonempty (↥E ⧸ primeComplementCore (G := ↥E) 5 ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨f, hf, hker⟩ := hA
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcore : CFSG.pPrimeCore 5 ↥E = f.ker :=
    a10t1_comp_pPrimeCore f hf (a10t1_comp_ker_card f hker hOc)
  have hiso : ↥E ⧸ CFSG.pPrimeCore 5 ↥E ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨?_, ⟨hiso⟩⟩
  rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent (by norm_num)]
  refine ⟨hEW, ?_⟩
  rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple]
  refine ⟨hsub, a10t1_comp_residual hEW hgen, ?_⟩
  let e : ↥(E.subgroupOf W) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEW
  have hmap : (CFSG.pPrimeCore 5 ↥(E.subgroupOf W)).map e.toMonoidHom = CFSG.pPrimeCore 5 ↥E :=
    CFSG.pPrimeCore_map_iso 5 e
  exact a10t1_comp_quasisimple ((QuotientGroup.congr _ _ e hmap).trans hiso)

private theorem a10t1_comp_ne {O E₁ E₂ : Subgroup G}
    (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b * a⁻¹ * b⁻¹ ∈ O)
    (hA : ∃ f : ↥E₁ →* alternatingGroup (Fin 5), Function.Surjective f ∧ f.ker = O.subgroupOf E₁) :
    E₁ ≠ E₂ := by
  intro heq
  subst heq
  obtain ⟨f, hf, hker⟩ := hA
  obtain ⟨a, b, hab⟩ := a10t1_comp_A5_nonab
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  apply hab
  have hxy : x * y * x⁻¹ * y⁻¹ ∈ f.ker := by
    rw [hker]
    exact hcomm x x.2 y y.2
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hxy
  exact (commutatorElement_eq_one_iff_mul_comm.1 hxy)

theorem a10_E_comp {W O N D E₁ E₂ : Subgroup G} (h : A10EData W O N D E₁ E₂) :
    GLAPComponent 5 W E₁ ∧ GLAPComponent 5 W E₂ ∧ E₁ ≠ E₂ ∧
      Nonempty (↥E₁ ⧸ primeComplementCore (G := ↥E₁) 5 ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (↥E₂ ⧸ primeComplementCore (G := ↥E₂) 5 ≃* alternatingGroup (Fin 5)) := by
  have hb := h.base
  have hs₁ : (E₁.subgroupOf W).IsSubnormal :=
    a10t1_comp_subnormal hb.E₁_le hb.E₂_le hb.E_norm hb.E₁_norm
  have hs₂ : (E₂.subgroupOf W).IsSubnormal :=
    a10t1_comp_subnormal hb.E₂_le hb.E₁_le
      (fun w hw e he => by
        rw [sup_comm] at he ⊢
        exact hb.E_norm w hw e he) hb.E₂_norm
  obtain ⟨c₁, i₁⟩ := a10t1_comp_one hb.E₁_le hs₁ hb.O_cop hb.E₁_gen hb.E₁_A5
  obtain ⟨c₂, i₂⟩ := a10t1_comp_one hb.E₂_le hs₂ hb.O_cop hb.E₂_gen hb.E₂_A5
  exact ⟨c₁, c₂, a10t1_comp_ne hb.comm hb.E₁_A5, i₁, i₂⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
