module

public import CFSG.GH74.Uniqueness.Section7Cor713Defs
public import CFSG.GH74.Uniqueness.Section6Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem Cor713.closure_zHull_eq_top (Z : Set X) (F : Subgroup X) :
    Subgroup.closure {l : zHull Z F | (l : X) ∈ Z} = ⊤ := by
  have e : {l : zHull Z F | (l : X) ∈ Z} =
      (Subtype.val : zHull Z F → X) ⁻¹' (Z ∩ (F : Set X)) := by
    ext l
    exact ⟨fun hl => ⟨hl, Cor713.zHull_le F l.2⟩, fun hl => hl.1⟩
  rw [e]
  exact Subgroup.closure_closure_coe_preimage

theorem Cor713.two_le_twoRank_of_fourGroup {G : Type*} [Group G] [Finite G]
    (hrank : CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo G) : 2 ≤ Open.twoRank G := by
  obtain ⟨E, hcard, hsquare⟩ := hrank
  have hE : Open.IsElemAbelian 2 E := by
    refine ⟨CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one hsquare, ?_⟩
    intro e he
    exact congrArg Subtype.val (hsquare ⟨e, he⟩)
  exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G E hE 2
    (by simpa only [Nat.reducePow] using hcard)

theorem ZDSetup.cor713_two_le_twoRank_zHull
    (S : ZDSetup X Z M) {F : Subgroup X} (hF : F ≠ ⊤)
    (hFM : ¬ F ≤ M) (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hns : ¬ Group.IsSolvable ↥(zHull Z F)) : 2 ≤ Open.twoRank ↥(zHull Z F) := by
  have hSE := S.cor713_isStronglyEmbedded_zHull hF hFM hne
  have hnat : CFSG.BenderSuzuki.IsStronglyEmbedded ((M ⊓ zHull Z F).subgroupOf (zHull Z F)) :=
    CFSG.BenderSuzuki.isStronglyEmbedded_of_parity _
      (isStronglyEmbeddedOrder_of_isStronglyEmbedded hSE)
  have hcore : CFSG.BenderSuzuki.involutionCore ↥(zHull Z F) = ⊤ := by
    rw [eq_top_iff, ← Cor713.closure_zHull_eq_top Z F, CFSG.BenderSuzuki.involutionCore_eq_closure]
    refine Subgroup.closure_mono fun l hl => ?_
    have h2 : orderOf l = 2 := by
      have := S.invariant.1 (l : X) hl
      rwa [Subgroup.orderOf_coe] at this
    have h := orderOf_eq_prime_iff.mp h2
    exact ⟨h.2, h.1⟩
  have h4 := hnat.twoRankAtLeastTwo_of_not_solvable_of_involutionCore_eq_top hcore hns
  exact Cor713.two_le_twoRank_of_fourGroup
    (CFSG.BenderSuzuki.twoRankAtLeastTwo_of_injective
      (((M ⊓ zHull Z F).subgroupOf (zHull Z F)).subtype)
      (Subgroup.subtype_injective _) h4)

theorem ZDSetup.cor713_centralizes_of_theorem4b (S : ZDSetup X Z M) (hT4b : Theorem4bStmt Z M)
    {F : Subgroup X} (hFM : ¬ F ≤ M) (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    {O : Subgroup X} (hOodd : Odd (Nat.card O)) (hOM : O ≤ M)
    (hOnorm : zHull Z F ≤ normalizer (O : Set X)) :
    ∀ w ∈ O, ∀ g ∈ zHull Z F, w * g = g * w := by
  have hLM : ¬ zHull Z F ≤ M := S.not_zHull_le hFM hne
  obtain ⟨z₁, hz₁, hz₁FM⟩ := hne
  have hz₁F : z₁ ∈ F := (Subgroup.mem_inf.mp hz₁FM).1
  have hz₁M : z₁ ∈ M := (Subgroup.mem_inf.mp hz₁FM).2
  have hz₁L : z₁ ∈ zHull Z F := Cor713.mem_zHull_of_mem hz₁ hz₁F
  have h1 : ∀ w ∈ O, z₁ * w = w * z₁ := by
    rcases hT4b z₁ hz₁ hz₁M O hOodd hOM (hOnorm hz₁L) with h | h
    · exact h
    · exfalso
      obtain ⟨g, hgL, hgM⟩ : ∃ g ∈ zHull Z F, g ∉ M := by
        by_contra hall
        push Not at hall
        exact hLM hall
      have hβ : conjugate M g ∈ omegaFix M (O : Set X) := by
        rw [S.prodDisc.mem_omegaFix_iff]
        refine ⟨⟨g, rfl⟩, fun w hw => ?_⟩
        rw [mem_conjugate_iff]
        exact hOM ((Subgroup.mem_normalizer_iff.mp (hOnorm hgL) w).mp hw)
      have h' := conjugate_eq_iff_mem_normalizer.mp (h _ hβ)
      rw [S.prodDisc.normalizer_eq_self] at h'
      exact hgM h'
  have h2 : ∀ y ∈ Z, y ∈ F → ∀ w ∈ O, w * y = y * w := by
    intro y hy hyF w hw
    obtain ⟨l, hl, hly⟩ := S.exists_conj_zHull hFM ⟨z₁, hz₁, hz₁FM⟩ hz₁ hz₁F hz₁M hy hyF
    have hlw : l * w * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hOnorm hl) w).mp hw
    have h3 := h1 _ hlw
    rw [← hly]
    calc w * (l⁻¹ * z₁ * l) = l⁻¹ * ((l * w * l⁻¹) * z₁) * l := by group
      _ = l⁻¹ * (z₁ * (l * w * l⁻¹)) * l := by rw [h3]
      _ = l⁻¹ * z₁ * l * w := by group
  have h4 : zHull Z F ≤ centralizer (O : Set X) := by
    rw [zHull, Subgroup.closure_le]
    rintro y ⟨hy, hyF⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    exact h2 y hy hyF w hw
  intro w hw g hg
  exact Subgroup.mem_centralizer_iff.mp (h4 hg) w hw

theorem ZDSetup.cor713_exists_bender_quotient
    (S : ZDSetup X Z M) (hT4b : Theorem4bStmt Z M)
    {F : Subgroup X} (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hns : ¬ Group.IsSolvable ↥(zHull Z F)) :
    ∃ (K : Type) (_ : Group K) (ψ : ↥(zHull Z F) →* K) (T₀ : Sylow 2 K),
      Function.Surjective ψ ∧ ψ.ker = pPrimeCore 2 ↥(zHull Z F) ∧
      CFSG.BenderSuzuki.IsBenderGroup K ∧
      (∀ g : ↥(zHull Z F), ψ g ∈ normalizer ((T₀ : Subgroup K) : Set K) ↔ (g : X) ∈ M) ∧
      (∀ o ∈ pPrimeCore 2 ↥(zHull Z F), ∀ g : ↥(zHull Z F), o * g = g * o) ∧
      (∀ y : X, y ∈ zHull Z F → orderOf y = 2 → y ∈ Z) := by
  have hrank2 := S.cor713_two_le_twoRank_zHull hF hFM hne hns
  have hLM : ¬ zHull Z F ≤ M := S.not_zHull_le hFM hne
  have hIH := S.zdConclusion_zHull hF hFM hne
  rw [zdConclusion_iff] at hIH
  obtain ⟨u₀, hdata⟩ :
      ∃ u, ZDData ↥(zHull Z F) {l | (l : X) ∈ Z} (M.comap (zHull Z F).subtype) u := by
    rcases hIH with h | h
    · omega
    · exact h
  have hD := hdata.toXData
  have hSE := S.cor713_isStronglyEmbedded_zHull hF hFM hne
  have hu1 : (u₀ : X) = 1 := by
    rcases hD.eq_one_or_orderOf_eq_two with h | h2
    · exact h
    · exfalso
      have hu : u₀ ∈ (M ⊓ zHull Z F).subgroupOf (zHull Z F) := by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨hD.mem_M, u₀.2⟩
      have hcent := centralizer_le_of_isStronglyEmbedded hSE hu (by rwa [← Subgroup.orderOf_coe])
      apply hLM
      intro l hl
      obtain ⟨o, ho, c, hcL, huc, rfl⟩ := hD.exists_mul_centralizer_L hl
      have hcY : (⟨c, hcL⟩ : ↥(zHull Z F)) ∈ centralizer ({u₀} : Set ↥(zHull Z F)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext huc.symm
      have hcM : c ∈ M := by
        have := hcent hcY
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at this
        exact this.1
      exact M.mul_mem (hD.O_M ho) hcM
  have hu₀ : u₀ = 1 := Subtype.ext hu1
  have hcomm : commutator ↥(zHull Z F) = ⊤ := by
    have h := hdata.sup
    rwa [hu₀, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at h
  obtain ⟨K, instK, φ, hφs, hφk, hKB, T₀, hT₀⟩ := hdata.bar
  have hmem : ∀ g : ↥(zHull Z F), g ∈ commutator ↥(zHull Z F) := fun g => hcomm ▸ Subgroup.mem_top g
  let ι : ↥(zHull Z F) →* ↥(commutator ↥(zHull Z F)) :=
    (MonoidHom.id ↥(zHull Z F)).codRestrict (commutator ↥(zHull Z F)) hmem
  let ψ : ↥(zHull Z F) →* K := φ.comp ι
  have hψ : ∀ g : ↥(zHull Z F), ψ g = φ ⟨g, hmem g⟩ := fun g => rfl
  have hker : ψ.ker = pPrimeCore 2 ↥(zHull Z F) := by
    ext g
    rw [MonoidHom.mem_ker, hψ, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  refine ⟨K, instK, ψ, T₀, ?_, hker, hKB, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨x, hx⟩ := hφs k
    exact ⟨x, by rw [hψ]; exact hx⟩
  · intro g
    have hle : ∀ x : ↥(zHull Z F), x ∈ pPrimeCore 2 ↥(zHull Z F) → (x : X) ∈ M := fun x hx =>
      hdata.le_M hx
    constructor
    · intro hg
      rw [← hT₀, hψ] at hg
      obtain ⟨m, hmA, hm⟩ := hg
      set x : ↥(commutator ↥(zHull Z F)) := ⟨g, hmem g⟩ with hx
      have hmx : m⁻¹ * x ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hm, inv_mul_cancel]
      have h1 : ((m⁻¹ * x : ↥(commutator ↥(zHull Z F))) : ↥(zHull Z F)) ∈
          pPrimeCore 2 ↥(zHull Z F) := by
        rw [hφk, Subgroup.mem_subgroupOf] at hmx
        exact hmx
      have hmM : ((m : ↥(zHull Z F)) : X) ∈ M := by
        have := hmA
        simpa [Subgroup.mem_subgroupOf] using this
      have h2 := hle _ h1
      have e : (g : X) = ((m : ↥(zHull Z F)) : X) *
          (((m⁻¹ * x : ↥(commutator ↥(zHull Z F))) : ↥(zHull Z F)) : X) := by
        simp [hx]
      rw [e]
      exact M.mul_mem hmM h2
    · intro hg
      rw [← hT₀, hψ]
      exact ⟨⟨g, hmem g⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  · intro o ho g
    have hO : (o : X) ∈ (pPrimeCore 2 ↥(zHull Z F)).map (zHull Z F).subtype :=
      Subgroup.mem_map_of_mem _ ho
    have := S.cor713_centralizes_of_theorem4b hT4b hFM hne hD.O_odd hD.O_M
      (fun x hx => hD.mem_normalizer_O hx) (o : X) hO (g : X) g.2
    exact Subtype.ext this
  · intro y hyL hy2
    obtain ⟨z, hz, hzFM⟩ := hne
    have hzL : z ∈ zHull Z F := Cor713.mem_zHull_of_mem hz (Subgroup.mem_inf.mp hzFM).1
    have hyy : y * y = 1 := by rw [← pow_two, ← hy2]; exact pow_orderOf_eq_one y
    refine hD.mem_of_involution S.invariant ⟨z, hz, hzL⟩ hyy ?_ ?_
    · refine ⟨y, ?_, by rw [hu1, one_mul]⟩
      have h : y ∈ ((commutator ↥(zHull Z F)).map (zHull Z F).subtype) ⊔ zpowers (u₀ : X) :=
        Eq.mp (congrArg (fun H => y ∈ H) hD.sup) hyL
      rwa [hu1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at h
    · intro o ho hyo
      rw [hu1, one_mul] at hyo
      exact CFSG.OddInversion.notMem_of_odd_card hD.O_odd hy2 (hyo ▸ ho)

end CFSG.GH74.Uniqueness
