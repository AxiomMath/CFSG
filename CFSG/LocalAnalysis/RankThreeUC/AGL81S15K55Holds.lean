module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K55Module
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K55Gen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541Even
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Gen2
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
  CFSG.QuasithinUnique.Setup.Family

namespace K55Proof

section Dict

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem subOf_sup (N₁ N₂ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) :
    subOf hV (N₁ ⊔ N₂) = subOf hV N₁ ⊔ subOf hV N₂ := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    rw [elt_add]
    exact Subgroup.mul_mem_sup ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  · exact sup_le ((subOf_le_subOf_iff hV).2 le_sup_left) ((subOf_le_subOf_iff hV).2 le_sup_right)

theorem subOf_inf (N₁ N₂ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) :
    subOf hV (N₁ ⊓ N₂) = subOf hV N₁ ⊓ subOf hV N₂ := by
  ext g
  constructor
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨w, h1, rfl⟩, ⟨w, h2, rfl⟩⟩
  · rintro ⟨⟨w₁, h1, rfl⟩, ⟨w₂, h2, h⟩⟩
    have : w₂ = w₁ := elt_injective hV h
    subst this
    exact ⟨w₂, ⟨h1, h2⟩, rfl⟩

theorem subOf_bot : subOf hV (⊥ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) = ⊥ := by
  ext g
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw0 : w = 0 := (Submodule.mem_bot _).1 hw
    rw [hw0, elt_zero]
    exact Subgroup.one_mem _
  · intro hg
    rw [Subgroup.mem_bot] at hg
    subst hg
    exact ⟨0, Submodule.zero_mem _, elt_zero hV⟩

end Dict

section Equiv

noncomputable def slEquivGL3 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL32 :=
  MulEquiv.ofBijective
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* _)
    CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two

theorem nonempty_equiv_gl32 {S : Type} [Group S] (h : KFactsPair.IsLThreeOfExp 1 S) :
    Nonempty (S ≃* GL32) := by
  rcases h with ⟨-, d, q, hq7, hd, ⟨e⟩⟩ | ⟨h2, -⟩
  · obtain ⟨e'⟩ := K541Proof.nonempty_equiv_sl3_two_of_catalog_A1 d q hq7 hd e
    exact ⟨e'.trans ((CFSG.LargeExtraspecial.A2Mod.slEquiv
      CFSG.LargeExtraspecial.A2Mod.galoisFieldTwoOneEquiv).trans slEquivGL3)⟩
  · exact absurd h2 (by norm_num)

end Equiv

section Natural

theorem isElemAbelian_of_le' {Y : Type*} [Group Y] {A B : Subgroup Y} (h : A ≤ B)
    (hB : IsElemAbelian 2 B) : IsElemAbelian 2 A :=
  ⟨⟨⟨fun a b => Subtype.ext (congrArg (Subtype.val : ↥B → Y)
    (hB.1.is_comm.comm ⟨a, h a.2⟩ ⟨b, h b.2⟩))⟩⟩, fun x hx => hB.2 x (h hx)⟩

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

open KFactsPair in
theorem isNaturalLThreeTwo_of_modEmb {Ls : Subgroup (X ⧸ gnC T)} (eL : ↥Ls ≃* GL32)
    {τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3)} (hτ : Function.Injective τ)
    {ι : Vec3 →ₗ[ZMod 2] Additive (IntMod (gnV T) hV)} (hι : ModEmb (gnRep hV) eL τ ι) :
    IsNaturalLThreeTwo (Ls.comap (toStar T)) (subOf hV (LinearMap.range ι)) := by
  classical
  set N := subOf hV (LinearMap.range ι) with hN
  have hact : ∀ (g : X) (hg : (QuotientGroup.mk g : X ⧸ gnC T) ∈ Ls) (v : Vec3),
      gnRep hV (QuotientGroup.mk g) (ι v) = ι (τ (eL ⟨QuotientGroup.mk g, hg⟩) v) := by
    intro g hg v
    have h := hι.2 (eL ⟨QuotientGroup.mk g, hg⟩) v
    rw [MulEquiv.symm_apply_apply] at h
    exact h.symm
  have hmemN : ∀ n : X, n ∈ N ↔ ∃ v, elt hV (ι v) = n := by
    intro n
    constructor
    · rintro ⟨w, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨ι v, ⟨v, rfl⟩, rfl⟩
  have hinv : ∀ g : X, (QuotientGroup.mk g : X ⧸ gnC T) ∈ Ls → ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    obtain ⟨v, rfl⟩ := (hmemN n).1 hn
    refine (hmemN _).2 ⟨τ (eL ⟨QuotientGroup.mk g, hg⟩) v, ?_⟩
    rw [← hact g hg v, elt_gnRep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isElemAbelian_of_le' (subOf_le_gnV hV _) hV
  · rw [card_subOf]
    have h1 : Nat.card ↥(LinearMap.range ι) = Nat.card Vec3 :=
      (Nat.card_congr (LinearEquiv.ofInjective ι hι.1).toEquiv).symm
    rw [h1]
    simp [Nat.card_eq_fintype_card]
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hinv g hg h hh
    · intro hh
      have hg' : (QuotientGroup.mk g⁻¹ : X ⧸ gnC T) ∈ Ls := by
        rw [QuotientGroup.mk_inv]
        exact Ls.inv_mem hg
      have h1 := hinv g⁻¹ hg' _ hh
      have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [e] at h1
      exact h1
  ·
    set L' : Subgroup X := Ls.comap (toStar T) with hL'
    let mkL : ↥L' →* ↥Ls := ((toStar T).comp L'.subtype).codRestrict Ls (fun g => g.2)
    have hker : (Subgroup.centralizer (N : Set X)).subgroupOf L' = mkL.ker := by
      ext g
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      have hgL : (QuotientGroup.mk (g : X) : X ⧸ gnC T) ∈ Ls := g.2
      constructor
      · intro hc
        have hfix : ∀ v, gnRep hV (QuotientGroup.mk (g : X)) (ι v) = ι v := by
          intro v
          apply elt_injective hV
          rw [elt_gnRep]
          have hn : elt hV (ι v) ∈ N := (hmemN _).2 ⟨v, rfl⟩
          have h1 := Subgroup.mem_centralizer_iff.1 hc _ hn
          have e : (g : X) * elt hV (ι v) * (g : X)⁻¹ = elt hV (ι v) := by
            rw [← h1]
            group
          exact e
        have h2 : τ (eL ⟨QuotientGroup.mk (g : X), hgL⟩) = 1 := by
          refine LinearEquiv.ext fun v => ?_
          apply hι.1
          rw [← hact (g : X) hgL v, hfix v]
          rfl
        have h3 : eL ⟨QuotientGroup.mk (g : X), hgL⟩ = 1 := hτ (by rw [h2, map_one])
        have h4 : (⟨QuotientGroup.mk (g : X), hgL⟩ : ↥Ls) = 1 := eL.injective (by rw [h3, map_one])
        exact Subtype.ext (congrArg Subtype.val h4)
      · intro h1
        have h2 : (QuotientGroup.mk (g : X) : X ⧸ gnC T) = 1 := congrArg Subtype.val h1
        have h3 : (g : X) ∈ gnC T := (QuotientGroup.eq_one_iff _).1 h2
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        have hhV : h ∈ gnV T := subOf_le_gnV hV _ hh
        exact (Subgroup.mem_centralizer_iff.1 h3 h hhV)
    have hsurj : Function.Surjective mkL := by
      intro q
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q.1
      refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
      rw [hL', Subgroup.mem_comap]
      show (QuotientGroup.mk g : X ⧸ gnC T) ∈ Ls
      rw [hg]
      exact q.2
    show ((Subgroup.centralizer (N : Set X)).subgroupOf L').index = 168
    rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
      Nat.card_congr eL.toEquiv, card_GL32]

end Natural

section Iso

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

@[expose] noncomputable def eltHom (N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) :
    Multiplicative ↥N →* ↥(subOf hV N) where
  toFun w := ⟨elt hV (((Multiplicative.toAdd w : ↥N)) : Additive (IntMod (gnV T) hV)),
    ⟨_, (Multiplicative.toAdd w).2, rfl⟩⟩
  map_one' := Subtype.ext (by simp [elt_zero])
  map_mul' a b := Subtype.ext (by simp [elt_add])

theorem eltHom_bijective (N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) :
    Function.Bijective (eltHom hV N) := by
  refine ⟨fun a b h => ?_, fun g => ?_⟩
  · have h1 := congrArg Subtype.val h
    have h2 : ((Multiplicative.toAdd a : ↥N) : Additive (IntMod (gnV T) hV)) =
        ((Multiplicative.toAdd b : ↥N) : Additive (IntMod (gnV T) hV)) := elt_injective hV h1
    exact Multiplicative.toAdd.injective (Subtype.ext h2)
  · obtain ⟨g, ⟨w, hw, hg⟩⟩ := g
    exact ⟨Multiplicative.ofAdd ⟨w, hw⟩, Subtype.ext hg⟩

@[expose] noncomputable def subOfEquiv (N₁ N₂ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)))
    (φ : ↥N₁ ≃ₗ[ZMod 2] ↥N₂) : ↥(subOf hV N₁) ≃* ↥(subOf hV N₂) :=
  (MulEquiv.ofBijective (eltHom hV N₁) (eltHom_bijective hV N₁)).symm.trans
    ((AddEquiv.toMultiplicative φ.toAddEquiv).trans
      (MulEquiv.ofBijective (eltHom hV N₂) (eltHom_bijective hV N₂)))

theorem subOfEquiv_elt (N₁ N₂ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)))
    (φ : ↥N₁ ≃ₗ[ZMod 2] ↥N₂) (w : ↥N₁) (a : ↥(subOf hV N₁))
    (h : (a : X) = elt hV (w : Additive (IntMod (gnV T) hV))) :
    ((subOfEquiv hV N₁ N₂ φ a : ↥(subOf hV N₂)) : X) =
      elt hV ((φ w : ↥N₂) : Additive (IntMod (gnV T) hV)) := by
  obtain rfl : a = ⟨elt hV (w : Additive (IntMod (gnV T) hV)), ⟨w, w.2, rfl⟩⟩ := Subtype.ext h
  have h1 : (⟨elt hV (w : Additive (IntMod (gnV T) hV)), ⟨w, w.2, rfl⟩⟩ : ↥(subOf hV N₁)) =
      MulEquiv.ofBijective (eltHom hV N₁) (eltHom_bijective hV N₁) (Multiplicative.ofAdd w) := rfl
  rw [subOfEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h1, MulEquiv.symm_apply_apply]
  rfl

theorem exists_conj_equiv (Ls : Subgroup (X ⧸ gnC T))
    (N₁ N₂ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)))
    (h₁ : ∀ q ∈ Ls, ∀ w ∈ N₁, gnRep hV q w ∈ N₁) (φ : ↥N₁ ≃ₗ[ZMod 2] ↥N₂)
    (hφ : ∀ (q : X ⧸ gnC T) (hq : q ∈ Ls) (w : ↥N₁),
      ((φ ⟨gnRep hV q (w : Additive (IntMod (gnV T) hV)), h₁ q hq w w.2⟩ : ↥N₂) :
        Additive (IntMod (gnV T) hV)) = gnRep hV q ((φ w : ↥N₂) : Additive (IntMod (gnV T) hV))) :
    ∃ f : ↥(subOf hV N₁) ≃* ↥(subOf hV N₂), ∀ l ∈ Ls.comap (toStar T), ∀ a b : ↥(subOf hV N₁),
      (b : X) = l * (a : X) * l⁻¹ → (f b : X) = l * (f a : X) * l⁻¹ := by
  refine ⟨subOfEquiv hV N₁ N₂ φ, fun l hl a b hab => ?_⟩
  obtain ⟨wa, hwa, haeq⟩ := a.2
  obtain ⟨wb, hwb, hbeq⟩ := b.2
  have hq : (QuotientGroup.mk l : X ⧸ gnC T) ∈ Ls := hl
  have hwb' : wb = gnRep hV (QuotientGroup.mk l) wa := by
    apply elt_injective hV
    rw [elt_gnRep, haeq, hbeq]
    exact hab
  have hsub : (⟨wb, hwb⟩ : ↥N₁) = ⟨gnRep hV (QuotientGroup.mk l) wa, h₁ _ hq wa hwa⟩ :=
    Subtype.ext hwb'
  rw [subOfEquiv_elt hV N₁ N₂ φ ⟨wa, hwa⟩ a haeq.symm, subOfEquiv_elt hV N₁ N₂ φ ⟨wb, hwb⟩ b hbeq.symm,
    hsub, hφ _ hq ⟨wa, hwa⟩, elt_gnRep]

end Iso

section Pair

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem modEmb_act {Ls : Subgroup (X ⧸ gnC T)} (eL : ↥Ls ≃* GL32)
    {τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3)} {ι : Vec3 →ₗ[ZMod 2] Additive (IntMod (gnV T) hV)}
    (hι : ModEmb (gnRep hV) eL τ ι) (q : X ⧸ gnC T) (hq : q ∈ Ls) (v : Vec3) :
    gnRep hV q (ι v) = ι (τ (eL ⟨q, hq⟩) v) := by
  have h := hι.2 (eL ⟨q, hq⟩) v
  rw [MulEquiv.symm_apply_apply] at h
  exact h.symm

@[expose] noncomputable def rangeEquiv {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ι₁ ι₂ : Vec3 →ₗ[ZMod 2] M) (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂) :
    ↥(LinearMap.range ι₁) ≃ₗ[ZMod 2] ↥(LinearMap.range ι₂) :=
  (LinearEquiv.ofInjective ι₁ h₁).symm.trans (LinearEquiv.ofInjective ι₂ h₂)

theorem rangeEquiv_apply {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ι₁ ι₂ : Vec3 →ₗ[ZMod 2] M) (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂)
    (v : Vec3) (x : ↥(LinearMap.range ι₁)) (h : (x : M) = ι₁ v) :
    (rangeEquiv ι₁ ι₂ h₁ h₂ x : M) = ι₂ v := by
  obtain rfl : x = ⟨ι₁ v, ⟨v, rfl⟩⟩ := Subtype.ext h
  have e : (LinearEquiv.ofInjective ι₁ h₁).symm ⟨ι₁ v, ⟨v, rfl⟩⟩ = v := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  rw [rangeEquiv, LinearEquiv.trans_apply, e]
  rfl

theorem exists_conj_equiv_of_modEmb {Ls : Subgroup (X ⧸ gnC T)} (eL : ↥Ls ≃* GL32)
    {τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3)} {ι₁ ι₂ : Vec3 →ₗ[ZMod 2] Additive (IntMod (gnV T) hV)}
    (h₁ : ModEmb (gnRep hV) eL τ ι₁) (h₂ : ModEmb (gnRep hV) eL τ ι₂) :
    ∃ f : ↥(subOf hV (LinearMap.range ι₁)) ≃* ↥(subOf hV (LinearMap.range ι₂)),
      ∀ l ∈ Ls.comap (toStar T), ∀ a b : ↥(subOf hV (LinearMap.range ι₁)),
        (b : X) = l * (a : X) * l⁻¹ → (f b : X) = l * (f a : X) * l⁻¹ := by
  have hinv : ∀ q ∈ Ls, ∀ w ∈ LinearMap.range ι₁, gnRep hV q w ∈ LinearMap.range ι₁ := by
    rintro q hq _ ⟨v, rfl⟩
    exact ⟨τ (eL ⟨q, hq⟩) v, (modEmb_act hV eL h₁ q hq v).symm⟩
  refine exists_conj_equiv hV Ls _ _ hinv (rangeEquiv ι₁ ι₂ h₁.1 h₂.1) ?_
  intro q hq w
  obtain ⟨v, hv⟩ := w.2
  have hw : (w : Additive (IntMod (gnV T) hV)) = ι₁ v := hv.symm
  have hw' : ((⟨gnRep hV q (w : Additive (IntMod (gnV T) hV)), hinv q hq _ w.2⟩ :
      ↥(LinearMap.range ι₁)) : Additive (IntMod (gnV T) hV)) = ι₁ (τ (eL ⟨q, hq⟩) v) := by
    show gnRep hV q (w : Additive (IntMod (gnV T) hV)) = _
    rw [hw]
    exact modEmb_act hV eL h₁ q hq v
  rw [rangeEquiv_apply ι₁ ι₂ h₁.1 h₂.1 _ _ hw', rangeEquiv_apply ι₁ ι₂ h₁.1 h₂.1 v w hw]
  exact (modEmb_act hV eL h₂ q hq v).symm

end Pair

end K55Proof

theorem K55_holds : K55 := by
  classical
  intro X _ _ T hX Ls hL hJ h3
  have hC : CharTwo (⊤ : Subgroup X) := hX.charTwo
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hC hQT
  letI : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hVT : gnV T ≤ T := gnV_le_of_le hC hQT
  obtain ⟨A, hA, hAN, hLA⟩ := exists_offender_of_le hV hVT Ls hL hJ
  set ρ := gnRep hV with hρ
  have hinj : Function.Injective ρ := gnRep_injective hV
  have hA2 := isElementaryAbelian_map_mk hA
  have hfaith : ∀ a ∈ A.map (QuotientGroup.mk' (gnC T)), (∀ v, ρ a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn ρ (A.map (QuotientGroup.mk' (gnC T))) ⊤ :=
    (isBestOffender_iff_on ρ _ hfaith).mp ⟨hA2, isBestOffender_gnRep_of_le hV hVT hA⟩
  obtain ⟨eL⟩ := K55Proof.nonempty_equiv_gl32 h3
  have hLcard : Nat.card ↥Ls = 168 := by rw [Nat.card_congr eL.toEquiv, K55Proof.card_GL32]
  obtain ⟨F, hFL, hF21⟩ := K55Proof.exists_subgroup_card_21_of_equiv eL
  have hFodd : Odd (Nat.card F) := by rw [hF21]; exact ⟨10, rfl⟩
  obtain ⟨S₀, hS₀, hgen⟩ := K55Proof.exists_sylow_generation hV hX.sylow hL.2.1
  have hS₀card : Nat.card S₀ = 8 := by
    rw [hS₀.card_eq, hLcard]
    have : (168 : ℕ).factorization 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      decide +kernel
    rw [this]
    norm_num
  have hLfs := K55Proof.exists_mul_of_sylow hFL hF21 hS₀.le hS₀card hLcard
  have hFix := K55Proof.fixed_eq_zero_of_generation ρ hFodd hLfs hgen
  obtain ⟨τ, hτ, ι₁, ι₂, hι₁, hcase⟩ :=
    K55Proof.k55_module ρ hinj eL hA2 hAN hLA hb hFL hFodd hFix
  have hτinj : Function.Injective τ := by
    rcases hτ with rfl | rfl
    · exact repV_injective
    · exact repDual_injective
  have hUs : subOf hV (commOn ρ Ls ⊤) = ⁅gnV T, Ls.comap (toStar T)⁆ :=
    subOf_commOn hV Ls
  rcases hcase with ⟨hr, -⟩ | ⟨hι₂, hsup, hinf⟩
  · refine ⟨subOf hV (LinearMap.range ι₁), ⊥,
      K55Proof.isNaturalLThreeTwo_of_modEmb hV eL hτinj hι₁, ?_, Or.inl rfl⟩
    rw [sup_bot_eq, ← hUs, hr]
  · refine ⟨subOf hV (LinearMap.range ι₁), subOf hV (LinearMap.range ι₂),
      K55Proof.isNaturalLThreeTwo_of_modEmb hV eL hτinj hι₁, ?_,
      Or.inr ⟨K55Proof.isNaturalLThreeTwo_of_modEmb hV eL hτinj hι₂, ?_, ?_⟩⟩
    · rw [← K55Proof.subOf_sup, hsup, hUs]
    · rw [← K55Proof.subOf_inf, hinf, K55Proof.subOf_bot]
    · exact K55Proof.exists_conj_equiv_of_modEmb hV eL hι₁ hι₂

end CFSG.LocalAnalysis.RankThreeUC.S15
