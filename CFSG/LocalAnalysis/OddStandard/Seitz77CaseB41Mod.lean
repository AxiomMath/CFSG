module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Pre
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Grp
public import CFSG.LocalAnalysis.OddStandard.Seitz77Mod44
public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreLie
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint CFSG.LocalCores
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf)
open scoped commutatorElement

noncomputable def supEquivProd {Q : Type*} [Group Q] (S₁ S₂ : Subgroup Q)
    (hc : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) (hd : Disjoint S₁ S₂) :
    ↥(S₁ ⊔ S₂) ≃* ↥S₁ × ↥S₂ := by
  have hcomm' : ∀ (a : ↥S₁) (b : ↥S₂), Commute (S₁.subtype a) (S₂.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod S₁.subtype S₂.subtype hcomm') :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm').mpr
      ⟨S₁.subtype_injective, S₂.subtype_injective, by
        simpa only [Subgroup.range_subtype] using hd⟩
  have hr : (MonoidHom.noncommCoprod S₁.subtype S₂.subtype hcomm').range = S₁ ⊔ S₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact (MulEquiv.subgroupCongr hr.symm).trans (MonoidHom.ofInjective hinj).symm

structure FacExtra {G : Type} [Group G] (W F₁ F₂ H₁ H₂ : Subgroup G) (t : G) : Prop where
  card₁ : Nat.card F₁ = 16
  card₂ : Nat.card F₂ = 16
  irr₁ : ∀ U : Subgroup G, U ≤ F₁ → (∀ y ∈ H₁, ∀ u ∈ U, y * u * y⁻¹ ∈ U) → U = ⊥ ∨ U = F₁
  irr₂ : ∀ U : Subgroup G, U ≤ F₂ → (∀ y ∈ H₂, ∀ u ∈ U, y * u * y⁻¹ ∈ U) → U = ⊥ ∨ U = F₂
  faithful₁ : ∀ y ∈ H₁, (∀ f ∈ F₁, y * f * y⁻¹ = f) → y ∈ centralizer (W : Set G)
  faithful₂ : ∀ y ∈ H₂, (∀ f ∈ F₂, y * f * y⁻¹ = f) → y ∈ centralizer (W : Set G)
  fpf₁ : ∀ y ∈ H₁, y ∉ centralizer (W : Set G) → y ^ 3 ∈ centralizer (W : Set G) →
    ∀ f ∈ F₁, y * f * y⁻¹ = f → f = 1
  fpf₂ : ∀ y ∈ H₂, y ∉ centralizer (W : Set G) → y ^ 3 ∈ centralizer (W : Set G) →
    ∀ f ∈ F₂, y * f * y⁻¹ = f → f = 1
  swap₁ : ∀ f ∈ F₁, t * f * t⁻¹ ∈ F₂
  swap₂ : ∀ f ∈ F₂, t * f * t⁻¹ ∈ F₁
  idx₁ : (centralizer (W : Set G)).relIndex H₁ = 60
  idx₂ : (centralizer (W : Set G)).relIndex H₂ = 60
  t_mem : t ∈ normalizer (W : Set G)
  perf_le : ∀ Q : Subgroup G, Q ≤ normalizer (W : Set G) → ⁅Q, Q⁆ = Q → Q ≤ H₁ ⊔ H₂
  a5₁ : ∃ π : ↥(perfectResidualOf H₁) →* alternatingGroup (Fin 5), Function.Surjective π ∧
    ∀ m : ↥(perfectResidualOf H₁), π m = 1 ↔ (m : G) ∈ centralizer (W : Set G)
  a5₂ : ∃ π : ↥(perfectResidualOf H₂) →* alternatingGroup (Fin 5), Function.Surjective π ∧
    ∀ m : ↥(perfectResidualOf H₂), π m = 1 ↔ (m : G) ∈ centralizer (W : Set G)

section Coord

variable {G : Type} [Group G] {W : Subgroup G}

@[expose] def coordSub (κ : ↥W ≃* Multiplicative (Fin 8 → ZMod 2))
    (F : Submodule (ZMod 2) (Fin 8 → ZMod 2)) : Subgroup G where
  carrier := {w | ∃ h : w ∈ W, Multiplicative.toAdd (κ ⟨w, h⟩) ∈ F}
  one_mem' := ⟨W.one_mem, by
    have : κ ⟨1, W.one_mem⟩ = 1 := map_one κ
    simp [this]⟩
  mul_mem' := by
    rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
    refine ⟨W.mul_mem ha hb, ?_⟩
    have : κ ⟨a * b, W.mul_mem ha hb⟩ = κ ⟨a, ha⟩ * κ ⟨b, hb⟩ := map_mul κ ⟨a, ha⟩ ⟨b, hb⟩
    rw [this, toAdd_mul]
    exact F.add_mem hfa hfb
  inv_mem' := by
    rintro a ⟨ha, hfa⟩
    refine ⟨W.inv_mem ha, ?_⟩
    have : κ ⟨a⁻¹, W.inv_mem ha⟩ = (κ ⟨a, ha⟩)⁻¹ := map_inv κ ⟨a, ha⟩
    rw [this, toAdd_inv]
    exact F.neg_mem hfa

variable {κ : ↥W ≃* Multiplicative (Fin 8 → ZMod 2)} {F F' : Submodule (ZMod 2) (Fin 8 → ZMod 2)}

theorem coordSub_le : (coordSub κ F : Subgroup G) ≤ W := fun _ hw => hw.1

theorem mem_coordSub_of {w : ↥W} (h : Multiplicative.toAdd (κ w) ∈ F) : (w : G) ∈ coordSub κ F :=
  ⟨w.2, h⟩

theorem card_coordSub : Nat.card (coordSub κ F : Subgroup G) = Nat.card F := by
  refine Nat.card_congr
    { toFun := fun w => ⟨Multiplicative.toAdd (κ ⟨w.1, w.2.1⟩), w.2.2⟩
      invFun := fun f => ⟨(κ.symm (Multiplicative.ofAdd f.1) : ↥W), ⟨(κ.symm _).2, by
        simp⟩⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun f => Subtype.ext (by simp) }

theorem coordSub_inf (h : Disjoint F F') : (coordSub κ F ⊓ coordSub κ F' : Subgroup G) = ⊥ := by
  refine eq_bot_iff.mpr fun w hw => ?_
  obtain ⟨⟨hW, h1⟩, ⟨hW', h2⟩⟩ := Subgroup.mem_inf.mp hw
  have : Multiplicative.toAdd (κ ⟨w, hW⟩) = 0 :=
    Submodule.disjoint_def.mp h _ h1 h2
  have h3 : κ ⟨w, hW⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using this
  have h4 : (⟨w, hW⟩ : ↥W) = 1 := κ.injective (h3.trans (map_one κ).symm)
  have : w = 1 := congrArg Subtype.val h4
  exact this

theorem coordSub_sup (h : F ⊔ F' = ⊤) : (coordSub κ F ⊔ coordSub κ F' : Subgroup G) = W := by
  refine le_antisymm (sup_le coordSub_le coordSub_le) fun w hw => ?_
  have hv : Multiplicative.toAdd (κ ⟨w, hw⟩) ∈ F ⊔ F' := h ▸ Submodule.mem_top
  obtain ⟨f, hf, f', hf', hff⟩ := Submodule.mem_sup.mp hv
  let a : ↥W := κ.symm (Multiplicative.ofAdd f)
  let b : ↥W := κ.symm (Multiplicative.ofAdd f')
  have ha : (a : G) ∈ coordSub κ F := mem_coordSub_of (by simpa [a] using hf)
  have hb : (b : G) ∈ coordSub κ F' := mem_coordSub_of (by simpa [b] using hf')
  have hab : (⟨w, hw⟩ : ↥W) = a * b := by
    apply κ.injective
    rw [map_mul]
    simp only [a, b, MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    simpa using hff.symm
  have : w = (a : G) * b := congrArg Subtype.val hab
  rw [this]
  exact Subgroup.mul_mem_sup ha hb

end Coord

section Mod

variable {G : Type} [Group G] [Finite G] {A R X O Sy Wt P : Subgroup G} {t : G}
  (H : Setup27 A R X O Sy Wt P t)

include H in
theorem Setup27.exists_rep :
    ∃ (κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2))
      (ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)), Function.Injective ρ ∧
      ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)), κ (alpha27 (Sy ⊓ Wt) h w) =
        Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
          (Multiplicative.toAdd (κ w))) := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hWab := hS.elem_inf_Wt hSy hWt
  exact exists_gl_rep (W := ↥(Sy ⊓ Wt))
    (fun a b => Subtype.ext (L34.comm_of_isElemAbelian hWab a.2 b.2))
    (fun a => Subtype.ext (by
      have := hWab.2 a.1 a.2
      rwa [sq] at this)) (hS.card_inf_Wt hSy hWt) (alpha27 (Sy ⊓ Wt)) (alpha27_injective _)

structure Setup27.FacSit (S₁ S₂ : Subgroup (Ntil27 (Sy ⊓ Wt))) : Prop where
  lie₁ : LieModel ↥S₁ .PSL 2 2 2
  lie₂ : LieModel ↥S₂ .PSL 2 2 2
  sup_eq : S₁ ⊔ S₂ = layer (Ntil27 (Sy ⊓ Wt))
  disj : Disjoint S₁ S₂
  comm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x
  swap : ∀ x ∈ S₁, H.ttilde27 * x * H.ttilde27⁻¹ ∈ S₂
  X_eq : H.X27 = centralizer ({H.ttilde27} : Set (Ntil27 (Sy ⊓ Wt))) ⊓
    layer (Ntil27 (Sy ⊓ Wt))

theorem Setup27.exists_facSit (B : Out27B (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27) :
    ∃ S₁ S₂ : Subgroup (Ntil27 (Sy ⊓ Wt)), H.FacSit S₁ S₂ := by
  obtain ⟨S₁, S₂, h₁, h₂, hsup, hdisj, hcomm, hswap, hX⟩ := B.exists_factors
  exact ⟨S₁, S₂, ⟨h₁, h₂, hsup, hdisj, hcomm, hswap, hX⟩⟩

variable {H} {S₁ S₂ : Subgroup (Ntil27 (Sy ⊓ Wt))}

theorem Setup27.facData (hF : H.FacSit S₁ S₂) :
    FacData H.piH27 S₁ S₂ := by
  obtain ⟨hs₁, hc₁⟩ := oddCore_lieModel_psl_two_two_two hF.lie₁
  obtain ⟨hs₂, hc₂⟩ := oddCore_lieModel_psl_two_two_two hF.lie₂
  have hcent := centralizer_layer_eq_bot27 H.local27
  have hT : TwoComp (Ntil27 (Sy ⊓ Wt)) S₁ S₂ :=
    ⟨hs₁, hs₂, exists_noncomm_of_simple_card_sixty hc₁, exists_noncomm_of_simple_card_sixty hc₂,
      hF.sup_eq, hF.disj, hF.comm, hcent⟩
  obtain ⟨κ, ρ, hρ, -⟩ := H.exists_rep
  have hmapH := map_fHhat H.piH27_surjective hT hc₁ hc₂
  have hperf : commutator ↥(fHhat H.piH27 S₁ S₂) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr fHhat_perfect)
  let e : ↥((fHhat H.piH27 S₁ S₂).map H.piH27) ≃* ↥S₁ × ↥S₂ :=
    (MulEquiv.subgroupCongr hmapH).trans (supEquivProd S₁ S₂ hF.comm hF.disj)
  have hker := odd_core_inf_ker_eq_bot_B_of_lieModel ρ hρ H.piH27 (fHhat H.piH27 S₁ S₂) hperf
    H.odd_card_ker_piH27 hF.lie₁ hF.lie₂ e
  exact ⟨H.piH27_surjective, hT, hc₁, hc₂, hker.1⟩

theorem Setup27.fpf_of_orderOf_three
    {κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)}
    (hρ : ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)), κ (alpha27 (Sy ⊓ Wt) h w) =
      Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
        (Multiplicative.toAdd (κ w))))
    {x : Hh27 (Sy ⊓ Wt)} (hx : x ∈ H.piHP.range) (hx3 : orderOf x = 3) (w : Fin 8 → ZMod 2)
    (hw : (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w) : w = 0 := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hRW : R ≤ Sy ⊓ Wt := hS.W_le_inf_Wt hSy hWt
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥P →* MulAut ↥R, σ = conjAct27 R P H.hP.le_norm := ⟨_, rfl⟩
  have hker : H.piHP.ker = σ.ker := hσ ▸ H.ker_piHP_eq
  have hcard60 : Nat.card ↥σ.range = 60 := hσ ▸ H.hP.card
  have htrans' : ∀ r s : ↥R, r ≠ 1 → s ≠ 1 → ∃ g ∈ σ.range, g r = s := by
    intro r s hr hs
    obtain ⟨p, hp, hps⟩ := H.hP.trans r.1 r.2 s.1 s.2 (fun h => hr (Subtype.ext h))
      (fun h => hs (Subtype.ext h))
    refine ⟨σ ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, Subtype.ext ?_⟩
    rw [hσ]
    exact hps
  have hRc : Nat.card ↥R = 16 := hS.W_card
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥(Sy ⊓ Wt), w₀ = κ.symm (Multiplicative.ofAdd w) := ⟨_, rfl⟩
  have hκw : κ w₀ = Multiplicative.ofAdd w := by rw [hw₀]; exact MulEquiv.apply_symm_apply _ _
  have hfix : alpha27 (Sy ⊓ Wt) (H.piHP q) w₀ = w₀ := by
    apply κ.injective
    rw [hρ, hκw, toAdd_ofAdd, hw]
  have hpw : (q : G) * (w₀ : G) * (q : G)⁻¹ = (w₀ : G) := congrArg Subtype.val hfix
  have hq3 : (σ q) ^ 3 = 1 := by
    have h1 : (H.piHP q) ^ 3 = 1 := by
      rw [← hx3]
      exact pow_orderOf_eq_one _
    have h2 : q ^ 3 ∈ H.piHP.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact h1
    rw [hker, MonoidHom.mem_ker, map_pow] at h2
    exact h2
  have hkey : ∀ r : ↥R, r ≠ 1 → σ q r = r → False := by
    intro r hr1 hfixr
    have h1 : σ q = 1 := stab_of_trans_sixty hRc σ.range hcard60 htrans' (σ q) ⟨q, rfl⟩ hq3 r
      hr1 hfixr
    have h2 : q ∈ H.piHP.ker := by
      rw [hker]
      exact h1
    rw [MonoidHom.mem_ker] at h2
    rw [h2, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  have hσapply : ∀ r : ↥R, ((σ q r : ↥R) : G) = (q : G) * (r : G) * (q : G)⁻¹ := by
    intro r
    rw [hσ]
    rfl
  have hcR : t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ ∈ R :=
    hS.commutator_t_mem_W (hSy.le (mem_inf.mp w₀.2).1)
  have hqt : (q : G) * t = t * (q : G) := H.P_comm_t q.2
  have hrfix : σ q ⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ =
      ⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ := by
    apply Subtype.ext
    rw [hσapply]
    show (q : G) * (t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹) * (q : G)⁻¹ = _
    have e1 : (q : G) * t * (q : G)⁻¹ = t := by rw [hqt]; group
    calc (q : G) * (t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹) * (q : G)⁻¹
        = ((q : G) * t * (q : G)⁻¹) * ((q : G) * (w₀ : G) * (q : G)⁻¹) *
          ((q : G) * t * (q : G)⁻¹)⁻¹ * ((q : G) * (w₀ : G) * (q : G)⁻¹)⁻¹ := by group
      _ = t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ := by rw [e1, hpw]
  have hr1 : (⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ : ↥R) = 1 := by
    by_contra hne
    exact hkey _ hne hrfix
  have hw₀R : (w₀ : G) ∈ R := by
    have h1 : t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ = 1 := congrArg Subtype.val hr1
    have h2 : (w₀ : G) * t = t * (w₀ : G) := by
      have := mul_inv_eq_one.mp h1
      calc (w₀ : G) * t = (t * (w₀ : G) * t⁻¹) * t := by rw [this]
        _ = t * (w₀ : G) := by group
    rw [← hS.inf_Wt_inf_centralizer_t hSy hWt]
    exact mem_inf.mpr ⟨w₀.2, mem_centralizer_singleton_iff.mpr h2⟩
  have hw₀1 : w₀ = 1 := by
    by_contra hne
    apply hkey ⟨(w₀ : G), hw₀R⟩ (fun h => hne (Subtype.ext (by
      have h' : (w₀ : G) = 1 := congrArg Subtype.val h
      exact h')))
    apply Subtype.ext
    rw [hσapply]
    exact hpw
  rw [hw₀1, map_one] at hκw
  have h0 := congrArg Multiplicative.toAdd hκw
  simpa using h0.symm

@[expose] noncomputable def Setup27.that (H : Setup27 A R X O Sy Wt P t) :
    Hh27 (Sy ⊓ Wt) :=
  qN (Sy ⊓ Wt) ⟨t, H.sit.S.t_mem_normalizer_inf_Wt H.sit.hSy H.sit.hWt⟩

theorem Setup27.piH27_that : H.piH27 H.that = H.ttilde27 := rfl

theorem Setup27.that_mul_self : H.that * H.that = 1 := by
  have hS := H.sit.S
  have htN := hS.t_mem_normalizer_inf_Wt H.sit.hSy H.sit.hWt
  have : (⟨t, htN⟩ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) * ⟨t, htN⟩ = 1 :=
    Subtype.ext hS.t_sq
  rw [Setup27.that, ← map_mul, this, map_one]

theorem Setup27.ttilde_mul_self : H.ttilde27 * H.ttilde27 = 1 := by
  rw [← H.piH27_that, ← map_mul, H.that_mul_self, map_one]

theorem Setup27.FacSit.swap₂ (hF : H.FacSit S₁ S₂) {x : Ntil27 (Sy ⊓ Wt)} (hx : x ∈ S₂) :
    H.ttilde27 * x * H.ttilde27⁻¹ ∈ S₁ := by
  have hc₁ := (oddCore_lieModel_psl_two_two_two hF.lie₁).2
  have hc₂ := (oddCore_lieModel_psl_two_two_two hF.lie₂).2
  let f : ↥S₁ → ↥S₂ := fun s => ⟨H.ttilde27 * (s : Ntil27 (Sy ⊓ Wt)) * H.ttilde27⁻¹,
    hF.swap s s.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h' : H.ttilde27 * (a : Ntil27 (Sy ⊓ Wt)) * H.ttilde27⁻¹ =
        H.ttilde27 * (b : Ntil27 (Sy ⊓ Wt)) * H.ttilde27⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h')
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hc₁, hc₂])
  obtain ⟨s, hs⟩ := hbij.2 ⟨x, hx⟩
  have hsx : H.ttilde27 * (s : Ntil27 (Sy ⊓ Wt)) * H.ttilde27⁻¹ = x := congrArg Subtype.val hs
  have ht2 := H.ttilde_mul_self
  have : H.ttilde27 * x * H.ttilde27⁻¹ = (s : Ntil27 (Sy ⊓ Wt)) := by
    rw [← hsx]
    calc H.ttilde27 * (H.ttilde27 * (s : Ntil27 (Sy ⊓ Wt)) * H.ttilde27⁻¹) * H.ttilde27⁻¹
        = (H.ttilde27 * H.ttilde27) * (s : Ntil27 (Sy ⊓ Wt)) *
          (H.ttilde27 * H.ttilde27)⁻¹ := by group
      _ = s := by rw [ht2]; group
  rw [this]
  exact s.2

theorem Setup27.fHhat_conj (hF : H.FacSit S₁ S₂) (g : Hh27 (Sy ⊓ Wt))
    {y : Hh27 (Sy ⊓ Wt)} (hy : y ∈ fHhat H.piH27 S₁ S₂) :
    g * y * g⁻¹ ∈ fHhat H.piH27 S₁ S₂ := by
  have : (layer (Ntil27 (Sy ⊓ Wt))).Characteristic := layer_characteristic
  refine prOf_conj_le g (fun x hx => ?_) hy
  rw [mem_comap] at hx ⊢
  rw [map_mul, map_mul, map_inv]
  rw [hF.sup_eq] at hx ⊢
  exact Subgroup.Normal.conj_mem inferInstance _ hx _

theorem Setup27.that_conj_lam₁ (hF : H.FacSit S₁ S₂) {x : Hh27 (Sy ⊓ Wt)}
    (hx : x ∈ fLam₁ H.piH27 S₁ S₂) : H.that * x * H.that⁻¹ ∈ fLam₂ H.piH27 S₁ S₂ := by
  obtain ⟨hxH, hxS⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨H.fHhat_conj hF _ hxH, ?_⟩
  rw [mem_comap, map_mul, map_mul, map_inv, H.piH27_that]
  exact hF.swap _ hxS

theorem Setup27.that_conj_lam₂ (hF : H.FacSit S₁ S₂) {x : Hh27 (Sy ⊓ Wt)}
    (hx : x ∈ fLam₂ H.piH27 S₁ S₂) : H.that * x * H.that⁻¹ ∈ fLam₁ H.piH27 S₁ S₂ := by
  obtain ⟨hxH, hxS⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨H.fHhat_conj hF _ hxH, ?_⟩
  rw [mem_comap, map_mul, map_mul, map_inv, H.piH27_that]
  exact hF.swap₂ hxS

theorem Setup27.Xh_perfect :
    ⁅H.piHP.range, H.piHP.range⁆ = H.piHP.range := by
  obtain ⟨e⟩ := H.Xh_equiv
  exact Subgroup.isPerfect_iff.mp
    (Group.isPerfect_def.mpr (s27_commutator_eq_top_of_equiv_alt5 e))

theorem Setup27.Xh_le_Hhat (hF : H.FacSit S₁ S₂) :
    H.piHP.range ≤ fHhat H.piH27 S₁ S₂ :=
  (H.facData hF).le_Hhat_of_perfect H.Xh_perfect

theorem Setup27.exists_mod44 (hF : H.FacSit S₁ S₂)
    {κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)} (hρinj : Function.Injective ρ)
    (hκρ : ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)), κ (alpha27 (Sy ⊓ Wt) h w) =
      Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
        (Multiplicative.toAdd (κ w)))) :
    ∃ F' F'' : Submodule (ZMod 2) (Fin 8 → ZMod 2),
      Mod44Split (ρ.comp (fHhat H.piH27 S₁ S₂).subtype)
        ((fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂))
        ((fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂)) (ρ H.that) F' F'' := by
  have D := H.facData hF
  have hL₁ : fLam₁ H.piH27 S₁ S₂ ≤ fHhat H.piH27 S₁ S₂ := inf_le_left
  have hL₂ : fLam₂ H.piH27 S₁ S₂ ≤ fHhat H.piH27 S₁ S₂ := inf_le_left
  have e₁ := Subgroup.subgroupOfEquivOfLe hL₁
  have e₂ := Subgroup.subgroupOfEquivOfLe hL₂
  have : IsSimpleGroup ↥(fLam₁ H.piH27 S₁ S₂) := D.Lam₁_simple
  have : IsSimpleGroup ↥(fLam₂ H.piH27 S₁ S₂) := D.Lam₂_simple
  have : IsSimpleGroup ↥((fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂)) :=
    e₁.isSimpleGroup
  have : IsSimpleGroup ↥((fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂)) :=
    e₂.isSimpleGroup
  have h60₁ : Nat.card ↥((fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂)) = 60 :=
    (Nat.card_congr e₁.toEquiv).trans D.Lam₁_card
  have h60₂ : Nat.card ↥((fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂)) = 60 :=
    (Nat.card_congr e₂.toEquiv).trans D.Lam₂_card
  have hcomm : ∀ x ∈ (fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂),
      ∀ y ∈ (fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂), x * y = y * x :=
    fun x hx y hy => Subtype.ext (D.Lam_comm hx hy)
  have hsup : (fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂) ⊔
      (fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hL₁ hL₂, D.Lam_sup, Subgroup.subgroupOf_self]
  have hinf : (fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂) ⊓
      (fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂) = ⊥ := by
    have : (fLam₁ H.piH27 S₁ S₂ ⊓ fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂) =
        (fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂) ⊓
          (fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂) := Subgroup.comap_inf _ _ _
    rw [← this, D.Lam_inf, Subgroup.bot_subgroupOf]
  have hτ : ρ H.that * ρ H.that = 1 := by rw [← map_mul, H.that_mul_self, map_one]
  have hexch : ∀ x ∈ (fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂),
      ∃ y ∈ (fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂),
        (ρ.comp (fHhat H.piH27 S₁ S₂).subtype) y =
          ρ H.that * (ρ.comp (fHhat H.piH27 S₁ S₂).subtype) x * (ρ H.that)⁻¹ := by
    intro x hx
    refine ⟨⟨H.that * (x : Hh27 (Sy ⊓ Wt)) * H.that⁻¹, H.fHhat_conj hF _ x.2⟩,
      H.that_conj_lam₁ hF hx, ?_⟩
    simp [map_mul, map_inv]
  refine mod44_of_forall (ρ.comp (fHhat H.piH27 S₁ S₂).subtype)
    (hρinj.comp (fHhat H.piH27 S₁ S₂).subtype_injective) _ _ h60₁ h60₂ hcomm hsup hinf (ρ H.that)
    hτ hexch ?_
  intro h' hh' hord h'' hh'' hconj v hv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a : Hh27 (Sy ⊓ Wt) := (h' : Hh27 (Sy ⊓ Wt)) with ha
  set b : Hh27 (Sy ⊓ Wt) := (h'' : Hh27 (Sy ⊓ Wt)) with hb
  have haL : a ∈ fLam₁ H.piH27 S₁ S₂ := hh'
  have hbL : b ∈ fLam₂ H.piH27 S₁ S₂ := hh''
  have hbta : b = H.that * a * H.that⁻¹ := by
    apply hρinj
    rw [map_mul, map_mul, map_inv]
    exact hconj
  have hab : a * b = b * a := D.Lam_comm haL hbL
  have ha3 : a ^ 3 = 1 := by
    have h1 : h' ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have := congrArg Subtype.val h1
    simpa using this
  have hb3 : b ^ 3 = 1 := by
    rw [hbta, conj_pow, ha3]
    group
  have hbt : H.that * b * H.that⁻¹ = a := by
    rw [hbta]
    calc H.that * (H.that * a * H.that⁻¹) * H.that⁻¹
        = (H.that * H.that) * a * (H.that * H.that)⁻¹ := by group
      _ = a := by rw [H.that_mul_self]; group
  have hconjab : H.that * (a * b) * H.that⁻¹ = a * b := by
    calc H.that * (a * b) * H.that⁻¹ = (H.that * a * H.that⁻¹) * (H.that * b * H.that⁻¹) := by
          group
      _ = b * a := by rw [← hbta, hbt]
      _ = a * b := hab.symm
  have hy1 : a * b ≠ 1 := by
    intro h1
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hbmem : b ∈ fLam₁ H.piH27 S₁ S₂ := hb' ▸ (fLam₁ H.piH27 S₁ S₂).inv_mem haL
    have hmem : b ∈ fLam₁ H.piH27 S₁ S₂ ⊓ fLam₂ H.piH27 S₁ S₂ :=
      Subgroup.mem_inf.mpr ⟨hbmem, hbL⟩
    rw [D.Lam_inf, Subgroup.mem_bot] at hmem
    have ha1 : a = 1 := inv_eq_one.mp (hb'.symm.trans hmem)
    have : h' = 1 := Subtype.ext ha1
    rw [this, orderOf_one] at hord
    omega
  have hy3 : (a * b) ^ 3 = 1 := by
    have hc : Commute a b := hab
    rw [hc.mul_pow, ha3, hb3, one_mul]
  have hyord : orderOf (a * b) = 3 := orderOf_eq_prime hy3 hy1
  have hyH : a * b ∈ fHhat H.piH27 S₁ S₂ := (fHhat H.piH27 S₁ S₂).mul_mem h'.2 h''.2
  have hπy : H.piH27 (a * b) ∈ H.X27 := by
    rw [hF.X_eq]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have h2 := congrArg H.piH27 hconjab
      rw [map_mul, map_mul, map_inv, H.piH27_that] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · rw [← hF.sup_eq]
      exact D.pi_mem_sup hyH
  obtain ⟨p, hp⟩ := hπy
  have hxX : H.piHP p ∈ H.piHP.range := ⟨p, rfl⟩
  have hxH : H.piHP p ∈ fHhat H.piH27 S₁ S₂ := H.Xh_le_Hhat hF hxX
  have hxy : H.piHP p = a * b := D.inj hxH hyH (by rw [← hp]; rfl)
  have hyX : a * b ∈ H.piHP.range := ⟨p, hxy⟩
  exact Setup27.fpf_of_orderOf_three hκρ hyX hyord v hv

omit [Finite G] in
theorem Setup27.kappa_conj
    {κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)}
    (hκρ : ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)), κ (alpha27 (Sy ⊓ Wt) h w) =
      Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
        (Multiplicative.toAdd (κ w))))
    {x : G} (hx : x ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) {w : G} (hw : w ∈ Sy ⊓ Wt) :
    ∃ hw' : x * w * x⁻¹ ∈ Sy ⊓ Wt,
      Multiplicative.toAdd (κ ⟨x * w * x⁻¹, hw'⟩) =
        (ρ (qG (Sy ⊓ Wt) x) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
          (Multiplicative.toAdd (κ ⟨w, hw⟩)) := by
  have hw' : x * w * x⁻¹ ∈ Sy ⊓ Wt := (mem_normalizer_iff.mp hx w).mp hw
  refine ⟨hw', ?_⟩
  have h := hκρ (qG (Sy ⊓ Wt) x) ⟨w, hw⟩
  have e : alpha27 (Sy ⊓ Wt) (qG (Sy ⊓ Wt) x) ⟨w, hw⟩ = ⟨x * w * x⁻¹, hw'⟩ :=
    Subtype.ext (qG_act hx ⟨w, hw⟩)
  rw [e] at h
  rw [h, toAdd_ofAdd]

omit [Finite G] in
theorem Setup27.coordSub_conj
    {κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)}
    (hκρ : ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)), κ (alpha27 (Sy ⊓ Wt) h w) =
      Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
        (Multiplicative.toAdd (κ w))))
    {F : Submodule (ZMod 2) (Fin 8 → ZMod 2)} {x : G}
    (hx : x ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))
    (hF : ∀ v ∈ F, (ρ (qG (Sy ⊓ Wt) x) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v ∈ F) {w : G}
    (hw : w ∈ coordSub κ F) : x * w * x⁻¹ ∈ coordSub κ F := by
  obtain ⟨hwW, hwF⟩ := hw
  obtain ⟨hw', h⟩ := Setup27.kappa_conj hκρ hx hwW
  exact ⟨hw', by rw [h]; exact hF _ hwF⟩

omit [Finite G] in
theorem Setup27.conj_eq_iff
    {κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)}
    (hκρ : ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)), κ (alpha27 (Sy ⊓ Wt) h w) =
      Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
        (Multiplicative.toAdd (κ w))))
    {x : G} (hx : x ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) {w : G} (hw : w ∈ Sy ⊓ Wt) :
    x * w * x⁻¹ = w ↔ (ρ (qG (Sy ⊓ Wt) x) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (Multiplicative.toAdd (κ ⟨w, hw⟩)) = Multiplicative.toAdd (κ ⟨w, hw⟩) := by
  obtain ⟨hw', h⟩ := Setup27.kappa_conj hκρ hx hw
  rw [← h]
  constructor
  · intro he
    have : (⟨x * w * x⁻¹, hw'⟩ : ↥(Sy ⊓ Wt)) = ⟨w, hw⟩ := Subtype.ext he
    rw [this]
  · intro he
    have := κ.injective (Multiplicative.toAdd.injective he)
    exact congrArg Subtype.val this

omit [Finite G] in
theorem Setup27.irr_of_vec
    {κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)}
    (hκρ : ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)), κ (alpha27 (Sy ⊓ Wt) h w) =
      Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
        (Multiplicative.toAdd (κ w))))
    {Lm : Subgroup (Hh27 (Sy ⊓ Wt))} {F : Submodule (ZMod 2) (Fin 8 → ZMod 2)}
    (hirr : ∀ Y : Submodule (ZMod 2) (Fin 8 → ZMod 2), Y ≤ F →
      (∀ x ∈ Lm, ∀ v ∈ Y, (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v ∈ Y) →
        Y = ⊥ ∨ Y = F)
    (U : Subgroup G) (hUF : U ≤ coordSub κ F)
    (hUinv : ∀ y ∈ preN (Sy ⊓ Wt) Lm, ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    U = ⊥ ∨ U = coordSub κ F := by
  let Yadd : AddSubgroup (Fin 8 → ZMod 2) :=
    { carrier := {v | ∃ u ∈ U, ∃ hW : u ∈ Sy ⊓ Wt, Multiplicative.toAdd (κ ⟨u, hW⟩) = v}
      zero_mem' := ⟨1, U.one_mem, (Sy ⊓ Wt).one_mem, by
        have : κ ⟨1, (Sy ⊓ Wt).one_mem⟩ = 1 := map_one κ
        simp [this]⟩
      add_mem' := by
        rintro _ _ ⟨u₁, hu₁, hW₁, rfl⟩ ⟨u₂, hu₂, hW₂, rfl⟩
        refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, (Sy ⊓ Wt).mul_mem hW₁ hW₂, ?_⟩
        have : κ ⟨u₁ * u₂, (Sy ⊓ Wt).mul_mem hW₁ hW₂⟩ = κ ⟨u₁, hW₁⟩ * κ ⟨u₂, hW₂⟩ :=
          map_mul κ ⟨u₁, hW₁⟩ ⟨u₂, hW₂⟩
        rw [this, toAdd_mul]
      neg_mem' := by
        rintro _ ⟨u, hu, hW, rfl⟩
        refine ⟨u⁻¹, U.inv_mem hu, (Sy ⊓ Wt).inv_mem hW, ?_⟩
        have : κ ⟨u⁻¹, (Sy ⊓ Wt).inv_mem hW⟩ = (κ ⟨u, hW⟩)⁻¹ := map_inv κ ⟨u, hW⟩
        rw [this, toAdd_inv] }
  let Y : Submodule (ZMod 2) (Fin 8 → ZMod 2) := AddSubgroup.toZModSubmodule 2 Yadd
  have hmemY : ∀ v, v ∈ Y ↔ ∃ u ∈ U, ∃ hW : u ∈ Sy ⊓ Wt, Multiplicative.toAdd (κ ⟨u, hW⟩) = v :=
    fun v => Iff.rfl
  have hYF : Y ≤ F := by
    intro v hv
    obtain ⟨u, hu, hW, rfl⟩ := (hmemY v).mp hv
    exact (hUF hu).2
  have hYinv : ∀ x ∈ Lm, ∀ v ∈ Y,
      (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v ∈ Y := by
    intro x hx v hv
    obtain ⟨u, hu, hW, rfl⟩ := (hmemY v).mp hv
    obtain ⟨y, hyN, hyx⟩ := qG_surjective x
    have hqy : qG (Sy ⊓ Wt) y = x := by rw [qG_of_mem hyN, hyx]
    have hyP : y ∈ preN (Sy ⊓ Wt) Lm := mem_preN'.mpr ⟨hyN, by rw [hqy]; exact hx⟩
    obtain ⟨hw', h⟩ := Setup27.kappa_conj hκρ hyN hW
    refine (hmemY _).mpr ⟨y * u * y⁻¹, hUinv y hyP u hu, hw', ?_⟩
    rw [h, hqy]
  rcases hirr Y hYF hYinv with h0 | h1
  · left
    refine eq_bot_iff.mpr fun u hu => ?_
    have hW : u ∈ Sy ⊓ Wt := (hUF hu).1
    have hv : Multiplicative.toAdd (κ ⟨u, hW⟩) ∈ Y := (hmemY _).mpr ⟨u, hu, hW, rfl⟩
    rw [h0, Submodule.mem_bot] at hv
    have h3 : κ ⟨u, hW⟩ = 1 := Multiplicative.toAdd.injective (by simpa using hv)
    have h4 : (⟨u, hW⟩ : ↥(Sy ⊓ Wt)) = 1 := κ.injective (h3.trans (map_one κ).symm)
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h4)
  · right
    refine le_antisymm hUF fun w hw => ?_
    obtain ⟨hwW, hwF⟩ := hw
    have hv : Multiplicative.toAdd (κ ⟨w, hwW⟩) ∈ Y := h1 ▸ hwF
    obtain ⟨u, hu, hW, heq⟩ := (hmemY _).mp hv
    have h3 : κ ⟨u, hW⟩ = κ ⟨w, hwW⟩ := Multiplicative.toAdd.injective heq
    have h4 : (⟨u, hW⟩ : ↥(Sy ⊓ Wt)) = ⟨w, hwW⟩ := κ.injective h3
    have : u = w := congrArg Subtype.val h4
    exact this ▸ hu

@[expose] noncomputable def Setup27.Hp₁ (H : Setup27 A R X O Sy Wt P t)
    (S₁ S₂ : Subgroup (Ntil27 (Sy ⊓ Wt))) : Subgroup G :=
  preN (Sy ⊓ Wt) (fLam₁ H.piH27 S₁ S₂)

@[expose] noncomputable def Setup27.Hp₂ (H : Setup27 A R X O Sy Wt P t)
    (S₁ S₂ : Subgroup (Ntil27 (Sy ⊓ Wt))) : Subgroup G :=
  preN (Sy ⊓ Wt) (fLam₂ H.piH27 S₁ S₂)

structure Setup27.ModHyp (H : Setup27 A R X O Sy Wt P t)
    (S₁ S₂ : Subgroup (Ntil27 (Sy ⊓ Wt)))
    (κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2))
    (ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2))
    (F' F'' : Submodule (ZMod 2) (Fin 8 → ZMod 2)) : Prop where
  inj : Function.Injective ρ
  act : ∀ (h : Hh27 (Sy ⊓ Wt)) (w : ↥(Sy ⊓ Wt)), κ (alpha27 (Sy ⊓ Wt) h w) =
    Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (Multiplicative.toAdd (κ w)))
  split : Mod44Split (ρ.comp (fHhat H.piH27 S₁ S₂).subtype)
    ((fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂))
    ((fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂)) (ρ H.that) F' F''

theorem Setup27.exists_modHyp (hF : H.FacSit S₁ S₂) :
    ∃ (κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2))
      (ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2))
      (F' F'' : Submodule (ZMod 2) (Fin 8 → ZMod 2)), H.ModHyp S₁ S₂ κ ρ F' F'' := by
  obtain ⟨κ, ρ, hρinj, hκρ⟩ := H.exists_rep
  obtain ⟨F', F'', hs⟩ := H.exists_mod44 hF hρinj hκρ
  exact ⟨κ, ρ, F', F'', ⟨hρinj, hκρ, hs⟩⟩

section Fac

variable {H : Setup27 A R X O Sy Wt P t} {S₁ S₂ : Subgroup (Ntil27 (Sy ⊓ Wt))}
  {κ : ↥(Sy ⊓ Wt) ≃* Multiplicative (Fin 8 → ZMod 2)}
  {ρ : Hh27 (Sy ⊓ Wt) →* GL (Fin 8) (ZMod 2)}
  {F' F'' : Submodule (ZMod 2) (Fin 8 → ZMod 2)}

theorem Setup27.mem_Hp₁ {x : G} :
    x ∈ H.Hp₁ S₁ S₂ ↔ x ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) ∧
      qG (Sy ⊓ Wt) x ∈ fLam₁ H.piH27 S₁ S₂ := mem_preN'

theorem Setup27.mem_Hp₂ {x : G} :
    x ∈ H.Hp₂ S₁ S₂ ↔ x ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) ∧
      qG (Sy ⊓ Wt) x ∈ fLam₂ H.piH27 S₁ S₂ := mem_preN'

theorem Setup27.Hp_sup_le :
    H.Hp₁ S₁ S₂ ⊔ H.Hp₂ S₁ S₂ ≤ preN (Sy ⊓ Wt) (fHhat H.piH27 S₁ S₂) :=
  sup_le (preN_mono inf_le_left) (preN_mono inf_le_left)

theorem Setup27.Hp_sup_eq (hF : H.FacSit S₁ S₂) :
    H.Hp₁ S₁ S₂ ⊔ H.Hp₂ S₁ S₂ = preN (Sy ⊓ Wt) (fHhat H.piH27 S₁ S₂) := by
  have D := H.facData hF
  refine le_antisymm H.Hp_sup_le ?_
  have := preN_sup_of_commute (W := Sy ⊓ Wt) (fun a ha b hb => D.Lam_comm ha hb)
  rw [D.Lam_sup] at this
  rw [this]
  exact le_rfl

theorem Setup27.Hp₁_le_normalizer : H.Hp₁ S₁ S₂ ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
  preN_le_normalizer _

theorem Setup27.Hp₂_le_normalizer : H.Hp₂ S₁ S₂ ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
  preN_le_normalizer _

theorem Setup27.exists_a5₁ (hF : H.FacSit S₁ S₂) :
    ∃ π : ↥(perfectResidualOf (H.Hp₁ S₁ S₂)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ ∀ m : ↥(perfectResidualOf (H.Hp₁ S₁ S₂)), π m = 1 ↔
        (m : G) ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  have D := H.facData hF
  have : IsSimpleGroup ↥(fLam₁ H.piH27 S₁ S₂) := D.Lam₁_simple
  have : Group.IsPerfect ↥(fLam₁ H.piH27 S₁ S₂) := isPerfect_of_simple_card_sixty D.Lam₁_card
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five D.Lam₁_card
  let π₀ : ↥(perfectResidualOf (H.Hp₁ S₁ S₂)) →* ↥(fLam₁ H.piH27 S₁ S₂) :=
    MonoidHom.mk' (fun m => ⟨qG (Sy ⊓ Wt) m.1, (mem_Hp₁.mp (prOf_le _ m.2)).2⟩)
      (fun a b => Subtype.ext (qG_mul (mem_Hp₁.mp (prOf_le _ a.2)).1
        (mem_Hp₁.mp (prOf_le _ b.2)).1))
  refine ⟨e.toMonoidHom.comp π₀, fun z => ?_, fun m => ?_⟩
  · obtain ⟨l, rfl⟩ := e.surjective z
    obtain ⟨x, hxN, hxq⟩ := qG_surjective (l : Hh27 (Sy ⊓ Wt))
    have hxq' : qG (Sy ⊓ Wt) x = l := by rw [qG_of_mem hxN, hxq]
    have hxH : x ∈ H.Hp₁ S₁ S₂ := mem_Hp₁.mpr ⟨hxN, by rw [hxq']; exact l.2⟩
    obtain ⟨k, hk, m, hm, hxkm⟩ := exists_mul_of_preN (fLam₁ H.piH27 S₁ S₂) hxH
    refine ⟨⟨m, hm⟩, ?_⟩
    have hkN : k ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hk
    have hmN : m ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
      (mem_Hp₁.mp (prOf_le _ hm)).1
    have hq : qG (Sy ⊓ Wt) m = l := by
      rw [← hxq', hxkm, qG_mul hkN hmN, (qG_eq_one_iff hkN).mpr hk, one_mul]
    show e (π₀ ⟨m, hm⟩) = e l
    congr 1
    exact Subtype.ext hq
  · have hmN := (mem_Hp₁.mp (prOf_le _ m.2)).1
    show e (π₀ m) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    show (⟨qG (Sy ⊓ Wt) m.1, _⟩ : ↥(fLam₁ H.piH27 S₁ S₂)) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact qG_eq_one_iff hmN

theorem Setup27.exists_a5₂ (hF : H.FacSit S₁ S₂) :
    ∃ π : ↥(perfectResidualOf (H.Hp₂ S₁ S₂)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ ∀ m : ↥(perfectResidualOf (H.Hp₂ S₁ S₂)), π m = 1 ↔
        (m : G) ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  have D := H.facData hF
  have : IsSimpleGroup ↥(fLam₂ H.piH27 S₁ S₂) := D.Lam₂_simple
  have : Group.IsPerfect ↥(fLam₂ H.piH27 S₁ S₂) := isPerfect_of_simple_card_sixty D.Lam₂_card
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five D.Lam₂_card
  let π₀ : ↥(perfectResidualOf (H.Hp₂ S₁ S₂)) →* ↥(fLam₂ H.piH27 S₁ S₂) :=
    MonoidHom.mk' (fun m => ⟨qG (Sy ⊓ Wt) m.1, (mem_Hp₂.mp (prOf_le _ m.2)).2⟩)
      (fun a b => Subtype.ext (qG_mul (mem_Hp₂.mp (prOf_le _ a.2)).1
        (mem_Hp₂.mp (prOf_le _ b.2)).1))
  refine ⟨e.toMonoidHom.comp π₀, fun z => ?_, fun m => ?_⟩
  · obtain ⟨l, rfl⟩ := e.surjective z
    obtain ⟨x, hxN, hxq⟩ := qG_surjective (l : Hh27 (Sy ⊓ Wt))
    have hxq' : qG (Sy ⊓ Wt) x = l := by rw [qG_of_mem hxN, hxq]
    have hxH : x ∈ H.Hp₂ S₁ S₂ := mem_Hp₂.mpr ⟨hxN, by rw [hxq']; exact l.2⟩
    obtain ⟨k, hk, m, hm, hxkm⟩ := exists_mul_of_preN (fLam₂ H.piH27 S₁ S₂) hxH
    refine ⟨⟨m, hm⟩, ?_⟩
    have hkN : k ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hk
    have hmN : m ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
      (mem_Hp₂.mp (prOf_le _ hm)).1
    have hq : qG (Sy ⊓ Wt) m = l := by
      rw [← hxq', hxkm, qG_mul hkN hmN, (qG_eq_one_iff hkN).mpr hk, one_mul]
    show e (π₀ ⟨m, hm⟩) = e l
    congr 1
    exact Subtype.ext hq
  · have hmN := (mem_Hp₂.mp (prOf_le _ m.2)).1
    show e (π₀ m) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    show (⟨qG (Sy ⊓ Wt) m.1, _⟩ : ↥(fLam₂ H.piH27 S₁ S₂)) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact qG_eq_one_iff hmN

namespace Setup27.ModHyp

variable (M : H.ModHyp S₁ S₂ κ ρ F' F'')

include M

theorem normF₁ {x : G} (hx : x ∈ preN (Sy ⊓ Wt) (fHhat H.piH27 S₁ S₂)) {w : G}
    (hw : w ∈ coordSub κ F') : x * w * x⁻¹ ∈ coordSub κ F' := by
  obtain ⟨hxN, hxH⟩ := mem_preN'.mp hx
  exact Setup27.coordSub_conj M.act hxN
    (fun v hv => M.split.left.invariant ⟨qG (Sy ⊓ Wt) x, hxH⟩ v hv) hw

theorem normF₂ {x : G} (hx : x ∈ preN (Sy ⊓ Wt) (fHhat H.piH27 S₁ S₂)) {w : G}
    (hw : w ∈ coordSub κ F'') : x * w * x⁻¹ ∈ coordSub κ F'' := by
  obtain ⟨hxN, hxH⟩ := mem_preN'.mp hx
  exact Setup27.coordSub_conj M.act hxN
    (fun v hv => M.split.right.invariant ⟨qG (Sy ⊓ Wt) x, hxH⟩ v hv) hw

theorem cent₁ {x : G} (hx : x ∈ H.Hp₁ S₁ S₂) {w : G} (hw : w ∈ coordSub κ F'') :
    x * w * x⁻¹ = w := by
  obtain ⟨hxN, hxL⟩ := Setup27.mem_Hp₁.mp hx
  obtain ⟨hwW, hwF⟩ := hw
  rw [Setup27.conj_eq_iff M.act hxN hwW]
  have h := (M.split.right.mem_iff _).mp hwF ⟨qG (Sy ⊓ Wt) x, (Subgroup.mem_inf.mp hxL).1⟩
    (Subgroup.mem_subgroupOf.mpr hxL)
  exact h

theorem cent₂ {x : G} (hx : x ∈ H.Hp₂ S₁ S₂) {w : G} (hw : w ∈ coordSub κ F') :
    x * w * x⁻¹ = w := by
  obtain ⟨hxN, hxL⟩ := Setup27.mem_Hp₂.mp hx
  obtain ⟨hwW, hwF⟩ := hw
  rw [Setup27.conj_eq_iff M.act hxN hwW]
  have h := (M.split.left.mem_iff _).mp hwF ⟨qG (Sy ⊓ Wt) x, (Subgroup.mem_inf.mp hxL).1⟩
    (Subgroup.mem_subgroupOf.mpr hxL)
  exact h

theorem fpf₁ (hF : H.FacSit S₁ S₂) :
    ∃ y ∈ H.Hp₁ S₁ S₂, ∀ f ∈ coordSub κ F', y * f * y⁻¹ = f → f = 1 := by
  have D := H.facData hF
  have hL₁ : fLam₁ H.piH27 S₁ S₂ ≤ fHhat H.piH27 S₁ S₂ := inf_le_left
  have e₁ := Subgroup.subgroupOfEquivOfLe hL₁
  have hcard : Nat.card ↥((fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂)) = 60 :=
    (Nat.card_congr e₁.toEquiv).trans D.Lam₁_card
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((fLam₁ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂))) 3 (by rw [hcard]; norm_num)
  have hgord : orderOf ((g : ↥(fHhat H.piH27 S₁ S₂))) = 3 := by
    rw [← hg]
    exact Subgroup.orderOf_coe g
  obtain ⟨y, hyN, hyq⟩ := qG_surjective ((g : ↥(fHhat H.piH27 S₁ S₂)) : Hh27 (Sy ⊓ Wt))
  have hqy : qG (Sy ⊓ Wt) y = ((g : ↥(fHhat H.piH27 S₁ S₂)) : Hh27 (Sy ⊓ Wt)) := by
    rw [qG_of_mem hyN, hyq]
  refine ⟨y, Setup27.mem_Hp₁.mpr ⟨hyN, ?_⟩, fun f hf hfix => ?_⟩
  · rw [hqy]
    exact g.2
  · obtain ⟨hfW, hfF⟩ := hf
    rw [Setup27.conj_eq_iff M.act hyN hfW, hqy] at hfix
    have h0 := M.split.left.fixedPointFree (g : ↥(fHhat H.piH27 S₁ S₂)) g.2 hgord _ hfF hfix
    have h1 : κ ⟨f, hfW⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2 : (⟨f, hfW⟩ : ↥(Sy ⊓ Wt)) = 1 := κ.injective (h1.trans (map_one κ).symm)
    exact congrArg Subtype.val h2

theorem fpf₂ (hF : H.FacSit S₁ S₂) :
    ∃ y ∈ H.Hp₂ S₁ S₂, ∀ f ∈ coordSub κ F'', y * f * y⁻¹ = f → f = 1 := by
  have D := H.facData hF
  have hL₂ : fLam₂ H.piH27 S₁ S₂ ≤ fHhat H.piH27 S₁ S₂ := inf_le_left
  have e₂ := Subgroup.subgroupOfEquivOfLe hL₂
  have hcard : Nat.card ↥((fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂)) = 60 :=
    (Nat.card_congr e₂.toEquiv).trans D.Lam₂_card
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((fLam₂ H.piH27 S₁ S₂).subgroupOf (fHhat H.piH27 S₁ S₂))) 3 (by rw [hcard]; norm_num)
  have hgord : orderOf ((g : ↥(fHhat H.piH27 S₁ S₂))) = 3 := by
    rw [← hg]
    exact Subgroup.orderOf_coe g
  obtain ⟨y, hyN, hyq⟩ := qG_surjective ((g : ↥(fHhat H.piH27 S₁ S₂)) : Hh27 (Sy ⊓ Wt))
  have hqy : qG (Sy ⊓ Wt) y = ((g : ↥(fHhat H.piH27 S₁ S₂)) : Hh27 (Sy ⊓ Wt)) := by
    rw [qG_of_mem hyN, hyq]
  refine ⟨y, Setup27.mem_Hp₂.mpr ⟨hyN, ?_⟩, fun f hf hfix => ?_⟩
  · rw [hqy]
    exact g.2
  · obtain ⟨hfW, hfF⟩ := hf
    rw [Setup27.conj_eq_iff M.act hyN hfW, hqy] at hfix
    have h0 := M.split.right.fixedPointFree (g : ↥(fHhat H.piH27 S₁ S₂)) g.2 hgord _ hfF hfix
    have h1 : κ ⟨f, hfW⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2 : (⟨f, hfW⟩ : ↥(Sy ⊓ Wt)) = 1 := κ.injective (h1.trans (map_one κ).symm)
    exact congrArg Subtype.val h2

theorem facSetup (hF : H.FacSit S₁ S₂) :
    FacSetup (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) (Sy ⊓ Wt) (coordSub κ F')
      (coordSub κ F'') (H.Hp₁ S₁ S₂) (H.Hp₂ S₁ S₂) t := by
  have D := H.facData hF
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hWab := hS.elem_inf_Wt hSy hWt
  have htN := hS.t_mem_normalizer_inf_Wt hSy hWt
  have hHsup := H.Hp_sup_le (S₁ := S₁) (S₂ := S₂)
  have hqt : qG (Sy ⊓ Wt) t = H.that := qG_of_mem htN
  have : IsSimpleGroup ↥(fLam₁ H.piH27 S₁ S₂) := D.Lam₁_simple
  have : IsSimpleGroup ↥(fLam₂ H.piH27 S₁ S₂) := D.Lam₂_simple
  have : Group.IsPerfect ↥(fLam₁ H.piH27 S₁ S₂) := isPerfect_of_simple_card_sixty D.Lam₁_card
  have : Group.IsPerfect ↥(fLam₂ H.piH27 S₁ S₂) := isPerfect_of_simple_card_sixty D.Lam₂_card
  refine
    { K_le₁ := centralizer_le_preN _
      K_le₂ := centralizer_le_preN _
      inf_eq := by
        rw [Setup27.Hp₁, Setup27.Hp₂, ← preN_inf, D.Lam_inf]
        exact Subgroup.ext fun x => mem_preN_bot
      comm_mem := fun x hx y hy => ?_
      norm₁ := fun x hx y hy => ?_
      norm₂ := fun x hx y hy => ?_
      normK := fun x hx k hk => ?_
      W_le := fun w hw => mem_centralizer_iff.mpr fun h hh =>
        L34.comm_of_isElemAbelian hWab hh hw
      W_pgroup := hSy.isPGroup.to_inf_left
      W_comm := fun w hw w' hw' => L34.comm_of_isElemAbelian hWab hw hw'
      W_central := fun w hw k hk => mem_centralizer_iff.mp hk w hw
      W_idx := hS.not_two_dvd_relIndex_centralizer_W hSy hWt
      F₁_le := coordSub_le
      F₂_le := coordSub_le
      F_disj := coordSub_inf M.split.isCompl.disjoint
      F_sup := coordSub_sup M.split.isCompl.sup_eq_top
      normF₁ := fun x hx f hf => M.normF₁ (hHsup hx) hf
      normF₂ := fun x hx f hf => M.normF₂ (hHsup hx) hf
      cent₁ := fun x hx f hf => M.cent₁ hx hf
      cent₂ := fun x hx f hf => M.cent₂ hx hf
      fpf₁ := M.fpf₁ hF
      fpf₂ := M.fpf₂ hF
      perf₁ := fun y hy => exists_mul_of_preN (fLam₁ H.piH27 S₁ S₂) hy
      perf₂ := fun y hy => exists_mul_of_preN (fLam₂ H.piH27 S₁ S₂) hy
      t_sq := hS.t_sq
      swap₁ := fun x hx => ?_
      swap₂ := fun x hx => ?_ }
  · obtain ⟨hxN, hxL⟩ := Setup27.mem_Hp₁.mp hx
    obtain ⟨hyN, hyL⟩ := Setup27.mem_Hp₂.mp hy
    have hc : ⁅x, y⁆ ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
    rw [← qG_eq_one_iff hc, qG_commutator hxN hyN]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (D.Lam_comm hxL hyL)
  · have hxP := hHsup hx
    obtain ⟨hxN, hxH⟩ := mem_preN'.mp hxP
    obtain ⟨hyN, hyL⟩ := Setup27.mem_Hp₁.mp hy
    refine Setup27.mem_Hp₁.mpr ⟨mul_mem (mul_mem hxN hyN) (inv_mem hxN), ?_⟩
    rw [qG_conj hxN hyN]
    exact D.Lam₁_norm hxH hyL
  · have hxP := hHsup hx
    obtain ⟨hxN, hxH⟩ := mem_preN'.mp hxP
    obtain ⟨hyN, hyL⟩ := Setup27.mem_Hp₂.mp hy
    refine Setup27.mem_Hp₂.mpr ⟨mul_mem (mul_mem hxN hyN) (inv_mem hxN), ?_⟩
    rw [qG_conj hxN hyN]
    exact D.Lam₂_norm hxH hyL
  · have hxN : x ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
      preN_le_normalizer _ (hHsup hx)
    exact (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer_W (Sy ⊓ Wt) hxN) k).mp hk
  · obtain ⟨hxN, hxL⟩ := Setup27.mem_Hp₁.mp hx
    refine Setup27.mem_Hp₂.mpr ⟨mul_mem (mul_mem htN hxN) (inv_mem htN), ?_⟩
    rw [qG_conj htN hxN, hqt]
    exact H.that_conj_lam₁ hF hxL
  · obtain ⟨hxN, hxL⟩ := Setup27.mem_Hp₂.mp hx
    refine Setup27.mem_Hp₁.mpr ⟨mul_mem (mul_mem htN hxN) (inv_mem htN), ?_⟩
    rw [qG_conj htN hxN, hqt]
    exact H.that_conj_lam₂ hF hxL

theorem card₁ : Nat.card (coordSub κ F' : Subgroup G) = 16 := by
  rw [card_coordSub, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    M.split.left.finrank_eq]
  norm_num

theorem card₂ : Nat.card (coordSub κ F'' : Subgroup G) = 16 := by
  rw [card_coordSub, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    M.split.right.finrank_eq]
  norm_num

theorem irr₁ (U : Subgroup G) (hUF : U ≤ coordSub κ F')
    (hU : ∀ y ∈ H.Hp₁ S₁ S₂, ∀ u ∈ U, y * u * y⁻¹ ∈ U) : U = ⊥ ∨ U = coordSub κ F' := by
  refine Setup27.irr_of_vec M.act (Lm := fLam₁ H.piH27 S₁ S₂) (fun Y hY hinv => ?_) U hUF hU
  exact M.split.left.irreducible Y hY fun x hx v hv =>
    hinv x.1 (Subgroup.mem_subgroupOf.mp hx) v hv

theorem irr₂ (U : Subgroup G) (hUF : U ≤ coordSub κ F'')
    (hU : ∀ y ∈ H.Hp₂ S₁ S₂, ∀ u ∈ U, y * u * y⁻¹ ∈ U) : U = ⊥ ∨ U = coordSub κ F'' := by
  refine Setup27.irr_of_vec M.act (Lm := fLam₂ H.piH27 S₁ S₂) (fun Y hY hinv => ?_) U hUF hU
  exact M.split.right.irreducible Y hY fun x hx v hv =>
    hinv x.1 (Subgroup.mem_subgroupOf.mp hx) v hv

theorem faithful₁ {y : G} (hy : y ∈ H.Hp₁ S₁ S₂)
    (hfix : ∀ f ∈ coordSub κ F', y * f * y⁻¹ = f) :
    y ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  obtain ⟨hyN, hyL⟩ := Setup27.mem_Hp₁.mp hy
  have hyH : qG (Sy ⊓ Wt) y ∈ fHhat H.piH27 S₁ S₂ := (Subgroup.mem_inf.mp hyL).1
  have h1 : (⟨qG (Sy ⊓ Wt) y, hyH⟩ : ↥(fHhat H.piH27 S₁ S₂)) = 1 := by
    refine M.split.left.faithful _ (Subgroup.mem_subgroupOf.mpr hyL) (fun v hv => ?_)
    let f : ↥(Sy ⊓ Wt) := κ.symm (Multiplicative.ofAdd v)
    have hf : (f : G) ∈ coordSub κ F' := mem_coordSub_of (by simpa [f] using hv)
    have := (Setup27.conj_eq_iff M.act hyN f.2).mp (hfix _ hf)
    simpa [f] using this
  have h2 : qG (Sy ⊓ Wt) y = 1 := congrArg Subtype.val h1
  exact (qG_eq_one_iff hyN).mp h2

theorem faithful₂ {y : G} (hy : y ∈ H.Hp₂ S₁ S₂)
    (hfix : ∀ f ∈ coordSub κ F'', y * f * y⁻¹ = f) :
    y ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  obtain ⟨hyN, hyL⟩ := Setup27.mem_Hp₂.mp hy
  have hyH : qG (Sy ⊓ Wt) y ∈ fHhat H.piH27 S₁ S₂ := (Subgroup.mem_inf.mp hyL).1
  have h1 : (⟨qG (Sy ⊓ Wt) y, hyH⟩ : ↥(fHhat H.piH27 S₁ S₂)) = 1 := by
    refine M.split.right.faithful _ (Subgroup.mem_subgroupOf.mpr hyL) (fun v hv => ?_)
    let f : ↥(Sy ⊓ Wt) := κ.symm (Multiplicative.ofAdd v)
    have hf : (f : G) ∈ coordSub κ F'' := mem_coordSub_of (by simpa [f] using hv)
    have := (Setup27.conj_eq_iff M.act hyN f.2).mp (hfix _ hf)
    simpa [f] using this
  have h2 : qG (Sy ⊓ Wt) y = 1 := congrArg Subtype.val h1
  exact (qG_eq_one_iff hyN).mp h2

theorem fpf₁' {y : G} (hy : y ∈ H.Hp₁ S₁ S₂)
    (hy1 : y ∉ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G))
    (hy3 : y ^ 3 ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) {f : G}
    (hf : f ∈ coordSub κ F') (hfix : y * f * y⁻¹ = f) : f = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hyN, hyL⟩ := Setup27.mem_Hp₁.mp hy
  have hyH : qG (Sy ⊓ Wt) y ∈ fHhat H.piH27 S₁ S₂ := (Subgroup.mem_inf.mp hyL).1
  obtain ⟨hfW, hfF⟩ := hf
  rw [Setup27.conj_eq_iff M.act hyN hfW] at hfix
  have hq1 : qG (Sy ⊓ Wt) y ≠ 1 := fun h => hy1 ((qG_eq_one_iff hyN).mp h)
  have hq3 : (qG (Sy ⊓ Wt) y) ^ 3 = 1 := by
    rw [← qG_pow hyN, qG_eq_one_iff (pow_mem hyN 3)]
    exact hy3
  have hord : orderOf (⟨qG (Sy ⊓ Wt) y, hyH⟩ : ↥(fHhat H.piH27 S₁ S₂)) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hq3)
    · intro h
      exact hq1 (congrArg Subtype.val h)
  have h0 := M.split.left.fixedPointFree ⟨qG (Sy ⊓ Wt) y, hyH⟩
    (Subgroup.mem_subgroupOf.mpr hyL) hord _ hfF (by simpa using hfix)
  have h1 : κ ⟨f, hfW⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h0)
  have h2 : (⟨f, hfW⟩ : ↥(Sy ⊓ Wt)) = 1 := κ.injective (h1.trans (map_one κ).symm)
  exact congrArg Subtype.val h2

theorem fpf₂' {y : G} (hy : y ∈ H.Hp₂ S₁ S₂)
    (hy1 : y ∉ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G))
    (hy3 : y ^ 3 ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) {f : G}
    (hf : f ∈ coordSub κ F'') (hfix : y * f * y⁻¹ = f) : f = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hyN, hyL⟩ := Setup27.mem_Hp₂.mp hy
  have hyH : qG (Sy ⊓ Wt) y ∈ fHhat H.piH27 S₁ S₂ := (Subgroup.mem_inf.mp hyL).1
  obtain ⟨hfW, hfF⟩ := hf
  rw [Setup27.conj_eq_iff M.act hyN hfW] at hfix
  have hq1 : qG (Sy ⊓ Wt) y ≠ 1 := fun h => hy1 ((qG_eq_one_iff hyN).mp h)
  have hq3 : (qG (Sy ⊓ Wt) y) ^ 3 = 1 := by
    rw [← qG_pow hyN, qG_eq_one_iff (pow_mem hyN 3)]
    exact hy3
  have hord : orderOf (⟨qG (Sy ⊓ Wt) y, hyH⟩ : ↥(fHhat H.piH27 S₁ S₂)) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hq3)
    · intro h
      exact hq1 (congrArg Subtype.val h)
  have h0 := M.split.right.fixedPointFree ⟨qG (Sy ⊓ Wt) y, hyH⟩
    (Subgroup.mem_subgroupOf.mpr hyL) hord _ hfF (by simpa using hfix)
  have h1 : κ ⟨f, hfW⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h0)
  have h2 : (⟨f, hfW⟩ : ↥(Sy ⊓ Wt)) = 1 := κ.injective (h1.trans (map_one κ).symm)
  exact congrArg Subtype.val h2

theorem swapF₁ {f : G} (hf : f ∈ coordSub κ F') : t * f * t⁻¹ ∈ coordSub κ F'' := by
  have htN := H.sit.S.t_mem_normalizer_inf_Wt H.sit.hSy H.sit.hWt
  have hqt : qG (Sy ⊓ Wt) t = H.that := qG_of_mem htN
  obtain ⟨hfW, hfF⟩ := hf
  obtain ⟨hw', h⟩ := Setup27.kappa_conj M.act htN hfW
  refine ⟨hw', ?_⟩
  rw [h, hqt]
  have hmem := Submodule.mem_map_of_mem
    (f := Matrix.mulVecLin ((ρ H.that : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)))
    hfF
  rw [M.split.map_left] at hmem
  simpa using hmem

theorem swapF₂ {f : G} (hf : f ∈ coordSub κ F'') : t * f * t⁻¹ ∈ coordSub κ F' := by
  have htN := H.sit.S.t_mem_normalizer_inf_Wt H.sit.hSy H.sit.hWt
  have hqt : qG (Sy ⊓ Wt) t = H.that := qG_of_mem htN
  obtain ⟨hfW, hfF⟩ := hf
  obtain ⟨hw', h⟩ := Setup27.kappa_conj M.act htN hfW
  refine ⟨hw', ?_⟩
  rw [h, hqt]
  have hmem := Submodule.mem_map_of_mem
    (f := Matrix.mulVecLin ((ρ H.that : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)))
    hfF
  rw [M.split.map_right] at hmem
  simpa using hmem

omit M in
theorem idx₁ (hF : H.FacSit S₁ S₂) :
    (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)).relIndex (H.Hp₁ S₁ S₂) = 60 := by
  rw [Setup27.Hp₁, relIndex_preN]
  exact (H.facData hF).Lam₁_card

omit M in
theorem idx₂ (hF : H.FacSit S₁ S₂) :
    (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)).relIndex (H.Hp₂ S₁ S₂) = 60 := by
  rw [Setup27.Hp₂, relIndex_preN]
  exact (H.facData hF).Lam₂_card

omit M in
theorem perf_le (hF : H.FacSit S₁ S₂) (Q : Subgroup G)
    (hQN : Q ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ H.Hp₁ S₁ S₂ ⊔ H.Hp₂ S₁ S₂ := by
  have D := H.facData hF
  rw [H.Hp_sup_eq hF]
  let f : ↥Q →* Hh27 (Sy ⊓ Wt) :=
    MonoidHom.mk' (fun z => qG (Sy ⊓ Wt) z.1) (fun a b => qG_mul (hQN a.2) (hQN b.2))
  have hperf : ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ = ⊤ := by
    have h := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hQ)
    rwa [_root_.commutator_def] at h
  have hrange : ⁅f.range, f.range⁆ = f.range := by
    rw [← Subgroup.map_top f, ← Subgroup.map_commutator, hperf]
  have hle : f.range ≤ fHhat H.piH27 S₁ S₂ := D.le_Hhat_of_perfect hrange
  intro q hq
  exact mem_preN'.mpr ⟨hQN hq, hle ⟨⟨q, hq⟩, rfl⟩⟩

theorem facExtra (hF : H.FacSit S₁ S₂) :
    FacExtra (Sy ⊓ Wt) (coordSub κ F') (coordSub κ F'') (H.Hp₁ S₁ S₂) (H.Hp₂ S₁ S₂) t where
  card₁ := M.card₁
  card₂ := M.card₂
  irr₁ := M.irr₁
  irr₂ := M.irr₂
  faithful₁ := fun _ hy hfix => M.faithful₁ hy hfix
  faithful₂ := fun _ hy hfix => M.faithful₂ hy hfix
  fpf₁ := fun _ hy hy1 hy3 _ hf hfix => M.fpf₁' hy hy1 hy3 hf hfix
  fpf₂ := fun _ hy hy1 hy3 _ hf hfix => M.fpf₂' hy hy1 hy3 hf hfix
  swap₁ := fun _ hf => M.swapF₁ hf
  swap₂ := fun _ hf => M.swapF₂ hf
  idx₁ := idx₁ hF
  idx₂ := idx₂ hF
  t_mem := H.sit.S.t_mem_normalizer_inf_Wt H.sit.hSy H.sit.hWt
  perf_le := perf_le hF
  a5₁ := H.exists_a5₁ hF
  a5₂ := H.exists_a5₂ hF

end Setup27.ModHyp

theorem Setup27.exists_facSetup (hF : H.FacSit S₁ S₂) :
    ∃ F₁ F₂ H₁ H₂ : Subgroup G,
      FacSetup (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) (Sy ⊓ Wt) F₁ F₂ H₁ H₂ t ∧
      FacExtra (Sy ⊓ Wt) F₁ F₂ H₁ H₂ t ∧ H₁ ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) ∧
      H₂ ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  obtain ⟨κ, ρ, F', F'', M⟩ := H.exists_modHyp hF
  exact ⟨coordSub κ F', coordSub κ F'', H.Hp₁ S₁ S₂, H.Hp₂ S₁ S₂, M.facSetup hF,
    M.facExtra hF, H.Hp₁_le_normalizer, H.Hp₂_le_normalizer⟩

end Fac

end Mod

end CFSG.OddStandard.Seitz77
