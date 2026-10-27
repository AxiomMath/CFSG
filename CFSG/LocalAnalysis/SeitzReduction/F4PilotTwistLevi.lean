module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistSp4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2B2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAmalgam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Chevalley (baseChangeGL baseChangeGL_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

local instance f4PilotTwistLeviNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Naturality


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem b2LeviHom_x {v : Fin 2 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) (c : K) :
    b2LeviHom K (Sp.x 2 K v c) = Adjoint.f4Par K (c2ToF4 v) c := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hv
  rw [Sp.x_eq hr, b2LeviHom_apply, spEmbed_elt, ← Sp.x_eq (stdVec_succIdx_eq hr), c3LeviHom_x,
    c2ToF4_apply]

theorem baseChangeGL_b2LeviHom {k : Type} [Field k] [Finite k] [CharP k 2] (ι : k →+* K)
    (g : StatedSp 2 k) :
    baseChangeGL ι ((b2LeviHom k g : adjointGroup .F4 k) : ModGL .F4 k) =
      ((b2LeviHom K (statedSpMap ι 2 g) : adjointGroup .F4 K) : ModGL .F4 K) := by
  have hle : ⨆ v ∈ roots (isFiniteType_cartanC 2) ∅, Symplectic.rootGroup 2 k v ≤
      MonoidHom.eqLocus ((baseChangeGL ι).comp ((adjointGroup .F4 k).subtype.comp (b2LeviHom k)))
        ((adjointGroup .F4 K).subtype.comp ((b2LeviHom K).comp (statedSpMap ι 2))) := by
    refine iSup₂_le fun v hv x hx => ?_
    obtain ⟨c, rfl⟩ := ((Sp.isParametrization (n := 2) (F := k) v hv).1 x).1 hx
    change baseChangeGL ι ((b2LeviHom k (Sp.x 2 k v c) : adjointGroup .F4 k) : ModGL .F4 k) =
      ((b2LeviHom K (statedSpMap ι 2 (Sp.x 2 k v c)) : adjointGroup .F4 K) : ModGL .F4 K)
    rw [b2LeviHom_x hv, baseChangeGL_f4Par, statedSpMap_x, b2LeviHom_x hv]
  rw [(Symplectic.isCTGroupDatum 2 k).iSup_eq_top] at hle
  exact hle (mem_top g)

end Naturality

section Levi12


variable {K : Type} [Field K]

theorem amalgamRoots_one_two_subset_b2LeviRoots : amalgamRoots {1, 2} ⊆ b2LeviRoots := by
  intro γ hγ
  obtain ⟨j, hj, hγj⟩ := hγ
  refine mem_b2LeviRoots.2 ⟨isRoot_of_mem_amalgamRoots ⟨j, hj, hγj⟩, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl <;> rcases hγj with rfl | rfl <;> decide

theorem levi_univ_statedSp_eq_top (n : ℕ) :
    CurtisTits.levi (Symplectic.rootGroup n K) Finset.univ = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← CurtisTits.iSup_leviAmalgam_eq_top (isCTRootSystem (isFiniteType_cartanC n) ∅)
    (Symplectic.isCTGroupDatum n K)]
  exact iSup_le fun J => biSup_mono fun j _ => Finset.mem_univ j

theorem rootGroup_le_levi_one_two {m : Fin (Tag.rank .F4)} (hm : m ∈ ({1, 2} : Finset _))
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ = Pi.single m 1 ∨ γ = -Pi.single m 1) :
    (Adjoint.f4Datum K).rootGroup γ ≤ CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} := by
  refine le_trans ?_ (CurtisTits.rankOne_le_levi (Adjoint.f4Datum K).rootGroup hm)
  rcases hγ with rfl | rfl
  exacts [le_sup_left, le_sup_right]

variable
  [Finite K] [CharP K 2]

theorem levi_one_two_eq_B2Levi :
    CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} = B2Levi K := by
  apply le_antisymm
  · rw [levi_f4Datum_eq]
    exact Subgroup.subgroupOf_mono _ (rootSpan_mono_F4 amalgamRoots_one_two_subset_b2LeviRoots)
  · rw [← range_b2LeviHom, MonoidHom.range_eq_map, ← levi_univ_statedSp_eq_top 2,
      Subgroup.map_le_iff_le_comap]
    have hc0 : c2ToF4 (Pi.single 0 1) = Pi.single 2 1 := by decide
    have hc1 : c2ToF4 (Pi.single 1 1) = Pi.single 1 1 := by decide
    have key : ∀ v : Fin 2 → ℤ, v ∈ c2Roots → (∃ m ∈ ({1, 2} : Finset (Fin (Tag.rank .F4))),
        c2ToF4 v = Pi.single m 1 ∨ c2ToF4 v = -Pi.single m 1) →
        Symplectic.rootGroup 2 K v ≤ (CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2}).comap
          (b2LeviHom K) := by
      intro v hv ⟨m, hm, hvm⟩
      rw [← Subgroup.map_le_iff_le_comap, map_b2LeviHom_rootGroup (mem_roots_of_mem_c2Roots hv)]
      exact rootGroup_le_levi_one_two hm hvm
    refine iSup₂_le fun j _ => sup_le ?_ ?_
    · fin_cases j
      · exact key _ (by decide) ⟨2, by decide, Or.inl hc0⟩
      · exact key _ (by decide) ⟨1, by decide, Or.inl hc1⟩
    · fin_cases j
      · exact key _ (by decide) ⟨2, by decide, Or.inr ((map_neg c2ToF4 _).trans
          (congrArg Neg.neg hc0))⟩
      · exact key _ (by decide) ⟨1, by decide, Or.inr ((map_neg c2ToF4 _).trans
          (congrArg Neg.neg hc1))⟩

theorem exists_ringEquiv_of_forall_B2Levi {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) (θ : MulAut (B2Levi K))
    (hθ : ∀ (x : B2Levi k) (y : B2Levi K), ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL ι ((x : adjointGroup .F4 k) : ModGL .F4 k) → θ y = y) :
    ∃ ρ : K ≃+* K, (∀ c, ρ (ι c) = ι c) ∧ ∀ y : B2Levi K,
      (((θ y : B2Levi K) : adjointGroup .F4 K) : ModGL .F4 K) =
        baseChangeGL (ρ : K →+* K) ((y : adjointGroup .F4 K) : ModGL .F4 K) := by
  set α : MulAut (StatedSp 2 K) := ((b2LeviEquiv K).trans θ).trans (b2LeviEquiv K).symm with hα
  have hfix : ∀ g : StatedSp 2 k, α (statedSpMap ι 2 g) = statedSpMap ι 2 g := by
    intro g
    have h := hθ (b2LeviEquiv k g) (b2LeviEquiv K (statedSpMap ι 2 g))
      (by rw [coe_b2LeviEquiv, coe_b2LeviEquiv, baseChangeGL_b2LeviHom])
    change (b2LeviEquiv K).symm (θ (b2LeviEquiv K (statedSpMap ι 2 g))) = _
    rw [h, MulEquiv.symm_apply_apply]
  obtain ⟨ρ, hρ, hαρ⟩ := exists_ringEquiv_eq_fieldSp_of_forall_statedSpMap ι α hfix
  refine ⟨ρ, hρ, fun y => ?_⟩
  obtain ⟨g, rfl⟩ := (b2LeviEquiv K).surjective y
  have h1 : θ (b2LeviEquiv K g) = b2LeviEquiv K (α g) := by
    change _ = b2LeviEquiv K ((b2LeviEquiv K).symm (θ (b2LeviEquiv K g)))
    rw [MulEquiv.apply_symm_apply]
  rw [h1, hαρ, fieldSp_eq_statedSpMap, coe_b2LeviEquiv, coe_b2LeviEquiv]
  exact (baseChangeGL_b2LeviHom (ρ : K →+* K) g).symm

theorem exists_ringEquiv_of_injective_of_range_eq {M : Type*} [Group M] {k : Type} [Field k]
    [Finite k] [CharP k 2] (ι : k →+* K) {f₁ f₂ : B2Levi K →* M} (h₁ : Function.Injective f₁)
    (h₂ : Function.Injective f₂) (hr : f₁.range = f₂.range)
    (hfix : ∀ (x : B2Levi k) (y : B2Levi K), ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL ι ((x : adjointGroup .F4 k) : ModGL .F4 k) → f₁ y = f₂ y) :
    ∃ ρ : K ≃+* K, (∀ c, ρ (ι c) = ι c) ∧ ∀ y y' : B2Levi K,
      ((y' : adjointGroup .F4 K) : ModGL .F4 K) =
        baseChangeGL (ρ : K →+* K) ((y : adjointGroup .F4 K) : ModGL .F4 K) → f₁ y = f₂ y' := by
  set θ : MulAut (B2Levi K) := ((MonoidHom.ofInjective h₁).trans
    (MulEquiv.subgroupCongr hr)).trans (MonoidHom.ofInjective h₂).symm with hθdef
  have hθ : ∀ y, f₂ (θ y) = f₁ y := by
    intro y
    have h := (MonoidHom.ofInjective h₂).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective h₁ y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨ρ, hρ, hθρ⟩ := exists_ringEquiv_of_forall_B2Levi ι θ fun x y hxy =>
    h₂ ((hθ y).trans (hfix x y hxy))
  refine ⟨ρ, hρ, fun y y' hy' => ?_⟩
  have h : θ y = y' := Subtype.ext (Subtype.ext ((hθρ y).trans hy'.symm))
  rw [← hθ y, h]

end Levi12


section RankOne

open CFSG.LieType.CurtisTits

variable {G : Type*} [Group G] {D : UniversalRootDatum G} {nw : Fin D.rank → G}
  {H : Fin D.rank → Subgroup G}

theorem neg_single_mem_roots (i : Fin D.rank) : -Pi.single i 1 ∈ D.roots := by
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have h := hΦ.smul_mem ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) _
    (hΦ.single_mem i)
  rwa [hΦ.simple_single] at h

theorem mem_torus_of_mem_rankOne_of_commute
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    (hext : SteinbergExtras D nw H) {i : Fin D.rank} {z : G} (hz : z ∈ rankOne D.rootGroup i)
    (hc : ∀ x ∈ rankOne D.rootGroup i, Commute z x) : z ∈ H i := by
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hpos : Pi.single i 1 ∈ D.roots := hΦ.single_mem i
  have hneg : -Pi.single i 1 ∈ D.roots := neg_single_mem_roots i
  have hcpos : ∀ x ∈ D.rootGroup (Pi.single i 1), Commute z x := fun x hx =>
    hc x (mem_sup_left hx)
  have hcneg : ∀ x ∈ D.rootGroup (-Pi.single i 1), Commute z x := fun x hx =>
    hc x (mem_sup_right hx)
  rcases hext.rankOne_bruhat i z hz with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · have hu1 : u = 1 := by
      refine hext.eq_one_of_mem_normalizer i u hu (mem_normalizer_iff.2 fun x => ?_)
      constructor
      · intro hx
        have hzx := (hcneg x hx).eq
        have h1 : u * x * u⁻¹ = h⁻¹ * x * h⁻¹⁻¹ := by
          calc u * x * u⁻¹ = h⁻¹ * ((h * u) * x) * u⁻¹ := by group
            _ = h⁻¹ * (x * (h * u)) * u⁻¹ := by rw [hzx]
            _ = h⁻¹ * x * h⁻¹⁻¹ := by group
        rw [h1]
        exact hct.H_conj_mem i _ hneg h⁻¹ (inv_mem hh) x hx
      · intro hx
        have hw : h * (u * x * u⁻¹) * h⁻¹ ∈ D.rootGroup (-Pi.single i 1) :=
          hct.H_conj_mem i _ hneg h hh _ hx
        have hzw := (hcneg _ hw).eq
        have hxw : x = h * (u * x * u⁻¹) * h⁻¹ := by
          calc x = (h * u)⁻¹ * ((h * (u * x * u⁻¹) * h⁻¹) * (h * u)) := by group
            _ = (h * u)⁻¹ * ((h * u) * (h * (u * x * u⁻¹) * h⁻¹)) := by rw [← hzw]
            _ = h * (u * x * u⁻¹) * h⁻¹ := by group
        rw [hxw]
        exact hw
    rw [hu1, mul_one]
    exact hh
  · exfalso
    have hht : CFSG.LieType.Steinberg.ht (Pi.single i 1 : Fin D.rank → ℤ) = 1 := by
      simp [CFSG.LieType.Steinberg.ht]
    have hhtn : CFSG.LieType.Steinberg.ht (-Pi.single i 1 : Fin D.rank → ℤ) = -1 := by
      simp [CFSG.LieType.Steinberg.ht]
    have hbot : D.rootGroup (Pi.single i 1) = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      have hy1 : nw i * (h * (v * x * v⁻¹) * h⁻¹) * (nw i)⁻¹ ∈ D.rootGroup (-Pi.single i 1) := by
        have h1 : v * x * v⁻¹ ∈ D.rootGroup (Pi.single i 1) :=
          mul_mem (mul_mem hv hx) (inv_mem hv)
        have h2 := hct.H_conj_mem i _ hpos h hh _ h1
        have h3 := hct.conj_mem i _ hpos _ h2
        rwa [hΦ.simple_single] at h3
      have hzx := (hcpos x hx).eq
      have hxy : x = u * (nw i * (h * (v * x * v⁻¹) * h⁻¹) * (nw i)⁻¹) * u⁻¹ := by
        calc x = (u * nw i * h * v) * x * (u * nw i * h * v)⁻¹ := by
              rw [hzx]
              group
          _ = u * (nw i * (h * (v * x * v⁻¹) * h⁻¹) * (nw i)⁻¹) * u⁻¹ := by group
      have hy2 : nw i * (h * (v * x * v⁻¹) * h⁻¹) * (nw i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
        have he : nw i * (h * (v * x * v⁻¹) * h⁻¹) * (nw i)⁻¹ = u⁻¹ * x * u := by
          nth_rewrite 2 [hxy]
          group
        rw [he]
        exact mul_mem (mul_mem (inv_mem hu) hx) hu
      have hmem : nw i * (h * (v * x * v⁻¹) * h⁻¹) * (nw i)⁻¹ ∈
          (⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < CFSG.LieType.Steinberg.ht γ}, D.rootGroup γ) ⊓
            (⨆ γ ∈ {γ | γ ∈ D.roots ∧ CFSG.LieType.Steinberg.ht γ < 0}, D.rootGroup γ) :=
        mem_inf.2 ⟨le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧
            0 < CFSG.LieType.Steinberg.ht γ}) => D.rootGroup γ) (Pi.single i 1)
            ⟨hpos, by rw [hht]; exact one_pos⟩ le_rfl hy2,
          le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧
            CFSG.LieType.Steinberg.ht γ < 0}) => D.rootGroup γ) (-Pi.single i 1)
            ⟨hneg, by rw [hhtn]; exact neg_one_lt_zero⟩ le_rfl hy1⟩
      rw [hext.posPart_inf_negPart, mem_bot] at hmem
      rw [mem_bot, hxy, hmem, mul_one, mul_inv_cancel]
    exact hext.ne_bot _ hpos hbot

theorem rankOne_inf_rankOne_eq_bot
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    (hext : SteinbergExtras D nw H) {i j : Fin D.rank} (hij : i ≠ j)
    (hcomm : ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup j, Commute x y) :
    rankOne D.rootGroup i ⊓ rankOne D.rootGroup j = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hzi, hzj⟩ := mem_inf.1 hz
  have hHi := mem_torus_of_mem_rankOne_of_commute hct hext hzi fun x hx => (hcomm x hx z hzj).symm
  have hHj := mem_torus_of_mem_rankOne_of_commute hct hext hzj fun y hy => hcomm z hzi y hy
  rw [mem_bot]
  exact Subgroup.disjoint_def.1 (hext.torus_iSupIndep.pairwiseDisjoint hij) hHi hHj

theorem commute_of_forall_not_mem_roots (hext : SteinbergExtras D nw H)
    {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (hind : CFSG.LieType.Steinberg.LinIndepPair γ δ)
    (hcone : ∀ a b : ℕ, 0 < a → 0 < b → a • γ + b • δ ∉ D.roots) {x y : G}
    (hx : x ∈ D.rootGroup γ) (hy : y ∈ D.rootGroup δ) : Commute x y := by
  have h := hext.commutator_mem γ hγ δ hδ hind x hx y hy
  have hbot : (⨆ ε ∈ CFSG.LieType.Steinberg.openCone D.roots γ δ, D.rootGroup ε) = ⊥ :=
    iSup₂_eq_bot.2 fun ε ⟨hε, a, b, ha, hb, he⟩ => absurd (he ▸ hε) (hcone a b ha hb)
  rw [hbot, mem_bot] at h
  exact commutatorElement_eq_one_iff_commute.1 h

end RankOne

section Commute

variable {G : Type*} [Group G]

theorem forall_commute_sup_left {A₁ A₂ B : Subgroup G}
    (h₁ : ∀ x ∈ A₁, ∀ y ∈ B, Commute x y) (h₂ : ∀ x ∈ A₂, ∀ y ∈ B, Commute x y) :
    ∀ x ∈ A₁ ⊔ A₂, ∀ y ∈ B, Commute x y := by
  intro x hx y hy
  have hle : A₁ ⊔ A₂ ≤ centralizer ({y} : Set G) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (h₁ a ha y hy).eq)
      (fun a ha => mem_centralizer_singleton_iff.2 (h₂ a ha y hy).eq)
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem forall_commute_sup_right {A B₁ B₂ : Subgroup G}
    (h₁ : ∀ x ∈ A, ∀ y ∈ B₁, Commute x y) (h₂ : ∀ x ∈ A, ∀ y ∈ B₂, Commute x y) :
    ∀ x ∈ A, ∀ y ∈ B₁ ⊔ B₂, Commute x y := fun x hx y hy =>
  (forall_commute_sup_left (fun a ha b hb => (h₁ b hb a ha).symm)
    (fun a ha b hb => (h₂ b hb a ha).symm) y hy x hx).symm

end Commute

section Product

variable {G M : Type*} [Group G] [Group M] {A B : Subgroup G}

theorem commute_subtype_subtype (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) :
    ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b => hcomm a a.2 b b.2

theorem injective_noncommCoprod_subtype (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hdisj : A ⊓ B = ⊥) :
    Function.Injective (A.subtype.noncommCoprod B.subtype (commute_subtype_subtype hcomm)) := by
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
  rw [range_subtype, range_subtype]
  exact disjoint_iff.2 hdisj

theorem range_noncommCoprod_subtype (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) :
    (A.subtype.noncommCoprod B.subtype (commute_subtype_subtype hcomm)).range = A ⊔ B := by
  rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]

@[expose] noncomputable def supMulEquivProd (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hdisj : A ⊓ B = ⊥) : ↥(A ⊔ B) ≃* A × B :=
  ((MonoidHom.ofInjective (injective_noncommCoprod_subtype hcomm hdisj)).trans
    (MulEquiv.subgroupCongr (range_noncommCoprod_subtype hcomm))).symm

theorem coe_supMulEquivProd_symm (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hdisj : A ⊓ B = ⊥)
    (p : A × B) : (((supMulEquivProd hcomm hdisj).symm p : ↥(A ⊔ B)) : G) = p.1 * p.2 :=
  rfl

@[expose] noncomputable def supLift (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hdisj : A ⊓ B = ⊥)
    (f : A →* M) (g : B →* M) (hfg : ∀ a b, Commute (f a) (g b)) : ↥(A ⊔ B) →* M :=
  (f.noncommCoprod g hfg).comp (supMulEquivProd hcomm hdisj).toMonoidHom

variable (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hdisj : A ⊓ B = ⊥) {f : A →* M} {g : B →* M}
  (hfg : ∀ a b, Commute (f a) (g b))

theorem supLift_apply_left (a : A) : supLift hcomm hdisj f g hfg ⟨a, mem_sup_left a.2⟩ = f a := by
  have h : supMulEquivProd hcomm hdisj ⟨a, mem_sup_left a.2⟩ = (a, 1) := by
    exact (MulEquiv.eq_symm_apply _).1 (Subtype.ext (by rw [coe_supMulEquivProd_symm]; simp))
  simp [supLift, h]

theorem supLift_apply_right (b : B) :
    supLift hcomm hdisj f g hfg ⟨b, mem_sup_right b.2⟩ = g b := by
  have h : supMulEquivProd hcomm hdisj ⟨b, mem_sup_right b.2⟩ = (1, b) := by
    exact (MulEquiv.eq_symm_apply _).1 (Subtype.ext (by rw [coe_supMulEquivProd_symm]; simp))
  simp [supLift, h]

theorem range_supLift : (supLift hcomm hdisj f g hfg).range = f.range ⊔ g.range := by
  rw [supLift, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (supMulEquivProd hcomm hdisj).surjective,
    ← MonoidHom.range_eq_map, MonoidHom.noncommCoprod_range]

end Product

theorem levi_pair {I : Type*} [DecidableEq I] {G : Type*} [Group G] (X : (I → ℤ) → Subgroup G)
    (i j : I) :
    CurtisTits.levi X {i, j} = CurtisTits.levi X {i} ⊔ CurtisTits.levi X {j} := by
  simp only [CurtisTits.levi, Finset.iSup_insert, Finset.iSup_singleton]

theorem f4_root_support_zero_three_check :
    ∀ γ ∈ rootFinset .F4, γ 1 = 0 → γ 2 = 0 → γ 0 = 0 ∨ γ 3 = 0 := by
  decide +kernel

section Pair


variable {K : Type} [Field K]

theorem commute_rootGroup_zero_three {s t : Fin (Tag.rank .F4) → ℤ}
    (hs : s = Pi.single 0 1 ∨ s = -Pi.single 0 1) (ht : t = Pi.single 3 1 ∨ t = -Pi.single 3 1)
    {x y : adjointGroup .F4 K} (hx : x ∈ (Adjoint.f4Datum K).rootGroup s)
    (hy : y ∈ (Adjoint.f4Datum K).rootGroup t) : Commute x y := by
  have hroot : ∀ v, v ∈ (Adjoint.f4Datum K).roots ↔ IsRoot .F4 v := fun v =>
    Adjoint.mem_adjDatum_roots
  have h10 : (1 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h20 : (2 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h30 : (3 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h13 : (1 : Fin (Tag.rank .F4)) ≠ 3 := by decide
  have h23 : (2 : Fin (Tag.rank .F4)) ≠ 3 := by decide
  have h03 : (0 : Fin (Tag.rank .F4)) ≠ 3 := by decide
  refine commute_of_forall_not_mem_roots (Adjoint.f4_steinbergExtras K) ?_ ?_ ?_ ?_ hx hy
  · rw [hroot]
    rcases hs with rfl | rfl
    exacts [isRoot_single _ 0, isRoot_neg_single _ 0]
  · rw [hroot]
    rcases ht with rfl | rfl
    exacts [isRoot_single _ 3, isRoot_neg_single _ 3]
  · intro a b hab
    have h0 := congrFun hab 0
    have h3 := congrFun hab 3
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [h30, h03] at h0 h3 <;> exact ⟨h0, h3⟩
  · intro a b ha hb hmem
    rw [hroot, ← mem_rootFinset] at hmem
    have h := f4_root_support_zero_three_check _ hmem
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [h10, h20, h30, h13, h23, h03] at h <;> omega

theorem commute_levi_zero_three :
    ∀ x ∈ CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0},
      ∀ y ∈ CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}, Commute x y := by
  rw [CurtisTits.levi_singleton, CurtisTits.levi_singleton, CurtisTits.rankOne,
    CurtisTits.rankOne]
  refine forall_commute_sup_left (forall_commute_sup_right ?_ ?_)
    (forall_commute_sup_right ?_ ?_)
  · exact fun x hx y hy => commute_rootGroup_zero_three (Or.inl rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_rootGroup_zero_three (Or.inl rfl) (Or.inr rfl) hx hy
  · exact fun x hx y hy => commute_rootGroup_zero_three (Or.inr rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_rootGroup_zero_three (Or.inr rfl) (Or.inr rfl) hx hy

theorem levi_zero_inf_levi_three_eq_bot :
    CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊓
      CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} = ⊥ := by
  have hc := commute_levi_zero_three (K := K)
  rw [CurtisTits.levi_singleton, CurtisTits.levi_singleton] at hc ⊢
  exact rankOne_inf_rankOne_eq_bot (Adjoint.f4_isCTGroupDatum K) (Adjoint.f4_steinbergExtras K)
    (by decide : (0 : Fin (Tag.rank .F4)) ≠ 3) hc

end Pair

end CFSG.SeitzReduction.F4Pilot
