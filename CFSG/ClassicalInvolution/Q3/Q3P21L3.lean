module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Model
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.RouteD.GapsFrIso
public import CFSG.ClassicalInvolution.RouteD.GapsToralD
public import CFSG.ClassicalInvolution.Q3.Q3TLKOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

section Group

theorem mem_sup_of_commuting {X : Type} [Group X] {P Q : Subgroup X}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) {g : X} (hg : g ∈ P ⊔ Q) :
    ∃ a ∈ P, ∃ b ∈ Q, a * b = g := by
  let S : Subgroup X :=
    { carrier := {g | ∃ a ∈ P, ∃ b ∈ Q, a * b = g}
      one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', P.mul_mem ha ha', b * b', Q.mul_mem hb hb', ?_⟩
        have h := hcomm a' ha' b hb
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, P.inv_mem ha, b⁻¹, Q.inv_mem hb, ?_⟩
        have h := hcomm a ha b hb
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [← h] }
  have hle : P ⊔ Q ≤ S := sup_le (fun a ha => ⟨a, ha, 1, Q.one_mem, by simp⟩)
    (fun b hb => ⟨1, P.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem map_mem_of_fixed_generating {X : Type} [Group X] [Finite X] (P Q H : Subgroup X)
    (hPQ : P ⊔ Q = ⊤) (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hH : H ≤ P)
    (hgen : P ≤ ⨆ g ∈ P, H.map (MulAut.conj g).toMonoidHom) (τ : X ≃* X)
    (hfix : ∀ h ∈ H, τ h = h) : ∀ k ∈ P, τ k ∈ P := by
  set P' : Subgroup X := P.map τ.toMonoidHom with hP'
  set Q' : Subgroup X := Q.map τ.toMonoidHom with hQ'
  have hsup : P' ⊔ Q' = ⊤ := by
    rw [hP', hQ', ← Subgroup.map_sup, hPQ, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr τ.surjective
  have hcomm' : ∀ p ∈ P', ∀ q ∈ Q', p * q = q * p := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    show τ p * τ q = τ q * τ p
    rw [← map_mul, ← map_mul, hcomm p hp q hq]
  have hHP' : H ≤ P' := fun h hh => ⟨h, hH hh, hfix h hh⟩
  have hconj : ∀ g ∈ P, (H.map (MulAut.conj g).toMonoidHom) ≤ P' := by
    intro g hg
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commuting hcomm' (hsup ▸ Subgroup.mem_top g)
    rintro _ ⟨h, hh, rfl⟩
    show g * h * g⁻¹ ∈ P'
    have hbh : b * h = h * b := (hcomm' h (hHP' hh) b hb).symm
    have : g * h * g⁻¹ = a * h * a⁻¹ := by
      rw [← hab]
      calc a * b * h * (a * b)⁻¹ = a * (b * h) * b⁻¹ * a⁻¹ := by group
        _ = a * (h * b) * b⁻¹ * a⁻¹ := by rw [hbh]
        _ = a * h * a⁻¹ := by group
    rw [this]
    exact P'.mul_mem (P'.mul_mem ha (hHP' hh)) (P'.inv_mem ha)
  have hPP' : P ≤ P' := hgen.trans (iSup₂_le fun g hg => hconj g hg)
  have hcard : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.equivMapOfInjective P τ.toMonoidHom τ.injective).toEquiv.symm
  have hEq : P = P' := Subgroup.eq_of_le_of_card_ge hPP' hcard.le
  intro k hk
  rw [hEq]
  exact ⟨k, hk, rfl⟩

end Group

section Shape


@[expose] noncomputable def congrData {ι X X' : Type} [Group X] [Group X'] {Φ : Set (Subgroup X)}
    (e : X ≃* X') (D : LieSystemData3 ι X Φ) :
    LieSystemData3 ι X' (Subgroup.map e.toMonoidHom '' Φ) where
  kind := D.kind
  valid := D.valid
  hom i := e.toMonoidHom.comp (D.hom i)
  ker_le_center i := by
    intro x hx
    have h1 : D.hom i x = 1 := by
      have h2 : e (D.hom i x) = 1 := hx
      simpa using h2
    exact D.ker_le_center i (by simpa using h1)
  commute i j h x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j h x y]
  generate := by
    have h1 : ∀ i, (e.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map e.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h1]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  fundamental := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
    exact ⟨i, R, hR, Subgroup.map_map _ _ _⟩
  meets i := by
    obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨R, hR, ⟨_, hmem, Subgroup.map_map _ _ _⟩⟩
  card_eq := by
    rintro _ ⟨L, hL, rfl⟩
    rw [← D.card_eq L hL]
    exact Nat.card_congr (L.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm

theorem exists_lieSystemData_of_eq {ι X : Type} [Group X] {Φ Φ' : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (h : Φ = Φ') :
    ∃ D' : LieSystemData3 ι X Φ', D'.kind = D.kind := by
  subst h
  exact ⟨D, rfl⟩

theorem localShapeC3_conj {G : Type} [Group G] {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {a : ℕ} {c : CompData} {x : G} (h : LocalShapeC3 a c Ω x) (g : G) :
    LocalShapeC3 a c Ω (g * x * g⁻¹) := by
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := h
  obtain ⟨D', hD'⟩ := exists_lieSystemData_of_eq (congrData (locQuotConj hΩ g x) D)
    (locFamily_conj hΩ g x)
  exact ⟨ι, hι, D', hcard, i₁, by rw [hD']; exact hk, fun i hi => by rw [hD']; exact hrest i hi⟩

end Shape

section Star


theorem star_of_component {X : Type} [Group X] (cc : CompData)
    (hk : cc = CompData.model .POmegaPlus 4)
    (φ : cc.G →* X) (hker : φ.ker ≤ Subgroup.center cc.G) (τ : X ≃* X)
    (hτ2 : ∀ y, τ (τ y) = y) (hτr : ∀ k, τ (φ k) ∈ φ.range) {A B C : Subgroup cc.G}
    (hA : A ∈ cc.fund) (hB : B ∈ cc.fund) (hC : C ∈ cc.fund) (hAB : A ≠ B)
    (hcAB : Commutes A B) (hcAC : Commutes A C) (hcBC : Commutes B C)
    (hfA : ∀ r ∈ A, τ (φ r) = φ r) (hfB : ∀ r ∈ B, τ (φ r) = φ r)
    {x : cc.G} (hxC : x ∈ C) (hx1 : φ x ≠ 1) (hx3 : x ^ 3 = 1) (hxi : τ (φ x) = (φ x)⁻¹) :
    ∃ R : Fin 4 → Subgroup cc.G, (∀ a, R a ∈ cc.fund) ∧
      (∀ a b, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a → Commutes (R a) (R b)) ∧
      (∀ a b, edgeD 4 a b → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R b)) ∧
      (∀ a : Fin 4, 1 ≤ a.val → ∀ g ∈ R a, τ (φ g) = φ g) ∧
      (∀ g ∈ R ⟨0, by omega⟩, τ (φ g) ∈ (R ⟨0, by omega⟩).map φ) ∧
      (∃ g ∈ R ⟨0, by omega⟩, τ (φ g) ≠ φ g) := by
  subst hk
  have hm3 : 3 ≤ 4 := by norm_num
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  let ψ : spinGroup (quadPlus 4 (GaloisField 3 1)) →* X := φ.comp ι.toMonoidHom
  have hker' : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) := by
    intro y hy
    have h1 : ι y ∈ φ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (hker h1)
  have hτr' : ∀ k, τ (ψ k) ∈ ψ.range := by
    intro k
    obtain ⟨y, hy⟩ := hτr (ι k)
    exact ⟨ι.symm y, by simpa [ψ] using hy⟩
  have hψ : ∀ r, ψ (ι.symm r) = φ r := fun r => by simp [ψ]
  obtain ⟨R', hRf, hRc, hRs, hRfix, hRn, hRm⟩ := Q3TD.modelLeafD3_proved ψ hker' τ hτ2 hτr'
    (A.map ι.symm.toMonoidHom) (B.map ι.symm.toMonoidHom) (C.map ι.symm.toMonoidHom)
    (map_symm_mem_fund_iso hm3 hcι hA) (map_symm_mem_fund_iso hm3 hcι hB)
    (map_symm_mem_fund_iso hm3 hcι hC)
    (fun h => hAB (Subgroup.map_injective ι.symm.injective h))
    ((commutes_map_equiv ι.symm).mpr hcAB) ((commutes_map_equiv ι.symm).mpr hcAC)
    ((commutes_map_equiv ι.symm).mpr hcBC)
    (by
      rintro _ ⟨r, hr, rfl⟩
      show τ (ψ (ι.symm r)) = ψ (ι.symm r)
      rw [hψ]
      exact hfA r hr)
    (by
      rintro _ ⟨r, hr, rfl⟩
      show τ (ψ (ι.symm r)) = ψ (ι.symm r)
      rw [hψ]
      exact hfB r hr)
    (ι.symm x) ⟨x, hxC, rfl⟩ (by rw [hψ]; exact hx1)
    (by rw [← map_pow, hx3, map_one]) (by rw [hψ]; exact hxi)
  refine ⟨fun a => (R' a).map ι.toMonoidHom, fun a => map_mem_fund_iso hm3 hcι (hRf a), ?_, ?_,
    ?_, ?_, ?_⟩
  · intro a b hab h1 h2
    exact (commutes_map_equiv ι).mpr (hRc a b hab h1 h2)
  · intro a b hab
    obtain ⟨W, hW⟩ := hRs a b hab
    exact ⟨_, linearBlockStandardPair_map_equiv ι hW⟩
  · intro a ha g hg
    obtain ⟨r, hr, rfl⟩ := hg
    exact hRfix a ha r hr
  · intro g hg
    obtain ⟨r, hr, rfl⟩ := hg
    obtain ⟨r', hr', hr'e⟩ := hRn r hr
    exact ⟨ι r', ⟨r', hr', rfl⟩, hr'e⟩
  · obtain ⟨g, hg, hne⟩ := hRm
    exact ⟨ι g, ⟨g, hg, rfl⟩, hne⟩

theorem component_facts (cc : CompData) (hk : cc = CompData.model .POmegaPlus 4) :
    (∀ R ∈ cc.fund, ∀ R' ∈ cc.fund, ∃ g, R' = conjSub g R) ∧ PowCop3 cc ∧
      (∀ {X : Type} [Group X] (φ : cc.G →* X), φ.range ≤ ⨆ R ∈ cc.fund, R.map φ) ∧
      (∀ R ∈ cc.fund, ∀ r ∈ R, r ∈ Subgroup.center cc.G → r = 1) := by
  subst hk
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  refine ⟨?_, powCop3_model trivial hadm (by decide) (by decide), ?_,
    Q3TLK.fundNoncentral_model3 trivial hadm (by decide)⟩
  · exact ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Nat.prime_three
      (modelFacts_isFundTag trivial) hadm (by decide) (by decide)
  · intro X _ φ
    exact range_le_iSup_fund_plus (p := 3) (f := 1) (by norm_num) hadm φ

theorem aut_preserves_range_of_fixed {ι X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (c : ι) (hk : D.kind c = CompData.model .POmegaPlus 4)
    {A : Subgroup (D.kind c).G} (hA : A ∈ (D.kind c).fund) (τ : X ≃* X)
    (hfix : ∀ r ∈ A, τ (D.hom c r) = D.hom c r) : ∀ k, τ (D.hom c k) ∈ (D.hom c).range := by
  classical
  obtain ⟨hsc, -, hgen, -⟩ := component_facts (D.kind c) hk
  set P : Subgroup X := (D.hom c).range with hP
  set Q : Subgroup X := ⨆ j, ⨆ (_ : j ≠ c), (D.hom j).range with hQ
  have hPQ : P ⊔ Q = ⊤ := by
    rw [eq_top_iff, ← D.generate]
    refine iSup_le fun i => ?_
    by_cases hi : i = c
    · subst hi
      exact le_sup_left
    · exact le_trans (le_iSup₂_of_le i hi le_rfl) le_sup_right
  have hQle : Q ≤ Subgroup.centralizer (P : Set X) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact D.commute c j (Ne.symm hj) x y
  have hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := fun p hp q hq =>
    Subgroup.mem_centralizer_iff.mp (hQle hq) p hp
  have hH : A.map (D.hom c) ≤ P := Subgroup.map_le_range _ _
  have hgenP : P ≤ ⨆ g ∈ P, (A.map (D.hom c)).map (MulAut.conj g).toMonoidHom := by
    refine (hgen (D.hom c)).trans (iSup₂_le fun R hR => ?_)
    obtain ⟨g₀, hg₀⟩ := hsc A hA R hR
    refine le_iSup₂_of_le (D.hom c g₀) ⟨g₀, rfl⟩ ?_
    rw [hg₀]
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hr
    exact ⟨D.hom c a, ⟨a, ha, rfl⟩, by simp [MulAut.conj_apply]⟩
  intro k
  exact map_mem_of_fixed_generating P Q (A.map (D.hom c)) hPQ hcomm hH hgenP τ
    (by rintro _ ⟨r, hr, rfl⟩; exact hfix r hr) _ ⟨k, rfl⟩

end Star

end CFSG.ClassicalInvolution.Q3.Q3P21
