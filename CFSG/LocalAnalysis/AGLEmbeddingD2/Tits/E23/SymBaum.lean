module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SymBaumComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Tits.E23

open Equiv CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_mul_of_mem_sup_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, g = a * b := by
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K H hK] at hg
  obtain ⟨y, hy, x, hx, rfl⟩ := hg
  exact ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.1 (hK hy) x).1 hx, y, hy, by group⟩

@[expose] def offGen (P K : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ B ∈ {B | B ∈ Hyp51.offSet P ∧ B ≤ K}, B

theorem offGen_le (P K : Subgroup (MulAut V)) : offGen P K ≤ K :=
  iSup₂_le fun _ hB => hB.2

section Global

variable {P T M : Subgroup (MulAut V)} {X : Subgroup (MulAut V)}
  {ℰ : Set (Subgroup (MulAut V))}

theorem le_iSup_offGen (hF : FiveFive P T M ℰ) (hXgen : X ≤ offGen P X) :
    X ≤ ⨆ E ∈ ℰ, offGen P (E ⊓ X) := by
  refine hXgen.trans (iSup₂_le fun B hB => ?_)
  obtain ⟨E, hE, hBE⟩ := hF.cover B hB.1
  exact le_iSup₂_of_le (f := fun (E : Subgroup (MulAut V)) (_ : E ∈ ℰ) => offGen P (E ⊓ X)) E hE
    (le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V))
      (_ : B ∈ {B | B ∈ Hyp51.offSet P ∧ B ≤ E ⊓ X}) => B) B ⟨hB.1, le_inf hBE hB.2⟩ le_rfl)

theorem le_iSup_inf_of_gen (hF : FiveFive P T M ℰ) (hXgen : X ≤ offGen P X) :
    X ≤ ⨆ E ∈ ℰ, (E ⊓ X) :=
  (le_iSup_offGen hF hXgen).trans (iSup₂_mono fun _ _ => offGen_le _ _)

theorem iSup_inf_le (X : Subgroup (MulAut V)) (ℰ : Set (Subgroup (MulAut V))) :
    (⨆ E ∈ ℰ, (E ⊓ X)) ≤ X :=
  iSup₂_le fun _ _ => inf_le_right

theorem inf_le_offGen (hF : FiveFive P T M ℰ) (hXgen : X ≤ offGen P X) {E : Subgroup (MulAut V)}
    (hE : E ∈ ℰ) : E ⊓ X ≤ offGen P (E ⊓ X) := by
  set F : Subgroup (MulAut V) := ⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E' with hFdef
  have hFcent : F ≤ Subgroup.centralizer (E : Set (MulAut V)) := by
    refine iSup₂_le fun E' hE' => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hF.comm E hE E' hE'.1 (Ne.symm hE'.2) x hx y hy
  set Y : Subgroup (MulAut V) := offGen P (E ⊓ X) with hY
  have hYE : Y ≤ E := (offGen_le _ _).trans inf_le_left
  have hFnorm : F ≤ Subgroup.normalizer (Y : Set (MulAut V)) :=
    hFcent.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hYE)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hX' : X ≤ Y ⊔ F := by
    refine (le_iSup_offGen hF hXgen).trans (iSup₂_le fun E' hE' => ?_)
    by_cases hEE : E' = E
    · rw [hEE]
      exact le_sup_left
    · exact ((offGen_le _ _).trans inf_le_left).trans
        ((le_iSup₂_of_le (f := fun (E'' : Subgroup (MulAut V)) (_ : E'' ∈ {E'' | E'' ∈ ℰ ∧ E'' ≠ E})
          => E'') E' ⟨hE', hEE⟩ le_rfl).trans le_sup_right)
  intro x hx
  obtain ⟨a, ha, f, hf, hxaf⟩ := exists_mul_of_mem_sup_of_le_normalizer hFnorm (hX' hx.2)
  have hfE : f ∈ E := by
    have : f = a⁻¹ * x := by rw [hxaf]; group
    rw [this]
    exact E.mul_mem (E.inv_mem (hYE ha)) hx.1
  have hf1 : f = 1 := Subgroup.disjoint_def.1 (hF.indep E hE) hfE hf
  rw [hxaf, hf1, mul_one]
  exact ha

theorem hcl_of {E : Subgroup (MulAut V)} {m : ℕ} {θ : ↥E ≃* Perm (Fin m)}
    {β : ↥(commV E) →* coreMod m} {i₀ : Fin m} (hc : SymComp P M E m θ β i₀)
    (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) (hXT : X ≤ T) (hXgen : X ≤ offGen P X) :
    ∀ g : ↥E, (g : MulAut V) ∈ X →
      g ∈ Subgroup.closure {e : ↥E | (e : MulAut V) ∈ T ∧ (θ e).IsSwap} := by
  intro g hg
  have h1 : (g : MulAut V) ∈ offGen P (E ⊓ X) := inf_le_offGen hF hXgen hE ⟨g.2, hg⟩
  have h2 : offGen P (E ⊓ X) ≤
      (Subgroup.closure {e : ↥E | (e : MulAut V) ∈ T ∧ (θ e).IsSwap}).map E.subtype := by
    refine iSup₂_le fun B hB => ?_
    intro b hb
    have hbE : b ∈ E := (hB.2 hb).1
    have hbT : b ∈ T := hXT (hB.2 hb).2
    obtain ⟨i, j, hij, hB'⟩ := hc.dsw B ⟨hB.1, hB.2.trans inf_le_left⟩
    refine ⟨⟨b, hbE⟩, ?_, rfl⟩
    rcases hB' ⟨b, hbE⟩ hb with h0 | h0
    · have : (⟨b, hbE⟩ : ↥E) = 1 := θ.injective (h0.trans (map_one θ).symm)
      rw [this]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hbT, i, j, hij, h0⟩
  obtain ⟨y, hy, hyg⟩ := h2 h1
  have : y = g := Subtype.ext hyg
  rw [← this]
  exact hy

theorem claim_two {E : Subgroup (MulAut V)} {m : ℕ} {θ : ↥E ≃* Perm (Fin m)}
    {β : ↥(commV E) →* coreMod m} {i₀ : Fin m} (hc : SymComp P M E m θ β i₀)
    (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ)
    (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X) (hXgen : X ≤ offGen P X) :
    E ⊓ X = Subgroup.closure
      {x : MulAut V | ∃ hx : x ∈ E, x ∈ T ∧ (θ ⟨x, hx⟩).IsSwap} := by
  apply le_antisymm
  · intro x hx
    have h1 := hcl_of hc hF hE hXT hXgen ⟨x, hx.1⟩ hx.2
    have h2 : Subgroup.closure {e : ↥E | (e : MulAut V) ∈ T ∧ (θ e).IsSwap} ≤
        (Subgroup.closure {x : MulAut V | ∃ hx : x ∈ E, x ∈ T ∧ (θ ⟨x, hx⟩).IsSwap}).comap
          E.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro e ⟨heT, hsw⟩
      exact Subgroup.subset_closure ⟨e.2, heT, hsw⟩
    exact h2 h1
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hx, hxT, c, d, hcd, hθ⟩
    exact ⟨hx, hc.swap_mem_X h hV hF hE hXT hTX hX₀ (x := ⟨x, hx⟩) hxT hcd hθ⟩

@[expose] def stabSub (w : V) : Subgroup (MulAut V) where
  carrier := {g | g w = w}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    show a (b w) = w
    have ha' : a w = w := ha
    have hb' : b w = w := hb
    rw [hb', ha']
  inv_mem' := by
    intro a ha
    show a⁻¹ w = w
    have ha' : a w = w := ha
    calc a⁻¹ w = a⁻¹ (a w) := by rw [ha']
      _ = w := by simp

theorem mem_stabSub {w : V} {g : MulAut V} : g ∈ stabSub w ↔ g w = w := Iff.rfl

theorem mem_fixV_of_fix (hF : FiveFive P T M ℰ) (hX : X ≤ ⨆ E ∈ ℰ, (E ⊓ X))
    {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) {w : V} (hw : w ∈ commV E)
    (hfix : ∀ g ∈ E, g ∈ X → g w = w) : w ∈ fixV X := by
  have : X ≤ stabSub w := by
    refine hX.trans (iSup₂_le fun E' hE' => ?_)
    intro g hg
    rw [mem_stabSub]
    by_cases hEE : E' = E
    · subst hEE
      exact hfix g hg.1 hg.2
    · exact hF.commV_le E hE E' hE' (Ne.symm hEE) hw g hg.1
  exact fun g hg => this hg

theorem fix_commV_of_mem_iSup (hF : FiveFive P T M ℰ) {F : Set (Subgroup (MulAut V))}
    (hFℰ : F ⊆ ℰ) {E₀ : Subgroup (MulAut V)} (hE₀ : E₀ ∈ ℰ) (hE₀F : E₀ ∉ F)
    {y : MulAut V} (hy : y ∈ ⨆ E ∈ F, (E ⊓ X)) {w : V} (hw : w ∈ commV E₀) : y w = w := by
  have : (⨆ E ∈ F, (E ⊓ X)) ≤ stabSub w := by
    refine iSup₂_le fun E hE => ?_
    intro g hg
    rw [mem_stabSub]
    have hne : E₀ ≠ E := fun h' => hE₀F (h' ▸ hE)
    exact hF.commV_le E₀ hE₀ E (hFℰ hE) hne hw g hg.1
  exact this hy

theorem SymComp.exists_fixed_vec {E : Subgroup (MulAut V)} {m : ℕ} {θ : ↥E ≃* Perm (Fin m)}
    {β : ↥(commV E) →* coreMod m} {i₀ : Fin m} (hc : SymComp P M E m θ β i₀)
    (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ)
    (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X)
    (hcl : ∀ g : ↥E, (g : MulAut V) ∈ X →
      g ∈ Subgroup.closure {e : ↥E | (e : MulAut V) ∈ T ∧ (θ e).IsSwap}) :
    ∃ w : ↥(commV E), w ≠ 1 ∧ ∀ g : ↥E, (g : MulAut V) ∈ X → (g : MulAut V) w.1 = w.1 := by
  obtain ⟨e, a, b, heX, hab, he⟩ := hc.exists_swap_mem_X h hV hF hE hTX hX₀
  obtain ⟨w, hw, hwfix⟩ := hc.exists_vec_of_swap h hV hF hE hXT hTX hX₀ hcl hab
    (mem_swapSub.2 ⟨e, heX, he⟩)
  refine ⟨w, fun h1 => ?_, hwfix⟩
  rw [h1, map_one] at hw
  exact uvec_mul_ne_one hc.odd hab hw.symm

theorem SymComp.mem_normalizer_of_cen {E : Subgroup (MulAut V)} {m : ℕ}
    {θ : ↥E ≃* Perm (Fin m)} {β : ↥(commV E) →* coreMod m} {i₀ : Fin m}
    (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1)
    (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) (hXT : X ≤ T)
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X) (hXgen : X ≤ offGen P X)
    {x : MulAut V} (hxT : x ∈ T) (hxfix : ∀ u ∈ fixV X, x u = u) :
    x ∈ Subgroup.normalizer (E : Set (MulAut V)) := by
  by_contra hxN
  have hcl := hcl_of hc hF hE hXT hXgen
  obtain ⟨w, hw1, hwfix⟩ := hc.exists_fixed_vec h hV hF hE hXT hTX hX₀ hcl
  have hwX : w.1 ∈ fixV X := mem_fixV_of_fix hF (le_iSup_inf_of_gen hF hXgen) hE w.2
    (fun g hg hgX => hwfix ⟨g, hg⟩ hgX)
  have hxw : x w.1 = w.1 := hxfix w.1 hwX
  have hE' : conjSub x E ∈ ℰ := hF.conj_mem E hE x (h.minpar.T_le hxT)
  have hne : E ≠ conjSub x E := fun h' =>
    hxN (Subgroup.mem_normalizer_iff_map_conj_eq.2 h'.symm)
  have hmem : x w.1 ∈ commV (conjSub x E) := by
    have := B19.commV_map_conj x E
    show x w.1 ∈ commV (E.map (MulAut.conj x).toMonoidHom)
    rw [this]
    exact ⟨w.1, w.2, rfl⟩
  have hw' : w.1 ∈ fixV E := by
    have := hF.commV_le (conjSub x E) hE' E hE (Ne.symm hne) (hxw ▸ hmem)
    exact this
  exact hw1 (hc.commV_inf_fixV (w := w) fun g => hw' g g.2)

theorem E_step (hS : ∀ E ∈ compSet P M, SymType (genD P ⊓ M) (Hyp51.offSet P) E)
    (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M (compSet P M))
    (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X) (hXgen : X ≤ offGen P X)
    {E : Subgroup (MulAut V)} (hE : E ∈ compSet P M) {x : MulAut V} (hxT : x ∈ T)
    (hxfix : ∀ u ∈ fixV X, x u = u) :
    x ∈ Subgroup.normalizer (E : Set (MulAut V)) ∧
      ∃ ε : ↥E, (ε : MulAut V) ∈ X ∧ ∀ w ∈ commV E, (ε : MulAut V) w = x w := by
  obtain ⟨m, θ, β, i₀, hc⟩ := SymComp.exists_of_symType (hS E hE)
  have hcl := hcl_of hc hF hE hXT hXgen
  have hxN := hc.mem_normalizer_of_cen h hV hF hE hXT hTX hX₀ hXgen hxT hxfix
  refine ⟨hxN, hc.local_step h hV hF hE hXT hTX hX₀ hcl hxT hxN ?_⟩
  intro w hw hwfix
  exact hxfix w (mem_fixV_of_fix hF (le_iSup_inf_of_gen hF hXgen) hE hw
    (fun g hg hgX => hwfix ⟨g, hg⟩ hgX))

theorem exists_agree (hS : ∀ E ∈ compSet P M, SymType (genD P ⊓ M) (Hyp51.offSet P) E)
    (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M (compSet P M))
    (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X) (hXgen : X ≤ offGen P X)
    {x : MulAut V} (hxT : x ∈ T) (hxfix : ∀ u ∈ fixV X, x u = u) :
    ∀ F : Finset (Subgroup (MulAut V)), (∀ E ∈ F, E ∈ compSet P M) →
      ∃ y ∈ ⨆ E ∈ (F : Set (Subgroup (MulAut V))), (E ⊓ X),
        ∀ E ∈ F, ∀ w ∈ commV E, y w = x w := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  | insert E₀ F hE₀F ih =>
    intro hFmem
    obtain ⟨yF, hyF, hyFagree⟩ := ih (fun E hE => hFmem E (Finset.mem_insert_of_mem hE))
    have hE₀ : E₀ ∈ compSet P M := hFmem E₀ (Finset.mem_insert_self _ _)
    obtain ⟨-, ε, hεX, hε⟩ := E_step hS h hV hF hXT hTX hX₀ hXgen hE₀ hxT hxfix
    have hFsub : ((F : Set (Subgroup (MulAut V)))) ⊆ compSet P M := fun E hE =>
      hFmem E (Finset.mem_insert_of_mem hE)
    have hE₀F' : E₀ ∉ (F : Set (Subgroup (MulAut V))) := by simpa using hE₀F
    refine ⟨(ε : MulAut V) * yF, ?_, ?_⟩
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact le_iSup₂_of_le (f := fun (E : Subgroup (MulAut V))
          (_ : E ∈ ((insert E₀ F : Finset (Subgroup (MulAut V))) : Set (Subgroup (MulAut V)))) =>
          E ⊓ X) E₀ (by simp) le_rfl ⟨ε.2, hεX⟩
      · have hmono : (⨆ E ∈ (F : Set (Subgroup (MulAut V))), (E ⊓ X)) ≤
            ⨆ E ∈ ((insert E₀ F : Finset (Subgroup (MulAut V))) : Set (Subgroup (MulAut V))),
              (E ⊓ X) :=
          iSup₂_le fun E hE => le_iSup₂_of_le (f := fun (E : Subgroup (MulAut V))
            (_ : E ∈ ((insert E₀ F : Finset (Subgroup (MulAut V))) :
              Set (Subgroup (MulAut V)))) => E ⊓ X) E
            (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hE))) le_rfl
        exact hmono hyF
    · intro E hE w hw
      rcases Finset.mem_insert.1 hE with rfl | hEF
      · show (ε : MulAut V) (yF w) = x w
        rw [fix_commV_of_mem_iSup hF hFsub hE₀ hE₀F' hyF hw]
        exact hε w hw
      · show (ε : MulAut V) (yF w) = x w
        rw [hyFagree E hEF w hw]
        have hxN : x ∈ Subgroup.normalizer (E : Set (MulAut V)) :=
          (E_step hS h hV hF hXT hTX hX₀ hXgen (hFsub hEF) hxT hxfix).1
        have hxw : x w ∈ commV E := mem_commV_of_mem_normalizer hxN hw
        have hne : E ≠ E₀ := fun h' => hE₀F (h' ▸ hEF)
        exact (hF.commV_le E (hFsub hEF) E₀ hE₀ hne hxw) ε ε.2

theorem symBaum (hsymT : BHSSymType) (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1)
    (hS : ∀ E ∈ compSet P M, SymType (genD P ⊓ M) (Hyp51.offSet P) E ∧ 120 ≤ Nat.card E)
    {X : Subgroup (MulAut V)} (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hXgen : X ≤ ⨆ B ∈ {B | B ∈ Hyp51.offSet P ∧ B ≤ X}, B)
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X) :
    X = (⨆ E ∈ compSet P M, (E ⊓ X)) ∧
    (∀ E ∈ compSet P M, ∃ (m : ℕ) (θ : ↥E ≃* Equiv.Perm (Fin m))
        (β : ↥(commV E) ≃* ↥(coreMod m)),
      (∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
        β ⟨(x : MulAut V) p, hp⟩ = coreAct m (θ x) (β p)) ∧
      E ⊓ X = Subgroup.closure {x | ∃ hx : x ∈ E, x ∈ T ∧ (θ ⟨x, hx⟩).IsSwap}) ∧
    cenIn T (fixV X) ≤ X := by
  have hF : FiveFive P T M (compSet P M) := five_five hsymT h hV
  have hS' : ∀ E ∈ compSet P M, SymType (genD P ⊓ M) (Hyp51.offSet P) E := fun E hE => (hS E hE).1
  have hXgen' : X ≤ offGen P X := hXgen
  refine ⟨le_antisymm (le_iSup_inf_of_gen hF hXgen') (iSup_inf_le X _), ?_, ?_⟩
  · intro E hE
    obtain ⟨m, θ, β, i₀, hc⟩ := SymComp.exists_of_symType (hS' E hE)
    have hcl := hcl_of hc hF hE hXT hXgen'
    exact ⟨m, θ, MulEquiv.ofBijective β ⟨(MonoidHom.ker_eq_bot_iff β).1 hc.ker, hc.surj⟩,
      hc.equiv, claim_two hc h hV hF hE hXT hTX hX₀ hXgen'⟩
  · intro x hx
    obtain ⟨hxT, hxfix⟩ := hx
    have hXgenD : X ≤ genD P := hXgen'.trans (iSup₂_le fun B hB =>
      le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ Hyp51.offSet P) => B) B hB.1
        le_rfl)
    obtain ⟨y, hy, hyagree⟩ := exists_agree hS' h hV hF hXT hTX hX₀ hXgen' hxT hxfix
      (Set.toFinite (compSet P M)).toFinset (fun E hE => (Set.Finite.mem_toFinset _).1 hE)
    have hyX : y ∈ X := by
      have hmono : (⨆ E ∈ (((Set.toFinite (compSet P M)).toFinset : Finset (Subgroup (MulAut V))) :
          Set (Subgroup (MulAut V))), (E ⊓ X)) ≤ ⨆ E ∈ compSet P M, (E ⊓ X) :=
        iSup₂_le fun E hE => le_iSup₂_of_le (f := fun (E : Subgroup (MulAut V))
          (_ : E ∈ compSet P M) => E ⊓ X) E
          ((Set.Finite.mem_toFinset _).1 (Finset.mem_coe.1 hE)) le_rfl
      exact iSup_inf_le X (compSet P M) (hmono hy)
    have hxy : ∀ v : V, x v = y v := by
      let eq : Subgroup V := x.toMonoidHom.eqLocus y.toMonoidHom
      have hle : (⊤ : Subgroup V) ≤ eq := by
        rw [← hF.decomp]
        refine sup_le (fun v hv => ?_) (iSup₂_le fun E hE => fun w hw => ?_)
        · show x v = y v
          have h1 : x v = v := hxfix v (fun g hg => hv g (hXgenD hg))
          have h2 : y v = v := hv y (hXgenD hyX)
          rw [h1, h2]
        · show x w = y w
          exact (hyagree E ((Set.Finite.mem_toFinset _).2 hE) w hw).symm
      exact fun v => hle (Subgroup.mem_top v)
    have : x = y := MulEquiv.ext hxy
    rw [this]
    exact hyX

end Global

end CFSG.AGLEmbeddingD2.Tits.E23
