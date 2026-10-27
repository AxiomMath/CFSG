module

public import CFSG.CGT.PushingUpLit.BHS5.FiveFive

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

variable {V : Type} [CommGroup V] {P T M : Subgroup (MulAut V)} {ℰ : Set (Subgroup (MulAut V))}

theorem mem_normalizer_of_fix (hF : FiveFive P T M ℰ) {E : Subgroup (MulAut V)} (hE : E ∈ ℰ)
    {t : MulAut V} (ht : t ∈ P) {w : V} (hw : w ∈ commV E) (hwE : w ∉ fixV E) (htw : t w = w) :
    t ∈ Subgroup.normalizer (E : Set (MulAut V)) := by
  have h1 : conjSub t E ∈ ℰ := hF.conj_mem E hE t ht
  by_contra hn
  have hne : conjSub t E ≠ E := fun h => by
    apply hn
    have h2 : conjSub t E ≤ E := h.le
    have h3 : conjSub t⁻¹ E ≤ E := by
      have := congrArg (conjSub t⁻¹) h
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
      exact this.symm.le
    exact CFSG.Quasithin.B6.mem_normalizer_of_conjSub_le h2 h3
  have h4 : w ∈ commV (conjSub t E) := by
    have h5 : commV (conjSub t E) = (commV E).map t.toMonoidHom := B19.commV_map_conj t E
    rw [h5]
    exact ⟨w, hw, htw⟩
  exact hwE (hF.commV_le (conjSub t E) h1 E hE hne h4)

theorem mem_normalizer_of_le_iSup (hF : FiveFive P T M ℰ) {E : Subgroup (MulAut V)} (hE : E ∈ ℰ)
    {x : MulAut V} (hx : x ∈ ⨆ E' ∈ ℰ, E') :
    x ∈ Subgroup.normalizer (E : Set (MulAut V)) := by
  have hle : (⨆ E' ∈ ℰ, E' : Subgroup (MulAut V)) ≤
      Subgroup.normalizer (E : Set (MulAut V)) := by
    refine iSup₂_le fun E' hE' => ?_
    by_cases hEE : E' = E
    · subst hEE
      exact Subgroup.le_normalizer
    · intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he
        have hc : y * e = e * y := hF.comm E' hE' E hE hEE y hy e he
        have : y * e * y⁻¹ = e := by rw [hc]; group
        rw [this]
        exact he
      · intro he'
        have hc : y * (y * e * y⁻¹) = (y * e * y⁻¹) * y := hF.comm E' hE' E hE hEE y hy _ he'
        have h2 : y * (y * e * y⁻¹) = y * e := by rw [hc]; group
        have h3 : y * e * y⁻¹ = e := mul_left_cancel h2
        rw [← h3]
        exact he'
  exact hle hx

theorem apply_mem_commV_of_mem {E : Subgroup (MulAut V)} {e : MulAut V} (he : e ∈ E) {w : V}
    (hw : w ∈ commV E) : e w ∈ commV E :=
  CFSG.Quasithin.G6.apply_mem_commV (fun _ hy => E.mul_mem (E.mul_mem he hy) (E.inv_mem he)) hw

@[expose] def restrE (E : Subgroup (MulAut V)) : Subgroup (MulAut V) where
  carrier := {x | ∃ e ∈ E, ∀ w ∈ commV E, x w = e w}
  one_mem' := ⟨1, E.one_mem, fun w _ => rfl⟩
  mul_mem' := by
    rintro x _ ⟨e, he, hxe⟩ ⟨e', he', hye⟩
    refine ⟨e * e', E.mul_mem he he', fun w hw => ?_⟩
    rw [MulAut.mul_apply, hye w hw, hxe _ (apply_mem_commV_of_mem he' hw)]
    rfl
  inv_mem' := by
    rintro x ⟨e, he, hxe⟩
    refine ⟨e⁻¹, E.inv_mem he, fun w hw => ?_⟩
    have h1 : e⁻¹ w ∈ commV E := apply_mem_commV_of_mem (E.inv_mem he) hw
    have h2 : x (e⁻¹ w) = w := by
      rw [hxe _ h1]
      show e (e⁻¹ w) = w
      simp
    show x.symm w = (e⁻¹ : MulAut V) w
    exact x.injective ((x.apply_symm_apply w).trans h2.symm)

theorem exists_comp_restr (hF : FiveFive P T M ℰ) {E : Subgroup (MulAut V)} (hE : E ∈ ℰ)
    {x : MulAut V} (hx : x ∈ ⨆ E' ∈ ℰ, E') :
    ∃ e ∈ E, ∀ w ∈ commV E, x w = e w := by
  have hle : (⨆ E' ∈ ℰ, E' : Subgroup (MulAut V)) ≤ restrE E := by
    refine iSup₂_le fun E' hE' => ?_
    intro y hy
    by_cases hEE : E' = E
    · subst hEE
      exact ⟨y, hy, fun w _ => rfl⟩
    · refine ⟨1, E.one_mem, fun w hw => ?_⟩
      have := hF.commV_le E hE E' hE' (fun h => hEE h.symm) hw
      rw [mem_fixV] at this
      exact this y hy
  exact hle hx

theorem fix_of_le_iSup {S : Set (Subgroup (MulAut V))} {v : V} (h : ∀ E ∈ S, v ∈ fixV E)
    {x : MulAut V} (hx : x ∈ ⨆ E ∈ S, E) : x v = v := by
  have hle : (⨆ E ∈ S, E : Subgroup (MulAut V)) ≤ MulAction.stabilizer (MulAut V) v := by
    refine iSup₂_le fun E hE y hy => ?_
    rw [MulAction.mem_stabilizer_iff]
    exact h E hE y hy
  have := hle hx
  rw [MulAction.mem_stabilizer_iff] at this
  exact this

theorem mem_genD_of_restr [Finite V] (hF : FiveFive P T M ℰ) {t : MulAut V}
    (hfix : ∀ v ∈ fixV (genD P), t v = v)
    (hcomp : ∀ E ∈ ℰ, ∃ e ∈ E, ∀ w ∈ commV E, t w = e w) : t ∈ genD P := by
  classical
  have hfin : ℰ.Finite := Set.toFinite _
  have key : ∀ s : Finset (Subgroup (MulAut V)), (↑s : Set (Subgroup (MulAut V))) ⊆ ℰ →
      ∃ x ∈ (⨆ E ∈ (↑s : Set (Subgroup (MulAut V))), E : Subgroup (MulAut V)),
        ∀ E ∈ s, ∀ w ∈ commV E, t w = x w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, Subgroup.one_mem _, by simp⟩
    | insert E s hEs ih =>
      intro hsub
      have hEℰ : E ∈ ℰ := hsub (Finset.mem_insert_self E s)
      have hsℰ : (↑s : Set (Subgroup (MulAut V))) ⊆ ℰ := fun a ha =>
        hsub (Finset.mem_insert_of_mem ha)
      obtain ⟨x', hx', hx'e⟩ := ih hsℰ
      obtain ⟨e, he, hte⟩ := hcomp E hEℰ
      have hx'fix : ∀ w ∈ commV E, x' w = w := by
        intro w hw
        refine fix_of_le_iSup (S := (↑s : Set (Subgroup (MulAut V)))) (fun E' hE' => ?_) hx'
        have hne : E ≠ E' := fun h => hEs (h ▸ hE')
        exact hF.commV_le E hEℰ E' (hsℰ hE') hne hw
      refine ⟨x' * e, ?_, ?_⟩
      · rw [Finset.coe_insert, iSup_insert]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx') (Subgroup.mem_sup_left he)
      · intro E'' hE'' w hw
        rcases Finset.mem_insert.mp hE'' with rfl | hE''s
        · rw [MulAut.mul_apply, hte w hw]
          exact (hx'fix _ (apply_mem_commV_of_mem he hw)).symm
        · have hne : E'' ≠ E := fun h => hEs (h ▸ hE''s)
          have hew : e w = w := by
            have := hF.commV_le E'' (hsℰ hE''s) E hEℰ hne hw
            rw [mem_fixV] at this
            exact this e he
          rw [MulAut.mul_apply, hew]
          exact hx'e E'' hE''s w hw
  obtain ⟨x, hx, hxe⟩ := key hfin.toFinset (by simp)
  have hxg : x ∈ genD P := by
    rw [← hF.iSup_eq]
    simpa using hx
  have hK : fixV (genD P) ⊔ (⨆ E ∈ ℰ, commV E) ≤ MonoidHom.eqLocus t.toMonoidHom x.toMonoidHom := by
    refine sup_le (fun v hv => ?_) (iSup₂_le fun E hE w hw => ?_)
    · show t v = x v
      rw [hfix v hv, (mem_fixV.mp hv) x hxg]
    · exact hxe E (hfin.mem_toFinset.mpr hE) w hw
  have htx : t = x := by
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV (genD P) ⊔ (⨆ E ∈ ℰ, commV E) := by
      rw [hF.decomp]
      exact Subgroup.mem_top v
    exact hK hv
  rw [htx]
  exact hxg

theorem not_commV_le_fixV (hF : FiveFive P T M ℰ) {X : Subgroup (MulAut V)} (hXle : X ≤ genD P)
    (hXne : X ≠ ⊥) (hXT : ∀ t ∈ T, conjSub t X = X) {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) :
    ¬ commV E ≤ fixV X := by
  intro h
  have hall : ∀ E' ∈ ℰ, commV E' ≤ fixV X := by
    intro E' hE'
    obtain ⟨t, ht, rfl⟩ := hF.trans E hE E' hE'
    have h5 : commV (conjSub t E) = (commV E).map t.toMonoidHom := B19.commV_map_conj t E
    rw [h5]
    rintro _ ⟨w₀, hw₀, rfl⟩
    rw [mem_fixV]
    intro x hx
    have hx' : t⁻¹ * x * t ∈ X := by
      have : x ∈ conjSub t X := (hXT t ht).symm ▸ hx
      simpa [mem_conjSub_iff] using this
    have := (mem_fixV.mp (h hw₀)) _ hx'
    simp only [MulAut.mul_apply] at this
    have h2 := congrArg t this
    simpa using h2
  have htop : ∀ v : V, ∀ x ∈ X, x v = v := by
    intro v x hx
    have hv : v ∈ fixV (genD P) ⊔ (⨆ E ∈ ℰ, commV E) := by
      rw [hF.decomp]
      exact Subgroup.mem_top v
    have hle : fixV (genD P) ⊔ (⨆ E ∈ ℰ, commV E) ≤ fixV X :=
      sup_le (CFSG.Quasithin.fixV_anti hXle) (iSup₂_le fun E' hE' => hall E' hE')
    exact (mem_fixV.mp (hle hv)) x hx
  apply hXne
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact MulEquiv.ext fun v => htop v x hx

end CFSG.CGT.PushingUpLit.BHS7
