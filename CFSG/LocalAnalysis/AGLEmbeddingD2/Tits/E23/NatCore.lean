module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Types
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixGen

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5 CFSG.RankThree.PartOne

section Sylow

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem isSylowOf_eq_of_le {B Y E : Subgroup Γ} (hB : IsSylowOf 2 B E) (hY : IsPGroup 2 Y)
    (hBY : B ≤ Y) (hYE : Y ≤ E) : Y = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.relIndex_mul_relIndex B Y E hBY hYE
  have hodd : ¬ 2 ∣ B.relIndex Y := fun h2 => hB.2.2 (h1 ▸ dvd_mul_of_dvd_left h2 _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hY
  have hdvd : B.relIndex Y ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    exact hodd (hj ▸ dvd_pow_self 2 hj0)
  rw [hj0, pow_zero] at hj
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hj) hBY

theorem mem_commV_of_mem {W : Type*} [CommGroup W] {E : Subgroup (MulAut W)} {e : MulAut W}
    (he : e ∈ E) {w : W} (hw : w ∈ commV E) : e w ∈ commV E :=
  CFSG.Quasithin.commV_apply_mem_of_mem he hw

end Sylow

section Abstract

variable {V : Type} [CommGroup V] [Finite V]
  {P T M : Subgroup (MulAut V)} {ℰ : Set (Subgroup (MulAut V))}
  (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)
  (hsyl : ∀ E ∈ ℰ, ∀ B ∈ Hyp51.offSet P, B ≤ E → IsSylowOf 2 B E)

include h hV hF hsyl

omit hV hF in
theorem inf_eq_of_mem_offSet {E B : Subgroup (MulAut V)} (hE : E ∈ ℰ)
    (hB : B ∈ Hyp51.offSet P) (hBE : B ≤ E) (hBT : B ≤ T) : T ⊓ E = B :=
  isSylowOf_eq_of_le (hsyl E hE B hB hBE) (h.minpar.syl.2.1.to_le inf_le_left)
    (le_inf hBT hBE) inf_le_right

variable {X : Subgroup (MulAut V)} (hXT : X ≤ T)
  (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
  (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X)

include hXT hTX hX₀

theorem inf_mem_offSet_and_le {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) :
    T ⊓ E ∈ Hyp51.offSet P ∧ T ⊓ E ≤ X := by
  have h43 := h.hyp43 hV
  obtain ⟨B₀, hB₀, hB₀X⟩ := hX₀
  obtain ⟨E₀, hE₀, hB₀E₀⟩ := hF.cover B₀ hB₀
  obtain ⟨t, htT, rfl⟩ := hF.trans E₀ hE₀ E hE
  have htP : t ∈ P := h.minpar.le_M.trans h.minpar.lt_P.le htT
  have hBc : conjSub t B₀ ∈ Hyp51.offSet P := h43.conj_mem B₀ hB₀ t htP
  have hXc : conjSub t X = X := conjSub_eq_of_mem_normalizer' (hTX htT)
  have hBX : conjSub t B₀ ≤ X := hXc ▸ conjSub_mono _ hB₀X
  have hBE : conjSub t B₀ ≤ conjSub t E₀ := conjSub_mono _ hB₀E₀
  rw [inf_eq_of_mem_offSet h hsyl hE hBc hBE (hBX.trans hXT)]
  exact ⟨hBc, hBX⟩

variable (hXgen : X ≤ ⨆ B ∈ {B | B ∈ Hyp51.offSet P ∧ B ≤ X}, B)

include hXgen

theorem eq_iSup_inf : X = ⨆ E ∈ ℰ, (T ⊓ E) := by
  refine le_antisymm (hXgen.trans (iSup₂_le fun B hB => ?_))
    (iSup₂_le fun E hE => (inf_mem_offSet_and_le h hV hF hsyl hXT hTX hX₀ hE).2)
  obtain ⟨E, hE, hBE⟩ := hF.cover B hB.1
  exact le_iSup₂_of_le (f := fun (E : Subgroup (MulAut V)) (_ : E ∈ ℰ) => T ⊓ E) E hE
    (le_inf (hB.2.trans hXT) hBE)

theorem mem_fixV_X {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) {w : V} (hw : w ∈ commV E)
    (hwf : w ∈ fixV (T ⊓ E)) : w ∈ fixV X := by
  rw [eq_iSup_inf h hV hF hsyl hXT hTX hX₀ hXgen]
  have hle : (⨆ E' ∈ ℰ, (T ⊓ E')) ≤ MulAction.stabilizer (MulAut V) w := by
    refine iSup₂_le fun E' hE' x hx => MulAction.mem_stabilizer_iff.2 ?_
    by_cases hne : E = E'
    · subst hne
      exact hwf x hx
    · exact hF.commV_le E hE E' hE' hne hw x hx.2
  intro x hx
  exact MulAction.mem_stabilizer_iff.1 (hle hx)

theorem conjSub_eq_of_fixV
    (hfix : ∀ E ∈ ℰ, ∃ w ∈ commV E, w ∈ fixV (T ⊓ E) ∧ w ∉ fixV E)
    {x : MulAut V} (hxT : x ∈ T) (hx : ∀ v ∈ fixV X, x v = v) {E : Subgroup (MulAut V)}
    (hE : E ∈ ℰ) : conjSub x E = E := by
  have hxP : x ∈ P := h.minpar.le_M.trans h.minpar.lt_P.le hxT
  have hE' : conjSub x E ∈ ℰ := hF.conj_mem E hE x hxP
  by_contra hne
  obtain ⟨w, hw, hwf, hwE⟩ := hfix E hE
  have hxw : x w = w := hx w (mem_fixV_X h hV hF hsyl hXT hTX hX₀ hXgen hE hw hwf)
  have hw' : x w ∈ commV (conjSub x E) := map_mem_commV_conj E x hw
  rw [hxw] at hw'
  exact hwE (hF.commV_le (conjSub x E) hE' E hE hne hw')

theorem mem_of_fixV
    (hfix : ∀ E ∈ ℰ, ∃ w ∈ commV E, w ∈ fixV (T ⊓ E) ∧ w ∉ fixV E)
    (hagree : ∀ E ∈ ℰ, ∀ x ∈ T, conjSub x E = E →
      (∀ w ∈ commV E, w ∈ fixV (T ⊓ E) → x w = w) →
      ∃ u ∈ T ⊓ E, ∀ w ∈ commV E, x w * (u w)⁻¹ ∈ fixV E)
    (hfaith : ∀ E ∈ ℰ, ∀ e ∈ E, (∀ w ∈ commV E, e w * w⁻¹ ∈ fixV E) → e = 1)
    {x : MulAut V} (hxT : x ∈ T) (hx : ∀ v ∈ fixV X, x v = v) : x ∈ X := by
  classical
  have hXeq := eq_iSup_inf h hV hF hsyl hXT hTX hX₀ hXgen
  have hXD : X ≤ genD P := by
    rw [hXeq, ← hF.iSup_eq]
    exact iSup₂_mono fun E _ => inf_le_right
  let S : MulAut V → Set (Subgroup (MulAut V)) := fun y =>
    {E | E ∈ ℰ ∧ ¬ ∀ w ∈ commV E, y w * w⁻¹ ∈ fixV E}
  have hSfin : ∀ y, (S y).Finite := fun y => (Set.toFinite ℰ).subset fun E hE => hE.1
  suffices key : ∀ n, ∀ y ∈ T, (∀ v ∈ fixV X, y v = v) → (S y).ncard = n → y ∈ X from
    key _ x hxT hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hyT hy hn
  have hnorm : ∀ E ∈ ℰ, conjSub y E = E := fun E hE =>
    conjSub_eq_of_fixV h hV hF hsyl hXT hTX hX₀ hXgen hfix hyT hy hE
  have hnorm' : ∀ E ∈ ℰ, conjSub y⁻¹ E = E := fun E hE => by
    conv_lhs => rw [← hnorm E hE]
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hcomm : ∀ E ∈ ℰ, ∀ w ∈ commV E, y w ∈ commV E := fun E hE w hw => by
    have := map_mem_commV_conj E y hw
    rwa [hnorm E hE] at this
  have hcomm' : ∀ E ∈ ℰ, ∀ w ∈ commV E, y⁻¹ w ∈ commV E := fun E hE w hw => by
    have := map_mem_commV_conj E y⁻¹ hw
    rwa [hnorm' E hE] at this
  by_cases hS : S y = ∅
  ·
    have htriv : ∀ E ∈ ℰ, ∀ w ∈ commV E, y w * w⁻¹ ∈ fixV E := by
      intro E hE
      by_contra hne
      have : E ∈ S y := ⟨hE, hne⟩
      rw [hS] at this
      exact this
    have hfixD : ∀ v ∈ fixV (genD P), y v = v := fun v hv => hy v (fun z hz => hv z (hXD hz))
    have hall : ∀ v : V, y v * v⁻¹ ∈ fixV (genD P) := by
      let K : Subgroup V :=
        { carrier := {v | y v * v⁻¹ ∈ fixV (genD P)}
          one_mem' := by simp [(fixV (genD P)).one_mem]
          mul_mem' := fun {a b} ha hb => by
            have e : y (a * b) * (a * b)⁻¹ = (y a * a⁻¹) * (y b * b⁻¹) := by
              rw [map_mul, mul_inv, mul_mul_mul_comm]
            simp only [Set.mem_ofPred_eq] at ha hb ⊢
            rw [e]
            exact (fixV (genD P)).mul_mem ha hb
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_ofPred_eq] at ha ⊢
            have e : y a⁻¹ * a⁻¹⁻¹ = (y a * a⁻¹)⁻¹ := by
              rw [map_inv, inv_inv, mul_inv, inv_inv]
            rw [e]
            exact (fixV (genD P)).inv_mem ha }
      have htop : (⊤ : Subgroup V) ≤ K := by
        rw [← hF.decomp]
        refine sup_le (fun v hv => ?_) (iSup₂_le fun E hE w hw => ?_)
        · show y v * v⁻¹ ∈ fixV (genD P)
          rw [hfixD v hv, mul_inv_cancel]
          exact (fixV (genD P)).one_mem
        · show y w * w⁻¹ ∈ fixV (genD P)
          exact commV_inf_fixV_le_fixV_genD hF hE
            ⟨(commV E).mul_mem (hcomm E hE w hw) ((commV E).inv_mem hw), htriv E hE w hw⟩
      exact fun v => htop (Subgroup.mem_top v)
    have hfixE : ∀ E ∈ ℰ, ∀ w ∈ commV E, y w = w := by
      intro E hE w hw
      have hyE : ∀ e ∈ E, y * e = e * y := by
        intro e he
        have hz : y * e * y⁻¹ * e⁻¹ ∈ E := by
          have h1 : y * e * y⁻¹ ∈ E := by
            have := mem_conjSub_of_mem (g := y) he
            rwa [hnorm E hE] at this
          exact E.mul_mem h1 (E.inv_mem he)
        have hz1 := hfaith E hE _ hz fun w hw => by
          have ha : e⁻¹ w ∈ commV E := mem_commV_of_mem (E.inv_mem he) hw
          have h1 : y⁻¹ (e⁻¹ w) * (e⁻¹ w)⁻¹ ∈ fixV E := by
            have := htriv E hE _ (hcomm' E hE _ ha)
            rw [show y (y⁻¹ (e⁻¹ w)) = e⁻¹ w by simp] at this
            have e2 : y⁻¹ (e⁻¹ w) * (e⁻¹ w)⁻¹ = (e⁻¹ w * (y⁻¹ (e⁻¹ w))⁻¹)⁻¹ := by
              rw [mul_inv_rev, inv_inv, mul_comm]
            rw [e2]
            exact (fixV E).inv_mem this
          set c₁ := y⁻¹ (e⁻¹ w) * (e⁻¹ w)⁻¹ with hc₁
          have hy1 : y⁻¹ (e⁻¹ w) = c₁ * e⁻¹ w := by rw [hc₁]; group
          have he1 : e (y⁻¹ (e⁻¹ w)) = c₁ * w := by
            rw [hy1, map_mul, h1 e he, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
          have hc₂ := htriv E hE w hw
          have hc₁c : c₁ ∈ commV E := by
            rw [hc₁]
            exact (commV E).mul_mem (hcomm' E hE _ ha) ((commV E).inv_mem ha)
          have hc₃ := htriv E hE c₁ hc₁c
          show (y * e * y⁻¹ * e⁻¹) w * w⁻¹ ∈ fixV E
          simp only [MulAut.mul_apply]
          rw [he1, map_mul]
          have e3 : y c₁ * y w * w⁻¹ = (y c₁ * c₁⁻¹) * (y w * w⁻¹) * c₁ := by
            rw [mul_right_comm (y c₁ * c₁⁻¹), inv_mul_cancel_right, ← mul_assoc]
          rw [e3]
          exact (fixV E).mul_mem ((fixV E).mul_mem hc₃ hc₂) h1
        have : y * e * y⁻¹ = e := by
          have := congrArg (· * e) hz1
          simpa [mul_assoc] using this
        calc y * e = (y * e * y⁻¹) * y := by group
          _ = e * y := by rw [this]
      refine Subgroup.closure_induction (p := fun w _ => y w = w) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨e, he, v, rfl⟩
        have hc := hall v
        have hcE : y v * v⁻¹ ∈ fixV E := fun z hz =>
          hc z (by
            rw [← hF.iSup_eq]
            exact (le_iSup₂_of_le (f := fun (E' : Subgroup (MulAut V)) (_ : E' ∈ ℰ) => E') E hE
              le_rfl) hz)
        have hyev : y (e v) = e (y v) := by
          rw [← MulAut.mul_apply, hyE e he, MulAut.mul_apply]
        set c := y v * v⁻¹ with hcdef
        have hyv : y v = c * v := by rw [hcdef]; group
        rw [map_mul, map_inv, hyev, hyv, map_mul, hcE e he]
        calc c * e v * (c * v)⁻¹ = e v * v⁻¹ * (c * c⁻¹) := by rw [mul_inv]; ac_rfl
          _ = e v * v⁻¹ := by rw [mul_inv_cancel, mul_one]
      · exact map_one y
      · intro a b _ _ ha hb
        rw [map_mul, ha, hb]
      · intro a _ ha
        rw [map_inv, ha]
    have hy1 : y = 1 := by
      ext v
      have hK : (⊤ : Subgroup V) ≤ {
          carrier := {v | y v = v}
          one_mem' := map_one y
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_ofPred_eq] at ha hb ⊢
            rw [map_mul, ha, hb]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_ofPred_eq] at ha ⊢
            rw [map_inv, ha] } := by
        rw [← hF.decomp]
        exact sup_le hfixD (iSup₂_le fun E hE w hw => hfixE E hE w hw)
      exact hK (Subgroup.mem_top v)
    rw [hy1]
    exact X.one_mem
  ·
    obtain ⟨E, hE, hEy⟩ := Set.nonempty_iff_ne_empty.2 hS
    obtain ⟨u, ⟨huT, huE⟩, hu⟩ := hagree E hE y hyT (hnorm E hE) fun w hw hwf =>
      hy w (mem_fixV_X h hV hF hsyl hXT hTX hX₀ hXgen hE hw hwf)
    have huX : u ∈ X := (inf_mem_offSet_and_le h hV hF hsyl hXT hTX hX₀ hE).2 ⟨huT, huE⟩
    set y₁ := u⁻¹ * y with hy₁
    have hy₁T : y₁ ∈ T := T.mul_mem (T.inv_mem huT) hyT
    have hy₁fix : ∀ v ∈ fixV X, y₁ v = v := by
      intro v hv
      have h1 : u⁻¹ v = v := hv _ (X.inv_mem huX)
      rw [hy₁, MulAut.mul_apply, hy v hv, h1]
    have hsub : S y₁ ⊆ S y \ {E} := by
      rintro E' ⟨hE', hE'y⟩
      by_cases hEE : E' = E
      · exfalso
        subst hEE
        apply hE'y
        intro w hw
        have hc := hu w hw
        set c := y w * (u w)⁻¹ with hcdef
        have hyw : y w = c * u w := by rw [hcdef]; group
        have hcu : u⁻¹ c = c := hc _ (E'.inv_mem huE)
        show (u⁻¹ * y) w * w⁻¹ ∈ fixV E'
        rw [MulAut.mul_apply, hyw, map_mul, hcu, ← MulAut.mul_apply, inv_mul_cancel,
          MulAut.one_apply, mul_assoc, mul_inv_cancel, mul_one]
        exact hc
      · refine ⟨⟨hE', fun hall => hE'y fun w hw => ?_⟩, hEE⟩
        have hw' : y w ∈ commV E' := hcomm E' hE' w hw
        have huw : u⁻¹ (y w) = y w :=
          hF.commV_le E' hE' E hE hEE hw' _ (E.inv_mem huE)
        show (u⁻¹ * y) w * w⁻¹ ∈ fixV E'
        rw [MulAut.mul_apply, huw]
        exact hall w hw
    have hlt : (S y₁).ncard < n := by
      rw [← hn]
      refine Set.ncard_lt_ncard (lt_of_le_of_lt hsub ?_) (hSfin y)
      exact Set.sdiff_singleton_ssubset.2 ⟨hE, hEy⟩
    have hy₁X := ih _ hlt y₁ hy₁T hy₁fix rfl
    have : y = u * y₁ := by rw [hy₁]; group
    rw [this]
    exact X.mul_mem huX hy₁X

end Abstract

end CFSG.AGLEmbeddingD2.Tits.E23
