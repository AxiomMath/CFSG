module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.NatCore

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5 CFSG.RankThree.PartOne

section Translate

variable {V : Type} [CommGroup V]

theorem mem_fixV_conjSub {g : MulAut V} {A : Subgroup (MulAut V)} {v : V} :
    v ∈ fixV (conjSub g A) ↔ g⁻¹ v ∈ fixV A :=
  CFSG.Quasithin.ConjTransport.mem_fixV_map_conj_iff

theorem commute_of_mem_iSup {𝒮 : Set (Subgroup (MulAut V))} {E₀ : Subgroup (MulAut V)}
    (hcomm : ∀ E ∈ 𝒮, ∀ x ∈ E, ∀ e ∈ E₀, x * e = e * x) {u : MulAut V}
    (hu : u ∈ ⨆ E ∈ 𝒮, E) {e : MulAut V} (he : e ∈ E₀) : u * e = e * u := by
  have hle : (⨆ E ∈ 𝒮, E) ≤ Subgroup.centralizer ({e} : Set (MulAut V)) := by
    refine iSup₂_le fun E hE x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hcomm E hE x hx h he).symm
  have := Subgroup.mem_centralizer_iff.1 (hle hu) e (Set.mem_singleton e)
  exact this.symm

theorem fix_of_mem_iSup {𝒮 : Set (Subgroup (MulAut V))} {w : V}
    (hw : ∀ E ∈ 𝒮, w ∈ fixV E) {u : MulAut V} (hu : u ∈ ⨆ E ∈ 𝒮, E) : u w = w :=
  mem_fixV_iSup hw u hu

theorem conjSub_eq_of_commute {u : MulAut V} {R : Subgroup (MulAut V)}
    (hu : ∀ r ∈ R, u * r = r * u) : conjSub u R = R := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have e : (u⁻¹ * x * u) * u = x * u := by rw [← hu _ hx]; group
    have := mul_right_cancel e
    rwa [this] at hx
  · intro hx
    have e : u⁻¹ * x * u = x := by
      calc u⁻¹ * x * u = u⁻¹ * (x * u) := mul_assoc _ _ _
        _ = u⁻¹ * (u * x) := by rw [hu x hx]
        _ = x := inv_mul_cancel_left _ _
    rwa [e]

end Translate

structure GoodEl {V : Type} [CommGroup V] (E R : Subgroup (MulAut V)) (y : MulAut V) : Prop where
  mem : y ∈ E
  order : orderOf y = 3
  gen : E ≤ R ⊔ conjSub y R
  fix : ∀ w ∈ commV E, y w = w → w ∈ fixV E
  split : ∀ w ∈ commV E, ∃ a ∈ commV E ⊓ fixV R, ∃ b ∈ commV E ⊓ fixV (conjSub y R), w = a * b

section Abstract

variable {V : Type} [CommGroup V]
  {P T M : Subgroup (MulAut V)} {ℰ : Set (Subgroup (MulAut V))}

theorem exists_prod_good (hF : FiveFive P T M ℰ)
    (hgood : ∀ E ∈ ℰ, ∃ y, GoodEl E (T ⊓ E) y) (S : Finset (Subgroup (MulAut V)))
    (hS : (↑S : Set (Subgroup (MulAut V))) ⊆ ℰ) :
    ∃ z : MulAut V, z ^ 3 = 1 ∧ z ∈ (⨆ E ∈ (↑S : Set (Subgroup (MulAut V))), E) ∧
      ∀ E ∈ S, ∃ y, GoodEl E (T ⊓ E) y ∧ y⁻¹ * z ∈ ⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E' := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, one_pow _, ?_, fun E hE => absurd hE (Finset.notMem_empty E)⟩
    exact Subgroup.one_mem _
  | insert E₀ S hE₀ ih =>
    have hE₀ℰ : E₀ ∈ ℰ := hS (by simp)
    have hSsub : (↑S : Set (Subgroup (MulAut V))) ⊆ ℰ := fun E hE => hS (by simp [hE])
    obtain ⟨z, hz3, hzmem, hzS⟩ := ih hSsub
    obtain ⟨y₀, hy₀⟩ := hgood E₀ hE₀ℰ
    have hzc : ∀ e ∈ E₀, z * e = e * z := fun e he =>
      commute_of_mem_iSup (𝒮 := (↑S : Set (Subgroup (MulAut V)))) (E₀ := E₀)
        (fun E hE x hx e he => hF.comm E (hSsub hE) E₀ hE₀ℰ (fun h => hE₀ (h ▸ hE)) x hx e he)
        hzmem he
    have hcom : Commute y₀ z := (hzc y₀ hy₀.mem).symm
    have hy₀3 : y₀ ^ 3 = 1 := by rw [← hy₀.order]; exact pow_orderOf_eq_one y₀
    refine ⟨y₀ * z, ?_, ?_, ?_⟩
    · rw [hcom.mul_pow, hy₀3, hz3, one_mul]
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.mem_iSup_of_mem E₀ (Subgroup.mem_iSup_of_mem (by simp) hy₀.mem)
      · refine (iSup₂_le fun E hE => le_iSup₂_of_le E ?_ le_rfl : (⨆ E ∈ (↑S : Set (Subgroup (MulAut V))), E) ≤
            ⨆ E ∈ (↑(insert E₀ S) : Set (Subgroup (MulAut V))), E) hzmem
        simp only [Finset.coe_insert, Set.mem_insert_iff]
        exact Or.inr hE
    · intro E hE
      rcases Finset.mem_insert.1 hE with rfl | hES
      · refine ⟨y₀, hy₀, ?_⟩
        rw [inv_mul_cancel_left]
        refine (iSup₂_le fun E' hE' => le_iSup₂_of_le E' ⟨hSsub hE', fun h => hE₀ (h ▸ hE')⟩ le_rfl :
          (⨆ E ∈ (↑S : Set (Subgroup (MulAut V))), E) ≤
            ⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E') hzmem
      · obtain ⟨y, hy, hu⟩ := hzS E hES
        refine ⟨y, hy, ?_⟩
        have hne : E₀ ≠ E := fun h => hE₀ (h ▸ hES)
        have hc : Commute y₀ y := hF.comm E₀ hE₀ℰ E (hSsub hES) hne y₀ hy₀.mem y hy.mem
        have e1 : y⁻¹ * (y₀ * z) = y₀ * (y⁻¹ * z) := by
          rw [← mul_assoc, ← hc.inv_right.eq, mul_assoc]
        rw [e1]
        exact Subgroup.mul_mem _
          (Subgroup.mem_iSup_of_mem E₀ (Subgroup.mem_iSup_of_mem ⟨hE₀ℰ, hne⟩ hy₀.mem)) hu

end Abstract

section Index

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem index_fixV_conjSub (g : MulAut V) (A : Subgroup (MulAut V)) :
    (fixV (conjSub g A)).index = (fixV A).index :=
  CFSG.Quasithin.ConjTransport.index_fixV_map_conj A g

theorem rkIdx_anti {U U' : Subgroup V} (h : U ≤ U') : rkIdx U' ≤ rkIdx U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rkIdx
  have hne : U.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  exact (padicValNat_dvd_iff_le hne).1
    (pow_padicValNat_dvd.trans (Subgroup.index_dvd_of_le h))

theorem rkIdx_inf_of_sup_eq_top {A B : Subgroup V} (h : A ⊔ B = ⊤) :
    rkIdx (A ⊓ B) = rkIdx A + rkIdx B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rkIdx
  have e : (A ⊓ B).index = A.index * B.index := by
    rw [Subgroup.index_inf]
    congr 1
    have h1 : A.relIndex (B ⊔ A) = A.relIndex B := Subgroup.relIndex_sup_right B A
    rw [sup_comm, h, Subgroup.relIndex_top_right] at h1
    exact h1.symm
  rw [e]
  exact padicValNat.mul Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

end Index

section Main

variable {V : Type} [CommGroup V] [Finite V]
  {P T M : Subgroup (MulAut V)} {ℰ : Set (Subgroup (MulAut V))}
  (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)
  (hsyl : ∀ E ∈ ℰ, ∀ B ∈ Hyp51.offSet P, B ≤ E → IsSylowOf 2 B E)
  {X : Subgroup (MulAut V)} (hXT : X ≤ T)
  (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
  (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X)
  (hXgen : X ≤ ⨆ B ∈ {B | B ∈ Hyp51.offSet P ∧ B ≤ X}, B)

include h hV hF hsyl hXT hTX hX₀ hXgen

theorem exists_gen_of_good (hgood : ∀ E ∈ ℰ, ∃ y, GoodEl E (T ⊓ E) y) :
    ∃ z : MulAut V, z ^ 3 = 1 ∧ z ∈ genD P ∧ genD P ≤ X ⊔ conjSub z X ∧
      ∀ K : Subgroup (MulAut V), K ≤ genD P → (∀ x ∈ P, orderOf x = 3 → x ∈ K) →
        2 * rkIdx (fixV X) ≤ rkIdx (fixV K) := by
  classical
  have hfin : ℰ.Finite := Set.toFinite ℰ
  obtain ⟨z, hz3, hzmem, hzS⟩ := exists_prod_good hF hgood hfin.toFinset
    (by rw [Set.Finite.coe_toFinset])
  rw [Set.Finite.coe_toFinset] at hzmem
  have hzS' : ∀ E ∈ ℰ, ∃ y, GoodEl E (T ⊓ E) y ∧
      y⁻¹ * z ∈ ⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E' :=
    fun E hE => hzS E (hfin.mem_toFinset.2 hE)
  have hzgen : z ∈ genD P := by rw [← hF.iSup_eq]; exact hzmem
  have hXle : X ≤ genD P := by
    rw [eq_iSup_inf h hV hF hsyl hXT hTX hX₀ hXgen, ← hF.iSup_eq]
    exact iSup₂_mono fun E _ => inf_le_right
  have comp : ∀ E ∈ ℰ, ∃ y, y ∈ E ∧ orderOf y = 3 ∧ E ≤ X ⊔ conjSub z X ∧
      (∀ w ∈ commV E, y w = w → w ∈ fixV E) ∧ commV E ≤ fixV X ⊔ fixV (conjSub z X) := by
    intro E hE
    obtain ⟨y, hy, hu⟩ := hzS' E hE
    set u := y⁻¹ * z with hu_def
    have hzu : z = y * u := by simp [hu_def]
    have hcomm : ∀ e ∈ E, u * e = e * u := fun e he =>
      commute_of_mem_iSup (𝒮 := {E' | E' ∈ ℰ ∧ E' ≠ E}) (E₀ := E)
        (fun E' hE' x hx e he => hF.comm E' hE'.1 E hE hE'.2 x hx e he) hu he
    have hfixu : ∀ w ∈ commV E, u w = w := fun w hw =>
      fix_of_mem_iSup (𝒮 := {E' | E' ∈ ℰ ∧ E' ≠ E})
        (fun E' hE' => hF.commV_le E hE E' hE'.1 (Ne.symm hE'.2) hw) hu
    have hconj : conjSub z (T ⊓ E) = conjSub y (T ⊓ E) := by
      rw [hzu, conjSub_mul, conjSub_eq_of_commute (fun r hr => hcomm r (inf_le_right (a := T) hr))]
    have hRX : T ⊓ E ≤ X := (inf_mem_offSet_and_le h hV hF hsyl hXT hTX hX₀ hE).2
    refine ⟨y, hy.mem, hy.order, ?_, hy.fix, ?_⟩
    · calc E ≤ T ⊓ E ⊔ conjSub y (T ⊓ E) := hy.gen
        _ = T ⊓ E ⊔ conjSub z (T ⊓ E) := by rw [hconj]
        _ ≤ X ⊔ conjSub z X := sup_le_sup hRX (conjSub_mono z hRX)
    · intro w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := hy.split w hw
      have haX : a ∈ fixV X := mem_fixV_X h hV hF hsyl hXT hTX hX₀ hXgen hE ha.1 ha.2
      have hbc : b ∈ fixV (conjSub z X) := by
        rw [mem_fixV_conjSub]
        have hb1 : y⁻¹ b ∈ fixV (T ⊓ E) := mem_fixV_conjSub.1 hb.2
        have hb2 : y⁻¹ b ∈ commV E := mem_commV_of_mem (E.inv_mem hy.mem) hb.1
        have hb3 : y⁻¹ b ∈ fixV X := mem_fixV_X h hV hF hsyl hXT hTX hX₀ hXgen hE hb2 hb1
        have hz' : z⁻¹ b = y⁻¹ b := by
          have h0 := hfixu _ hb2
          have h1 : u⁻¹ (y⁻¹ b) = y⁻¹ b := by
            calc u⁻¹ (y⁻¹ b) = u⁻¹ (u (y⁻¹ b)) := by rw [h0]
              _ = y⁻¹ b := by simp
          rw [hzu, mul_inv_rev]
          simpa [MulAut.mul_apply] using h1
        rw [hz']
        exact hb3
      exact Subgroup.mul_mem_sup haX hbc
  choose! y hy1 hy2 hgen hfix hsplit using comp
  have hconjle : conjSub z X ≤ genD P := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have := (genD P).mul_mem ((genD P).mul_mem hzgen (hXle hx)) ((genD P).inv_mem hzgen)
    simpa [mul_assoc] using this
  refine ⟨z, hz3, hzgen, ?_, ?_⟩
  · rw [← hF.iSup_eq]
    exact iSup₂_le fun E hE => hgen E hE
  intro K hKD hK3
  have hF3 : fixV (genD P) ≤ fixV X ⊓ fixV (conjSub z X) :=
    le_inf (fun v hv x hx => hv x (hXle hx)) (fun v hv x hx => hv x (hconjle hx))
  have hsup : fixV X ⊔ fixV (conjSub z X) = ⊤ := by
    rw [eq_top_iff, ← hF.decomp]
    exact sup_le (hF3.trans (inf_le_left.trans le_sup_left))
      (iSup₂_le fun E hE => hsplit E hE)
  have hKfix : ∀ S : Finset (Subgroup (MulAut V)), (↑S : Set (Subgroup (MulAut V))) ⊆ ℰ →
      ∀ v ∈ fixV (genD P) ⊔ ⨆ E ∈ (↑S : Set (Subgroup (MulAut V))), commV E,
        v ∈ fixV K → v ∈ fixV (genD P) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ v hv _
      simpa using hv
    | insert E₀ S hE₀ ih =>
      intro hS v hv hvK
      have hE₀ℰ : E₀ ∈ ℰ := hS (by simp)
      have hSsub : (↑S : Set (Subgroup (MulAut V))) ⊆ ℰ := fun E hE => hS (by simp [hE])
      have hsplit' : fixV (genD P) ⊔ ⨆ E ∈ (↑(insert E₀ S) : Set (Subgroup (MulAut V))), commV E =
          (fixV (genD P) ⊔ ⨆ E ∈ (↑S : Set (Subgroup (MulAut V))), commV E) ⊔ commV E₀ := by
        rw [Finset.coe_insert, iSup_insert, sup_comm (commV E₀), ← sup_assoc]
      rw [hsplit'] at hv
      obtain ⟨c', hc', w₀, hw₀, rfl⟩ := Subgroup.mem_sup.1 hv
      have hE₀gen : E₀ ≤ genD P := by
        rw [← hF.iSup_eq]; exact le_iSup₂_of_le E₀ hE₀ℰ le_rfl
      have hy₀K : y E₀ ∈ K := hK3 _ (hF.le_P h hV hE₀ℰ (hy1 E₀ hE₀ℰ)) (hy2 E₀ hE₀ℰ)
      have hc'E₀ : c' ∈ fixV E₀ := by
        have : fixV (genD P) ⊔ ⨆ E ∈ (↑S : Set (Subgroup (MulAut V))), commV E ≤ fixV E₀ := by
          refine sup_le (fun v hv x hx => hv x (hE₀gen hx)) (iSup₂_le fun E hE => ?_)
          exact hF.commV_le E (hSsub hE) E₀ hE₀ℰ (fun h => hE₀ (h ▸ hE))
        exact this hc'
      have hyc : y E₀ c' = c' := hc'E₀ _ (hy1 E₀ hE₀ℰ)
      have hyv : y E₀ (c' * w₀) = c' * w₀ := hvK _ hy₀K
      have hw₀fix : y E₀ w₀ = w₀ := by
        rw [map_mul, hyc] at hyv
        exact mul_left_cancel hyv
      have hw₀E₀ : w₀ ∈ fixV E₀ := hfix E₀ hE₀ℰ w₀ hw₀ hw₀fix
      have hw₀gen : w₀ ∈ fixV (genD P) :=
        commV_inf_fixV_le_fixV_genD hF hE₀ℰ ⟨hw₀, hw₀E₀⟩
      have hw₀K : w₀ ∈ fixV K := fun x hx => hw₀gen x (hKD hx)
      have hc'K : c' ∈ fixV K := by
        have := (fixV K).mul_mem hvK ((fixV K).inv_mem hw₀K)
        simpa using this
      exact (fixV (genD P)).mul_mem (ih hSsub c' hc' hc'K) hw₀gen
  have h1 : fixV K ≤ fixV (genD P) := by
    intro v hv
    refine hKfix hfin.toFinset (by rw [Set.Finite.coe_toFinset]) v ?_ hv
    rw [Set.Finite.coe_toFinset, hF.decomp]
    exact Subgroup.mem_top v
  have e : rkIdx (fixV (conjSub z X)) = rkIdx (fixV X) := by
    unfold rkIdx
    rw [index_fixV_conjSub]
  calc 2 * rkIdx (fixV X) = rkIdx (fixV X) + rkIdx (fixV (conjSub z X)) := by rw [e]; ring
    _ = rkIdx (fixV X ⊓ fixV (conjSub z X)) := (rkIdx_inf_of_sup_eq_top hsup).symm
    _ ≤ rkIdx (fixV K) := rkIdx_anti (h1.trans hF3)

end Main

end CFSG.AGLEmbeddingD2.Tits.E23
