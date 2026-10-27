module

public import CFSG.Sporadic.Schreier.Co1NormalThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Tree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Bound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveBAbs
public import Certificates.Certificate17325
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.Co1OuterImage

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Dickson.I271.TabCo1FiveB CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271

section Tree

theorem exists_mem_closure_list_of_lt {Gs : List Native.Rows} {gens : List GL24}
    (hG : List.Forall₂ MRep Gs gens) {cap : ℕ}
    (h : gtOK Gs.toArray (gtBFS Gs.toArray cap) = true) {i : ℕ}
    (hi : i < (gtBFS Gs.toArray cap).pts.size) :
    ∃ y ∈ Subgroup.closure {g | g ∈ gens}, MRep (gtBFS Gs.toArray cap).pts[i]! y := by
  obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq valHom valHom_injective h
    (fun l => gens.getD l 1) (rep_arr hG)
  have e : Subgroup.closure ((fun l => gens.getD l 1) '' {l | l < Gs.toArray.size}) =
      Subgroup.closure {g | g ∈ gens} := by
    rw [size_eq_of_rep hG, image_getD_lt]
  have hmem : f i ∈ (Subgroup.closure ((fun l => gens.getD l 1) ''
      {l | l < Gs.toArray.size}) : Set GL24) := by
    rw [heq]
    exact ⟨i, hi, rfl⟩
  rw [e] at hmem
  exact ⟨f i, hmem, (hf i hi).symm⟩

theorem commRows_sound {Gs : List Native.Rows} {gens : List GL24}
    (hG : List.Forall₂ MRep Gs gens) {cap : ℕ}
    (h : gtOK Gs.toArray (gtBFS Gs.toArray cap) = true)
    (hinv : invOK (gtBFS Gs.toArray cap).pts = true) {target : Native.Rows}
    (hc : commRows (gtBFS Gs.toArray cap).pts target = true) {t : GL24} (ht : MRep target t) :
    ∃ u ∈ Subgroup.closure {g | g ∈ gens}, ∃ v ∈ Subgroup.closure {g | g ∈ gens},
      t = u * v * u⁻¹ * v⁻¹ := by
  simp only [commRows, List.any_eq_true, List.mem_range, beq_iff_eq] at hc
  obtain ⟨i, hi, j, hj, hij⟩ := hc
  simp only [invOK, List.all_eq_true, List.mem_range, beq_iff_eq] at hinv
  obtain ⟨u, hu, ru⟩ := exists_mem_closure_list_of_lt hG h hi
  obtain ⟨v, hv, rv⟩ := exists_mem_closure_list_of_lt hG h hj
  have rui : MRep (Native.inv (gtBFS Gs.toArray cap).pts[i]!) u⁻¹ := ru.inv (hinv i hi)
  have rvi : MRep (Native.inv (gtBFS Gs.toArray cap).pts[j]!) v⁻¹ := rv.inv (hinv j hj)
  have := (ru.mul rv).mul (rui.mul rvi)
  rw [hij] at this
  refine ⟨u, hu, v, hv, ?_⟩
  rw [mul_assoc (u * v) u⁻¹ v⁻¹]
  exact ht.eq this

end Tree

section Comm

theorem comm_of_centralizer_five {G : Type} [Group G] {a b c d e : G} :
    ∀ g ∈ Subgroup.centralizer ({a, b, c, d, e} : Set G), ∀ β ∈ [a, b, c, d, e],
      g * β = β * g := by
  intro g hg β hβ
  have : β ∈ ({a, b, c, d, e} : Set G) := by simpa using hβ
  exact (Subgroup.mem_centralizer_iff.1 hg β this).symm

end Comm

section PtBound


theorem ptB_bound {kR x1R y1R tR tI : Native.Rows} {k x1 y1 t : GL24} (rk : MRep kR k)
    (rx : MRep x1R x1) (ry : MRep y1R y1) (rt : MRep tR t) (rtI : MRep tI t⁻¹) {base : List ℕ}
    {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (hb : boundOK (colsOf (ptRowsB kR x1R y1R tR tI)) 5 base conds cnts span comb = true) :
    Nat.card ↥(Subgroup.centralizer ({k, x1, y1, t * x1 * t⁻¹, t * y1 * t⁻¹} : Set GL24) ⊓
      GA) ≤ cnts.prod := by
  have hr : List.Forall₂ MRep (ptRowsB kR x1R y1R tR tI)
      [k, x1, y1, t * x1 * t⁻¹, t * y1 * t⁻¹] := by
    unfold ptRowsB
    exact List.Forall₂.cons rk (List.Forall₂.cons rx (List.Forall₂.cons ry
      (List.Forall₂.cons ((rt.mul rx).mul rtI) (List.Forall₂.cons ((rt.mul ry).mul rtI)
        List.Forall₂.nil))))
  have hL := @comm_of_centralizer_five GL24 _ k x1 y1 (t * x1 * t⁻¹) (t * y1 * t⁻¹)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({k, x1, y1, t * x1 * t⁻¹, t * y1 * t⁻¹} : Set GL24) ⊓
      GA, ∀ β ∈ [k, x1, y1, t * x1 * t⁻¹, t * y1 * t⁻¹], g * β = β * g :=
    fun g hg => hL g (Subgroup.mem_inf.1 hg).1
  exact card_le_of_listBound hr inf_le_right hcomm (by simp [ptRowsB]) hb

end PtBound

section Data


theorem fiveB_data :
    ∃ k x₁ y₁ τ : GL24, MRep repD1 k ∧ k ∈ GA ∧ x₁ ∈ GA ∧ y₁ ∈ GA ∧ τ ∈ GA ∧ k ^ 5 = 1 ∧
      k ≠ 1 ∧ k * x₁ = x₁ * k ∧ k * y₁ = y₁ * k ∧ k * τ = τ * k ∧ τ * τ = 1 ∧
      x₁ * (τ * x₁ * τ⁻¹) = (τ * x₁ * τ⁻¹) * x₁ ∧
      x₁ * (τ * y₁ * τ⁻¹) = (τ * y₁ * τ⁻¹) * x₁ ∧
      y₁ * (τ * x₁ * τ⁻¹) = (τ * x₁ * τ⁻¹) * y₁ ∧
      y₁ * (τ * y₁ * τ⁻¹) = (τ * y₁ * τ⁻¹) * y₁ ∧
      Nat.card ↥(Subgroup.closure ({x₁, y₁} : Set GL24)) = 60 ∧
      (∃ u ∈ Subgroup.closure ({x₁, y₁} : Set GL24), ∃ v ∈ Subgroup.closure ({x₁, y₁} : Set GL24),
        x₁ = u * v * u⁻¹ * v⁻¹) ∧
      (∃ u ∈ Subgroup.closure ({x₁, y₁} : Set GL24), ∃ v ∈ Subgroup.closure ({x₁, y₁} : Set GL24),
        y₁ = u * v * u⁻¹ * v⁻¹) ∧
      Nat.card ↥(Subgroup.closure ({k, x₁, y₁, τ} : Set GL24)) = 36000 ∧
      Nat.card ↥(Subgroup.centralizer ({k} : Set GL24) ⊓ GA) ≤ 36000 ∧
      Nat.card ↥(Subgroup.centralizer ({k, x₁, y₁, τ * x₁ * τ⁻¹, τ * y₁ * τ⁻¹} : Set GL24) ⊓
        GA) ≤ 5 := by
  have h := (Certificates.certificate17325 : fiveBCheck () = true)
  simp only [fiveBCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨hD, hwk, hw1, hkrep, hk5, hk1, hkx, hky, hkt, htt, hc1, hc2, hc3, hc4, hLok, hLsz,
    hinv, hcx, hcy, hEok, hEsz, hb1, hcnt1, hb2, hcnt2⟩ := h
  have rk := rep_nd (ext := ext) hD 88
  have rx := rep_nd (ext := ext) hD 89
  have ry := rep_nd (ext := ext) hD 90
  have rt := rep_nd (ext := ext) hD 91
  have rtI := rep_ndI (ext := ext) hD 91
  have rx2 := (rt.mul rx).mul rtI
  have ry2 := (rt.mul ry).mul rtI
  have hGL := List.Forall₂.cons rx (List.Forall₂.cons ry List.Forall₂.nil)
  have hGE := List.Forall₂.cons rk (List.Forall₂.cons rx (List.Forall₂.cons ry
    (List.Forall₂.cons rt List.Forall₂.nil)))
  have cardL := card_closure_list hGL hLok
  have cardE := card_closure_list hGE hEok
  rw [hLsz, setOf_mem_pair] at cardL
  rw [hEsz, setOf_mem_four] at cardE
  have hX := commRows_sound hGL hLok hinv hcx rx
  have hY := commRows_sound hGL hLok hinv hcy ry
  rw [setOf_mem_pair] at hX hY
  refine ⟨kG ext 88, kG ext 89, kG ext 90, kG ext 91, hkrep ▸ rk, kG_mem ext 88, kG_mem ext 89,
    kG_mem ext 90, kG_mem ext 91, eq_one_of_rep (rk.pow 5) hk5, ne_one_of_rep rk hwk hw1 hk1,
    (rk.mul rx).eq (by rw [hkx]; exact rx.mul rk), (rk.mul ry).eq (by rw [hky]; exact ry.mul rk),
    (rk.mul rt).eq (by rw [hkt]; exact rt.mul rk), eq_one_of_rep (rt.mul rt) htt,
    (rx.mul rx2).eq (by rw [hc1]; exact rx2.mul rx),
    (rx.mul ry2).eq (by rw [hc2]; exact ry2.mul rx),
    (ry.mul rx2).eq (by rw [hc3]; exact rx2.mul ry),
    (ry.mul ry2).eq (by rw [hc4]; exact ry2.mul ry),
    cardL, hX, hY, cardE, ?_, ?_⟩
  · exact (card_centralizer_le_of_powBound rk hb1).trans hcnt1
  · exact (ptB_bound rk rx ry rt rtI hb2).trans hcnt2

end Data

section Good

theorem goodSpor_alt5 : GoodSpor 5 [.J2] ↥(alternatingGroup (Fin 5)) :=
  Or.inl (Or.inr ⟨5, le_rfl, by norm_num, dvd_rfl, ⟨MulEquiv.refl _⟩⟩)

theorem card_alt5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

end Good

section RkJ2


theorem rkSpor_J2_of_card_lt {T : Type} [Group T] [Finite T] (h : Nat.card T < 604800) :
    RkSpor 5 [.J2] T := by
  rintro (⟨h3, -⟩ | ⟨S, hS, ⟨f⟩⟩)
  · norm_num at h3
  · simp only [List.mem_singleton] at hS
    subst hS
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
    have b₀ : NativeSporadic.J2 ≃* (TauCeti.CFSGIndex.sporadic .J2).Group := b
    have h1 : Nat.card (T ⧸ Subgroup.center T) = 604800 := by
      rw [Nat.card_congr (f.trans b₀.symm).toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    have h2 : Nat.card (T ⧸ Subgroup.center T) ≤ Nat.card T :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center T))
    omega

theorem rkSpor_alt5 : RkSpor 5 [.J2] ↥(alternatingGroup (Fin 5)) :=
  rkSpor_J2_of_card_lt (by rw [card_alt5]; norm_num)

end RkJ2

section Final


theorem tabCo1_fiveB (x : ↥GA) (hx : MRep repD1 (x : GL24)) :
    MultiShapeAt 5 (GoodSpor 5 [.J2]) (RkSpor 5 [.J2]) x := by
  haveI : Finite ↥GA := finite_GA
  obtain ⟨k, x₁, y₁, τ, hk, -, hx₁, hy₁, hτ, hk5, hk1, hkx, hky, hkt, htt, hc1, hc2, hc3, hc4,
    hL, hX, hY, hE, hCbd, hpt⟩ := fiveB_data
  exact multiShapeAt_A5A5_of_data (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
    (fun _ _ _ _ e h => RkSpor.of_equiv e h) goodSpor_alt5 rkSpor_alt5 GA x k x₁ y₁ τ (hx.eq hk)
    hk5 hk1 hx₁ hy₁ hτ hkx hky hkt htt hc1 hc2 hc3 hc4 hL hX hY hE hCbd hpt

end Final

section Order


theorem card_cent_fiveB_le (x : ↥GA) (hx : MRep repD1 (x : GL24)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥GA)) ≤ 36000 := by
  obtain ⟨k, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCbd, -⟩ :=
    fiveB_data
  have hxk : (x : GL24) = k := hx.eq hk
  rw [← Subgroup.card_map_of_injective (f := GA.subtype) GA.subtype_injective,
    map_centralizer_subtype' GA x, hxk]
  exact hCbd

end Order

end CFSG.HardMathSupport.Dickson.I271.TabCo1
