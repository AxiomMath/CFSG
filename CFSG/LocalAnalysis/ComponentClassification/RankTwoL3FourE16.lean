module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypII

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.PSL3Four
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem exists_mem_not_mem_finset {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (F : Finset G) (h : F.card < Nat.card E) : ∃ x ∈ E, x ∉ F := by
  by_contra hcon
  push Not at hcon
  have hsub : (E : Set G) ⊆ (F : Set G) := fun x hx => hcon x hx
  have h1 : Nat.card E ≤ F.card := by
    have hE : Nat.card E = (E : Set G).ncard := (Nat.card_coe_set_eq _).symm
    rw [hE, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet F)
  omega

theorem isInvA_of_rep {a : Array ℕ} {u : Equiv.Perm (Fin 42)} (ha : Rep 42 a u)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) : isInvA a = true := by
  rw [isInvA, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨(eqA_iff (rep_compA ha ha) rep_idA).2 hu2, ?_⟩
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hu1 ((eqA_iff ha rep_idA).1 h)

theorem le_of_e16OKW {inS : Array ℕ → Bool}
    (hS : ∀ {a : Array ℕ} {g : Equiv.Perm (Fin 42)}, Rep 42 a g → inS a = true → g ∈ S)
    {I : List (Array ℕ)}
    (h : e16OKW inS I = true) {E : Subgroup (Equiv.Perm (Fin 42))} (hE : IsElemAbelian 2 E)
    (hE16 : 16 ≤ Nat.card E)
    (hI : ∀ x ∈ E, x ≠ 1 → ∃ a ∈ I, Rep 42 a x) : E ≤ S := by
  by_contra hES
  obtain ⟨u, huE, huS⟩ : ∃ u ∈ E, u ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hES hcon
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := hE.2 x hx
    rwa [sq] at this
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hu1 : u ≠ 1 := fun h => huS (h ▸ one_mem S)
  obtain ⟨au, hauI, hau⟩ := hI u huE hu1
  have hfu := (List.all_eq_true.mp h) au hauI
  rw [Bool.or_eq_true] at hfu
  rcases hfu with hin | hfu
  · exact huS (hS hau hin)
  obtain ⟨v, hvE, hvF⟩ := exists_mem_not_mem_finset E [1, u].toFinset
    (lt_of_le_of_lt (List.toFinset_card_le _) (by simp; omega))
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at hvF
  obtain ⟨hv1, hvu⟩ := hvF
  obtain ⟨av, havI, hav⟩ := hI v hvE hv1
  have hfv := (List.all_eq_true.mp hfu) av havI
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hfv
  rcases hfv with (hc | hc) | hfv
  · rw [(commA_iff hau hav).2 (hcomm u huE v hvE)] at hc
    exact Bool.noConfusion hc
  · exact hvu ((eqA_iff hav hau).1 hc)
  obtain ⟨w, hwE, hwF⟩ := exists_mem_not_mem_finset E [1, u, v, u * v].toFinset
    (lt_of_le_of_lt (List.toFinset_card_le _) (by simp; omega))
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at hwF
  obtain ⟨hw1, hwu, hwv, hwuv⟩ := hwF
  obtain ⟨aw, hawI, haw⟩ := hI w hwE hw1
  have hfw := (List.all_eq_true.mp hfv) aw hawI
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hfw
  rcases hfw with ((((hc | hc) | hc) | hc) | hc) | hfw
  · rw [(commA_iff hau haw).2 (hcomm u huE w hwE)] at hc
    exact Bool.noConfusion hc
  · rw [(commA_iff hav haw).2 (hcomm v hvE w hwE)] at hc
    exact Bool.noConfusion hc
  · exact hwu ((eqA_iff haw hau).1 hc)
  · exact hwv ((eqA_iff haw hav).1 hc)
  · exact hwuv ((eqA_iff haw (rep_compA hau hav)).1 hc)
  obtain ⟨t, htE, htF⟩ := exists_mem_not_mem_finset E
    [1, u, v, w, u * v, u * w, v * w, u * (v * w)].toFinset
    (lt_of_le_of_lt (List.toFinset_card_le _) (by simp; omega))
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at htF
  obtain ⟨ht1, htu, htv, htw, htuv, htuw, htvw, htuvw⟩ := htF
  obtain ⟨at', hatI, hat⟩ := hI t htE ht1
  have hft := (List.all_eq_true.mp hfw) at' hatI
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hft
  rcases hft with ((hc | hc) | hc) | hspan
  · rw [(commA_iff hat hau).2 (hcomm t htE u huE)] at hc
    exact Bool.noConfusion hc
  · rw [(commA_iff hat hav).2 (hcomm t htE v hvE)] at hc
    exact Bool.noConfusion hc
  · rw [(commA_iff hat haw).2 (hcomm t htE w hwE)] at hc
    exact Bool.noConfusion hc
  · rw [inSpan3, List.any_eq_true] at hspan
    obtain ⟨b, hb, hbt⟩ := hspan
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ht1 ((eqA_iff hat rep_idA).1 hbt)
    · exact htu ((eqA_iff hat hau).1 hbt)
    · exact htv ((eqA_iff hat hav).1 hbt)
    · exact htw ((eqA_iff hat haw).1 hbt)
    · exact htuv ((eqA_iff hat (rep_compA hau hav)).1 hbt)
    · exact htuw ((eqA_iff hat (rep_compA hau haw)).1 hbt)
    · exact htvw ((eqA_iff hat (rep_compA hav haw)).1 hbt)
    · exact htuvw ((eqA_iff hat (rep_compA hau (rep_compA hav haw))).1 hbt)

theorem l34_le_of_sixteen_le {d : L34E16Cert}
    (h : l34CheckWE16 d = true) {E : Subgroup ↥R} (hE : IsElemAbelian 2 E)
    (hE16 : 16 ≤ Nat.card E) : E ≤ S.subgroupOf R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [l34CheckWE16, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hch, hslp⟩, hT⟩, hgen⟩, hsize⟩, he16⟩ := h
  replace hT := enumOK_of_enumOKK hT
  set sGens := d.sG.map (CFSG.KC.Census.unpackP 42 6)
  set cT := d.cS.toMain 42 6
  set T' := closure (permsA 42 sGens)
  have hT'le : T' ≤ R.subtype.range := by
    rw [closure_le, range_subtype]
    rintro _ ⟨j, hj, rfl⟩
    have hr := rep_of_validA (enumOK_gens_valid hT hj)
    have h1 := allLt_spec hgen hj
    rw [inRegsL, List.any_eq_true] at h1
    obtain ⟨r, hr', he⟩ := h1
    obtain ⟨g, hg, hrep⟩ := rep_slpRegs hslp r (List.mem_range.mp hr')
    change permOfArr 42 sGens[j]! ∈ R
    rw [eq_of_eqA hr hrep he, ← closure_permsA_l34GensR]
    exact hg
  obtain ⟨hTmem, hTcard, hTval⟩ := enumOK_spec l34PS_lt hT
  set Tc := T'.comap R.subtype
  have hTmap : Tc.map R.subtype = T' := map_comap_eq_self hT'le
  have hTcardc : Nat.card Tc = 2 ^ 8 := by
    rw [← card_map_of_injective R.subtype_injective, hTmap, hTcard, hsize]
    norm_num
  have hTsyl : IsSylowOf 2 Tc ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hTcardc, fun h2 => ?_⟩
    have h1 := Tc.card_mul_index
    rw [hTcardc, card_R] at h1
    have hidx : Tc.index = 945 := by omega
    rw [hidx] at h2
    omega
  obtain ⟨m, -, hm⟩ := exists_conj_le_of_isSylowOf hTsyl (isPGroup_of_isElemAbelian hE) le_top
  set σ := MulAut.conj m⁻¹
  have hle : E.map σ.toMonoidHom ≤ Tc := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [σ, MulAut.conj_apply] using hm x hx
  set E' := (E.map σ.toMonoidHom).map R.subtype
  have hE' : IsElemAbelian 2 E' := isElemAbelian_map (isElemAbelian_map hE _) _
  have hE'16 : 16 ≤ Nat.card E' := by
    rw [card_map_of_injective R.subtype_injective,
      card_map_of_injective (MulAut.conj m⁻¹).injective]
    exact hE16
  have hE'T : E' ≤ T' := hTmap ▸ map_mono hle
  have hE'S : E' ≤ S := by
    refine le_of_e16OKW (fun ha hin => (l34InSW_iff hch ha).1 hin) he16 hE' hE'16
      fun x hx hx1 => ?_
    obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep l34PS_lt hT (hE'T hx)
    refine ⟨cT.pts[i]!, ?_, hrep⟩
    rw [List.mem_filter]
    refine ⟨?_, isInvA_of_rep hrep (by have := hE'.2 x hx; rwa [sq] at this) hx1⟩
    rw [getElem!_pos cT.pts i hi]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hi)
  intro x hx
  have hx' : (σ x : ↥R) ∈ S.subgroupOf R := by
    rw [mem_subgroupOf]
    exact hE'S ⟨σ x, ⟨x, hx, rfl⟩, rfl⟩
  have := S_normal.conj_mem _ hx' m
  simpa [σ, MulAut.conj_apply, mul_assoc] using this

end CFSG.ComponentClassification.RankTwoL3Four.HypII
