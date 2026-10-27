module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.Sporadic.FischerOddCore.Fi23Aut

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi23

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
    CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] noncomputable def fi23Hom : J →* Equiv.Perm (Fin 31671) :=
  MulAction.toPermHom J (Fin 31671)

theorem fi23Hom_apply (g : J) (i : Fin 31671) :
    fi23Hom g i = g • i := rfl

theorem fi23Hom_injective : Function.Injective fi23Hom := by
  intro g h hgh
  apply eq_of_smul_eq_smul (α := Fin 31671)
  intro i
  exact congrArg (fun f : Equiv.Perm (Fin 31671) => f i) hgh

@[expose] noncomputable def fi23P :
    Subgroup (Equiv.Perm (Fin 31671)) := fi23Hom.range

@[expose] noncomputable def fi23JEquiv : J ≃* ↥fi23P :=
  MonoidHom.ofInjective fi23Hom_injective

@[expose] noncomputable def fi23PermEquiv :
    Blueprint.NativeSporadic.Fi23 ≃* ↥fi23P :=
  fi23EquivJ.trans fi23JEquiv

theorem card_fi23P : Nat.card ↥fi23P = 4089470473293004800 := by
  rw [← Nat.card_congr fi23JEquiv.toEquiv, card_J]

theorem fi23P_eq_closure :
    fi23P = closure {fi23Hom a, fi23Hom b} := by
  rw [fi23P, MonoidHom.range_eq_map, ← closure_ab, MonoidHom.map_closure, Set.image_pair]

theorem rep_of_table {T : Table} {g : J}
    (hT : CFSG.Sporadic.Th.Rep 31671 T g) (hs : T.size = 31671) :
    CFSG.Monster.B.Co2.Rep 31671 (T.map UInt32.toNat) (fi23Hom g) := by
  intro x
  rw [getElem!_pos _ x.val (by simp [hs]), Array.getElem_map, fi23Hom_apply]
  have h := hT x.val x.2
  rw [idx_of_lt g x.2] at h
  rw [← h, ap, getElem!_pos T x.val (by rw [hs]; exact x.2)]

theorem rep_fi23GenA :
    CFSG.Monster.B.Co2.Rep 31671 fi23Gens[0]! (fi23Hom a) := by
  have h := rep_of_table rep_alpha actionFacts.alpha_size
  exact h

theorem rep_fi23GenB :
    CFSG.Monster.B.Co2.Rep 31671 fi23Gens[1]! (fi23Hom b) := by
  have h := rep_of_table rep_beta actionFacts.beta_size
  exact h

theorem fi23P_eq_closure_permsA :
    fi23P = closure (CFSG.RankThree.Native.permsA 31671 fi23Gens) := by
  rw [fi23P_eq_closure]
  congr 1
  ext g
  simp only [CFSG.RankThree.Native.permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have h0 := CFSG.RankThree.Native.permOfArr_eq_of_rep rep_fi23GenA
  have h1 := CFSG.RankThree.Native.permOfArr_eq_of_rep rep_fi23GenB
  have hsz : fi23Gens.size = 2 := rfl
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [hsz]; norm_num, h0⟩
    · exact ⟨1, by rw [hsz]; norm_num, h1⟩
  · rintro ⟨k, hk, rfl⟩
    rw [hsz] at hk
    interval_cases k
    · exact Or.inl h0
    · exact Or.inr h1

theorem fi23P_center_eq_bot : center ↥fi23P = ⊥ := by
  have h : center J = ⊥ := center_J
  rw [eq_bot_iff] at h ⊢
  intro x hx
  obtain ⟨g, rfl⟩ := fi23JEquiv.surjective x
  have hg : g ∈ center J := by
    rw [mem_center_iff] at hx ⊢
    intro h'
    apply fi23JEquiv.injective
    rw [map_mul, map_mul]
    exact hx _
  rw [h hg, map_one]
  exact one_mem _

theorem forall_inner_of_mulEquiv {K H : Type*} [Group K] [Group H] (e : K ≃* H)
    (h : ∀ α : MulAut H, ∃ g : H, α = MulAut.conj g) :
    ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g := by
  intro α
  obtain ⟨g, hg⟩ := h ((e.symm.trans α).trans e)
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun β : MulAut H => β (e x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem fi23P_allInner :
    ∀ α : MulAut ↥fi23P, ∃ g : ↥fi23P, α = MulAut.conj g :=
  @forall_inner_of_mulEquiv ↥fi23P Blueprint.NativeSporadic.Fi23 _ Units.instGroup
    fi23PermEquiv.symm CFSG.Sporadic.FischerOddCore.CTUC_Fi23_Schreier.2.1

theorem fi23AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Fi23) ↥fi23P (fi23P.subgroupOf fi23P) :=
  autModel_of_allInner fi23PermEquiv.symm fi23P_center_eq_bot fi23P_allInner

theorem fixP_fi23Hom (g : J) :
    fixP (fi23Hom g) = Nat.card {x : D23 // g * x * g⁻¹ = x} := by
  rw [fixP, ← Nat.card_eq_fintype_card]
  let e : Fin 31671 ≃ D23 := ptEquiv.trans (Equiv.subtypeEquivRight fun x => by
    rw [ConjAct.mem_orbit_conjAct]
    exact ⟨fun h => h.symm, fun h => h.symm⟩)
  refine Nat.card_congr (Equiv.subtypeEquiv e fun i => ?_)
  rw [fi23Hom_apply]
  have h := smul_eq_iff g i i
  change g • i = i ↔ g * ((ptEquiv i : J)) * g⁻¹ = (ptEquiv i : J)
  rw [h, ptEquiv_apply]

@[expose] noncomputable def fi23Reps :
    List (Equiv.Perm (Fin 31671)) := [fi23Hom d, fi23Hom (d * d1), fi23Hom t2]

theorem fixP_fi23Reps :
    fi23Reps.map fixP = [3511, 695, 183] := by
  simp only [fi23Reps, List.map_cons, List.map_nil, fixP_fi23Hom, card_fixed_d,
    card_fixed_d_mul_d1, card_fixed_t2]

theorem fi23_conj_rep
    {g : Equiv.Perm (Fin 31671)} (hg : g ∈ fi23P)
    (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) : ∃ c ∈ fi23Reps, ∃ w ∈ fi23P, w * g * w⁻¹ = c := by
  obtain ⟨j, rfl⟩ := hg
  have hj2 : j ^ 2 = 1 := fi23Hom_injective (by rw [map_pow, hg2, map_one])
  have hj1 : j ≠ 1 := fun h => hg1 (by rw [h, map_one])
  have key : ∀ c : J, IsConj c j → ∃ w ∈ fi23P, w * fi23Hom j * w⁻¹ = fi23Hom c := by
    intro c hc
    obtain ⟨w, hw⟩ := isConj_iff.mp hc.symm
    exact ⟨fi23Hom w, ⟨w, rfl⟩, by rw [← map_inv, ← map_mul, ← map_mul, hw]⟩
  rcases involution_cover j hj2 hj1 with h | h | h
  · exact ⟨_, by simp [fi23Reps], key _ h⟩
  · exact ⟨_, by simp [fi23Reps], key _ h⟩
  · exact ⟨_, by simp [fi23Reps], key _ h⟩

theorem fi23_conj_of_fix
    {g x : Equiv.Perm (Fin 31671)} (hg : g ∈ fi23P)
    (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) (hx : x ∈ fi23P) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hgx : fixP g = fixP x) : ∃ w ∈ fi23P, w * g * w⁻¹ = x := by
  obtain ⟨c, hc, w, hw, hwc⟩ := fi23_conj_rep hg hg2 hg1
  obtain ⟨c', hc', w', hw', hwc'⟩ := fi23_conj_rep hx hx2 hx1
  have hcc : c = c' := by
    have h1 : fixP c = fixP c' := by rw [← hwc, ← hwc', fixP_conj, fixP_conj, hgx]
    have hf := fixP_fi23Reps
    simp only [fi23Reps, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hf
    obtain ⟨h0, h1', h2⟩ := hf
    simp only [fi23Reps, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rcases hc with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;>
      first | (exfalso; omega) | rfl
  refine ⟨w'⁻¹ * w, fi23P.mul_mem (fi23P.inv_mem hw') hw, ?_⟩
  rw [hcc] at hwc
  calc w'⁻¹ * w * g * (w'⁻¹ * w)⁻¹ = w'⁻¹ * (w * g * w⁻¹) * w' := by group
    _ = w'⁻¹ * (w' * x * w'⁻¹) * w' := by rw [hwc, hwc']
    _ = x := by group

end CFSG.ComponentClassification.RankTwoSporadic.Fi23
