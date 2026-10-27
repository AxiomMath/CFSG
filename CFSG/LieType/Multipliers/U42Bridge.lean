module

public import CFSG.LieType.Multipliers.U42Data
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import Certificates.Certificate10011
public import CFSG.LieType.Multipliers.CoverBounds
public meta import CFSG.LieType.Multipliers.U42Data
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Assembly.Subnormal
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LieType.Multipliers.U42

open CFSG.GH74.Exceptional CFSG.Fischer.Classification.Beta CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.CosetTable

noncomputable def psi : PSp43 →* Equiv.Perm (Fin 45) :=
  rho43.comp psp43EquivU2.toMonoidHom

theorem psi_injective : Function.Injective psi :=
  rho43_injective.comp psp43EquivU2.injective

theorem psi_apply (g : PSp43) (j : Fin 45) : psi g j = s43Idx (g * s43 j * g⁻¹) := by
  have : psi g =
      sigma43 (((MulEquiv.subgroupCongr Y43_eq_top).trans Subgroup.topEquiv).symm g) := by
    show rho43 (psp43EquivU2 g) = _
    rw [psp43EquivU2, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
    rfl
  rw [this, sigma43_apply]
  rfl

theorem psi_s43 (i j : Fin 45) : psi (s43 i) j = tauFun i j := by
  rw [psi_apply, s43_inv, s43_tau, s43Idx_s43]
  rfl

theorem conj_s43 (g : PSp43) (j : Fin 45) : g * s43 j * g⁻¹ = s43 (psi g j) := by
  have hg : g ∈ Y43 := by rw [Y43_eq_top]; exact Subgroup.mem_top g
  rw [psi_apply, s43_s43Idx (conj_mem_range hg j).1]

theorem card_PSp43 : Nat.card PSp43 = 25920 := by
  rw [Nat.card_congr psp43EquivU2.toEquiv]
  exact card_U2_four

@[expose] noncomputable def xElt : PSp43 := s43 0

@[expose] noncomputable def yElt : PSp43 := (bIdx.map s43).prod

private theorem prod_inv (l : List (Fin 45)) :
    ((l.map s43).prod)⁻¹ = (l.reverse.map s43).prod := by
  rw [List.prod_inv_reverse, List.map_map, List.map_reverse]
  simp only [Function.comp_def, s43_inv]

private theorem psi_prod (l : List (Fin 45)) (j : Fin 45) :
    psi (l.map s43).prod j = seqFun l j := by
  induction l with
  | nil => simp [seqFun]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Equiv.Perm.mul_apply, ih, psi_s43]
    rfl

private theorem psi_letter (l : ℕ × Bool) (j : Fin 45) :
    psi (if l.2 then img2 xElt yElt l.1 else (img2 xElt yElt l.1)⁻¹) j = letterFun l j := by
  obtain ⟨i, s⟩ := l
  by_cases hi : i = 0
  · subst hi
    cases s <;> simp [img2, letterFun, xElt, s43_inv, psi_s43]
  · cases s <;> simp only [img2, letterFun, hi, Bool.false_eq_true, ↓reduceIte, yElt, prod_inv,
      psi_prod]

private theorem psi_wordProd (v : List (ℕ × Bool)) (j : Fin 45) :
    psi (wordProd (img2 xElt yElt) v) j = applyWord v j := by
  induction v with
  | nil => simp [wordProd, applyWord]
  | cons l v ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [map_mul, Equiv.Perm.mul_apply, ih, psi_letter]
    rfl

theorem witness_check : ∀ j : Fin 45, applyWord (wit j) 0 = j := by
  decide +kernel

theorem closure_xy : Subgroup.closure ({xElt, yElt} : Set PSp43) = ⊤ := by
  rw [eq_top_iff, ← Y43_eq_top, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  set H := Subgroup.closure ({xElt, yElt} : Set PSp43)
  have hw : wordProd (img2 xElt yElt) (wit j) ∈ H :=
    wordProd_mem (fun i => by
      unfold img2
      split <;> exact Subgroup.subset_closure (by simp)) _
  have hx : xElt ∈ H := Subgroup.subset_closure (by simp)
  have h := conj_s43 (wordProd (img2 xElt yElt) (wit j)) 0
  rw [psi_wordProd, witness_check] at h
  rw [SetLike.mem_coe, ← h]
  exact H.mul_mem (H.mul_mem hw hx) (H.inv_mem hw)

theorem relCheck_eq :
    relCheck 45 (tauTab 0) (tauTab 0) (seqTab bIdx) (seqTab bIdx.reverse) checkWords = true :=
  Certificates.certificate10011.1

theorem relators_eval :
    ∀ v ∈ checkWords, wordProd (img2 xElt yElt) v = 1 := by
  let : MulAction PSp43 (Fin 45) := MulAction.compHom _ psi
  have : FaithfulSMul PSp43 (Fin 45) := ⟨fun h => psi_injective (Equiv.ext h)⟩
  have hn : (45 : ℕ) < 2 ^ 32 := by norm_num
  have rep_tau : ∀ i, Rep 45 (tauTab i) (s43 i) := by
    intro i j hj
    rw [tauTab, ap_ofFn _ hj, idx_of_lt _ hj]
    show (UInt32.ofNat (tauFun i ⟨j, hj⟩).val).toNat = (psi (s43 i) ⟨j, hj⟩).val
    rw [psi_s43, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt ((tauFun i ⟨j, hj⟩).isLt.trans (by norm_num))]
  have rep_seq : ∀ l : List (Fin 45), Rep 45 (seqTab l) ((l.map s43).prod) := by
    intro l
    induction l with
    | nil =>
      have e : seqTab [] = idT 45 := by simp only [seqTab, List.foldr_nil]
      rw [e, List.map_nil, List.prod_nil]
      exact Rep.idT hn
    | cons i l ih =>
      have e : seqTab (i :: l) = compT 45 (tauTab i) (seqTab l) := by
        simp only [seqTab, List.foldr_cons]
      rw [e, List.map_cons, List.prod_cons]
      exact Rep.compT (rep_tau i) ih
  have hxi : Rep 45 (tauTab 0) xElt⁻¹ := by
    rw [xElt, s43_inv]
    exact rep_tau 0
  have hyi : Rep 45 (seqTab bIdx.reverse) yElt⁻¹ := by
    rw [yElt, prod_inv]
    exact rep_seq _
  exact wordProd_eq_one_of_relCheck hn (rep_tau 0) hxi (rep_seq bIdx) hyi relCheck_eq

theorem card_le :
    Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 25920 :=
  Certificates.certificate10011.2

theorem isPresentation_PSp43 :
    IsPresentation (fun i : Fin 2 => img2 xElt yElt i.val) (wordSet rels) :=
  IsPresentation.of_wordProd_of_card closure_xy
    (fun v hv => relators_eval v (by
      rw [checkWords, List.map_append]
      exact List.mem_append_left _ hv))
    card_le (by rw [card_PSp43])

theorem commWord_eval (i : Fin 2) :
    FreeGroup.lift (fun j : Fin 2 => img2 xElt yElt j.val)
      (FreeGroup.mk (commWords (coverPairs i))) = img2 xElt yElt i.val := by
  refine lift_mk_eq_of_wordProd _ (relators_eval _ ?_)
  rw [checkWords, List.map_append]
  refine List.mem_append_right _ ?_
  fin_cases i <;> simp

end CFSG.LieType.Multipliers.U42
