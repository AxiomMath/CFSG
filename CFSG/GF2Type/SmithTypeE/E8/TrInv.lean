module

public import CFSG.GF2Type.SmithTypeE.E8.TrAct
public import CFSG.GF2Type.SmithTypeE.E8.TrCheck
public import CFSG.GF2Type.SmithTypeE.E8.FactsForm
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.SmithE8M CFSG.SeitzReduction.E7Pilot CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction
open CFSG.SeitzReduction.EPilot (pinnedElt)

section Rep


theorem finrank_commSp_rep_ge (k : Fin 5) :
    12 ≤ Module.finrank (ZMod 2) (commSp (e7Rep (ZMod 2) k)) ∧
      (k ≠ 0 → 14 ≤ Module.finrank (ZMod 2) (commSp (e7Rep (ZMod 2) k))) := by
  have hmem : ∀ c ∈ PivSet k,
      (Finsupp.single c 1 : Fin e7Data.d →₀ ZMod 2) ∈ commSp (e7Rep (ZMod 2) k) := by
    intro c hc
    rw [PivSet, Finset.mem_filter] at hc
    obtain ⟨-, a, β, hβ, ha, hothers, hcw⟩ := hc
    have hpiv := actL_pivot (e7RepFrames k) (e7RepFrames_isRoot k) (e7RepFrames_nodup_pos k).1 β
      hβ a c ha hcw (fun γ hγ hne => ⟨hothers γ hγ hne, frame_orth k β hβ γ hγ (Ne.symm hne)⟩)
    refine mem_commSp.2 ⟨Finsupp.single a 1, ?_⟩
    rw [e7Rep_apply, hpiv, add_sub_cancel_left]
  have h1 := card_le_finrank_of_single_mem (PivSet k) _ hmem
  obtain ⟨h2, h3⟩ := card_Piv k
  exact ⟨h2.trans h1, fun hk => (h3 hk).trans h1⟩

@[expose] def Socle (a : ↥(adjointGroup .E7 (ZMod 2))) : Prop :=
  ∀ N : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2), N ≠ ⊥ → N ≤ commSp a →
    (∀ c : ↥(adjointGroup .E7 (ZMod 2)), c * a = a * c → ∀ n ∈ N, e7Rep56 (ZMod 2) c n ∈ N) →
      ∃ w ∈ weightVec, w ∈ N

@[expose] noncomputable def Sk (k : Fin 5) : Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
  Subgroup.closure {x | ∃ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ ∧ 0 < height δ ∧
    (∀ β ∈ e7RepFrames k, 0 ≤ iform δ β) ∧ x = pinnedElt .E7 δ (1 : ZMod 2)}

theorem Sk_isPGroup (k : Fin 5) : IsPGroup 2 (Sk k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Sk k ≤ (posUnipotent .E7 (ZMod 2)).comap (adjointGroup .E7 (ZMod 2)).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨δ, hδ, hpos, -, rfl⟩
    exact F.pinnedElt_mem_posUnipotent hδ hpos
  intro s
  obtain ⟨n, hn⟩ := CFSG.SignalizerFunctorTheorem.NonLocalExc.isPGroup_posUnipotent
    (τ := .E7) (K := ZMod 2) 2 ⟨((s : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)), hle s.2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun x : ↥(posUnipotent .E7 (ZMod 2)) => (x : ModGL .E7 (ZMod 2))) hn
  simpa using this

theorem Sk_commute (k : Fin 5) {s : ↥(adjointGroup .E7 (ZMod 2))} (hs : s ∈ Sk k) :
    s * e7Rep (ZMod 2) k = e7Rep (ZMod 2) k * s := by
  have hle : Sk k ≤ Subgroup.centralizer {e7Rep (ZMod 2) k} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨δ, hδ, -, hdot, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, e7Rep_eq_prod]
    refine Commute.eq (Commute.list_prod_right _ _ fun y hy => ?_)
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hy
    have hc := CFSG.SeitzReduction.classD4_commute_pinnedX (R := ZMod 2)
      (Or.inr (Or.inr (Or.inl rfl))) hδ (e7RepFrames_isRoot k β hβ) (hdot β hβ) 1 1
    exact Subtype.ext hc.eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hs)

theorem socle_rep (k : Fin 5) (hk : k.val ≤ 2) : Socle (e7Rep (ZMod 2) k) := by
  intro N hN hNle hinv
  obtain ⟨n, hnN, hn0, hnfix⟩ := exists_fixed_vec8 (Sk_isPGroup k) (e7Rep56 (ZMod 2)) N hN
    (fun s hs n hn => hinv s (Sk_commute k hs) n hn)
  obtain ⟨y, hy⟩ := mem_commSp.1 (hNle hnN)
  have hsupp : ∀ c : Fin e7Data.d, n c ≠ 0 → c ∈ Bk k := by
    intro c hc
    rw [Bk, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_, ?_⟩
    · have h1 : (actL (e7RepFrames k) y - y) c ≠ 0 := by
        rw [← e7Rep_apply, hy]
        exact hc
      obtain ⟨β, hβ, h⟩ := actL_sub_support (e7RepFrames k) (e7RepFrames_isRoot k) y h1
      exact ⟨β, hβ, h⟩
    · intro i hpos hiform hci
      have hδ : IsRoot .E7 (e8mRoot i) := e8mRoot_isRoot i.2
      have hx : pinnedElt .E7 (e8mRoot i) (1 : ZMod 2) ∈ Sk k :=
        Subgroup.subset_closure ⟨e8mRoot i, hδ, hpos, hiform, rfl⟩
      obtain ⟨c', hc'⟩ := F.exists_shift hδ hci
      have h0 := coord_pinned_sub hδ n hci hc'
      rw [hnfix _ hx] at h0
      apply hc
      rw [← h0]
      simp
  have hne : n.support.Nonempty := Finsupp.support_nonempty_iff.2 hn0
  have hsub : n.support ⊆ Bk k := fun c hc => hsupp c (Finsupp.mem_support_iff.1 hc)
  have hT : ∀ μ ∈ n.support, ∀ l ∈ n.support, μ ≠ l → ∃ β : Fin (Tag.rank .E7) → ℤ,
      IsRoot .E7 β ∧ e7Data.wt l = e7Data.wt μ + MinData.toWeight β ∧
        e7Data.wt μ ⬝ᵥ β = -1 ∧ ∀ ν ∈ n.support, ν ≠ μ → ν ≠ l → e7Data.wt ν ⬝ᵥ β ≠ -1 := by
    intro μ hμ l hl hμl
    obtain ⟨i, h1, h2, h3⟩ := bk_clique k hk μ (hsub hμ) l (hsub hl) hμl
    exact ⟨e8mRoot i, e8mRoot_isRoot i.2, h1, h2, fun ν hν hνμ hνl => h3 ν (hsub hν) hνμ hνl⟩
  have hw := F.sum_single_mem_weightVec n.support hne hT
  rw [← F.finsupp_eq_sum_single n] at hw
  exact ⟨n, hw, hnN⟩

theorem socle_of_conj (g a : ↥(adjointGroup .E7 (ZMod 2))) (h : Socle (g * a * g⁻¹)) :
    Socle a := by
  intro N hN hNle hinv
  have hN' : N.map (e7Rep56 (ZMod 2) g) ≠ ⊥ := by
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    refine Submodule.ne_bot_iff _ |>.2 ⟨e7Rep56 (ZMod 2) g n, Submodule.mem_map_of_mem hn, ?_⟩
    intro h0
    apply hn0
    have := congrArg (e7Rep56 (ZMod 2) g⁻¹) h0
    rwa [F.rep_inv_apply', map_zero] at this
  have hle' : N.map (e7Rep56 (ZMod 2) g) ≤ commSp (g * a * g⁻¹) := by
    rw [commSp_conj]
    exact Submodule.map_mono hNle
  obtain ⟨w, hw, hwN⟩ := h _ hN' hle' (by
    intro c hc n' hn'
    obtain ⟨n, hn, rfl⟩ := hn'
    refine ⟨e7Rep56 (ZMod 2) (g⁻¹ * c * g) n, hinv _ ?_ n hn, ?_⟩
    · have : c * (g * a * g⁻¹) = g * a * g⁻¹ * c := hc
      calc g⁻¹ * c * g * a = g⁻¹ * (c * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * a * g⁻¹ * c) * g := by rw [this]
        _ = a * (g⁻¹ * c * g) := by group
    · rw [← F.rep_mul_apply, ← F.rep_mul_apply]
      congr 1
      group)
  obtain ⟨n, hn, rfl⟩ := hwN
  refine ⟨n, ?_, hn⟩
  have := F.rep_mem_weightVec hw g⁻¹
  rwa [F.rep_inv_apply'] at this

theorem ff_single_right (u : Fin e7Data.d →₀ ZMod 2) (a : Fin e7Data.d) :
    F.ff u (Finsupp.single a 1) = u (F.opI a) := by
  have h1 : F.ff u (Finsupp.single a 1) = F.ffForm u (Finsupp.single a 1) := rfl
  have h2 : ∀ b : Fin e7Data.d, F.ffForm (Finsupp.single b 1) (Finsupp.single a 1) =
      if b = F.opI a then 1 else 0 := fun b => by
    have h := F.ff_single_single b a
    by_cases hb : b = F.opI a
    · have hab : a = F.opI b := by rw [hb, F.opI_opI]
      rw [if_pos hab] at h
      rw [if_pos hb]
      exact h
    · have hab : ¬ a = F.opI b := fun h' => hb (by rw [h', F.opI_opI])
      rw [if_neg hab] at h
      rw [if_neg hb]
      exact h
  conv_lhs => rw [h1, F.finsupp_eq_sum_single u]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl (fun b _ => h2 b),
    Finset.sum_ite_eq' u.support (F.opI a)]
  by_cases h : u (F.opI a) = 0
  · rw [if_neg (fun hm => (Finsupp.mem_support_iff.1 hm) h), h]
  · have h1' : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    rw [if_pos (Finsupp.mem_support_iff.2 h), h1' _ h]

theorem exists_ne_zero_of_rep (k : Fin 5) (hk : 3 ≤ k.val)
    (q : QuadraticForm (ZMod 2) (Fin e7Data.d →₀ ZMod 2))
    (hpol : ∀ u v, QuadraticMap.polar q u v = F.ff u v) (hwt : ∀ w ∈ weightVec, q w = 0) :
    ∃ v ∈ commSp (e7Rep (ZMod 2) k), q v ≠ 0 := by
  obtain ⟨a, c, hP, hcopp, hcsum⟩ := witness_rep k hk
  have hcoord := actL_coord_prod (e7RepFrames k) (e7RepFrames_isRoot k)
    (e7RepFrames_nodup_pos k).1 (frame_orth k) Pk a c hP hcsum
  have hca : c = F.opI a := e7Data_valid.wt_injective (hcopp.trans (F.wt_opI a).symm)
  rw [hca] at hcoord
  set u := e7Rep56 (ZMod 2) (e7Rep (ZMod 2) k) (Finsupp.single a 1) with hu
  have hu' : u = actL (e7RepFrames k) (Finsupp.single a 1) := e7Rep_apply k _
  refine ⟨u - Finsupp.single a 1, mem_commSp.2 ⟨Finsupp.single a 1, rfl⟩, ?_⟩
  have hsub : u - Finsupp.single a 1 = u + Finsupp.single a 1 := by
    rw [sub_eq_add_neg, ZModModule.neg_eq_self]
  rw [hsub, QuadraticMap.map_add q u (Finsupp.single a 1), hwt u (F.rep_mem_weightVec (F.single_mem_weightVec a) _),
    hwt _ (F.single_mem_weightVec a), hpol, ff_single_right, hu', hcoord]
  decide

structure InvFacts8 (a : ↥(adjointGroup .E7 (ZMod 2))) : Prop where
  five_le : 5 ≤ Module.finrank (ZMod 2) (commSp a)
  root_of_le : Module.finrank (ZMod 2) (commSp a) ≤ 13 → IsRootInvol a
  socle_of_ts : ∀ q : QuadraticForm (ZMod 2) (Fin e7Data.d →₀ ZMod 2),
    (∀ u v, QuadraticMap.polar q u v = F.ff u v) → (∀ w ∈ weightVec, q w = 0) →
    (∀ v ∈ commSp a, q v = 0) → Socle a

theorem involutionFacts8 (a : ↥(adjointGroup .E7 (ZMod 2))) (ha : a * a = 1) (ha1 : a ≠ 1) :
    InvFacts8 a := by
  obtain ⟨k, c, hc⟩ := exists_conj_eq_e7Rep_of_sq (K := ZMod 2) (y := a) (by rw [pow_two]; exact ha) ha1
  have hdim : Module.finrank (ZMod 2) (commSp a) =
      Module.finrank (ZMod 2) (commSp (e7Rep (ZMod 2) k)) := by
    rw [← hc, finrank_commSp_conj]
  have hcs : commSp (e7Rep (ZMod 2) k) = (commSp a).map (e7Rep56 (ZMod 2) c) := by
    rw [← hc, commSp_conj]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdim]
    have := (finrank_commSp_rep_ge k).1
    omega
  · intro hle
    rw [hdim] at hle
    have hk0 : k = 0 := by
      by_contra hk
      have := (finrank_commSp_rep_ge k).2 hk
      omega
    subst hk0
    have hroot : IsRootInvol (e7Rep (ZMod 2) 0) := by
      rw [e7Rep_zero_eq_pinnedElt]
      have hmem : (![0, 1, 0, 0, 0, 0, 0] : Fin (Tag.rank .E7) → ℤ) ∈ e7RepFrames 0 := by
        have h : e7RepFrames 0 = [![0, 1, 0, 0, 0, 0, 0]] := rfl
        rw [h]
        exact List.mem_singleton_self _
      exact F.isRootInvol_pinnedElt (e7RepFrames_isRoot 0 _ hmem)
    have := F.isRootInvol_conj hroot c⁻¹
    rwa [← hc, show c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a by group] at this
  · intro q hpol hwt hts
    by_cases hk : k.val ≤ 2
    · exact socle_of_conj c a (by rw [hc]; exact socle_rep k hk)
    · exfalso
      have hk3 : 3 ≤ k.val := by omega
      let q' : QuadraticForm (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
        q.comp (e7Rep56 (ZMod 2) c⁻¹)
      have hpol' : ∀ u v, QuadraticMap.polar q' u v = F.ff u v := by
        intro u v
        have h1 : QuadraticMap.polar q' u v = QuadraticMap.polar q (e7Rep56 (ZMod 2) c⁻¹ u)
            (e7Rep56 (ZMod 2) c⁻¹ v) := by
          simp only [QuadraticMap.polar, q', QuadraticMap.comp_apply, map_add]
        rw [h1, hpol]
        exact F.ff_rep c⁻¹ u v
      have hwt' : ∀ w ∈ weightVec, q' w = 0 := fun w hw =>
        hwt _ (F.rep_mem_weightVec hw c⁻¹)
      obtain ⟨v, hv, hqv⟩ := exists_ne_zero_of_rep k hk3 q' hpol' hwt'
      rw [hcs] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      apply hqv
      show q (e7Rep56 (ZMod 2) c⁻¹ (e7Rep56 (ZMod 2) c w)) = 0
      rw [F.rep_inv_apply']
      exact hts w hw

end Rep

end CFSG.GF2Type.SmithTypeE.E8
