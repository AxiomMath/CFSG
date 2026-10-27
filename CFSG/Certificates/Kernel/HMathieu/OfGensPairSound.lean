
module

public import Certificates.Data.Kernel.HMathieu.RootsPair
public import CFSG.Certificates.Kernel.HMathieu.OfGensSound
public import CFSG.Quasithin.H13.A5M12CentBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

theorem permM_lt {σ : Equiv.Perm (Fin 24)} {a : Array Nat} (ha : HasArr σ a) (x : Nat) :
    permM a x < 2 ^ 24 := by
  refine actM_lt (fun c hc => ?_) x
  simp only [permCols, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have e : a[j]! = (σ ⟨j, hj⟩ : Nat) := (ha ⟨j, hj⟩).symm
  rw [e]
  exact Nat.pow_lt_pow_right (by norm_num) (σ _).2

theorem mem_m24Pair_of_dod {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) {a : Array Nat}
    (ha : HasArr σ a)
    (h : (permM a dodecadMask == dodecadMask ||
      permM a dodecadMask == dodecadMask ^^^ (2 ^ 24 - 1)) = true) : σ ∈ m24Pair := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  refine mem_m24Pair.2 ⟨hσ, ?_⟩
  rcases h with h0 | h1
  · exact Or.inl (permAct_dodecadE_of_arr ha h0)
  · right
    rw [permAct_dodecadE_of_arr ha h1, bvec_compl]
    rfl

theorem okPair_of_mem : ∀ σ ∈ m24Pair, ∀ a b, HasArr σ a → HasArr σ⁻¹ b →
    okPair a b = true := by
  intro σ hσ a b ha hb
  obtain ⟨hA, hY⟩ := mem_m24Pair.1 hσ
  have key : ∀ x, x < 2 ^ 24 → G6.permAct 24 σ dodecadE = Multiplicative.ofAdd (bvec 24 x) →
      permM a dodecadMask = x := fun x hx e =>
    CFSG.Quasithin.H.Mathieu.bvec_inj (permM_lt ha _) hx
      (congrArg Multiplicative.toAdd ((permAct_dodecadE_of_arr ha rfl).symm.trans e))
  have ec : dodecadE * G6.allOnes 24 =
      Multiplicative.ofAdd (bvec 24 (dodecadMask ^^^ (2 ^ 24 - 1))) := by
    rw [bvec_compl]
    rfl
  simp only [okPair, autArrOK_of_mem ha hb hA, Bool.true_and, Bool.or_eq_true, beq_iff_eq]
  rcases hY with h0 | h1
  · exact Or.inl (key _ (by decide +kernel) h0)
  · exact Or.inr (key _ (by decide +kernel) (h1.trans ec))

variable {gs E : List Nat} {fuel np : Nat}

theorem rootPairK_spec (h : rootPairK np gs E = true) :
    rootK 0 np gs E = true ∧ ∀ g ∈ gs, dodK g = true := by
  simpa only [rootPairK, Bool.and_eq_true, List.all_eq_true] using h

theorem closure_rootPairK (h : rootPairK np gs E = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) : Closure gs E m24Pair := by
  obtain ⟨hr, hd⟩ := rootPairK_spec h
  refine closure_of m24Pair (fun g hg => ?_) (rootK_vp hr) hbfs (rootK_spec hr).2
  obtain ⟨-, σ, hσ, hs, -⟩ := genK_spec ((rootK_spec hr).1 g hg)
  exact ⟨σ, mem_m24Pair_of_dod hσ hs (hd g hg), hs⟩

theorem ok_pair_of_rootPairK {T : PT 24} {m : Nat} (hT : T = PT.ofGens 24 (gs.map unpk) fuel)
    (h : rootPairK np gs E = true) (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E)
    (hm : E.length = m) : T.check = true ∧ T.n = m ∧ T.allOK okPair = true := by
  subst hT
  have hv := rootK_vp (rootPairK_spec h).1
  have H := closure_rootPairK h hbfs
  obtain ⟨hc, hn⟩ := check_ofGens hv hbfs H
  exact ⟨hc, hn.trans hm, allOK_ofGens okPair_of_mem hv hbfs H⟩

end CFSG.KC.HMathieu

end
