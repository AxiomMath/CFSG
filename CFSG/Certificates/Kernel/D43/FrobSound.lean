module

public import CFSG.Certificates.Kernel.D43.KeySound

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.ON.Native CFSG.ASVolI CFSG.Blueprint.Chevalley


section Frob

variable {K : Type*} [Field K]

@[expose] noncomputable def frobV (v : RootModule .D4 K) : RootModule .D4 K :=
  Finsupp.mapRange (fun c => c ^ 3) (by simp) v

theorem frobV_apply (v : RootModule .D4 K) (l : Label .D4) : frobV v l = v l ^ 3 :=
  Finsupp.mapRange_apply ..

theorem frobV_smul (c : K) (v : RootModule .D4 K) : frobV (c • v) = c ^ 3 • frobV v := by
  ext l
  rw [frobV_apply, Finsupp.smul_apply, Finsupp.smul_apply, frobV_apply, smul_eq_mul, smul_eq_mul,
    mul_pow]

theorem frobV_e (l : ℕ) : frobV (burnsideF48d_e K l) = burnsideF48d_e K l := by
  rw [frobV, burnsideF48d_e, Finsupp.mapRange_single, one_pow]

variable [CharP K 3]

theorem frobV_add (v w : RootModule .D4 K) : frobV (v + w) = frobV v + frobV w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  ext l
  rw [frobV_apply, Finsupp.add_apply, Finsupp.add_apply, frobV_apply, frobV_apply,
    add_pow_char]

@[expose] noncomputable def frobH : RootModule .D4 K →+ RootModule .D4 K where
  toFun := frobV
  map_zero' := by
    ext l
    rw [frobV_apply]
    simp
  map_add' := frobV_add

theorem frobH_apply (v : RootModule .D4 K) : frobH v = frobV v := rfl

variable (ω : K)

theorem frobV_Ψ (r : Fin 154 → ZMod 3) :
    frobV (burnsideF48d_Ψ ω r) = ∑ q : Fin 154, burnsideF48d_z K (r q) • frobV (burnsideF48d_b ω q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← frobH_apply, burnsideF48d_Ψ, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [frobH_apply, frobV_smul, ← map_pow, ZMod.pow_card]

variable (hω : ω ^ 3 = ω + 1)

include hω in
theorem vec_map_frob {a : Array ℕ} (ha : a.size = 28) (c : ℕ) :
    burnsideF48d_vec ω (a.map fun x => burnsideF48d_frobC (burnsideF48d_mulC c x)) =
      frobV (burnsideF48d_φ ω c • burnsideF48d_vec ω a) := by
  rw [← frobH_apply, burnsideF48d_vec, burnsideF48d_vec, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [burnsideF48d_getElem!_map ha _ (Finset.mem_range.1 hl), burnsideF48d_φ_frob ω hω,
    burnsideF48d_φ_mul ω hω, smul_smul, frobH_apply, frobV_smul, frobV_e]

include hω in
theorem Ψ_frobRows (q : Fin 154) :
    burnsideF48d_Ψ ω (vecOf (burnsideF48d_frobRows ())[q.val]!) = frobV (burnsideF48d_b ω q) := by
  have e : (burnsideF48d_frobRows ())[q.val]! = if q.val < 84 then
      burnsideF48d_realW ((burnsideF48d_unit (q.val / 3)).map fun x =>
        burnsideF48d_frobC (burnsideF48d_mulC (burnsideF48d_powC 3 (q.val % 3)) x)) else W.zero := by
    rw [burnsideF48d_frobRows, getElem!_pos _ q.val (by simp), Array.getElem_ofFn]
  rw [e]
  by_cases hq : q.val < 84
  · have hl : q.val / 3 < 28 := by omega
    have hs : (burnsideF48d_unit (q.val / 3)).size = 28 := by simp [burnsideF48d_unit]
    rw [if_pos hq, burnsideF48d_Ψ_realW, burnsideF48d_b, if_pos hq, vec_map_frob ω hω hs,
      burnsideF48d_vec_unit ω hl, burnsideF48d_φ_pow ω hω, burnsideF48d_φ_three]
  · rw [if_neg hq, burnsideF48d_b, if_neg hq, ← frobH_apply, map_zero]
    have : vecOf W.zero = 0 := by
      funext j
      rw [vecOf_apply, W.toV_zero, V.val_zero]
      rfl
    rw [this, burnsideF48d_Ψ_zero]

theorem frobRows_wf : RowsWF (toVM (burnsideF48d_frobRows ())) := by
  intro j
  have hs : (burnsideF48d_frobRows ()).size = 154 := by
    rw [burnsideF48d_frobRows, Array.size_ofFn]
  rw [toVM_getElem!]
  by_cases hj : j < 154
  · rw [burnsideF48d_frobRows, getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj),
      Array.getElem_ofFn]
    split_ifs
    · obtain ⟨hp, hm⟩ := V.ofFn_lt 154 fun q => if q < 84 then
        ((burnsideF48d_unit (j / 3)).map fun x =>
          burnsideF48d_frobC (burnsideF48d_mulC (burnsideF48d_powC 3 (j % 3)) x))[q / 3]! /
            3 ^ (q % 3) % 3 else 0
      rw [burnsideF48d_realW, W.toV_ofV
        (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
        (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by norm_num)))]
      exact V.wf_ofFn _ _
    · rw [W.toV_zero]; exact V.wf_zero
  · rw [getElem!_neg _ j (by rw [hs]; exact hj), W.toV_default]
    exact V.wf_zero

include hω in
theorem Ψ_combW_frob {r : W} (hr : r.toV.wf = true) :
    burnsideF48d_Ψ ω (vecOf (combW 154 (burnsideF48d_frobRows ()) r)) =
      frobV (burnsideF48d_Ψ ω (vecOf r)) := by
  rw [vecOf_combW frobRows_wf hr, burnsideF48d_Ψ_sum, frobV_Ψ]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [burnsideF48d_Ψ_smul, Ψ_frobRows ω hω]

end Frob

section Action

@[expose] def negPerm (K : Type) [Field K] : Subgroup (Equiv.Perm (RootModule Tag.D4 K)) where
  carrier := {g | ∀ v, g (-v) = -g v}
  mul_mem' := by
    intro a b ha hb v
    change a (b (-v)) = -a (b v)
    rw [hb, ha]
  one_mem' := fun _ => rfl
  inv_mem' := by
    intro a ha v
    change a.symm (-v) = -a.symm v
    apply a.injective
    rw [ha, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem exists_ρhat_of_checks {KT : Nat → Nat} {RL : List (List Nat)} {T : Nat → Nat → Nat}
    (hrows : ∀ k < 9, rowsOK (RL.getD k []) k = true)
    (hkeys : ∀ k < 9, ∀ p < 26572, T k p < 26572 ∧ (mv (RL.getD k []) (key KT p) = key KT (T k p) ∨
      mv (RL.getD k []) (key KT p) = vneg (key KT (T k p))))
    (hwf : ∀ p < 26572, wf84 (key KT p) = true)
    (hdist : ∀ p < 26572, ∀ q < 26572, canonPk (key KT p) = canonPk (key KT q) → p = q)
    {K : Type} [Field K] (ω : K) (hK : Nat.card K = 27) (hω : ω ^ 3 = ω + 1)
    (h : Fin 9 → ↥(negPerm K))
    (hg : ∀ k : Fin 9, k.val < 8 → ∀ v, (h k : Equiv.Perm (RootModule Tag.D4 K)) v =
      burnsideF48d_genEnd ω k v)
    (hF : ∀ v, (h 8 : Equiv.Perm (RootModule Tag.D4 K)) v = frobV v) :
    ∃ ρ : ↥(Subgroup.closure (Set.range h)) →* Equiv.Perm (Fin 26572),
      ∀ k (p : Fin 26572), ((ρ ⟨h k, Subgroup.subset_closure ⟨k, rfl⟩⟩ p : Fin 26572) : ℕ) =
        T k p := by
  haveI : CharP K 3 := by
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hc : ∀ p < 26572, canon (key KT p) = true := fun p hp => (wf84_spec (hwf p hp)).2.1
  have hb : ∀ p < 26572, VB 84 (vOf (key KT p)) := fun p hp => (wf84_spec (hwf p hp)).1
  let P : ℕ → RootModule Tag.D4 K := fun p => burnsideF48d_Ψ ω (vecOf (ofV (vOf (key KT p))))
  have hsmul : ∀ (g : ↥(negPerm K)) (v : RootModule Tag.D4 K),
      g • v = (g : Equiv.Perm (RootModule Tag.D4 K)) v := fun _ _ => rfl
  have hT : ∀ k : Fin 9, ∀ p < 26572, T k p < 26572 ∧
      (h k • P p = P (T k p) ∨ h k • P p = -P (T k p)) := by
    intro k p hp
    obtain ⟨hlt, hmv⟩ := hkeys k k.2 p hp
    refine ⟨hlt, ?_⟩
    have hwr := wf_of_canon154 (canon154_vOf (hc p hp))
    have e : h k • P p =
        burnsideF48d_Ψ ω (vecOf (ofV (vOf (mv (RL.getD k []) (key KT p))))) := by
      rw [hsmul, ← rows_mulVecT (hrows k k.2) (hb p hp)]
      by_cases h8 : k.val = 8
      · have hk : k = 8 := Fin.ext h8
        subst hk
        have hrk : burnsideF48d_rows (burnsideF48d_colTab ()) ((8 : Fin 9) : ℕ) =
            burnsideF48d_frobRows () := if_pos rfl
        rw [hF, hrk]
        exact (Ψ_combW_frob ω hω hwr).symm
      · have hrk : burnsideF48d_rows (burnsideF48d_colTab ()) k =
            burnsideF48d_genRows (burnsideF48d_colTab ()) k := if_neg h8
        rw [hg k (by omega), hrk]
        exact (burnsideF48d_Ψ_combW ω (burnsideF48d_rowsWF _) hwr _
          (burnsideF48d_Ψ_genRows ω hω k)).symm
    rcases hmv with e2 | e2
    · exact Or.inl (by rw [e, e2])
    · refine Or.inr ?_
      rw [e, e2, vecOf_vneg (hc _ hlt), burnsideF48d_Ψ_neg]
  have hinj : ∀ p < 26572, ∀ q < 26572, (P p = P q ∨ P p = -P q) → p = q := by
    intro p hp q hq e
    have hpH := vecOf_high (hc p hp) (hb p hp)
    rcases e with e | e
    · have := burnsideF48d_Ψ_inj ω hω hpH (vecOf_high (hc q hq) (hb q hq)) e
      exact hdist p hp q hq (by rw [vecOf_vOf_inj (hc p hp) (hc q hq) this])
    · have e' : P p = burnsideF48d_Ψ ω (vecOf (ofV (vOf (vneg (key KT q))))) := by
        rw [vecOf_vneg (hc q hq), burnsideF48d_Ψ_neg]
        exact e
      have hnb : VB 84 (vOf (vneg (key KT q))) := by
        rw [vOf_vneg (hc q hq)]
        exact (hb q hq).neg
      have := burnsideF48d_Ψ_inj ω hω hpH (vecOf_high (canon_vneg (hc q hq)) hnb) e'
      have e3 := vecOf_vOf_inj (hc p hp) (canon_vneg (hc q hq)) this
      exact hdist p hp q hq (by rw [e3, canonPk_vneg (hc q hq)])
  exact exists_hom_signed h P (fun k p => T k p) (fun g v => g.2 v) hT hinj

end Action

end CFSG.KC.D43

end
