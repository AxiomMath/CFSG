module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import Certificates.Data.Odd87F3CC

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier CFSG.Certificates Certificates.Odd87F3

variable {n : ℕ}

theorem fixes_base_of_commutes_odd (E : List ℤ → Equiv.Perm (Fin n)) {z : Equiv.Perm (Fin n)}
    (hE : ∀ w, z * E w = E w * z) (b y₀ : Fin n) (sg ns : List (List ℤ))
    (hsg : ∀ s ∈ sg, E s b = b) (hns : ∀ c ∈ ns, E c b ≠ b)
    (hF : ∀ y, (∀ s ∈ sg, E s y = y) → (∀ c ∈ ns, E c y ≠ y) → y = b ∨ y = y₀)
    (hodd : Odd (orderOf z)) : z b = b := by
  have hmove : ∀ w y, E w (z y) = z (E w y) := fun w y => by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f y) (hE w)
    simpa using this.symm
  set S : Fin n → Prop := fun y => (∀ s ∈ sg, E s y = y) ∧ (∀ c ∈ ns, E c y ≠ y) with hSdef
  have hSz : ∀ y, S y → S (z y) := by
    intro y hy
    refine ⟨fun s hs => ?_, fun c hc h3 => ?_⟩
    · rw [hmove, hy.1 s hs]
    · rw [hmove] at h3
      exact hy.2 c hc (z.injective h3)
  have hSb : S b := ⟨hsg, hns⟩
  have hF' : ∀ y, S y → y = b ∨ y = y₀ := fun y hy => hF y hy.1 hy.2
  by_contra hzb
  have h1 : z b = y₀ := (hF' _ (hSz _ hSb)).resolve_left hzb
  have hSy0 : S y₀ := h1 ▸ hSz _ hSb
  have h2 : z y₀ = b := by
    rcases hF' _ (hSz _ hSy0) with h | h
    · exact h
    · exfalso
      have h3 : y₀ = b := z.injective (h.trans h1.symm)
      exact hzb (h1.trans h3)
  have h4 : (z ^ 2) y₀ = y₀ := by
    rw [pow_two, Equiv.Perm.mul_apply, h2, h1]
  obtain ⟨k, hk⟩ := hodd
  have h5 : (z ^ orderOf z) b = z b := by
    rw [hk, pow_succ, pow_mul, Equiv.Perm.mul_apply, h1]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h4 k
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at h5
  exact hzb h5.symm

theorem eq_one_of_commutes_odd (E : List ℤ → Equiv.Perm (Fin n)) {z : Equiv.Perm (Fin n)}
    (hE : ∀ w, z * E w = E w * z)
    (hbase : ∀ v : Fin n, ∃ b : Fin n, z b = b ∧ ∃ w, E w b = v) : z = 1 := by
  ext v
  obtain ⟨b, hb, w, hw⟩ := hbase v
  have : z (E w b) = E w (z b) := by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f b) (hE w)
    simpa using this
  rw [Equiv.Perm.one_apply, ← hw, this, hb]

theorem ap_eq_of_rep {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) (y : Fin n) :
    ap T y.val = (g y).val := by
  rw [hT y.val y.isLt, idx_of_lt _ y.isLt]
  rfl

theorem eq_one_of_ccOK (hn : n < 2 ^ 32) {gT : List Table} {gs : List (Equiv.Perm (Fin n))}
    (hgT : List.Forall₂ (Rep n) gT gs) {orbs : List Orb} {cov : List (ℕ × List ℤ)}
    (h : ccOK n gT orbs cov = true) {z : Equiv.Perm (Fin n)} (hz : ∀ g ∈ gs, z * g = g * z)
    (hodd : Odd (orderOf z)) : z = 1 := by
  classical
  simp only [ccOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hinv, horb⟩, hcov⟩ := h
  have hgI := forall₂_inv_of_invOK hgT hinv
  set E : List ℤ → Equiv.Perm (Fin n) := evalCodes gs with hEdef
  have hrep : ∀ w, Rep n (evalT n gT (gT.map (invT n)) w) (E w) := fun w => rep_evalT hn hgT hgI w
  have hE : ∀ w, z * E w = E w * z := fun w => commute_evalCodes hz w
  have hfix : ∀ o ∈ orbs, ∃ hb : o.base < n, z ⟨o.base, hb⟩ = ⟨o.base, hb⟩ := by
    intro o ho
    have h1 := horb o ho
    simp only [decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, List.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at h1
    obtain ⟨⟨⟨⟨hb, hy0⟩, hsg⟩, hns⟩, hF⟩ := h1
    refine ⟨hb, ?_⟩
    set bF : Fin n := ⟨o.base, hb⟩
    set y0F : Fin n := ⟨o.y0, hy0⟩
    refine fixes_base_of_commutes_odd E hE bF y0F o.sg o.ns ?_ ?_ ?_ hodd
    · intro s hs
      apply Fin.ext
      have := hsg s hs
      rw [ap_eq_of_rep (hrep s) bF] at this
      exact this
    · intro c hc hcb
      have := hns c hc
      rw [show o.base = bF.val from rfl, ap_eq_of_rep (hrep c) bF, hcb] at this
      exact this rfl
    · intro y hy1 hy2
      have h := hF y.val (List.mem_range.2 y.isLt)
      have hSG : ((o.sg.map (evalT n gT (gT.map (invT n)))).all fun T => ap T y.val == y.val) =
          true := by
        rw [List.all_eq_true]
        intro T hT
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hT
        rw [beq_iff_eq, ap_eq_of_rep (hrep s) y, hy1 s hs]
      have hNS : ((o.ns.map (evalT n gT (gT.map (invT n)))).all fun T => ap T y.val != y.val) =
          true := by
        rw [List.all_eq_true]
        intro T hT
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hT
        rw [bne_iff_ne, ne_eq, ap_eq_of_rep (hrep c) y]
        intro hcy
        exact hy2 c hc (Fin.ext hcy)
      rw [hSG, hNS] at h
      simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
  refine eq_one_of_commutes_odd E hE fun v => ?_
  have hv := hcov v.val (List.mem_range.2 v.isLt)
  cases hc : cov[v.val]? with
  | none => rw [hc] at hv; exact absurd hv (by simp)
  | some p =>
    obtain ⟨i, w⟩ := p
    rw [hc] at hv
    simp only at hv
    cases ho : orbs[i]? with
    | none => rw [ho] at hv; exact absurd hv (by simp)
    | some o =>
      rw [ho] at hv
      simp only [beq_iff_eq] at hv
      have hom : o ∈ orbs := List.mem_of_getElem? ho
      obtain ⟨hb, hzb⟩ := hfix o hom
      refine ⟨⟨o.base, hb⟩, hzb, w, Fin.ext ?_⟩
      rw [← ap_eq_of_rep (hrep w) ⟨o.base, hb⟩]
      exact hv

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
