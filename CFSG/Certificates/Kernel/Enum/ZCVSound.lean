module

public import CFSG.Certificates.Kernel.Enum.ZCV
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w : Nat}

noncomputable def sprod {A : Type} [Group A] (V : Nat → A) (s : Nat) : Nat → A
  | 0 => 1
  | k + 1 => sprod V s k * (if sbit s k then V k else 1)

theorem spt_prep {VP : Nat → Nat} {o s : Nat} {V : Nat → Equiv.Perm (Fin n)} :
    ∀ k, (∀ f < k, PRep n w (VP (o + f)) (V f)) → ∀ q (hq : q < n),
      spt w (mask w) VP o s k q = ((sprod V s k) ⟨q, hq⟩ : Nat)
  | 0, _, _, _ => rfl
  | k + 1, hV, q, hq => by
    change strictN (nIf(sbit s k, pg w (mask w) (VP (o + k)) q, q))
      (fun q => spt w (mask w) VP o s k q) = _
    rw [PK.strictN_eq, PK.nIf_eq]
    have ih := spt_prep (s := s) k (fun f hf => hV f (by omega))
    simp only [sprod, Equiv.Perm.mul_apply]
    cases hb : sbit s k
    · simp only [Bool.false_eq_true, ↓reduceIte, Equiv.Perm.one_apply]
      exact ih q hq
    · simp only [↓reduceIte]
      rw [prep_at (hV k (by omega)) hq]
      exact ih _ _

theorem sprod_mem {A : Type} [Group A] (V : Nat → A) (s p : Nat) :
    ∀ k ≤ p, sprod V s k ∈ Subgroup.closure {c | c ∈ (List.range p).map V}
  | 0, _ => Subgroup.one_mem _
  | k + 1, hk => by
    refine Subgroup.mul_mem _ (sprod_mem V s p k (by omega)) ?_
    split
    · exact Subgroup.subset_closure (by
        simp only [Set.mem_setOf_eq, List.mem_map, List.mem_range]
        exact ⟨k, by omega, rfl⟩)
    · exact Subgroup.one_mem _

theorem vChkS_prep {T : Nat → Nat} {sh lm rb rm pm p o i h hi : Nat} {Z Zi VP VC : Nat → Nat}
    {gz g u : Equiv.Perm (Fin n)}
    (hv : vChkS T sh lm rb rm n w (mask w) pm Z Zi VP VC h hi p o i = true)
    (hu : PRep n w (rperm T sh lm rb rm pm i) u)
    (hZ : ∀ e < p, PRep n w (Z e) (gz ^ e) ∧ PRep n w (Zi e) (gz ^ e)⁻¹)
    (hh : PRep n w h g) (hhi : PRep n w hi g⁻¹) :
    ∀ e < p, g * (gz ^ e * u * (gz ^ e)⁻¹) * g⁻¹ ∈
      Subgroup.closure {c | c ∈ (List.range p).map (fun e => gz ^ e * u * (gz ^ e)⁻¹)} := by
  unfold vChkS at hv
  simp only [PK.strictB_eq, PK.allN_iff, PK.bAnd_eq, Bool.and_eq_true, beq_iff,
    Nat.add_eq] at hv
  have hVP : ∀ e < p, PRep n w (VP (o + e)) (gz ^ e * u * (gz ^ e)⁻¹) := fun e he =>
    eq3_prep (hv e he).1 (hZ e he).1 hu (hZ e he).2
  intro e he
  have hs := (hv e he).2
  have heq : g * (gz ^ e * u * (gz ^ e)⁻¹) * g⁻¹ =
      sprod (fun e => gz ^ e * u * (gz ^ e)⁻¹) (VC (o + e)) p := by
    refine Equiv.ext fun x => Fin.ext ?_
    have e1 := hs x x.2
    rw [hhi x, hVP e he (g⁻¹ x), hh _, spt_prep p hVP x x.2] at e1
    simp only [Equiv.Perm.mul_apply]
    exact e1
  rw [heq]
  exact sprod_mem _ _ p p le_rfl

theorem vRangeS_iff {T : Nat → Nat} {sh lm rb rm m pm h hi p st lo cnt : Nat}
    {Z Zi VP VC : Nat → Nat} :
    vRangeS T sh lm rb rm n w m pm Z Zi VP VC h hi p st lo cnt = true ↔
      ∀ t < cnt, vChkS T sh lm rb rm n w m pm Z Zi VP VC h hi p (p * (st + t)) (lo + t) = true := by
  unfold vRangeS
  exact PK.allN_iff

end CFSG.KC.EnumSound

end
