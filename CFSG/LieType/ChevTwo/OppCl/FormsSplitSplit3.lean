module

public import CFSG.LieType.ChevTwo.OppCl.FormsSplitPair
public import CFSG.LieType.ChevTwo.OppCl.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl.FS

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V] [Finite V]

theorem split3_of_graph (Φ : ReflForm F V) (TS : Submodule F V → Prop)
    (W Cc W' M : Submodule F V) (hW : Φ.IsTotallyIsotropic W) (hC : IsCompl (Φ.perp W) Cc)
    (hsymm : ∀ u v, Φ.β v u = Φ.σ (Φ.β u v)) (s : V →ₗ[F] V) (hsW : ∀ v, s v ∈ W)
    (hs0 : ∀ v ∈ Φ.perp W, s v = 0) (hW' : ∀ v, v ∈ W' ↔ ∃ c ∈ Cc, c + s c = v)
    (hti : ∀ c ∈ Cc, ∀ c' ∈ Cc, Φ.β (c + s c) (c' + s c') = 0)
    (hM : M = Φ.perp W ⊓ Φ.perp W') (hTW : TS W) (hTW' : TS W') : Split3 Φ TS W M W' := by
  have hWle : W ≤ Φ.perp W := hW
  have hW'perp : ∀ x ∈ W', x ∈ Φ.perp W → x = 0 := by
    intro x hx' hxp
    obtain ⟨c, hc, rfl⟩ := (hW' _).mp hx'
    have hcp : c ∈ Φ.perp W := by
      have h := sub_mem hxp (hWle (hsW c))
      have heq : c + s c - s c = c := by abel
      rwa [heq] at h
    have hc0 : c = 0 := Submodule.disjoint_def.mp hC.disjoint c hcp hc
    subst hc0
    simp
  have hMmem : ∀ x, x ∈ M ↔ x ∈ Φ.perp W ∧ x ∈ Φ.perp W' := fun x => by
    rw [hM, Submodule.mem_inf]
  have hsup : W ⊔ M ⊔ W' = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ Φ.perp W ⊔ Cc := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨p, hp, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    have hu : p - s c ∈ Φ.perp W := sub_mem hp (hWle (hsW c))
    obtain ⟨w, hw, hwφ⟩ := exists_β_eq Φ W Cc hC
      { toFun := fun d => Φ.β (p - s c) (d : V)
        map_add' := fun a b => by simp only [Submodule.coe_add, Φ.add_right]
        map_smul' := fun r a => by
          simp only [Submodule.coe_smul, Φ.smul_right, RingHom.id_apply, smul_eq_mul] }
    have hm1 : p - s c - w ∈ Φ.perp W := sub_mem hu (hWle hw)
    have hm2 : p - s c - w ∈ Φ.perp W' := by
      rw [Φ.mem_perp]
      intro x hx
      obtain ⟨d, hdC, rfl⟩ := (hW' x).mp hx
      have hsd : Φ.β (s d) (p - s c) = 0 := (Φ.mem_perp).mp hu (s d) (hsW d)
      have hsd' : Φ.β (s d) w = 0 := (Φ.mem_perp).mp (hWle hw) (s d) (hsW d)
      have key : Φ.β w d = Φ.β (p - s c) d := hwφ ⟨d, hdC⟩
      have h1 : Φ.β d (p - s c) = Φ.β d w := by
        rw [hsymm (p - s c) d, hsymm w d, key]
      rw [Φ.add_left, Φ.β_sub_right d (p - s c) w, Φ.β_sub_right (s d) (p - s c) w]
      linear_combination h1 + hsd - hsd'
    have hmM : p - s c - w ∈ M := (hMmem _).mpr ⟨hm1, hm2⟩
    refine Submodule.mem_sup.mpr ⟨w + (p - s c - w),
      Submodule.mem_sup.mpr ⟨w, hw, p - s c - w, hmM, rfl⟩, c + s c,
      (hW' _).mpr ⟨c, hc, rfl⟩, ?_⟩
    abel
  refine ⟨hTW, hTW', ?_, ?_, hsup, ?_, ?_⟩
  · intro w hw m hm
    exact (Φ.mem_perp).mp ((hMmem m).mp hm).1 w hw
  · intro m hm w hw
    exact Φ.refl _ _ ((Φ.mem_perp).mp ((hMmem m).mp hm).2 w hw)
  · rw [Submodule.disjoint_def]
    intro x hxW hxMW'
    obtain ⟨m, hm, w', hw', hmw⟩ := Submodule.mem_sup.mp hxMW'
    have hxp : x ∈ Φ.perp W := hWle hxW
    have hw'p : w' ∈ Φ.perp W := by
      have h := sub_mem hxp ((hMmem m).mp hm).1
      have heq : x - m = w' := by rw [← hmw]; abel
      rwa [heq] at h
    have hw'0 : w' = 0 := hW'perp w' hw' hw'p
    subst hw'0
    have hxM : x ∈ M := by
      rw [← hmw, add_zero]
      exact hm
    have hxW'perp : x ∈ Φ.perp W' := ((hMmem x).mp hxM).2
    have hcx : ∀ c ∈ Cc, Φ.β c x = 0 := by
      intro c hc
      have h1 : Φ.β (c + s c) x = 0 :=
        (Φ.mem_perp).mp hxW'perp (c + s c) ((hW' _).mpr ⟨c, hc, rfl⟩)
      have h2 : Φ.β (s c) x = 0 := (Φ.mem_perp).mp hxp (s c) (hsW c)
      rw [Φ.add_left, h2, add_zero] at h1
      exact h1
    exact eq_zero_of_forall_β_compl Φ W Cc hC hxW fun c hc => Φ.refl _ _ (hcx c hc)
  · rw [Submodule.disjoint_def]
    intro x hxM hxW'
    exact hW'perp x hxW' ((hMmem x).mp hxM).1

end CFSG.LieType.ChevTwo.OppCl.FS
