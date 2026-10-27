module

public import CFSG.CGT.PushingUpLit.CGT6X.End4Conf
public import CFSG.CGT.PushingUpLit.CGT6X.End4A9Sub
public import CFSG.Alternating.Multipliers.OddKernel

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3

section Center

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem piHom_injective_a9 (cfg : EndCfg4 G T Y) (e : LayerQ G Y ≃* alternatingGroup (Fin 9)) :
    Function.Injective (piHom e) := by
  have : Group.IsPerfect ↥(CGT6.conjClosure Y G) := ⟨cfg.quasi.1⟩
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd
    (P := ↥(CGT6.conjClosure Y G)) (m := 7) (by norm_num) (piHom e) (piHom_surjective e)
    (ker_piHom e).le (by rw [ker_piHom e]; exact cfg.oddZ)
  exact (MonoidHom.ker_eq_bot_iff _).mp (Subgroup.card_eq_one.mp h1)

theorem exists_theta_a9 (cfg : EndCfg4 G T Y) (e : LayerQ G Y ≃* alternatingGroup (Fin 9)) :
    ∃ θ : ↥(CGT6.conjClosure Y G) ≃* alternatingGroup (Fin 9), θ.toMonoidHom = piHom e :=
  ⟨MulEquiv.ofBijective (piHom e) ⟨piHom_injective_a9 cfg e, piHom_surjective e⟩, rfl⟩

omit [Finite V] in
theorem sigma_theta {e : LayerQ G Y ≃* alternatingGroup (Fin 9)}
    {θ : ↥(CGT6.conjClosure Y G) ≃* alternatingGroup (Fin 9)} (hθ : θ.toMonoidHom = piHom e)
    {t : MulAut V} (htG : t ∈ G) {σ : Equiv.Perm (Fin 9)}
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure htG hl⟩ : alternatingGroup (Fin 9)) :
        Equiv.Perm (Fin 9)) = σ * ((piHom e ⟨l, hl⟩ : alternatingGroup (Fin 9)) :
          Equiv.Perm (Fin 9)) * σ⁻¹) :
    ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((θ ⟨t * l * t⁻¹, conj_mem_conjClosure htG hl⟩ : alternatingGroup (Fin 9)) :
        Equiv.Perm (Fin 9)) = σ * ((θ ⟨l, hl⟩ : alternatingGroup (Fin 9)) :
          Equiv.Perm (Fin 9)) * σ⁻¹ := by
  intro l hl
  have := hσ l hl
  rw [← hθ] at this
  exact this

end Center

section YCard

variable {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)}

theorem card_Y_sixty (hY2 : YSL Y 2) : Nat.card ↥Y = 60 := by
  rw [YSL.card_eq (by norm_num) hY2]
  norm_num

end YCard

section Conj

variable {M : Type*} [Group M] {L : Subgroup M} {n : ℕ} {θ : ↥L ≃* alternatingGroup (Fin n)}
  {S : Subgroup (alternatingGroup (Fin n))} {t : M} {σ : Equiv.Perm (Fin n)}

theorem conj_mem_layerPre (ht : ∀ l ∈ L, t * l * t⁻¹ ∈ L)
    (hσ : ∀ (l : M) (hl : l ∈ L),
      ((θ ⟨t * l * t⁻¹, ht l hl⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ⁻¹)
    (hS : ∀ g ∈ S, ∀ g' : alternatingGroup (Fin n),
      (g' : Equiv.Perm (Fin n)) = σ * (g : Equiv.Perm (Fin n)) * σ⁻¹ → g' ∈ S) :
    ∀ k ∈ layerPre θ S, t * k * t⁻¹ ∈ layerPre θ S := by
  intro k hk
  obtain ⟨hkL, hkS⟩ := mem_layerPre.mp hk
  exact mem_layerPre.mpr ⟨ht k hkL, hS _ hkS _ (hσ k hkL)⟩

theorem comm_layerPre (ht : ∀ l ∈ L, t * l * t⁻¹ ∈ L)
    (hσ : ∀ (l : M) (hl : l ∈ L),
      ((θ ⟨t * l * t⁻¹, ht l hl⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ⁻¹)
    (hS : ∀ g ∈ S, σ * (g : Equiv.Perm (Fin n)) * σ⁻¹ = (g : Equiv.Perm (Fin n))) :
    ∀ k ∈ layerPre θ S, t * k = k * t := by
  intro k hk
  obtain ⟨hkL, hkS⟩ := mem_layerPre.mp hk
  have h1 : θ ⟨t * k * t⁻¹, ht k hkL⟩ = θ ⟨k, hkL⟩ :=
    Subtype.ext ((hσ k hkL).trans (hS _ hkS))
  have h2 := congrArg Subtype.val (θ.injective h1)
  exact (mul_inv_eq_iff_eq_mul.mp h2)

end Conj

end CFSG.CGT.PushingUpLit.CGT6X.End4
