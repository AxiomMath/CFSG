
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase

@[expose] public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Fischer CFSG.ComponentClassification.M12Cover
open scoped Pointwise

theorem hn693 : (693 : ℕ) < 2 ^ 32 := by norm_num

theorem perm_apply_inv_self {α : Type*} (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x :=
  Equiv.apply_symm_apply f x

theorem perm_inv_apply_self {α : Type*} (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x :=
  Equiv.symm_apply_apply f x

theorem closure_le_of_mem {H : Subgroup (Equiv.Perm (Fin 693))} {gs : List (Equiv.Perm (Fin 693))}
    (h : ∀ g ∈ gs, g ∈ H) : Subgroup.closure {g | g ∈ gs} ≤ H :=
  (Subgroup.closure_le _).2 fun g hg => h g hg

theorem mem_normalizer_of_conj_gens {H : Subgroup (Equiv.Perm (Fin 693))}
    {gs : List (Equiv.Perm (Fin 693))} (hH : H = Subgroup.closure {g | g ∈ gs})
    {k : Equiv.Perm (Fin 693)} (hk : ∀ a ∈ gs, k * a * k⁻¹ ∈ H) :
    k ∈ Subgroup.normalizer (H : Set (Equiv.Perm (Fin 693))) := by
  have hconj : ∀ x ∈ H, k * x * k⁻¹ ∈ H := by
    have hle : H ≤ H.comap (MulAut.conj k).toMonoidHom := by
      rw [hH, Subgroup.closure_le]
      intro a ha
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [← hH]
      exact hk a ha
    intro x hx
    simpa using hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj x, fun hx => ?_⟩
  have hinj : Function.Injective fun y : H => (⟨k * y * k⁻¹, hconj y y.2⟩ : H) := by
    intro y z hyz
    apply Subtype.ext
    have := congrArg Subtype.val hyz
    simpa using this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨k * x * k⁻¹, hx⟩
  have hyx : (y : Equiv.Perm (Fin 693)) = x := by
    have := congrArg Subtype.val hy
    simpa using this
  rw [← hyx]
  exact y.2

theorem card_eq_countP_allTables (Q : RawSchreierDatum 693) (hQ : ValidSchreier Q)
    (f : Table → Bool) (P : Equiv.Perm (Fin 693) → Prop) [DecidablePred P]
    (hfP : ∀ T g, Rep 693 T g → (f T = true ↔ P g)) :
    Nat.card {x : Q.originalSubgroup // P x} = (allTables Q).countP f := by
  have hmem : ∀ g, g ∈ (enumeration Q).reverse ↔ g ∈ Q.originalSubgroup := fun g => by
    rw [List.mem_reverse]
    exact mem_enumeration_iff Q hQ g
  rw [card_subtype_eq_countP Q.originalSubgroup (enumeration Q).reverse
    (List.nodup_reverse.2 (enumeration_nodup Q hQ)) hmem P]
  exact (countP_eq_of_forall₂ (forall₂_allTables hn693 Q) fun T g hT _ => by
    rw [hfP T g hT, decide_eq_true_iff]).symm

theorem rep_arrOf (g : Equiv.Perm (Fin 693)) : CFSG.Monster.B.Co2.Rep 693 (arrOf g) g :=
  fun x => CFSG.Monster.B.Co2.getElem!_ofFn_nat _ x.2

theorem co2Rep_of_rep {T : Table} {g : Equiv.Perm (Fin 693)} (h : Rep 693 T g) :
    CFSG.Monster.B.Co2.Rep 693 (T.map UInt32.toNat) g := by
  intro x
  have hx := h x x.2
  rw [idx_of_lt _ x.2, Equiv.Perm.smul_def] at hx
  rw [← hx, ap]
  by_cases hlt : (x : ℕ) < T.size
  · rw [getElem!_pos (T.map UInt32.toNat) (x : ℕ) (by simpa using hlt),
      getElem!_pos T (x : ℕ) hlt, Array.getElem_map]
  · rw [getElem!_neg (T.map UInt32.toNat) (x : ℕ) (by simpa using hlt),
      getElem!_neg T (x : ℕ) hlt]
    rfl

theorem stabilizer_eq_of_le {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] (Δ : Set Ω)
    (H : Subgroup G) (hH : H ≤ MulAction.stabilizer G Δ)
    (horb : H.index ≤ (Set.range fun g : G => g • Δ).ncard) :
    MulAction.stabilizer G Δ = H := by
  have hidx : H.index ≤ (MulAction.stabilizer G Δ).index := by
    rw [MulAction.index_stabilizer]
    exact horb
  have h1 := Subgroup.relIndex_mul_index hH
  have hS0 : (MulAction.stabilizer G Δ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hR1 : H.relIndex (MulAction.stabilizer G Δ) = 1 := by
    rcases Nat.lt_or_ge (H.relIndex (MulAction.stabilizer G Δ)) 2 with h | h
    · have h0 : H.relIndex (MulAction.stabilizer G Δ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact Subgroup.index_ne_zero_of_finite h1.symm
      omega
    · have : 2 * (MulAction.stabilizer G Δ).index ≤ H.index := by
        rw [← h1]
        exact Nat.mul_le_mul_right _ h
      omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hR1) hH

theorem card_T46_eq :
    Nat.card T46 = 9196830720 := card_T46

open CFSG.ComponentClassification.PSL3Four in
def betaF (i : Fin 42) : Fin 693 := ⟨beta[i.val]! % 693, Nat.mod_lt _ (by norm_num)⟩

def InOmega (x : Fin 693) : Prop := ∃ i : Fin 42, betaF i = x

open CFSG.ComponentClassification.PSL3Four in
theorem lieModel_of_mulEquiv_S {H : Type} [Group H] (e' : H ≃* S) :
    CFSG.Blueprint.LieModel H .PSL 3 2 2 := by
  obtain ⟨hadm, F, hF, hfin, hcard, ⟨e⟩⟩ := statedClassicalModel_S
  exact Or.inl ⟨by decide, hadm, F, hF, hfin, hcard, ⟨e'.trans e⟩⟩

end CFSG.EvenSmallLie.UnitarySix
