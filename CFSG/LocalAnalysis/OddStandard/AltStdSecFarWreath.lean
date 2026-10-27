module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdBalAct
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Wreath

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_not_comm_of_isComponent {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    ∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hJ.1
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', a'.2, b', b'.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext h

omit [Finite X] in
theorem le_layer_of_isComponent {J : Subgroup X} (hJ : CFSG.IsComponent J) : J ≤ CFSG.layer X :=
  le_sSup (show J ∈ {K : Subgroup X | CFSG.IsComponent K} from hJ)

theorem eq_or_eq_of_isComponent_of_layer {K K' J : Subgroup X} (hK : CFSG.IsComponent K)
    (hK' : CFSG.IsComponent K') (hlay : CFSG.layer X = K ⊔ K') (hJ : CFSG.IsComponent J) :
    J = K ∨ J = K' := by
  by_contra hne
  push Not at hne
  obtain ⟨hJK, hJK'⟩ := hne
  have h1 : ⁅J, K⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hJ hK).resolve_left hJK
  have h2 : ⁅J, K'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hJ hK').resolve_left hJK'
  have hc : K ⊔ K' ≤ centralizer (J : Set X) := by
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
    · rw [← Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
  obtain ⟨a, ha, b, hb, hab⟩ := exists_not_comm_of_isComponent hJ
  have hbl : b ∈ K ⊔ K' := hlay ▸ le_layer_of_isComponent hJ hb
  exact hab (mem_centralizer_iff.1 (hc hbl) a ha)

omit [Finite X] in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup X} {g : X}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ normalizer (K : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    rw [← this]
    exact hy

omit [Finite X] in
theorem map_conj_map_conj (K : Subgroup X) (a b : X) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite X] in
theorem map_conj_eq_of_odd {K₁ K₂ : Subgroup X} (hne : K₁ ≠ K₂)
    (h₁ : ∀ g : X, K₁.map (MulAut.conj g).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj g).toMonoidHom = K₂)
    (h₂ : ∀ g : X, K₂.map (MulAut.conj g).toMonoidHom = K₁ ∨
      K₂.map (MulAut.conj g).toMonoidHom = K₂) {l : X} (hl : Odd (orderOf l)) :
    K₁.map (MulAut.conj l).toMonoidHom = K₁ := by
  have hinj : ∀ g : X, Function.Injective (Subgroup.map (MulAut.conj g).toMonoidHom) :=
    fun g => Subgroup.map_injective (MulAut.conj g).injective
  have hsq : K₁.map (MulAut.conj (l * l)).toMonoidHom = K₁ := by
    rcases h₁ l with h | h
    · rw [← map_conj_map_conj, h, h]
    · rw [← map_conj_map_conj, h]
      rcases h₂ l with h' | h'
      · exact h'
      · exact absurd (hinj l (h.trans h'.symm)) hne
  have hpow : ∀ k : ℕ, K₁.map (MulAut.conj ((l * l) ^ k)).toMonoidHom = K₁ := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x, hx, by simp⟩
    | succ k ih =>
      rw [pow_succ, ← map_conj_map_conj, hsq, ih]
  obtain ⟨k, hk⟩ := hl
  have hl' : l = (l * l) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    calc l = l ^ (orderOf l) * l := by rw [pow_orderOf_eq_one, one_mul]
      _ = l ^ (2 * (k + 1)) := by rw [← pow_succ, hk]; ring_nf
  rw [hl']
  exact hpow (k + 1)

theorem le_centralizer_of_simple_of_card_lt {J L : Subgroup X} {m : ℕ} (hm5 : 5 ≤ m)
    (hm6 : m ≠ 6) (eJ : J ≃* alternatingGroup (Fin m)) [IsSimpleGroup L]
    (hLJ : L ≤ normalizer (J : Set X)) (hcard : m.factorial < Nat.card L) :
    L ≤ centralizer (J : Set X) := by
  classical
  let f : L →* MulAut J := (AltStdBal.normAct J).comp (Subgroup.inclusion hLJ)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hker | hker
  · exfalso
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hker
    have h1 := Nat.card_le_card_of_injective f hinj
    have h2 : Nat.card (MulAut J) = m.factorial := by
      rw [Nat.card_congr (MulAut.congr eJ).toEquiv,
        ← Nat.card_congr (Equiv.ofBijective _
          (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5 hm6)),
        Nat.card_perm, Nat.card_fin]
    omega
  · intro l hl
    have hlk : (⟨l, hl⟩ : L) ∈ f.ker := hker ▸ mem_top _
    rw [MonoidHom.mem_ker] at hlk
    rw [mem_centralizer_iff]
    intro j hj
    have h1 := congrArg (fun φ : MulAut J => ((φ ⟨j, hj⟩ : J) : X)) hlk
    change ((AltStdBal.normAct J (Subgroup.inclusion hLJ ⟨l, hl⟩) ⟨j, hj⟩ : J) : X) = j at h1
    rw [AltStdBal.coe_normAct_apply] at h1
    change l * j * l⁻¹ = j at h1
    calc j * l = l * j * l⁻¹ * l := by rw [h1]
      _ = l * j := by group

theorem false_of_wreath_of_big {t : X} {A : Subgroup X} {m : ℕ} (hm : 7 ≤ m)
    (hW : WreathOutcome t A m) {L : Subgroup X} [IsSimpleGroup L]
    (hodd : closure {x : L | Odd (orderOf x)} = ⊤) (hAL : A ≤ L)
    (hcard : m.factorial < Nat.card L) (hA : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) : False := by
  obtain ⟨K, hKc, hKne, hlay, ⟨eK⟩, hdiag⟩ := hW
  set K' : Subgroup X := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
  have hcomp : ∀ J : Subgroup X, CFSG.IsComponent J → J = K ∨ J = K' :=
    fun J hJ => eq_or_eq_of_isComponent_of_layer hKc hK'c hlay hJ
  have h₁ : ∀ g : X, K.map (MulAut.conj g).toMonoidHom = K ∨
      K.map (MulAut.conj g).toMonoidHom = K' :=
    fun g => hcomp _ (CFSG.LocalCores.isComponent_map_mulEquiv _ hKc)
  have h₂ : ∀ g : X, K'.map (MulAut.conj g).toMonoidHom = K ∨
      K'.map (MulAut.conj g).toMonoidHom = K' :=
    fun g => hcomp _ (CFSG.LocalCores.isComponent_map_mulEquiv _ hK'c)
  have hne : K ≠ K' := fun h => hKne h.symm
  have hnorm : ∀ {J₁ J₂ : Subgroup X}, J₁ ≠ J₂ →
      (∀ g : X, J₁.map (MulAut.conj g).toMonoidHom = J₁ ∨
        J₁.map (MulAut.conj g).toMonoidHom = J₂) →
      (∀ g : X, J₂.map (MulAut.conj g).toMonoidHom = J₁ ∨
        J₂.map (MulAut.conj g).toMonoidHom = J₂) →
      L ≤ normalizer (J₁ : Set X) := by
    intro J₁ J₂ hJ hJ₁ hJ₂ l hl
    have hle : closure {x : L | Odd (orderOf x)} ≤ (normalizer (J₁ : Set X)).subgroupOf L := by
      rw [closure_le]
      intro x hx
      have hx' : Odd (orderOf (x : X)) := by rw [Subgroup.orderOf_coe]; exact hx
      exact mem_normalizer_of_map_conj_eq (map_conj_eq_of_odd hJ hJ₁ hJ₂ hx')
    rw [hodd] at hle
    exact hle (mem_top (⟨l, hl⟩ : L))
  have hLK : L ≤ normalizer (K : Set X) := hnorm hne h₁ h₂
  have hLK' : L ≤ normalizer (K' : Set X) :=
    hnorm (fun h => hne h.symm) (fun g => (h₂ g).symm) (fun g => (h₁ g).symm)
  have hcent : ∀ {J : Subgroup X} (eJ : J ≃* alternatingGroup (Fin m)),
      L ≤ normalizer (J : Set X) → L ≤ centralizer (J : Set X) := fun eJ hLJ =>
    le_centralizer_of_simple_of_card_lt (by omega) (by omega) eJ hLJ hcard
  have eK' : K' ≃* alternatingGroup (Fin m) :=
    (K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans eK
  have hcK := hcent eK hLK
  have hcK' := hcent eK' hLK'
  have hcL : L ≤ centralizer ((K ⊔ K' : Subgroup X) : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff]; exact hcK
    · rw [← Subgroup.le_centralizer_iff]; exact hcK'
  have hAlay : ∀ a ∈ A, a ∈ K ⊔ K' := by
    intro a ha
    have ha' : a ∈ (A : Set X) := ha
    rw [hdiag] at ha'
    obtain ⟨k, hk, rfl⟩ := ha'
    refine mul_mem (le_sup_left (a := K) hk) (le_sup_right (b := K') ?_)
    exact ⟨k, hk, by simp [MulAut.conj_apply]⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hA
  exact hab (mem_centralizer_iff.1 (hcL (hAL hb)) a (hAlay a ha))

end Wreath

section Index

variable {X : Type*} [Group X]

theorem mem_of_odd_of_index_two {W : Subgroup X} (hW : W.index = 2) {x : X}
    (hx : Odd (orderOf x)) : x ∈ W := by
  have hsq : ∀ y : X, y * y ∈ W := fun y => by
    have := Subgroup.sq_mem_of_index_two hW y
    rwa [pow_two] at this
  obtain ⟨k, hk⟩ := hx
  have hxk : x = (x * x) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    calc x = x ^ (orderOf x) * x := by rw [pow_orderOf_eq_one, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [← pow_succ, hk]; ring_nf
  rw [hxk]
  exact pow_mem (hsq x) _

end Index

end CFSG.OddStandard.AltStdSec
