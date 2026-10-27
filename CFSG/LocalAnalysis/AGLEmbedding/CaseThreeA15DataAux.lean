module

import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreEmbedding
public import CFSG.Open.LocalVocabulary
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open Equiv

@[expose] def a15PermC (i : Fin 3) : Perm (Fin 15) :=
  let b : Fin 15 := ⟨5 * i.1, by omega⟩
  swap b (b + 4) * swap b (b + 3) * swap b (b + 2) * swap b (b + 1)

@[expose] def a15PermD (i : Fin 3) : Perm (Fin 15) :=
  let b : Fin 15 := ⟨5 * i.1, by omega⟩
  swap (b + 1) (b + 3) * swap (b + 1) (b + 4) * swap (b + 1) (b + 2)

@[expose] def a15PermSigma : Perm (Fin 15) :=
  (swap 0 10 * swap 0 5) * (swap 1 11 * swap 1 6) * (swap 2 12 * swap 2 7) *
    (swap 3 13 * swap 3 8) * (swap 4 14 * swap 4 9)

@[expose] def a15PermTau : Perm (Fin 15) := a15PermD 0 * a15PermD 2

@[expose] def a15PermBase (a b c : ℕ) : Perm (Fin 15) :=
  a15PermC 0 ^ a * a15PermC 1 ^ b * a15PermC 2 ^ c

theorem sign_a15PermC : ∀ i, Perm.sign (a15PermC i) = 1 := by decide

@[expose] def a15c (i : Fin 3) : alternatingGroup (Fin 15) :=
  ⟨a15PermC i, Perm.mem_alternatingGroup.mpr (sign_a15PermC i)⟩

@[expose] def a15σ : alternatingGroup (Fin 15) :=
  ⟨a15PermSigma, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a15τ : alternatingGroup (Fin 15) :=
  ⟨a15PermTau, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem a15c_pow_five (i : Fin 3) : a15c i ^ 5 = 1 :=
  Subtype.ext (show a15PermC i ^ 5 = 1 by revert i; decide)

theorem commute_a15c (i j : Fin 3) : Commute (a15c i) (a15c j) :=
  Subtype.ext (show a15PermC i * a15PermC j = a15PermC j * a15PermC i by revert i j; decide)

theorem coe_a15c_pow (a b c : ℕ) :
    ((a15c 0 ^ a * a15c 1 ^ b * a15c 2 ^ c : alternatingGroup (Fin 15)) : Perm (Fin 15)) =
      a15PermBase a b c := rfl

theorem a15c_pow_mul (a b c a' b' c' : ℕ) :
    a15c 0 ^ a * a15c 1 ^ b * a15c 2 ^ c * (a15c 0 ^ a' * a15c 1 ^ b' * a15c 2 ^ c') =
      a15c 0 ^ (a + a') * a15c 1 ^ (b + b') * a15c 2 ^ (c + c') := by
  simp only [pow_add, mul_assoc]
  rw [((commute_a15c 0 2).pow_pow a' c).symm.left_comm,
    ((commute_a15c 0 1).pow_pow a' b).symm.left_comm,
    ((commute_a15c 1 2).pow_pow b' c).symm.left_comm]

theorem a15c_pow_five_mul (a b c : ℕ) :
    a15c 0 ^ (5 * a) * a15c 1 ^ (5 * b) * a15c 2 ^ (5 * c) = 1 := by
  simp only [pow_mul, a15c_pow_five, one_pow, mul_one]

def a15Base : Subgroup (alternatingGroup (Fin 15)) where
  carrier := {x | ∃ a b c : ℕ, x = a15c 0 ^ a * a15c 1 ^ b * a15c 2 ^ c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b', c + c', a15c_pow_mul a b c a' b' c'⟩
  one_mem' := ⟨0, 0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    refine ⟨4 * a, 4 * b, 4 * c, inv_eq_of_mul_eq_one_right ?_⟩
    rw [a15c_pow_mul, show a + 4 * a = 5 * a by ring, show b + 4 * b = 5 * b by ring,
      show c + 4 * c = 5 * c by ring, a15c_pow_five_mul]

theorem mem_a15Base {x : alternatingGroup (Fin 15)} :
    x ∈ a15Base ↔ ∃ a b c : ℕ, x = a15c 0 ^ a * a15c 1 ^ b * a15c 2 ^ c := Iff.rfl

theorem a15c_mem (i : Fin 3) : a15c i ∈ a15Base := by
  refine mem_a15Base.mpr ?_
  fin_cases i
  · exact ⟨1, 0, 0, by simp⟩
  · exact ⟨0, 1, 0, by simp⟩
  · exact ⟨0, 0, 1, by simp⟩

theorem exists_fin_of_mem_a15Base {x : alternatingGroup (Fin 15)} (hx : x ∈ a15Base) :
    ∃ a b c : Fin 5, x = a15c 0 ^ (a : ℕ) * a15c 1 ^ (b : ℕ) * a15c 2 ^ (c : ℕ) := by
  obtain ⟨a, b, c, rfl⟩ := mem_a15Base.mp hx
  refine ⟨⟨a % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨b % 5, Nat.mod_lt _ (by norm_num)⟩,
    ⟨c % 5, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  rw [pow_eq_pow_mod a (a15c_pow_five 0), pow_eq_pow_mod b (a15c_pow_five 1),
    pow_eq_pow_mod c (a15c_pow_five 2)]

theorem isElemAbelian_a15Base : Open.IsElemAbelian 5 a15Base := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, b, c, hx⟩ := mem_a15Base.mp x.2
    obtain ⟨a', b', c', hy⟩ := mem_a15Base.mp y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy, a15c_pow_mul, a15c_pow_mul, add_comm a,
      add_comm b, add_comm c]
  · obtain ⟨a, b, c, rfl⟩ := mem_a15Base.mp hx
    have hc : Commute (a15c 0 ^ a * a15c 1 ^ b) (a15c 2 ^ c) :=
      ((commute_a15c 0 2).pow_pow a c).mul_left ((commute_a15c 1 2).pow_pow b c)
    rw [hc.mul_pow, ((commute_a15c 0 1).pow_pow a b).mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
      mul_comm a, mul_comm b, mul_comm c, a15c_pow_five_mul]

theorem a15PermBase_apply (a b c : Fin 5) :
    ((a15PermBase a b c) 0 : ℕ) = a ∧ ((a15PermBase a b c) 5 : ℕ) = 5 + b ∧
      ((a15PermBase a b c) 10 : ℕ) = 10 + c := by
  revert a b c
  decide

theorem card_a15Base : Nat.card a15Base = 5 ^ 3 := by
  let f : Fin 5 × Fin 5 × Fin 5 → a15Base := fun t =>
    ⟨a15c 0 ^ (t.1 : ℕ) * a15c 1 ^ (t.2.1 : ℕ) * a15c 2 ^ (t.2.2 : ℕ),
      mem_a15Base.mpr ⟨_, _, _, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s t hst => ?_, fun x => ?_⟩
    · have h : a15PermBase s.1 s.2.1 s.2.2 = a15PermBase t.1 t.2.1 t.2.2 := by
        rw [← coe_a15c_pow, ← coe_a15c_pow]
        exact congrArg (fun x : a15Base => ((x : alternatingGroup (Fin 15)) : Perm (Fin 15))) hst
      obtain ⟨h1, h2, h3⟩ := a15PermBase_apply s.1 s.2.1 s.2.2
      obtain ⟨h1', h2', h3'⟩ := a15PermBase_apply t.1 t.2.1 t.2.2
      rw [h] at h1 h2 h3
      exact Prod.ext (Fin.ext (h1.symm.trans h1')) (Prod.ext (Fin.ext (by omega))
        (Fin.ext (by omega)))
    · obtain ⟨a, b, c, h⟩ := exists_fin_of_mem_a15Base x.2
      exact ⟨(a, b, c), Subtype.ext h.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem closure_range_a15c : Subgroup.closure (Set.range a15c) = a15Base := by
  refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) fun x hx => ?_
  · rintro _ ⟨i, rfl⟩
    exact a15c_mem i
  · obtain ⟨a, b, c, rfl⟩ := mem_a15Base.mp hx
    have h : ∀ i, a15c i ∈ Subgroup.closure (Set.range a15c) := fun i =>
      Subgroup.subset_closure ⟨i, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (h 0) a)
      (Subgroup.pow_mem _ (h 1) b)) (Subgroup.pow_mem _ (h 2) c)

theorem card_alternatingGroup_fifteen :
    Nat.card (alternatingGroup (Fin 15)) = 5 ^ 3 * 5230697472 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem a15σ_conj (i : Fin 3) : a15σ * a15c i * a15σ⁻¹ = a15c (i + 1) :=
  Subtype.ext (show a15PermSigma * a15PermC i * a15PermSigma⁻¹ = a15PermC (i + 1) by
    revert i; decide)

theorem a15τ_conj : a15τ * a15c 0 * a15τ⁻¹ = a15c 0 ^ 2 ∧ a15τ * a15c 1 * a15τ⁻¹ = a15c 1 ∧
    a15τ * a15c 2 * a15τ⁻¹ = a15c 2 ^ 2 :=
  ⟨Subtype.ext (show a15PermTau * a15PermC 0 * a15PermTau⁻¹ = a15PermC 0 ^ 2 by decide),
    Subtype.ext (show a15PermTau * a15PermC 1 * a15PermTau⁻¹ = a15PermC 1 by decide),
    Subtype.ext (show a15PermTau * a15PermC 2 * a15PermTau⁻¹ = a15PermC 2 ^ 2 by decide)⟩

theorem a15PermSigma_conj (a b c : Fin 5) :
    a15PermSigma * a15PermBase a b c * a15PermSigma⁻¹ = a15PermBase c a b := by
  revert a b c
  decide

theorem a15PermSigma_conj_inv (a b c : Fin 5) :
    a15PermSigma⁻¹ * a15PermBase a b c * a15PermSigma = a15PermBase b c a := by
  revert a b c
  decide

theorem a15PermTau_conj (a b c : Fin 5) :
    a15PermTau * a15PermBase a b c * a15PermTau⁻¹ = a15PermBase (2 * a) b (2 * c) := by
  revert a b c
  decide

theorem a15PermTau_conj_inv (a b c : Fin 5) :
    a15PermTau⁻¹ * a15PermBase a b c * a15PermTau = a15PermBase (3 * a) b (3 * c) := by
  revert a b c
  decide

theorem mem_normalizer_a15Base {g : alternatingGroup (Fin 15)}
    (h : ∀ a b c : Fin 5, ∃ a' b' c' : ℕ,
      (g : Perm (Fin 15)) * a15PermBase a b c * (g : Perm (Fin 15))⁻¹ = a15PermBase a' b' c')
    (h' : ∀ a b c : Fin 5, ∃ a' b' c' : ℕ,
      (g : Perm (Fin 15))⁻¹ * a15PermBase a b c * (g : Perm (Fin 15)) = a15PermBase a' b' c') :
    g ∈ Subgroup.normalizer (a15Base : Set (alternatingGroup (Fin 15))) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨a, b, c, rfl⟩ := exists_fin_of_mem_a15Base hx
    obtain ⟨a', b', c', e⟩ := h a b c
    exact mem_a15Base.mpr ⟨a', b', c', Subtype.ext (e.trans (coe_a15c_pow a' b' c').symm)⟩
  · obtain ⟨a, b, c, e₀⟩ := exists_fin_of_mem_a15Base hx
    obtain ⟨a', b', c', e⟩ := h' a b c
    have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    refine mem_a15Base.mpr ⟨a', b', c', ?_⟩
    rw [hx', e₀]
    exact Subtype.ext (e.trans (coe_a15c_pow a' b' c').symm)

theorem a15σ_mem_normalizer :
    a15σ ∈ Subgroup.normalizer (a15Base : Set (alternatingGroup (Fin 15))) :=
  mem_normalizer_a15Base (fun a b c => ⟨c, a, b, a15PermSigma_conj a b c⟩)
    fun a b c => ⟨b, c, a, a15PermSigma_conj_inv a b c⟩

theorem a15τ_mem_normalizer :
    a15τ ∈ Subgroup.normalizer (a15Base : Set (alternatingGroup (Fin 15))) :=
  mem_normalizer_a15Base (fun a b c => ⟨2 * a, b, 2 * c, a15PermTau_conj a b c⟩)
    fun a b c => ⟨3 * a, b, 3 * c, a15PermTau_conj_inv a b c⟩

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem exists_injective_map_a15Base_eq {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (e : K ≃* alternatingGroup (Fin 15)) (T : Sylow 5 Y) (hTK : (T : Subgroup Y) ≤ K) :
    ∃ ψ : alternatingGroup (Fin 15) →* Y, Function.Injective ψ ∧ (∀ x, ψ x ∈ K) ∧
      a15Base.map ψ = T := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card K = 5 ^ 3 * 5230697472 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fifteen]
  have hm : ¬ 5 ∣ 5230697472 := by norm_num
  set Q : Subgroup K := a15Base.map e.symm.toMonoidHom with hQ
  have hQcard : Nat.card Q = 5 ^ 3 := by
    rw [hQ, Subgroup.card_map_of_injective e.symm.injective, card_a15Base]
  obtain ⟨S, hQS⟩ := (IsPGroup.of_card hQcard).exists_le_sylow
  have hQS' : Q = S := Subgroup.eq_of_le_of_card_ge hQS
    (by rw [hQcard, card_sylow_eq_pow_of_card_eq hcard hm S])
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S (T.subtype hTK)
  have h1 := congrArg (fun S : Sylow 5 K => (S : Subgroup K)) hk
  simp only [sylow_conjugate_eq_map, Sylow.coe_subtype] at h1
  refine ⟨K.subtype.comp ((MulAut.conj k).toMonoidHom.comp e.symm.toMonoidHom),
    K.subtype_injective.comp ((MulAut.conj k).injective.comp e.symm.injective),
    fun x => (_ : K).2, ?_⟩
  rw [← Subgroup.map_map, ← Subgroup.map_map, ← hQ, hQS', h1,
    Subgroup.map_subgroupOf_eq_of_le hTK]

end CFSG.AGLEmbedding
