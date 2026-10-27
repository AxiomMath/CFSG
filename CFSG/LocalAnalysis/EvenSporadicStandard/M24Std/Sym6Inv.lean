module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Sign
public import Certificates.Certificate24866

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

@[expose] def TetPair (p : S24 × Equiv.Perm (Fin 6)) : Prop :=
  QdNorm p.1 ∧ ∀ i : Fin 6, tetIdx ((p.1 : Equiv.Perm (Fin 24)) (tetRep i)) = p.2 i

theorem tetPair_one : TetPair (1, 1) :=
  ⟨fun s => by simp, fun i => by simp [tetIdx_tetRep]⟩

theorem mem_foldl_addNew {x : S24 × Equiv.Perm (Fin 6)} :
    ∀ (l acc : List (S24 × Equiv.Perm (Fin 6))), x ∈ l.foldl addNew acc → x ∈ acc ∨ x ∈ l
  | [], _, h => Or.inl h
  | c :: l, acc, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_addNew l (addNew acc c) h with h1 | h1
    · unfold addNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · rw [List.mem_singleton.1 h2]
          exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem tetPair_gens : ∀ g ∈ symGens, TetPair g := by
  intro g hg
  simp only [symGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨qdNorm_sxS, fun i => by rw [← tetAct_apply qdNorm_sxS, tetAct_sxS]⟩
  · exact ⟨qdNorm_sxT, fun i => by rw [← tetAct_apply qdNorm_sxT, tetAct_sxT]⟩

theorem tetPair_mul {g p : S24 × Equiv.Perm (Fin 6)} (hg : TetPair g) (hp : TetPair p) :
    TetPair (normH NativeSporadic.M24 (g.1 * p.1), tab (g.2 * p.2)) := by
  refine ⟨?_, fun i => ?_⟩
  · show QdNorm (normH NativeSporadic.M24 (g.1 * p.1))
    rw [normH_eq]
    exact hg.1.mul hp.1
  · show tetIdx (((normH NativeSporadic.M24 (g.1 * p.1) : S24) : Equiv.Perm (Fin 24))
      (tetRep i)) = tab (g.2 * p.2) i
    rw [normH_eq, tab_eq, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ← tetAct_tetIdx hg.1, hp.2 i, tetAct_apply, hg.2]

theorem tetPair_symStep
    {st : List (S24 × Equiv.Perm (Fin 6)) × List (S24 × Equiv.Perm (Fin 6))}
    (h1 : ∀ x ∈ st.1, TetPair x) (h2 : ∀ x ∈ st.2, TetPair x) :
    (∀ x ∈ (symStep st).1, TetPair x) ∧ ∀ x ∈ (symStep st).2, TetPair x := by
  have key : ∀ x ∈ (symStep st).1, TetPair x := by
    intro x hx
    rcases mem_foldl_addNew _ _ hx with hx | hx
    · exact h1 x hx
    · obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      exact tetPair_mul (tetPair_gens g hg) (h2 p hp)
  exact ⟨key, fun x hx => key x (List.mem_of_mem_drop hx)⟩

theorem tetPair_iterate : ∀ n : ℕ, (∀ x ∈ (symStep^[n] ([(1, 1)], [(1, 1)])).1, TetPair x) ∧
    ∀ x ∈ (symStep^[n] ([(1, 1)], [(1, 1)])).2, TetPair x
  | 0 => ⟨fun x hx => by rw [List.mem_singleton.1 hx]; exact tetPair_one,
      fun x hx => by rw [List.mem_singleton.1 hx]; exact tetPair_one⟩
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact tetPair_symStep (tetPair_iterate n).1 (tetPair_iterate n).2

theorem tetPair_of_mem {p : S24 × Equiv.Perm (Fin 6)} (hp : p ∈ sym6T) : TetPair p :=
  (tetPair_iterate 20).1 p hp

theorem length_fix_of_involution
    {g : S24} (hg : QdNorm g)
    (hgg : g * g = 1) (hgE : g ∉ m24E1l) :
    (m24E1l.filter fun x => decide (g * x * g⁻¹ = x)).length =
      if Equiv.Perm.sign (tetAct g hg) = 1 then 16 else 8 := by
  obtain ⟨hcov, hinv, -⟩ := Certificates.certificate24866
  obtain ⟨p, hp, hpσ⟩ := hcov (tetAct g hg)
  obtain ⟨hpN, hpT⟩ := tetPair_of_mem hp
  have hpA : tetAct p.1 hpN = tetAct g hg := by
    rw [← hpσ]
    exact Equiv.ext fun i => hpT i
  have hkN : QdNorm (g * p.1⁻¹) := hg.mul (qdNorm_inv hpN)
  have hkfix : ∀ q : Fin 24,
      tetIdx (((g * p.1⁻¹ : S24) : Equiv.Perm (Fin 24)) q) = tetIdx q := by
    intro q
    have h1 : tetAct p.1 hpN (tetIdx (((p.1⁻¹ : S24) : Equiv.Perm (Fin 24)) q)) = tetIdx q := by
      rw [tetAct_tetIdx, Subgroup.coe_inv, perm_apply_inv]
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, ← tetAct_tetIdx hg, ← hpA, h1]
  have hkK := mem_sxK0_of_fix hkN hkfix
  have hkp : g * p.1⁻¹ * p.1 = g := by group
  have hσ2 : p.2 * p.2 = 1 := by
    rw [hpσ, ← tetAct_mul hg hg]
    exact (tetAct_eq_one_iff (hg.mul hg)).2 fun q => by rw [hgg]; rfl
  have h := hinv p hp hσ2 _ hkK (by rw [hkp]; exact hgg) (by rw [hkp]; exact hgE)
  rw [hkp] at h
  rw [h, hpσ]

end CFSG.EvenSporadicStandard.M24Std.Sym6

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

variable {G : Type} [Group G] {L A : Subgroup G} {e : L ≃* S24}
  (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l)
include hA

theorem card_fix_tetE (hAL : A ≤ L) (t : egNL L A) (htt : t * t = 1) (htA : (t : G) ∉ A) :
    Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} =
      if Equiv.Perm.sign (tetE hA t) = 1 then 16 else 8 := by
  have hgN := nlE_norm hA t
  have hgg : nlE e t * nlE e t = 1 := by rw [← map_mul, htt, map_one]
  have hgE : nlE e t ∉ m24E1l := fun h =>
    htA ((hA (Subgroup.inclusion (inf_le_right : egNL L A ≤ L) t)).2 h)
  rw [show tetE hA t = tetAct (nlE e t) hgN from rfl,
    ← length_fix_of_involution hgN hgg hgE]
  refine card_eq_length (fun a : A => (t : G) * a * (t : G)⁻¹ = a)
    (fun a => e ⟨a, hAL a.2⟩) ?_ _ (m24_e1_check.2.1.filter _) fun b => ?_
  · intro a a' h
    exact Subtype.ext (congrArg (fun y : L => (y : G)) (e.injective h))
  · simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨hb, hbf⟩
      refine ⟨⟨qdIota e b, (qdIota_mem_A e hA b).2 hb⟩, ?_, ?_⟩
      · show (t : G) * qdIota e b * (t : G)⁻¹ = qdIota e b
        rw [← qdIota_nlE e t, qdIota_conj, hbf]
      · have h1 : (⟨qdIota e b, hAL ((qdIota_mem_A e hA b).2 hb)⟩ : L) = e.symm b :=
          Subtype.ext rfl
        show e ⟨qdIota e b, _⟩ = b
        rw [h1, MulEquiv.apply_symm_apply]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨(hA ⟨a, hAL a.2⟩).1 a.2, qdIota_injective e ?_⟩
      rw [map_mul, map_mul, map_inv, qdIota_nlE, qdIota_apply]
      exact ha

theorem card_fix_of_index_two (hAL : A ≤ L) {H : Subgroup (egNL L A)} (hH : H.index = 2)
    (t : egNL L A) (htt : t * t = 1) (htA : (t : G) ∉ A) :
    (t ∈ H → Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 16) ∧
      (t ∉ H → Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 8) := by
  have hmem : t ∈ H ↔ Equiv.Perm.sign (tetE hA t) = 1 := by
    rw [(index_two_iff hA hAL H).1 hH, Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
  rw [card_fix_tetE hA hAL t htt htA]
  exact ⟨fun ht => ite_eq_left (hmem.1 ht), fun ht => ite_eq_right fun h => ht (hmem.2 h)⟩

theorem exists_involution_not_mem (hAL : A ≤ L) :
    ∃ t : egNL L A, t * t = 1 ∧ (t : G) ∉ A ∧ ∀ H : Subgroup (egNL L A), H.index = 2 → t ∉ H := by
  obtain ⟨-, -, k, hk, hks⟩ := Certificates.certificate24866
  have hkfix := (norm_of_mem_sxK0 hk).2
  have hgN : QdNorm (k * sxS) := (norm_of_mem_sxK0 hk).1.mul qdNorm_sxS
  have hmem := qdIota_mem_egNL e hAL hA hgN
  have hte : tetE hA ⟨qdIota e (k * sxS), hmem⟩ = Equiv.swap 0 1 := by
    refine Equiv.ext fun i => ?_
    rw [tetE_apply, nlE_mk, Subgroup.coe_mul, Equiv.Perm.mul_apply, hkfix,
      ← tetAct_apply qdNorm_sxS, tetAct_sxS]
  have hodd : Equiv.Perm.sign (tetE hA ⟨qdIota e (k * sxS), hmem⟩) ≠ 1 := by
    rw [hte, Equiv.Perm.sign_swap (by decide)]
    decide
  refine ⟨⟨qdIota e (k * sxS), hmem⟩, Subtype.ext ?_, fun htA => hodd ?_,
    fun H hH htH => hodd ?_⟩
  · show qdIota e (k * sxS) * qdIota e (k * sxS) = 1
    rw [← map_mul, hks, map_one]
  · have h1 := le_ker_tetE hA (Subgroup.mem_subgroupOf.2 htA)
    rw [MonoidHom.mem_ker] at h1
    rw [h1, map_one]
  · rwa [(index_two_iff hA hAL H).1 hH, Subgroup.mem_comap,
      Equiv.Perm.mem_alternatingGroup] at htH

end CFSG.EvenSporadicStandard.M24Std.Sym6

namespace CFSG.EvenSporadicStandard.M24Std

open Sym6

variable {G : Type} [Group G]

theorem card_fix_involution_of_type
    {L A : Subgroup G} (h : SextetType L A) :
    ∀ H : Subgroup (egNL L A), H.index = 2 → ∀ t : egNL L A, t * t = 1 → (t : G) ∉ A →
      (t ∈ H → Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 16) ∧
        (t ∉ H → Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 8) := by
  obtain ⟨hAL, e, hA⟩ := h
  exact fun H hH t htt htA => card_fix_of_index_two hA hAL hH t htt htA

end CFSG.EvenSporadicStandard.M24Std
