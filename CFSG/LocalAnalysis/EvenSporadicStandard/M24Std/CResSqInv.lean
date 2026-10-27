module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Inv
public import Certificates.Certificate25731

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint


theorem length_fix_of_sq_mem {g : S24} (hg : QdNorm g) (hgg : g * g ∈ m24E1l)
    (hgE : g ∉ m24E1l) :
    (m24E1l.filter fun x => decide (g * x * g⁻¹ = x)).length =
      if Equiv.Perm.sign (tetAct g hg) = 1 then 16 else 8 := by
  obtain ⟨hcov, -, -⟩ := Certificates.certificate24866
  have hinv := Certificates.certificate25731
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
    exact (tetAct_eq_one_iff (hg.mul hg)).2 (tetIdx_of_mem hgg)
  have h := hinv p hp hσ2 _ hkK (by rw [hkp]; exact hgg) (by rw [hkp]; exact hgE)
  rw [hkp] at h
  rw [h, hpσ]

variable {G : Type} [Group G] {L A : Subgroup G} {e : L ≃* S24}
  (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l)
include hA

theorem card_fix_tetE_sq (hAL : A ≤ L) (t : egNL L A) (htt : (t : G) * t ∈ A)
    (htA : (t : G) ∉ A) :
    Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} =
      if Equiv.Perm.sign (tetE hA t) = 1 then 16 else 8 := by
  have hgN := nlE_norm hA t
  have hgg : nlE e t * nlE e t ∈ m24E1l := by
    have h1 : ((t * t : egNL L A) : G) ∈ A := htt
    have h2 := (hA (Subgroup.inclusion (inf_le_right : egNL L A ≤ L) (t * t))).1 h1
    have h3 : nlE e t * nlE e t = nlE e (t * t) := (map_mul _ _ _).symm
    rw [h3]
    exact h2
  have hgE : nlE e t ∉ m24E1l := fun h =>
    htA ((hA (Subgroup.inclusion (inf_le_right : egNL L A ≤ L) t)).2 h)
  rw [show tetE hA t = tetAct (nlE e t) hgN from rfl,
    ← length_fix_of_sq_mem hgN hgg hgE]
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

theorem card_fix_of_sq_mem_of_index_two (hAL : A ≤ L) {H : Subgroup (egNL L A)}
    (hH : H.index = 2) (t : egNL L A) (htt : (t : G) * t ∈ A) (htA : (t : G) ∉ A) :
    (t ∈ H → Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 16) ∧
      (t ∉ H → Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 8) := by
  have hmem : t ∈ H ↔ Equiv.Perm.sign (tetE hA t) = 1 := by
    rw [(index_two_iff hA hAL H).1 hH, Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
  rw [card_fix_tetE_sq hA hAL t htt htA]
  exact ⟨fun ht => ite_eq_left (hmem.1 ht), fun ht => ite_eq_right fun h => ht (hmem.2 h)⟩

end CFSG.EvenSporadicStandard.M24Std.Sym6

namespace CFSG.EvenSporadicStandard.M24Std

open Sym6

variable {G : Type} [Group G]

theorem card_fix_sq_mem_of_type
    {L A : Subgroup G} (h : SextetType L A) :
    ∀ H : Subgroup (egNL L A), H.index = 2 → ∀ t : egNL L A, (t : G) * t ∈ A → (t : G) ∉ A →
      (t ∈ H → Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 16) ∧
        (t ∉ H → Nat.card {a : A // (t : G) * a * (t : G)⁻¹ = a} = 8) := by
  obtain ⟨hAL, e, hA⟩ := h
  exact fun H hH t htt htA => card_fix_of_sq_mem_of_index_two hA hAL hH t htt htA

end CFSG.EvenSporadicStandard.M24Std
