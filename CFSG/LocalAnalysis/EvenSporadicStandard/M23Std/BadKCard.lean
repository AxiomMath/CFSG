module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.BadKStruct

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F : Subgroup G}

omit [Finite G] in
theorem phiv_one_eq (h : OneClassData L z t) : phiv z (1 : G) = 1 := by
  unfold phiv
  simp [h.z_mul_self]

theorem lbad_le_Ksub (h : OneClassData L z t) (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z))
    (D : NData L F) (X : FixedData L F) (hbad : BadK z F) :
    LbadSub h hZ D X hbad ≤ Ksub z F := fun _ hk => hk.1

theorem card_lbad (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) (hbad : BadK z F) : Nat.card (LbadSub h hZ D X hbad) = 256 := by
  let ψ : LbadSub h hZ D X hbad →* F :=
    (phiHom h D).comp (Subgroup.inclusion (lbad_le_Ksub h hZ D X hbad))
  have hψ : ∀ x : LbadSub h hZ D X hbad, ((ψ x : F) : G) = phiv z (x : G) := fun x => rfl
  have hsurj : Function.Surjective ψ := by
    rintro ⟨f, hf⟩
    by_cases hf1 : f = 1
    · refine ⟨1, Subtype.ext ?_⟩
      rw [hψ]
      exact (phiv_one_eq h).trans hf1.symm
    · obtain ⟨k, hk, hkf⟩ := exists_lbad_over h hZ D X htrans hf hf1
      exact ⟨⟨k, hk⟩, Subtype.ext (by rw [hψ]; exact hkf)⟩
  have hker : Nat.card ψ.ker = 16 := by
    rw [← D.F_card]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ψ.ker => (⟨(x.1 : G), ?_⟩ : F)) ⟨?_, ?_⟩)
    · have h1 : phiv z (x.1 : G) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
        rwa [hψ] at this
      exact mem_F_of_lbad_phiv x.1.2 h1
    · intro x y hxy
      have h1 : ((x.1 : LbadSub h hZ D X hbad) : G) = ((y.1 : LbadSub h hZ D X hbad) : G) :=
        congrArg (fun e : F => (e : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨u, hu⟩
      refine ⟨⟨⟨u, F_le_LbadSub h hZ D X hbad hu⟩, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (by rw [hψ]; exact phiv_eq_one_of_mem_F h D hu)
  have := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, D.F_card] at this
  omega

end CFSG.EvenSporadicStandard.M23Std
