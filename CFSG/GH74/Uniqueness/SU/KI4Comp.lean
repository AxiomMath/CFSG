module

public import CFSG.Goldschmidt.Steps.GoldType

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.Open
open CFSG.Goldschmidt (Omega1)
open CFSG.ComponentClassification.AschbacherToolkit.Bender (mem_sylowCenter sylowCenter_le)

theorem omega1_sq_eq_one_of_comm {Q : Type*} [Group Q] {T : Subgroup Q}
    (hT : IsMulCommutative (Omega1 T)) {u : Q} (hu : u ∈ Omega1 T) : u ^ 2 = 1 := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := congrArg Subtype.val (hT.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hcomm : Commute x y := hxy
    rw [hcomm.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem omega1_comm_of_bender
    {X : Type} [Group X] [Finite X] (hX : fusionIsBenderGroup X)
    (T : Sylow 2 X) : IsMulCommutative (Omega1 (T : Subgroup X)) := by
  rw [CFSG.Goldschmidt.GoldType.omega1_eq_sylowCenter_of_bender hX T]
  exact ⟨⟨fun a b => Subtype.ext ((mem_sylowCenter.mp b.2).2 a (sylowCenter_le _ a.2))⟩⟩

theorem goldschmidt_omega1_data
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hty : goldschmidtSimpleType L) (T : Sylow 2 L) :
    IsMulCommutative (Omega1 (T : Subgroup L)) ∧ 4 ≤ Nat.card (Omega1 (T : Subgroup L)) ∧
      ∀ x ∈ Omega1 (T : Subgroup L), ∀ y ∈ Omega1 (T : Subgroup L), x ≠ 1 → y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer ((Omega1 (T : Subgroup L) : Subgroup L) : Set L),
          n⁻¹ * x * n = y := by
  have hcomm : IsMulCommutative (Omega1 (T : Subgroup L)) := by
    rcases hty with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | h
    · exact omega1_comm_of_bender (Or.inl ⟨f, by omega, ⟨e⟩⟩) T
    · exact omega1_comm_of_bender (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)) T
    · exact omega1_comm_of_bender (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩)) T
    · obtain ⟨hTc, hexp, -, -⟩ := CFSG.Goldschmidt.GoldType.elementary_of_clauses h T
      rw [CFSG.Goldschmidt.GoldType.omega1_eq_self hexp]
      exact hTc
  obtain ⟨h4, htrans⟩ := CFSG.Goldschmidt.N11b L hty T hcomm
  exact ⟨hcomm, h4, htrans⟩

theorem mem_normalizer_comap_of_mem_normalizer {K : Type*} [Group K] {N : Subgroup K} [N.Normal]
    {Ω : Subgroup (K ⧸ N)} {n : K} (hn : (n : K ⧸ N) ∈ Subgroup.normalizer (Ω : Set (K ⧸ N))) :
    n ∈ Subgroup.normalizer ((Ω.comap (QuotientGroup.mk' N) : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  have h := hn (x : K ⧸ N)
  simp only [Subgroup.mem_comap, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv]
  exact h

theorem goldschmidt_component_data
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hty : CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K)) (S₀ : Sylow 2 K) :
    ∃ Ω : Subgroup (K ⧸ Subgroup.center K),
      (∀ x ∈ Ω, x * x = 1) ∧
      Ω ≤ (S₀ : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)) ∧
      (∀ x ∈ (S₀ : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)), x * x = 1 → x ∈ Ω) ∧
      IsMulCommutative Ω ∧ 4 ≤ Nat.card Ω ∧
      ∀ u ∈ Ω, ∀ v ∈ Ω, u ≠ 1 → v ≠ 1 →
        ∃ n : K, n ∈ Subgroup.normalizer ((Ω.comap (QuotientGroup.mk' (Subgroup.center K)) :
            Subgroup K) : Set K) ∧
          ((n : K ⧸ Subgroup.center K))⁻¹ * u * (n : K ⧸ Subgroup.center K) = v := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.1
  obtain ⟨T, hT⟩ : ∃ T : Sylow 2 (K ⧸ Subgroup.center K), (T : Subgroup (K ⧸ Subgroup.center K)) =
      (S₀ : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)) :=
    ⟨S₀.mapSurjective (QuotientGroup.mk'_surjective _), Sylow.coe_mapSurjective _ _⟩
  obtain ⟨hcomm, h4, htrans⟩ := goldschmidt_omega1_data hty T
  refine ⟨Omega1 (T : Subgroup (K ⧸ Subgroup.center K)), fun x hx => ?_, ?_, fun x hx hx2 => ?_,
    hcomm, h4, fun u hu v hv hu1 hv1 => ?_⟩
  · rw [← sq]
    exact omega1_sq_eq_one_of_comm hcomm hx
  · rw [← hT]
    exact CFSG.Goldschmidt.GoldType.omega1_le _
  · rw [← hT] at hx
    exact CFSG.Goldschmidt.GoldType.mem_omega1 hx (by rw [sq]; exact hx2)
  · obtain ⟨n₀, hn₀, hn₀uv⟩ := htrans u hu v hv hu1 hv1
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective n₀
    exact ⟨n, mem_normalizer_comap_of_mem_normalizer hn₀, hn₀uv⟩

end CFSG.GH74.Uniqueness.SU.K.R4
