module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftLocal

public section

open scoped Classical

namespace CFSG.Wreathed.NormalComponentLift

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.BaseFourCentralizerStructure
  CFSG.Wreathed.TorusSplitting

variable {G : Type} [Group G]

theorem le_ambientOddCore {Q H : Subgroup G} (hQH : Q ≤ H)
    (hn : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) (hodd : Odd (Nat.card Q)) :
    Q ≤ ambientOddCore H := by
  have hN : (Q.subgroupOf H).Normal := ⟨fun q hq h => by
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    exact hn h h.2 q hq⟩
  have hodd' : Odd (Nat.card (Q.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv]
  have hle : Q.subgroupOf H ≤ CFSG.oddCore H := le_sSup ⟨hN, hodd'⟩
  intro q hq
  exact ⟨⟨q, hQH hq⟩, hle (Subgroup.mem_subgroupOf.mpr hq), rfl⟩

theorem ambientOddCore_conj_mem_of_mem {H : Subgroup G} {h k : G} (hh : h ∈ H)
    (hk : k ∈ ambientOddCore H) : h * k * h⁻¹ ∈ ambientOddCore H := by
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨⟨h, hh⟩ * k' * (⟨h, hh⟩ : H)⁻¹,
    (inferInstance : (CFSG.oddCore H).Normal).conj_mem k' hk' _, rfl⟩

theorem map_centralizer_singleton {A B : Type*} [Group A] [Group B] (θ : A ≃* B) (a : A) :
    (Subgroup.centralizer {a}).map θ.toMonoidHom = Subgroup.centralizer {θ a} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' := Subgroup.mem_centralizer_singleton_iff.mp hw
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change θ w * θ a = θ a * θ w
    rw [← map_mul, ← map_mul, hw']
  · intro hz
    refine ⟨θ.symm z, ?_, θ.apply_symm_apply z⟩
    have hz' := Subgroup.mem_centralizer_singleton_iff.mp hz
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply θ.injective
    rw [map_mul, map_mul, θ.apply_symm_apply, hz']

variable {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem x_eq_mul :
    wreathModelHom S e (Original.x (2 ^ n)) =
      wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2) *
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2) := by
  rw [Original.x, Original.a, map_pow, map_mul]
  exact (actual_s_t_commute S e).mul_pow _

theorem mem_centralizer_four_iff (c : involutionCentralizer n S e) :
    (c : G) ∈ Subgroup.centralizer (Subgroup.closure
      {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) ↔
      c * nModel n hn S e (Original.x2 (2 ^ n)) = nModel n hn S e (Original.x2 (2 ^ n)) * c := by
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hy
  constructor
  · intro hc
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hc y (x2_mem_four n S e)).symm
  · intro hc
    have hcy : (c : G) * y = y * c := congrArg Subtype.val hc
    have hcx : (c : G) * wreathModelHom S e (Original.x (2 ^ n)) =
        wreathModelHom S e (Original.x (2 ^ n)) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    have hys : y = wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2) := by
      rw [hy, Original.x2, map_pow]
    have hct : (c : G) * wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2) =
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2) * c := by
      have ht : wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2) =
          y⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) := by
        rw [x_eq_mul S e, ← hys, inv_mul_cancel_left]
      rw [ht]
      calc (c : G) * (y⁻¹ * wreathModelHom S e (Original.x (2 ^ n))) =
          (c * y⁻¹) * wreathModelHom S e (Original.x (2 ^ n)) := by group
        _ = (y⁻¹ * c) * wreathModelHom S e (Original.x (2 ^ n)) := by
          rw [show (c : G) * y⁻¹ = y⁻¹ * c by
            rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hcy, mul_assoc, mul_inv_cancel, mul_one]]
        _ = y⁻¹ * ((c : G) * wreathModelHom S e (Original.x (2 ^ n))) := by group
        _ = y⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) * c := by rw [hcx]; group
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hle : Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} ≤
        Subgroup.centralizer {(c : G)} := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      · rw [← hys]
        exact hcy.symm
      · exact hct.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)

end CFSG.Wreathed.NormalComponentLift
