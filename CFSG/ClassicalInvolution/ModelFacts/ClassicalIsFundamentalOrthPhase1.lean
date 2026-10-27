module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplitProd

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {F V : Type} [Field F] [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {K : Type} [Group K] [Finite K] (θ : K →* (V ≃ₗ[F] V))

structure ImageFacts (Q : QuadraticForm F V) (θ : K →* (V ≃ₗ[F] V)) (L : Subgroup K) (z : K) :
    Prop where
  mem_orthogonalGroup : θ z ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  mul_self : θ z * θ z = 1
  orderOf_eq_two : orderOf (θ z) = 2
  perfect : ⁅L.map θ, L.map θ⁆ = L.map θ
  subnormal : IsSubnormal (L.map θ) ((Subgroup.centralizer ({z} : Set K)).map θ)
  le_nM : L.map θ ≤ nM Q (θ z)
  mem : θ z ∈ L.map θ
  unique : ∀ a ∈ L.map θ, ∀ b ∈ L.map θ, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b
  le_map_centralizer : ∀ {N : Subgroup (V ≃ₗ[F] V)}, N ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
    N ≤ Subgroup.centralizer ({θ z} : Set (V ≃ₗ[F] V)) → ⁅N, N⁆ = N →
    N ≤ (Subgroup.centralizer ({z} : Set K)).map θ

theorem imageFacts_of_isClassicalMember [Finite (V ≃ₗ[F] V)] (h2 : (2 : F) ≠ 0)
    (hker : θ.ker ≤ Subgroup.center K) (hker2 : ∀ c ∈ θ.ker, c * c = 1)
    (hrange : θ.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hodd : Odd (Nat.card (GaloisField p f))) {L : Subgroup K} {z : K}
    (h : IsClassicalMember p f L z) (hz : θ z ≠ 1) : ImageFacts Q θ L z := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set i := θ z with hi_def
  have hrangeO : θ.range ≤ O := by
    rw [hrange]
    exact Subgroup.commutator_le_of_le le_rfl le_rfl
  have hiO : i ∈ O := hrangeO ⟨z, rfl⟩
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hii : i * i = 1 := by rw [hi_def, ← map_mul, hz2, map_one]
  have hi2 : orderOf i = 2 := orderOf_eq_prime (by rw [pow_two]; exact hii) hz
  have hLinf := inf_ker_eq_bot_of_isClassicalMember θ hker hker2 hodd h hz
  set A := L.map θ with hA_def
  have hAperf : ⁅A, A⁆ = A := by
    rw [hA_def, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp h.perfect]
  set T := (Subgroup.centralizer ({z} : Set K)).map θ with hT_def
  have hsub : IsSubnormal A T := isSubnormal_map θ h.subnormal
  have hLC : L ≤ Subgroup.centralizer ({z} : Set K) := isSubnormal_le h.subnormal
  have hAC : A ≤ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw, hi_def, ← map_mul, ← map_mul]
    exact congrArg θ (Subgroup.mem_centralizer_iff.mp (hLC hx) z (Set.mem_singleton z))
  have hAO : A ≤ O := fun a ha => by
    obtain ⟨x, -, rfl⟩ := ha
    exact hrangeO ⟨x, rfl⟩
  have hAHle : A ≤ O ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) := le_inf hAO hAC
  have hN : ∀ {N : Subgroup (V ≃ₗ[F] V)}, N ≤ O → N ≤ Subgroup.centralizer ({i} : Set _) →
      ⁅N, N⁆ = N → N ≤ T := fun hNO hNC hNp =>
    le_map_centralizer_of_isPerfect θ hker hrange z hNO hNC hNp
  set N₁ := perfectCore (nP Q i) with hN₁_def
  set N₂ := perfectCore (nM Q i) with hN₂_def
  have hN₁T : N₁ ≤ T :=
    hN ((perfectCore_le _).trans nP_le_orthogonalGroup) ((perfectCore_le _).trans nP_le_centralizer)
      (perfectCore_perfect _)
  have hN₂T : N₂ ≤ T :=
    hN ((perfectCore_le _).trans nM_le_orthogonalGroup) ((perfectCore_le _).trans nM_le_centralizer)
      (perfectCore_perfect _)
  have hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x := fun x hx y hy =>
    nP_comm_nM h2 hii (perfectCore_le _ hx) (perfectCore_le _ hy)
  have hdisj : ∀ x ∈ N₁, x ∈ N₂ → x = 1 := fun x hx hx' =>
    eq_one_of_mem_nP_of_mem_nM h2 hii (perfectCore_le _ hx) (perfectCore_le _ hx')
  have hperfA : Group.IsPerfect A := Subgroup.isPerfect_iff.mpr hAperf
  have hdec : ∀ a ∈ A, ∃ n ∈ N₁, ∃ m ∈ N₂, a = n * m := by
    let φ : A →* (V ≃ₗ[F] V) := (blockP h2 hii).comp (Subgroup.inclusion hAHle)
    let ψ : A →* (V ≃ₗ[F] V) := (blockM h2 hii).comp (Subgroup.inclusion hAHle)
    have hφ : φ.range ≤ N₁ := by
      have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
      exact le_perfectCore (fun r ⟨a, ha⟩ => ha ▸ blockP_mem_nP h2 hii hiO _)
        (Subgroup.isPerfect_iff.mp this)
    have hψ : ψ.range ≤ N₂ := by
      have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
      exact le_perfectCore (fun r ⟨a, ha⟩ => ha ▸ blockM_mem_nM h2 hii hiO _)
        (Subgroup.isPerfect_iff.mp this)
    intro a ha
    refine ⟨φ ⟨a, ha⟩, hφ ⟨⟨a, ha⟩, rfl⟩, ψ ⟨a, ha⟩, hψ ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    exact (blockP_mul_blockM h2 hii ⟨a, hAHle ha⟩).symm
  have huniq := uniqueInvolution_map θ hodd h hLinf
  have hiA : i ∈ A := ⟨z, h.mem, rfl⟩
  have hiM : i ∈ nM Q i := ⟨hiO, rfl, fun v hv => mem_plusSp.mp hv⟩
  have hi' : ∀ n ∈ N₁, ∀ m ∈ N₂, i = n * m → n = 1 := by
    intro n hn m hm hnm
    have hnP : n ∈ nP Q i := perfectCore_le _ hn
    have hmM : m ∈ nM Q i := perfectCore_le _ hm
    have hnM : n ∈ nM Q i := by
      have : n = i * m⁻¹ := by rw [hnm]; group
      rw [this]
      exact (nM Q i).mul_mem hiM ((nM Q i).inv_mem hmM)
    exact eq_one_of_mem_nP_of_mem_nM h2 hii hnP hnM
  have hAN₂ : A ≤ N₂ :=
    le_of_isSubnormal_perfect_of_uniqueInvolution hN₁T hN₂T hcomm hdisj hAperf hsub hdec huniq hiA
      hi2 hi'
  exact ⟨hiO, hii, hi2, hAperf, hsub, fun a ha => perfectCore_le _ (hAN₂ ha), hiA, huniq, hN⟩

end CFSG.ClassicalInvolution.ModelFacts
