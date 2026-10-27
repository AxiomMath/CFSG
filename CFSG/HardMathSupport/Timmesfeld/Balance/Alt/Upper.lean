module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Perm
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Orbit

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem exists_normal_coprime_map {M M' : Type*} [Group M] [Group M'] [Finite M]
    (ι : M →* M') (p : ℕ) (K : Subgroup M) (z : M) (hz : z ∈ GLAPPrimeCoreOf p K) :
    ∃ N : Subgroup M', N ≤ K.map ι ∧ (N.subgroupOf (K.map ι)).Normal ∧
      Nat.Coprime p (Nat.card N) ∧ ι z ∈ N := by
  set N₀ : Subgroup M := GLAPPrimeCoreOf p K with hN₀
  have hN₀K : N₀ ≤ K := Subgroup.map_subtype_le _
  have hnormK : (N₀.subgroupOf K).Normal := by
    have : N₀.subgroupOf K = GLAPPrimeCore p ↥K := by
      rw [hN₀, GLAPPrimeCoreOf]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [this]
    infer_instance
  have hKnorm : K ≤ Subgroup.normalizer (N₀ : Set M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀K).1 hnormK
  refine ⟨N₀.map ι, Subgroup.map_mono hN₀K, ?_, ?_, ⟨z, hz, rfl⟩⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hN₀K)]
    exact (Subgroup.map_mono hKnorm).trans (Subgroup.le_normalizer_map ι)
  · have h1 : Nat.card (N₀.map ι) ∣ Nat.card N₀ := Subgroup.card_map_dvd N₀ ι
    have h2 : Nat.card N₀ = Nat.card (GLAPPrimeCore p ↥K) := by
      rw [hN₀, GLAPPrimeCoreOf]
      exact Subgroup.card_map_of_injective K.subtype_injective
    rw [h2] at h1
    exact (coprime_card_gLAPPrimeCore_aux p ↥K).coprime_dvd_right h1

theorem isMulCommutative_map {M M' : Type*} [Group M] [Group M'] (ι : M →* M') (A : Subgroup M)
    (h : IsMulCommutative A) : IsMulCommutative (A.map ι) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, hx, hxa⟩ := a.2
  obtain ⟨y, hy, hyb⟩ := b.2
  apply Subtype.ext
  show (a : M') * b = b * a
  rw [← hxa, ← hyb, ← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val (h.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

theorem map_inf_centralizer_singleton {M M' : Type*} [Group M] [Group M'] (ι : M →* M')
    (hι : Function.Injective ι) (H : Subgroup M) (d : M) :
    (H ⊓ Subgroup.centralizer ({d} : Set M)).map ι =
      H.map ι ⊓ Subgroup.centralizer ({ι d} : Set M') := by
  ext y
  constructor
  · rintro ⟨k, ⟨hkH, hkc⟩, rfl⟩
    refine ⟨⟨k, hkH, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    exact congrArg ι (Subgroup.mem_centralizer_iff.1 hkc d rfl)
  · rintro ⟨⟨k, hkH, rfl⟩, hc⟩
    refine ⟨k, ⟨hkH, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply hι
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hc (ι h) rfl

theorem upper_bound_of_delta {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type*} [Group M] {n : ℕ}
    (ι : M →* Equiv.Perm (Fin n)) (hι : Function.Injective ι) (innerM : Subgroup M)
    (hinner : alternatingGroup (Fin n) ≤ innerM.map ι)
    (A D H : Subgroup M) (hDA : D ≤ A) (hA : IsElemAbelian p A) (hD : IsElemAbelian p D)
    (hD3 : Nat.card D = p ^ 3) (hH : innerM ≤ H) (hΔ : localDeltaIn p H D ≠ ⊥) :
    p ^ 3 ≤ n ∧ ∃ β : ℕ, Nat.card A = p ^ β ∧ p ^ 2 * β ≤ n + p ^ 2 := by
  have : Finite M := Finite.of_injective ι hι
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ localDeltaIn p H D, z₀ ≠ 1 := by
    by_contra h
    apply hΔ
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD3
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hDne' : D.map ι ≠ ⊥ := fun h =>
    hDne ((Subgroup.map_eq_bot_iff_of_injective D hι).1 h)
  have hHalt : alternatingGroup (Fin n) ≤ H.map ι :=
    hinner.trans (Subgroup.map_mono hH)
  obtain ⟨F, hF, hFd⟩ := fixedSet_eq_of_delta hp hp2 (D.map ι) (H.map ι)
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hD.2 x hx, map_one])
    (isMulCommutative_map ι D hD.1) hHalt hDne' (ι z₀) (fun h => hz₀1 (hι (by rw [h, map_one])))
    (by
      rintro _ ⟨d₀, hd₀, rfl⟩ hd1
      have hd₀1 : d₀ ≠ 1 := fun h => hd1 (by rw [h, map_one])
      have hz : z₀ ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d₀} : Set M)) := by
        have := (Subgroup.mem_iInf.1 hz₀) d₀
        have := (Subgroup.mem_iInf.1 this) hd₀
        exact (Subgroup.mem_iInf.1 this) hd₀1
      obtain ⟨N, hNle, hNn, hNc, hzN⟩ := exists_normal_coprime_map ι p _ z₀ hz
      rw [map_inf_centralizer_singleton ι hι] at hNle hNn
      exact ⟨N, hNle, hNn, hNc, hzN⟩)
  have hcomm := isMulCommutative_map ι A hA.1
  have hexp : ∀ x ∈ A.map ι, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA.2 x hx, map_one]
  have hcardD : Nat.card (D.map ι) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hι]; exact hD3
  obtain ⟨h1, β, hβ, h2⟩ := card_le_of_fixedSet hp hp3 F hF (A.map ι) (D.map ι)
    (Subgroup.map_mono hDA) hcomm hexp hcardD hFd
  rw [Fintype.card_fin] at h1 h2
  refine ⟨h1, β, ?_, h2⟩
  rw [← hβ, Subgroup.card_map_of_injective hι]

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
