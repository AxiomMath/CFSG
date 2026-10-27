module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem false_of_mem_normal_E8_of_le_two_pow_eight {𝒮 : Sylow 2 G} {E : Subgroup G}
    (hE𝒮 : E ≤ (𝒮 : Subgroup G)) (hEn : (E.subgroupOf (𝒮 : Subgroup G)).Normal)
    (hEc : Nat.card E = 8) (hG2 : 2 ^ 11 ∣ Nat.card G) {c : G} (hc : c ∈ E) (hc1 : c ≠ 1)
    (hbound : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer ({c} : Set G) →
      Nat.card Q ≤ 2 ^ 8) : False := by
  have hSnorm : (𝒮 : Subgroup G) ≤ normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE𝒮).mp hEn
  let C : Subgroup G := (𝒮 : Subgroup G) ⊓ centralizer ({c} : Set G)
  have hCc : C ≤ centralizer ({c} : Set G) := inf_le_right
  have hCp : IsPGroup 2 C := 𝒮.isPGroup'.to_le inf_le_left
  have hCbound : Nat.card C ≤ 2 ^ 8 := hbound C hCp hCc
  have hcardC' : Nat.card (C.subgroupOf (𝒮 : Subgroup G)) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let φ : ↥𝒮 →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hSnorm)
  letI : MulAction ↥𝒮 ↥E := MulAction.compHom (↥E) φ
  have hsmul : ∀ (n : ↥𝒮) (x : ↥E),
      ((n • x : ↥E) : G) = (n : G) * (x : G) * (n : G)⁻¹ := fun n x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E (Subgroup.inclusion hSnorm n) x
  have hstab : MulAction.stabilizer ↥𝒮 (⟨c, hc⟩ : ↥E) = C.subgroupOf (𝒮 : Subgroup G) := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨n.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h' := congrArg (fun e : ↥E => (e : G)) h
      simp only [hsmul] at h'
      calc (n : G) * c = ((n : G) * c * (n : G)⁻¹) * n := by group
        _ = c * n := by rw [h']
    · intro h
      apply Subtype.ext
      rw [hsmul]
      have h' := Subgroup.mem_centralizer_singleton_iff.mp h.2
      rw [h', mul_inv_cancel_right]
  have hidx : (C.subgroupOf (𝒮 : Subgroup G)).index =
      (MulAction.orbit ↥𝒮 (⟨c, hc⟩ : ↥E)).ncard := by
    rw [← hstab]
    exact MulAction.index_stabilizer ↥𝒮 _
  have hcardE : Nat.card ↥E = 8 := hEc
  have horbit_ne_one : ∀ y ∈ MulAction.orbit ↥𝒮 (⟨c, hc⟩ : ↥E), y ≠ 1 := by
    rintro y ⟨n, rfl⟩ hy1
    have h' : (n : G) * c * (n : G)⁻¹ = 1 := by
      have hval := congrArg (fun e : ↥E => (e : G)) hy1
      simpa [hsmul] using hval
    have hnc : (n : G) * c = (n : G) := mul_inv_eq_one.mp h'
    exact hc1 (mul_left_cancel (a := (n : G)) (by simpa using hnc))
  have horbit_le : (MulAction.orbit ↥𝒮 (⟨c, hc⟩ : ↥E)).ncard ≤ 7 := by
    have hsub : MulAction.orbit ↥𝒮 (⟨c, hc⟩ : ↥E) ⊆ {x : ↥E | x ≠ 1} :=
      fun y hy => horbit_ne_one y hy
    have hfin : ({x : ↥E | x ≠ 1} : Set ↥E).Finite :=
      Set.finite_univ.subset (Set.subset_univ _)
    calc (MulAction.orbit ↥𝒮 (⟨c, hc⟩ : ↥E)).ncard
        ≤ ({x : ↥E | x ≠ 1} : Set ↥E).ncard := Set.ncard_le_ncard hsub hfin
      _ = Nat.card ↥E - 1 := by
        rw [show {x : ↥E | x ≠ 1} = (Set.univ : Set ↥E) \ {1} by ext x; simp]
        rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : ↥E)), Set.ncard_univ]
      _ = 7 := by rw [hcardE]
  have hidx_le7 : (C.subgroupOf (𝒮 : Subgroup G)).index ≤ 7 := by
    rw [hidx]; exact horbit_le
  have hdiv : (C.subgroupOf (𝒮 : Subgroup G)).index ∣ 2 ^ (Nat.card G).factorization 2 := by
    rw [← Sylow.card_eq_multiplicity 𝒮]
    exact Subgroup.index_dvd_card (C.subgroupOf (𝒮 : Subgroup G))
  obtain ⟨j, _hj, hidxj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
  have hidx_le : (C.subgroupOf (𝒮 : Subgroup G)).index ≤ 4 := by
    rw [hidxj] at hidx_le7 ⊢
    have hj2 : j ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ j := by omega
      have h8 : 8 ≤ 2 ^ j := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h3
      omega
    calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
      _ = 4 := by norm_num
  have hcardS_le : Nat.card (𝒮 : Subgroup G) ≤ 2 ^ 10 := by
    rw [← Subgroup.card_mul_index (C.subgroupOf (𝒮 : Subgroup G))]
    calc Nat.card (C.subgroupOf (𝒮 : Subgroup G)) * (C.subgroupOf (𝒮 : Subgroup G)).index
        ≤ Nat.card C * 4 := Nat.mul_le_mul hcardC'.le hidx_le
      _ ≤ 2 ^ 8 * 4 := Nat.mul_le_mul hCbound le_rfl
      _ = 2 ^ 10 := by norm_num
  have hfac : 11 ≤ (Nat.card G).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos (α := G)).ne').mp hG2
  have hcardS_ge : 2 ^ 11 ≤ Nat.card (𝒮 : Subgroup G) := by
    rw [show Nat.card (𝒮 : Subgroup G) = 2 ^ (Nat.card G).factorization 2 from
      Sylow.card_eq_multiplicity 𝒮]
    exact Nat.pow_le_pow_right (by norm_num) hfac
  have hcontra : (2 : ℕ) ^ 11 ≤ 2 ^ 10 := le_trans hcardS_ge hcardS_le
  norm_num at hcontra

theorem card_le_card_of_isPGroup_le_centralizer_conj {S : Subgroup G} {t : G}
    (hSH : S ≤ centralizer ({t} : Set G)) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G))) (g : G)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQc : Q ≤ centralizer ({g * t * g⁻¹} : Set G)) :
    Nat.card Q ≤ Nat.card S := by
  let Q' : Subgroup G := Q.map (MulAut.conj g⁻¹).toMonoidHom
  have hQ'p : IsPGroup 2 Q' := hQ.map (MulAut.conj g⁻¹).toMonoidHom
  have hQ'c : Q' ≤ centralizer ({t} : Set G) := by
    rintro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqcomm : q * (g * t * g⁻¹) = (g * t * g⁻¹) * q :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQc hq)
    have hconj : (MulAut.conj g⁻¹) (g * t * g⁻¹) = t := by
      rw [MulAut.conj_apply]
      group
    have key : (MulAut.conj g⁻¹) q * t = t * (MulAut.conj g⁻¹) q := by
      have h := congrArg (MulAut.conj g⁻¹) hqcomm
      simpa only [map_mul, hconj] using h
    exact key
  obtain ⟨k, _hkH, hk⟩ := exists_conj_le_of_isPGroup hQ'c hQ'p hSH hS hSi
  have hmap : Q'.map (MulAut.conj k).toMonoidHom ≤ S := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hk q hq
  calc Nat.card Q = Nat.card Q' :=
        (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    _ = Nat.card (Q'.map (MulAut.conj k).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj k).injective).symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hmap

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
