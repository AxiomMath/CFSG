module

public import CFSG.CharacterTheory.Semidihedral.StationaryOddLocalization

public section

namespace CFSG.Wreathed.InvertedLocalSylow

open scoped Pointwise
open CFSG.Semidihedral.StationaryOddLocalization

universe u

variable {G : Type u} [Group G]

section Model

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem modelHom_r_pow_half (hn : 1 ≤ n) :
    wreathModelHom S e (Original.r (2 ^ n)) ^ (2 ^ n / 2) =
      wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [← map_pow]
  congr 1
  rw [Original.r_eq, element_base_pow, Original.x_eq]
  simp only [nsmul_eq_mul, mul_one, mul_neg]
  rw [BrauerWong.neg_half n hn]

theorem modelHom_r_comm_x2 :
    wreathModelHom S e (Original.r (2 ^ n)) * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.r (2 ^ n)) := by
  rw [← map_mul, ← map_mul]
  congr 1
  rw [Original.r_eq, Original.x2_eq, element_base_mul, element_base_mul, add_comm (1 : ZMod _),
    add_comm (-1 : ZMod _)]

theorem modelHom_d_conj_x2 (hn : 1 ≤ n) :
    wreathModelHom S e (Original.d (2 ^ n)) * wreathModelHom S e (Original.x2 (2 ^ n)) *
        (wreathModelHom S e (Original.d (2 ^ n)))⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n)) * wreathModelHom S e (Original.x2 (2 ^ n)) := by
  rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  rw [Original.d_eq, Original.x2_eq, Original.x_eq, element_swap_mul, element_base_mul,
    element_base_mul, BrauerWong.half_add_half n hn]
  simp

theorem modelHom_d_conj_x (hn : 1 ≤ n) :
    wreathModelHom S e (Original.d (2 ^ n)) * wreathModelHom S e (Original.x (2 ^ n)) *
        (wreathModelHom S e (Original.d (2 ^ n)))⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
  congr 1
  rw [Original.d_eq, Original.x_eq, element_swap_mul, element_base_mul,
    BrauerWong.half_add_half n hn]
  simp

end Model

theorem map_conj_inf_centralizer (W : Subgroup G) (g u : G)
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    (W ⊓ Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom =
      W ⊓ Subgroup.centralizer ({g * u * g⁻¹} : Set G) := by
  ext w
  constructor
  · rintro ⟨v, ⟨hvW, hvu⟩, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg v).mp hvW, ?_⟩
    have hvu' : v * u = u * v := Subgroup.mem_centralizer_singleton_iff.mp hvu
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change g * v * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * v * g⁻¹)
    calc g * v * g⁻¹ * (g * u * g⁻¹) = g * (v * u) * g⁻¹ := by group
      _ = g * (u * v) * g⁻¹ := by rw [hvu']
      _ = g * u * g⁻¹ * (g * v * g⁻¹) := by group
  · rintro ⟨hwW, hwu⟩
    have hginv : g⁻¹ ∈ Subgroup.normalizer (W : Set G) := (Subgroup.normalizer _).inv_mem hg
    refine ⟨g⁻¹ * w * g, ⟨?_, ?_⟩, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp hginv w).mp hwW
      rwa [inv_inv] at h
    · have hwu' : w * (g * u * g⁻¹) = g * u * g⁻¹ * w :=
        Subgroup.mem_centralizer_singleton_iff.mp hwu
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc g⁻¹ * w * g * u = g⁻¹ * (w * (g * u * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * u * g⁻¹) * w) * g := by rw [hwu']
        _ = u * (g⁻¹ * w * g) := by group
    · change g * (g⁻¹ * w * g) * g⁻¹ = w
      group

theorem fixed_sup_inverted_of_inverted [Finite G] (W : Subgroup G) (hWodd : Odd (Nat.card W))
    (x y : G) (hinv : ∀ w ∈ W, x * w * x⁻¹ = w⁻¹)
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) (hy2 : y * y = 1) :
    (W ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ (W ⊓ Subgroup.centralizer ({x * y} : Set G)) = W ∧
    (W ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ (W ⊓ Subgroup.centralizer ({x * y} : Set G)) =
      ⊥ := by
  have hab := abelian_of_inverted x W hinv
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  constructor
  · apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro w hw
    have hvW : y * w * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hyW w).mp hw
    have hyv : y * (y * w * y⁻¹) * y⁻¹ = w := by
      rw [hyinv]
      calc y * (y * w * y) * y = (y * y) * w * (y * y) := by group
        _ = w := by rw [hy2, one_mul, mul_one]
    have h1 : w * (y * w * y⁻¹) ∈ W ⊓ Subgroup.centralizer ({y} : Set G) := by
      refine ⟨W.mul_mem hw hvW, (conj_fixed_iff y _).mp ?_⟩
      calc y * (w * (y * w * y⁻¹)) * y⁻¹ =
          (y * w * y⁻¹) * (y * (y * w * y⁻¹) * y⁻¹) := by group
        _ = (y * w * y⁻¹) * w := by rw [hyv]
        _ = w * (y * w * y⁻¹) := hcomm _ hvW _ hw
    have h2 : w * (y * w * y⁻¹)⁻¹ ∈ W ⊓ Subgroup.centralizer ({x * y} : Set G) := by
      refine ⟨W.mul_mem hw (W.inv_mem hvW), (conj_fixed_iff (x * y) _).mp ?_⟩
      have hmem : (y * w * y⁻¹) * w⁻¹ ∈ W := W.mul_mem hvW (W.inv_mem hw)
      calc x * y * (w * (y * w * y⁻¹)⁻¹) * (x * y)⁻¹ =
          x * ((y * w * y⁻¹) * (y * (y * w * y⁻¹) * y⁻¹)⁻¹) * x⁻¹ := by group
        _ = x * ((y * w * y⁻¹) * w⁻¹) * x⁻¹ := by rw [hyv]
        _ = ((y * w * y⁻¹) * w⁻¹)⁻¹ := hinv _ hmem
        _ = w * (y * w * y⁻¹)⁻¹ := by group
    have hsq : w ^ 2 ∈ (W ⊓ Subgroup.centralizer ({y} : Set G)) ⊔
        (W ⊓ Subgroup.centralizer ({x * y} : Set G)) := by
      have heq : w * (y * w * y⁻¹) * (w * (y * w * y⁻¹)⁻¹) = w ^ 2 := by
        calc w * (y * w * y⁻¹) * (w * (y * w * y⁻¹)⁻¹) =
            w * ((y * w * y⁻¹) * w) * (y * w * y⁻¹)⁻¹ := by group
          _ = w * (w * (y * w * y⁻¹)) * (y * w * y⁻¹)⁻¹ := by rw [hcomm _ hvW w hw]
          _ = w ^ 2 := by rw [sq]; group
      rw [← heq]
      exact Subgroup.mul_mem_sup h1 h2
    obtain ⟨j, hj⟩ := hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hw)
    have hw' : w = (w ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = orderOf w + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [hw']
    exact Subgroup.pow_mem _ hsq _
  · rw [eq_bot_iff]
    rintro w ⟨⟨hwW, hwy⟩, ⟨-, hwxy⟩⟩
    have hy : y * w * y⁻¹ = w := (conj_fixed_iff y w).mpr hwy
    have hxy : x * y * w * (x * y)⁻¹ = w := (conj_fixed_iff (x * y) w).mpr hwxy
    have hww : w = w⁻¹ := by
      calc w = x * y * w * (x * y)⁻¹ := hxy.symm
        _ = x * (y * w * y⁻¹) * x⁻¹ := by group
        _ = x * w * x⁻¹ := by rw [hy]
        _ = w⁻¹ := hinv w hwW
    have hw2 : w ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hww]
      exact mul_inv_cancel w
    have hodd : Odd (orderOf w) := hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hwW)
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
    have hone : orderOf w = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

theorem eigensubgroup_structure [Finite G] (W : Subgroup G) (hW : W ≠ ⊥)
    (hWodd : Odd (Nat.card W)) (x y d : G) (hx2 : x * x = 1)
    (hinv : ∀ w ∈ W, x * w * x⁻¹ = w⁻¹)
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) (hy2 : y * y = 1)
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hdy : d * y * d⁻¹ = x * y)
    (hdx : d * x * d⁻¹ = x) :
    IsMulCommutative W ∧
    ((W ⊓ Subgroup.centralizer ({y} : Set G)) ⊔
        (W ⊓ Subgroup.centralizer ({x * y} : Set G)) = W ∧
      (W ⊓ Subgroup.centralizer ({y} : Set G)) ⊓
        (W ⊓ Subgroup.centralizer ({x * y} : Set G)) = ⊥) ∧
    (W ⊓ Subgroup.centralizer ({y} : Set G) ≠ ⊥ ∧
      W ⊓ Subgroup.centralizer ({x * y} : Set G) ≠ ⊥) ∧
    ((W ⊓ Subgroup.centralizer ({y} : Set G)).map (MulAut.conj d).toMonoidHom =
        W ⊓ Subgroup.centralizer ({x * y} : Set G) ∧
      (W ⊓ Subgroup.centralizer ({x * y} : Set G)).map (MulAut.conj d).toMonoidHom =
        W ⊓ Subgroup.centralizer ({y} : Set G)) ∧
    Nat.card W = Nat.card (W ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) ^ 2 := by
  have hab := abelian_of_inverted x W hinv
  obtain ⟨hsup, hinf⟩ := fixed_sup_inverted_of_inverted W hWodd x y hinv hyW hy2
  have hEF : (W ⊓ Subgroup.centralizer ({y} : Set G)).map (MulAut.conj d).toMonoidHom =
      W ⊓ Subgroup.centralizer ({x * y} : Set G) := by
    rw [map_conj_inf_centralizer W d y hdW, hdy]
  have hFE : (W ⊓ Subgroup.centralizer ({x * y} : Set G)).map (MulAut.conj d).toMonoidHom =
      W ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [map_conj_inf_centralizer W d (x * y) hdW]
    congr 3
    calc d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
      _ = y := by rw [hdx, hdy, ← mul_assoc, hx2, one_mul]
  have hcardEF : Nat.card (W ⊓ Subgroup.centralizer ({x * y} : Set G) : Subgroup G) =
      Nat.card (W ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
    rw [← hEF, Subgroup.card_map_of_injective (MulAut.conj d).injective]
  have hFN : W ⊓ Subgroup.centralizer ({x * y} : Set G) ≤
      Subgroup.normalizer ((W ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have hc : f * v = v * f :=
        congrArg Subtype.val (hab.is_comm.comm ⟨f, hf.1⟩ ⟨v, hv.1⟩)
      rw [hc, mul_inv_cancel_right]
      exact hv
    · intro hv
      have hvW : v ∈ W := by
        have h := W.mul_mem (W.mul_mem (W.inv_mem hf.1) hv.1) hf.1
        simpa [mul_assoc] using h
      have hc : f * v = v * f :=
        congrArg Subtype.val (hab.is_comm.comm ⟨f, hf.1⟩ ⟨v, hvW⟩)
      rw [hc, mul_inv_cancel_right] at hv
      exact hv
  have hcard : Nat.card W =
      Nat.card (W ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) ^ 2 := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hFN
      (disjoint_iff.mpr hinf)
    rw [hsup, hcardEF] at h
    rw [h, sq]
  have hEne : W ⊓ Subgroup.centralizer ({y} : Set G) ≠ ⊥ := by
    intro hE
    apply hW
    rw [← Subgroup.card_eq_one, hcard, Subgroup.card_eq_one.mpr hE, one_pow]
  have hFne : W ⊓ Subgroup.centralizer ({x * y} : Set G) ≠ ⊥ := by
    intro hF
    apply hEne
    rw [← hFE, hF, Subgroup.map_bot]
  exact ⟨hab, ⟨hsup, hinf⟩, ⟨hEne, hFne⟩, ⟨hEF, hFE⟩, hcard⟩

end CFSG.Wreathed.InvertedLocalSylow
