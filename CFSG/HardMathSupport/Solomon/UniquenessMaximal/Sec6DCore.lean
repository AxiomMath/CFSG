module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DCal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open scoped commutatorElement
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

variable {Q : Type*} [Group Q]

@[expose] def sg (σ x : Q) : Q := σ * x * σ⁻¹

theorem sg_mul (σ x y : Q) : sg σ (x * y) = sg σ x * sg σ y := by simp only [sg]; group
theorem sg_one (σ : Q) : sg σ 1 = 1 := by simp [sg]
theorem sg_inv (σ x : Q) : sg σ x⁻¹ = (sg σ x)⁻¹ := by simp only [sg]; group
theorem sg_pow (σ x : Q) (n : ℕ) : sg σ (x ^ n) = (sg σ x) ^ n := by
  induction n with
  | zero => simp [sg_one]
  | succ n ih => rw [pow_succ, sg_mul, ih, pow_succ]
theorem sg_zpow (σ x : Q) (n : ℤ) : sg σ (x ^ n) = (sg σ x) ^ n := by
  simp only [sg]; rw [conj_zpow]
theorem sg_comm (σ x y : Q) : sg σ ⁅x, y⁆ = ⁅sg σ x, sg σ y⁆ := by
  simp only [sg, commutatorElement_def]; group
theorem sg_sg_sg {σ : Q} (h3 : σ ^ 3 = 1) (x : Q) : sg σ (sg σ (sg σ x)) = x := by
  have h3' : σ * σ * σ = 1 := by simpa [pow_succ] using h3
  simp only [sg]
  calc σ * (σ * (σ * x * σ⁻¹) * σ⁻¹) * σ⁻¹ = (σ * σ * σ) * x * (σ * σ * σ)⁻¹ := by group
    _ = x := by rw [h3']; simp

theorem sg_mem_cj {σ : Q} {R : Subgroup Q} {x : Q} (hx : x ∈ R) : sg σ x ∈ cj σ R :=
  conj_mem_cj hx


theorem L1_mod3 (k : ℤ) (h : 3 ∣ k * (k * k) - 1) : 3 ∣ k - 1 := by
  have h1 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h1 with h1 | h1 | h1
  · exfalso
    have : (k * (k * k) - 1) % 3 = 2 := by
      simp [Int.sub_emod, Int.mul_emod, h1]
    omega
  · omega
  · exfalso
    have : (k * (k * k) - 1) % 3 = 1 := by
      simp [Int.sub_emod, Int.mul_emod, h1]
    omega

theorem L2_mod3 (α β : ℤ) (h1 : 3 ∣ α * β - 1) (h2 : 3 ∣ α + β * β) :
    3 ∣ α + 1 ∧ 3 ∣ β + 1 := by
  have hb : β % 3 = 0 ∨ β % 3 = 1 ∨ β % 3 = 2 := by omega
  have ha : α % 3 = 0 ∨ α % 3 = 1 ∨ α % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    first
    | (constructor <;> omega)
    | (exfalso; have e1 : (α * β - 1) % 3 = 0 := by omega
       have e2 : (α + β * β) % 3 = 0 := by omega
       simp [Int.sub_emod, Int.mul_emod, Int.add_emod, ha, hb] at e1 e2)

theorem sg_injective (σ : Q) : Function.Injective (sg σ) := by
  intro x y hxy
  simpa [sg] using hxy

theorem sg_noncomm {a b : Q} (hab : a * b ≠ b * a) (σ : Q) : sg σ a * sg σ b ≠ sg σ b * sg σ a := by
  intro h2
  apply hab
  apply sg_injective σ
  rw [sg_mul, sg_mul, h2]

theorem sg_eq_one_iff (σ x : Q) : sg σ x = 1 ↔ x = 1 := by
  constructor
  · intro h; exact sg_injective σ (by rw [h, sg_one])
  · rintro rfl; exact sg_one σ

theorem cj_zpowers (σ x : Q) : cj σ (Subgroup.zpowers x) = Subgroup.zpowers (sg σ x) := by
  unfold cj
  rw [MonoidHom.map_zpowers]
  rfl

theorem cj_inf (σ : Q) (A B : Subgroup Q) : cj σ (A ⊓ B) = cj σ A ⊓ cj σ B := by
  unfold cj
  exact Subgroup.map_inf A B _ (MulAut.conj σ).injective

theorem cj_bot (σ : Q) : cj σ (⊥ : Subgroup Q) = ⊥ := by
  unfold cj
  exact Subgroup.map_bot _

theorem inf_eq_bot_of_card_three {A B : Subgroup Q} (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hne : A ≠ B) : A ⊓ B = ⊥ := by
  have hfA : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hfB : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  by_contra hI
  have hdvd : Nat.card ↥(A ⊓ B) ∣ 3 := hA ▸ Subgroup.card_dvd_of_le (inf_le_left : A ⊓ B ≤ A)
  have hI1 : Nat.card ↥(A ⊓ B) ≠ 1 := fun h1 => hI (Subgroup.eq_bot_of_card_eq _ h1)
  have hI3 : Nat.card ↥(A ⊓ B) = 3 := by
    have := (Nat.dvd_prime Nat.prime_three).1 hdvd
    omega
  apply hne
  have e1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ B ≤ A) (by omega)
  have e2 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge (inf_le_right : A ⊓ B ≤ B) (by omega)
  exact e1.symm.trans e2

theorem exp_relation {u v : Q} (huv : Commute u v) (α β : ℤ)
    (hE : u = v ^ α * (u ^ α * v ^ β) ^ β) : u ^ (α * β - 1) * v ^ (α + β * β) = 1 := by
  rw [Commute.mul_zpow (huv.zpow_zpow α β), ← zpow_mul, ← zpow_mul] at hE
  have cA : Commute (u ^ (α * β)) (v ^ α) := huv.zpow_zpow _ _
  have cB : Commute (u ^ (α * β)) (v ^ (β * β)) := huv.zpow_zpow _ _
  have cC : Commute (u⁻¹) (v ^ α * v ^ (β * β)) :=
    Commute.mul_right (huv.inv_left.zpow_right α) (huv.inv_left.zpow_right (β * β))
  calc u ^ (α * β - 1) * v ^ (α + β * β)
      = u ^ (α * β) * (u⁻¹ * (v ^ α * v ^ (β * β))) := by
        rw [zpow_sub_one, zpow_add, mul_assoc]
    _ = u ^ (α * β) * ((v ^ α * v ^ (β * β)) * u⁻¹) := by rw [cC.eq]
    _ = (v ^ α * (u ^ (α * β) * v ^ (β * β))) * u⁻¹ := by
        have := cA.eq
        calc u ^ (α * β) * ((v ^ α * v ^ (β * β)) * u⁻¹)
            = (u ^ (α * β) * v ^ α) * v ^ (β * β) * u⁻¹ := by group
          _ = (v ^ α * u ^ (α * β)) * v ^ (β * β) * u⁻¹ := by rw [this]
          _ = _ := by group
    _ = u * u⁻¹ := by rw [← hE]
    _ = 1 := by simp

theorem commutatorElement_ne_one {a b : Q} (hab : a * b ≠ b * a) : ⁅a, b⁆ ≠ 1 := by
  intro h1
  apply hab
  rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  simpa [mul_assoc] using h1

theorem index_subgroupOf_mul_card {N H : Subgroup Q} (h : N ≤ H) :
    (N.subgroupOf H).index * Nat.card N = Nat.card H := by
  have := Subgroup.relIndex_mul_card N H
  rwa [inf_eq_left.2 h] at this

theorem three_mul_card_le [Finite Q] {C : Subgroup Q} {x : Q}
    (hexp : ∀ g ∈ C ⊔ Subgroup.zpowers x, g ^ 3 = 1) (hx : x ∉ C) :
    3 * Nat.card C ≤ Nat.card ↥(C ⊔ Subgroup.zpowers x) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := C ⊔ Subgroup.zpowers x with hD
  have hCD : C ≤ D := le_sup_left
  have hxD : x ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hDp : IsPGroup 3 D := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hexp g g.2)⟩
  have hCp : IsPGroup 3 C := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hexp g (hCD g.2))⟩
  obtain ⟨k, hk⟩ := exists_card_eq_pow hDp
  obtain ⟨j, hj⟩ := exists_card_eq_pow hCp
  have hlt : j < k := by
    by_contra hjk
    have : Nat.card D ≤ Nat.card C := by
      rw [hk, hj]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hx (Subgroup.eq_of_le_of_card_ge hCD this ▸ hxD)
  rw [hk, hj]
  calc 3 * 3 ^ j = 3 ^ (j + 1) := by ring
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hlt

theorem comm_mul_central {x y z : Q} (hxz : x * z = z * x) : ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h1 : z * x⁻¹ = x⁻¹ * z := by
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * (z * x) * x⁻¹ := by rw [hxz]
      _ = x⁻¹ * z := by group
  simp only [commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [h1]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem mem_Zc_of_closure {R : Subgroup Q} {a b x : Q} (hcl : Subgroup.closure {a, b} = R)
    (hx : x ∈ R) (hxa : ⁅x, a⁆ = 1) (hxb : ⁅x, b⁆ = 1) : x ∈ Zc R := by
  refine mem_Zc.2 ⟨hx, fun r hr => ?_⟩
  have hle : Subgroup.closure {a, b} ≤ Subgroup.centralizer ({x} : Set Q) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (commutatorElement_eq_one_iff_mul_comm.1 hxa).symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (commutatorElement_eq_one_iff_mul_comm.1 hxb).symm
  rw [hcl] at hle
  have := Subgroup.mem_centralizer_singleton_iff.1 (hle hr)
  exact this.symm

theorem not_mem_of_centralizer {D : Subgroup Q} {y t : Q} (hD : D ≤ Subgroup.centralizer ({y} : Set Q))
    (ht : t * y ≠ y * t) : t ∉ D := fun h => ht (Subgroup.mem_centralizer_singleton_iff.1 (hD h))

theorem zpowers_le_cent {x y : Q} (hxy : x * y = y * x) :
    Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set Q) := by
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Commute.zpow_left (show Commute x y from hxy) k).eq

theorem zpowers_le_cent_zpowers {x y : Q} (hxy : x * y = y * x) :
    Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers y : Set Q) := by
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ((Commute.zpow_zpow (show Commute x y from hxy) k m).eq).symm

theorem isElemAbelian_zpowers {x : Q} (hx : x ^ 3 = 1) : IsElemAbelian 3 (Subgroup.zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers hx

namespace Triple

variable {σ : Q} {R₁ : Subgroup Q} (h : Triple σ R₁)
include h

theorem sg_mem_R₁_of_R₃ {x : Q} (hx : x ∈ cj σ (cj σ R₁)) : sg σ x ∈ R₁ := by
  have := sg_mem_cj (σ := σ) hx
  rwa [cj_cj_cj h.pow3] at this

theorem sg_Zc₃ {z : Q} (hz : z ∈ Zc (cj σ R₁)) : sg σ z ∈ Zc (cj σ (cj σ R₁)) := by
  rw [Zc_cj]
  exact sg_mem_cj hz

theorem sg_Zc₂ {z : Q} (hz : z ∈ Zc R₁) : sg σ z ∈ Zc (cj σ R₁) := by
  rw [Zc_cj]
  exact sg_mem_cj hz

theorem exists_gens {a : Q} (ha : a ∈ R σ R₁) (hσa : sg σ a = a) (hna : a ∉ W σ R₁) :
    ∃ a₁ ∈ R₁, ∃ ζ₂ ∈ Zc (cj σ R₁), ∃ ζ₃ ∈ Zc (cj σ (cj σ R₁)), a₁ ∉ Zc R₁ ∧
      a = a₁ * (sg σ a₁ * ζ₂) * (sg σ (sg σ a₁) * ζ₃) := by
  have hc := h.comm3
  obtain ⟨u₁, hu₁, u₂, hu₂, u₃, hu₃, hau⟩ := hc.mem_sup3 ha
  have hv₁ : sg σ u₃ ∈ R₁ := h.sg_mem_R₁_of_R₃ hu₃
  have hv₂ : sg σ u₁ ∈ cj σ R₁ := sg_mem_cj hu₁
  have hv₃ : sg σ u₂ ∈ cj σ (cj σ R₁) := sg_mem_cj hu₂
  have e : u₁ * u₂ * u₃ = sg σ u₃ * sg σ u₁ * sg σ u₂ := by
    calc u₁ * u₂ * u₃ = a := hau.symm
      _ = sg σ a := hσa.symm
      _ = sg σ (u₁ * u₂ * u₃) := by rw [hau]
      _ = sg σ u₁ * sg σ u₂ * sg σ u₃ := by simp only [sg_mul]
      _ = sg σ u₃ * (sg σ u₁ * sg σ u₂) := by
        have := Commute.mul_left (show Commute (sg σ u₁) (sg σ u₃) from
          (hc.c12 _ hv₁ _ hv₂).symm) (show Commute (sg σ u₂) (sg σ u₃) from
          (hc.c13 _ hv₁ _ hv₃).symm)
        exact this.eq
      _ = sg σ u₃ * sg σ u₁ * sg σ u₂ := by group
  obtain ⟨-, d2, d3⟩ := hc.unique_decomp hu₁ hu₂ hu₃ hv₁ hv₂ hv₃ e
  obtain ⟨ζ₂, hζ₂, hv₂e⟩ : ∃ ζ₂ ∈ Zc (cj σ R₁), sg σ u₁ = u₂ * ζ₂ := ⟨_, d2, by group⟩
  obtain ⟨ζ₃, hζ₃, hv₃e⟩ : ∃ ζ₃ ∈ Zc (cj σ (cj σ R₁)), sg σ u₂ = u₃ * ζ₃ := ⟨_, d3, by group⟩
  have e2 : u₂ = sg σ u₁ * ζ₂⁻¹ := by rw [hv₂e]; group
  have e3 : u₃ = sg σ (sg σ u₁) * (sg σ (ζ₂⁻¹) * ζ₃⁻¹) := by
    calc u₃ = sg σ u₂ * ζ₃⁻¹ := by rw [hv₃e]; group
      _ = sg σ (sg σ u₁ * ζ₂⁻¹) * ζ₃⁻¹ := by rw [← e2]
      _ = _ := by rw [sg_mul]; group
  have hζ₂' : ζ₂⁻¹ ∈ Zc (cj σ R₁) := (Zc (cj σ R₁)).inv_mem hζ₂
  have hζ₃' : sg σ (ζ₂⁻¹) * ζ₃⁻¹ ∈ Zc (cj σ (cj σ R₁)) :=
    (Zc _).mul_mem (h.sg_Zc₃ hζ₂') ((Zc _).inv_mem hζ₃)
  have eq : a = u₁ * (sg σ u₁ * ζ₂⁻¹) * (sg σ (sg σ u₁) * (sg σ (ζ₂⁻¹) * ζ₃⁻¹)) := by
    rw [hau]
    have : u₂ = sg σ u₁ * ζ₂⁻¹ := e2
    rw [← e2, ← e3]
  refine ⟨u₁, hu₁, _, hζ₂', _, hζ₃', fun hz => hna ?_, eq⟩
  rw [eq]
  have m1 : u₁ ∈ W σ R₁ := Subgroup.mem_sup_left (Subgroup.mem_sup_left hz)
  have m2 : sg σ u₁ * ζ₂⁻¹ ∈ W σ R₁ :=
    (W σ R₁).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right (h.sg_Zc₂ hz)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hζ₂'))
  have m3 : sg σ (sg σ u₁) * (sg σ (ζ₂⁻¹) * ζ₃⁻¹) ∈ W σ R₁ :=
    (W σ R₁).mul_mem (Subgroup.mem_sup_right (h.sg_Zc₃ (h.sg_Zc₂ hz)))
      (Subgroup.mem_sup_right hζ₃')
  exact (W σ R₁).mul_mem ((W σ R₁).mul_mem m1 m2) m3

theorem rel [Finite Q] {a₁ b₁ : Q} (ha₁ : a₁ ∈ R₁) (hb₁ : b₁ ∈ R₁) (hab : a₁ * b₁ ≠ b₁ * a₁)
    (hW : Nat.card (W σ R₁) ≤ 9) :
    (sg σ ⁅a₁, b₁⁆ = ⁅a₁, b₁⁆ ∧ sg σ (sg σ ⁅a₁, b₁⁆) = ⁅a₁, b₁⁆) ∨
    (⁅a₁, b₁⁆ * sg σ ⁅a₁, b₁⁆ * sg σ (sg σ ⁅a₁, b₁⁆) = 1 ∧
      Zc R₁ ⊓ Zc (cj σ R₁) = ⊥ ∧ Zc (cj σ R₁) ⊓ Zc (cj σ (cj σ R₁)) = ⊥ ∧
      Nat.card (W σ R₁) = 9) := by
  have hc := h.comm3
  have hz₁m : ⁅a₁, b₁⁆ ∈ Zc R₁ := h.heis.comm_mem_Zc ha₁ hb₁
  have hz₁1 : ⁅a₁, b₁⁆ ≠ 1 := commutatorElement_ne_one hab
  have hZ₁ : Zc R₁ = Subgroup.zpowers ⁅a₁, b₁⁆ := h.heis.Zc_eq_zpowers ha₁ hb₁ hab
  have hz₁3 : ⁅a₁, b₁⁆ ^ 3 = 1 := h.heis.2.2 _ (Zc_le _ hz₁m)
  have hord : orderOf ⁅a₁, b₁⁆ = 3 := orderOf_eq_prime hz₁3 hz₁1
  have hZ₂ : Zc (cj σ R₁) = Subgroup.zpowers (sg σ ⁅a₁, b₁⁆) := by
    rw [Zc_cj, hZ₁, cj_zpowers]
  have hZ₃ : Zc (cj σ (cj σ R₁)) = Subgroup.zpowers (sg σ (sg σ ⁅a₁, b₁⁆)) := by
    rw [Zc_cj, hZ₂, cj_zpowers]
  have hz₂m : sg σ ⁅a₁, b₁⁆ ∈ Zc (cj σ R₁) := h.sg_Zc₂ hz₁m
  have hz₃m : sg σ (sg σ ⁅a₁, b₁⁆) ∈ Zc (cj σ (cj σ R₁)) := h.sg_Zc₃ hz₂m
  have c12 : Commute ⁅a₁, b₁⁆ (sg σ ⁅a₁, b₁⁆) :=
    hc.c12 _ (Zc_le _ hz₁m) _ (Zc_le _ hz₂m)
  have hsz₃ : sg σ (sg σ (sg σ ⁅a₁, b₁⁆)) = ⁅a₁, b₁⁆ := sg_sg_sg h.pow3 _
  have hcard₁ : Nat.card (Zc R₁) = 3 := h.heis.card_Zc
  have hcard₂ : Nat.card (Zc (cj σ R₁)) = 3 := h.heis₂.card_Zc
  generalize ⁅a₁, b₁⁆ = u at *
  by_cases hZ12 : Zc R₁ = Zc (cj σ R₁)
  ·
    left
    have hmem : sg σ u ∈ Subgroup.zpowers u := by
      rw [← hZ₁, hZ12]; exact hz₂m
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hv : sg σ u = u ^ k := hk.symm
    have hw : sg σ (sg σ u) = (u ^ k) ^ k := by rw [hv, sg_zpow, hv]
    have he : u ^ (1 : ℤ) = u ^ (k * k * k) := by
      calc u ^ (1 : ℤ) = u := zpow_one u
        _ = sg σ (sg σ (sg σ u)) := hsz₃.symm
        _ = sg σ ((u ^ k) ^ k) := by rw [hw]
        _ = ((u ^ k) ^ k) ^ k := by rw [sg_zpow, sg_zpow, hv]
        _ = u ^ (k * k * k) := by rw [← zpow_mul, ← zpow_mul]; congr 1; ring
    have hmod := (zpow_eq_zpow_iff_modEq.1 he)
    rw [hord, Int.modEq_iff_dvd] at hmod
    have h3 : (3 : ℤ) ∣ k - 1 := L1_mod3 k (by simpa [mul_assoc] using hmod)
    have hk1 : u ^ k = u ^ (1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hord]
      simp only [Nat.cast_ofNat, Int.ModEq]
      omega
    have hvu : sg σ u = u := by rw [hv, hk1, zpow_one]
    exact ⟨hvu, by rw [hvu, hvu]⟩
  ·
    right
    have hI12 : Zc R₁ ⊓ Zc (cj σ R₁) = ⊥ := inf_eq_bot_of_card_three hcard₁ hcard₂ hZ12
    have hI23 : Zc (cj σ R₁) ⊓ Zc (cj σ (cj σ R₁)) = ⊥ := by
      have e2 : Zc (cj σ R₁) = cj σ (Zc R₁) := Zc_cj σ R₁
      have e3 : Zc (cj σ (cj σ R₁)) = cj σ (Zc (cj σ R₁)) := Zc_cj σ (cj σ R₁)
      rw [e3, e2, ← cj_inf, ← e2, hI12, cj_bot]
    have hz₂1 : sg σ u ≠ 1 := fun h1 => hz₁1 ((sg_eq_one_iff σ u).1 h1)
    have hz₂3 : (sg σ u) ^ 3 = 1 := by rw [← sg_pow, hz₁3, sg_one]
    have hord₂ : orderOf (sg σ u) = 3 := orderOf_eq_prime hz₂3 hz₂1
    have hnot : sg σ u ∉ Zc R₁ := by
      intro hmem
      have hle : Zc (cj σ R₁) ≤ Zc R₁ := by
        rw [hZ₂]; exact (Subgroup.zpowers_le).2 hmem
      have : Finite ↥(Zc R₁) := inferInstance
      exact hZ12 (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
    have hsup9 : Nat.card ↥(Zc R₁ ⊔ Zc (cj σ R₁)) = 9 := by
      rw [hZ₂, card_sup_zpowers_of_pow_three_eq_one hz₂3 hnot
        (fun z hz => (hc.c12 z (Zc_le _ hz) _ (Zc_le _ hz₂m))), hcard₁]
    have hWeq : Zc R₁ ⊔ Zc (cj σ R₁) = W σ R₁ := by
      have : Finite ↥(W σ R₁) := inferInstance
      exact Subgroup.eq_of_le_of_card_ge (le_sup_left : Zc R₁ ⊔ Zc (cj σ R₁) ≤ W σ R₁)
        (by rw [hsup9]; exact hW)
    have hW9 : Nat.card ↥(W σ R₁) = 9 := by rw [← hWeq, hsup9]
    have hz₃W : sg σ (sg σ u) ∈ Zc R₁ ⊔ Zc (cj σ R₁) := by
      rw [hWeq]; exact Subgroup.mem_sup_right hz₃m
    have hAB : Zc R₁ ≤ Subgroup.centralizer (Zc (cj σ R₁) : Set Q) := fun z hz y hy =>
      (hc.c12 z (Zc_le _ hz) y (Zc_le _ hy)).symm
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup hAB hz₃W
    rw [hZ₁] at hx
    rw [hZ₂] at hy
    obtain ⟨α, hα⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨β, hβ⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← hα, ← hβ] at hxy
    have hE : u = sg σ u ^ α * (u ^ α * sg σ u ^ β) ^ β := by
      calc u = sg σ (sg σ (sg σ u)) := hsz₃.symm
        _ = sg σ (u ^ α * sg σ u ^ β) := by rw [hxy]
        _ = sg σ u ^ α * (sg σ (sg σ u)) ^ β := by rw [sg_mul, sg_zpow, sg_zpow]
        _ = _ := by rw [hxy]
    have hrel := exp_relation c12 α β hE
    have hm : u ^ (α * β - 1) = 1 := by
      have h1 : u ^ (α * β - 1) ∈ Zc R₁ := by
        rw [hZ₁]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) _
      have h2 : u ^ (α * β - 1) ∈ Zc (cj σ R₁) := by
        have : u ^ (α * β - 1) = (sg σ u ^ (α + β * β))⁻¹ := eq_inv_of_mul_eq_one_left hrel
        rw [this, hZ₂]
        exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
      have : u ^ (α * β - 1) ∈ Zc R₁ ⊓ Zc (cj σ R₁) := ⟨h1, h2⟩
      rw [hI12] at this
      exact Subgroup.mem_bot.1 this
    have hn : sg σ u ^ (α + β * β) = 1 := by
      rw [hm, one_mul] at hrel; exact hrel
    have h3m : (3 : ℤ) ∣ α * β - 1 := by
      have := (zpow_eq_one_iff_modEq (x := u) (n := α * β - 1)).1 hm
      rw [hord] at this
      exact (Int.modEq_zero_iff_dvd.1 (by simpa using this))
    have h3n : (3 : ℤ) ∣ α + β * β := by
      have := (zpow_eq_one_iff_modEq (x := sg σ u) (n := α + β * β)).1 hn
      rw [hord₂] at this
      exact (Int.modEq_zero_iff_dvd.1 (by simpa using this))
    obtain ⟨hα1, hβ1⟩ := L2_mod3 α β h3m h3n
    have eα : u ^ α = u⁻¹ := by
      rw [← zpow_neg_one, zpow_eq_zpow_iff_modEq, hord]
      simp only [Nat.cast_ofNat, Int.ModEq]
      omega
    have eβ : sg σ u ^ β = (sg σ u)⁻¹ := by
      rw [← zpow_neg_one, zpow_eq_zpow_iff_modEq, hord₂]
      simp only [Nat.cast_ofNat, Int.ModEq]
      omega
    refine ⟨?_, hI12, hI23, hW9⟩
    rw [hxy, eα, eβ]
    calc u * sg σ u * (u⁻¹ * (sg σ u)⁻¹) = (sg σ u * u) * (u⁻¹ * (sg σ u)⁻¹) := by rw [c12.eq]
      _ = 1 := by group

theorem comm_mem_Zc₁ {g y : Q} (hg : g ∈ R σ R₁) (hy : y ∈ R₁) : ⁅g, y⁆ ∈ Zc R₁ := by
  have hc := h.comm3
  obtain ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, rfl⟩ := hc.mem_sup3 hg
  have := hc.comm_prod3 hg₁ hy hg₂ (one_mem _) hg₃ (one_mem _)
  simp only [mul_one, commutatorElement_one_right] at this
  rw [this]; exact h.heis.comm_mem_Zc hg₁ hy

theorem comm_mem_Zc₂ {g y : Q} (hg : g ∈ R σ R₁) (hy : y ∈ cj σ R₁) : ⁅g, y⁆ ∈ Zc (cj σ R₁) := by
  have hc := h.comm3
  obtain ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, rfl⟩ := hc.mem_sup3 hg
  have := hc.comm_prod3 hg₁ (one_mem _) hg₂ hy hg₃ (one_mem _)
  simp only [mul_one, one_mul, commutatorElement_one_right] at this
  rw [this]; exact h.heis₂.comm_mem_Zc hg₂ hy

theorem comm_mem_Zc₃ {g y : Q} (hg : g ∈ R σ R₁) (hy : y ∈ cj σ (cj σ R₁)) :
    ⁅g, y⁆ ∈ Zc (cj σ (cj σ R₁)) := by
  have hc := h.comm3
  obtain ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, rfl⟩ := hc.mem_sup3 hg
  have := hc.comm_prod3 hg₁ (one_mem _) hg₂ (one_mem _) hg₃ hy
  simp only [one_mul, commutatorElement_one_right] at this
  rw [this]; exact h.heis₃.comm_mem_Zc hg₃ hy

theorem exp3_R {g : Q} (hg : g ∈ R σ R₁) : g ^ 3 = 1 := by
  have hc := h.comm3
  obtain ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, rfl⟩ := hc.mem_sup3 hg
  have c12 : Commute g₁ g₂ := hc.c12 _ hg₁ _ hg₂
  have c13 : Commute g₁ g₃ := hc.c13 _ hg₁ _ hg₃
  have c23 : Commute g₂ g₃ := hc.c23 _ hg₂ _ hg₃
  have h123 : Commute (g₁ * g₂) g₃ := c13.mul_left c23
  rw [h123.mul_pow, c12.mul_pow, h.heis.2.2 g₁ hg₁, h.heis₂.2.2 g₂ hg₂, h.heis₃.2.2 g₃ hg₃]
  simp

@[expose] def S (σ : Q) (R₁ : Subgroup Q) (a b₁ : Q) : Subgroup Q :=
  R σ R₁ ⊓ Subgroup.centralizer ({a, b₁} : Set Q)

theorem mem_S {a b₁ g : Q} : g ∈ S σ R₁ a b₁ ↔ g ∈ R σ R₁ ∧ a * g = g * a ∧ b₁ * g = g * b₁ := by
  unfold S
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 a (by simp), h2 b₁ (by simp)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · exact h2
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact h3

theorem S_le_R {a b₁ : Q} : S σ R₁ a b₁ ≤ R σ R₁ := inf_le_left

theorem R₁_le_R : R₁ ≤ R σ R₁ := le_sup_left.trans le_sup_left
theorem R₂_le_R : cj σ R₁ ≤ R σ R₁ := le_sup_right.trans le_sup_left
theorem R₃_le_R : cj σ (cj σ R₁) ≤ R σ R₁ := le_sup_right

omit h in
theorem W_le_R' : W σ R₁ ≤ R σ R₁ := W_le_R

theorem comm_eq₁ {x₁ x₂ x₃ y : Q} (hx₁ : x₁ ∈ R₁) (hx₂ : x₂ ∈ cj σ R₁)
    (hx₃ : x₃ ∈ cj σ (cj σ R₁)) (hy : y ∈ R₁) : ⁅x₁ * x₂ * x₃, y⁆ = ⁅x₁, y⁆ := by
  have := h.comm3.comm_prod3 hx₁ hy hx₂ (one_mem _) hx₃ (one_mem _)
  simpa using this

theorem comm_eq₂ {x₁ x₂ x₃ y : Q} (hx₁ : x₁ ∈ R₁) (hx₂ : x₂ ∈ cj σ R₁)
    (hx₃ : x₃ ∈ cj σ (cj σ R₁)) (hy : y ∈ cj σ R₁) : ⁅x₁ * x₂ * x₃, y⁆ = ⁅x₂, y⁆ := by
  have := h.comm3.comm_prod3 hx₁ (one_mem _) hx₂ hy hx₃ (one_mem _)
  simpa using this

theorem comm_eq₃ {x₁ x₂ x₃ y : Q} (hx₁ : x₁ ∈ R₁) (hx₂ : x₂ ∈ cj σ R₁)
    (hx₃ : x₃ ∈ cj σ (cj σ R₁)) (hy : y ∈ cj σ (cj σ R₁)) : ⁅x₁ * x₂ * x₃, y⁆ = ⁅x₃, y⁆ := by
  have := h.comm3.comm_prod3 hx₁ (one_mem _) hx₂ (one_mem _) hx₃ hy
  simpa using this

theorem prod_mem_R {x₁ x₂ x₃ : Q} (hx₁ : x₁ ∈ R₁) (hx₂ : x₂ ∈ cj σ R₁)
    (hx₃ : x₃ ∈ cj σ (cj σ R₁)) : x₁ * x₂ * x₃ ∈ R σ R₁ :=
  (R σ R₁).mul_mem ((R σ R₁).mul_mem (h.R₁_le_R hx₁) (h.R₂_le_R hx₂)) (h.R₃_le_R hx₃)

theorem exists_section [Finite Q] (hW : Nat.card (W σ R₁) ≤ 9) {a : Q} (ha : a ∈ R σ R₁)
    (hσa : sg σ a = a) (hna : a ∉ W σ R₁) :
    ∃ S' : Subgroup Q, S' ≤ R σ R₁ ∧ (∀ s ∈ S', s * a = a * s) ∧
      (∀ z ∈ S', (∀ s ∈ S', z * s = s * z) → z ∈ W σ R₁) ∧ HasElemSection3 S' 4 := by
  have hc := h.comm3
  have hC := h.class2
  obtain ⟨a₁, ha₁, ζ₂, hζ₂, ζ₃, hζ₃, ha₁n, haeq⟩ := h.exists_gens ha hσa hna
  obtain ⟨b₁, hb₁, hab⟩ : ∃ b₁ ∈ R₁, a₁ * b₁ ≠ b₁ * a₁ := by
    by_contra hcon
    push Not at hcon
    exact ha₁n (mem_Zc.2 ⟨ha₁, hcon⟩)
  obtain ⟨a₂, ha₂d⟩ : ∃ a₂, a₂ = sg σ a₁ := ⟨_, rfl⟩
  obtain ⟨a₃, ha₃d⟩ : ∃ a₃, a₃ = sg σ a₂ := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂d⟩ : ∃ b₂, b₂ = sg σ b₁ := ⟨_, rfl⟩
  obtain ⟨b₃, hb₃d⟩ : ∃ b₃, b₃ = sg σ b₂ := ⟨_, rfl⟩
  have ha₂ : a₂ ∈ cj σ R₁ := ha₂d ▸ sg_mem_cj ha₁
  have ha₃ : a₃ ∈ cj σ (cj σ R₁) := ha₃d ▸ sg_mem_cj ha₂
  have hb₂ : b₂ ∈ cj σ R₁ := hb₂d ▸ sg_mem_cj hb₁
  have hb₃ : b₃ ∈ cj σ (cj σ R₁) := hb₃d ▸ sg_mem_cj hb₂
  have hab₂ : a₂ * b₂ ≠ b₂ * a₂ := by rw [ha₂d, hb₂d]; exact sg_noncomm hab σ
  have hab₃ : a₃ * b₃ ≠ b₃ * a₃ := by rw [ha₃d, hb₃d]; exact sg_noncomm hab₂ σ
  rw [← ha₂d, ← ha₃d] at haeq
  have hrel := h.rel ha₁ hb₁ hab hW
  have hz₂ : ⁅a₂, b₂⁆ = sg σ ⁅a₁, b₁⁆ := by rw [ha₂d, hb₂d, sg_comm]
  have hz₃ : ⁅a₃, b₃⁆ = sg σ ⁅a₂, b₂⁆ := by rw [ha₃d, hb₃d, sg_comm]
  have hz₁m : ⁅a₁, b₁⁆ ∈ Zc R₁ := h.heis.comm_mem_Zc ha₁ hb₁
  have hz₂m : ⁅a₂, b₂⁆ ∈ Zc (cj σ R₁) := h.heis₂.comm_mem_Zc ha₂ hb₂
  have hz₃m : ⁅a₃, b₃⁆ ∈ Zc (cj σ (cj σ R₁)) := h.heis₃.comm_mem_Zc ha₃ hb₃
  have hz₁1 : ⁅a₁, b₁⁆ ≠ 1 := commutatorElement_ne_one hab
  have hz₂1 : ⁅a₂, b₂⁆ ≠ 1 := commutatorElement_ne_one hab₂
  have hz₃1 : ⁅a₃, b₃⁆ ≠ 1 := commutatorElement_ne_one hab₃
  have hcl₁ : Subgroup.closure {a₁, b₁} = R₁ := h.heis.closure_eq ha₁ hb₁ hab
  have hcl₂ : Subgroup.closure {a₂, b₂} = cj σ R₁ := h.heis₂.closure_eq ha₂ hb₂ hab₂
  have hcl₃ : Subgroup.closure {a₃, b₃} = cj σ (cj σ R₁) := h.heis₃.closure_eq ha₃ hb₃ hab₃
  have hrel' : (⁅a₂, b₂⁆ = ⁅a₁, b₁⁆ ∧ ⁅a₃, b₃⁆ = ⁅a₁, b₁⁆) ∨
      (⁅a₁, b₁⁆ * ⁅a₂, b₂⁆ * ⁅a₃, b₃⁆ = 1 ∧ Zc R₁ ⊓ Zc (cj σ R₁) = ⊥ ∧
        Zc (cj σ R₁) ⊓ Zc (cj σ (cj σ R₁)) = ⊥ ∧ Nat.card (W σ R₁) = 9) := by
    rcases hrel with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · left
      refine ⟨by rw [hz₂]; exact h1, by rw [hz₃, hz₂]; exact h2⟩
    · right
      exact ⟨by rw [hz₂, hz₃, hz₂]; exact h1, h2, h3, h4⟩
  have hA₂ : a₂ * ζ₂ ∈ cj σ R₁ := (cj σ R₁).mul_mem ha₂ (Zc_le _ hζ₂)
  have hA₃ : a₃ * ζ₃ ∈ cj σ (cj σ R₁) := (cj σ (cj σ R₁)).mul_mem ha₃ (Zc_le _ hζ₃)
  have commA : ∀ {x₁ x₂ x₃ : Q}, x₁ ∈ R₁ → x₂ ∈ cj σ R₁ → x₃ ∈ cj σ (cj σ R₁) →
      ⁅x₁ * x₂ * x₃, a⁆ = ⁅x₁, a₁⁆ * ⁅x₂, a₂⁆ * ⁅x₃, a₃⁆ := by
    intro x₁ x₂ x₃ hx₁ hx₂ hx₃
    rw [haeq, hc.comm_prod3 hx₁ ha₁ hx₂ hA₂ hx₃ hA₃,
      comm_mul_central (((mem_Zc.1 hζ₂).2 x₂ hx₂).symm), comm_mul_central (((mem_Zc.1 hζ₃).2 x₃ hx₃).symm)]
  have hS_mem : ∀ {x₁ x₂ x₃ : Q}, x₁ ∈ R₁ → x₂ ∈ cj σ R₁ → x₃ ∈ cj σ (cj σ R₁) →
      ⁅x₁, a₁⁆ * ⁅x₂, a₂⁆ * ⁅x₃, a₃⁆ = 1 → ⁅x₁, b₁⁆ = 1 → x₁ * x₂ * x₃ ∈ S σ R₁ a b₁ := by
    intro x₁ x₂ x₃ hx₁ hx₂ hx₃ h1 h2
    refine h.mem_S.2 ⟨h.prod_mem_R hx₁ hx₂ hx₃, ?_, ?_⟩
    · have : ⁅x₁ * x₂ * x₃, a⁆ = 1 := by rw [commA hx₁ hx₂ hx₃]; exact h1
      exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
    · have : ⁅x₁ * x₂ * x₃, b₁⁆ = 1 := by rw [h.comm_eq₁ hx₁ hx₂ hx₃ hb₁]; exact h2
      exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
  have hsA2 : a₂ ∈ S σ R₁ a b₁ := by
    have := hS_mem (x₁ := 1) (x₂ := a₂) (x₃ := 1) (one_mem _) ha₂ (one_mem _)
      (by simp [commutatorElement_def]) (by simp [commutatorElement_def])
    simpa using this
  have hsA3 : a₃ ∈ S σ R₁ a b₁ := by
    have := hS_mem (x₁ := 1) (x₂ := 1) (x₃ := a₃) (one_mem _) (one_mem _) ha₃
      (by simp [commutatorElement_def]) (by simp [commutatorElement_def])
    simpa using this
  have hz123 : ⁅a₁, b₁⁆ * ⁅a₂, b₂⁆ * ⁅a₃, b₃⁆ = 1 := by
    rcases hrel' with ⟨e2, e3⟩ | ⟨e, -, -, -⟩
    · rw [e2, e3]
      have := h.heis.2.2 ⁅a₁, b₁⁆ (Zc_le _ hz₁m)
      simpa [pow_succ] using this
    · exact e
  have c23z : Commute ⁅a₂, b₂⁆ ⁅a₃, b₃⁆ := hc.c23 _ (Zc_le _ hz₂m) _ (Zc_le _ hz₃m)
  have hw : ⁅b₁, a₁⁆ * ⁅b₂, a₂⁆ * ⁅b₃, a₃⁆ = 1 := by
    rw [← commutatorElement_inv' (x := a₁) (y := b₁), ← commutatorElement_inv' (x := a₂) (y := b₂),
      ← commutatorElement_inv' (x := a₃) (y := b₃)]
    have e : ⁅a₁, b₁⁆⁻¹ = ⁅a₂, b₂⁆ * ⁅a₃, b₃⁆ := inv_eq_of_mul_eq_one_right (by
      rw [← mul_assoc]; exact hz123)
    rw [e]
    calc ⁅a₂, b₂⁆ * ⁅a₃, b₃⁆ * ⁅a₂, b₂⁆⁻¹ * ⁅a₃, b₃⁆⁻¹ = ⁅⁅a₂, b₂⁆, ⁅a₃, b₃⁆⁆ := rfl
      _ = 1 := commutatorElement_eq_one_iff_mul_comm.2 c23z.eq
  have hsB : b₁ * b₂ * b₃ ∈ S σ R₁ a b₁ :=
    hS_mem hb₁ hb₂ hb₃ hw (by simp [commutatorElement_def])
  have hb₁R : b₁ ∈ R σ R₁ := h.R₁_le_R hb₁
  have hb₂R : b₂ ∈ R σ R₁ := h.R₂_le_R hb₂
  have hb₃R : b₃ ∈ R σ R₁ := h.R₃_le_R hb₃
  have ha₁R : a₁ ∈ R σ R₁ := h.R₁_le_R ha₁
  have ha₂R : a₂ ∈ R σ R₁ := h.R₂_le_R ha₂
  have ha₃R : a₃ ∈ R σ R₁ := h.R₃_le_R ha₃
  have hcaseA : (⁅a₂, b₂⁆ = ⁅a₁, b₁⁆ ∧ ⁅a₃, b₃⁆ = ⁅a₁, b₁⁆) →
      (b₁ * b₂⁻¹ * 1 ∈ S σ R₁ a b₁ ∧ 1 * b₂ * b₃⁻¹ ∈ S σ R₁ a b₁) := by
    rintro ⟨e2, e3⟩
    refine ⟨hS_mem hb₁ ((cj σ R₁).inv_mem hb₂) (one_mem _) ?_ (by simp [commutatorElement_def]),
      hS_mem (one_mem _) hb₂ ((cj σ (cj σ R₁)).inv_mem hb₃) ?_ (by simp [commutatorElement_def])⟩
    · rw [hC.inv_left hb₂R ha₂R, ← commutatorElement_inv' (x := a₁) (y := b₁),
        ← commutatorElement_inv' (x := a₂) (y := b₂), e2]
      simp only [commutatorElement_def]; group
    · rw [hC.inv_left hb₃R ha₃R, ← commutatorElement_inv' (x := a₃) (y := b₃),
        ← commutatorElement_inv' (x := a₂) (y := b₂), e2, e3]
      simp only [commutatorElement_def]; group
  have hcenter : ∀ g ∈ S σ R₁ a b₁, (∀ s ∈ S σ R₁ a b₁, g * s = s * g) → g ∈ W σ R₁ := by
    intro g hg hgc
    obtain ⟨hgR, hga, hgb⟩ := h.mem_S.1 hg
    obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, rfl⟩ := hc.mem_sup3 hgR
    have e2 : ⁅x₂, a₂⁆ = 1 := by
      have h' : ⁅x₁ * x₂ * x₃, a₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hgc a₂ hsA2)
      rwa [h.comm_eq₂ hx₁ hx₂ hx₃ ha₂] at h'
    have e3 : ⁅x₃, a₃⁆ = 1 := by
      have h' : ⁅x₁ * x₂ * x₃, a₃⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hgc a₃ hsA3)
      rwa [h.comm_eq₃ hx₁ hx₂ hx₃ ha₃] at h'
    have e1 : ⁅x₁, a₁⁆ = 1 := by
      have h' : ⁅x₁ * x₂ * x₃, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hga.symm
      rw [commA hx₁ hx₂ hx₃, e2, e3] at h'
      simpa using h'
    have f1 : ⁅x₁, b₁⁆ = 1 := by
      have h' : ⁅x₁ * x₂ * x₃, b₁⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hgb.symm
      rwa [h.comm_eq₁ hx₁ hx₂ hx₃ hb₁] at h'
    have hgb' : ⁅x₂, b₂⁆ * ⁅x₃, b₃⁆ = 1 := by
      have h' : ⁅x₁ * x₂ * x₃, b₁ * b₂ * b₃⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (hgc _ hsB)
      rw [hc.comm_prod3 hx₁ hb₁ hx₂ hb₂ hx₃ hb₃, f1] at h'
      simpa using h'
    have f2f3 : ⁅x₂, b₂⁆ = 1 ∧ ⁅x₃, b₃⁆ = 1 := by
      rcases hrel' with ⟨e2', e3'⟩ | ⟨-, -, hI23, -⟩
      · obtain ⟨hv1, -⟩ := hcaseA ⟨e2', e3'⟩
        have h' : ⁅x₁ * x₂ * x₃, b₁ * b₂⁻¹ * 1⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.2 (hgc _ hv1)
        rw [hc.comm_prod3 hx₁ hb₁ hx₂ ((cj σ R₁).inv_mem hb₂) hx₃ (one_mem _), f1,
          hC.inv_right (h.R₂_le_R hx₂) hb₂R] at h'
        simp only [one_mul, commutatorElement_one_right, mul_one, inv_eq_one] at h'
        refine ⟨h', ?_⟩
        rw [h', one_mul] at hgb'; exact hgb'
      · have m2 : ⁅x₂, b₂⁆ ∈ Zc (cj σ R₁) := h.heis₂.comm_mem_Zc hx₂ hb₂
        have m3 : ⁅x₃, b₃⁆ ∈ Zc (cj σ (cj σ R₁)) := h.heis₃.comm_mem_Zc hx₃ hb₃
        have hmem : ⁅x₂, b₂⁆ ∈ Zc (cj σ R₁) ⊓ Zc (cj σ (cj σ R₁)) := ⟨m2, by
          have : ⁅x₂, b₂⁆ = ⁅x₃, b₃⁆⁻¹ := eq_inv_of_mul_eq_one_left hgb'
          rw [this]; exact (Zc _).inv_mem m3⟩
        rw [hI23, Subgroup.mem_bot] at hmem
        refine ⟨hmem, ?_⟩
        rw [hmem, one_mul] at hgb'; exact hgb'
    have z1 : x₁ ∈ Zc R₁ := mem_Zc_of_closure hcl₁ hx₁ e1 f1
    have z2 : x₂ ∈ Zc (cj σ R₁) := mem_Zc_of_closure hcl₂ hx₂ e2 f2f3.1
    have z3 : x₃ ∈ Zc (cj σ (cj σ R₁)) := mem_Zc_of_closure hcl₃ hx₃ e3 f2f3.2
    exact (W σ R₁).mul_mem ((W σ R₁).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left z1))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right z2))) (Subgroup.mem_sup_right z3)
  have hWS : W σ R₁ ≤ S σ R₁ a b₁ := fun w hw =>
    h.mem_S.2 ⟨(W_le_R (σ := σ) (R₁ := R₁)) hw, (h.W_central w hw a ha).symm,
      (h.W_central w hw b₁ hb₁R).symm⟩
  have hz₁W : ⁅a₁, b₁⁆ ∈ W σ R₁ := Subgroup.mem_sup_left (Subgroup.mem_sup_left hz₁m)
  have hz₂W : ⁅a₂, b₂⁆ ∈ W σ R₁ := Subgroup.mem_sup_left (Subgroup.mem_sup_right hz₂m)
  have hz₃W : ⁅a₃, b₃⁆ ∈ W σ R₁ := Subgroup.mem_sup_right hz₃m
  have hSR : S σ R₁ a b₁ ≤ R σ R₁ := h.S_le_R
  refine ⟨S σ R₁ a b₁, hSR, fun s hs => (h.mem_S.1 hs).2.1.symm, hcenter, ?_⟩
  have hexp : ∀ D : Subgroup Q, D ≤ R σ R₁ → ∀ g ∈ D, g ^ 3 = 1 :=
    fun D hD g hg => h.exp3_R (hD hg)
  have cb2 : ∀ w ∈ W σ R₁, w * b₂ = b₂ * w := fun w hw => h.W_central w hw b₂ hb₂R
  have cb3 : ∀ w ∈ W σ R₁, w * b₃ = b₃ * w := fun w hw => h.W_central w hw b₃ hb₃R
  have ca23 : a₂ * a₃ = a₃ * a₂ := hc.c23 _ ha₂ _ ha₃
  have ca2b3 : a₂ * b₃ = b₃ * a₂ := hc.c23 _ ha₂ _ hb₃
  have hsz : ∀ {x : Q}, x ∈ W σ R₁ → x ∈ S σ R₁ a b₁ := fun hx => hWS hx
  rcases hrel' with ⟨e2, e3⟩ | ⟨hz, hI12, hI23, hW9⟩
  ·
    obtain ⟨hv1', hv2'⟩ := hcaseA ⟨e2, e3⟩
    have hv1 : b₁ * b₂⁻¹ ∈ S σ R₁ a b₁ := by simpa using hv1'
    have hv2 : b₂ * b₃⁻¹ ∈ S σ R₁ a b₁ := by simpa using hv2'
    have hv1a2 : ⁅b₁ * b₂⁻¹, a₂⁆ = ⁅a₂, b₂⁆ := by
      have := hc.comm_prod3 hb₁ (one_mem _) ((cj σ R₁).inv_mem hb₂) ha₂ (one_mem (cj σ (cj σ R₁)))
        (one_mem _)
      simp only [mul_one, one_mul, commutatorElement_one_left, commutatorElement_one_right] at this
      rw [this, hC.inv_left hb₂R ha₂R, commutatorElement_inv']
    have hv1a3 : ⁅b₁ * b₂⁻¹, a₃⁆ = 1 := by
      have := hc.comm_prod3 hb₁ (one_mem _) ((cj σ R₁).inv_mem hb₂) (one_mem _) (one_mem _) ha₃
      simp only [mul_one, one_mul, commutatorElement_one_left, commutatorElement_one_right] at this
      exact this
    have hv2a3 : ⁅b₂ * b₃⁻¹, a₃⁆ = ⁅a₃, b₃⁆ := by
      have := hc.comm_prod3 (one_mem _) (one_mem _) hb₂ (one_mem _) ((cj σ (cj σ R₁)).inv_mem hb₃) ha₃
      simp only [mul_one, one_mul, commutatorElement_one_left, commutatorElement_one_right] at this
      rw [this, hC.inv_left hb₃R ha₃R, commutatorElement_inv']
    have hWcent : ∀ {y : Q}, y ∈ R σ R₁ → W σ R₁ ≤ Subgroup.centralizer ({y} : Set Q) := by
      intro y hy w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.W_central w hw y hy
    have hfin : Finite ↥(W σ R₁) := inferInstance
    set D₁ : Subgroup Q := W σ R₁ ⊔ Subgroup.zpowers a₂ with hD₁
    set D₂ : Subgroup Q := D₁ ⊔ Subgroup.zpowers a₃ with hD₂
    set D₃ : Subgroup Q := D₂ ⊔ Subgroup.zpowers (b₁ * b₂⁻¹) with hD₃
    set D₄ : Subgroup Q := D₃ ⊔ Subgroup.zpowers (b₂ * b₃⁻¹) with hD₄
    have hD₁S : D₁ ≤ S σ R₁ a b₁ := sup_le hWS (Subgroup.zpowers_le.2 hsA2)
    have hD₂S : D₂ ≤ S σ R₁ a b₁ := sup_le hD₁S (Subgroup.zpowers_le.2 hsA3)
    have hD₃S : D₃ ≤ S σ R₁ a b₁ := sup_le hD₂S (Subgroup.zpowers_le.2 hv1)
    have hD₄S : D₄ ≤ S σ R₁ a b₁ := sup_le hD₃S (Subgroup.zpowers_le.2 hv2)
    have n1 : a₂ ∉ W σ R₁ := not_mem_of_centralizer (hWcent hb₂R) (by
      intro h2; exact hab₂ h2)
    have n2 : a₃ ∉ D₁ := not_mem_of_centralizer (y := b₃) (sup_le (hWcent hb₃R)
      (zpowers_le_cent ca2b3)) (by intro h2; exact hab₃ h2)
    have n3 : b₁ * b₂⁻¹ ∉ D₂ := by
      refine not_mem_of_centralizer (y := a₂) (sup_le (sup_le (hWcent ha₂R)
        (zpowers_le_cent rfl)) (zpowers_le_cent ca23.symm)) ?_
      intro h2
      have := commutatorElement_eq_one_iff_mul_comm.2 h2
      rw [hv1a2] at this
      exact hz₂1 this
    have n4 : b₂ * b₃⁻¹ ∉ D₃ := by
      refine not_mem_of_centralizer (y := a₃) (sup_le (sup_le (sup_le (hWcent ha₃R)
        (zpowers_le_cent ca23)) (zpowers_le_cent rfl))
        (zpowers_le_cent (commutatorElement_eq_one_iff_mul_comm.1 hv1a3))) ?_
      intro h2
      have := commutatorElement_eq_one_iff_mul_comm.2 h2
      rw [hv2a3] at this
      exact hz₃1 this
    have hR1 : ∀ g ∈ D₁, g ^ 3 = 1 := hexp _ (hD₁S.trans hSR)
    have hR2 : ∀ g ∈ D₂, g ^ 3 = 1 := hexp _ (hD₂S.trans hSR)
    have hR3 : ∀ g ∈ D₃, g ^ 3 = 1 := hexp _ (hD₃S.trans hSR)
    have hR4 : ∀ g ∈ D₄, g ^ 3 = 1 := hexp _ (hD₄S.trans hSR)
    have c1 : 3 * Nat.card (W σ R₁) ≤ Nat.card D₁ :=
      three_mul_card_le (C := W σ R₁) (x := a₂) hR1 n1
    have c2 : 3 * Nat.card D₁ ≤ Nat.card D₂ := three_mul_card_le (C := D₁) (x := a₃) hR2 n2
    have c3 : 3 * Nat.card D₂ ≤ Nat.card D₃ :=
      three_mul_card_le (C := D₂) (x := b₁ * b₂⁻¹) hR3 n3
    have c4 : 3 * Nat.card D₃ ≤ Nat.card D₄ :=
      three_mul_card_le (C := D₃) (x := b₂ * b₃⁻¹) hR4 n4
    refine ⟨D₄, W σ R₁, ?_, hD₄S, ?_, ?_, ?_, ?_⟩
    · exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · intro g hg k hk
      have hgR : g ∈ R σ R₁ := hSR (hD₄S hg)
      have : g * k * g⁻¹ = k := by
        rw [← h.W_central k hk g hgR]; group
      rw [this]; exact hk
    · intro g hg g' hg'
      exact hC.comm_mem g (hSR (hD₄S hg)) g' (hSR (hD₄S hg'))
    · intro g hg
      rw [hR4 g hg]; exact one_mem _
    · have hmul := index_subgroupOf_mul_card (show W σ R₁ ≤ D₄ from
        le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
      have hpos : 0 < Nat.card ↥(W σ R₁) := Nat.card_pos
      have h81 : 81 * Nat.card ↥(W σ R₁) ≤ Nat.card D₄ := by omega
      have : 3 ^ 4 * Nat.card ↥(W σ R₁) ≤ ((W σ R₁).subgroupOf D₄).index * Nat.card ↥(W σ R₁) := by
        rw [hmul]; norm_num; exact h81
      exact Nat.le_of_mul_le_mul_right this hpos
  ·
    have hZ₁ : Zc R₁ = Subgroup.zpowers ⁅a₁, b₁⁆ := h.heis.Zc_eq_zpowers ha₁ hb₁ hab
    have hz₁S : ⁅a₁, b₁⁆ ∈ S σ R₁ a b₁ := hWS hz₁W
    have hz₂S : ⁅a₂, b₂⁆ ∈ S σ R₁ a b₁ := hWS hz₂W
    have cz1b2 : ⁅a₁, b₁⁆ * b₂ = b₂ * ⁅a₁, b₁⁆ := hc.c12 _ (Zc_le _ hz₁m) _ hb₂
    have cz1b3 : ⁅a₁, b₁⁆ * b₃ = b₃ * ⁅a₁, b₁⁆ := hc.c13 _ (Zc_le _ hz₁m) _ hb₃
    have cz2b3 : ⁅a₂, b₂⁆ * b₃ = b₃ * ⁅a₂, b₂⁆ := hc.c23 _ (Zc_le _ hz₂m) _ hb₃
    have cz2b2 : ⁅a₂, b₂⁆ * b₂ = b₂ * ⁅a₂, b₂⁆ := (mem_Zc.1 hz₂m).2 b₂ hb₂
    have cz12 : ⁅a₁, b₁⁆ * ⁅a₂, b₂⁆ = ⁅a₂, b₂⁆ * ⁅a₁, b₁⁆ :=
      hc.c12 _ (Zc_le _ hz₁m) _ (Zc_le _ hz₂m)
    have cz1a2 : ⁅a₁, b₁⁆ * a₂ = a₂ * ⁅a₁, b₁⁆ := hc.c12 _ (Zc_le _ hz₁m) _ ha₂
    have cz2a2 : ⁅a₂, b₂⁆ * a₂ = a₂ * ⁅a₂, b₂⁆ := (mem_Zc.1 hz₂m).2 a₂ ha₂
    have cz1a3 : ⁅a₁, b₁⁆ * a₃ = a₃ * ⁅a₁, b₁⁆ := hc.c13 _ (Zc_le _ hz₁m) _ ha₃
    have cz2a3 : ⁅a₂, b₂⁆ * a₃ = a₃ * ⁅a₂, b₂⁆ := hc.c23 _ (Zc_le _ hz₂m) _ ha₃
    have hz₁3 : ⁅a₁, b₁⁆ ^ 3 = 1 := h.exp3_R (h.R₁_le_R (Zc_le _ hz₁m))
    have hz₂3 : ⁅a₂, b₂⁆ ^ 3 = 1 := h.exp3_R (h.R₂_le_R (Zc_le _ hz₂m))
    have ha₂3 : a₂ ^ 3 = 1 := h.exp3_R ha₂R
    have ha₃3 : a₃ ^ 3 = 1 := h.exp3_R ha₃R
    have hz₂nZ₁ : ⁅a₂, b₂⁆ ∉ Subgroup.zpowers ⁅a₁, b₁⁆ := by
      intro hmem
      have : ⁅a₂, b₂⁆ ∈ Zc R₁ ⊓ Zc (cj σ R₁) := ⟨by rw [hZ₁]; exact hmem, hz₂m⟩
      rw [hI12, Subgroup.mem_bot] at this
      exact hz₂1 this
    set D₁ : Subgroup Q := (⊥ : Subgroup Q) ⊔ Subgroup.zpowers ⁅a₁, b₁⁆ with hD₁
    set D₂ : Subgroup Q := D₁ ⊔ Subgroup.zpowers ⁅a₂, b₂⁆ with hD₂
    set D₃ : Subgroup Q := D₂ ⊔ Subgroup.zpowers a₂ with hD₃
    set D₄ : Subgroup Q := D₃ ⊔ Subgroup.zpowers a₃ with hD₄
    have hD₁S : D₁ ≤ S σ R₁ a b₁ := sup_le bot_le (Subgroup.zpowers_le.2 hz₁S)
    have hD₂S : D₂ ≤ S σ R₁ a b₁ := sup_le hD₁S (Subgroup.zpowers_le.2 hz₂S)
    have hD₃S : D₃ ≤ S σ R₁ a b₁ := sup_le hD₂S (Subgroup.zpowers_le.2 hsA2)
    have hD₄S : D₄ ≤ S σ R₁ a b₁ := sup_le hD₃S (Subgroup.zpowers_le.2 hsA3)
    have n1 : ⁅a₁, b₁⁆ ∉ (⊥ : Subgroup Q) := by
      intro hm; exact hz₁1 (Subgroup.mem_bot.1 hm)
    have n2 : ⁅a₂, b₂⁆ ∉ D₁ := by
      intro hm
      rw [hD₁, bot_sup_eq] at hm
      exact hz₂nZ₁ hm
    have n3 : a₂ ∉ D₂ := not_mem_of_centralizer (y := b₂) (sup_le (sup_le bot_le
      (zpowers_le_cent cz1b2)) (zpowers_le_cent cz2b2)) (by intro h2; exact hab₂ h2)
    have n4 : a₃ ∉ D₃ := not_mem_of_centralizer (y := b₃) (sup_le (sup_le (sup_le bot_le
      (zpowers_le_cent cz1b3)) (zpowers_le_cent cz2b3)) (zpowers_le_cent ca2b3))
      (by intro h2; exact hab₃ h2)
    have hR1 : ∀ g ∈ D₁, g ^ 3 = 1 := hexp _ (hD₁S.trans hSR)
    have hR2 : ∀ g ∈ D₂, g ^ 3 = 1 := hexp _ (hD₂S.trans hSR)
    have hR3 : ∀ g ∈ D₃, g ^ 3 = 1 := hexp _ (hD₃S.trans hSR)
    have hR4 : ∀ g ∈ D₄, g ^ 3 = 1 := hexp _ (hD₄S.trans hSR)
    have c1 : 3 * Nat.card (⊥ : Subgroup Q) ≤ Nat.card D₁ :=
      three_mul_card_le (C := ⊥) (x := ⁅a₁, b₁⁆) hR1 n1
    have c2 : 3 * Nat.card D₁ ≤ Nat.card D₂ :=
      three_mul_card_le (C := D₁) (x := ⁅a₂, b₂⁆) hR2 n2
    have c3 : 3 * Nat.card D₂ ≤ Nat.card D₃ := three_mul_card_le (C := D₂) (x := a₂) hR3 n3
    have c4 : 3 * Nat.card D₃ ≤ Nat.card D₄ := three_mul_card_le (C := D₃) (x := a₃) hR4 n4
    have hD₄eq : D₄ = Subgroup.zpowers ⁅a₁, b₁⁆ ⊔ Subgroup.zpowers ⁅a₂, b₂⁆ ⊔
        Subgroup.zpowers a₂ ⊔ Subgroup.zpowers a₃ := by
      simp [hD₄, hD₃, hD₂, hD₁]
    have hab4 : IsElemAbelian 3 D₄ := by
      rw [hD₄eq]
      exact isElemAbelian_sup_of_commute (isElemAbelian_sup_of_commute
        (isElemAbelian_sup_of_commute (isElemAbelian_zpowers hz₁3) (isElemAbelian_zpowers hz₂3)
          (zpowers_le_cent_zpowers cz12))
        (isElemAbelian_zpowers ha₂3)
        (sup_le (zpowers_le_cent_zpowers cz1a2) (zpowers_le_cent_zpowers cz2a2)))
        (isElemAbelian_zpowers ha₃3)
        (sup_le (sup_le (zpowers_le_cent_zpowers cz1a3) (zpowers_le_cent_zpowers cz2a3))
          (zpowers_le_cent_zpowers ca23))
    refine ⟨D₄, ⊥, bot_le, hD₄S, ?_, ?_, ?_, ?_⟩
    · intro g hg k hk
      rw [Subgroup.mem_bot] at hk
      subst hk; simp
    · intro g hg g' hg'
      rw [Subgroup.mem_bot]
      have hcomm : g * g' = g' * g := elemAbelian_comm hab4 hg hg'
      rw [hcomm]; group
    · intro g hg
      rw [Subgroup.mem_bot]; exact hR4 g hg
    · have hmul := index_subgroupOf_mul_card (show (⊥ : Subgroup Q) ≤ D₄ from bot_le)
      rw [Subgroup.card_bot, mul_one] at hmul
      rw [Subgroup.card_bot] at c1
      rw [hmul]; norm_num; omega

end Triple

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
