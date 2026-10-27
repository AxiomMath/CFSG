module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisRoot
public import CFSG.LieType.Ree.SmallReeFrattini

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.LieType.Ree CFSG.Blueprint.Chevalley

theorem pow_three_pow_injective {K : Type} [Field K] [CharP K 3] (a : ℕ) :
    Function.Injective fun x : K => x ^ 3 ^ a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x y h
  have h' : iterateFrobenius K 3 a x = iterateFrobenius K 3 a y := by
    simpa [iterateFrobenius_def] using h
  exact (iterateFrobenius K 3 a).injective h'


theorem two_pow_le_card_of_reeGamma {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {L : Subgroup (MulAut W)}
    (π : ↥L →* ↥(ReeTag.G2.reeGamma K a)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hZ : ¬ 3 ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod 3) * ((Nat.card K - 1) * Nat.card K / (3 - 1))) ≤ Nat.card W := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := by simpa [ReeTag.prime] using (inferInstance : CharP K ReeTag.G2.prime)
  have hle : ReeTag.G2.reeFixedPosUnipotent K a ≤ ReeTag.G2.reeGamma K a := inf_le_right
  let ι := Subgroup.inclusion hle
  let u : K → K → K → ↥(ReeTag.G2.reeGamma K a) := fun t b c =>
    ι (ReeTag.smallReeCoordU hK t b c)
  have hu_mul : ∀ t b c s d e, u t b c * u s d e =
      u (t + s) (b + d + smallReeSigma a t * s) (c + e - b * s + smallReeSigma a t * s ^ 2) :=
    fun t b c s d e => by
      simp only [u, ← map_mul, ReeTag.smallReeCoordU_mul hK]
  have hu_zero : u 0 0 0 = 1 := by
    simp only [u, ReeTag.smallReeCoordU_zero hK, map_one]
  have hu_val : ∀ t b c, ((u t b c : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) =
      smallReeCoord a K t b c := fun _ _ _ => rfl
  have hσ0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  let z : Multiplicative K →* ↥(ReeTag.G2.reeGamma K a) :=
    { toFun := fun c => u 0 0 (Multiplicative.toAdd c)
      map_one' := hu_zero
      map_mul' := fun c c' => by
        rw [hu_mul]
        simp [hσ0] }
  let A : Multiplicative K →* ↥(ReeTag.G2.reeGamma K a) :=
    { toFun := fun b => u 0 (Multiplicative.toAdd b) 0
      map_one' := hu_zero
      map_mul' := fun b b' => by
        rw [hu_mul]
        simp [hσ0] }
  let B : K → ↥(ReeTag.G2.reeGamma K a) := fun v => u v 0 0
  have hinv : ∀ t : K, (u t 0 0)⁻¹ = u (-t) (t * smallReeSigma a t) (-(t ^ 2 * smallReeSigma a t)) := by
    intro t
    rw [inv_eq_iff_mul_eq_one, hu_mul, ← hu_zero]
    congr 1 <;> ring
  have hzA : ∀ c b, z c * A b = A b * z c := by
    intro c b
    show u 0 0 _ * u 0 _ 0 = u 0 _ 0 * u 0 0 _
    rw [hu_mul, hu_mul]
    simp [hσ0]
  have hBz : ∀ (c : Multiplicative K) (v : K), B v * z c = z c * B v := by
    intro c v
    show u v 0 0 * u 0 0 _ = u 0 0 _ * u v 0 0
    rw [hu_mul, hu_mul]
    simp [hσ0]
  have hBA : ∀ (b v : K), B v * A (Multiplicative.ofAdd b) * (B v)⁻¹ =
      A (Multiplicative.ofAdd b) * z (Multiplicative.ofAdd (b * v)) := by
    intro b v
    show u v 0 0 * u 0 b 0 * (u v 0 0)⁻¹ = u 0 b 0 * u 0 0 (b * v)
    rw [hinv, hu_mul, hu_mul, hu_mul]
    congr 1 <;> simp [hσ0] <;> ring
  have hinj : ∀ (c b : K), z (Multiplicative.ofAdd c) * A (Multiplicative.ofAdd b) = 1 →
      c = 0 ∧ b = 0 := by
    intro c b h
    have h1 : u 0 b c = u 0 0 0 := by
      have h2 : z (Multiplicative.ofAdd c) * A (Multiplicative.ofAdd b) = u 0 b c := by
        show u 0 0 c * u 0 b 0 = u 0 b c
        rw [hu_mul]
        simp [hσ0]
      rw [← h2, h, hu_zero]
    have h3 := ReeTag.smallReeCoordU_injective hK (Subgroup.inclusion_injective hle h1)
    exact ⟨h3.2.2, h3.2.1⟩
  obtain ⟨⟨φ, hφ⟩, hconj, -, -⟩ := small_Ree_positive_torus_action a K hK
  let t : Kˣ →* ↥(ReeTag.G2.reeGamma K a) :=
    (Subgroup.inclusion (inf_le_right : ReeTag.G2.reeFixedTorus K a ≤ ReeTag.G2.reeGamma K a)).comp
      φ.toMonoidHom
  have ht : ∀ s, ((t s : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) =
      smallReeTorusElt a K s := fun s => hφ s
  let χ : Kˣ →* Kˣ := powMonoidHom (3 ^ a)
  have htz : ∀ (s : Kˣ) (c : K), t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)) := by
    intro s c
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht]
    have := hconj s 0 0 c
    simp only [mul_zero] at this
    rw [show ((χ s : Kˣ) : K) = (s : K) ^ 3 ^ a by simp [χ]]
    exact this
  have hta : ∀ (s : Kˣ) (b : K), ∃ b', t s * A (Multiplicative.ofAdd b) * (t s)⁻¹ =
      A (Multiplicative.ofAdd b') := by
    intro s b
    refine ⟨(((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b), Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht]
    have := hconj s 0 b 0
    simp only [mul_zero] at this
    exact this
  have hχ : Nat.card χ.range = Nat.card K - 1 := by
    have hinjχ : Function.Injective χ := by
      intro s s' h
      apply Units.ext
      apply pow_three_pow_injective (K := K) a
      have := congrArg (fun x : Kˣ => (x : K)) h
      simpa [χ] using this
    rw [← Nat.card_congr (MonoidHom.ofInjective hinjχ).toEquiv, Nat.card_units]
  have hmain := FFToolkit.two_pow_le_card_of_heis_root hW (p := 3) (by norm_num) π hπ hker hZ
    (K := K) (V := K) z A B (LinearMap.mul K K)
    (fun v hv => ⟨1, by simpa using hv⟩) hinj hzA
    (fun b v => by simpa [LinearMap.mul_apply'] using hBA b v) hBz t χ htz hta
  rwa [hχ] at hmain

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
