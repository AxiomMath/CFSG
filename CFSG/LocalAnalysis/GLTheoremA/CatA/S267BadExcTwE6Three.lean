module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.Universal.Unitary (SU SUid antidiag conjTr conjEquiv)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelBGen)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU mem_coordBlockSU_iff)

@[expose] def snocOneHom (G : Type*) [Group G] (m : ℕ) : (Fin m → G) →* (Fin (m + 1) → G) where
  toFun x := Fin.snoc x 1
  map_one' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  map_mul' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

theorem snocOneHom_apply_castSucc {G : Type*} [Group G] {m : ℕ} (x : Fin m → G) (j : Fin m) :
    snocOneHom G m x j.castSucc = x j := by
  simp [snocOneHom]

theorem snocOneHom_apply_last {G : Type*} [Group G] {m : ℕ} (x : Fin m → G) :
    snocOneHom G m x (Fin.last m) = 1 := by
  simp [snocOneHom]

theorem snocOneHom_injective (G : Type*) [Group G] (m : ℕ) : Function.Injective (snocOneHom G m) := by
  intro x y h
  funext j
  have := congrFun h j.castSucc
  rwa [snocOneHom_apply_castSucc, snocOneHom_apply_castSucc] at this

section Diag


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {p : ℕ}
  [Fact p.Prime] (c : Kˣ) (hc : orderOf c = p) (hpQ : p ∣ ℓ ^ f + 1)

@[expose] noncomputable def diagThreeHom : (Fin 4 → Multiplicative (ZMod p)) →* Su K ℓ f 6 :=
  (diagSUHom c hc hpQ).comp (snocOneHom (Multiplicative (ZMod p)) 4)

theorem diagThreeHom_injective : Function.Injective (diagThreeHom c hc hpQ) :=
  (diagSUHom_injective c hc hpQ).comp (snocOneHom_injective _ 4)

theorem coe_diagThreeHom (x : Fin 4 → Multiplicative (ZMod p)) :
    (((diagThreeHom c hc hpQ x : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal fun i => (diagTuple c hc (snocOneHom (Multiplicative (ZMod p)) 4 x) i : K) :=
  rfl

theorem diagThreeHom_apply_four (x : Fin 4 → Multiplicative (ZMod p)) :
    (diagTuple c hc (snocOneHom (Multiplicative (ZMod p)) 4 x) 4 : K) = 1 := by
  have h := diagTuple_castSucc c hc (snocOneHom (Multiplicative (ZMod p)) 4 x) (Fin.last 4)
  rw [snocOneHom_apply_last, map_one] at h
  have e : (Fin.last 4).castSucc = (4 : Fin 6) := rfl
  rw [e] at h
  rw [h, Units.val_one]

variable {hK : Nat.card K = (ℓ ^ f) ^ 2} {hf : 1 ≤ f} {ζ : K} {hζ : ζ ≠ 0}
  {hσζ : unitaryInvolution K ℓ f ζ = -ζ} {P : GL (Fin 6) K}
  {hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6}

theorem leviSU_comp_diagThreeHom_injective :
    Function.Injective ((leviSU hK hf hζ hσζ P hP).comp (diagThreeHom c hc hpQ)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨μ, hμ⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP hx
  have e44 := congrFun (congrFun hμ 4) 4
  rw [coe_diagThreeHom, diagonal_apply_eq, diagThreeHom_apply_four] at e44
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e44
  have h1 : diagThreeHom c hc hpQ x = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hμ, ← e44, one_smul]
    rfl
  exact diagThreeHom_injective c hc hpQ (h1.trans (map_one _).symm)

end Diag

section Transport


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_twistedE6_of_not_mem_inndiag_of_model (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hf : 1 ≤ f) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n) (hS : S.Normal)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hBn : Nat.card B ≤ p ^ (n + 2))
    {φ : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →* Ω} (hφ : Function.Injective φ)
    (hφS : φ.range = S) {b : Ω} (hb : b ∈ B)
    {β : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hβ : β ∉ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f))
    (hβφ : ∀ x, φ (β x) = b * φ x * b⁻¹)
    (hM : ∀ ε : K ≃+* K, orderOf ε = p → fieldActor (unitaryInvolution K ℓ f) ε ∉
        (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
          MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range →
      ModelBGen p n ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))
        (fieldActor (unitaryInvolution K ℓ f) ε)) :
    S267ConcA p S B := by
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Finite.of_injective φ hφ
  haveI : Fact p.Prime := ⟨hp⟩
  have hσ : ∀ c, unitaryInvolution K ℓ f c = c ^ (ℓ ^ f) := fun c => unitaryInvolution_apply K ℓ f c
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form (Fact.out : ℓ.Prime) hf K hK
      (unitaryInvolution K ℓ f) hσ
  have hbp : b ^ p = 1 := hB.2 b hb
  have hβk : ∀ k : ℕ, ∀ x, φ ((β ^ k) x) = b ^ k * φ x * (b ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ β k, MulAut.mul_apply, ih, hβφ, pow_succ b k]
      group
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun x => hφ ?_
    rw [hβk p x, hbp, one_mul, inv_one, mul_one, MulAut.one_apply]
  have hΘβ : Θ β ≠ 1 := fun h => hβ (by rw [← hker]; exact MonoidHom.mem_ker.2 h)
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨d, -, -, r, ε₀, -, ψ', -, hψ'⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_conj_of_prime_order
      (Fact.out : ℓ.Prime) hf K hK' (unitaryInvolution K ℓ f) hσ Θ hΘ hp hp2 β hβp hΘβ
  have hεp : Θ β ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hεo : orderOf (Θ β) = p := orderOf_eq_prime hεp hΘβ
  have hout : fieldActor (unitaryInvolution K ℓ f) (Θ β) ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range := by
    rintro ⟨g, hg⟩
    apply hβ
    refine Subgroup.mem_sup_left ⟨ψ'⁻¹ g, MulEquiv.ext fun x => ?_⟩
    have h1 : β = ψ'⁻¹ * fieldActor (unitaryInvolution K ℓ f) (Θ β) * ψ' := by
      rw [← hψ']
      group
    rw [h1, ← hg, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv, MulAut.inv_apply_self]
  refine ModelGen.concA_of_modelBGen hp hn hS hcore hZ hB hBC hBn (φ.comp ψ'.symm.toMonoidHom)
    (hφ.comp ψ'.symm.injective) ?_ hbp
    (fun c hc => congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc.1⟩)) (fun x => ?_)
    (hM (Θ β) hεo hout)
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ'.symm.surjective,
      ← MonoidHom.range_eq_map, hφS]
  · rw [← hψ', MulAut.mul_apply, MulAut.mul_apply]
    change b * φ (ψ'.symm x) * b⁻¹ = φ (ψ'.symm (ψ' (β (ψ'⁻¹ x))))
    rw [MulEquiv.symm_apply_apply, hβφ]
    rfl

end Transport

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

end
