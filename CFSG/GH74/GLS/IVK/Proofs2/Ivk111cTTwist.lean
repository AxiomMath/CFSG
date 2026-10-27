module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface

public section

namespace CFSG.GH74.GLS.Stage4.Rest

section Twist

variable {F : Type} [Field F]

theorem pow_mul_rot {p n : ℕ} (hn : 0 < n) [Fintype F] (hF : Fintype.card F = p ^ n) (z : F) (A : ℕ) :
    z ^ (p * A) = z ^ rot p n A := by
  have hz : z ^ (p ^ n) = z := by
    rw [← hF]
    exact FiniteField.pow_card z
  have hP : p ^ n = p * p ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hdm := Nat.div_add_mod A (p ^ (n - 1))
  have h1 : p * A = p ^ n * (A / p ^ (n - 1)) + p * (A % p ^ (n - 1)) := by
    calc p * A = p * (p ^ (n - 1) * (A / p ^ (n - 1)) + A % p ^ (n - 1)) := by rw [hdm]
      _ = p ^ n * (A / p ^ (n - 1)) + p * (A % p ^ (n - 1)) := by rw [hP]; ring
  unfold rot
  rw [h1, pow_add, pow_mul, hz, ← pow_add]
  congr 1
  ring

variable (p : ℕ) [Fact p.Prime] [CharP F p]

@[expose] noncomputable def frobFun : ((Fin 2 → F) → F) →ₛₗ[frobenius F p] ((Fin 2 → F) → F) where
  toFun f := fun v => (f v) ^ p
  map_add' f g := by
    funext v
    exact add_pow_char (f v) (g v) p
  map_smul' c f := by
    funext v
    exact mul_pow c (f v) p

theorem frobFun_apply (f : (Fin 2 → F) → F) (v : Fin 2 → F) : frobFun p f v = (f v) ^ p := rfl

theorem frobFun_funRep (g : SLm F) (f : (Fin 2 → F) → F) :
    frobFun p (funRep F F g f) = funRep F F g (frobFun p f) := rfl

theorem frobFun_injective : Function.Injective (frobFun p (F := F)) := by
  intro f g h
  funext v
  exact frobenius_inj F p (congrFun h v)

variable {p}

theorem frobFun_monoFun {n : ℕ} (hn : 0 < n) [Fintype F] (hF : Fintype.card F = p ^ n) (A : ℕ) :
    frobFun p (monoFun F F A 0) = monoFun F F (rot p n A) 0 := by
  funext v
  simp only [frobFun_apply, monoFun, Algebra.algebraMap_self, RingHom.id_apply, pow_zero, mul_one]
  rw [← pow_mul, mul_comm, pow_mul_rot hn hF]

end Twist

theorem steinberg_twist_holds : SteinbergTwistStmt := by
  intro p n F _ _ hp _ hF hn A hA
  have := Fact.mk hp
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have : CharP F p := charP_of_card_eq_prime_pow hF'
  have : RingHomSurjective (frobenius F p) :=
    ⟨Finite.surjective_of_injective (frobenius_inj F p)⟩
  have hmap : Submodule.map (frobFun p) (steinbergSub F F A) = steinbergSub F F (rot p n A) := by
    unfold steinbergSub
    rw [Submodule.map_span, ← Set.range_comp]
    have hfun : (frobFun p ∘ fun g : SLm F => funRep F F g (monoFun F F A 0)) =
        fun g : SLm F => funRep F F g (monoFun F F (rot p n A) 0) := by
      funext g
      show frobFun p (funRep F F g (monoFun F F A 0)) = funRep F F g (monoFun F F (rot p n A) 0)
      rw [frobFun_funRep, frobFun_monoFun hn hF']
    rw [hfun]
  let Θ' : steinbergSub F F A →ₛₗ[frobenius F p] steinbergSub F F (rot p n A) :=
    LinearMap.codRestrict (steinbergSub F F (rot p n A))
      ((frobFun p).domRestrict (steinbergSub F F A))
      (fun x => by rw [← hmap]; exact Submodule.mem_map_of_mem x.2)
  refine ⟨Θ'.toAddMonoidHom, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact frobFun_injective p (congrArg Subtype.val hxy)
  · intro y
    have hy : (y : (Fin 2 → F) → F) ∈ Submodule.map (frobFun p) (steinbergSub F F A) := by
      rw [hmap]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · intro c x
    exact map_smulₛₗ Θ' c x
  · intro g x
    exact Subtype.ext rfl

end CFSG.GH74.GLS.Stage4.Rest
