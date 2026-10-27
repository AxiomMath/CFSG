module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.IrredThree
public import CFSG.CGT.PushingUpLit.CGT6X.End4L34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourCentre

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.HardMathSupport.Lang.Coordinator
  CFSG.Assembly.LowTwoRank

theorem mulEquiv_of_lift {k : Type} [Field k] [Finite k] {K : Type} [Group K] [Finite K]
    (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 k) (hz : Subgroup.center K ≠ ⊥)
    (α : Matrix.SpecialLinearGroup (Fin 3) k →* K)
    (hα : ∀ s, e (QuotientGroup.mk (α s)) = proj 3 k s) (hαsurj : Function.Surjective α) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 3) k ≃* K,
      ∀ s, e (QuotientGroup.mk (φ s)) = proj 3 k s := by
  have hηker : ∀ z : K, e (QuotientGroup.mk z) = 1 ↔ z ∈ Subgroup.center K := fun z => by
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hβker : (proj 3 k).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k) := by
    rw [ker_proj, scalars_eq_center]
  obtain ⟨⟨z, hzc⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hz
  have hz1 : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨s, hs⟩ := hαsurj z
  have hsker : s ∈ (proj 3 k).ker := by
    rw [MonoidHom.mem_ker, ← hα, hs]
    exact (hηker z).2 hzc
  have hαker : α.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k) := by
    intro t ht
    rw [← hβker, MonoidHom.mem_ker, ← hα, MonoidHom.mem_ker.1 ht, QuotientGroup.mk_one,
      map_one]
  have hcard : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k)) ∣ 3 :=
    (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by norm_num) k).trans
      (Nat.gcd_dvd_left _ _)
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.ker_eq_bot_of_card_dvd_prime
      Nat.prime_three α hαker hcard ⟨s, hβker ▸ hsker, by rw [hs]; exact hz1⟩
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hαsurj⟩, fun s => hα s⟩

theorem exists_mulEquiv_over_sl3
    {k : Type} [Field k] [Finite k] {p f : ℕ} (hk : Nat.card k = p ^ f)
    (h3 : 3 ∣ Nat.card k - 1) {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 p f)
    (hodd : Odd (Nat.card (Subgroup.center K))) (hz : Subgroup.center K ≠ ⊥)
    (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 k) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 3) k ≃* K,
      ∀ s, e (QuotientGroup.mk (φ s)) = proj 3 k s := by
  by_cases h4 : Nat.card k = 4
  ·
    have hp : p.Prime := hmod.1.1
    have hp2 : p = 2 ∧ f = 2 := by
      have h1 : p ^ f = 2 ^ 2 := by rw [← hk, h4]; norm_num
      have hf : f ≠ 0 := by have := hmod.1.2.1; omega
      have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h1 ▸ dvd_pow_self p hf))
      subst h2
      exact ⟨rfl, Nat.pow_right_injective (le_refl 2) h1⟩
    obtain ⟨rfl, rfl⟩ := hp2
    have : Group.IsPerfect K := ⟨hK⟩
    obtain ⟨ρ, hρ⟩ := CFSG.CGT.PushingUpLit.CGT6X.End4.exists_cover_l34 hmod h4 e hodd
    have hsurj : Function.Surjective ρ := by
      have hdec : ∀ g : K, ∃ z ∈ Subgroup.center K, ∃ l ∈ ρ.range, g = z * l := by
        intro g
        obtain ⟨s, hs⟩ := proj_surjective 3 k (e (QuotientGroup.mk g))
        have h1 : (QuotientGroup.mk g : K ⧸ Subgroup.center K) = QuotientGroup.mk (ρ s) :=
          e.injective (by rw [hρ s, hs])
        refine ⟨g * (ρ s)⁻¹, ?_, ρ s, ⟨s, rfl⟩, by group⟩
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
          mul_inv_cancel]
      exact MonoidHom.range_eq_top.1
        (CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour.eq_top_of_perfect_of_dec hK hdec)
    exact mulEquiv_of_lift e hz ρ hρ hsurj
  ·
    let β : Matrix.SpecialLinearGroup (Fin 3) k →* projectiveSL 3 k := proj 3 k
    let η : K →* projectiveSL 3 k :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
    have hβ : Function.Surjective β := proj_surjective 3 k
    have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hcen : η.ker ≤ Subgroup.center K := fun z hz => by
      have : e (QuotientGroup.mk z) = 1 := hz
      rwa [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff] at this
    obtain ⟨α, hα, hαsurj⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.exists_surjective_lift
      hK hβ hcen
      (CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.exists_section_pullback h3 h4 hη hcen)
    exact mulEquiv_of_lift e hz α hα hαsurj

theorem exists_lin_irred_alternative
    {k : Type} [Field k] [Finite k] {p f : ℕ} (hk : Nat.card k = p ^ f)
    (h3 : 3 ∣ Nat.card k - 1) {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (hperf : commutator ↥L = ⊤) (hZ : IsPGroup 3 (Subgroup.center ↥L))
    (hZ1 : Subgroup.center ↥L ≠ ⊥)
    (hmod : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p f)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 k) {u : X}
    (huN : u ∈ Subgroup.normalizer (L : Set X)) (B : GL (Fin 3) k)
    (hβ : ∀ z, e (centerQuotientConj L huN z) = conjAut 3 k B (e z))
    (ω : k) (H : Matrix.SpecialLinearGroup (Fin 3) k) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hH3 : H ^ 3 = 1)
    (hBH : ((B : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (H : Matrix (Fin 3) (Fin 3) k) =
      ω⁻¹ • ((H : Matrix (Fin 3) (Fin 3) k) * ((B : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))) :
    ∃ y ∈ L, y ^ 3 = 1 ∧ ∃ c ∈ L, u * y * u⁻¹ = c * y ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧ c * u = u * c ∧
      ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) ↔ x ∈ Subgroup.zpowers c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hZ
    rw [hm]
    exact Odd.pow (by decide)
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_over_sl3 hk h3 hperf hmod hodd hZ1 e
  let ζ : (Matrix.SpecialLinearGroup (Fin 3) k) ≃* (Matrix.SpecialLinearGroup (Fin 3) k) := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k B
  have hζ : ∀ s : (Matrix.SpecialLinearGroup (Fin 3) k), ((ζ s : (Matrix.SpecialLinearGroup (Fin 3) k)) : Matrix (Fin 3) (Fin 3) k) =
      (B : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
        ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) :=
    fun s => coe_slConjugation B s
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨u, huN⟩
  have hα : ∀ l : ↥L, ((α l : ↥L) : X) = u * l * u⁻¹ := fun l => rfl
  let ζL : ↥L ≃* ↥L := φ.symm.trans (ζ.trans φ)
  have hζL : ∀ s : (Matrix.SpecialLinearGroup (Fin 3) k), ζL (φ s) = φ (ζ s) := fun s => by simp [ζL]
  have hcen : ∀ l : ↥L, l ∈ Subgroup.center ↥L ↔ e (QuotientGroup.mk l) = 1 := fun l => by
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hagree : ∀ s : (Matrix.SpecialLinearGroup (Fin 3) k), e (QuotientGroup.mk (α (φ s))) = e (QuotientGroup.mk (φ (ζ s))) := by
    intro s
    have h1 := hβ (QuotientGroup.mk (φ s))
    rw [centerQuotientConj_mk, hφ s, conjAut_proj] at h1
    rw [hφ (ζ s)]
    exact h1
  have hperfL : ∀ l : ↥L, α l = ζL l := by
    have := perfect_aut_eq_of_central hperf α ζL ?_
    · intro l; exact DFunLike.congr_fun this l
    · intro l
      obtain ⟨s, rfl⟩ := φ.surjective l
      rw [hcen, hζL, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hagree,
        mul_inv_cancel]
  have hconj : ∀ s : (Matrix.SpecialLinearGroup (Fin 3) k), u * (φ s : X) * u⁻¹ = (φ (ζ s) : X) := fun s => by
    have := congrArg Subtype.val (hperfL (φ s))
    rwa [hα, hζL] at this
  have hω0 : ω ≠ 0 := fun h0 => by simp [h0] at hω3
  let cu : kˣ := Units.mk0 ω⁻¹ (inv_ne_zero hω0)
  have hcu : (cu : k) = ω⁻¹ := rfl
  have hcu3 : cu ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hcu, inv_pow, hω3, inv_one, Units.val_one]
  let c0 : (Matrix.SpecialLinearGroup (Fin 3) k) := scalarElement cu hcu3
  have hc0mem : c0 ∈ scalars 3 k := scalarElement_mem_scalars cu hcu3
  have hc0pow : c0 ^ 3 = 1 := by
    have hm : ((c0 : Matrix (Fin 3) (Fin 3) k)) ^ 3 = 1 := by
      change (Matrix.scalar (Fin 3) (cu : k)) ^ 3 = 1
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hcu3, Units.val_one, map_one]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hm]
  have hc0ne : c0 ≠ 1 := by
    intro h1
    have h2 := congrArg (fun g : (Matrix.SpecialLinearGroup (Fin 3) k) => (g : Matrix (Fin 3) (Fin 3) k) 0 0) h1
    simp [c0, scalarElement, Matrix.scalar_apply] at h2
    have h3 : (cu : k) = 1 := by rw [h2]; rfl
    exact hω1 (inv_eq_one.1 (hcu ▸ h3))
  have hzp : Subgroup.zpowers c0 = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k) := by
    rw [← scalars_eq_center]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hc0mem
    · rw [Nat.card_zpowers, orderOf_eq_prime hc0pow hc0ne, scalars_eq_center]
      exact Nat.le_of_dvd (by norm_num) ((CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd
        (by norm_num) k).trans (Nat.gcd_dvd_left _ _))
  have hcenter : ∀ l : ↥L, l ∈ Subgroup.center ↥L ↔ l ∈ Subgroup.zpowers (φ c0) := fun l => by
    obtain ⟨s, rfl⟩ := φ.surjective l
    rw [hcen, hφ, ← MonoidHom.mem_ker, ker_proj, scalars_eq_center, ← hzp,
      Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by simp⟩
    · rintro ⟨k, hk⟩; exact ⟨k, φ.injective (by simpa using hk)⟩
  have hBinv : (B : Matrix (Fin 3) (Fin 3) k) * ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hζc0 : ζ c0 = c0 := by
    apply Subtype.ext
    rw [hζ]
    change (B : Matrix (Fin 3) (Fin 3) k) * Matrix.scalar (Fin 3) (cu : k) *
      ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) (cu : k)
    rw [← (Matrix.scalar_commute (cu : k) (fun r => Commute.all _ r) _).eq, mul_assoc, hBinv,
      mul_one]
  have hζH : ζ H = c0 * H := by
    apply Subtype.ext
    rw [hζ]
    change _ = Matrix.scalar (Fin 3) (cu : k) * (H : Matrix (Fin 3) (Fin 3) k)
    rw [hBH, smul_mul_assoc, mul_assoc, hBinv, mul_one, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, hcu]
  have hconjc : u * (φ c0 : X) * u⁻¹ = (φ c0 : X) := by
    have := hconj c0
    rwa [hζc0] at this
  refine ⟨φ H, (φ H).2, ?_, φ c0, (φ c0).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hH3, map_one]; rfl
  · rw [hconj, hζH, map_mul]; rfl
  · intro h1
    have h2 : φ c0 = 1 := Subtype.ext h1
    exact hc0ne (by simpa using h2)
  · rw [← Subgroup.coe_pow, ← map_pow, hc0pow, map_one]; rfl
  · calc (φ c0 : X) * u = (u * (φ c0 : X) * u⁻¹) * u := by rw [hconjc]
      _ = u * (φ c0 : X) := by group
  · intro x hx
    have h1 : (∀ l ∈ L, x * l = l * x) ↔ (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      constructor
      · intro hl l; exact Subtype.ext (hl l l.2).symm
      · intro hl l hlL; exact (congrArg Subtype.val (hl ⟨l, hlL⟩)).symm
    rw [h1, hcenter, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k, Subtype.ext (by simpa using hk)⟩

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
