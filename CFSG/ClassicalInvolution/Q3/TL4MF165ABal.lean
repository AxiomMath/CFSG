module

public import CFSG.ClassicalInvolution.Asc77.WP3L52Comp
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalancePow
public import CFSG.ClassicalInvolution.Q3.Q3NMAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF165A

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Balance.StrongBalance
open scoped commutatorElement

section Lift

variable {K L : Type} [Group K] [Group L] {ψ₀ : K →* L} (hker : ψ₀.ker ≤ Subgroup.center K)
  (hZ3 : ∀ z ∈ Subgroup.center K, z ^ 3 = 1)
include hker hZ3

theorem exists_involution_lift (hsurj : Function.Surjective ψ₀) {s : L} (hs : s * s = 1) :
    ∃ x : K, x * x = 1 ∧ ψ₀ x = s := by
  obtain ⟨y, rfl⟩ := hsurj s
  have hz : y * y ∈ Subgroup.center K := hker (by rw [MonoidHom.mem_ker, map_mul, hs])
  refine ⟨y * (y * y), ?_, ?_⟩
  · calc y * (y * y) * (y * (y * y)) = (y * y) ^ 3 := by rw [pow_three]; simp only [mul_assoc]
      _ = 1 := hZ3 _ hz
  · rw [map_mul, map_mul, hs, mul_one]

theorem commute_of_lifts {x y : K} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : ψ₀ x * ψ₀ y = ψ₀ y * ψ₀ x) : x * y = y * x := by
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hcK : c ∈ Subgroup.center K := hker (by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
    group)
  have hcc : ∀ w, c * w = w * c := fun w => (Subgroup.mem_center_iff.mp hcK w).symm
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have e : x * y * x = c * y := by rw [hcdef, hxi]; group
  have hc2 : c * c = 1 := by
    calc c * c = c * c * (y * y) := by rw [hy, mul_one]
      _ = c * (c * y) * y := by simp only [mul_assoc]
      _ = c * (y * c) * y := by rw [hcc y]
      _ = (c * y) * (c * y) := by simp only [mul_assoc]
      _ = (x * y * x) * (x * y * x) := by rw [e]
      _ = x * (y * (x * x) * y) * x := by simp only [mul_assoc]
      _ = 1 := by rw [hx, mul_one, hy, mul_one, hx]
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hZ3 c hcK, hc2, inv_one, mul_one]
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [← hcdef, hc1, one_mul]

end Lift

theorem alphaOf_eq_bot_of_strongConclusion {L K : Type} [Group L] [Group K]
    (hZ : Subgroup.center L = ⊥) {ψ₀ : K →* L} (hsurj : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center K) (hZ3 : ∀ z ∈ Subgroup.center K, z ^ 3 = 1)
    {𝒳 : Subgroup (MulAut L)} (hinn : innSubgroup L ≤ 𝒳) {A : Subgroup ↥𝒳}
    (hAinn : ∀ a ∈ A, ((a : ↥𝒳) : MulAut L) ∈ innSubgroup L) (hA2 : ∀ a ∈ A, a * a = 1)
    (hSB : ∀ ψ : K →* ↥𝒳, ψ.ker ≤ Subgroup.center K → ψ.range.Normal →
      (∀ f ∈ A, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) → ToralActionPow 2 ψ A →
        StrongConclusion ψ.range A) :
    alphaOf A = ⊥ := by
  have hinj := conj_injective_of_center_eq_bot hZ
  let ψ : K →* ↥𝒳 := (MulAut.conj.comp ψ₀).codRestrict 𝒳 fun y => hinn ⟨ψ₀ y, rfl⟩
  have hψ : ∀ y, ((ψ y : ↥𝒳) : MulAut L) = MulAut.conj (ψ₀ y) := fun y => rfl
  have hcent : ∀ φ : ↥𝒳, (∀ x ∈ ψ.range, φ * x = x * φ) → φ = 1 := by
    intro φ hφ
    refine Subtype.ext (MulEquiv.ext fun l => ?_)
    obtain ⟨y, rfl⟩ := hsurj l
    have h1 : (φ : MulAut L) * MulAut.conj (ψ₀ y) = MulAut.conj (ψ₀ y) * (φ : MulAut L) :=
      congrArg Subtype.val (hφ (ψ y) ⟨y, rfl⟩)
    have h2 : MulAut.conj ((φ : MulAut L) (ψ₀ y)) = MulAut.conj (ψ₀ y) := by
      rw [← mul_conj_mul_inv, h1]
      group
    exact hinj h2
  have hkerψ : ψ.ker ≤ Subgroup.center K := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    apply hinj
    rw [map_one, ← hψ y, hy]
    rfl
  have hnorm : ψ.range.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨y', hy'⟩ := hsurj ((g : MulAut L) (ψ₀ y))
    refine ⟨y', Subtype.ext ?_⟩
    rw [hψ, hy']
    show MulAut.conj ((g : MulAut L) (ψ₀ y)) =
      (g : MulAut L) * MulAut.conj (ψ₀ y) * (g : MulAut L)⁻¹
    rw [mul_conj_mul_inv]
  have hfaith : ∀ f ∈ A, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f :=
    fun f _ hf1 hall => hf1 (hcent f hall)
  have hdata : ∀ f : ↥A, ∃ x : K, x * x = 1 ∧
      MulAut.conj (ψ₀ x) = (((f : ↥𝒳) : MulAut L)) := by
    intro f
    obtain ⟨s, hs⟩ := hAinn f f.2
    have hs2 : s * s = 1 := by
      apply hinj
      rw [map_mul, hs, map_one]
      exact congrArg Subtype.val (hA2 f f.2)
    obtain ⟨x, hx, hxs⟩ := exists_involution_lift hker hZ3 hsurj hs2
    exact ⟨x, hx, by rw [hxs, hs]⟩
  choose lift hlift2 hlift using hdata
  have hAcomm : ∀ f g : ↥A, (f : ↥𝒳) * g = g * f := by
    intro f g
    have hfi : (f : ↥𝒳)⁻¹ = f := inv_eq_of_mul_eq_one_right (hA2 _ f.2)
    have hgi : (g : ↥𝒳)⁻¹ = g := inv_eq_of_mul_eq_one_right (hA2 _ g.2)
    have hfgi : ((f : ↥𝒳) * g)⁻¹ = f * g :=
      inv_eq_of_mul_eq_one_right (hA2 _ (A.mul_mem f.2 g.2))
    rw [← hfgi, mul_inv_rev, hfi, hgi]
  have hlcomm : ∀ f g : ↥A, lift f * lift g = lift g * lift f := by
    intro f g
    refine commute_of_lifts hker hZ3 (hlift2 f) (hlift2 g) (hinj ?_)
    rw [map_mul, map_mul, hlift, hlift]
    exact congrArg Subtype.val (hAcomm f g)
  have hPc : ∀ x ∈ Subgroup.closure (Set.range lift), ∀ y ∈ Subgroup.closure (Set.range lift),
      x * y = y * x := by
    have hpw : (Set.range lift).Pairwise Commute := by
      rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩ -
      exact hlcomm f g
    intro x hx y hy
    exact congrArg Subtype.val ((Subgroup.isMulCommutative_closure hpw).is_comm.comm
      (⟨x, hx⟩ : ↥(Subgroup.closure (Set.range lift))) ⟨y, hy⟩)
  have htor : ToralActionPow 2 ψ A := by
    refine ⟨Subgroup.closure (Set.range lift), hPc, fun f hf => ?_⟩
    refine ⟨lift ⟨f, hf⟩, Subgroup.subset_closure ⟨⟨f, hf⟩, rfl⟩, by rw [sq]; exact hlift2 _,
      fun y => Subtype.ext ?_⟩
    have hl : MulAut.conj (ψ₀ (lift ⟨f, hf⟩)) = (f : MulAut L) := hlift ⟨f, hf⟩
    show (f : MulAut L) * MulAut.conj (ψ₀ y) * (f : MulAut L)⁻¹ =
      MulAut.conj (ψ₀ (lift ⟨f, hf⟩ * y * (lift ⟨f, hf⟩)⁻¹))
    rw [← hl]
    simp only [map_mul, map_inv]
  have hSC := hSB ψ hkerψ hnorm hfaith htor
  rw [alphaOf_eq_bot_iff]
  refine ⟨fun a ha ha1 => ?_, ?_⟩
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd g hg
    have hc := hSC.2 a ha ha1 d hd g hg
    have hu : (g * d)⁻¹ * (d * g) = 1 := by
      apply hcent
      intro y hy
      have h1 := hc y hy
      calc (g * d)⁻¹ * (d * g) * y = (g * d)⁻¹ * ((d * g) * y * (d * g)⁻¹) * (d * g) := by
            group
        _ = (g * d)⁻¹ * ((g * d) * y * (g * d)⁻¹) * (d * g) := by rw [h1]
        _ = y * ((g * d)⁻¹ * (d * g)) := by group
    have hdg : d * g = g * d := by
      have := congrArg (fun w => (g * d) * w) hu
      simpa [mul_assoc] using this
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc d * g * d⁻¹ * g⁻¹ = (g * d) * d⁻¹ * g⁻¹ := by rw [hdg]
      _ = 1 := by group
  · rw [eq_bot_iff]
    intro d hd
    have hd' : d ∈ CFSG.ClassicalInvolution.Balance.deltaCore A := hd
    rw [Subgroup.mem_bot]
    exact hcent d fun y hy => hSC.1 d hd' y hy

end CFSG.ClassicalInvolution.Q3.TL4.MF165A
