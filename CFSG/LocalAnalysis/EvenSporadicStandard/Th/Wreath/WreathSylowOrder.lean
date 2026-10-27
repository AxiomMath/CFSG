module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathP1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathE2

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory Matrix

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D : Subgroup G} {z b : G}

private theorem mul_add_one_comm (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) : w * (w + 1) = (w + 1) * w := by
  calc w * (w + 1) = w * w + w * 1 := by rw [mul_add]
    _ = w + w := by rw [hww, mul_one]
    _ = 0 := VSub.add_self hD w
    _ = w + w := (VSub.add_self hD w).symm
    _ = w * w + 1 * w := by rw [hww, one_mul]
    _ = (w + 1) * w := by rw [add_mul]

private theorem commute_add_one_of_cases (hD : DHyp A Aa t D) {w f : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hf : f = 0 ∨ f = 1 ∨ f = w ∨ f = w + 1) :
    f * (w + 1) = (w + 1) * f := by
  have hw := mul_add_one_comm hD hww
  rcases hf with rfl | rfl | rfl | rfl
  · rw [zero_mul, mul_zero]
  · rw [one_mul, mul_one]
  · exact hw
  · rfl

private theorem phiQ_mul_add_one_comm (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) {Q : Subgroup G}
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1) :
    ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c * (w + 1) = (w + 1) * phiQ hD Q c :=
  fun c hc => commute_add_one_of_cases hD hww (hΦ c hc)

private theorem vConj_eq_one_of_mem_centralizer (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ centralizer (omega1 D hD.comm : Set G)) : vConj hD n = 1 := by
  have hnN : n ∈ normalizer (omega1 D hD.comm : Set G) :=
    Subgroup.centralizer_le_normalizer _ hn
  refine AbelianSub.end_ext fun v => ?_
  rw [val_vConj_apply hD hnN v]
  change n * v.val * n⁻¹ = v.val
  have hcomm : v.val * n = n * v.val := mem_centralizer_iff.1 hn v.val v.2
  rw [← hcomm]
  group

private theorem mem_wComm_of_mem_centralizer (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)} {n : G}
    (hn : n ∈ centralizer (omega1 D hD.comm : Set G)) : n ∈ wComm hD w := by
  refine ⟨Subgroup.centralizer_le_normalizer _ hn, ?_⟩
  rw [vConj_eq_one_of_mem_centralizer hD hn, one_mul, mul_one]

private theorem Q_le_centralizer_omega1 (hD : DHyp A Aa t D) {Q : Subgroup G}
    (hQ : QHyp L A D t Q) : Q ≤ centralizer (omega1 D hD.comm : Set G) := by
  intro q hq
  refine mem_centralizer_iff.2 fun v hv => ?_
  exact mem_centralizer_iff.1 (hQ.le_centralizer hq) v hv.1

private theorem exists_wreathRep_add_one (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) :
    ∃ c₁ : G → (Fin 4 → ZMod 2), IsCoord (wFix hD (w + 1)) c₁ ∧
      ∃ ρ₁ : ↥(wreathN₁ hD Q (w + 1)) →* GL (Fin 4) (ZMod 2),
        (∀ σ : ↥(wreathN₁ hD Q (w + 1)),
          IsRep (wFix hD (w + 1)) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2))) ∧
          Function.Surjective ρ₁ := by
  have hww' : (w + 1) * (w + 1) = w + 1 := add_one_mul_add_one hD hww
  have hτw' : vConj hD t * (w + 1) * vConj hD t = (w + 1) + 1 :=
    vConj_t_mul_add_one_mul H W W2 hD hτw
  have hwH' : ∀ n ∈ L ⊓ normalizer (A : Set G),
      vConj hD n * (w + 1) = (w + 1) * vConj hD n :=
    fun n hn => commute_add_one_of_commute hD (hwH n hn)
  have hgw' : g ∈ wComm hD (w + 1) := by
    rwa [wComm_add_one hD w]
  exact H.exists_wreathN₁_matHom W W2 hD h4 hb hwH' hww' hτw' hQ hgQ hgw' hgM

private theorem wreathE₂_add_one_fixedPointFree (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) {σ : G}
    (hσfree : ∀ v ∈ wFix hD w, σ * v * σ⁻¹ = v → v = 1) :
    ∀ e ∈ wreathE₂ hD Q (w + 1), σ * e * σ⁻¹ = e → e = 1 := by
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, hsurj₂⟩ :=
    exists_wreathRep_add_one H W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM
  have hww' : (w + 1) * (w + 1) = w + 1 := add_one_mul_add_one hD hww
  have hEint : wreathE₂ hD Q (w + 1) ⊓ omega1 D hD.comm = wKer hD (w + 1) :=
    wreathE₂_inf_omega1 hD hww' hQ hc₂ ρ₂ hρ₂ hsurj₂
  intro e he hfix
  have he2ker : e ^ 2 ∈ wKer hD (w + 1) :=
    sq_mem_wKer_of_mem_wreathE₂ hD hww' hQ hq4 hc₂ ρ₂ hρ₂ hsurj₂ he
  have hfix2 : σ * e ^ 2 * σ⁻¹ = e ^ 2 := by
    calc σ * e ^ 2 * σ⁻¹ = (σ * e * σ⁻¹) * (σ * e * σ⁻¹) := by
          rw [sq]
          group
      _ = e * e := by rw [hfix]
      _ = e ^ 2 := by rw [sq]
  have he2fix : e ^ 2 ∈ wFix hD w := by
    rw [← wKer_add_one hD w]
    exact he2ker
  have he2one : e ^ 2 = 1 := hσfree (e ^ 2) he2fix hfix2
  have heV : e ∈ omega1 D hD.comm :=
    (QHyp.mem_omega1_iff hD hQ (wreathE₂_le hD Q (w + 1) he)).2 he2one
  have heint : e ∈ wreathE₂ hD Q (w + 1) ⊓ omega1 D hD.comm := ⟨he, heV⟩
  rw [hEint, wKer_add_one hD w] at heint
  exact hσfree e heint hfix

private theorem wreathE₂_add_one_le_of_fixedPointFree (hD : DHyp A Aa t D)
    {Q : Subgroup G} {w : AddMonoid.End (VSub hD)} {σ : G}
    (hQ : QHyp L A D t Q) (hσP : σ ∈ wreathP₁ hD Q w)
    (hσfreeE : ∀ e ∈ wreathE₂ hD Q (w + 1), σ * e * σ⁻¹ = e → e = 1) :
    wreathE₂ hD Q (w + 1) ≤ wreathP₁ hD Q w := by
  have hσN0 : σ ∈ normalizer (Q : Set G) ⊓ wComm hD w := wreathP₁_le hD Q w hσP
  have hσN0' : σ ∈ normalizer (Q : Set G) ⊓ wComm hD (w + 1) := by
    simpa only [wComm_add_one hD w] using hσN0
  have hσE : ∀ e ∈ wreathE₂ hD Q (w + 1), σ * e * σ⁻¹ ∈ wreathE₂ hD Q (w + 1) :=
    fun e he => conj_mem_wreathE₂ hD hσN0' he
  have hfP : ∀ e ∈ wreathE₂ hD Q (w + 1), e * σ * e⁻¹ * σ⁻¹ ∈ wreathP₁ hD Q w := by
    intro e he
    have heC : e ∈ centralizer (omega1 D hD.comm : Set G) :=
      Q_le_centralizer_omega1 hD hQ (wreathE₂_le hD Q (w + 1) he)
    have heNV : e ∈ normalizer (Q : Set G) ⊓ wComm hD w :=
      ⟨Q.le_normalizer (wreathE₂_le hD Q (w + 1) he),
        mem_wComm_of_mem_centralizer hD heC⟩
    have h1 : e * σ * e⁻¹ ∈ wreathP₁ hD Q w := conj_mem_wreathP₁ hD heNV hσP
    exact (wreathP₁ hD Q w).mul_mem h1 ((wreathP₁ hD Q w).inv_mem hσP)
  let F : ↥(wreathE₂ hD Q (w + 1)) → ↥(wreathE₂ hD Q (w + 1)) :=
    fun e => ⟨e.1 * σ * e.1⁻¹ * σ⁻¹, by
      have h1 : σ * e.1⁻¹ * σ⁻¹ ∈ wreathE₂ hD Q (w + 1) :=
        hσE e.1⁻¹ ((wreathE₂ hD Q (w + 1)).inv_mem e.2)
      rw [show e.1 * σ * e.1⁻¹ * σ⁻¹ = e.1 * (σ * e.1⁻¹ * σ⁻¹) by group]
      exact (wreathE₂ hD Q (w + 1)).mul_mem e.2 h1⟩
  have hF_inj : Function.Injective F := by
    intro e e' h
    have hval : e.1 * σ * e.1⁻¹ * σ⁻¹ = e'.1 * σ * e'.1⁻¹ * σ⁻¹ :=
      congrArg Subtype.val h
    have h2 : e.1 * σ * e.1⁻¹ = e'.1 * σ * e'.1⁻¹ := by
      have := congrArg (fun x => x * σ) hval
      simpa [mul_assoc] using this
    have h3 : (e'.1⁻¹ * e.1) * σ = σ * (e'.1⁻¹ * e.1) := by
      calc (e'.1⁻¹ * e.1) * σ
          = e'.1⁻¹ * (e.1 * σ * e.1⁻¹) * e.1 := by group
        _ = e'.1⁻¹ * (e'.1 * σ * e'.1⁻¹) * e.1 := by rw [h2]
        _ = σ * (e'.1⁻¹ * e.1) := by group
    have hxf : σ * (e'.1⁻¹ * e.1) * σ⁻¹ = e'.1⁻¹ * e.1 := by
      rw [← h3]
      group
    have hxE : e'.1⁻¹ * e.1 ∈ wreathE₂ hD Q (w + 1) :=
      (wreathE₂ hD Q (w + 1)).mul_mem
        ((wreathE₂ hD Q (w + 1)).inv_mem e'.2) e.2
    have hx1 : e'.1⁻¹ * e.1 = 1 := hσfreeE _ hxE hxf
    apply Subtype.ext
    have h4 := congrArg (fun y => e'.1 * y) hx1
    simpa [mul_assoc] using h4
  have hF_surj : Function.Surjective F := Finite.surjective_of_injective hF_inj
  intro e he
  obtain ⟨e', he'⟩ := hF_surj ⟨e, he⟩
  have hval : (F e').1 = e := congrArg Subtype.val he'
  exact hval ▸ hfP e'.1 e'.2

theorem ThCyc.wreathE₂_add_one_le_wreathP₁ (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) :
    wreathE₂ hD Q (w + 1) ≤ wreathP₁ hD Q w := by
  classical
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, hsurj⟩ :=
    H.exists_wreathN₁_matHom W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM
  obtain ⟨σ, hσP, -, hσfree⟩ :=
    exists_fixedPointFree_mem_wreathP₁ hD hc₁ ρ₁ hρ₁ hsurj
  exact wreathE₂_add_one_le_of_fixedPointFree hD hQ hσP
    (wreathE₂_add_one_fixedPointFree H W W2 hD h4 hb hwH hww hτw hQ hq4
      hgQ hgw hgM hσfree)

private def restrictRho (hD : DHyp A Aa t D) (Q : Subgroup G)
    (w : AddMonoid.End (VSub hD))
    (ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2)) :
    ↥(wreathP₁ hD Q w) →* GL (Fin 4) (ZMod 2) :=
  { toFun := fun x => ρ₁ ⟨x.1, wreathP₁_le_wreathN₁ hD Q w x.2⟩
    map_one' := by
      show ρ₁ ⟨(1 : G), wreathP₁_le_wreathN₁ hD Q w
        (wreathP₁ hD Q w).one_mem⟩ = 1
      rw [show (⟨(1 : G), wreathP₁_le_wreathN₁ hD Q w
          (wreathP₁ hD Q w).one_mem⟩ : ↥(wreathN₁ hD Q w)) = 1 from Subtype.ext rfl]
      exact map_one ρ₁
    map_mul' := fun x y => by
      show ρ₁ ⟨x.1 * y.1, wreathP₁_le_wreathN₁ hD Q w
          ((wreathP₁ hD Q w).mul_mem x.2 y.2)⟩ =
        ρ₁ ⟨x.1, wreathP₁_le_wreathN₁ hD Q w x.2⟩ *
          ρ₁ ⟨y.1, wreathP₁_le_wreathN₁ hD Q w y.2⟩
      rw [show (⟨x.1 * y.1, wreathP₁_le_wreathN₁ hD Q w
          ((wreathP₁ hD Q w).mul_mem x.2 y.2)⟩ : ↥(wreathN₁ hD Q w)) =
        ⟨x.1, wreathP₁_le_wreathN₁ hD Q w x.2⟩ *
          ⟨y.1, wreathP₁_le_wreathN₁ hD Q w y.2⟩ from Subtype.ext rfl]
      exact map_mul ρ₁ _ _ }

private theorem ker_restrictRho (hD : DHyp A Aa t D) {Q : Subgroup G}
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w)
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    {ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2)}
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2))) :
    (restrictRho hD Q w ρ₁).ker = (normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G)).subgroupOf (wreathP₁ hD Q w) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hxN : x.1 ∈ wreathN₁ hD Q w := wreathP₁_le_wreathN₁ hD Q w x.2
    have hxN' := (mem_wreathN₁_iff hD).1 hxN
    have hx1 : ρ₁ ⟨x.1, hxN⟩ = 1 := hx
    refine ⟨hxN'.1, mem_centralizer_iff.2 fun v hv => ?_⟩
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hv
    have hxv₁ : x.1 * v₁ * x.1⁻¹ = v₁ := by
      have hrep := hρ₁ ⟨x.1, hxN⟩ v₁ hv₁
      rw [hx1,
        show (↑(1 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 from rfl,
        Matrix.one_mulVec] at hrep
      exact hc₁.inj _ (conj_mem_wFix_of_mem_wComm hD hxN'.2.1 hv₁) v₁ hv₁ hrep
    have hxv₂ : x.1 * v₂ * x.1⁻¹ = v₂ := hxN'.2.2 v₂ hv₂
    have hconj : x.1 * (v₁ * v₂) * x.1⁻¹ = v₁ * v₂ := by
      rw [show x.1 * (v₁ * v₂) * x.1⁻¹ =
        (x.1 * v₁ * x.1⁻¹) * (x.1 * v₂ * x.1⁻¹) by group, hxv₁, hxv₂]
    calc v₁ * v₂ * x.1 = (x.1 * (v₁ * v₂) * x.1⁻¹) * x.1 := by rw [hconj]
      _ = x.1 * (v₁ * v₂) := by group
  · intro hx
    have hxN : x.1 ∈ wreathN₁ hD Q w := wreathP₁_le_wreathN₁ hD Q w x.2
    have hrep : IsRep (wFix hD w) c₁ (⟨x.1, hxN⟩ : ↥(wreathN₁ hD Q w))
        (ρ₁ ⟨x.1, hxN⟩) := hρ₁ _
    have hone : ρ₁ ⟨x.1, hxN⟩ = 1 := by
      refine Units.ext (hc₁.rep_unique hrep ?_)
      intro v hv
      change c₁ (x.1 * v * x.1⁻¹) =
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c₁ v
      rw [Matrix.one_mulVec]
      have hcomm : v * x.1 = x.1 * v :=
        mem_centralizer_iff.1 hx.2 v (wFix_le_omega1 hD w hv)
      rw [show x.1 * v * x.1⁻¹ = v by rw [← hcomm]; group]
    exact hone

private theorem surj_restrictRho (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G))
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    {ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2)}
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁) :
    Function.Surjective (restrictRho hD Q w ρ₁) := by
  intro M
  obtain ⟨m, hm⟩ := hsurj M
  obtain ⟨p, hpP, hpconj⟩ :=
    H.exists_wreathP₁_conj_eq W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM m.2
  have hpN : p ∈ wreathN₁ hD Q w := wreathP₁_le_wreathN₁ hD Q w hpP
  have hrep : IsRep (wFix hD w) c₁ (⟨p, hpN⟩ : ↥(wreathN₁ hD Q w)) (ρ₁ m) := by
    intro v hv
    rw [hpconj v hv]
    exact hρ₁ m v hv
  have hEq : ρ₁ ⟨p, hpN⟩ = ρ₁ m :=
    Units.ext (hc₁.rep_unique (hρ₁ ⟨p, hpN⟩) hrep)
  refine ⟨⟨p, hpP⟩, ?_⟩
  show ρ₁ ⟨p, wreathP₁_le_wreathN₁ hD Q w hpP⟩ = M
  rw [show (⟨p, wreathP₁_le_wreathN₁ hD Q w hpP⟩ : ↥(wreathN₁ hD Q w)) =
    ⟨p, hpN⟩ from Subtype.ext rfl, hEq, hm]

private theorem two_pow_fifteen_dvd_card_of_ker (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G))
    {c₁ : G → (Fin 4 → ZMod 2)} (hc₁ : IsCoord (wFix hD w) c₁)
    {ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2)}
    (hρ₁ : ∀ σ : ↥(wreathN₁ hD Q w),
      IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : Function.Surjective ρ₁)
    (hdvdNV : 2 ^ 9 ∣ Nat.card ↥((normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G)).subgroupOf (wreathP₁ hD Q w))) :
    2 ^ 15 ∣ Nat.card (wreathP₁ hD Q w) := by
  have hker := ker_restrictRho hD hww hc₁ hρ₁
  have hsurjφ := surj_restrictRho H W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM
    hc₁ hρ₁ hsurj
  have hGL : 2 ^ 6 ∣ Nat.card (GL (Fin 4) (ZMod 2)) := by
    have hUT : Nat.card ↥(CFSG.Quasithin.FFC.UT 4) = 2 ^ 6 := by
      rw [CFSG.Quasithin.FFC.card_UT]
    have h := Subgroup.card_dvd_of_le (show CFSG.Quasithin.FFC.UT 4 ≤ ⊤ from le_top)
    rwa [hUT, Subgroup.card_top] at h
  have hcardK : Nat.card ↥(wreathP₁ hD Q w) =
      Nat.card ↥((normalizer (Q : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G)).subgroupOf (wreathP₁ hD Q w)) *
        Nat.card (GL (Fin 4) (ZMod 2)) := by
    have h := Subgroup.card_ker_mul_card_range (restrictRho hD Q w ρ₁)
    rw [hker, MonoidHom.range_eq_top_of_surjective _ hsurjφ, Subgroup.card_top] at h
    exact h.symm
  have h15 : 2 ^ 15 ∣
      Nat.card ↥((normalizer (Q : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G)).subgroupOf (wreathP₁ hD Q w)) *
        Nat.card (GL (Fin 4) (ZMod 2)) := by
    have h := mul_dvd_mul hdvdNV hGL
    rwa [← pow_add] at h
  rw [hcardK]
  exact h15

private theorem two_pow_nine_dvd_card_inf (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) (hw0 : w ≠ 0)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
       phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G))
    (hp : ∃ p ∈ wreathP₁ hD Q w,
      p ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ∧
        (∃ k : ℕ, orderOf p = 2 ^ k) ∧ phiQ hD Q p = w) :
    2 ^ 9 ∣ Nat.card ↥((normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G)).subgroupOf (wreathP₁ hD Q w)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, hpP, hpNV, ⟨k, hpk⟩, hpphi⟩ := hp
  have hQ_le_CV : Q ≤ centralizer (omega1 D hD.comm : Set G) :=
    Q_le_centralizer_omega1 hD hQ
  have hE_NV : wreathE₂ hD Q (w + 1) ≤
      normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
    intro e he
    exact ⟨Q.le_normalizer (wreathE₂_le hD Q (w + 1) he),
      hQ_le_CV (wreathE₂_le hD Q (w + 1) he)⟩
  have hp_notQ : p ∉ Q := by
    intro hpQ
    have hpC : p ∈ centralizer (Q : Set G) :=
      mem_centralizer_iff.2 fun q hq => hQ.comm q hq p hpQ
    have hzero : phiQ hD Q p = 0 :=
      (QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq hpNV).2 hpC
    exact hw0 (hpphi ▸ hzero)
  have hp_notE : p ∉ wreathE₂ hD Q (w + 1) :=
    fun h => hp_notQ (wreathE₂_le hD Q (w + 1) h)
  let Y : Subgroup G := wreathE₂ hD Q (w + 1) ⊔ Subgroup.zpowers p
  have hEpg : IsPGroup 2 ↥(wreathE₂ hD Q (w + 1)) :=
    hQ.pgroup.to_le (wreathE₂_le hD Q (w + 1))
  have hZpg : IsPGroup 2 ↥(Subgroup.zpowers p) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hpk])
  have hp_norm : p ∈ Subgroup.normalizer ↑(wreathE₂ hD Q (w + 1)) := by
    refine mem_normalizer_iff.2 fun e => ⟨?_, ?_⟩
    · intro he
      exact conj_mem_wreathE₂ hD ⟨hpNV.1, mem_wComm_of_mem_centralizer hD hpNV.2⟩ he
    · intro he
      have h := conj_mem_wreathE₂ hD
        ⟨(normalizer (Q : Set G)).inv_mem hpNV.1,
          mem_wComm_of_mem_centralizer hD ((centralizer _).inv_mem hpNV.2)⟩ he
      rwa [show p⁻¹ * (p * e * p⁻¹) * (p⁻¹)⁻¹ = e by group] at h
  have hYpg : IsPGroup 2 ↥Y :=
    IsPGroup.to_sup_of_normal_left' hEpg hZpg (Subgroup.zpowers_le.2 hp_norm)
  have hE_sub : wreathE₂ hD Q (w + 1) ≤ Y := le_sup_left
  have hE_lt : wreathE₂ hD Q (w + 1) < Y := by
    refine lt_of_le_of_ne hE_sub ?_
    intro hEq
    have hpY : p ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers p)
    rw [← hEq] at hpY
    exact hp_notE hpY
  obtain ⟨n, hn⟩ := hYpg.exists_card_eq
  have hcardE : Nat.card ↥(wreathE₂ hD Q (w + 1)) = 2 ^ 8 := by
    obtain ⟨c₂, hc₂, ρ₂, hρ₂, hsurj₂⟩ :=
      exists_wreathRep_add_one H W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM
    exact card_wreathE₂ H W W2 hD (add_one_mul_add_one hD hww)
      (vConj_t_mul_add_one_mul H W W2 hD hτw) hQ hq4 hsq hc₂ ρ₂ hρ₂ hsurj₂
      (phiQ_mul_add_one_comm hD hww hΦ)
  have hn8 : 8 < n := by
    have hlt : 2 ^ 8 < 2 ^ n := by
      simpa only [hcardE, hn] using (Subgroup.card_lt_of_lt hE_lt)
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
  have h9n : 9 ≤ n := by omega
  have hdvdY : 2 ^ 9 ∣ Nat.card ↥Y := by
    rw [hn]
    exact pow_dvd_pow 2 h9n
  have hYK : Y ≤ wreathP₁ hD Q w :=
    sup_le (ThCyc.wreathE₂_add_one_le_wreathP₁ H W W2 hD h4 hb hwH hww hτw hQ hq4
      hgQ hgw hgM) (Subgroup.zpowers_le.2 hpP)
  have hYNV : Y ≤ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    sup_le hE_NV (Subgroup.zpowers_le.2 hpNV)
  have h1 : Nat.card ↥(Y.subgroupOf (wreathP₁ hD Q w)) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv
  have h2 : Nat.card ↥(Y.subgroupOf (wreathP₁ hD Q w)) ∣
      Nat.card ↥((normalizer (Q : Set G) ⊓
        centralizer (omega1 D hD.comm : Set G)).subgroupOf (wreathP₁ hD Q w)) :=
    Subgroup.card_dvd_of_le (Subgroup.subgroupOf_mono _ hYNV)
  rw [← h1] at hdvdY
  exact dvd_trans hdvdY h2

theorem ThCyc.two_pow_fifteen_dvd_card_wreathP₁ (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) (hw0 : w ≠ 0)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
       phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G))
    (hp : ∃ p ∈ wreathP₁ hD Q w,
      p ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ∧
        (∃ k : ℕ, orderOf p = 2 ^ k) ∧ phiQ hD Q p = w) :
    2 ^ 15 ∣ Nat.card (wreathP₁ hD Q w) := by
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, hsurj⟩ :=
    H.exists_wreathN₁_matHom W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM
  exact two_pow_fifteen_dvd_card_of_ker H W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM
    hc₁ hρ₁ hsurj
    (two_pow_nine_dvd_card_inf H W W2 hD h4 hb hwH hww hτw hw0 hQ hq4 hsq hΦ
      hgQ hgw hgM hp)

theorem ThCyc.exists_le_wreathP₁_card_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) (hw0 : w ≠ 0)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
       phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G))
    (hp : ∃ p ∈ wreathP₁ hD Q w,
      p ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ∧
        (∃ k : ℕ, orderOf p = 2 ^ k) ∧ phiQ hD Q p = w) :
    ∃ X₀ : Subgroup G, X₀ ≤ wreathP₁ hD Q w ∧ IsPGroup 2 X₀ ∧ Nat.card X₀ = 2 ^ 15 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ 15 ∣ Nat.card (wreathP₁ hD Q w) :=
    ThCyc.two_pow_fifteen_dvd_card_wreathP₁ H W W2 hD h4 hb hwH hww hτw hw0 hQ hq4 hsq hΦ
      hgQ hgw hgM hp
  obtain ⟨X', hX'card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := ↥(wreathP₁ hD Q w)) 2 (n := 15) hdvd
  refine ⟨X'.map (wreathP₁ hD Q w).subtype, Subgroup.map_subtype_le X', ?_, ?_⟩
  · exact IsPGroup.of_card (by
      rw [Subgroup.card_map_of_injective (wreathP₁ hD Q w).subtype_injective, hX'card])
  · rw [Subgroup.card_map_of_injective (wreathP₁ hD Q w).subtype_injective, hX'card]

end CFSG.EvenSporadicStandard.ThStd
