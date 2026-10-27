module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqAbs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Chevalley TwE6InnerAbs
open scoped commutatorElement

namespace TwE6InnerAbs

theorem ker_subgroupMap_le_center {K Q : Type*} [Group K] [Group Q] (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) (J : Subgroup K) :
    (π.subgroupMap J).ker ≤ Subgroup.center ↥J := fun b hb => by
  rw [Subgroup.mem_center_iff]
  intro g
  have hbk : (b : K) ∈ π.ker := by
    have := congrArg Subtype.val hb
    exact this
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hbk) (g : K))

theorem isLieQuot_of_central_epi {H H' : Type*} [Group H] [Group H'] (hH : commutator H = ⊤)
    (ψ : H →* H') (hψ : Function.Surjective ψ) (hk : ψ.ker ≤ Subgroup.center H)
    {P : TauCeti.LieTypeIndex → Prop} (h : IsLieQuot H' P) : IsLieQuot H P := by
  obtain ⟨d, hd, ⟨φ⟩⟩ := h
  obtain ⟨e⟩ := LieComp.nonempty_centralQuotient_mulEquiv hH ψ hψ hk
  exact ⟨d, hd, ⟨e.trans φ⟩⟩

section Main



theorem bal209TwoInnerCompType_of_model (hM : TwE6InnerCompModel) : Bal209TwoInnerCompType := by
  classical
  intro X _ _ K a hKq hLie ha3 haC hin J hJ
  obtain ⟨k, hk, hc⟩ := hin
  have hconj : ∀ y ∈ K, a * y * a⁻¹ = k * y * k⁻¹ := by
    intro y hy
    have h := Subgroup.mem_centralizer_iff.1 hc y hy
    have e1 : (k⁻¹ * a) * y * (k⁻¹ * a)⁻¹ = y := by rw [← h]; group
    calc a * y * a⁻¹ = k * ((k⁻¹ * a) * y * (k⁻¹ * a)⁻¹) * k⁻¹ := by group
      _ = k * y * k⁻¹ := by rw [e1]
  have haN : a ∈ Subgroup.normalizer (K : Set X) := by
    set c := k⁻¹ * a with hcdef
    have hcN : c ∈ Subgroup.normalizer (K : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h := Subgroup.mem_centralizer_iff.1 hc x hx
        have e : c * x * c⁻¹ = x := by rw [← h]; group
        rw [e]
        exact hx
      · intro hx
        have h : (c * x * c⁻¹) * c = c * (c * x * c⁻¹) := Subgroup.mem_centralizer_iff.1 hc _ hx
        have e : x = c * x * c⁻¹ := by
          calc x = c⁻¹ * ((c * x * c⁻¹) * c) := by group
            _ = c⁻¹ * (c * (c * x * c⁻¹)) := by rw [h]
            _ = c * x * c⁻¹ := by group
        rw [e]
        exact hx
    have hkN : k ∈ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer hk
    have e : a = k * c := by rw [hcdef]; group
    rw [e]
    exact Subgroup.mul_mem _ hkN hcN
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨a, haN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hαdef, ← map_pow, h1, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    apply haC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨y, hy⟩)
    have h2 : a * y * a⁻¹ = y := by simpa [hαdef] using h1
    calc y * a = (a * y * a⁻¹) * a := by rw [h2]
      _ = a * y := by group
  set k' : ↥K := ⟨k, hk⟩ with hk'
  have hαk : α = MulAut.conj k' := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have h1 : ((α y : ↥K) : X) = a * y * a⁻¹ := by simp [hαdef]
    rw [h1, hconj y y.2]
    simp [MulAut.conj_apply, hk']
  set Z := Subgroup.center ↥K with hZ
  set π : ↥K →* ↥K ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker ≤ Subgroup.center ↥K := by rw [hπ, QuotientGroup.ker_mk']
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  set β : MulAut (↥K ⧸ Z) := QuotientGroup.congr Z Z α (Subgroup.map_center_eq α) with hβdef
  have hαβ : ∀ y, π (α y) = β (π y) := fun y => (QuotientGroup.congr_mk Z Z α _ y).symm
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := hπs q
    have h1 : ∀ n : ℕ, ∀ y : ↥K, (β ^ n) (π y) = π ((α ^ n) y) := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ← hαβ, ih]
    rw [h1 3 y, hα3]
    rfl
  have hβ1 : β ≠ 1 := fun h =>
    hα1 (TwE6UniqAbs.alpha_eq_one_of_beta_eq_one π hker α β hαβ hKq.1 h)
  have hβk : β = MulAut.conj (π k') := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := hπs q
    rw [← hαβ, hαk]
    simp [MulAut.conj_apply]
  have hk3 : π (k' ^ 3) = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    have h1 : (MulAut.conj k') ^ 3 = 1 := by rw [← hαk]; exact hα3
    have h2 := DFunLike.congr_fun h1 y
    rw [← map_pow, MulAut.conj_apply] at h2
    have h3 : k' ^ 3 * y * (k' ^ 3)⁻¹ = y := by simpa using h2
    calc y * k' ^ 3 = (k' ^ 3 * y * (k' ^ 3)⁻¹) * k' ^ 3 := by rw [h3]
      _ = k' ^ 3 * y := by group
  have hJ₁ := glaPComponent_fixSubgroup Nat.prime_three haN hJ
  rw [← hαdef] at hJ₁
  have hJ₂ := glaPComponent_map_fixSubgroup π hker α β hαβ hπs Nat.prime_three hJ₁
  obtain ⟨d, hd, ⟨e0⟩⟩ := hLie
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 ∧ q.exponent = 1 := hd
    obtain ⟨K', hKf, σ, hcard, hσ, ⟨eC⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hcard4 : Nat.card K' = 4 := by
      rw [hcard, hq2.1, hq2.2]; norm_num
    haveI : Finite K' := Nat.finite_of_card_ne_zero (by rw [hcard4]; norm_num)
    have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by
      have := hσ c
      rwa [hq2.1, hq2.2, pow_one] at this
    set e : (↥K ⧸ Z) ≃* ↥(twistedE6RootGroup K' σ) := e0.trans eC with he
    set s : ↥(twistedE6RootGroup K' σ) := e (π k') with hs
    have hcongr : MulAut.congr e β = MulAut.conj s := by
      refine MulEquiv.ext fun x => ?_
      rw [hβk]
      show e (MulAut.conj (π k') (e.symm x)) = MulAut.conj s x
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    have hs3 : s ^ 3 = 1 := by
      rw [hs, ← map_pow, ← map_pow, hk3, map_one]
    have hs1 : s ≠ 1 := by
      intro h
      apply hβ1
      apply (MulAut.congr e).injective
      rw [hcongr, h, map_one, map_one]
    have hmap : GLAPComponent 3 (fixSubgroup (MulAut.conj s))
        (((J.subgroupOf K).map π).map e.toMonoidHom) := by
      have h1 := glaPComponent_map Nat.prime_three e.toMonoidHom (coprime_ker_mulEquiv e _) hJ₂
      rwa [← fixSubgroup_congr e β, hcongr] at h1
    have hfin := hM K' hcard4 σ hσ2 s hs3 hs1 _ hmap
    have h1 : IsLieQuot ↥((J.subgroupOf K).map π) TwE6TwoInnerCompIndex :=
      Bal209F4Aux.isLieQuot_mulEquiv
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).symm hfin
    have hperf : Group.IsPerfect ↥(J.subgroupOf K) :=
      Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ₁)
    have h2 : IsLieQuot ↥(J.subgroupOf K) TwE6TwoInnerCompIndex :=
      isLieQuot_of_central_epi hperf.commutator_eq_top (π.subgroupMap (J.subgroupOf K))
        (MonoidHom.subgroupMap_surjective π _) (ker_subgroupMap_le_center π hker _) h1
    have hJK : J ≤ K := hJ.1.trans inf_le_left
    exact Bal209F4Aux.isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) h2
  | _ => exact absurd hd (by simp [Bal209TwoIndex])

end Main

end TwE6InnerAbs

section Final



theorem bal209TwoInnerCompType_holds : Bal209TwoInnerCompType :=
  bal209TwoInnerCompType_of_model twE6InnerCompModel_holds

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
