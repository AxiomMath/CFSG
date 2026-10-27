module

public import CFSG.LieType.ChevTwo.OppositeFixedExcE78
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalTwisted

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical

variable {K : Type} [Field K]

@[expose] def fixSub {τ : Tag} (S : Subgroup (GamL τ K)) : Subgroup (ModGL τ K) where
  carrier := {z | ∀ s ∈ S, conjAct τ K s z = z}
  one_mem' := fun s _ => map_one _
  mul_mem' := fun {a b} ha hb s hs => by rw [map_mul, ha s hs, hb s hs]
  inv_mem' := fun {a} ha s hs => by rw [map_inv, ha s hs]

theorem twistHom_conjAct (t : TwistTag) (σ₀ : RingAut K) (s : GamL t.tag K)
    (hs : twistHom t K (σ₀ : K →+* K) s.left = s.left) (hc : s.right * σ₀ = σ₀ * s.right)
    (z : ModGL t.tag K) :
    twistHom t K (σ₀ : K →+* K) (conjAct t.tag K s z) =
      conjAct t.tag K s (twistHom t K (σ₀ : K →+* K) z) := by
  have hcomm : ((s.right : K →+* K)).comp (σ₀ : K →+* K) = (σ₀ : K →+* K).comp (s.right : K →+* K) := by
    ext c
    exact congrArg (fun τ : RingAut K => τ c) hc
  rw [conjAct_apply, conjAct_apply, map_mul, map_mul, map_inv, hs]
  congr 2
  rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp, units_map_entrywiseHom_comp,
    hcomm]

section Cert

theorem exists_fixed_mem_oppRadical_twisted [Finite K] [CharP K 2] (σ₀ : RingAut K)
    (hσ₀ : ∀ c, σ₀ (σ₀ c) = c) {J : Set (Fin TwistTag.E6.foldedTag.rank)}
    {S : Subgroup (GamL TwistTag.E6.tag K)}
    (hSL : ∀ s ∈ S, s.left ∈ parabolicLevi TwistTag.E6.tag K (TwistTag.E6.orbitUnion J))
    (hSΓ : ∀ s ∈ S, twistHom TwistTag.E6 K (σ₀ : K →+* K) s.left = s.left ∧
      s.right * σ₀ = σ₀ * s.right)
    (hodd : Odd (Nat.card S)) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ parabolicRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J)) (hu1 : u ≠ 1)
    (hfix : ∀ s ∈ S, conjAct TwistTag.E6.tag K s u = u) :
    ∃ w ∈ oppRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J), w ≠ 1 ∧
      twistHom TwistTag.E6 K (σ₀ : K →+* K) w = w ∧
      ∀ s ∈ S, conjAct TwistTag.E6.tag K s w = w := by
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  obtain ⟨v, hvQ, hv1, hvfix⟩ := exists_fixed_mem_oppRadical_semi hτ hSL hodd hu hu1 hfix
  set X : Subgroup (ModGL TwistTag.E6.tag K) :=
    oppRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) ⊓ fixSub S with hX
  have hvX : v ∈ X := Subgroup.mem_inf.2 ⟨hvQ, hvfix⟩
  have hX2 : IsPGroup 2 X :=
    (isPGroup_negUnipotent TwistTag.E6.tag).to_le
      (inf_le_left.trans (oppRadical_le_negUnipotent _))
  have hXne : X ≠ ⊥ := fun h => hv1 (Subgroup.mem_bot.1 (h ▸ hvX))
  have hσ₀' : (σ₀ : K →+* K) ^ TwistTag.E6.order = 1 := by
    show (σ₀ : K →+* K) ^ 2 = 1
    rw [pow_two]
    refine RingHom.ext fun c => ?_
    exact hσ₀ c
  have hFQ := map_twistHom_oppRadical TwistTag.E6 (σ₀ : K →+* K) σ₀.surjective J
  obtain ⟨w, hwX, hw1, hwF⟩ := exists_fixed_ne_one (X := X) hX2 hXne
    (twistHom TwistTag.E6 K (σ₀ : K →+* K))
    (fun x hx => Subgroup.mem_inf.2 ⟨by
        rw [← hFQ]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 hx).1,
      fun s hs => by
        rw [← twistHom_conjAct TwistTag.E6 σ₀ s (hSΓ s hs).1 (hSΓ s hs).2,
          (Subgroup.mem_inf.1 hx).2 s hs]⟩)
    (fun x _ => twistHom_iterate_order_of_pow_eq_one (σ₀ : K →+* K) hσ₀' x)
  exact ⟨w, (Subgroup.mem_inf.1 hwX).1, hw1, hwF, (Subgroup.mem_inf.1 hwX).2⟩

theorem twistHom_fieldAut (t : TwistTag) (σ₀ δ : RingAut K) (hc : δ * σ₀ = σ₀ * δ)
    (z : ModGL t.tag K) :
    twistHom t K (σ₀ : K →+* K) (fieldAutHom t.tag K δ z) =
      fieldAutHom t.tag K δ (twistHom t K (σ₀ : K →+* K) z) := by
  have hcomm : ((δ : K →+* K)).comp (σ₀ : K →+* K) = (σ₀ : K →+* K).comp (δ : K →+* K) := by
    ext c
    exact congrArg (fun τ : RingAut K => τ c) hc
  rw [fieldAutHom_apply, fieldAutHom_apply, twistHom_apply, twistHom_apply, map_mul, map_mul,
    map_inv, units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp,
    units_map_entrywiseHom_comp, hcomm]

theorem fieldAut_mem_twistedFixedGroup (t : TwistTag) (σ₀ δ : RingAut K) (hc : δ * σ₀ = σ₀ * δ)
    {g : ModGL t.tag K} (hg : g ∈ twistedFixedGroup t K (σ₀ : K →+* K)) :
    fieldAutHom t.tag K δ g ∈ twistedFixedGroup t K (σ₀ : K →+* K) := by
  rw [mem_twistedFixedGroup_iff_twistHom] at hg ⊢
  exact ⟨fieldAut_mem_adjointGroup δ hg.1, by rw [twistHom_fieldAut t σ₀ δ hc, hg.2]⟩

theorem exists_conj_into_complement [Finite K] {τ : Tag} [Finite (ModGL τ K)]
    (Pp Qq Mm : Subgroup (ModGL τ K))
    (hQ2 : IsPGroup 2 Qq) (hQP : Qq ≤ Pp) (hPQ : ∀ x ∈ Pp, ∀ y ∈ Qq, x * y * x⁻¹ ∈ Qq)
    (hPσ : ∀ σ : RingAut K, ∀ h ∈ Pp, fieldAutHom τ K σ h ∈ Pp)
    (hMσ : ∀ σ : RingAut K, ∀ h ∈ Mm, fieldAutHom τ K σ h ∈ Mm)
    (hQσ : ∀ σ : RingAut K, ∀ h ∈ Qq, fieldAutHom τ K σ h ∈ Qq)
    (hQM : Qq ⊓ Mm = ⊥) (hdec : ∀ g ∈ Pp, ∃ q ∈ Qq, ∃ m ∈ Mm, q * m = g)
    {T : Subgroup (GamL τ K)} (hT : ∀ s ∈ T, s.left ∈ Pp) (hodd : ¬ 2 ∣ Nat.card T) :
    ∃ y ∈ Qq, ∀ s ∈ T,
      ((SemidirectProduct.inl y : GamL τ K) * s * (SemidirectProduct.inl y)⁻¹).left ∈ Mm := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinσ : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have hfinΓ : Finite (GamL τ K) :=
    Finite.of_equiv (ModGL τ K × RingAut K) (SemidirectProduct.equivProd).symm
  let Ppar : Subgroup (GamL τ K) := gamSub Pp hPσ
  let Mlev : Subgroup (GamL τ K) := gamSub Mm hMσ
  let Qrad : Subgroup (GamL τ K) := Qq.map SemidirectProduct.inl
  have hQrad2 : IsPGroup 2 Qrad := hQ2.map _
  have hQP' : Qrad ≤ Ppar := by
    rintro _ ⟨q, hq, rfl⟩
    exact hQP hq
  have hPN : Ppar ≤ Subgroup.normalizer (Qrad : Set (GamL τ K)) := by
    refine le_normalizer_of_conj_mem fun s hs y hy => ?_
    obtain ⟨q, hq, rfl⟩ := hy
    rw [conj_inl]
    refine ⟨conjAct τ K s q, ?_, rfl⟩
    rw [conjAct_apply]
    exact hPQ s.left hs _ (hQσ _ _ hq)
  have hQM' : Qrad ⊓ Mlev = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨q, hq, rfl⟩, hxM⟩ := Subgroup.mem_inf.1 hx
    have : q = 1 := Subgroup.mem_bot.1 (hQM ▸ Subgroup.mem_inf.2 ⟨hq, hxM⟩)
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hdec' : ∀ g ∈ Ppar, ∃ q ∈ Qrad, ∃ m ∈ Mlev, q * m = g := by
    intro g hg
    obtain ⟨q, hq, m, hm, hqm⟩ := hdec g.left hg
    refine ⟨SemidirectProduct.inl q, ⟨q, hq, rfl⟩, ⟨m, g.right⟩, hm, ?_⟩
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        map_one, MulAut.one_apply]
      exact hqm
    · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
  obtain ⟨y, hyQ, hyM⟩ := exists_conj_le_of_complement (p := 2) (P := Ppar) (Q := Qrad)
    (M := Mlev) hQrad2 hQP' hPN hQM' hdec' hT hodd
  obtain ⟨y₀, hy₀, rfl⟩ := hyQ
  refine ⟨y₀, hy₀, fun s hs => ?_⟩
  exact hyM (Subgroup.mem_map_of_mem _ hs)

theorem left_mem_normalizer {τ : Tag} {Cg Qg : Subgroup (ModGL τ K)}
    (hCσ : ∀ σ : RingAut K, ∀ h ∈ Cg, fieldAutHom τ K σ h ∈ Cg)
    (hQσ : ∀ σ : RingAut K, ∀ h ∈ Qg, fieldAutHom τ K σ h ∈ Qg)
    {α : MulAut ↥Cg} (hα : (Qg.subgroupOf Cg).map α.toMonoidHom = Qg.subgroupOf Cg)
    {s : GamL τ K} (hs : s.left ∈ Cg)
    (hspec : ∀ h : ↥Cg, ((α h : ↥Cg) : ModGL τ K) = conjAct τ K s (h : ModGL τ K)) :
    (⟨s.left, hs⟩ : ↥Cg) ∈ Subgroup.normalizer ((Qg.subgroupOf Cg : Subgroup ↥Cg) : Set ↥Cg) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  let x'' : ↥Cg := ⟨fieldAutHom τ K s.right⁻¹ (x : ModGL τ K), hCσ _ _ x.2⟩
  have hαx : ((α x'' : ↥Cg) : ModGL τ K) = s.left * (x : ModGL τ K) * s.left⁻¹ := by
    rw [hspec, conjAct_apply]
    change s.left * fieldAutHom τ K s.right (fieldAutHom τ K s.right⁻¹ (x : ModGL τ K)) *
      s.left⁻¹ = _
    rw [fieldAut_mul_inv_apply]
  have e : (⟨s.left, hs⟩ * x * (⟨s.left, hs⟩ : ↥Cg)⁻¹ : ↥Cg) = α x'' :=
    Subtype.ext (by rw [hαx]; rfl)
  have h1 : (α x'' ∈ Qg.subgroupOf Cg) ↔ x'' ∈ Qg.subgroupOf Cg := by
    constructor
    · intro h
      rw [← hα] at h
      obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 h
      have : q = x'' := α.injective hqe
      exact this ▸ hq
    · intro h
      rw [← hα]
      exact Subgroup.mem_map_of_mem _ h
  have h2 : x'' ∈ Qg.subgroupOf Cg ↔ x ∈ Qg.subgroupOf Cg := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have := hQσ s.right _ h
      rwa [fieldAut_mul_inv_apply] at this
    · exact fun h => hQσ _ _ h
  rw [e]
  exact h2.symm.trans h1.symm

end Cert

end CFSG.LieType.ChevTwo.Semi
