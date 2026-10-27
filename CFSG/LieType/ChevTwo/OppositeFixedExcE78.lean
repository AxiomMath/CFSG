module

public import CFSG.LieType.ChevTwo.OppositeFixedExcSemi
public import CFSG.LieType.ChevTwo.OppositeFixedExcBase
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalGroup
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalKempf

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits

variable {τ : Tag} {K : Type} [Field K]

@[expose] def gamSub (H : Subgroup (ModGL τ K))
    (hH : ∀ σ : RingAut K, ∀ h ∈ H, fieldAutHom τ K σ h ∈ H) : Subgroup (GamL τ K) where
  carrier := {s | s.left ∈ H}
  one_mem' := by
    change (1 : ModGL τ K) ∈ H
    exact one_mem H
  mul_mem' := fun {a b} ha hb => by
    change a.left * fieldAutHom τ K a.right b.left ∈ H
    exact mul_mem ha (hH _ _ hb)
  inv_mem' := fun {a} ha => by
    change fieldAutHom τ K a.right⁻¹ a.left⁻¹ ∈ H
    exact hH _ _ (inv_mem ha)

theorem mem_gamSub {H : Subgroup (ModGL τ K)}
    {hH : ∀ σ : RingAut K, ∀ h ∈ H, fieldAutHom τ K σ h ∈ H} {s : GamL τ K} :
    s ∈ gamSub H hH ↔ s.left ∈ H := Iff.rfl

section Cert


theorem fieldAut_mem_parabolicSubgroup (σ : RingAut K) {J : Set (Fin τ.rank)} {h : ModGL τ K}
    (hh : h ∈ parabolicSubgroup τ K J) : fieldAutHom τ K σ h ∈ parabolicSubgroup τ K J := by
  have hle : parabolicSubgroup τ K J ≤
      (parabolicSubgroup τ K J).comap (fieldAutHom τ K σ).toMonoidHom := by
    refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_sup_left (entrywise_mem_borelGroup (σ := σ) hb)
    · rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      change Units.map (entrywiseHom σ.toRingHom) (weylElt τ K j 1) ∈ _
      rw [entrywise_weylElt_one]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, rfl⟩)
  exact hle hh

theorem fieldAut_mem_parabolicLevi (σ : RingAut K) {J : Set (Fin τ.rank)} {h : ModGL τ K}
    (hh : h ∈ parabolicLevi τ K J) : fieldAutHom τ K σ h ∈ parabolicLevi τ K J := by
  have hle : parabolicLevi τ K J ≤
      (parabolicLevi τ K J).comap (fieldAutHom τ K σ).toMonoidHom := by
    refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_sup_left (entrywise_mem_torusGroup (σ := σ) hb)
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        change Units.map (entrywiseHom σ.toRingHom) (xUnit τ K j c) ∈ _
        rw [units_map_entrywiseHom_xUnit]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, _, Or.inl rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        change Units.map (entrywiseHom σ.toRingHom) (yUnit τ K j c) ∈ _
        rw [units_map_entrywiseHom_yUnit]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, _, Or.inr rfl⟩)
  exact hle hh

theorem fieldAut_mem_parabolicRadical (σ : RingAut K) {J : Set (Fin τ.rank)} {h : ModGL τ K}
    (hh : h ∈ parabolicRadical τ K J) : fieldAutHom τ K σ h ∈ parabolicRadical τ K J :=
  entrywise_mem_rootSpan (σ := σ) hh

theorem fieldAut_mem_adjointGroup (σ : RingAut K) {h : ModGL τ K}
    (hh : h ∈ adjointGroup τ K) : fieldAutHom τ K σ h ∈ adjointGroup τ K := by
  have := map_exactEntrywiseAut (τ := τ) (K := K) σ (H := adjointGroup τ K) (Or.inl rfl)
  rw [← this]
  exact Subgroup.mem_map_of_mem _ hh

variable (τ K) in
@[expose] def UniqueNormalForm : Prop :=
  ∀ α : MulAut ↥(adjointGroup τ K), ∃! gσ : ↥(adjointGroup τ K) × RingAut K,
    ∀ h : ↥(adjointGroup τ K), ((α h : ↥(adjointGroup τ K)) : ModGL τ K) =
      (gσ.1 : ModGL τ K) * Units.map (entrywiseHom (gσ.2 : K →+* K)) (h : ModGL τ K) *
        (gσ.1 : ModGL τ K)⁻¹

theorem uniqueNormalForm_E78
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hτ : τ = Tag.E7 ∨ τ = Tag.E8) : UniqueNormalForm τ K :=
  (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ).1

section Lift

variable (hNF : UniqueNormalForm τ K)

@[expose] noncomputable def liftAut (α : MulAut ↥(adjointGroup τ K)) : GamL τ K :=
  ⟨((hNF α).choose.1 : ModGL τ K), (hNF α).choose.2⟩

theorem liftAut_left_mem (α : MulAut ↥(adjointGroup τ K)) :
    (liftAut hNF α).left ∈ adjointGroup τ K :=
  (hNF α).choose.1.2

theorem liftAut_spec (α : MulAut ↥(adjointGroup τ K)) (h : ↥(adjointGroup τ K)) :
    ((α h : ↥(adjointGroup τ K)) : ModGL τ K) = conjAct τ K (liftAut hNF α) (h : ModGL τ K) := by
  rw [conjAct_apply]
  exact (hNF α).choose_spec.1 h

theorem liftAut_unique (α : MulAut ↥(adjointGroup τ K)) (g : GamL τ K)
    (hg : g.left ∈ adjointGroup τ K)
    (hspec : ∀ h : ↥(adjointGroup τ K),
      ((α h : ↥(adjointGroup τ K)) : ModGL τ K) = conjAct τ K g (h : ModGL τ K)) :
    liftAut hNF α = g := by
  have h : (hNF α).choose = ((⟨g.left, hg⟩ : ↥(adjointGroup τ K)), g.right) :=
    (hNF α).unique (hNF α).choose_spec.1 (fun h => by
      rw [hspec h, conjAct_apply])
  refine SemidirectProduct.ext ?_ ?_
  · exact congrArg (fun p : ↥(adjointGroup τ K) × RingAut K => (p.1 : ModGL τ K)) h
  · exact congrArg (fun p : ↥(adjointGroup τ K) × RingAut K => p.2) h

theorem liftAut_one : liftAut hNF 1 = 1 :=
  liftAut_unique hNF 1 1 (one_mem _) fun h => by
    rw [map_one, MulAut.one_apply]
    rfl

theorem liftAut_mul (α β : MulAut ↥(adjointGroup τ K)) :
    liftAut hNF (α * β) = liftAut hNF α * liftAut hNF β := by
  refine liftAut_unique hNF _ _ ?_ fun h => ?_
  · change (liftAut hNF α).left * fieldAutHom τ K (liftAut hNF α).right (liftAut hNF β).left ∈ _
    exact mul_mem (liftAut_left_mem hNF α)
      (fieldAut_mem_adjointGroup _ (liftAut_left_mem hNF β))
  · rw [MulAut.mul_apply, liftAut_spec hNF α, liftAut_spec hNF β, map_mul, MulAut.mul_apply]

@[expose] noncomputable def liftHom : MulAut ↥(adjointGroup τ K) →* GamL τ K where
  toFun := liftAut hNF
  map_one' := liftAut_one hNF
  map_mul' := liftAut_mul hNF

theorem liftHom_injective : Function.Injective (liftHom hNF) := fun α β h => by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [liftAut_spec hNF α, liftAut_spec hNF β]
  exact congrArg (fun s => conjAct τ K s (x : ModGL τ K)) h

end Lift

theorem fieldAut_mul_inv_apply (σ : RingAut K) (x : ModGL τ K) :
    fieldAutHom τ K σ (fieldAutHom τ K σ⁻¹ x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem conj_inl (s : GamL τ K) (q : ModGL τ K) :
    s * SemidirectProduct.inl q * s⁻¹ = SemidirectProduct.inl (conjAct τ K s q) := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      SemidirectProduct.left_inl, mul_one, fieldAut_mul_inv_apply, conjAct_apply]
    rfl
  · rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.right_inl, SemidirectProduct.inv_right, mul_one, mul_inv_cancel]

theorem exists_conj_into_levi [Finite K] [CharP K 2] [Finite (ModGL τ K)] (J : Set (Fin τ.rank))
    {T : Subgroup (GamL τ K)} (hT : ∀ s ∈ T, s.left ∈ parabolicSubgroup τ K J)
    (hodd : ¬ 2 ∣ Nat.card T) :
    ∃ y ∈ parabolicRadical τ K J, ∀ s ∈ T,
      ((SemidirectProduct.inl y : GamL τ K) * s * (SemidirectProduct.inl y)⁻¹).left ∈
        parabolicLevi τ K J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinσ : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have hfinΓ : Finite (GamL τ K) :=
    Finite.of_equiv (ModGL τ K × RingAut K) (SemidirectProduct.equivProd).symm
  obtain ⟨hQP, -, -, -, hQM, -, hdec, -⟩ := parabolic_root_radical_Levi_factors τ K J
  have hQ2 : IsPGroup 2 (parabolicRadical τ K J) :=
    (isPGroup_posUnipotent 2 τ).to_le (parabolicRadical_le_posUnipotent J)
  let Ppar : Subgroup (GamL τ K) :=
    gamSub (parabolicSubgroup τ K J) fun σ h hh => fieldAut_mem_parabolicSubgroup σ hh
  let Mlev : Subgroup (GamL τ K) :=
    gamSub (parabolicLevi τ K J) fun σ h hh => fieldAut_mem_parabolicLevi σ hh
  let Qrad : Subgroup (GamL τ K) := (parabolicRadical τ K J).map SemidirectProduct.inl
  have hQrad2 : IsPGroup 2 Qrad := hQ2.map _
  have hQradPpar : Qrad ≤ Ppar := by
    rintro _ ⟨q, hq, rfl⟩
    exact hQP hq
  have hPparN : Ppar ≤ Subgroup.normalizer (Qrad : Set (GamL τ K)) := by
    refine le_normalizer_of_conj_mem fun s hs y hy => ?_
    obtain ⟨q, hq, rfl⟩ := hy
    rw [conj_inl]
    refine ⟨conjAct τ K s q, ?_, rfl⟩
    rw [conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical J hs) _).1
      (fieldAut_mem_parabolicRadical s.right hq)
  have hQradMlev : Qrad ⊓ Mlev = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨q, hq, rfl⟩, hxM⟩ := Subgroup.mem_inf.1 hx
    have : q = 1 := Subgroup.mem_bot.1 (hQM ▸ Subgroup.mem_inf.2 ⟨hq, hxM⟩)
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hdec' : ∀ g ∈ Ppar, ∃ q ∈ Qrad, ∃ m ∈ Mlev, q * m = g := by
    intro g hg
    obtain ⟨qm, ⟨hq, hm, hx⟩, -⟩ := hdec g.left hg
    refine ⟨SemidirectProduct.inl qm.1, ⟨qm.1, hq, rfl⟩, ⟨qm.2, g.right⟩, hm, ?_⟩
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        map_one, MulAut.one_apply]
      exact hx.symm
    · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
  obtain ⟨y, hyQ, hyM⟩ := exists_conj_le_of_complement (p := 2) (P := Ppar) (Q := Qrad) (M := Mlev)
    hQrad2 hQradPpar hPparN hQradMlev hdec' hT hodd
  obtain ⟨y₀, hy₀, rfl⟩ := hyQ
  refine ⟨y₀, hy₀, fun s hs => ?_⟩
  exact hyM (Subgroup.mem_map_of_mem _ hs)

variable (τ K) in
@[expose] noncomputable def radG (J : Set (Fin τ.rank)) : Subgroup ↥(adjointGroup τ K) :=
  (parabolicRadical τ K J).subgroupOf (adjointGroup τ K)

variable (τ K) in
@[expose] noncomputable def parG (J : Set (Fin τ.rank)) : Subgroup ↥(adjointGroup τ K) :=
  (parabolicSubgroup τ K J).subgroupOf (adjointGroup τ K)

theorem conjAct_conj (y s : GamL τ K) (g : ModGL τ K) :
    conjAct τ K (y * s * y⁻¹) g =
      conjAct τ K y (conjAct τ K s (conjAct τ K y⁻¹ g)) := by
  rw [map_mul (conjAct τ K), map_mul (conjAct τ K)]
  rfl

theorem liftAut_left_mem_parabolic (hNF : UniqueNormalForm τ K) (J : Set (Fin τ.rank))
    {α : MulAut ↥(adjointGroup τ K)} (hα : (radG τ K J).map α.toMonoidHom = radG τ K J)
    (hNQ : Subgroup.normalizer ((radG τ K J : Subgroup ↥(adjointGroup τ K)) :
      Set ↥(adjointGroup τ K)) = parG τ K J) :
    (liftAut hNF α).left ∈ parabolicSubgroup τ K J := by
  set s := liftAut hNF α with hs
  have hm : s.left ∈ adjointGroup τ K := liftAut_left_mem hNF α
  have hmem : (⟨s.left, hm⟩ : ↥(adjointGroup τ K)) ∈ Subgroup.normalizer
      ((radG τ K J : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    let x'' : ↥(adjointGroup τ K) :=
      ⟨fieldAutHom τ K s.right⁻¹ (x : ModGL τ K), fieldAut_mem_adjointGroup _ x.2⟩
    have hαx : ((α x'' : ↥(adjointGroup τ K)) : ModGL τ K) =
        s.left * (x : ModGL τ K) * s.left⁻¹ := by
      rw [liftAut_spec hNF α, conjAct_apply]
      change s.left * fieldAutHom τ K s.right (fieldAutHom τ K s.right⁻¹ (x : ModGL τ K)) *
        s.left⁻¹ = _
      rw [fieldAut_mul_inv_apply]
    have e : (⟨s.left, hm⟩ * x * (⟨s.left, hm⟩ : ↥(adjointGroup τ K))⁻¹ :
        ↥(adjointGroup τ K)) = α x'' := Subtype.ext (by rw [hαx]; rfl)
    have h1 : (α x'' ∈ radG τ K J) ↔ x'' ∈ radG τ K J := by
      constructor
      · intro h
        rw [← hα] at h
        obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 h
        have : q = x'' := α.injective hqe
        exact this ▸ hq
      · intro h
        rw [← hα]
        exact Subgroup.mem_map_of_mem _ h
    have h2 : x'' ∈ radG τ K J ↔ x ∈ radG τ K J := by
      rw [radG, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have := fieldAut_mem_parabolicRadical s.right h
        rwa [fieldAut_mul_inv_apply] at this
      · exact fun h => fieldAut_mem_parabolicRadical _ h
    rw [e]
    exact h2.symm.trans h1.symm
  rw [hNQ] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem autCentralizer_inf_radG_eq_bot [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hNF : UniqueNormalForm τ K)
    (J : Set (Fin τ.rank)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut ↥(adjointGroup τ K))} (hR : IsPGroup p R)
    (hQR : ∀ α ∈ R, (radG τ K J).map α.toMonoidHom = radG τ K J)
    (hNQ : Subgroup.normalizer ((radG τ K J : Subgroup ↥(adjointGroup τ K)) :
      Set ↥(adjointGroup τ K)) = parG τ K J)
    (hC : autCentralizer R ≤ parG τ K J) :
    autCentralizer R ⊓ radG τ K J = ⊥ := by
  classical
  have hfinM : Finite (ModGL τ K) := finite_modGL
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  obtain ⟨⟨w₁, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hwC, hwQ⟩ := Subgroup.mem_inf.1 hw
  have hw1' : (w₁ : ModGL τ K) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  obtain ⟨hQP, -, -, -, hQM, -, hdec, -⟩ := parabolic_root_radical_Levi_factors τ K J
  set T : Subgroup (GamL τ K) := R.map (liftHom hNF) with hT
  have hTcard : Nat.card T = Nat.card R :=
    Subgroup.card_map_of_injective (liftHom_injective hNF)
  have hRodd : Nat.card R % 2 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    rw [hk]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow)
  have hTodd : ¬ 2 ∣ Nat.card T := by
    rw [hTcard]; exact Nat.two_dvd_ne_zero.2 hRodd
  have hTP : ∀ s ∈ T, s.left ∈ parabolicSubgroup τ K J := by
    rintro _ ⟨α, hα, rfl⟩
    exact liftAut_left_mem_parabolic hNF J (hQR α hα) hNQ
  obtain ⟨y₀, hy₀, hyM⟩ := exists_conj_into_levi J hTP hTodd
  set y : GamL τ K := SemidirectProduct.inl y₀ with hy
  set S : Subgroup (GamL τ K) := T.map (MulAut.conj y).toMonoidHom with hS
  have hSM : ∀ s ∈ S, s.left ∈ parabolicLevi τ K J := by
    rintro _ ⟨s, hs, rfl⟩
    exact hyM s hs
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj y).injective, hTcard]
    exact Nat.odd_iff.2 hRodd
  have hconjy : ∀ g : ModGL τ K, conjAct τ K y g = y₀ * g * y₀⁻¹ := fun g => by
    rw [hy, conjAct_inl, MulAut.conj_apply]
  have hconjyinv : ∀ g : ModGL τ K, conjAct τ K y⁻¹ g = y₀⁻¹ * g * y₀ := fun g => by
    rw [map_inv, hy, conjAct_inl, ← map_inv, MulAut.conj_apply, inv_inv]
  have hu : (w₁ : ModGL τ K) ∈ parabolicRadical τ K J := Subgroup.mem_subgroupOf.1 hwQ
  have hy₀P : y₀ ∈ parabolicSubgroup τ K J := hQP hy₀
  have hu' : y₀ * (w₁ : ModGL τ K) * y₀⁻¹ ∈ parabolicRadical τ K J :=
    (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical J hy₀P) _).1 hu
  have hu'1 : y₀ * (w₁ : ModGL τ K) * y₀⁻¹ ≠ 1 := fun h => hw1' (by
    have := congrArg (fun z => y₀⁻¹ * z * y₀) h
    simpa [mul_assoc] using this)
  have hfixT : ∀ s ∈ T, conjAct τ K s (w₁ : ModGL τ K) = w₁ := by
    rintro _ ⟨α, hα, rfl⟩
    change conjAct τ K (liftAut hNF α) _ = _
    rw [← liftAut_spec hNF α, hwC α hα]
  have hfix : ∀ s ∈ S, conjAct τ K s (y₀ * (w₁ : ModGL τ K) * y₀⁻¹) =
      y₀ * (w₁ : ModGL τ K) * y₀⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : conjAct τ K y⁻¹ (y₀ * (w₁ : ModGL τ K) * y₀⁻¹) = w₁ := by
      rw [hconjyinv]; group
    rw [conjAct_conj, h1, hfixT s hs, hconjy]
  obtain ⟨v, hvQ, hv1, hvfix⟩ := exists_fixed_mem_oppRadical_semi hτ hSM hSodd hu' hu'1 hfix
  have hvG : v ∈ adjointGroup τ K := rootSpan_le_adjointGroup K _ hvQ
  have hy₀G : y₀ ∈ adjointGroup τ K := rootSpan_le_adjointGroup K _ hy₀
  have hwG : y₀⁻¹ * v * y₀ ∈ adjointGroup τ K := mul_mem (mul_mem (inv_mem hy₀G) hvG) hy₀G
  have hwfix : ∀ s ∈ T, conjAct τ K s (y₀⁻¹ * v * y₀) = y₀⁻¹ * v * y₀ := by
    intro s hs
    have h := hvfix _ (Subgroup.mem_map_of_mem _ hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [conjAct_conj, hconjyinv, hconjy] at h
    calc conjAct τ K s (y₀⁻¹ * v * y₀) =
        y₀⁻¹ * (y₀ * conjAct τ K s (y₀⁻¹ * v * y₀) * y₀⁻¹) * y₀ := by group
      _ = y₀⁻¹ * v * y₀ := by rw [h]
  have hwC' : (⟨y₀⁻¹ * v * y₀, hwG⟩ : ↥(adjointGroup τ K)) ∈ autCentralizer R := by
    intro α hα
    refine Subtype.ext ?_
    rw [liftAut_spec hNF α]
    exact hwfix (liftHom hNF α) ⟨α, hα, rfl⟩
  have hwP : y₀⁻¹ * v * y₀ ∈ parabolicSubgroup τ K J := Subgroup.mem_subgroupOf.1 (hC hwC')
  have hvP : v ∈ parabolicSubgroup τ K J := by
    have e : v = y₀ * (y₀⁻¹ * v * y₀) * y₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hy₀P hwP) (inv_mem hy₀P)
  have h0 := Subgroup.mem_inf.2 ⟨hvP, hvQ⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hv1 (Subgroup.mem_bot.1 h0)

theorem mem_normalizer_map_subtype {G : Type*} [Group G] {K' : Subgroup G} {Q : Subgroup K'}
    {x : K'} (hx : x ∈ Subgroup.normalizer (Q : Set K')) :
    (x : G) ∈ Subgroup.normalizer ((Q.map K'.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨x * q * x⁻¹, (hx q).1 hq, rfl⟩
  · rintro ⟨q', hq', hq'e⟩
    refine ⟨x⁻¹ * q' * x, (hx _).2 (by rw [show x * (x⁻¹ * q' * x) * x⁻¹ = q' by group]; exact hq'), ?_⟩
    have h1 : (q' : G) = (x : G) * h * (x : G)⁻¹ := hq'e
    change ((x⁻¹ * q' * x : K') : G) = h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1]
    group

theorem oppositeFixed_adjointGroup_of_normalForm [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hNF : UniqueNormalForm τ K) :
    OppositeFixed ↥(adjointGroup τ K) := by
  intro p hp hp2 R hR Q hQ0 hQ2 hcore hne hRQ hC
  classical
  have hfinM : Finite (ModGL τ K) := finite_modGL
  have hQ₀ne : Q.map (adjointGroup τ K).subtype ≠ ⊥ := fun h =>
    hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q (adjointGroup τ K).subtype_injective).1 h)
  obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_ordinary (Subgroup.map_subtype_le Q)
    (hQ2.map (adjointGroup τ K).subtype) hQ₀ne
  have hQJle : parabolicRadical τ K J ≤ adjointGroup τ K := fun x hx => rootSpan_le_adjointGroup K _ hx
  have hQJ2 : IsPGroup 2 (radG τ K J) := by
    have h2 : IsPGroup 2 (parabolicRadical τ K J) :=
      (isPGroup_posUnipotent 2 τ).to_le (parabolicRadical_le_posUnipotent J)
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe hQJle).symm
  have hPJ : parG τ K J ≤ Subgroup.normalizer ((radG τ K J : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := parabolicSubgroup_le_normalizer_parabolicRadical J (Subgroup.mem_subgroupOf.1 hx)
    simp only [radG, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' _
  have hN : ∀ x ∈ Subgroup.normalizer (Q : Set ↥(adjointGroup τ K)), (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ * x * ⟨g, hg⟩ ∈ parG τ K J :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hP x x.2 (mem_normalizer_map_subtype hx))
  have hQ : ∀ q ∈ Q, (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ * q * ⟨g, hg⟩ ∈ radG τ K J :=
    fun q hq => Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)
  obtain ⟨hQ', hNQ⟩ := std_position (⟨g, hg⟩ : ↥(adjointGroup τ K)) hcore hQJ2 hPJ hN hQ
  set γ : MulAut ↥(adjointGroup τ K) := MulAut.conj (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ with hγ
  set R' : Subgroup (MulAut ↥(adjointGroup τ K)) := R.map (MulAut.conj γ).toMonoidHom with hR'
  have hR'p : IsPGroup p R' := hR.map _
  have hQmap : Q.map γ.toMonoidHom = radG τ K J := hQ'
  have hQR' : ∀ α' ∈ R', (radG τ K J).map α'.toMonoidHom = radG τ K J := by
    rintro _ ⟨α, hα, rfl⟩
    have e : ((MulAut.conj γ).toMonoidHom α).toMonoidHom.comp γ.toMonoidHom =
        γ.toMonoidHom.comp α.toMonoidHom := by
      ext x; simp [MulAut.conj_apply]
    rw [← hQmap, Subgroup.map_map, e, ← Subgroup.map_map, hRQ α hα]
  have hC' : autCentralizer R' ≤ parG τ K J := by
    intro x hx
    have hx' : γ⁻¹ x ∈ autCentralizer R := by
      intro α hα
      have h := hx ((MulAut.conj γ).toMonoidHom α) ⟨α, hα, rfl⟩
      have h2 : γ (α (γ⁻¹ x)) = x := by simpa [MulAut.conj_apply] using h
      calc α (γ⁻¹ x) = γ⁻¹ (γ (α (γ⁻¹ x))) := by simp
        _ = γ⁻¹ x := by rw [h2]
    have hN' : γ⁻¹ x ∈ Subgroup.normalizer (Q : Set ↥(adjointGroup τ K)) := hC hx'
    have h3 : x ∈ Subgroup.normalizer ((Q.map γ.toMonoidHom : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
      rw [← Subgroup.map_equiv_normalizer_eq Q γ]
      exact ⟨γ⁻¹ x, hN', by simp⟩
    rw [hQmap, hNQ] at h3
    exact h3
  have key := autCentralizer_inf_radG_eq_bot hτ hNF J hp hp2 hR'p hQR' hNQ hC'
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzC, hzQ⟩ := Subgroup.mem_inf.1 hz
  have hz1 : γ z ∈ autCentralizer R' ⊓ radG τ K J := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      have h := hzC α hα
      change (γ * α * γ⁻¹) (γ z) = γ z
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h]
    · rw [← hQmap]
      exact Subgroup.mem_map_of_mem _ hzQ
  rw [key] at hz1
  exact Subgroup.mem_bot.2 ((MulEquiv.map_eq_one_iff γ).1 (Subgroup.mem_bot.1 hz1))

theorem charP_two_of_card_two_pow {f : ℕ} [Finite K] (h : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem oppositeFixed_adjointGroup_E78 [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hτ : τ = Tag.E7 ∨ τ = Tag.E8) :
    OppositeFixed ↥(adjointGroup τ K) := by
  haveI : CharP K 2 := charP_two_of_card_two_pow hK
  exact oppositeFixed_adjointGroup_of_normalForm
    (hτ.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr h))))
    (uniqueNormalForm_E78 hf hK hτ)

theorem oppositeFixed_of_untwistedChevalleyModel_E78 {S : Type} [Group S] (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    {f : ℕ} (hf : 1 ≤ f) (h : UntwistedChevalleyModel S τ (2 ^ f)) : OppositeFixed S := by
  obtain ⟨K', _, hfin, hcard, ⟨e⟩⟩ := h
  have e' : S ≃* ↥(adjointGroup τ K') := e.trans
    ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := τ) (K := K'))).trans
      QuotientGroup.quotientBot)
  exact oppositeFixed_of_mulEquiv e' (oppositeFixed_adjointGroup_E78 hf hcard hτ)

end Cert

end CFSG.LieType.ChevTwo.Semi
