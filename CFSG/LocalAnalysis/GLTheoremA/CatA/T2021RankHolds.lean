module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCanon
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrthKind
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.I2015

section Induced

instance instCharacteristicGLAPPrimeCore (p : ℕ) (H : Type) [Group H] :
    (GLAPPrimeCore p H).Characteristic :=
  CFSG.pPrimeCore_characteristic

noncomputable def psAutHom (p : ℕ) (H : Type) [Group H] : MulAut H →* MulAut (psimpleOf p H) :=
  (MulAut.mapQuotient (Subgroup.center (ppQuot p H))).comp (MulAut.mapQuotient (GLAPPrimeCore p H))

noncomputable def autR (p : ℕ) {H : Type} [Group H] {R : Type} [Group R] (θ : psimpleOf p H ≃* R) :
    MulAut H →* MulAut R :=
  (MulAut.congr θ).toMonoidHom.comp (psAutHom p H)

variable {p : ℕ} {H : Type} [Group H]

theorem autR_apply_mk {R : Type} [Group R] (θ : psimpleOf p H ≃* R) (φ : MulAut H) (l : H) :
    autR p θ φ (θ (QuotientGroup.mk (QuotientGroup.mk l : ppQuot p H))) =
      θ (QuotientGroup.mk (QuotientGroup.mk (φ l) : ppQuot p H)) := by
  simp [autR, psAutHom, MulAut.congr_apply]

theorem induces_iff {R : Type} [Group R] (θ : psimpleOf p H ≃* R) (φ : MulAut H) (u : MulAut R) :
    GLAInduces θ (relOfAut p φ) u ↔ u = autR p θ φ := by
  constructor
  · intro h
    ext r
    obtain ⟨s, rfl⟩ := θ.surjective r
    induction s using QuotientGroup.induction_on with
    | H q =>
      induction q using QuotientGroup.induction_on with
      | H l =>
        rw [autR_apply_mk]
        exact h _ _ ⟨l, φ l, rfl, rfl, rfl⟩
  · rintro rfl q q' ⟨l, l', rfl, rfl, hl⟩
    rw [autR_apply_mk, hl]

theorem trivAut_iff (φ : MulAut H) :
    TrivAut p H φ ↔ MulAut.mapQuotient (GLAPPrimeCore p H) φ = 1 := by
  constructor
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [MulAut.mapQuotient_mk, MulAut.one_apply]
      exact QuotientGroup.eq_iff_div_mem.2 (by rw [div_eq_mul_inv]; exact h y)
  · intro h y
    have h1 := congrArg (fun α : MulAut (ppQuot p H) => α (QuotientGroup.mk y)) h
    simp only [MulAut.mapQuotient_mk, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq_iff_div_mem.1 h1
    rwa [div_eq_mul_inv] at h2

theorem eq_one_of_mapQuotient_center_eq_one {K : Type} [Group K] (hperf : commutator K = ⊤)
    (φ : MulAut K) (h : MulAut.mapQuotient (Subgroup.center K) φ = 1) : φ = 1 := by
  have hcent : ∀ x : K, x⁻¹ * φ x ∈ Subgroup.center K := by
    intro x
    have h1 := congrArg (fun α : MulAut (K ⧸ Subgroup.center K) => α (QuotientGroup.mk x)) h
    simp only [MulAut.mapQuotient_mk, MulAut.one_apply] at h1
    have : (QuotientGroup.mk (x⁻¹ * φ x) : K ⧸ Subgroup.center K) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
      exact inv_mul_cancel _
    exact (QuotientGroup.eq_one_iff _).1 this
  let c : K →* K :=
    { toFun := fun x => x⁻¹ * φ x
      map_one' := by simp
      map_mul' := fun x y => by
        have hx := (Subgroup.mem_center_iff.1 (hcent x)) (y⁻¹)
        calc (x * y)⁻¹ * φ (x * y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by simp [mul_assoc]
          _ = (x⁻¹ * φ x) * y⁻¹ * φ y := by
            rw [mul_assoc y⁻¹, ← hx]
            simp [mul_assoc]
          _ = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by simp [mul_assoc] }
  have hker : commutator K ≤ c.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.1 (hcent x) (c y)).symm
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ c.ker := hker (hperf ▸ Subgroup.mem_top x)
  have h2 : x⁻¹ * φ x = 1 := hx
  show φ x = x
  exact (inv_mul_eq_one.1 h2).symm

theorem trivAut_iff_autR {R : Type} [Group R] (θ : psimpleOf p H ≃* R)
    (hperf : commutator (ppQuot p H) = ⊤) (φ : MulAut H) : TrivAut p H φ ↔ autR p θ φ = 1 := by
  rw [trivAut_iff]
  constructor
  · intro h
    simp only [autR, psAutHom, MonoidHom.comp_apply, h, map_one]
  · intro h
    have h1 : psAutHom p H φ = 1 := (MulAut.congr θ).injective (by rw [map_one]; exact h)
    exact eq_one_of_mapQuotient_center_eq_one hperf _ h1

end Induced

section Datum

@[expose] def RankBody (p : ℕ) : LargeEvenRawCont := fun R _ I _ =>
  ∀ E : Subgroup (MulAut R), IsElemAbelian p E → p ^ 3 ≤ Nat.card E → ∃ e ∈ E, e ∈ I ∧ e ≠ 1

@[expose] def DatumFacts (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  CFSG.StandardType.GGRawInnField p R I F ∧ CFSG.StandardType.GGRawFieldCentral R I F ∧
    CFSG.StandardType.LargeEvenSimpleGuard (RankBody p) R I F ∧
    (¬ (lab.tag = .triD4 ∧ p = 3) → CFSG.StandardType.GGRawFieldConj p R I F)

theorem largeEvenRawDatum_exists_repack {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F ∧
      ∀ Q' : LargeEvenRawCont, Q' R I F → CFSG.Assembly.LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨_, _, _, _, hq, fun Q' hQ' => ⟨K, i1, i2, hK, b, c, hbc, hQ'⟩⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨_, _, _, _, hq, fun Q' hQ' => ⟨K, i1, i2, hK, hQ'⟩⟩)

theorem cAll_of_forall {lab : LargeEvenLabel} {P : LargeEvenRawCont}
    (h : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F) : MI.CAll lab P := fun _ hQ =>
  CFSG.StandardType.Canonical.largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq, h R I F⟩) hQ

theorem marking_and_datumFacts {X : Type} [Group X] {p : ℕ} {P : LargeEvenMarkProp X}
    (hall : ∀ lab, LargeEvenInLambda2 lab → MI.CAll lab (DatumFacts p lab))
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ DatumFacts p lab R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ (hall lab hlab _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hD⟩
  exact ⟨hs, hna, θ, hθ, hD⟩

theorem rankBody_of_pCyclic {R : Type} [Group R] {I F : Set (MulAut R)} {p : ℕ} (hp : p.Prime)
    (h : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧ (J.subgroupOf S).Normal ∧
      (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S) :
    RankBody p R I F := by
  obtain ⟨J, S, hJI, -, hN, hcyc, hpS⟩ := h
  intro E hE hcard
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hgE, hle⟩ := CFSG.StandardType.exists_le_zpowers_sup_of_cyclic (U := E) (U₁ := E ⊓ J)
    E.subtype hN hcyc (fun u => hpS u ⟨1, by simpa using hE.2 u u.2⟩)
    (fun u => ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨u.2, h⟩⟩)
  have hEJ : E ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨heE, heJ⟩ := Subgroup.mem_inf.1 he
    rw [Subgroup.mem_bot]
    exact hcon e heE (hJI ▸ heJ)
  rw [hEJ, sup_bot_eq] at hle
  have hEg : E = Subgroup.zpowers g := le_antisymm hle ((Subgroup.zpowers_le).2 hgE)
  have hcardle : Nat.card E ≤ p := by
    rw [hEg, Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos (hE.2 g hgE)
  have hp3 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end Datum

section D4


theorem rankBody_omegaPlusFour (K : Type) [Field K] [Finite K]
    {F : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))} :
    RankBody 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _) F := by
  classical
  intro E hE hcard
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hpE : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp3 hpE hcard
  set E' : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))) :=
    E₀.map E.subtype with hE'
  have hE'le : E' ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE'ab : IsElemAbelian 3 E' := isElemAbelian_mono hE hE'le
  have hE'card : Nat.card E' = 3 ^ 3 := by
    rw [hE', Subgroup.card_map_of_injective E.subtype_injective, hE₀]
  set σ := CFSG.HardMathSupport.Dickson.Bal207.D4Graph.isoAdj K with hσ
  set E'' := E'.map (MulAut.congr σ).toMonoidHom with hE''
  have hE''ab : IsElemAbelian 3 E'' := hE'ab.map _
  have hE''card : Nat.card E'' = 3 ^ 3 := by
    rw [hE'', Subgroup.card_map_of_injective (MulAut.congr σ).injective, hE'card]
  obtain ⟨k, hk1, hkE⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.exists_inner_ne_one_of_cube hE''ab hE''card
  obtain ⟨e, heE', he⟩ := Subgroup.mem_map.1 hkE
  have he' : (MulAut.congr σ) e = MulAut.conj k := he
  refine ⟨e, hE'le heE', ⟨σ.symm k, ?_⟩, ?_⟩
  · apply (MulAut.congr σ).injective
    rw [he']
    ext x
    simp [MulAut.congr_apply]
  · rintro rfl
    rw [map_one] at he'
    apply hk1
    have hkc : k ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun α : MulAut _ => α g) he'
      simp only [MulAut.one_apply, MulAut.conj_apply] at h1
      calc g * k = k * g * k⁻¹ * k := by rw [← h1]
        _ = k * g := by group
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot] at hkc
    exact (Subgroup.mem_bot).1 hkc

end D4

section Main


theorem rankBody_all {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (lab : LargeEvenLabel)
    (hlab : LargeEvenInLambda2 lab) :
    MI.CAll lab (CFSG.StandardType.LargeEvenSimpleGuard (RankBody p)) := by
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · obtain ⟨t, l, n⟩ := lab
    obtain ⟨ht, h4, rfl⟩ := hD
    dsimp only at ht h4
    subst ht h4
    exact Y10GClsOrth.canonicalLabelAll_omegaPlus rfl le_rfl fun K _ _ _ _ _ _ =>
      rankBody_omegaPlusFour K
  · exact MI.CAll.mono (fun R _ I F hc hs hna => rankBody_of_pCyclic hp (hc hs hna))
      (FP.canonRawPCyclic hp hp2 hlab hD)

theorem datumFacts_all {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (lab : LargeEvenLabel)
    (hlab : LargeEvenInLambda2 lab) : MI.CAll lab (DatumFacts p lab) := by
  have hconj : MI.CAll lab fun R _ I F =>
      ¬ (lab.tag = .triD4 ∧ p = 3) → CFSG.StandardType.GGRawFieldConj p R I F := by
    by_cases h3 : lab.tag = .triD4 ∧ p = 3
    · exact cAll_of_forall fun R _ I F h => absurd h3 h
    · exact MI.CAll.mono (fun R _ I F hc _ => hc) (FP.canonRawFieldConj hp hp2 hlab h3)
  exact (MI.canonRawInn hp hp2 hlab).and
    ((FP.canonRawFieldCentral hlab).and ((rankBody_all hp hp2 lab hlab).and hconj))

theorem t2021RankFact_holds : T2021RankFact := by
  classical
  intro H _ _ p 𝔅 _ _ ψ b hp hp2 _ hexp hcomm hTD4 hrank hF
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hF with hM | ⟨h3, hT4, -⟩
  swap
  · exact absurd ⟨h3, hT4⟩ hTD4
  obtain ⟨hperf, lab, hlab, hraw⟩ := marking_and_datumFacts (datumFacts_all hp hp2) hM
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, ⟨hlabp, f₀, hf₀F, u₀, hu₀I, hf₀p, hind⟩, hInn, hCent, hRank, hConj⟩,
    hrepack⟩ := largeEvenRawDatum_exists_repack hraw
  obtain ⟨hImul, hIinv, hIconj, hFI⟩ := hInn hs hna
  let J : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun ha hb => hImul _ ha _ hb
      one_mem' := by simpa using hIconj 1
      inv_mem' := fun ha => hIinv _ ha }
  have hu₀J : u₀ ∈ J := hu₀I
  have hf₀J : f₀ ∉ J := hFI f₀ hf₀F hf₀p
  haveI : Finite R := Finite.of_equiv _ θ.toEquiv
  haveI : Finite (MulAut R) := Finite.of_injective (fun φ : MulAut R => (φ : R → R)) DFunLike.coe_injective
  let ρ : 𝔅 →* MulAut R := (autR p θ).comp ψ
  have hρind : ∀ g, GLAInduces θ (relOfAut p (ψ g)) (ρ g) := fun g =>
    (induces_iff θ (ψ g) (ρ g)).2 rfl
  have hρb : ρ b = u₀ * f₀ * u₀⁻¹ := ((induces_iff θ (ψ b) _).1 hind).symm
  have hρtriv : ∀ g, TrivAut p H (ψ g) ↔ ρ g = 1 := fun g => trivAut_iff_autR θ hperf (ψ g)
  have hρexp : ∀ g, ρ g ^ p = 1 := fun g => by rw [← map_pow, hexp, map_one]
  have hker : Nat.card {g : 𝔅 // TrivAut p H (ψ g)} = Nat.card ρ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => (hρtriv g).trans MonoidHom.mem_ker.symm)
  have hcardE : p ^ 3 ≤ Nat.card ρ.range := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    have hpos : 0 < Nat.card ρ.ker := Nat.card_pos
    rw [hker] at hrank
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [h1, mul_comm]
    exact hrank
  have hEab : IsElemAbelian p ρ.range := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨g, hg⟩ := x.2
      obtain ⟨h, hh⟩ := y.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hg, ← hh, ← map_mul, ← map_mul, hcomm]
    · rintro _ ⟨g, rfl⟩
      exact hρexp g
  obtain ⟨_, ⟨b₁, rfl⟩, heI, he1⟩ := hRank hs hna ρ.range hEab hcardE
  have heJ : ρ b₁ ∈ J := heI
  have hordb₁ : orderOf (ρ b₁) = p := orderOf_eq_prime (hρexp b₁) he1
  have hf₀pow : f₀ ^ p = 1 := hf₀p ▸ pow_orderOf_eq_one f₀
  have hJpow : ∀ i : ℤ, f₀ ^ i ∈ J → f₀ ^ i = 1 := by
    intro i hi
    by_contra hne
    have hord : orderOf (f₀ ^ i) = p := by
      refine orderOf_eq_prime ?_ hne
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf₀pow, one_zpow]
    have hle : Subgroup.zpowers (f₀ ^ i) ≤ Subgroup.zpowers f₀ :=
      (Subgroup.zpowers_le).2 (Subgroup.zpow_mem_zpowers f₀ i)
    have heq : Subgroup.zpowers (f₀ ^ i) = Subgroup.zpowers f₀ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hf₀p])
    apply hf₀J
    have h1 : f₀ ∈ Subgroup.zpowers (f₀ ^ i) := heq ▸ Subgroup.mem_zpowers f₀
    exact (Subgroup.zpowers_le).2 hi h1
  have hconjJ : ∀ {x : MulAut R}, u₀ * x * u₀⁻¹ ∈ J → x ∈ J := by
    intro x hx
    have := J.mul_mem (J.mul_mem (J.inv_mem hu₀J) hx) hu₀J
    simpa [mul_assoc] using this
  have hbb₁ : b ∉ Subgroup.zpowers b₁ := by
    intro hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
    have h1 : ρ b ∈ J := by
      rw [← hk, map_zpow]
      exact J.zpow_mem heJ k
    rw [hρb] at h1
    exact hf₀J (hconjJ h1)
  have hNb : (Subgroup.zpowers b₁).Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have hdecomp : ∀ c ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers b₁, ∃ i j : ℤ, c = b ^ i * b₁ ^ j := by
    intro c hc
    have hc' : c ∈ ((Subgroup.zpowers b ⊔ Subgroup.zpowers b₁ : Subgroup 𝔅) : Set 𝔅) := hc
    rw [Subgroup.mul_normal] at hc'
    obtain ⟨y, hy, z, hz, rfl⟩ := hc'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨i, j, rfl⟩
  have hρij : ∀ i j : ℤ, ρ (b ^ i * b₁ ^ j) = u₀ * f₀ ^ i * u₀⁻¹ * ρ b₁ ^ j := by
    intro i j
    rw [map_mul, map_zpow, map_zpow, hρb, conj_zpow]
  have hpdvd : ∀ i : ℤ, f₀ ^ i = 1 → b ^ i = 1 := by
    intro i h4
    have : (p : ℤ) ∣ i := by
      rw [← hf₀p]
      exact orderOf_dvd_iff_zpow_eq_one.2 h4
    obtain ⟨k, rfl⟩ := this
    rw [zpow_mul, zpow_natCast, hexp, one_zpow]
  have hkerD : ∀ c ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers b₁, TrivAut p H (ψ c) → c = 1 := by
    intro c hc htriv
    obtain ⟨i, j, rfl⟩ := hdecomp c hc
    have h1 : ρ (b ^ i * b₁ ^ j) = 1 := (hρtriv _).1 htriv
    rw [hρij] at h1
    have h2 : u₀ * f₀ ^ i * u₀⁻¹ ∈ J := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact J.inv_mem (J.zpow_mem heJ j)
    have h4 : f₀ ^ i = 1 := hJpow i (hconjJ h2)
    rw [h4, mul_one, mul_inv_cancel, one_mul] at h1
    have h5 : b₁ ^ j = 1 := by
      have : (p : ℤ) ∣ j := by
        rw [← hordb₁]
        exact orderOf_dvd_iff_zpow_eq_one.2 h1
      obtain ⟨k, rfl⟩ := this
      rw [zpow_mul, zpow_natCast, hexp, one_zpow]
    rw [hpdvd i h4, h5, mul_one]
  have hnormal : ∀ α : MulAut R, ∀ v ∈ J, α * v * α⁻¹ ∈ J := by
    intro α v hv
    have h1 := hCent hs hna α v hv 1 (Subgroup.one_mem _)
    rw [mul_one] at h1
    have := J.mul_mem h1 hv
    simpa [mul_assoc] using this
  have hfield : ∀ c ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers b₁, c ∉ Subgroup.zpowers b₁ →
      FieldAutOn p H (ψ c) ∧ ¬ TrivAut p H (ψ c) := by
    intro c hc hcb
    refine ⟨?_, fun htriv => hcb ((hkerD c hc htriv).symm ▸ Subgroup.one_mem _)⟩
    obtain ⟨i, j, rfl⟩ := hdecomp c hc
    have hfi : f₀ ^ i ∉ J := by
      intro h
      apply hcb
      rw [hpdvd i (hJpow i h), one_mul]
      exact Subgroup.zpow_mem_zpowers b₁ j
    set d' := u₀⁻¹ * ρ b₁ ^ j * u₀ with hd'
    have hd'J : d' ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hu₀J) (J.zpow_mem heJ j)) hu₀J
    set d'' := f₀ ^ i * d' * (f₀ ^ i)⁻¹ with hd''
    have hd''J : d'' ∈ J := hnormal _ _ hd'J
    have hfcl : f₀ ^ i ∈ Subgroup.closure F := Subgroup.zpow_mem _ (Subgroup.subset_closure hf₀F) i
    have hx : ρ (b ^ i * b₁ ^ j) = u₀ * (d'' * f₀ ^ i) * u₀⁻¹ := by
      rw [hρij, hd'', hd']
      group
    have hxI : d'' * f₀ ^ i ∉ I := by
      intro h
      apply hfi
      have : (d'')⁻¹ * (d'' * f₀ ^ i) ∈ J := J.mul_mem (J.inv_mem hd''J) h
      simpa using this
    have hxp : (d'' * f₀ ^ i) ^ p = 1 := by
      have h1 : d'' * f₀ ^ i = u₀⁻¹ * ρ (b ^ i * b₁ ^ j) * u₀⁻¹⁻¹ := by
        rw [hx]
        group
      rw [h1, conj_pow, hρexp, mul_one, mul_inv_cancel]
    have hne : ¬ (lab.tag = .triD4 ∧ p = 3) := fun ⟨h1, h2⟩ => hlabp.elim (· h1) (· h2)
    obtain ⟨f', hf'F, u', hu'I, hf'p, hconj⟩ := hConj hne hs hna d'' hd''J (f₀ ^ i) hfcl hxI hxp
    have hρc : ρ (b ^ i * b₁ ^ j) = (u₀ * u') * f' * (u₀ * u')⁻¹ := by
      rw [hx, hconj]
      group
    refine Or.inl ⟨hperf, lab, hlab, hrepack _ ⟨hs, hna, θ, hlabp, f', hf'F, u₀ * u',
      J.mul_mem hu₀J hu'I, hf'p, ?_⟩⟩
    rw [← hρc]
    exact hρind _
  exact ⟨b₁, fun h => he1 ((hρtriv b₁).1 h), ⟨hperf, lab, hlab, hrepack _ ⟨hs, hna, θ, ρ b₁, heI, hρind b₁⟩⟩,
    hbb₁, hkerD, hfield⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
