module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerAffine

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def normalizerConjHom (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K →* K where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] def quotientNormalizerConjHom (Q U : Subgroup G) [(U.subgroupOf Q).Normal] {g : G}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    Q ⧸ U.subgroupOf Q →* Q ⧸ U.subgroupOf Q :=
  QuotientGroup.map _ _ (normalizerConjHom Q hgQ) fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hgU x).mp hx

theorem le_normalizer_commutator (H Q : Subgroup G) :
    H ≤ Subgroup.normalizer ((⁅H, Q⁆ : Subgroup G) : Set G) := by
  have key : ∀ a ∈ H, ∀ y ∈ ⁅H, Q⁆, a * y * a⁻¹ ∈ ⁅H, Q⁆ := by
    intro a ha y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a', ha', x, hx, rfl⟩ := hy
      have : a * ⁅a', x⁆ * a⁻¹ = ⁅a * a', x⁆ * ⁅a, x⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (H.mul_mem ha ha') hx)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ha hx))
    | one => simp only [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    | mul y z _ _ hy hz =>
      have : a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have : a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key a ha y, fun hy => ?_⟩
  have h := key a⁻¹ (H.inv_mem ha) _ hy
  have h2 : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rwa [h2] at h

theorem not_mem_sup_commutator_of_odd_normal [Finite G] {Q U A C : Subgroup G} {u : G}
    (hUQ : U ≤ Q) (hQU : Q ≤ Subgroup.centralizer (U : Set G))
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ U)
    (huQ : u ∈ Q) (huU : u ∉ U) (hu : u * u = 1)
    (hθ : ∀ x ∈ Q, involutionDisplacement u x ∈ U)
    (hE : ∀ x ∈ Q, x * u = u * x → x ∈ U ∨ u * x ∈ U)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hAu : A ≤ Subgroup.centralizer ({u} : Set G))
    (hCA : C ≤ A) (hAC : A ≤ Subgroup.normalizer (C : Set G)) (hCodd : Odd (Nat.card C))
    (hCfix : ∀ b ∈ U, (∀ c ∈ C, c * b * c⁻¹ = b) → b = 1) :
    u ∉ U ⊔ ⁅A, Q⁆ := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  have hnormal : (U.subgroupOf Q).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hc : (g : G) * x = x * g := (Subgroup.mem_centralizer_iff.mp (hQU g.2) x hx).symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc, mul_inv_cancel_right]
    exact hx⟩
  have hcommF : ∀ a b : Q ⧸ U.subgroupOf Q, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hQcomm _ (Q.inv_mem y.2) _ (Q.inv_mem x.2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h ⊢
    convert h using 1
    group
  let _ : CommGroup (Q ⧸ U.subgroupOf Q) :=
    { (inferInstance : Group (Q ⧸ U.subgroupOf Q)) with mul_comm := hcommF }
  have hUcomm : ∀ a b : U, a * b = b * a := fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (hQU (hUQ a.2)) b b.2).symm
  let _ : CommGroup U := { (inferInstance : Group U) with mul_comm := hUcomm }
  have hCQ : ∀ c ∈ C, c ∈ Subgroup.normalizer (Q : Set G) := fun c hc => hAQ (hCA hc)
  have hCU : ∀ c ∈ C, c ∈ Subgroup.normalizer (U : Set G) := fun c hc => hAU (hCA hc)
  have hcu : ∀ g ∈ A, g * u = u * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp (hAu hg)
  let act : A → Q ⧸ U.subgroupOf Q →* Q ⧸ U.subgroupOf Q := fun a =>
    quotientNormalizerConjHom Q U (hAQ a.2) (hAU a.2)
  have hact : ∀ (a : A) (x : Q), act a (QuotientGroup.mk x) =
      QuotientGroup.mk (normalizerConjHom Q (hAQ a.2) x) := fun _ _ => rfl
  let Nm : Q ⧸ U.subgroupOf Q →* Q ⧸ U.subgroupOf Q := ∏ c : C, act ⟨c, hCA c.2⟩
  have hNm : ∀ f, Nm f = ∏ c : C, act ⟨c, hCA c.2⟩ f := fun f =>
    MonoidHom.finsetProd_apply _ _ _
  let ubar : Q ⧸ U.subgroupOf Q := QuotientGroup.mk ⟨u, huQ⟩
  have hubar2 : ubar * ubar = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change u * u ∈ U
    rw [hu]
    exact U.one_mem
  have hubar1 : ubar ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact huU
  have hactu : ∀ a : A, act a ubar = ubar := by
    intro a
    rw [hact]
    congr 1
    apply Subtype.ext
    change (a : G) * u * (a : G)⁻¹ = u
    rw [hcu a a.2, mul_inv_cancel_right]
  have hNmu : Nm ubar = ubar := by
    rw [hNm]
    simp only [hactu, Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card]
    obtain ⟨k, hk⟩ := hCodd
    rw [hk, pow_succ, pow_mul, pow_two, hubar2, one_pow, one_mul]
  let θQ : Q →* U :=
    { toFun := fun x => ⟨involutionDisplacement u x, hθ x x.2⟩
      map_one' := Subtype.ext (by simp [involutionDisplacement, hu])
      map_mul' := fun x y => Subtype.ext
        (involutionDisplacement_mul hu (hQU x.2) (hθ y y.2)) }
  have hUker : U.subgroupOf Q ≤ θQ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change involutionDisplacement u x = 1
    rw [involutionDisplacement_eq_one_iff hu]
    exact Subgroup.mem_centralizer_iff.mp (hQU huQ) x hx
  let θbar : Q ⧸ U.subgroupOf Q →* U := QuotientGroup.lift _ θQ hUker
  let conjU : C → U →* U := fun c => normalizerConjHom U (hCU c c.2)
  have hθbar : ∀ (c : C) f, θbar (act ⟨c, hCA c.2⟩ f) = conjU c (θbar f) := by
    intro c f
    induction f using QuotientGroup.induction_on with | H x => ?_
    apply Subtype.ext
    change involutionDisplacement u ((c : G) * x * (c : G)⁻¹) =
      (c : G) * involutionDisplacement u x * (c : G)⁻¹
    exact involutionDisplacement_conj (hcu c (hCA c.2)) x
  have hNU : ∀ b : U, ∏ c : C, conjU c b = 1 := by
    intro b
    apply Subtype.ext
    apply hCfix _ (∏ c : C, conjU c b).2
    intro c₀ hc₀
    have h1 : conjU ⟨c₀, hc₀⟩ (∏ c : C, conjU c b) = ∏ c : C, conjU c b := by
      rw [map_prod]
      apply Fintype.prod_equiv (Equiv.mulLeft (⟨c₀, hc₀⟩ : C))
      intro c
      apply Subtype.ext
      change c₀ * ((c : G) * b * (c : G)⁻¹) * c₀⁻¹ = (c₀ * c) * b * (c₀ * (c : G))⁻¹
      group
    exact congrArg Subtype.val h1
  have hNmval : ∀ f, Nm f = 1 ∨ Nm f = ubar := by
    intro f
    have h1 : θbar (Nm f) = 1 := by
      rw [hNm, map_prod]
      simp only [hθbar]
      exact hNU (θbar f)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Nm f)
    rw [← hy] at h1 ⊢
    have h2 : (y : G) * u = u * y := by
      have h3 := congrArg Subtype.val h1
      exact (involutionDisplacement_eq_one_iff hu _).mp h3
    rcases hE y y.2 h2 with hyU | huy
    · left
      exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr hyU)
    · right
      have h3 : ubar * QuotientGroup.mk y = 1 := by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact huy
      calc (QuotientGroup.mk y : Q ⧸ U.subgroupOf Q) = ubar * (ubar * QuotientGroup.mk y) := by
            rw [← mul_assoc, hubar2, one_mul]
        _ = ubar := by rw [h3, mul_one]
  have hNmact : ∀ (a : A) f, Nm (act a f) = Nm f := by
    intro a f
    have haC := hAC a.2
    have hmem : ∀ c : C, (a : G)⁻¹ * c * a ∈ C := fun c => by
      apply (Subgroup.mem_normalizer_iff.mp haC _).mpr
      have : (a : G) * ((a : G)⁻¹ * c * a) * (a : G)⁻¹ = c := by group
      rw [this]
      exact c.2
    let e : C ≃ C :=
      { toFun := fun c => ⟨(a : G)⁻¹ * c * a, hmem c⟩
        invFun := fun c => ⟨(a : G) * c * (a : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp haC _).mp c.2⟩
        left_inv := fun c => Subtype.ext (by simp only; group)
        right_inv := fun c => Subtype.ext (by simp only; group) }
    have h1 : Nm (act a f) = act a (Nm f) := by
      rw [hNm, hNm, map_prod]
      apply Fintype.prod_equiv e
      intro c
      induction f using QuotientGroup.induction_on with | H x => ?_
      simp only [hact]
      congr 1
      apply Subtype.ext
      change (c : G) * ((a : G) * x * (a : G)⁻¹) * (c : G)⁻¹ =
        (a : G) * (((a : G)⁻¹ * c * a) * x * ((a : G)⁻¹ * c * a)⁻¹) * (a : G)⁻¹
      group
    rw [h1]
    rcases hNmval f with h | h <;> rw [h]
    · exact map_one _
    · exact hactu a
  let K : Subgroup G := ((Nm.comp (QuotientGroup.mk' (U.subgroupOf Q))).ker).map Q.subtype
  have hmemK : ∀ x : Q, Nm (QuotientGroup.mk x) = 1 → (x : G) ∈ K := fun x hx =>
    Subgroup.mem_map.mpr ⟨x, MonoidHom.mem_ker.mpr hx, rfl⟩
  have hUK : U ≤ K := by
    intro b hb
    refine hmemK ⟨b, hUQ hb⟩ ?_
    rw [(QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hb), map_one]
  have hcommK : ⁅A, Q⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have hmem : ⁅a, x⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAQ ha) x).mp hx) (Q.inv_mem hx)
    refine hmemK ⟨⁅a, x⁆, hmem⟩ ?_
    have h1 : (QuotientGroup.mk ⟨⁅a, x⁆, hmem⟩ : Q ⧸ U.subgroupOf Q) =
        act ⟨a, ha⟩ (QuotientGroup.mk ⟨x, hx⟩) * (QuotientGroup.mk ⟨x, hx⟩)⁻¹ := by
      rw [hact, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
    rw [h1, map_mul, map_inv, hNmact, mul_inv_cancel]
  intro huV
  obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp ((sup_le hUK hcommK) huV)
  have hy' : y = ⟨u, huQ⟩ := Subtype.ext hyu
  rw [hy', MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hy
  exact hubar1 (hNmu ▸ hy)

end CFSG.ProperTwoGeneratedCore.HighRankPair
