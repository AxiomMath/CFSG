module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.HardMathSupport.Solomon.Coordinator.I14_5STr
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def NoLocalTwo (p : ℕ) {R : Type} [Group R] (β : MulAut R) : Prop :=
  ∀ J J₀ : Subgroup R, GLAPComponent p (fixSub β) J → J₀ ≤ J → J₀ ⊔ GLAPPrimeCoreOf p J = J →
    ∀ U : Subgroup R, U ≠ ⊥ → IsPGroup 2 U → ¬ (J₀ ≤ Subgroup.normalizer (U : Set R))

private theorem fixSub_eq_fixSubgroup {R : Type} [Group R] (β : MulAut R) :
    fixSub β = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := by
  ext x
  exact Iff.rfl

theorem mem_fixSub {R : Type} [Group R] {β : MulAut R} {x : R} : x ∈ fixSub β ↔ β x = x := Iff.rfl

theorem fixSub_congr {R R' : Type} [Group R] [Group R'] (e : R ≃* R') (β : MulAut R) :
    fixSub (MulAut.congr e β) = (fixSub β).map e.toMonoidHom := by
  ext y
  rw [mem_fixSub, Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixSub]
    apply e.injective
    have : e (β (e.symm y)) = y := by simpa [MulAut.congr_apply] using hy
    simpa using this
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSub] at hx
    simp [MulAut.congr_apply, hx]

theorem map_le_normalizer_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {A U : Subgroup G}
    (h : A ≤ Subgroup.normalizer (U : Set G)) :
    A.map e.toMonoidHom ≤ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup G') : Set G') := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨a * u * a⁻¹, (Subgroup.mem_normalizer_iff.1 (h ha) u).1 hu, by simp⟩
  · rintro ⟨u, hu, hz⟩
    refine ⟨a⁻¹ * u * a, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (h (A.inv_mem ha)) u).1 hu
      simpa using this
    · show e (a⁻¹ * u * a) = z
      have h2 : e u = e a * z * (e a)⁻¹ := hz
      rw [map_mul, map_mul, map_inv, h2]
      group

theorem noLocalTwo_congr {p : ℕ} (hp : p.Prime) {R R' : Type} [Group R] [Group R'] [Finite R]
    [Finite R'] (e : R ≃* R') {β : MulAut R} (h : NoLocalTwo p β) :
    NoLocalTwo p (MulAut.congr e β) := by
  intro J' J₀' hJ' hJ₀ hcov U' hU hU2 hN
  have hker : ∀ A : Subgroup R', Nat.Coprime p (Nat.card ↥(A ⊓ e.symm.toMonoidHom.ker)) := by
    intro A
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.symm.injective, inf_bot_eq]
    simp
  have hmap : ∀ A : Subgroup R, (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    intro A
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  have hJ : GLAPComponent p (fixSub β) (J'.map e.symm.toMonoidHom) := by
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp e.symm.toMonoidHom (hker _) hJ'
    rwa [fixSub_congr, hmap] at this
  have hcore := CFSG.HardMathSupport.Solomon.Coordinator.i145s_primeCoreOf_map hp
    e.symm.toMonoidHom J' (hker _)
  have hcov' : J₀'.map e.symm.toMonoidHom ⊔ GLAPPrimeCoreOf p (J'.map e.symm.toMonoidHom) =
      J'.map e.symm.toMonoidHom := by
    rw [← hcore, ← Subgroup.map_sup, hcov]
  have hU0 : U'.map e.symm.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hU ((Subgroup.map_eq_bot_iff_of_injective U' e.symm.injective).1 hbot)
  have hU2' : IsPGroup 2 (U'.map e.symm.toMonoidHom) := hU2.map _
  exact h _ _ hJ (Subgroup.map_mono hJ₀) hcov' _ hU0 hU2' (map_le_normalizer_map e.symm hN)

section Induced

variable {H : Type} [Group H]

@[expose] noncomputable def ppAut (p : ℕ) (δ : MulAut H) : MulAut (ppQuot p H) :=
  QuotientGroup.congr (GLAPPrimeCore p H) (GLAPPrimeCore p H) δ (CFSG.pPrimeCore_map_iso p δ)

theorem ppAut_mk (p : ℕ) (δ : MulAut H) (x : H) :
    ppAut p δ (QuotientGroup.mk x) = QuotientGroup.mk (δ x) :=
  QuotientGroup.congr_mk _ _ δ _ x

@[expose] noncomputable def psAut (p : ℕ) (δ : MulAut H) : MulAut (psimpleOf p H) :=
  CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (ppAut p δ)

theorem piOf_apply (p : ℕ) (x : H) :
    piOf p H x = (QuotientGroup.mk' (Subgroup.center (ppQuot p H)))
      ((QuotientGroup.mk' (GLAPPrimeCore p H)) x) := rfl

theorem piOf_surjective (p : ℕ) : Function.Surjective (piOf p H) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem psAut_piOf (p : ℕ) (δ : MulAut H) (x : H) :
    psAut p δ (piOf p H x) = piOf p H (δ x) := by
  rw [piOf_apply, piOf_apply, psAut,
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  simp only [QuotientGroup.mk'_apply]
  rw [ppAut_mk]

theorem psAut_pow_piOf (p : ℕ) (δ : MulAut H) (k : ℕ) (x : H) :
    ((psAut p δ) ^ k) (piOf p H x) = piOf p H ((δ ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, psAut_piOf, pow_succ' δ, MulAut.mul_apply]

theorem psAut_pow_eq_one (p : ℕ) (δ : MulAut H) (hδ : δ ^ p = 1) : (psAut p δ) ^ p = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := piOf_surjective p y
  rw [psAut_pow_piOf, hδ]
  simp

theorem congr_apply_self {R R' : Type} [Group R] [Group R'] (e : R ≃* R') (f : MulAut R) (x : R) :
    MulAut.congr e f (e x) = e (f x) := by
  simp [MulAut.congr_apply]

theorem glaInduces_relOfAut_iff (p : ℕ) (δ : MulAut H) {R : Type} [Group R]
    (θ : psimpleOf p H ≃* R) (φ : MulAut R) :
    GLAInduces θ (relOfAut p δ) φ ↔ φ = MulAut.congr θ (psAut p δ) := by
  constructor
  · intro h
    ext r
    obtain ⟨y, hy⟩ := piOf_surjective p (θ.symm r)
    have hr : θ (piOf p H y) = r := by rw [hy]; simp
    have h1 : φ (θ (piOf p H y)) = θ (piOf p H (δ y)) :=
      h (QuotientGroup.mk y) (QuotientGroup.mk (δ y)) ⟨y, δ y, rfl, rfl, rfl⟩
    rw [← hr, h1, congr_apply_self, psAut_piOf]
  · intro hφ l l' ⟨y, y', hl, hl', hδ⟩
    subst hl hl' hδ
    have h2 : (θ (psAut p δ (piOf p H y))) = θ (piOf p H (δ y)) := by rw [psAut_piOf]
    rw [hφ]
    exact (congr_apply_self θ (psAut p δ) _).trans h2

private theorem inv_mul_apply_mem_of_zpowers {N : Subgroup H} (hN : ∀ g : MulAut H, N.map g.toMonoidHom = N)
    (hNn : N.Normal) {δ : MulAut H} {x : H} (hx : x⁻¹ * δ x ∈ N) :
    ∀ g ∈ Subgroup.zpowers δ, x⁻¹ * g x ∈ N := by
  intro g hg
  have hmapN : ∀ (g : MulAut H) (n : H), n ∈ N → g n ∈ N := by
    intro g n hn
    have : g n ∈ N.map g.toMonoidHom := Subgroup.mem_map_of_mem _ hn
    rwa [hN g] at this
  rw [Subgroup.zpowers_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.1 hy]
    exact hx
  | one => simp
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    have : x⁻¹ * (g₁ * g₂) x = (x⁻¹ * g₁ x) * g₁ (x⁻¹ * g₂ x) := by
      simp [MulAut.mul_apply, map_mul, map_inv, mul_assoc]
    rw [this]
    exact N.mul_mem ih₁ (hmapN g₁ _ ih₂)
  | inv g _ ih =>
    have h1 : g⁻¹ (x⁻¹ * g x) ∈ N := hmapN g⁻¹ _ ih
    have h2 : g⁻¹ (x⁻¹ * g x) = (g⁻¹ x)⁻¹ * x := by
      simp [map_mul, map_inv]
    have h3 : x⁻¹ * g⁻¹ x = ((g⁻¹ x)⁻¹ * x)⁻¹ := by group
    rw [h3]
    exact N.inv_mem (h2 ▸ h1)

theorem map_fixSub_ppQuot [Finite H] {p : ℕ} (hp : p.Prime) (δ : MulAut H) (hδ : δ ^ p = 1) :
    (fixSub δ).map (QuotientGroup.mk' (GLAPPrimeCore p H)) = fixSub (ppAut p δ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : δ x = x := hx
    show ppAut p δ ((QuotientGroup.mk' (GLAPPrimeCore p H)) x) = _
    rw [QuotientGroup.mk'_apply, ppAut_mk, hx']
  · intro hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [mem_fixSub, ppAut_mk] at hy
    have hx : x⁻¹ * δ x ∈ GLAPPrimeCore p H := QuotientGroup.eq.1 hy.symm
    have hN : ∀ g : MulAut H, (GLAPPrimeCore p H).map g.toMonoidHom = GLAPPrimeCore p H :=
      fun g => CFSG.pPrimeCore_map_iso p g
    have hP : IsPGroup p (Subgroup.zpowers δ) := by
      intro g
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      show (g : MulAut H) ^ p ^ 1 = 1
      rw [← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hδ, one_zpow]
    have hall := inv_mul_apply_mem_of_zpowers hN inferInstance hx
    have hmem : ∀ (g : Subgroup.zpowers δ) (n : GLAPPrimeCore p H),
        x⁻¹ * ((g : MulAut H) (x * (n : H))) ∈ GLAPPrimeCore p H := by
      intro g n
      have h1 : x⁻¹ * (g : MulAut H) x ∈ GLAPPrimeCore p H := hall g g.2
      have h2 : (g : MulAut H) (n : H) ∈ GLAPPrimeCore p H := by
        have : (g : MulAut H) (n : H) ∈ (GLAPPrimeCore p H).map (g : MulAut H).toMonoidHom :=
          Subgroup.mem_map_of_mem _ n.2
        rwa [hN] at this
      have : x⁻¹ * ((g : MulAut H) (x * (n : H))) =
          (x⁻¹ * (g : MulAut H) x) * (g : MulAut H) (n : H) := by
        rw [map_mul, ← mul_assoc]
      rw [this]
      exact (GLAPPrimeCore p H).mul_mem h1 h2
    letI act : MulAction (Subgroup.zpowers δ) (GLAPPrimeCore p H) :=
      { smul := fun g n => ⟨x⁻¹ * ((g : MulAut H) (x * (n : H))), hmem g n⟩
        one_smul := fun n => Subtype.ext (show x⁻¹ * ((1 : MulAut H) (x * (n : H))) = (n : H) by
          simp)
        mul_smul := fun g h n => Subtype.ext (show x⁻¹ * (((g * h : Subgroup.zpowers δ) : MulAut H)
            (x * (n : H))) = x⁻¹ * ((g : MulAut H) (x * (x⁻¹ * ((h : MulAut H) (x * (n : H)))))) by
          simp [Subgroup.coe_mul, MulAut.mul_apply]) }
    have hOp : ¬ p ∣ Nat.card (GLAPPrimeCore p H) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    obtain ⟨n, hn⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (GLAPPrimeCore p H) hOp
    have hfix : x⁻¹ * (δ (x * (n : H))) = (n : H) :=
      congrArg Subtype.val (hn ⟨δ, Subgroup.mem_zpowers δ⟩)
    refine ⟨x * (n : H), ?_, ?_⟩
    · show δ (x * (n : H)) = x * (n : H)
      calc δ (x * (n : H)) = x * (x⁻¹ * δ (x * (n : H))) := by group
        _ = x * (n : H) := by rw [hfix]
    · show QuotientGroup.mk (x * (n : H)) = (QuotientGroup.mk x : ppQuot p H)
      rw [QuotientGroup.eq]
      simp

theorem map_primeCoreOf_le_of_map [Finite H] {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q]
    (ψ : H →* Q) (A : Subgroup H) :
    (GLAPPrimeCoreOf p A).map ψ ≤ GLAPPrimeCoreOf p (A.map ψ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (GLAPPrimeCore p ↥A).map (ψ.subgroupMap A) ≤ GLAPPrimeCore p ↥(A.map ψ) := by
    have hf := ψ.subgroupMap_surjective A
    haveI : Finite ↥(A.map ψ) := Finite.of_surjective _ hf
    exact le_sSup ⟨Subgroup.Normal.map inferInstance _ hf,
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) CFSG.pPrimeCore_coprime_card⟩
  unfold GLAPPrimeCoreOf
  have h2 : (A.map ψ).subtype.comp (ψ.subgroupMap A) = ψ.comp A.subtype := by
    ext x
    rfl
  calc ((GLAPPrimeCore p ↥A).map A.subtype).map ψ
      = ((GLAPPrimeCore p ↥A).map (ψ.subgroupMap A)).map (A.map ψ).subtype := by
        rw [Subgroup.map_map, Subgroup.map_map, h2]
    _ ≤ (GLAPPrimeCore p ↥(A.map ψ)).map (A.map ψ).subtype := Subgroup.map_mono h

theorem glaPComponent_map_piOf [Finite H] {p : ℕ} (hp : p.Prime) (δ : MulAut H) (hδ : δ ^ p = 1)
    {I : Subgroup H} (hI : GLAPComponent p (fixSub δ) I) :
    GLAPComponent p (fixSub (psAut p δ)) (I.map (piOf p H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hker : Nat.Coprime p
      (Nat.card ↥(fixSub δ ⊓ (QuotientGroup.mk' (GLAPPrimeCore p H)).ker)) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp
    (QuotientGroup.mk' (GLAPPrimeCore p H)) hker hI
  rw [map_fixSub_ppQuot hp δ hδ, fixSub_eq_fixSubgroup] at h1
  have h2 := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup
    (QuotientGroup.mk' (Subgroup.center (ppQuot p H))) (by rw [QuotientGroup.ker_mk'])
    (ppAut p δ) (psAut p δ)
    (fun k => (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
      (ppAut p δ) k).symm)
    (QuotientGroup.mk'_surjective _) hp h1
  rw [← fixSub_eq_fixSubgroup, Subgroup.map_map] at h2
  exact h2

theorem noParabolicFact_of_noLocalTwo
    (h : ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (δ : MulAut H), p.Prime → p ≠ 2 → δ ^ p = 1 →
      commutator (ppQuot p H) = ⊤ → IsChevSimple 2 (psimpleOf p H) → FieldAutOn p H δ →
      NoLocalTwo p (psAut p δ)) :
    I2015NoParabolicFact := by
  intro H _ _ p δ I I₀ hp hp2 hδ hperf hchev hfield hI hI0 hcov U hU hU2 hN
  have hNL := h H p δ hp hp2 hδ hperf hchev hfield
  have hJ := glaPComponent_map_piOf hp δ hδ hI
  have hcov' : I₀.map (piOf p H) ⊔ GLAPPrimeCoreOf p (I.map (piOf p H)) = I.map (piOf p H) := by
    apply le_antisymm
    · exact sup_le (Subgroup.map_mono hI0) (Subgroup.map_subtype_le _)
    · calc I.map (piOf p H) = (I₀ ⊔ GLAPPrimeCoreOf p I).map (piOf p H) := by rw [hcov]
        _ = I₀.map (piOf p H) ⊔ (GLAPPrimeCoreOf p I).map (piOf p H) := Subgroup.map_sup _ _ _
        _ ≤ _ := sup_le_sup_left (map_primeCoreOf_le_of_map hp (piOf p H) I) _
  exact hNL _ _ hJ (Subgroup.map_mono hI0) hcov' U hU hU2 hN

end Induced

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
