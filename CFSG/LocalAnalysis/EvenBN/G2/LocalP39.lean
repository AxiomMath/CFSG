module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalP35B
public import CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

public import CFSG.LocalAnalysis.EvenBN.G2.LocalPDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace ModCoset

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo conj_mem_oTwo)

variable {G : Type*} [Group G]

theorem proj_comm_of_commutator_mem {Z : Subgroup G} {x y : normalizer (Z : Set G)}
    (hxy : ⁅(x : G), (y : G)⁆ ∈ Z) : proj Z x * proj Z y = proj Z y * proj Z x := by
  have h1 : proj Z ⁅x, y⁆ = 1 := proj_eq_one_iff.2 (by simpa [commutatorElement_def] using hxy)
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem commutator_mem_of_proj_comm {Z : Subgroup G} {x y : normalizer (Z : Set G)}
    (h : proj Z x * proj Z y = proj Z y * proj Z x) : ⁅(x : G), (y : G)⁆ ∈ Z := by
  have h1 : proj Z ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 h
  simpa [commutatorElement_def] using proj_eq_one_iff.1 h1

theorem exists_proj_of_mem_bar {Z X : Subgroup G} {x : Bar Z} (hx : x ∈ bar Z X) :
    ∃ y : normalizer (Z : Set G), (y : G) ∈ X ∧ proj Z y = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, mem_subgroupOf.1 hy, rfl⟩

theorem proj_conj_normalizer {Z : Subgroup G} {c x : G} (hc : c ∈ normalizer (Z : Set G))
    (hx : x ∈ normalizer (Z : Set G)) :
    proj Z ⟨c * x * c⁻¹, mul_mem (mul_mem hc hx) (inv_mem hc)⟩ =
      proj Z ⟨c, hc⟩ * proj Z ⟨x, hx⟩ * (proj Z ⟨c, hc⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem mul_comm_of_forall_mul_self_eq_one {Y : Subgroup G} (h : ∀ x ∈ Y, x * x = 1) {a b : G}
    (ha : a ∈ Y) (hb : b ∈ Y) : a * b = b * a := by
  have hab := h (a * b) (mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b hb)
  have : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, ha', hb'] at this
  exact this.symm

theorem cosetData_bar [Finite G] {Z H Mt : Subgroup G} {t : G}
    (hHN : H ≤ normalizer (Z : Set G)) (hZM : Z ≤ Mt) (hMN : Mt ≤ normalizer (Z : Set G))
    (hHM : H ≤ normalizer (Mt : Set G)) (htN : t ∈ normalizer (Z : Set G)) (ht2 : t * t = 1)
    (hMsq : ∀ x ∈ Mt, x * x ∈ Z) (htc : ∀ y ∈ Mt, ⁅y, t⁆ ∈ Z)
    (hcr : ∀ h ∈ H, h⁻¹ * t * h * t ∈ Mt) :
    CosetData (bar Z H) (bar Z Mt) (proj Z ⟨t, htN⟩) where
  mul_self := by
    rw [← map_mul, proj_eq_one_iff]
    show t * t ∈ Z
    rw [ht2]
    exact one_mem _
  le_centralizer := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_centralizer_singleton_iff.2
      (proj_comm_of_commutator_mem (x := y) (y := ⟨t, htN⟩) (htc _ (mem_subgroupOf.1 hy)))
  isElementaryAbelian := by
    have hsq : ∀ x ∈ bar Z Mt, x * x = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, proj_eq_one_iff]
      exact hMsq _ (mem_subgroupOf.1 hy)
    exact CFSG.IsElementaryAbelian.two_of_forall_mul_self
      (fun a ha b hb => mul_comm_of_forall_mul_self_eq_one hsq ha hb) hsq
  le_normalizer := bar_le_normalizer_bar hZM hHM
  crossed_mem := by
    rintro _ ⟨n, hn, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact proj_mem_bar (hcr _ (mem_subgroupOf.1 hn))

structure NatModData (Z Mt : Subgroup G) {K : Type*} [Field K] (ψ : (Fin 2 → K) → G)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G) : Prop where
  mem : ∀ v, ψ v ∈ Mt
  eq_zero : ∀ v, ψ v ∈ Z → v = 0
  surj : ∀ x ∈ Mt, ∃ v, (ψ v)⁻¹ * x ∈ Z
  add : ∀ v w, (ψ v * ψ w)⁻¹ * ψ (v + w) ∈ Z
  conj : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
    (ψ (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v))⁻¹ * (ρ g * ψ v * (ρ g)⁻¹) ∈ Z

theorem exists_iota {Z Mt : Subgroup G} {K : Type*} [Field K] {ψ : (Fin 2 → K) → G}
    {ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G} (hN : NatModData Z Mt ψ ρ)
    (hMN : Mt ≤ normalizer (Z : Set G)) :
    ∃ ι : Multiplicative (Fin 2 → K) ≃* ↥(bar Z Mt), ∀ v : Fin 2 → K,
      ((ι (Multiplicative.ofAdd v) : ↥(bar Z Mt)) : Bar Z) = proj Z ⟨ψ v, hMN (hN.mem v)⟩ := by
  have hψ0 : ψ 0 ∈ Z := by
    have h0 := hN.add 0 0
    rw [add_zero] at h0
    have h1 : ((ψ 0 * ψ 0)⁻¹ * ψ 0)⁻¹ ∈ Z := inv_mem h0
    rwa [show ((ψ 0 * ψ 0)⁻¹ * ψ 0)⁻¹ = ψ 0 by group] at h1
  let ι₀ : Multiplicative (Fin 2 → K) →* Bar Z :=
    { toFun := fun m => proj Z ⟨ψ (Multiplicative.toAdd m), hMN (hN.mem _)⟩
      map_one' := by
        rw [toAdd_one]
        exact proj_eq_one_iff.2 hψ0
      map_mul' := fun a b => by
        rw [← map_mul]
        refine proj_eq_proj_iff.2 ?_
        have h1 := inv_mem (hN.add (Multiplicative.toAdd a) (Multiplicative.toAdd b))
        rw [toAdd_mul]
        change (ψ (Multiplicative.toAdd a + Multiplicative.toAdd b))⁻¹ *
          (ψ (Multiplicative.toAdd a) * ψ (Multiplicative.toAdd b)) ∈ Z
        rwa [show ((ψ (Multiplicative.toAdd a) * ψ (Multiplicative.toAdd b))⁻¹ *
          ψ (Multiplicative.toAdd a + Multiplicative.toAdd b))⁻¹ =
          (ψ (Multiplicative.toAdd a + Multiplicative.toAdd b))⁻¹ *
            (ψ (Multiplicative.toAdd a) * ψ (Multiplicative.toAdd b)) by group] at h1 }
  have hinj : Function.Injective ι₀ := by
    refine (injective_iff_map_eq_one _).2 fun m hm => ?_
    have h1 : ψ (Multiplicative.toAdd m) ∈ Z := proj_eq_one_iff.1 hm
    exact toAdd_eq_zero.1 (hN.eq_zero _ h1)
  have hrange : ι₀.range = bar Z Mt := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact proj_mem_bar (hN.mem _)
    · intro hy
      obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := exists_proj_of_mem_bar hy
      obtain ⟨v, hv⟩ := hN.surj x hx
      exact ⟨Multiplicative.ofAdd v, proj_eq_proj_iff.2 hv⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun v => rfl⟩

theorem two_core_mod [Finite G] {Z H Mt B : Subgroup G} {t : G} {K : Type*} [Field K] [Fintype K]
    [CharP K 2] {ψ : (Fin 2 → K) → G} {ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G}
    (hZ2 : IsPGroup 2 Z) (hZH : Z ≤ H) (hHN : H ≤ normalizer (Z : Set G))
    (hZM : Z ≤ Mt) (hMN : Mt ≤ normalizer (Z : Set G)) (hHM : H ≤ normalizer (Mt : Set G))
    (htN : t ∈ normalizer (Z : Set G)) (ht2 : t * t = 1)
    (hMsq : ∀ x ∈ Mt, x * x ∈ Z) (htc : ∀ y ∈ Mt, ⁅y, t⁆ ∈ Z)
    (hcr : ∀ h ∈ H, h⁻¹ * t * h * t ∈ Mt)
    (hN : NatModData Z Mt ψ ρ) (hρH : ∀ g, ρ g ∈ H) (hρt : ∀ g, ρ g * t = t * ρ g)
    (hpt : ∃ f₀ ∈ Mt, f₀ ∉ Z ∧ ∃ g₀ ∈ H, (t * f₀)⁻¹ * (g₀⁻¹ * t * g₀) ∈ Z)
    (hAn : ∀ x ∈ H, ⁅x, t⁆ ∈ Z → ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      ∃ g' : Matrix.SpecialLinearGroup (Fin 2) K, ∃ b ∈ B, x * ρ g * x⁻¹ = b * ρ g')
    (hBZ : Z ≤ B) (hBH : B ≤ H) (hB2 : IsPGroup 2 B)
    (hBc : ∀ b ∈ B, ⁅b, t⁆ ∈ Z) (hBM : ∀ b ∈ B, ∀ y ∈ Mt, ⁅b, y⁆ ∈ Z)
    (hKB : ∀ k ∈ H, ⁅k, t⁆ ∈ Z → (∀ y ∈ Mt, ⁅k, y⁆ ∈ Z) → k ∈ B)
    (hBmax : ∀ R : Subgroup G, Z ≤ R → (∀ x ∈ R, x ∈ H ∧ ⁅x, t⁆ ∈ Z) →
      (∀ c ∈ H, ⁅c, t⁆ ∈ Z → ∀ x ∈ R, c * x * c⁻¹ ∈ R) → IsPGroup 2 R → R ≤ B) :
    ∃ P : Subgroup G, Z ≤ P ∧ P ≤ H ∧ IsPGroup 2 P ∧ H ≤ normalizer (P : Set G) ∧ B ≤ P ∧
      H ≤ normalizer (B : Set G) ∧ (∀ x ∈ P, ∀ y ∈ Mt, ⁅x, y⁆ ∈ Z) ∧
      (∀ x ∈ P, ⁅x, t⁆ ∈ Z → x ∈ B) ∧
      (∀ y ∈ Mt, ∃ x ∈ P, (t * y)⁻¹ * (x⁻¹ * t * x) ∈ Z) ∧
      (∀ g ∈ H, ∃ c ∈ H, ⁅c, t⁆ ∈ Z ∧ ∃ x ∈ P, g = c * x) ∧
      (∀ Q : Subgroup G, Q ≤ H → H ≤ normalizer (Q : Set G) → IsPGroup 2 Q → Q ≤ P) := by
  classical
  have hMH : ∀ y : G, y ∈ Mt → y ∈ normalizer (Z : Set G) := fun y hy => hMN hy
  set tb : Bar Z := proj Z ⟨t, htN⟩ with htb
  have hc := cosetData_bar hHN hZM hMN hHM htN ht2 hMsq htc hcr
  obtain ⟨ι, hι⟩ := exists_iota hN hMN
  have hρN : ∀ g, ρ g ∈ normalizer (Z : Set G) := fun g => hHN (hρH g)
  have hρc : ∀ g, ⁅ρ g, t⁆ ∈ Z := fun g => by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hρt g)]
    exact one_mem _
  set A : Subgroup (Bar Z) := bar Z ρ.range with hA
  have hAH : A ≤ bar Z H := bar_mono (by rintro _ ⟨g, rfl⟩; exact hρH g)
  have hAC : A ≤ bar Z H ⊓ centralizer ({tb} : Set (Bar Z)) := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨hAH hg, ?_⟩
    obtain ⟨y, ⟨M₀, hM₀⟩, rfl⟩ := exists_proj_of_mem_bar hg
    refine mem_centralizer_singleton_iff.2 (proj_comm_of_commutator_mem (x := y) (y := ⟨t, htN⟩) ?_)
    rw [← hM₀]
    exact hρc M₀
  have hconj : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      proj Z ⟨ρ M, hρN M⟩ * proj Z ⟨ψ v, hMN (hN.mem v)⟩ * (proj Z ⟨ρ M, hρN M⟩)⁻¹ =
        proj Z ⟨ψ (Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) v), hMN (hN.mem _)⟩ := by
    intro M v
    rw [← map_inv, ← map_mul, ← map_mul]
    refine proj_eq_proj_iff.2 ?_
    have h1 := inv_mem (hN.conj M v)
    rw [show ((ψ (Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) v))⁻¹ *
      (ρ M * ψ v * (ρ M)⁻¹))⁻¹ = (ρ M * ψ v * (ρ M)⁻¹)⁻¹ *
        ψ (Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) v) by group] at h1
    exact h1
  have hnat : ∀ g ∈ A, ∃ M : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v : Fin 2 → K,
      g * ((ι (Multiplicative.ofAdd v) : ↥(bar Z Mt)) : Bar Z) * g⁻¹ =
        ((ι (Multiplicative.ofAdd (Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) v)) :
          ↥(bar Z Mt)) : Bar Z) := by
    intro g hg
    obtain ⟨y, ⟨M₀, hM₀⟩, rfl⟩ := exists_proj_of_mem_bar hg
    refine ⟨M₀, fun v => ?_⟩
    rw [hι, hι]
    have : y = ⟨ρ M₀, hρN M₀⟩ := Subtype.ext hM₀.symm
    subst this
    exact hconj M₀ v
  have hsurj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) K, ∃ g ∈ A, ∀ v : Fin 2 → K,
      g * ((ι (Multiplicative.ofAdd v) : ↥(bar Z Mt)) : Bar Z) * g⁻¹ =
        ((ι (Multiplicative.ofAdd (Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) v)) :
          ↥(bar Z Mt)) : Bar Z) := fun M =>
    ⟨proj Z ⟨ρ M, hρN M⟩, proj_mem_bar ⟨M, rfl⟩, fun v => by rw [hι, hι]; exact hconj M v⟩
  have hψ0 : ψ 0 ∈ Z := by
    have h0 := hN.add 0 0
    rw [add_zero] at h0
    have h1 : ((ψ 0 * ψ 0)⁻¹ * ψ 0)⁻¹ ∈ Z := inv_mem h0
    rwa [show ((ψ 0 * ψ 0)⁻¹ * ψ 0)⁻¹ = ψ 0 by group] at h1
  have htr' : ∀ y ∈ bar Z Mt, ∃ g ∈ bar Z H, g⁻¹ * tb * g = tb * y := by
    obtain ⟨f₀, hf₀M, hf₀Z, g₀, hg₀H, hg₀⟩ := hpt
    have hg₀b : (proj Z ⟨g₀, hHN hg₀H⟩)⁻¹ * tb * proj Z ⟨g₀, hHN hg₀H⟩ =
        tb * proj Z ⟨f₀, hMN hf₀M⟩ := by
      rw [htb]
      simp only [← map_mul, ← map_inv]
      refine proj_eq_proj_iff.2 ?_
      have h1 := inv_mem hg₀
      rw [show ((t * f₀)⁻¹ * (g₀⁻¹ * t * g₀))⁻¹ = (g₀⁻¹ * t * g₀)⁻¹ * (t * f₀) by group] at h1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    obtain ⟨u, hu⟩ := hN.surj f₀ hf₀M
    have hu0 : u ≠ 0 := by
      rintro rfl
      apply hf₀Z
      have := mul_mem hψ0 hu
      rwa [mul_inv_cancel_left] at this
    have hpf₀ : proj Z ⟨f₀, hMN hf₀M⟩ =
        ((ι (Multiplicative.ofAdd u) : ↥(bar Z Mt)) : Bar Z) := by
      rw [hι]
      exact (proj_eq_proj_iff.2 hu).symm
    intro y hy
    obtain ⟨m, hm⟩ := ι.surjective ⟨y, hy⟩
    set v : Fin 2 → K := Multiplicative.toAdd m with hv
    have hmv : m = Multiplicative.ofAdd v := rfl
    have hyv : y = ((ι (Multiplicative.ofAdd v) : ↥(bar Z Mt)) : Bar Z) := by
      rw [← hmv, hm]
    by_cases hv0 : v = 0
    · refine ⟨1, one_mem _, ?_⟩
      have hy1 : y = 1 := by
        rw [hyv, hι, hv0]
        exact proj_eq_one_iff.2 hψ0
      rw [hy1]
      group
    · obtain ⟨M, hM⟩ := CFSG.LocalAnalysis.EvenBN.LinearThree.Plane.exists_sl_smul hu0 hv0
      set a : Bar Z := proj Z ⟨ρ M, hρN M⟩ with ha
      have haA : a ∈ A := proj_mem_bar ⟨M, rfl⟩
      have hac : a * tb = tb * a :=
        mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hAC haA)).2
      have h1 : a * ((ι (Multiplicative.ofAdd u) : ↥(bar Z Mt)) : Bar Z) * a⁻¹ =
          ((ι (Multiplicative.ofAdd v) : ↥(bar Z Mt)) : Bar Z) := by
        rw [hι, hι, ha, hconj M u,
          show Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) u = v from hM]
      refine ⟨proj Z ⟨g₀, hHN hg₀H⟩ * a⁻¹,
        mul_mem (proj_mem_bar hg₀H) (inv_mem (hAH haA)), ?_⟩
      calc (proj Z ⟨g₀, hHN hg₀H⟩ * a⁻¹)⁻¹ * tb * (proj Z ⟨g₀, hHN hg₀H⟩ * a⁻¹) =
          a * ((proj Z ⟨g₀, hHN hg₀H⟩)⁻¹ * tb * proj Z ⟨g₀, hHN hg₀H⟩) * a⁻¹ := by group
        _ = a * (tb * ((ι (Multiplicative.ofAdd u) : ↥(bar Z Mt)) : Bar Z)) * a⁻¹ := by
          rw [hg₀b, hpf₀]
        _ = (a * tb * a⁻¹) * (a * ((ι (Multiplicative.ofAdd u) : ↥(bar Z Mt)) : Bar Z) * a⁻¹) := by
          group
        _ = tb * y := by rw [hac, mul_inv_cancel_right, h1, ← hyv]
  have hAn' : ∀ x ∈ bar Z H ⊓ centralizer ({tb} : Set (Bar Z)), ∀ g ∈ A, ∃ g' ∈ A,
      ∀ w ∈ bar Z Mt, x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ = g' * w * g'⁻¹ := by
    intro x hx g hg
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨x₀, hx₀H, rfl⟩ := exists_proj_of_mem_bar hxH
    have hxt : ⁅(x₀ : G), t⁆ ∈ Z := commutator_mem_of_proj_comm (x := x₀) (y := ⟨t, htN⟩)
      (mem_centralizer_singleton_iff.1 hxC)
    obtain ⟨y, ⟨M₀, hM₀⟩, rfl⟩ := exists_proj_of_mem_bar hg
    obtain ⟨M', b, hbB, hxb⟩ := hAn (x₀ : G) hx₀H hxt M₀
    have hbN : b ∈ normalizer (Z : Set G) := hHN (hBH hbB)
    have ha'A : proj Z ⟨ρ M', hρN M'⟩ ∈ A := proj_mem_bar ⟨M', rfl⟩
    refine ⟨proj Z ⟨ρ M', hρN M'⟩, ha'A, fun w hw => ?_⟩
    have e : proj Z x₀ * proj Z y * (proj Z x₀)⁻¹ = proj Z ⟨b, hbN⟩ * proj Z ⟨ρ M', hρN M'⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      refine congrArg (proj Z) (Subtype.ext ?_)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hM₀]
      exact hxb
    have hpbc : ∀ z ∈ bar Z Mt, proj Z ⟨b, hbN⟩ * z = z * proj Z ⟨b, hbN⟩ := fun z hz => by
      obtain ⟨z₀, hz₀, rfl⟩ := exists_proj_of_mem_bar hz
      exact (proj_comm_of_commutator_mem (x := z₀) (y := ⟨b, hbN⟩) (by
        have h1 := inv_mem (hBM b hbB _ hz₀)
        rwa [commutatorElement_inv] at h1)).symm
    have haw : proj Z ⟨ρ M', hρN M'⟩ * w * (proj Z ⟨ρ M', hρN M'⟩)⁻¹ ∈ bar Z Mt :=
      (mem_normalizer_iff.1 (hc.le_normalizer (hAH ha'A)) w).1 hw
    rw [e]
    have := hpbc _ haw
    calc proj Z ⟨b, hbN⟩ * proj Z ⟨ρ M', hρN M'⟩ * w *
          (proj Z ⟨b, hbN⟩ * proj Z ⟨ρ M', hρN M'⟩)⁻¹ =
        proj Z ⟨b, hbN⟩ * (proj Z ⟨ρ M', hρN M'⟩ * w * (proj Z ⟨ρ M', hρN M'⟩)⁻¹) *
          (proj Z ⟨b, hbN⟩)⁻¹ := by group
      _ = proj Z ⟨ρ M', hρN M'⟩ * w * (proj Z ⟨ρ M', hρN M'⟩)⁻¹ := by
        rw [this]; group
  set Bb : Subgroup (Bar Z) := bar Z B with hBb
  have hB2' : IsPGroup 2 Bb := isPGroup_bar hB2
  have hBbH : Bb ≤ bar Z H := bar_mono hBH
  have hKBb : bar Z H ⊓ centralizer ((bar Z Mt : Subgroup (Bar Z)) : Set (Bar Z)) ⊓
      centralizer ({tb} : Set (Bar Z)) ≤ Bb := by
    intro k hk
    obtain ⟨⟨hkH, hkY⟩, hkt⟩ := hk
    obtain ⟨k₀, hk₀H, rfl⟩ := exists_proj_of_mem_bar hkH
    have hkt' : ⁅(k₀ : G), t⁆ ∈ Z := commutator_mem_of_proj_comm (x := k₀) (y := ⟨t, htN⟩)
      (mem_centralizer_singleton_iff.1 hkt)
    have hky : ∀ y ∈ Mt, ⁅(k₀ : G), y⁆ ∈ Z := by
      intro y hy
      have h1 := mem_centralizer_iff.1 hkY (proj Z ⟨y, hMN hy⟩) (proj_mem_bar hy)
      have h2 : ⁅y, (k₀ : G)⁆ ∈ Z := commutator_mem_of_proj_comm (x := ⟨y, hMN hy⟩) (y := k₀) h1
      have h3 := inv_mem h2
      rwa [commutatorElement_inv] at h3
    exact proj_mem_bar (hKB _ hk₀H hkt' hky)
  have hBK : Bb ≤ bar Z H ⊓ centralizer ((bar Z Mt : Subgroup (Bar Z)) : Set (Bar Z)) ⊓
      centralizer ({tb} : Set (Bar Z)) := by
    intro b hb
    obtain ⟨b₀, hb₀B, rfl⟩ := exists_proj_of_mem_bar hb
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hBbH hb, mem_centralizer_iff.2 fun y hy => ?_⟩,
      mem_centralizer_singleton_iff.2
        (proj_comm_of_commutator_mem (x := b₀) (y := ⟨t, htN⟩) (hBc _ hb₀B))⟩
    obtain ⟨y₀, hy₀, rfl⟩ := exists_proj_of_mem_bar hy
    exact (proj_comm_of_commutator_mem (x := b₀) (y := y₀) (hBM _ hb₀B _ hy₀)).symm
  have hBn : bar Z H ≤ normalizer (Bb : Set (Bar Z)) := by
    intro g hg
    refine mem_normalizer_fintype fun x hx => ?_
    exact hKBb (hc.conj_mem_kernel hg (hBK hx))
  have hBmax' : ∀ R : Subgroup (Bar Z), R ≤ bar Z H ⊓ centralizer ({tb} : Set (Bar Z)) →
      bar Z H ⊓ centralizer ({tb} : Set (Bar Z)) ≤ normalizer (R : Set (Bar Z)) →
        IsPGroup 2 R → R ≤ Bb := by
    intro R hR hRn hR2
    have hRlift : lift R ≤ B := by
      refine hBmax (lift R) (le_lift R) (fun x hx => ?_) (fun c hc hct x hx => ?_)
        (isPGroup_lift hZ2 hR2)
      · obtain ⟨hxN, hxR⟩ := mem_lift_iff.1 hx
        obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 (hR hxR)
        exact ⟨(mem_bar_iff hZH ⟨x, hxN⟩).1 hxH, commutator_mem_of_proj_comm (x := ⟨x, hxN⟩)
          (y := ⟨t, htN⟩) (mem_centralizer_singleton_iff.1 hxC)⟩
      · obtain ⟨hxN, hxR⟩ := mem_lift_iff.1 hx
        have hcb : proj Z ⟨c, hHN hc⟩ ∈ bar Z H ⊓ centralizer ({tb} : Set (Bar Z)) :=
          Subgroup.mem_inf.2 ⟨proj_mem_bar hc, mem_centralizer_singleton_iff.2
            (proj_comm_of_commutator_mem (x := ⟨c, hHN hc⟩) (y := ⟨t, htN⟩) hct)⟩
        have h1 := (mem_normalizer_iff.1 (hRn hcb) _).1 hxR
        exact mem_lift_iff.2 ⟨mul_mem (mul_mem (hHN hc) hxN) (inv_mem (hHN hc)), by
          rw [proj_conj_normalizer (hHN hc) hxN]; exact h1⟩
    intro r hr
    obtain ⟨r₀, rfl⟩ := proj_surjective r
    exact proj_mem_bar (hRlift (mem_lift_iff.2 ⟨r₀.2, hr⟩))
  have hAK : ∀ a ∈ A, ∀ k ∈ bar Z H ⊓ centralizer ((bar Z Mt : Subgroup (Bar Z)) : Set (Bar Z)) ⊓
      centralizer ({tb} : Set (Bar Z)), a * k * a⁻¹ * k⁻¹ ∈ Bb := fun a ha k hk =>
    mul_mem ((mem_normalizer_iff.1 (hBn (hAH ha)) k).1 (hKBb hk)) (inv_mem (hKBb hk))
  obtain ⟨o1, o2, o3, o4⟩ := hc.sl_two_core ι htr' (A := A) hAC hnat hsurj hAn' hB2' hBK hBn
    hBmax' hAK
  set P : Subgroup G := lift (oTwo (bar Z H)) with hP
  have hZP : Z ≤ P := le_lift _
  have hPH : P ≤ H := fun x hx => by
    obtain ⟨hxN, hxo⟩ := mem_lift_iff.1 hx
    exact (mem_bar_iff hZH ⟨x, hxN⟩).1 (oTwo_le _ hxo)
  have hP2 : IsPGroup 2 P := isPGroup_lift hZ2 (isPGroup_oTwo _)
  have hHP : H ≤ normalizer (P : Set G) := fun g hg => by
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxN, hxo⟩ := mem_lift_iff.1 hx
    refine mem_lift_iff.2 ⟨mul_mem (mul_mem (hHN hg) hxN) (inv_mem (hHN hg)), ?_⟩
    rw [proj_conj_normalizer (hHN hg) hxN]
    exact conj_mem_oTwo (proj_mem_bar hg) hxo
  refine ⟨P, hZP, hPH, hP2, hHP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hbN : b ∈ normalizer (Z : Set G) := hHN (hBH hb)
    refine mem_lift_iff.2 ⟨hbN, ?_⟩
    have : proj Z ⟨b, hbN⟩ ∈ oTwo (bar Z H) ⊓ centralizer ({tb} : Set (Bar Z)) := by
      rw [o2]
      exact proj_mem_bar hb
    exact this.1
  · intro g hg
    refine mem_normalizer_fintype fun x hx => ?_
    have hxN : x ∈ normalizer (Z : Set G) := hHN (hBH hx)
    have h1 : proj Z ⟨g * x * g⁻¹, mul_mem (mul_mem (hHN hg) hxN) (inv_mem (hHN hg))⟩ ∈ Bb := by
      rw [proj_conj_normalizer (hHN hg) hxN]
      exact (mem_normalizer_iff.1 (hBn (proj_mem_bar hg)) _).1 (proj_mem_bar hx)
    exact (mem_bar_iff hBZ _).1 h1
  · intro x hx y hy
    obtain ⟨hxN, hxo⟩ := mem_lift_iff.1 hx
    have h1 := mem_centralizer_iff.1 (o1 hxo) (proj Z ⟨y, hMN hy⟩) (proj_mem_bar hy)
    have h2 : ⁅y, x⁆ ∈ Z := commutator_mem_of_proj_comm (x := ⟨y, hMN hy⟩) (y := ⟨x, hxN⟩) h1
    have h3 := inv_mem h2
    rwa [commutatorElement_inv] at h3
  · intro x hx hxt
    obtain ⟨hxN, hxo⟩ := mem_lift_iff.1 hx
    have : proj Z ⟨x, hxN⟩ ∈ oTwo (bar Z H) ⊓ centralizer ({tb} : Set (Bar Z)) :=
      Subgroup.mem_inf.2 ⟨hxo, mem_centralizer_singleton_iff.2
        (proj_comm_of_commutator_mem (x := ⟨x, hxN⟩) (y := ⟨t, htN⟩) hxt)⟩
    rw [o2] at this
    exact (mem_bar_iff hBZ _).1 this
  · intro y hy
    obtain ⟨d, hd, hdy⟩ := o3 (proj Z ⟨y, hMN hy⟩) (proj_mem_bar hy)
    obtain ⟨x, rfl⟩ := proj_surjective d
    refine ⟨x, mem_lift_iff.2 ⟨x.2, hd⟩, ?_⟩
    simp only [← map_mul, ← map_inv] at hdy
    have h1 := proj_eq_proj_iff.1 hdy.symm
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  · intro g hg
    obtain ⟨c, hc', d, hd, hgcd⟩ := o4 (proj Z ⟨g, hHN hg⟩) (proj_mem_bar hg)
    obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.1 hc'
    obtain ⟨c₀, hc₀H, rfl⟩ := exists_proj_of_mem_bar hcH
    obtain ⟨x, rfl⟩ := proj_surjective d
    have hxP : (x : G) ∈ P := mem_lift_iff.2 ⟨x.2, hd⟩
    have hct : ⁅(c₀ : G), t⁆ ∈ Z := commutator_mem_of_proj_comm (x := c₀) (y := ⟨t, htN⟩)
      (mem_centralizer_singleton_iff.1 hcC)
    rw [← map_mul] at hgcd
    have hz := proj_eq_proj_iff.1 hgcd
    simp only [Subgroup.coe_mul] at hz
    exact ⟨c₀, hc₀H, hct, (x : G) * ((g : G)⁻¹ * ((c₀ : G) * (x : G)))⁻¹,
      mul_mem hxP (hZP (inv_mem hz)), by group⟩
  · intro Q hQH hHQ hQ2
    have hQ'H : bar Z Q ≤ bar Z H := bar_mono hQH
    have hQ'n : bar Z H ≤ normalizer ((bar Z Q : Subgroup (Bar Z)) : Set (Bar Z)) := by
      intro g hg
      obtain ⟨g₀, hg₀H, rfl⟩ := exists_proj_of_mem_bar hg
      refine mem_normalizer_fintype fun x hx => ?_
      obtain ⟨x₀, hx₀Q, rfl⟩ := exists_proj_of_mem_bar hx
      rw [← map_inv, ← map_mul, ← map_mul]
      exact proj_mem_bar ((mem_normalizer_iff.1 (hHQ hg₀H) _).1 hx₀Q)
    have h1 := le_oTwo hQ'H hQ'n (isPGroup_bar hQ2)
    intro q hq
    exact mem_lift_iff.2 ⟨hHN (hQH hq), h1 (proj_mem_bar hq)⟩

theorem commutator_mem_of_mul_self_mem {Z X : Subgroup G} (hXN : X ≤ normalizer (Z : Set G))
    (hsq : ∀ x ∈ X, x * x ∈ Z) {a b : G} (ha : a ∈ X) (hb : b ∈ X) : ⁅a, b⁆ ∈ Z := by
  have hsq' : ∀ x ∈ bar Z X, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, proj_eq_one_iff]
    exact hsq _ (mem_subgroupOf.1 hy)
  exact commutator_mem_of_proj_comm (x := ⟨a, hXN ha⟩) (y := ⟨b, hXN hb⟩)
    (mul_comm_of_forall_mul_self_eq_one hsq' (proj_mem_bar ha) (proj_mem_bar hb))

theorem commutator_mul_mem_mod {Z : Subgroup G} {a b y : G} (ha : a ∈ normalizer (Z : Set G))
    (hb : b ∈ normalizer (Z : Set G)) (hy : y ∈ normalizer (Z : Set G)) (h1 : ⁅a, y⁆ ∈ Z)
    (h2 : ⁅b, y⁆ ∈ Z) : ⁅a * b, y⁆ ∈ Z := by
  have c1 := proj_comm_of_commutator_mem (x := ⟨a, ha⟩) (y := ⟨y, hy⟩) h1
  have c2 := proj_comm_of_commutator_mem (x := ⟨b, hb⟩) (y := ⟨y, hy⟩) h2
  refine commutator_mem_of_proj_comm (x := ⟨a * b, mul_mem ha hb⟩) (y := ⟨y, hy⟩) ?_
  change proj Z (⟨a, ha⟩ * ⟨b, hb⟩) * proj Z ⟨y, hy⟩ = proj Z ⟨y, hy⟩ * proj Z (⟨a, ha⟩ * ⟨b, hb⟩)
  rw [map_mul]
  exact (Commute.mul_left (c1 : Commute _ _) (c2 : Commute _ _)).eq

theorem commutator_inv_mem_mod {Z : Subgroup G} {a y : G} (ha : a ∈ normalizer (Z : Set G))
    (hy : y ∈ normalizer (Z : Set G)) (h1 : ⁅a, y⁆ ∈ Z) : ⁅a⁻¹, y⁆ ∈ Z := by
  have c1 := proj_comm_of_commutator_mem (x := ⟨a, ha⟩) (y := ⟨y, hy⟩) h1
  refine commutator_mem_of_proj_comm (x := ⟨a⁻¹, inv_mem ha⟩) (y := ⟨y, hy⟩) ?_
  change proj Z (⟨a, ha⟩⁻¹) * proj Z ⟨y, hy⟩ = proj Z ⟨y, hy⟩ * proj Z (⟨a, ha⟩⁻¹)
  rw [map_inv]
  exact (Commute.inv_left (c1 : Commute _ _)).eq

end ModCoset

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

open ModCoset

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem W_le_M (d : G2Data L K) : d.W ≤ d.M := by
  obtain ⟨-, -, -, -, hWF, -, hFM, -⟩ := d.inclusions
  exact hWF.trans hFM

theorem yamadaW₂_le_yamadaM₂ (d : G2Data L K) (t : G) : yamadaW₂ d t ≤ yamadaM₂ d t :=
  sup_le_sup_right (W_le_M d) _

theorem M_le_normalizer_W (d : G2Data L K) : d.M ≤ normalizer (d.W : Set G) := fun m hm => by
  have : m ∈ L ⊓ normalizer (d.W : Set G) := by
    rw [(d.yamada_3_13_3_G).2.1]
    exact mem_sup_left hm
  exact (Subgroup.mem_inf.1 this).2

theorem yamadaM₂_le_normalizer_yamadaW₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaM₂ d t ≤ normalizer (yamadaW₂ d t : Set G) := by
  have hMW := M_le_normalizer_W (d := d)
  have hMY : d.M ≤ normalizer (yamadaY₂ d t : Set G) := fun m hm =>
    Subgroup.centralizer_le_normalizer _ (h.M_le_centralizer_yamadaY₂ d hK hD hm)
  have hYW : yamadaY₂ d t ≤ normalizer (yamadaW₂ d t : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _
      (h.yamadaW₂_le_centralizer d hK hD ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hy))
  exact sup_le (fun m hm => Common.mem_normalizer_sup (hMW hm) (hMY hm)) hYW

theorem M_inf_yamadaW₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.M ⊓ yamadaW₂ d t = d.W := by
  obtain ⟨-, -, hYW, -⟩ := d.inclusions
  refine le_antisymm (fun x hx => ?_) (le_inf (W_le_M d) le_sup_left)
  obtain ⟨hxM, hxW₂⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨w, hw, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_W d hK hD) x hxW₂
  have hyM : y ∈ d.M := by
    have := mul_mem (inv_mem (W_le_M d hw)) hxM
    rwa [inv_mul_cancel_left] at this
  have hyY : y ∈ d.Y := by
    rw [← h.M_inf_yamadaY₂ d hK hD]
    exact Subgroup.mem_inf.2 ⟨hyM, hy⟩
  exact mul_mem hw (hYW hyY)

theorem mul_self_mem_Y_of_mem_yamadaM₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaM₂ d t) :
    x * x ∈ d.Y :=
  h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD (h.yamadaM₂_le_yamadaL₂ d hK hD hx)

theorem commutator_t_mem_Y_of_mem_yamadaL₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {y : G} (hy : y ∈ yamadaL₂ d t) : ⁅y, t⁆ ∈ d.Y := by
  have h1 := (h.cosetData_tY d hK).crossed_mem y⁻¹ (yamadaL₂_le d t (inv_mem hy))
  rw [inv_inv] at h1
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right h.t_mul_t]
  exact h1

theorem conj_t_mul_t_mem_yamadaM₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {g : G} (hg : g ∈ normalizer (yamadaL₂ d t : Set G)) :
    g⁻¹ * t * g * t ∈ yamadaM₂ d t := by
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htN : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂
  have hgM : g ∈ normalizer (yamadaM₂ d t : Set G) := (h.normalizer_yamadaL₂_le d hK hD).1 hg
  have h1 : g⁻¹ * t * g ∈ yamadaL₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hg) t).1 htL₂
    rwa [inv_inv] at this
  rw [h.yamadaL₂_eq_sup d hK hD] at h1
  rcases (mem_sup_zpowers_iff_of h.t_mul_t htN).1 h1 with h2 | ⟨a, ha, e⟩
  · exfalso
    have := (mem_normalizer_iff.1 hgM _).1 h2
    rw [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at this
    exact h.t_not_mem_yamadaM₂ d hK hD this
  · rw [e, mul_assoc, h.t_mul_t, mul_one]
    exact ha

theorem isPGroup_yamadaW₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : IsPGroup 2 (yamadaW₂ d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := f * 5) (by rw [h.card_yamadaW₂ d hK hD, hK, ← pow_mul])

theorem normalizer_yamadaV₂_le_inf (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) ≤
      normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) :=
  le_inf (h.normalizer_le_normalizer_yamadaL₂ hW d hK hD)
    (h.normalizer_yamadaV₂_le hW d hK hD).1

theorem mem_normalizer_yamadaV₂_of_commutator_mem (h : Setup G L f t) (d : G2Data L K) {g : G}
    (hgW : g ∈ normalizer (yamadaW₂ d t : Set G)) (hgt : ⁅g, t⁆ ∈ yamadaW₂ d t) :
    g ∈ normalizer (yamadaV₂ d t : Set G) := by
  refine mem_normalizer_sup_zpowers_of_conj_mem hgW ?_
  have e : g * t * g⁻¹ = ⁅g, t⁆ * t := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mem_sup_left hgt) (mem_sup_right (mem_zpowers t))

theorem commutator_t_mem_W_of_mem_normalizer_yamadaV₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {g : G} (hg : g ∈ normalizer (yamadaV₂ d t : Set G)) : ⁅g, t⁆ ∈ d.W := by
  have hu := h.crossed_mem_W hW d hK hD hg
  have hc : Commute (t * g * t * g⁻¹) t :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hu))
  have hc' : Commute (t * g * t * g⁻¹) t⁻¹ := hc.inv_right
  have ht : t⁻¹ * t⁻¹ = 1 := by
    rw [← mul_inv_rev, h.t_mul_t, inv_one]
  have e : ⁅g, t⁆ = t⁻¹ * (t * g * t * g⁻¹) * t⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e, mul_assoc, hc'.eq, ← mul_assoc, ht, one_mul]
  exact hu

theorem exists_mul_yamadaL₃_centralizer_inf_normalizer_Y (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {g : G} (hg : g ∈ normalizer (yamadaV₂ d t : Set G)) :
    ∃ l ∈ yamadaL₃ d t, ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G),
      g = l * c := by
  have hg' : g ∈ ((normalizer (yamadaV₂ d t : Set G) : Subgroup G) : Set G) := hg
  rw [(h.yamada_5_23_1 hW d hK hD).2.2.1] at hg'
  obtain ⟨l, hl, c', hc', rfl⟩ := Set.mem_mul.1 hg'
  have hc'' : c' ∈ ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
      Set G) := hc'
  rw [(h.yamada_5_5_1 d hK).2.2.1] at hc''
  obtain ⟨l₂, hl₂, c, hc, rfl⟩ := Set.mem_mul.1 hc''
  refine ⟨l * l₂, mul_mem hl ((h.yamadaL₃_facts hW d hK hD).1 hl₂), c, hc, ?_⟩
  group

theorem mem_sup_zpowers_of_commutator_mem_M (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) (hcW : ∀ y ∈ d.M, ⁅c, y⁆ ∈ yamadaW₂ d t) :
    c ∈ d.M ⊔ zpowers t := by
  have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hc
  have hsec : ∀ y ∈ d.image (Model.M K), y⁻¹ * (c * y * c⁻¹) ∈ d.image (Model.W K) := by
    intro y hy
    have hyL : y ∈ L := d.image_le _ hy
    have hL : ⁅c, y⁆ ∈ L := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 hcL y).1 hyL) (inv_mem hyL)
    have h1 : ⁅c, y⁆ ∈ d.W := by
      rw [← h.yamadaW₂_inf_centralizer d hK hD]
      exact Subgroup.mem_inf.2 ⟨hcW y hy, h.L_le_centralizer hL⟩
    have h2 := (mem_normalizer_iff.1 (M_le_normalizer_W d (inv_mem hy)) _).1 h1
    rw [inv_inv, show y⁻¹ * ⁅c, y⁆ * y = y⁻¹ * (c * y * c⁻¹) by
      rw [commutatorElement_def]; group] at h2
    exact h2
  have hc' := (d.act_sectionCentralizer_eq (H₁ := Model.M K) (H₂ := Model.W K)
    (R := Model.M K) (Model.W_le_F.trans Model.F_le_M) (Model.yamada_3_23_M_W hK h.two_le)
    hcL).1 hsec
  have hZ : centralizer (L : Set G) ≤ normalizer (d.M : Set G) := fun z hz =>
    mem_normalizer_of_conj_mem fun x hx => by
      rw [← mem_centralizer_iff.1 hz x (d.image_le _ hx), mul_inv_cancel_right]
      exact hx
  obtain ⟨m, hm, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer hZ c hc'
  have hmC : m ∈ centralizer ({t} : Set G) := h.L_le_centralizer (d.image_le _ hm)
  have hzt : z ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem hmC) hc
    rwa [inv_mul_cancel_left] at this
  have hzt' : z ∈ zpowers t := by
    rw [← h.centralizer_L_inf]
    exact Subgroup.mem_inf.2 ⟨hz, hzt⟩
  exact mul_mem (mem_sup_left hm) (mem_sup_right hzt')

theorem mul_self_mem_yamadaW₂_of_mem_yamadaL₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {x : G} (hx : x ∈ yamadaL₃ d t) : x * x ∈ yamadaW₂ d t := by
  have h1 : x ^ 2 ∈ closure {z | ∃ g ∈ yamadaL₃ d t, z = g ^ 2} := subset_closure ⟨x, hx, rfl⟩
  rw [(h.yamada_5_35_3 hW d hK hQ).2.2.1, sq] at h1
  exact h1

theorem commutator_mem_yamadaW₂_of_mem_yamadaL₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {a b : G} (ha : a ∈ yamadaL₃ d t) (hb : b ∈ yamadaL₃ d t) : ⁅a, b⁆ ∈ yamadaW₂ d t :=
  commutator_mem_of_mul_self_mem (X := yamadaL₃ d t)
    (fun x hx => (h.normalizer_yamadaV₂_le hW d hK hQ.doubling).1
      (LieType.BorelTits.pCoreOf_le 2 _ hx))
    (fun x hx => h.mul_self_mem_yamadaW₂_of_mem_yamadaL₃ hW d hK hQ hx) ha hb

theorem leviB_le_normalizer_yamadaV₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.leviB ≤ normalizer (yamadaV₂ d t : Set G) := fun b hb =>
  (h.normalizer_tY_le d hK hD).2.2
    (h.centralizer_inf_normalizer_Y_le d (h.leviB_le_centralizer_inf_normalizer_Y d hb))

theorem exists_natModData (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ∃ (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G) (ψ : (Fin 2 → K) → G),
      ρ.range = d.leviB ∧ NatModData (yamadaW₂ d t) (yamadaM₂ d t) ψ ρ := by
  obtain ⟨ρ, hρ, -, -, ψ, hψM, hψW, hψs, hψa, hψc⟩ := d.yamada_3_16_2_natural_G
  have hWW₂ : d.W ≤ yamadaW₂ d t := le_sup_left
  refine ⟨ρ, ψ, hρ, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact mem_sup_left (hψM v)
  · intro v hv
    exact hψW v (by
      rw [← h.M_inf_yamadaW₂ d hK hD]
      exact Subgroup.mem_inf.2 ⟨hψM v, hv⟩)
  · intro x hx
    obtain ⟨m, hm, y, hy, rfl⟩ :=
      Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_M d hK hD) x hx
    obtain ⟨v, hv⟩ := hψs m hm
    refine ⟨v, ?_⟩
    rw [← mul_assoc]
    exact mul_mem (hWW₂ hv) ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hy)
  · intro v w
    exact hWW₂ (hψa v w)
  · intro g v
    exact hWW₂ (hψc g v)

theorem exists_point_yamadaM₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    ∃ f₀ ∈ yamadaM₂ d t, f₀ ∉ yamadaW₂ d t ∧
      ∃ g₀ ∈ normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G),
        (t * f₀)⁻¹ * (g₀⁻¹ * t * g₀) ∈ yamadaW₂ d t := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, -, -, -, -, -, hFM, -⟩ := d.inclusions
  have hFW : ¬ d.F ≤ yamadaW₂ d t := by
    intro hle
    have hFW' : d.F ≤ d.W := by
      rw [← h.M_inf_yamadaW₂ d hK hD]
      exact le_inf hFM hle
    have h1 := Subgroup.card_le_of_le hFW'
    rw [d.cards.2.2.2.2.1, d.cards.2.2.2.1] at h1
    have : Nat.card K ^ 3 < Nat.card K ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  obtain ⟨f₀, hf₀F, hf₀W⟩ := Set.not_subset.1 hFW
  have hf₀F₂ : f₀ ∈ yamadaF₂ d t := (le_sup_left : d.F ≤ yamadaF₂ d t) hf₀F
  obtain ⟨g, hg, y, hy, e⟩ := (h.yamada_5_21_3 hW d hK hD).2.1 f₀ hf₀F₂
  refine ⟨f₀, (le_sup_left : d.M ≤ yamadaM₂ d t) (hFM hf₀F), hf₀W, g⁻¹, ?_, ?_⟩
  · have hg' : g⁻¹ ∈ normalizer (yamadaR₂ d t : Set G) := inv_mem hg
    exact Subgroup.mem_inf.2 ⟨h.normalizer_yamadaR₂_le_normalizer_yamadaL₂ d hK hD hg',
      ((h.yamada_5_21_4 hW d hK hD).2 hg').1⟩
  · rw [inv_inv, e]
    have : (t * f₀)⁻¹ * (t * f₀ * y) = y := by group
    rw [this]
    exact (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hy

theorem conj_leviB_mem (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G} (hρ : ρ.range = d.leviB) {x : G}
    (hx : x ∈ normalizer (yamadaV₂ d t : Set G)) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ g' : Matrix.SpecialLinearGroup (Fin 2) K, ∃ b ∈ yamadaL₃ d t, x * ρ g * x⁻¹ = b * ρ g' := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨l, hl, c, hc, rfl⟩ := h.exists_mul_yamadaL₃_centralizer_inf_normalizer_Y hW d hK hD hx
  have hBM : d.leviB ≤ normalizer (d.M : Set G) :=
    d.image_le_normalizer (Model.leviB_le_adjointGroup K) Model.M_le_adjointGroup
      Model.leviB_le_normalizer_M
  have hcLY : c ∈ normalizer ((L ⊓ normalizer (d.Y : Set G) : Subgroup G) : Set G) :=
    Common.mem_normalizer_inf (h.centralizer_le_normalizer hc.1) (Subgroup.le_normalizer hc.2)
  rw [(d.yamada_3_13_3_G).1, ← (d.yamada_3_13_3_G).2.2.1] at hcLY
  have hcD := normalizer_le_normalizer_commutator _ hcLY
  rw [(d.yamada_3_13_4_G hK4).2.2.1] at hcD
  have hρg : ρ g ∈ d.leviB := by
    rw [← hρ]
    exact ⟨g, rfl⟩
  have h1 : c * ρ g * c⁻¹ ∈ d.M ⊔ d.leviB := (mem_normalizer_iff.1 hcD (ρ g)).1 (mem_sup_right hρg)
  obtain ⟨m, hm, g₂, hg₂, he⟩ := Common.exists_mul_of_le_normalizer hBM _ h1
  rw [← hρ] at hg₂
  obtain ⟨g', rfl⟩ := hg₂
  have hρ'N : ρ g' ∈ normalizer (yamadaL₃ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (h.leviB_le_normalizer_yamadaV₂ d hK hD (by rw [← hρ]; exact ⟨g', rfl⟩))
  have hmL₃ : m ∈ yamadaL₃ d t :=
    (h.yamadaL₃_facts hW d hK hD).1 ((h.yamadaM₂_le_yamadaL₂ d hK hD)
      ((le_sup_left : d.M ≤ yamadaM₂ d t) hm))
  refine ⟨g', l * m * (ρ g' * l⁻¹ * (ρ g')⁻¹), mul_mem (mul_mem hl hmL₃) ?_, ?_⟩
  · exact (mem_normalizer_iff.1 hρ'N l⁻¹).1 (inv_mem hl)
  · calc l * c * ρ g * (l * c)⁻¹ = l * (c * ρ g * c⁻¹) * l⁻¹ := by group
      _ = l * (m * ρ g') * l⁻¹ := by rw [he]
      _ = l * m * (ρ g' * l⁻¹ * (ρ g')⁻¹) * ρ g' := by group

theorem exists_two_core (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ P : Subgroup G, yamadaW₂ d t ≤ P ∧
      P ≤ normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) ∧
      IsPGroup 2 P ∧
      normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) ≤
        normalizer (P : Set G) ∧ yamadaL₃ d t ≤ P ∧
      normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) ≤
        normalizer (yamadaL₃ d t : Set G) ∧
      (∀ x ∈ P, ∀ y ∈ yamadaM₂ d t, ⁅x, y⁆ ∈ yamadaW₂ d t) ∧
      (∀ x ∈ P, ⁅x, t⁆ ∈ yamadaW₂ d t → x ∈ yamadaL₃ d t) ∧
      (∀ y ∈ yamadaM₂ d t, ∃ x ∈ P, (t * y)⁻¹ * (x⁻¹ * t * x) ∈ yamadaW₂ d t) ∧
      (∀ g ∈ normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G),
        ∃ c ∈ normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G),
          ⁅c, t⁆ ∈ yamadaW₂ d t ∧ ∃ x ∈ P, g = c * x) ∧
      (∀ Q : Subgroup G,
        Q ≤ normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) →
        normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) ≤
          normalizer (Q : Set G) → IsPGroup 2 Q → Q ≤ P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hQ.doubling
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ρ, ψ, hρ, hN⟩ := h.exists_natModData d hK hD
  have hWW₂ : d.W ≤ yamadaW₂ d t := le_sup_left
  have hYW₂ : d.Y ≤ yamadaW₂ d t := d.inclusions.2.2.1.trans hWW₂
  have hW₂M₂ := yamadaW₂_le_yamadaM₂ d t
  have hM₂N := h.yamadaM₂_le_normalizer_yamadaW₂ d hK hD
  have hM₂L₂ := h.yamadaM₂_le_yamadaL₂ d hK hD
  have hL₂L₃ := (h.yamadaL₃_facts hW d hK hD).1
  have hL₃V : yamadaL₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hVH := h.normalizer_yamadaV₂_le_inf hW d hK hD
  have hW2 := h.isPGroup_yamadaW₂ d hK hD
  have hρmem : ∀ g, ρ g ∈ d.leviB := fun g => by
    rw [← hρ]
    exact ⟨g, rfl⟩
  have hL₃W₂ : yamadaW₂ d t ≤ yamadaL₃ d t :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((le_sup_left : yamadaW₂ d t ≤ yamadaV₂ d t).trans Subgroup.le_normalizer)
      (h.normalizer_yamadaV₂_le hW d hK hD).1 hW2
  refine two_core_mod (Z := yamadaW₂ d t) (Mt := yamadaM₂ d t) (B := yamadaL₃ d t) (t := t)
    (ψ := ψ) (ρ := ρ) hW2
    (le_inf (hW₂M₂.trans (hM₂L₂.trans Subgroup.le_normalizer)) Subgroup.le_normalizer)
    inf_le_right hW₂M₂ hM₂N
    (inf_le_left.trans (h.normalizer_yamadaL₂_le d hK hD).1)
    (h.t_mem_normalizer_yamadaW₂ d hK hD).1 h.t_mul_t
    (fun x hx => hYW₂ (h.mul_self_mem_Y_of_mem_yamadaM₂ d hK hD hx))
    (fun y hy => hYW₂ (h.commutator_t_mem_Y_of_mem_yamadaL₂ d hK (hM₂L₂ hy)))
    (fun g hg => h.conj_t_mul_t_mem_yamadaM₂ d hK hD hg.1) hN
    (fun g => hVH (h.leviB_le_normalizer_yamadaV₂ d hK hD (hρmem g)))
    (fun g => mem_centralizer_singleton_iff.1
      (h.L_le_centralizer (d.image_le _ (hρmem g))))
    (h.exists_point_yamadaM₂ hW d hK hD)
    (fun x hx hxt g => h.conj_leviB_mem hW d hK hD hρ
      (h.mem_normalizer_yamadaV₂_of_commutator_mem d hx.2 hxt) g)
    hL₃W₂ (hL₃V.trans hVH) (LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (fun b hb => hWW₂ (h.commutator_t_mem_W_of_mem_normalizer_yamadaV₂ hW d hK hD (hL₃V hb)))
    (fun b hb y hy => h.commutator_mem_yamadaW₂_of_mem_yamadaL₃ hW d hK hQ hb (hL₂L₃ (hM₂L₂ hy)))
    ?_ ?_
  ·
    intro k hkH hkt hky
    have hkV := h.mem_normalizer_yamadaV₂_of_commutator_mem d hkH.2 hkt
    obtain ⟨l, hl, c, hc, rfl⟩ :=
      h.exists_mul_yamadaL₃_centralizer_inf_normalizer_Y hW d hK hD hkV
    have hlN : l ∈ normalizer (yamadaW₂ d t : Set G) := (hL₃V.trans hVH) hl |>.2
    have hcM : ∀ y ∈ d.M, ⁅c, y⁆ ∈ yamadaW₂ d t := by
      intro y hy
      have hyM₂ : y ∈ yamadaM₂ d t := (le_sup_left : d.M ≤ yamadaM₂ d t) hy
      have hyN : y ∈ normalizer (yamadaW₂ d t : Set G) := hM₂N hyM₂
      have h1 : ⁅l⁻¹, y⁆ ∈ yamadaW₂ d t := by
        refine commutator_inv_mem_mod hlN hyN ?_
        exact h.commutator_mem_yamadaW₂_of_mem_yamadaL₃ hW d hK hQ hl (hL₂L₃ (hM₂L₂ hyM₂))
      have h2 : ⁅l * c, y⁆ ∈ yamadaW₂ d t := hky y hyM₂
      have := commutator_mul_mem_mod (inv_mem hlN) hkH.2 hyN h1 h2
      rwa [inv_mul_cancel_left] at this
    have hcMt := h.mem_sup_zpowers_of_commutator_mem_M d hK hD hc.1 hcM
    exact mul_mem hl (hL₂L₃ (h.tM_le_yamadaL₂ d hK hcMt))
  ·
    intro R hWR hR hRn hR2
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (fun x hx => h.mem_normalizer_yamadaV₂_of_commutator_mem d (hR x hx).1.2 (hR x hx).2)
      (fun g hg => mem_normalizer_fintype fun x hx => hRn g (hVH hg)
        (hWW₂ (h.commutator_t_mem_W_of_mem_normalizer_yamadaV₂ hW d hK hD hg)) x hx) hR2

theorem exists_mem_crossed_mem_yamadaY₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {P : Subgroup G}
    (hPN : P ≤ normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G))
    (hL₃P : yamadaL₃ d t ≤ P)
    (hPtr : ∀ y ∈ yamadaM₂ d t, ∃ x ∈ P, (t * y)⁻¹ * (x⁻¹ * t * x) ∈ yamadaW₂ d t) :
    ∀ y ∈ yamadaM₂ d t, ∃ p ∈ P, (t * y)⁻¹ * (p⁻¹ * t * p) ∈ yamadaY₂ d t := by
  intro y hy
  obtain ⟨x, hxP, hx⟩ := hPtr y hy
  have hxH := hPN hxP
  have hxY₂ : x ∈ normalizer (yamadaY₂ d t : Set G) :=
    (h.normalizer_yamadaL₂_le d hK hD).2 hxH.1
  have hWW₂ : d.W ≤ yamadaW₂ d t := le_sup_left
  have hYY₂ : yamadaY₂ d t ≤ yamadaW₂ d t := le_sup_right
  set w₂ := (t * y)⁻¹ * (x⁻¹ * t * x) with hw₂
  obtain ⟨w₀, hw₀, z, hz, hw₂e⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_W d hK hD) w₂ hx
  have h1 : x * w₀⁻¹ * x⁻¹ ∈ yamadaW₂ d t :=
    (mem_normalizer_iff.1 hxH.2 _).1 (hWW₂ (inv_mem hw₀))
  obtain ⟨w₁, hw₁, z₁, hz₁, he₁⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_W d hK hD) _ h1
  obtain ⟨g, hg, hgt⟩ := (h.yamada_5_23_2 hW d hK hD).2 w₁ hw₁
  have hxw₁ : x⁻¹ * w₁ * x = w₀⁻¹ * (x⁻¹ * z₁ * x)⁻¹ := by
    have : w₁ = x * w₀⁻¹ * x⁻¹ * z₁⁻¹ := by rw [he₁]; group
    rw [this]
    group
  have hcomm : w₀ * z = z * w₀ :=
    mem_centralizer_iff.1 (h.yamadaW₂_le_centralizer d hK hD (hYY₂ hz)) w₀ (hWW₂ hw₀)
  refine ⟨g⁻¹ * x, mul_mem (inv_mem (hL₃P hg)) hxP, ?_⟩
  have e : (t * y)⁻¹ * ((g⁻¹ * x)⁻¹ * t * (g⁻¹ * x)) = z * (x⁻¹ * z₁ * x)⁻¹ := by
    calc (t * y)⁻¹ * ((g⁻¹ * x)⁻¹ * t * (g⁻¹ * x)) =
          (t * y)⁻¹ * (x⁻¹ * (g * t * g⁻¹) * x) := by group
      _ = (t * y)⁻¹ * (x⁻¹ * (t * w₁) * x) := by rw [hgt]
      _ = ((t * y)⁻¹ * (x⁻¹ * t * x)) * (x⁻¹ * w₁ * x) := by group
      _ = (w₀ * z) * (w₀⁻¹ * (x⁻¹ * z₁ * x)⁻¹) := by rw [← hw₂e, hxw₁]
      _ = (z * w₀) * (w₀⁻¹ * (x⁻¹ * z₁ * x)⁻¹) := by rw [hcomm]
      _ = z * (x⁻¹ * z₁ * x)⁻¹ := by group
  rw [e]
  refine mul_mem hz (inv_mem ?_)
  have := (mem_normalizer_iff.1 (inv_mem hxY₂) z₁).1 hz₁
  rwa [inv_inv] at this

theorem normalizer_yamadaL₂_le_normalizer_yamadaW₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaW₂ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨P, -, hPH, -, -, hL₃P, -, -, -, hPtr, -, -⟩ := h.exists_two_core hW d hK hQ
  have hPY := h.exists_mem_crossed_mem_yamadaY₂ hW d hK hD hPH hL₃P hPtr
  have hVH := h.normalizer_yamadaV₂_le_inf hW d hK hD
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htM : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂
  intro n hn
  have hnY := (h.normalizer_yamadaL₂_le d hK hD).2 hn
  have hm := h.conj_t_mul_t_mem_yamadaM₂ d hK hD hn
  set y' := t * (n⁻¹ * t * n * t) * t with hy'
  have hy'M : y' ∈ yamadaM₂ d t := by
    have := (mem_normalizer_iff.1 htM _).1 hm
    rwa [inv_eq_of_mul_eq_one_right h.t_mul_t] at this
  have hny : t * y' = n⁻¹ * t * n := by
    calc t * y' = (t * t) * (n⁻¹ * t * n * t) * t := by rw [hy']; group
      _ = (n⁻¹ * t * n * t) * t := by rw [h.t_mul_t, one_mul]
      _ = n⁻¹ * t * n * (t * t) := by group
      _ = n⁻¹ * t * n := by rw [h.t_mul_t, mul_one]
  obtain ⟨p, hpP, hp⟩ := hPY y' hy'M
  set z := (t * y')⁻¹ * (p⁻¹ * t * p) with hz
  have hpt : p⁻¹ * t * p = t * y' * z := by rw [hz]; group
  have hg : (p * n⁻¹)⁻¹ * t * (p * n⁻¹) = t * (n * z * n⁻¹) := by
    calc (p * n⁻¹)⁻¹ * t * (p * n⁻¹) = n * (p⁻¹ * t * p) * n⁻¹ := by group
      _ = n * (t * y' * z) * n⁻¹ := by rw [hpt]
      _ = n * (n⁻¹ * t * n * z) * n⁻¹ := by rw [← hny]
      _ = t * (n * z * n⁻¹) := by group
  have hgN : (p * n⁻¹)⁻¹ ∈ normalizer (yamadaY₂ d t : Set G) :=
    inv_mem (mul_mem ((h.normalizer_yamadaL₂_le d hK hD).2 (hPH hpP).1) (inv_mem hnY))
  have hnz : n * z * n⁻¹ ∈ yamadaY₂ d t := (mem_normalizer_iff.1 hnY z).1 hp
  have hgS : (p * n⁻¹)⁻¹ ∈ normalizer ((yamadaY₂ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    refine mem_normalizer_sup_zpowers_of_conj_mem hgN ?_
    rw [inv_inv, hg]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hnz)
  rw [h.yamada_5_17_2 hW d hK hD] at hgS
  have hgH := hVH ((h.normalizer_tY_le d hK hD).2.2 hgS)
  have e : n = (p * n⁻¹)⁻¹ * p := by group
  rw [e]
  exact mul_mem hgH.2 (hPH hpP).2

theorem crossed_mem_yamadaM₂' (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ normalizer (yamadaL₂ d t : Set G)) :
    t * x * t * x⁻¹ ∈ yamadaM₂ d t := by
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htM : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂
  have hm := h.conj_t_mul_t_mem_yamadaM₂ d hK hD (inv_mem hx)
  rw [inv_inv] at hm
  have := (mem_normalizer_iff.1 htM _).1 hm
  rwa [show t * (x * t * x⁻¹ * t) * t⁻¹ = t * x * t * x⁻¹ by group] at this

theorem exists_mulEquiv_M_W (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ∃ (_ : (d.W.subgroupOf d.M).Normal)
      (_ : ((yamadaW₂ d t).subgroupOf (yamadaM₂ d t)).Normal),
      ∃ η : d.M ⧸ d.W.subgroupOf d.M ≃*
          yamadaM₂ d t ⧸ (yamadaW₂ d t).subgroupOf (yamadaM₂ d t),
        ∀ m : d.M, η (QuotientGroup.mk m) =
          QuotientGroup.mk ⟨(m : G), (le_sup_left : d.M ≤ yamadaM₂ d t) m.2⟩ := by
  have hMM₂ : d.M ≤ yamadaM₂ d t := le_sup_left
  have hn1 : (d.W.subgroupOf d.M).Normal :=
    (normal_subgroupOf_iff_le_normalizer (W_le_M d)).2 (M_le_normalizer_W d)
  have hn2 : ((yamadaW₂ d t).subgroupOf (yamadaM₂ d t)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (yamadaW₂_le_yamadaM₂ d t)).2
      (h.yamadaM₂_le_normalizer_yamadaW₂ d hK hD)
  refine ⟨hn1, hn2, ?_⟩
  let incl : d.M →* yamadaM₂ d t := Subgroup.inclusion hMM₂
  have hle : d.W.subgroupOf d.M ≤ ((yamadaW₂ d t).subgroupOf (yamadaM₂ d t)).comap incl :=
    fun w hw => by
      rw [mem_comap, mem_subgroupOf]
      exact (le_sup_left : d.W ≤ yamadaW₂ d t) (mem_subgroupOf.1 hw)
  let η₀ : d.M ⧸ d.W.subgroupOf d.M →*
      yamadaM₂ d t ⧸ (yamadaW₂ d t).subgroupOf (yamadaM₂ d t) :=
    QuotientGroup.map _ _ incl hle
  have hinj : Function.Injective η₀ := by
    refine (injective_iff_map_eq_one η₀).2 fun q hq => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : η₀ (QuotientGroup.mk m) = QuotientGroup.mk (incl m) := rfl
    rw [h1, QuotientGroup.eq_one_iff, mem_subgroupOf] at hq
    have hmW : (m : G) ∈ d.W := by
      rw [← h.M_inf_yamadaW₂ d hK hD]
      exact Subgroup.mem_inf.2 ⟨m.2, hq⟩
    exact (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hmW)
  have hsurj : Function.Surjective η₀ := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm, y, hy, hb⟩ :=
      Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_M d hK hD) (b : G) b.2
    refine ⟨QuotientGroup.mk ⟨m, hm⟩, ?_⟩
    show QuotientGroup.mk (incl ⟨m, hm⟩) = QuotientGroup.mk b
    rw [QuotientGroup.eq, mem_subgroupOf]
    show (m : G)⁻¹ * (b : G) ∈ yamadaW₂ d t
    rw [hb, inv_mul_cancel_left]
    exact (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hy
  exact ⟨MulEquiv.ofBijective η₀ ⟨hinj, hsurj⟩, fun m => rfl⟩

theorem yamadaL₆_spec (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₃ d t ≤ yamadaL₆ d t ∧
      (∀ x ∈ yamadaL₆ d t, ∀ y ∈ yamadaM₂ d t, ⁅x, y⁆ ∈ yamadaW₂ d t) ∧
      (∀ x ∈ yamadaL₆ d t, ⁅x, t⁆ ∈ yamadaW₂ d t → x ∈ yamadaL₃ d t) ∧
      (∀ y ∈ yamadaM₂ d t, ∃ x ∈ yamadaL₆ d t, (t * y)⁻¹ * (x⁻¹ * t * x) ∈ yamadaW₂ d t) ∧
      (∀ g ∈ normalizer (yamadaL₂ d t : Set G), ∃ c ∈ normalizer (yamadaV₂ d t : Set G),
        ∃ x ∈ yamadaL₆ d t, g = c * x) ∧
      normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaL₃ d t : Set G) ∧
      normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaW₂ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hQ.doubling
  obtain ⟨P, -, hPH, hP2, hHP, hL₃P, hHB, hPM, hPB, hPtr, hPfac, hPmax⟩ :=
    h.exists_two_core hW d hK hQ
  have hN₂W := h.normalizer_yamadaL₂_le_normalizer_yamadaW₂ hW d hK hQ
  have hHN : normalizer (yamadaL₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) =
      normalizer (yamadaL₂ d t : Set G) := inf_eq_left.2 hN₂W
  rw [hHN] at hPH hHP hHB hPfac hPmax
  have hL₆P : yamadaL₆ d t = P := le_antisymm
    (hPmax _ (yamadaL₆_le d t) (le_normalizer_yamadaL₆ d t)
      (LieType.BorelTits.pCoreOf_isPGroup 2 _))
    (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPH hHP hP2)
  rw [hL₆P]
  refine ⟨hL₃P, hPM, hPB, hPtr, fun g hg => ?_, hHB, hN₂W⟩
  obtain ⟨c, hc, hct, x, hx, rfl⟩ := hPfac g hg
  exact ⟨c, h.mem_normalizer_yamadaV₂_of_commutator_mem d (hN₂W hc) hct, x, hx, rfl⟩

theorem yamada_5_39_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (normalizer (yamadaL₂ d t : Set G) = yamadaL₆ d t ⊔ normalizer (yamadaV₂ d t : Set G) ∧
      ((normalizer (yamadaL₂ d t : Set G) : Subgroup G) : Set G) =
        (yamadaL₆ d t : Set G) * ((normalizer (yamadaV₂ d t : Set G) : Subgroup G) : Set G) ∧
      normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaL₃ d t : Set G)) ∧
    yamadaL₆ d t ⊓ normalizer (yamadaV₂ d t : Set G) = yamadaL₃ d t := by
  have hD := hQ.doubling
  obtain ⟨hL₃P, -, hPB, -, hfac, hHB, -⟩ := h.yamadaL₆_spec hW d hK hQ
  have hVN := (h.normalizer_yamadaV₂_le_inf hW d hK hD).trans (inf_le_left)
  refine ⟨⟨le_antisymm (fun g hg => ?_) (sup_le (yamadaL₆_le d t) hVN), le_antisymm
    (fun g hg => ?_) (fun g hg => ?_), hHB⟩, le_antisymm (fun x hx => ?_) (le_inf hL₃P
    (LieType.BorelTits.pCoreOf_le 2 _))⟩
  · obtain ⟨c, hc, x, hx, rfl⟩ := hfac g hg
    exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
  · obtain ⟨c, hc, x, hx, rfl⟩ := hfac g hg
    exact Set.mem_mul.2 ⟨c * x * c⁻¹,
      (mem_normalizer_iff.1 (le_normalizer_yamadaL₆ d t (hVN hc)) x).1 hx, c, hc, by group⟩
  · obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.1 hg
    exact mul_mem (yamadaL₆_le d t hl) (hVN hc)
  · obtain ⟨hxP, hxV⟩ := Subgroup.mem_inf.1 hx
    exact hPB x hxP ((le_sup_left : d.W ≤ yamadaW₂ d t)
      (h.commutator_t_mem_W_of_mem_normalizer_yamadaV₂ hW d hK hD hxV))

theorem yamada_5_39_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ _ : ((yamadaL₃ d t).subgroupOf (yamadaL₆ d t)).Normal,
      ∃ _ : (d.W.subgroupOf d.M).Normal,
        ∃ φ : yamadaL₆ d t ⧸ (yamadaL₃ d t).subgroupOf (yamadaL₆ d t) ≃*
          d.M ⧸ d.W.subgroupOf d.M,
        (∀ (x : yamadaL₆ d t) (m : d.M), ∀ y ∈ yamadaY₂ d t,
          (x : G) * t * (x : G)⁻¹ = t * m * y → φ (QuotientGroup.mk x) = QuotientGroup.mk m) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G),
          ∀ (x : yamadaL₆ d t) (m : d.M), φ (QuotientGroup.mk x) = QuotientGroup.mk m →
            ∃ (hx : c * x * c⁻¹ ∈ yamadaL₆ d t) (hm : c * m * c⁻¹ ∈ d.M),
              φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, hm⟩ := by
  have hD := hQ.doubling
  obtain ⟨hL₃P, hPM, hPB, hPtr, -, -, -⟩ := h.yamadaL₆_spec hW d hK hQ
  obtain ⟨hn1, hn2, η, hη⟩ := h.exists_mulEquiv_M_W d hK hD
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have htW₂ : t ∈ normalizer (yamadaW₂ d t : Set G) := (h.t_mem_normalizer_yamadaW₂ d hK hD).1
  have hL₃V : yamadaL₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hκ : ∀ x : yamadaL₆ d t, t * (x : G) * t * (x : G)⁻¹ ∈ yamadaM₂ d t := fun x =>
    h.crossed_mem_yamadaM₂' d hK hD (yamadaL₆_le d t x.2)
  let ψ : yamadaL₆ d t →* yamadaM₂ d t ⧸ (yamadaW₂ d t).subgroupOf (yamadaM₂ d t) :=
    { toFun := fun x => QuotientGroup.mk ⟨t * (x : G) * t * (x : G)⁻¹, hκ x⟩
      map_one' := by
        refine (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ?_)
        show t * 1 * t * (1 : G)⁻¹ ∈ yamadaW₂ d t
        rw [mul_one, inv_one, mul_one, h.t_mul_t]
        exact one_mem _
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        show (t * ((x : G) * y) * t * ((x : G) * y)⁻¹)⁻¹ *
          ((t * (x : G) * t * (x : G)⁻¹) * (t * (y : G) * t * (y : G)⁻¹)) ∈ yamadaW₂ d t
        rw [h.crossed_mul' x y, show (t * (x : G) * t * (x : G)⁻¹ *
          ((x : G) * (t * (y : G) * t * (y : G)⁻¹) * (x : G)⁻¹))⁻¹ *
            ((t * (x : G) * t * (x : G)⁻¹) * (t * (y : G) * t * (y : G)⁻¹)) =
              ⁅(x : G), (t * (y : G) * t * (y : G)⁻¹)⁻¹⁆ by
          rw [commutatorElement_def]; group]
        exact hPM (x : G) x.2 _ (inv_mem (hκ y)) }
  have hψ : ∀ x : yamadaL₆ d t, ψ x = QuotientGroup.mk ⟨t * (x : G) * t * (x : G)⁻¹, hκ x⟩ :=
    fun _ => rfl
  have hker : ψ.ker = (yamadaL₃ d t).subgroupOf (yamadaL₆ d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro hx
      have e1 : ⁅(x : G), t⁆ = (x : G) * t * (x : G)⁻¹ * t := by
        rw [commutatorElement_def, ht']
      have e2 : (x : G) * t * (x : G)⁻¹ * t = t⁻¹ * (t * (x : G) * t * (x : G)⁻¹) * t := by
        group
      have h1 := (mem_normalizer_iff.1 (inv_mem htW₂) _).1 hx
      rw [inv_inv] at h1
      exact hPB x x.2 (by rw [e1, e2]; exact h1)
    · intro hx
      exact (le_sup_left : d.W ≤ yamadaW₂ d t)
        (h.crossed_mem_W hW d hK hD (hL₃V hx))
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hxP, hx⟩ := hPtr (y : G) y.2
    refine ⟨⟨x⁻¹, inv_mem hxP⟩, ?_⟩
    rw [hψ, QuotientGroup.eq, mem_subgroupOf]
    have e := h.conj_t_eq_mul_crossed x⁻¹
    rw [inv_inv] at e
    rw [e] at hx
    have h1 := inv_mem hx
    show (t * x⁻¹ * t * (x⁻¹)⁻¹)⁻¹ * (y : G) ∈ yamadaW₂ d t
    rw [inv_inv]
    rwa [show ((t * (y : G))⁻¹ * (t * (t * x⁻¹ * t * x)))⁻¹ = (t * x⁻¹ * t * x)⁻¹ * (y : G) by
      group] at h1
  have hL₃n : ((yamadaL₃ d t).subgroupOf (yamadaL₆ d t)).Normal := hker ▸ ψ.normal_ker
  set φ₀ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj) with hφ₀def
  have hφ₀ : ∀ x : yamadaL₆ d t, φ₀ (QuotientGroup.mk x) = ψ x := fun _ => rfl
  refine ⟨hL₃n, hn1, φ₀.trans η.symm, ?_, ?_⟩
  · intro x m y hy e
    show η.symm (φ₀ (QuotientGroup.mk x)) = QuotientGroup.mk m
    rw [hφ₀, MulEquiv.symm_apply_eq, hη, hψ, QuotientGroup.eq, mem_subgroupOf]
    have hκx : t * (x : G) * t * (x : G)⁻¹ = (m : G) * y := by
      rw [show t * (x : G) * t * (x : G)⁻¹ = t * ((x : G) * t * (x : G)⁻¹) by group, e,
        ← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
    show (t * (x : G) * t * (x : G)⁻¹)⁻¹ * (m : G) ∈ yamadaW₂ d t
    rw [hκx, show ((m : G) * y)⁻¹ * (m : G) = y⁻¹ by group]
    exact inv_mem ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hy)
  · intro c hc x m hxm
    obtain ⟨hct, hcY⟩ := Subgroup.mem_inf.1 hc
    have hcN := h.centralizer_inf_normalizer_Y_le d hc
    have hcL₆ : c ∈ normalizer (yamadaL₆ d t : Set G) :=
      le_normalizer_yamadaL₆ d t (le_normalizer_yamadaL₂ d t hcN)
    have hcM : c ∈ normalizer (d.M : Set G) := by
      refine h.mem_normalizer_of_mem_normalizer_sup_t (E := d.M) (d.image_le _) hct ?_
      rw [← (h.yamada_5_5_1 d hK).1]
      exact hcN
    have hcW₂ : c ∈ normalizer (yamadaW₂ d t : Set G) :=
      Common.mem_normalizer_sup ((h.normalizer_tY_le d hK hD).1 hcN)
        ((h.normalizer_tY_le d hK hD).2.1 hcN)
    have hx : c * x * c⁻¹ ∈ yamadaL₆ d t := (mem_normalizer_iff.1 hcL₆ x).1 x.2
    have hm : c * m * c⁻¹ ∈ d.M := (mem_normalizer_iff.1 hcM m).1 m.2
    refine ⟨hx, hm, ?_⟩
    have h1 : (t * (x : G) * t * (x : G)⁻¹)⁻¹ * (m : G) ∈ yamadaW₂ d t := by
      have h2 : η.symm (φ₀ (QuotientGroup.mk x)) = QuotientGroup.mk m := hxm
      rw [hφ₀, MulEquiv.symm_apply_eq, hη, hψ, QuotientGroup.eq, mem_subgroupOf] at h2
      exact h2
    show η.symm (φ₀ (QuotientGroup.mk ⟨c * x * c⁻¹, hx⟩)) = QuotientGroup.mk ⟨c * m * c⁻¹, hm⟩
    rw [hφ₀, MulEquiv.symm_apply_eq, hη, hψ, QuotientGroup.eq, mem_subgroupOf]
    have hcte : c * t = t * c := mem_centralizer_singleton_iff.1 hct
    have hct' : c⁻¹ * t * c = t := by rw [mul_assoc, ← hcte, inv_mul_cancel_left]
    have hκc : t * (c * (x : G) * c⁻¹) * t * (c * (x : G) * c⁻¹)⁻¹ =
        c * (t * (x : G) * t * (x : G)⁻¹) * c⁻¹ := by
      calc t * (c * (x : G) * c⁻¹) * t * (c * (x : G) * c⁻¹)⁻¹ =
            (t * c) * x * (c⁻¹ * t * c) * (x : G)⁻¹ * c⁻¹ := by group
        _ = (c * t) * x * t * (x : G)⁻¹ * c⁻¹ := by rw [hct', ← hcte]
        _ = c * (t * (x : G) * t * (x : G)⁻¹) * c⁻¹ := by group
    show (t * (c * (x : G) * c⁻¹) * t * (c * (x : G) * c⁻¹)⁻¹)⁻¹ * (c * (m : G) * c⁻¹) ∈
      yamadaW₂ d t
    rw [hκc, show (c * (t * (x : G) * t * (x : G)⁻¹) * c⁻¹)⁻¹ * (c * (m : G) * c⁻¹) =
      c * ((t * (x : G) * t * (x : G)⁻¹)⁻¹ * (m : G)) * c⁻¹ by group]
    exact (mem_normalizer_iff.1 hcW₂ _).1 h1

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
