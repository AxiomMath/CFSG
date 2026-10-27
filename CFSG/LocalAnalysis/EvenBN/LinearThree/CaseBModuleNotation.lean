module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBModule
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint Matrix
open CFSG.OddStandard.Seitz77 (Datum)

namespace CaseBModule

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}

@[expose] def preim {q : ℕ} (w : WData d Vi q) (X : Subgroup w.Nbar) : Subgroup G :=
  (X.comap w.projBar).map w.N.subtype

theorem mem_preim {q : ℕ} (w : WData d Vi q) (X : Subgroup w.Nbar) {g : G} :
    g ∈ preim w X ↔ ∃ hg : g ∈ w.N, w.projBar ⟨g, hg⟩ ∈ X := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hg, hgX⟩
    exact ⟨⟨g, hg⟩, hgX, rfl⟩

theorem preim_le_N {q : ℕ} (w : WData d Vi q) (X : Subgroup w.Nbar) : preim w X ≤ w.N := by
  rintro _ ⟨n, -, rfl⟩
  exact n.2

theorem W_le_preim {q : ℕ} (w : WData d Vi q) (X : Subgroup w.Nbar) : w.W ≤ preim w X := by
  intro x hx
  refine (mem_preim w X).mpr ⟨w.W_le_N hx, ?_⟩
  rw [(w.projBar_eq_one_iff _).mpr hx]
  exact one_mem X

section Multiplier

variable [Finite G]

theorem commutator_preim_inf_le {q : ℕ} (w : WData d Vi q) {K : Type} [Field K] [Finite K]
    (hK5 : 5 ≤ Nat.card K) (hK9 : Nat.card K ≠ 9)
    (σ : Matrix.SpecialLinearGroup (Fin 2) K →* w.Nbar) (hσinj : Function.Injective σ)
    {W₁ W₂ : Subgroup G} (hW₁ : W₁ ≤ w.W) (hW : W₁ ⊔ W₂ = w.W)
    (hcen : ∀ n : w.N, w.projBar n ∈ σ.range → ∀ y ∈ W₂, (n : G) * y * (n : G)⁻¹ = y)
    (hnor : ∀ n : w.N, w.projBar n ∈ σ.range → ∀ x ∈ W₁, (n : G) * x * (n : G)⁻¹ ∈ W₁) :
    ⁅preim w σ.range, preim w σ.range⁆ ⊓ w.W ≤ W₁ := by
  set PN : Subgroup w.N := σ.range.comap w.projBar with hPN
  set W₁P : Subgroup PN := (W₁.comap w.N.subtype).subgroupOf PN with hW₁P
  have hnormal : W₁P.Normal := by
    constructor
    intro x hx p
    rw [hW₁P, mem_subgroupOf, mem_comap] at hx ⊢
    exact hnor (p : w.N) p.2 _ hx
  let σinv : σ.range ≃* Matrix.SpecialLinearGroup (Fin 2) K := (MonoidHom.ofInjective hσinj).symm
  let π : PN →* Matrix.SpecialLinearGroup (Fin 2) K :=
    σinv.toMonoidHom.comp ((w.projBar.comp PN.subtype).codRestrict σ.range fun x => x.2)
  have hπW : ∀ x : PN, π x = 1 ↔ ((x : w.N) : G) ∈ w.W := by
    intro x
    rw [← w.projBar_eq_one_iff]
    constructor
    · intro h
      have h1 : ((w.projBar.comp PN.subtype).codRestrict σ.range fun x => x.2) x = 1 := by
        apply σinv.injective
        rw [map_one]
        exact h
      exact congrArg Subtype.val h1
    · intro h
      have h1 : ((w.projBar.comp PN.subtype).codRestrict σ.range fun x => x.2) x = 1 :=
        Subtype.ext h
      change σinv _ = 1
      rw [h1, map_one]
  have hW₁ker : W₁P ≤ π.ker := fun x hx => (hπW x).mpr (hW₁ hx)
  let πQ : PN ⧸ W₁P →* Matrix.SpecialLinearGroup (Fin 2) K := QuotientGroup.lift W₁P π hW₁ker
  have hπQ : ∀ x : PN, πQ x = π x := fun x => QuotientGroup.lift_mk _ _ x
  have hπsurj : Function.Surjective π := by
    intro B
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective w.WN (σ B)
    refine ⟨⟨n, mem_comap.mpr ⟨B, hn.symm⟩⟩, ?_⟩
    change σinv _ = B
    rw [← MulEquiv.eq_symm_apply]
    apply Subtype.ext
    simp only [σinv, MulEquiv.symm_symm, MonoidHom.ofInjective_apply]
    exact hn
  have hπQsurj : Function.Surjective πQ := by
    intro B
    obtain ⟨x, hx⟩ := hπsurj B
    exact ⟨x, by rw [hπQ, hx]⟩
  have hker : πQ.ker ≤ center (PN ⧸ W₁P) := by
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective W₁P x
    have hp : π p = 1 := by
      have := (MonoidHom.mem_ker).mp hx
      rwa [QuotientGroup.mk'_apply, hπQ] at this
    have hpW := (hπW p).mp hp
    rw [mem_center_iff]
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective W₁P y
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [hW₁P, mem_subgroupOf, mem_comap]
    set p' : G := ((p : w.N) : G) with hp'
    set r' : G := ((r : w.N) : G) with hr'
    have hW₁₂ : W₁ ≤ normalizer (W₂ : Set G) := by
      intro a ha
      refine mem_normalizer_fintype fun b hb => ?_
      have hab := comm_of_isElemAbelian w.elem (hW₁ ha) (hW ▸ mem_sup_right hb)
      rw [hab, mul_inv_cancel_right]
      exact hb
    have hp'W : p' ∈ (W₁ ⊔ W₂ : Subgroup G) := hW ▸ hpW
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hW₁₂, Set.mem_mul] at hp'W
    obtain ⟨a, ha, b, hb, hab⟩ := hp'W
    have hrinv : w.projBar (r : w.N)⁻¹ ∈ σ.range := by rw [map_inv]; exact inv_mem r.2
    have hb' : r'⁻¹ * b * r' = b := by
      have := hcen (r : w.N)⁻¹ hrinv b hb
      simpa [hr'] using this
    have ha' : r'⁻¹ * a * r' ∈ W₁ := by
      have := hnor (r : w.N)⁻¹ hrinv a ha
      simpa [hr'] using this
    have hgoal : (((r * p)⁻¹ * (p * r) : PN) : w.N) = (p'⁻¹ * (r'⁻¹ * p' * r') : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hp', hr']
      group
    change ((((r * p)⁻¹ * (p * r) : PN) : w.N) : G) ∈ W₁
    rw [hgoal, ← hab]
    have e1 : r'⁻¹ * (a * b) * r' = (r'⁻¹ * a * r') * (r'⁻¹ * b * r') := by group
    rw [e1, hb']
    have hc : (r'⁻¹ * a * r') * b = b * (r'⁻¹ * a * r') :=
      comm_of_isElemAbelian w.elem (hW₁ ha') (hW ▸ mem_sup_right hb)
    rw [hc, _root_.mul_inv_rev, show b⁻¹ * a⁻¹ * (b * (r'⁻¹ * a * r')) =
      a⁻¹ * (b⁻¹ * b) * (r'⁻¹ * a * r') by
        rw [show b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ from
          (comm_of_isElemAbelian w.elem (hW ▸ mem_sup_right (inv_mem hb))
            (hW₁ (inv_mem ha)))]
        group, inv_mul_cancel, mul_one]
    exact mul_mem (inv_mem ha) ha'
  obtain ⟨σ₂, hσ₂⟩ :=
    LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central hK5 hK9 hπQsurj hker
  have hcomQ : commutator (PN ⧸ W₁P) ≤ σ₂.range := by
    rw [_root_.commutator_def, commutator_le]
    intro x _ y _
    have hz : ∀ u : PN ⧸ W₁P, (σ₂ (πQ u))⁻¹ * u ∈ center (PN ⧸ W₁P) := fun u =>
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hσ₂, inv_mul_cancel])
    have hx : x = σ₂ (πQ x) * ((σ₂ (πQ x))⁻¹ * x) := by group
    have hy : y = σ₂ (πQ y) * ((σ₂ (πQ y))⁻¹ * y) := by group
    rw [hx, hy, LieType.Steinberg.CentralExt.TorusLift.commutatorElement_mul_central_left (hz x),
      LieType.Steinberg.CentralExt.TorusLift.commutatorElement_mul_central_right (hz y),
      ← map_commutatorElement]
    exact ⟨_, rfl⟩
  rintro c ⟨hc, hcW⟩
  have hP : preim w σ.range = PN.map w.N.subtype := rfl
  rw [hP, ← map_commutator] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  have hPN : PN = (⊤ : Subgroup PN).map PN.subtype := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  rw [hPN, ← map_commutator] at hc'
  obtain ⟨c'', hc'', rfl⟩ := hc'
  have hmk : (QuotientGroup.mk' W₁P c'') ∈ σ₂.range := by
    apply hcomQ
    rw [← _root_.commutator_def] at hc''
    have := map_commutator (⊤ : Subgroup PN) ⊤ (QuotientGroup.mk' W₁P)
    rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
    rw [_root_.commutator_def, ← this]
    exact ⟨c'', hc'', rfl⟩
  obtain ⟨B, hB⟩ := hmk
  have hB1 : B = 1 := by
    have h1 := hσ₂ B
    rw [hB, QuotientGroup.mk'_apply, hπQ, (hπW c'').mpr hcW] at h1
    exact h1.symm
  rw [hB1, map_one] at hB
  have := (QuotientGroup.eq_one_iff _).mp hB.symm
  rw [hW₁P, mem_subgroupOf, mem_comap] at this
  exact this

end Multiplier

section Generic

variable [Finite G]

omit [Finite G] in
theorem map_conj_commutator_sup_le {Q R : Subgroup G} {g : G}
    (hQ : Q.map (MulAut.conj g).toMonoidHom ≤ Q) (hR : R.map (MulAut.conj g).toMonoidHom ≤ R) :
    (⁅Q, Q⁆ ⊔ R).map (MulAut.conj g).toMonoidHom ≤ ⁅Q, Q⁆ ⊔ R := by
  rw [Subgroup.map_sup, map_commutator]
  exact sup_le_sup (commutator_mono hQ hQ) hR

theorem mem_normalizer_of_map_le {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set G) :=
  mem_normalizer_fintype fun x hx => h ⟨x, hx, rfl⟩

omit [Finite G] in
theorem map_conj_le_of_forall {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    H.map (MulAut.conj g).toMonoidHom ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

end Generic

section Notation

variable [Finite G]
  {f : ℕ}

theorem exists_caseB_notation (hf : 3 ≤ f) (w : WData d Vi (2 ^ f)) {K : Type} [Field K]
    [Finite K] (hKc : Nat.card K = 2 ^ f) (D : LeviData A Vi K) (hB : w.CaseB D.lev.range)
    (hcomm : ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥) :
    ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) K →* w.Nbar) (W₁ M₁ : Subgroup G)
      (ℓ : Matrix.SpecialLinearGroup (Fin 2) K →* G),
      W₁ ≤ w.W ∧ W₁ ⊓ W₁.map (MulAut.conj d.t).toMonoidHom = ⊥ ∧
      W₁ ⊔ W₁.map (MulAut.conj d.t).toMonoidHom = w.W ∧ Nat.card W₁ = (2 ^ f) ^ 2 ∧
      (∀ v ∈ Vi, ∃! x, x ∈ W₁ ∧ d.t * x * d.t * x⁻¹ = v) ∧
      Function.Injective ℓ ∧ (∀ B, ℓ B ∈ M₁) ∧
      (∀ B, ℓ B * (d.t * ℓ B * d.t) = D.lev B) ∧
      (∀ B B', ℓ B * (d.t * ℓ B' * d.t) = d.t * ℓ B' * d.t * ℓ B) ∧
      (∀ B, ∀ y ∈ W₁.map (MulAut.conj d.t).toMonoidHom, ℓ B * y * (ℓ B)⁻¹ = y) ∧
      (∀ B, ∀ x ∈ W₁, ℓ B * x * (ℓ B)⁻¹ ∈ W₁ ∧
        d.t * (ℓ B * x * (ℓ B)⁻¹) * d.t * (ℓ B * x * (ℓ B)⁻¹)⁻¹ =
          D.lev B * (d.t * x * d.t * x⁻¹) * (D.lev B)⁻¹) ∧
      (∀ B, ∀ x ∈ W₁, (d.t * ℓ B * d.t) * x * (d.t * ℓ B * d.t)⁻¹ = x) ∧
      M₁ ≤ w.N ∧ M₁ ⊓ w.W = W₁ ∧ W₁ ⊔ ℓ.range = M₁ ∧ W₁ ⊓ ℓ.range = ⊥ ∧
      M₁ ⊓ M₁.map (MulAut.conj d.t).toMonoidHom = ⊥ ∧
      (∀ x ∈ M₁, ∀ y ∈ M₁.map (MulAut.conj d.t).toMonoidHom, x * y = y * x) ∧
      (∀ B, ∃ h : ℓ B ∈ w.N, w.projBar ⟨ℓ B, h⟩ = σ B) ∧
      (∀ B B', σ B * (w.tbar * σ B' * w.tbar) = w.tbar * σ B' * w.tbar * σ B) ∧
      Function.Injective σ ∧ (∀ B, σ B ∈ w.Ebar D.lev.range) ∧
      (∀ x ∈ w.Ebar D.lev.range, ∃ B B',
        w.projTil x = w.projTil (σ B * (w.tbar * σ B' * w.tbar))) ∧
      (∀ B B', σ B = w.tbar * σ B' * w.tbar → B = 1) ∧
      M₁ ⊔ M₁.map (MulAut.conj d.t).toMonoidHom =
        preim w (σ.range ⊔ σ.range.map (MulAut.conj w.tbar).toMonoidHom) := by
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hKc
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨σ, W₁, hσinj, hσE, hσc, hσd, -, hσXY, hσon, hW₁W, hW₁₂, hW₁sup, hW₁card, hcenL2, hcenL1,
    hnat, hbij⟩ := exists_caseB_module hf w hKc D hB hcomm
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right d.t_mul_self
  set ct : G →* G := (MulAut.conj d.t).toMonoidHom with hct
  have hct_apply : ∀ x, ct x = d.t * x * d.t := fun x => by
    rw [hct, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htinv]
  have hctct : ∀ x, ct (ct x) = x := fun x => by
    rw [hct_apply, hct_apply]
    calc d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) := by group
      _ = x := by rw [d.t_mul_self, one_mul, mul_one]
  have hmapmap : ∀ H : Subgroup G, (H.map ct).map ct = H := fun H => by
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id H]
    congr 1
    ext x
    exact hctct x
  set W₂ := W₁.map ct with hW₂
  have hWW : w.W.map ct = w.W := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hct_apply]
      have := (mem_normalizer_iff.mp w.t_norm x).mp hx
      rwa [htinv] at this
    · intro x hx
      refine ⟨ct x, ?_, hctct x⟩
      rw [hct_apply]
      have := (mem_normalizer_iff.mp w.t_norm x).mp hx
      rwa [htinv] at this
  have hW₂W : W₂ ≤ w.W := by rw [← hWW]; exact map_mono hW₁W
  set P := preim w σ.range with hP
  set Pt := preim w (σ.range.map (MulAut.conj w.tbar).toMonoidHom) with hPt
  have hmemP : ∀ g, g ∈ P ↔ ∃ hg : g ∈ w.N, ∃ B, w.projBar ⟨g, hg⟩ = σ B := fun g => by
    rw [hP, mem_preim]
    exact ⟨fun ⟨hg, B, hB⟩ => ⟨hg, B, hB.symm⟩, fun ⟨hg, B, hB⟩ => ⟨hg, B, hB.symm⟩⟩
  have htbar : (MulAut.conj w.tbar).toMonoidHom = fun x => w.tbar * x * w.tbar := by
    ext x
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, tbar_inv w]
  have hmemPt : ∀ g, g ∈ Pt ↔ ∃ hg : g ∈ w.N, ∃ B, w.projBar ⟨g, hg⟩ =
      w.tbar * σ B * w.tbar := fun g => by
    rw [hPt, mem_preim]
    constructor
    · rintro ⟨hg, _, ⟨B, rfl⟩, hB⟩
      refine ⟨hg, B, ?_⟩
      rw [← hB, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, tbar_inv w]
    · rintro ⟨hg, B, hB⟩
      refine ⟨hg, σ B, ⟨B, rfl⟩, ?_⟩
      rw [hB, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, tbar_inv w]
  have hpb : ∀ (g h : G) (hg : g ∈ w.N) (hh : h ∈ w.N),
      w.projBar ⟨g * h, mul_mem hg hh⟩ = w.projBar ⟨g, hg⟩ * w.projBar ⟨h, hh⟩ :=
    fun g h hg hh => by rw [← map_mul]; rfl
  have hpbi : ∀ (g : G) (hg : g ∈ w.N), w.projBar ⟨g⁻¹, inv_mem hg⟩ = (w.projBar ⟨g, hg⟩)⁻¹ :=
    fun g hg => by rw [← map_inv]; rfl
  have htN : d.t ∈ w.N := w.t_norm
  have hctN : ∀ g ∈ w.N, ct g ∈ w.N := fun g hg => by
    rw [hct_apply]
    exact mul_mem (mul_mem htN hg) htN
  have hpbct : ∀ (g : G) (hg : g ∈ w.N), w.projBar ⟨ct g, hctN g hg⟩ =
      w.tbar * w.projBar ⟨g, hg⟩ * w.tbar := fun g hg => by
    have e : (⟨ct g, hctN g hg⟩ : w.N) = w.tN * ⟨g, hg⟩ * w.tN := Subtype.ext (hct_apply g)
    rw [e, map_mul, map_mul]
  have hPtP : Pt = P.map ct := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgN, B, hB⟩ := (hmemPt g).mp hg
      refine ⟨ct g, (hmemP _).mpr ⟨hctN g hgN, B, ?_⟩, hctct g⟩
      rw [hpbct g hgN, hB]
      calc w.tbar * (w.tbar * σ B * w.tbar) * w.tbar =
          (w.tbar * w.tbar) * σ B * (w.tbar * w.tbar) := by group
        _ = σ B := by rw [tbar_mul_self w, one_mul, mul_one]
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨hgN, B, hB⟩ := (hmemP g).mp hg
      exact (hmemPt _).mpr ⟨hctN g hgN, B, by rw [hpbct g hgN, hB]⟩
  have hPN : P ≤ w.N := preim_le_N w _
  have hPtN : Pt ≤ w.N := preim_le_N w _
  have hWP : w.W ≤ P := W_le_preim w _
  have hWPt : w.W ≤ Pt := W_le_preim w _
  have hPW₂ : ∀ g ∈ P, ∀ y ∈ W₂, g * y * g⁻¹ = y := fun g hg y hy => by
    obtain ⟨hgN, B, hB⟩ := (hmemP g).mp hg
    exact hcenL1 ⟨g, hgN⟩ B hB y hy
  have hPW₁ : ∀ g ∈ P, ∀ x ∈ W₁, g * x * g⁻¹ ∈ W₁ := fun g hg x hx => by
    obtain ⟨hgN, B, hB⟩ := (hmemP g).mp hg
    exact (hnat ⟨g, hgN⟩ B hB x hx).1
  have hPtW₁ : ∀ g ∈ Pt, ∀ x ∈ W₁, g * x * g⁻¹ = x := fun g hg x hx => by
    obtain ⟨hgN, B, hB⟩ := (hmemPt g).mp hg
    exact hcenL2 ⟨g, hgN⟩ B hB x hx
  have hPtW₂ : ∀ g ∈ Pt, ∀ y ∈ W₂, g * y * g⁻¹ ∈ W₂ := fun g hg y hy => by
    rw [hPtP] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨p * x * p⁻¹, hPW₁ p hp x hx, ?_⟩
    simp only [map_mul, map_inv]
  have hPPt : P ⊓ Pt ≤ w.W := by
    rintro g ⟨hg, hg'⟩
    obtain ⟨hgN, B, hB⟩ := (hmemP g).mp hg
    obtain ⟨hgN', B', hB'⟩ := (hmemPt g).mp hg'
    have h1 : σ B = w.tbar * σ B' * w.tbar := hB.symm.trans hB'
    have h2 := hσXY B B' h1
    rw [h2, map_one] at hB
    exact (w.projBar_eq_one_iff _).mp hB
  have hcommσ : ∀ B B', σ B * (w.tbar * σ B' * w.tbar) = w.tbar * σ B' * w.tbar * σ B := hσc
  have hPtnormP : ∀ g ∈ Pt, P.map (MulAut.conj g).toMonoidHom ≤ P := by
    intro g hg
    apply map_conj_le_of_forall
    intro p hp
    obtain ⟨hgN, B', hB'⟩ := (hmemPt g).mp hg
    obtain ⟨hpN, B, hB⟩ := (hmemP p).mp hp
    refine (hmemP _).mpr ⟨mul_mem (mul_mem hgN hpN) (inv_mem hgN), B, ?_⟩
    rw [hpb _ _ (mul_mem hgN hpN) (inv_mem hgN), hpb _ _ hgN hpN, hpbi _ hgN, hB, hB']
    rw [← hcommσ, mul_inv_cancel_right]
  have hPnormPt : ∀ g ∈ P, Pt.map (MulAut.conj g).toMonoidHom ≤ Pt := by
    intro g hg
    apply map_conj_le_of_forall
    intro p hp
    obtain ⟨hgN, B, hB⟩ := (hmemP g).mp hg
    obtain ⟨hpN, B', hB'⟩ := (hmemPt p).mp hp
    refine (hmemPt _).mpr ⟨mul_mem (mul_mem hgN hpN) (inv_mem hgN), B', ?_⟩
    rw [hpb _ _ (mul_mem hgN hpN) (inv_mem hgN), hpb _ _ hgN hpN, hpbi _ hgN, hB, hB']
    rw [hcommσ, mul_inv_cancel_right]
  have hcommP : ∀ H : Subgroup G, ⁅H, H⁆ ≤ H := fun H =>
    commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  set M₁ : Subgroup G := ⁅P, P⁆ ⊔ W₁ with hM₁
  set M₂ : Subgroup G := M₁.map ct with hM₂
  have hM₂eq : M₂ = ⁅Pt, Pt⁆ ⊔ W₂ := by
    rw [hM₂, hM₁, Subgroup.map_sup, map_commutator, ← hPtP]
  have hM₁P : M₁ ≤ P := sup_le (hcommP P) (hW₁W.trans hWP)
  have hM₂Pt : M₂ ≤ Pt := by
    rw [hM₂eq]
    exact sup_le (hcommP Pt) (hW₂W.trans hWPt)
  have hW₁M₁ : W₁ ≤ M₁ := le_sup_right
  have hW₂M₂ : W₂ ≤ M₂ := by rw [hM₂eq]; exact le_sup_right
  have hK5 : 5 ≤ Nat.card K := by
    rw [hKc]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK9 : Nat.card K ≠ 9 := by
    rw [hKc]
    intro h
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hmult := commutator_preim_inf_le w hK5 hK9 σ hσinj hW₁W hW₁sup
    (fun n ⟨B, hB⟩ => hcenL1 n B hB.symm) (fun n ⟨B, hB⟩ x hx => (hnat n B hB.symm x hx).1)
  have hcPnW₁ : ⁅P, P⁆ ≤ normalizer (W₁ : Set G) := fun g hg =>
    mem_normalizer_of_map_le (map_conj_le_of_forall (hPW₁ g (hcommP P hg)))
  have hM₁W : M₁ ⊓ w.W = W₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hW₁M₁ hW₁W)
    obtain ⟨hxM, hxW⟩ := mem_inf.mp hx
    rw [hM₁, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hcPnW₁, Set.mem_mul] at hxM
    obtain ⟨c, hc, a, ha, rfl⟩ := hxM
    have hcW : c ∈ w.W := by
      have := mul_mem hxW (inv_mem (hW₁W ha))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (hmult ⟨hc, hcW⟩) ha
  have hM₂W : M₂ ⊓ w.W = W₂ := by
    rw [hM₂, ← hWW, ← Subgroup.map_inf_eq _ _ ct (MulAut.conj d.t).injective, hM₁W]
  have hnormM₁P : ∀ g ∈ P, g ∈ normalizer (M₁ : Set G) := fun g hg =>
    mem_normalizer_of_map_le (map_conj_commutator_sup_le
      (map_conj_le_of_forall fun p hp => mul_mem (mul_mem hg hp) (inv_mem hg))
      (map_conj_le_of_forall (hPW₁ g hg)))
  have hnormM₁Pt : ∀ g ∈ Pt, g ∈ normalizer (M₁ : Set G) := fun g hg =>
    mem_normalizer_of_map_le (map_conj_commutator_sup_le (hPtnormP g hg)
      (map_conj_le_of_forall fun x hx => by rw [hPtW₁ g hg x hx]; exact hx))
  have hnormM₂Pt : ∀ g ∈ Pt, g ∈ normalizer (M₂ : Set G) := fun g hg => by
    rw [hM₂eq]
    exact mem_normalizer_of_map_le (map_conj_commutator_sup_le
      (map_conj_le_of_forall fun p hp => mul_mem (mul_mem hg hp) (inv_mem hg))
      (map_conj_le_of_forall (hPtW₂ g hg)))
  have hnormM₂P : ∀ g ∈ P, g ∈ normalizer (M₂ : Set G) := fun g hg => by
    rw [hM₂eq]
    exact mem_normalizer_of_map_le (map_conj_commutator_sup_le (hPnormPt g hg)
      (map_conj_le_of_forall fun y hy => by rw [hPW₂ g hg y hy]; exact hy))
  have hW₁W₂ : W₁ ⊓ W₂ = ⊥ := hW₁₂
  have hM₁M₂ : M₁ ⊓ M₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
    have hxW : x ∈ w.W := hPPt ⟨hM₁P hx₁, hM₂Pt hx₂⟩
    have h1 : x ∈ W₁ := hM₁W ▸ mem_inf.mpr ⟨hx₁, hxW⟩
    have h2 : x ∈ W₂ := hM₂W ▸ mem_inf.mpr ⟨hx₂, hxW⟩
    rw [← hW₁W₂]
    exact mem_inf.mpr ⟨h1, h2⟩
  have hcomm₁₂ : ∀ x ∈ M₁, ∀ y ∈ M₂, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ M₂ :=
      mul_mem ((mem_normalizer_iff.mp (hnormM₂P x (hM₁P hx)) y).mp hy) (inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ M₁ := by
      rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
      exact mul_mem hx ((mem_normalizer_iff.mp (hnormM₁Pt y (hM₂Pt hy)) x⁻¹).mp (inv_mem hx))
    have h3 : x * y * x⁻¹ * y⁻¹ = 1 := by
      have : x * y * x⁻¹ * y⁻¹ ∈ M₁ ⊓ M₂ := mem_inf.mpr ⟨h2, h1⟩
      rwa [hM₁M₂, mem_bot] at this
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ := by
    obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) (by omega)
    exact Matrix.SL2.commutator_eq_top μ.ne_zero (sq_ne_one_of_charTwo hμ)
  set PN : Subgroup w.N := σ.range.comap w.projBar
  have hPPN : P = PN.map w.N.subtype := rfl
  have hPNmap : PN.map w.projBar = σ.range :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hσperf : ⁅σ.range, σ.range⁆ = σ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def, hperf]
  have hWM : w.W ≤ M₁ ⊔ M₂ := by rw [← hW₁sup]; exact sup_le_sup hW₁M₁ hW₂M₂
  have hPle : P ≤ M₁ ⊔ M₂ := by
    intro p hp
    obtain ⟨hpN, B, hB⟩ := (hmemP p).mp hp
    have hσB : σ B ∈ (⁅PN, PN⁆).map w.projBar := by
      rw [map_commutator, hPNmap, hσperf]
      exact ⟨B, rfl⟩
    obtain ⟨c, hc, hcB⟩ := hσB
    have hcP : (c : G) ∈ ⁅P, P⁆ := by
      rw [hPPN, ← map_commutator]
      exact ⟨c, hc, rfl⟩
    have hcp : (c : G)⁻¹ * p ∈ w.W := by
      have : w.projBar (c⁻¹ * ⟨p, hpN⟩) = 1 := by rw [map_mul, map_inv, hcB, hB, inv_mul_cancel]
      exact (w.projBar_eq_one_iff _).mp this
    have e : p = (c : G) * ((c : G)⁻¹ * p) := by group
    rw [e]
    exact mul_mem (mem_sup_left (mem_sup_left hcP)) (hWM hcp)
  have hM₂M₁ : M₂.map ct = M₁ := hmapmap M₁
  have hPtle : Pt ≤ M₁ ⊔ M₂ := by
    rw [hPtP]
    have := map_mono (f := ct) hPle
    rwa [Subgroup.map_sup, hM₂M₁, sup_comm] at this
  have hlevMM : ∀ B, D.lev B ∈ M₁ ⊔ M₂ := by
    intro B
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective w.WN (σ B)
    have hn' : w.projBar ⟨(n : G), n.2⟩ = σ B := hn
    have hnP : (n : G) ∈ P := (hmemP _).mpr ⟨n.2, B, hn'⟩
    have hlevN := w.lev_mem_N D B
    have hq : D.lev B * (n : G)⁻¹ ∈ Pt := by
      refine (hmemPt _).mpr ⟨mul_mem hlevN (inv_mem n.2), B, ?_⟩
      rw [hpb _ _ hlevN (inv_mem n.2), hpbi _ n.2, ← levQ_apply, ← hσd, hn', hcommσ, mul_assoc,
        mul_inv_cancel, mul_one]
    have e : D.lev B = (D.lev B * (n : G)⁻¹) * n := by group
    rw [e]
    exact mul_mem (hPtle hq) (hPle hnP)
  let φ : M₁ × M₂ →* G := M₁.subtype.noncommCoprod M₂.subtype fun a b => hcomm₁₂ a a.2 b b.2
  have hφinj : Function.Injective φ :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr ⟨subtype_injective _, subtype_injective _, by
      rw [range_subtype, range_subtype, disjoint_iff]
      exact hM₁M₂⟩
  have hφrange : φ.range = M₁ ⊔ M₂ := by
    rw [show φ.range = _ from MonoidHom.noncommCoprod_range _ _ _, range_subtype, range_subtype]
  let e := MonoidHom.ofInjective hφinj
  let levR : Matrix.SpecialLinearGroup (Fin 2) K →* φ.range :=
    D.lev.codRestrict φ.range fun B => hφrange ▸ hlevMM B
  let ℓ₀ : Matrix.SpecialLinearGroup (Fin 2) K →* M₁ :=
    (MonoidHom.fst M₁ M₂).comp (e.symm.toMonoidHom.comp levR)
  let ℓ₂ : Matrix.SpecialLinearGroup (Fin 2) K →* M₂ :=
    (MonoidHom.snd M₁ M₂).comp (e.symm.toMonoidHom.comp levR)
  have hdec : ∀ B, (ℓ₀ B : G) * ℓ₂ B = D.lev B := fun B => by
    have h := congrArg Subtype.val (e.apply_symm_apply (levR B))
    rw [MonoidHom.ofInjective_apply] at h
    exact h
  have hφeq : ∀ (a b : M₁) (c c' : M₂), (a : G) * c = (b : G) * c' → a = b ∧ c = c' := by
    intro a b c c' h
    have h' := @hφinj (a, c) (b, c') h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hctM₁ : ∀ x ∈ M₁, ct x ∈ M₂ := fun x hx => ⟨x, hx, rfl⟩
  have hctM₂ : ∀ y ∈ M₂, ct y ∈ M₁ := fun y hy => by
    rw [← hM₂M₁]
    exact ⟨y, hy, rfl⟩
  have hlevt : ∀ B, ct (D.lev B) = D.lev B := fun B => by
    rw [hct_apply, ← d.comm_t_of_mem (D.lev_mem B), mul_assoc, d.t_mul_self, mul_one]
  have hℓ₂ : ∀ B, (ℓ₂ B : G) = ct (ℓ₀ B) := by
    intro B
    have h1 : (ℓ₀ B : G) * ℓ₂ B = ct (ℓ₂ B) * ct (ℓ₀ B) := by
      rw [hdec, ← hlevt, ← hdec, map_mul]
      exact hcomm₁₂ _ (hctM₂ _ (ℓ₂ B).2) _ (hctM₁ _ (ℓ₀ B).2) ▸
        (hcomm₁₂ _ (hctM₂ _ (ℓ₂ B).2) _ (hctM₁ _ (ℓ₀ B).2)).symm
    have h2 := hφeq (ℓ₀ B) ⟨ct (ℓ₂ B), hctM₂ _ (ℓ₂ B).2⟩ (ℓ₂ B) ⟨ct (ℓ₀ B), hctM₁ _ (ℓ₀ B).2⟩ h1
    exact congrArg Subtype.val h2.2
  set ℓ : Matrix.SpecialLinearGroup (Fin 2) K →* G := M₁.subtype.comp ℓ₀ with hℓ
  have hℓapply : ∀ B, ℓ B = (ℓ₀ B : G) := fun B => rfl
  have hℓM₁ : ∀ B, ℓ B ∈ M₁ := fun B => (ℓ₀ B).2
  have hℓdiag : ∀ B, ℓ B * (d.t * ℓ B * d.t) = D.lev B := fun B => by
    rw [hℓapply, ← hct_apply, ← hℓ₂, hdec]
  have hℓN : ∀ B, ℓ B ∈ w.N := fun B => hPN (hM₁P (hℓM₁ B))
  have hℓbar : ∀ B, w.projBar ⟨ℓ B, hℓN B⟩ = σ B := by
    intro B
    obtain ⟨hN', B', hB'⟩ := (hmemP _).mp (hM₁P (hℓM₁ B))
    have h1 : levQ w D B = levQ w D B' := by
      rw [levQ_apply, ← hσd]
      have e : (⟨D.lev B, w.lev_mem_N D B⟩ : w.N) =
          ⟨ℓ B, hN'⟩ * ⟨ct (ℓ B), hctN _ hN'⟩ := Subtype.ext (by
        change D.lev B = ℓ B * ct (ℓ B)
        rw [hct_apply, hℓdiag])
      rw [e, map_mul, hpbct _ hN', hB']
    have h2 := levQ_injective w D h1
    subst h2
    exact hB'
  refine ⟨σ, W₁, M₁, ℓ, hW₁W, hW₁₂, hW₁sup, hW₁card, hbij, ?_, hℓM₁, hℓdiag, ?_, ?_, ?_, ?_,
    hM₁P.trans hPN, hM₁W, ?_, ?_, hM₁M₂, hcomm₁₂, fun B => ⟨hℓN B, hℓbar B⟩, hσc, hσinj,
    hσE, hσon, hσXY, ?_⟩
  ·
    rw [injective_iff_map_eq_one]
    intro B hB1
    apply D.lev_injective
    rw [map_one, ← hdec, ← hℓapply, hB1, hℓ₂, ← hℓapply, hB1, map_one, mul_one]
  ·
    intro B B'
    rw [← hct_apply]
    exact hcomm₁₂ _ (hℓM₁ B) _ (hctM₁ _ (hℓM₁ B'))
  ·
    intro B y hy
    rw [hcomm₁₂ _ (hℓM₁ B) _ (hW₂M₂ hy), mul_inv_cancel_right]
  ·
    intro B x hx
    exact hnat ⟨ℓ B, hℓN B⟩ B (hℓbar B) x hx
  ·
    intro B x hx
    rw [← hct_apply, ← hcomm₁₂ _ (hW₁M₁ hx) _ (hctM₁ _ (hℓM₁ B)), mul_inv_cancel_right]
  ·
    refine le_antisymm (sup_le hW₁M₁ ?_) fun m hm => ?_
    · rintro _ ⟨B, rfl⟩
      exact hℓM₁ B
    · obtain ⟨hmN, B, hB⟩ := (hmemP m).mp (hM₁P hm)
      have h1 : (ℓ B)⁻¹ * m ∈ M₁ ⊓ w.W := by
        refine mem_inf.mpr ⟨mul_mem (inv_mem (hℓM₁ B)) hm,
          (w.projBar_eq_one_iff ((⟨ℓ B, hℓN B⟩ : w.N)⁻¹ * ⟨m, hmN⟩)).mp ?_⟩
        rw [map_mul, map_inv, hℓbar, hB, inv_mul_cancel]
      rw [hM₁W] at h1
      have e : m = (ℓ B)⁻¹⁻¹ * ((ℓ B)⁻¹ * m) := by group
      rw [e, inv_inv]
      exact mul_mem (mem_sup_right ⟨B, rfl⟩) (mem_sup_left h1)
  ·
    rw [eq_bot_iff]
    rintro _ ⟨hx, ⟨B, rfl⟩⟩
    have h1 : w.projBar ⟨ℓ B, hℓN B⟩ = 1 := (w.projBar_eq_one_iff _).mpr (hW₁W hx)
    rw [hℓbar] at h1
    have h2 : B = 1 := hσinj (by rw [h1, map_one])
    rw [h2, map_one]
    exact one_mem _
  ·
    have hXY : σ.range ≤
        normalizer ((σ.range.map (MulAut.conj w.tbar).toMonoidHom) : Set w.Nbar) := by
      rintro _ ⟨B, rfl⟩
      refine mem_normalizer_fintype fun y hy => ?_
      obtain ⟨_, ⟨B', rfl⟩, rfl⟩ := hy
      have e : (MulAut.conj w.tbar).toMonoidHom (σ B') = w.tbar * σ B' * w.tbar := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, tbar_inv w]
      rw [e, hcommσ, mul_inv_cancel_right, ← e]
      exact ⟨σ B', ⟨B', rfl⟩, rfl⟩
    refine le_antisymm (sup_le (hM₁P.trans ?_) (hM₂Pt.trans ?_)) fun g hg => ?_
    · intro x hx
      obtain ⟨hxN, hxX⟩ := (mem_preim w _).mp hx
      exact (mem_preim w _).mpr ⟨hxN, mem_sup_left hxX⟩
    · intro x hx
      obtain ⟨hxN, hxX⟩ := (mem_preim w _).mp hx
      exact (mem_preim w _).mpr ⟨hxN, mem_sup_right hxX⟩
    · obtain ⟨hgN, hgX⟩ := (mem_preim w _).mp hg
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hXY, Set.mem_mul] at hgX
      obtain ⟨_, ⟨B, rfl⟩, y, hy, hxy⟩ := hgX
      obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective w.WN (σ B)
      have hn' : w.projBar ⟨(n : G), n.2⟩ = σ B := hn
      have hnP : (n : G) ∈ P := (hmemP _).mpr ⟨n.2, B, hn'⟩
      have hq : (n : G)⁻¹ * g ∈ Pt := by
        refine (mem_preim w _).mpr ⟨mul_mem (inv_mem n.2) hgN, ?_⟩
        rw [hpb _ _ (inv_mem n.2) hgN, hpbi _ n.2, hn', ← hxy, inv_mul_cancel_left]
        exact hy
      have e : g = (n : G) * ((n : G)⁻¹ * g) := by group
      rw [e]
      exact mul_mem (hPle hnP) (hPtle hq)

end Notation

end CaseBModule

end CFSG.LocalAnalysis.EvenBN.LinearThree
