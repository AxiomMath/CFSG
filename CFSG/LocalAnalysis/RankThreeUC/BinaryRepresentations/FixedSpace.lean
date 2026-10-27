module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

variable {G : Type} [Group G]

variable {q : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod q) V]

@[expose] noncomputable def fixedSpace (ρ : Representation (ZMod q) G V) (D : Subgroup G) : Submodule (ZMod q) V :=
  Representation.invariants (MonoidHom.comp ρ D.subtype)

@[expose] def commSpace (ρ : Representation (ZMod q) G V) (X : Subgroup G) : Submodule (ZMod q) V :=
  Submodule.span (ZMod q) {w | ∃ x ∈ X, ∃ v : V, w = ρ x v - v}

@[expose] def hyperplanes (p : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  {D | D ≤ A ∧ D.relIndex A = p}

theorem mem_fixedSpace_iff (ρ : Representation (ZMod q) G V) (D : Subgroup G) (v : V) :
    v ∈ fixedSpace ρ D ↔ ∀ d ∈ D, ρ d v = v := by
  unfold fixedSpace
  rw [Representation.mem_invariants]
  exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d d.2⟩

theorem rho_mul_apply (ρ : Representation (ZMod q) G V) (g h : G) (v : V) :
    ρ (g * h) v = ρ g (ρ h v) := by rw [map_mul]; rfl

@[expose] noncomputable def normOp (ρ : Representation (ZMod q) G V) (B : Subgroup G) [Fintype B] :
    V →ₗ[ZMod q] V := ∑ b : B, ρ b

theorem normOp_apply (ρ : Representation (ZMod q) G V) (B : Subgroup G) [Fintype B] (v : V) :
    normOp ρ B v = ∑ b : B, ρ b v := by
  unfold normOp; simp [LinearMap.sum_apply]

theorem normOp_of_mem_fixedSpace (ρ : Representation (ZMod q) G V) (B : Subgroup G) [Fintype B]
    {v : V} (hv : v ∈ fixedSpace ρ B) : normOp ρ B v = (Fintype.card B : ZMod q) • v := by
  rw [normOp_apply]
  rw [mem_fixedSpace_iff] at hv
  simp [fun b : B => hv b b.2, Finset.card_univ, Nat.cast_smul_eq_nsmul]

theorem mem_fixedSpace_normOp (ρ : Representation (ZMod q) G V) (B : Subgroup G) [Fintype B]
    (v : V) : normOp ρ B v ∈ fixedSpace ρ B := by
  rw [mem_fixedSpace_iff]
  intro d hd
  rw [normOp_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨d, hd⟩ : B)) _ _ (fun b => ?_)
  simp [rho_mul_apply]

theorem normOp_comm (ρ : Representation (ZMod q) G V) (B : Subgroup G) [Fintype B]
    {g : G} (hg : ∀ b ∈ B, g * b = b * g) (v : V) :
    ρ g (normOp ρ B v) = normOp ρ B (ρ g v) := by
  rw [normOp_apply, normOp_apply, map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← rho_mul_apply, hg b b.2, rho_mul_apply]

theorem normOp_commSpace (ρ : Representation (ZMod q) G V) (B : Subgroup G) [Fintype B]
    {w : V} (hw : w ∈ commSpace ρ B) : normOp ρ B w = 0 := by
  have key : ∀ x ∈ B, ∀ v : V, normOp ρ B (ρ x v - v) = 0 := by
    intro x hx v
    rw [map_sub, sub_eq_zero, normOp_apply, normOp_apply]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨x, hx⟩ : B)) _ _ (fun b => ?_)
    simp [rho_mul_apply]
  unfold commSpace at hw
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨x, hx, v, rfl⟩ := hw; exact key x hx v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

theorem fixedSpace_eq_bot [Fact q.Prime] (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Fintype A]
    (hq : (Fintype.card A : ZMod q) ≠ 0) (hV : commSpace ρ A = ⊤) :
    fixedSpace ρ A = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have h1 := normOp_of_mem_fixedSpace ρ A hv
  have h2 := normOp_commSpace ρ A (hV ▸ Submodule.mem_top (x := v))
  rw [h2] at h1
  rcases smul_eq_zero.mp h1.symm with h | h
  · exact absurd h hq
  · simp [h]

theorem mem_fixedSpace_sup (ρ : Representation (ZMod q) G V) (D B : Subgroup G) {v : V}
    (hD : v ∈ fixedSpace ρ D) (hB : v ∈ fixedSpace ρ B) : v ∈ fixedSpace ρ (D ⊔ B) := by
  let S : Subgroup G :=
    { carrier := {g | ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [rho_mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        have : ρ a⁻¹ (ρ a v) = v := by rw [← rho_mul_apply]; simp
        rwa [ha] at this }
  rw [mem_fixedSpace_iff] at *
  have : D ⊔ B ≤ S := sup_le (fun d hd => hD d hd) (fun b hb => hB b hb)
  exact fun g hg => this hg

theorem normOp_eq_zero_of_fixedSpace (ρ : Representation (ZMod q) G V) (A D B : Subgroup G)
    [Fintype B] (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hDA : D ≤ A) (hBA : B ≤ A)
    (hsup : D ⊔ B = A) (hfix : fixedSpace ρ A = ⊥) {v : V} (hv : v ∈ fixedSpace ρ D) :
    normOp ρ B v = 0 := by
  have hB := mem_fixedSpace_normOp ρ B v
  have hD : normOp ρ B v ∈ fixedSpace ρ D := by
    rw [mem_fixedSpace_iff] at hv ⊢
    intro d hd
    rw [normOp_comm ρ B (fun b hb => hcomm d (hDA hd) b (hBA hb)), hv d hd]
  have := mem_fixedSpace_sup ρ D B hD hB
  rw [hsup, hfix] at this
  simpa using this

theorem sup_eq_of_hyperplanes {p : ℕ} [Fact p.Prime] {A D B : Subgroup G}
    (hD : D ∈ hyperplanes p A) (hB : B ∈ hyperplanes p A) (hne : D ≠ B) : D ⊔ B = A := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨hDA, hDi⟩ := hD
  obtain ⟨hBA, hBi⟩ := hB
  have hle : D ⊔ B ≤ A := sup_le hDA hBA
  have h1 := Subgroup.relIndex_mul_relIndex D (D ⊔ B) A le_sup_left hle
  rw [hDi] at h1
  have hdvd : (D ⊔ B).relIndex A ∣ p := ⟨_, by rw [← h1]; ring⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact le_antisymm hle (Subgroup.relIndex_eq_one.1 h)
  · exfalso
    rw [h] at h1
    have h2 : D.relIndex (D ⊔ B) = 1 := by
      have := hp.pos
      nlinarith
    have hBD : B ≤ D := le_trans le_sup_right (Subgroup.relIndex_eq_one.1 h2)
    have h3 := Subgroup.relIndex_mul_relIndex B D A hBD hDA
    rw [hBi, hDi] at h3
    have h4 : B.relIndex D = 1 := by
      have := hp.pos
      nlinarith
    exact hne (le_antisymm (Subgroup.relIndex_eq_one.1 h4) hBD)

theorem natCard_ne_zero_of_le {p : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {A B : Subgroup G} [Finite A] (hA : CFSG.Open.IsElemAbelian p A) (hBA : B ≤ A) :
    (Nat.card B : ZMod q) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have hpg : IsPGroup p A := fun g => ⟨1, by
    have := hA.2 g g.2
    simpa using Subtype.ext this⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hdvd : Nat.card B ∣ Nat.card A := Subgroup.card_dvd_of_le hBA
  rw [hn] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rw [hk, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hp).1 (Nat.Prime.dvd_of_dvd_pow (Fact.out : q.Prime) h)).symm

theorem fixedSpace_eq_bot_of_hyp {p : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Finite A]
    (hA : CFSG.Open.IsElemAbelian p A) (hV : commSpace ρ A = ⊤) : fixedSpace ρ A = ⊥ := by
  haveI := Fintype.ofFinite A
  refine fixedSpace_eq_bot ρ A ?_ hV
  have := natCard_ne_zero_of_le hpq hA (le_refl A)
  rwa [Nat.card_eq_fintype_card] at this

theorem iSupIndep_fixedSpace {p : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Finite A]
    (hA : CFSG.Open.IsElemAbelian p A) (hV : commSpace ρ A = ⊤) :
    iSupIndep (fun D : hyperplanes p A => fixedSpace ρ D.1) := by
  have hfix := fixedSpace_eq_bot_of_hyp hpq ρ A hA hV
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => by
    have := hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  intro B
  rw [Submodule.disjoint_def]
  intro v hvB hvsup
  haveI : Finite B.1 := Finite.of_injective (Subgroup.inclusion B.2.1) (Subgroup.inclusion_injective B.2.1)
  haveI := Fintype.ofFinite B.1
  have hker : (⨆ j ≠ B, fixedSpace ρ j.1) ≤ LinearMap.ker (normOp ρ B.1) := by
    refine iSup₂_le (fun j hj => fun w hw => ?_)
    rw [LinearMap.mem_ker]
    exact normOp_eq_zero_of_fixedSpace ρ A j.1 B.1 hcomm j.2.1 B.2.1
      (sup_eq_of_hyperplanes j.2 B.2 (fun h => hj (Subtype.ext h))) hfix hw
  have h0 := normOp_of_mem_fixedSpace ρ B.1 hvB
  rw [LinearMap.mem_ker.1 (hker hvsup)] at h0
  have hc : (Fintype.card B.1 : ZMod q) ≠ 0 := by
    have := natCard_ne_zero_of_le hpq hA B.2.1
    rwa [Nat.card_eq_fintype_card] at this
  rcases smul_eq_zero.mp h0.symm with h | h
  · exact absurd h hc
  · exact h

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC

namespace CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.Gen

section LA

variable {F : Type*} [Field F] [Finite F] {E : Type*} [AddCommGroup E] [Module F E] [Finite E]

theorem dual_ker_card (a : E) (ha : a ≠ 0) :
    Nat.card {f : (E →ₗ[F] F) // f a = 0} * Nat.card F = Nat.card (E →ₗ[F] F) := by
  let ev : (E →ₗ[F] F) →ₗ[F] F := LinearMap.applyₗ a
  have hs : Function.Surjective ev := by
    obtain ⟨φ, hφ⟩ : ∃ φ : (E →ₗ[F] F), φ a ≠ 0 := by
      by_contra h
      push Not at h
      exact ha ((Module.forall_dual_apply_eq_zero_iff F a).1 h)
    intro c
    exact ⟨(c / φ a) • φ, by simp [ev, hφ]⟩
  have e1 : ((E →ₗ[F] F) ⧸ LinearMap.ker ev) ≃ₗ[F] F := LinearMap.quotKerEquivOfSurjective ev hs
  have e2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker ev)
  rw [Nat.card_congr e1.toEquiv] at e2
  rw [e2]
  congr 1

theorem dual_zero_card [Fintype (E →ₗ[F] F)] [DecidableEq (E →ₗ[F] F)] (a : E) [DecidablePred (fun f : E →ₗ[F] F => f a = 0)] :
    (Finset.univ.filter (fun f : (E →ₗ[F] F) => f a = 0 ∧ f ≠ 0)).card + 1 =
      (Finset.univ.filter (fun f : (E →ₗ[F] F) => f a = 0)).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun f : (E →ₗ[F] F) => f a = 0)) (fun f => f = 0)
  have h1 : (Finset.univ.filter (fun f : (E →ₗ[F] F) => f a = 0)).filter (fun f => f = 0) = {0} := by
    ext f; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; simp
  have h2 : (Finset.univ.filter (fun f : (E →ₗ[F] F) => f a = 0)).filter (fun f => ¬ f = 0) =
      Finset.univ.filter (fun f : (E →ₗ[F] F) => f a = 0 ∧ f ≠ 0) := by
    ext f; simp [Finset.mem_filter]
  rw [h1, h2] at h
  simpa [add_comm] using h

theorem fibre_card [Fintype (E →ₗ[F] F)] [DecidableEq (E →ₗ[F] F)] (f0 : E →ₗ[F] F) (h0 : f0 ≠ 0)
    [DecidablePred (fun g : E →ₗ[F] F => g ≠ 0 ∧ LinearMap.ker g = LinearMap.ker f0)] [Fintype F] [DecidableEq F] :
    (Finset.univ.filter (fun g : (E →ₗ[F] F) => g ≠ 0 ∧ LinearMap.ker g = LinearMap.ker f0)).card + 1 = Fintype.card F := by
  have hc : ((Finset.univ : Finset F).filter (fun c => c ≠ 0)).card + 1 = Fintype.card F := by
    rw [Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have := Fintype.card_pos (α := F)
    omega
  rw [← hc]
  congr 1
  have : (Finset.univ.filter (fun g : (E →ₗ[F] F) => g ≠ 0 ∧ LinearMap.ker g = LinearMap.ker f0)) =
      ((Finset.univ : Finset F).filter (fun c => c ≠ 0)).image (fun c => c • f0) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hg, hk⟩
      obtain ⟨x, hx⟩ : ∃ x, f0 x ≠ 0 := by
        by_contra h; push Not at h; exact h0 (LinearMap.ext h)
      have hgx : g x ≠ 0 := by
        intro h
        apply hx
        have : x ∈ LinearMap.ker g := h
        rw [hk] at this
        exact this
      refine ⟨g x / f0 x, div_ne_zero hgx hx, ?_⟩
      symm
      refine Module.Dual.eq_of_ker_eq_of_apply_eq x ?_ ?_ ?_
      · rw [hk]
        ext y
        simp [hx, hgx]
      · simp [hx]
      · simp [hx, hgx]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · intro h
        apply h0
        have := congrArg (fun f => c⁻¹ • f) h
        simpa [hc] using this
      · ext y
        simp [hc]
  rw [this, Finset.card_image_of_injective _ (smul_left_injective F h0)]

end LA

end CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.Gen

namespace CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.Gen

section

variable {G : Type} [Group G] {F : Type*} [Field F] {E : Type*} [AddCommGroup E] [Module F E] {A : Subgroup G}

@[expose] noncomputable def psi (e : Multiplicative E ≃* A) (f : E →ₗ[F] F) : A →* Multiplicative F :=
  (AddMonoidHom.toMultiplicative (f : E →+ F)).comp e.symm.toMonoidHom

theorem psi_apply (e : Multiplicative E ≃* A) (f : E →ₗ[F] F) (a : A) :
    psi e f a = Multiplicative.ofAdd (f (Multiplicative.toAdd (e.symm a))) := rfl

@[expose] noncomputable def hyp (e : Multiplicative E ≃* A) (f : E →ₗ[F] F) : Subgroup G :=
  (psi e f).ker.map A.subtype

theorem mem_hyp (e : Multiplicative E ≃* A) (f : E →ₗ[F] F) (a : A) :
    (a : G) ∈ hyp e f ↔ f (Multiplicative.toAdd (e.symm a)) = 0 := by
  unfold hyp
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, hba⟩
    have : b = a := Subtype.ext hba
    subst this
    simpa [psi_apply] using hb
  · intro h
    exact ⟨a, by simpa [psi_apply] using h, rfl⟩

theorem hyp_le (e : Multiplicative E ≃* A) (f : E →ₗ[F] F) : hyp e f ≤ A :=
  Subgroup.map_subtype_le _

theorem mem_hyp_iff (e : Multiplicative E ≃* A) (f : E →ₗ[F] F) (g : G) :
    g ∈ hyp e f ↔ ∃ h : g ∈ A, f (Multiplicative.toAdd (e.symm ⟨g, h⟩)) = 0 := by
  constructor
  · intro hg
    have hA := hyp_le e f hg
    exact ⟨hA, (mem_hyp e f ⟨g, hA⟩).1 hg⟩
  · rintro ⟨hA, h⟩
    exact (mem_hyp e f ⟨g, hA⟩).2 h

theorem hyp_eq_iff (e : Multiplicative E ≃* A) (f g : E →ₗ[F] F) :
    hyp e f = hyp e g ↔ LinearMap.ker f = LinearMap.ker g := by
  constructor
  · intro h
    ext y
    have := mem_hyp e f (e (Multiplicative.ofAdd y))
    have h2 := mem_hyp e g (e (Multiplicative.ofAdd y))
    rw [h] at this
    simp only [MulEquiv.symm_apply_apply, toAdd_ofAdd] at this h2
    simpa using this.symm.trans h2
  · intro h
    ext x
    rw [mem_hyp_iff, mem_hyp_iff]
    constructor <;> rintro ⟨hA, hx⟩ <;> refine ⟨hA, ?_⟩
    · have : _ ∈ LinearMap.ker f := hx
      rw [h] at this; exact this
    · have : _ ∈ LinearMap.ker g := hx
      rw [← h] at this; exact this

theorem relIndex_hyp {p : ℕ} (hF : Nat.card F = p) (e : Multiplicative E ≃* A) (f : E →ₗ[F] F) (hf : f ≠ 0) :
    (hyp e f).relIndex A = p := by
  unfold Subgroup.relIndex hyp
  have hsub : (Subgroup.map A.subtype (psi e f).ker).subgroupOf A = (psi e f).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hbx⟩
      have : b = x := Subtype.ext hbx
      rwa [← this]
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [hsub, Subgroup.index_ker]
  have : (psi e f).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro c
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h; push Not at h; exact hf (LinearMap.ext h)
    refine ⟨e (Multiplicative.ofAdd ((Multiplicative.toAdd c / f x) • x)), ?_⟩
    rw [psi_apply]
    simp [hx]
  rw [this, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, hF]

end

section

variable {G : Type} [Group G] {q : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod q) V]

open Classical in
@[expose] noncomputable def S (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Fintype A] (D : Subgroup G) (v : V) : V :=
  ∑ a : A, if (a : G) ∈ D then ρ a v else 0

theorem S_mem_fixed (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Fintype A] (D : Subgroup G)
    (hD : D ≤ A) (v : V) : S ρ A D v ∈ fixedSpace ρ D := by
  classical
  rw [mem_fixedSpace_iff]
  intro d hd
  unfold S
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨d, hD hd⟩ : A)) _ _ (fun a => ?_)
  have h1 : ((⟨d, hD hd⟩ * a : A) : G) ∈ D ↔ (a : G) ∈ D := by
    change d * (a : G) ∈ D ↔ _
    exact ⟨fun h => by simpa using D.mul_mem (D.inv_mem hd) h, fun h => D.mul_mem hd h⟩
  by_cases ha : (a : G) ∈ D
  · rw [if_pos ha, Equiv.coe_mulLeft, if_pos (h1.2 ha)]
    exact (rho_mul_apply ρ d a v).symm
  · rw [if_neg ha, Equiv.coe_mulLeft, if_neg (mt h1.1 ha), map_zero]

open Classical in
theorem sum_S (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Fintype A] (Δ : Finset (Subgroup G)) (v : V) :
    ∑ D ∈ Δ, S ρ A D v = ∑ a : A, (Δ.filter (fun D => (a : G) ∈ D)).card • ρ a v := by
  classical
  unfold S
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]

end

section

variable {G : Type} [Group G] {q : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod q) V]

theorem gen_aux {p : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Finite A]
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = p)
    {E : Type*} [AddCommGroup E] [Module F E] [Finite E]
    (e : Multiplicative E ≃* A) (hV : commSpace ρ A = ⊤) :
    (⨆ D : hyperplanes p A, fixedSpace ρ D.1) = ⊤ := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Module.Finite F E := inferInstance
  haveI : Finite (E →ₗ[F] F) := Module.finite_of_finite F
  haveI : Fintype (E →ₗ[F] F) := Fintype.ofFinite _
  have hp := (Fact.out : p.Prime)
  rw [eq_top_iff]
  intro v _
  by_cases hE : Subsingleton E
  · have hv : v ∈ commSpace ρ A := hV ▸ Submodule.mem_top
    have hz : commSpace ρ A ≤ ⊥ := by
      unfold commSpace
      refine Submodule.span_le.2 ?_
      rintro w ⟨x, hx, v', rfl⟩
      have : (⟨x, hx⟩ : A) = 1 := by
        haveI : Subsingleton (Multiplicative E) := inferInstanceAs (Subsingleton E)
        haveI : Subsingleton A := e.toEquiv.symm.subsingleton
        exact Subsingleton.elim _ _
      have h1 : x = 1 := congrArg Subtype.val this
      subst h1
      simp
    have := hz hv
    rw [Submodule.mem_bot] at this
    rw [this]; exact Submodule.zero_mem _
  rw [not_subsingleton_iff_nontrivial] at hE
  obtain ⟨a0, ha0⟩ : ∃ a0 : E, a0 ≠ 0 := exists_ne 0
  obtain ⟨f1, hf1⟩ : ∃ f : E →ₗ[F] F, f a0 ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 ((Module.forall_dual_apply_eq_zero_iff F a0).1 h)
  have hf1' : f1 ≠ 0 := fun h => hf1 (by simp [h])
  let Δ' : Finset (Subgroup G) := (Finset.univ.filter (fun f : E →ₗ[F] F => f ≠ 0)).image (hyp e)
  have hΔ : ∀ D ∈ Δ', D ∈ hyperplanes p A := by
    intro D hD
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hD
    exact ⟨hyp_le e f, relIndex_hyp hF e f (Finset.mem_filter.1 hf).2⟩
  have hD0 : hyp e f1 ∈ Δ' := Finset.mem_image.2 ⟨f1, by simp [hf1'], rfl⟩
  have hWle : ∀ D ∈ hyperplanes p A, fixedSpace ρ D ≤ (⨆ D : hyperplanes p A, fixedSpace ρ D.1) :=
    fun D hD => le_iSup (fun D : hyperplanes p A => fixedSpace ρ D.1) ⟨D, hD⟩
  have hNd : Nat.card (E →ₗ[F] F) = p ^ (Module.finrank F (E →ₗ[F] F)) := by
    have hFcard : Fintype.card F = p := by rw [← hF, Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := E →ₗ[F] F), hFcard]
  obtain ⟨r, hr⟩ : ∃ r, Module.finrank F (E →ₗ[F] F) = r + 1 := by
    rcases Nat.eq_zero_or_pos (Module.finrank F (E →ₗ[F] F)) with h | h
    · exfalso
      rw [h, pow_zero, Nat.card_eq_one_iff_unique] at hNd
      obtain ⟨hs, _⟩ := hNd
      exact hf1' (Subsingleton.elim _ _)
    · exact ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  rw [hr, pow_succ'] at hNd
  set t := p ^ r with ht
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hkpos : 0 < k := by have := hp.two_le; omega
  have hFcard : Fintype.card F = p := by rw [← hF, Nat.card_eq_fintype_card]
  let cnt : A → ℕ := fun a => (Δ'.filter (fun D => (a : G) ∈ D)).card
  have key : ∀ a : A, cnt a * k =
      (Finset.univ.filter (fun f : E →ₗ[F] F => f ≠ 0 ∧ f (Multiplicative.toAdd (e.symm a)) = 0)).card := by
    intro a
    have H : ∀ f ∈ Finset.univ.filter (fun f : E →ₗ[F] F => f ≠ 0 ∧ f (Multiplicative.toAdd (e.symm a)) = 0),
        hyp e f ∈ Δ'.filter (fun D => (a : G) ∈ D) := by
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨f, by simp [hf.1], rfl⟩, ?_⟩
      exact (mem_hyp e f a).2 hf.2
    rw [Finset.card_eq_sum_card_fiberwise H]
    rw [Finset.sum_congr rfl (g := fun _ => k)]
    · rw [Finset.sum_const, smul_eq_mul]
    · intro D hD
      obtain ⟨hDΔ, haD⟩ := Finset.mem_filter.1 hD
      obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hDΔ
      have hf0' : f0 ≠ 0 := (Finset.mem_filter.1 hf0).2
      have hfib := fibre_card f0 hf0'
      rw [hFcard] at hfib
      have : (Finset.univ.filter (fun f : E →ₗ[F] F => f ≠ 0 ∧ f (Multiplicative.toAdd (e.symm a)) = 0)).filter
          (fun g => hyp e g = hyp e f0) =
          Finset.univ.filter (fun g : E →ₗ[F] F => g ≠ 0 ∧ LinearMap.ker g = LinearMap.ker f0) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hyp_eq_iff]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          refine ⟨⟨h1, ?_⟩, h3⟩
          have h4 : hyp e g = hyp e f0 := (hyp_eq_iff e g f0).2 h3
          have := (mem_hyp e f0 a).1 haD
          have h5 := (mem_hyp e g a).1 (h4 ▸ haD)
          exact h5
      rw [this]; omega
  have hNdfilter : ∀ x : E, Nat.card {f : (E →ₗ[F] F) // f x = 0} =
      (Finset.univ.filter (fun f : E →ₗ[F] F => f x = 0)).card := by
    intro x
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : cnt 1 * k + 1 = (k + 1) * t := by
    rw [key 1]
    have := dual_zero_card (F := F) (E := E) 0
    have h3 : (Finset.univ.filter (fun f : E →ₗ[F] F => f 0 = 0)).card = Nat.card (E →ₗ[F] F) := by
      simp [Nat.card_eq_fintype_card]
    have h4 : (Finset.univ.filter (fun f : E →ₗ[F] F => f ≠ 0 ∧ f (Multiplicative.toAdd (e.symm 1)) = 0)) =
        Finset.univ.filter (fun f : E →ₗ[F] F => f 0 = 0 ∧ f ≠ 0) := by
      ext f; simp [and_comm]
    rw [h4]
    rw [h3, hNd, hk] at this
    rw [hk] at *
    omega
  have h2 : ∀ a : A, a ≠ 1 → cnt a * k + 1 = t := by
    intro a ha
    rw [key a]
    have hx : Multiplicative.toAdd (e.symm a) ≠ 0 := by
      intro h
      apply ha
      have : e.symm a = 1 := h
      simpa using congrArg e this
    have := dual_zero_card (F := F) (E := E) (Multiplicative.toAdd (e.symm a))
    have h5 := dual_ker_card (F := F) (E := E) _ hx
    rw [hNdfilter, hNd, hF] at h5
    have h6 : (Finset.univ.filter (fun f : E →ₗ[F] F => f (Multiplicative.toAdd (e.symm a)) = 0)).card = t := by
      have : (Finset.univ.filter (fun f : E →ₗ[F] F => f (Multiplicative.toAdd (e.symm a)) = 0)).card * p = t * p := by
        rw [h5]; ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    have h4 : (Finset.univ.filter (fun f : E →ₗ[F] F => f ≠ 0 ∧ f (Multiplicative.toAdd (e.symm a)) = 0)) =
        Finset.univ.filter (fun f : E →ₗ[F] F => f (Multiplicative.toAdd (e.symm a)) = 0 ∧ f ≠ 0) := by
      ext f; simp [and_comm]
    rw [h4]
    omega
  have ha1 : (e (Multiplicative.ofAdd a0)) ≠ 1 := by
    intro h
    have : Multiplicative.ofAdd a0 = (1 : Multiplicative E) := by
      simpa using congrArg e.symm h
    exact ha0 this
  set c := cnt (e (Multiplicative.ofAdd a0)) with hc_def
  have hc : ∀ a : A, a ≠ 1 → cnt a = c := by
    intro a ha
    have := h2 a ha
    have h' : c * k + 1 = t := h2 _ ha1
    exact Nat.eq_of_mul_eq_mul_right hkpos (by omega)
  have h0 : cnt 1 = c + t := by
    have h' : c * k + 1 = t := h2 _ ha1
    refine Nat.eq_of_mul_eq_mul_right hkpos ?_
    nlinarith
  set Y : V := ∑ D ∈ Δ', S ρ A D v with hY
  have hYeq : Y = c • (∑ a : A, ρ a v) + t • v := by
    rw [hY, sum_S]
    have : ∀ a : A, cnt a • ρ a v = c • ρ a v + (if a = 1 then t • ρ a v else 0) := by
      intro a
      by_cases ha : a = 1
      · subst ha; simp [h0, add_smul]
      · simp [hc a ha, ha]
    rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_add_distrib, ← Finset.smul_sum,
      Finset.sum_ite_eq' Finset.univ (1 : A)]
    simp
  have hYmem : Y ∈ (⨆ D : hyperplanes p A, fixedSpace ρ D.1) := by
    refine Submodule.sum_mem _ (fun D hD => ?_)
    exact hWle D (hΔ D hD) (S_mem_fixed ρ A D (hΔ D hD).1 v)
  have hNmem : (∑ a : A, ρ a v) ∈ (⨆ D : hyperplanes p A, fixedSpace ρ D.1) := by
    have hN : (∑ a : A, ρ a v) ∈ fixedSpace ρ A := by
      rw [← normOp_apply]; exact mem_fixedSpace_normOp ρ A v
    have hDA : hyp e f1 ≤ A := hyp_le e f1
    refine hWle _ (hΔ _ hD0) ?_
    rw [mem_fixedSpace_iff] at hN ⊢
    intro d hd
    exact hN d (hDA hd)
  have htv : t • v ∈ (⨆ D : hyperplanes p A, fixedSpace ρ D.1) := by
    have : t • v = Y - c • (∑ a : A, ρ a v) := by rw [hYeq]; abel
    rw [this]
    exact Submodule.sub_mem _ hYmem (nsmul_mem hNmem c)
  have htq : ((t : ℕ) : ZMod q) ≠ 0 := by
    rw [ht, Nat.cast_pow]
    refine pow_ne_zero _ ?_
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hp).1 h).symm
  have : v = ((t : ℕ) : ZMod q)⁻¹ • ((t : ℕ) • v) := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod q), inv_smul_smul₀ htq]
  rw [this]
  exact Submodule.smul_mem _ _ htv

end

end CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.Gen

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

variable {G : Type} [Group G]

variable {q : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod q) V]

theorem iSup_fixedSpace_hyperplanes {p : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Finite A]
    (hA : CFSG.Open.IsElemAbelian p A) (hV : commSpace ρ A = ⊤) :
    (⨆ D : hyperplanes p A, fixedSpace ρ D.1) = ⊤ := by
  haveI := hA.1
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun a b => hA.1.is_comm.comm a b }
  have hexp : ∀ x : Additive A, p • x = 0 := by
    intro x
    have := hA.2 (Additive.toMul x : A) (Additive.toMul x).2
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa using this
  letI : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule hexp
  let e : Multiplicative (Additive A) ≃* A :=
    { toFun := fun x => Additive.toMul (Multiplicative.toAdd x)
      invFun := fun a => Multiplicative.ofAdd (Additive.ofMul a)
      left_inv := fun x => rfl
      right_inv := fun a => rfl
      map_mul' := fun x y => rfl }
  exact Gen.gen_aux hpq ρ A (F := ZMod p) (Nat.card_zmod p) e hV

theorem coprime_hyperplane_decomposition {p : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (ρ : Representation (ZMod q) G V) (A : Subgroup G) [Finite A]
    (hA : CFSG.Open.IsElemAbelian p A) (hV : commSpace ρ A = ⊤) :
    open scoped Classical in
    DirectSum.IsInternal (fun D : hyperplanes p A => fixedSpace ρ D.1) := by
  classical
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_fixedSpace hpq ρ A hA hV, iSup_fixedSpace_hyperplanes hpq ρ A hA hV⟩

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC
