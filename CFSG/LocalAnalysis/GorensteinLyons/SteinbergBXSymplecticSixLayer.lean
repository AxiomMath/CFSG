module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCBinarySixGenerated

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Module
open scoped commutatorElement
open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open CFSG.LargeEvenClassification.Helpers (pGeneratorRank pGeneratorRank_le_generators
  pGeneratorRank_generators)

namespace SymplecticSixLayer

theorem card_le_pow_of_injective_vanishing {U U' ι : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] [AddCommGroup U'] [Module (ZMod 2) U']
    [FiniteDimensional (ZMod 2) U'] (F : ι → U →ₗ[ZMod 2] U') (hF : Function.Injective F)
    (A : Submodule (ZMod 2) U) (B : Submodule (ZMod 2) U') (hA : ∀ i, ∀ x ∈ A, F i x = 0)
    (hB : ∀ i x, F i x ∈ B) :
    Nat.card ι ≤ 2 ^ ((finrank (ZMod 2) U - finrank (ZMod 2) A) * finrank (ZMod 2) B) := by
  let G : ι → (U ⧸ A) →ₗ[ZMod 2] B := fun i =>
    A.liftQ ((F i).codRestrict B (hB i)) (fun x hx => by
      rw [LinearMap.mem_ker]
      exact Subtype.ext (hA i x hx))
  have hG : Function.Injective G := by
    intro i j h
    apply hF
    ext x
    have := congrArg (fun φ : (U ⧸ A) →ₗ[ZMod 2] B => ((φ (A.mkQ x) : B) : U')) h
    simpa [G] using this
  have : Finite ((U ⧸ A) →ₗ[ZMod 2] B) := Module.finite_of_finite (R := ZMod 2)
  have hq := Submodule.finrank_quotient_add_finrank A
  calc Nat.card ι ≤ Nat.card ((U ⧸ A) →ₗ[ZMod 2] B) := Nat.card_le_card_of_injective G hG
    _ = 2 ^ finrank (ZMod 2) ((U ⧸ A) →ₗ[ZMod 2] B) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ = 2 ^ ((finrank (ZMod 2) U - finrank (ZMod 2) A) * finrank (ZMod 2) B) := by
        rw [Module.finrank_linearMap]
        congr 2
        omega

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem pGeneratorRank_congr {p : ℕ} {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') :
    pGeneratorRank p X = pGeneratorRank p X' := by
  unfold pGeneratorRank
  congr 1
  have hf : (frattini X).map e.toMonoidHom = frattini X' :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  exact Nat.card_congr (QuotientGroup.congr (frattini X) (frattini X') e hf).toEquiv

theorem card_frattini_quotient_eq_pow {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup p X) : Nat.card (X ⧸ frattini X) = p ^ pGeneratorRank p X := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := (hX.to_quotient (frattini X)).exists_card_eq
  rw [pGeneratorRank, hk, Nat.log_pow hp.one_lt]

theorem pow_pGeneratorRank_le_card {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup p X) : p ^ pGeneratorRank p X ≤ Nat.card X := by
  rw [← card_frattini_quotient_eq_pow hp hX]
  exact Nat.le_of_dvd Nat.card_pos (index_dvd_card (frattini X))

theorem pGeneratorRank_le_log_card (p : ℕ) {X : Type*} [Group X] [Finite X] :
    pGeneratorRank p X ≤ Nat.log p (Nat.card X) :=
  Nat.log_mono_right (Nat.le_of_dvd Nat.card_pos (index_dvd_card (frattini X)))

theorem pGeneratorRank_le_quotient_add {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup p X) (K : Subgroup X) [K.Normal] :
    pGeneratorRank p X ≤ pGeneratorRank p (X ⧸ K) + pGeneratorRank p K := by
  have := Fact.mk hp
  obtain ⟨-, -, -, -, dP, dQ, dN, hdP, hdQ, hdN, hle, -⟩ :=
    p_group_Frattini_coinvariant_generator_bound hX K rfl
  have h1 : pGeneratorRank p X = dP := by rw [pGeneratorRank, hdP, Nat.log_pow hp.one_lt]
  have h2 : pGeneratorRank p (X ⧸ K) = dQ := by rw [pGeneratorRank, hdQ, Nat.log_pow hp.one_lt]
  have h3 : dN ≤ pGeneratorRank p K := by
    have hle' : frattini K ≤ ((frattini K).map K.subtype ⊔ ⁅K, ⊤⁆).subgroupOf K := by
      intro x hx
      rw [mem_subgroupOf]
      exact mem_sup_left ⟨x, hx, rfl⟩
    have hdvd := index_dvd_of_le hle'
    have hpos : 0 < (frattini K).index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hcard : p ^ dN ≤ p ^ pGeneratorRank p K := by
      rw [← hdN, ← card_frattini_quotient_eq_pow hp (hX.to_subgroup K)]
      exact Nat.le_of_dvd hpos hdvd
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
  omega

theorem pGeneratorRank_le_one_of_isCyclic {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (hX : IsPGroup p X) [IsCyclic X] : pGeneratorRank p X ≤ 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
  have hcl : closure ((({g} : Finset X)) : Set X) = ⊤ := by
    rw [Finset.coe_singleton, ← zpowers_eq_closure, eq_top_iff]
    exact fun x _ => hg x
  simpa using pGeneratorRank_le_generators hp hX {g} hcl

theorem frattini_map_subtype_le {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup p X) {A B : Subgroup X} (hAB : A ≤ B) :
    (frattini A).map A.subtype ≤ (frattini B).map B.subtype := by
  have := Fact.mk hp
  have : Fact (IsPGroup p B) := ⟨hX.to_subgroup B⟩
  rw [frattini_eq_pow_sup_commutator (hX.to_subgroup A), Subgroup.map_sup, MonoidHom.map_closure]
  refine sup_le ?_ ?_
  · rw [closure_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨⟨a, hAB a.2⟩ ^ p, CFSG.pth_power_mem_frattini_of_isPGroup (p := p) _, by simp⟩
  · have e : ∀ C : Subgroup X, (commutator C).map C.subtype = ⁅C, C⁆ := fun C => by
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [e A]
    calc ⁅A, A⁆ ≤ ⁅B, B⁆ := commutator_mono hAB hAB
      _ = (commutator B).map B.subtype := (e B).symm
      _ ≤ (frattini B).map B.subtype :=
          map_mono (CFSG.commutator_le_frattini_of_isPGroup (p := p))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}

abbrev spEnd (g : bilinIsometryGroup b) : V →ₗ[ZMod 2] V :=
  ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)

theorem spEnd_mul (g h : bilinIsometryGroup b) (v : V) : spEnd (g * h) v = spEnd g (spEnd h v) :=
  rfl

theorem spEnd_one (v : V) : spEnd (1 : bilinIsometryGroup b) v = v :=
  rfl

theorem spEnd_inv_apply (g : bilinIsometryGroup b) (v : V) : spEnd g (spEnd g⁻¹ v) = v := by
  rw [← spEnd_mul, mul_inv_cancel, spEnd_one]

theorem spEnd_apply_inv (g : bilinIsometryGroup b) (v : V) : spEnd g⁻¹ (spEnd g v) = v := by
  rw [← spEnd_mul, inv_mul_cancel, spEnd_one]

theorem spEnd_isometry (g : bilinIsometryGroup b) (x y : V) : b (spEnd g x) (spEnd g y) = b x y :=
  g.2 x y

theorem spEnd_injective : Function.Injective (spEnd (b := b)) := by
  intro g h hgh
  exact Subtype.ext (Units.ext hgh)

@[expose] def spFixed (Γ : Subgroup (bilinIsometryGroup b)) : Submodule (ZMod 2) V where
  carrier := {v | ∀ g ∈ Γ, spEnd g v = v}
  add_mem' := fun {u v} hu hv g hg => by rw [map_add, hu g hg, hv g hg]
  zero_mem' := fun g _ => map_zero _
  smul_mem' := fun c {v} hv g hg => by rw [map_smul, hv g hg]

@[expose] def spCommutator (Γ : Subgroup (bilinIsometryGroup b)) (W : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {v | ∃ g ∈ Γ, ∃ w ∈ W, v = spEnd g w - w}

theorem mem_spFixed {Γ : Subgroup (bilinIsometryGroup b)} {v : V} :
    v ∈ spFixed Γ ↔ ∀ g ∈ Γ, spEnd g v = v :=
  Iff.rfl

theorem spCommutator_le {Γ : Subgroup (bilinIsometryGroup b)} {W : Submodule (ZMod 2) V}
    (hW : ∀ g ∈ Γ, ∀ w ∈ W, spEnd g w ∈ W) : spCommutator Γ W ≤ W := by
  rw [spCommutator, Submodule.span_le]
  rintro _ ⟨g, hg, w, hw, rfl⟩
  exact sub_mem (hW g hg w hw) hw

theorem spCommutator_invariant {Γ : Subgroup (bilinIsometryGroup b)} {W : Submodule (ZMod 2) V}
    {h : bilinIsometryGroup b} (hh : h ∈ Γ) {v : V}
    (hv : v ∈ spCommutator Γ W) : spEnd h v ∈ spCommutator Γ W := by
  have hle : spCommutator Γ W ≤ (spCommutator Γ W).comap (spEnd h) := by
    rw [spCommutator, Submodule.span_le]
    rintro _ ⟨g, hg, w, hw, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub]
    have e : spEnd h (spEnd g w) - spEnd h w =
        (spEnd (h * g) w - w) - (spEnd h w - w) := by
      rw [spEnd_mul]
      abel
    rw [e]
    exact sub_mem (Submodule.subset_span ⟨h * g, mul_mem hh hg, w, hw, rfl⟩)
      (Submodule.subset_span ⟨h, hh, w, hw, rfl⟩)
  exact hle hv

variable [FiniteDimensional (ZMod 2) V]

theorem card_le_of_forall_fixes (hnd : b.Nondegenerate) (Γ : Subgroup (bilinIsometryGroup b))
    (T : Submodule (ZMod 2) V) (hT : ∀ g ∈ Γ, ∀ x ∈ T, spEnd g x = x) :
    Nat.card Γ ≤ 2 ^ ((finrank (ZMod 2) V - finrank (ZMod 2) T) *
      (finrank (ZMod 2) V - finrank (ZMod 2) T)) := by
  let F : Γ → V →ₗ[ZMod 2] V := fun g => spEnd (g : bilinIsometryGroup b) - LinearMap.id
  have hF : Function.Injective F := by
    intro g h hgh
    have : spEnd (g : bilinIsometryGroup b) = spEnd (h : bilinIsometryGroup b) := by
      have := congrArg (· + LinearMap.id) hgh
      simpa [F] using this
    exact Subtype.ext (spEnd_injective this)
  have hA : ∀ g, ∀ x ∈ T, F g x = 0 := by
    intro g x hx
    simp [F, hT g g.2 x hx]
  have hB : ∀ g x, F g x ∈ b.orthogonal T := by
    intro g x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have h1 : b n (spEnd (g : bilinIsometryGroup b) x) = b n x := by
      conv_lhs => rw [← hT g g.2 n hn]
      exact spEnd_isometry _ n x
    simp only [F, LinearMap.sub_apply, LinearMap.id_apply]
    rw [LinearMap.BilinForm.sub_right, h1, sub_self]
  have h := card_le_pow_of_injective_vanishing F hF T (b.orthogonal T) hA hB
  rwa [LinearMap.BilinForm.finrank_orthogonal hnd] at h

theorem finrank_spFixed_add_finrank_spCommutator (hnd : b.Nondegenerate)
    (Γ : Subgroup (bilinIsometryGroup b)) :
    finrank (ZMod 2) (spFixed Γ) + finrank (ZMod 2) (spCommutator Γ ⊤) = finrank (ZMod 2) V := by
  have heq : spFixed Γ = b.orthogonal (spCommutator Γ ⊤) := by
    ext x
    rw [mem_spFixed, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hx n hn
      have hle : spCommutator Γ ⊤ ≤ LinearMap.ker (b.flip x) := by
        rw [spCommutator, Submodule.span_le]
        rintro _ ⟨g, hg, w, -, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.BilinForm.flip_apply,
          LinearMap.BilinForm.sub_left]
        have h1 : b (spEnd g w) x = b w x := by
          conv_lhs => rw [← hx g hg]
          exact spEnd_isometry g w x
        rw [h1, sub_self]
      exact hle hn
    · intro hx g hg
      have hv : ∀ v, b v (spEnd g x - x) = 0 := by
        intro v
        have h1 := hx (spEnd g⁻¹ v - v)
          (Submodule.subset_span ⟨g⁻¹, inv_mem hg, v, Submodule.mem_top, rfl⟩)
        rw [LinearMap.BilinForm.sub_left, sub_eq_zero] at h1
        have h2 : b (spEnd g⁻¹ v) x = b v (spEnd g x) := by
          rw [← spEnd_isometry g, spEnd_inv_apply]
        rw [LinearMap.BilinForm.sub_right, ← h2, h1, sub_self]
      exact sub_eq_zero.mp (hnd.2 _ hv)
  rw [heq, LinearMap.BilinForm.finrank_orthogonal hnd]
  have := Submodule.finrank_le (spCommutator Γ ⊤)
  omega

theorem fixes_of_finrank_eq_one {L : Submodule (ZMod 2) V} (hL : finrank (ZMod 2) L = 1)
    {g : bilinIsometryGroup b} (hg : ∀ v ∈ L, spEnd g v ∈ L) : ∀ v ∈ L, spEnd g v = v := by
  obtain ⟨v₀, hv₀, hall⟩ := finrank_eq_one_iff'.mp hL
  have hpair : ∀ x : L, x = 0 ∨ x = v₀ := by
    intro x
    obtain ⟨c, hc⟩ := hall x
    rcases zmod_two_cases c with rfl | rfl
    · left
      rw [← hc, zero_smul]
    · right
      rw [← hc, one_smul]
  have hgv₀ : spEnd g (v₀ : V) = v₀ := by
    rcases hpair ⟨spEnd g v₀, hg _ v₀.2⟩ with h | h
    · exfalso
      have h1 : spEnd g (v₀ : V) = 0 := congrArg Subtype.val h
      have h2 : (v₀ : V) = 0 := by
        rw [← spEnd_apply_inv g v₀, h1, map_zero]
      exact hv₀ (Subtype.ext h2)
    · exact congrArg Subtype.val h
  intro v hv
  rcases hpair ⟨v, hv⟩ with h | h
  · have : v = 0 := congrArg Subtype.val h
    rw [this, map_zero]
  · have : v = v₀ := congrArg Subtype.val h
    rw [this, hgv₀]

theorem card_le_of_commutator_line (hV : finrank (ZMod 2) V = 6) (hnd : b.Nondegenerate)
    (Γ : Subgroup (bilinIsometryGroup b)) (W : Submodule (ZMod 2) V)
    (hW : ∀ g ∈ Γ, ∀ w ∈ W, spEnd g w ∈ W) (hW5 : finrank (ZMod 2) W = 5)
    (hL : finrank (ZMod 2) (spCommutator Γ W) = 1) : Nat.card Γ ≤ 32 := by
  set L := spCommutator Γ W with hLdef
  have hLW : L ≤ W := spCommutator_le hW
  have hfixL : ∀ g ∈ Γ, ∀ v ∈ L, spEnd g v = v := fun g hg =>
    fixes_of_finrank_eq_one hL fun v hv => spCommutator_invariant hg hv
  let K : Subgroup (bilinIsometryGroup b) :=
    { carrier := {g | g ∈ Γ ∧ ∀ w ∈ W, spEnd g w = w}
      mul_mem' := fun {g h} hg hh => ⟨mul_mem hg.1 hh.1, fun w hw => by
        rw [spEnd_mul, hh.2 w hw, hg.2 w hw]⟩
      one_mem' := ⟨one_mem _, fun w _ => spEnd_one w⟩
      inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun w hw => by
        conv_lhs => rw [← hg.2 w hw]
        exact spEnd_apply_inv g w⟩ }
  have hKΓ : K ≤ Γ := fun g hg => hg.1
  have hKcard : Nat.card K ≤ 2 := by
    have h := card_le_of_forall_fixes hnd K W fun g hg => hg.2
    rw [hV, hW5] at h
    simpa using h
  have hres : ∀ g : Γ, ∀ w ∈ W,
      (spEnd (g : bilinIsometryGroup b) - LinearMap.id : V →ₗ[ZMod 2] V) w ∈ W :=
    fun g w hw => by
      rw [LinearMap.sub_apply, LinearMap.id_apply]
      exact sub_mem (hW g g.2 w hw) hw
  let F : Γ → W →ₗ[ZMod 2] W := fun g =>
    (spEnd (g : bilinIsometryGroup b) - LinearMap.id).restrict (hres g)
  have hFapply : ∀ (g : Γ) (w : W), ((F g w : W) : V) = spEnd (g : bilinIsometryGroup b) w - w :=
    fun _ _ => rfl
  let K' : Subgroup Γ := K.subgroupOf Γ
  have hFconst : ∀ a c : Γ, a⁻¹ * c ∈ K' → F a = F c := by
    intro a c hac
    ext w
    rw [hFapply, hFapply]
    have h1 := (mem_subgroupOf.mp hac).2 w w.2
    have h2 : spEnd (c : bilinIsometryGroup b) w = spEnd (a : bilinIsometryGroup b) w := by
      have := congrArg (spEnd (a : bilinIsometryGroup b)) h1
      rwa [Subgroup.coe_mul, spEnd_mul, Subgroup.coe_inv, spEnd_inv_apply] at this
    rw [h2]
  let Fbar : Γ ⧸ K' → W →ₗ[ZMod 2] W :=
    Quotient.lift F fun a c hac => hFconst a c (QuotientGroup.leftRel_apply.mp hac)
  have hFbar : Function.Injective Fbar := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H c =>
    have hac : F a = F c := hxy
    rw [QuotientGroup.eq, mem_subgroupOf]
    refine ⟨mul_mem (inv_mem a.2) c.2, fun w hw => ?_⟩
    have h1 := congrArg (fun φ : W →ₗ[ZMod 2] W => ((φ ⟨w, hw⟩ : W) : V)) hac
    simp only [hFapply, sub_left_inj] at h1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, spEnd_mul, ← h1, spEnd_apply_inv]
  have hA : ∀ x : Γ ⧸ K', ∀ w ∈ L.comap W.subtype, Fbar x w = 0 := by
    intro x w hw
    induction x using QuotientGroup.induction_on with | H a =>
    change F a w = 0
    have hw' : (w : V) ∈ L := Submodule.mem_comap.mp hw
    exact Subtype.ext (by rw [hFapply, hfixL _ a.2 _ hw', sub_self]; rfl)
  have hB : ∀ (x : Γ ⧸ K') (w : W), Fbar x w ∈ L.comap W.subtype := by
    intro x w
    induction x using QuotientGroup.induction_on with | H a =>
    change F a w ∈ L.comap W.subtype
    rw [Submodule.mem_comap, Submodule.coe_subtype, hFapply]
    exact Submodule.subset_span ⟨a, a.2, w, w.2, rfl⟩
  have hLc : finrank (ZMod 2) (L.comap W.subtype) = 1 := by
    rw [(Submodule.comapSubtypeEquivOfLe hLW).finrank_eq, hL]
  have hq := card_le_pow_of_injective_vanishing Fbar hFbar (L.comap W.subtype)
    (L.comap W.subtype) hA hB
  rw [hW5, hLc] at hq
  have hcard := card_eq_card_quotient_mul_card_subgroup K'
  have hK'card : Nat.card K' = Nat.card K := Nat.card_congr (subgroupOfEquivOfLe hKΓ).toEquiv
  rw [hcard, hK'card]
  calc Nat.card (Γ ⧸ K') * Nat.card K ≤ 16 * 2 := Nat.mul_le_mul (by simpa using hq) hKcard
    _ = 32 := by norm_num

theorem table_arith {t k m : ℕ} (ht6 : t ≤ 6) (hk6 : k ≤ 6) (hmk : m ≤ k)
    (hfixW : m = 0 → t ≤ (6 - k) * (6 - k)) (hfixV : k = 6 → t ≤ m * m)
    (hline : k = 5 → m = 1 → t ≤ 5) :
    (t = 0 → k - m ≤ 6) ∧ (t = 1 → k - m ≤ 5) ∧ (2 ≤ t → k - m ≤ 4) ∧ (t = 6 → k - m ≤ 3) ∧
      k - m + t ≤ 9 := by
  interval_cases k <;> interval_cases m <;> omega

theorem coinvariant_table (hV : finrank (ZMod 2) V = 6) (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (Γ : Subgroup (bilinIsometryGroup b)) (hΓ : IsPGroup 2 Γ) (W : Submodule (ZMod 2) V)
    (hW : ∀ g ∈ Γ, ∀ w ∈ W, spEnd g w ∈ W) :
    pGeneratorRank 2 Γ ≤ 6 ∧
      (pGeneratorRank 2 Γ = 0 →
        finrank (ZMod 2) W - finrank (ZMod 2) (spCommutator Γ W) ≤ 6) ∧
      (pGeneratorRank 2 Γ = 1 →
        finrank (ZMod 2) W - finrank (ZMod 2) (spCommutator Γ W) ≤ 5) ∧
      (2 ≤ pGeneratorRank 2 Γ →
        finrank (ZMod 2) W - finrank (ZMod 2) (spCommutator Γ W) ≤ 4) ∧
      (pGeneratorRank 2 Γ = 6 →
        finrank (ZMod 2) W - finrank (ZMod 2) (spCommutator Γ W) ≤ 3) ∧
      finrank (ZMod 2) W - finrank (ZMod 2) (spCommutator Γ W) + pGeneratorRank 2 Γ ≤ 9 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have ht6 := (binary_symplectic_six_subgroup_six_generated hV hb hnd Γ hΓ).1
  have : Finite (bilinIsometryGroup b) := by
    have : Finite (V →ₗ[ZMod 2] V) := Module.finite_of_finite (ZMod 2)
    exact Finite.of_injective _ spEnd_injective
  have hΓcard : 2 ^ pGeneratorRank 2 Γ ≤ Nat.card Γ := pow_pGeneratorRank_le_card Nat.prime_two hΓ
  have hexp : ∀ e : ℕ, Nat.card Γ ≤ 2 ^ e → pGeneratorRank 2 Γ ≤ e := fun e he =>
    (Nat.pow_le_pow_iff_right (by norm_num)).mp (hΓcard.trans he)
  have hk6 : finrank (ZMod 2) W ≤ 6 := hV ▸ Submodule.finrank_le W
  have hmk : finrank (ZMod 2) (spCommutator Γ W) ≤ finrank (ZMod 2) W :=
    Submodule.finrank_mono (spCommutator_le hW)
  have hfixW : finrank (ZMod 2) (spCommutator Γ W) = 0 →
      pGeneratorRank 2 Γ ≤ (6 - finrank (ZMod 2) W) * (6 - finrank (ZMod 2) W) := by
    intro hm0
    have hbot : spCommutator Γ W = ⊥ := Submodule.finrank_eq_zero.mp hm0
    refine hexp _ (hV ▸ card_le_of_forall_fixes hnd Γ W fun g hg w hw => ?_)
    have : spEnd g w - w ∈ spCommutator Γ W := Submodule.subset_span ⟨g, hg, w, hw, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hfixV : finrank (ZMod 2) W = 6 → pGeneratorRank 2 Γ ≤
      finrank (ZMod 2) (spCommutator Γ W) * finrank (ZMod 2) (spCommutator Γ W) := by
    intro hk
    have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (hk.trans hV.symm)
    have h1 := finrank_spFixed_add_finrank_spCommutator hnd Γ
    rw [← hWtop] at h1
    have h2 := card_le_of_forall_fixes hnd Γ (spFixed Γ) fun g hg x hx => hx g hg
    have h3 : finrank (ZMod 2) V - finrank (ZMod 2) (spFixed Γ) =
        finrank (ZMod 2) (spCommutator Γ W) := by omega
    rw [h3] at h2
    exact hexp _ h2
  have hline : finrank (ZMod 2) W = 5 → finrank (ZMod 2) (spCommutator Γ W) = 1 →
      pGeneratorRank 2 Γ ≤ 5 := fun h5 h1 =>
    hexp 5 ((card_le_of_commutator_line hV hnd Γ W hW h5 h1).trans (by norm_num))
  exact ⟨ht6, table_arith ht6 hk6 hmk hfixW hfixV hline⟩

theorem card_quotient_layer_le {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    (K C : Subgroup X) (hCK : C ≤ K) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (φ : K →* Multiplicative V) (hφker : φ.ker = C.subgroupOf K)
    (W WR : Submodule (ZMod 2) V) (hWR : WR ≤ W)
    (hW : ∀ v, v ∈ W ↔ Multiplicative.ofAdd v ∈ φ.range)
    (hWRsub : ∀ v ∈ WR, ∃ k : K, (k : X) ∈ ⁅K, (⊤ : Subgroup X)⁆ ∧
      φ k = Multiplicative.ofAdd v) :
    Nat.card (K ⧸ ((frattini K).map K.subtype ⊔ ⁅K, ⊤⁆).subgroupOf K) ≤
      2 ^ (pGeneratorRank 2 C + (finrank (ZMod 2) W - finrank (ZMod 2) WR)) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  set M := (frattini K).map K.subtype ⊔ ⁅K, ⊤⁆ with hMdef
  set Mk := M.subgroupOf K with hMkdef
  have hKφ : Nat.card K = Nat.card C * Nat.card W := by
    rw [card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
    congr 1
    · rw [hφker]
      exact Nat.card_congr (subgroupOfEquivOfLe hCK).toEquiv
    · exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun x => by
        rw [hW]
        rfl)
  let φM : Mk →* Multiplicative V := φ.comp Mk.subtype
  have hMk : Nat.card (frattini C) * Nat.card WR ≤ Nat.card Mk := by
    have hΦ : ∀ f : frattini C, ((f : C) : X) ∈ M := fun f =>
      mem_sup_left (frattini_map_subtype_le Nat.prime_two hX hCK ⟨f, f.2, rfl⟩)
    have h1 : Nat.card (frattini C) ≤ Nat.card φM.ker := by
      refine Nat.card_le_card_of_injective
        (fun f => ⟨⟨⟨(f : C), hCK (f : C).2⟩, mem_subgroupOf.mpr (hΦ f)⟩, ?_⟩) ?_
      · rw [MonoidHom.mem_ker]
        change φ ⟨(f : C), hCK (f : C).2⟩ = 1
        rw [← MonoidHom.mem_ker, hφker, mem_subgroupOf]
        exact (f : C).2
      · intro f g hfg
        have := congrArg (fun x : φM.ker => (((x : Mk) : K) : X)) hfg
        exact Subtype.ext (Subtype.ext this)
    have h2 : Nat.card WR ≤ Nat.card φM.range := by
      refine Nat.card_le_card_of_injective
        (fun v : WR => (⟨Multiplicative.ofAdd (v : V), ?_⟩ : φM.range)) ?_
      · obtain ⟨k, hkM, hk⟩ := hWRsub v v.2
        exact ⟨⟨k, mem_subgroupOf.mpr (mem_sup_right hkM)⟩, hk⟩
      · intro v w hvw
        have := congrArg (fun x : φM.range => Multiplicative.toAdd (x : Multiplicative V)) hvw
        exact Subtype.ext this
    calc Nat.card (frattini C) * Nat.card WR ≤ Nat.card φM.ker * Nat.card φM.range :=
          Nat.mul_le_mul h1 h2
      _ = Nat.card Mk := by
          rw [card_eq_card_quotient_mul_card_subgroup φM.ker,
            Nat.card_congr (QuotientGroup.quotientKerEquivRange φM).toEquiv, mul_comm]
  have hC : Nat.card C = Nat.card (frattini C) * 2 ^ pGeneratorRank 2 C := by
    rw [card_eq_card_quotient_mul_card_subgroup (frattini C),
      card_frattini_quotient_eq_pow Nat.prime_two (hX.to_subgroup C), mul_comm]
  have hWcard : Nat.card W = Nat.card WR * 2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) WR) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := WR), Nat.card_zmod, ← pow_add]
    congr 1
    have := Submodule.finrank_mono hWR
    omega
  have hKMk := card_eq_card_quotient_mul_card_subgroup Mk
  have hpos : 0 < Nat.card Mk := Nat.card_pos
  have key : Nat.card Mk * Nat.card (K ⧸ Mk) ≤
      Nat.card Mk * 2 ^ (pGeneratorRank 2 C + (finrank (ZMod 2) W - finrank (ZMod 2) WR)) := by
    calc Nat.card Mk * Nat.card (K ⧸ Mk) = Nat.card K := by rw [hKMk, mul_comm]
      _ = Nat.card (frattini C) * Nat.card WR *
            (2 ^ pGeneratorRank 2 C * 2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) WR)) := by
          rw [hKφ, hC, hWcard]
          ring
      _ ≤ Nat.card Mk *
            (2 ^ pGeneratorRank 2 C * 2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) WR)) :=
          Nat.mul_le_mul_right _ hMk
      _ = Nat.card Mk * 2 ^ (pGeneratorRank 2 C +
            (finrank (ZMod 2) W - finrank (ZMod 2) WR)) := by rw [pow_add]
  exact Nat.le_of_mul_le_mul_left key hpos

end SymplecticSixLayer

open SymplecticSixLayer in
theorem cyclic_layer_symplectic_six_extension_eleven_generated {H : Type*} [Group H] [Finite H]
    {Y D Q : Subgroup H} [Y.Normal] [hDn : D.Normal] [hQn : Q.Normal] (hYD : Y ≤ D)
    (hDQ : D ≤ Q) (_hQ : IsPGroup 2 Q) (hYc : IsCyclic Y) (hQD : D.relIndex Q ≤ 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (hV : Nat.card V = 64)
    (π : D →* Multiplicative V) (_hπ : Function.Surjective π) (hπker : π.ker = Y.subgroupOf D)
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (ρ : H →* bilinIsometryGroup b)
    (hρ : ∀ (h : H) (d d' : D), (d' : H) = h * d * h⁻¹ →
      Multiplicative.toAdd (π d') = ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) (Multiplicative.toAdd (π d)))
    (hρker : ρ.ker = Q) (P : Subgroup H) (hP : IsPGroup 2 P) (W : Submodule (ZMod 2) V)
    (hW : W = Submodule.span (ZMod 2)
      {v | ∃ d : D, (d : H) ∈ P ∧ v = Multiplicative.toAdd (π d)})
    (WR : Submodule (ZMod 2) V)
    (hWR : WR = Submodule.span (ZMod 2) {v | ∃ h ∈ P, ∃ w ∈ W,
      v = ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w - w})
    (t c : ℕ) (ht : t = pGeneratorRank 2 (P ⧸ Q.subgroupOf P))
    (hc : c = finrank (ZMod 2) (W ⧸ WR.comap W.subtype)) :
    t ≤ 6 ∧ (t = 0 → c ≤ 6) ∧ (t = 1 → c ≤ 5) ∧ (2 ≤ t → t ≤ 5 → c ≤ 4) ∧ (t = 6 → c ≤ 3) ∧
      c + t ≤ 9 ∧
      pGeneratorRank 2 P ≤ pGeneratorRank 2 (Y.subgroupOf P) +
        pGeneratorRank 2 (Q.subgroupOf P ⧸ (D.subgroupOf P).subgroupOf (Q.subgroupOf P)) +
          c + t ∧
      pGeneratorRank 2 P ≤ 11 ∧ (∃ S : Finset P, S.card ≤ 11 ∧ closure (S : Set P) = ⊤) ∧
      (∀ (L : Subgroup P) [L.Normal], CFSG.IsElementaryAbelian 2 (P ⧸ L) →
        Nat.card (P ⧸ L) ≤ 2 ^ 11) ∧
      (Q = D → pGeneratorRank 2 P ≤ 10 ∧
        ∃ S : Finset P, S.card ≤ 10 ∧ closure (S : Set P) = ⊤) := by
  classical
  have := Fact.mk Nat.prime_two
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hV6 : finrank (ZMod 2) V = 6 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num))
  set K := D.subgroupOf P with hKdef
  set C := Y.subgroupOf P with hCdef
  set N := Q.subgroupOf P with hNdef
  have hCK : C ≤ K := fun x hx => hYD hx
  have hKN : K ≤ N := fun x hx => hDQ hx
  have hKn : K.Normal := hDn.subgroupOf P
  have hNn : N.Normal := hQn.subgroupOf P
  let ι : K →* D :=
    { toFun := fun x => ⟨((x : P) : H), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let φ : K →* Multiplicative V := π.comp ι
  have hφker : φ.ker = C.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hCdef, mem_subgroupOf]
    change π (ι x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hπker, mem_subgroupOf]
    rfl
  have hWmem : ∀ v, v ∈ W ↔ Multiplicative.ofAdd v ∈ φ.range := by
    let Wsub : Submodule (ZMod 2) V :=
      { carrier := {v | Multiplicative.ofAdd v ∈ φ.range}
        add_mem' := fun {u v} hu hv => by
          change Multiplicative.ofAdd u * Multiplicative.ofAdd v ∈ φ.range
          exact mul_mem hu hv
        zero_mem' := one_mem φ.range
        smul_mem' := fun a {v} hv => by
          rcases zmod_two_cases a with rfl | rfl
          · rw [zero_smul]
            exact one_mem φ.range
          · rwa [one_smul] }
    have hWeq : W = Wsub := by
      rw [hW]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨d, hdP, rfl⟩
        exact ⟨⟨⟨d, hdP⟩, d.2⟩, rfl⟩
      · intro v hv
        obtain ⟨x, hx⟩ := hv
        refine Submodule.subset_span ⟨ι x, (x : P).2, ?_⟩
        change v = Multiplicative.toAdd (φ x)
        rw [hx]
        rfl
    intro v
    rw [hWeq]
    rfl
  have hconj : ∀ h ∈ P, ∀ x : K, ∃ y : K, ((y : P) : H) = h * ((x : P) : H) * h⁻¹ ∧
      Multiplicative.toAdd (φ y) = spEnd (ρ h) (Multiplicative.toAdd (φ x)) := by
    intro h hh x
    have hD : h * ((x : P) : H) * h⁻¹ ∈ D := hDn.conj_mem _ x.2 h
    have hPm : h * ((x : P) : H) * h⁻¹ ∈ P := mul_mem (mul_mem hh (x : P).2) (inv_mem hh)
    refine ⟨⟨⟨_, hPm⟩, hD⟩, rfl, ?_⟩
    exact hρ h (ι x) ⟨_, hD⟩ rfl
  set Γ := P.map ρ with hΓdef
  have hΓ : IsPGroup 2 Γ := hP.map ρ
  have hWinv : ∀ g ∈ Γ, ∀ w ∈ W, spEnd g w ∈ W := by
    rintro _ ⟨h, hh, rfl⟩ w hw
    obtain ⟨x, hx⟩ := (hWmem w).mp hw
    obtain ⟨y, -, hy⟩ := hconj h hh x
    rw [hWmem]
    refine ⟨y, ?_⟩
    change φ y = Multiplicative.ofAdd (spEnd (ρ h) w)
    apply Multiplicative.toAdd.injective
    rw [hy, hx]
    rfl
  have hWRΓ : WR = spCommutator Γ W := by
    rw [hWR, spCommutator]
    congr 1
    ext v
    constructor
    · rintro ⟨h, hh, w, hw, rfl⟩
      exact ⟨ρ h, mem_map_of_mem ρ hh, w, hw, rfl⟩
    · rintro ⟨_, ⟨h, hh, rfl⟩, w, hw, rfl⟩
      exact ⟨h, hh, w, hw, rfl⟩
  have hWRW : WR ≤ W := hWRΓ ▸ spCommutator_le hWinv
  have htΓ : t = pGeneratorRank 2 Γ := by
    rw [ht]
    let ψ : P →* bilinIsometryGroup b := ρ.comp P.subtype
    have hker : N = ψ.ker := by
      ext x
      rw [hNdef, mem_subgroupOf, ← hρker, MonoidHom.mem_ker, MonoidHom.mem_ker]
      rfl
    have hrange : ψ.range = Γ := by
      rw [MonoidHom.range_comp, range_subtype]
    exact pGeneratorRank_congr ((QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)))
  have hcWR : c = finrank (ZMod 2) W - finrank (ZMod 2) WR := by
    have h1 := Submodule.finrank_quotient_add_finrank (WR.comap W.subtype)
    rw [(Submodule.comapSubtypeEquivOfLe hWRW).finrank_eq] at h1
    omega
  obtain ⟨ht6, h0, h1, h2, h6, h9⟩ := coinvariant_table hV6 hb hnd Γ hΓ W hWinv
  rw [← hWRΓ, ← htΓ, ← hcWR] at h0 h1 h2 h6 h9
  rw [← htΓ] at ht6
  have hWRsub : ∀ v ∈ WR, ∃ k : K, (k : P) ∈ ⁅K, (⊤ : Subgroup P)⁆ ∧
      φ k = Multiplicative.ofAdd v := by
    let WRsub : Submodule (ZMod 2) V :=
      { carrier := {v | ∃ k : K, (k : P) ∈ ⁅K, (⊤ : Subgroup P)⁆ ∧ φ k = Multiplicative.ofAdd v}
        add_mem' := fun {u v} ⟨k, hk, hku⟩ ⟨l, hl, hlv⟩ =>
          ⟨k * l, mul_mem hk hl, by rw [map_mul, hku, hlv]; rfl⟩
        zero_mem' := ⟨1, one_mem _, map_one φ⟩
        smul_mem' := fun a {v} hv => by
          rcases zmod_two_cases a with rfl | rfl
          · rw [zero_smul]
            exact ⟨1, one_mem _, map_one φ⟩
          · rwa [one_smul] }
    have hle : WR ≤ WRsub := by
      rw [hWR, Submodule.span_le]
      rintro _ ⟨h, hh, w, hw, rfl⟩
      obtain ⟨x, hx⟩ := (hWmem w).mp hw
      obtain ⟨y, hy, hyφ⟩ := hconj h hh x
      refine ⟨y * x⁻¹, ?_, ?_⟩
      · have e : ((y * x⁻¹ : K) : P) = ⁅(x : P), ⟨h, hh⟩⁆⁻¹ := by
          apply Subtype.ext
          change ((y : P) : H) * ((x : P) : H)⁻¹ = _
          rw [hy]
          simp only [commutatorElement_def, Subgroup.coe_inv, Subgroup.coe_mul]
          group
        rw [e]
        exact inv_mem (commutator_mem_commutator x.2 (mem_top _))
      · rw [map_mul, map_inv]
        change φ y * (φ x)⁻¹ = Multiplicative.ofAdd (spEnd (ρ h) w - w)
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, hyφ, hx, toAdd_ofAdd, toAdd_ofAdd, sub_eq_add_neg]
    exact fun v hv => hle hv
  have hlayer := card_quotient_layer_le hP K C hCK φ hφker W WR hWRW hWmem hWRsub
  obtain ⟨-, -, -, -, dP, dQ, dN, hdP, hdQ, hdN, hle, -⟩ :=
    p_group_Frattini_coinvariant_generator_bound hP K rfl
  have hdPeq : pGeneratorRank 2 P = dP := by rw [pGeneratorRank, hdP, Nat.log_pow (by norm_num)]
  have hdQeq : pGeneratorRank 2 (P ⧸ K) = dQ := by
    rw [pGeneratorRank, hdQ, Nat.log_pow (by norm_num)]
  have hdNle : dN ≤ pGeneratorRank 2 C + c := by
    rw [hdN, ← hcWR] at hlayer
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hlayer
  have hPK : pGeneratorRank 2 (P ⧸ K) ≤ t + pGeneratorRank 2 (N ⧸ K.subgroupOf N) := by
    have hNbar : (N.map (QuotientGroup.mk' K)).Normal :=
      hNn.map _ (QuotientGroup.mk'_surjective K)
    have h := pGeneratorRank_le_quotient_add Nat.prime_two (hP.to_quotient K)
      (N.map (QuotientGroup.mk' K))
    rw [pGeneratorRank_congr (QuotientGroup.quotientQuotientEquivQuotient K N hKN), ← ht] at h
    let ψ : N →* P ⧸ K := (QuotientGroup.mk' K).comp N.subtype
    have hker : K.subgroupOf N = ψ.ker := by
      ext x
      rw [mem_subgroupOf, MonoidHom.mem_ker]
      change _ ↔ (QuotientGroup.mk' K) (x : P) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hrange : ψ.range = N.map (QuotientGroup.mk' K) := by
      rw [MonoidHom.range_comp, range_subtype]
    rwa [← pGeneratorRank_congr ((QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)))] at h
  have hmain : pGeneratorRank 2 P ≤ pGeneratorRank 2 C +
      pGeneratorRank 2 (N ⧸ K.subgroupOf N) + c + t := by
    omega
  have hdC : pGeneratorRank 2 C ≤ 1 := by
    have : IsCyclic C := by
      let f : C →* Y :=
        { toFun := fun x => ⟨((x : P) : H), x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine isCyclic_of_injective f fun x y hxy => ?_
      have h' : ((f x : Y) : H) = ((f y : Y) : H) := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h')
    exact pGeneratorRank_le_one_of_isCyclic Nat.prime_two (hP.to_subgroup C)
  have hNKcard : Nat.card (N ⧸ K.subgroupOf N) ≤ 2 := by
    change K.relIndex N ≤ 2
    rw [hKdef, hNdef, subgroupOf, relIndex_comap, subgroupOf_map_subtype]
    exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hQD
  have hdNK : pGeneratorRank 2 (N ⧸ K.subgroupOf N) ≤ 1 := by
    refine (pGeneratorRank_le_log_card 2).trans ((Nat.log_mono_right hNKcard).trans ?_)
    simpa using (Nat.log_pow (b := 2) (by norm_num) 1).le
  have hdP11 : pGeneratorRank 2 P ≤ 11 := by omega
  have hgen : ∀ n, pGeneratorRank 2 P ≤ n →
      ∃ S : Finset P, S.card ≤ n ∧ closure (S : Set P) = ⊤ := by
    intro n hn
    obtain ⟨S, hS, hScard⟩ := pGeneratorRank_generators Nat.prime_two hP
    exact ⟨S, hScard ▸ hn, hS⟩
  refine ⟨ht6, h0, h1, fun h2t _ => h2 h2t, h6, h9, hmain, hdP11, hgen 11 hdP11,
    fun L _ hEA => ?_, fun hQD' => ?_⟩
  · have hle' : frattini P ≤ L := CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary
      (p := 2) L (fun a b => hEA.is_comm.comm a b)
      (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEA.exponent_dvd_p a)
    have hdvd : L.index ∣ (frattini P).index := index_dvd_of_le hle'
    have hΦ : (frattini P).index = 2 ^ pGeneratorRank 2 P :=
      card_frattini_quotient_eq_pow Nat.prime_two hP
    calc Nat.card (P ⧸ L) = L.index := rfl
      _ ≤ (frattini P).index := Nat.le_of_dvd (by rw [hΦ]; positivity) hdvd
      _ = 2 ^ pGeneratorRank 2 P := hΦ
      _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) hdP11
  · have hKN' : K = N := by rw [hKdef, hNdef, hQD']
    have hdNK0 : pGeneratorRank 2 (N ⧸ K.subgroupOf N) = 0 := by
      have hcard : Nat.card (N ⧸ K.subgroupOf N) = 1 := by
        rw [hKN', subgroupOf_self]
        exact index_top
      have := pGeneratorRank_le_log_card 2 (X := N ⧸ K.subgroupOf N)
      rw [hcard, Nat.log_one_right] at this
      omega
    have hdP10 : pGeneratorRank 2 P ≤ 10 := by omega
    exact ⟨hdP10, hgen 10 hdP10⟩

end CFSG.LocalAnalysis.GorensteinLyons
