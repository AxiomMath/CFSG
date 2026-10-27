module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Omega1
import CFSG.LieType.SeitzGeneration.UnitaryNonabNonPthAlgebra
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LieType.SeitzGeneration
open scoped commutatorElement MatrixGroups IsMulCommutative

open Polynomial

private theorem hasEnoughRootsOfUnity_of_dvd_card_sub_one {F : Type} [Field F] [Finite F]
    {n : ℕ} [NeZero n] (hn : n ∣ Nat.card F - 1) : HasEnoughRootsOfUnity F n := by
  set N := Nat.card F - 1 with hN
  have hNu : Nat.card Fˣ = N := Nat.card_units F
  have hNpos : 0 < N := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  haveI : NeZero N := ⟨by omega⟩
  have htop : rootsOfUnity N F = ⊤ := by
    ext x
    simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
    rw [← hNu]
    exact pow_card_eq_one'
  have hNcard : N ≤ Nat.card (rootsOfUnity N F) := by
    rw [htop, Subgroup.card_top, hNu]
  haveI : HasEnoughRootsOfUnity F N := HasEnoughRootsOfUnity.of_card_le hNcard
  exact HasEnoughRootsOfUnity.of_dvd F hn

private lemma mapsTo_eigenspace_of_comm {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {f h : Module.End F V} (hc : Commute f h) (μ : F) :
    Set.MapsTo f (h.eigenspace μ) (h.eigenspace μ) := by
  intro x hx
  exact Module.End.mem_eigenspace_iff.mpr (by
    rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply,
      Module.End.mem_eigenspace_iff.mp hx, map_smul])

private theorem natDegree_dvd_finrank_of_aeval_eq_zero
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {P : K[X]} (hP : Irreducible P) {T : Module.End K M} (hT : aeval T P = 0) :
    P.natDegree ∣ Module.finrank K M := by
  have : Fact (Irreducible P) := ⟨hP⟩
  let ψ : AdjoinRoot P →+* Module.End K M :=
    Ideal.Quotient.lift (Ideal.span {P}) (aeval T).toRingHom (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hT])
  let _ : Module (AdjoinRoot P) M := Module.compHom M ψ
  have hψ : ∀ c : K, ψ (algebraMap K (AdjoinRoot P) c) = algebraMap _ _ c := by
    intro c
    change (aeval T) (C c) = _
    rw [aeval_C]
  have : IsScalarTower K (AdjoinRoot P) M := by
    constructor
    intro c k m
    change ψ (c • k) m = c • ψ k m
    rw [Algebra.smul_def, map_mul, hψ]
    rfl
  have hpb := (AdjoinRoot.powerBasis hP.ne_zero).finrank
  rw [AdjoinRoot.powerBasis_dim] at hpb
  have : Module.Finite (AdjoinRoot P) M := Module.Finite.of_restrictScalars_finite K _ _
  rw [← Module.finrank_mul_finrank K (AdjoinRoot P) M, hpb]
  exact dvd_mul_right _ _

theorem tor_lemmaB {p d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) {G : Subgroup (GL (Fin d) F)}
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (hel : MElemMod p d F G) {g : GL (Fin d) F}
    (hg : g ∈ G) (hgc : ∀ a : Fˣ, g ^ p ≠ (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p)
    (hrad : ∀ h ∈ G,
      (∃ a : Fˣ, h ^ p = (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p) →
        ∀ g' ∈ G, ⁅g', h⁆ = 1) :
    p ∣ d ∧ (LargeEvenScalars (Fin d) F).relIndex G ≤ p ^ (d / p) := by
  classical
  by_cases hd0 : d = 0
  · subst hd0
    exact absurd (Subsingleton.elim (g ^ p) ((Matrix.GeneralLinearGroup.scalar (Fin 0) 1) ^ p))
      (hgc 1)
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hel_mem : ∀ x : ↥G, ∃ a : Fˣ,
      Matrix.GeneralLinearGroup.scalar (Fin d) a = (x : GL (Fin d) F) ^ p := by
    intro x
    have h : (x : GL (Fin d) F) ^ p ∈
        (Matrix.GeneralLinearGroup.scalar (Fin d)).range := by
      simpa [largeEvenScalars_def] using hel.1 x x.2
    exact MonoidHom.mem_range.mp h
  let s : ↥G → Fˣ := fun x => Classical.choose (hel_mem x)
  have hs : ∀ x : ↥G,
      Matrix.GeneralLinearGroup.scalar (Fin d) (s x) = (x : GL (Fin d) F) ^ p :=
    fun x => Classical.choose_spec (hel_mem x)
  have scalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin d) : Fˣ → GL (Fin d) F) := by
    intro a b hab
    exact Units.ext (Matrix.scalar_inj.mp (by
      have h := congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) hab
      exact h))
  have comm_scalar : ∀ z ∈ LargeEvenScalars (Fin d) F, ∀ w : GL (Fin d) F, Commute w z := by
    intro z hz w
    have h : z ∈ (Matrix.GeneralLinearGroup.scalar (Fin d)).range := by
      simpa [largeEvenScalars_def] using hz
    obtain ⟨μ, rfl⟩ := MonoidHom.mem_range.mp h
    exact (Matrix.GeneralLinearGroup.scalar_commute μ w).symm
  have hmul : ∀ x y : ↥G, s (x * y) = s x * s y := by
    intro x y
    apply scalar_inj
    rw [map_mul, hs, hs, hs]
    have hz : ⁅(y : GL (Fin d) F), (x : GL (Fin d) F)⁆ ∈ LargeEvenScalars (Fin d) F :=
      hel.2 y y.2 x x.2
    have hcx : Commute (x : GL (Fin d) F) ⁅(y : GL (Fin d) F), (x : GL (Fin d) F)⁆ :=
      comm_scalar _ hz (x : GL (Fin d) F)
    have hcy : Commute (y : GL (Fin d) F) ⁅(y : GL (Fin d) F), (x : GL (Fin d) F)⁆ :=
      comm_scalar _ hz (y : GL (Fin d) F)
    have h := CFSG.GH74.GLS.Stage2.Bender.Thm1.mul_pow_class_two hcx hcy p
    have hzp : ⁅(y : GL (Fin d) F), (x : GL (Fin d) F)⁆ ^ p = 1 := by
      rw [Commute.commutatorElement_pow_left (h := hcy) p]
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (by
        simpa [largeEvenScalars_def] using hel.1 y y.2)
      rw [← ha]
      exact commutatorElement_eq_one_iff_commute.mpr
        (Matrix.GeneralLinearGroup.scalar_commute a (x : GL (Fin d) F))
    have hch : ⁅(y : GL (Fin d) F), (x : GL (Fin d) F)⁆ ^ (p.choose 2) = 1 := by
      obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := by
        rcases hp.eq_two_or_odd' with h | h
        · exact absurd h hp2
        · exact h
      have hchoose : p.choose 2 = p * m := by
        rw [Nat.choose_two_right, hm]
        have : (2 * m + 1) * (2 * m + 1 - 1) = 2 * ((2 * m + 1) * m) := by
          rw [show 2 * m + 1 - 1 = 2 * m by omega]; ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      rw [hchoose, pow_mul, hzp, one_pow]
    rw [Subgroup.coe_mul, h, hch, mul_one]
  let c : ↥G →* Fˣ :=
    { toFun := s
      map_one' := by
        apply scalar_inj
        rw [hs]
        simp
      map_mul' := hmul }
  let Q := Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range
  let C : ↥G →* Q := (QuotientGroup.mk' (powMonoidHom p : Fˣ →* Fˣ).range).comp c
  let K₀ : Subgroup ↥G := C.ker
  have hK0_central : ∀ h : ↥G, h ∈ K₀ → ∀ g' : ↥G, g' * h = h * g' := by
    intro h hh g'
    have hex : ∃ a : Fˣ, ((h : ↥G) : GL (Fin d) F) ^ p =
        (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p := by
      have hmem : c h ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
        have hQ : ((c h : Fˣ) : Q) = 1 := by
          have hker : C h = 1 := MonoidHom.mem_ker.mp hh
          simpa only [C, MonoidHom.comp_apply, QuotientGroup.mk'_apply] using hker
        exact (QuotientGroup.eq_one_iff (N := (powMonoidHom p : Fˣ →* Fˣ).range)
          (c h)).mp hQ
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
      have ha' : a ^ p = c h := ha
      refine ⟨a, ?_⟩
      calc ((h : ↥G) : GL (Fin d) F) ^ p
          = Matrix.GeneralLinearGroup.scalar (Fin d) (s h) := (hs h).symm
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) (a ^ p) := by rw [ha']; rfl
        _ = (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p := by rw [map_pow]
    apply Subtype.ext
    simpa using commutatorElement_eq_one_iff_mul_comm.mp
      (hrad (h : GL (Fin d) F) h.2 hex (g' : GL (Fin d) F) g'.2)
  let K₁ : Subgroup ↥G :=
    { carrier := {x | x ∈ K₀ ∧ x ^ p = 1}
      mul_mem' := by
        intro x y hx hy
        refine ⟨K₀.mul_mem hx.1 hy.1, ?_⟩
        have hcomm : Commute x y := (hK0_central x hx.1 y).symm
        rw [hcomm.mul_pow p, hx.2, hy.2, mul_one]
      one_mem' := ⟨K₀.one_mem, one_pow p⟩
      inv_mem' := by
        intro x hx
        refine ⟨K₀.inv_mem hx.1, ?_⟩
        rw [inv_pow, hx.2, inv_one] }
  let G₀ : Subgroup (GL (Fin d) F) := K₀.map G.subtype
  let G₁ : Subgroup (GL (Fin d) F) := K₁.map G.subtype
  have hCg : C ⟨g, hg⟩ ≠ 1 := by
    intro h
    have hmem : c ⟨g, hg⟩ ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
      have hQ : ((c ⟨g, hg⟩ : Fˣ) : Q) = 1 := by
        simpa only [C, MonoidHom.comp_apply, QuotientGroup.mk'_apply] using h
      exact (QuotientGroup.eq_one_iff (N := (powMonoidHom p : Fˣ →* Fˣ).range)
        (c ⟨g, hg⟩)).mp hQ
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
    have ha' : a ^ p = c ⟨g, hg⟩ := ha
    exact hgc a (by
      calc g ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) (s ⟨g, hg⟩) :=
            (hs ⟨g, hg⟩).symm
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) (a ^ p) := by rw [ha']; rfl
        _ = (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p := by rw [map_pow])
  have hQcard : Nat.card Q = p := by
    have h1 : Nat.card Q = (powMonoidHom p : Fˣ →* Fˣ).range.index := rfl
    rw [h1, IsCyclic.index_powMonoidHom_range, Nat.card_units F, Nat.gcd_eq_right hpF]
  have hK0_index : K₀.index = p := by
    rw [Subgroup.index_ker]
    have hdvd : Nat.card C.range ∣ p := by
      have h := Subgroup.card_mul_index (H := C.range)
      rw [hQcard] at h
      exact ⟨C.range.index, h.symm⟩
    have hne : C.range ≠ ⊥ := by
      intro hbot
      exact hCg (Subgroup.mem_bot.mp (by
        have : C ⟨g, hg⟩ ∈ C.range := ⟨⟨g, hg⟩, rfl⟩
        rwa [hbot] at this))
    rcases hp.eq_one_or_self_of_dvd (Nat.card C.range) hdvd with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq C.range h1) hne
    · exact h1
  have hG1_exp : ∀ x : G₁, x ^ p = 1 := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    apply Subtype.ext
    show x ^ p = 1
    rw [← hkx, ← map_pow]
    have hk1 : (k : ↥G) ^ p = 1 := hk.2
    rw [hk1, map_one]
  have hG1p : IsPGroup p G₁ := fun x => ⟨1, by rw [pow_one]; exact hG1_exp x⟩
  have hcardUnit : IsUnit (Nat.card G₁ : F) := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    have h2dvd : 2 ∣ Nat.card G₁ := (CharP.cast_eq_zero_iff F 2 _).mp hzero
    obtain ⟨k, hk⟩ := hG1p.exists_card_eq
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    rw [hk] at h2dvd
    exact (Nat.not_even_iff_odd.mpr hpodd.pow) (even_iff_two_dvd.mpr h2dvd)
  have hExpDvd : Monoid.exponent G₁ ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hG1_exp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : HasEnoughRootsOfUnity F p := hasEnoughRootsOfUnity_of_dvd_card_sub_one hpF
  haveI : HasEnoughRootsOfUnity F (Monoid.exponent G₁) :=
    HasEnoughRootsOfUnity.of_dvd F hExpDvd
  haveI : IsMulCommutative G₁ := IsMulCommutative.of_comm fun a b => by
    obtain ⟨ka, hka, hkaeq⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨kb, hkb, hkbeq⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change (a : GL (Fin d) F) * (b : GL (Fin d) F) = (b : GL (Fin d) F) * (a : GL (Fin d) F)
    rw [← hkaeq, ← hkbeq, ← map_mul, ← map_mul]
    exact congrArg G.subtype (hK0_central ka hka.1 kb).symm
  have hsc_le_K0 : (LargeEvenScalars (Fin d) F).subgroupOf G ≤ K₀ := by
    intro z hz
    have hzsc : (z : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := hz
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (by simpa [largeEvenScalars_def] using hzsc)
    rw [MonoidHom.mem_ker]
    show C z = 1
    have hsz : s z = a ^ p := by
      apply scalar_inj
      calc Matrix.GeneralLinearGroup.scalar (Fin d) (s z)
          = (z : GL (Fin d) F) ^ p := hs z
        _ = (Matrix.GeneralLinearGroup.scalar (Fin d) a) ^ p := by rw [← ha]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) (a ^ p) := by rw [map_pow]
    have hCval : C z = ((a ^ p : Fˣ) : Q) := by
      simp only [C, MonoidHom.comp_apply]
      rw [show c z = a ^ p from hsz]
      rfl
    rw [hCval]
    exact (QuotientGroup.eq_one_iff (N := (powMonoidHom p : Fˣ →* Fˣ).range) (a ^ p)).mpr
      ⟨a, rfl⟩
  have hsc_le_G0 : LargeEvenScalars (Fin d) F ≤ G₀ := by
    intro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hZG hz⟩, hsc_le_K0 ?_, rfl⟩
    exact hz
  have hG0_le_G : G₀ ≤ G := by
    rintro x ⟨k, hk, rfl⟩
    exact k.2
  have hK0_eq : K₀ = (LargeEvenScalars (Fin d) F).subgroupOf G ⊔ K₁ := by
    apply le_antisymm
    · intro h hh
      have hmem : c h ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
        have hQ : ((c h : Fˣ) : Q) = 1 := by
          have hker : C h = 1 := MonoidHom.mem_ker.mp hh
          simpa only [C, MonoidHom.comp_apply, QuotientGroup.mk'_apply] using hker
        exact (QuotientGroup.eq_one_iff (N := (powMonoidHom p : Fˣ →* Fˣ).range)
          (c h)).mp hQ
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
      have ha' : a ^ p = c h := ha
      let z : ↥G := ⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hZG (by
        rw [largeEvenScalars_def]; exact ⟨a, rfl⟩)⟩
      have hzsc : z ∈ (LargeEvenScalars (Fin d) F).subgroupOf G := by
        show (z : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F
        rw [largeEvenScalars_def]; exact ⟨a, rfl⟩
      have hzK0 : z ∈ K₀ := hsc_le_K0 hzsc
      have htK1 : z⁻¹ * h ∈ K₁ := by
        refine ⟨K₀.mul_mem (K₀.inv_mem hzK0) hh, ?_⟩
        have hzp : (z : GL (Fin d) F) ^ p = (h : GL (Fin d) F) ^ p := by
          show Matrix.GeneralLinearGroup.scalar (Fin d) a ^ p = (h : GL (Fin d) F) ^ p
          rw [← map_pow, ha']
          exact hs h
        have hzpG : z ^ p = h ^ p := Subtype.ext hzp
        have hcomm : Commute z⁻¹ h :=
          (show Commute z h from (hK0_central z hzK0 h).symm).inv_left
        rw [hcomm.mul_pow p, inv_pow, hzpG, inv_mul_cancel]
      have heq : z * (z⁻¹ * h) = h := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [← heq]
      exact Subgroup.mul_mem_sup hzsc htK1
    · refine sup_le hsc_le_K0 ?_
      intro x hx
      exact hx.1
  have hG0_eq : G₀ = LargeEvenScalars (Fin d) F ⊔ G₁ := by
    show K₀.map G.subtype = LargeEvenScalars (Fin d) F ⊔ K₁.map G.subtype
    rw [hK0_eq, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hZG]
  have hmap_top : Subgroup.map G.subtype (⊤ : Subgroup ↥G) = G := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hG0_relIndex : G₀.relIndex G = K₀.index := by
    have h := Subgroup.relIndex_map_map_of_injective (f := G.subtype) K₀ ⊤ G.subtype_injective
    rw [hmap_top, Subgroup.relIndex_top_right] at h
    exact h
  have hsc_ker : LargeEvenScalars (Fin d) F ⊓ G₁ =
      (powMonoidHom p : Fˣ →* Fˣ).ker.map
        (Matrix.GeneralLinearGroup.scalar (Fin d)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxsc, hxG1⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨k, hkK1, hk⟩ := Subgroup.mem_map.mp hxG1
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (by simpa [largeEvenScalars_def] using hxsc)
      have hap : a ^ p = 1 := by
        apply scalar_inj
        have hk1 : (k : ↥G) ^ p = 1 := hkK1.2
        have h1 : G.subtype (k ^ p) = G.subtype (1 : ↥G) := congrArg G.subtype hk1
        rw [map_pow, ha, ← hk, ← map_pow]
        simpa [map_one] using h1
      exact Subgroup.mem_map.mpr ⟨a, MonoidHom.mem_ker.mpr hap, ha⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [largeEvenScalars_def]; exact ⟨a, rfl⟩
      · refine Subgroup.mem_map.mpr ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin d) a,
            hZG (by rw [largeEvenScalars_def]; exact ⟨a, rfl⟩)⟩, ?_, rfl⟩
        refine ⟨?_, ?_⟩
        · refine hsc_le_K0 ?_
          rw [Subgroup.mem_subgroupOf]
          show Matrix.GeneralLinearGroup.scalar (Fin d) a ∈ LargeEvenScalars (Fin d) F
          rw [largeEvenScalars_def]; exact ⟨a, rfl⟩
        · apply Subtype.ext
          show Matrix.GeneralLinearGroup.scalar (Fin d) a ^ p = 1
          have ha' : a ^ p = 1 := MonoidHom.mem_ker.mp ha
          rw [← map_pow, ha', map_one]
  have hcap : Nat.card (LargeEvenScalars (Fin d) F ⊓ G₁ :
      Subgroup (GL (Fin d) F)) = p := by
    have hker_card : Nat.card (powMonoidHom p : Fˣ →* Fˣ).ker = p := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.card_units F, Nat.gcd_eq_right hpF]
    rw [hsc_ker]
    rw [Subgroup.card_map_of_injective (K := (powMonoidHom p : Fˣ →* Fˣ).ker) scalar_inj,
      hker_card]
  let V := Fin d → F
  let toEnd : GL (Fin d) F →* Module.End F V :=
    (Matrix.toLinAlgEquiv'.toRingEquiv.toMonoidHom).comp
      (Units.coeHom (Matrix (Fin d) (Fin d) F))
  let ρ : G₁ →* Module.End F V := toEnd.comp G₁.subtype
  let ρg : Module.End F V := toEnd g
  have hρg_pow : ρg ^ p = algebraMap F (Module.End F V) ((s ⟨g, hg⟩ : Fˣ) : F) := by
    have h1 : ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p =
        ((s ⟨g, hg⟩ : Fˣ) : F) • (1 : Matrix (Fin d) (Fin d) F) := by
      rw [← Units.val_pow_eq_pow_val, ← hs ⟨g, hg⟩, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_smul, map_one] at h2
    show Matrix.toLinAlgEquiv' ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p = _
    rw [h2, Algebra.algebraMap_eq_smul_one]
  have hc : ¬ ∃ μ : F, μ ^ p = ((s ⟨g, hg⟩ : Fˣ) : F) := by
    rintro ⟨μ, hμ⟩
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact (s ⟨g, hg⟩).ne_zero (by rw [hμ.symm]; exact zero_pow hp.ne_zero)
    let μu : Fˣ := Units.mk0 μ hμ0
    have hsp : s ⟨g, hg⟩ = μu ^ p := by
      apply Units.ext
      show ((s ⟨g, hg⟩ : Fˣ) : F) = ((μu ^ p : Fˣ) : F)
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      exact hμ.symm
    exact hgc μu (by rw [← hs ⟨g, hg⟩, hsp, map_pow])
  have hρinj : Function.Injective ρ := by
    have toEnd_inj : Function.Injective toEnd := by
      intro a b hab
      have h1 : Matrix.toLinAlgEquiv' ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          Matrix.toLinAlgEquiv' ((b : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
        simpa [toEnd] using hab
      exact Units.ext ((Matrix.toLinAlgEquiv').injective h1)
    exact toEnd_inj.comp G₁.subtype_injective
  have hρg_comm : ∀ t : G₁, Commute ρg (ρ t) := by
    intro t
    obtain ⟨k, hkK1, hk⟩ := Subgroup.mem_map.mp t.2
    have hgt : Commute g (t : GL (Fin d) F) := by
      rw [← hk]
      exact congrArg (fun z : ↥G => (z : GL (Fin d) F))
        (hK0_central k hkK1.1 ⟨g, hg⟩)
    simpa [ρ, ρg] using hgt.map toEnd
  let W : (G₁ →* Fˣ) → Submodule F V := fun χ => ⨅ t : G₁, (ρ t).eigenspace (χ t)
  have hind : iSupIndep W := by
    simpa [W] using TauCeti.iSupIndep_iInf_eigenspace_unitHom (ρ := ρ)
  have htop : ⨆ χ : G₁ →* Fˣ, W χ = ⊤ := by
    simpa [W] using TauCeti.iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup (ρ := ρ) hcardUnit
  let S := {χ : G₁ →* Fˣ // W χ ≠ ⊥}
  haveI : Fintype S := hind.fintypeNeBotOfFiniteDimensional
  let b := Fintype.card S
  have hindS : iSupIndep (fun χ : S => W χ.1) := hind.comp Subtype.coe_injective
  have htopS : ⨆ χ : S, W χ.1 = ⊤ := by
    rw [← htop]
    apply le_antisymm
    · exact iSup_le fun χ => le_iSup W χ.1
    · refine iSup_le fun χ => ?_
      by_cases h : W χ = ⊥
      · rw [h]; exact bot_le
      · exact le_iSup (fun χ : S => W χ.1) ⟨χ, h⟩
  have hintS : DirectSum.IsInternal (fun χ : S => W χ.1) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindS htopS
  have hfin : Module.finrank F V = ∑ χ : S, Module.finrank F (W χ.1) := by
    rw [Module.finrank_eq_card_basis
        (hintS.collectedBasis (fun χ : S => Module.finBasis F (W χ.1))),
      Fintype.card_sigma]
    simp
  have p_le_finrank_W : ∀ χ : S, p ≤ Module.finrank F (W χ.1) := by
    intro χ
    refine NonPth.p_le_finrank_of_stable hp hρg_pow hc ?_ χ.2
    intro s hs
    dsimp only [W] at hs ⊢
    rw [Submodule.mem_iInf] at hs ⊢
    intro t
    exact mapsTo_eigenspace_of_comm (hρg_comm t) (χ.1 t) (hs t)
  have hb_le : b ≤ d / p := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    calc b * p = ∑ _ : S, p := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ χ : S, Module.finrank F (W χ.1) :=
          Finset.sum_le_sum fun χ _ => p_le_finrank_W χ
      _ = Module.finrank F V := hfin.symm
      _ = d := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hG1_le : Nat.card G₁ ≤ p ^ b := by
    have hinj : Function.Injective (fun t : G₁ => fun χ : S =>
        (⟨χ.1 t, by rw [mem_rootsOfUnity, ← map_pow, hG1_exp t, map_one]⟩ :
          rootsOfUnity p F)) := by
      intro t t' h
      have hχ : ∀ χ : S, χ.1 t = χ.1 t' := fun χ =>
        congrArg (fun z : rootsOfUnity p F => (z : Fˣ)) (congrFun h χ)
      apply hρinj
      apply LinearMap.ext
      intro v
      have hv : v ∈ ⨆ χ : S, W χ.1 := by rw [htopS]; trivial
      refine Submodule.iSup_induction (fun χ : S => W χ.1)
        (motive := fun v => ρ t v = ρ t' v) hv ?_ ?_ ?_
      · intro χ w hw
        have hwmem : w ∈ ⨅ u : G₁, (ρ u).eigenspace (χ.1 u) := by simpa [W] using hw
        have h1 : ρ t w = (χ.1 t : F) • w :=
          Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hwmem t)
        have h2 : ρ t' w = (χ.1 t' : F) • w :=
          Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hwmem t')
        rw [h1, h2, hχ χ]
      · simp
      · intro a c' ha hc'; rw [map_add, map_add, ha, hc']
    calc Nat.card G₁ ≤ Nat.card (S → rootsOfUnity p F) :=
          Nat.card_le_card_of_injective _ hinj
      _ = Nat.card (rootsOfUnity p F) ^ Nat.card S := Nat.card_fun
      _ ≤ p ^ Nat.card S := Nat.pow_le_pow_left (card_rootsOfUnity F p) _
      _ = p ^ b := by rw [Nat.card_eq_fintype_card]
  have hG1_le_pow : Nat.card G₁ ≤ p ^ (d / p) :=
    hG1_le.trans (Nat.pow_le_pow_right hp.pos hb_le)
  have hrel_sc_G0 : (LargeEvenScalars (Fin d) F).relIndex G₀ =
      (LargeEvenScalars (Fin d) F).relIndex G₁ := by
    rw [hG0_eq]
    exact Subgroup.relIndex_sup_left (H := G₁) (K := LargeEvenScalars (Fin d) F)
  have hG0_rel : G₀.relIndex G = p := by
    rw [hG0_relIndex, hK0_index]
  have hrel_card : (LargeEvenScalars (Fin d) F).relIndex G₁ *
      Nat.card (LargeEvenScalars (Fin d) F ⊓ G₁ : Subgroup (GL (Fin d) F)) =
        Nat.card G₁ :=
    Subgroup.relIndex_mul_card (LargeEvenScalars (Fin d) F) G₁
  have hfinal : (LargeEvenScalars (Fin d) F).relIndex G = Nat.card G₁ := by
    have h1 : (LargeEvenScalars (Fin d) F).relIndex G =
        (LargeEvenScalars (Fin d) F).relIndex G₀ * G₀.relIndex G :=
      (Subgroup.relIndex_mul_relIndex (LargeEvenScalars (Fin d) F) G₀ G
        hsc_le_G0 hG0_le_G).symm
    rw [h1, hrel_sc_G0, hG0_rel, ← hcap]
    exact hrel_card
  have hpd : p ∣ d := by
    haveI : Nontrivial V := Function.nontrivial
    have hmin : minpoly F ρg = Polynomial.X ^ p - Polynomial.C ((s ⟨g, hg⟩ : Fˣ) : F) :=
      NonPth.minpoly_eq_X_pow_sub_C hp hρg_pow hc
    have hPirr : Irreducible (minpoly F ρg) := by
      rw [hmin]; exact NonPth.irreducible_X_pow_sub_C hp hc
    have hdvd : (minpoly F ρg).natDegree ∣ Module.finrank F V :=
      natDegree_dvd_finrank_of_aeval_eq_zero hPirr (minpoly.aeval F ρg)
    rw [hmin, natDegree_X_pow_sub_C] at hdvd
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdvd
  exact ⟨hpd, by rw [hfinal]; exact hG1_le_pow⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
