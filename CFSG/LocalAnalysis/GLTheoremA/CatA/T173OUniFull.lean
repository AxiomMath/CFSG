module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniIvDiag
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.GLTheoremA.T173A
open scoped MatrixGroups

private theorem p_dvd_natCard_units {p n : ℕ} {F : Type} [Field F] [Finite F]
    (hpq : p ∣ 2 ^ n + 1) (hcardF : Nat.card F = (2 ^ n) ^ 2) :
    p ∣ Nat.card Fˣ := by
  have h2dvd_sq : p ∣ (2 ^ n) ^ 2 - 1 := by
    have hmod : ((2 ^ n) ^ 2 : ℕ) ≡ 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have h1 : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := by
        obtain ⟨k, hk⟩ := hpq
        rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      have hx : ((2 ^ n : ℕ) : ZMod p) = -1 := by
        have h := congrArg (fun z : ZMod p => z - 1) h1
        rw [Nat.cast_add, Nat.cast_one] at h
        rwa [add_sub_cancel_right, zero_sub] at h
      have hsq : (((2 ^ n) ^ 2 : ℕ) : ZMod p) = ((2 ^ n : ℕ) : ZMod p) ^ 2 := by
        push_cast
        ring
      rw [hsq, hx]
      rw [show ((1 : ℕ) : ZMod p) = 1 by norm_num]
      exact neg_one_sq (R := ZMod p)
    have hmod' : 1 ≡ (2 ^ n) ^ 2 [MOD p] := hmod.symm
    rwa [Nat.modEq_iff_dvd' (Nat.one_le_pow 2 (2 ^ n) (by positivity))] at hmod'
  rw [Nat.card_units, hcardF]
  exact h2dvd_sq

private theorem card_rootsOfUnity_eq {p n : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hcardF : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card (rootsOfUnity p F) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvd_card : p ∣ Nat.card Fˣ := p_dvd_natCard_units hpq hcardF
  obtain ⟨ω, hωorder⟩ := exists_prime_orderOf_dvd_card' p hp_dvd_card
  have hmem : ω ∈ rootsOfUnity p F := by
    rw [mem_rootsOfUnity, ← hωorder]
    exact pow_orderOf_eq_one ω
  have hge : p ≤ Nat.card (rootsOfUnity p F) := by
    calc p = Nat.card (Subgroup.zpowers ω) := by rw [Nat.card_zpowers, hωorder]
      _ ≤ Nat.card (rootsOfUnity p F) :=
        Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hmem)
  exact le_antisymm (card_rootsOfUnity (R := F) (k := p)) hge

private theorem diagHom_injective (d : ℕ) (F : Type) [Field F] :
    Function.Injective (diagHom d F) := by
  intro f g h
  ext i
  have hii := congrArg (fun x : GL (Fin d) F =>
    ((x : Matrix (Fin d) (Fin d) F) i i)) h
  simpa [diagHom] using hii

private def diagProd (p d : ℕ) (F : Type) [Field F] :
    (Fin d → rootsOfUnity p F) →* rootsOfUnity p F where
  toFun g := ⟨∏ i, (g i : Fˣ),
    Subgroup.prod_mem (rootsOfUnity p F) fun i _ => (g i).2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    simp [Finset.prod_mul_distrib]

private theorem diagProd_surjective {p d : ℕ} {F : Type} [Field F] (hd : 1 ≤ d) :
    Function.Surjective (diagProd p d F) := by
  intro ζ
  let i0 : Fin d := ⟨0, hd⟩
  refine ⟨fun i => if i = i0 then ζ else 1, ?_⟩
  apply Subtype.ext
  show (∏ i, ((if i = i0 then ζ else 1 : rootsOfUnity p F) : Fˣ)) = (ζ : Fˣ)
  rw [Finset.prod_eq_single i0]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i0) h

private theorem card_diagPTorsion_le {p d : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hμ : Nat.card (rootsOfUnity p F) = p) (hd : 1 ≤ d) :
    Nat.card (diagPTorsion p d F) ≤ p ^ (d - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let prod := diagProd p d F
  have hsurj : Function.Surjective prod := diagProd_surjective hd
  have hrange : Nat.card prod.range = p := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    exact hμ
  have hdom : Nat.card (Fin d → rootsOfUnity p F) = p ^ d := by
    rw [Nat.card_fun, Nat.card_fin, hμ]
  have hker : Nat.card prod.ker = p ^ (d - 1) := by
    have h := Subgroup.card_ker_mul_card_range prod
    rw [hdom, hrange] at h
    have hpd : p ^ d = p ^ (d - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [hpd] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  rw [← hker]
  let toKer : ↥(diagPTorsion p d F) → ↥prod.ker := fun f =>
    ⟨fun i => ⟨f.1 i, (mem_rootsOfUnity p (f.1 i)).mpr (by
      have h := congrFun (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp f.2).1) i
      simpa using h)⟩, by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show (∏ i, (f.1 i : Fˣ)) = 1
      exact MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp f.2).2⟩
  refine Nat.card_le_card_of_injective toKer ?_
  intro f g hfg
  apply Subtype.ext
  funext i
  have h := congrFun (congrArg (fun x : ↥prod.ker =>
    ((x : prod.ker) : Fin d → rootsOfUnity p F)) hfg) i
  exact congrArg (fun ζ : rootsOfUnity p F => (ζ : Fˣ)) h

private theorem card_diagPGroup_le {p d : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hμ : Nat.card (rootsOfUnity p F) = p) (hd : 1 ≤ d) :
    Nat.card (diagPGroup p d F) ≤ p ^ (d - 1) := by
  rw [diagPGroup, Subgroup.card_map_of_injective (diagHom_injective d F)]
  exact card_diagPTorsion_le hp hμ hd

private theorem diagEntries_mem_diagPTorsion {p d : ℕ} {F : Type} [Field F]
    {a : GL (Fin d) F}
    (hdiag : (a : Matrix (Fin d) (Fin d) F) = Matrix.diagonal (fun i => a i i))
    (hdet : (a : Matrix (Fin d) (Fin d) F).det = 1) (hap : a ^ p = 1) :
    ∃ f : Fin d → Fˣ, f ∈ diagPTorsion p d F ∧ diagHom d F f = a := by
  have hdet_ne : (a : Matrix (Fin d) (Fin d) F).det ≠ 0 := by
    simpa using (Matrix.GeneralLinearGroup.det a).ne_zero
  have hne : ∀ i, (a : Matrix (Fin d) (Fin d) F) i i ≠ 0 := by
    intro i hi0
    apply hdet_ne
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi0
  let f : Fin d → Fˣ :=
    fun i => Units.mk0 ((a : Matrix (Fin d) (Fin d) F) i i) (hne i)
  have hf_eq : diagHom d F f = a := by
    apply Units.ext
    rw [hdiag]
    rfl
  have hfT : f ∈ diagPTorsion p d F := by
    rw [diagPTorsion, Subgroup.mem_inf]
    constructor
    · rw [MonoidHom.mem_ker]
      have h1 : diagHom d F (f ^ p) = 1 := by
        rw [map_pow, hf_eq, hap]
      funext i
      have h2 := congrArg (fun g : GL (Fin d) F =>
        ((g : Matrix (Fin d) (Fin d) F) i i)) h1
      exact Units.ext (by simpa [diagHom] using h2)
    · rw [MonoidHom.mem_ker]
      show (∏ i, f i) = 1
      have hprodF : ∏ i, (f i : F) = 1 := by
        have hdet_diag : ((diagHom d F f : GL (Fin d) F) :
            Matrix (Fin d) (Fin d) F).det = ∏ i, (f i : F) := by
          change (Matrix.diagonal fun i => (f i : F)).det = ∏ i, (f i : F)
          rw [Matrix.det_diagonal]
        rw [← hf_eq] at hdet
        rwa [hdet_diag] at hdet
      apply Units.ext
      simpa using hprodF
  exact ⟨f, hfT, hf_eq⟩

private theorem le_diagPGroup_of_diagonal {p n d : ℕ} {F : Type} [Field F]
    {A : Subgroup (GL (Fin d) F)} (hA : A ≤ UniSU n d F) (hAe : IsElemAbelian p A)
    (hAd : ∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0) :
    A ≤ diagPGroup p d F := by
  intro a ha
  have hdiag : (a : Matrix (Fin d) (Fin d) F) = Matrix.diagonal (fun i => a i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]; exact hAd a ha i j hij
  obtain ⟨f, hfT, hf_eq⟩ := diagEntries_mem_diagPTorsion hdiag
    (det_eq_one_of_mem_UniSU (hA ha)) (hAe.2 a ha)
  rw [diagPGroup]
  exact Subgroup.mem_map.mpr ⟨f, hfT, hf_eq⟩

private theorem uniMk_ker_disjoint_of_isPGroup_two {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hcardF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 1 ≤ d)
    {M : Subgroup ↥(UniSU n d F)} (hM : IsPGroup 2 M) :
    M ⊓ (UniMk n d F).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxM, hxker⟩ := hx
  rw [Subgroup.mem_bot]
  have hxsc : (x : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
    have hxker' : x ∈ (LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F) := by
      simpa [UniMk, LargeEvenProjMk, QuotientGroup.ker_mk'] using hxker
    exact Subgroup.mem_subgroupOf.mp hxker'
  obtain ⟨c, hc⟩ := hxsc
  have hcSU : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ StatedSU d (2 ^ n) F := by
    have hxSU : (x : GL (Fin d) F) ∈ UniSU n d F := x.2
    rw [hc]
    exact hxSU
  have hcq : c ^ (2 ^ n + 1) = 1 :=
    ((CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := n) (n := d)
      Nat.prime_two (by simpa using hcardF) hd c).1 hcSU).2
  have hxq : x ^ (2 ^ n + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (x : GL (Fin d) F) ^ (2 ^ n + 1) = 1
    rw [← hc, ← map_pow, hcq, map_one]
  obtain ⟨k, hk⟩ := hM ⟨x, hxM⟩
  have hk' : orderOf x ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk x hxM]
    exact orderOf_dvd_of_pow_eq_one hk
  have hodd : Odd (2 ^ n + 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    rw [pow_succ]
    exact ⟨2 ^ m, by ring⟩
  have hcop : Nat.Coprime (2 ^ k) (2 ^ n + 1) :=
    (hodd.coprime_two_left).pow_left k
  have hdvd : orderOf x ∣ Nat.gcd (2 ^ k) (2 ^ n + 1) :=
    Nat.dvd_gcd hk' (orderOf_dvd_of_pow_eq_one hxq)
  rw [hcop.gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hdvd)

private theorem pow_sub_one_le_natCard_A {p n d : ℕ} {F : Type} [Field F] [Finite F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : UniDiagFrame p n d F ψ Bbar A)
    (hcard : Nat.card Bbar = p ^ (d - 1)) :
    p ^ (d - 1) ≤ Nat.card A := by
  obtain ⟨hAsu, _hAe, _hAd, hBmap⟩ := hfr
  let φbar : ↥A → ↥Bbar := fun a =>
    ⟨ψ.symm (UniMk n d F ⟨a.1, hAsu a.2⟩), by
      have hψ : UniMk n d F ⟨a.1, hAsu a.2⟩ ∈ Bbar.map ψ.toMonoidHom := by
        rw [hBmap]
        exact Subgroup.mem_map_of_mem (UniMk n d F)
          (Subgroup.mem_subgroupOf.mpr a.2)
      exact (Subgroup.mem_map_equiv (f := ψ) (K := Bbar)).mp hψ⟩
  have hφsurj : Function.Surjective φbar := by
    intro b
    have hb : ψ b ∈ Bbar.map ψ.toMonoidHom := Subgroup.mem_map_of_mem ψ.toMonoidHom b.2
    rw [hBmap] at hb
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hb
    refine ⟨⟨(a : GL (Fin d) F), Subgroup.mem_subgroupOf.mp ha⟩, ?_⟩
    apply Subtype.ext
    show ψ.symm (UniMk n d F a) = b
    rw [haeq]
    exact ψ.symm_apply_apply b
  rw [← hcard]
  exact Nat.card_le_card_of_surjective φbar hφsurj

private theorem eq_diagPGroup_of_frame {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F}
    {Bbar : Subgroup Q} {A : Subgroup (GL (Fin d) F)}
    (hfr : UniDiagFrame p n d F ψ Bbar A) (hcard : Nat.card Bbar = p ^ (d - 1)) :
    A = diagPGroup p d F := by
  have hAsu : A ≤ UniSU n d F := hfr.1
  have hAe : IsElemAbelian p A := hfr.2.1
  have hAd : ∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0 :=
    hfr.2.2.1
  have hp : p.Prime := h.1
  have hpq : p ∣ 2 ^ n + 1 := h.2.1
  have hcardF : Nat.card F = (2 ^ n) ^ 2 := h.2.2.2.1
  have hd1 : 1 ≤ d := by
    have := h.2.2.2.2.2.1
    omega
  have hμ : Nat.card (rootsOfUnity p F) = p := card_rootsOfUnity_eq hp hpq hcardF
  have hDle : Nat.card (diagPGroup p d F) ≤ p ^ (d - 1) := card_diagPGroup_le hp hμ hd1
  have hAle : p ^ (d - 1) ≤ Nat.card A := pow_sub_one_le_natCard_A hfr hcard
  have hA_le_D : A ≤ diagPGroup p d F := le_diagPGroup_of_diagonal hAsu hAe hAd
  exact Subgroup.eq_of_le_of_card_ge hA_le_D (le_trans hDle hAle)

private theorem exists_pair_element {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) {A : Subgroup (GL (Fin d) F)}
    (hAeq : A = diagPGroup p d F) {I : Finset (Fin d)} (hI : 2 ≤ I.card) :
    ∃ (ω : Fˣ) (b b' : Fin d), orderOf ω = p ∧ b ∈ I ∧ b' ∈ I ∧ b ≠ b' ∧
      diagHom d F (pairUnit b b' ω ω⁻¹) ∈ A := by
  have hp : p.Prime := h.1
  have hpq : p ∣ 2 ^ n + 1 := h.2.1
  have hcardF : Nat.card F = (2 ^ n) ^ 2 := h.2.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvd_card : p ∣ Nat.card Fˣ := p_dvd_natCard_units hpq hcardF
  obtain ⟨ω, hωorder⟩ := exists_prime_orderOf_dvd_card' p hp_dvd_card
  have hωp : ω ^ p = 1 := by simpa [hωorder] using pow_orderOf_eq_one ω
  have hωip : (ω⁻¹) ^ p = 1 := by rw [inv_pow, hωp, inv_one]
  obtain ⟨b, hbI, b', hb'I, hbb'⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num : 1 < 2) hI)
  have hvbbD : diagHom d F (pairUnit b b' ω ω⁻¹) ∈ diagPGroup p d F := by
    rw [diagPGroup]
    exact Subgroup.mem_map.mpr
      ⟨pairUnit b b' ω ω⁻¹, pairUnit_mem_diagPTorsion hbb' hωp hωip (mul_inv_cancel ω), rfl⟩
  exact ⟨ω, b, b', hωorder, hbI, hb'I, hbb', by rw [hAeq]; exact hvbbD⟩

private theorem uniImage_ne_bot {n d : ℕ} {F : Type} [Field F] [Finite F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {I : Finset (Fin d)}
    {U_GL : Subgroup (GL (Fin d) F)} (hU_GL_ne : U_GL ≠ ⊥)
    (hU_GL_2 : IsPGroup 2 U_GL) (hU_GL_block : ∀ u ∈ U_GL, u ∈ UniBlockSet n d F I)
    (hcardF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    ((U_GL.subgroupOf (UniSU n d F)).map (UniMk n d F) |>.map ψ.symm.toMonoidHom :
      Subgroup Q) ≠ ⊥ := by
  have hU_SU : U_GL ≤ UniSU n d F := fun u hu => (hU_GL_block u hu).1
  let U_SU : Subgroup ↥(UniSU n d F) := U_GL.subgroupOf (UniSU n d F)
  let U_PSU : Subgroup (UniPSU n d F) := U_SU.map (UniMk n d F)
  let U : Subgroup Q := U_PSU.map ψ.symm.toMonoidHom
  have hU_SU_2 : IsPGroup 2 U_SU :=
    hU_GL_2.of_equiv (Subgroup.subgroupOfEquivOfLe hU_SU).symm
  have hU_SU_ne : U_SU ≠ ⊥ := by
    intro hbot
    apply hU_GL_ne
    apply bot_unique
    intro u hu
    have huSU : u ∈ UniSU n d F := hU_SU hu
    have hxu : (⟨u, huSU⟩ : ↥(UniSU n d F)) ∈ U_SU := Subgroup.mem_subgroupOf.mpr hu
    rw [hbot] at hxu
    have hx1 : (⟨u, huSU⟩ : ↥(UniSU n d F)) = 1 := Subgroup.mem_bot.mp hxu
    simpa using congrArg (fun y : ↥(UniSU n d F) => (y : GL (Fin d) F)) hx1
  have hU_SU_ker : U_SU ⊓ (UniMk n d F).ker = ⊥ :=
    uniMk_ker_disjoint_of_isPGroup_two hcardF hn hd hU_SU_2
  have hU_PSU_ne : U_PSU ≠ ⊥ := by
    intro hbot
    apply hU_SU_ne
    have hmap : U_SU.map (UniMk n d F) = ⊥ := by
      rw [← hbot]
    rw [Subgroup.map_eq_bot_iff] at hmap
    rw [eq_bot_iff]
    intro x hx
    have hxker : x ∈ U_SU ⊓ (UniMk n d F).ker := ⟨hx, hmap hx⟩
    rwa [hU_SU_ker] at hxker
  have hU_ne : U ≠ ⊥ := by
    intro hbot
    apply hU_PSU_ne
    exact (Subgroup.map_eq_bot_iff_of_injective (H := U_PSU)
      (f := ψ.symm.toMonoidHom) ψ.symm.injective).mp hbot
  simpa [U_SU, U_PSU, U] using hU_ne

private theorem uniImage_isPGroup {n d : ℕ} {F : Type} [Field F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {I : Finset (Fin d)}
    {U_GL : Subgroup (GL (Fin d) F)} (hU_GL_2 : IsPGroup 2 U_GL)
    (hU_GL_block : ∀ u ∈ U_GL, u ∈ UniBlockSet n d F I) :
    IsPGroup 2 ((U_GL.subgroupOf (UniSU n d F)).map (UniMk n d F) |>.map
      ψ.symm.toMonoidHom) := by
  have hU_SU : U_GL ≤ UniSU n d F := fun u hu => (hU_GL_block u hu).1
  let U_SU : Subgroup ↥(UniSU n d F) := U_GL.subgroupOf (UniSU n d F)
  have hU_SU_2 : IsPGroup 2 U_SU :=
    hU_GL_2.of_equiv (Subgroup.subgroupOfEquivOfLe hU_SU).symm
  have hU_PSU_2 : IsPGroup 2 (U_SU.map (UniMk n d F)) := hU_SU_2.map (UniMk n d F)
  exact hU_PSU_2.map ψ.symm.toMonoidHom

private theorem uniImage_le_Kbar {n d : ℕ} {F : Type} [Field F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Kbar : Subgroup Q}
    {I : Finset (Fin d)}
    (hKI : (Kbar.map ψ.toMonoidHom : Set (UniPSU n d F)) = UniBlockImage n d F I)
    {U_GL : Subgroup (GL (Fin d) F)} (hU_GL_block : ∀ u ∈ U_GL, u ∈ UniBlockSet n d F I) :
    ((U_GL.subgroupOf (UniSU n d F)).map (UniMk n d F) |>.map ψ.symm.toMonoidHom) ≤ Kbar := by
  have hU_SU : U_GL ≤ UniSU n d F := fun u hu => (hU_GL_block u hu).1
  let U_SU : Subgroup ↥(UniSU n d F) := U_GL.subgroupOf (UniSU n d F)
  let U_PSU : Subgroup (UniPSU n d F) := U_SU.map (UniMk n d F)
  have hmemKI : ∀ z : UniPSU n d F,
      z ∈ Kbar.map ψ.toMonoidHom ↔ z ∈ UniBlockImage n d F I :=
    fun z => Iff.of_eq (congrArg (fun s : Set (UniPSU n d F) => z ∈ s) hKI)
  have hU_PSU_le : U_PSU ≤ Kbar.map ψ.toMonoidHom := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxU : (x : GL (Fin d) F) ∈ U_GL := Subgroup.mem_subgroupOf.mp hx
    exact (hmemKI _).mpr ⟨x, hU_GL_block _ hxU, rfl⟩
  intro u hu
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu
  exact (Subgroup.mem_map_equiv (f := ψ) (K := Kbar)).mp (hU_PSU_le hy)

private theorem image_mem_Bbar {n d : ℕ} {F : Type} [Field F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)}
    (hBmap : Bbar.map ψ.toMonoidHom = (A.subgroupOf (UniSU n d F)).map (UniMk n d F))
    {g : ↥(UniSU n d F)} (hg : (g : GL (Fin d) F) ∈ A) :
    ψ.symm (UniMk n d F g) ∈ Bbar := by
  have h : UniMk n d F g ∈ Bbar.map ψ.toMonoidHom := by
    rw [hBmap]
    exact Subgroup.mem_map_of_mem (UniMk n d F) (Subgroup.mem_subgroupOf.mpr hg)
  exact (Subgroup.mem_map_equiv (f := ψ) (K := Bbar)).mp h

private theorem image_mem_Kbar {n d : ℕ} {F : Type} [Field F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Kbar : Subgroup Q}
    {I : Finset (Fin d)}
    (hKI : (Kbar.map ψ.toMonoidHom : Set (UniPSU n d F)) = UniBlockImage n d F I)
    {g : ↥(UniSU n d F)} (hg : (g : GL (Fin d) F) ∈ UniBlockSet n d F I) :
    ψ.symm (UniMk n d F g) ∈ Kbar := by
  have hmemKI : ∀ z : UniPSU n d F,
      z ∈ Kbar.map ψ.toMonoidHom ↔ z ∈ UniBlockImage n d F I :=
    fun z => Iff.of_eq (congrArg (fun s : Set (UniPSU n d F) => z ∈ s) hKI)
  have h : UniMk n d F g ∈ Kbar.map ψ.toMonoidHom := (hmemKI _).mpr ⟨g, hg, rfl⟩
  exact (Subgroup.mem_map_equiv (f := ψ) (K := Kbar)).mp h

private theorem normalizer_image_mem {n d : ℕ} {F : Type} [Field F] [Finite F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {I : Finset (Fin d)}
    {U_GL : Subgroup (GL (Fin d) F)} (hU_GL_block : ∀ u ∈ U_GL, u ∈ UniBlockSet n d F I)
    {c : GL (Fin d) F} (hcN : c ∈ Subgroup.normalizer (U_GL : Set (GL (Fin d) F)))
    (hcSU : c ∈ UniSU n d F) :
    ψ.symm (UniMk n d F ⟨c, hcSU⟩) ∈
      Subgroup.normalizer
        (((U_GL.subgroupOf (UniSU n d F)).map (UniMk n d F) |>.map ψ.symm.toMonoidHom :
          Subgroup Q) : Set Q) := by
  have hU_SU : U_GL ≤ UniSU n d F := fun u hu => (hU_GL_block u hu).1
  let U_SU : Subgroup ↥(UniSU n d F) := U_GL.subgroupOf (UniSU n d F)
  let U_PSU : Subgroup (UniPSU n d F) := U_SU.map (UniMk n d F)
  let U : Subgroup Q := U_PSU.map ψ.symm.toMonoidHom
  have hchatN : (⟨c, hcSU⟩ : ↥(UniSU n d F)) ∈ Subgroup.normalizer (U_SU : Set _) := by
    rw [show U_SU = U_GL.subgroupOf (UniSU n d F) from rfl,
      ← Subgroup.subgroupOf_normalizer_eq hU_SU]
    exact Subgroup.mem_subgroupOf.mpr hcN
  have hpsuN : UniMk n d F ⟨c, hcSU⟩ ∈
      Subgroup.normalizer (U_PSU : Set (UniPSU n d F)) := by
    rw [show U_PSU = U_SU.map (UniMk n d F) from rfl]
    exact Subgroup.le_normalizer_map (UniMk n d F)
      (Subgroup.mem_map_of_mem (UniMk n d F) hchatN)
  have hqN : ψ.symm (UniMk n d F ⟨c, hcSU⟩) ∈
      Subgroup.normalizer (U_PSU.map ψ.symm.toMonoidHom : Set Q) :=
    Subgroup.le_normalizer_map ψ.symm.toMonoidHom
      (Subgroup.mem_map_of_mem ψ.symm.toMonoidHom hpsuN)
  simpa [U_SU, U_PSU, U] using hqN

private theorem mem_sup_of_uni_decomp {p n d : ℕ} {F : Type} [Field F] [Finite F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : UniDiagFrame p n d F ψ Bbar A)
    {Kbar : Subgroup Q} {I : Finset (Fin d)}
    (hKI : (Kbar.map ψ.toMonoidHom : Set (UniPSU n d F)) = UniBlockImage n d F I)
    {U_GL : Subgroup (GL (Fin d) F)} (hU_GL_block : ∀ u ∈ U_GL, u ∈ UniBlockSet n d F I)
    (hdec : ∀ a ∈ A, ∃ m ∈ A, m ∈ UniBlockSet n d F I ∧
      ∃ c ∈ A, c ∈ Subgroup.normalizer (U_GL : Set (GL (Fin d) F)) ∧ a = m * c)
    {x : Q} (hx : x ∈ Bbar) :
    x ∈ (Bbar ⊓ Kbar) ⊔
      (Bbar ⊓ Subgroup.normalizer
        (((U_GL.subgroupOf (UniSU n d F)).map (UniMk n d F) |>.map ψ.symm.toMonoidHom :
          Subgroup Q) : Set Q)) := by
  classical
  obtain ⟨hAsu, _hAe, _hAd, hBmap⟩ := hfr
  let U_SU : Subgroup ↥(UniSU n d F) := U_GL.subgroupOf (UniSU n d F)
  let U_PSU : Subgroup (UniPSU n d F) := U_SU.map (UniMk n d F)
  let U : Subgroup Q := U_PSU.map ψ.symm.toMonoidHom
  have hxψ : ψ x ∈ Bbar.map ψ.toMonoidHom := Subgroup.mem_map_of_mem ψ.toMonoidHom hx
  rw [hBmap] at hxψ
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hxψ
  have haGL : (a : GL (Fin d) F) ∈ A := Subgroup.mem_subgroupOf.mp ha
  obtain ⟨m, hmA, hmblk, c, hcA, hcN, hamc⟩ := hdec (a : GL (Fin d) F) haGL
  have hmSU : m ∈ UniSU n d F := hAsu hmA
  have hcSU : c ∈ UniSU n d F := hAsu hcA
  let mhat : ↥(UniSU n d F) := ⟨m, hmSU⟩
  let chat : ↥(UniSU n d F) := ⟨c, hcSU⟩
  have haeq' : a = mhat * chat := by
    apply Subtype.ext
    simpa [mhat, chat] using hamc
  let u₁ : Q := ψ.symm (UniMk n d F mhat)
  let u₂ : Q := ψ.symm (UniMk n d F chat)
  have hx_eq : x = u₁ * u₂ := by
    apply ψ.injective
    calc ψ x = UniMk n d F a := haeq.symm
      _ = UniMk n d F mhat * UniMk n d F chat := by rw [haeq', map_mul]
      _ = ψ (u₁ * u₂) := by simp [u₁, u₂]
  have hu1B : u₁ ∈ Bbar := image_mem_Bbar hBmap hmA
  have hu1K : u₁ ∈ Kbar := image_mem_Kbar hKI hmblk
  have hu2B : u₂ ∈ Bbar := image_mem_Bbar hBmap hcA
  have hu2N : u₂ ∈ Subgroup.normalizer (U : Set Q) :=
    normalizer_image_mem hU_GL_block hcN hcSU
  rw [hx_eq]
  exact Subgroup.mul_mem_sup ⟨hu1B, hu1K⟩ ⟨hu2B, hu2N⟩

private theorem Bbar_eq_sup_of_uni_decomp {p n d : ℕ} {F : Type} [Field F] [Finite F]
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : UniDiagFrame p n d F ψ Bbar A)
    {Kbar : Subgroup Q} {I : Finset (Fin d)}
    (hKI : (Kbar.map ψ.toMonoidHom : Set (UniPSU n d F)) = UniBlockImage n d F I)
    {U_GL : Subgroup (GL (Fin d) F)} (hU_GL_block : ∀ u ∈ U_GL, u ∈ UniBlockSet n d F I)
    (hdec : ∀ a ∈ A, ∃ m ∈ A, m ∈ UniBlockSet n d F I ∧
      ∃ c ∈ A, c ∈ Subgroup.normalizer (U_GL : Set (GL (Fin d) F)) ∧ a = m * c) :
    Bbar = (Bbar ⊓ Kbar) ⊔
      (Bbar ⊓ Subgroup.normalizer
        (((U_GL.subgroupOf (UniSU n d F)).map (UniMk n d F) |>.map ψ.symm.toMonoidHom :
          Subgroup Q) : Set Q)) := by
  apply le_antisymm
  · intro x hx
    exact mem_sup_of_uni_decomp hfr hKI hU_GL_block hdec hx
  · exact sup_le inf_le_left inf_le_left

theorem uni_split_of_full {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : UniArith p n d F)
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : UniDiagFrame p n d F ψ Bbar A)
    (hcard : Nat.card Bbar = p ^ (d - 1)) {Kbar : Subgroup Q} {I : Finset (Fin d)}
    (hI : 2 ≤ I.card)
    (hKI : (Kbar.map ψ.toMonoidHom : Set (UniPSU n d F)) = UniBlockImage n d F I) :
    ∃ U : Subgroup Q, U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ Kbar ∧
      Bbar = (Bbar ⊓ Kbar) ⊔ (Bbar ⊓ Subgroup.normalizer (U : Set Q)) := by
  classical
  have hAeq : A = diagPGroup p d F := eq_diagPGroup_of_frame h hfr hcard
  obtain ⟨ω, b, b', hωorder, hbI, hb'I, hbb', hvbbA⟩ := exists_pair_element h hAeq hI
  obtain ⟨U_GL, hU_GL_ne, hU_GL_2, hU_GL_block, hdec⟩ :=
    uni_diag_decomp h (le_of_eq hAeq) I hI b b' hbI hb'I hbb' ω hωorder hvbbA
  have hcardF : Nat.card F = (2 ^ n) ^ 2 := h.2.2.2.1
  have hn : 1 ≤ n := h.2.2.2.2.1
  have hd : 1 ≤ d := by
    have := h.2.2.2.2.2.1
    omega
  let U : Subgroup Q :=
    ((U_GL.subgroupOf (UniSU n d F)).map (UniMk n d F) |>.map ψ.symm.toMonoidHom :
      Subgroup Q)
  have hU_ne : U ≠ ⊥ := uniImage_ne_bot hU_GL_ne hU_GL_2 hU_GL_block hcardF hn hd
  have hU_2 : IsPGroup 2 U := uniImage_isPGroup hU_GL_2 hU_GL_block
  have hU_le : U ≤ Kbar := uniImage_le_Kbar hKI hU_GL_block
  have hdec' : Bbar = (Bbar ⊓ Kbar) ⊔ (Bbar ⊓ Subgroup.normalizer (U : Set Q)) :=
    Bbar_eq_sup_of_uni_decomp hfr hKI hU_GL_block hdec
  exact ⟨U, hU_ne, hU_2, hU_le, hdec'⟩
