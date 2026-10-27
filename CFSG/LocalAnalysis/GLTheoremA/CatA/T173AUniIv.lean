module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniIvDiag
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly
open scoped MatrixGroups

private theorem uniSU_eq_statedSU (n d : ℕ) (F : Type) [Field F] :
    UniSU n d F = StatedSU d (2 ^ n) F := rfl

private theorem statedScalars_subgroupOf_eq_bot_of_isPGroup {d p m : ℕ} {F : Type} [Field F]
    [Finite F] (hp : p.Prime) (hpd : ¬ p ∣ m) (M : Subgroup (GL (Fin d) F)) [Finite M]
    (hMp : IsPGroup p M)
    (hd : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ M → c ^ m = 1) :
    (StatedScalars (Fin d) F).subgroupOf M = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨kx, hkx⟩ := hMp x
  have h1 : orderOf x ∣ p ^ kx := orderOf_dvd_of_pow_eq_one hkx
  have h2 : orderOf x ∣ Nat.card ((StatedScalars (Fin d) F).subgroupOf M) :=
    Subgroup.orderOf_dvd_natCard _ hx
  have hdvd : ¬ p ∣ Nat.card ((StatedScalars (Fin d) F).subgroupOf M) :=
    CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf M hp hpd hd
  have hcop : Nat.Coprime (p ^ kx) (Nat.card ((StatedScalars (Fin d) F).subgroupOf M)) :=
    Nat.Coprime.pow_left kx ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd)
  have h3 : orderOf x = 1 := (Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2
  exact orderOf_eq_one_iff.mp h3

private theorem map_eq_of_map_eq_of_disjoint_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) {P : Subgroup G} (hdisj : Disjoint P f.ker)
    {K L : Subgroup G} (hK : K ≤ P) (hL : L ≤ P) (h : K.map f = L.map f) : K = L := by
  have hbot : P ⊓ f.ker = ⊥ := disjoint_iff.mp hdisj
  apply le_antisymm
  · intro x hx
    have hfx : f x ∈ L.map f := by rw [← h]; exact Subgroup.mem_map_of_mem f hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hfx
    have hker : x⁻¹ * y ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hmem : x⁻¹ * y ∈ P ⊓ f.ker := ⟨mul_mem (P.inv_mem (hK hx)) (hL hy), hker⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hxy : x = y := inv_mul_eq_one.mp hmem
    rwa [hxy]
  · intro x hx
    have hfx : f x ∈ K.map f := by rw [h]; exact Subgroup.mem_map_of_mem f hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hfx
    have hker : x⁻¹ * y ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hmem : x⁻¹ * y ∈ P ⊓ f.ker := ⟨mul_mem (P.inv_mem (hL hx)) (hK hy), hker⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hxy : x = y := inv_mul_eq_one.mp hmem
    rwa [hxy]

private theorem diagonal_mul_mul_apply {d : ℕ} {F : Type} [Field F]
    {a g ap : Matrix (Fin d) (Fin d) F} (ha : a.IsDiag) (hap : ap.IsDiag) (i j : Fin d) :
    (a * g * ap) i j = a i i * g i j * ap j j := by
  have h1 : (a * g * ap) i j =
      (Matrix.diagonal (Matrix.diag a) * g * Matrix.diagonal (Matrix.diag ap)) i j := by
    rw [ha.diagonal_diag, hap.diagonal_diag]
  rw [h1, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [Matrix.diag_apply, mul_assoc]

private theorem isDiag_inv_of_isDiag {d : ℕ} {F : Type} [Field F] {a : GL (Fin d) F}
    (ha : (a : Matrix (Fin d) (Fin d) F).IsDiag) :
    (((a⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F).IsDiag := by
  have hAA : (a : Matrix (Fin d) (Fin d) F) *
      (((a⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) = 1 := by
    simpa using congrArg (fun u : GL (Fin d) F => (u : Matrix (Fin d) (Fin d) F))
      (mul_inv_cancel a)
  intro i j hij
  have h := congrFun (congrFun hAA i) j
  rw [← ha.diagonal_diag, Matrix.diagonal_mul, Matrix.diag_apply, Matrix.one_apply,
    if_neg hij] at h
  have haii : (a : Matrix (Fin d) (Fin d) F) i i ≠ 0 := by
    intro h0
    have hd := congrFun (congrFun hAA i) i
    rw [← ha.diagonal_diag, Matrix.diagonal_mul, Matrix.diag_apply, Matrix.one_apply_eq,
      h0, zero_mul] at hd
    exact one_ne_zero hd.symm
  exact (mul_eq_zero.mp h).resolve_left haii

private theorem diag_conj_mem_uniBlockSet {n d : ℕ} {F : Type} [Field F] {I : Finset (Fin d)}
    {a : GL (Fin d) F} (haSU : a ∈ UniSU n d F)
    (ha : ∀ i j, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    {g : GL (Fin d) F} (hg : g ∈ UniBlockSet n d F I) :
    a * g * a⁻¹ ∈ UniBlockSet n d F I := by
  rw [UniBlockSet] at hg ⊢
  refine ⟨mul_mem (mul_mem haSU hg.1) (inv_mem haSU), ?_⟩
  have hdiag : (a : Matrix (Fin d) (Fin d) F).IsDiag := ha
  have hdiag' : (((a⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F).IsDiag :=
    isDiag_inv_of_isDiag hdiag
  have ha_ap : ∀ i, (a : Matrix (Fin d) (Fin d) F) i i *
      (((a⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) i i = 1 := by
    intro i
    have hAA : (a : Matrix (Fin d) (Fin d) F) *
        (((a⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) = 1 := by
      simpa using congrArg (fun u : GL (Fin d) F => (u : Matrix (Fin d) (Fin d) F))
        (mul_inv_cancel a)
    have h := congrFun (congrFun hAA i) i
    rw [← hdiag.diagonal_diag, Matrix.diagonal_mul, Matrix.diag_apply, Matrix.one_apply_eq] at h
    exact h
  intro i j hij
  rw [Units.val_mul, Units.val_mul,
    diagonal_mul_mul_apply (a := (a : Matrix (Fin d) (Fin d) F)) (g := (g : Matrix _ _ F))
      (ap := (((a⁻¹ : GL (Fin d) F)) : Matrix _ _ F)) hdiag hdiag' i j]
  by_cases h : i = j
  · subst h
    rw [hg.2 i i hij, if_pos rfl, mul_one, ha_ap i]
  · rw [hg.2 i j hij, if_neg h, mul_zero, zero_mul]

theorem uni_iv_frame {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : UniArith p n d F)
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : UniDiagFrame p n d F ψ Bbar A)
    (hrep : ∃ i j : Fin d, i ≠ j ∧ ∀ a ∈ A,
      (a : Matrix (Fin d) (Fin d) F) i i = (a : Matrix (Fin d) (Fin d) F) j j)
    {Kbar : Subgroup Q} {I : Finset (Fin d)} (hI : 2 ≤ I.card)
    (hKI : (Kbar.map ψ.toMonoidHom : Set (UniPSU n d F)) = UniBlockImage n d F I) :
    ∃ B' U : Subgroup Q, IsElemAbelian p B' ∧ Bbar ≤ B' ∧ Bbar ≠ B' ∧
      B' ≤ Subgroup.normalizer (Kbar : Set Q) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ Kbar ∧
      B' = (B' ⊓ Kbar) ⊔ (B' ⊓ Subgroup.normalizer (U : Set Q)) := by
  classical
  have hp : p.Prime := h.1
  have hcard : Nat.card F = (2 ^ n) ^ 2 := h.2.2.2.1
  have hpd : ¬ p ∣ d := h.2.2.1
  have hn : 1 ≤ n := h.2.2.2.2.1
  have hd3 : 3 ≤ d := h.2.2.2.2.2.1
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hAsu, hAe, hAd, hBmap⟩ := hfr
  obtain ⟨A', U, hAA', hA'ne, hA'su, hA'e, hA'd, hUbot, hU2, hUblk, hdec⟩ :=
    uni_iv_diag h hAsu hAe hAd hrep I hI
  have hU_le_SU : U ≤ UniSU n d F := fun u hu => (hUblk u hu).1
  have hdA' : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ A' → c ^ d = 1 := by
    intro c hc
    have hcSU : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ StatedSU d (2 ^ n) F := by
      rw [← uniSU_eq_statedSU]
      exact hA'su hc
    exact ((CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := n) Nat.prime_two
      hcard hd1 c).1 hcSU).1
  have hStatedScalars_A'_bot : (StatedScalars (Fin d) F).subgroupOf A' = ⊥ :=
    statedScalars_subgroupOf_eq_bot_of_isPGroup hp hpd A' hA'e.isPGroup hdA'
  have h2dvd : ¬ 2 ∣ 2 ^ n + 1 := by
    have hpow : 2 ∣ 2 ^ n := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      rw [pow_succ]
      exact dvd_mul_left 2 (2 ^ m)
    have hodd : Odd (2 ^ n + 1) := (even_iff_two_dvd.mpr hpow).add_one
    exact fun hd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  have hdU : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ U → c ^ (2 ^ n + 1) = 1 := by
    intro c hc
    have hcSU : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ StatedSU d (2 ^ n) F := by
      rw [← uniSU_eq_statedSU]
      exact (hUblk _ hc).1
    exact ((CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := n) Nat.prime_two
      hcard hd1 c).1 hcSU).2
  have hStatedScalars_U_bot : (StatedScalars (Fin d) F).subgroupOf U = ⊥ :=
    statedScalars_subgroupOf_eq_bot_of_isPGroup Nat.prime_two h2dvd U hU2 hdU
  have hπker : (UniMk n d F).ker = (StatedScalars (Fin d) F).subgroupOf (UniSU n d F) := by
    simpa [UniMk, LargeEvenProjMk] using
      (QuotientGroup.ker_mk' ((LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F)))
  set KA : Subgroup ↥(UniSU n d F) := A.subgroupOf (UniSU n d F) with hKA
  set KA' : Subgroup ↥(UniSU n d F) := A'.subgroupOf (UniSU n d F) with hKA'
  set KU : Subgroup ↥(UniSU n d F) := U.subgroupOf (UniSU n d F) with hKU
  set BP : Subgroup (UniPSU n d F) := KA'.map (UniMk n d F) with hBP
  set UP : Subgroup (UniPSU n d F) := KU.map (UniMk n d F) with hUP
  set B' : Subgroup Q := BP.map ψ.symm.toMonoidHom with hB'def
  set Uq : Subgroup Q := UP.map ψ.symm.toMonoidHom with hUqdef
  have hmemKI : ∀ z : UniPSU n d F,
      z ∈ Kbar.map ψ.toMonoidHom ↔ z ∈ UniBlockImage n d F I :=
    fun z => Iff.of_eq (congrArg (fun s : Set (UniPSU n d F) => z ∈ s) hKI)
  have hKA_le : KA ≤ KA' := by
    rw [hKA, hKA']
    exact Subgroup.subgroupOf_mono (UniSU n d F) hAA'
  have hKA_ne : KA ≠ KA' := by
    intro hEq
    apply hA'ne
    apply le_antisymm hAA'
    intro x hx
    have hxSU : x ∈ UniSU n d F := hA'su hx
    have hx' : (⟨x, hxSU⟩ : ↥(UniSU n d F)) ∈ KA' := by
      rw [hKA']
      exact Subgroup.mem_subgroupOf.2 hx
    have hx'' : (⟨x, hxSU⟩ : ↥(UniSU n d F)) ∈ KA := le_of_eq hEq.symm hx'
    have : ((⟨x, hxSU⟩ : ↥(UniSU n d F)) : GL (Fin d) F) ∈ A := by
      rw [hKA] at hx''
      exact Subgroup.mem_subgroupOf.1 hx''
    simpa using this
  have hKA'_ker_bot : KA' ⊓ (UniMk n d F).ker = ⊥ := by
    rw [hKA', hπker]
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxA', hxZ⟩ := hx
    have hxA'GL : (x : GL (Fin d) F) ∈ A' := by
      rw [← hKA'] at hxA'
      exact Subgroup.mem_subgroupOf.1 hxA'
    have hxZGL : (x : GL (Fin d) F) ∈ StatedScalars (Fin d) F :=
      Subgroup.mem_subgroupOf.1 hxZ
    have hmem : (⟨(x : GL (Fin d) F), hxA'GL⟩ : ↥A') ∈
        (StatedScalars (Fin d) F).subgroupOf A' :=
      Subgroup.mem_subgroupOf.2 hxZGL
    rw [hStatedScalars_A'_bot, Subgroup.mem_bot] at hmem
    apply Subgroup.mem_bot.2
    apply Subtype.ext
    have hcongr := congrArg (fun y : ↥A' => (y : GL (Fin d) F)) hmem
    simpa using hcongr
  have hKU_ker_bot : KU ⊓ (UniMk n d F).ker = ⊥ := by
    rw [hKU, hπker]
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxZ⟩ := hx
    have hxUGL : (x : GL (Fin d) F) ∈ U := by
      rw [← hKU] at hxU
      exact Subgroup.mem_subgroupOf.1 hxU
    have hxZGL : (x : GL (Fin d) F) ∈ StatedScalars (Fin d) F :=
      Subgroup.mem_subgroupOf.1 hxZ
    have hmem : (⟨(x : GL (Fin d) F), hxUGL⟩ : ↥U) ∈
        (StatedScalars (Fin d) F).subgroupOf U :=
      Subgroup.mem_subgroupOf.2 hxZGL
    rw [hStatedScalars_U_bot, Subgroup.mem_bot] at hmem
    apply Subgroup.mem_bot.2
    apply Subtype.ext
    have hcongr := congrArg (fun y : ↥U => (y : GL (Fin d) F)) hmem
    simpa using hcongr
  have hKU_ne : KU ≠ ⊥ := by
    intro hKUbot
    apply hUbot
    apply bot_unique
    intro u hu
    rw [Subgroup.mem_bot]
    have huSU : u ∈ UniSU n d F := (hUblk u hu).1
    have hxu : (⟨u, huSU⟩ : ↥(UniSU n d F)) ∈ KU := by
      rw [hKU]
      exact Subgroup.mem_subgroupOf.2 hu
    rw [hKUbot] at hxu
    have hcongr := congrArg (fun y : ↥(UniSU n d F) => (y : GL (Fin d) F))
      (Subgroup.mem_bot.mp hxu)
    simpa using hcongr
  have hKU2 : IsPGroup 2 KU := by
    rw [hKU]
    exact hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hU_le_SU).symm
  have hUP_ne : UP ≠ ⊥ := by
    intro hUPbot
    apply hKU_ne
    have hker : KU.map (UniMk n d F) = ⊥ := by rw [← hUP]; exact hUPbot
    rw [Subgroup.map_eq_bot_iff] at hker
    have hle : KU ≤ KU ⊓ (UniMk n d F).ker := le_inf le_rfl hker
    rw [hKU_ker_bot] at hle
    exact le_bot_iff.mp hle
  have hUq_ne : Uq ≠ ⊥ := by
    intro hUqbot
    apply hUP_ne
    have hbot : UP.map ψ.symm.toMonoidHom = ⊥ := by rw [← hUqdef]; exact hUqbot
    exact (Subgroup.map_eq_bot_iff_of_injective (H := UP) (f := ψ.symm.toMonoidHom)
      ψ.symm.injective).mp hbot
  have hUq2 : IsPGroup 2 Uq := by
    rw [hUqdef, hUP]
    exact (hKU2.map (UniMk n d F)).map ψ.symm.toMonoidHom
  have hUP_le : UP ≤ Kbar.map ψ.toMonoidHom := by
    intro y hy
    rw [hUP] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hxU : (x : GL (Fin d) F) ∈ U := by
      rw [hKU] at hx
      exact Subgroup.mem_subgroupOf.1 hx
    exact (hmemKI (UniMk n d F x)).mpr ⟨x, hUblk (x : GL (Fin d) F) hxU, rfl⟩
  have hUq_le : Uq ≤ Kbar := by
    intro x hx
    rw [hUqdef] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hyK : y ∈ Kbar.map ψ.toMonoidHom := hUP_le hy
    rw [← hyx]
    exact (Subgroup.mem_map_equiv (f := ψ) (K := Kbar)).1 hyK
  have hB'e : IsElemAbelian p B' := by
    rw [hB'def]
    have h1 : IsElemAbelian p BP := by
      rw [hBP]
      have h2 : IsElemAbelian p KA' := by
        rw [hKA']
        exact hA'e.subgroupOf (UniSU n d F)
      exact h2.map (UniMk n d F)
    exact h1.map ψ.symm.toMonoidHom
  have hBbar_map : Bbar.map ψ.toMonoidHom = KA.map (UniMk n d F) := hBmap
  have hB'map : B'.map ψ.toMonoidHom = BP := by
    rw [hB'def]
    rw [Subgroup.map_map]
    have hcomp : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id (UniPSU n d F) := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hBbar_le : Bbar ≤ B' := by
    rw [hB'def, ← Subgroup.comap_equiv_eq_map_symm' ψ BP]
    exact (Subgroup.map_le_iff_le_comap).1 (by
      rw [hBbar_map, hBP]
      exact Subgroup.map_mono hKA_le)
  have hBne : Bbar ≠ B' := by
    intro hEq
    have hmapEq : KA.map (UniMk n d F) = KA'.map (UniMk n d F) := by
      have h1 : Bbar.map ψ.toMonoidHom = B'.map ψ.toMonoidHom := by rw [hEq]
      rw [hBbar_map, hB'map] at h1
      exact h1
    have hdisj : Disjoint KA' (UniMk n d F).ker := disjoint_iff.mpr hKA'_ker_bot
    exact hKA_ne (map_eq_of_map_eq_of_disjoint_ker (UniMk n d F) hdisj hKA_le le_rfl hmapEq)
  have hB'_le_norm : B' ≤ Subgroup.normalizer (Kbar : Set Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx k hk
    rw [hB'def] at hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    rw [hBP] at hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
    have haGL : (a : GL (Fin d) F) ∈ A' := by
      rw [hKA'] at ha
      exact Subgroup.mem_subgroupOf.1 ha
    have hk' : ψ k ∈ UniBlockImage n d F I := (hmemKI (ψ k)).mp ⟨k, hk, rfl⟩
    obtain ⟨g, hg, hgk⟩ := hk'
    have hdiag : ∀ i j, i ≠ j → (((a : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) i j = 0 :=
      fun i j hij => hA'd (a : GL (Fin d) F) haGL i j hij
    have hconj_blk : (a : GL (Fin d) F) * (g : GL (Fin d) F) * (a : GL (Fin d) F)⁻¹ ∈
        UniBlockSet n d F I :=
      diag_conj_mem_uniBlockSet (hA'su haGL) hdiag hg
    have hkey : ψ (ψ.symm (UniMk n d F a) * k * (ψ.symm (UniMk n d F a))⁻¹) ∈
        Kbar.map ψ.toMonoidHom := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← hgk]
      exact (hmemKI _).mpr ⟨a * g * a⁻¹, by simpa using hconj_blk, by simp [map_mul]⟩
    have := (Subgroup.mem_map_equiv (f := ψ) (K := Kbar)).1 hkey
    simpa using this
  have hdec' : B' = (B' ⊓ Kbar) ⊔ (B' ⊓ Subgroup.normalizer (Uq : Set Q)) := by
    apply le_antisymm
    · intro x hx
      rw [hB'def] at hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
      rw [hBP] at hu
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
      have haGL : (a : GL (Fin d) F) ∈ A' := by
        rw [hKA'] at ha
        exact Subgroup.mem_subgroupOf.1 ha
      obtain ⟨m, hmA', hmblk, c, hcA', hcN, hamc⟩ := hdec (a : GL (Fin d) F) haGL
      have hmSU : m ∈ UniSU n d F := hA'su hmA'
      have hcSU : c ∈ UniSU n d F := hA'su hcA'
      set mhat : ↥(UniSU n d F) := ⟨m, hmSU⟩ with hmhat
      set chat : ↥(UniSU n d F) := ⟨c, hcSU⟩ with hchat
      have haeq : a = mhat * chat := by
        apply Subtype.ext
        simpa [hmhat, hchat] using hamc
      have hx_decomp : ψ.symm.toMonoidHom (UniMk n d F a) =
          ψ.symm.toMonoidHom (UniMk n d F mhat) * ψ.symm.toMonoidHom (UniMk n d F chat) := by
        rw [haeq, map_mul, map_mul]
      rw [hx_decomp]
      have hm : ψ.symm.toMonoidHom (UniMk n d F mhat) ∈ B' ⊓ Kbar := by
        refine ⟨?_, ?_⟩
        · exact Subgroup.mem_map_of_mem ψ.symm.toMonoidHom
            (Subgroup.mem_map_of_mem (UniMk n d F) (by
              rw [hKA']; exact Subgroup.mem_subgroupOf.2 hmA'))
        · exact (Subgroup.mem_map_equiv (f := ψ) (K := Kbar)).1
            ((hmemKI (UniMk n d F mhat)).mpr ⟨mhat, hmblk, rfl⟩)
      have hc : ψ.symm.toMonoidHom (UniMk n d F chat) ∈
          B' ⊓ Subgroup.normalizer (Uq : Set Q) := by
        refine ⟨?_, ?_⟩
        · exact Subgroup.mem_map_of_mem ψ.symm.toMonoidHom
            (Subgroup.mem_map_of_mem (UniMk n d F) (by
              rw [hKA']; exact Subgroup.mem_subgroupOf.2 hcA'))
        · have hchat_norm : chat ∈ Subgroup.normalizer (KU : Set ↥(UniSU n d F)) := by
            rw [hKU, ← Subgroup.subgroupOf_normalizer_eq hU_le_SU]
            exact Subgroup.mem_subgroupOf.2 hcN
          have hchat_norm_up : UniMk n d F chat ∈
              Subgroup.normalizer (UP : Set (UniPSU n d F)) := by
            rw [hUP]
            exact Subgroup.le_normalizer_map (UniMk n d F)
              (Subgroup.mem_map_of_mem (UniMk n d F) hchat_norm)
          have hnormq : ψ.symm.toMonoidHom (UniMk n d F chat) ∈
              Subgroup.normalizer (UP.map ψ.symm.toMonoidHom : Set Q) :=
            Subgroup.le_normalizer_map ψ.symm.toMonoidHom
              (Subgroup.mem_map_of_mem ψ.symm.toMonoidHom hchat_norm_up)
          rwa [hUqdef]
      exact Subgroup.mul_mem_sup hm hc
    · exact sup_le inf_le_left inf_le_left
  exact ⟨B', Uq, hB'e, hBbar_le, hBne, hB'_le_norm, hUq_ne, hUq2, hUq_le, hdec'⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
