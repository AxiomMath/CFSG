module

public import CFSG.Holt.H78.Data
import CFSG.Holt.H78.AltModelSylow
import CFSG.Holt.H78.SEModelFive
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open CFSG.Open (fusionIsSylowIn)
open scoped Pointwise

section LongInvMul

variable {Δ : Type*}

@[expose] def mulLongInvClosure (R : Subgroup (Equiv.Perm Δ)) (a : Δ) :
    Subgroup (Equiv.Perm Δ) :=
  (Subgroup.closure {g : R | ∃ u ∈ longInvAt R Δ a, ∃ v ∈ longInvAt R Δ a, u * v = g}).map
    R.subtype

theorem mulLongInvClosure_le (R : Subgroup (Equiv.Perm Δ)) (a : Δ) :
    mulLongInvClosure R a ≤ R ⊓ stabilizer (Equiv.Perm Δ) a := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g.2, ?_⟩
  have hle : Subgroup.closure {g : R | ∃ u ∈ longInvAt R Δ a, ∃ v ∈ longInvAt R Δ a, u * v = g} ≤
      stabilizer R a := by
    rw [Subgroup.closure_le]
    rintro _ ⟨u, hu, v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_stabilizer_iff, mul_smul, hv.2, hu.2]
  exact hle hg

theorem mul_mem_mulLongInvClosure {R : Subgroup (Equiv.Perm Δ)} {a : Δ} {u v : R}
    (hu : u ∈ longInvAt R Δ a) (hv : v ∈ longInvAt R Δ a) :
    (u : Equiv.Perm Δ) * v ∈ mulLongInvClosure R a :=
  ⟨u * v, Subgroup.subset_closure ⟨u, hu, v, hv, rfl⟩, rfl⟩

theorem conj_mem_mulLongInvClosure {R : Subgroup (Equiv.Perm Δ)} {a : Δ} {r : Equiv.Perm Δ}
    (hr : r ∈ R) (hra : r a = a) {w : Equiv.Perm Δ} (hw : w ∈ mulLongInvClosure R a) :
    r * w * r⁻¹ ∈ mulLongInvClosure R a := by
  obtain ⟨g, hg, rfl⟩ := hw
  set rR : R := ⟨r, hr⟩
  have hra' : rR • a = a := hra
  have hle : Subgroup.closure {g : R | ∃ u ∈ longInvAt R Δ a, ∃ v ∈ longInvAt R Δ a, u * v = g} ≤
      (Subgroup.closure {g : R | ∃ u ∈ longInvAt R Δ a, ∃ v ∈ longInvAt R Δ a, u * v = g}).comap
        (MulAut.conj rR).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨u, hu, v, hv, rfl⟩
    have hu' := conj_mem_longInvAt hu rR
    have hv' := conj_mem_longInvAt hv rR
    rw [hra'] at hu' hv'
    refine Subgroup.subset_closure ⟨_, hu', _, hv', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact ⟨rR * g * rR⁻¹, hle hg, rfl⟩

end LongInvMul

section SylowHelpers

variable {G : Type*} [Group G]

private theorem mem_normalizer_iSup {ι : Sort*} {U : ι → Subgroup G} {x : G}
    (hx : ∀ i, x ∈ Subgroup.normalizer (U i : Set G)) :
    x ∈ Subgroup.normalizer ((⨆ i, U i : Subgroup G) : Set G) := by
  have key : ∀ y : G, (∀ i, y ∈ Subgroup.normalizer (U i : Set G)) →
      ∀ z ∈ ⨆ i, U i, y * z * y⁻¹ ∈ ⨆ i, U i := by
    intro y hy z hz
    have hle : (⨆ i, U i) ≤ (⨆ i, U i).comap (MulAut.conj y).toMonoidHom :=
      iSup_le fun i u hu => Subgroup.mem_iSup_of_mem i
        ((Subgroup.mem_normalizer_iff.mp (hy i) u).mp hu)
    exact hle hz
  refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨key x hx z, fun hz => ?_⟩
  have h := key x⁻¹ (fun i => Subgroup.inv_mem _ (hx i)) _ hz
  rwa [show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z by group] at h

variable [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
private theorem fusionIsSylowIn_of_isSylowOf' {P K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) : fusionIsSylowIn p P K := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, fun R hRK hR hQR => ?_⟩
  have hQR' : (Q : Subgroup K) ≤ R.subgroupOf K := fun x hx => hQR ⟨x, hx, rfl⟩
  rw [← Q.is_maximal' (hR.comap_of_injective K.subtype K.subtype_injective) hQR']
  exact ((Subgroup.subgroupOf_map_subtype R K).trans (inf_eq_left.mpr hRK)).symm

private theorem fusionIsSylowIn_inf_of_le_normalizer' {P K N : Subgroup G}
    (hP : fusionIsSylowIn p P K) (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) :
    fusionIsSylowIn p (P ⊓ N) N :=
  fusionIsSylowIn_of_isSylowOf' (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
    (exists_sylow_map_eq_of_fusionIsSylowIn hP) hNK hKN)

private theorem exists_fusionIsSylowIn_mem_normalizer' {Y : Subgroup G} {s : G}
    (hs : IsPGroup p (Subgroup.zpowers s)) (hsY : s ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ P, fusionIsSylowIn p P Y ∧ s ∈ Subgroup.normalizer (P : Set G) := by
  have hY' : Y ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsY)
  obtain ⟨Q, hsQ, hQ⟩ := exists_fusionIsSylowIn_ge hs (le_sup_right : _ ≤ Y ⊔ Subgroup.zpowers s)
  refine ⟨Q ⊓ Y, fusionIsSylowIn_inf_of_le_normalizer' hQ le_sup_left hY', ?_⟩
  have hsQ' : s ∈ Q := hsQ (Subgroup.mem_zpowers s)
  refine Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨?_, hsY⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => Q.mul_mem (Q.mul_mem hsQ' hx) (Q.inv_mem hsQ'), fun hx => ?_⟩
  have := Q.mul_mem (Q.mul_mem (Q.inv_mem hsQ') hx) hsQ'
  simpa [mul_assoc] using this

end SylowHelpers

section FactorFree

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ] {M : Subgroup (Equiv.Perm Δ)}

theorem IsNaturalSE.not_isOuterFactor (hM : IsNaturalSE M) : ¬ IsOuterFactor M := by
  rintro ⟨-, h3⟩
  obtain ⟨q, e, h⟩ := hM
  have h4 : 4 ∣ q ^ e := by
    rcases h.model with ⟨rfl, f, hf, rfl, -⟩ | ⟨rfl, a, ha, rfl, -⟩ | ⟨rfl, f, hf, rfl, -⟩
    · exact (pow_dvd_pow 2 hf).trans (dvd_pow_self _ one_ne_zero)
    · exact (pow_dvd_pow 2 (by omega : 2 ≤ 2 * a + 1)).trans (dvd_pow_self _ two_ne_zero)
    · exact (pow_dvd_pow 2 hf).trans (dvd_pow_self _ (by norm_num))
  have hc := h.card_eq
  rw [Nat.card_eq_fintype_card] at hc
  omega

theorem IsHoltFactor.two_dvd_card (hM : IsHoltFactor M) : 2 ∣ Nat.card M := by
  rcases hM with ⟨rfl, h7⟩ | ⟨q, e, h⟩
  · have : Nontrivial Δ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have h1 := two_mul_card_alternatingGroup (α := Δ)
    rw [Fintype.card_perm] at h1
    have h2 : 2 * 2 ∣ 2 * Fintype.card (alternatingGroup Δ) :=
      h1 ▸ Nat.dvd_factorial (by norm_num) (by omega)
    rw [Nat.card_eq_fintype_card]
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  · obtain ⟨S⟩ : Nonempty (Sylow 2 M) := inferInstance
    obtain ⟨-, h2, he, -⟩ := h.params
    have hS : 2 ∣ Nat.card (S : Subgroup M) := by
      rw [h.card_sylow S]
      exact dvd_pow h2 (by omega)
    exact hS.trans (Subgroup.card_subgroup_dvd_card _)

private theorem exists_ne_ne (h3 : 3 ≤ Fintype.card Δ) (a b : Δ) : ∃ c : Δ, c ≠ a ∧ c ≠ b := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset Δ) ⊆ {a, b} := fun x _ => by
    by_cases hx : x = a
    · simp [hx]
    · simp [h x hx]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le a ({b} : Finset Δ)
  rw [Finset.card_univ] at h1
  rw [Finset.card_singleton] at h2
  omega

theorem mulLongInvClosure_eq_of_alternatingGroup_le (h7 : 7 ≤ Fintype.card Δ)
    {R : Subgroup (Equiv.Perm Δ)} (hAR : alternatingGroup Δ ≤ R) {s : Equiv.Perm Δ} (hsR : s ∈ R)
    (hs : s ∈ longInv (Equiv.Perm Δ) Δ) (a : Δ) :
    mulLongInvClosure R a = alternatingGroup Δ ⊓ stabilizer (Equiv.Perm Δ) a :=
  map_closure_mul_longInvAt_eq_of_alternatingGroup_le h7 hAR hsR hs a

end FactorFree

section Factor

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ] {M : Subgroup (Equiv.Perm Δ)}

theorem IsHoltFactor.exists_mem_apply_eq_apply_ne (hM : IsHoltFactor M) {a b : Δ} (hba : b ≠ a) :
    ∃ m ∈ M, m a = a ∧ m b ≠ b := by
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne (by have := hM.five_le_card; omega) a b
  rcases hM with ⟨rfl, h7⟩ | hSE
  · obtain ⟨g, hg, hga, hgb⟩ := exists_mem_alternatingGroup_fix_apply_eq (by omega) hba hca
    exact ⟨g, hg, hga, by rw [hgb]; exact hcb⟩
  · obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hSE
    obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
    obtain ⟨p, hp, hpb⟩ := hA.exists_mem_smul_eq hQ hba hca
    have hpa : p • a = a := hQ hp
    refine ⟨p, p.2, hpa, fun h => hcb ?_⟩
    rw [← hpb]
    exact h

theorem IsHoltFactor.eq_of_forall_apply_eq (hM : IsHoltFactor M) {a b : Δ}
    (h : ∀ m ∈ M, m a = a → m b = b) : b = a := by
  by_contra hba
  obtain ⟨m, hm, hma, hmb⟩ := hM.exists_mem_apply_eq_apply_ne hba
  exact hmb (h m hm hma)

theorem IsHoltFactor.centralizer_eq_bot (hM : IsHoltFactor M) :
    Subgroup.centralizer (M : Set (Equiv.Perm Δ)) = ⊥ := by
  refine eq_bot_iff.mpr fun c hc => Subgroup.mem_bot.mpr (Equiv.ext fun a => ?_)
  rw [Equiv.Perm.one_apply]
  refine hM.eq_of_forall_apply_eq fun m hm hma => ?_
  have hcm := Subgroup.mem_centralizer_iff.mp hc m hm
  calc m (c a) = (m * c) a := rfl
    _ = (c * m) a := by rw [hcm]
    _ = c a := by rw [Equiv.Perm.mul_apply, hma]

theorem IsHoltFactor.fixSet_eq_singleton (hM : IsHoltFactor M) (hodd : Odd (Fintype.card Δ))
    {a : Δ} {P : Subgroup (Equiv.Perm Δ)}
    (hP : fusionIsSylowIn 2 P (M ⊓ stabilizer (Equiv.Perm Δ) a)) : fixSet Δ P = {a} := by
  have h5 := hM.five_le_card
  rcases hM with ⟨rfl, h7⟩ | hSE
  · exact fixSet_eq_singleton_of_fusionIsSylowIn_alternatingGroup hodd (by omega) hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hSE
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
  set T : Subgroup (Equiv.Perm Δ) := (Q : Subgroup M).map M.subtype with hTdef
  have hTle : T ≤ M ⊓ stabilizer (Equiv.Perm Δ) a := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q.2, hQ hq⟩
  have hT : fusionIsSylowIn 2 T (M ⊓ stabilizer (Equiv.Perm Δ) a) := by
    refine ⟨hTle, Q.isPGroup'.map _, fun R hRle hR hTR => ?_⟩
    have hR' : IsPGroup 2 (R.subgroupOf M) := hR.comap_of_injective _ M.subtype_injective
    have hQR : (Q : Subgroup M) ≤ R.subgroupOf M := fun q hq => hTR ⟨q, hq, rfl⟩
    rw [hTdef, ← Q.is_maximal' hR' hQR, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (hRle.trans inf_le_left)]
  have hTfix : fixSet Δ T = {a} := by
    ext b
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · by_contra hba
      obtain ⟨c, hca, hcb⟩ := exists_ne_ne (by omega) a b
      obtain ⟨p, hp, hpb⟩ := hA.exists_mem_smul_eq hQ hba hca
      have hpb' : p • b = b := hb (p : Equiv.Perm Δ) ⟨p, hp, rfl⟩
      exact hcb (hpb.symm.trans hpb')
    · rw [Set.mem_singleton_iff.mp hb]
      rintro _ ⟨q, hq, rfl⟩
      exact hQ hq
  refine fixSet_eq_of_fusionIsSylowIn (fun x hx => ?_) hT hP hTfix
  rw [mem_stabilizer_iff, Set.smul_set_singleton, hx.2]

theorem IsHoltFactor.exists_conj_eq (hM : IsHoltFactor M) {y y' : Equiv.Perm Δ}
    (hy : y ∈ longInv (Equiv.Perm Δ) Δ) (hy' : y' ∈ longInv (Equiv.Perm Δ) Δ)
    (hmem : (y ∈ M ∧ y' ∈ M) ∨ M = alternatingGroup Δ) : ∃ g ∈ M, g * y * g⁻¹ = y' := by
  by_cases hA : M = alternatingGroup Δ
  · subst hA
    exact exists_mem_alternatingGroup_conj_eq hy hy'
  obtain ⟨hyM, hy'M⟩ := hmem.resolve_right hA
  have hSE : IsNaturalSE M := hM.resolve_left fun h => hA h.1
  have h2 : orderOf (⟨y, hyM⟩ : M) = 2 := by rw [Subgroup.orderOf_mk]; exact hy.1
  have h2' : orderOf (⟨y', hy'M⟩ : M) = 2 := by rw [Subgroup.orderOf_mk]; exact hy'.1
  obtain ⟨c, hc⟩ := isConj_iff.mp (hSE.isConj h2 h2')
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

end Factor

section SEFactor

variable {Δ : Type*} [Fintype Δ] {M : Subgroup (Equiv.Perm Δ)}

open CFSG.GH74.Uniqueness.Bender

theorem IsNaturalSE.mulLongInvClosure_eq (hM : IsNaturalSE M) {a : Δ} {Q : Sylow 2 M}
    (hQ : (Q : Subgroup M) ≤ stabilizer M a) :
    mulLongInvClosure M a = (rootCenter (Q : Subgroup M)).map M.subtype := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hM
  rw [mulLongInvClosure, ← hA.closure_longInvAt hQ]
  congr 1
  refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) (Subgroup.closure_le _ |>.mpr ?_)
  · rintro _ ⟨u, hu, v, hv, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hu) (Subgroup.subset_closure hv)
  · intro y hy
    have h1 : 1 < (longInvAt M Δ a).ncard := by
      rw [hA.ncard_longInvAt]
      have := hA.four_le_q
      omega
    obtain ⟨z, hz, hzy⟩ := Set.exists_ne_of_one_lt_ncard h1 y
    have hzZ := ((hA.mem_longInvAt_iff hQ).mp hz).1
    have hyZ := ((hA.mem_longInvAt_iff hQ).mp hy).1
    have hzy' : z * y ∈ longInvAt M Δ a := by
      refine (hA.mem_longInvAt_iff hQ).mpr ⟨Subgroup.mul_mem _ hzZ hyZ, fun h1 => hzy ?_⟩
      rw [← inv_eq_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right
        (mul_self_eq_one_of_mem_longInv hy.1)]
    refine Subgroup.subset_closure ⟨z, hz, z * y, hzy', ?_⟩
    rw [← mul_assoc, mul_self_eq_one_of_mem_longInv hz.1, one_mul]

theorem IsNaturalSE.mul_self_of_mem_mulLongInvClosure (hM : IsNaturalSE M) {a : Δ}
    {w : Equiv.Perm Δ} (hw : w ∈ mulLongInvClosure M a) : w * w = 1 := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hM
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
  have : Nontrivial Δ := hA.nontrivial
  obtain ⟨b, hb⟩ := exists_ne a
  obtain ⟨t, ht, hta⟩ := hA.exists_involution_smul_eq hb.symm
  have hL := hA.lemma32 hQ ht (by rw [hta]; exact hb)
  rw [hM.mulLongInvClosure_eq hQ] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  have h2 := hL.elemAbelian_center.2 z hz
  rw [← map_mul, ← pow_two, h2, map_one]

theorem IsNaturalSE.commute_of_mem_mulLongInvClosure (hM : IsNaturalSE M) {a : Δ}
    {w w' : Equiv.Perm Δ} (hw : w ∈ mulLongInvClosure M a) (hw' : w' ∈ mulLongInvClosure M a) :
    w * w' = w' * w := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hM
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
  rw [hM.mulLongInvClosure_eq hQ] at hw hw'
  obtain ⟨z, hz, rfl⟩ := hw
  obtain ⟨z', hz', rfl⟩ := hw'
  rw [← map_mul, ← map_mul, (mem_rootCenter_iff.mp hz').2 z (rootCenter_le _ hz)]

theorem IsNaturalSE.mem_mulLongInvClosure_of_mul_self (hM : IsNaturalSE M) {a : Δ}
    {y : Equiv.Perm Δ} (hyM : y ∈ M) (hya : y a = a) (hy : y * y = 1) :
    y ∈ mulLongInvClosure M a := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hM
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
  rw [hM.mulLongInvClosure_eq hQ]
  by_cases h1 : y = 1
  · rw [h1]
    exact Subgroup.one_mem _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf (⟨y, hyM⟩ : M) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy) h1
  have hJ : (⟨y, hyM⟩ : M) ∈ longInvAt M Δ a := ⟨hA.mem_longInv_iff.mpr h2, hya⟩
  exact ⟨_, ((hA.mem_longInvAt_iff hQ).mp hJ).1, rfl⟩

end SEFactor

namespace HoltData

section Coordinates

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem exists_mem_finsetSup_rho_eq (s : Finset D.ι) (m : ∀ i, Equiv.Perm (D.Ψc i))
    (hm : ∀ i ∈ s, m i ∈ D.M i) :
    ∃ h : jHull G Ω, (h : G) ∈ s.sup D.L ∧ ∀ i ∈ s, D.ρ i h = m i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨h, hh, hhs⟩ := ih fun i hi => hm i (Finset.mem_insert_of_mem hi)
    obtain ⟨l, hl, hla⟩ := mem_M.mp (hm a (Finset.mem_insert_self a s))
    refine ⟨h * l, ?_, fun i hi => ?_⟩
    · rw [Finset.sup_insert]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hl)
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [map_mul, (D.rho_eq_one_of_mem_sup_finsetSup s (h := h)
          (Subgroup.mem_sup_right hh)).1 i ha, one_mul, hla]
      · rw [map_mul, rho_eq_one_of_mem_L (by rintro rfl; exact ha hi) hl, mul_one, hhs i hi]

theorem mem_orbit_sup_finsetSup_iff (s : Finset D.ι) (ω ω' : Ω) :
    ω' ∈ orbit (jOddCore G Ω ⊔ s.sup D.L : Subgroup G) ω ↔
      ∀ j ∉ s, D.coord ω' j = D.coord ω j := by
  have hle : jOddCore G Ω ⊔ s.sup D.L ≤ jHull G Ω :=
    sup_le jOddCore_le_jHull (Finset.sup_le fun i _ => D.L_le i)
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩ j hj
    have h1 := (D.rho_eq_one_of_mem_sup_finsetSup s (h := ⟨g, hle hg⟩) hg).1 j hj
    have h2 := D.coord_smul ⟨g, hle hg⟩ ω j
    rw [h1, Equiv.Perm.one_apply] at h2
    exact h2
  · intro h
    have hm : ∀ i, ∃ m : D.M i, m • D.coord ω i = D.coord ω' i := fun i =>
      have := (D.factor i).isPretransitive
      exists_smul_eq (D.M i) (D.coord ω i) (D.coord ω' i)
    choose m hm using hm
    obtain ⟨g, hg, hgm⟩ :=
      D.exists_mem_finsetSup_rho_eq s (fun i => (m i : Equiv.Perm (D.Ψc i))) fun i _ => (m i).2
    have hc : D.coord ((g : G) • ω) = D.coord ω' := by
      funext i
      rw [D.coord_smul]
      by_cases hi : i ∈ s
      · rw [hgm i hi]
        exact hm i
      · rw [(D.rho_eq_one_of_mem_sup_finsetSup s (h := g) (Subgroup.mem_sup_right hg)).1 i hi,
          Equiv.Perm.one_apply, h i hi]
    obtain ⟨⟨o, ho⟩, hoω⟩ := (D.coord_eq_iff _ _).mp hc
    refine ⟨⟨o * g, Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hg)⟩,
      ?_⟩
    change (o * (g : G)) • ω = ω'
    rw [mul_smul]
    exact hoω

include D in
theorem isPretransitive_jHull : IsPretransitive (jHull G Ω) Ω := by
  refine ⟨fun ω ω' => ?_⟩
  obtain ⟨⟨g, hg⟩, hgω⟩ := (D.mem_orbit_sup_finsetSup_iff Finset.univ ω ω').mpr
    fun j hj => absurd (Finset.mem_univ j) hj
  exact ⟨⟨g, sup_le jOddCore_le_jHull (Finset.sup_le fun i _ => D.L_le i) hg⟩, hgω⟩

include D in
theorem longInvAt_nonempty (β : Ω) : (longInvAt G Ω β).Nonempty := by
  obtain ⟨ω₀, hω₀⟩ := exists_mem_longInvAt D.t_mem
  have := D.isPretransitive_jHull
  obtain ⟨h, hh⟩ := exists_smul_eq (jHull G Ω) ω₀ β
  have h2 := conj_mem_longInvAt hω₀ (h : G)
  rw [show (h : G) • ω₀ = β from hh] at h2
  exact ⟨_, h2⟩

variable {D}

theorem exists_rho_eq_of_mem_iSup {V : D.ι → Subgroup G} (hV : ∀ i, V i ≤ D.L i)
    {h : jHull G Ω} (hh : (h : G) ∈ ⨆ i, V i) (i : D.ι) :
    ∃ v : jHull G Ω, (v : G) ∈ V i ∧ D.ρ i v = D.ρ i h := by
  set C : Subgroup (jHull G Ω) := (((V i).subgroupOf (jHull G Ω)).map (D.ρ i)).comap (D.ρ i)
  have hle : (⨆ j, V j) ≤ C.map (jHull G Ω).subtype := by
    refine iSup_le fun j g hg => ?_
    have hgH : g ∈ jHull G Ω := D.L_le j (hV j hg)
    refine ⟨⟨g, hgH⟩, ?_, rfl⟩
    by_cases hji : j = i
    · subst hji
      exact ⟨⟨g, hgH⟩, hg, rfl⟩
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [map_one, rho_eq_one_of_mem_L hji (hV j hg)]
  obtain ⟨c, hc, hch⟩ := hle hh
  obtain rfl : c = h := Subtype.ext hch
  obtain ⟨v, hv, hvh⟩ := hc
  exact ⟨v, hv, hvh⟩

theorem coord_injective (hO : jOddCore G Ω = ⊥) : Function.Injective D.coord := fun ω ω' h => by
  have h' := (D.coord_eq_iff ω ω').mp h
  rw [orbit_jOddCore_eq_singleton hO] at h'
  exact (Set.mem_singleton_iff.mp h').symm

theorem eq_one_of_forall_rho_eq_one [FaithfulSMul G Ω] (hO : jOddCore G Ω = ⊥)
    {h : jHull G Ω} (h1 : ∀ i, D.ρ i h = 1) : h = 1 := by
  have hk : (h : G) ∈ jOrbitKernel G Ω := mem_jOrbitKernel_iff_rho.mpr h1
  rw [jOrbitKernel_eq_bot hO, Subgroup.mem_bot] at hk
  exact Subtype.ext hk

theorem commute_of_mem_L (hO : jOddCore G Ω = ⊥) {i j : D.ι} (hij : i ≠ j) {x y : G}
    (hx : x ∈ D.L i) (hy : y ∈ D.L j) : x * y = y * x := by
  have h := commutator_L_le hij (Subgroup.commutator_mem_commutator hx hy)
  rw [hO, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

theorem eq_of_rho_eq_of_mem_L (hO : jOddCore G Ω = ⊥) {i : D.ι} {h h' : jHull G Ω}
    (hh : (h : G) ∈ D.L i) (hh' : (h' : G) ∈ D.L i) (he : D.ρ i h = D.ρ i h') : h = h' := by
  have hm : ((h⁻¹ * h' : jHull G Ω) : G) ∈ D.L i := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (D.L i).mul_mem ((D.L i).inv_mem hh) hh'
  have h1 := mem_jOddCore_of_mem_L hm (by rw [map_mul, map_inv, he, inv_mul_cancel])
  rw [hO, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp (Subtype.ext h1)

theorem mem_iSup_of_forall_rho [FaithfulSMul G Ω] (hO : jOddCore G Ω = ⊥)
    {V : D.ι → Subgroup G} (hV : ∀ i, V i ≤ D.L i) {h : jHull G Ω}
    (hh : ∀ i, ∃ v : jHull G Ω, (v : G) ∈ V i ∧ D.ρ i v = D.ρ i h) : (h : G) ∈ ⨆ i, V i := by
  suffices key : ∀ (s : Finset D.ι) (h : jHull G Ω),
      (∀ i ∈ s, ∃ v : jHull G Ω, (v : G) ∈ V i ∧ D.ρ i v = D.ρ i h) →
        (∀ j ∉ s, D.ρ j h = 1) → (h : G) ∈ s.sup V by
    have h1 := key Finset.univ h (fun i _ => hh i) fun j hj => absurd (Finset.mem_univ j) hj
    rwa [Finset.sup_univ_eq_iSup] at h1
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro h _ h1
    rw [eq_one_of_forall_rho_eq_one hO fun j => h1 j (Finset.notMem_empty j)]
    exact Subgroup.one_mem _
  | insert a s ha ih =>
    intro h hs hout
    obtain ⟨v, hv, hva⟩ := hs a (Finset.mem_insert_self a s)
    have hvL := hV a hv
    have hrest := ih (v⁻¹ * h) (fun i hi => ?_) (fun j hj => ?_)
    · rw [Finset.sup_insert]
      have e : (h : G) = v * ((v⁻¹ * h : jHull G Ω) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hrest)
    · obtain ⟨w, hw, hwi⟩ := hs i (Finset.mem_insert_of_mem hi)
      refine ⟨w, hw, ?_⟩
      rw [map_mul, map_inv, rho_eq_one_of_mem_L (by rintro rfl; exact ha hi) hvL, inv_one,
        one_mul, hwi]
    · rw [map_mul, map_inv]
      by_cases hja : j = a
      · subst hja
        rw [hva, inv_mul_cancel]
      · rw [rho_eq_one_of_mem_L (Ne.symm hja) hvL, inv_one, one_mul]
        exact hout j (by simp [hja, hj])

variable (D) in
abbrev wModel (B : Ω) (i : D.ι) : Subgroup (Equiv.Perm (D.Ψc i)) :=
  mulLongInvClosure (D.ρ i).range (D.coord B i)

variable (D) in
@[expose] def W (B : Ω) (i : D.ι) : Subgroup G :=
  D.L i ⊓ ((D.wModel B i).comap (D.ρ i)).map (jHull G Ω).subtype

theorem mem_W {B : Ω} {i : D.ι} {g : G} :
    g ∈ D.W B i ↔ g ∈ D.L i ∧ ∃ h : jHull G Ω, (h : G) = g ∧ D.ρ i h ∈ D.wModel B i := by
  simp only [W, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  exact and_congr_right fun _ => ⟨fun ⟨h, h1, h2⟩ => ⟨h, h2, h1⟩, fun ⟨h, h1, h2⟩ => ⟨h, h2, h1⟩⟩

variable (D) in
theorem W_le_L (B : Ω) (i : D.ι) : D.W B i ≤ D.L i := inf_le_left

variable (D) in
theorem W_le_jHull (B : Ω) (i : D.ι) : D.W B i ≤ jHull G Ω := (D.W_le_L B i).trans (D.L_le i)

variable (D) in
theorem wModel_le_M (B : Ω) (i : D.ι) : D.wModel B i ≤ D.M i := by
  rw [wModel, mulLongInvClosure, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨u, hu, v, hv, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, Subgroup.coe_subtype]
  have hu' := (mem_longInvAt_subgroup_perm_iff.mp hu).1
  have hv' := (mem_longInvAt_subgroup_perm_iff.mp hv).1
  by_cases hout : IsOuterFactor (D.M i)
  · rw [hout.1, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      sign_eq_of_mem_longInv_perm hu' hv', Int.units_mul_self]
  · have hR := D.range_rho_of_not_isOuterFactor hout
    have hu2 : (u : Equiv.Perm (D.Ψc i)) ∈ D.M i := hR ▸ u.2
    have hv2 : (v : Equiv.Perm (D.Ψc i)) ∈ D.M i := hR ▸ v.2
    exact (D.M i).mul_mem hu2 hv2

theorem exists_mem_W_rho_eq {B : Ω} {i : D.ι} {y : Equiv.Perm (D.Ψc i)}
    (hy : y ∈ D.wModel B i) : ∃ v : jHull G Ω, (v : G) ∈ D.W B i ∧ D.ρ i v = y := by
  obtain ⟨l, hl, hly⟩ := mem_M.mp (D.wModel_le_M B i hy)
  exact ⟨l, mem_W.mpr ⟨hl, l, rfl, hly ▸ hy⟩, hly⟩

theorem conj_mem_W {B : Ω} {i : D.ι} {h : G} (hh : h ∈ jHull G Ω) (hB : h • B = B) {g : G}
    (hg : g ∈ D.W B i) : h * g * h⁻¹ ∈ D.W B i := by
  obtain ⟨hgL, g', rfl, hg'⟩ := mem_W.mp hg
  refine mem_W.mpr ⟨(Subgroup.mem_normalizer_iff.mp (D.le_normalizer i hh) _).mp hgL,
    ⟨h, hh⟩ * g' * ⟨h, hh⟩⁻¹, rfl, ?_⟩
  rw [map_mul, map_mul, map_inv]
  have hfix : D.ρ i ⟨h, hh⟩ (D.coord B i) = D.coord B i := by
    rw [← D.coord_smul]
    exact congrFun (congrArg D.coord hB) i
  exact conj_mem_mulLongInvClosure (R := (D.ρ i).range) ⟨⟨h, hh⟩, rfl⟩ hfix hg'

theorem mem_normalizer_W {B : Ω} {i : D.ι} {h : G} (hh : h ∈ jHull G Ω) (hB : h • B = B) :
    h ∈ Subgroup.normalizer (D.W B i : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨conj_mem_W hh hB, fun hg => ?_⟩
  have hB' : h⁻¹ • B = B := by rw [inv_smul_eq_iff, hB]
  have h' := conj_mem_W (inv_mem hh) hB' hg
  rwa [show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at h'

theorem smul_eq_of_mem_W (hO : jOddCore G Ω = ⊥) {B : Ω} {i : D.ι} {g : G} (hg : g ∈ D.W B i) :
    g • B = B := by
  obtain ⟨hgL, g', rfl, hg'⟩ := mem_W.mp hg
  refine coord_injective (D := D) hO (funext fun j => ?_)
  rw [D.coord_smul]
  by_cases hji : j = i
  · subst hji
    exact (mulLongInvClosure_le _ _ hg').2
  · rw [rho_eq_one_of_mem_L (Ne.symm hji) hgL, Equiv.Perm.one_apply]

variable (D) in
theorem mem_socPre_or_t_mul_mem {v : G} (hv : v ∈ jHull G Ω) :
    v ∈ D.socPre ∨ D.t * v ∈ D.socPre := by
  have hN : Subgroup.zpowers D.t ≤ Subgroup.normalizer (D.socPre : Set G) :=
    (Subgroup.zpowers_le.mpr (mem_jHull_of_mem_longInv D.t_mem)).trans D.le_normalizer_socPre
  rw [← D.socPre_sup_zpowers, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hv
  obtain ⟨a, ha, s, hs, rfl⟩ := Set.mem_mul.mp hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have htt := mul_self_eq_one_of_mem_longInv D.t_mem
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, htt, one_zpow, one_mul]
    exact hs
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul, ← mul_assoc, htt, one_mul]
    exact hs

theorem isPGroup_iSup_of_le_L (hO : jOddCore G Ω = ⊥) {U : D.ι → Subgroup G}
    (hUL : ∀ i, U i ≤ D.L i) (hU : ∀ i, IsPGroup 2 (U i)) : IsPGroup 2 (⨆ i, U i : Subgroup G) := by
  suffices key : ∀ s : Finset D.ι, IsPGroup 2 (s.sup U : Subgroup G) by
    have h := key Finset.univ
    rwa [Finset.sup_univ_eq_iSup] at h
  intro s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact IsPGroup.of_bot
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    refine (hU a).to_sup_of_normal_left' ih ?_
    refine Finset.sup_le fun j hj => ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (commute_of_mem_L hO (by rintro rfl; exact ha hj) (hUL j hy) (hUL a hz)).symm

end Coordinates

section Lifting

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem exists_conj_rho_eq {u : G} {B : Ω} (hu : u ∈ longInvAt G Ω B) (s : Finset D.ι)
    (y : ∀ i, Equiv.Perm (D.Ψc i))
    (hy : ∀ i ∈ s, y i ∈ longInvAt (Equiv.Perm (D.Ψc i)) (D.Ψc i) (D.coord B i))
    (hyR : ∀ i ∈ s, y i ∈ (D.ρ i).range) :
    ∃ l : jHull G Ω, (l : G) ∈ jOddCore G Ω ⊔ s.sup D.L ∧ (l : G) • B = B ∧
      ∀ i ∈ s, D.ρ i (l * ⟨u, mem_jHull_of_mem_longInv hu.1⟩ * l⁻¹) = y i := by
  set uH : jHull G Ω := ⟨u, mem_jHull_of_mem_longInv hu.1⟩
  have hg : ∀ i ∈ s, ∃ g ∈ D.M i, g * D.ρ i uH * g⁻¹ = y i := fun i hi =>
    (D.factor i).exists_conj_eq (D.rho_mem_longInvAt hu i).1 (hy i hi).1 (by
      by_cases hout : IsOuterFactor (D.M i)
      · exact Or.inr hout.1
      · have h := hyR i hi
        rw [D.range_rho_of_not_isOuterFactor hout] at h
        exact Or.inl ⟨(D.rho_mem_M_iff hu.1 i).mpr hout, h⟩)
  choose! g hgM hgy using hg
  obtain ⟨h, hh, hhg⟩ := D.exists_mem_finsetSup_rho_eq s g hgM
  have hfix : ∀ i ∈ s, g i (D.coord B i) = D.coord B i := by
    intro i hi
    have h1 : y i (g i (D.coord B i)) = g i (D.coord B i) := by
      rw [← hgy i hi]
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
      rw [(D.rho_apply_eq_iff hu i (D.coord B i)).mpr rfl]
    exact (apply_eq_self_iff_of_mem_longInvAt_perm (hy i hi)).mp h1
  have hc : D.coord ((h : G) • B) = D.coord B := by
    funext i
    rw [D.coord_smul]
    by_cases hi : i ∈ s
    · rw [hhg i hi, hfix i hi]
    · rw [(D.rho_eq_one_of_mem_sup_finsetSup s (h := h) (Subgroup.mem_sup_right hh)).1 i hi,
        Equiv.Perm.one_apply]
  obtain ⟨⟨o, ho⟩, hoB⟩ := (D.coord_eq_iff _ _).mp hc
  refine ⟨⟨o, jOddCore_le_jHull ho⟩ * h, Subgroup.mul_mem _ (Subgroup.mem_sup_left ho)
    (Subgroup.mem_sup_right hh), ?_, fun i hi => ?_⟩
  · change (o * (h : G)) • B = B
    rw [mul_smul]
    exact hoB
  · have hρo : D.ρ i ⟨o, jOddCore_le_jHull ho⟩ = 1 := rho_eq_one_of_mem_jOddCore ho i
    rw [map_mul, map_mul, map_inv, map_mul, hρo, one_mul, hhg i hi, hgy i hi]

theorem exists_mem_L_conj_rho_eq {u : G} {B : Ω} (hu : u ∈ longInvAt G Ω B) {i : D.ι}
    {y : Equiv.Perm (D.Ψc i)}
    (hy : y ∈ longInvAt (Equiv.Perm (D.Ψc i)) (D.Ψc i) (D.coord B i))
    (hyR : y ∈ (D.ρ i).range) :
    ∃ l : jHull G Ω, (l : G) ∈ D.L i ∧ (l : G) • B = B ∧
      D.ρ i (l * ⟨u, mem_jHull_of_mem_longInv hu.1⟩ * l⁻¹) = y ∧
      ∀ j, j ≠ i → D.ρ j (l * ⟨u, mem_jHull_of_mem_longInv hu.1⟩ * l⁻¹) =
        D.ρ j ⟨u, mem_jHull_of_mem_longInv hu.1⟩ := by
  obtain ⟨l, hl, hlB, hly⟩ := D.exists_conj_rho_eq hu {i} (Function.update 1 i y)
    (by simpa using hy) (by simpa using hyR)
  have hlL : (l : G) ∈ D.L i := by
    rwa [Finset.sup_singleton, sup_eq_right.mpr (D.oddCore_le i)] at hl
  refine ⟨l, hlL, hlB, by simpa using hly i (Finset.mem_singleton_self i), fun j hj => ?_⟩
  rw [map_mul, map_mul, map_inv, rho_eq_one_of_mem_L (Ne.symm hj) hlL, one_mul, inv_one, mul_one]

end Lifting

section K1

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem wModel_eq_of_alternatingGroup (B : Ω) {i : D.ι}
    (hM : D.M i = alternatingGroup (D.Ψc i)) (h7 : 7 ≤ Fintype.card (D.Ψc i)) :
    D.wModel B i =
      alternatingGroup (D.Ψc i) ⊓ stabilizer (Equiv.Perm (D.Ψc i)) (D.coord B i) := by
  have hAR : alternatingGroup (D.Ψc i) ≤ (D.ρ i).range := by
    rw [D.range_rho, ← hM]
    exact le_sup_left
  exact mulLongInvClosure_eq_of_alternatingGroup_le h7 hAR ⟨D.tHull, rfl⟩
    (D.rho_mem_longInv D.t_mem i) _

omit [Finite G] in
theorem wModel_eq_of_isNaturalSE (B : Ω) {i : D.ι} (hM : IsNaturalSE (D.M i)) :
    D.wModel B i = mulLongInvClosure (D.M i) (D.coord B i) := by
  rw [wModel, D.range_rho_of_not_isOuterFactor hM.not_isOuterFactor]

theorem mem_wModel_of_mul_self (B : Ω) {i : D.ι} {y : Equiv.Perm (D.Ψc i)} (hyM : y ∈ D.M i)
    (hyB : y (D.coord B i) = D.coord B i) (hy : y * y = 1) : y ∈ D.wModel B i := by
  rcases D.factor i with ⟨hA, h7⟩ | hSE
  · have hA' : D.M i = alternatingGroup (D.Ψc i) := hA
    rw [D.wModel_eq_of_alternatingGroup B hA' h7]
    exact ⟨hA' ▸ hyM, hyB⟩
  · rw [D.wModel_eq_of_isNaturalSE B hSE]
    exact hSE.mem_mulLongInvClosure_of_mul_self hyM hyB hy

variable {D}

theorem W_le_closure (hO : jOddCore G Ω = ⊥) (B : Ω) (i : D.ι) :
    D.W B i ≤ Subgroup.closure (longInvAt G Ω B) := by
  obtain ⟨x, hx⟩ := D.longInvAt_nonempty B
  set xH : jHull G Ω := ⟨x, mem_jHull_of_mem_longInv hx.1⟩
  set C := Subgroup.closure (longInvAt G Ω B)
  have hT : D.wModel B i ≤ ((D.L i ⊓ C).subgroupOf (jHull G Ω)).map (D.ρ i) := by
    rw [wModel, mulLongInvClosure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    obtain ⟨l, hlL, hlB, hlu, -⟩ :=
      D.exists_mem_L_conj_rho_eq hx (mem_longInvAt_subgroup_perm_iff.mp hu) u.2
    obtain ⟨l', hlL', hlB', hlv, -⟩ :=
      D.exists_mem_L_conj_rho_eq hx (mem_longInvAt_subgroup_perm_iff.mp hv) v.2
    have hJ : ∀ m : jHull G Ω, (m : G) • B = B → ((m * xH * m⁻¹ : jHull G Ω) : G) ∈ C :=
      fun m hm => Subgroup.subset_closure (by
        have h := conj_mem_longInvAt hx (m : G)
        rwa [hm] at h)
    refine ⟨(l * xH * l⁻¹) * (l' * xH * l'⁻¹), ⟨?_, Subgroup.mul_mem _ (hJ l hlB) (hJ l' hlB')⟩,
      by rw [map_mul, hlu, hlv]; rfl⟩
    have e : (((l * xH * l⁻¹) * (l' * xH * l'⁻¹) : jHull G Ω) : G) =
        (l : G) * (x * ((l : G)⁻¹ * l') * x⁻¹) * (l' : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, xH]
      rw [inv_eq_self_of_mem_longInv hx.1]
      group
    show (((l * xH * l⁻¹) * (l' * xH * l'⁻¹) : jHull G Ω) : G) ∈ D.L i
    rw [e]
    refine (D.L i).mul_mem ((D.L i).mul_mem hlL ?_) ((D.L i).inv_mem hlL')
    exact (Subgroup.mem_normalizer_iff.mp (D.le_normalizer i (mem_jHull_of_mem_longInv hx.1))
      _).mp ((D.L i).mul_mem ((D.L i).inv_mem hlL) hlL')
  intro g hg
  obtain ⟨hgL, g', rfl, hg'⟩ := mem_W.mp hg
  obtain ⟨c, ⟨hcL, hcC⟩, hcg⟩ := hT hg'
  rw [← eq_of_rho_eq_of_mem_L hO hcL hgL hcg]
  exact hcC

theorem closure_longInv_stabilizer [FaithfulSMul G Ω] (hO : jOddCore G Ω = ⊥) {B : Ω} {x : G}
    (hx : x ∈ longInvAt G Ω B) :
    Subgroup.closure (longInvAt G Ω B) = Subgroup.zpowers x ⊔ ⨆ i, D.W B i := by
  refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure hx))
    (iSup_le fun i => W_le_closure hO B i))
  rw [Subgroup.closure_le]
  intro u hu
  set xH : jHull G Ω := ⟨x, mem_jHull_of_mem_longInv hx.1⟩
  set uH : jHull G Ω := ⟨u, mem_jHull_of_mem_longInv hu.1⟩
  have hxu : ((xH * uH : jHull G Ω) : G) ∈ ⨆ i, D.W B i := by
    refine mem_iSup_of_forall_rho hO (V := D.W B) (fun i => D.W_le_L B i) fun i =>
      exists_mem_W_rho_eq ?_
    rw [map_mul]
    exact mul_mem_mulLongInvClosure (R := (D.ρ i).range) (u := ⟨D.ρ i xH, xH, rfl⟩)
      (v := ⟨D.ρ i uH, uH, rfl⟩)
      (mem_longInvAt_subgroup_perm_iff.mpr (D.rho_mem_longInvAt hx i))
      (mem_longInvAt_subgroup_perm_iff.mpr (D.rho_mem_longInvAt hu i))
  have e : u = x * (x * u) := by rw [← mul_assoc, mul_self_eq_one_of_mem_longInv hx.1, one_mul]
  rw [SetLike.mem_coe, e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    (Subgroup.mem_sup_right hxu)

theorem mem_closure_longInv_stabilizer_of_mul_self (D : HoltData G Ω) [FaithfulSMul G Ω]
    (hO : jOddCore G Ω = ⊥) {B : Ω} {v : G} (hv : v ∈ jHull G Ω) (hvB : v • B = B)
    (hv2 : v * v = 1) : v ∈ Subgroup.closure (longInvAt G Ω B) := by
  obtain ⟨x, hx⟩ := D.longInvAt_nonempty B
  rw [D.closure_longInv_stabilizer hO hx]
  set vH : jHull G Ω := ⟨v, hv⟩
  set xH : jHull G Ω := ⟨x, mem_jHull_of_mem_longInv hx.1⟩
  have hvi : ∀ i, D.ρ i vH (D.coord B i) = D.coord B i := fun i => by
    rw [← D.coord_smul]
    exact congrFun (congrArg D.coord hvB) i
  have hvi2 : ∀ i, D.ρ i vH * D.ρ i vH = 1 := fun i => by
    rw [← map_mul, show vH * vH = 1 from Subtype.ext hv2, map_one]
  have hxi : ∀ i, D.ρ i xH (D.coord B i) = D.coord B i := fun i =>
    (D.rho_apply_eq_iff hx i (D.coord B i)).mpr rfl
  rcases D.mem_socPre_or_t_mul_mem hv with hs | hs
  · refine Subgroup.mem_sup_right (mem_iSup_of_forall_rho hO (V := D.W B)
      (fun i => D.W_le_L B i) (h := vH) fun i => exists_mem_W_rho_eq ?_)
    exact D.mem_wModel_of_mul_self B (rho_mem_M_of_mem_socPre (h := vH) hs i) (hvi i) (hvi2 i)
  · have hxv : ((xH * vH : jHull G Ω) : G) ∈ ⨆ i, D.W B i := by
      refine mem_iSup_of_forall_rho hO (V := D.W B) (fun i => D.W_le_L B i) fun i =>
        exists_mem_W_rho_eq ?_
      rcases D.factor i with ⟨hA, h7⟩ | hSE
      · have hA' : D.M i = alternatingGroup (D.Ψc i) := hA
        rw [D.wModel_eq_of_alternatingGroup B hA' h7]
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have htv := rho_mem_M_of_mem_socPre (h := D.tHull * vH) hs i
          rw [hA', map_mul, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul] at htv
          rw [map_mul, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
            sign_eq_of_mem_longInv_perm (D.rho_mem_longInv hx.1 i) (D.rho_mem_longInv D.t_mem i)]
          exact htv
        · change (D.ρ i (xH * vH)) (D.coord B i) = D.coord B i
          rw [map_mul, Equiv.Perm.mul_apply, hvi i, hxi i]
      · rw [D.wModel_eq_of_isNaturalSE B hSE, map_mul]
        have hR := D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor
        have hxM : D.ρ i xH ∈ D.M i := hR ▸ ⟨xH, rfl⟩
        have hvM : D.ρ i vH ∈ D.M i := hR ▸ ⟨vH, rfl⟩
        exact Subgroup.mul_mem _
          (hSE.mem_mulLongInvClosure_of_mul_self hxM (hxi i) (by
            rw [← map_mul, show xH * xH = 1 from
              Subtype.ext (mul_self_eq_one_of_mem_longInv hx.1), map_one]))
          (hSE.mem_mulLongInvClosure_of_mul_self hvM (hvi i) (hvi2 i))
    have e : v = x * (x * v) := by rw [← mul_assoc, mul_self_eq_one_of_mem_longInv hx.1, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
      (Subgroup.mem_sup_right hxv)

omit [Finite G] in
theorem mem_iSup_W_iff [FaithfulSMul G Ω] (hO : jOddCore G Ω = ⊥) {B : Ω} {g : G}
    (hg : g ∈ jHull G Ω) : g ∈ ⨆ i, D.W B i ↔ ∀ i, D.ρ i ⟨g, hg⟩ ∈ D.wModel B i := by
  refine ⟨fun h i => ?_, fun h => mem_iSup_of_forall_rho hO (V := D.W B) (fun i => D.W_le_L B i)
    (h := ⟨g, hg⟩) fun i => exists_mem_W_rho_eq (h i)⟩
  obtain ⟨v, hvW, hvg⟩ := exists_rho_eq_of_mem_iSup (fun j => D.W_le_L B j) (h := ⟨g, hg⟩) h i
  obtain ⟨-, v', hv', hv'W⟩ := mem_W.mp hvW
  rw [← hvg, ← show v' = v from Subtype.ext hv']
  exact hv'W

theorem mem_iSup_W_iff_of_mem_longInvAt [FaithfulSMul G Ω] (hO : jOddCore G Ω = ⊥) {B : Ω}
    {u : G} (hu : u ∈ longInvAt G Ω B) :
    u ∈ ⨆ i, D.W B i ↔ ∀ i, ¬ IsOuterFactor (D.M i) := by
  rw [D.mem_iSup_W_iff hO (mem_jHull_of_mem_longInv hu.1)]
  refine ⟨fun h i => (D.rho_mem_M_iff hu.1 i).mp (D.wModel_le_M B i (h i)), fun h i => ?_⟩
  refine D.mem_wModel_of_mul_self B ((D.rho_mem_M_iff hu.1 i).mpr (h i))
    ((D.rho_apply_eq_iff hu i (D.coord B i)).mpr rfl) ?_
  rw [← map_mul, show (⟨u, mem_jHull_of_mem_longInv hu.1⟩ : jHull G Ω) *
    ⟨u, mem_jHull_of_mem_longInv hu.1⟩ = 1 from Subtype.ext (mul_self_eq_one_of_mem_longInv hu.1),
    map_one]

end K1

section K4

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {D : HoltData G Ω}

private theorem isPerfect_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Group.IsPerfect X) : Group.IsPerfect Y := by
  refine ⟨?_⟩
  have h1 := h.commutator_eq_top
  rw [commutator_def] at h1 ⊢
  have h2 := congrArg (Subgroup.map e.toMonoidHom) h1
  rw [Subgroup.map_commutator, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective _ e.surjective] at h2
  exact h2

variable (D) in
@[expose] noncomputable def wEquiv (hO : jOddCore G Ω = ⊥) (B : Ω) (i : D.ι) :
    D.W B i ≃* D.wModel B i :=
  MulEquiv.ofBijective
    (((D.ρ i).comp (Subgroup.inclusion (D.W_le_jHull B i))).codRestrict (D.wModel B i)
      fun g => by
        obtain ⟨-, h, hh, hρ⟩ := mem_W.mp g.2
        rwa [MonoidHom.comp_apply,
          show Subgroup.inclusion (D.W_le_jHull B i) g = h from Subtype.ext hh.symm])
    ⟨fun g g' hgg' => by
      have h1 := congrArg Subtype.val hgg'
      simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply] at h1
      have h2 := eq_of_rho_eq_of_mem_L hO ((D.W_le_L B i) g.2) ((D.W_le_L B i) g'.2) h1
      have h3 : ((Subgroup.inclusion (D.W_le_jHull B i) g : jHull G Ω) : G) =
          (Subgroup.inclusion (D.W_le_jHull B i) g' : jHull G Ω) := congrArg Subtype.val h2
      exact Subtype.ext h3,
    fun y => by
      obtain ⟨v, hvW, hvy⟩ := exists_mem_W_rho_eq y.2
      refine ⟨⟨v, hvW⟩, Subtype.ext ?_⟩
      simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
      exact hvy⟩

@[simp] theorem coe_wEquiv_apply (hO : jOddCore G Ω = ⊥) {B : Ω} {i : D.ι} (g : D.W B i) :
    ((D.wEquiv hO B i g : D.wModel B i) : Equiv.Perm (D.Ψc i)) =
      D.ρ i (Subgroup.inclusion (D.W_le_jHull B i) g) := rfl

theorem mul_self_eq_one_of_mem_W (hO : jOddCore G Ω = ⊥) {B : Ω} {i : D.ι}
    (hM : IsNaturalSE (D.M i)) {w : G} (hw : w ∈ D.W B i) : w * w = 1 := by
  obtain ⟨hwL, w', rfl, hw'⟩ := mem_W.mp hw
  rw [D.wModel_eq_of_isNaturalSE B hM] at hw'
  have h1 := mem_jOddCore_of_mem_L (h := w' * w') ((D.L i).mul_mem hwL hwL)
    (by rw [map_mul]; exact hM.mul_self_of_mem_mulLongInvClosure hw')
  rw [hO, Subgroup.mem_bot] at h1
  exact h1

theorem commute_of_mem_W (hO : jOddCore G Ω = ⊥) {B : Ω} {i : D.ι} (hM : IsNaturalSE (D.M i))
    {w w' : G} (hw : w ∈ D.W B i) (hw' : w' ∈ D.W B i) : w * w' = w' * w := by
  obtain ⟨hwL, v, rfl, hv⟩ := mem_W.mp hw
  obtain ⟨hwL', v', rfl, hv'⟩ := mem_W.mp hw'
  rw [D.wModel_eq_of_isNaturalSE B hM] at hv hv'
  have h := eq_of_rho_eq_of_mem_L hO (h := v * v') (h' := v' * v) ((D.L i).mul_mem hwL hwL')
    ((D.L i).mul_mem hwL' hwL)
    (by rw [map_mul, map_mul]; exact hM.commute_of_mem_mulLongInvClosure hv hv')
  exact congrArg Subtype.val h

theorem isSimpleGroup_W_of_alternatingGroup [Finite G] (hO : jOddCore G Ω = ⊥) (B : Ω)
    {i : D.ι} (hM : D.M i = alternatingGroup (D.Ψc i)) (h7 : 7 ≤ Fintype.card (D.Ψc i)) :
    IsSimpleGroup (D.W B i) := by
  have := isSimpleGroup_alternatingGroup_inf_stabilizer (by omega) (D.coord B i)
  exact ((D.wEquiv hO B i).trans
    (MulEquiv.subgroupCongr (D.wModel_eq_of_alternatingGroup B hM h7))).isSimpleGroup

theorem isPerfect_W_of_alternatingGroup [Finite G] (hO : jOddCore G Ω = ⊥) (B : Ω)
    {i : D.ι} (hM : D.M i = alternatingGroup (D.Ψc i)) (h7 : 7 ≤ Fintype.card (D.Ψc i)) :
    Group.IsPerfect (D.W B i) :=
  isPerfect_of_mulEquiv' ((D.wEquiv hO B i).trans
    (MulEquiv.subgroupCongr (D.wModel_eq_of_alternatingGroup B hM h7))).symm
    (isPerfect_alternatingGroup_inf_stabilizer (by omega) (D.coord B i))

theorem commute_of_mem_W_of_ne (hO : jOddCore G Ω = ⊥) {B : Ω} {i j : D.ι} (hij : i ≠ j)
    {w w' : G} (hw : w ∈ D.W B i) (hw' : w' ∈ D.W B j) : w * w' = w' * w :=
  commute_of_mem_L hO hij ((D.W_le_L B i) hw) ((D.W_le_L B j) hw')

end K4

section K3

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] {D : HoltData G Ω}

omit [Finite G] in
private theorem conj_mem_stabilizer_iff {g h : G} {α : Ω} (hg : g • α = α) :
    g * h * g⁻¹ ∈ stabilizer G α ↔ h ∈ stabilizer G α := by
  have hg' : g⁻¹ • α = α := by rw [inv_smul_eq_iff, hg]
  simp only [mem_stabilizer_iff, mul_smul, hg']
  constructor
  · intro h1
    have h2 := congrArg (g⁻¹ • ·) h1
    simp only [inv_smul_smul, hg'] at h2
    exact h2
  · intro h1
    rw [h1, hg]

theorem fixSet_sylow_twoPoint_jHull (hO : jOddCore G Ω = ⊥) {α β : Ω} {i : D.ι}
    (hαβ : ∀ j, j ≠ i → D.coord β j = D.coord α j) {P : Subgroup G}
    (hP : fusionIsSylowIn 2 P (jHull G Ω ⊓ stabilizer G α ⊓ stabilizer G β)) :
    fixSet Ω P ⊆ orbit (D.L i) α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro γ hγ
  have hLi : jOddCore G Ω ⊔ ({i} : Finset D.ι).sup D.L = D.L i := by
    rw [Finset.sup_singleton, sup_eq_right.mpr (D.oddCore_le i)]
  rw [← hLi]
  refine (D.mem_orbit_sup_finsetSup_iff {i} α γ).mpr fun j hj => ?_
  have hji : j ≠ i := by simpa using hj
  obtain ⟨T, -, hT⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
    (bot_le : ⊥ ≤ D.M j ⊓ stabilizer (Equiv.Perm (D.Ψc j)) (D.coord α j))
  have hTfix := (D.factor j).fixSet_eq_singleton (D.odd_card_Ψc j) hT
  set Y : Subgroup (jHull G Ω) := (D.L j ⊓ stabilizer G α).subgroupOf (jHull G Ω)
  have hTY : T ≤ Y.map (D.ρ j) := by
    intro m hm
    obtain ⟨l, hl, hlm⟩ := mem_M.mp (hT.1 hm).1
    have hmα : m (D.coord α j) = D.coord α j := (hT.1 hm).2
    refine ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hl, ?_⟩, hlm⟩
    refine coord_injective (D := D) hO (funext fun k => ?_)
    rw [D.coord_smul]
    by_cases hkj : k = j
    · subst hkj
      rw [hlm]
      exact hmα
    · rw [rho_eq_one_of_mem_L (Ne.symm hkj) hl, Equiv.Perm.one_apply]
  obtain ⟨E, -, hEY, hE, hET⟩ :=
    exists_isPGroup_map_eq_of_map_le (D.ρ j) hT.2.1 hTY IsPGroup.of_bot bot_le (by simp)
  have hE'le : E.map (jHull G Ω).subtype ≤ jHull G Ω ⊓ stabilizer G α ⊓ stabilizer G β := by
    rintro _ ⟨e, he, rfl⟩
    have he' := Subgroup.mem_subgroupOf.mp (hEY he)
    refine ⟨⟨e.2, he'.2⟩, ?_⟩
    have heα : (e : G) • α = α := he'.2
    show (e : G) • β = β
    refine coord_injective (D := D) hO (funext fun k => ?_)
    rw [D.coord_smul]
    by_cases hkj : k = j
    · subst hkj
      rw [hαβ k hji, ← D.coord_smul, heα]
    · rw [rho_eq_one_of_mem_L (Ne.symm hkj) he'.1, Equiv.Perm.one_apply]
  obtain ⟨R, hER, hR⟩ := exists_fusionIsSylowIn_ge (hE.map _) hE'le
  obtain ⟨k, hk, hkfix⟩ := exists_smul_fixSet_eq_of_fusionIsSylowIn (Ω := Ω) hR hP
  rw [hkfix] at hγ
  obtain ⟨γ', hγ', rfl⟩ := Set.mem_smul_set.mp hγ
  have h1 : D.coord γ' j ∈ fixSet (D.Ψc j) T := by
    intro m hm
    rw [← hET] at hm
    obtain ⟨e, he, rfl⟩ := hm
    have he2 : (e : G) • γ' = γ' := hγ' (e : G) (hER ⟨e, he, rfl⟩)
    rw [Equiv.Perm.smul_def, ← D.coord_smul, he2]
  rw [hTfix, Set.mem_singleton_iff] at h1
  have hkH : k ∈ jHull G Ω := hk.1.1
  have hkα : k • α = α := hk.1.2
  rw [show D.coord (k • γ') j = D.ρ j ⟨k, hkH⟩ (D.coord γ' j) from D.coord_smul ⟨k, hkH⟩ γ' j,
    h1, ← D.coord_smul]
  exact congrFun (congrArg D.coord hkα) j

theorem fixSet_sylow_twoPoint (hO : jOddCore G Ω = ⊥) {α β : Ω} {i : D.ι}
    (hαβ : ∀ j, j ≠ i → D.coord β j = D.coord α j) {P : Subgroup G}
    (hP : fusionIsSylowIn 2 P (stabilizer G α ⊓ stabilizer G β)) :
    fixSet Ω P ⊆ orbit (D.L i) α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : jHull G Ω ⊓ stabilizer G α ⊓ stabilizer G β ≤ stabilizer G α ⊓ stabilizer G β := by
    rw [inf_assoc]
    exact inf_le_right
  have hKN : stabilizer G α ⊓ stabilizer G β ≤
      Subgroup.normalizer ((jHull G Ω ⊓ stabilizer G α ⊓ stabilizer G β : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_inf]
    rw [conj_mem_stabilizer_iff hg.1, conj_mem_stabilizer_iff hg.2]
    exact and_congr_left' (and_congr_left' ⟨fun hh => (jHull_normal).conj_mem h hh g,
      fun hh => by simpa [mul_assoc] using (jHull_normal).conj_mem _ hh g⁻¹⟩)
  exact (fixSet_anti inf_le_left).trans
    (fixSet_sylow_twoPoint_jHull hO hαβ (fusionIsSylowIn_inf_of_le_normalizer' hP hN hKN))

end K3

section T8c

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {D : HoltData G Ω}

private theorem smul_mem_orbit_iff_of_mem_normalizer {N : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) {ω ω' : Ω} :
    g • ω ∈ orbit N (g • ω') ↔ ω ∈ orbit N ω' := by
  have key : ∀ y : G, y ∈ Subgroup.normalizer (N : Set G) → ∀ a b : Ω, a ∈ orbit N b →
      y • a ∈ orbit N (y • b) := by
    rintro y hy a b ⟨⟨n, hn⟩, rfl⟩
    refine ⟨⟨y * n * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy n).mp hn⟩, ?_⟩
    change (y * n * y⁻¹) • y • b = y • n • b
    rw [mul_smul, mul_smul, inv_smul_smul]
  refine ⟨fun h => ?_, key g hg ω ω'⟩
  have h2 := key g⁻¹ (inv_mem hg) _ _ h
  rwa [inv_smul_smul, inv_smul_smul] at h2

private theorem smul_mem_orbit_jOddCore_iff {k : D.ι} {l : jHull G Ω} (hl : (l : G) ∈ D.L k)
    (ω : Ω) : (l : G) • ω ∈ orbit (jOddCore G Ω) ω ↔ D.ρ k l (D.coord ω k) = D.coord ω k := by
  rw [← D.coord_eq_iff, ← D.coord_smul]
  constructor
  · intro h
    exact (congrFun h k).symm
  · intro h
    funext j
    by_cases hjk : j = k
    · subst hjk
      exact h.symm
    · rw [D.coord_smul, rho_eq_one_of_mem_L (Ne.symm hjk) hl, Equiv.Perm.one_apply]

theorem normalizer_L_preserves_fibres {k : D.ι} {g : G}
    (hg : g ∈ Subgroup.normalizer (D.L k : Set G)) (ω ω' : Ω) :
    (D.coord (g • ω) k = D.coord (g • ω') k ↔ D.coord ω k = D.coord ω' k) ∧
      ((∀ i, i ≠ k → D.coord (g • ω) i = D.coord (g • ω') i) ↔
        ∀ i, i ≠ k → D.coord ω i = D.coord ω' i) := by
  constructor
  ·
    have hchar : ∀ a b : Ω, D.coord a k = D.coord b k ↔ ∀ l : jHull G Ω, (l : G) ∈ D.L k →
        ((l : G) • a ∈ orbit (jOddCore G Ω) a ↔ (l : G) • b ∈ orbit (jOddCore G Ω) b) := by
      intro a b
      refine ⟨fun h l hl => by rw [smul_mem_orbit_jOddCore_iff hl, smul_mem_orbit_jOddCore_iff hl,
        h], fun h => ?_⟩
      refine ((D.factor k).eq_of_forall_apply_eq fun m hm hma => ?_).symm
      obtain ⟨l, hl, rfl⟩ := mem_M.mp hm
      exact (smul_mem_orbit_jOddCore_iff hl b).mp ((h l hl).mp
        ((smul_mem_orbit_jOddCore_iff hl a).mpr hma))
    have htr : ∀ (l : jHull G Ω) (a : Ω), (l : G) • g • a ∈ orbit (jOddCore G Ω) (g • a) ↔
        (g⁻¹ * l * g) • a ∈ orbit (jOddCore G Ω) a := by
      intro l a
      rw [← smul_orbit_eq_orbit_smul, Set.mem_smul_set_iff_inv_smul_mem, ← mul_smul, ← mul_smul]
    rw [hchar, hchar]
    constructor
    · intro h l hl
      have hgl : g * l * g⁻¹ ∈ D.L k := (Subgroup.mem_normalizer_iff.mp hg l).mp hl
      set l' : jHull G Ω := ⟨g * l * g⁻¹, D.L_le k hgl⟩
      have h1 := h l' hgl
      rw [htr, htr] at h1
      simpa [l', mul_assoc] using h1
    · intro h l hl
      have hgl : g⁻¹ * l * g ∈ D.L k := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) l).mp hl
        rwa [inv_inv] at this
      rw [htr, htr]
      exact h ⟨g⁻¹ * l * g, D.L_le k hgl⟩ hgl
  ·
    have hLk : jOddCore G Ω ⊔ ({k} : Finset D.ι).sup D.L = D.L k := by
      rw [Finset.sup_singleton, sup_eq_right.mpr (D.oddCore_le k)]
    have hchar : ∀ a b : Ω, (∀ i, i ≠ k → D.coord a i = D.coord b i) ↔ a ∈ orbit (D.L k) b := by
      intro a b
      rw [← hLk, D.mem_orbit_sup_finsetSup_iff]
      simp only [Finset.mem_singleton]
    rw [hchar, hchar]
    exact smul_mem_orbit_iff_of_mem_normalizer hg

end T8c

end HoltData

end CFSG.Holt.H78
