module

public import CFSG.Holt.H78.Start
import CFSG.Holt.H78.Conjugacy
import CFSG.Holt.H78.DataPrimitive
import CFSG.Holt.H78.AltModelAut
import CFSG.Holt.General.CaseIPrimitiveBasic

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section Factor

variable {Δ : Type} [Fintype Δ] [DecidableEq Δ] {Mf : Subgroup (Equiv.Perm Δ)}

omit [Fintype Δ] [DecidableEq Δ] in
theorem inf_stabilizer_subgroupOf (δ : Δ) :
    (Mf ⊓ stabilizer (Equiv.Perm Δ) δ).subgroupOf Mf = stabilizer Mf δ := by
  ext m
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, SetLike.coe_mem, true_and,
    mem_stabilizer_iff, Subgroup.smul_def]

theorem IsHoltFactor.relIndex_inf_stabilizer (hM : IsHoltFactor Mf) (δ : Δ) :
    (Mf ⊓ stabilizer (Equiv.Perm Δ) δ).relIndex Mf = Fintype.card Δ := by
  rcases hM with ⟨rfl, h7⟩ | hSE
  · exact relIndex_alternatingGroup_inf_stabilizer (by omega) δ
  · obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hSE
    have := hA.isPretransitive
    change ((Mf ⊓ stabilizer (Equiv.Perm Δ) δ).subgroupOf Mf).index = _
    rw [inf_stabilizer_subgroupOf, index_stabilizer, orbit_eq_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card]

theorem IsHoltFactor.exists_eq_inf_stabilizer (hM : IsHoltFactor Mf)
    {Y : Subgroup (Equiv.Perm Δ)} (hYM : Y ≤ Mf) (hidx : Y.relIndex Mf = Fintype.card Δ) :
    ∃ δ : Δ, Y = Mf ⊓ stabilizer (Equiv.Perm Δ) δ := by
  rcases hM with ⟨rfl, h7⟩ | hSE
  · exact exists_eq_alternatingGroup_inf_stabilizer_of_relIndex_eq (by omega) (by omega) hYM hidx
  · obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hSE
    have hcard := hA.card_eq
    obtain ⟨δ, hδ⟩ := hA.exists_eq_stabilizer (Y := Y.subgroupOf Mf) (by
      change Y.relIndex Mf = _
      rw [hidx, ← Nat.card_eq_fintype_card, hcard])
    refine ⟨δ, ?_⟩
    rw [← inf_stabilizer_subgroupOf] at hδ
    have := congrArg (Subgroup.map Mf.subtype) hδ
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hYM, inf_eq_left.mpr inf_le_left] at this

end Factor

section StabClass

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

theorem mem_toConjAct_smul_iff {g x : G} {S : Subgroup G} :
    x ∈ ConjAct.toConjAct g • S ↔ g⁻¹ * x * g ∈ S := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv]

theorem toConjAct_smul_inf_stabilizer {M : Subgroup G} [hM : M.Normal] (g : G) (ω : Ω) :
    ConjAct.toConjAct g • (M ⊓ stabilizer G ω) = M ⊓ stabilizer G (g • ω) := by
  ext x
  rw [mem_toConjAct_smul_iff, Subgroup.mem_inf, Subgroup.mem_inf, mem_stabilizer_iff,
    mem_stabilizer_iff, mul_smul, mul_smul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa [mul_assoc] using hM.conj_mem _ h1 g, ?_⟩
    calc x • g • ω = g • g⁻¹ • x • g • ω := by rw [smul_inv_smul]
      _ = g • ω := by rw [h2]
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa [mul_assoc] using hM.conj_mem _ h1 g⁻¹, by rw [h2, inv_smul_smul]⟩

variable (M : Subgroup G) (α : Ω)

abbrev StabClass : Type := orbit (ConjAct G) (M ⊓ stabilizer G α)

variable {M} [M.Normal] [IsPretransitive G Ω]

theorem inf_stabilizer_mem_orbit (ω : Ω) :
    M ⊓ stabilizer G ω ∈ orbit (ConjAct G) (M ⊓ stabilizer G α) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
  exact ⟨ConjAct.toConjAct g, toConjAct_smul_inf_stabilizer g α⟩

variable (M) in
@[expose] def stabClassOf (ω : Ω) : StabClass M α :=
  ⟨M ⊓ stabilizer G ω, inf_stabilizer_mem_orbit α ω⟩

@[simp] theorem coe_stabClassOf (ω : Ω) :
    (stabClassOf M α ω : Subgroup G) = M ⊓ stabilizer G ω := rfl

theorem stabClassOf_smul (g : G) (ω : Ω) :
    stabClassOf M α (g • ω) = ConjAct.toConjAct g • stabClassOf M α ω :=
  Subtype.ext (toConjAct_smul_inf_stabilizer g ω).symm

variable (M) in
@[expose] noncomputable def stabClassHom : G →* Equiv.Perm (StabClass M α) :=
  (toPermHom (ConjAct G) (StabClass M α)).comp ConjAct.toConjAct.toMonoidHom

omit [M.Normal] [IsPretransitive G Ω] in
@[simp] theorem stabClassHom_apply (g : G) (l : StabClass M α) :
    stabClassHom M α g l = ConjAct.toConjAct g • l := rfl

end StabClass

section BlockModel

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α : Ω} {K : Subgroup G}
  {Δ : Type} [Fintype Δ] [DecidableEq Δ] {M : Subgroup G} {Mf : Subgroup (Equiv.Perm Δ)}

variable (e : (K ⧸ (stabilizer G α).subgroupOf K) ≃ Δ)

@[expose] noncomputable def blockModelHom : K →* Equiv.Perm Δ :=
  e.permCongrHom.toMonoidHom.comp (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K))

@[expose] noncomputable def blockModelHomOn (hMK : M ≤ K) : M →* Equiv.Perm Δ :=
  (blockModelHom e).comp (Subgroup.inclusion hMK)

omit [Fintype Δ] [DecidableEq Δ] in
@[simp] theorem blockModelHom_apply (k : K) (c : K ⧸ (stabilizer G α).subgroupOf K) :
    blockModelHom e k (e c) = e (k • c) := by
  simp [blockModelHom, Equiv.permCongrHom, Equiv.permCongr_apply]

omit [Fintype Δ] [DecidableEq Δ] in
@[simp] theorem blockModelHomOn_apply (hMK : M ≤ K) (x : M)
    (c : K ⧸ (stabilizer G α).subgroupOf K) :
    blockModelHomOn e hMK x (e c) = e ((Subgroup.inclusion hMK x) • c) :=
  blockModelHom_apply e _ c

variable {e}

omit [Fintype Δ] [DecidableEq Δ] in
theorem smul_eq_iff_smul_blockPoint_eq (k : K) (c : K ⧸ (stabilizer G α).subgroupOf K) :
    k • c = c ↔ (k : G) • blockPoint α K c = blockPoint α K c := by
  rw [← blockPoint_smul, blockPoint_injective.eq_iff]

omit [Fintype Δ] [DecidableEq Δ] in
theorem map_inf_stabilizer_blockPoint (hMK : M ≤ K) (hrange : (blockModelHomOn e hMK).range = Mf)
    (c : K ⧸ (stabilizer G α).subgroupOf K) :
    ((M ⊓ stabilizer G (blockPoint α K c)).subgroupOf M).map (blockModelHomOn e hMK) =
      Mf ⊓ stabilizer (Equiv.Perm Δ) (e c) := by
  ext m
  rw [Subgroup.mem_map, Subgroup.mem_inf, mem_stabilizer_iff, ← hrange]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    have hx2 : ((Subgroup.inclusion hMK x : K) : G) • blockPoint α K c = blockPoint α K c :=
      hx.2
    rw [Equiv.Perm.smul_def, blockModelHomOn_apply,
      (smul_eq_iff_smul_blockPoint_eq _ c).mpr hx2]
  · rintro ⟨⟨x, rfl⟩, hx⟩
    rw [Equiv.Perm.smul_def, blockModelHomOn_apply, e.injective.eq_iff,
      smul_eq_iff_smul_blockPoint_eq] at hx
    exact ⟨x, ⟨x.2, hx⟩, rfl⟩

theorem eq_of_inf_stabilizer_le (hMK : M ≤ K) (hrange : (blockModelHomOn e hMK).range = Mf)
    (hMf : IsHoltFactor Mf) {c c' : K ⧸ (stabilizer G α).subgroupOf K}
    (h : M ⊓ stabilizer G (blockPoint α K c) ≤ stabilizer G (blockPoint α K c')) : c = c' := by
  apply e.injective
  refine (hMf.eq_of_forall_apply_eq (a := e c) (b := e c') fun m hm hma => ?_).symm
  rw [← hrange] at hm
  obtain ⟨x, rfl⟩ := hm
  rw [blockModelHomOn_apply, e.injective.eq_iff, smul_eq_iff_smul_blockPoint_eq] at hma ⊢
  exact h ⟨x.2, hma⟩

omit [Fintype Δ] [DecidableEq Δ] in
theorem map_conj_eq_toConjAct_smul (g : G) (S : Subgroup G) :
    S.map (MulAut.conj g).toMonoidHom = ConjAct.toConjAct g • S := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_toConjAct_smul_iff, MulAut.conj_symm_apply]

theorem exists_inf_stabilizer_eq [Finite G] [IsPretransitive G Ω] [hMn : M.Normal]
    (hMK : M ≤ K) (hinj : Function.Injective (blockModelHomOn e hMK))
    (hrange : (blockModelHomOn e hMK).range = Mf) (hMf : IsHoltFactor Mf) (γ : Ω) :
    ∃ c, M ⊓ stabilizer G γ = M ⊓ stabilizer G (blockPoint α K c) := by
  have hmapθ : ∀ S : Subgroup G, S ≤ M → (S.relIndex M =
      ((S.subgroupOf M).map (blockModelHomOn e hMK)).relIndex Mf) := fun S _ => by
    rw [← Subgroup.relIndex_subgroupOf (le_refl M), Subgroup.subgroupOf_self,
      ← Subgroup.relIndex_map_map_of_injective _ _ hinj, ← MonoidHom.range_eq_map, hrange]
  have hrel : ∀ c, (M ⊓ stabilizer G (blockPoint α K c)).relIndex M = Fintype.card Δ := by
    intro c
    rw [hmapθ _ inf_le_left, map_inf_stabilizer_blockPoint hMK hrange c]
    exact hMf.relIndex_inf_stabilizer (e c)
  obtain ⟨g, rfl⟩ := exists_smul_eq G (blockPoint α K ((1 : K) : K ⧸ _)) γ
  have hconj : M ⊓ stabilizer G (g • blockPoint α K ((1 : K) : K ⧸ _)) =
      (M ⊓ stabilizer G (blockPoint α K ((1 : K) : K ⧸ _))).map
        (MulAut.conj g).toMonoidHom := by
    rw [map_conj_eq_toConjAct_smul, toConjAct_smul_inf_stabilizer]
  have hMg : M.map (MulAut.conj g).toMonoidHom = M := by
    rw [map_conj_eq_toConjAct_smul]
    exact hMn.conjAct (ConjAct.toConjAct g)
  have hγ : (M ⊓ stabilizer G (g • blockPoint α K ((1 : K) : K ⧸ _))).relIndex M =
      Fintype.card Δ := by
    rw [hconj]
    calc ((M ⊓ stabilizer G (blockPoint α K ((1 : K) : K ⧸ _))).map
          (MulAut.conj g).toMonoidHom).relIndex M =
        ((M ⊓ stabilizer G (blockPoint α K ((1 : K) : K ⧸ _))).map
          (MulAut.conj g).toMonoidHom).relIndex (M.map (MulAut.conj g).toMonoidHom) := by
          rw [hMg]
      _ = Fintype.card Δ := by
          rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hrel]
  rw [hmapθ _ inf_le_left] at hγ
  obtain ⟨δ, hδ⟩ := hMf.exists_eq_inf_stabilizer
    (by rw [← hrange]; exact Subgroup.map_le_range _ _) hγ
  refine ⟨e.symm δ, ?_⟩
  rw [← e.apply_symm_apply δ, ← map_inf_stabilizer_blockPoint hMK hrange] at hδ
  have h := Subgroup.map_injective hinj hδ
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr inf_le_left, inf_eq_left.mpr inf_le_left] at h
  exact h

end BlockModel

section StabClassModel

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [IsPretransitive G Ω]
  {α : Ω} {K : Subgroup G} {Δ : Type} [Fintype Δ] [DecidableEq Δ] {M : Subgroup G} [M.Normal]
  {Mf : Subgroup (Equiv.Perm Δ)} {e : (K ⧸ (stabilizer G α).subgroupOf K) ≃ Δ}
  (hMK : M ≤ K) (hinj : Function.Injective (blockModelHomOn e hMK))
  (hrange : (blockModelHomOn e hMK).range = Mf) (hMf : IsHoltFactor Mf)

include hinj hrange hMf

theorem stabClassOf_blockPoint_bijective :
    Function.Bijective fun c : K ⧸ (stabilizer G α).subgroupOf K =>
      stabClassOf M α (blockPoint α K c) := by
  refine ⟨fun c c' h => ?_, fun l => ?_⟩
  · have h' := congrArg Subtype.val h
    simp only [coe_stabClassOf] at h'
    exact eq_of_inf_stabilizer_le hMK hrange hMf (h'.le.trans inf_le_right)
  · obtain ⟨S, g, hg⟩ := l
    obtain ⟨c, hc⟩ := exists_inf_stabilizer_eq hMK hinj hrange hMf (ConjAct.ofConjAct g • α)
    refine ⟨c, Subtype.ext ?_⟩
    change M ⊓ stabilizer G (blockPoint α K c) = S
    change g • (M ⊓ stabilizer G α) = S at hg
    rw [← hc, ← hg, ← toConjAct_smul_inf_stabilizer, ConjAct.toConjAct_ofConjAct]

@[expose] noncomputable def blockStabClassEquiv :
    (K ⧸ (stabilizer G α).subgroupOf K) ≃ StabClass M α :=
  Equiv.ofBijective _ (stabClassOf_blockPoint_bijective hMK hinj hrange hMf)

theorem blockStabClassEquiv_apply (c : K ⧸ (stabilizer G α).subgroupOf K) :
    blockStabClassEquiv hMK hinj hrange hMf c = stabClassOf M α (blockPoint α K c) := rfl

theorem blockStabClassEquiv_smul (k : K) (c : K ⧸ (stabilizer G α).subgroupOf K) :
    blockStabClassEquiv hMK hinj hrange hMf (k • c) =
      stabClassHom M α k (blockStabClassEquiv hMK hinj hrange hMf c) := by
  rw [blockStabClassEquiv_apply, blockStabClassEquiv_apply, blockPoint_smul, stabClassOf_smul,
    stabClassHom_apply]

theorem eq_one_of_forall_stabClassHom_eq {x : G} (hx : x ∈ M)
    (h : ∀ l, stabClassHom M α x l = l) : x = 1 := by
  have hfix : ∀ c, (⟨x, hMK hx⟩ : K) • c = c := fun c =>
    (stabClassOf_blockPoint_bijective hMK hinj hrange hMf).1 (by
      have := blockStabClassEquiv_smul hMK hinj hrange hMf ⟨x, hMK hx⟩ c
      rw [h] at this
      exact this)
  have h1 : blockModelHomOn e hMK ⟨x, hx⟩ = 1 := by
    ext d
    obtain ⟨c, rfl⟩ := e.surjective d
    rw [blockModelHomOn_apply]
    exact congrArg e (hfix c)
  exact congrArg Subtype.val (hinj (h1.trans (map_one _).symm))

@[expose] noncomputable def stabClassEquiv : StabClass M α ≃ Δ :=
  (blockStabClassEquiv hMK hinj hrange hMf).symm.trans e

theorem stabClassEquiv_permCongr (x : M) :
    (stabClassEquiv hMK hinj hrange hMf).permCongr (stabClassHom M α x) =
      blockModelHomOn e hMK x := by
  ext d
  obtain ⟨c, rfl⟩ := e.surjective d
  rw [Equiv.permCongr_apply, blockModelHomOn_apply, stabClassEquiv, Equiv.symm_trans_apply,
    Equiv.symm_symm, e.symm_apply_apply]
  change ((blockStabClassEquiv hMK hinj hrange hMf).symm.trans e)
    (stabClassHom M α ((Subgroup.inclusion hMK x : K) : G)
      (blockStabClassEquiv hMK hinj hrange hMf c)) = _
  rw [← blockStabClassEquiv_smul hMK hinj hrange hMf (Subgroup.inclusion hMK x),
    Equiv.trans_apply, Equiv.symm_apply_apply]

theorem map_stabClassHom_permCongr :
    (M.map (stabClassHom M α)).map
        (stabClassEquiv hMK hinj hrange hMf).permCongrHom.toMonoidHom = Mf := by
  ext m
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hm : _ ∈ (blockModelHomOn e hMK).range :=
      ⟨⟨x, hx⟩, (stabClassEquiv_permCongr hMK hinj hrange hMf ⟨x, hx⟩).symm⟩
    rwa [hrange] at hm
  · intro hm
    have hm' : m ∈ (blockModelHomOn e hMK).range := by rwa [hrange]
    obtain ⟨x, rfl⟩ := hm'
    exact ⟨_, ⟨x, x.2, rfl⟩, stabClassEquiv_permCongr hMK hinj hrange hMf x⟩

theorem eq_of_blockCoset_eq_of_stabClassOf_eq (hαK : stabilizer G α ≤ K) {ω ω' : Ω}
    (hb : blockCoset α K ω = blockCoset α K ω')
    (hs : stabClassOf M α ω = stabClassOf M α ω') : ω = ω' := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
  have h1 : ω' ∈ g • orbit K α := by
    rw [← blockCoset_preimage_mk hαK, Set.mem_preimage, Set.mem_singleton_iff, ← hb,
      blockCoset_smul_self hαK]
  obtain ⟨β, hβ, rfl⟩ := Set.mem_smul_set.mp h1
  obtain ⟨c, rfl⟩ := exists_blockPoint_eq hβ
  rw [stabClassOf_smul, stabClassOf_smul] at hs
  have hs' := smul_left_cancel _ hs
  have hα : blockPoint α K ((1 : K) : K ⧸ (stabilizer G α).subgroupOf K) = α := by
    rw [blockPoint_mk, Subgroup.coe_one, one_smul]
  have := (stabClassOf_blockPoint_bijective hMK hinj hrange hMf).1
    (show stabClassOf M α (blockPoint α K ((1 : K) : K ⧸ _)) =
      stabClassOf M α (blockPoint α K c) by rw [hα]; exact hs')
  rw [← this, hα]

theorem exists_blockCoset_eq_stabClassOf_eq (hαK : stabilizer G α ≤ K) (ψ : G ⧸ K)
    (l : StabClass M α) : ∃ ω, blockCoset α K ω = ψ ∧ stabClassOf M α ω = l := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ψ
  obtain ⟨c, hc⟩ := (stabClassOf_blockPoint_bijective hMK hinj hrange hMf).2
    (ConjAct.toConjAct g⁻¹ • l)
  refine ⟨g • blockPoint α K c, ?_, ?_⟩
  · rw [blockCoset_smul hαK, (blockCoset_eq_one_iff hαK).mpr (blockPoint_mem_orbit c),
      MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  · rw [stabClassOf_smul]
    simp only at hc
    rw [hc, map_inv, smul_inv_smul]

theorem stabClassHom_mem_longInv (hαK : stabilizer G α ≤ K)
    [hnt : Nontrivial (K ⧸ (stabilizer G α).subgroupOf K)] {u : G} (hu : u ∈ longInv G Ω) :
    stabClassHom M α u ∈ longInv (Equiv.Perm (StabClass M α)) (StabClass M α) := by
  obtain ⟨β, hβ, -⟩ := hu.2
  obtain ⟨g, rfl⟩ := exists_smul_eq G α β
  have hu' : g⁻¹ * u * g ∈ longInvAt G Ω α := by
    have := conj_mem_longInvAt ⟨hu, hβ⟩ g⁻¹
    rwa [inv_inv, inv_smul_smul] at this
  have hK' : g⁻¹ * u * g ∈ K := hαK hu'.2
  have hconj : stabClassHom M α u = stabClassHom M α g * stabClassHom M α (g⁻¹ * u * g) *
      (stabClassHom M α g)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [hconj]
  apply conj_mem_longInv
  have hα : blockPoint α K ((1 : K) : K ⧸ (stabilizer G α).subgroupOf K) = α := by
    rw [blockPoint_mk, Subgroup.coe_one, one_smul]
  have hfix : ∀ l, stabClassHom M α (g⁻¹ * u * g) l = l ↔
      l = blockStabClassEquiv hMK hinj hrange hMf ((1 : K) : K ⧸ _) := by
    intro l
    obtain ⟨c, rfl⟩ := (blockStabClassEquiv hMK hinj hrange hMf).surjective l
    rw [(blockStabClassEquiv hMK hinj hrange hMf).injective.eq_iff,
      show (g⁻¹ * u * g : G) = ((⟨g⁻¹ * u * g, hK'⟩ : K) : G) from rfl,
      ← blockStabClassEquiv_smul, (blockStabClassEquiv hMK hinj hrange hMf).injective.eq_iff,
      smul_eq_iff_smul_blockPoint_eq, smul_eq_iff_of_mem_longInvAt hu']
    exact ⟨fun h => blockPoint_injective (h.trans hα.symm), fun h => h ▸ hα⟩
  refine ⟨?_, _, (hfix _).mpr rfl, fun l hl => (hfix l).mp hl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← map_pow, ← hu'.1.1, pow_orderOf_eq_one, map_one]
  · intro h1
    obtain ⟨c, hc⟩ := exists_ne ((1 : K) : K ⧸ (stabilizer G α).subgroupOf K)
    have := (hfix (blockStabClassEquiv hMK hinj hrange hMf c)).mp (by rw [h1]; rfl)
    exact hc ((blockStabClassEquiv hMK hinj hrange hMf).injective this)

end StabClassModel

section BlockLongInv

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] [IsPretransitive G Ω] {α : Ω}
  {K : Subgroup G} {Δ : Type} {e : (K ⧸ (stabilizer G α).subgroupOf K) ≃ Δ}

theorem blockModelHom_mem_longInv (hΩ : Odd (Nat.card Ω)) (hαK : stabilizer G α ≤ K)
    [Nontrivial (K ⧸ (stabilizer G α).subgroupOf K)] {v : G} (hv : v ∈ longInv G Ω)
    (hvK : v ∈ K) : blockModelHom e ⟨v, hvK⟩ ∈ longInv (Equiv.Perm Δ) Δ := by
  obtain ⟨β, hβ, -⟩ := hv.2
  have hβB : β ∈ orbit K α := by
    have h1 := (smul_eq_iff_of_mem_longInvAt_quotient hΩ hαK ⟨hv, hβ⟩ ((1 : G) : G ⧸ K)).mp
      (by rw [← mem_stabilizer_iff, MulAction.stabilizer_quotient]; exact hvK)
    exact (blockCoset_eq_one_iff hαK).mp h1.symm
  obtain ⟨c₀, rfl⟩ := exists_blockPoint_eq hβB
  have hfix : ∀ d, blockModelHom e ⟨v, hvK⟩ d = d ↔ d = e c₀ := by
    intro d
    obtain ⟨c, rfl⟩ := e.surjective d
    rw [blockModelHom_apply, e.injective.eq_iff, e.injective.eq_iff,
      smul_eq_iff_smul_blockPoint_eq, smul_eq_iff_of_mem_longInvAt ⟨hv, hβ⟩]
    exact ⟨fun h => blockPoint_injective h, fun h => h ▸ rfl⟩
  refine ⟨?_, e c₀, (hfix _).mpr rfl, fun d hd => (hfix d).mp hd⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · have hv2 : (⟨v, hvK⟩ : K) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hv.1, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [← map_pow, hv2, map_one]
  · intro h1
    obtain ⟨c, hc⟩ := exists_ne c₀
    have := (hfix (e c)).mp (by rw [h1]; rfl)
    exact hc (e.injective this)

end BlockLongInv

section StabClassLe

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α : Ω} {M : Subgroup G} [M.Normal]

theorem coe_le_of_stabClass (l : StabClass M α) : (l : Subgroup G) ≤ M := by
  obtain ⟨S, g, hg⟩ := l
  change g • (M ⊓ stabilizer G α) = S at hg
  subst hg
  intro x hx
  rw [← ConjAct.toConjAct_ofConjAct g, mem_toConjAct_smul_iff] at hx
  have := (inferInstance : M.Normal).conj_mem _ hx.1 (ConjAct.ofConjAct g)
  simpa [mul_assoc] using this

theorem stabClassHom_eq_one_of_mem_centralizer {c : G}
    (hc : c ∈ Subgroup.centralizer (M : Set G)) : stabClassHom M α c = 1 := by
  ext l : 2
  change ConjAct.toConjAct c • (l : Subgroup G) = (l : Subgroup G)
  have hlM := coe_le_of_stabClass l
  ext x
  rw [mem_toConjAct_smul_iff]
  constructor
  · intro hx
    have hcx := Subgroup.mem_centralizer_iff.mp hc _ (hlM hx)
    have : x = c⁻¹ * x * c :=
      calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
        _ = c⁻¹ * x * c * c * c⁻¹ := by rw [hcx]
        _ = c⁻¹ * x * c := by group
    rw [this]
    exact hx
  · intro hx
    have hcx := Subgroup.mem_centralizer_iff.mp hc _ (hlM hx)
    have : c⁻¹ * x * c = x :=
      calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
        _ = c⁻¹ * (c * x) := by rw [hcx]
        _ = x := by group
    rw [this]
    exact hx

end StabClassLe

section Assembly

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem holtStructure_of_factor (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (hH : jHull G Ω = ⊤)
    (hO : CFSG.pPrimeCore 2 G = ⊥) {α : Ω} {K : Subgroup G} (hαK : stabilizer G α < K)
    (hK : K ≠ ⊤) {M : Subgroup G} [hMn : M.Normal] (hMN : M ≤ K.normalCore)
    {Δ : Type} [Fintype Δ] [DecidableEq Δ] {Mf : Subgroup (Equiv.Perm Δ)}
    {e : (K ⧸ (stabilizer G α).subgroupOf K) ≃ Δ}
    (hrange : (blockModelHomOn e (hMN.trans K.normalCore_le)).range = Mf)
    (hMf : IsHoltFactor Mf)
    (hinner : ¬ IsOuterFactor Mf → ∀ u ∈ longInv G Ω, ∀ hu : u ∈ K,
      blockModelHom e ⟨u, hu⟩ ∈ Mf) :
    HoltStructure G Ω := by
  classical
  have := hG.isPretransitive
  have hMK : M ≤ K := hMN.trans K.normalCore_le
  have hnt : Nontrivial (K ⧸ (stabilizer G α).subgroupOf K) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := three_le_relIndex hG hαK
    change 1 < (stabilizer G α).relIndex K
    omega
  have hκ := blockKernelHom_injective hG hαK.le hO
  have hΘ1 : ∀ k : K, blockModelHom e k = 1 ↔
      ∀ c : K ⧸ (stabilizer G α).subgroupOf K, k • c = c := by
    intro k
    constructor
    · intro h c
      apply e.injective
      rw [← blockModelHom_apply, h, Equiv.Perm.one_apply]
    · intro h
      ext d
      obtain ⟨c, rfl⟩ := e.surjective d
      rw [blockModelHom_apply, h, Equiv.Perm.one_apply]
  have hNfaith : ∀ n (hn : n ∈ K.normalCore),
      (∀ c : K ⧸ (stabilizer G α).subgroupOf K, (⟨n, K.normalCore_le hn⟩ : K) • c = c) →
        n = 1 := by
    intro n hn h
    have h1 : blockKernelHom G α K ⟨n, hn⟩ = 1 :=
      Subtype.ext (Equiv.ext fun c => (blockKernelHom_smul _ c).trans (h c))
    exact congrArg Subtype.val (hκ (h1.trans (map_one _).symm))
  have hinj : Function.Injective (blockModelHomOn e hMK) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hNfaith x (hMN x.2) ((hΘ1 (Subgroup.inclusion hMK x)).mp hx))
  have hcentK : ∀ k : K, (∀ c : K ⧸ (stabilizer G α).subgroupOf K, k • c = c) →
      (k : G) ∈ Subgroup.centralizer (M : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hmem : (k : G) * x * (k : G)⁻¹ * x⁻¹ ∈ K.normalCore :=
      K.normalCore.mul_mem (K.normalCore_normal.conj_mem x (hMN hx) k)
        (K.normalCore.inv_mem (hMN hx))
    have hk' : ∀ c : K ⧸ (stabilizer G α).subgroupOf K, k⁻¹ • c = c := fun c => by
      rw [inv_smul_eq_iff, hk]
    have h1 := hNfaith _ hmem fun c => by
      change (k * ⟨x, hMK hx⟩ * k⁻¹ * (⟨x, hMK hx⟩ : K)⁻¹) • c = c
      rw [mul_smul, mul_smul, mul_smul, hk, hk', smul_inv_smul]
    have h2 : (k : G) * x = x * k := by
      have h1' : (k : G) * x * (k : G)⁻¹ = x := by
        rw [← mul_inv_eq_one]
        exact h1
      calc (k : G) * x = (k : G) * x * (k : G)⁻¹ * k := by group
        _ = x * k := by rw [h1']
    exact h2.symm
  have hCN : ∀ n ∈ K.normalCore, n ∈ Subgroup.centralizer (M : Set G) → n = 1 := by
    intro n hn hc
    refine hNfaith n hn ((hΘ1 _).mp ?_)
    have hcent : blockModelHom e ⟨n, K.normalCore_le hn⟩ ∈
        Subgroup.centralizer (Mf : Set (Equiv.Perm Δ)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [← hrange] at hm
      obtain ⟨x, rfl⟩ := hm
      change blockModelHom e (Subgroup.inclusion hMK x) * blockModelHom e ⟨n, _⟩ =
        blockModelHom e ⟨n, _⟩ * blockModelHom e (Subgroup.inclusion hMK x)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc x x.2)
    rwa [hMf.centralizer_eq_bot] at hcent
  let : Fintype (StabClass M α) := Fintype.ofFinite _
  have hfacΛ := map_stabClassHom_permCongr hMK hinj hrange hMf
  have hHFΛ : IsHoltFactor (M.map (stabClassHom M α)) := by
    rw [← isHoltFactor_map_permCongrHom_iff (stabClassEquiv hMK hinj hrange hMf)]
    convert hMf
    exact hfacΛ
  have hOFΛ : IsOuterFactor (M.map (stabClassHom M α)) ↔ IsOuterFactor Mf := by
    rw [← isOuterFactor_map_permCongrHom_iff (stabClassEquiv hMK hinj hrange hMf)]
    convert Iff.rfl
    exact hfacΛ.symm
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  have htK : t ∈ K := hαK.le ht.2
  have hCn : (Subgroup.centralizer (M : Set G)).Normal := Subgroup.normal_centralizer
  have hconjK : ∀ u ∈ longInv G Ω, ∃ g : G, g⁻¹ * u * g ∈ longInv G Ω ∧ g⁻¹ * u * g ∈ K := by
    intro u hu
    obtain ⟨β, hβ, -⟩ := hu.2
    obtain ⟨g, rfl⟩ := exists_smul_eq G α β
    have hv := conj_mem_longInvAt ⟨hu, hβ⟩ g⁻¹
    rw [inv_inv, inv_smul_smul] at hv
    exact ⟨g, hv.1, hαK.le hv.2⟩
  have hJin : ¬ IsOuterFactor Mf → ∀ u ∈ longInv G Ω,
      u ∈ M ⊔ Subgroup.centralizer (M : Set G) := by
    intro hno u hu
    obtain ⟨g, hv, hvK⟩ := hconjK u hu
    have hΘv := hinner hno _ hv hvK
    rw [← hrange] at hΘv
    obtain ⟨x, hx⟩ := hΘv
    have h1 : blockModelHom e ((Subgroup.inclusion hMK x)⁻¹ * ⟨_, hvK⟩) = 1 := by
      rw [map_mul, map_inv]
      change (blockModelHomOn e hMK x)⁻¹ * _ = 1
      rw [hx, inv_mul_cancel]
    have hc := hcentK _ ((hΘ1 _).mp h1)
    have hv' : g⁻¹ * u * g ∈ M ⊔ Subgroup.centralizer (M : Set G) := by
      have : g⁻¹ * u * g = (x : G) * ((x : G)⁻¹ * (g⁻¹ * u * g)) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right hc)
    have := (Subgroup.sup_normal M (Subgroup.centralizer (M : Set G))).conj_mem _ hv' g
    simpa [mul_assoc] using this
  have hJout : IsOuterFactor Mf → ∀ u ∈ longInv G Ω,
      u * t ∈ M ⊔ Subgroup.centralizer (M : Set G) := by
    intro hout u hu
    obtain ⟨hMalt, hmod⟩ := hOFΛ.mpr hout
    have hu' := stabClassHom_mem_longInv (M := M) hMK hinj hrange hMf hαK.le hu
    have ht' := stabClassHom_mem_longInv (M := M) hMK hinj hrange hMf hαK.le ht.1
    have h1 := (notMem_alternatingGroup_iff_of_mem_longInv_perm hu').mpr hmod
    have h2 := (notMem_alternatingGroup_iff_of_mem_longInv_perm ht').mpr hmod
    have h3 : stabClassHom M α (u * t) ∈ alternatingGroup (StabClass M α) := by
      rw [Equiv.Perm.mem_alternatingGroup] at h1 h2 ⊢
      rw [map_mul, Equiv.Perm.sign_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (stabClassHom M α u)) with h | h
      · exact absurd h h1
      rcases Int.units_eq_one_or (Equiv.Perm.sign (stabClassHom M α t)) with h' | h'
      · exact absurd h' h2
      rw [h, h']
      rfl
    rw [← hMalt] at h3
    obtain ⟨x, hx, hxut⟩ := h3
    have hg1 : stabClassHom M α (x⁻¹ * (u * t)) = 1 := by
      rw [map_mul, map_inv, hxut, inv_mul_cancel]
    have hc : x⁻¹ * (u * t) ∈ Subgroup.centralizer (M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hm : (x⁻¹ * (u * t)) * y * (x⁻¹ * (u * t))⁻¹ * y⁻¹ ∈ M :=
        M.mul_mem (hMn.conj_mem y hy _) (M.inv_mem hy)
      have h4 := eq_one_of_forall_stabClassHom_eq hMK hinj hrange hMf hm fun l => by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg1, inv_one, mul_one, one_mul,
          mul_inv_cancel, Equiv.Perm.one_apply]
      have h5 : (x⁻¹ * (u * t)) * y * (x⁻¹ * (u * t))⁻¹ = y := by
        rw [← mul_inv_eq_one]
        exact h4
      calc y * (x⁻¹ * (u * t)) = (x⁻¹ * (u * t)) * y * (x⁻¹ * (u * t))⁻¹ * (x⁻¹ * (u * t)) := by
            rw [h5]
        _ = (x⁻¹ * (u * t)) * y := by group
    have : u * t = x * (x⁻¹ * (u * t)) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)
  have hall : ∀ u ∈ longInv G Ω,
      u ∈ M ⊔ Subgroup.centralizer (M : Set G) ⊔ Subgroup.zpowers t := by
    intro u hu
    by_cases hout : IsOuterFactor Mf
    · have h1 := hJout hout u hu
      have : u = (u * t) * t⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)))
    · exact Subgroup.mem_sup_left (hJin hout u hu)
  have hGeq : M ⊔ Subgroup.centralizer (M : Set G) ⊔ Subgroup.zpowers t = ⊤ := by
    rw [eq_top_iff, ← hH]
    exact jHull_le_iff.mpr hall
  have h1K : 1 < K.index := by
    have := three_le_index hG hαK.le hK
    omega
  have hπJ : ∀ u ∈ longInv G Ω, (toPermHom G (G ⧸ K)).rangeRestrict u ∈
      longInv (toPermHom G (G ⧸ K)).range (G ⧸ K) := fun u hu =>
    rangeRestrict_mem_longInv_quotient hG.odd_card hαK.le h1K hu
  obtain ⟨DΨ0⟩ := holtStructure_range_quotient hG hB hαK hK
  have hGΨ := isStarGroup_range_quotient hG hαK.le (three_le_index hG hαK.le hK)
  have hBΨ := holtTheorem1Below_range_quotient hG hB hαK
  set DΨ := DΨ0.withT hGΨ hBΨ (hπJ t ht.1) with hDΨ
  have hDΨt : DΨ.t = (toPermHom G (G ⧸ K)).rangeRestrict t := HoltData.withT_t _ _ _ _
  have hπsurj : Function.Surjective (toPermHom G (G ⧸ K)).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hπker : ∀ g : G, (toPermHom G (G ⧸ K)).rangeRestrict g = 1 ↔ g ∈ K.normalCore := by
    intro g
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker, ← MonoidHom.coe_rangeRestrict,
      Subtype.ext_iff]
    rfl
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht.1.1]; exact pow_orderOf_eq_one t
  have hCtop : Subgroup.zpowers ((toPermHom G (G ⧸ K)).rangeRestrict t) ⊔
      (Subgroup.centralizer (M : Set G)).map (toPermHom G (G ⧸ K)).rangeRestrict = ⊤ := by
    have h := congrArg (Subgroup.map (toPermHom G (G ⧸ K)).rangeRestrict) hGeq
    have hMπ : M.map (toPermHom G (G ⧸ K)).rangeRestrict = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      exact fun x hx => (hπker x).mpr (hMN hx)
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, hMπ, bot_sup_eq,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπsurj, sup_comm] at h
    exact h
  have hCπn : ((Subgroup.centralizer (M : Set G)).map
      (toPermHom G (G ⧸ K)).rangeRestrict).Normal := hCn.map _ hπsurj
  have hidxΨ : ((Subgroup.centralizer (M : Set G)).map
      (toPermHom G (G ⧸ K)).rangeRestrict).relIndex ⊤ ≤ 2 :=
    relIndex_le_two_of_sup_zpowers (by rw [← map_mul, ht2, map_one]) le_top (Subgroup.mem_top _)
      (fun b _ p hp => hCπn.conj_mem p hp b) hCtop
  have hidxΨ' : ∀ A : Subgroup (toPermHom G (G ⧸ K)).range,
      ((Subgroup.centralizer (M : Set G)).map (toPermHom G (G ⧸ K)).rangeRestrict).relIndex A
        ≤ 2 := fun A =>
    (Subgroup.relIndex_le_of_le_right le_top
      (Subgroup.index_ne_zero_of_finite : (((Subgroup.centralizer (M : Set G)).map
        (toPermHom G (G ⧸ K)).rangeRestrict).subgroupOf ⊤).index ≠ 0)).trans hidxΨ
  have hπC : ∀ c ∈ Subgroup.centralizer (M : Set G),
      (toPermHom G (G ⧸ K)).rangeRestrict c = 1 → c = 1 := fun c hc h1 =>
    hCN c ((hπker c).mp h1) hc
  have hOΨ : jOddCore (toPermHom G (G ⧸ K)).range (G ⧸ K) = ⊥ := by
    have hodd : Odd (Nat.card (jOddCore (toPermHom G (G ⧸ K)).range (G ⧸ K))) :=
      odd_card_jOddCore
    have hle : jOddCore (toPermHom G (G ⧸ K)).range (G ⧸ K) ≤
        (Subgroup.centralizer (M : Set G)).map (toPermHom G (G ⧸ K)).rangeRestrict :=
      le_of_relIndex_le_two_of_odd (hidxΨ' _) hodd
    have hZinj : Function.Injective ((toPermHom G (G ⧸ K)).rangeRestrict.comp
        (Subgroup.centralizer (M : Set G) ⊓ (jOddCore (toPermHom G (G ⧸ K)).range
          (G ⧸ K)).comap (toPermHom G (G ⧸ K)).rangeRestrict).subtype) := by
      rw [injective_iff_map_eq_one]
      intro z hz
      exact Subtype.ext (hπC z z.2.1 hz)
    have hZodd : Odd (Nat.card ↥(Subgroup.centralizer (M : Set G) ⊓
        (jOddCore (toPermHom G (G ⧸ K)).range (G ⧸ K)).comap
          (toPermHom G (G ⧸ K)).rangeRestrict)) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hZinj).toEquiv]
      refine Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le ?_)
      rintro _ ⟨z, rfl⟩
      exact z.2.2
    have hZ := eq_bot_of_odd_of_normal hO hZodd
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨c, hc, rfl⟩ := hle hy
    have hcZ : c ∈ Subgroup.centralizer (M : Set G) ⊓ (jOddCore (toPermHom G (G ⧸ K)).range
        (G ⧸ K)).comap (toPermHom G (G ⧸ K)).rangeRestrict := ⟨hc, hy⟩
    rw [hZ, Subgroup.mem_bot] at hcZ
    rw [hcZ, map_one]
    exact Subgroup.one_mem _
  have hHΨ : jHull (toPermHom G (G ⧸ K)).range (G ⧸ K) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := hπsurj y
    have hle : (jHull G Ω).map (toPermHom G (G ⧸ K)).rangeRestrict ≤
        jHull (toPermHom G (G ⧸ K)).range (G ⧸ K) := by
      rw [jHull, MonoidHom.map_closure]
      exact (Subgroup.closure_le _).mpr (by
        rintro _ ⟨u, hu, rfl⟩
        exact mem_jHull_of_mem_longInv (hπJ u hu))
    exact hle ⟨g, hH ▸ Subgroup.mem_top g, rfl⟩
  have hLC : ∀ i, DΨ.L i ≤ (Subgroup.centralizer (M : Set G)).map
      (toPermHom G (G ⧸ K)).rangeRestrict := by
    intro i
    have h := commutator_le_of_relIndex_le_two (hidxΨ' (DΨ.L i))
    rwa [DΨ.commutator_L_eq hOΨ i] at h
  have hLift : ∀ i, (Subgroup.centralizer (M : Set G) ⊓
      (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict).map
        (toPermHom G (G ⧸ K)).rangeRestrict = DΨ.L i := by
    intro i
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hc.2
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := hLC i hy
      exact ⟨c, ⟨hc, hy⟩, rfl⟩
  have hL'C : (⨆ i, Subgroup.centralizer (M : Set G) ⊓
      (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict) ≤
        Subgroup.centralizer (M : Set G) := iSup_le fun i => inf_le_left
  have hmapL' : (⨆ i, Subgroup.centralizer (M : Set G) ⊓
      (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict).map
        (toPermHom G (G ⧸ K)).rangeRestrict = ⨆ i, DΨ.L i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hLift
  have htv : ∀ v ∈ longInv G Ω, (toPermHom G (G ⧸ K)).rangeRestrict v =
      (toPermHom G (G ⧸ K)).rangeRestrict t → t⁻¹ * v ∈ M := by
    intro v hv hπv
    have htvN : t⁻¹ * v ∈ K.normalCore :=
      (hπker _).mp (by rw [map_mul, map_inv, hπv, inv_mul_cancel])
    have hvK : v ∈ K := by
      have := K.mul_mem htK (K.normalCore_le htvN)
      rwa [mul_inv_cancel_left] at this
    have hΘ : blockModelHom e (⟨t, htK⟩⁻¹ * ⟨v, hvK⟩) ∈ Mf := by
      rw [map_mul, map_inv]
      by_cases hout : IsOuterFactor Mf
      · obtain ⟨hMalt, hmod⟩ := hout
        have h1 := (notMem_alternatingGroup_iff_of_mem_longInv_perm
          (blockModelHom_mem_longInv (e := e) hG.odd_card hαK.le ht.1 htK)).mpr hmod
        have h2 := (notMem_alternatingGroup_iff_of_mem_longInv_perm
          (blockModelHom_mem_longInv (e := e) hG.odd_card hαK.le hv hvK)).mpr hmod
        rw [hMalt, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
        rw [Equiv.Perm.mem_alternatingGroup] at h1 h2
        rcases Int.units_eq_one_or (Equiv.Perm.sign (blockModelHom e ⟨t, htK⟩)) with h | h
        · exact absurd h h1
        rcases Int.units_eq_one_or (Equiv.Perm.sign (blockModelHom e ⟨v, hvK⟩)) with h' | h'
        · exact absurd h' h2
        rw [h, h']
        rfl
      · exact Mf.mul_mem (Mf.inv_mem (hinner hout t ht.1 htK)) (hinner hout v hv hvK)
    rw [← hrange] at hΘ
    obtain ⟨x, hx⟩ := hΘ
    have hmem : (x : G)⁻¹ * (t⁻¹ * v) ∈ K.normalCore :=
      K.normalCore.mul_mem (K.normalCore.inv_mem (hMN x.2)) htvN
    have h1 : blockModelHom e ⟨(x : G)⁻¹ * (t⁻¹ * v), K.normalCore_le hmem⟩ = 1 := by
      have hk : (⟨(x : G)⁻¹ * (t⁻¹ * v), K.normalCore_le hmem⟩ : K) =
          (Subgroup.inclusion hMK x)⁻¹ * (⟨t, htK⟩⁻¹ * ⟨v, hvK⟩) := Subtype.ext rfl
      rw [hk, map_mul, map_inv]
      change (blockModelHomOn e hMK x)⁻¹ * _ = 1
      rw [hx, inv_mul_cancel]
    have h2 := hNfaith _ hmem ((hΘ1 _).mp h1)
    rw [inv_mul_eq_one] at h2
    exact h2 ▸ x.2
  have hsup : M ⊔ (⨆ i, Subgroup.centralizer (M : Set G) ⊓
      (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict) ⊔ Subgroup.zpowers t = ⊤ := by
    rw [eq_top_iff, ← hH]
    refine jHull_le_iff.mpr fun u hu => ?_
    obtain ⟨h, hh, hhu⟩ := DΨ.exists_mem_iSup_conj_eq hOΨ (hπJ t ht.1) (hπJ u hu)
    rw [← hmapL'] at hh
    obtain ⟨h', hh'L, rfl⟩ := hh
    have hv := conj_mem_longInv hu h'⁻¹
    rw [inv_inv] at hv
    have hπv : (toPermHom G (G ⧸ K)).rangeRestrict (h'⁻¹ * u * h') =
        (toPermHom G (G ⧸ K)).rangeRestrict t := by
      rw [map_mul, map_mul, map_inv, ← hhu]
      group
    have hx := htv _ hv hπv
    have hxM := hMn.conj_mem _ hx h'
    have hu_eq : u = h' * t * h'⁻¹ * (h' * (t⁻¹ * (h'⁻¹ * u * h')) * h'⁻¹) := by group
    rw [hu_eq]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hxM))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hh'L)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.inv_mem _ hh'L))
  have htMC : ¬ IsOuterFactor Mf → ∃ x ∈ M, ∃ c ∈ Subgroup.centralizer (M : Set G),
      x * c = t := fun hno =>
    Subgroup.mem_sup_of_normal_right.mp (hJin hno t ht.1)
  have hO' : jOddCore G Ω = ⊥ := jOddCore_eq_bot_of_pPrimeCore_eq_bot hO
  let πH : jHull G Ω →* jHull (toPermHom G (G ⧸ K)).range (G ⧸ K) :=
    ((toPermHom G (G ⧸ K)).rangeRestrict.comp (jHull G Ω).subtype).codRestrict _
      fun h => by rw [hHΨ]; exact Subgroup.mem_top _
  have hfacNone : factorImage G Ω M ((stabClassHom M α).comp (jHull G Ω).subtype) =
      M.map (stabClassHom M α) := by
    rw [factorImage, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, hH, inf_top_eq]
  have hfacSome : ∀ i, factorImage G Ω (Subgroup.centralizer (M : Set G) ⊓
      (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict) ((DΨ.ρ i).comp πH) = DΨ.M i := by
    intro i
    have h1 : ((Subgroup.centralizer (M : Set G) ⊓ (DΨ.L i).comap
        (toPermHom G (G ⧸ K)).rangeRestrict).subgroupOf (jHull G Ω)).map πH =
          (DΨ.L i).subgroupOf (jHull (toPermHom G (G ⧸ K)).range (G ⧸ K)) := by
      apply Subgroup.map_injective (jHull (toPermHom G (G ⧸ K)).range (G ⧸ K)).subtype_injective
      rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (DΨ.L_le i),
        show (jHull (toPermHom G (G ⧸ K)).range (G ⧸ K)).subtype.comp πH =
          (toPermHom G (G ⧸ K)).rangeRestrict.comp (jHull G Ω).subtype from rfl,
        ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, hH, inf_top_eq, hLift]
    rw [factorImage, ← Subgroup.map_map, h1]
    rfl
  refine ⟨{
    ι := Option DΨ.ι
    Ψc := fun o => match o with
      | none => StabClass M α
      | some i => DΨ.Ψc i
    fintypeΨ := fun o => match o with
      | none => inferInstance
      | some i => inferInstance
    decEqΨ := fun o => match o with
      | none => inferInstance
      | some i => inferInstance
    coord := fun ω o => match o with
      | none => stabClassOf M α ω
      | some i => DΨ.coord (blockCoset α K ω) i
    ρ := fun o => match o with
      | none => (stabClassHom M α).comp (jHull G Ω).subtype
      | some i => (DΨ.ρ i).comp πH
    L := fun o => match o with
      | none => M
      | some i => Subgroup.centralizer (M : Set G) ⊓
          (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict
    t := t
    t_mem := ht.1
    coord_eq_iff := ?_
    coord_surjective := ?_
    coord_smul := ?_
    L_le := ?_
    oddCore_le := ?_
    le_normalizer := ?_
    le_ker := ?_
    inf_ker := ?_
    factor := ?_
    sup_eq := ?_
    inner := ?_
    ker_outer := ?_
    ker_inner := ?_ }⟩
  ·
    intro ω ω'
    rw [orbit_jOddCore_eq_singleton hO' ω, Set.mem_singleton_iff]
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    have h1 : stabClassOf M α ω = stabClassOf M α ω' := congrFun h none
    have h2 : DΨ.coord (blockCoset α K ω) = DΨ.coord (blockCoset α K ω') :=
      funext fun i => congrFun h (some i)
    exact (eq_of_blockCoset_eq_of_stabClassOf_eq hMK hinj hrange hMf hαK.le
      (DΨ.coord_injective hOΨ h2) h1).symm
  ·
    intro f
    obtain ⟨ψ, hψ⟩ := DΨ.coord_surjective (fun i => f (some i))
    obtain ⟨ω, hω1, hω2⟩ :=
      exists_blockCoset_eq_stabClassOf_eq hMK hinj hrange hMf hαK.le ψ (f none)
    refine ⟨ω, funext fun o => ?_⟩
    cases o with
    | none => exact hω2
    | some i =>
      change DΨ.coord (blockCoset α K ω) i = f (some i)
      rw [hω1, hψ]
  ·
    intro h ω o
    cases o with
    | none => exact stabClassOf_smul α (h : G) ω
    | some i =>
      change DΨ.coord (blockCoset α K ((h : G) • ω)) i =
        DΨ.ρ i (πH h) (DΨ.coord (blockCoset α K ω) i)
      rw [blockCoset_smul hαK.le, ← DΨ.coord_smul]
      rfl
  ·
    intro o
    rw [hH]
    exact le_top
  ·
    intro o
    rw [hO']
    exact bot_le
  ·
    intro o
    cases o with
    | none => exact (Subgroup.normalizer_eq_top_iff.mpr hMn).ge.trans' le_top
    | some i =>
      have hLn : (DΨ.L i).Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hHΨ]
        exact DΨ.le_normalizer i
      have : (Subgroup.centralizer (M : Set G) ⊓
          (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict).Normal :=
        Subgroup.normal_inf_normal _ _
      exact (Subgroup.normalizer_eq_top_iff.mpr this).ge.trans' le_top
  ·
    intro o o' hoo' h hh
    rw [MonoidHom.mem_ker]
    cases o with
    | none =>
      cases o' with
      | none => exact absurd rfl hoo'
      | some j =>
        change DΨ.ρ j (πH h) = 1
        have h1 : πH h = 1 := Subtype.ext (Subtype.ext (congrArg Subtype.val
          ((hπker (h : G)).mpr (hMN hh))))
        rw [h1, map_one]
    | some i =>
      cases o' with
      | none => exact stabClassHom_eq_one_of_mem_centralizer hh.1
      | some j =>
        change DΨ.ρ j (πH h) = 1
        exact DΨ.rho_eq_one_of_mem_L (fun hij => hoo' (congrArg some hij)) hh.2
  ·
    intro o
    rw [hO', Subgroup.bot_subgroupOf, eq_bot_iff]
    rintro h ⟨hh, hker⟩
    rw [Subgroup.mem_bot]
    cases o with
    | none =>
      have hker' : stabClassHom M α (h : G) = 1 := hker
      exact Subtype.ext (eq_one_of_forall_stabClassHom_eq hMK hinj hrange hMf hh
        fun l => by rw [hker', Equiv.Perm.one_apply])
    | some i =>
      have hmem : πH h ∈ (DΨ.L i).subgroupOf (jHull (toPermHom G (G ⧸ K)).range (G ⧸ K)) ⊓
          (DΨ.ρ i).ker := ⟨hh.2, hker⟩
      rw [DΨ.inf_ker i, hOΨ, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at hmem
      exact Subtype.ext (hπC _ hh.1 (congrArg Subtype.val hmem))
  ·
    intro o
    cases o with
    | none =>
      change IsHoltFactor (factorImage G Ω M ((stabClassHom M α).comp (jHull G Ω).subtype))
      rw [hfacNone]
      exact hHFΛ
    | some i =>
      change IsHoltFactor (factorImage G Ω (Subgroup.centralizer (M : Set G) ⊓
        (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict) ((DΨ.ρ i).comp πH))
      rw [hfacSome]
      exact DΨ.factor i
  ·
    rw [hO', bot_sup_eq, iSup_option, hH]
    exact hsup
  ·
    intro o hno
    cases o with
    | none =>
      change ¬ IsOuterFactor (factorImage G Ω M ((stabClassHom M α).comp
        (jHull G Ω).subtype)) at hno
      change (stabClassHom M α).comp (jHull G Ω).subtype ⟨t, _⟩ ∈
        factorImage G Ω M ((stabClassHom M α).comp (jHull G Ω).subtype)
      rw [hfacNone] at hno ⊢
      obtain ⟨x, hx, c, hc, hxc⟩ := htMC (fun h => hno (hOFΛ.mpr h))
      refine ⟨x, hx, ?_⟩
      change stabClassHom M α x = stabClassHom M α t
      rw [← hxc, map_mul, stabClassHom_eq_one_of_mem_centralizer hc, mul_one]
    | some i =>
      change ¬ IsOuterFactor (factorImage G Ω (Subgroup.centralizer (M : Set G) ⊓
        (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict) ((DΨ.ρ i).comp πH)) at hno
      rw [hfacSome] at hno
      change DΨ.ρ i (πH ⟨t, _⟩) ∈ factorImage G Ω (Subgroup.centralizer (M : Set G) ⊓
        (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict) ((DΨ.ρ i).comp πH)
      rw [hfacSome, show πH ⟨t, mem_jHull_of_mem_longInv ht.1⟩ = DΨ.tHull from
        Subtype.ext (by
          change (toPermHom G (G ⧸ K)).rangeRestrict t = DΨ.t
          exact hDΨt.symm)]
      exact DΨ.inner i hno
  ·
    intro _
    rw [jOrbitKernel_eq_bot hO', hO']
  ·
    intro hall
    refine ⟨?_, fun h => absurd hO' h⟩
    rw [jOrbitKernel_eq_bot hO', hO', bot_sup_eq, sup_bot_eq, iSup_option]
    have hno : ¬ IsOuterFactor Mf := fun h => hall none (by
      change IsOuterFactor (factorImage G Ω M ((stabClassHom M α).comp (jHull G Ω).subtype))
      rw [hfacNone]
      exact hOFΛ.mpr h)
    obtain ⟨x, hx, c, hc, hxc⟩ := htMC hno
    have hDt := (DΨ.ker_inner fun i h => hall (some i) (by
      change IsOuterFactor (factorImage G Ω (Subgroup.centralizer (M : Set G) ⊓
        (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict) ((DΨ.ρ i).comp πH))
      rw [hfacSome]
      exact h)).1
    rw [hOΨ, jOrbitKernel_eq_bot hOΨ, bot_sup_eq, sup_bot_eq, hDΨt, ← hmapL'] at hDt
    obtain ⟨ℓ, hℓ, hℓc⟩ := hDt
    have hcπ : (toPermHom G (G ⧸ K)).rangeRestrict c = (toPermHom G (G ⧸ K)).rangeRestrict t := by
      rw [← hxc, map_mul, (hπker x).mpr (hMN hx), one_mul]
    have hℓeq : ℓ = c := by
      have h1 := hπC (ℓ⁻¹ * c) (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hL'C hℓ)) hc)
        (by rw [map_mul, map_inv, hℓc, hcπ, inv_mul_cancel])
      rw [inv_mul_eq_one] at h1
      exact h1
    have hmem : x * c ∈ M ⊔ ⨆ i, Subgroup.centralizer (M : Set G) ⊓
        (DΨ.L i).comap (toPermHom G (G ⧸ K)).rangeRestrict :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (hℓeq ▸ hℓ))
    rw [hxc] at hmem
    exact hmem

end Assembly

section LemmaThreeOne

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem holtStructure_of_kernel_ne_bot (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (hH : jHull G Ω = ⊤)
    (hO : CFSG.pPrimeCore 2 G = ⊥) {α : Ω} {K : Subgroup G} (hαK : stabilizer G α < K)
    (hK : K ≠ ⊤)
    (hprim : IsPreprimitive (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K))
    (hN : K.normalCore ≠ ⊥)
    (hT : ¬ IsPretransitive (jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K)) (K ⧸ (stabilizer G α).subgroupOf K)) :
    HoltStructure G Ω := by
  obtain ⟨D, j₀, hj₀, hOB, hLN, hMn⟩ :=
    exists_component_of_kernel_ne_bot hG hB hH hO hαK hK hprim hN hT
  have hMN : ((D.L j₀).comap (blockKernelHom G α K)).map K.normalCore.subtype ≤
      K.normalCore := Subgroup.map_subtype_le _
  have hbij : Function.Bijective fun c : K ⧸ (stabilizer G α).subgroupOf K => D.coord c j₀ := by
    refine ⟨fun c c' h => D.coord_injective hOB (funext fun j => ?_), fun b => ?_⟩
    · rw [hj₀ j]
      exact h
    · exact D.exists_coord_apply_eq j₀ b
  set e := Equiv.ofBijective _ hbij with hedef
  have heq : ∀ (k : K) (h : jHull (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K)),
      (h : (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range) =
        (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict k →
      blockModelHom e k = D.ρ j₀ h := by
    intro k h hk
    ext b
    obtain ⟨c, rfl⟩ := e.surjective b
    rw [blockModelHom_apply]
    change D.coord (k • c) j₀ = D.ρ j₀ h (D.coord c j₀)
    rw [← D.coord_smul, hk]
    rfl
  have := hG.isPretransitive
  have h1rel : 1 < (stabilizer G α).relIndex K := by
    have := three_le_relIndex hG hαK
    omega
  have := hMn
  refine holtStructure_of_factor hG hB hH hO hαK hK hMN (e := e) (Mf := D.M j₀) ?_
    (D.factor j₀) ?_
  · ext m
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨n, hn, hnx⟩ := x.2
      have hh : blockKernelHom G α K n ∈ jHull
          (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
          (K ⧸ (stabilizer G α).subgroupOf K) := D.L_le j₀ hn
      have hk : Subgroup.inclusion K.normalCore_le n =
          Subgroup.inclusion (hMN.trans K.normalCore_le) x := Subtype.ext hnx
      have h1 := heq (Subgroup.inclusion (hMN.trans K.normalCore_le) x) ⟨_, hh⟩ (by
        rw [← hk]
        rfl)
      change blockModelHom e (Subgroup.inclusion (hMN.trans K.normalCore_le) x) ∈ D.M j₀
      rw [h1]
      exact D.rho_mem_M hn
    · intro hm
      obtain ⟨h, hhL, rfl⟩ := D.mem_M.mp hm
      obtain ⟨n, hn⟩ := hLN hhL
      have hnM : (n : G) ∈ ((D.L j₀).comap (blockKernelHom G α K)).map K.normalCore.subtype :=
        ⟨n, by
          change blockKernelHom G α K n ∈ D.L j₀
          rw [hn]
          exact hhL, rfl⟩
      refine ⟨⟨n, hnM⟩, ?_⟩
      change blockModelHom e (Subgroup.inclusion (hMN.trans K.normalCore_le) ⟨n, hnM⟩) = _
      exact heq _ h (hn.symm.trans rfl)
  · intro hno u hu huK
    have hu' := rangeRestrict_mem_longInv_block hG.odd_card hαK.le h1rel huK hu
    rw [heq ⟨u, huK⟩ ⟨_, mem_jHull_of_mem_longInv hu'⟩ rfl]
    exact (D.rho_mem_M_iff hu' j₀).mpr hno

theorem holtStructure_of_not_isPreprimitive (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (hH : jHull G Ω = ⊤)
    (hO : CFSG.pPrimeCore 2 G = ⊥) (hprim : ¬ IsPreprimitive G Ω) : HoltStructure G Ω := by
  have := hG.isPretransitive
  have : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := hG.three_le_card
    omega
  obtain ⟨α⟩ : Nonempty Ω := inferInstance
  obtain ⟨K₀, hαK₀, hK₀⟩ := exists_stabilizer_lt_of_not_isPreprimitive hprim α
  obtain ⟨K, ⟨hαK, hKK₀⟩, hmin⟩ := wellFounded_lt.has_min
    {K : Subgroup G | stabilizer G α < K ∧ K ≤ K₀} ⟨K₀, hαK₀, le_rfl⟩
  have hK : K ≠ ⊤ := fun h => hK₀ (top_le_iff.mp (h ▸ hKK₀))
  have hprimB := isPreprimitive_range_block hαK fun K' h1 h2 =>
    (eq_or_lt_of_le h2).resolve_right fun hlt => hmin K' ⟨h1, h2.trans hKK₀⟩ hlt
  by_cases hN : K.normalCore = ⊥
  · exact (false_of_kernel_eq_bot hG hB hO hαK hK hprimB hN).elim
  · by_cases hT : IsPretransitive (jOddCore (toPermHom K
        (K ⧸ (stabilizer G α).subgroupOf K)).range (K ⧸ (stabilizer G α).subgroupOf K))
        (K ⧸ (stabilizer G α).subgroupOf K)
    · exact (false_of_isPretransitive_oddCore_block hG hO hαK.le hN hT).elim
    · exact holtStructure_of_kernel_ne_bot hG hB hH hO hαK hK hprimB hN hT

end LemmaThreeOne

end CFSG.Holt.H78
