module

public import CFSG.LieType.Ree.BorelSelfNormalizers
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem reeFixedPosUnipotent_le_reeGamma :
    t.reeFixedPosUnipotent K a ≤ t.reeGamma K a :=
  inf_le_right

theorem reeFixedNegUnipotent_le_reeGamma :
    t.reeFixedNegUnipotent K a ≤ t.reeGamma K a :=
  inf_le_right

theorem reeFixedBorel_le_normalizer_reeFixedPosUnipotent :
    t.reeFixedBorel K a ≤
      Subgroup.normalizer (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer reeFixedPosUnipotent_le_reeFixedBorel).1
    reeFixedPosUnipotent_subgroupOf_normal

theorem reeFixedPosUnipotent_inf_reeFixedNegUnipotent :
    t.reeFixedPosUnipotent K a ⊓ t.reeFixedNegUnipotent K a = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_right _ reeFixedPosUnipotent_le_reeFixedBorel).trans
    reeFixedBorel_inf_reeFixedNegUnipotent.le)

section Sylow

theorem isPGroup_reeFixedPosUnipotent_subgroupOf :
    IsPGroup t.prime ((t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a)) :=
  ((isPGroup_posUnipotent t.prime t.tag).to_le
    (inf_le_left : t.reeFixedPosUnipotent K a ≤ _)).of_equiv
      (Subgroup.subgroupOfEquivOfLe reeFixedPosUnipotent_le_reeGamma).symm

theorem pow_card_sub_one_mem_reeFixedPosUnipotent
    {b : ModGL t.tag K}
    (hb : b ∈ t.reeFixedBorel K a) : b ^ (Nat.card K - 1) ∈ t.reeFixedPosUnipotent K a := by
  have hb' : b ∈ (t.reeFixedBorel K a : Set (ModGL t.tag K)) := hb
  rw [reeFixedBorel_eq_mul'] at hb'
  obtain ⟨u, hu, h, hh, rfl⟩ := hb'
  obtain ⟨u', hu', e⟩ := exists_mul_pow_eq_mul_pow hu
    (reeFixedBorel_le_normalizer_reeFixedPosUnipotent (reeFixedTorus_le_reeFixedBorel hh))
    (Nat.card K - 1)
  have hhT : h ∈ torusGroup t.tag K := (Subgroup.mem_inf.1 hh).1
  rw [e, pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hhT), mul_one]
  exact hu'

theorem not_dvd_index_reeFixedPosUnipotent
    [Fact t.prime.Prime] :
    ¬ t.prime ∣ ((t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a)).index := by
  have := finite_modGL (τ := t.tag) (K := K)
  refine not_dvd_index_of_forall_pow_mem isPGroup_reeFixedPosUnipotent_subgroupOf
    (not_dvd_natCard_sub_one (K := K) t.prime) fun x hx => ?_
  rw [Subgroup.mem_subgroupOf]
  have hxB : (x : ModGL t.tag K) ∈ t.reeFixedBorel K a := by
    rw [← reeGamma_inf_normalizer_reeFixedPosUnipotent]
    exact Subgroup.mem_inf.2 ⟨x.2,
      mem_normalizer_of_mem_normalizer_subgroupOf reeFixedPosUnipotent_le_reeGamma hx⟩
  exact pow_card_sub_one_mem_reeFixedPosUnipotent hxB

end Sylow

theorem reeFixedPosUnipotent_inf_map_conj_eq_bot_iff
    {w₀ : WeylGroup t.tag}
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) {g : ModGL t.tag K}
    (hg : g ∈ t.reeFixedBruhatCell K a w) :
    t.reeFixedPosUnipotent K a ⊓
        (t.reeFixedPosUnipotent K a).map (MulAut.conj g).toMonoidHom = ⊥ ↔ w = w₀ := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hg
  have hBN := reeFixedBorel_le_normalizer_reeFixedPosUnipotent (t := t) (K := K) (a := a)
  have hred : t.reeFixedPosUnipotent K a ⊓ (t.reeFixedPosUnipotent K a).map
      (MulAut.conj (b * canonicalRep (coxeterSystem t.tag) K w * b')).toMonoidHom =
      (t.reeFixedPosUnipotent K a ⊓ (t.reeFixedPosUnipotent K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom).map
          (MulAut.conj b).toMonoidHom := by
    rw [map_conj_mul, map_conj_mul, map_conj_eq_of_mem_normalizer (hBN hb'),
      Subgroup.map_inf_eq _ _ _ (MulAut.conj b).injective, map_conj_eq_of_mem_normalizer (hBN hb)]
  rw [hred, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj b).injective]
  constructor
  · intro hbot
    by_contra hne
    have hv : w₀ * w⁻¹ ∈ t.relWeylRee := mul_mem (longest_mem_relWeylRee hw₀) (inv_mem hw)
    have hv1 : w₀ * w⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.1 h).symm
    obtain ⟨j, hj⟩ := exists_fixedOrbitRoots_neg hv hv1
    have hpos : ∀ α ∈ t.fixedOrbitRoots j, 0 < height (w⁻¹ • α) := fun α hα => by
      have h1 := hj α hα
      rw [mul_smul, smul_longest hw₀, height_neg] at h1
      omega
    have hn : canonicalRep (coxeterSystem t.tag) K w ∈ t.reeGamma K a :=
      (canonicalRep_mem_reeFixedMonomial t K a hw).2
    have hroots : ∀ α ∈ (fun α => w⁻¹ • α) '' t.fixedOrbitRoots j, IsRoot t.tag α := by
      rintro _ ⟨α, hα, rfl⟩
      exact IsRoot.smul (mem_fixedOrbitRoots_iff.1 hα).1 _
    have htrans : (rootSpan t.tag K ((fun α => w⁻¹ • α) '' t.fixedOrbitRoots j) ⊓
        t.reeGamma K a).map (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom =
          t.reeFixedOrbitUnipotent K a j := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
        (canonical_weyl_root_transport t.tag K).1 w _ hroots, Set.image_image,
        map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
      simp only [smul_inv_smul, Set.image_id']
      rfl
    have hle : rootSpan t.tag K ((fun α => w⁻¹ • α) '' t.fixedOrbitRoots j) ⊓
        t.reeGamma K a ≤ t.reeFixedPosUnipotent K a :=
      inf_le_inf_right _ (rootSpan_le_posUnipotent fun α hα => ⟨hroots α hα, by
        obtain ⟨β, hβ, rfl⟩ := hα
        exact hpos β hβ⟩)
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
    have hx : u ∈ t.reeFixedPosUnipotent K a ⊓ (t.reeFixedPosUnipotent K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j hu,
        Subgroup.map_mono hle ?_⟩
      rw [htrans]
      exact hu
    rw [hbot, Subgroup.mem_bot] at hx
    exact hu1 hx
  · rintro rfl
    rw [map_conj_reeFixedPosUnipotent hw₀]
    exact reeFixedPosUnipotent_inf_reeFixedNegUnipotent

theorem large_Ree_Sylow_opposition
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (w₀ : WeylGroup t.tag)
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) :
    (∃ P : Sylow t.prime (t.reeGamma K a), (P : Subgroup (t.reeGamma K a)) =
      (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a)) ∧
    (∃ P : Sylow t.prime (t.reeGamma K a), (P : Subgroup (t.reeGamma K a)) =
      (t.reeFixedNegUnipotent K a).subgroupOf (t.reeGamma K a)) ∧
    t.reeFixedPosUnipotent K a ⊓ t.reeFixedNegUnipotent K a = ⊥ ∧
    (∀ w ∈ t.relWeylRee, ∀ g ∈ t.reeFixedBruhatCell K a w,
      t.reeFixedPosUnipotent K a ⊓
          (t.reeFixedPosUnipotent K a).map (MulAut.conj g).toMonoidHom = ⊥ ↔ w = w₀) ∧
    (∀ S : Sylow t.prime (t.reeGamma K a),
      (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) ⊓ S = ⊥ ↔
        ∃ u ∈ (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a),
          (S : Subgroup (t.reeGamma K a)) =
            ((t.reeFixedNegUnipotent K a).subgroupOf (t.reeGamma K a)).map
              (MulAut.conj u).toMonoidHom) ∧
    ∀ α : MulAut (t.reeGamma K a), ∃ (c : t.reeGamma K a) (β : MulAut (t.reeGamma K a)),
      ((t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a)).map β.toMonoidHom =
        (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) ∧
      ((t.reeFixedNegUnipotent K a).subgroupOf (t.reeGamma K a)).map β.toMonoidHom =
        (t.reeFixedNegUnipotent K a).subgroupOf (t.reeGamma K a) ∧
      α = MulAut.conj c * β := by
  have : Fact t.prime.Prime := ⟨by cases t <;> decide⟩
  have := finite_modGL (τ := t.tag) (K := K)
  have hUC := reeFixedPosUnipotent_le_reeGamma (t := t) (K := K) (a := a)
  have hVC := reeFixedNegUnipotent_le_reeGamma (t := t) (K := K) (a := a)
  have hn₀ : canonicalRep (coxeterSystem t.tag) K w₀ ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a (longest_mem_relWeylRee hw₀)).2
  have hUp := isPGroup_reeFixedPosUnipotent_subgroupOf (t := t) (K := K) (a := a)
  have hUi := not_dvd_index_reeFixedPosUnipotent (t := t) (K := K) (a := a)
  have hPU := IsPGroup.toSylow_coe hUp hUi
  set PU : Sylow t.prime (t.reeGamma K a) := hUp.toSylow hUi
  set n₀ : t.reeGamma K a := ⟨_, hn₀⟩ with hn₀def
  have hPV : ((n₀ • PU : Sylow t.prime (t.reeGamma K a)) : Subgroup (t.reeGamma K a)) =
      (t.reeFixedNegUnipotent K a).subgroupOf (t.reeGamma K a) := by
    rw [coe_smul_sylow_eq_map, hPU, map_conj_subgroupOf hUC, hn₀def,
      map_conj_reeFixedPosUnipotent hw₀]
  set PV : Sylow t.prime (t.reeGamma K a) := n₀ • PU
  set UC := (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) with hUCdef
  set VC := (t.reeFixedNegUnipotent K a).subgroupOf (t.reeGamma K a) with hVCdef
  have hUV : UC ⊓ VC = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL t.tag K) ∈ t.reeFixedPosUnipotent K a ⊓ t.reeFixedNegUnipotent K a :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [reeFixedPosUnipotent_inf_reeFixedNegUnipotent, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  have hkey : ∀ S : Sylow t.prime (t.reeGamma K a), UC ⊓ S = ⊥ →
      ∃ u ∈ UC, (S : Subgroup (t.reeGamma K a)) = VC.map (MulAut.conj u).toMonoidHom := by
    intro S hS
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (t.reeGamma K a) PU S
    have hSc : (S : Subgroup (t.reeGamma K a)) = UC.map (MulAut.conj c).toMonoidHom := by
      rw [← hc, coe_smul_sylow_eq_map, hPU]
    rw [hSc, map_conj_subgroupOf hUC] at hS ⊢
    have hamb : t.reeFixedPosUnipotent K a ⊓
        (t.reeFixedPosUnipotent K a).map (MulAut.conj (c : ModGL t.tag K)).toMonoidHom = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      have hxC : x ∈ t.reeGamma K a := hUC (Subgroup.mem_inf.1 hx).1
      have h : (⟨x, hxC⟩ : t.reeGamma K a) ∈ UC ⊓ ((t.reeFixedPosUnipotent K a).map
          (MulAut.conj (c : ModGL t.tag K)).toMonoidHom).subgroupOf (t.reeGamma K a) :=
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
      rw [hS, Subgroup.mem_bot] at h
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h)
    have hcell : (c : ModGL t.tag K) ∈ ⋃ w : t.relWeylRee, t.reeFixedBruhatCell K a w := by
      rw [← reeGamma_eq_iUnion_reeFixedBruhatCell]
      exact c.2
    obtain ⟨⟨w, hw⟩, hcw⟩ := Set.mem_iUnion.1 hcell
    obtain rfl := (reeFixedPosUnipotent_inf_map_conj_eq_bot_iff hw₀ hw hcw).1 hamb
    obtain ⟨b, hb, b', hb', hbb⟩ := mem_reeFixedBruhatCell.1 hcw
    have hb'' : b ∈ (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) *
        (t.reeFixedTorus K a : Set (ModGL t.tag K)) := by
      rw [← reeFixedBorel_eq_mul']
      exact hb
    obtain ⟨u, hu, h, hh, rfl⟩ := hb''
    have hmapc : (t.reeFixedPosUnipotent K a).map
        (MulAut.conj (c : ModGL t.tag K)).toMonoidHom =
          (t.reeFixedNegUnipotent K a).map (MulAut.conj u).toMonoidHom := by
      rw [← hbb, map_conj_mul, map_conj_mul, map_conj_eq_of_mem_normalizer
        (reeFixedBorel_le_normalizer_reeFixedPosUnipotent hb'),
        map_conj_reeFixedPosUnipotent hw₀, map_conj_mul, map_conj_eq_of_mem_normalizer
        (reeFixedTorus_le_normalizer_reeFixedNegUnipotent hh)]
    refine ⟨⟨u, hUC hu⟩, hu, ?_⟩
    rw [hmapc, map_conj_subgroupOf hVC]
  have hkey' : ∀ S : Sylow t.prime (t.reeGamma K a),
      (∃ u ∈ UC, (S : Subgroup (t.reeGamma K a)) = VC.map (MulAut.conj u).toMonoidHom) →
        UC ⊓ S = ⊥ := by
    rintro S ⟨u, hu, hS⟩
    rw [hS, ← map_conj_self hu, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj u).injective, hUV,
      Subgroup.map_bot]
  have hAut : ∀ α : MulAut (t.reeGamma K a), ∃ (c : t.reeGamma K a)
      (β : MulAut (t.reeGamma K a)),
        UC.map β.toMonoidHom = UC ∧ VC.map β.toMonoidHom = VC ∧ α = MulAut.conj c * β := by
    intro α
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (t.reeGamma K a) PU (α • PU)
    have hαU : UC.map α.toMonoidHom = UC.map (MulAut.conj c).toMonoidHom := by
      rw [← hPU, ← coe_mulAut_smul_sylow, ← coe_smul_sylow_eq_map, hc]
    set α₁ := (MulAut.conj c)⁻¹ * α with hα₁
    have hα₁U : UC.map α₁.toMonoidHom = UC := by
      rw [map_mulAut_mul, hαU, ← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
    have hS : UC ⊓ ((α₁ • PV : Sylow t.prime (t.reeGamma K a)) : Subgroup (t.reeGamma K a)) =
        ⊥ := by
      rw [coe_mulAut_smul_sylow, hPV, ← hα₁U, ← Subgroup.map_inf_eq _ _ _ α₁.injective, hUV,
        Subgroup.map_bot]
    obtain ⟨u, hu, hu'⟩ := hkey _ hS
    rw [coe_mulAut_smul_sylow, hPV] at hu'
    refine ⟨c * u, (MulAut.conj u)⁻¹ * α₁, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul, hα₁U, ← map_inv, map_conj_self (inv_mem hu)]
    · rw [map_mulAut_mul, hu', ← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
    · rw [hα₁, map_mul]
      group
  exact ⟨⟨PU, hPU⟩, ⟨PV, hPV⟩, reeFixedPosUnipotent_inf_reeFixedNegUnipotent,
    fun w hw g hg => reeFixedPosUnipotent_inf_map_conj_eq_bot_iff hw₀ hw hg,
    fun S => ⟨hkey S, hkey' S⟩, hAut⟩

end ReeTag

end CFSG.LieType.Ree
