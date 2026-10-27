module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section General

variable {G : Type*} [Group G]

theorem coe_mem_normalizer_of_subgroupOf {X T : Subgroup G} (hTX : T ≤ X) {x : ↥X}
    (hx : x ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    (x : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact (Subgroup.mem_normalizer_iff.mp hx ⟨g, hTX hg⟩).mp hg
  · intro hg
    have hgX : g ∈ X := by
      have h := X.mul_mem (X.mul_mem (X.inv_mem x.2) (hTX hg)) x.2
      simpa [mul_assoc] using h
    exact (Subgroup.mem_normalizer_iff.mp hx ⟨g, hgX⟩).mpr hg

theorem isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf {X T : Subgroup G} (hT : IsSylowTwoOf T X) :
    IsSylowTwoOf (T.subgroupOf X) ⊤ := by
  refine ⟨le_top, hT.2.1.comap_subtype, ?_⟩
  have h : ((T.subgroupOf X).subgroupOf ⊤).index = (T.subgroupOf X).index :=
    Subgroup.relIndex_top_right _
  rw [h]
  exact hT.2.2

theorem isSylowTwoOf_map_top_of_surjective {X Y : Type*} [Group X] [Group Y] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) {f : X →* Y} (hf : Function.Surjective f) :
    IsSylowTwoOf (T.map f) ⊤ := by
  refine ⟨le_top, hT.2.1.map f, fun hd => hT.2.2 ?_⟩
  have h1 : ((T.map f).subgroupOf ⊤).index = (T.map f).index := Subgroup.relIndex_top_right _
  have h2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right _
  rw [h1] at hd
  rw [h2]
  exact hd.trans (Subgroup.index_map_dvd T hf)

theorem eq_one_of_forall_commute_perm_fin {m : ℕ} (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ τ : Equiv.Perm (Fin m), σ * τ = τ * σ) : σ = 1 := by
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext fun x => by simpa using h x)
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, σ a} : Finset (Fin m))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt Finset.card_le_two (by omega))
  have hca : c ≠ a := fun h => hc (by simp [h])
  have hcb : c ≠ σ a := fun h => hc (by simp [h])
  have h1 := congrArg (fun f : Equiv.Perm (Fin m) => f a) (hσ (Equiv.swap a c))
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h1
  rw [Equiv.swap_apply_of_ne_of_ne ha hcb.symm] at h1
  exact hca (σ.injective h1)

theorem isPGroup_of_mulEquiv_quotient_pCore {X Y : Type*} [Group X] [Group Y]
    (e : X ⧸ CFSG.pCore 2 X ≃* Y) (hY : IsPGroup 2 Y) : IsPGroup 2 X := by
  intro x
  obtain ⟨k, hk⟩ := hY (e (QuotientGroup.mk x))
  have h1 : x ^ 2 ^ k ∈ CFSG.pCore 2 X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact e.injective (by rw [map_pow, hk, map_one])
  obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup ⟨_, h1⟩
  refine ⟨k + j, ?_⟩
  rw [pow_add, pow_mul]
  simpa using congrArg Subtype.val hj

theorem mk_eq_one_iff_coe_mem_pCoreOf {M : Subgroup G} (m : ↥M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = 1 ↔ (m : G) ∈ pCoreOf 2 M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hm
    have h : (m : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨m, hm, rfl⟩
    exact h
  · intro hm
    have h : (m : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := by
      exact hm
    obtain ⟨q, hq, hqm⟩ := h
    rwa [show m = q from Subtype.ext hqm.symm]

variable [Finite G]

theorem not_dvd_index_of_normalizer_inf_le_self {p : ℕ} [Fact p.Prime] {X S : Subgroup G}
    (hSX : S ≤ X) (hS : IsPGroup p S) (hN : X ⊓ Subgroup.normalizer (S : Set G) ≤ S) :
    ¬ p ∣ (S.subgroupOf X).index := by
  intro hdvd
  have hH : IsPGroup p (S.subgroupOf X) := hS.comap_subtype
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  have hX : p ^ (n + 1) ∣ Nat.card X := by
    rw [← (S.subgroupOf X).card_mul_index, hn, pow_succ]
    exact Nat.mul_dvd_mul_left _ hdvd
  have h1 := Sylow.prime_pow_dvd_card_normalizer hX hn
  have hle : Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) ≤ S.subgroupOf X :=
    fun x hx => hN ⟨x.2, coe_mem_normalizer_of_subgroupOf hSX hx⟩
  have h2 := Subgroup.card_le_of_le hle
  rw [hn] at h2
  have h3 := Nat.le_of_dvd Nat.card_pos h1
  have h4 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_add_one n)
  omega

omit [Finite G] in
theorem mem_normalizer_of_mk_center_mem_normalizer {X : Type*} [Group X] [Finite X]
    {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) {z : X}
    (hz : QuotientGroup.mk' (Subgroup.center X) z ∈ Subgroup.normalizer
      ((T.map (QuotientGroup.mk' (Subgroup.center X)) : Subgroup (X ⧸ Subgroup.center X)) :
        Set (X ⧸ Subgroup.center X))) :
    z ∈ Subgroup.normalizer (T : Set X) := by
  set q := QuotientGroup.mk' (Subgroup.center X)
  have hodd : ¬ 2 ∣ T.relIndex (T ⊔ Subgroup.center X) :=
    (B6.isSylowTwoOf_mono hT le_sup_left le_top).2.2
  have hconj : ∀ w : X, q w ∈ Subgroup.normalizer ((T.map q : Subgroup _) : Set _) →
      B6.conjSub w T ≤ T := by
    intro w hw
    refine B6.le_of_isPGroup_of_odd_relIndex (fun x hx => ?_) (B6.isSylowTwoOf_conjSub hT w).2.1
      le_sup_left (sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)) hodd
    rw [B6.mem_conjSub] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hw (q (w⁻¹ * x * w))).mp
      (Subgroup.mem_map_of_mem q hx)
    have h2 : q x ∈ T.map q := by simpa [mul_assoc] using h1
    have h3 : x ∈ (T.map q).comap q := h2
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h3
  exact B6.mem_normalizer_of_conjSub_le (hconj z hz)
    (hconj z⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hz))

end General

section Blocks

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_of_isPGroup_barM {M X : Subgroup G} (hXM : X ≤ M) (h : IsPGroup 2 (barM M X)) :
    IsPGroup 2 X := by
  intro x
  obtain ⟨k, hk⟩ := h ⟨QuotientGroup.mk' _ ⟨x, hXM x.2⟩,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ((⟨x, hXM x.2⟩ : ↥M) ^ 2 ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  rw [mk_eq_one_iff_coe_mem_pCoreOf] at h1
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 M ⟨_, h1⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have hj' := congrArg Subtype.val hj
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hj' ⊢
  rw [pow_add, pow_mul]
  exact hj'

theorem blockHasThree_of_three_dvd_card_range {M S L : Subgroup G} (hLM : L ≤ M) {C : Type*}
    [Group C] (ρ : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →* C)
    (h3 : 3 ∣ Nat.card ρ.range)
    (hρ : ∀ g : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)),
      (g : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → ρ g = 1) :
    BlockHasThree M S L := by
  have hAM : Subgroup.normalizer (S : Set G) ⊓ L ≤ M := inf_le_right.trans hLM
  let ι : ↥(Subgroup.normalizer (S : Set G) ⊓ L) →*
      ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hAM)).codRestrict _
      fun x => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hι : Function.Surjective ι := by
    rintro ⟨_, m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  have hf : Function.Surjective (ρ.rangeRestrict.comp ι) := ρ.rangeRestrict_surjective.comp hι
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥(Subgroup.normalizer (S : Set G) ⊓ L)) := inferInstance
  have hne := Sylow.ne_bot_of_dvd_card (P.mapSurjective hf) h3
  rw [Sylow.coe_mapSurjective] at hne
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.mp hc
  have hy1 : ρ (ι y) ≠ 1 := fun h1 => hc1 (Subtype.ext (Subtype.ext h1))
  have hyC : (ι y : ↥M ⧸ CFSG.pCore 2 ↥M) ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun h => hy1 (hρ _ h)
  rw [Subgroup.mem_centralizer_iff] at hyC
  push Not at hyC
  obtain ⟨_, ⟨m, hm, rfl⟩, hne'⟩ := hyC
  refine ⟨y, y.2, ?_, m, Subgroup.mem_subgroupOf.mp hm, fun hQ => hne' ?_⟩
  · exact (P.isPGroup'.map (Subgroup.subtype _)).to_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem (Subgroup.subtype _) hyP))
  · have h1 := (mk_eq_one_iff_coe_mem_pCoreOf
      ((Subgroup.inclusion hAM y) * m * (Subgroup.inclusion hAM y)⁻¹ * m⁻¹)).mpr hQ
    simp only [map_mul, map_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm

omit [Finite G] in
theorem barM_normalizer_inf_le (M S L : Subgroup G) :
    barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).2

theorem blockHasThree_of_surjective_perm {M S L : Subgroup G} (hLM : L ≤ M) {m : ℕ} (hm : 3 ≤ m)
    (ρ : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →* Equiv.Perm (Fin m))
    (hρ : Function.Surjective ρ) : BlockHasThree M S L := by
  refine blockHasThree_of_three_dvd_card_range hLM ρ ?_ fun g hg => ?_
  · rw [MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    exact Nat.dvd_factorial (by norm_num) hm
  · refine eq_one_of_forall_commute_perm_fin hm _ fun τ => ?_
    obtain ⟨h, rfl⟩ := hρ τ
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext ((Subgroup.mem_centralizer_iff.mp hg) _
      (barM_normalizer_inf_le M S L h.2)).symm)

theorem blockHasThree_of_three_dvd_card_map_center {M S L : Subgroup G} (hLM : L ≤ M)
    (h3 : 3 ∣ Nat.card (((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
      (barM M L)).map (QuotientGroup.mk' (Subgroup.center ↥(barM M L))))) :
    BlockHasThree M S L := by
  refine blockHasThree_of_three_dvd_card_range hLM
    ((QuotientGroup.mk' (Subgroup.center ↥(barM M L))).comp
      (Subgroup.inclusion (barM_normalizer_inf_le M S L))) ?_ fun g hg => ?_
  · rwa [MonoidHom.range_comp, Subgroup.inclusion_range]
  · rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_center_iff]
    exact fun h => Subtype.ext ((Subgroup.mem_centralizer_iff.mp hg) h h.2)

end Blocks

end CFSG.AGLEmbedding
