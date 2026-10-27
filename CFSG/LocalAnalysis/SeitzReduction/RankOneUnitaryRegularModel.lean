module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryAffine
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryPartition
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartNormalizer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.GH74.Uniqueness.Bender AffineModel
open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev commGroupOf {G : Type*} [Group G] (A : Subgroup G)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : CommGroup A :=
  { A.toGroup with mul_comm := fun x y => Subtype.ext (hA x x.2 y y.2) }

theorem mem_borel_iff_mem_normalizer {G : Type*} [Group G] {L T₁ : Subgroup G} {Q : Subgroup L}
    (hmemQ : ∀ y : L, y ∈ Q ↔ (y : G) ∈ T₁) (hT₁L : T₁ ≤ L) (d : L) :
    d ∈ borel Q ↔ (d : G) ∈ normalizer (T₁ : Set G) := by
  constructor
  · intro hdN
    refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have hyL : y ∈ L := hT₁L hy
      have h1 := (mem_normalizer_iff.mp hdN ⟨y, hyL⟩).mp ((hmemQ ⟨y, hyL⟩).mpr hy)
      have h2 := (hmemQ _).mp h1
      simpa using h2
    · have hyL : y ∈ L := by
        have h1 : (d : G) * y * (d : G)⁻¹ ∈ L := hT₁L hy
        have h2 := mul_mem (mul_mem (inv_mem d.2) h1) d.2
        simpa [mul_assoc] using h2
      have h1 : d * ⟨y, hyL⟩ * d⁻¹ ∈ Q := (hmemQ _).mpr (by simpa using hy)
      exact (hmemQ ⟨y, hyL⟩).mp ((mem_normalizer_iff.mp hdN ⟨y, hyL⟩).mpr h1)
  · intro hdT
    refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · refine (hmemQ _).mpr ?_
      have := (mem_normalizer_iff.mp hdT y).mp ((hmemQ y).mp hy)
      simpa using this
    · refine (hmemQ y).mpr ((mem_normalizer_iff.mp hdT y).mpr ?_)
      have := (hmemQ _).mp hy
      simpa using this

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem normalizer_szA_ne_top_of_card_sylow
    (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    normalizer (szA L T t : Set G) ≠ ⊤ := by
  intro htop
  have hnorm : (szA L T t).Normal := normalizer_eq_top_iff.mp htop
  have : IsSimpleGroup G := h.setting.1
  rcases Subgroup.Normal.eq_bot_or_eq_top (szA L T t) with hbot | htop'
  · have ht := mem_szA_right L T t
    rw [hbot, mem_bot] at ht
    have h2 := h.inv
    rw [ht, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · obtain ⟨x, y, hxy⟩ := h.setting.2.1
    obtain ⟨-, -, -, hcomm⟩ := h.szA_facts_of_card_sylow hS2
    exact hxy (hcomm x (htop' ▸ mem_top x) y (htop' ▸ mem_top y))

theorem mem_centralizer_szA₁_of_commute_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {l a : G} (hl : l ∈ L) (ha : a ∈ szA₁ (szT₁ L T)) (ha1 : a ≠ 1) (hla : l * a = a * l) :
    l ∈ centralizer (szA₁ (szT₁ L T) : Set G) := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  have hA₁L : ∀ x ∈ szA₁ (szT₁ L T), x ∈ L := fun x hx => szT₁_le_right L T (szA₁_le _ hx)
  have haZ : (⟨a, hA₁L a ha⟩ : L) ∈ rootCenter (Q : Subgroup L) := (hmemZ _).mpr ha
  have ha1' : (⟨a, hA₁L a ha⟩ : L) ≠ 1 := fun h1 => ha1 (congrArg Subtype.val h1)
  have hlC : (⟨l, hl⟩ : L) ∈ centralizer ({⟨a, hA₁L a ha⟩} : Set L) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hla
  rw [hc.centralizer_eq haZ ha1'] at hlC
  refine mem_centralizer_iff.mpr fun x hx => ?_
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  have hxZ : (⟨x, hA₁L x hx⟩ : L) ∈ rootCenter (Q : Subgroup L) := (hmemZ _).mpr hx
  have hx1' : (⟨x, hA₁L x hx⟩ : L) ≠ 1 := fun h1 => hx1 (congrArg Subtype.val h1)
  rw [← hc.centralizer_eq hxZ hx1', mem_centralizer_singleton_iff] at hlC
  exact (congrArg Subtype.val hlC).symm

theorem mem_centralizer_szA_of_mem_centralizer_szA₁ (h : U3Start G L f t T) {c : G} (hcL : c ∈ L)
    (hc : c ∈ centralizer (szA₁ (szT₁ L T) : Set G)) : c ∈ centralizer (szA L T t : Set G) := by
  have hle : szA L T t ≤ centralizer ({c} : Set G) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc a ha))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.mem c hcL).symm))
  exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hle hx)

theorem inf_normalizer_le_normalizer_szA (h : U3Start G L f t T) :
    L ⊓ normalizer (szT₁ L T : Set G) ≤ normalizer (szA L T t : Set G) := by
  rintro b ⟨hbL, hbT⟩
  exact SzPartition.mem_normalizer_sup_zpowers (centralizer_le (szA₁_le _) h.mem_centralizer_szT₁)
    (normalizer_le_normalizer_inf_centralizer (szT₁ L T) hbT)
    (mem_centralizer_iff.mp h.mem b hbL)

theorem exists_orbitEquiv_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ e : MulAction.orbit (szA L T t).normalizerMonoidHom.range
        (⟨t, mem_szA_right L T t⟩ : szA L T t) ≃ gmsRootConjugates (szA L T t) (zpowers t),
      (gmsRootConjugateAction (szA L T t) (zpowers t)).range =
        (MulAction.toPermHom (szA L T t).normalizerMonoidHom.range
          (MulAction.orbit (szA L T t).normalizerMonoidHom.range
            (⟨t, mem_szA_right L T t⟩ : szA L T t))).range.map e.permCongrHom.toMonoidHom := by
  classical
  have hD := h.partitionData_of_card_sylow hS2
  set A := szA L T t with hA
  set N := normalizer (A : Set G) with hN
  set ρ : N →* MulAut A := A.normalizerMonoidHom with hρ
  have hρa : ∀ (n : N) (a : A), ((ρ n a : A) : G) = (n : G) * a * (n : G)⁻¹ := fun n a => rfl
  set M := ρ.range with hM
  set t' : A := ⟨t, mem_szA_right L T t⟩ with ht'
  set Ω := MulAction.orbit M t' with hΩ
  set π := gmsRootConjugateAction A (zpowers t) with hπ
  have hR₀ : zpowers t ∈ gmsRootConjugates A (zpowers t) := SzPartitionData.zpowers_mem
  have horb : ∀ s : Ω, ∃ n : N, ((s : A) : G) = (n : G) * t * (n : G)⁻¹ := by
    rintro ⟨s, m, rfl⟩
    obtain ⟨n, hn⟩ := m.2
    refine ⟨n, ?_⟩
    change (((m : MulAut A) t' : A) : G) = _
    rw [← hn]
    rfl
  have hmem : ∀ s : Ω, zpowers ((s : A) : G) ∈ gmsRootConjugates A (zpowers t) := by
    intro s
    obtain ⟨n, hn⟩ := horb s
    rw [hn, ← SzPartition.map_conj_zpowers]
    exact map_conj_mem_gmsRootConjugates hR₀ n.2
  have hne : ∀ s : Ω, ((s : A) : G) ≠ 1 := by
    intro s hs
    obtain ⟨n, hn⟩ := horb s
    rw [hn] at hs
    exact hD.not_mem (by rw [conj_eq_one_iff.mp hs]; exact one_mem _)
  have hsq : ∀ s : Ω, ((s : A) : G) ^ 2 = 1 := by
    intro s
    obtain ⟨n, hn⟩ := horb s
    rw [hn, conj_pow, hD.sq_eq_one, mul_one, mul_inv_cancel]
  set e₀ : Ω → gmsRootConjugates A (zpowers t) := fun s => ⟨zpowers ((s : A) : G), hmem s⟩
    with he₀
  have hbij : Function.Bijective e₀ := by
    refine ⟨fun s s' hss => ?_, fun Q => ?_⟩
    · have h1 : zpowers ((s : A) : G) = zpowers ((s' : A) : G) := congrArg Subtype.val hss
      have h2 : ((s : A) : G) ∈ zpowers ((s' : A) : G) := by rw [← h1]; exact mem_zpowers _
      rcases mem_zpowers_involution_eq_one_or_eq (hsq s') h2 with h3 | h3
      · exact absurd h3 (hne s)
      · exact Subtype.ext (Subtype.ext h3)
    · obtain ⟨l, hl⟩ := hD.exists_smul_eq_zpowers Q
      refine ⟨⟨ρ l⁻¹ t', ⟨ρ l⁻¹, l⁻¹, rfl⟩, rfl⟩, Subtype.ext ?_⟩
      change zpowers (((ρ l⁻¹ t' : A) : G)) = (Q : Subgroup G)
      rw [hρa]
      obtain ⟨g, hg⟩ : ∃ g : G, g = (l : G) := ⟨_, rfl⟩
      have h1 : (Q : Subgroup G).map (MulAut.conj g).toMonoidHom = zpowers t := by
        rw [hg]
        exact hl
      have hQ : (Q : Subgroup G) = (zpowers t).map (MulAut.conj g⁻¹).toMonoidHom := by
        conv_rhs => rw [← h1]
        rw [Subgroup.map_map]
        refine (Subgroup.map_id _).symm.trans ?_
        congr 1
        ext x
        simp only [MonoidHom.id_apply, MonoidHom.coe_comp, Function.comp_apply,
          MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hQ, SzPartition.map_conj_zpowers, hg]
      rfl
  set e := Equiv.ofBijective e₀ hbij with he
  refine ⟨e, ?_⟩
  have key : ∀ n : N, π n = e.permCongrHom (MulAction.toPermHom M Ω (ρ.rangeRestrict n)) := by
    intro n
    ext Q : 1
    obtain ⟨s, rfl⟩ := e.surjective Q
    rw [permCongrHom_apply_apply, Equiv.symm_apply_apply]
    apply Subtype.ext
    change (zpowers ((s : A) : G)).map (MulAut.conj (n : G)).toMonoidHom =
      zpowers ((((ρ.rangeRestrict n) • s : Ω) : A) : G)
    rw [SzPartition.map_conj_zpowers]
    rfl
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    exact ⟨_, ⟨ρ.rangeRestrict n, rfl⟩, (key n).symm⟩
  · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    obtain ⟨n, hn⟩ := ρ.rangeRestrict_surjective m
    exact ⟨n, by rw [key, hn]; rfl⟩

section Certificates



theorem regularNormal_or_projective_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hf : 3 ≤ f) :
    HasRegularNormalSubgroup (gmsRootConjugateAction (szA L T t) (zpowers t)).range ∨
      (f = 3 ∧ IsProjectiveEight (gmsRootConjugateAction (szA L T t) (zpowers t)).range) := by
  classical
  obtain ⟨-, hA2, hAC, hAcomm⟩ := h.szA_facts_of_card_sylow hS2
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨hNA₁, -, -⟩ := h.partition_of_card_sylow hS2
  have hD := h.partitionData_of_card_sylow hS2
  have hNT₁ := h.normalizer_szA_le_of_card_sylow hS2
  set A := szA L T t with hA
  set A₁ := szA₁ (szT₁ L T) with hA₁
  set N := normalizer (A : Set G) with hN
  let _ : CommGroup A := commGroupOf A hAcomm
  set ρ : N →* MulAut A := A.normalizerMonoidHom with hρ
  have hρa : ∀ (n : N) (a : A), ((ρ n a : A) : G) = (n : G) * a * (n : G)⁻¹ := fun n a => rfl
  set M := ρ.range with hM
  set t' : A := ⟨t, mem_szA_right L T t⟩ with ht'
  set U : Subgroup A := A₁.subgroupOf A with hU
  have hA₁A : A₁ ≤ A := szA₁_le_szA L T t
  have hV : ∀ v : A, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 v v.2)
  have hUcard : Nat.card U = 2 ^ f := by
    rw [hU, Nat.card_congr (subgroupOfEquivOfLe hA₁A).toEquiv, hA₁card]
  have hUt : IsCompl U (zpowers t') := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxt⟩ := mem_inf.mp hx
      rcases mem_zpowers_involution_eq_one_or_eq (hV t') hxt with rfl | rfl
      · exact one_mem _
      · exact absurd (mem_subgroupOf.mp hxU) hD.not_mem
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨b, hb, z, hz, hbz⟩ := exists_mul_eq_of_mem_sup_zpowers
        (centralizer_le (szA₁_le _) h.mem_centralizer_szT₁) x.2
      have hzA : z ∈ A := mem_sup_right hz
      have hx : x = ⟨b, hA₁A hb⟩ * ⟨z, hzA⟩ := Subtype.ext hbz.symm
      rw [hx]
      refine mul_mem_sup (mem_subgroupOf.mpr hb) ?_
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers t'
  have hMU : ∀ m ∈ M, ∀ u ∈ U, m u ∈ U := by
    rintro _ ⟨n, rfl⟩ u hu
    rw [mem_subgroupOf] at hu ⊢
    rw [hρa]
    exact (mem_normalizer_iff.mp (hNA₁ n.2) _).mp hu
  set B := L ⊓ normalizer (szT₁ L T : Set G) with hB
  have hBN : B ≤ N := h.inf_normalizer_le_normalizer_szA
  set H : Subgroup (MulAut A) := (B.subgroupOf N).map ρ with hH
  have hHM : H ≤ M := map_le_range ρ _
  have hHt : ∀ x ∈ H, x t' = t' := by
    rintro _ ⟨b, hb, rfl⟩
    apply Subtype.ext
    rw [hρa]
    have hbL : (b : G) ∈ L := (mem_inf.mp (mem_subgroupOf.mp hb)).1
    change (b : G) * t * (b : G)⁻¹ = t
    rw [mem_centralizer_iff.mp h.mem _ hbL, mul_inv_cancel_right]
  have hCtL : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.setting.standardSetting.standard h.mem h.inv).1
  have hHn : ∀ m ∈ M, m t' = t' → ∀ x ∈ H, m * x * m⁻¹ ∈ H := by
    rintro _ ⟨n, rfl⟩ hnt _ ⟨b, hb, rfl⟩
    have hnt' : (n : G) * t * (n : G)⁻¹ = t := by
      have := congrArg Subtype.val hnt
      rw [hρa] at this
      exact this
    have hnC : (n : G) ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (n : G) * t = (n : G) * t * (n : G)⁻¹ * n := by group
        _ = t * n := by rw [hnt']
    have hnL := hCtL hnC
    have hnT := hNT₁ n.2
    obtain ⟨hbL, hbT⟩ := mem_inf.mp (mem_subgroupOf.mp hb)
    refine ⟨n * b * n⁻¹, mem_subgroupOf.mpr (mem_inf.mpr ⟨?_, ?_⟩), by
      simp only [map_mul, map_inv]⟩
    · simpa using (mem_normalizer_iff.mp hnL _).mp hbL
    · have := mul_mem (mul_mem hnT hbT) (inv_mem hnT)
      simpa using this
  have hHc : IsCyclic H := by
    obtain ⟨e', Q, hBd, hmemQ, -⟩ := h.exists_bender_of_card_sylow hS2
    obtain ⟨t₀, hc⟩ := hBd.exists_benderCore Q
    have hcart : ∀ d ∈ cartan (Q : Subgroup L) t₀, ((d : L) : G) ∈ B := fun d hd =>
      mem_inf.mpr ⟨d.2, (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) d).mp
        (cartan_le_borel _ _ hd)⟩
    let φ : cartan (Q : Subgroup L) t₀ →* MulAut A :=
      MonoidHom.mk' (fun d => ρ ⟨(((d : cartan (Q : Subgroup L) t₀) : L) : G),
        hBN (hcart d d.2)⟩) (fun d d' => by rw [← map_mul]; rfl)
    have hle : H ≤ φ.range := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨hbL, hbT⟩ := mem_inf.mp (mem_subgroupOf.mp hb)
      have hbB : (⟨(b : G), hbL⟩ : L) ∈ borel (Q : Subgroup L) :=
        (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) _).mpr hbT
      rw [← hc.sup_eq] at hbB
      have hbB' : (⟨(b : G), hbL⟩ : L) ∈
          ((Q : Subgroup L) : Set L) * (cartan (Q : Subgroup L) t₀ : Set L) := by
        rw [← coe_mul_of_right_le_normalizer_left _ _ (cartan_le_borel _ _)]
        exact hbB
      obtain ⟨p, hp, d, hd, hpd⟩ := Set.mem_mul.mp hbB'
      have hpT : ((p : L) : G) ∈ szT₁ L T := (hmemQ p).mp hp
      have hpN : ((p : L) : G) ∈ N := hBN (mem_inf.mpr ⟨p.2, Subgroup.le_normalizer hpT⟩)
      have hp1 : ρ ⟨(p : G), hpN⟩ = 1 := MulEquiv.ext fun a => Subtype.ext (by
        rw [hρa, MulAut.one_apply]
        have := mem_centralizer_iff.mp (hAC a.2) _ (mem_sup_left hpT)
        rw [this, mul_inv_cancel_right])
      refine ⟨⟨d, hd⟩, ?_⟩
      have hbpd : b = ⟨(p : G), hpN⟩ * ⟨((d : L) : G), hBN (hcart d hd)⟩ := Subtype.ext (by
        have := congrArg Subtype.val hpd
        simpa using this.symm)
      rw [hbpd, map_mul, hp1, one_mul]
      rfl
    have := hc.isCyclic
    exact isCyclic_of_le_isCyclic
      (isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective) hle
  have hHreg : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃! x : H, (x : MulAut A) u = v := by
    intro u v hu hv
    have huA₁ : ((u : A) : G) ∈ A₁ := mem_subgroupOf.mp u.2
    have hvA₁ : ((v : A) : G) ∈ A₁ := mem_subgroupOf.mp v.2
    have hu1 : ((u : A) : G) ≠ 1 := fun h1 => hu (Subtype.ext (Subtype.ext h1))
    have hv1 : ((v : A) : G) ≠ 1 := fun h1 => hv (Subtype.ext (Subtype.ext h1))
    obtain ⟨d, hdL, hdv, -, hdT, -⟩ := h.exists_cartan_conj_of_card_sylow hS2 huA₁ hu1 hvA₁ hv1
    have hdB : d ∈ B := mem_inf.mpr ⟨hdL, hdT⟩
    have hdB' : d⁻¹ ∈ B := inv_mem hdB
    refine ⟨⟨ρ ⟨d⁻¹, hBN hdB'⟩, ⟨d⁻¹, hBN hdB'⟩, mem_subgroupOf.mpr hdB', rfl⟩, ?_, ?_⟩
    · apply Subtype.ext
      change (((ρ ⟨d⁻¹, hBN hdB'⟩) (u : A) : A) : G) = ((v : A) : G)
      rw [hρa, hdv]
      group
    · rintro ⟨_, ⟨b, hb, rfl⟩⟩ hbuv
      obtain ⟨hbL, -⟩ := mem_inf.mp (mem_subgroupOf.mp hb)
      have hbuv' : (b : G) * ((u : A) : G) * (b : G)⁻¹ = ((v : A) : G) := by
        have := congrArg Subtype.val hbuv
        rw [hρa] at this
        exact this
      have hcA₁ : d * b ∈ centralizer (A₁ : Set G) := by
        refine h.mem_centralizer_szA₁_of_commute_of_card_sylow hS2 (mul_mem hdL hbL) huA₁ hu1 ?_
        have e1 : d * ((b : G) * ((u : A) : G) * (b : G)⁻¹) * d⁻¹ = ((u : A) : G) := by
          rw [hbuv', hdv]
          group
        calc d * b * ((u : A) : G) = d * ((b : G) * ((u : A) : G) * (b : G)⁻¹) * d⁻¹ * (d * b) := by
              group
          _ = ((u : A) : G) * (d * b) := by rw [e1]
      have hcA : d * b ∈ centralizer (A : Set G) :=
        h.mem_centralizer_szA_of_mem_centralizer_szA₁ (mul_mem hdL hbL) hcA₁
      have hρc : ρ (⟨d, hBN hdB⟩ * b) = 1 := MulEquiv.ext fun a => Subtype.ext (by
        rw [hρa, MulAut.one_apply]
        change d * b * (a : G) * (d * b)⁻¹ = a
        rw [← mem_centralizer_iff.mp hcA a a.2, mul_inv_cancel_right])
      apply Subtype.ext
      change ρ b = ρ ⟨d⁻¹, hBN hdB'⟩
      rw [map_mul] at hρc
      rw [eq_inv_of_mul_eq_one_right hρc, ← map_inv]
      rfl
  have hcat : NonabelianSimpleNormalCatalog (orbitImage M t') := by
    intro S hSN hSn hs hnab
    let φ : N →* Equiv.Perm (Orbit M t') :=
      (MulAction.toPermHom M (Orbit M t')).comp ρ.rangeRestrict
    have hrange : φ.range = orbitImage M t' := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ρ.rangeRestrict_surjective,
        ← MonoidHom.range_eq_map]
    exact catalog_of_le_range_of_kProper h.setting.2.2.1
      (h.normalizer_szA_ne_top_of_card_sylow hS2) φ (hSN.trans hrange.ge) hs hnab
  have key := regularNormal_or_projective_of_affineModel hV hf hUcard hUt hMU hHM hHt hHn hHc
    hHreg hcat
  obtain ⟨e, he⟩ := h.exists_orbitEquiv_of_card_sylow hS2
  rw [he]
  rcases key with hreg | ⟨hf3, hproj⟩
  · exact Or.inl (hreg.map_permCongr e)
  · exact Or.inr ⟨hf3, hproj.map_permCongr e⟩

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
