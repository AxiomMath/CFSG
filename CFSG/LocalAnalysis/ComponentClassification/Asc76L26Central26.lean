module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Red26

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

theorem IsSzOrU3.isSimpleGroup {X : Type*} [Group X] [Finite X] (h : IsSzOrU3 X) :
    IsSimpleGroup X := by
  apply CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
  rcases h with ⟨a, ha, e⟩ | ⟨f, hf, e⟩
  · exact Or.inr (Or.inr ⟨a, ha, e⟩)
  · exact Or.inr (Or.inl ⟨f, hf, e⟩)

theorem commutator_eq_top_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ¬ IsMulCommutative X) : commutator X = ⊤ := by
  rcases (commutator_normal (⊤ : Subgroup X) (⊤ : Subgroup X)).eq_bot_or_eq_top with h | h
  · exfalso
    apply hX
    refine ⟨⟨fun a b => ?_⟩⟩
    have hc : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup X), ⊤⁆ := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}
  {R : Subgroup G}

theorem false_of_central_mem (h : Hyp26 S 𝒯 R) (hO : CFSG.Assembly.oddCore G = ⊥) {u : G}
    (hu : u ∈ center G) (hu2 : orderOf u = 2) (huR : u ∉ R)
    (huniq : ∀ R' ∈ 𝒯, IsBig R' → R' = R) (hRN : R ⊓ zpowers u = ⊥) [(zpowers u).Normal]
    (hsyl : IsSylowOf 2 (R.map (QuotientGroup.mk' (zpowers u)))
      (normalClosure ((R.map (QuotientGroup.mk' (zpowers u)) : Subgroup (G ⧸ zpowers u)) :
        Set (G ⧸ zpowers u))))
    (hsz : IsSzOrU3
      (↥(normalClosure ((R.map (QuotientGroup.mk' (zpowers u)) : Subgroup (G ⧸ zpowers u)) :
        Set (G ⧸ zpowers u))) ⧸
        CFSG.Assembly.oddCore
          ↥(normalClosure ((R.map (QuotientGroup.mk' (zpowers u)) : Subgroup (G ⧸ zpowers u)) :
            Set (G ⧸ zpowers u)))))
    (hshape : SylowShape (R.map (QuotientGroup.mk' (zpowers u))))
    (huL : u ∈ normalClosure (R : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := zpowers u with hNdef
  have hNc : N ≤ center G := zpowers_le.mpr hu
  set π := QuotientGroup.mk' N with hπ
  set L := normalClosure (R : Set G) with hLdef
  rw [normalClosure_map_mk N R] at hsyl hsz
  have hLn : L.Normal := normalClosure_normal
  have hRL : R ≤ L := subset_normalClosure
  have hRS : R ≤ S := h.le R h.mem
  have hNL : N ≤ L := zpowers_le.mpr huL
  have hN2 : Nat.card N = 2 := by rw [Nat.card_zpowers, hu2]
  have huu : u * u = 1 := by rw [← sq, ← hu2]; exact pow_orderOf_eq_one u
  have hucomm : ∀ g : G, u * g = g * u := fun g => (mem_center_iff.mp hu g).symm
  have hNS : N ≤ S := by
    have h2 : IsPGroup 2 N := IsPGroup.of_card (hN2.trans (pow_one 2).symm)
    have h3 : IsPGroup 2 (N ⊔ S : Subgroup G) := h2.to_sup_of_normal_left h.sylow.isPGroup
    exact (h.sylow.eq_of_le le_sup_right le_top h3) ▸ le_sup_left
  have hOq : CFSG.oddCore (G ⧸ N) = ⊥ :=
    AschbacherStrongEmbedding.oddCore_central_quotient_eq_bot hO N hNc hN2
  have hLbn : (L.map π).Normal := hLn.map π (QuotientGroup.mk'_surjective N)
  have hOLb : CFSG.Assembly.oddCore (L.map π) = ⊥ :=
    AschbacherStrongEmbedding.Lemma34.oddCore_eq_bot_of_normal' hOq (L.map π)
  have hSzLb : IsSzOrU3 (L.map π) := IsSzOrU3.of_mulEquiv hsz
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hOLb).symm)
  have hLbnc : ¬ IsMulCommutative (L.map π) := by
    intro hc
    apply hshape.not_comm
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hRLb : R.map π ≤ L.map π := map_mono hRL
    have := congrArg Subtype.val
      (mul_comm' (⟨(a : G ⧸ N), hRLb a.2⟩ : L.map π) ⟨(b : G ⧸ N), hRLb b.2⟩)
    exact this
  have : IsSimpleGroup (L.map π) := IsSzOrU3.isSimpleGroup hSzLb
  have hLbperf : commutator (L.map π) = ⊤ := commutator_eq_top_of_simple hLbnc
  set D := ⁅L, L⁆ with hDdef
  have hDmap : D.map π = L.map π := by
    rw [hDdef, map_commutator, ← (L.map π).map_subtype_commutator, hLbperf,
      ← MonoidHom.range_eq_map, range_subtype]
  have hLDN : L ≤ D ⊔ N := by
    intro x hx
    have hmem : π x ∈ D.map π := hDmap ▸ mem_map_of_mem π hx
    obtain ⟨y, hy, hyx⟩ := hmem
    have h1 : y⁻¹ * x ∈ N := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      exact hyx
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact mul_mem_sup hy h1
  have hSL : IsSylowOf 2 (S ⊓ L) L :=
    h.sylow.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hLn])
  have hcardL : Nat.card L = Nat.card (L.map π) * 2 := by
    have := Asc76X.card_map_mul_card_inf_ker π L
    rw [QuotientGroup.ker_mk', inf_eq_left.mpr hNL, hN2] at this
    exact this.symm
  have hcardR : Nat.card R = Nat.card (R.map π) := Nat.card_congr (equivMapMk hRN).toEquiv
  have hSLcard : Nat.card (S ⊓ L : Subgroup G) = 2 * Nat.card R := by
    rw [hSL.card_eq, hcardR, hsyl.card_eq, hcardL,
      Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_one, mul_comm]
  have huD : u ∉ D := by
    intro huD
    obtain ⟨Q, hQ⟩ := hSL.exists_sylow_eq_subgroupOf
    have hRSL : R ≤ S ⊓ L := le_inf hRS hRL
    have hRi : ((R.subgroupOf L).subgroupOf (Q : Subgroup L)).index = 2 := by
      change (R.subgroupOf L).relIndex (Q : Subgroup L) = 2
      rw [hQ, relIndex_subgroupOf inf_le_right]
      have hmul := relIndex_mul_card R (S ⊓ L)
      rw [inf_eq_left.mpr hRSL, hSLcard] at hmul
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
    have huX : (⟨u, huL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hucomm g).symm
    have huRX : (⟨u, huL⟩ : L) ∉ R.subgroupOf L := by
      rw [mem_subgroupOf]
      exact huR
    have hu2X : (⟨u, huL⟩ : L) ^ 2 = 1 := Subtype.ext (by simp [sq, huu])
    apply not_mem_commutator_of_index_two Q.not_dvd_index hRi huX huRX hu2X
    rw [hDdef, ← L.map_subtype_commutator] at huD
    obtain ⟨y, hy, hyu⟩ := huD
    have : y = ⟨u, huL⟩ := Subtype.ext hyu
    rwa [← this]
  have hDN : D ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxD, hxN⟩ := mem_inf.mp hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxN
    rw [mem_bot]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · rw [hm, zpow_mul, zpow_two, huu, one_zpow]
    · exfalso
      apply huD
      rw [hm, zpow_add_one, zpow_mul, zpow_two, huu, one_zpow, one_mul] at hxD
      exact hxD
  have heD : D ≃* L.map π := (equivMapMk hDN).trans (MulEquiv.subgroupCongr hDmap)
  have hSzD : IsSzOrU3 D := IsSzOrU3.of_mulEquiv hSzLb heD
  have : IsSimpleGroup D := IsSzOrU3.isSimpleGroup hSzD
  have hDperf : commutator D = ⊤ := commutator_eq_top_of_simple fun hc => hLbnc
    ⟨⟨fun a b => heD.symm.injective (by
      rw [map_mul, map_mul]
      exact mul_comm' (heD.symm a) (heD.symm b))⟩⟩
  set P' := S ⊓ D with hP'def
  have hP'syl : IsSylowOf 2 P' D :=
    h.sylow.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr inferInstance])
  have hP'card : Nat.card P' = Nat.card R := by
    rw [hP'syl.card_eq, hcardR, hsyl.card_eq, Nat.card_congr heD.toEquiv]
  have hP'N : P' ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N inf_le_right).trans hDN.le)
  have hRP'N : R ≤ P' ⊔ N := by
    intro r hr
    obtain ⟨y, hy, n, hn, rfl⟩ := mem_sup_of_normal_right.mp (hLDN (hRL hr))
    have hyS : y ∈ S := by
      have : y = (y * n) * n⁻¹ := by group
      rw [this]
      exact S.mul_mem (hRS hr) (S.inv_mem (hNS hn))
    exact mul_mem_sup (mem_inf.mpr ⟨hyS, hy⟩) hn
  have hRw : ∀ w : G, w ∈ normalizer (P' : Set G) → rightConjugate R w = R := by
    intro w hwN
    apply huniq _ (h.conj w ?_) (h.big.rightConjugate w)
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    obtain ⟨y, hy, n, hn, hyn⟩ := mem_sup_of_normal_right.mp (hRP'N hx)
    have hy' : w⁻¹ * y * w ∈ P' := by
      have := (mem_normalizer_iff.mp (inv_mem hwN) y).mp hy
      simpa using this
    have hnc : w⁻¹ * n * w = n := by
      have := mem_center_iff.mp (hNc hn) w
      calc w⁻¹ * n * w = w⁻¹ * (n * w) := by group
        _ = w⁻¹ * (w * n) := by rw [this]
        _ = n := by group
    have : x = (w⁻¹ * y * w) * n := by
      calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
        _ = w⁻¹ * (y * n) * w := by rw [hyn]
        _ = (w⁻¹ * y * w) * (w⁻¹ * n * w) := by group
        _ = (w⁻¹ * y * w) * n := by rw [hnc]
    rw [this]
    exact S.mul_mem (mem_inf.mp hy').1 (hNS hn)
  have hP'R : ∀ x ∈ P', x ∈ R ∨ x * u ∈ R := by
    intro x hx
    have hle : R.map π ≤ P'.map π := by
      rw [map_le_iff_le_comap, comap_map_mk]
      exact hRP'N
    have heq : R.map π = P'.map π := by
      refine eq_of_le_of_card_ge hle ?_
      rw [← Nat.card_congr (equivMapMk hRN).toEquiv, ← Nat.card_congr (equivMapMk hP'N).toEquiv,
        hP'card]
    have hmem : π x ∈ R.map π := heq ▸ mem_map_of_mem π hx
    obtain ⟨r, hr, hrx⟩ := hmem
    have h1 : r⁻¹ * x ∈ N := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrx
      exact hrx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, zpow_two, huu, one_zpow] at hk
      have : x = r := by
        calc x = r * (r⁻¹ * x) := by group
          _ = r := by rw [← hk, mul_one]
      rw [this]
      exact hr
    · right
      rw [hm, zpow_add_one, zpow_mul, zpow_two, huu, one_zpow, one_mul] at hk
      have : x * u = r := by
        calc x * u = r * (r⁻¹ * x) * u := by group
          _ = r * u * u := by rw [← hk]
          _ = r := by rw [mul_assoc, huu, mul_one]
      rw [this]
      exact hr
  obtain ⟨T₁, hT₁⟩ := hP'syl.exists_sylow_eq_subgroupOf
  have hfoc := Subgroup.commutator_inf_eq_focalSubgroup T₁
  rw [hDperf, top_inf_eq] at hfoc
  have hT₁R : (T₁ : Subgroup D) ≤ R.subgroupOf D := by
    rw [hfoc, focalSubgroup_def, closure_le]
    rintro g ⟨hgT, x, hxT, w, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    by_cases hx1 : x = 1
    · rw [hx1, commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact one_mem _
    have hwN : w ∈ normalizer ((T₁ : Subgroup D) : Set D) := by
      by_contra hwN
      have hne : (MulAut.conj w⁻¹) • T₁ ≠ T₁ := by
        intro heq
        apply hwN
        have : w⁻¹ ∈ normalizer ((T₁ : Subgroup D) : Set D) :=
          Sylow.smul_eq_iff_mem_normalizer.mp (by rw [Sylow.smul_def]; exact heq)
        simpa using inv_mem this
      have hinf := Asc76X.benderFacts.sylow_inf D hSzD _ _ hne
      have hx' : x⁻¹ ∈ ((MulAut.conj w⁻¹ • T₁ : Sylow 2 D) : Subgroup D) ⊓ (T₁ : Subgroup D) := by
        refine mem_inf.mpr ⟨?_, inv_mem hxT⟩
        have hα : (MulAut.conj w⁻¹)⁻¹ = MulAut.conj w := by rw [← map_inv, inv_inv]
        rw [Bender.Omega.mem_smul_iff, hα, MulAut.conj_apply]
        have e : w * x⁻¹ * w⁻¹ = x⁻¹ * ⁅x, w⁆ := by rw [commutatorElement_def]; group
        rw [e]
        exact mul_mem (inv_mem hxT) hgT
      rw [hinf, mem_bot, inv_eq_one] at hx'
      exact hx1 hx'
    have hwN' : (w : G) ∈ normalizer (P' : Set G) :=
      BenderExt.Bridge.mem_normalizer_subgroupOf (inf_le_right : P' ≤ D) w (hT₁ ▸ hwN)
    have hRw' := hRw w hwN'
    have hRwinv : ∀ y ∈ R, (w : G) * y * (w : G)⁻¹ ∈ R := by
      intro y hy
      have : y ∈ rightConjugate R w := hRw'.symm ▸ hy
      rwa [mem_rightConjugate_iff] at this
    have hxP' : (x : G) ∈ P' := by
      have := hxT
      rw [hT₁, mem_subgroupOf] at this
      exact this
    have hcoe : ((⁅x, w⁆ : D) : G) = (x : G) * w * (x : G)⁻¹ * (w : G)⁻¹ := by
      rw [commutatorElement_def]
      rfl
    rw [hcoe]
    rcases hP'R _ hxP' with hxR | hxuR
    · have e : (x : G) * w * (x : G)⁻¹ * (w : G)⁻¹ = x * ((w : G) * (x : G)⁻¹ * (w : G)⁻¹) := by
        group
      rw [e]
      exact R.mul_mem hxR (hRwinv _ (R.inv_mem hxR))
    · have hwu := hucomm (w : G)
      have e : (x : G) * w * (x : G)⁻¹ * (w : G)⁻¹ =
          ((x : G) * u) * ((w : G) * ((x : G) * u)⁻¹ * (w : G)⁻¹) := by
        calc (x : G) * w * (x : G)⁻¹ * (w : G)⁻¹ =
            (x : G) * (u * u) * w * (x : G)⁻¹ * (w : G)⁻¹ := by rw [huu, mul_one]
          _ = (x : G) * u * (u * w) * (x : G)⁻¹ * (w : G)⁻¹ := by group
          _ = (x : G) * u * (w * u) * (x : G)⁻¹ * (w : G)⁻¹ := by rw [hwu]
          _ = ((x : G) * u) * ((w : G) * ((x : G) * u)⁻¹ * (w : G)⁻¹) := by
            rw [mul_inv_rev, show u⁻¹ = u from inv_eq_of_mul_eq_one_right huu]
            group
      rw [e]
      exact R.mul_mem hxuR (hRwinv _ (R.inv_mem hxuR))
  have hP'R' : P' ≤ R := by
    intro x hx
    have : (⟨x, (mem_inf.mp hx).2⟩ : D) ∈ (T₁ : Subgroup D) := by
      rw [hT₁, mem_subgroupOf]
      exact hx
    exact mem_subgroupOf.mp (hT₁R this)
  have hRP' : P' = R := eq_of_le_of_card_ge hP'R' (by rw [hP'card])
  apply huD
  have hDn : D.Normal := inferInstance
  exact normalClosure_le_normal (hRP' ▸ inf_le_right) huL

theorem concl26_of_central (IH : Statement26 (Nat.card G - 1)) (h : Hyp26 S 𝒯 R)
    (hO : CFSG.Assembly.oddCore G = ⊥) {u : G} (hu : u ∈ center G) (hu2 : orderOf u = 2) :
    Concl26 𝒯 R := by
  by_cases hH : fusionGen (memberSet 𝒯) = ⊤
  · exact Or.inl hH
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := zpowers u with hNdef
  have hNn : N.Normal := normal_of_le_center (zpowers_le.mpr hu)
  have hΓS : memberSet 𝒯 ⊆ S := memberSet_subset h.toHypCore
  have huΓ : u ∉ memberSet 𝒯 := fun huΓ =>
    hH (fusionGen_eq_top_of_mem_center h.sylow h.closed hΓS huΓ hu)
  have huu : u * u = 1 := by rw [← sq, ← hu2]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h' => by rw [h', orderOf_one] at hu2; omega
  have huR : u ∉ R := fun h' => huΓ (mem_memberSet h.mem h' hu1)
  have hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥ := by
    intro T hT
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyT, hyu⟩ := mem_inf.mp hy
    rw [mem_bot]
    by_contra hy1
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hyu
    have hu' : u ∈ T := by
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
      · exfalso
        apply hy1
        rw [hk, zpow_mul, zpow_two, huu, one_zpow]
      · have : u ^ n = u := by
          rw [hk, zpow_add, zpow_mul, zpow_two, huu, one_zpow, one_mul, zpow_one]
        rw [this] at hyT
        exact hyT
    exact huΓ (mem_memberSet hT hu' hu1)
  obtain ⟨E, hER, hE4, -⟩ := exists_four_le h.big.1
  obtain ⟨v, hvE, hv1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left (fun h' => by
    rw [h', Subgroup.card_bot] at hE4; omega)
  have hvΓ := mem_memberSet h.mem (hER hvE) hv1
  have hNH : N ≤ fusionGen (memberSet 𝒯) := by
    rw [zpowers_le]
    exact centralizer_le_fusionGen hvΓ
      (mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hu v).symm)
  have hcard : Nat.card (G ⧸ N) ≤ Nat.card G - 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [Nat.card_zpowers, hu2] at h1
    have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    omega
  rcases IH _ hcard _ _ _ (h.quot hN) with htop | ⟨huniq', hsyl', hsz', hshape'⟩
  · exact absurd (fusionGen_eq_top_of_quot h.toHypCore hN hNH htop) hH
  have huniq : ∀ R' ∈ 𝒯, IsBig R' → R' = R := by
    intro R' hR' hbig'
    by_contra hne
    have hc := h.comm R' hR' R h.mem hne
    have h1 : R'.map (QuotientGroup.mk' N) = R.map (QuotientGroup.mk' N) :=
      huniq' _ ⟨R', hR', rfl⟩ (hbig'.of_mulEquiv (equivMapMk (hN R' hR')))
    apply hshape'.not_comm
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    obtain ⟨r, hr, hrx⟩ := x.2
    have hy : (y : G ⧸ N) ∈ R'.map (QuotientGroup.mk' N) := by rw [h1]; exact y.2
    obtain ⟨r', hr', hry⟩ := hy
    change (x : G ⧸ N) * y = y * x
    rw [← hrx, ← hry, ← map_mul, ← map_mul, commute_of_commutator_eq_bot hc hr' hr]
  have hRN := hN R h.mem
  by_cases huL : u ∈ normalClosure (R : Set G)
  · exact absurd (false_of_central_mem h hO hu hu2 huR huniq hRN hsyl' hsz' hshape' huL) id
  · have hNL : N ⊓ normalClosure (R : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxN, hxL⟩ := mem_inf.mp hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxN
      rw [mem_bot]
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
      · rw [hm, zpow_mul, zpow_two, huu, one_zpow]
      · exfalso
        apply huL
        rw [hm, zpow_add_one, zpow_mul, zpow_two, huu, one_zpow, one_mul] at hxL
        exact hxL
    have hodd : Odd (Nat.card (N ⊓ normalClosure (R : Set G) : Subgroup G)) := by
      rw [hNL, card_bot]
      exact odd_one
    exact ⟨huniq, concl26_lift hRN hodd hsyl' hsz' hshape'⟩

end CFSG.ComponentClassification.Asc76.L26
