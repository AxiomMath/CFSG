module

public import CFSG.LargeExtraspecial.S4Weak
public import CFSG.LargeExtraspecial.S4Lin
public import CFSG.LargeExtraspecial.S4Restrict
public import CFSG.LargeExtraspecial.S4Span

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_clSub_QG_inf_Qa (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hcard : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1)) :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = S.width := by
  have hz : S.z ∈ S.QG ⊓ S.Qa g := ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl haQ hne⟩
  have h1 := S.card_clPre (S.clSub (S.QG ⊓ S.Qa g))
  rw [S.clPre_clSub inf_le_left hz, hcard, S.card_submodule, pow_succ, mul_comm] at h1
  exact (Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by norm_num) h1)).symm

theorem lemma_4_3_core (H : Hyp4 S g) (H11 : Cons311 S g) (h : S.M) {D : Subgroup S.O}
    (hD : IsPGroup 2 D) (hDX : D ≤ S.Lbar g ⊔ S.Lbar ((h : G) * g))
    (hXD : S.Lbar g ⊔ S.Lbar ((h : G) * g) ≤ normalizer (D : Set S.O))
    (hLD : ¬ S.Lbar g ≤ D)
    (hidx : ∀ x ∈ S.Lbar g, ∀ y ∈ S.Lbar g, x ∉ D → y ∉ D → x * y ∈ D) :
    (h : G) * g * S.z * ((h : G) * g)⁻¹ ∈ S.Qa g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := g * S.z * g⁻¹ with ha
  set b := (h : G) * g * S.z * ((h : G) * g)⁻¹ with hb
  have haQ : a ∈ S.QG := H.conj_mem
  have hbQ : b ∈ S.QG := conj_mem_QG' S h.2 haQ
  have hw : WeaklyClosed S g := H11.weaklyClosed
  have hXM : S.Lbar g ⊔ S.Lbar ((h : G) * g) ≤ S.Mbar :=
    sup_le (S.Lbar_le_Mbar _) (S.Lbar_le_Mbar _)
  have hDN1 : D ≤ normalizer (S.Lbar g : Set S.O) := by
    have hT := (isPGroup_Lbar S haQ).to_sup_of_normal_right' hD (le_sup_left.trans hXD)
    exact le_sup_right.trans (le_normalizer_of_weaklyClosed hw hT
      (sup_le (le_sup_left.trans hXM) (hDX.trans hXM)) le_sup_left)
  have hDN2 : D ≤ normalizer (S.Lbar ((h : G) * g) : Set S.O) := by
    have hT := (isPGroup_Lbar S hbQ).to_sup_of_normal_right' hD (le_sup_right.trans hXD)
    exact le_sup_right.trans (le_normalizer_Lbar_mul hw h hT
      (sup_le (le_sup_right.trans hXM) (hDX.trans hXM)) le_sup_left)
  have hDb : ∀ d ∈ D, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) = S.cl b := fun d hd =>
    fix_of_mem_normalizer_mul H h (hDN2 hd)
  by_contra hbQa
  obtain ⟨t, htL, htD⟩ := Set.not_subset.mp hLD
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ htL
  have hact : ∀ s ∈ S.Lbar g, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) = S.cl b ∨
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) := by
    intro s hs
    by_cases hsD : s ∈ D
    · exact Or.inl (hDb s hsD)
    · right
      have hts := hidx t htL s hs htD hsD
      have e : s = t * (t * s) := by rw [← mul_assoc, htt, one_mul]
      rw [e, coe_mul_apply, hDb _ hts]
  set w := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) - S.cl b with hwdef
  have hwfix : w ∈ fixSub S (S.Lbar g) := by
    intro s hs
    have hst : s * t = t * s := Lbar_comm S haQ hs htL
    have e1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b)) =
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b)) := by
      rw [← coe_mul_apply, hst, coe_mul_apply]
    rw [hwdef, map_sub, e1]
    rcases hact s hs with h1 | h1
    · rw [h1]
    · rw [h1, ← coe_mul_apply, htt]
      change S.cl b - (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) = _
      rw [OrthoF2.vec_sub, OrthoF2.vec_sub, add_comm]
  have hw0 : w ≠ 0 := by
    intro hw0
    have htb : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) = S.cl b := sub_eq_zero.mp hw0
    have hbfix : S.cl b ∈ fixSub S (S.Lbar g) := fun s hs => by
      rcases hact s hs with h1 | h1
      · exact h1
      · rw [h1, htb]
    rw [H.fixSub_eq, mem_span_cl_iff] at hbfix
    rcases hbfix with h0 | h1
    · exact cl_conj_z_ne_zero S hbQ (conj_ne_z' S h.2 H.conj_ne) h0
    · rcases (S.cl_eq_cl_iff haQ hbQ).mp h1.symm with h2 | h2
      · exact hbQa (h2 ▸ (S.conjBy g).z_mem_QG)
      · exact hbQa (h2 ▸ mul_mem (S.conjBy g).z_mem_QG
          (S.z_mem_Qa_of_mem_QG rfl haQ H.conj_ne))
  have hwa : w = S.cl a := by
    rw [H.fixSub_eq, mem_span_cl_iff] at hwfix
    exact hwfix.resolve_left hw0
  have hLb : ∀ s ∈ S.Lbar g, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) - S.cl b ∈
      (ZMod 2) ∙ S.cl a := by
    intro s hs
    rcases hact s hs with h1 | h1
    · rw [h1, sub_self]
      exact Submodule.zero_mem _
    · rw [h1, ← hwdef, hwa]
      exact Submodule.mem_span_singleton_self _
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set U := P ⊔ (ZMod 2) ∙ S.cl b with hU
  have hLP : ∀ s ∈ S.Lbar g, ∀ v ∈ P, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (ZMod 2) ∙ S.cl a := by
    intro s hs v hv
    obtain ⟨x, hx, -, rfl⟩ := S.mem_clSub_iff.mp hv
    exact Lbar_apply_sub_mem_span haQ hx hs
  have hLU : ∀ s ∈ S.Lbar g, ∀ v ∈ U, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (ZMod 2) ∙ S.cl a := by
    intro s hs v hv
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have e : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + c • S.cl b) - (p + c • S.cl b) =
        ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) +
          c • ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) - S.cl b) := by
      rw [map_add, map_smul, smul_sub]
      abel
    rw [e]
    exact add_mem (hLP s hs p hp) (Submodule.smul_mem _ c (hLb s hs))
  have haP : S.cl a ∈ P := S.cl_mem_clSub ⟨haQ, (S.conjBy g).z_mem_QG⟩ haQ
  have haU : S.cl a ∈ U := Submodule.mem_sup_left haP
  have hUinv : ∀ (x : S.Lbar g) u, u ∈ U →
      ((S.O.subtype.comp (S.Lbar g).subtype) x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := by
    intro x u hu
    have h1 := hLU x x.2 u hu
    have : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
        (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) + u := by abel
    change ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U
    rw [this]
    exact add_mem ((Submodule.span_singleton_le_iff_mem _ _).mpr haU h1) hu
  set ψ := restrictHom (S.O.subtype.comp (S.Lbar g).subtype) U hUinv with hψ
  have hψc : ∀ x (u : U), ψ x u - u ∈ (ZMod 2) ∙ (⟨S.cl a, haU⟩ : U) := by
    intro x u
    rw [mem_span_singleton_subtype]
    exact hLU x x.2 u u.2
  have hcardL : Nat.card (S.Lbar g) ≤ 2 ^ (S.width - 1) := H11.card_Lbar.le
  have key := finrank_le_of_transvections (isPGroup_Lbar S haQ) ψ _ hψc hcardL
  have hfix1 : finrank (ZMod 2) (fixSpaceOf ψ.range) ≤ 1 := by
    have hle : fixSpaceOf ψ.range ≤ (ZMod 2) ∙ (⟨S.cl a, haU⟩ : U) := by
      intro u hu
      rw [mem_fixSpaceOf_range] at hu
      rw [mem_span_singleton_subtype, ← H.fixSub_eq]
      intro s hs
      have := congrArg Subtype.val (hu ⟨s, hs⟩)
      exact this
    calc finrank (ZMod 2) (fixSpaceOf ψ.range) ≤
          finrank (ZMod 2) ((ZMod 2) ∙ (⟨S.cl a, haU⟩ : U)) := Submodule.finrank_mono hle
      _ = 1 := finrank_span_singleton fun h0 =>
          cl_conj_z_ne_zero S haQ H.conj_ne (congrArg Subtype.val h0)
  have hbP : S.cl b ∉ P := by
    intro hbP
    obtain ⟨x, hx, hxQ, hxb⟩ := S.mem_clSub_iff.mp hbP
    rcases (S.cl_eq_cl_iff hxQ hbQ).mp hxb with h1 | h1
    · exact hbQa (h1 ▸ hx.2)
    · exact hbQa (h1 ▸ mul_mem hx.2 (S.z_mem_Qa_of_mem_QG rfl haQ H.conj_ne))
  have hPdim := finrank_clSub_QG_inf_Qa haQ H.conj_ne H11.card_QG_inf_Qa
  have hinf : P ⊓ (ZMod 2) ∙ S.cl b = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvP, hvb⟩ := Submodule.mem_inf.mp hv
    rcases mem_span_cl_iff.mp hvb with h0 | h1
    · exact h0 ▸ Submodule.zero_mem _
    · exact absurd (h1 ▸ hvP) hbP
  have hUdim : finrank (ZMod 2) U = S.width + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq P ((ZMod 2) ∙ S.cl b)
    rw [hinf, finrank_bot, add_zero, hPdim,
      finrank_span_singleton (cl_conj_z_ne_zero S hbQ (conj_ne_z' S h.2 H.conj_ne))] at h1
    exact h1
  have hn := H.two_lt_width
  omega

theorem lemma_4_3 (H : Hyp4 S g) (H11 : NoA2 S g → Cons311 S g) (h : S.M)
    (hX : Nonempty ((↥(S.Lbar g ⊔ S.Lbar ((h : G) * g)) ⧸
      CFSG.pCore 2 ↥(S.Lbar g ⊔ S.Lbar ((h : G) * g))) ≃* Equiv.Perm (Fin 3))) :
    (h : G) * g * S.z * ((h : G) * g)⁻¹ ∈ S.Qa g ∨
      ∃ α : S.M, (α : G) ∈ S.La g ∧ (α : G) ∉ S.QG ∧ S.IsTypeAOn α 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hno : NoA2 S g
  swap
  · right
    unfold NoA2 at hno
    push Not at hno
    obtain ⟨α, h1, h2, h3⟩ := hno
    exact ⟨α, h1, h2, h3⟩
  left
  obtain ⟨e⟩ := hX
  set X := S.Lbar g ⊔ S.Lbar ((h : G) * g) with hXdef
  set P := CFSG.pCore 2 ↥X with hPdef
  set D := P.map X.subtype with hDdef
  have haQ : g * S.z * g⁻¹ ∈ S.QG := H.conj_mem
  have hbQ := conj_mem_QG' S h.2 haQ
  have hcard6 : Nat.card (↥X ⧸ P) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hD : IsPGroup 2 D := CFSG.pCore_isPGroup.map _
  have hDX : D ≤ X := map_subtype_le _
  have hXD : X ≤ normalizer (D : Set S.O) := by
    have h1 := le_normalizer_map (H := P) X.subtype
    rw [normalizer_eq_top_iff.mpr CFSG.pCore_normal, ← MonoidHom.range_eq_map,
      range_subtype] at h1
    exact h1
  set φ : S.Lbar g →* ↥X ⧸ P :=
    (QuotientGroup.mk' P).comp (Subgroup.inclusion (le_sup_left : S.Lbar g ≤ X)) with hφ
  have hker : ∀ x : S.Lbar g, x ∈ φ.ker ↔ (x : S.O) ∈ D := by
    intro x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨_, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = Subgroup.inclusion (le_sup_left : S.Lbar g ≤ X) x := Subtype.ext hyx
      rwa [← this]
  have hrange2 : IsPGroup 2 φ.range :=
    (isPGroup_Lbar S haQ).of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hrange_dvd : Nat.card φ.range ∣ 6 := hcard6 ▸ Subgroup.card_subgroup_dvd_card _
  have : Finite (↥X ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard6]; norm_num)
  obtain ⟨k, hk⟩ := hrange2.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ k)).trans (hk ▸ hrange_dvd)
    omega
  have hLD : ¬ S.Lbar g ≤ D := by
    intro hLD
    have hX2 : IsPGroup 2 X := by
      have h1 := (isPGroup_Lbar S hbQ).to_sup_of_normal_right' hD (le_sup_right.trans hXD)
      have h2 : X ≤ S.Lbar ((h : G) * g) ⊔ D := sup_le (hLD.trans le_sup_right) le_sup_left
      exact h1.to_le h2
    have hQ2 : IsPGroup 2 (↥X ⧸ P) := hX2.to_quotient P
    obtain ⟨j, hj⟩ := hQ2.exists_card_eq
    rw [hcard6] at hj
    have : (2 : ℕ) ∣ 3 := by
      have h2 : 2 ^ j = 2 * 3 := hj.symm
      rcases j with _ | j
      · omega
      · rw [pow_succ] at h2
        have h3 : 2 ^ j = 3 := by omega
        rcases j with _ | j
        · omega
        · rw [pow_succ] at h3
          omega
    omega
  have hidx2 : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, hk]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
    · exfalso
      apply hLD
      intro x hx
      have h1 : Nat.card φ.range = 1 := by rw [hk, pow_zero]
      have hbot : φ.range = ⊥ := Subgroup.card_eq_one.mp h1
      have hx1 : φ ⟨x, hx⟩ = 1 :=
        (Subgroup.eq_bot_iff_forall _).mp hbot _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      exact (hker ⟨x, hx⟩).mp hx1
    · rfl
  refine lemma_4_3_core H (H11 hno) h hD hDX hXD hLD fun x hx y hy hxD hyD => ?_
  have h1 := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    ⟨fun h' => absurd ((hker _).mp h') hxD, fun h' => absurd ((hker _).mp h') hyD⟩
  exact (hker _).mp h1

end CFSG.LargeExtraspecial.S4
