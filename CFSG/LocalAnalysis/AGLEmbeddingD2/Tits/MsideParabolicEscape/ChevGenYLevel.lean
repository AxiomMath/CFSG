module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenOdd

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open scoped commutatorElement

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank CFSG.AGLEmbedding.ParabPrime

@[expose] def YData (S : Type) [Group S] (T : Subgroup S) : Prop :=
  ∃ Ps : Set (Subgroup S), (∀ P ∈ Ps, IsMinOverBorel ⊤ T P) ∧
    (⨆ P ∈ Ps, pElementSubgroup 2 P) = ⊤ ∧
    ∀ P ∈ Ps, ∃ a ∈ pElementSubgroup 2 P, ∃ g ∈ pElementSubgroup 2 P,
      a ^ 3 = 1 ∧ a ≠ 1 ∧ g * a * g⁻¹ = a⁻¹

section Iso

variable {S S' : Type} [Group S] [Group S']

theorem pElementSubgroup_map_equiv (e : S ≃* S') (P : Subgroup S) :
    pElementSubgroup 2 (P.map e.toMonoidHom) = (pElementSubgroup 2 P).map e.toMonoidHom := by
  unfold pElementSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ⟨hy, k, ?_⟩, rfl⟩
    rwa [orderOf_injective e.toMonoidHom e.injective y] at hk
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, k, by rwa [orderOf_injective e.toMonoidHom e.injective y]⟩

theorem isMinOverBorel_top_map (e : S ≃* S') {T P : Subgroup S} (h : IsMinOverBorel ⊤ T P) :
    IsMinOverBorel ⊤ (T.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨-, h1, h2⟩ := h
  have hN : (Subgroup.normalizer (T : Set S)).map e.toMonoidHom =
      Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup S') : Set S') :=
    Subgroup.map_equiv_normalizer_eq T e
  rw [top_inf_eq] at h1 h2
  refine ⟨le_top, ?_, ?_⟩
  · rw [top_inf_eq, ← hN]
    exact lt_of_le_of_ne (Subgroup.map_mono h1.le) fun heq =>
      h1.ne (Subgroup.map_injective e.injective heq)
  · intro Q hQ1 hQ2
    rw [top_inf_eq, ← hN] at hQ1 ⊢
    have h3 := Subgroup.comap_mono (f := e.toMonoidHom) hQ1
    have h4 := Subgroup.comap_mono (f := e.toMonoidHom) hQ2
    rw [Subgroup.comap_map_eq_self_of_injective e.injective] at h3 h4
    rcases h2 (Q.comap e.toMonoidHom) h3 h4 with h5 | h5
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Q, h5]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Q, h5]

theorem YData.map (e : S ≃* S') {T : Subgroup S} (h : YData S T) :
    YData S' (T.map e.toMonoidHom) := by
  obtain ⟨Ps, h1, h2, h3⟩ := h
  refine ⟨(fun P => P.map e.toMonoidHom) '' Ps, ?_, ?_, ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    exact isMinOverBorel_top_map e (h1 P hP)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ∈ (⨆ P ∈ Ps, pElementSubgroup 2 P) := by rw [h2]; trivial
    have hmap : (⨆ P ∈ Ps, pElementSubgroup 2 P).map e.toMonoidHom ≤
        ⨆ P ∈ ((fun P => P.map e.toMonoidHom) '' Ps), pElementSubgroup 2 P := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun P => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hP => ?_
      rw [← pElementSubgroup_map_equiv]
      exact le_iSup₂ (f := fun (Q : Subgroup S') (_ : Q ∈ ((fun P => P.map e.toMonoidHom) '' Ps)) =>
        pElementSubgroup 2 Q) (P.map e.toMonoidHom) ⟨P, hP, rfl⟩
    exact hmap ⟨y, hy, rfl⟩
  · rintro _ ⟨P, hP, rfl⟩
    obtain ⟨a, ha, g, hg, h3a, h1a, hinv⟩ := h3 P hP
    rw [pElementSubgroup_map_equiv]
    refine ⟨e a, ⟨a, ha, rfl⟩, e g, ⟨g, hg, rfl⟩, ?_, ?_, ?_⟩
    · rw [← map_pow, h3a, map_one]
    · intro h; exact h1a (e.injective (by rw [h, map_one]))
    · rw [← map_mul, ← map_inv, ← map_mul, hinv, map_inv]

end Iso


theorem exists_conj_of_sylowTwo {X : Type} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem YData.of_sylow {S : Type} [Group S] [Finite S] {T₀ T : Subgroup S}
    (h0 : IsSylowTwoOf T₀ ⊤) (hT : IsSylowTwoOf T ⊤) (h : YData S T₀) : YData S T := by
  obtain ⟨g, hg⟩ := exists_conj_of_sylowTwo h0 hT
  rw [← hg]
  exact h.map (MulAut.conj g)

theorem isSylowTwoOf_top_map_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hT.2.1.map _, ?_⟩
  have h2 : (T.map e.toMonoidHom).index = T.index := Subgroup.index_map_equiv _ e
  rw [show ((T.map e.toMonoidHom).subgroupOf ⊤).index = (T.map e.toMonoidHom).index from
    Subgroup.relIndex_top_right _, h2]
  have := hT.2.2
  rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right _] at this

theorem YData.of_mulEquiv_sylow {S S' : Type} [Group S] [Group S'] [Finite S] [Finite S']
    (e : S' ≃* S) {T₀ : Subgroup S} (h0 : IsSylowTwoOf T₀ ⊤) (h : YData S T₀)
    {T : Subgroup S'} (hT : IsSylowTwoOf T ⊤) : YData S' T := by
  have h1 : YData S (T.map e.toMonoidHom) :=
    YData.of_sylow h0 (isSylowTwoOf_top_map_equiv e hT) h
  have h2 := h1.map e.symm
  have h3 : (T.map e.toMonoidHom).map e.symm.toMonoidHom = T := by
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S' := by ext x; simp
    rw [this, Subgroup.map_id]
  rwa [h3] at h2

section Transport

variable {W : Type} [Group W] [Finite W]

theorem isSylowTwoOf_top_map_center {L S₀ : Subgroup W} (hS : IsSylowTwoOf S₀ L) :
    IsSylowTwoOf ((S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⊤ := by
  have hP : IsPGroup 2 (S₀.subgroupOf L) := hS.2.1.comap_subtype
  refine ⟨le_top, hP.map _, ?_⟩
  rw [show ((_ : Subgroup (↥L ⧸ Subgroup.center ↥L)).subgroupOf ⊤).index = _ from
    Subgroup.relIndex_top_right _]
  intro h2
  exact hS.2.2 (h2.trans ((S₀.subgroupOf L).index_map_dvd (QuotientGroup.mk'_surjective _)))

theorem isMinOverBorel_preimage {L S₀ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    {P : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (h : IsMinOverBorel ⊤ ((S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) P) :
    IsMinOverBorel L S₀ ((P.comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have hqker : q.ker = Z := by rw [hqdef, QuotientGroup.ker_mk']
  obtain ⟨S, hSS⟩ := McLaughlin.Lie.exists_sylow_of_isSylowTwoOf hS
  have hS₀L : S₀ ≤ L := hS.1
  set S₀' : Subgroup ↥L := S₀.subgroupOf L with hS₀'
  set B : Subgroup (↥L ⧸ Z) := Subgroup.normalizer (((S₀').map q : Subgroup _) : Set _) with hBdef
  obtain ⟨-, h1, h2⟩ := h
  rw [top_inf_eq] at h1 h2
  have hBL : Subgroup.normalizer (S₀' : Set ↥L) = B.comap q := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_comap]
      exact Subgroup.le_normalizer_map q ⟨x, hx, rfl⟩
    · intro hx
      rw [Subgroup.mem_comap] at hx
      have h1 := normalizer_map_le S hq (by rw [hqker]) (by rw [hSS]; exact hx)
      obtain ⟨x', hx', hxx'⟩ := h1
      have hz : x'⁻¹ * x ∈ Z := by
        rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel]
      have : x = x' * (x'⁻¹ * x) := by group
      rw [this]
      refine Subgroup.mul_mem _ (by rwa [hSS] at hx')
        (Subgroup.center_le_normalizer (S₀' : Set ↥L) hz)
  set PL : Subgroup ↥L := P.comap q with hPL
  set BL : Subgroup ↥L := B.comap q with hBLdef
  have hBW : L ⊓ Subgroup.normalizer (S₀ : Set W) = BL.map L.subtype := by
    rw [show BL = Subgroup.normalizer (S₀' : Set ↥L) from hBL.symm, map_normalizer_eq_inf', hS₀',
      Subgroup.map_subgroupOf_eq_of_le hS₀L, inf_comm]
  have hZBL : Z ≤ BL := by
    intro z hz
    rw [hBLdef, Subgroup.mem_comap]
    have : q z = 1 := by rw [← MonoidHom.mem_ker, hqker]; exact hz
    rw [this]
    exact one_mem _
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [hBW]
    refine lt_of_le_of_ne (Subgroup.map_mono (Subgroup.comap_mono h1.le)) fun heq => ?_
    have h1' : BL = PL := Subgroup.map_injective L.subtype_injective heq
    have h2' := congrArg (Subgroup.map q) h1'
    rw [hBLdef, hPL, Subgroup.map_comap_eq_self_of_surjective hq,
      Subgroup.map_comap_eq_self_of_surjective hq] at h2'
    exact h1.ne h2'
  · intro Q hQ1 hQ2
    rw [hBW] at hQ1 ⊢
    have hQL : Q ≤ L := hQ2.trans (Subgroup.map_subtype_le _)
    have hQe : (Q.subgroupOf L).map L.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQL
    have hB' : BL ≤ Q.subgroupOf L := by
      have h1 : BL.map L.subtype ≤ (Q.subgroupOf L).map L.subtype := by rw [hQe]; exact hQ1
      exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).1 h1
    have hP' : Q.subgroupOf L ≤ PL := by
      have h1 : (Q.subgroupOf L).map L.subtype ≤ PL.map L.subtype := by rw [hQe]; exact hQ2
      exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).1 h1
    have hlow : B ≤ (Q.subgroupOf L).map q := by
      have := Subgroup.map_mono (f := q) hB'
      rwa [hBLdef, Subgroup.map_comap_eq_self_of_surjective hq] at this
    have hup : (Q.subgroupOf L).map q ≤ P := by
      have := Subgroup.map_mono (f := q) hP'
      rwa [hPL, Subgroup.map_comap_eq_self_of_surjective hq] at this
    have hcm : ((Q.subgroupOf L).map q).comap q = Q.subgroupOf L := by
      rw [Subgroup.comap_map_eq, hqker]
      exact sup_eq_left.2 (hZBL.trans hB')
    rcases h2 _ hlow hup with h1 | h1
    · left
      rw [← hQe]
      congr 1
      rw [← hcm, h1]
    · right
      rw [← hQe]
      congr 1
      rw [← hcm, h1]



theorem pElementSubgroup_le_map_pElementSubgroup_comap {L : Subgroup W}
    (P : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
    pElementSubgroup 2 P ≤
      (pElementSubgroup 2 (P.comap (QuotientGroup.mk' (Subgroup.center ↥L)))).map
        (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  unfold pElementSubgroup
  rw [Subgroup.closure_le]
  rintro x ⟨hxP, k, hk⟩
  obtain ⟨xt, hxt⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) x
  obtain ⟨e, ⟨j, hj⟩, hfe⟩ := exists_pElement_lift q (p := 2) (x := xt) ⟨k, by rw [hxt]; exact hk⟩
  refine ⟨xt ^ e, Subgroup.subset_closure ⟨?_, j, hj⟩, ?_⟩
  · rw [Subgroup.mem_comap, hfe]
    have h0 : q xt = x := hxt
    rw [h0]; exact hxP
  · rw [hfe]; exact hxt

theorem map_pElementSubgroup_le {L : Subgroup W} (P : Subgroup ↥L) :
    (pElementSubgroup 2 P).map L.subtype ≤ pElementSubgroup 2 (P.map L.subtype) := by
  unfold pElementSubgroup
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, ⟨hxP, k, hk⟩, rfl⟩
  exact Subgroup.subset_closure ⟨⟨x, hxP, rfl⟩, k, by
    show orderOf ((x : ↥L) : W) = 2 ^ k
    rw [Subgroup.orderOf_coe]; exact hk⟩

theorem pElementSubgroup_le_map_subgroupOf {L : Subgroup W} (G' : Subgroup W)
    (P : Subgroup (↥L ⧸ Subgroup.center ↥L))
    (h : pElementSubgroup 2 ((P.comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype) ≤ G') :
    pElementSubgroup 2 P ≤ (G'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  refine (pElementSubgroup_le_map_pElementSubgroup_comap (L := L) P).trans
    (Subgroup.map_mono ?_)
  intro y hy
  refine (Subgroup.mem_subgroupOf).2 ?_
  exact h (map_pElementSubgroup_le (P.comap (QuotientGroup.mk' (Subgroup.center ↥L))) ⟨y, hy, rfl⟩)

theorem chevGen_of_yData {L S₀ : Subgroup W} (hL : Open.IsQuasisimple ↥L)
    (hS : IsSylowTwoOf S₀ L)
    (hY : YData (↥L ⧸ Subgroup.center ↥L)
      ((S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))) :
    ∃ Ps : Set (Subgroup W), (∀ P ∈ Ps, IsMinOverBorel L S₀ P) ∧
      L = ⨆ P ∈ Ps, pElementSubgroup 2 P ∧
      ∀ P ∈ Ps, ∃ x ∈ pElementSubgroup 2 P, orderOf x = 3 ∧
        x ∉ (Subgroup.center ↥L).map L.subtype := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Ps, hmin, hgen, hdat⟩ := hY
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have hqker : q.ker = Z := by rw [hqdef, QuotientGroup.ker_mk']
  refine ⟨(fun P => (P.comap q).map L.subtype) '' Ps, ?_, ?_, ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    exact isMinOverBorel_preimage hS (hmin P hP)
  · set G' : Subgroup W := ⨆ P ∈ ((fun P => (P.comap q).map L.subtype) '' Ps),
      pElementSubgroup 2 P with hG'
    have hG'L : G' ≤ L := by
      refine iSup₂_le fun P' hP' => ?_
      obtain ⟨P, hP, rfl⟩ := hP'
      exact (pElementSubgroup_le _).trans (Subgroup.map_subtype_le _)
    set Gs : Subgroup ↥L := G'.subgroupOf L with hGs
    have hPG : ∀ P ∈ Ps, pElementSubgroup 2 P ≤ Gs.map q := by
      intro P hP
      refine pElementSubgroup_le_map_subgroupOf G' P ?_
      exact le_iSup₂ (f := fun (Q : Subgroup W) (_ : Q ∈ ((fun P => (P.comap q).map L.subtype) '' Ps)) =>
        pElementSubgroup 2 Q) ((P.comap q).map L.subtype) ⟨P, hP, rfl⟩
    have htop : Gs.map q = ⊤ := by
      have h0 : (⨆ P ∈ Ps, pElementSubgroup 2 P) ≤ Gs.map q :=
        iSup₂_le fun P hP => hPG P hP
      rw [hgen] at h0
      exact top_le_iff.1 h0
    have hLG : (⊤ : Subgroup ↥L) ≤ Gs := by
      have hc : (⊤ : Subgroup ↥L) = ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ := by
        rw [← commutator_def]; exact hL.1.symm
      rw [hc, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have hmem : ∀ g : ↥L, ∃ g' ∈ Gs, g'⁻¹ * g ∈ Subgroup.center ↥L := fun g => by
        have hg : q g ∈ Gs.map q := by rw [htop]; trivial
        obtain ⟨g', hg', e⟩ := hg
        refine ⟨g', hg', ?_⟩
        have : g'⁻¹ * g ∈ q.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
        rwa [hqker] at this
      obtain ⟨g₁', hg₁', hz₁⟩ := hmem g₁
      obtain ⟨g₂', hg₂', hz₂⟩ := hmem g₂
      have e : ⁅g₁, g₂⁆ = ⁅g₁', g₂'⁆ := by
        have h1 : g₁ = g₁' * (g₁'⁻¹ * g₁) := by group
        have h2 : g₂ = g₂' * (g₂'⁻¹ * g₂) := by group
        conv_lhs => rw [h1, h2]
        exact commutator_mul_central hz₁ hz₂
      rw [e, commutatorElement_def]
      exact Gs.mul_mem (Gs.mul_mem (Gs.mul_mem hg₁' hg₂') (Gs.inv_mem hg₁')) (Gs.inv_mem hg₂')
    exact le_antisymm (fun g hg => (Subgroup.mem_subgroupOf).1 (hLG (Subgroup.mem_top ⟨g, hg⟩)))
      hG'L
  · rintro _ ⟨P, hP, rfl⟩
    obtain ⟨a, ha, g, hg, ha3, ha1, hinv⟩ := hdat P hP
    set A := pElementSubgroup 2 (P.comap q) with hA
    have hle := pElementSubgroup_le_map_pElementSubgroup_comap (L := L) P
    obtain ⟨a', hatA, hataq⟩ := hle ha
    obtain ⟨gt, hgtA, hgtq⟩ := hle hg
    have hker : ∀ z, q z = 1 → z ∈ Subgroup.center ↥L := fun z hz => by
      have h0 : z ∈ q.ker := hz
      rw [hqker] at h0; exact h0
    obtain ⟨y, hyA, hy3, hyq⟩ := exists_prime_order_inverted q hker A Nat.prime_three
      (by norm_num) hatA hgtA (by rw [hataq]; exact ha3)
      (by rw [map_mul, map_mul, map_inv, hgtq, hataq, hinv])
    have hy1 : y ≠ 1 := fun h => ha1 (by rw [← hataq, ← hyq, h, map_one])
    refine ⟨(y : W), ?_, ?_, ?_⟩
    · exact map_pElementSubgroup_le (P.comap q) ⟨y, hyA, rfl⟩
    · rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hy3 hy1
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      subst hzy'
      have : q z = 1 := by rw [← MonoidHom.mem_ker, hqker]; exact hz
      exact ha1 (by rw [← hataq, ← hyq, this])

end Transport

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
