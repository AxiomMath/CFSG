module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Three
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped MatrixGroups
open CFSG.RankThreeCoreUniqueness
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf
  finite_perfectResidual_surjects_to_perfect_image finite_perfectResidual_map_eq
  finite_perfectResidualOf_isPerfect perfect_subgroup_le_perfectResidualOf
  perfectResidualOf_normalizer_contains normalizer_le_normalizer_characteristic_map
  pCoreOf_le pCoreOf_subgroupOf pCoreOf_isPGroup normal_pGroup_le_pCore
  normal_pGroup_le_pCoreOf)

namespace K63ThreeProof

theorem pElementSubgroup_top_normal (p : ℕ) {Y : Type*} [Group Y] :
    (pElementSubgroup p (⊤ : Subgroup Y)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 : pElementSubgroup p (⊤ : Subgroup Y) ≤
      (pElementSubgroup p (⊤ : Subgroup Y)).comap (MulAut.conj g).toMonoidHom := by
    unfold pElementSubgroup
    rw [Subgroup.closure_le]
    intro x hx
    apply Subgroup.subset_closure
    obtain ⟨-, k, hk⟩ := hx
    refine ⟨trivial, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  exact h1 hn

theorem le_of_open_subnormal {A : Type*} [Group A] {H G : Subgroup A}
    (h : CFSG.Open.IsSubnormal H G) : H ≤ G := by
  induction h with
  | refl => exact le_rfl
  | step hHM _ _ ih => exact hHM.trans ih

theorem isPerfect_of_simple {S : Type*} [Group S] (hs : IsSimpleGroup S)
    (hna : ¬ IsMulCommutative S) : Group.IsPerfect S := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exact absurd ((commutator_eq_bot_iff S).mp h) hna
  · exact h

theorem not_subsingleton_of_simple {S : Type*} [Group S] (hs : IsSimpleGroup S) :
    ¬ ∀ a b : S, a = b := fun h => by
  obtain ⟨x, hx⟩ := exists_ne (1 : S)
  exact hx (h x 1)

theorem perfectResidualOf_normal {A : Type*} [Group A] {G : Subgroup A} (hG : G.Normal) :
    (perfectResidualOf G).Normal := by
  have h := perfectResidualOf_normalizer_contains G
  rw [(Subgroup.normalizer_eq_top_iff).mpr hG] at h
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)

theorem subnormal_inf_top_or_le_center {A : Type*} [Group A] {G P : Subgroup A}
    (hPG : P ≤ G) (hq : CFSG.IsQuasisimple ↥P) {K : Subgroup A}
    (hK : CFSG.Open.IsSubnormal K G) :
    (K ⊓ P).subgroupOf P = ⊤ ∨ (K ⊓ P).subgroupOf P ≤ Subgroup.center ↥P := by
  induction hK with
  | refl K =>
    left
    rw [inf_eq_right.mpr hPG]
    exact Subgroup.subgroupOf_self P
  | @step K M G hKM hKMn hMG ih =>
    rcases ih hPG with ih | ih
    · have hPM : P ≤ M := (Subgroup.subgroupOf_eq_top.mp ih).trans inf_le_left
      have hnormal : ((K ⊓ P).subgroupOf P).Normal := by
        refine ⟨fun x hx g => ?_⟩
        have hxK : (x : A) ∈ K := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
        have hgM : (g : A) ∈ M := hPM g.2
        have h1 : (g : A) * x * (g : A)⁻¹ ∈ K :=
          (Subgroup.normal_subgroupOf_iff hKM).mp hKMn x g hxK hgM
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨h1, (g * x * g⁻¹ : ↥P).2⟩)
      exact CFSG.LocalCores.quasisimple_normal_subgroups hq hnormal
    · right
      refine le_trans (fun x hx => ?_) ih
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
        ⟨hKM (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1, x.2⟩)

theorem exists_decomp {A : Type*} [Group A] [Finite A] {H N : Subgroup A}
    [(N.subgroupOf H).Normal] [Group.IsPerfect (↥H ⧸ N.subgroupOf H)] {h : A} (hh : h ∈ H) :
    ∃ d ∈ perfectResidualOf H, ∃ n ∈ N, h = d * n := by
  have hmap := finite_perfectResidual_surjects_to_perfect_image
    (QuotientGroup.mk' (N.subgroupOf H)) (QuotientGroup.mk'_surjective _)
  have hmem : (QuotientGroup.mk' (N.subgroupOf H)) ⟨h, hh⟩ ∈
      Subgroup.map (QuotientGroup.mk' (N.subgroupOf H)) (Helpers.perfectResidual ↥H) := by
    rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨d, hd, hdf⟩ := hmem
  have h1 : d⁻¹ * ⟨h, hh⟩ ∈ N.subgroupOf H := by
    rw [← QuotientGroup.eq]
    exact hdf
  refine ⟨(d : A), Subgroup.mem_map_of_mem H.subtype hd, (d : A)⁻¹ * h, ?_, by group⟩
  exact Subgroup.mem_subgroupOf.mp h1

theorem not_perfectResidualOf_le {A : Type*} [Group A] [Finite A] {G H N : Subgroup A}
    (hHG : H ≤ G) (hN : (N.subgroupOf H).Normal)
    (hs : IsSimpleGroup (↥H ⧸ N.subgroupOf H)) (hna : ¬ IsMulCommutative (↥H ⧸ N.subgroupOf H)) :
    ¬ perfectResidualOf G ≤ N := by
  intro hle
  haveI : Group.IsPerfect (↥H ⧸ N.subgroupOf H) := isPerfect_of_simple hs hna
  have hDP : perfectResidualOf H ≤ perfectResidualOf G :=
    perfect_subgroup_le_perfectResidualOf _ _ (finite_perfectResidualOf_isPerfect H)
      ((Subgroup.map_subtype_le _).trans hHG)
  apply not_subsingleton_of_simple hs
  intro a b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [QuotientGroup.eq]
  refine Subgroup.mem_subgroupOf.mpr ?_
  obtain ⟨d, hd, n, hn, hdn⟩ := exists_decomp (N := N) (mul_mem (inv_mem a.2) b.2)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hdn]
  exact mul_mem (hle (hDP hd)) hn

theorem section_equiv_center_quot {A : Type*} [Group A] [Finite A] {G H N : Subgroup A}
    (hGn : G.Normal) (hH : CFSG.Open.IsSubnormal H G) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal)
    (hs : IsSimpleGroup (↥H ⧸ N.subgroupOf H)) (hna : ¬ IsMulCommutative (↥H ⧸ N.subgroupOf H))
    (hq : CFSG.IsQuasisimple ↥(perfectResidualOf G)) :
    Nonempty ((↥H ⧸ N.subgroupOf H) ≃*
      (↥(perfectResidualOf G) ⧸ Subgroup.center ↥(perfectResidualOf G))) := by
  set P := perfectResidualOf G with hPdef
  have hPG : P ≤ G := Subgroup.map_subtype_le _
  have hHG : H ≤ G := le_of_open_subnormal hH
  have hPn : P.Normal := perfectResidualOf_normal hGn
  haveI : Group.IsPerfect (↥H ⧸ N.subgroupOf H) := isPerfect_of_simple hs hna
  have hDP : perfectResidualOf H ≤ P :=
    perfect_subgroup_le_perfectResidualOf _ _ (finite_perfectResidualOf_isPerfect H)
      ((Subgroup.map_subtype_le _).trans hHG)
  have hDH : perfectResidualOf H ≤ H := Subgroup.map_subtype_le _
  have hPN : ¬ P ≤ N := not_perfectResidualOf_le hHG hN hs hna
  rcases subnormal_inf_top_or_le_center hPG hq hH with htop | hcen
  ·
    have hPH : P ≤ H := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left
    let f : ↥H →* ↥H ⧸ N.subgroupOf H := QuotientGroup.mk' (N.subgroupOf H)
    let ψ : ↥P →* ↥H ⧸ N.subgroupOf H := f.comp (Subgroup.inclusion hPH)
    have hsurj : Function.Surjective ψ := by
      haveI : (P.subgroupOf H).Normal := Subgroup.normal_subgroupOf
      have hnorm : ((P.subgroupOf H).map f).Normal :=
        Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
      rcases hs.eq_bot_or_eq_top_of_normal ((P.subgroupOf H).map f) with hbot | htop'
      · exfalso
        apply hPN
        intro p hp
        have h1 : f ⟨p, hPH hp⟩ ∈ (P.subgroupOf H).map f :=
          Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hp)
        rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      · intro s
        have h1 : s ∈ (P.subgroupOf H).map f := by rw [htop']; exact Subgroup.mem_top s
        obtain ⟨x, hx, rfl⟩ := h1
        exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    have hker : ψ.ker = Subgroup.center ↥P := by
      apply le_antisymm
      · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker ψ) with h | h
        · exfalso
          apply not_subsingleton_of_simple hs
          intro a b
          obtain ⟨x, rfl⟩ := hsurj a
          obtain ⟨y, rfl⟩ := hsurj b
          have hx : x ∈ ψ.ker := by rw [h]; exact Subgroup.mem_top x
          have hy : y ∈ ψ.ker := by rw [h]; exact Subgroup.mem_top y
          rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
        · exact h
      · intro z hz
        rw [MonoidHom.mem_ker]
        have hcent : ψ z ∈ Subgroup.center (↥H ⧸ N.subgroupOf H) := by
          rw [Subgroup.mem_center_iff]
          intro g
          obtain ⟨x, rfl⟩ := hsurj g
          rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) x]
        have hcb : Subgroup.center (↥H ⧸ N.subgroupOf H) = ⊥ := by
          rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (↥H ⧸ N.subgroupOf H)) with h | h
          · exact h
          · exfalso
            apply hna
            refine ⟨⟨fun a b => ?_⟩⟩
            have : b ∈ Subgroup.center (↥H ⧸ N.subgroupOf H) := by
              rw [h]; exact Subgroup.mem_top b
            exact (Subgroup.mem_center_iff.mp this a)
        rw [hcb, Subgroup.mem_bot] at hcent
        exact hcent
    exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker)⟩
  ·
    exfalso
    apply hna
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨d₁, hd₁, n₁, hn₁, ha⟩ := exists_decomp (N := N) a.2
    obtain ⟨d₂, hd₂, n₂, hn₂, hb⟩ := exists_decomp (N := N) b.2
    have hd₁H : d₁ ∈ H := hDH hd₁
    have hd₂H : d₂ ∈ H := hDH hd₂
    have hcomm : d₁ * d₂ = d₂ * d₁ := by
      have hz : (⟨d₁, hDP hd₁⟩ : ↥P) ∈ Subgroup.center ↥P :=
        hcen (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hd₁H, hDP hd₁⟩))
      have := (Subgroup.mem_center_iff.mp hz) ⟨d₂, hDP hd₂⟩
      exact (congrArg Subtype.val this).symm
    have key : ∀ (c : ↥H) (d n : A) (hdH : d ∈ H), n ∈ N → (c : A) = d * n →
        (QuotientGroup.mk c : ↥H ⧸ N.subgroupOf H) = QuotientGroup.mk ⟨d, hdH⟩ := by
      intro c d n hdH hn hc
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      have e : ((c⁻¹ * ⟨d, hdH⟩ : ↥H) : A) = n⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc]
        group
      rw [e]
      exact inv_mem hn
    rw [key a d₁ n₁ hd₁H hn₁ ha, key b d₂ n₂ hd₂H hn₂ hb, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext hcomm)

theorem perfectResidual_equiv {X : Type} [Group X] [Finite X]
    (hC : Subgroup.centralizer (CFSG.pCore 3 X : Set X) ≤ CFSG.pCore 3 X)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    {G : Subgroup (X ⧸ CFSG.pCore 3 X)} (hG : G.Normal) (hP : perfectResidualOf G ≠ ⊥) :
    Nonempty (↥(perfectResidualOf G) ≃* SL(3, ZMod 3)) ∨
      Nonempty (↥(perfectResidualOf G) ≃* SL(2, ZMod 5)) := by
  classical
  set Q : Subgroup X := CFSG.pCore 3 X with hQdef
  haveI hQn : Q.Normal := Helpers.pCore_normal 3
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
  let Y : Subgroup X := G.comap π
  haveI hYn : Y.Normal := Subgroup.Normal.comap hG π
  set W : Subgroup X := perfectResidualOf Y with hWdef
  haveI hWn : W.Normal := perfectResidualOf_normal hYn
  have hWperf : Group.IsPerfect ↥W := finite_perfectResidualOf_isPerfect Y
  have hWmap : W.map π = perfectResidualOf G := by
    let ρ : ↥Y →* ↥G := (π.comp Y.subtype).codRestrict G (fun y => Subgroup.mem_comap.mp y.2)
    have hρ : Function.Surjective ρ := by
      intro g
      obtain ⟨x, hx⟩ := hπ g
      exact ⟨⟨x, Subgroup.mem_comap.mpr (by rw [hx]; exact g.2)⟩, Subtype.ext hx⟩
    have h1 := finite_perfectResidual_map_eq ρ hρ
    have h2 : (π.comp Y.subtype) = G.subtype.comp ρ := MonoidHom.ext fun _ => rfl
    show Subgroup.map π (Subgroup.map Y.subtype (Helpers.perfectResidual ↥Y)) =
      Subgroup.map G.subtype (Helpers.perfectResidual ↥G)
    rw [Subgroup.map_map, h2, ← Subgroup.map_map, h1]
  have hpCoreOf : CFSG.Open.pCoreOf 3 W = Q ⊓ W := by
    apply le_antisymm
    · refine le_inf ?_ (pCoreOf_le 3 W)
      have hnorm : (CFSG.Open.pCoreOf 3 W).Normal := by
        have h := normalizer_le_normalizer_characteristic_map W (CFSG.pCore 3 ↥W)
          (Helpers.pCore_characteristic 3)
        rw [Subgroup.normalizer_eq_top_iff.mpr hWn] at h
        exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)
      exact normal_pGroup_le_pCore 3 _ hnorm (pCoreOf_isPGroup 3 W)
    · exact normal_pGroup_le_pCoreOf 3 (Q ⊓ W) W inf_le_right inferInstance
        ((Helpers.pCore_isPGroup 3).to_le inf_le_left)
  have hpCore : CFSG.pCore 3 ↥W = Q.subgroupOf W := by
    rw [← pCoreOf_subgroupOf 3 W, hpCoreOf, Subgroup.inf_subgroupOf_right]
  let φ : ↥W →* X ⧸ Q := π.comp W.subtype
  have hφker : φ.ker = CFSG.pCore 3 ↥W := by
    rw [hpCore]
    ext x
    simp only [φ, π, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφrange : φ.range = perfectResidualOf G := by
    rw [← hWmap, MonoidHom.range_comp, Subgroup.range_subtype]
  let e₀ : ↥W ⧸ CFSG.pCore 3 ↥W ≃* ↥(perfectResidualOf G) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange))
  have hWC : Subgroup.centralizer (CFSG.pCore 3 ↥W : Set ↥W) ≤ CFSG.pCore 3 ↥W :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroup_self_centralizing_pCore 3
      Nat.prime_three hC W hWn
  have hWr : CFSG.pRank 3 ↥W ≤ 3 :=
    (CFSG.RankThree.PartTwo.Sec4.Census.pRank_le_pRank_top Nat.prime_three W).trans hr
  have hWne : CFSG.pCore 3 ↥W ≠ ⊤ := by
    intro htop
    apply hP
    rw [← hWmap, eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have h1 : (⟨w, hw⟩ : ↥W) ∈ CFSG.pCore 3 ↥W := by rw [htop]; exact Subgroup.mem_top _
    rw [hpCore, Subgroup.mem_subgroupOf] at h1
    exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff _).mpr h1)
  rcases CFSG.RankThree.PartTwo.Sec4.Census.primeThreeLinear ↥W hWperf hWC hWr hWne with
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨e₀.symm.trans e⟩
  · exact Or.inr ⟨e₀.symm.trans e⟩

end K63ThreeProof

open K63ThreeProof in
theorem K63_three_holds :
    K63_three := by
  intro X _ _ _hK hC hr H N hH hNH hN hs hna
  have hGn : (pElementSubgroup 3 (⊤ : Subgroup (X ⧸ CFSG.pCore 3 X))).Normal :=
    pElementSubgroup_top_normal 3
  set G := pElementSubgroup 3 (⊤ : Subgroup (X ⧸ CFSG.pCore 3 X)) with hGdef
  have hHG : H ≤ G := le_of_open_subnormal hH
  have hP : perfectResidualOf G ≠ ⊥ := fun h =>
    not_perfectResidualOf_le hHG hN hs hna (h ▸ bot_le)
  have hP5 : Nonempty (PSL(2, ZMod 5) ≃* alternatingGroup (Fin 5)) :=
    CFSG.SectionRank.Ccomm.projective_five_alternating
  rcases perfectResidual_equiv hC hr hGn hP with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hq : CFSG.IsQuasisimple ↥(perfectResidualOf G) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        CFSG.RankThree.PartTwo.Sec4.Census.isQuasisimple_SL3_three
    obtain ⟨f⟩ := section_equiv_center_quot hGn hH hNH hN hs hna hq
    exact Or.inr (Or.inl ⟨f.trans (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))⟩)
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hq : CFSG.IsQuasisimple ↥(perfectResidualOf G) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (CFSG.RankThree.PartTwo.Sec4.Census.isQuasisimple_SL2 (le_refl 5))
    obtain ⟨f⟩ := section_equiv_center_quot hGn hH hNH hN hs hna hq
    obtain ⟨g⟩ := hP5
    exact Or.inr (Or.inr ⟨(f.trans (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))).trans g⟩)

theorem K63_holds : K63 :=
  K63_three_holds

end CFSG.LocalAnalysis.RankThreeUC.S15
