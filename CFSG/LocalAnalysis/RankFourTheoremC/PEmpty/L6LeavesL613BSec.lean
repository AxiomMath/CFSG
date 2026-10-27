module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Sec
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Coord

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613B

open CFSG CFSG.LocalCores Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

theorem card_dvd_pi_aux {ι : Type} [Finite ι] [DecidableEq ι] {C : ι → Type} [∀ i, Group (C i)]
    [∀ i, Finite (C i)] {S : Type} [Group S] [IsSimpleGroup S] (J : Finset ι) :
    ∀ (T : Type) [Group T] (h : T →* ∀ i, C i), Function.Injective h →
      ∀ ψ : T →* S, Function.Surjective ψ → (∀ t : T, ∀ i, i ∉ J → h t i = 1) →
        ∃ i ∈ J, Nat.card S ∣ Nat.card (C i) := by
  induction J using Finset.induction_on with
  | empty =>
    intro T _ h hh ψ hψ hsupp
    exfalso
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨t, rfl⟩ := hψ s
    have ht : t = 1 := hh (by
      funext i
      simpa using hsupp t i (by simp))
    subst ht
    exact hs (map_one ψ)
  | insert a J haJ ih =>
    intro T _ h hh ψ hψ hsupp
    let g : T →* C a := (Pi.evalMonoidHom C a).comp h
    by_cases hK : g.ker ≤ ψ.ker
    · refine ⟨a, Finset.mem_insert_self a J, ?_⟩
      let ψ' : g.range →* S := (QuotientGroup.lift g.ker ψ hK).comp
        (QuotientGroup.quotientKerEquivRange g).symm.toMonoidHom
      have hψ' : Function.Surjective ψ' := by
        intro s
        obtain ⟨t, rfl⟩ := hψ s
        exact ⟨(QuotientGroup.quotientKerEquivRange g) (QuotientGroup.mk t), by simp [ψ']⟩
      have hsec : L613.IsSecOf (⊤ : Subgroup (C a)) S := ⟨g.range, le_top, ψ', hψ'⟩
      have hd := L613.IsSecOf.card_dvd hsec
      rwa [Subgroup.card_top] at hd
    · have hKtop : g.ker.map ψ = ⊤ := by
        haveI : (g.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (g.ker.map ψ) with hb | ht
        · exfalso
          apply hK
          intro t ht
          have hmem : ψ t ∈ g.ker.map ψ := Subgroup.mem_map_of_mem ψ ht
          rw [hb, Subgroup.mem_bot] at hmem
          exact MonoidHom.mem_ker.mpr hmem
        · exact ht
      have hψK : Function.Surjective (ψ.comp g.ker.subtype) := by
        intro s
        have hs : s ∈ g.ker.map ψ := by
          rw [hKtop]
          exact Subgroup.mem_top s
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hs
        exact ⟨⟨k, hk⟩, rfl⟩
      have hhK : Function.Injective (h.comp g.ker.subtype) :=
        hh.comp g.ker.subtype_injective
      obtain ⟨i, hi, hd⟩ := ih ↥g.ker (h.comp g.ker.subtype) hhK (ψ.comp g.ker.subtype) hψK
        (fun k i hi => by
          by_cases hia : i = a
          · rw [hia]
            have hk : g (k : T) = 1 := k.2
            simpa [g] using hk
          · exact hsupp (k : T) i (by simp [hia, hi]))
      exact ⟨i, Finset.mem_insert_of_mem hi, hd⟩

theorem card_dvd_pi_of_isSecOf {ι : Type} [Finite ι] {C : ι → Type} [∀ i, Group (C i)]
    [∀ i, Finite (C i)] {Q : Type} [Group Q] (e : Q →* ∀ i, C i)
    (he : Function.Injective e) {S : Type} [Group S] [IsSimpleGroup S] {U : Subgroup Q}
    (hU : L613.IsSecOf U S) : ∃ i, Nat.card S ∣ Nat.card (C i) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨H, -, ψ, hψ⟩ := hU
  obtain ⟨i, -, hi⟩ := card_dvd_pi_aux (S := S) Finset.univ ↥H (e.comp H.subtype)
    (he.comp H.subtype_injective) ψ hψ (fun _ i hi => absurd (Finset.mem_univ i) hi)
  exact ⟨i, hi⟩

theorem card_dvd_component_of_simple_quotient {Y K : Type} [Group Y] [Finite Y] [Group K]
    [Finite K] (hZ : ∀ C : ComponentIndex K, Subgroup.center C.1 = ⊥) (F : Y →* K)
    (D : Subgroup Y) [D.Normal] (hS : IsSimpleGroup (Y ⧸ D)) (hker : F.ker ≤ D) (z : Y)
    (hzD : z ∉ D) (hzL : F z ∈ CFSG.layer K) :
    ∃ C : ComponentIndex K, Nat.card (Y ⧸ D) ∣ Nat.card C.1 := by
  classical
  haveI hLn : (CFSG.layer K).Normal := ⟨fun n hn g => conj_mem_layer g hn⟩
  let φ : Y →* Y ⧸ D := QuotientGroup.mk' D
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective D
  let T : Subgroup Y := (CFSG.layer K).comap F
  haveI hTn : T.Normal := Subgroup.Normal.comap hLn F
  haveI hφT : (T.map φ).Normal := Subgroup.Normal.map hTn φ hφs
  have hzT : z ∈ T := hzL
  have htop : T.map φ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.map φ) with hb | ht
    · exfalso
      have hmem : φ z ∈ T.map φ := Subgroup.mem_map_of_mem φ hzT
      rw [hb, Subgroup.mem_bot] at hmem
      exact hzD ((QuotientGroup.eq_one_iff z).mp hmem)
    · exact ht
  let g : T →* ↥(CFSG.layer K) := (F.comp T.subtype).codRestrict (CFSG.layer K) (fun t => t.2)
  have hk : g.ker ≤ (φ.comp T.subtype).ker := by
    intro t ht
    have hFt : F (t : Y) = 1 := by
      have h1 : ((g t : ↥(CFSG.layer K)) : K) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
      exact h1
    have htD : (t : Y) ∈ D := hker (MonoidHom.mem_ker.mpr hFt)
    exact MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff _).mpr htD)
  let ψ : g.range →* Y ⧸ D := (QuotientGroup.lift g.ker (φ.comp T.subtype) hk).comp
    (QuotientGroup.quotientKerEquivRange g).symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro s
    have hs : s ∈ T.map φ := by
      rw [htop]
      exact Subgroup.mem_top s
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    exact ⟨(QuotientGroup.quotientKerEquivRange g) (QuotientGroup.mk ⟨t, ht⟩), by simp [ψ]⟩
  obtain ⟨C, hC⟩ := card_dvd_pi_of_isSecOf ((layerEquiv hZ).symm.toMonoidHom)
    (layerEquiv hZ).symm.injective (U := g.range) ⟨g.range, le_rfl, ψ, hψ⟩
  exact ⟨C, hC⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613B
