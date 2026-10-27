module

public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernel
public import CFSG.LocalAnalysis.EvenSmallLie.StandardForm
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic

public section

namespace CFSG.EvenSmallLie

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.ComponentClassification

theorem oddCore_map_mulEquiv {K K' : Type*} [Group K] [Group K'] (f : K ≃* K') :
    (CFSG.Assembly.oddCore K).map f.toMonoidHom = CFSG.Assembly.oddCore K' := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup ⟨hN.1.map _ f.surjective, by rw [card_map_of_injective f.injective]; exact hN.2⟩
  · refine sSup_le fun N hN => ?_
    have h1 : N.comap f.toMonoidHom ≤ CFSG.Assembly.oddCore K := by
      refine le_sSup ⟨hN.1.comap _, ?_⟩
      rw [Nat.card_congr (f.toEquiv.subtypeEquiv fun a => (mem_comap (f := f.toMonoidHom)))]
      exact hN.2
    calc N = (N.comap f.toMonoidHom).map f.toMonoidHom :=
          (map_comap_eq_self_of_surjective f.surjective N).symm
      _ ≤ _ := map_mono h1

theorem hypothesisOne_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : HypothesisOne X) : HypothesisOne Y := by
  intro M' hM' x' hx'M hx'2 B' hB' hiso
  set E : MulAut X ≃* MulAut Y := MulAut.congr e with hEdef
  have hEconj : ∀ a : X, E (MulAut.conj a) = MulAut.conj (e a) := by
    intro a
    ext y
    simp [hEdef, MulAut.conj_apply]
  set M : Subgroup (MulAut X) := M'.comap E.toMonoidHom with hMdef
  set x : MulAut X := E.symm x' with hxdef
  have hM : (MulAut.conj : X →* MulAut X).range ≤ M := by
    rintro _ ⟨a, rfl⟩
    show E (MulAut.conj a) ∈ M'
    rw [hEconj]
    exact hM' ⟨e a, rfl⟩
  have hxM : x ∈ M := by
    show E x ∈ M'
    simpa [hxdef] using hx'M
  have hx2 : orderOf x = 2 := by rw [hxdef, MulEquiv.orderOf_eq, hx'2]
  have hK : (M ⊓ centralizer ({x} : Set (MulAut X))).map E.toMonoidHom =
      M' ⊓ centralizer ({x'} : Set (MulAut Y)) := by
    ext z
    rw [mem_map_equiv, mem_inf, mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa [hMdef] using h1, ?_⟩
      have := congrArg E h2
      simpa [hxdef] using this
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa [hMdef] using h1, ?_⟩
      rw [hxdef, ← map_mul, ← map_mul, h2]
  let f := (E.subgroupMap (M ⊓ centralizer ({x} : Set (MulAut X)))).trans
    (MulEquiv.subgroupCongr hK)
  let q := QuotientGroup.congr _ _ f (oddCore_map_mulEquiv f)
  have hB : (B'.comap q.toMonoidHom).Normal := hB'.comap _
  have eB : B'.comap q.toMonoidHom ≃* B' := (q.subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective q.surjective B'))
  apply h M hM x hxM hx2 _ hB
  rcases hiso with hi | hi
  · exact Or.inl (hi.map eB.trans)
  · exact Or.inr (hi.map eB.trans)

variable {G : Type} [Group G] [Finite G]

theorem card_sylow_eq_two_of_standard {L : Subgroup G} (hset : StandardSetting G L)
    (hI : HypothesisOne (L ⧸ center L)) (hFG : FoursGroupCondition L)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hset.isCyclic_sylow S
  have h2 : 2 ∣ Nat.card S := S.dvd_card_of_dvd_card (even_iff_two_dvd.mp hset.standard.2.1)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  by_contra hne
  have hS4 : 4 ≤ Nat.card S := by
    rw [hn] at h2 hne ⊢
    rcases n with _ | _ | n
    · norm_num at h2
    · norm_num at hne
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
      IsPGroup 2 P → Nat.card P ≤ 2
  · exact hset.false_of_forall_card_le_two hFG S hS4 hall
  · push Not at hall
    obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hall
    have hP4 : 4 ≤ Nat.card P := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
      rw [hm] at hPcard ⊢
      rcases m with _ | _ | m
      · norm_num at hPcard
      · norm_num at hPcard
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨g', hg', R, T, hRC, hR, hRcard, hTg, hTN, hT, hTcard, hRT⟩ :=
      exists_full_conj_centralized hset.standard S hS hg (hP.trans inf_le_left)
        (hP.trans inf_le_right) hP2 hP4
    exact not_hypothesisOne_of_full_conj hset.standard S hS hS4 hg' hRC hR hRcard hTg hTN hT
      hTcard hRT hI

theorem inf_centralizer_eq_zpowers_of_standard {L : Subgroup G} (hset : StandardSetting G L)
    (hI : HypothesisOne (L ⧸ center L)) (hFG : FoursGroupCondition L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : centralizer (L : Set G) := ⟨t, htC⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, ht]
  have hp : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have htS : tC ∈ (S : Subgroup (centralizer (L : Set G))) := hS (mem_zpowers tC)
  obtain ⟨-, -, -, -, -, -, hCH, -, -⟩ :=
    StandardRecognition.standard_cyclic_local_centralizer_kernel hset.standard S
      (hset.isCyclic_sylow S) htS htC2 (hset.core t ht)
  have hSeq : (S : Subgroup (centralizer (L : Set G))) = zpowers tC :=
    (eq_of_le_of_card_ge hS (by
      rw [card_sylow_eq_two_of_standard hset hI hFG S, Nat.card_zpowers, htC2])).symm
  rw [hCH, hSeq, MonoidHom.map_zpowers]
  rfl

theorem centralizer_eq_zpowers_of_standard {L : Subgroup G} (hset : StandardSetting G L)
    (hI : HypothesisOne (L ⧸ center L)) (hFG : FoursGroupCondition L) {t : G}
    (ht : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype) :
    centralizer (L : Set G) = zpowers t := by
  obtain ⟨htC, -, -, -, -, -, hCt⟩ := std_center_facts hset ht htZ
  rw [← inf_of_le_left hCt, inf_centralizer_eq_zpowers_of_standard hset hI hFG htC ht]

end CFSG.EvenSmallLie
