module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Defs
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open Subgroup
open scoped commutatorElement

section Glue

variable {p : ℕ}

private theorem giW6_bdd {G : Type*} [Group G] [Finite G] (hp : 1 < p) (H : Subgroup G) :
    BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨E, -, -, hE⟩
  have h1 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  have h2 : k < p ^ k := Nat.lt_pow_self hp
  omega

private theorem giW6_spec {G : Type*} [Group G] [Finite G] (hp : 1 < p) (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ CFSG.Open.pRank p H := by
  have hne : {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}.Nonempty := by
    refine ⟨0, ⊥, bot_le, ⟨inferInstance, ?_⟩, by simp⟩
    intro x hx
    rw [Subgroup.mem_bot.mp hx]
    exact one_pow p
  exact Nat.sSup_mem hne (giW6_bdd hp H)

private theorem giW6_le {G : Type*} [Group G] [Finite G] (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H :=
  le_csSup (giW6_bdd hp H) ⟨E, hEH, hE, hk⟩

private theorem giW6_mono {G : Type*} [Group G] [Finite G] (hp : 1 < p) {H H' : Subgroup G} (h : H ≤ H') :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p H' := by
  obtain ⟨E, hEH, hE, hk⟩ := giW6_spec hp H
  exact giW6_le hp (hEH.trans h) hE hk

private theorem giW6_le_map {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G'] (hp : 1 < p) {f : G →* G'}
    (hf : Function.Injective f) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (H.map f) := by
  obtain ⟨E, hEH, hE, hk⟩ := giW6_spec hp H
  have hE' : IsElemAbelian p (E.map f) := by
    haveI := hE.1
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  exact giW6_le hp (Subgroup.map_mono hEH) hE' ((Subgroup.card_map_of_injective hf).trans hk)

theorem two_le_pRank_of_I713 (hI : GL83.I_7_13_1) (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hKs : IsSimpleGroup K) (hKnab : ∃ a b : K, a * b ≠ b * a)
    (hKcat : IsCatalogGroup K) (hKc : centralizer (K : Set X) = ⊥) {Q : Subgroup X}
    (hQ : 3 ≤ CFSG.Open.pRank p Q) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥K) := by
  by_contra hlt
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 1 := by omega
  have h2 := (hI p hp hp2 ↥K hKs hKnab hKcat h1).2
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut ↥K) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hmem : u ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h := congrArg (fun α : MulAut ↥K => (α ⟨y, hy⟩ : X)) hu
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc y * u = (u * y * u⁻¹) * u := by rw [h]
        _ = u * y := by group
    rw [hKc] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h3 := giW6_le_map hp.one_lt hinj Q
  have h4 := giW6_mono hp.one_lt (le_top : Q.map (MulAut.conjNormal : X →* MulAut ↥K) ≤ ⊤)
  omega

theorem mem_of_fixes_sylow (hL : OuterHeisInner) (hp : p.Prime) (h5 : 5 ≤ p) {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hKs : IsSimpleGroup K) (hKnab : ∃ a b : K, a * b ≠ b * a)
    (hKcat : IsCatalogGroup K) (hKc : centralizer (K : Set X) = ⊥) (hKdvd : p ∣ Nat.card K)
    (S : Sylow p ↥K) (hS : IsMulCommutative (S : Subgroup ↥K) ∨ (Nat.card K).factorization p ≤ 3) {u : X}
    (hu : u ^ p = 1) (hfix : ∀ s ∈ (S : Subgroup ↥K), u * (s : X) * u⁻¹ = (s : X)) : u ∈ K := by
  have hαp : (MulAut.conjNormal u : MulAut ↥K) ^ p = 1 := by
    rw [← map_pow, hu, map_one]
  have hαS : ∀ s ∈ (S : Subgroup ↥K), (MulAut.conjNormal u : MulAut ↥K) s = s := by
    intro s hs
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hfix s hs
  obtain ⟨k, hk⟩ := hL ↥K hKs hKnab hKcat p hp h5 hKdvd S hS _ hαp hαS
  have hmem : (k : X)⁻¹ * u ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun α : MulAut ↥K => (α ⟨y, hy⟩ : X)) hk
    simp only [MulAut.conjNormal_apply] at h
    have h' : (k : X) * y * (k : X)⁻¹ = u * y * u⁻¹ := h
    calc y * ((k : X)⁻¹ * u) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * u := by group
      _ = (k : X)⁻¹ * (u * y * u⁻¹) * u := by rw [h']
      _ = (k : X)⁻¹ * u * y := by group
  rw [hKc] at hmem
  have h0 : (k : X)⁻¹ * u = 1 := Subgroup.mem_bot.mp hmem
  have hu' : u = k := by
    calc u = (k : X) * ((k : X)⁻¹ * u) := by group
      _ = k := by rw [h0, mul_one]
  rw [hu']
  exact k.2

theorem wcOn_of_kFactWeakClosure (hWC : KFactWeakClosure) (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    [Finite K] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K)
    (P : Sylow p K) (hab : IsMulCommutative (P : Subgroup K)) (hrk : 2 ≤ CFSG.Open.pRank p (P : Subgroup K))
    (A : Subgroup K) (hAP : A ≤ (P : Subgroup K)) (hA : Nat.card A = p) :
    ∃ g : K, A.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup K) ∧ A.map (MulAut.conj g).toMonoidHom ≠ A := by
  have hTs : IsSimpleGroup (⊤ : Subgroup K) := (Subgroup.topEquiv (G := K)).isSimpleGroup
  have hTnab : ∃ a b : (⊤ : Subgroup K), a * b ≠ b * a := by
    obtain ⟨a, b, h⟩ := hnab
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h' => h (congrArg Subtype.val h')⟩
  have hTcat : IsCatalogGroup (⊤ : Subgroup K) := by
    obtain ⟨i, ⟨e⟩⟩ := hcat
    exact ⟨i, ⟨Subgroup.topEquiv.trans e⟩⟩
  have hTc : centralizer ((⊤ : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    haveI := hs
    exact CFSG.ComponentClassification.Helpers.center_eq_bot K hnab
  have hdvd : p ∣ Nat.card (⊤ : Subgroup K) := by
    obtain ⟨E, -, -, hE⟩ := giW6_spec hp.one_lt (P : Subgroup K)
    have h1 : p ∣ Nat.card E := by
      rw [hE]
      exact dvd_pow_self p (by omega)
    exact h1.trans ((Subgroup.card_subgroup_dvd_card E).trans (by
      rw [Nat.card_congr (Subgroup.topEquiv (G := K)).toEquiv]))
  exact hWC p hp hp2 K (⊤ : Subgroup K) inferInstance hTs hTnab hTcat hTc hdvd P (top_sup_eq _) hab
    (by rw [inf_top_eq]; exact hrk) A hAP hA

theorem map_conj_subgroupOf {X : Type*} [Group X] (K : Subgroup X) [K.Normal] (A : Subgroup X) (hAK : A ≤ K)
    (g : ↥K) : (A.subgroupOf K).map (MulAut.conj g).toMonoidHom =
      (A.map (MulAut.conj (g : X)).toMonoidHom).subgroupOf K := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨⟨x, hAK hx⟩, hx, ?_⟩
    exact Subtype.ext hxy

end Glue

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
