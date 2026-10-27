module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem gnC_le_normalizer_of_isGNPair {T T₁ T₂ : Subgroup X} (hg : IsGNPair T T₁ T₂) :
    gnC T ≤ Subgroup.normalizer (T₁ : Set X) := by
  intro c hc
  have h1 : T₁ ≤ gnV T := fun x hx => Subgroup.le_normalClosure (hg.le_center hx)
  have h2 : gnC T ≤ Subgroup.centralizer (T₁ : Set X) :=
    Subgroup.centralizer_le (fun x hx => h1 hx)
  exact Subgroup.centralizer_le_normalizer (T₁ : Set X) (h2 hc)

theorem not_dvd_card_gnC_of_inf {T T₁ T₂ L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hg : IsGNPair T T₁ T₂) (hL : LiftOf T L Ls) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : p ∣ Nat.card (gnA T T₁ Ls)) (hN : mN T₁ p ≤ 1)
    (hLC : ∀ c ∈ L ⊓ gnC T, orderOf c ≠ p) : ¬ p ∣ Nat.card (gnC T) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hpC
  set N := Subgroup.normalizer (T₁ : Set X)
  have hN' : CFSG.Open.pRank p N ≤ 1 := hN
  have hCN : gnC T ≤ N := gnC_le_normalizer_of_isGNPair hg
  have hA1 : gnA T T₁ Ls ≤ (L ⊓ N).map (toStar T) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy1
    rw [← hL.2] at hy2
    obtain ⟨l, hl, hln⟩ := Subgroup.mem_map.1 hy2
    have hc : n⁻¹ * l ∈ gnC T := QuotientGroup.eq.1 hln.symm
    refine ⟨l, ⟨hl, ?_⟩, hln⟩
    have e : l = n * (n⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem _ hn (hCN hc)
  have hdvd : p ∣ Nat.card ↥(L ⊓ N) :=
    (hA.trans (Subgroup.card_dvd_of_le hA1)).trans (Subgroup.card_map_dvd _ _)
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' p hpC
  have hbL : (b₀ : X) ∈ L := (Subgroup.mem_inf.1 b₀.2).1
  set b : ↥N := ⟨b₀, (Subgroup.mem_inf.1 b₀.2).2⟩ with hb
  set c : ↥N := ⟨c₀, hCN c₀.2⟩ with hc
  have hbo : orderOf b = p := by rw [hb, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hb₀]
  have hco : orderOf c = p := by rw [hc, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hc₀]
  have hpb : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hbo, pow_one]⟩
  have hpc : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hco, pow_one]⟩
  obtain ⟨P, hbP⟩ := hpb.exists_le_sylow
  obtain ⟨Q, hcQ⟩ := hpc.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥N) Q P
  have hc'P : g * c * g⁻¹ ∈ (P : Subgroup ↥N) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨c, hcQ (Subgroup.mem_zpowers c), rfl⟩
  set E : Subgroup X := (P : Subgroup ↥N).map N.subtype
  have hEp : IsPGroup p E := P.isPGroup'.map N.subtype
  have hEc : IsCyclic E := by
    by_contra hnc
    have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hp hp2 hEp hnc
    have h2 : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p N :=
      CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.map_subtype_le _)
    omega
  have hbE : (b : X) ∈ E := ⟨b, hbP (Subgroup.mem_zpowers b), rfl⟩
  have hcE : ((g * c * g⁻¹ : ↥N) : X) ∈ E := ⟨_, hc'P, rfl⟩
  set x₁ : ↥E := ⟨b, hbE⟩ with hx₁
  set x₂ : ↥E := ⟨_, hcE⟩ with hx₂
  have hx₁o : orderOf x₁ = p := by rw [hx₁, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hbo]
  have hgc : orderOf (g * c * g⁻¹) = p := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
    simpa [MulAut.conj_apply, hco] using this
  have hx₂o : orderOf x₂ = p := by rw [hx₂, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hgc]
  have hle : Subgroup.zpowers x₂ ≤ Subgroup.zpowers x₁ :=
    (IsCyclic.subgroup_le_iff_card_dvd).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hx₁o, hx₂o])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hle (Subgroup.mem_zpowers x₂))
  have hk' : (b : X) ^ k = ((g * c * g⁻¹ : ↥N) : X) := by
    have := congrArg Subtype.val hk
    simpa [hx₁, hx₂] using this
  apply hLC ((g * c * g⁻¹ : ↥N) : X)
  · refine ⟨?_, ?_⟩
    · rw [← hk']
      exact Subgroup.zpow_mem _ hbL k
    · simpa [hc] using (gnC_normal T).conj_mem (c₀ : X) c₀.2 (g : X)
  · rw [Subgroup.orderOf_coe, hgc]

theorem mk_mem_center_of_mem_inf {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {c : X} (hc : c ∈ L ⊓ gnC T) (hco : orderOf c = p) :
    QuotientGroup.mk' (CFSG.pCore 2 X) c ∈ (Subgroup.center ↥(barO2 L)).map (barO2 L).subtype ∧
      orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) c) = p := by
  refine ⟨(liftOf_central_ext hX hLs hL).1 ⟨c, hc, rfl⟩, ?_⟩
  have hd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) c) ∣ p := hco ▸ orderOf_map_dvd _ c
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exfalso
    have hc2 : c ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff c).1 (orderOf_eq_one_iff.1 h1)
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := X) ⟨c, hc2⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : p ∣ 2 ^ k := hco ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  · exact h1

theorem dvd_card_center_of_mem_inf {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {c : X} (hc : c ∈ L ⊓ gnC T) (hco : orderOf c = p) :
    p ∣ Nat.card (Subgroup.center ↥(barO2 L)) := by
  obtain ⟨⟨z, hz, hzc⟩, hzo⟩ := mk_mem_center_of_mem_inf hX hLs hL hp hp2 hc hco
  have h1 : orderOf z = p := by
    rw [← Subgroup.orderOf_coe]
    exact (congrArg orderOf hzc).trans hzo
  have h2 : orderOf (⟨z, hz⟩ : Subgroup.center ↥(barO2 L)) = p := by rw [Subgroup.orderOf_mk, h1]
  exact h2 ▸ orderOf_dvd_natCard _

theorem orderOf_ne_of_alt (hKSMAlt : KSMAlt) {T T₁ T₂ L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (halt7 : GNAlt7 T T₁ T₂)
    (hLs : IsComponentOf Ls ⊤) (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (hL : LiftOf T L Ls) {n : ℕ} (hn : n = 7 ∨ (8 < n ∧ Even n))
    (e : Nonempty (↥Ls ≃* alternatingGroup (Fin n))) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h₁ : mS T T₁ p Ls = 1) (h₂ : mS T T₂ p Ls = 1) : ∀ c ∈ L ⊓ gnC T, orderOf c ≠ p := by
  intro c hc hco
  have hpZ := dvd_card_center_of_mem_inf hX hLs hL hp hp2 hc hco
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  obtain ⟨e'⟩ := e
  have hn4 : 4 ≤ n := by omega
  obtain ⟨-, ⟨e''⟩⟩ := quotCenter_equiv_alt hn4 e'
  have hZ := hKSMAlt ↥(barO2 L) hL.1.component.2.2 n ⟨eQ.trans e''⟩ (centre_barO2_odd hL.1)
  rcases hn with rfl | ⟨h8, -⟩
  · have h3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hpZ.trans (hZ.1 (Or.inr rfl)))
    subst h3
    have h₁' : CFSG.Open.pRank 3 (gnA T T₁ Ls) = 1 := h₁
    have h₂' : CFSG.Open.pRank 3 (gnA T T₂ Ls) = 1 := h₂
    rcases halt7 Ls hLs hinv ⟨e'⟩ with h | h <;> omega
  · rw [hZ.2 (by omega)] at hpZ
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpZ)

end CFSG.LocalAnalysis.RankThreeUC.S15
