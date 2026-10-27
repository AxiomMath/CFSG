module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeSteps
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

theorem pRank_inf_centralizer_component_le_one {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {R X₀ : Subgroup X}
    (hC : ∀ A : Subgroup X, A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
      3 ≤ CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (A : Set X)) →
      Subgroup.centralizer (A : Set X) ≤ X₀)
    {L : Subgroup X} (hLX : ¬ L ≤ X₀)
    {u : X} (huR : u ∈ R) (huL : u ∈ L) (hup : orderOf u = p) (hunc : ∃ c ∈ L, u * c ≠ c * u) :
    CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (L : Set X)) ≤ 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hAle, hA, hAcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2)
      (H := R ⊓ Subgroup.centralizer (L : Set X)) (by omega)
  have hAR : A ≤ R := hAle.trans inf_le_left
  have hAC : A ≤ Subgroup.centralizer (L : Set X) := hAle.trans inf_le_right
  have hup' : u ^ p = 1 := by rw [← hup, pow_orderOf_eq_one]
  obtain ⟨c, hcL, hcu⟩ := hunc
  have huA : u ∉ A := by
    intro h
    apply hcu
    exact (Subgroup.mem_centralizer_iff.mp (hAC h) c hcL).symm
  have huAc : ∀ e ∈ A, e * u = u * e := fun e he =>
    (Subgroup.mem_centralizer_iff.mp (hAC he) u huL).symm
  obtain ⟨hE, hEcard⟩ :=
    CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hp hA hAcard hup' huA huAc
  have hEle : A ⊔ Subgroup.zpowers u ≤ R ⊓ Subgroup.centralizer (A : Set X) := by
    refine le_inf (sup_le hAR (Subgroup.zpowers_le.mpr huR)) ?_
    have hAc : A ≤ Subgroup.centralizer (A : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hA.1
      exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : A) ⟨x, hx⟩)
    refine sup_le hAc (Subgroup.zpowers_le.mpr ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact huAc y hy
  have hrank : 3 ≤ CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (A : Set X)) :=
    (three_le_pRank_of_card hp hE hEcard).trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hEle)
  apply hLX
  refine le_trans ?_ (hC A hAR hA hAcard hrank)
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hAC ha) l hl).symm

theorem le_normalizer_all_components {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {R X₀ : Subgroup X} (hR : IsPGroup p R) (hRX₀ : R ≤ X₀)
    (hC : ∀ A : Subgroup X, A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
      3 ≤ CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (A : Set X)) →
      Subgroup.centralizer (A : Set X) ≤ X₀)
    (hu : ∀ L : Subgroup X, IsComponentOf L ⊤ →
      ∃ u ∈ R, u ∈ L ∧ orderOf u = p ∧ ∃ c ∈ L, u * c ≠ c * u)
    {L₀ : Subgroup X} (hL₀ : IsComponentOf L₀ ⊤) (hL₀X : ¬ L₀ ≤ X₀) :
    ∀ L : Subgroup X, IsComponentOf L ⊤ → R ≤ Subgroup.normalizer (L : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro L hL
  by_cases hLX : L ≤ X₀
  swap
  · obtain ⟨u, huR, huL, hup, hunc⟩ := hu L hL
    exact le_normalizer_component_of_centralizer_le hp hp2 hR hC hL hLX huR huL hup hunc
  intro r hr
  by_contra hrN
  set L₂ : Subgroup X := L.map (MulAut.conj r).toMonoidHom with hL₂
  have hL₂c : IsComponentOf L₂ ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj r) L).mpr hL
  have hne : L ≠ L₂ := by
    intro h
    apply hrN
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [h]
    exact ⟨n, hn, rfl⟩
  have hL₂X : L₂ ≤ X₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact X₀.mul_mem (X₀.mul_mem (hRX₀ hr) (hLX hy)) (X₀.inv_mem (hRX₀ hr))
  have hL₀L : L₀ ≠ L := fun h => hL₀X (h ▸ hLX)
  have hL₀L₂ : L₀ ≠ L₂ := fun h => hL₀X (h ▸ hL₂X)
  obtain ⟨u₀, hu₀R, hu₀L, hu₀p, hu₀nc⟩ := hu L₀ hL₀
  obtain ⟨u₁, hu₁R, hu₁L, hu₁p, c₁, hc₁, hu₁nc⟩ := hu L hL
  obtain ⟨u₂, hu₂R, hu₂L, hu₂p, c₂, hc₂, hu₂nc⟩ := hu L₂ hL₂c
  have hrank := pRank_inf_centralizer_component_le_one hp hC hL₀X hu₀R hu₀L hu₀p hu₀nc
  have hcen : ∀ (L' : Subgroup X), IsComponentOf L' ⊤ → L₀ ≠ L' →
      L' ≤ Subgroup.centralizer (L₀ : Set X) := by
    intro L' hL' hne'
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact KFactProofs.K3.component_commute hL₀ hL' hne' hl hx
  have hu₁p' : u₁ ^ p = 1 := by rw [← hu₁p, pow_orderOf_eq_one]
  have hu₂p' : u₂ ^ p = 1 := by rw [← hu₂p, pow_orderOf_eq_one]
  have hE₁ : IsElemAbelian p (Subgroup.zpowers u₁) :=
    ⟨inferInstance, fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu₁p', one_zpow]⟩
  have hcard₁ : Nat.card (Subgroup.zpowers u₁) = p ^ 1 := by
    rw [Nat.card_zpowers, pow_one, hu₁p]
  have hu₂E : u₂ ∉ Subgroup.zpowers u₁ := by
    intro h
    apply hu₂nc
    have hu₂L₁ : u₂ ∈ L := (Subgroup.zpowers_le.mpr hu₁L) h
    exact (KFactProofs.K3.component_commute hL hL₂c hne hu₂L₁ hc₂)
  have hcomm : ∀ e ∈ Subgroup.zpowers u₁, e * u₂ = u₂ * e := fun e he =>
    KFactProofs.K3.component_commute hL hL₂c hne ((Subgroup.zpowers_le.mpr hu₁L) he) hu₂L
  obtain ⟨hA, hAcard⟩ :=
    CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hp hE₁ hcard₁ hu₂p' hu₂E hcomm
  have hAle : Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ≤
      R ⊓ Subgroup.centralizer (L₀ : Set X) :=
    le_inf (sup_le (Subgroup.zpowers_le.mpr hu₁R) (Subgroup.zpowers_le.mpr hu₂R))
      (sup_le (Subgroup.zpowers_le.mpr (hcen L hL hL₀L hu₁L))
        (Subgroup.zpowers_le.mpr (hcen L₂ hL₂c hL₀L₂ hu₂L)))
  have h2 : 2 ≤ CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (L₀ : Set X)) := by
    have := (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hAle)
    have h2' : 2 ≤ CFSG.Open.pRank p (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) := by
      have hle : (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ : Subgroup X) ≤
          Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ := le_rfl
      exact le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp _)
        ⟨_, hle, hA, hAcard⟩
    omega
  omega

theorem normal_sup_components_of_sylow {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {X₀ : Subgroup X} (R : Sylow p X) (hNR : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ X₀)
    (hall : ∀ L : Subgroup X, IsComponentOf L ⊤ →
      (R : Subgroup X) ≤ Subgroup.normalizer (L : Set X)) :
    (⨆ (L : Subgroup X) (_ : IsComponentOf L ⊤ ∧ ¬ L ≤ X₀), L).Normal := by
  classical
  have hcomp : ∀ (g : X) (L : Subgroup X), IsComponentOf L ⊤ →
      IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ := fun g L hL =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  set N₀ : Subgroup X := ⨅ (L : Subgroup X) (_ : IsComponentOf L ⊤),
    Subgroup.normalizer (L : Set X) with hN₀
  have memN₀ : ∀ n, n ∈ N₀ ↔ ∀ L : Subgroup X, IsComponentOf L ⊤ →
      n ∈ Subgroup.normalizer (L : Set X) := by
    intro n
    simp only [hN₀, Subgroup.mem_iInf]
  have hN₀n : N₀.Normal := ⟨fun n hn g => by
    rw [memN₀] at hn ⊢
    intro L hL
    have hL' := hcomp g⁻¹ L hL
    have hn' := hn _ hL'
    rw [Subgroup.mem_normalizer_iff] at hn' ⊢
    intro y
    have key := hn' (g⁻¹ * y * g)
    constructor
    · intro hy
      have h1 : g⁻¹ * y * g ∈ L.map (MulAut.conj g⁻¹).toMonoidHom := ⟨y, hy, by simp⟩
      obtain ⟨z, hz, hze⟩ := key.mp h1
      have : g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹ = z := by
        have hze' : g⁻¹ * z * g = n * (g⁻¹ * y * g) * n⁻¹ := by simpa using hze
        calc g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹ = g * (n * (g⁻¹ * y * g) * n⁻¹) * g⁻¹ := by
              group
          _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hze']
          _ = z := by group
      rw [this]
      exact hz
    · intro hy
      have h1 : n * (g⁻¹ * y * g) * n⁻¹ ∈ L.map (MulAut.conj g⁻¹).toMonoidHom := by
        refine ⟨g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹, hy, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      obtain ⟨z, hz, hze⟩ := key.mpr h1
      have : y = z := by
        have hze' : g⁻¹ * z * g = g⁻¹ * y * g := by simpa using hze
        have := congrArg (fun w => g * w * g⁻¹) hze'
        simpa [mul_assoc] using this.symm
      rw [this]
      exact hz⟩
  have hRN₀ : (R : Subgroup X) ≤ N₀ := fun r hr => (memN₀ r).mpr fun L hL => hall L hL hr
  have htop := Sylow.normalizer_sup_eq_top' R hRN₀
  set K : Subgroup X := ⨆ (L : Subgroup X) (_ : IsComponentOf L ⊤ ∧ ¬ L ≤ X₀), L with hK
  refine ⟨fun k hk g => ?_⟩
  have hg := (eq_top_iff.mp htop) (Subgroup.mem_top g)
  rw [sup_comm] at hg
  obtain ⟨n, hn, x, hx, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  have hxK : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ →
      L.map (MulAut.conj (n * x)).toMonoidHom ≤ K := by
    intro L hL hLX
    have hxX₀ : x ∈ X₀ := hNR hx
    set L' := L.map (MulAut.conj x).toMonoidHom with hL'
    have hL'c := hcomp x L hL
    have hL'X : ¬ L' ≤ X₀ := by
      intro h
      apply hLX
      intro l hl
      have hmem : x * l * x⁻¹ ∈ X₀ := h ⟨l, hl, rfl⟩
      have := X₀.mul_mem (X₀.mul_mem (X₀.inv_mem hxX₀) hmem) hxX₀
      simpa [mul_assoc] using this
    have hnL' : L'.map (MulAut.conj n).toMonoidHom = L' := by
      have hnN := (memN₀ n).mp hn L' hL'c
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hnN y).mp hy
      · intro y hy
        refine ⟨n⁻¹ * y * n, ?_, by simp [mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) y).mp hy
        simpa using this
    have e : L.map (MulAut.conj (n * x)).toMonoidHom = L'.map (MulAut.conj n).toMonoidHom := by
      rw [hL', Subgroup.map_map]
      congr 1
      ext y
      simp [mul_assoc]
    rw [e, hnL']
    exact le_iSup₂_of_le L' ⟨hL'c, hL'X⟩ le_rfl
  have hle : K.map (MulAut.conj (n * x)).toMonoidHom ≤ K := by
    rw [hK, Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hL => hxK L hL.1 hL.2
  exact hle ⟨k, hk, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
