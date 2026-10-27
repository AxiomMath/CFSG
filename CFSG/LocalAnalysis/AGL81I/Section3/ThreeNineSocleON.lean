module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleCore
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporON
public import Certificates.Certificate5185
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.CentralizerM

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ONSchreier CFSG.HardMathSupport.Dickson.I271
open CFSG.LocalAnalysis.RankThreeTheoremC.ONPair
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (oPPrimeHull)

theorem nonempty_mulEquiv_M1
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 7 19) (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .ONan)
    (hDK : D ≤ K) : Nonempty (↥X₁ ≃* ↥CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.M1) := by
  obtain ⟨e⟩ := hs
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.ON.isSimpleGroup_ON e
  have hcK : Nat.card ↥K = 460815505920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.ON.card_ON
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  obtain ⟨θ⟩ : Nonempty (↥K ≃* ↥Pv) := ⟨e.trans onEquivPv⟩
  have hO : Nat.card (Outer ↥K) ∣ 2 := by
    rw [Nat.card_congr (equivalence θ).toEquiv]
    exact CFSG.Sporadic.SteinbergBI.card_outer_Pv_dvd_two
  have hO0 : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hout7 : ¬ 7 ∣ Nat.card (Outer ↥K) := fun h7 => by
    have := Nat.le_of_dvd (by norm_num) hO
    have := Nat.le_of_dvd hO0 h7
    omega
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  obtain ⟨Ebar, -, hEc, -, hN⟩ := h.exists_barE hZ hout7
  obtain ⟨S, hES⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  have hNS := hN S S.isPGroup' hES
  obtain ⟨g, hg⟩ := sylow_eq_map_on7F (Sylow.mapSurjective (f := θ.toMonoidHom) θ.surjective S)
  have hg' : (S : Subgroup ↥K).map θ.toMonoidHom =
      (on7F 0).map (MulAut.conj g : Pv ≃* Pv).toMonoidHom := hg
  set φ : ↥K ≃* ↥Pv := θ.trans (MulAut.conj g⁻¹) with hφ
  have hSφ : (S : Subgroup ↥K).map φ.toMonoidHom = on7F 0 := by
    have h1 : ((S : Subgroup ↥K).map θ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
        (S : Subgroup ↥K).map φ.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [← h1, hg', map_map_equiv]
    convert Subgroup.map_id (on7F 0)
    ext x
    simp
  set Y : Subgroup ↥Pv := (X₁.subgroupOf K).map φ.toMonoidHom with hYdef
  have hYc : Nat.card Y = Nat.card (X₁.subgroupOf K) :=
    Subgroup.card_map_of_injective φ.injective
  have hNY : Subgroup.normalizer ((on7F 0 : Subgroup Pv) : Set Pv) ≤ Y := by
    rw [← hSφ, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNS
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    obtain ⟨k, hk, hkx⟩ : φ ⟨x, hx⟩ ∈ Y := htop ▸ Subgroup.mem_top _
    have hk' : k = ⟨x, hx⟩ := φ.injective hkx
    exact Subgroup.mem_subgroupOf.mp (hk' ▸ hk)
  have hYM : Y ≤ M1 ∨ Y ≤ G2 := by
    have h1 := onanNQOvergroups_holds Y hNY hYtop
    rwa [onanM_one_eq, onanM_two_eq] at h1
  obtain ⟨hd1, -⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  rw [← hYc] at hd1
  have hYN : Y ≠ Subgroup.normalizer ((on7F 0 : Subgroup Pv) : Set Pv) := by
    intro hYeq
    rw [hYeq, card_normalizer_on7F0] at hd1
    exact absurd hd1 (by norm_num)
  have hcases : Y = M1 ∨ Y = G2 := by
    rcases hYM with hle | hle
    · exact Or.inl ((eq_normalizer_or_eq card_on7F0 card_M1 card_normalizer_on7F0
        normalizer_on7F0_le_M1 noInvariantPlane_on7F0 hNY hle).resolve_left hYN)
    · exact Or.inr ((eq_normalizer_or_eq card_on7F0 card_G2 card_normalizer_on7F0
        normalizer_on7F0_le_G2 noInvariantPlane_on7F0 hNY hle).resolve_left hYN)
  obtain ⟨e3⟩ : Nonempty (↥Y ≃* ↥M1) := by
    rcases hcases with hY | hY
    · exact ⟨MulEquiv.subgroupCongr hY⟩
    · exact ⟨(MulEquiv.subgroupCongr (hY.trans G2_eq_map)).trans
        (M1.equivMapOfInjective _ (MulEquiv.injective _)).symm⟩
  have e1 : ↥X₁ ≃* ↥(X₁.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hX₁K).symm
  have e2 : ↥(X₁.subgroupOf K) ≃* ↥Y :=
    (X₁.subgroupOf K).equivMapOfInjective φ.toMonoidHom φ.injective
  exact ⟨(e1.trans e2).trans e3⟩

theorem socle_of_onan
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 7 19) (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .ONan)
    (hDK : D ≤ K) :
    IsSimpleGroup ↥(oPPrimeHull 19 X₁) ∧
      Subgroup.centralizer (oPPrimeHull 19 X₁ : Set X) ⊓ K = ⊥ := by
  obtain ⟨ψ⟩ := nonempty_mulEquiv_M1 h hs hDK
  have hn : (Q0.subgroupOf M1).Normal := Subgroup.normal_of_index_eq_two index_Q0_M1
  have hsQ : IsSimpleGroup ↥(Q0.subgroupOf M1) :=
    @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_Q0 (Subgroup.subgroupOfEquivOfLe Q0_le_M1)
  obtain ⟨T₀, hT, hnT, hsT, ⟨eT⟩, hidx⟩ :=
    SporCent.exists_normal_of_mulEquiv ψ (Q0.subgroupOf M1) hn hsQ
  have hcT : Nat.card ↥T₀ = 1876896 := by
    rw [Nat.card_congr eT.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q0_le_M1).toEquiv, card_Q0]
  have hidxT : (T₀.subgroupOf X₁).index = 2 := by rw [hidx, index_Q0_M1]
  have hpT : ¬ (Nat.card ↥T₀).Prime := by rw [hcT]; norm_num
  have hdT : 19 ∣ Nat.card ↥T₀ := by rw [hcT]; norm_num
  obtain ⟨e⟩ := hs
  have hinv : ∀ z : ↥K, orderOf z = 2 →
      ¬ Nat.card ↥T₀ ∣ Nat.card (Subgroup.centralizer ({z} : Set ↥K)) := by
    intro z hz hdiv
    have hcard : Nat.card (Subgroup.centralizer ({z} : Set ↥K)) = 161280 := by
      rw [Nat.card_congr
        (CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.centralizerEquivM e hz).toEquiv]
      exact card_onM
    rw [hcT, hcard] at hdiv
    norm_num at hdiv
  exact h.socle_of_index_two hDK hT hnT hsT hpT hdT hidxT hinv

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
