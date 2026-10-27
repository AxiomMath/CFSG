module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

namespace UpsilonTypeNs

variable {G : Type} [Group G] [Finite G]

theorem not_balanced_of_branch_b (h191 : Lemma54Ns.Input19_1_2) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} (hBel : IsElemAbelian 3 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L : Subgroup G}
    (hcomp : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    {D : Subgroup G} (hD : IsEkIn 3 2 B D)
    (hnot : ¬ ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L) :
    ¬ IsCompLocallyBalanced 3 2 B L := by
  have := hS.simple
  obtain ⟨hDB, hDel, hDcard⟩ := hD
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set X : Subgroup G := GLADelta 3 D ⊓ C with hXdef
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  have hbD : b ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact elemAbelian_comm hBel (hDB hd) hb
  obtain ⟨hnorm, hmain⟩ :=
    h191 G hS.nonabelian hS.kProper 3 Nat.prime_three D hDel hDne b hbD hb1 (hBel.2 b hb)
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := hnorm L hcomp
  have hnot' : ¬ ⁅L, X⁆ ≤ GLAPPrimeCoreOf 3 C := by
    intro hle
    apply hnot
    have hLX : ⁅L, X⁆ ≤ L := Subgroup.commutator_le.2 fun ℓ hℓ x hx => by
      rw [commutatorElement_def]
      have h1 := (Subgroup.mem_normalizer_iff.1 (hXN hx) ℓ⁻¹).1 (L.inv_mem hℓ)
      have h2 := L.mul_mem hℓ h1
      simpa [mul_assoc] using h2
    intro y hy
    have h3 := gLAPPrimeCoreOf_inf_le Nat.prime_three C L ⟨hle hy, hLX hy⟩
    rwa [inf_eq_right.2 hcomp.1] at h3
  obtain ⟨hker, hDN, himg⟩ := hmain L hcomp hnot'
  set Dt : Subgroup (MulAut (barOf 3 L)) :=
    (D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hDt
  set Ht : Subgroup (MulAut (barOf 3 L)) :=
    ((X ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hHt
  have hDcard9 : Nat.card ↥Dt = 9 := by
    rw [hDt, Lemma54Ns.card_map_barAut_of_kerB_eq_bot hDN hker, hDcard]
    norm_num
  have hDtE : IsEkIn 3 2 ⊤ Dt :=
    ⟨le_top, isElemAbelian_map (isElemAbelian_subgroupOf hDel) _, by rw [hDcard9]; norm_num⟩
  have hinn : innerAut (barOf 3 L) ≤ Ht :=
    Lemma54Ns.innerAut_le_map (p := 3) (le_sup_right : L ≤ X ⊔ L)
  have hconjT : ∀ d ∈ D, ∀ t ∈ X ⊔ L, d * t * d⁻¹ ∈ X ⊔ L := by
    intro d hd t ht
    have hle : X ⊔ L ≤ (X ⊔ L).comap (MulAut.conj d).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun ℓ hℓ => ?_)
      · have hdx : d * x = x * d :=
          Subgroup.mem_centralizer_iff.1 (Lemma54Ns.gLADelta_le_centralizer hd hx.1) d rfl
        have e : d * x * d⁻¹ = x := by rw [hdx]; group
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
        exact Subgroup.mem_sup_left hx
      · have hdl : d * ℓ * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hDN hd) ℓ).1 hℓ
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_right hdl
    have := hle ht
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hconjH : ∀ d ∈ Dt, ∀ h ∈ Ht, d * h * d⁻¹ ∈ Ht := by
    rintro _ ⟨⟨d, hdN⟩, hdD, rfl⟩ _ ⟨⟨t, htN⟩, htT, rfl⟩
    refine ⟨⟨d, hdN⟩ * ⟨t, htN⟩ * ⟨d, hdN⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact Subgroup.mem_subgroupOf.2
      (hconjT d (Subgroup.mem_subgroupOf.1 hdD) t (Subgroup.mem_subgroupOf.1 htT))
  have hnormH : Dt ≤ Subgroup.normalizer (Ht : Set (MulAut (barOf 3 L))) := by
    intro d hd
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hconjH d hd h hh, fun hh => ?_⟩
    have h2 := hconjH d⁻¹ (Dt.inv_mem hd) _ hh
    have e : d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have hdelta : localDeltaIn 3 Ht Dt ≠ ⊥ := by
    intro hbot
    rw [hbot] at himg
    exact Lemma54Ns.map_barAut_ne_bot hXN hnot (le_bot_iff.1 himg)
  have hDtB : Dt ≤ autBar 3 B L := Subgroup.map_mono (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hDB hx, x.2⟩)
  intro hbal
  exact hdelta (hbal Dt ⟨hDtB, hDtE.2⟩ Ht hinn hnormH)

theorem upsilonType_core (h31 : Lemma31) (h1910 : Input19_10) (h191 : Lemma54Ns.Input19_1_2)
    {m : ℕ} (hS : GLStanding G m 3) {B : Subgroup G} (hB : GLAIsBmax 3 B) (hsc : IsSCp 3 ⊤ B)
    {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsUpsilonComponent B b L) :
    IsExtremalType (↥L ⧸ oPrimeP 3 ↥L) ∨ IsHatON (barOf 3 L) := by
  have := hS.simple
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hLC, hdisj⟩ := hL
  rcases hdisj with ⟨hΛ, hψ⟩ | ⟨D, hD, hDnc⟩
  ·
    have hlam := lambdaOf_eq_of_lemma31 h31 hS hB hsc hb hb1
    rw [lambdaMOf_eq_bot_of_ne_five (by norm_num), sup_bot_eq] at hlam
    set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCdef
    set S1 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
      IsInGOne 3 B L} with hS1
    set S2 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
      Lemma31iii 3 B L} with hS2
    set S3 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
      Lemma31iv 3 B L} with hS3
    have hle : L ≤ sSup (S1 ∪ S2 ∪ S3) := by
      rw [sSup_union, sSup_union]
      have : lambdaOf 3 B b = sSup S1 ⊔ sSup S2 ⊔ sSup S3 := hlam
      rw [← this]
      exact hΛ
    have hmem := Lemma510Ns.mem_of_le_sSup hLC (fun A hA => by
      rcases hA with (hA | hA) | hA
      · exact hA.1
      · exact hA.1
      · exact hA.1) hle
    rcases hmem with (hm | hm) | hm
    · exfalso
      apply hψ
      have h1 : L ≤ psiOf 3 B b := le_sSup hm
      have h2 : psiOf 3 B b ≤ psiStarGroup 3 B :=
        le_iSup₂_of_le b hb (le_iSup_of_le hb1 (le_sup_left.trans le_sup_left))
      exact h1.trans h2
    · obtain ⟨-, -, -, -, ⟨K, hK, hKf, hKc, ⟨e⟩⟩, -⟩ := hm
      exact Or.inl (Or.inl ⟨K, hK, hKf, by rw [hKc], ⟨e⟩⟩)
    · exact Or.inr hm.2.2.2.2.1
  ·
    have hBel : IsElemAbelian 3 B := hB.1
    set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCdef
    have hBC : B ≤ C := le_centralizer_of_mem hBel hb
    have hCne : C ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hb1
    have hcard : Nat.card B = 3 ^ m := by
      have h := hB.2.1
      rw [hS.rank_eq] at h
      exact h
    have hmB : m ≤ CFSG.Open.pRank 3 B :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB.1 hcard
    have hrk : GLATwoLocalRank 3 ↥C ≤ CFSG.Open.pRank 3 B :=
      (glaTwoLocalRank_subgroup_le hp C).trans (hS.rank_eq.le.trans hmB)
    have h2rk : 2 ≤ CFSG.Open.pRank 3 B :=
      le_trans (by have := hS.four_le; omega) hmB
    have hbal : ¬ IsCompLocallyBalanced 3 2 B L :=
      not_balanced_of_branch_b h191 hS hBel hb hb1 hLC hD hDnc
    have h3 := (h1910 G hS.nonabelian hS.kProper 3 hp (by norm_num) C hCne B hBC hBel hrk L hLC).2.2
      h2rk
    rcases h3 with h3 | ⟨h5, -⟩ | ⟨-, h3⟩ | ⟨h5, -⟩
    · exact absurd h3 hbal
    · exact absurd h5 (by norm_num)
    · exact Or.inl (by simpa using h3)
    · exact absurd h5 (by norm_num)

end UpsilonTypeNs

theorem upsilonType_of_inputs (h31 : Lemma31) (h1910 : Input19_10)
    (h191 : Lemma54Ns.Input19_1_2) : Lemma55Ns.InputUpsilonType := by
  intro G _ _ m hS _ B hB hsc b hb hb1 L hL
  exact UpsilonTypeNs.upsilonType_core h31 h1910 h191 hS hB hsc hb hb1 hL

theorem upsilonType56_of_inputs (h31 : Lemma31) (h1910 : Input19_10)
    (h191 : Lemma54Ns.Input19_1_2) : Lemma56Ns.InputUpsilonType := by
  intro G _ _ m hS _ B hB b hb hb1 L hL
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by norm_num) hB
  exact UpsilonTypeNs.upsilonType_core h31 h1910 h191 hS hB.1 (lemma23_proved G m 3 hS B hB1)
    hb hb1 hL

end CFSG.HardMathSupport.Solomon.LocalBalance
