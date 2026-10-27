module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713K

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Family

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem l7_13_on (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) (h67 : RCommute Ω) (h71 : L71On Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {J : Subgroup G}
    (hJ : J ∈ Ω) {a : G} (ha : IsUniqueInvolution J a)
    (haW : a ∈ Subgroup.normalizer (W : Set G)) (hord3 : DOrder3 W R (conjSub a R))
    {T : Subgroup G} (hT : T ∈ DSet Ω W) (hTle : T ≤ R ⊔ conjSub a R ⊔ W ⊔ OCW W)
    (hTR : ¬ T ≤ R ⊔ W ⊔ OCW W) (hTRa : ¬ T ≤ conjSub a R ⊔ W ⊔ OCW W) {L : Subgroup G}
    (hL : L ∈ Ω) (hTL : T ≤ L) : L = J ∨ L ∈ omegaStarNbr Ω J := by
  obtain ⟨r, hrR, s, hsRa, hrX, hsX, h3, hne⟩ := hord3
  have hrW : r ∉ W := fun h => hrX (Subgroup.mem_sup_left h)
  have hsW : s ∉ W := fun h => hsX (Subgroup.mem_sup_left h)
  have hRa : conjSub a R ∈ DSet Ω W := ⟨RSet.conj hΩ.conjInvariant hR.1 a, by
    have := conjSub_le_normalizer hR.2 a
    rwa [mem_normalizer_iff_conjSub_eq.mp haW] at this⟩
  have hrN := hR.2 hrR
  have hsN := hRa.2 hsRa
  have ha2 : a * a = 1 := ha.sq
  obtain ⟨-, hx1, hx⟩ := bar_of_mem_DSet hp hΩ h611 hW hR hrR hrW
  have hα : bar haW * bar haW = 1 :=
    (bar_eq_one_iff (Subgroup.mul_mem _ haW haW)).mpr (by rw [ha2]; exact Subgroup.one_mem _)
  have hsRa' : a * r * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hrR
  have hys : bar hsN = bar haW * bar hrN * (bar haW)⁻¹ := by
    rcases (bar_of_mem_DSet hp hΩ h611 hW hRa hsRa hsW).1 _ hsRa' with h | h
    · exfalso
      apply hx1
      have h' : bar haW * bar hrN * (bar haW)⁻¹ = 1 := h
      calc bar hrN = (bar haW)⁻¹ * (bar haW * bar hrN * (bar haW)⁻¹) * bar haW := by group
        _ = 1 := by rw [h']; group
    · exact h.symm
  have h3o : (bar hrN * bar hsN) ^ 3 = 1 := by
    have hmem : r * s * (r * s * (r * s)) ∈ W ⊔ OCW W := by rw [← pow_three]; exact h3
    rw [pow_three]
    exact (bar_eq_one_iff (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hsN)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hsN) (Subgroup.mul_mem _ hrN hsN)))).mpr hmem
  have hneo : bar hrN * bar hsN ≠ 1 :=
    fun h => hne ((bar_eq_one_iff (Subgroup.mul_mem _ hrN hsN)).mp h)
  have h3' : (bar hrN * (bar haW * bar hrN * (bar haW)⁻¹)) ^ 3 = 1 := by rw [← hys]; exact h3o
  have hne' : bar hrN * (bar haW * bar hrN * (bar haW)⁻¹) ≠ 1 := by rw [← hys]; exact hneo
  have hy : (bar haW * bar hrN * (bar haW)⁻¹) * (bar haW * bar hrN * (bar haW)⁻¹) = 1 := by
    calc _ = bar haW * (bar hrN * bar hrN) * (bar haW)⁻¹ := by group
      _ = 1 := by rw [hx]; group
  obtain ⟨t₀, ht₀T, ht₀W⟩ := exists_not_mem_W hp hΩ h611 hW hT hL hTL
  have hbt₀ : bar (hT.2 ht₀T) = bar hrN * (bar haW * bar hrN * (bar haW)⁻¹) * bar hrN := by
    rw [← hys]
    exact bar_eq_xyx hp hΩ h611 hW hR hRa hT hrR hrW hsRa hsW h3o hneo hTle hTR hTRa ht₀T ht₀W
  have haL : conjSub a L = L := by
    refine conjSub_eq_of_bar hp hΩ h611 habel h67 hW hT hT haW ht₀T ht₀W ht₀T ?_ hL hL hTL hTL
    change bar haW * bar (hT.2 ht₀T) * (bar haW)⁻¹ = bar (hT.2 ht₀T)
    rw [hbt₀]
    exact s3_fix hx hy h3' rfl hα
  have ha2' : IsPGroup 2 (Subgroup.zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ha2) ha.ne_one, pow_one])
  obtain ⟨T', hT', hT'L, -, hT'a, hT'T⟩ := exists_invariant_DSet hp hq hΩ habel h611 hW hT hL
    hTL ha2' haW (mem_normalizer_iff_conjSub_eq.mpr haL)
  have hTT' : T ≤ T' ⊔ OCW W := keyOn_strong hp hq hΩ habel h611 hW hT' hT hL hT'L hTL
  have hT'le : T' ≤ R ⊔ conjSub a R ⊔ W ⊔ OCW W := hT'T.trans (sup_le hTle le_sup_right)
  have hT'R : ¬ T' ≤ R ⊔ W ⊔ OCW W := fun h => hTR (hTT'.trans (sup_le h le_sup_right))
  have hT'Ra : ¬ T' ≤ conjSub a R ⊔ W ⊔ OCW W :=
    fun h => hTRa (hTT'.trans (sup_le h le_sup_right))
  obtain ⟨t, htT', htW⟩ := exists_not_mem_W hp hΩ h611 hW hT' hL hT'L
  have hbt : bar (hT'.2 htT') = bar hrN * (bar haW * bar hrN * (bar haW)⁻¹) * bar hrN := by
    rw [← hys]
    exact bar_eq_xyx hp hΩ h611 hW hR hRa hT' hrR hrW hsRa hsW h3o hneo hT'le hT'R hT'Ra htT' htW
  obtain ⟨J₀, hJ₀, hRJ₀⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨-, hRWU, hRcard, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hR hJ₀ hRJ₀.1
  obtain ⟨-, hT'WU, hT'card, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hT' hL hT'L
  obtain ⟨-, -, -, -, -, -, hUc, -⟩ := hΩ.exists_data_of_mem_USet hp hRWU
  obtain ⟨-, -, -, -, -, -, hVc, -⟩ := hΩ.exists_data_of_mem_USet hp hT'WU
  obtain ⟨u, hu⟩ := exists_zpowers_eq hUc
  obtain ⟨v, hv⟩ := exists_zpowers_eq hVc
  have hRcl := eq_closure_of_index_two (relIndex_eq_two_of_card inf_le_left hRcard) inf_le_left
    hu hrR (fun h => hrW (Subgroup.mem_inf.mp h).2)
  have hT'cl := eq_closure_of_index_two (relIndex_eq_two_of_card inf_le_left hT'card)
    inf_le_left hv htT' (fun h => htW (Subgroup.mem_inf.mp h).2)
  rcases h71 W hW R hR T' hT' u r v t hu hRcl hv hT'cl with
    ⟨J₁, hJ₁, hRJ₁, hT'J₁⟩ | ⟨_, -, _, -, -, -, -, hcomm⟩ |
      ⟨J₁, hJ₁, _, -, hRJ₁, -, -, -, v', hv', h1, h2⟩
  · exact absurd ((keyOn_strong hp hq hΩ habel h611 hW hR hT' hJ₁ hRJ₁ hT'J₁).trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) hT'R
  · exfalso
    apply hne'
    have hcN : r * t * r⁻¹ * t⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN (hT'.2 htT'))
        (Subgroup.inv_mem _ hrN)) (Subgroup.inv_mem _ (hT'.2 htT'))
    have hb : bar hcN = 1 := (bar_eq_one_iff hcN).mpr (Subgroup.mem_sup_right (hcomm r hrR t htT'))
    change bar hrN * bar (hT'.2 htT') * (bar hrN)⁻¹ * (bar (hT'.2 htT'))⁻¹ = 1 at hb
    rw [hbt] at hb
    exact s3_comm_contra hx hy h3' hb
  · exact case_three hp hq hΩ habel h611 h67 hW hR hT' hJ₁ hRJ₁ hL hT'L hJ ha haW hT'a hu hrR
      hrW (hv'.trans hv) htT' htW h1 h2 h3' hbt

end Family

variable (p f : ℕ) [Fact p.Prime]

theorem l7_13ModTmp_of (h71 : L7_1 p f) : L7_13ModTmp p f := by
  intro G _ _ Ω hΩ W hW R hR J hJ a ha haW hord3 T hT hTle hTR hTRa L hL hTL
  have hp := hΩ.1
  have hq := hΩ.2.1
  have hmod := hΩ.2.2.1
  exact l7_13_on hp hq hmod
    (fun η ⟨S, hS, hinv⟩ => ((l6_9_proved p f hp hq G Ω hmod S).2 η hS hinv).1)
    (l6_11_proved p f hp hq G Ω hmod) (l6_7_proved p f hp hq G Ω hmod) (l71On_of h71 hΩ) hW hR
    hJ ha haW hord3 hT hTle hTR hTRa hL hTL

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
