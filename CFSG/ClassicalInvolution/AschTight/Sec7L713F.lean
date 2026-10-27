module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713B
public import CFSG.ClassicalInvolution.AschTight.Sec7L713D

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem keyOn_strong (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) {J : Subgroup G} (hJ : J ∈ Ω)
    (hRJ : R ≤ J) (hTJ : T ≤ J) : T ≤ R ⊔ OCW W := by
  have hRsyl := isSylow2In_of_mem_RSet_of_le hp hΩ hR.1 hJ hRJ
  have h8 := hΩ.eight_le_of_mem_RSet hp hR.1
  have hWJ := le_normalizer_of_mem_DSet hp hq hΩ habel h611 hW hR hJ hRJ
  obtain ⟨-, hUU, -, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hR hJ hRJ
  obtain ⟨heq, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hR hJ hRJ
  rw [← heq] at hUU
  obtain ⟨-, -, -, -, -, -, hUc, -, hU4⟩ := hΩ.exists_data_of_mem_USet hp hUU
  have hU2 : IsPGroup 2 ↥(J ⊓ W) := hΩ.isPGroup_of_mem_USet hp hUU
  obtain ⟨g, hg⟩ := hUc.exists_generator
  have hgord : orderOf (g : G) = Nat.card ↥(J ⊓ W) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have huu : (g : G) * g ≠ 1 := by
    intro h
    have := Nat.le_of_dvd two_pos
      (orderOf_dvd_of_pow_eq_one (x := (g : G)) (n := 2) (by rw [pow_two]; exact h))
    omega
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hzU : z ∈ J ⊓ W := hz.mem_of_le inf_le_left hU2 (by omega)
  have hOH : oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) ≤
      J ⊓ Subgroup.normalizer (W : Set G) :=
    (oddCoreOf_le_self _).trans
      (inf_le_inf_left J (Subgroup.centralizer_le_normalizer (W : Set G)))
  have hHO : J ⊓ Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) : Set G) :=
    fun h hh => mem_normalizer_oddCoreOf_of_mem_normalizer
      (mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_inf.mp hh).1)
        (normalizer_le_normalizer_centralizer W (Subgroup.mem_inf.mp hh).2))
  have hRH : IsSylow2In R (J ⊓ Subgroup.normalizer (W : Set G)) :=
    ⟨le_inf hRJ hR.2, hRsyl.2.1, fun V' hV'H hV'2 hRV' =>
      hRsyl.2.2 V' (hV'H.trans inf_le_left) hV'2 hRV'⟩
  have hle := le_sup_of_pow_mem hOH hHO hRH fun h hh =>
    exists_pow_two_pow_mem hΩ hJ hWJ hUc hU2 g.2 huu (Subgroup.mem_inf.mp hh).1
      (Subgroup.mem_inf.mp hh).2
  have hOX := oddCoreOf_inf_centralizer_le_OCW hΩ hJ hz (Subgroup.mem_inf.mp hzU).2
  intro t ht
  exact sup_le le_sup_left (hOX.trans le_sup_right) (hle ⟨hTJ ht, hT.2 ht⟩)

theorem conjSub_eq_of_bar (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h611 : EtaMeets Ω)
    (habel : EtaAbelian Ω) (h67 : RCommute Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {T R' : Subgroup G} (hT : T ∈ DSet Ω W) (hR' : R' ∈ DSet Ω W) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {t r' : G} (htT : t ∈ T) (htW : t ∉ W)
    (hr'R' : r' ∈ R')
    (he : bar (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hT.2 htT)) (Subgroup.inv_mem _ hg)) =
      bar (hR'.2 hr'R')) {L K' : Subgroup G} (hL : L ∈ Ω) (hK' : K' ∈ Ω) (hTL : T ≤ L)
    (hR'K' : R' ≤ K') : conjSub g L = K' := by
  have hgW : conjSub g W = W := mem_normalizer_iff_conjSub_eq.mp hg
  have hgT : conjSub g T ∈ DSet Ω W := by
    refine ⟨RSet.conj hΩ.conjInvariant hT.1 g, ?_⟩
    have := conjSub_le_normalizer hT.2 g
    rwa [hgW] at this
  have hgtT : g * t * g⁻¹ ∈ conjSub g T := conj_mem_conjSub htT
  have hgtW : g * t * g⁻¹ ∉ W := by
    intro h
    apply htW
    have h1 : g * t * g⁻¹ ∈ conjSub g W := by rw [hgW]; exact h
    rw [mem_conjSub_iff] at h1
    simpa [mul_assoc] using h1
  have hle := le_sup_of_bar_eq hp hΩ h611 hW hR' hgT hr'R' hgtT hgtW he
  exact eq_of_le_sup hp hΩ h611 habel h67 hW hgT hR' hle (hΩ.conjInvariant g L hL) hK'
    (conjSub_mono hTL) hR'K'

theorem isSylow2In_inf_of_normal {V X Y : Subgroup G} (hV : IsSylow2In V X)
    (hYX : Y ≤ X) (hn : X ≤ Subgroup.normalizer (Y : Set G)) : IsSylow2In (V ⊓ Y) Y := by
  refine ⟨inf_le_right, hV.2.1.to_le inf_le_left, fun T hTY hT2 hle => ?_⟩
  obtain ⟨x, hx, hTx⟩ := exists_conj_le_of_isSylow2In hV hT2 (hTY.trans hYX)
  have hxY : conjSub x⁻¹ Y = Y :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (Y : Set G)).inv_mem (hn hx))
  have hTV : conjSub x⁻¹ T ≤ V ⊓ Y := by
    refine le_inf ?_ ?_
    · rw [conjSub_le_iff, inv_inv]
      exact hTx
    · have := conjSub_mono (n := x⁻¹) hTY
      rwa [hxY] at this
  have hcard : Nat.card T ≤ Nat.card ↥(V ⊓ Y) := by
    rw [← natCard_conjSub T x⁻¹]
    exact Subgroup.card_le_of_le hTV
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem exists_invariant_DSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {T L : Subgroup G} (hT : T ∈ DSet Ω W) (hL : L ∈ Ω) (hTL : T ≤ L) {a : G}
    (ha2 : IsPGroup 2 (Subgroup.zpowers a)) (haW : a ∈ Subgroup.normalizer (W : Set G))
    (haL : a ∈ Subgroup.normalizer (L : Set G)) :
    ∃ T' ∈ DSet Ω W, T' ≤ L ∧ IsSylow2In T' L ∧ conjSub a T' = T' ∧ T' ≤ T ⊔ OCW W := by
  set H := L ⊓ Subgroup.normalizer (W : Set G) with hH
  have haH : a ∈ Subgroup.normalizer (H : Set G) :=
    mem_normalizer_inf haL (Subgroup.le_normalizer haW)
  have hXN : Subgroup.zpowers a ⊔ H ≤ Subgroup.normalizer (H : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr haH) Subgroup.le_normalizer
  obtain ⟨P, hP, haP⟩ := IsSylow2In.exists_ge ha2 (le_sup_left : Subgroup.zpowers a ≤ _ ⊔ H)
  have hT'H := isSylow2In_inf_of_normal hP le_sup_right hXN
  have hTsyl := isSylow2In_of_mem_RSet_of_le hp hΩ hT.1 hL hTL
  have hTH : IsSylow2In T H := ⟨le_inf hTL hT.2, hTsyl.2.1, fun V' hV'H hV'2 hTV' =>
    hTsyl.2.2 V' (hV'H.trans inf_le_left) hV'2 hTV'⟩
  have hT'L : IsSylow2In (P ⊓ H) L := by
    refine IsSylow2In.of_natCard_le hTsyl hT'H.2.1 (inf_le_right.trans inf_le_left) ?_
    rw [hTH.natCard_eq hT'H]
  have hT'D : P ⊓ H ∈ DSet Ω W :=
    ⟨mem_RSet_of_isSylow2In hL hT'L, inf_le_right.trans inf_le_right⟩
  refine ⟨P ⊓ H, hT'D, hT'L.1, hT'L, ?_, keyOn_strong hp hq hΩ habel h611 hW hT hT'D hL hTL
    hT'L.1⟩
  rw [conjSub_inf, conjSub_eq_self_of_mem (haP (Subgroup.mem_zpowers a)),
    mem_normalizer_iff_conjSub_eq.mp haH]

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
