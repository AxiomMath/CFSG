module

public import CFSG.ClassicalInvolution.AschTight.Sec7KeyC
public import CFSG.ClassicalInvolution.AschTight.Sec7L76D

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem le_sup_of_pow_mem {H O R : Subgroup G} (hOH : O ≤ H)
    (hHO : H ≤ Subgroup.normalizer (O : Set G)) (hR : IsSylow2In R H)
    (hpow : ∀ h ∈ H, ∃ n : ℕ, h ^ (2 ^ n) ∈ O) : H ≤ R ⊔ O := by
  have hN : (O.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mpr hHO
  let P : Sylow 2 ↥H :=
    { toSubgroup := R.subgroupOf H
      isPGroup' := hR.2.1.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hVQ : R ≤ Q.map H.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hR.1]
          exact Subgroup.map_mono hle
        have := hR.2.2 (Q.map H.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
        rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q, this]
        rfl }
  have hq : IsPGroup 2 (↥H ⧸ O.subgroupOf H) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H h =>
      obtain ⟨n, hn⟩ := hpow h h.2
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hn)
  set π := QuotientGroup.mk' (O.subgroupOf H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmap : (P : Subgroup ↥H).map π = ⊤ :=
    ((P.mapSurjective hπs).is_maximal' (hq.to_subgroup ⊤) le_top).symm
  have h1 := Subgroup.comap_map_eq π (P : Subgroup ↥H)
  rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥H) ∈ (P : Subgroup ↥H) ⊔ O.subgroupOf H := h1 ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem H.subtype hx'
  have hPR : (P : Subgroup ↥H).map H.subtype = R := Subgroup.map_subgroupOf_eq_of_le hR.1
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hOH, hPR] at h2
  exact h2

theorem oddCoreOf_inf_centralizer_le_OCW (hΩ : HypOmegaMod p f Ω) {J W : Subgroup G}
    (hJ : J ∈ Ω) {z : G} (hz : IsUniqueInvolution J z) (hzW : z ∈ W) :
    oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) ≤ OCW W := by
  obtain ⟨z', hz'⟩ := hΩ.classical J hJ
  have hz'2 : z' * z' = 1 := by rw [← pow_two, ← hz'.orderOf_eq_two, pow_orderOf_eq_one]
  have hz'1 : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hzz : z' = z := (hz.unique z' hz'.mem hz'2).resolve_left hz'1
  have hCW : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer ({z'} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hzz ▸ hzW))
  have h1 := isSubnormal_inf hz'.subnormal (Subgroup.centralizer (W : Set G))
  rw [inf_eq_right.mpr hCW] at h1
  rw [oddCoreOf_eq_oddCoreIn, OCW, oddCoreOf_eq_oddCoreIn]
  exact Balance.oddCoreIn_le_of_isSubnormal h1

theorem isSylow2In_of_mem_RSet_of_le (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {R J : Subgroup G}
    (hR : R ∈ RSet Ω) (hJ : J ∈ Ω) (hRJ : R ≤ J) : IsSylow2In R J := by
  obtain ⟨J', hJ', hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  rwa [hΩ.eq_of_le_of_le hJ' hJ hRJ'.2.1 (by omega) hRJ'.1 hRJ] at hRJ'

theorem keyOn (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (habel : EtaAbelian Ω)
    (h611 : EtaMeets Ω) : KeyOn Ω := by
  intro W hW R hR T hT J hJ hRJ hTJ
  have hRsyl := isSylow2In_of_mem_RSet_of_le hp hΩ hR.1 hJ hRJ
  have h8 := hΩ.eight_le_of_mem_RSet hp hR.1
  have hWJ := le_normalizer_of_mem_DSet hp hq hΩ habel h611 hW hR hJ hRJ
  obtain ⟨η, hη, hWη⟩ := id hW
  obtain ⟨S₁, hS₁⟩ := (IsPGroup.to_sup_of_normal_right' (isPGroup_of_mem_RSet hR.1)
    (isPGroup_of_mem_WSet hW) hR.2).exists_le_sylow
  have hJS₁ : 2 < Nat.card ↥(J ⊓ (S₁ : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hRJ (le_sup_left.trans hS₁))
    omega
  have hU : J ⊓ W ∈ η := by
    have := h611 S₁ η hη (fun V hV => (hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) V hV
      le_rfl : V ≤ W).trans (le_sup_right.trans hS₁)) J hJ hJS₁
    rwa [← hWη] at this
  have hUU := mem_USet_of_mem_etaG hη hU
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
  exact sup_le (le_sup_left.trans le_sup_left) (hOX.trans le_sup_right) (hle ⟨hTJ ht, hT.2 ht⟩)

variable (p f) in
theorem l7_1Key : L7_1Key p f := by
  intro G _ _ Ω hΩ
  have hp := hΩ.1
  have hq := hΩ.2.1
  have hmod := hΩ.2.2.1
  exact keyOn hp hq hmod (fun η ⟨S, hS, hinv⟩ => ((l6_9_proved p f hp hq G Ω hmod S).2 η hS hinv).1)
    (l6_11_proved p f hp hq G Ω hmod)

variable (p f) in
theorem l7_6_mod : L7_6ModTmp p f := l7_6ModTmp_of_key p f (l7_1Key p f)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
