module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Facts
public import CFSG.GH74.GLS.C3.Layer1.BkP85SpLift
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.TwoThin
open CFSG.GH74.GLS.C3.Layer1.Bk.J2C
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure P89Std (M W Q : Subgroup G) (v : G) (Ebar : Subgroup (Mb M)) : Prop where
  W_syl : IsSylowOf 2 W ⊤
  W_le : W ≤ M
  v_mem : v ∈ W
  v_two : orderOf v = 2
  v_cent : ∀ w ∈ W, v * w = w * v
  Q_le : Q ≤ W
  Q_card : Nat.card ↥Q = 4
  Q_elem : IsElementaryAbelian 2 ↥Q
  Q_cent : ∀ q ∈ Q, q ≠ 1 → centralizer ({q} : Set G) ≤ M
  Mb_card : Nat.card (Mb M) = 604800
  facts : J2CentFacts (Mb M) (barMk ↥M ⟨v, W_le v_mem⟩) Ebar

variable {M W Q : Subgroup G} {v : G} {Ebar : Subgroup (Mb M)}

namespace P89Std

variable (h : P89Std M W Q v Ebar)
include h

omit [Finite G] in
theorem v_mem_M : v ∈ M := h.W_le h.v_mem

noncomputable abbrev vb : Mb M := barMk ↥M ⟨v, h.v_mem_M⟩

theorem vb_two : orderOf h.vb = 2 :=
  orderOf_barMk ((Subgroup.orderOf_mk v h.v_mem_M).trans h.v_two)



omit [Finite G] h in
theorem imgM_top : imgM M M = ⊤ := by
  unfold imgM
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ barMk_surjective

theorem W_syl_M : IsSylowOf 2 W M := h.W_syl.of_le h.W_le le_top

theorem Wb_syl : IsSylowOf 2 (imgM M W) ⊤ := by
  have := isSylowOf_imgM_of_le (le_refl M) h.W_syl_M
  rwa [imgM_top] at this

theorem card_Wb : Nat.card ↥(imgM M W) = 2 ^ 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(h.Wb_syl).card_eq, Subgroup.card_top, h.Mb_card]
  rw [CFSG.GH74.Generic.S45.factorization_604800]


omit h in
theorem eq_of_barMk_eq {A : Subgroup G} (hAM : A ≤ M) (hA : IsPGroup 2 ↥A) {x y : G} (hx : x ∈ A)
    (hy : y ∈ A) (hxy : barMk ↥M ⟨x, hAM hx⟩ = barMk ↥M ⟨y, hAM hy⟩) : x = y := by
  have h1 : barMk ↥M ((⟨x, hAM hx⟩ : ↥M)⁻¹ * ⟨y, hAM hy⟩) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 : x⁻¹ * y ∈ pPrimeCoreOf 2 M := (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h1
  have h3 : x⁻¹ * y ∈ A ⊓ pPrimeCoreOf 2 M := ⟨A.mul_mem (A.inv_mem hx) hy, h2⟩
  rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot M hA, Subgroup.mem_bot] at h3
  exact (inv_mul_eq_one.1 h3)

omit [Finite G] in
theorem W_pGroup : IsPGroup 2 ↥W := h.W_syl.isPGroup

theorem card_W : Nat.card ↥W = 2 ^ 7 := by
  obtain ⟨e⟩ := equiv_imgM h.W_le h.W_pGroup
  rw [Nat.card_congr e.toEquiv, h.card_Wb]

omit [Finite G] in
theorem vb_cent_Wb : ∀ w ∈ imgM M W, w * h.vb = h.vb * w := by
  intro w hw
  obtain ⟨m, hm', rfl⟩ := mem_imgM_iff.1 hw
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h.v_cent _ hm').symm

omit [Finite G] in
theorem Wb_le_cent : imgM M W ≤ centralizer ({h.vb} : Set (Mb M)) := fun w hw =>
  mem_centralizer_singleton_iff.2 (h.vb_cent_Wb w hw)

omit [Finite G] in
theorem Ebar_pGroup : IsPGroup 2 ↥Ebar := IsPGroup.of_card (n := 5) (by
  rw [h.facts.card_E]
  norm_num)

theorem Ebar_le_Wb : Ebar ≤ imgM M W := by
  have hsyl : IsSylowOf 2 (imgM M W) (centralizer ({h.vb} : Set (Mb M))) :=
    h.Wb_syl.of_le h.Wb_le_cent le_top
  exact C3.Layer1.Bk.J2C.le_of_normal_isPGroup hsyl h.facts.E_le h.facts.E_normal h.Ebar_pGroup


end P89Std

@[expose] def W0 (M W : Subgroup G) (Ebar : Subgroup (Mb M)) : Subgroup G := W ⊓ preimgM M Ebar

omit [Finite G] in
theorem mem_W0_iff {x : G} :
    x ∈ W0 M W Ebar ↔ x ∈ W ∧ ∃ hx : x ∈ M, barMk ↥M ⟨x, hx⟩ ∈ Ebar := by
  unfold W0
  rw [Subgroup.mem_inf, mem_preimgM_iff]

omit [Finite G] in
theorem W0_le_W : W0 M W Ebar ≤ W := inf_le_left

namespace P89Std

variable (h : P89Std M W Q v Ebar)
include h

omit [Finite G] in
theorem W0_le_M : W0 M W Ebar ≤ M := (W0_le_W).trans h.W_le

omit [Finite G] in
theorem v_mem_W0 : v ∈ W0 M W Ebar :=
  mem_W0_iff.2 ⟨h.v_mem, h.v_mem_M, h.facts.t_mem⟩

omit [Finite G] in
theorem W0_pGroup : IsPGroup 2 ↥(W0 M W Ebar) := h.W_pGroup.to_le W0_le_W

theorem imgM_W0 : imgM M (W0 M W Ebar) = Ebar := by
  apply le_antisymm
  · intro e he
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 he
    obtain ⟨-, hmM, hmE⟩ := mem_W0_iff.1 hm
    exact hmE
  · intro e he
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 (h.Ebar_le_Wb he)
    exact mem_imgM_iff.2 ⟨m, mem_W0_iff.2 ⟨hm, m.2, he⟩, rfl⟩

theorem card_W0 : Nat.card ↥(W0 M W Ebar) = 32 := by
  obtain ⟨e⟩ := equiv_imgM h.W0_le_M h.W0_pGroup
  rw [Nat.card_congr e.toEquiv, h.imgM_W0, h.facts.card_E]

omit [Finite G] in
theorem W0_normal_W : ∀ w ∈ W, ∀ x ∈ W0 M W Ebar, w * x * w⁻¹ ∈ W0 M W Ebar := by
  intro w hw x hx
  obtain ⟨hxW, hxM, hxE⟩ := mem_W0_iff.1 hx
  have hwM : w ∈ M := h.W_le hw
  have hwc : barMk ↥M ⟨w, hwM⟩ ∈ centralizer ({h.vb} : Set (Mb M)) :=
    h.Wb_le_cent (mem_imgM_iff.2 ⟨⟨w, hwM⟩, hw, rfl⟩)
  have hM : w * x * w⁻¹ ∈ M := M.mul_mem (M.mul_mem hwM hxM) (M.inv_mem hwM)
  refine mem_W0_iff.2 ⟨W.mul_mem (W.mul_mem hw hxW) (W.inv_mem hw), hM, ?_⟩
  have h1 : (⟨w * x * w⁻¹, hM⟩ : ↥M) = ⟨w, hwM⟩ * ⟨x, hxM⟩ * ⟨w, hwM⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv]
  exact h.facts.E_normal _ hwc _ hxE

theorem W0_center : ∀ x ∈ W0 M W Ebar, (∀ y ∈ W0 M W Ebar, x * y = y * x) → x = 1 ∨ x = v := by
  intro x hx hxc
  obtain ⟨hxW, hxM, hxE⟩ := mem_W0_iff.1 hx
  have key : ∀ e ∈ Ebar, barMk ↥M ⟨x, hxM⟩ * e = e * barMk ↥M ⟨x, hxM⟩ := by
    intro e he
    have heW : e ∈ imgM M (W0 M W Ebar) := by rw [h.imgM_W0]; exact he
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 heW
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxc _ hm)
  rcases h.facts.center _ hxE key with h1 | h1
  · left
    exact eq_of_barMk_eq h.W_le h.W_pGroup hxW W.one_mem
      (by rw [h1]; exact (map_one _).symm)
  · right
    exact eq_of_barMk_eq h.W_le h.W_pGroup hxW h.v_mem h1

theorem cent_W0_in_W : ∀ g ∈ W, (∀ y ∈ W0 M W Ebar, g * y = y * g) → g = 1 ∨ g = v := by
  intro g hg hgc
  have hgM : g ∈ M := h.W_le hg
  have hgv : barMk ↥M ⟨g, hgM⟩ ∈ centralizer ({h.vb} : Set (Mb M)) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.v_cent g hg).symm
  have key : ∀ e ∈ Ebar, barMk ↥M ⟨g, hgM⟩ * e = e * barMk ↥M ⟨g, hgM⟩ := by
    intro e he
    have heW : e ∈ imgM M (W0 M W Ebar) := by rw [h.imgM_W0]; exact he
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 heW
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hgc _ hm)
  rcases h.facts.cent_E _ hgv key with h1 | h1
  · left
    exact eq_of_barMk_eq h.W_le h.W_pGroup hg W.one_mem
      (by rw [h1]; exact (map_one _).symm)
  · right
    exact eq_of_barMk_eq h.W_le h.W_pGroup hg h.v_mem h1

end P89Std

theorem le_M_of_sylow_two_card_two {D M Q W : Subgroup G} (hS : IsSylowOf 2 (W ⊓ D) D)
    (hW2 : Nat.card ↥(W ⊓ D) = 2) (hWM : W ≤ M)
    (hQnorm : Q ≤ normalizer (pPrimeCoreOf 2 D : Set G)) (hQcard : Nat.card ↥Q = 4)
    (hQpow : ∀ q : ↥Q, q ^ 2 = 1) (hQM : ∀ q ∈ Q, q ≠ 1 → centralizer ({q} : Set G) ≤ M) :
    D ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS
  have hPcard : Nat.card ↥(P : Subgroup ↥D) = 2 := by
    have h1 : Nat.card ↥(P : Subgroup ↥D) = Nat.card ↥(W ⊓ D) := by
      rw [← hP]
      exact (Subgroup.card_map_of_injective D.subtype_injective).symm
    exact h1.trans hW2
  have hPcyc : IsCyclic ↥(P : Subgroup ↥D) := isCyclic_of_prime_card hPcard
  obtain ⟨N, hNn, hNc⟩ := exists_normal_isComplement'_of_isCyclic_sylow_two P hPcyc
  have hNodd : ¬ 2 ∣ Nat.card ↥N := by
    have h1 := hNc.index_eq_card
    rw [← h1]
    exact P.not_dvd_index
  have hNle : N ≤ pPrimeCore 2 ↥D :=
    CFSG.GroupTheory.le_pPrimeCore_of_normal hNn
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hNodd)
  have hKodd : ¬ 2 ∣ Nat.card ↥(pPrimeCoreOf 2 D) := by
    have hodd := TwoThin.card_pPrimeCoreOf_odd D
    rw [Nat.odd_iff] at hodd
    omega
  have hKM : pPrimeCoreOf 2 D ≤ M := by
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      2 Nat.prime_two Q (pPrimeCoreOf 2 D) (fun q => hQpow q) hQcard hKodd hQnorm
    rw [hgen]
    exact iSup_le fun q => iSup_le fun hq =>
      inf_le_right.trans (hQM q q.2 (fun h => hq (Subtype.ext h)))
  intro d hd
  obtain ⟨⟨n, p⟩, hnp⟩ := hNc.2 (⟨d, hd⟩ : ↥D)
  have hnN : (n : ↥D) ∈ N := n.2
  have hpP : (p : ↥D) ∈ (P : Subgroup ↥D) := p.2
  have hnM : ((n : ↥D) : G) ∈ M := by
    have hn' : (n : ↥D) ∈ pPrimeCore 2 ↥D := hNle hnN
    exact hKM (Subgroup.mem_map.2 ⟨(n : ↥D), hn', rfl⟩)
  have hpW : ((p : ↥D) : G) ∈ W := by
    have : ((p : ↥D) : G) ∈ (P : Subgroup ↥D).map D.subtype :=
      Subgroup.mem_map.2 ⟨(p : ↥D), hpP, rfl⟩
    rw [hP] at this
    exact this.1
  have hd' : d = ((n : ↥D) : G) * ((p : ↥D) : G) := congrArg Subtype.val hnp.symm
  rw [hd']
  exact M.mul_mem hnM (hWM hpW)


namespace P89Std

variable (h : P89Std M W Q v Ebar)
include h

theorem W_le_normalizer_W0 : W ≤ normalizer (W0 M W Ebar : Set G) := fun w hw =>
  CFSG.GH74.Generic.S45.EvSpor.mem_normalizer_of_conj_le (h.W0_normal_W w hw)

omit [Finite G] h in
theorem cent_W0_le_normalizer : centralizer (W0 M W Ebar : Set G) ≤ normalizer (W0 M W Ebar : Set G) :=
  Subgroup.centralizer_le_normalizer _

omit [Finite G] h in
theorem normalizer_W0_le_normalizer_cent :
    normalizer (W0 M W Ebar : Set G) ≤ normalizer (centralizer (W0 M W Ebar : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro d
  have hn' := Subgroup.mem_normalizer_iff.1 hn
  have key : ∀ g : G, g ∈ normalizer (W0 M W Ebar : Set G) → ∀ d ∈ centralizer (W0 M W Ebar : Set G),
      g * d * g⁻¹ ∈ centralizer (W0 M W Ebar : Set G) := by
    intro g hg d hd
    rw [Subgroup.mem_centralizer_iff] at hd ⊢
    intro y hy
    have h1 := Subgroup.mem_normalizer_iff.1 hg
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ W0 M W Ebar :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    have := hd _ hy'
    calc y * (g * d * g⁻¹) = g * ((g⁻¹ * y * g) * d) * g⁻¹ := by group
      _ = g * (d * (g⁻¹ * y * g)) * g⁻¹ := by
        have h2 : g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ := by simp
        rw [h2, this]
      _ = g * d * g⁻¹ * y := by group
  constructor
  · intro hd
    exact key n hn d hd
  · intro hd
    have := key n⁻¹ (inv_mem hn) _ hd
    simpa [mul_assoc] using this


omit [Finite G] in
theorem Q_pow : ∀ q : ↥Q, q ^ 2 = 1 := fun q =>
  Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h.Q_elem.exponent_dvd_p q

theorem W_inf_cent_W0 : W ⊓ centralizer (W0 M W Ebar : Set G) = zpowers v := by
  ext x
  constructor
  · rintro ⟨hxW, hxD⟩
    rcases h.cent_W0_in_W x hxW
      (fun y hy => (Subgroup.mem_centralizer_iff.1 hxD y hy).symm) with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨W.zpow_mem h.v_mem k, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hc : Commute y v := (h.v_cent y (W0_le_W hy)).symm
    exact (hc.zpow_right k).eq

theorem cent_W0_le_M : centralizer (W0 M W Ebar : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWsylN : IsSylowOf 2 W (normalizer (W0 M W Ebar : Set G)) :=
    h.W_syl.of_le h.W_le_normalizer_W0 le_top
  have hS : IsSylowOf 2 (W ⊓ centralizer (W0 M W Ebar : Set G))
      (centralizer (W0 M W Ebar : Set G)) :=
    hWsylN.inf_of_le_normalizer cent_W0_le_normalizer normalizer_W0_le_normalizer_cent
  have hW2 : Nat.card ↥(W ⊓ centralizer (W0 M W Ebar : Set G)) = 2 := by
    rw [h.W_inf_cent_W0, Nat.card_zpowers, h.v_two]
  refine le_M_of_sylow_two_card_two hS hW2 h.W_le ?_ h.Q_card h.Q_pow h.Q_cent
  intro q hq
  exact TwoThin.mem_normalizer_pPrimeCoreOf
    (normalizer_W0_le_normalizer_cent (h.W_le_normalizer_W0 (h.Q_le hq)))

end P89Std

end CFSG.GH74.GLS.Th2.P85.Sp
