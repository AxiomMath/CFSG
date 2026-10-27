module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Contra
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9.Cl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Cfg (x y z : G) (L Bs D J E₀ : Subgroup G) : Prop where
  bs_bmax : GLAIsBmax 3 Bs
  D_le : D ≤ Bs
  D_el : IsElemAbelian 3 D
  D_card : Nat.card D = 3 ^ 2
  D_gen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y
  y_L : y ∈ L
  J_L : J ≤ L
  D_cJ : D ≤ Subgroup.centralizer (J : Set G)
  DJ : D ⊓ J = ⊥
  J_comp : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J
  J_type : catalogIs (PSimple 3 J) isU4two
  E₀_le : E₀ ≤ J
  E₀_el : IsElemAbelian 3 E₀
  E₀_card : Nat.card E₀ = 3 ^ 3
  z_J : z ∈ J
  z_sq : z ^ 2 = 1
  z_ne : z ≠ 1
  Bs_z : Bs ≤ cx z

theorem eq_one_of_mem_of_centMod {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hZ : Subgroup.center (PQuot p L) = ⊥) {g : G} (hgL : g ∈ L) (hg : CentMod p L g)
    (hgp : g ^ p = 1) : g = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : ⁅(u : G)⁻¹, g⁻¹⁆ ∈ GLAPPrimeCoreOf p L :=
      hg.2 (Subgroup.commutator_mem_commutator (L.inv_mem u.2)
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)))
    obtain ⟨o, ho, hoe⟩ := h1
    have heq : (u * (⟨g, hgL⟩ : ↥L))⁻¹ * ((⟨g, hgL⟩ : ↥L) * u) = o⁻¹ := by
      apply Subtype.ext
      have hoe' : (o : G) = ⁅(u : G)⁻¹, g⁻¹⁆ := hoe
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hoe', commutatorElement_def]
      group
    rw [heq]
    exact (GLAPPrimeCore p ↥L).inv_mem ho
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  by_contra hne
  have hord : orderOf g = p := orderOf_eq_prime hgp hne
  have hdvd : orderOf g ∣ Nat.card (GLAPPrimeCoreOf p L) :=
    Subgroup.orderOf_dvd_natCard _ ⟨⟨g, hgL⟩, hmem, rfl⟩
  rw [hord] at hdvd
  exact not_dvd_card_glaPPrimeCoreOf hp L hdvd

theorem D_facts {x y : G} {L J : Subgroup G} (hL : GLAPComponent 3 (cx x) L) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hxcm : CentMod 3 L x) (hZL : Subgroup.center (PQuot 3 L) = ⊥) (hyL : y ∈ L)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hJ : GLAPComponent 3 (L ⊓ cx y) J)
    (hZJ : Subgroup.center (PQuot 3 J) = ⊥) :
    IsElemAbelian 3 (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ∧
      Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = 3 ^ 2 ∧
      (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊓ J = ⊥ ∧
      Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer (J : Set G) := by
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hJL : J ≤ L := (hJ.1).trans inf_le_left
  have hJy : J ≤ cx y := (hJ.1).trans inf_le_right
  have hLx : L ≤ cx x := hL.1
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 (hLx hyL)).symm
  have hel : ∀ {w : G}, w ^ 3 = 1 → IsElemAbelian 3 (Subgroup.zpowers w) := by
    intro w hw
    refine ⟨inferInstance, fun v hv => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  have hxel : IsElemAbelian 3 (Subgroup.zpowers x) := hel hx3
  have hyel : IsElemAbelian 3 (Subgroup.zpowers y) := hel hy3
  have hcomm : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    rw [Subgroup.zpowers_le, S3.centralizer_zpowers, Subgroup.mem_centralizer_singleton_iff]
    exact hxy
  have hxcm' : Subgroup.zpowers x ≤ centModSubgroup 3 L := by
    rw [Subgroup.zpowers_le]
    exact centMod_iff.1 hxcm
  have hyx : y ∉ Subgroup.zpowers x := fun hy =>
    hy1 (eq_one_of_mem_of_centMod hp3 hZL hyL (centMod_iff.2 (hxcm' hy)) hy3)
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hinf : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers y : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers y : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤
        Subgroup.zpowers y)
      rwa [Nat.card_zpowers, hoy] at this
    rcases (Nat.dvd_prime hp3).1 hdvd with h | h
    · exact h
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge
        (inf_le_right : Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y)
        (by rw [h, Nat.card_zpowers, hoy])
      apply hyx
      have : y ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact this.1
  refine ⟨isElemAbelian_sup_of_commute hxel hyel hcomm, ?_, ?_, ?_⟩
  · have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
      (Subgroup.le_centralizer_iff.1 hcomm).trans (Subgroup.centralizer_le_normalizer _)
    have h := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hinf, mul_one, Nat.card_zpowers, Nat.card_zpowers, hox, hoy] at h
    rw [h]
    norm_num
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgD, hgJ⟩ := hg
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hgD
    have haL : a ∈ L := by
      have := L.mul_mem (hJL hgJ) (L.inv_mem (Subgroup.zpowers_le.2 hyL hb))
      simpa using this
    have ha1 : a = 1 :=
      eq_one_of_mem_of_centMod hp3 hZL haL (centMod_iff.2 (hxcm' ha)) (hxel.2 a ha)
    subst ha1
    rw [one_mul] at hgJ ⊢
    have hbJ : CentMod 3 J b := by
      refine ⟨?_, ?_⟩
      · refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hly : l ∈ Subgroup.centralizer ({y} : Set G) := hJy hl
        rw [← S3.centralizer_zpowers] at hly
        exact (Subgroup.mem_centralizer_iff.1 hly b hb).symm
      · rw [Subgroup.commutator_le]
        intro l hl k hk
        have hly : l ∈ Subgroup.centralizer ({y} : Set G) := hJy hl
        rw [← S3.centralizer_zpowers] at hly
        have hkb : k ∈ Subgroup.zpowers y := by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
          exact Subgroup.zpow_mem _ hb n
        have hc2 : l * k = k * l := (Subgroup.mem_centralizer_iff.1 hly k hkb).symm
        rw [commutatorElement_def, hc2]
        simp
    have := eq_one_of_mem_of_centMod hp3 hZJ hgJ hbJ (hyel.2 b hb)
    rw [this]
    exact Subgroup.one_mem _
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 (hLx (hJL hl))
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJy hl)

theorem bstar_facts {D E J : Subgroup G} {z : G} (hD : IsElemAbelian 3 D) (hE : IsElemAbelian 3 E)
    (hEJ : E ≤ J ⊓ cx z) (hDJ : D ≤ Subgroup.centralizer (J : Set G)) (hDJ' : D ⊓ J = ⊥)
    (hzJ : z ∈ J) :
    IsElemAbelian 3 (E ⊔ D) ∧ Nat.card (E ⊔ D : Subgroup G) = Nat.card E * Nat.card D ∧
      E ⊔ D ≤ cx z := by
  have hEJ' : E ≤ J := hEJ.trans inf_le_left
  have hEcD : E ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.le_centralizer_iff.1 (hDJ.trans (Subgroup.centralizer_le hEJ'))
  have hDnE : D ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.le_centralizer_iff.2 hEcD).trans (Subgroup.centralizer_le_normalizer _)
  have hinf : E ⊓ D = ⊥ := by
    rw [eq_bot_iff, ← hDJ']
    exact le_inf inf_le_right (inf_le_left.trans hEJ')
  refine ⟨isElemAbelian_sup_of_commute hE hD hEcD, ?_, sup_le (hEJ.trans inf_le_right) ?_⟩
  · have h := card_sup_mul_card_inf_of_le_normalizer hDnE
    rwa [hinf, Subgroup.card_bot, mul_one] at h
  · intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (hDJ hd) z hzJ).symm

theorem isPGroup_zpowers_of_sq {z : G} (hz2 : z ^ 2 = 1) : IsPGroup 2 (Subgroup.zpowers z) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    hz2, one_zpow]
  rfl

theorem centralizer_eq_inf_of_gen {D : Subgroup G} {u v : G}
    (hD : D = Subgroup.zpowers u ⊔ Subgroup.zpowers v) :
    Subgroup.centralizer (D : Set G) = cx u ⊓ cx v := by
  have hu : u ∈ D := hD ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hv : v ∈ D := hD ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hu))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hv))
  · intro g hg
    have hle : D ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [hD]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hg.1).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hg.2).symm
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)

theorem isTwoLocal_cx_of_sq {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : IsTwoLocal (cx z) := by
  have hord : orderOf z = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hz2 hz1
  have hzp : ∀ w ∈ Subgroup.zpowers z, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · left
      simp [h]
    · right
      simp [h]
  refine ⟨Subgroup.zpowers z, fun h => hz1 (Subgroup.zpowers_eq_bot.1 h), ?_, ?_⟩
  · exact isPGroup_zpowers_of_sq hz2
  · ext g
    constructor
    · intro hg
      have hg' : g ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
        rw [S3.centralizer_zpowers]
        exact hg
      exact Subgroup.centralizer_le_normalizer _ hg'
    · intro hg
      have h1 : g * z * g⁻¹ ∈ Subgroup.zpowers z :=
        (Subgroup.mem_normalizer_iff.1 hg z).1 (Subgroup.mem_zpowers z)
      rcases hzp _ h1 with h | h
      · exfalso
        apply hz1
        exact conj_eq_one_iff.1 h
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.1 h

theorem bmax_of_elem {Bs : Subgroup G} {z : G} (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 4) (hrank : GLATwoLocalRank 3 G = 4) (hBz : Bs ≤ cx z)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : GLAIsBmax 3 Bs := by
  refine ⟨hBs, by rw [hcard, hrank], Subgroup.zpowers z,
    fun h => hz1 (Subgroup.zpowers_eq_bot.1 h), isPGroup_zpowers_of_sq hz2, ?_⟩
  intro g hg
  have hg' : g ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [S3.centralizer_zpowers]
    exact hBz hg
  exact Subgroup.centralizer_le_normalizer _ hg'

theorem J_comp_centralizer {x y : G} {L J D : Subgroup G} (hL : GLAPComponent 3 (cx x) L)
    (hJ : GLAPComponent 3 (L ⊓ cx y) J) (hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hxD : x ∈ D := hD ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hcD : Subgroup.centralizer (D : Set G) = cx x ⊓ cx y := centralizer_eq_inf_of_gen hD
  have hLeq : L ⊓ cx y = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hcD]
    apply le_antisymm
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hL.1) inf_le_right)
    · exact inf_le_inf_left L inf_le_right
  have hsn : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G))
      (cx x ⊓ Subgroup.centralizer (D : Set G)) := isSubnormal_inf hL.2.1 _
  have hcx : cx x ⊓ Subgroup.centralizer (D : Set G) = Subgroup.centralizer (D : Set G) :=
    inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD))
  rw [hcx] at hsn
  rw [hLeq] at hJ
  exact glaPComponent_of_isSubnormal' hp3 hsn hJ

theorem exists_cfg (hc : S9Ctx G 3) (h23 : Rank23At G) (h81 : I81U5At G) (h2811 : I2811At G)
    (h102 : I102U4At G) {q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G}
    (hC : Contra92 3 B x L q Q₁) (hB : Concl96 3 B x L Q₁) :
    ∃ (Bs D J E₀ : Subgroup G) (y z : G), Cfg x y z L Bs D J E₀ := by
  have hp3 : Nat.Prime 3 := hc.ctx.prime
  have hL : GLAPComponent 3 (cx x) L := hC.h.comp
  have hX : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_cx hc hC.h.ne_one
  obtain ⟨y, hyL, hy3, hy1, J, hJ, hJt, hJO⟩ := h81 (cx x) L hX hL hB.type
  have hZL : Subgroup.center (PQuot 3 L) = ⊥ :=
    (h23 (cx x) L hL (catalogIs_mono (fun i hi => Or.inr (Or.inr (Or.inr hi))) hB.type)).1
  have hZJ : Subgroup.center (PQuot 3 J) = ⊥ :=
    (h23 (L ⊓ cx y) J hJ (catalogIs_mono (fun i hi => Or.inr (Or.inl hi)) hJt)).1
  have hoddL : Odd (Nat.card (GLAPPrimeCoreOf 3 L)) :=
    hB.odd.of_dvd_nat (Subgroup.card_dvd_of_le (glaPPrimeCoreOf_le_of_isSubnormal hp3 hL.2.1))
  have hoddJ : Odd (Nat.card (GLAPPrimeCoreOf 3 J)) :=
    hoddL.of_dvd_nat (Subgroup.card_dvd_of_le hJO)
  obtain ⟨z, hzJ, hz2, hz1, E, hEJ, hEel, hEc⟩ := h2811 (L ⊓ cx y) J hJ hJt hoddJ
  obtain ⟨E₀, hE₀J, hE₀el, hE₀c⟩ := h102 (L ⊓ cx y) J hJ hJt
  have hx3 : x ^ 3 = 1 := hC.h.bmax.1.2 x hC.h.mem
  have hxcm : CentMod 3 L x := (hC.h.cent x hC.h.mem).2 (Subgroup.mem_zpowers x)
  obtain ⟨hDel, hDc, hDJ, hDcJ⟩ := D_facts hL hx3 hC.h.ne_one hxcm hZL hyL hy3 hy1 hJ hZJ
  obtain ⟨hBel, hBc, hBz⟩ := bstar_facts hDel hEel hEJ hDcJ hDJ hzJ
  have hrank : GLATwoLocalRank 3 G = 4 := by
    have h1 : 3 ^ GLATwoLocalRank 3 G = 3 ^ 4 := hC.h.bmax.2.1.symm.trans hB.card
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hBc' : Nat.card (E ⊔ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Subgroup G) = 3 ^ 4 := by
    rw [hBc, hEc, hDc]
    norm_num
  exact ⟨E ⊔ (Subgroup.zpowers x ⊔ Subgroup.zpowers y), Subgroup.zpowers x ⊔ Subgroup.zpowers y, J, E₀,
    y, z, bmax_of_elem hBel hBc' hrank hBz hz2 hz1, le_sup_right, hDel, hDc, rfl, hyL,
    (hJ.1).trans inf_le_left, hDcJ, hDJ, J_comp_centralizer hL hJ rfl, hJt, hE₀J, hE₀el, hE₀c, hzJ,
    hz2, hz1, hBz⟩

end CFSG.LocalAnalysis.GLTheoremA.S9.Cl
