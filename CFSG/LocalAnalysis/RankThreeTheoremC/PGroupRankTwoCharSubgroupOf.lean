module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFiveDefs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_map_of_characteristic {Q : Subgroup G} (K : Subgroup Q)
    [K.Characteristic] :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (K.map Q.subtype : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∀ x ∈ K.map Q.subtype,
      g * x * g⁻¹ ∈ K.map Q.subtype := by
    rintro g hg _ ⟨k, hk, rfl⟩
    set φ : MulAut Q := Q.normalizerMonoidHom ⟨g, hg⟩
    have hφ : K.map φ.toMonoidHom = K := Subgroup.characteristic_iff_map_eq.mp inferInstance φ
    have hk' : φ k ∈ K := by
      rw [← hφ]
      exact ⟨k, hk, rfl⟩
    exact ⟨φ k, hk', rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

section InQ

variable {P : Type} [Group P] [Finite P] {p : ℕ}

theorem card_sup_of_commute_of_disjoint' {F K : Subgroup P}
    (hc : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f) (hd : F ⊓ K = ⊥) :
    Nat.card ↥(F ⊔ K) = Nat.card F * Nat.card K := by
  have hcomm : ∀ (m : ↥F) (n : ↥K), Commute (F.subtype m) (K.subtype n) :=
    fun m n => hc m m.2 n n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod F.subtype K.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨F.subtype_injective, K.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange := MonoidHom.noncommCoprod_range F.subtype K.subtype hcomm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem isElemAbelian_sup_zpowers [hp : Fact p.Prime] {E : Subgroup P}
    (hE : IsElemAbelian p E) {c : P} (hcE : c ∉ E) (hc : orderOf c = p)
    (hcc : ∀ a ∈ E, a * c = c * a) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers c) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers c) = Nat.card E * p := by
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hcp : c ^ p = 1 := hc ▸ pow_orderOf_eq_one c
  have hyC : c ∈ Subgroup.centralizer (E : Set P) := Subgroup.mem_centralizer_iff.2 hcc
  have hEC : E ≤ Subgroup.centralizer (E : Set P) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hEc b hb a ha
  have hyy : c ∈ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup P) : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (Commute.refl c) k).eq
  have h1 : E ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer (E : Set P) :=
    sup_le hEC ((Subgroup.zpowers_le).2 hyC)
  have h2 : E ⊔ Subgroup.zpowers c ≤
      Subgroup.centralizer ((Subgroup.zpowers c : Subgroup P) : Set P) :=
    sup_le (Subgroup.le_centralizer_iff.1 ((Subgroup.zpowers_le).2 hyC))
      ((Subgroup.zpowers_le).2 hyy)
  have hcent : E ⊔ Subgroup.zpowers c ≤
      Subgroup.centralizer ((E ⊔ Subgroup.zpowers c : Subgroup P) : Set P) :=
    sup_le (Subgroup.le_centralizer_iff.1 h1) (Subgroup.le_centralizer_iff.1 h2)
  have hcomm : ∀ a ∈ E ⊔ Subgroup.zpowers c, ∀ b ∈ E ⊔ Subgroup.zpowers c, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hcent hb) a ha
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun a ha => ?_⟩, ?_⟩
  · have key : a ∈ E ⊔ Subgroup.zpowers c ∧ a ^ p = 1 := by
      rw [Subgroup.sup_eq_closure] at ha
      induction ha using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact ⟨Subgroup.mem_sup_left hx, hE.2 x hx⟩
        · refine ⟨Subgroup.mem_sup_right hx, ?_⟩
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
      | one => exact ⟨one_mem _, one_pow p⟩
      | mul a b _ _ ha hb =>
        exact ⟨mul_mem ha.1 hb.1, by
          rw [(Commute.mul_pow (hcomm a ha.1 b hb.1)), ha.2, hb.2, one_mul]⟩
      | inv a _ ha => exact ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩
    exact key.2
  · have hcard : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hc]
    have hd : E ⊓ Subgroup.zpowers c = ⊥ := by
      have hdvd : Nat.card ↥(E ⊓ Subgroup.zpowers c) ∣ p :=
        hcard ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
      · exact Subgroup.card_eq_one.1 h
      · exfalso
        have heq : E ⊓ Subgroup.zpowers c = Subgroup.zpowers c :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcard])
        have hy' : c ∈ E ⊓ Subgroup.zpowers c := by rw [heq]; exact Subgroup.mem_zpowers c
        exact hcE hy'.1
    rw [card_sup_of_commute_of_disjoint' (fun a ha b hb => ?_) hd, hcard]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hcc a ha) k).eq

theorem isElemAbelian_zpowers {z : P} (hz : z ^ p = 1) : IsElemAbelian p (Subgroup.zpowers z) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self z i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

theorem exists_characteristic_rankTwo [hp : Fact p.Prime] (hp2 : p ≠ 2) (hP : IsPGroup p P)
    (hrk : Open.pRank p (⊤ : Subgroup P) = 2) :
    ∃ D : Subgroup P, D.Characteristic ∧ 2 ≤ Open.pRank p D ∧
      ((IsElemAbelian p D ∧ Nat.card D = p ^ 2) ∨ IsExtraspecialExpP p D) := by
  have hp1 := hp.out.one_lt
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup P)
  rw [hrk] at hEc
  haveI : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Nat.card E ≤ 1 := by
      rw [← Nat.card_unique (α := P)]
      exact Subgroup.card_le_card_group E
    rw [hEc] at this
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
    omega
  obtain ⟨D, hDc, hDne, hDp, hDZ, htors, -⟩ := CFSG.SectionRank.Ccomm.supercritical_witness hp2 hP
  haveI := hDc
  refine ⟨D, hDc, ?_⟩
  have hD2 : 2 ≤ Open.pRank p D := by
    by_contra hlt
    push Not at hlt
    haveI : Group.IsNilpotent P := hP.isNilpotent
    have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hDne
    obtain ⟨⟨z, hzD, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
    have hzp : (z : P) ^ p = 1 := hDp z hzD
    have hzord : orderOf (z : P) = p :=
      orderOf_eq_prime hzp fun h => hz1 (Subtype.ext h)
    have hDz : D ≤ Subgroup.zpowers (z : P) := by
      intro x hx
      by_contra hxz
      have hcomm : ∀ a ∈ Subgroup.zpowers (z : P), a * x = x * a := by
        intro a ha
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        exact ((show Commute z x from (Subgroup.mem_center_iff.1 hzZ x).symm).zpow_left i).eq
      have hxord : orderOf x = p := by
        refine orderOf_eq_prime (hDp x hx) fun h => hxz ?_
        rw [h]; exact one_mem _
      obtain ⟨hF, hFc⟩ := isElemAbelian_sup_zpowers (isElemAbelian_zpowers hzp) hxz hxord
        hcomm
      have hFD : Subgroup.zpowers (z : P) ⊔ Subgroup.zpowers x ≤ D :=
        sup_le ((Subgroup.zpowers_le).2 hzD) ((Subgroup.zpowers_le).2 hx)
      have := CFSG.SectionRank.le_pRank (k := 2) hp1 hFD hF (by
        rw [hFc, Nat.card_zpowers, hzord]; ring)
      omega
    have hcen : Subgroup.centralizer (D : Set P) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hDz hd)
      exact ((show Commute z y from (Subgroup.mem_center_iff.1 hzZ y).symm).zpow_left i).eq
    have hEz : E ≤ Subgroup.zpowers (z : P) := by
      intro e he
      by_cases he1 : e = 1
      · rw [he1]; exact one_mem _
      · have hord : orderOf e = p := orderOf_eq_prime (hE.2 e he) he1
        exact hDz (htors e (hcen ▸ Subgroup.mem_top e) hord)
    have := Subgroup.card_le_of_le hEz
    rw [hEc, Nat.card_zpowers, hzord] at this
    have : p < p ^ 2 := by nlinarith
    omega
  refine ⟨hD2, ?_⟩
  have hDrk : Open.pRank p (⊤ : Subgroup D) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    rw [← hrk]
    exact CFSG.SectionRank.pRank_mono hp1 le_top
  obtain ⟨hD3, -⟩ := CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound
    (hP.to_subgroup D) (fun x => Subtype.ext (by simpa using hDp x x.2)) hDrk
  obtain ⟨k, hk⟩ := (hP.to_subgroup D).exists_card_eq
  obtain ⟨E₂, hE₂D, hE₂, hE₂c⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hD2
  have hk2 : 2 ≤ k := by
    have h1 := Subgroup.card_dvd_of_le hE₂D
    rw [hE₂c, hk] at h1
    exact (Nat.pow_dvd_pow_iff_le_right hp1).mp h1
  have hk3 : k ≤ 3 := by
    rw [hk] at hD3
    exact (Nat.pow_le_pow_iff_right hp1).mp hD3
  by_cases hab : IsMulCommutative D
  · left
    have hDel : IsElemAbelian p D := ⟨hab, hDp⟩
    refine ⟨hDel, ?_⟩
    have := CFSG.SectionRank.le_pRank hp1 le_rfl hDel hk
    have hk' : k ≤ 2 := this.trans (by
      rw [← hrk]; exact CFSG.SectionRank.pRank_mono hp1 le_top)
    rw [hk, show k = 2 by omega]
  · right
    refine ⟨hab, ?_, hDp⟩
    rw [hk]
    congr 1
    by_contra hk3'
    have hk2' : k = 2 := by omega
    apply hab
    exact ⟨⟨fun a b => Subtype.ext (by
      have := IsPGroup.commutative_of_card_eq_prime_sq (p := p) (hk2' ▸ hk) a b
      exact congrArg Subtype.val this)⟩⟩

end InQ

theorem pGroupRankTwoCharSubgroup : PGroupRankTwoCharSubgroup G := by
  intro p hp hp2 Q hQ hrk
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hrk
  obtain ⟨D, hDc, hD2, hD⟩ := exists_characteristic_rankTwo hp2 hQ hrk
  haveI := hDc
  set Y := D.map Q.subtype with hYdef
  have e : D ≃* Y := D.equivMapOfInjective Q.subtype Q.subtype_injective
  have hYc : Nat.card Y = Nat.card D := Subgroup.card_map_of_injective Q.subtype_injective
  have hY2 : 2 ≤ Open.pRank p Y := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank, ← CFSG.pRank_congr_of_mulEquiv e,
      CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hD2
  refine ⟨Y, Subgroup.map_subtype_le D, normalizer_le_normalizer_map_of_characteristic D, hY2, ?_⟩
  rcases hD with ⟨hDel, hDcard⟩ | ⟨hab, hDcard, hDp⟩
  · exact Or.inl ⟨CFSG.SectionRank.isElemAbelian_map hDel Q.subtype, hYc.trans hDcard⟩
  · refine Or.inr ⟨fun h => hab ?_, hYc.trans hDcard, ?_⟩
    · haveI := h
      exact ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul]
        exact h.is_comm.comm (e a) (e b))⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hDp y hy, Subgroup.coe_one]

end CFSG.LocalAnalysis.RankThreeTheoremC
