module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootCentralizer
public import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomes
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSectionsBender
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_of_card)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem injective_mk'_comp_of_isPGroup (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card O))
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) :
    Function.Injective ((QuotientGroup.mk' O).comp Q.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxO : (x : X) ∈ O := (QuotientGroup.eq_one_iff _).1 hx
  obtain ⟨k, hk⟩ := hQ x
  have h1 : orderOf (x : X) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf (x : X) ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨x, hxO⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2))

omit [Finite X] in
theorem eq_of_mk'_eq_of_isPGroup (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card O))
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) {x y : X} (hx : x ∈ Q) (hy : y ∈ Q)
    (h : QuotientGroup.mk' O x = QuotientGroup.mk' O y) : x = y :=
  congrArg Subtype.val (injective_mk'_comp_of_isPGroup O hO hQ
    (show (QuotientGroup.mk' O).comp Q.subtype ⟨x, hx⟩ =
      (QuotientGroup.mk' O).comp Q.subtype ⟨y, hy⟩ from h))

omit [Finite X] in
theorem card_map_mk'_of_isPGroup (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card O))
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) :
    Nat.card (Q.map (QuotientGroup.mk' O)) = Nat.card Q := by
  have hinj := injective_mk'_comp_of_isPGroup O hO hQ
  have hr : ((QuotientGroup.mk' O).comp Q.subtype).range = Q.map (QuotientGroup.mk' O) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_lift_of_odd (O : Subgroup X) [O.Normal] {Qb : Subgroup (X ⧸ O)}
    (hQb : IsPGroup 2 Qb) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPQ : P.map (QuotientGroup.mk' O) ≤ Qb) :
    ∃ Q : Subgroup X, P ≤ Q ∧ IsPGroup 2 Q ∧ Q.map (QuotientGroup.mk' O) = Qb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' O with hπ
  set Y := Qb.comap π with hY
  have hPY : P ≤ Y := map_le_iff_le_comap.1 hPQ
  let πY : Y →* Qb := (π.comp Y.subtype).codRestrict Qb fun y => y.2
  have hπY : Function.Surjective πY := by
    intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective O (q : X ⧸ O)
    exact ⟨⟨x, show π x ∈ Qb by rw [hπ, hx]; exact q.2⟩, Subtype.ext hx⟩
  have hP' : IsPGroup 2 (P.subgroupOf Y) := hP.comap_subtype
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  have htop : ((S.mapSurjective hπY : Sylow 2 Qb) : Subgroup Qb) = ⊤ :=
    ((S.mapSurjective hπY).3 (hQb.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(S : Subgroup Y).map Y.subtype, fun x hx => ⟨⟨x, hPY hx⟩, hS hx, rfl⟩,
    S.isPGroup'.map _, ?_⟩
  have hcomp : π.comp Y.subtype = Qb.subtype.comp πY := by
    ext y
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map,
    range_subtype]

omit [Finite X] in
theorem exists_isSylowOf_ge {K B : Subgroup X} (hBK : B ≤ K) (hB : IsPGroup 2 B) :
    ∃ P : Subgroup X, IsSylowOf 2 P K ∧ B ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hB.comap_subtype (K := K)).exists_le_sylow
  exact ⟨_, ⟨S, rfl⟩, fun x hx => ⟨⟨x, hBK hx⟩, hS hx, rfl⟩⟩

theorem exists_conj_le_of_isSylowOf {P K B : Subgroup X} (hP : IsSylowOf 2 P K) (hBK : B ≤ K)
    (hB : IsPGroup 2 B) : ∃ k ∈ K, ∀ x ∈ B, k⁻¹ * x * k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP', hBP'⟩ := exists_isSylowOf_ge hBK hB
  obtain ⟨k, hk, hk'⟩ := hP.exists_mem_conj hP'
  exact ⟨k, hk, fun x hx => (hk' x).mp (hBP' hx)⟩

theorem le_zpowers_of_inf_centralizer_le {S : Subgroup X} (hS : IsPGroup 2 S) {t : X}
    (htt : t * t = 1) (htS : t ∈ S) (hC : S ⊓ centralizer ({t} : Set X) ≤ zpowers t) :
    S ≤ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases ht1 : t = 1
  · subst ht1
    intro s hs
    exact hC (mem_inf.2 ⟨hs, mem_centralizer_singleton_iff.2 (by rw [mul_one, one_mul])⟩)
  have : Nontrivial S := ⟨⟨⟨t, htS⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
  have := hS.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : center S)
  have hzS : ((z : S) : X) ∈ S ⊓ centralizer ({t} : Set X) := by
    refine mem_inf.2 ⟨(z : S).2, mem_centralizer_singleton_iff.2 ?_⟩
    have := mem_center_iff.1 z.2 ⟨t, htS⟩
    exact (congrArg Subtype.val this).symm
  have hzt : ((z : S) : X) = t := by
    rcases eq_one_or_eq_of_mem_zpowers htt (hC hzS) with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hz
    · exact h1
  intro s hs
  refine hC (mem_inf.2 ⟨hs, mem_centralizer_singleton_iff.2 ?_⟩)
  have := mem_center_iff.1 z.2 ⟨s, hs⟩
  have h2 := congrArg Subtype.val this
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mk, hzt] at h2
  exact h2

omit [Finite X] in
theorem exists_inv_mul_mem_centralizer_of_odd_outer {L : Subgroup X}
    (hOut : Odd (Nat.card (Outer L))) {x : X} (hxN : x ∈ normalizer (L : Set X)) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : ∃ l ∈ L, l⁻¹ * x ∈ centralizer (L : Set X) := by
  have hαk : L.normalizerMonoidHom ⟨x, hxN⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : normalizer (L : Set X)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer L)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hOut)
  have h1 : orderOf ((L.normalizerMonoidHom ⟨x, hxN⟩ : MulAut L) : Outer L) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hαk, QuotientGroup.mk_one]))
      (_root_.orderOf_dvd_natCard _)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, y.2, ?_⟩
  rw [mem_centralizer_iff]
  intro z hz
  have h2 := congrArg (fun φ : MulAut L => ((φ ⟨z, hz⟩ : L) : X)) hy
  simp only [MulAut.conj_apply, coe_mul, coe_inv, normalizerMonoidHom_apply_apply_coe] at h2
  calc z * ((y : X)⁻¹ * x) = (y : X)⁻¹ * (y * z * (y : X)⁻¹) * x := by group
    _ = (y : X)⁻¹ * (x * z * x⁻¹) * x := by rw [h2]
    _ = (y : X)⁻¹ * x * z := by group

theorem exists_lift_benderSylow_of_odd (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card O))
    {a : X} {V : Subgroup X} (hV : IsPGroup 2 (V ⊔ zpowers a : Subgroup X))
    {D Wb : Subgroup (X ⧸ O)} [D.Normal]
    (hB : BenderSylow D (QuotientGroup.mk' O a) (V.map (QuotientGroup.mk' O)) Wb)
    (hC : IsSylowOf 2 (V.map (QuotientGroup.mk' O) ⊔ zpowers (QuotientGroup.mk' O a))
      (centralizer ({QuotientGroup.mk' O a} : Set (X ⧸ O))))
    (hcent : ∀ o ∈ O, (∀ x ∈ V ⊔ zpowers a, o⁻¹ * x * o = x) →
      ∃ z ∈ center X, ∃ c ∈ zpowers a, o = z * c) :
    ∃ W : Subgroup X, BenderSylow W a V W ∧
      (∀ S : Subgroup X, IsPGroup 2 S → V ⊔ zpowers a ≤ S → S ≤ W ⊔ zpowers a) ∧
      ∀ x : X, x * a = a * x → x ∈ normalizer (V : Set X) → ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' O with hπ
  set tb := π a with htb
  have hVTmap : (V ⊔ zpowers a).map π = V.map π ⊔ zpowers tb := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  have hVTle : (V ⊔ zpowers a).map π ≤ Wb ⊔ zpowers tb := by
    rw [hVTmap]
    exact sup_le_sup_right hB.le _
  obtain ⟨Q, hVTQ, hQ2, hQmap⟩ := exists_lift_of_odd O hB.isPGroup_sup hV hVTle
  set WX : Subgroup X := Q ⊓ Wb.comap π with hWXdef
  have haQ : a ∈ Q := hVTQ (mem_sup_right (mem_zpowers _))
  have hVQ : V ≤ Q := le_sup_left.trans hVTQ
  have hWXQ : WX ≤ Q := inf_le_left
  have hWXmap : WX.map π = Wb := by
    apply le_antisymm
    · exact (map_mono inf_le_right).trans (map_comap_le _ _)
    · intro w hw
      have hw' : w ∈ Q.map π := by
        rw [hQmap]
        exact mem_sup_left hw
      obtain ⟨q, hq, rfl⟩ := hw'
      exact ⟨q, mem_inf.2 ⟨hq, hw⟩, rfl⟩
  have hQWt : Q ≤ WX ⊔ zpowers a := by
    intro q hq
    have hqb : π q ∈ Wb ⊔ zpowers tb := by
      rw [← hQmap]
      exact mem_map_of_mem π hq
    obtain ⟨wb, hwb, hcase⟩ := exists_eq_or_eq_mul_of_mem_sup hB.mul_self hB.mem_normalizer hqb
    rw [← hWXmap] at hwb
    obtain ⟨w, hw, rfl⟩ := hwb
    rcases hcase with hc | hc
    · have := eq_of_mk'_eq_of_isPGroup O hO hQ2 hq (hWXQ hw) hc
      rw [this]
      exact mem_sup_left hw
    · have := eq_of_mk'_eq_of_isPGroup O hO hQ2 hq (mul_mem (hWXQ hw) haQ)
        (by rw [map_mul]; exact hc)
      rw [this]
      exact mul_mem (mem_sup_left hw) (mem_sup_right (mem_zpowers _))
  set ψ : Q →* X ⧸ O := π.comp Q.subtype with hψdef
  have hψ : Function.Injective ψ := injective_mk'_comp_of_isPGroup O hO hQ2
  have hVQmap : (V.subgroupOf Q).map ψ = V.map π := by
    rw [hψdef, ← Subgroup.map_map, subgroupOf_map_subtype, inf_eq_left.2 hVQ]
  have hWQmap : (WX.subgroupOf Q).map ψ = Wb := by
    rw [hψdef, ← Subgroup.map_map, subgroupOf_map_subtype, inf_eq_left.2 hWXQ, hWXmap]
  have haQ' : ψ ⟨a, haQ⟩ = tb := rfl
  have hB' := hB
  rw [← hVQmap, ← hWQmap, ← haQ'] at hB'
  have hBX := ((BenderSylow.comap hψ hB').self).map (subtype_injective Q)
  have e1 : (V.subgroupOf Q).map Q.subtype = V := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hVQ]
  have e2 : (WX.subgroupOf Q).map Q.subtype = WX := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hWXQ]
  rw [e1, e2] at hBX
  have hcap : ∀ y ∈ Q, π y ∈ D → y ∈ WX := by
    intro y hy hyD
    have hyb : π y ∈ Wb ⊔ zpowers tb := by
      rw [← hQmap]
      exact mem_map_of_mem π hy
    obtain ⟨wb, hwb, hcase⟩ := exists_eq_or_eq_mul_of_mem_sup hB.mul_self hB.mem_normalizer hyb
    rcases hcase with hc | hc
    · exact mem_inf.2 ⟨hy, by rw [mem_comap, hc]; exact hwb⟩
    · refine absurd ?_ hB.not_mem
      have e : tb = wb⁻¹ * π y := by rw [hc]; group
      rw [e]
      exact mul_mem (inv_mem (hB.le_D hwb)) hyD
  have huniq : ∀ S : Subgroup X, IsPGroup 2 S → V ⊔ zpowers a ≤ S → S ≤ WX ⊔ zpowers a := by
    intro S hS2 hVS
    have hSb : S.map π ≤ Wb ⊔ zpowers tb :=
      hB.le_sup_of_isPGroup hC (hS2.map π) (hVTmap ▸ map_mono hVS)
    set Y : Subgroup X := (Wb ⊔ zpowers tb).comap π with hYdef
    have hSY : S ≤ Y := map_le_iff_le_comap.1 hSb
    have hQY : Q ≤ Y := map_le_iff_le_comap.1 hQmap.le
    have hQsyl : IsSylowOf 2 Q Y := by
      refine isSylowOf_of_forall_card_le hQY hQ2 fun R hRY hR2 => ?_
      calc Nat.card R = Nat.card (R.map π) := (card_map_mk'_of_isPGroup O hO hR2).symm
        _ ≤ Nat.card (Wb ⊔ zpowers tb : Subgroup (X ⧸ O)) :=
            Subgroup.card_le_of_le (map_le_iff_le_comap.2 hRY)
        _ = Nat.card (Q.map π) := by rw [hQmap]
        _ = Nat.card Q := card_map_mk'_of_isPGroup O hO hQ2
    obtain ⟨g, hgY, hg⟩ := exists_conj_le_of_isSylowOf hQsyl hSY hS2
    have hgQ : π g ∈ Q.map π := by
      rw [hQmap]
      exact hgY
    obtain ⟨q, hq, hqg⟩ := hgQ
    set o : X := g * q⁻¹ with hodef
    have ho : o ∈ O := by
      rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, hodef, map_mul, map_inv, ← hπ, hqg,
        mul_inv_cancel]
    have hπo : π o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    have hoQ : ∀ x ∈ S, o⁻¹ * x * o ∈ Q := by
      intro x hx
      have h1 : g⁻¹ * x * g ∈ Q := hg x hx
      have h2 : o⁻¹ * x * o = q * (g⁻¹ * x * g) * q⁻¹ := by
        rw [hodef]
        group
      rw [h2]
      exact mul_mem (mul_mem hq h1) (inv_mem hq)
    have hoc : ∀ x ∈ V ⊔ zpowers a, o⁻¹ * x * o = x := by
      intro x hx
      refine eq_of_mk'_eq_of_isPGroup O hO hQ2 (hoQ x (hVS hx)) (hVTQ hx) ?_
      rw [map_mul, map_mul, map_inv, hπo, inv_one, one_mul, mul_one]
    obtain ⟨z, hz, c, hc, hozc⟩ := hcent o ho hoc
    have hcQ : c ∈ Q := (zpowers_le.2 haQ) hc
    intro x hx
    apply hQWt
    have h1 := hoQ x hx
    have h2 : o⁻¹ * x * o = c⁻¹ * x * c := by
      have hzx : z⁻¹ * x * z = x := by
        rw [mul_assoc, mem_center_iff.1 hz x]
        group
      rw [hozc, mul_inv_rev, show c⁻¹ * z⁻¹ * x * (z * c) = c⁻¹ * (z⁻¹ * x * z) * c by group, hzx]
    rw [h2] at h1
    have h3 : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [h3]
    exact mul_mem (mul_mem hcQ h1) (inv_mem hcQ)
  refine ⟨WX, hBX, huniq, ?_⟩
  intro x hxa hxV w hw
  have hxa' : x * a * x⁻¹ = a := by rw [hxa, mul_inv_cancel_right]
  have hS : ((WX ⊔ zpowers a).map (MulAut.conj x).toMonoidHom) ≤ WX ⊔ zpowers a := by
    refine huniq _ (hBX.isPGroup_sup.map _) (sup_le (fun v hv => ?_) (zpowers_le.2 ?_))
    · refine ⟨x⁻¹ * v * x, mem_sup_left (hBX.le ?_), ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem hxV) v).1 hv
        rwa [inv_inv] at this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · exact ⟨a, mem_sup_right (mem_zpowers a), hxa'⟩
  have h1 : x * w * x⁻¹ ∈ WX ⊔ zpowers a := hS ⟨w, mem_sup_left hw, rfl⟩
  refine hcap _ (sup_le hWXQ (zpowers_le.2 haQ) h1) ?_
  rw [map_mul, map_mul, map_inv]
  exact (inferInstance : D.Normal).conj_mem _ (hB.le_D (mem_comap.1 (mem_inf.1 hw).2)) _

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

abbrev CH (i : Idx) : Subgroup G := centralizer (h.Ht i : Set G)

theorem t_mem_CH (i : Idx) : h.t ∈ h.CH i :=
  mem_centralizer_iff.2 fun _ hy => (h.t_commute_L (h.pull_le_L _ hy)).symm

abbrev tH (i : Idx) : h.CH i := ⟨h.t, h.t_mem_CH i⟩

abbrev NH (i : Idx) : Subgroup (h.CH i) := (h.N i).subgroupOf (h.CH i)

abbrev VH (i : Idx) : Subgroup (h.CH i) := (h.V i).subgroupOf (h.CH i)

theorem map_NH {i : Idx} (hi : i.isCenter = false) : (h.NH i).map (h.CH i).subtype = h.N i := by
  rw [subgroupOf_map_subtype, inf_eq_left.2 (h.levi_core_G hi).2.1]

theorem map_VH {i : Idx} (hi : i.isCenter = false) : (h.VH i).map (h.CH i).subtype = h.V i := by
  rw [subgroupOf_map_subtype, inf_eq_left.2 (h.V_le_centralizer_Ht hi)]

theorem CH_ne_top (i : Idx) : h.CH i ≠ ⊤ := by
  intro htop
  have hle : h.Ht i ≤ center G := by
    intro x hx
    rw [mem_center_iff]
    intro g
    have hg : g ∈ h.CH i := htop ▸ mem_top g
    exact (mem_centralizer_iff.1 hg x hx).symm
  rw [h.center_G_eq_bot, le_bot_iff] at hle
  have hc := h.card_Ht i
  rw [hle, Subgroup.card_bot] at hc
  have : 8 ≤ 2 ^ (2 * h.a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * h.a + 1) := Nat.pow_le_pow_right (by norm_num) (by have := h.one_le_a; omega)
  omega

theorem orderOf_tH (i : Idx) : orderOf (h.tH i) = 2 := by
  rw [Subgroup.orderOf_mk]
  exact h.ht

theorem tH_mem_centralizer_NH (i : Idx) : h.tH i ∈ centralizer (h.NH i : Set (h.CH i)) := by
  rw [mem_centralizer_iff]
  intro n hn
  exact Subtype.ext (h.t_commute_L (h.N_le_L i (mem_subgroupOf.1 hn))).symm

theorem NH_le_centralizer_tH (i : Idx) :
    h.NH i ≤ centralizer ({h.tH i} : Set (h.CH i)) := fun n hn =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (h.tH_mem_centralizer_NH i) n hn)

theorem normal_NH {i : Idx} (hi : i.isCenter = false) :
    ((h.NH i).subgroupOf (centralizer ({h.tH i} : Set (h.CH i)))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (h.NH_le_centralizer_tH i)).2 ?_
  intro x hx
  have hxC : (x : G) ∈ h.C := by
    rw [mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Subtype.val hx
  have hxN := h.C_inf_centralizer_Ht_le_normalizer_N hi (mem_inf.2 ⟨hxC, x.2⟩)
  rw [mem_normalizer_iff] at hxN ⊢
  intro n
  rw [mem_subgroupOf, mem_subgroupOf]
  exact hxN n

theorem lieModel_NH {i : Idx} (hi : i.isSz = true) :
    LieModel (h.NH i) .twistedB2 0 2 (2 * h.a + 1) := by
  have hic : i.isCenter = false := by cases i <;> simp_all [Idx.isSz, Idx.isCenter]
  have hil : i.isLin = false := by cases i <;> simp_all [Idx.isSz, Idx.isLin]
  obtain ⟨e⟩ := h.nonempty_N_equiv_suzuki hil
  have e' : h.NH i ≃* CFSG.Blueprint.suzukiGroup h.a h.K :=
    (subgroupOfEquivOfLe (h.levi_core_G hic).2.1).trans e
  exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, h.a, h.one_le_a, h.K, inferInstance, inferInstance,
    rfl, h.card_K, ⟨e'⟩⟩))

theorem isSimpleGroup_NH {i : Idx} (hi : i.isCenter = false) :
    IsSimpleGroup (h.NH i) ∧ ∃ x y : h.NH i, x * y ≠ y * x := by
  obtain ⟨hs, x, y, hxy⟩ := h.isSimpleGroup_N i
  have := hs
  let e : h.NH i ≃* h.N i := subgroupOfEquivOfLe (h.levi_core_G hi).2.1
  refine ⟨e.isSimpleGroup, e.symm x, e.symm y, fun h' => hxy (e.symm.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem injective_NH {i : Idx} (hi : i.isCenter = false) :
    Function.Injective ((QuotientGroup.mk' (standardComponentOddCore (h.CH i))).comp
      (h.NH i).subtype) := by
  obtain ⟨hs, hne⟩ := h.isSimpleGroup_NH hi
  set O := standardComponentOddCore (h.CH i)
  have hO := GMSK.odd_card_standardComponentOddCore (h.CH i)
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxO : ((x : h.CH i)) ∈ O := (QuotientGroup.eq_one_iff _).1 hx
  have hnorm : (O.subgroupOf (h.NH i)).Normal := inferInstance
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hnorm with h1 | h1
  · have : x ∈ O.subgroupOf (h.NH i) := mem_subgroupOf.2 hxO
    rwa [h1, mem_bot] at this
  · exfalso
    have hle : h.NH i ≤ O := fun n hn => by
      have : (⟨n, hn⟩ : h.NH i) ∈ O.subgroupOf (h.NH i) := h1 ▸ mem_top _
      exact mem_subgroupOf.1 this
    have hdvd := Subgroup.card_dvd_of_le hle
    obtain ⟨u, v, huv⟩ := hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have heven : 2 ∣ Nat.card (h.NH i) := by
      have hV := h.isSylowOf_V_N hi
      have hVN : h.V i ≤ h.N i := hV.le
      have hcard : Nat.card (h.V i) ∣ Nat.card (h.NH i) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe (h.levi_core_G hi).2.1).toEquiv]
        exact Subgroup.card_dvd_of_le hVN
      have h2 : 2 ∣ Nat.card (h.V i) := by
        rw [h.card_V]
        split <;> exact dvd_pow_self 2 (by positivity) |>.trans (pow_dvd_pow_of_dvd
          (dvd_pow_self 2 (by omega)) _)
      exact h2.trans hcard
    exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 (heven.trans hdvd))

theorem L_inf_zpowers_t : h.L ⊓ zpowers h.t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxt⟩ := mem_inf.1 hx
  rcases eq_one_or_eq_of_mem_zpowers h.t_mul_t hxt with h1 | h1
  · rw [h1]; exact one_mem _
  · exact absurd (h1 ▸ hxL) h.t_not_mem_L

theorem mem_zpowers_of_mem_Ht_sup {i : Idx} {x : G} (hx : x ∈ h.Ht i ⊔ zpowers h.t) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : x ∈ zpowers h.t := by
  have hle : zpowers h.t ≤ normalizer (h.Ht i : Set G) :=
    zpowers_le.2 (Subgroup.centralizer_le_normalizer _ (h.t_mem_CH i))
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left (h.Ht i) (zpowers h.t) hle] at hx
  obtain ⟨y, hy, c, hc, rfl⟩ := hx
  beta_reduce at hxk ⊢
  have hyt : Commute y h.t := mem_centralizer_iff.1 (h.t_mem_CH i) y hy
  have hyc : Commute y c := by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hc
    exact hyt.zpow_right m
  rw [hyc.mul_pow] at hxk
  have hy1 : y ^ 2 ^ k = 1 := by
    have h1 : y ^ 2 ^ k = (c ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hxk
    have hmem : y ^ 2 ^ k ∈ h.L ⊓ zpowers h.t :=
      mem_inf.2 ⟨pow_mem (h.pull_le_L _ hy) _, h1 ▸ inv_mem (pow_mem hc _)⟩
    rw [h.L_inf_zpowers_t, mem_bot] at hmem
    exact hmem
  have hy' : y = 1 := by
    have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy1
    have h2 : orderOf y ∣ Nat.card (h.Ht i) := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : h.Ht i)
      rwa [Subgroup.orderOf_mk] at this
    rw [h.card_Ht] at h2
    have hodd : Odd (2 ^ (2 * h.a + 1) - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
    have hcop : Nat.Coprime (2 ^ k) (2 ^ (2 * h.a + 1) - 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [hy', one_mul]
  exact hc

theorem rank_NH {i : Idx} (hi : i.isCenter = false)
    (hσ : ∀ x : h.C, (∀ n ∈ h.N i, (x : G) * n = n * x) → h.fieldFactor x = 1)
    (P : Subgroup (h.CH i)) (hP : P ≤ centralizer (h.NH i : Set (h.CH i)))
    (hP2 : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := h.CH i ⊓ centralizer (h.N i : Set G) with hY
  set P' : Subgroup G := P.map (h.CH i).subtype with hP'
  have hP'Y : P' ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨x.2, mem_centralizer_iff.2 fun n hn => ?_⟩
    have hnX : n ∈ h.CH i := (h.levi_core_G hi).2.1 hn
    have := mem_centralizer_iff.1 (hP hx) ⟨n, hnX⟩ (mem_subgroupOf.2 hn)
    exact congrArg Subtype.val this
  have htY : zpowers h.t ≤ Y := zpowers_le.2 (mem_inf.2 ⟨h.t_mem_CH i,
    mem_centralizer_iff.2 fun n hn => (h.t_commute_L (h.N_le_L i hn)).symm⟩)
  obtain ⟨S, hSY, hPS⟩ := exists_isSylowOf_ge hP'Y (hP2.map _)
  obtain ⟨S', hS'Y, htS'⟩ := exists_isSylowOf_ge htY h.isPGroup_zpowers_t
  have hS'le : S' ≤ zpowers h.t := by
    refine le_zpowers_of_inf_centralizer_le hS'Y.isPGroup h.t_mul_t (htS' (mem_zpowers _)) ?_
    rintro x ⟨hxS', hxt⟩
    have hxY := hS'Y.le hxS'
    have hmem := h.mem_Ht_sup_of_commute_N hi hσ hxt (mem_inf.1 hxY).1
      fun n hn => (mem_centralizer_iff.1 (mem_inf.1 hxY).2 n hn).symm
    obtain ⟨k, hk⟩ := hS'Y.isPGroup ⟨x, hxS'⟩
    exact h.mem_zpowers_of_mem_Ht_sup hmem (k := k) (by simpa using congrArg Subtype.val hk)
  calc Nat.card P = Nat.card P' :=
        Nat.card_congr (P.equivMapOfInjective _ (subtype_injective _)).toEquiv
    _ ≤ Nat.card S := Subgroup.card_le_of_le hPS
    _ = Nat.card S' := by rw [hSY.card_eq, hS'Y.card_eq]
    _ ≤ Nat.card (zpowers h.t) := Subgroup.card_le_of_le hS'le
    _ = 2 := h.card_zpowers_t

theorem VH_le_NH (i : Idx) : h.VH i ≤ h.NH i := fun _ hv =>
  mem_subgroupOf.2 (h.V_le_N i (mem_subgroupOf.1 hv))

theorem isPGroup_VH (i : Idx) : IsPGroup 2 (h.VH i) := (h.isPGroup_V i).comap_subtype

theorem isSylowOf_VH_NH {i : Idx} (hi : i.isCenter = false) :
    IsSylowOf 2 (h.VH i) (h.NH i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.isSylowOf_V_N hi
  rw [← h.map_VH hi, ← h.map_NH hi, CFSG.ABGLocalTools.isSylowOf_map_subtype_iff] at hs
  exact hs

theorem isSylowOf_VH_bar {i : Idx} (hi : i.isCenter = false) :
    IsSylowOf 2 ((h.VH i).map (QuotientGroup.mk' (standardComponentOddCore (h.CH i))))
      ((h.NH i).map (QuotientGroup.mk' (standardComponentOddCore (h.CH i)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (standardComponentOddCore (h.CH i))
  have hs := h.isSylowOf_VH_NH hi
  have hV : ((h.VH i).subgroupOf (h.NH i)).map (h.NH i).subtype = h.VH i := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 (h.VH_le_NH i)]
  have hN : (⊤ : Subgroup (h.NH i)).map (h.NH i).subtype = h.NH i := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hs' : IsSylowOf 2 ((h.VH i).subgroupOf (h.NH i)) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (h.NH i), hV, hN]
    exact hs
  have := isSylowOf_map_of_injective hs' (h.injective_NH hi)
  rwa [← Subgroup.map_map, ← Subgroup.map_map, hV, hN] at this

theorem card_VH_bar {i : Idx} (hi : i.isSz = true) :
    Nat.card ((h.VH i).map (QuotientGroup.mk' (standardComponentOddCore (h.CH i)))) =
      2 ^ (2 * (2 * h.a + 1)) := by
  have hic : i.isCenter = false := by cases i <;> simp_all [Idx.isSz, Idx.isCenter]
  rw [card_map_mk'_of_isPGroup _ (GMSK.odd_card_standardComponentOddCore _) (h.isPGroup_VH i),
    Nat.card_congr (subgroupOfEquivOfLe (h.V_le_centralizer_Ht hic)).toEquiv, h.card_V]
  simp only [hi, ↓reduceIte]
  rw [← pow_mul, mul_comm]

theorem suzukiSylowFacts_VH_bar {i : Idx} (hi : i.isSz = true) :
    SuzukiSylowFacts ((h.VH i).map (QuotientGroup.mk' (standardComponentOddCore (h.CH i)))) := by
  have hic : i.isCenter = false := by cases i <;> simp_all [Idx.isSz, Idx.isCenter]
  set π := QuotientGroup.mk' (standardComponentOddCore (h.CH i))
  have h1 := h.suzukiSylowFacts_V hi
  rw [← h.map_VH hic] at h1
  have h2 := h1.of_map (subtype_injective (h.CH i))
  have hV : (⊤ : Subgroup (h.VH i)).map (h.VH i).subtype = h.VH i := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  rw [← hV] at h2
  have h3 := (h2.of_map (subtype_injective (h.VH i))).map
    (injective_mk'_comp_of_isPGroup _ (GMSK.odd_card_standardComponentOddCore _) (h.isPGroup_VH i))
  rwa [← Subgroup.map_map, hV] at h3

theorem isPGroup_VH_sup_tH (i : Idx) :
    IsPGroup 2 (h.VH i ⊔ zpowers (h.tH i) : Subgroup (h.CH i)) := by
  have hz : IsPGroup 2 (zpowers (h.tH i)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_tH, pow_one])
  refine (h.isPGroup_VH i).to_sup_of_normal_left' hz (zpowers_le.2 ?_)
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun v hv => ?_)
  exact Subtype.ext (h.t_commute_L (h.pull_le_L _ (mem_subgroupOf.1 hv))).symm

theorem isSylowOf_V_sup_t_bar {i : Idx} (hi : i.isCenter = false) :
    IsSylowOf 2 ((h.VH i).map (QuotientGroup.mk' (standardComponentOddCore (h.CH i))) ⊔
        zpowers (QuotientGroup.mk' (standardComponentOddCore (h.CH i)) (h.tH i)))
      (centralizer ({QuotientGroup.mk' (standardComponentOddCore (h.CH i)) (h.tH i)} :
        Set (h.CH i ⧸ standardComponentOddCore (h.CH i)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := standardComponentOddCore (h.CH i)
  set π := QuotientGroup.mk' O
  have hO : Odd (Nat.card O) := GMSK.odd_card_standardComponentOddCore _
  set tb := π (h.tH i)
  have hVTmap : (h.VH i ⊔ zpowers (h.tH i)).map π = (h.VH i).map π ⊔ zpowers tb := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  have hVT2 := h.isPGroup_VH_sup_tH i
  have hcardVT : Nat.card ((h.VH i).map π ⊔ zpowers tb : Subgroup _) = 2 * Nat.card (h.V i) := by
    rw [← hVTmap, card_map_mk'_of_isPGroup O hO hVT2, ← h.card_V_sup_t i]
    have e : (h.VH i ⊔ zpowers (h.tH i)).map (h.CH i).subtype = h.V i ⊔ zpowers h.t := by
      rw [Subgroup.map_sup, h.map_VH hi, MonoidHom.map_zpowers]
      rfl
    rw [← e]
    exact Nat.card_congr ((h.VH i ⊔ zpowers (h.tH i)).equivMapOfInjective _
      (subtype_injective _)).toEquiv
  have hle : (h.VH i).map π ⊔ zpowers tb ≤ centralizer ({tb} : Set (h.CH i ⧸ O)) := by
    refine sup_le ?_ (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.t_commute_L (h.pull_le_L _ (mem_subgroupOf.1 hv))).symm
  refine isSylowOf_of_forall_card_le hle (hVTmap ▸ hVT2.map π) fun Qb hQb hQb2 => ?_
  have hQt : IsPGroup 2 (Qb ⊔ zpowers tb : Subgroup (h.CH i ⧸ O)) := by
    refine hQb2.to_sup_of_normal_left' ((h.isPGroup_VH_sup_tH i).map π |>.to_le ?_) ?_
    · rw [hVTmap]; exact le_sup_right
    · refine zpowers_le.2 (Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.2 fun q hq => ?_))
      exact (mem_centralizer_singleton_iff.1 (hQb hq))
  have hzle : (zpowers (h.tH i)).map π ≤ Qb ⊔ zpowers tb := by
    rw [MonoidHom.map_zpowers]; exact le_sup_right
  have hz2 : IsPGroup 2 (zpowers (h.tH i)) := hVT2.to_le le_sup_right
  obtain ⟨Q₀, htQ, hQ₀2, hQ₀map⟩ := exists_lift_of_odd O hQt hz2 hzle
  have hQ₀C : ∀ q ∈ Q₀, q * h.tH i = h.tH i * q := by
    intro q hq
    have htQ₀ : h.tH i ∈ Q₀ := htQ (mem_zpowers _)
    refine eq_of_mk'_eq_of_isPGroup O hO hQ₀2 (mul_mem hq htQ₀) (mul_mem htQ₀ hq) ?_
    have hqb : π q ∈ Qb ⊔ zpowers tb := hQ₀map ▸ mem_map_of_mem π hq
    have hqc : π q ∈ centralizer ({tb} : Set (h.CH i ⧸ O)) :=
      sup_le hQb (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) hqb
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.1 hqc
  have hQ₀G : Q₀.map (h.CH i).subtype ≤ h.C ⊓ centralizer (h.Ht i : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (congrArg Subtype.val (hQ₀C q hq)), q.2⟩
  have hcardQ₀ := h.card_le_of_isPGroup_C_inf hi hQ₀G (hQ₀2.map _)
  rw [← Nat.card_congr (Q₀.equivMapOfInjective _ (subtype_injective _)).toEquiv] at hcardQ₀
  rw [hcardVT]
  calc Nat.card Qb ≤ Nat.card (Qb ⊔ zpowers tb : Subgroup _) := Subgroup.card_le_of_le le_sup_left
    _ = Nat.card Q₀ := by rw [← hQ₀map, card_map_mk'_of_isPGroup O hO hQ₀2]
    _ ≤ 2 * Nat.card (h.V i) := hcardQ₀

theorem not_normal_NH {i : Idx} (hi : i.isSz = true)
    (hσ : ∀ x : h.C, (∀ n ∈ h.N i, (x : G) * n = n * x) → h.fieldFactor x = 1)
    (hns : ∃ S : Subgroup G, S ≤ h.CH i ∧ IsPGroup 2 S ∧ h.V i ⊔ zpowers h.t < S) :
    ¬ ((h.NH i).map (QuotientGroup.mk' (standardComponentOddCore (h.CH i)))).Normal := by
  intro hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hic : i.isCenter = false := by cases i <;> simp_all [Idx.isSz, Idx.isCenter]
  set O := standardComponentOddCore (h.CH i) with hO
  set π := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := GMSK.odd_card_standardComponentOddCore _
  set A := (h.NH i).map π with hA
  have hsyl := GMSK.exists_sylow_inf_centralizer_eq_zpowers (h.orderOf_tH i)
    (h.tH_mem_centralizer_NH i) (h.rank_NH hic hσ)
  obtain ⟨-, hT, -, -, -, hS2⟩ := GMSK.stdData_odd_quotient GMSK.stdTypeFacts_T_Sz
    GMSK.isoInvariant_T_Sz (h.lieModel_NH hi : GMSK.T_Sz (2 * h.a + 1) (h.NH i))
    (h.orderOf_tH i) (h.NH_le_centralizer_tH i) (h.normal_NH hic) hsyl O hOodd
  have hTA : LieModel A .twistedB2 0 2 (2 * h.a + 1) := hT
  have hOut := GMSK.odd_card_outer_of_lieModel_twistedB2 hTA
  have hAs := GMSK.isSimpleGroup_of_lieModel_twistedB2 hTA
  have hAne := GMSK.exists_mul_ne_of_lieModel_twistedB2 hTA
  set CA := centralizer (A : Set (h.CH i ⧸ O)) with hCA
  have hAC : A ⊓ CA = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    exact (eq_one_of_forall_commute_of_isSimpleGroup hAs hAne hxA fun y hy =>
      (mem_centralizer_iff.1 hxC y hy).symm) ▸ one_mem _
  obtain ⟨S, hSX, hS2', hlt⟩ := hns
  set SX := S.subgroupOf (h.CH i)
  have hSX2 : IsPGroup 2 SX := hS2'.comap_subtype
  set Sb := SX.map π
  have hcardSb : Nat.card Sb = Nat.card S := by
    rw [card_map_mk'_of_isPGroup O hOodd hSX2]
    exact Nat.card_congr (subgroupOfEquivOfLe hSX).toEquiv
  have hSbAC : Sb ≤ A ⊔ CA := by
    intro s hs
    obtain ⟨k, hk⟩ := (hSX2.map π) ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hsN : s ∈ normalizer (A : Set (h.CH i ⧸ O)) := by
      rw [normalizer_eq_top_iff.2 hN]
      exact mem_top s
    obtain ⟨l, hl, hlc⟩ := exists_inv_mul_mem_centralizer_of_odd_outer hOut hsN hk'
    have e : s = l * (l⁻¹ * s) := by group
    rw [e]
    exact mul_mem (mem_sup_left hl) (mem_sup_right hlc)
  have hfA : (Nat.card A).factorization 2 = 2 * (2 * h.a + 1) := by
    have := (h.isSylowOf_VH_bar hic).card_eq
    rw [h.card_VH_bar hi] at this
    exact (Nat.pow_right_injective le_rfl this).symm
  obtain ⟨S₂⟩ := (inferInstance : Nonempty (Sylow 2 CA))
  have hfC : (Nat.card CA).factorization 2 = 1 := by
    have h1 := S₂.card_eq_multiplicity
    rw [hS2 S₂] at h1
    exact (Nat.pow_right_injective le_rfl (h1.symm.trans (pow_one 2).symm))
  have hcardM : Nat.card (A ⊔ CA : Subgroup _) = Nat.card A * Nat.card CA := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A CA fun x hx y hy =>
      mem_centralizer_iff.1 hy x hx).1
    rwa [hAC, Subgroup.card_bot, mul_one] at this
  obtain ⟨SM, hSM⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (A ⊔ CA)
  have hcardSM : Nat.card SM = 2 ^ (2 * (2 * h.a + 1) + 1) := by
    rw [hSM.card_eq, hcardM, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, hfA, hfC]
  have hle : Nat.card Sb ≤ Nat.card SM := card_le_of_isSylowOf hSM hSbAC (hSX2.map π)
  have hcardVt : Nat.card (h.V i ⊔ zpowers h.t : Subgroup G) = 2 ^ (2 * (2 * h.a + 1) + 1) := by
    rw [h.card_V_sup_t, h.card_V]
    simp only [hi, ↓reduceIte]
    rw [← pow_mul, pow_succ]
    ring
  have heq : h.V i ⊔ zpowers h.t = S := Subgroup.eq_of_le_of_card_ge hlt.le (by
    rw [hcardVt, ← hcardSM, ← hcardSb]
    exact hle)
  exact hlt.ne heq


theorem oddCore_centralizer_mem {i : Idx} (hi : i.isCenter = false)
    (hσ : ∀ x : h.C, (∀ n ∈ h.N i, (x : G) * n = n * x) → h.fieldFactor x = 1) :
    ∀ o ∈ standardComponentOddCore (h.CH i),
      (∀ x ∈ h.VH i ⊔ zpowers (h.tH i), o⁻¹ * x * o = x) →
        ∃ z ∈ center (h.CH i), ∃ c ∈ zpowers (h.tH i), o = z * c := by
  intro o ho hoc
  have hot : o * h.tH i = h.tH i * o := by
    have h1 := hoc (h.tH i) (mem_sup_right (mem_zpowers _))
    calc o * h.tH i = o * (o⁻¹ * h.tH i * o) := by rw [h1]
      _ = h.tH i * o := by group
  have hoCG : (o : G) ∈ h.C ⊓ centralizer (h.Ht i : Set G) :=
    mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (congrArg Subtype.val hot), o.2⟩
  have hoNorm := h.C_inf_centralizer_Ht_le_normalizer_N hi hoCG
  have hoN : ∀ n ∈ h.N i, (o : G) * n = n * o := by
    intro n hn
    have hnX : n ∈ h.CH i := (h.levi_core_G hi).2.1 hn
    have hnNH : (⟨n, hnX⟩ : h.CH i) ∈ h.NH i := mem_subgroupOf.2 hn
    have hcO : o * ⟨n, hnX⟩ * o⁻¹ * (⟨n, hnX⟩ : h.CH i)⁻¹ ∈ standardComponentOddCore (h.CH i) := by
      have h1 : (⟨n, hnX⟩ : h.CH i) * o⁻¹ * (⟨n, hnX⟩ : h.CH i)⁻¹ ∈
          standardComponentOddCore (h.CH i) :=
        (inferInstance : (standardComponentOddCore (h.CH i)).Normal).conj_mem _ (inv_mem ho) _
      have h2 : o * ⟨n, hnX⟩ * o⁻¹ * (⟨n, hnX⟩ : h.CH i)⁻¹ =
          o * ((⟨n, hnX⟩ : h.CH i) * o⁻¹ * (⟨n, hnX⟩ : h.CH i)⁻¹) := by group
      rw [h2]
      exact mul_mem ho h1
    have hcN : o * ⟨n, hnX⟩ * o⁻¹ * (⟨n, hnX⟩ : h.CH i)⁻¹ ∈ h.NH i := by
      have h1 : ((o * ⟨n, hnX⟩ * o⁻¹ : h.CH i) : G) ∈ h.N i := (mem_normalizer_iff.1 hoNorm n).1 hn
      exact mul_mem (mem_subgroupOf.2 h1) (inv_mem hnNH)
    have hc1 : o * ⟨n, hnX⟩ * o⁻¹ * (⟨n, hnX⟩ : h.CH i)⁻¹ = 1 := by
      have h1 : ((QuotientGroup.mk' (standardComponentOddCore (h.CH i))).comp (h.NH i).subtype)
          ⟨_, hcN⟩ = ((QuotientGroup.mk' (standardComponentOddCore (h.CH i))).comp
            (h.NH i).subtype) 1 := by
        rw [map_one]
        exact (QuotientGroup.eq_one_iff _).2 hcO
      exact congrArg Subtype.val (h.injective_NH hi h1)
    have h2 : o * ⟨n, hnX⟩ = ⟨n, hnX⟩ * o := by
      calc o * ⟨n, hnX⟩ = o * ⟨n, hnX⟩ * o⁻¹ * (⟨n, hnX⟩ : h.CH i)⁻¹ * (⟨n, hnX⟩ * o) := by
            group
        _ = ⟨n, hnX⟩ * o := by rw [hc1, one_mul]
    exact congrArg Subtype.val h2
  have hoHt := h.mem_Ht_sup_of_commute_N hi hσ hoCG.1 o.2 hoN
  have hle : zpowers h.t ≤ normalizer (h.Ht i : Set G) :=
    zpowers_le.2 (Subgroup.centralizer_le_normalizer _ (h.t_mem_CH i))
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left (h.Ht i) (zpowers h.t) hle,
    Set.mem_mul] at hoHt
  obtain ⟨y, hy, c, hc, hyc⟩ := hoHt
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hc
  have hyX : y ∈ h.CH i := h.Ht_le_centralizer_Ht i hy
  refine ⟨⟨y, hyX⟩, mem_center_iff.2 fun x => Subtype.ext (mem_centralizer_iff.1 x.2 y hy).symm,
    h.tH i ^ m, zpow_mem_zpowers _ _, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_zpow]
  exact hyc.symm

theorem exists_lift_benderSylow {i : Idx} (hi : i.isCenter = false)
    (hσ : ∀ x : h.C, (∀ n ∈ h.N i, (x : G) * n = n * x) → h.fieldFactor x = 1)
    {Wb : Subgroup (h.CH i ⧸ standardComponentOddCore (h.CH i))}
    (hB : BenderSylow (CFSG.layer (h.CH i ⧸ standardComponentOddCore (h.CH i)))
      (QuotientGroup.mk' (standardComponentOddCore (h.CH i)) (h.tH i))
      ((h.VH i).map (QuotientGroup.mk' (standardComponentOddCore (h.CH i)))) Wb) :
    ∃ W : Subgroup G, W ≤ h.CH i ∧ BenderSylow W h.t (h.V i) W ∧
      (∀ S : Subgroup G, S ≤ h.CH i → IsPGroup 2 S → h.V i ⊔ zpowers h.t ≤ S →
        S ≤ W ⊔ zpowers h.t) ∧
      ∀ x ∈ h.CH i, x * h.t = h.t * x → x ∈ normalizer (h.V i : Set G) →
        ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
  have : (CFSG.layer (h.CH i ⧸ standardComponentOddCore (h.CH i))).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  have hO := GMSK.odd_card_standardComponentOddCore (h.CH i)
  obtain ⟨W, hBW, huniq, hnorm⟩ := exists_lift_benderSylow_of_odd _ hO (h.isPGroup_VH_sup_tH i)
    hB (h.isSylowOf_V_sup_t_bar hi) (h.oddCore_centralizer_mem hi hσ)
  have hmap : (W ⊔ zpowers (h.tH i)).map (h.CH i).subtype =
      W.map (h.CH i).subtype ⊔ zpowers h.t := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  refine ⟨W.map (h.CH i).subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · have := hBW.map (subtype_injective (h.CH i))
    rwa [h.map_VH hi] at this
  · intro S hSX hS2 hVS
    have hVS' : h.VH i ⊔ zpowers (h.tH i) ≤ S.subgroupOf (h.CH i) := by
      refine sup_le (fun v hv => mem_subgroupOf.2 (hVS (mem_sup_left (mem_subgroupOf.1 hv))))
        (zpowers_le.2 (mem_subgroupOf.2 (hVS (mem_sup_right (mem_zpowers h.t)))))
    have h1 := huniq (S.subgroupOf (h.CH i)) hS2.comap_subtype hVS'
    intro x hx
    rw [← hmap]
    exact ⟨⟨x, hSX hx⟩, h1 (mem_subgroupOf.2 hx), rfl⟩
  · rintro x hxX hxt hxV _ ⟨w, hw, rfl⟩
    have hxV' : (⟨x, hxX⟩ : h.CH i) ∈ normalizer (h.VH i : Set (h.CH i)) :=
      mem_normalizer_iff.2 fun v => mem_normalizer_iff.1 hxV v
    exact ⟨_, hnorm ⟨x, hxX⟩ (Subtype.ext hxt) hxV' w hw, rfl⟩

theorem sec3_2_sz (hGMS : GMSK.GMSSuzukiSharpKRankOneStatement)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {i : Idx} (hi : i.isSz = true)
    (hσ : ∀ x : h.C, (∀ n ∈ h.N i, (x : G) * n = n * x) → h.fieldFactor x = 1)
    (hns : ∃ S : Subgroup G, S ≤ h.CH i ∧ IsPGroup 2 S ∧ h.V i ⊔ zpowers h.t < S) :
    ∃ W : Subgroup G, W ≤ h.CH i ∧ BenderSylow W h.t (h.V i) W ∧
      (∀ S : Subgroup G, S ≤ h.CH i → IsPGroup 2 S → h.V i ⊔ zpowers h.t ≤ S →
        S ≤ W ⊔ zpowers h.t) ∧
      ∀ x ∈ h.CH i, x * h.t = h.t * x → x ∈ normalizer (h.V i : Set G) →
        ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
  have hic : i.isCenter = false := by cases i <;> simp_all [Idx.isSz, Idx.isCenter]
  have hS := GMSK.sharpOutcomeSz_oddCore_quotient hGMS
    (CFSG.QuasithinUnique.isKGroupCat_of_kProper hK (h.CH_ne_top i)) (h.lieModel_NH hi)
    (h.orderOf_tH i) (h.tH_mem_centralizer_NH i) (h.normal_NH hic) (h.rank_NH hic hσ)
    (h.not_normal_NH hi hσ hns)
  have htt : QuotientGroup.mk' (standardComponentOddCore (h.CH i)) (h.tH i) *
      QuotientGroup.mk' (standardComponentOddCore (h.CH i)) (h.tH i) = 1 := by
    rw [← map_mul, show h.tH i * h.tH i = 1 from Subtype.ext h.t_mul_t, map_one]
  have hAt : (h.NH i).map (QuotientGroup.mk' (standardComponentOddCore (h.CH i))) ≤
      centralizer ({QuotientGroup.mk' (standardComponentOddCore (h.CH i)) (h.tH i)} :
        Set (h.CH i ⧸ standardComponentOddCore (h.CH i))) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 (h.NH_le_centralizer_tH i hn)]
  have hF := h.suzukiSylowFacts_VH_bar hi
  obtain ⟨Wb, hB⟩ := benderSylow_of_sharpOutcome_suzuki hS htt ⟨h.a, rfl⟩
    (by have := h.one_le_a; omega) hAt (h.isSylowOf_VH_bar hic) (h.card_VH_bar hi)
    hF.center_mul_self hF.mul_self_mem hF.commutator_le hF.mem_center
  exact h.exists_lift_benderSylow hic hσ hB

theorem Ht5_le_normalizer_E : h.Ht .i5 ≤ normalizer (h.E : Set G) := by
  intro x hx
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
  have hE : h.E ≤ centralizer ({x} : Set G) := by
    refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 ?_)) fun v hv => ?_
    · exact (mem_centralizer_iff.1 (h.t_mem_CH .i5) x hx).symm
    · have hv5 : v ∈ h.CH .i5 := h.V_le_centralizer_Ht rfl (h.V_center_le .i5 hv)
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hv5 x hx).symm
  exact mem_centralizer_singleton_iff.1 (hE hy)

theorem exists_gt_V5_sup_t :
    ∃ S : Subgroup G, S ≤ h.CH .i5 ∧ IsPGroup 2 S ∧ h.V .i5 ⊔ zpowers h.t < S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, hY2, hRTY, hYX, hYN, hYC, -, hYt⟩ := h.sec3_3
  have hVR : h.V .i5 ≤ h.R := h.pull_mono (rootV_le_rootJoin (by decide))
  have hVt : h.V .i5 ⊔ zpowers h.t ≤ h.RT := sup_le_sup_right hVR _
  have hHY : h.Ht .i5 ≤ normalizer (Y : Set G) := fun b hb =>
    mem_normalizer_of_conj_mem (hYN b (h.Ht5_le_normalizer_E hb)) fun y hy => by
      have := hYN b⁻¹ (inv_mem (h.Ht5_le_normalizer_E hb)) y hy
      rwa [inv_inv] at this
  have hbt : ∀ b ∈ h.Ht .i5, b ∈ normalizer ((zpowers h.t : Subgroup G) : Set G) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute h.t b from
      (mem_centralizer_iff.1 (h.t_mem_CH .i5) b hb).symm) k).eq
  have hHRT : h.Ht .i5 ≤ normalizer (h.RT : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      (mem_inf.2 ⟨h.H_le_normalizer_R (h.Ht_le_H .i5 hb), hbt b hb⟩)
  have hYRT : Y ≤ normalizer (h.RT : Set G) := fun y hy =>
    ((mem_sectionCentralizer_iff).1 (mem_inf.1 (hYX hy)).2).2.1
  obtain ⟨he12, -, he2, -⟩ := h.e_f_mem_orderOf
  obtain ⟨y₀, hy₀Y, hy₀⟩ := hYt h.e he12
  have he1 : h.e ≠ 1 := fun h1 => by rw [h1, orderOf_one] at he2; exact absurd he2 (by norm_num)
  letI : MulDistribMulAction (h.Ht .i5) Y :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (h.Ht .i5) Y hHY
  set N : Subgroup Y := h.RT.subgroupOf Y with hNdef
  have : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYRT
  have hNinv : CFSG.IsInvariant (h.Ht .i5) Y N :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun b z hz => by
      rw [mem_subgroupOf] at hz ⊢
      exact (mem_normalizer_iff.1 (hHRT b.2) z).1 hz
  have hN2 : IsPGroup 2 N := (hY2.to_le hRTY).of_equiv (subgroupOfEquivOfLe hRTY).symm
  have hNsolv : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (h.Ht .i5)) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN2
    rw [hk, h.card_Ht]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
      (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one))
  have hcoset : ∀ b : h.Ht .i5, (⟨y₀, hy₀Y⟩ : Y)⁻¹ * (b • (⟨y₀, hy₀Y⟩ : Y)) ∈ N := by
    intro b
    have hsmul : ((b • (⟨y₀, hy₀Y⟩ : Y) : Y) : G) = (b : G) * y₀ * (b : G)⁻¹ := rfl
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hsmul]
    have hbt' : (b : G) * h.t = h.t * b := (mem_centralizer_iff.1 (h.t_mem_CH .i5) b b.2)
    have hbe : (b : G) * h.e = h.e * b := by
      have he5 : h.e ∈ h.CH .i5 := h.V_le_centralizer_Ht rfl (h.V_center_le .i5 he12)
      exact mem_centralizer_iff.1 he5 b b.2
    have hmemY : y₀⁻¹ * ((b : G) * y₀ * (b : G)⁻¹) ∈ Y :=
      mul_mem (inv_mem hy₀Y) ((mem_normalizer_iff.1 (hHY b.2) y₀).1 hy₀Y)
    rw [← hYC]
    refine mem_inf.2 ⟨hmemY, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : (b : G) * y₀ * (b : G)⁻¹ * h.t * ((b : G) * y₀ * (b : G)⁻¹)⁻¹ = h.t * h.e := by
      have hbt'' : (b : G)⁻¹ * h.t * b = h.t := by
        calc (b : G)⁻¹ * h.t * b = (b : G)⁻¹ * (h.t * b) := by group
          _ = (b : G)⁻¹ * (b * h.t) := by rw [hbt']
          _ = h.t := by group
      calc (b : G) * y₀ * (b : G)⁻¹ * h.t * ((b : G) * y₀ * (b : G)⁻¹)⁻¹ =
          (b : G) * (y₀ * ((b : G)⁻¹ * h.t * b) * y₀⁻¹) * (b : G)⁻¹ := by group
        _ = (b : G) * (h.t * h.e) * (b : G)⁻¹ := by rw [hbt'', hy₀]
        _ = h.t * h.e := by
          rw [show (b : G) * (h.t * h.e) * (b : G)⁻¹ = (b * h.t) * h.e * (b : G)⁻¹ by group, hbt',
            mul_assoc h.t, hbe]
          group
    calc y₀⁻¹ * ((b : G) * y₀ * (b : G)⁻¹) * h.t =
        y₀⁻¹ * ((b : G) * y₀ * (b : G)⁻¹ * h.t * ((b : G) * y₀ * (b : G)⁻¹)⁻¹) *
          ((b : G) * y₀ * (b : G)⁻¹) := by group
      _ = y₀⁻¹ * (h.t * h.e) * ((b : G) * y₀ * (b : G)⁻¹) := by rw [h1]
      _ = h.t * (y₀⁻¹ * ((b : G) * y₀ * (b : G)⁻¹)) := by
        rw [← hy₀]
        group
  obtain ⟨c, hc, hcN⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed N hNinv hNsolv hcop
    ⟨y₀, hy₀Y⟩ hcoset
  have hcH : (c : G) ∈ h.CH .i5 := by
    refine mem_centralizer_iff.2 fun b hb => ?_
    have := congrArg Subtype.val (hc ⟨b, hb⟩)
    have hsmul : (((⟨b, hb⟩ : h.Ht .i5) • c : Y) : G) = b * (c : G) * b⁻¹ := rfl
    rw [hsmul] at this
    calc b * (c : G) = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [this]
  have hcRT : (c : G) ∉ h.RT := by
    intro hcRT
    have hy₀RT : y₀ ∈ h.RT := by
      have h1 : ((c⁻¹ * ⟨y₀, hy₀Y⟩ : Y) : G) ∈ h.RT := mem_subgroupOf.1 hcN
      have e : y₀ = (c : G) * ((c⁻¹ * ⟨y₀, hy₀Y⟩ : Y) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [e]
      exact mul_mem hcRT h1
    have hy₀C : y₀ ∈ h.C := by
      rw [← hYC] at hy₀RT
      exact (mem_inf.1 hy₀RT).2
    have : h.t * h.e = h.t := by
      rw [← hy₀, mem_centralizer_singleton_iff.1 hy₀C, mul_inv_cancel_right]
    exact he1 (by simpa using this)
  refine ⟨Y ⊓ h.CH .i5, inf_le_right, hY2.to_le inf_le_left, lt_of_le_of_ne
    (le_inf (hVt.trans hRTY) (sup_le (h.V_le_centralizer_Ht rfl)
      (zpowers_le.2 (h.t_mem_CH .i5)))) fun heq => hcRT (hVt ?_)⟩
  rw [heq]
  exact mem_inf.2 ⟨c.2, hcH⟩

theorem sec3_2_five (hGMS : GMSK.GMSSuzukiSharpKRankOneStatement)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) :
    ∃ W : Subgroup G, W ≤ h.CH .i5 ∧ BenderSylow W h.t (h.V .i5) W ∧
      (∀ S : Subgroup G, S ≤ h.CH .i5 → IsPGroup 2 S → h.V .i5 ⊔ zpowers h.t ≤ S →
        S ≤ W ⊔ zpowers h.t) ∧
      ∀ x ∈ h.CH .i5, x * h.t = h.t * x → x ∈ normalizer (h.V .i5 : Set G) →
        ∀ w ∈ W, x * w * x⁻¹ ∈ W :=
  h.sec3_2_sz hGMS hK rfl h.fieldFactor_eq_one_of_commute_N5 h.exists_gt_V5_sup_t

end Setup

end CFSG.LocalAnalysis.EvenBN.TwoF4
