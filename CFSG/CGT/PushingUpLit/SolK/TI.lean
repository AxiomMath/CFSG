module

public import CFSG.CGT.PushingUpLit.SolK.JFour
public import CFSG.CGT.PushingUpLit.SolK.Weight
public import CFSG.CGT.PushingUpLit.SolK.Tight
public import CFSG.CGT.PushingUpLit.SolK.Centralizers

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

@[expose] def QElem (_S : SolCfg G M X n) : Prop := ∀ q ∈ pCoreOf 2 M, q ^ 2 = 1

@[expose] def CentInM (_S : SolCfg G M X n) : Prop :=
  ∀ x ∈ pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M

structure TIData (_S : SolCfg G M X n) : Prop where
  elem : CFSG.Open.IsElemAbelian 2 (pCoreOf 2 M)
  ti : IsTI (pCoreOf 2 M)
  wc : WeaklyClosedIn (pCoreOf 2 M) (Subgroup.normalizer (pCoreOf 2 M : Set G))
  cent : Subgroup.centralizer ((pCoreOf 2 M : Subgroup G) : Set G) = pCoreOf 2 M

variable (S : SolCfg G M X n)

namespace SolCfg

include S

theorem elemAbelian_of_QElem (hT : TightData S) (hQe : QElem S) :
    CFSG.Open.IsElemAbelian 2 (pCoreOf 2 M) :=
  ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hT.abelian a a.2 b b.2), fun x hx => hQe x hx⟩

theorem elemAbelian_conj (hT : TightData S) (hQe : QElem S) (g : G) :
    CFSG.Open.IsElemAbelian 2 (conjSubgroup g (pCoreOf 2 M)) := by
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
  · have h1 := hT.abelian _ (mem_conjSubgroup.1 a.2) _ (mem_conjSubgroup.1 b.2)
    calc (a : G) * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group
  · have h1 := hQe _ (mem_conjSubgroup.1 hx)
    rw [pow_two] at h1 ⊢
    calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem centralizer_Q_eq (hT : TightData S) :
    Subgroup.centralizer ((pCoreOf 2 M : Subgroup G) : Set G) = pCoreOf 2 M := by
  classical
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set K : Subgroup G := Subgroup.centralizer (Q : Set G) with hK
  have hQ2 : IsPGroup 2 Q := isPGroup_pCoreOf' M
  have hQne : Q ≠ ⊥ := fun hbot => S.W_ne_bot (le_bot_iff.1 (hbot ▸ S.W_le_Q))
  have hKM : K ≤ M := by
    intro k hk
    rw [← S.normalizer_Q_eq]
    exact Subgroup.centralizer_le_normalizer (Q : Set G) hk
  have hQK : Q ≤ K := fun q hq => Subgroup.mem_centralizer_iff.2 fun b hb => hT.abelian b hb q hq
  have hQnorm : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := fun k hk q hq =>
    pCoreOf_normalized M (hKM hk) hq
  have hQP : Q ≤ pCoreOf 2 K := le_pCoreOf_of_normalized hQK hQnorm hQ2
  have hPQ : pCoreOf 2 K ≤ Q := by
    intro p hp
    have hpK : p ∈ K := pCoreOf_le_self K hp
    have hpM : p ∈ M := hKM hpK
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf' K ⟨p, hp⟩
    have hθ : S.θ ⟨p, hpM⟩ = 1 := by
      refine (theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨p, hpM⟩).2 fun w hw => ?_
      have h1 := Subgroup.mem_centralizer_iff.1 hpK w (S.W_le_Q hw)
      show p * w * p⁻¹ = w
      rw [← h1]
      group
    exact hT.ker_two ⟨p, hpM⟩ hθ ⟨j, by simpa using congrArg Subtype.val hj⟩
  have hPeq : pCoreOf 2 K = Q := le_antisymm hPQ hQP
  have hcons := centralizer_two_constrained S.hyp.charTwo hQne hQ2
  refine le_antisymm (fun k hk => ?_) hQK
  have hk' : k ∈ K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hk, ?_⟩
    rw [hPeq]
    exact hk
  rw [← hPeq]
  exact hcons hk'

theorem conj_le_TOf (hT : TightData S) (hH : CentInM S) {a g : G} (ha : a ∈ pCoreOf 2 M)
    (ha1 : a ≠ 1) (hag : g⁻¹ * a * g ∈ pCoreOf 2 M) :
    conjSubgroup g (pCoreOf 2 M) ≤ TOf M a := by
  classical
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set q : G := g⁻¹ * a * g with hq
  have hq1 : q ≠ 1 := by
    intro h
    apply ha1
    have : a = g * q * g⁻¹ := by rw [hq]; group
    rw [this, h]
    group
  have hMa : ∀ k : G, k * a * k⁻¹ = a → k ∈ M := fun k hk =>
    hH a ha ha1 (Subgroup.mem_centralizer_singleton_iff.2 (by
      calc k * a = (k * a * k⁻¹) * k := by group
        _ = a * k := by rw [hk]))
  have hMq : ∀ k : G, k * q * k⁻¹ = q → k ∈ M := fun k hk =>
    hH q hag hq1 (Subgroup.mem_centralizer_singleton_iff.2 (by
      calc k * q = (k * q * k⁻¹) * k := by group
        _ = q * k := by rw [hk]))
  have hU2 : IsPGroup 2 (conjSubgroup g Q) := (isPGroup_pCoreOf' M).map _
  have hUC : conjSubgroup g Q ≤
      M ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro u hu
    have hu' : g⁻¹ * u * g ∈ Q := mem_conjSubgroup.1 hu
    have hcomm : u * a * u⁻¹ = a := by
      have h1 := hT.abelian _ hu' _ hag
      have h2 : u * a = a * u :=
        calc u * a = g * ((g⁻¹ * u * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * a * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
          _ = a * u := by group
      calc u * a * u⁻¹ = (a * u) * u⁻¹ := by rw [h2]
        _ = a := by group
    exact Subgroup.mem_inf.2 ⟨hMa u hcomm, mem_centralizer_zpowers_iff.2 hcomm⟩
  have hnorm : ∀ k ∈ M ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G),
      ∀ u ∈ conjSubgroup g Q, k * u * k⁻¹ ∈ conjSubgroup g Q := by
    intro k hk u hu
    have hka : k * a * k⁻¹ = a := mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hk).2
    have hkq : (g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹ = q := by
      calc (g⁻¹ * k * g) * q * (g⁻¹ * k * g)⁻¹ = g⁻¹ * (k * a * k⁻¹) * g := by rw [hq]; group
        _ = q := by rw [hka]
    have hk'M : g⁻¹ * k * g ∈ M := hMq _ hkq
    have hu' : g⁻¹ * u * g ∈ Q := mem_conjSubgroup.1 hu
    refine mem_conjSubgroup.2 ?_
    have e : g⁻¹ * (k * u * k⁻¹) * g = (g⁻¹ * k * g) * (g⁻¹ * u * g) * (g⁻¹ * k * g)⁻¹ := by
      group
    rw [e]
    exact pCoreOf_normalized M hk'M hu'
  exact le_pCoreOf_of_normalized hUC hnorm hU2

theorem thetaN_card_le_two {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) : Nat.card ↥(S.thetaN (w * r)) ≤ 2 := by
  have hn : 2 ≤ n := S.hyp.two_le
  refine card_le_two_of_two (odd_two_mul_add_one n) (by omega) hcard (S.isPGroup_thetaN (w * r))
    (S.thetaN_le_setStab hw hr) ?_
  intro τ hτ
  exact S.thetaN_normalized hw hr (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2)
    (by
      intro y
      have := altOn_le_setStab (vsupp (S.D.β ⟨w, hw⟩))ᶜ hτ y
      rw [Finset.mem_compl, Finset.mem_compl] at this
      exact not_iff_not.1 this)

theorem card_le_two_mul_of_len_two (hT : TightData S) {a : G} (ha : S.HasLen a 2)
    {U : Subgroup G} (hUT : U ≤ TOf M a) (hU2 : IsPGroup 2 U) :
    Nat.card ↥U ≤ 2 * Nat.card ↥(U ⊓ pCoreOf 2 M) := by
  obtain ⟨w, hw, r, hr, rfl, hcard⟩ := ha
  have hUM : U ≤ M := hUT.trans (TOf_le_M M _)
  have h1 := S.card_eq_card_inf_mul hT hUM hU2
  have hsub : (U.subgroupOf M).map S.θ ≤ S.thetaN (w * r) := by
    intro σ hσ
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    exact S.mem_thetaN.2 ⟨m, hUT hm, rfl⟩
  have h2 : Nat.card ↥((U.subgroupOf M).map S.θ) ≤ 2 :=
    (Subgroup.card_le_of_le hsub).trans (S.thetaN_card_le_two hw hr hcard)
  calc Nat.card ↥U = Nat.card ↥(U ⊓ pCoreOf 2 M) * Nat.card ↥((U.subgroupOf M).map S.θ) := h1
    _ ≤ Nat.card ↥(U ⊓ pCoreOf 2 M) * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card ↥(U ⊓ pCoreOf 2 M) := mul_comm _ _

theorem conj_eq_of_not_len_two (hT : TightData S) (hQe : QElem S) (hH : CentInM S) {g h : G}
    (hh : h ∈ pCoreOf 2 M) (hh1 : h ≠ 1) (hhg : g⁻¹ * h * g ∈ pCoreOf 2 M)
    (hlen : ¬ S.HasLen h 2) : conjSubgroup g (pCoreOf 2 M) = pCoreOf 2 M := by
  have hle : conjSubgroup g (pCoreOf 2 M) ≤ TOf M h := S.conj_le_TOf hT hH hh hh1 hhg
  have hcardg : Nat.card ↥(conjSubgroup g (pCoreOf 2 M)) = Nat.card ↥(pCoreOf 2 M) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨l, hl⟩ := S.exists_hasLen hh
  by_cases hl4 : l = 4
  · subst hl4
    obtain ⟨w, hw, r, hr, hhwr, hcard⟩ := hl
    subst hhwr
    obtain ⟨-, hEq⟩ := S.elem_le_of_len_four hT hw hr hcard hle (S.elemAbelian_conj hT hQe g)
    exact hEq hcardg
  · have hl2 : l ≠ 2 := fun h2 => hlen (h2 ▸ hl)
    have hTQ := S.pCoreOf_centralizer_le_of_len hT hl hl2 hl4
    exact Subgroup.eq_of_le_of_card_ge (hle.trans hTQ) hcardg.ge

theorem conj_eq_of_inf_ne_bot (hT : TightData S) (hQe : QElem S) (hH : CentInM S) {g : G}
    (hne : pCoreOf 2 M ⊓ conjSubgroup g (pCoreOf 2 M) ≠ ⊥) :
    conjSubgroup g (pCoreOf 2 M) = pCoreOf 2 M := by
  classical
  by_contra hQg
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set Qg : Subgroup G := conjSubgroup g Q with hQg'
  have hall : ∀ h ∈ Q ⊓ Qg, h ≠ 1 → S.HasLen h 2 := by
    intro h hh hh1
    by_contra hlen
    exact hQg (S.conj_eq_of_not_len_two hT hQe hH (Subgroup.mem_inf.1 hh).1 hh1
      (mem_conjSubgroup.1 (Subgroup.mem_inf.1 hh).2) hlen)
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haQ : a ∈ Q := (Subgroup.mem_inf.1 ha).1
  have haQg : g⁻¹ * a * g ∈ Q := mem_conjSubgroup.1 (Subgroup.mem_inf.1 ha).2
  have hlen2 := hall a ha ha1'
  have hle : Qg ≤ TOf M a := S.conj_le_TOf hT hH haQ ha1' haQg
  have hQg2 : IsPGroup 2 Qg := (isPGroup_pCoreOf' M).map _
  have hcard1 := S.card_le_two_mul_of_len_two hT hlen2 hle hQg2
  have hcardg : Nat.card ↥Qg = Nat.card ↥Q :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hH2 : Nat.card ↥Q ≤ 2 * Nat.card ↥(Q ⊓ Qg) :=
    calc Nat.card ↥Q = Nat.card ↥Qg := hcardg.symm
      _ ≤ 2 * Nat.card ↥(Qg ⊓ Q) := hcard1
      _ = 2 * Nat.card ↥(Q ⊓ Qg) := by rw [inf_comm]
  let H0 : Subgroup ↥Q := (Q ⊓ Qg).subgroupOf Q
  let f : ↥H0 →* ↥S.D.W := (projW S).comp H0.subtype
  have hkf := Subgroup.card_ker_mul_card_range f
  have hH0 : Nat.card ↥H0 = Nat.card ↥(Q ⊓ Qg) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hker : Nat.card f.ker ≤ Nat.card ↥(rOf M X) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨(((k : ↥H0) : ↥Q) : G),
      (mem_ker_projW S).1 k.2⟩) ?_
    intro k k' hk
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))
  have hrange : Nat.card f.range ≤ 4 := by
    let V : Subgroup ↥(coreMod (2 * n + 1)) := f.range.map S.D.β.toMonoidHom
    have hV : Nat.card ↥V = Nat.card f.range :=
      Subgroup.card_map_of_injective S.D.β.injective
    have hV4 : Nat.card ↥V ≤ 4 := by
      refine card_le_four_of_weight_two V (fun v hv hv1 => ?_)
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hv
      obtain ⟨k, rfl⟩ := hu
      have hkmem : (((k : ↥H0) : ↥Q) : G) ∈ Q ⊓ Qg := Subgroup.mem_subgroupOf.1 k.2
      have hq1 : (((k : ↥H0) : ↥Q) : G) ≠ 1 := by
        intro h1
        apply hv1
        have : ((k : ↥H0) : ↥Q) = 1 := Subtype.ext h1
        simp [f, this]
      obtain ⟨w', hw', r', hr', hq, hcard'⟩ := hall _ hkmem hq1
      have hproj : ((projW S ((k : ↥H0) : ↥Q) : ↥S.D.W) : G) = w' := projW_apply S hw' hr' hq
      have hu : f k = ⟨w', hw'⟩ := Subtype.ext hproj
      show (vsupp (S.D.β.toMonoidHom (f k))).card = 2
      rw [hu]
      exact hcard'
    rw [← hV]
    exact hV4
  have hcardQ := S.card_Q
  have hW16 := S.card_W_ge
  have hRpos : 0 < Nat.card ↥(rOf M X) := Nat.card_pos
  rw [hH0] at hkf
  have hH_le : Nat.card ↥(Q ⊓ Qg) ≤ 4 * Nat.card ↥(rOf M X) := by
    rw [← hkf]
    calc Nat.card f.ker * Nat.card f.range ≤ Nat.card ↥(rOf M X) * 4 :=
          Nat.mul_le_mul hker hrange
      _ = 4 * Nat.card ↥(rOf M X) := mul_comm _ _
  nlinarith

theorem isTI_of_H (hT : TightData S) (hQe : QElem S) (hH : CentInM S) : IsTI (pCoreOf 2 M) := by
  intro g
  by_cases hbot : pCoreOf 2 M ⊓ conjSubgroup g (pCoreOf 2 M) = ⊥
  · exact Or.inl hbot
  · right
    rw [S.conj_eq_of_inf_ne_bot hT hQe hH hbot, inf_idem]

theorem weaklyClosed_of_H (hT : TightData S) (hQe : QElem S) (hH : CentInM S) :
    WeaklyClosedIn (pCoreOf 2 M) (Subgroup.normalizer (pCoreOf 2 M : Set G)) := by
  classical
  refine ⟨Subgroup.le_normalizer, fun g hg => ?_⟩
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set U : Subgroup G := conjSubgroup g Q with hU
  have hQ2 : IsPGroup 2 Q := isPGroup_pCoreOf' M
  have hU2 : IsPGroup 2 U := hQ2.map _
  have hUN : U ≤ Subgroup.normalizer (Q : Set G) := hg
  have hN2 : IsPGroup 2 (Q ⊔ U : Subgroup G) := hQ2.to_sup_of_normal_left' hU2 hUN
  have : Group.IsNilpotent ↥(Q ⊔ U : Subgroup G) := hN2.isNilpotent
  have hQN : Q ≤ Q ⊔ U := le_sup_left
  have : (Q.subgroupOf (Q ⊔ U)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).2 (sup_le Subgroup.le_normalizer hUN)
  have hQne : Q ≠ ⊥ := fun hbot => S.W_ne_bot (le_bot_iff.1 (hbot ▸ S.W_le_Q))
  have hne : Q.subgroupOf (Q ⊔ U) ≠ ⊥ := by
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨(q : G), hQN q.2⟩, Subgroup.mem_subgroupOf.2 q.2⟩, ?_⟩
    intro h
    apply hq1
    have := congrArg (fun z : ↥(Q.subgroupOf (Q ⊔ U)) => ((z : ↥(Q ⊔ U)) : G)) h
    exact Subtype.ext this
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
  have hzQ : ((z : ↥(Q ⊔ U)) : G) ∈ Q := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hz).1
  have hzc : ∀ m ∈ Q ⊔ U, m * ((z : ↥(Q ⊔ U)) : G) = ((z : ↥(Q ⊔ U)) : G) * m := fun m hm =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 hz).2 ⟨m, hm⟩)
  have hz1' : ((z : ↥(Q ⊔ U)) : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  set y : G := ((z : ↥(Q ⊔ U)) : G) with hy
  have hcent : Subgroup.centralizer (Q : Set G) = Q := S.centralizer_Q_eq hT
  have hyU : y ∈ U := by
    refine mem_conjSubgroup.2 ?_
    rw [← hcent]
    refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
    have hgq : g * q * g⁻¹ ∈ U := by
      refine mem_conjSubgroup.2 ?_
      have : g⁻¹ * (g * q * g⁻¹) * g = q := by group
      rw [this]
      exact hq
    have h1 := hzc _ ((le_sup_right : U ≤ Q ⊔ U) hgq)
    calc q * (g⁻¹ * y * g) = g⁻¹ * ((g * q * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * q * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * y * g * q := by group
  have hbot : Q ⊓ U ≠ ⊥ := by
    intro h
    have : y ∈ Q ⊓ U := Subgroup.mem_inf.2 ⟨hzQ, hyU⟩
    rw [h] at this
    exact hz1' (Subgroup.mem_bot.1 this)
  exact S.conj_eq_of_inf_ne_bot hT hQe hH hbot

theorem tiData_of_H (hT : TightData S) (hQe : QElem S) (hH : CentInM S) : TIData S :=
  ⟨S.elemAbelian_of_QElem hT hQe, S.isTI_of_H hT hQe hH, S.weaklyClosed_of_H hT hQe hH,
    S.centralizer_Q_eq hT⟩

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
