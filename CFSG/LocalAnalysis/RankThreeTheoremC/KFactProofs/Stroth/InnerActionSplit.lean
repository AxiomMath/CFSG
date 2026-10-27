module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionReduction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.FocalSubgroup
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Burnside

variable {W : Type*} [Group W] [Finite W] {p : ℕ} [Fact p.Prime]

private theorem exists_disjoint_commutator_of_abelian_sylow (S : Sylow p W)
    (hS : IsMulCommutative (S : Subgroup W)) :
    ∃ D : Subgroup W, D ≤ (S : Subgroup W) ∧ Disjoint D (commutator W) ∧
      (S : Subgroup W) ≤ D ⊔ commutator W := by
  classical
  have hp : p.Prime := Fact.out
  set N := Subgroup.normalizer ((S : Subgroup W) : Set W) with hNdef
  have hSN : (S : Subgroup W) ≤ N := Subgroup.le_normalizer
  set S' : Subgroup N := (S : Subgroup W).subgroupOf N with hS'def
  have hS'n : S'.Normal := Subgroup.normal_in_normalizer
  have hS'card : Nat.card S' = Nat.card (S : Subgroup W) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hS'idx : ¬ p ∣ S'.index := fun h =>
    S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hSN))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hcop : (Nat.card S').Coprime S'.index := by
    rw [hS'card, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hS'idx)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set H : Subgroup W := K.map N.subtype with hHdef
  have hHN : H ≤ N := Subgroup.map_subtype_le K
  have hHcard : Nat.card H = S'.index := by
    rw [hHdef, Subgroup.card_map_of_injective N.subtype_injective]
    exact hK.symm.index_eq_card.symm
  have hdecomp : ∀ n ∈ N, ∃ s ∈ (S : Subgroup W), ∃ h ∈ H, s * h = n := by
    intro n hn
    obtain ⟨⟨s, h⟩, hsh⟩ := (hK.existsUnique ⟨n, hn⟩).exists
    exact ⟨s, Subgroup.mem_subgroupOf.mp s.2, h, ⟨h, h.2, rfl⟩, congrArg Subtype.val hsh⟩
  have hfus : ∀ x ∈ (S : Subgroup W), ∀ g : W, g⁻¹ * x * g ∈ (S : Subgroup W) →
      ∃ h ∈ H, g⁻¹ * x * g = h⁻¹ * x * h := by
    intro x hx g hg
    have := hS
    obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem S x g hx hg
    obtain ⟨s, hs, h, hh, rfl⟩ := hdecomp n hn
    refine ⟨h, hh, ?_⟩
    have hxs : x * s = s * x := congrArg Subtype.val (hS.is_comm.comm ⟨x, hx⟩ ⟨s, hs⟩)
    rw [hgn]
    calc (s * h)⁻¹ * x * (s * h) = h⁻¹ * (s⁻¹ * (x * s)) * h := by group
      _ = h⁻¹ * x * h := by rw [hxs, inv_mul_cancel_left]
  have hfocal : (S : Subgroup W) ⊓ commutator W ≤ ⁅(S : Subgroup W), H⁆ := by
    have h := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup p S
    rw [CFSG.derivedSubgroup, derivedSeries_one] at h
    rw [h, Subgroup.closure_le]
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    have hy' : c⁻¹⁻¹ * x * c⁻¹ = y := by rw [inv_inv]; exact hc
    obtain ⟨h, hh, hxh⟩ := hfus x hx c⁻¹ (by rw [hy']; exact hy)
    rw [← hy', hxh]
    have he : x⁻¹ * (h⁻¹ * x * h) = ⁅x⁻¹, h⁻¹⁆ := by
      rw [commutatorElement_def, inv_inv, inv_inv]
      group
    rw [he]
    exact Subgroup.commutator_mem_commutator ((S : Subgroup W).inv_mem hx) (H.inv_mem hh)
  have hSH : ⁅(S : Subgroup W), H⁆ ≤ commutator W := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hSab' : ∀ x y : (S : Subgroup W), x * y = y * x := fun x y => hS.is_comm.comm x y
  have hcopHS : Nat.Coprime (Nat.card H) (Nat.card (S : Subgroup W)) := by
    rw [hHcard, hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hS'idx).symm
  obtain ⟨hdsup, hddisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp (S : Subgroup W) H hHN hSab' hcopHS
  refine ⟨(S : Subgroup W) ⊓ Subgroup.centralizer (H : Set W), inf_le_left, ?_, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro x hxD hxW
    exact Subgroup.disjoint_def.mp hddisj hxD (hfocal ⟨hxD.1, hxW⟩)
  · calc (S : Subgroup W)
        = ((S : Subgroup W) ⊓ Subgroup.centralizer (H : Set W)) ⊔ ⁅(S : Subgroup W), H⁆ :=
          hdsup.symm
      _ ≤ ((S : Subgroup W) ⊓ Subgroup.centralizer (H : Set W)) ⊔ commutator W :=
          sup_le_sup_left hSH _

end Burnside

section Ambient

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem exists_disjoint_commutator_of_maximal_abelian (W S : Subgroup G) (hSW : S ≤ W)
    (hSp : IsPGroup p S) (hmax : ∀ Q : Subgroup G, Q ≤ W → IsPGroup p Q → S ≤ Q → Q = S)
    (hS : IsMulCommutative S) :
    ∃ D : Subgroup G, D ≤ S ∧ Disjoint D ⁅W, W⁆ ∧ S ≤ D ⊔ ⁅W, W⁆ := by
  let S' : Sylow p W :=
    ⟨S.subgroupOf W, IsPGroup.of_equiv hSp (Subgroup.subgroupOfEquivOfLe hSW).symm, by
      intro Q' hQ' hle
      have hQW : Q'.map W.subtype ≤ W := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hSQ : S ≤ Q'.map W.subtype := fun x hx =>
        ⟨⟨x, hSW hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
      have h := hmax _ hQW (hQ'.map W.subtype) hSQ
      calc Q' = (Q'.map W.subtype).comap W.subtype :=
            (Subgroup.comap_map_eq_self_of_injective W.subtype_injective Q').symm
        _ = S.subgroupOf W := by rw [h]; rfl⟩
  have hS'ab : IsMulCommutative (S' : Subgroup W) := by
    have := hS
    exact Subgroup.comap_injective_isMulCommutative S W.subtype_injective
  obtain ⟨D', hD'S, hD'dis, hS'le⟩ := exists_disjoint_commutator_of_abelian_sylow S' hS'ab
  refine ⟨D'.map W.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hD'S hd)
  · rw [Subgroup.disjoint_def]
    rintro _ ⟨d, hd, rfl⟩ hdc
    rw [← Subgroup.map_subtype_commutator] at hdc
    obtain ⟨c, hc, hcd⟩ := hdc
    obtain rfl : c = d := Subtype.ext hcd
    rw [Subgroup.disjoint_def.mp hD'dis hd hc]
    rfl
  · intro s hs
    have h : (⟨s, hSW hs⟩ : W) ∈ D' ⊔ commutator W := hS'le (Subgroup.mem_subgroupOf.mpr hs)
    have h2 := Subgroup.mem_map_of_mem W.subtype h
    rwa [Subgroup.map_sup, Subgroup.map_subtype_commutator] at h2

end Ambient

theorem exists_outer_order_p_of_outer_centralizes
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K) (hnonab : ∃ a b : K, a * b ≠ b * a)
    {p : ℕ} [Fact p.Prime] (P : Sylow p K) (hPab : IsMulCommutative (P : Subgroup K))
    {φ : MulAut K} (hφ : ∃ n : ℕ, φ ^ (p ^ n) = 1)
    (hcomm : ∀ g ∈ (P : Subgroup K), φ * MulAut.conj g = MulAut.conj g * φ)
    (hout : φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ α : MulAut K, α ^ p = 1 ∧ α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K ∧
      ∀ g ∈ (P : Subgroup K), α * MulAut.conj g = MulAut.conj g * α := by
  classical
  haveI : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    (fun f g h => MulEquiv.ext (congrFun h))
  obtain ⟨n, hn⟩ := hφ
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 := mem_center_of_conj_eq_one (MonoidHom.mem_ker.mp hx)
    rwa [center_eq_bot_of_simple hs hnonab] at h1
  have hperf : commutator K = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator K) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator K := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  set I : Subgroup (MulAut K) := inner K with hI
  set W : Subgroup (MulAut K) :=
    (Subgroup.zpowers (QuotientGroup.mk φ : MulAut K ⧸ I)).comap (QuotientGroup.mk' I) with hW
  have hIW : I ≤ W := fun x hx => by
    rw [hW, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  have hφW : φ ∈ W := by
    rw [hW, Subgroup.mem_comap, QuotientGroup.mk'_apply]
    exact Subgroup.mem_zpowers _
  have hWI : ⁅W, W⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.1 hb
    have h1 : QuotientGroup.mk' I ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, ← hm, ← hm', commutatorElement_eq_one_iff_mul_comm]
      exact (Commute.zpow_zpow_self _ m m').eq
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hIW' : I ≤ ⁅W, W⁆ := by
    have h1 : I = (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) :=
      MonoidHom.range_eq_map _
    have h2 : ⁅I, I⁆ =
        Subgroup.map (MulAut.conj : K →* MulAut K) ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ := by
      rw [Subgroup.map_commutator, ← h1]
    have h3 : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
      rw [← _root_.commutator_def]
      exact hperf
    have h4 : I ≤ ⁅I, I⁆ := by rw [h2, h3, ← h1]
    exact h4.trans (Subgroup.commutator_mono hIW hIW)
  set Pi : Subgroup (MulAut K) := (P : Subgroup K).map (MulAut.conj : K →* MulAut K) with hPi
  set S : Subgroup (MulAut K) := Pi ⊔ Subgroup.zpowers φ with hS
  have hPiI : Pi ≤ I := by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  have hSW : S ≤ W := sup_le (hPiI.trans hIW) (Subgroup.zpowers_le.2 hφW)
  have hφS : φ ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers φ)
  have hPiS : ∀ g ∈ (P : Subgroup K), MulAut.conj g ∈ S := fun g hg =>
    Subgroup.mem_sup_left ⟨g, hg, rfl⟩
  have hφPi : ∀ x ∈ Pi, x * φ = φ * x := by
    rintro _ ⟨g, hg, rfl⟩
    exact (hcomm g hg).symm
  have hpz : IsPGroup p (Subgroup.zpowers φ) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨n, Subtype.ext ?_⟩
    show (φ ^ m) ^ (p ^ n) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]
  have hSp : IsPGroup p S := by
    refine IsPGroup.to_sup_of_normal_left' (P.isPGroup'.map _) hpz ?_
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    exact hφPi
  have hSab : IsMulCommutative S := by
    have := hPab
    have hPiab : IsMulCommutative Pi := Subgroup.map_isMulCommutative _ _
    rw [hS, Subgroup.sup_eq_closure]
    apply Subgroup.isMulCommutative_closure
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Subgroup.mul_comm_of_mem_isMulCommutative Pi hx hy
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute x φ from hφPi x hx).zpow_right m).eq
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact (((show Commute y φ from hφPi y hy).zpow_right m).eq).symm
    · exact Subgroup.mul_comm_of_mem_isMulCommutative _ hx hy
  have hmax : ∀ Q : Subgroup (MulAut K), Q ≤ W → IsPGroup p Q → S ≤ Q → Q = S := by
    intro Q hQW hQp hSQ
    refine le_antisymm (fun q hq => ?_) hSQ
    have hqW : (QuotientGroup.mk q : MulAut K ⧸ I) ∈ Subgroup.zpowers (QuotientGroup.mk φ) :=
      hQW hq
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hqW
    have hf : φ ^ m ∈ S := S.zpow_mem hφS m
    have hi : q * (φ ^ m)⁻¹ ∈ I := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow, hm, mul_inv_cancel]
    have hiQ : q * (φ ^ m)⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem (hSQ hf))
    have hQkp : IsPGroup p ((Q ⊓ I).comap (MulAut.conj : K →* MulAut K)) :=
      hQp.to_inf_left.comap_of_injective _ hinj
    have hPQk : (P : Subgroup K) ≤ (Q ⊓ I).comap (MulAut.conj : K →* MulAut K) := fun g hg =>
      ⟨hSQ (hPiS g hg), ⟨g, rfl⟩⟩
    have hQkP := P.is_maximal' hQkp hPQk
    obtain ⟨k, hk⟩ := hi
    have hkP : k ∈ (P : Subgroup K) := by
      rw [← hQkP]
      exact ⟨by rw [hk]; exact hiQ, ⟨k, rfl⟩⟩
    have h1 : q * (φ ^ m)⁻¹ ∈ S := by
      rw [← hk]
      exact hPiS k hkP
    have h2 : q = (q * (φ ^ m)⁻¹) * φ ^ m := by group
    rw [h2]
    exact S.mul_mem h1 hf
  obtain ⟨D, hDS, hDdis, hSle⟩ :=
    exists_disjoint_commutator_of_maximal_abelian W S hSW hSp hmax hSab
  have hDne : D ≠ ⊥ := by
    intro hD
    apply hout
    have h1 : φ ∈ D ⊔ ⁅W, W⁆ := hSle hφS
    rw [hD, bot_sup_eq] at h1
    exact hWI h1
  have hDp : IsPGroup p D := hSp.to_le hDS
  have hpD : p ∣ Nat.card D := by
    rcases hDp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hDne
    · exact h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := D) p hpD
  have hzord : orderOf (u : MulAut K) = p := by rw [Subgroup.orderOf_coe, hu]
  refine ⟨(u : MulAut K), ?_, ?_, ?_⟩
  · rw [← hzord]
    exact pow_orderOf_eq_one _
  · intro hzI
    have h1 := Subgroup.disjoint_def.mp hDdis u.2 (hIW' hzI)
    rw [h1, orderOf_one] at hzord
    exact (Fact.out : p.Prime).one_lt.ne hzord
  · intro g hg
    exact congrArg Subtype.val (hSab.is_comm.comm ⟨_, hDS u.2⟩ ⟨_, hPiS g hg⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
