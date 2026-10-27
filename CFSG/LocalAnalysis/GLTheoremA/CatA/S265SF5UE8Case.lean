module

import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5USC5
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UY6Max
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGPin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.Blueprint.Chevalley

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

private theorem five_dvd_sq_add_one_of_rk2Ord_four {n : ℕ} (h : rk2Ord 5 n = 4) :
    5 ∣ 2 ^ n * 2 ^ n + 1 := by
  have key : ∀ a : ZMod 5, a ^ 4 = 1 → a ^ 2 ≠ 1 → a * a + 1 = 0 := by decide
  have h4 : ((2 : ZMod 5) ^ n) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, show (2 : ZMod 5) ^ 4 = 1 from by decide, one_pow]
  have h2 : ((2 : ZMod 5) ^ n) ^ 2 ≠ 1 := fun h2 => by
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [show orderOf ((2 : ZMod 5) ^ n) = 4 from h] at h3
    norm_num at h3
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact key _ h4 h2


theorem false_of_e8_rk2Ord_four (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {lab : GLALabel} (hlab : InnLabelOf B S lab)
    (hlab2 : GLAInLambda2 lab) (ht : lab.tag = .E8) (he : rk2Ord 5 lab.n = 4) : False := by
  have hc := h.cfg
  haveI : Fact (Nat.Prime 5) := ⟨hc.prime⟩
  haveI := hc.normal
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht he
  subst ht
  have hn : 1 ≤ n := hlab2.1
  obtain ⟨hcomm, lab', -, hraw⟩ := hlab
  obtain ⟨-, -, -, -, -, -, -, hl, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hl
  obtain ⟨F, _, _, hFc, -, ⟨a₀, b₀, hab₀⟩, θ, -, -, hind⟩ := hraw
  haveI : CharP F 2 := CFSG.StandardType.charP_two_of_card hFc
  have hZ : Subgroup.center ↥S = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8
      ⟨⟨hcomm⟩, hc.quasi.2, θ.symm a₀, θ.symm b₀, fun h' => hab₀ (by simpa using congrArg θ h')⟩
      hn hFc (θ.trans (Classical.choice (CFSG.StandardType.centerQuot_chevGroup_equiv F .E8)))
  have hinn : ∀ φ ∈ CFSG.Assembly.LargeEvenChevIDImage (CFSG.Assembly.LargeEvenCartanE 8) F
      (CFSG.Assembly.LargeEvenChevH (CFSG.Assembly.LargeEvenCartanE 8) F false),
      ∃ r, MulAut.conj r = φ := fun φ hφ => CFSG.StandardType.TableBExc.idImage_subset_inn_E8 F hφ
  have hdec : ∀ b ∈ B, ∃ s ∈ S, s⁻¹ * b ∈ Subgroup.centralizer (S : Set Ω) := by
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hind b⁻¹ (B.inv_mem hb)
    obtain ⟨r, hr⟩ := hinn φ hφI
    obtain ⟨qs, rfl⟩ := θ.surjective r
    obtain ⟨⟨s, hsS⟩, rfl⟩ := QuotientGroup.mk_surjective qs
    refine ⟨s, hsS, inv_mul_mem_centralizer_of_mk_eq ⟨hcomm⟩ (hSN s) (hSN b)
      fun k k₁ k₂ hk₁ hk₂ => θ.injective ?_⟩
    rw [← hφ k k₂ (by rw [inv_inv]; exact hk₂), ← hr, MulAut.conj_apply, ← map_inv, ← map_mul,
      ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg (fun y : ↥S => θ (y : ↥S ⧸ Subgroup.center ↥S)) (Subtype.ext hk₁)
  set N := Subgroup.centralizer (S : Set Ω)
  set q : Ω →* Ω ⧸ N := QuotientGroup.mk' N
  set ν : ↥S →* Ω ⧸ N := q.comp S.subtype
  have hνi : Function.Injective ν := by
    refine (injective_iff_map_eq_one ν).2 fun s hs => ?_
    have hsN : (s : Ω) ∈ N := (QuotientGroup.eq_one_iff _).1 hs
    have hsZ : s ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun t =>
      Subtype.ext (Subgroup.mem_centralizer_iff.1 hsN t t.2)
    rwa [hZ, Subgroup.mem_bot] at hsZ
  have hBQ : IsElemAbelian 5 (B.map q) := hc.elem.map q
  set BS : Subgroup ↥S := (B.map q).comap ν
  have hmem : ∀ b ∈ B, ∀ s : ↥S, (s : Ω)⁻¹ * b ∈ N → s ∈ BS := fun b hb s hsb =>
    ⟨b, hb, (QuotientGroup.eq.2 hsb).symm⟩
  have hle : B.map q ≤ ν.range := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨s, hsS, hsb⟩ := hdec b hb
    exact ⟨⟨s, hsS⟩, QuotientGroup.eq.2 hsb⟩
  have hBSel : IsElemAbelian 5 BS := by
    refine ⟨⟨⟨fun a c => Subtype.ext (hνi ?_)⟩⟩, fun s hs => hνi ?_⟩
    · have := hBQ.1.is_comm.comm ⟨ν a, a.2⟩ ⟨ν c, c.2⟩
      simpa only [Subgroup.coe_mul, map_mul, Subtype.ext_iff] using this
    · rw [map_pow, map_one]
      exact hBQ.2 _ hs
  have hBN : N ⊓ B = Subgroup.zpowers x ⊓ B := by
    apply le_antisymm
    · rintro g ⟨hgN, hgB⟩
      refine ⟨(hc.centB g hgB).1 ⟨hSN g, ?_⟩, hgB⟩
      rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).2
        (Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2 hgN))]
      exact bot_le
    · rintro g ⟨hgx, hgB⟩
      exact ⟨((Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 hc.xcen)).trans
        (Subgroup.center_le_centralizer _)) hgx, hgB⟩
  have hcard : Nat.card BS = 5 ^ 3 := by
    have h1 : Nat.card BS = Nat.card (B.map q) := by
      rw [← Subgroup.card_map_of_injective hνi, Subgroup.map_comap_eq, inf_of_le_right hle]
    have h2 := Subgroup.card_ker_mul_card_range (q.comp B.subtype)
    have hker : q.ker = N := QuotientGroup.ker_mk' N
    rw [MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.comap_ker, hker] at h2
    have h3 : Nat.card (N.comap B.subtype) = 5 := by
      change Nat.card (N.subgroupOf B) = 5
      rw [Subgroup.subgroupOf_inj.2 hBN,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hc.xB)).toEquiv,
        Nat.card_zpowers, orderOf_eq_prime (hc.elem.2 x hc.xB) hc.x1]
    rw [h3, card_eq_of_qsnl h hF] at h2
    rw [h1]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h2.trans (by norm_num))
  set ι : ↥S ≃* adjointGroup .E8 F := (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
      (θ.trans (CFSG.StandardType.TableBExc.recipeEquiv .E8 F))
  have h5 : 5 ∣ Nat.card F * Nat.card F + 1 := by
    rw [hFc]
    exact five_dvd_sq_add_one_of_rk2Ord_four he
  obtain ⟨E', hEE', hE'el, hE'card⟩ := e8FiveMaxRank_holds F h5 (BS.map ι.toMonoidHom)
    (hBSel.map _) ((Subgroup.card_map_of_injective ι.injective).trans hcard)
  set H' : Subgroup ↥S := E'.comap ι.toMonoidHom
  have hH'eq : H' = E'.map ι.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm' ι E'
  have hH'el : IsElemAbelian 5 H' := hH'eq ▸ hE'el.map _
  have hBSH' : BS ≤ H' := Subgroup.map_le_iff_le_comap.1 hEE'
  have hHB : H'.map S.subtype ≤ B := by
    rintro _ ⟨h', hh', rfl⟩
    refine mem_of_pow_eq_one_of_forall_commute h hF (by
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hH'el.2 h' hh', Subgroup.coe_one])
      fun b hb => ?_
    obtain ⟨s, hsS, hsb⟩ := hdec b hb
    have e1 : (h' : Ω) * s = s * h' := by
      have := congrArg (fun z : ↥H' => ((z : ↥S) : Ω))
        (hH'el.1.is_comm.comm ⟨h', hh'⟩ ⟨⟨s, hsS⟩, hBSH' (hmem b hb ⟨s, hsS⟩ hsb)⟩)
      simpa using this
    have e2 : (h' : Ω) * (s⁻¹ * b) = s⁻¹ * b * h' := Subgroup.mem_centralizer_iff.1 hsb _ h'.2
    calc S.subtype h' * b = (h' : Ω) * s * (s⁻¹ * b) := by simp [mul_assoc]
      _ = s * ((h' : Ω) * (s⁻¹ * b)) := by rw [e1, mul_assoc]
      _ = s * (s⁻¹ * b * h') := by rw [e2]
      _ = b * S.subtype h' := by simp [mul_assoc]
  have hHcard : Nat.card (H'.map S.subtype) = 5 ^ 4 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hH'eq,
      Subgroup.card_map_of_injective ι.symm.injective, hE'card]
  have hHeq := Subgroup.eq_of_le_of_card_ge hHB (by rw [card_eq_of_qsnl h hF, hHcard])
  obtain ⟨y, -, hy⟩ : x ∈ H'.map S.subtype := hHeq ▸ hc.xB
  have hyZ : y ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun t => by
    have hyx : (y : Ω) = x := hy
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hyx]; exact hc.xcen t)
  rw [hZ, Subgroup.mem_bot] at hyZ
  exact hc.x1 (by rw [← hy, hyZ, map_one])

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
