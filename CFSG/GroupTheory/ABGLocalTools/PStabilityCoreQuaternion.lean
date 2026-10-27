module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreGW
public import CFSG.GroupTheory.QuasiDihedralFusion.Defs
import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralClassification
import CFSG.GroupTheory.QuasiDihedralFusion.Structure
import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport

public section

open Subgroup
open CFSG.QuasiDihedralFusion

namespace CFSG.ABGLocalTools

theorem quaternionGroup_eq_a_of_orderOf_eq_two {n : ℕ} [NeZero n] {c : QuaternionGroup n}
    (hc : orderOf c = 2) : c = QuaternionGroup.a n := by
  cases c with
  | a i =>
    have h2 : QuaternionGroup.a (i + i) = QuaternionGroup.a (0 : ZMod (2 * n)) := by
      rw [← QuaternionGroup.a_mul_a, ← QuaternionGroup.one_def, ← sq, ← hc, pow_orderOf_eq_one]
    have hii : i + i = 0 := QuaternionGroup.a.inj h2
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [← QuaternionGroup.one_def, orderOf_one] at hc
      exact absurd hc (by norm_num)
    have hval := ZMod.val_add i i
    rw [hii, ZMod.val_zero] at hval
    have hpos : i.val ≠ 0 := fun h => hi0 ((ZMod.val_eq_zero i).mp h)
    have hn : i.val = n := by
      have h1 : 2 * n ∣ 2 * i.val := by
        rw [two_mul i.val]
        exact Nat.dvd_of_mod_eq_zero hval.symm
      exact Nat.eq_of_dvd_of_lt_two_mul hpos (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1)
        (ZMod.val_lt i)
    rw [← ZMod.natCast_zmod_val i, hn]
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hc
    exact absurd hc (by norm_num)

variable {H : Type*} [Group H] [Finite H]

theorem exists_mem_orderOf_eq_two {X : Subgroup H} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥) :
    ∃ x ∈ X, orderOf x = 2 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hX1 (card_eq_one.mp (by simpa using hn))
  have h2 : 2 ∣ Nat.card X := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨c, c.2, by rw [orderOf_coe]; exact hc⟩

theorem inf_centerOf_ne_bot {R N : Subgroup H} (hR : IsPGroup 2 R) [N.Normal]
    (hNR : N ⊓ R ≠ ⊥) : N ⊓ centerOf R ≠ ⊥ := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hM : N.subgroupOf R ≠ ⊥ := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := ne_bot_iff_exists_ne_one.mp hNR
    have hx' := mem_inf.mp hx
    intro h
    have hmem : (⟨x, hx'.2⟩ : R) ∈ N.subgroupOf R := mem_subgroupOf.mpr hx'.1
    rw [h, mem_bot] at hmem
    have hx1' : x = 1 := by simpa using congrArg Subtype.val hmem
    exact hx1 (Subtype.ext hx1')
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hM
  obtain ⟨⟨m, hm⟩, hm1⟩ := ne_bot_iff_exists_ne_one.mp h
  have hmN : m ∈ N.subgroupOf R := (mem_inf.mp hm).1
  have hmZ : m ∈ center R := (mem_inf.mp hm).2
  have hmC : (m : H) ∈ centerOf R := by
    refine mem_inf.mpr ⟨m.2, ?_⟩
    rw [mem_centralizer_iff]
    intro r hr
    have := mem_center_iff.mp hmZ ⟨r, hr⟩
    simpa using congrArg Subtype.val this
  rw [ne_bot_iff_exists_ne_one]
  refine ⟨⟨m, mem_inf.mpr ⟨mem_subgroupOf.mp hmN, hmC⟩⟩, fun h1 => hm1 ?_⟩
  have hm1' : (m : H) = 1 := by simpa using congrArg Subtype.val h1
  exact Subtype.ext (Subtype.ext (by simpa using hm1'))

theorem inf_inf_ne_bot_of_isCyclic {R A B : Subgroup H} (hR : IsPGroup 2 R)
    [IsCyclic (centerOf R)] (hA : A ⊓ centerOf R ≠ ⊥) (hB : B ⊓ centerOf R ≠ ⊥) :
    A ⊓ B ⊓ R ≠ ⊥ := by
  have hZ : centerOf R ≤ R := inf_le_left
  obtain ⟨a, ha, hao⟩ := exists_mem_orderOf_eq_two
    (hR.to_le (inf_le_right.trans hZ)) hA
  obtain ⟨b, hb, hbo⟩ := exists_mem_orderOf_eq_two
    (hR.to_le (inf_le_right.trans hZ)) hB
  have hab : (⟨a, ha.2⟩ : centerOf R) = ⟨b, hb.2⟩ :=
    eq_of_orderOf_eq_two_of_isCyclic (by rw [← orderOf_coe]; exact hao)
      (by rw [← orderOf_coe]; exact hbo)
  have hab' : a = b := congrArg Subtype.val hab
  rw [ne_bot_iff_exists_ne_one]
  refine ⟨⟨a, ⟨ha.1, hab' ▸ hb.1⟩, hZ ha.2⟩, fun h => ?_⟩
  have : a = 1 := congrArg Subtype.val h
  rw [this, orderOf_one] at hao
  exact absurd hao (by norm_num)

omit [Finite H] in
theorem isCyclic_centerOf_of_hasQDOrWreathedSylow (h : HasQDOrWreathedSylow H) (R : Sylow 2 H) :
    IsCyclic (centerOf (R : Subgroup H)) := by
  obtain ⟨m, hm | hm⟩ := h
  · obtain ⟨-, n, hn, hR⟩ := hm
    obtain ⟨f⟩ := hR R
    rw [centerOf_eq_zpowers_z hn (R : Subgroup H) f]
    infer_instance
  · obtain ⟨hm2, hR⟩ := hm
    obtain ⟨e⟩ := hR R
    rw [centerOf_eq_modelCenter hm2 R e, CFSG.Wreathed.modelCenter, CFSG.Wreathed.Original.Z,
      MonoidHom.map_zpowers]
    infer_instance

theorem quaternion_involution_mem {R : Sylow 2 H} {K : Subgroup H} (hRK : IsQGroupData R K)
    (hZ : IsCyclic (centerOf (R : Subgroup H))) (L : Subgroup H) [L.Normal]
    (hL : ¬ L ≤ CFSG.oddCore H) {k : ℕ}
    (eY : (K ⊓ (R : Subgroup H) : Subgroup H) ≃* QuaternionGroup (2 ^ k)) :
    ((eY.symm (QuaternionGroup.a (2 ^ k : ℕ)) : H) ∈ L) := by
  have hK := hRK.normal
  have hR : IsPGroup 2 (R : Subgroup H) := R.isPGroup'
  have hLR : L ⊓ (R : Subgroup H) ≠ ⊥ := by
    intro hbot
    apply hL
    refine le_oddCore_of_normal inferInstance (Nat.odd_iff.mpr ?_)
    have hidx := not_dvd_relIndex_of_normal R L
    have hsub : (R : Subgroup H).subgroupOf L = ⊥ := by
      rw [subgroupOf_eq_bot, disjoint_iff, inf_comm]
      exact hbot
    rw [hsub, index_bot] at hidx
    omega
  have hKR : K ⊓ (R : Subgroup H) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (K ⊓ (R : Subgroup H) : Subgroup H) = 1 := by
      rw [hbot]; exact card_bot
    rw [Nat.card_congr eY.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] at h1
    have : 0 < 2 ^ k := by positivity
    omega
  have hA := inf_centerOf_ne_bot hR hLR
  have hB := inf_centerOf_ne_bot hR hKR
  have hLKR := inf_inf_ne_bot_of_isCyclic hR hA hB
  obtain ⟨c, hc, hco⟩ := exists_mem_orderOf_eq_two (hR.to_le inf_le_right) hLKR
  set c' : (K ⊓ (R : Subgroup H) : Subgroup H) := ⟨c, hc.1.2, hc.2⟩
  have hc'o : orderOf (eY c') = 2 := by
    rw [MulEquiv.orderOf_eq, ← orderOf_coe]
    exact hco
  have hq := quaternionGroup_eq_a_of_orderOf_eq_two hc'o
  rw [← hq, MulEquiv.symm_apply_apply]
  exact hc.1.1

variable {p : ℕ} [Fact p.Prime]

theorem mem_pCore_quotient_of_not_le_oddCore (hp : p ≠ 2) {R : Sylow 2 H} {K : Subgroup H}
    (hRK : IsQGroupData R K) (hZ : IsCyclic (centerOf (R : Subgroup H))) (L : Subgroup H)
    [L.Normal] (hL : ¬ L ≤ CFSG.oddCore H) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (ρ : H ⧸ L →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hρ : Function.Injective ρ) (x : H) (hxp : ∃ k : ℕ, x ^ p ^ k = 1)
    (hx : ((ρ (x : H ⧸ L) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) :
    (x : H ⧸ L) ∈ pCore p (H ⧸ L) := by
  have hK := hRK.normal
  obtain ⟨k, -, ⟨eY⟩⟩ := hRK.quaternion.exists_quaternion_equiv
  have hz := quaternion_involution_mem hRK hZ L hL eY
  have hxK : x ∈ K := by
    obtain ⟨j, hj⟩ := hRK.index_eq_two_pow
    obtain ⟨e, he⟩ := hxp
    refine CFSG.Semidihedral.Local.mem_of_pow_eq_one_of_index K ?_ he
    rw [hj]
    intro hdvd
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd))
  set Kb := K.map (QuotientGroup.mk' L) with hKb
  have hKbn : Kb.Normal := hK.map _ (QuotientGroup.mk'_surjective L)
  set f := (QuotientGroup.mk' L).subgroupMap K with hf
  have hfs : Function.Surjective f := (QuotientGroup.mk' L).subgroupMap_surjective K
  set P : Sylow 2 Kb := (sylowInfNormal R K).mapSurjective hfs with hPdef
  have hP : CyclicModInvolutions (P : Subgroup Kb) := by
    rw [hPdef, Sylow.coe_mapSurjective]
    change CyclicModInvolutions (((R : Subgroup H).subgroupOf K).map f)
    set g₀ : (K ⊓ (R : Subgroup H) : Subgroup H) := eY.symm (QuaternionGroup.a 1) with hg₀
    have hg₀K : (g₀ : H) ∈ K := g₀.2.1
    refine ⟨zpowers (f ⟨g₀, hg₀K⟩), ?_, inferInstance, ?_⟩
    · rw [zpowers_le]
      exact ⟨⟨g₀, hg₀K⟩, mem_subgroupOf.mpr g₀.2.2, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩ hyC
      set y' : (K ⊓ (R : Subgroup H) : Subgroup H) := ⟨y, y.2, mem_subgroupOf.mp hy⟩ with hy'
      cases hq : eY y' with
      | a i =>
        exfalso
        apply hyC
        have h1 : y' = g₀ ^ i.val := by
          rw [← eY.symm_apply_apply y', hq, hg₀, ← map_pow, QuaternionGroup.a_one_pow,
            ZMod.natCast_zmod_val]
        have h2 : y = ⟨g₀, hg₀K⟩ ^ i.val := by
          apply Subtype.ext
          have := congrArg Subtype.val h1
          simpa [hy'] using this
        rw [h2, map_pow]
        exact pow_mem (mem_zpowers _) _
      | xa i =>
        have h2 : eY (y' ^ 2) = QuaternionGroup.a (2 ^ k : ℕ) := by
          rw [map_pow, hq, QuaternionGroup.xa_sq]
        have h3 : ((y' ^ 2 : (K ⊓ (R : Subgroup H) : Subgroup H)) : H) ∈ L := by
          rw [← eY.symm_apply_apply (y' ^ 2), h2]
          exact hz
        rw [← map_pow]
        apply Subtype.ext
        change QuotientGroup.mk' L ((y : H) ^ 2) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        simpa [hy'] using h3
  have hsec : TwoSectionsCyclic Kb := twoSectionsCyclic_of_sylow P hP
  have hxKb : (x : H ⧸ L) ∈ Kb := ⟨x, hxK, rfl⟩
  have hmem := mem_pCore_of_twoSectionsCyclic hsec hp (ρ.comp Kb.subtype)
    (hρ.comp (subtype_injective _)) ⟨_, hxKb⟩ hx
  have hn : Kb.subtype.range.Normal := by
    rw [range_subtype]
    exact hKbn
  exact map_pCore_le_of_injective_of_normal _ (subtype_injective _) hn ⟨_, hmem, rfl⟩

end CFSG.ABGLocalTools
