module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.BProg.B3.S3T2A7Defs
public import CFSG.GH74.Generic.Certificates
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}

theorem mem_of_comm_of_sq_mem (hs : Setting125 Y L B X₀ z)
    (hc : RankCertified (↥L ⧸ center ↥L) 3) {u : Y} (hu : ∀ x ∈ L, u * x = x * u)
    (hu2 : u * u ∈ L) : u ∈ L := by
  by_contra huL
  obtain ⟨K, A, _, _, _, α, β, hβ, hAc, hAs, hcard, hker⟩ := hc
  set Z : Subgroup Y := zpowers u with hZ
  have hZc : ∀ t ∈ Z, ∀ x ∈ L, t * x = x * t := by
    intro t ht x hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_left (hu x hx) j).eq
  have hZab : ∀ s t : ↥Z, s * t = t * s := by
    rintro ⟨s, hsZ⟩ ⟨t, htZ⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hsZ
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp htZ
    exact Subtype.ext (by simp only [Subgroup.coe_mul, ← zpow_add, add_comm])
  set N : Subgroup ↥Z := L.subgroupOf Z with hN
  have hNn : N.Normal := ⟨fun n hn g => by rwa [hZab g n, mul_inv_cancel_right]⟩
  let P : Subgroup (K × ↥L) := (α.comp (MonoidHom.fst K ↥L)).eqLocus
    ((QuotientGroup.mk' (center ↥L)).comp (MonoidHom.snd K ↥L))
  have hmul : ∀ (l l' : ↥L) (t t' : ↥Z), ((l * l' : ↥L) : Y) * ((t * t' : ↥Z) : Y) =
      ((l : Y) * (t : Y)) * ((l' : Y) * (t' : Y)) := by
    intro l l' t t'
    have h := hZc _ t.2 _ l'.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc (l : Y) * l' * (t * t') = (l : Y) * ((l' : Y) * t) * t' := by
          simp only [mul_assoc]
      _ = (l : Y) * ((t : Y) * l') * t' := by rw [h]
      _ = (l : Y) * t * (l' * t') := by simp only [mul_assoc]
  let Φ : ↥P × ↥Z →* Y :=
    { toFun := fun p => (((p.1 : K × ↥L).2 : ↥L) : Y) * (p.2 : Y)
      map_one' := by simp
      map_mul' := fun p q => hmul _ _ _ _ }
  let β' : ↥P × ↥Z →* A × (↥Z ⧸ N) :=
    (β.comp ((MonoidHom.fst K ↥L).comp P.subtype)).prodMap (QuotientGroup.mk' N)
  have hQc : ∀ a b : ↥Z ⧸ N, a * b = b * a := by
    rintro ⟨s⟩ ⟨t⟩
    exact congrArg (QuotientGroup.mk (s := N)) (hZab s t)
  have hQs : ∀ a : ↥Z ⧸ N, a ^ 2 = 1 := by
    rintro ⟨⟨t, htZ⟩⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp htZ
    change (QuotientGroup.mk (⟨u ^ j, htZ⟩ ^ 2 : ↥Z) : ↥Z ⧸ N) = 1
    rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    have : ((⟨u ^ j, htZ⟩ ^ 2 : ↥Z) : Y) = (u * u) ^ j := by
      rw [Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, ← sq, ← zpow_natCast, ← zpow_mul,
        mul_comm]
    rw [this]
    exact zpow_mem hu2 j
  have hQ2 : 2 ≤ Nat.card (↥Z ⧸ N) := by
    have hne : (QuotientGroup.mk (⟨u, mem_zpowers u⟩ : ↥Z) : ↥Z ⧸ N) ≠ 1 := by
      rw [Ne, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
      exact huL
    have : Nontrivial (↥Z ⧸ N) := ⟨⟨_, _, hne⟩⟩
    exact Finite.one_lt_card
  have hY4 : RankCertified Y 4 := by
    refine ⟨↥P × ↥Z, A × (↥Z ⧸ N), inferInstance, inferInstance, inferInstance, Φ, β', ?_,
      ?_, ?_, ?_, ?_⟩
    · rintro ⟨a, q⟩
      obtain ⟨k, rfl⟩ := hβ a
      obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (center ↥L) (α k)
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N q
      exact ⟨(⟨(k, l), hl.symm⟩, t), rfl⟩
    · rintro ⟨a, q⟩ ⟨a', q'⟩
      exact Prod.ext (hAc a a') (hQc q q')
    · rintro ⟨a, q⟩
      exact Prod.ext (hAs a) (hQs q)
    · rw [Nat.card_prod]
      calc 2 ^ 4 = 2 ^ 3 * 2 := by norm_num
        _ < Nat.card A * Nat.card (↥Z ⧸ N) :=
          Nat.mul_lt_mul_of_lt_of_le hcard hQ2 (by norm_num)
    · rintro ⟨⟨⟨k, l⟩, hkl⟩, t⟩ hp
      have h1 : (l : Y) * (t : Y) = 1 := MonoidHom.mem_ker.mp hp
      have htl : (t : Y) = (l : Y)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hlZ : l ∈ center ↥L := mem_center_iff.mpr fun x => Subtype.ext <| by
        have hx := hZc _ t.2 _ x.2
        rw [htl] at hx
        calc (x : Y) * l = (l : Y) * ((l : Y)⁻¹ * x) * l := by group
          _ = (l : Y) * (x * (l : Y)⁻¹) * l := by rw [hx]
          _ = l * x := by group
      have hk : α k = 1 := by
        have : α k = QuotientGroup.mk' (center ↥L) l := hkl
        rw [this, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hlZ
      have htN : t ∈ N := by
        rw [hN, Subgroup.mem_subgroupOf, htl]
        exact inv_mem l.2
      rw [MonoidHom.mem_ker]
      refine Prod.ext ?_ ?_
      · exact MonoidHom.mem_ker.mp (hker (MonoidHom.mem_ker.mpr hk))
      · exact (QuotientGroup.eq_one_iff t).mpr htN
  exact hY4.not_sectionalTwoRankLE (hs.sec4.mono (by norm_num))

theorem mem_of_inner (hs : Setting125 Y L B X₀ z) (hc : RankCertified (↥L ⧸ center ↥L) 3)
    {b l : Y} (hl : l ∈ L) (hb2 : b * b = 1) (h : ∀ x ∈ L, b * x * b⁻¹ = l * x * l⁻¹) :
    b ∈ L := by
  have hu : ∀ x ∈ L, l⁻¹ * b * x = x * (l⁻¹ * b) := by
    intro x hx
    calc l⁻¹ * b * x = l⁻¹ * (b * x * b⁻¹) * b := by group
      _ = l⁻¹ * (l * x * l⁻¹) * b := by rw [h x hx]
      _ = x * (l⁻¹ * b) := by group
  have hu2 : l⁻¹ * b * (l⁻¹ * b) ∈ L := by
    have h1 : b * l⁻¹ * b⁻¹ = l⁻¹ := by rw [h _ (inv_mem hl)]; group
    have h2 : l⁻¹ * b * (l⁻¹ * b) = l⁻¹ * (b * l⁻¹ * b⁻¹) * (b * b) := by group
    rw [h2, h1, hb2, mul_one]
    exact mul_mem (inv_mem hl) (inv_mem hl)
  have huL := mem_of_comm_of_sq_mem hs hc hu hu2
  have hb : b = l * (l⁻¹ * b) := by group
  rw [hb]
  exact mul_mem hl huL

end CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR
