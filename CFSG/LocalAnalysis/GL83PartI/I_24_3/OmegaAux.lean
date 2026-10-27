module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Walter.AStar.Subnormal

public section

namespace GL83.I243

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {Y : Type*} [Group Y]

theorem exists_mem_not_mem_conj_mem [Finite Y] {p : ℕ} [Fact p.Prime] {P V N : Subgroup Y}
    (hP : IsPGroup p P) (hV : IsPGroup p V) (hPV : ∀ c ∈ P, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hPN : ∀ c ∈ P, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hNV : N < V) :
    ∃ v ∈ V, v ∉ N ∧ ∀ c ∈ P, v⁻¹ * (c * v * c⁻¹) ∈ N := by
  have hnorm : P ≤ Subgroup.normalizer (V : Set Y) := fun c hc =>
    Subgroup.mem_normalizer_iff.mpr fun v =>
      ⟨hPV c hc v, fun hv => by
        have h := hPV c⁻¹ (P.inv_mem hc) _ hv
        rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
          inv_mul_cancel, mul_one] at h⟩
  let ψ : P →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  letI : MulAction P V := MulAction.compHom V ψ
  have hψ : ∀ (c : P) (v : V), ((c • v : V) : Y) = c * v * c⁻¹ := fun c v => rfl
  let N' : Subgroup V := N.subgroupOf V
  haveI : MulAction.QuotientAction P N' :=
    ⟨fun c a a' h => by
      rw [Subgroup.mem_subgroupOf] at h ⊢
      have h' := hPN c c.2 _ h
      convert h' using 1
      simp only [hψ, Subgroup.coe_mul, Subgroup.coe_inv]
      group⟩
  have hdvd : p ∣ Nat.card (V ⧸ N') := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV
    have h2 : N'.index ∣ p ^ k := hk ▸ Subgroup.index_dvd_card N'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).1 h2
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hj
      exact absurd hNV (not_lt_of_ge hj)
    rw [← Subgroup.index, hj]
    exact dvd_pow_self p hj0
  have h1 : ((1 : V) : V ⧸ N') ∈ MulAction.fixedPoints P (V ⧸ N') := fun c => by
    rw [MulAction.Quotient.smul_coe]
    exact congrArg _ (Subtype.ext (by simp [hψ]))
  obtain ⟨q, hq, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (V ⧸ N') hdvd h1
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨v, v.2, fun hvN => hne ?_, fun c hc => ?_⟩
  · rw [QuotientGroup.eq, inv_one, one_mul]
    exact hvN
  · have h := (hq ⟨c, hc⟩).symm
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simpa [hψ] using h

theorem card_le_mul_card_inf_centralizer_of_mem_zpowers [Finite Y] {p : ℕ} {B : Subgroup Y}
    {z w : Y} (hz : orderOf z = p) (hBz : ∀ b ∈ B, b * z = z * b)
    (hBw : ∀ b ∈ B, w⁻¹ * (b * w * b⁻¹) ∈ Subgroup.zpowers z) :
    Nat.card B ≤ p * Nat.card (B ⊓ Subgroup.centralizer ({w} : Set Y) : Subgroup Y) := by
  have hcomm : ∀ a ∈ B, ∀ c ∈ Subgroup.zpowers z, a * c * a⁻¹ = c := fun a ha c hc => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [mul_inv_eq_iff_eq_mul]
    exact (Commute.zpow_right (hBz a ha) n).eq
  let f : B →* Y := MonoidHom.mk' (fun b => w⁻¹ * ((b : Y) * w * (b : Y)⁻¹)) (fun a b => by
    have h := hcomm a a.2 _ (hBw b b.2)
    simp only [Subgroup.coe_mul, mul_inv_rev]
    calc w⁻¹ * ((a : Y) * (b : Y) * w * ((b : Y)⁻¹ * (a : Y)⁻¹))
        = w⁻¹ * ((a : Y) * w * (a : Y)⁻¹) * ((a : Y) * (w⁻¹ * ((b : Y) * w * (b : Y)⁻¹)) *
            (a : Y)⁻¹) := by group
      _ = _ := by rw [h])
  have hrange : f.range ≤ Subgroup.zpowers z := by
    rintro _ ⟨b, rfl⟩
    exact hBw b b.2
  have hker : f.ker = (B ⊓ Subgroup.centralizer ({w} : Set Y)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    change w⁻¹ * ((b : Y) * w * (b : Y)⁻¹) = 1 ↔ _
    rw [inv_mul_eq_one, eq_comm, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hcard := Subgroup.card_ker_mul_card_range f
  have hker' : Nat.card f.ker = Nat.card (B ⊓ Subgroup.centralizer ({w} : Set Y) : Subgroup Y) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange' : Nat.card f.range ≤ p := by
    have := Subgroup.card_le_of_le hrange
    rwa [Nat.card_zpowers, hz] at this
  calc Nat.card B = Nat.card f.ker * Nat.card f.range := hcard.symm
    _ ≤ Nat.card f.ker * p := Nat.mul_le_mul_left _ hrange'
    _ = p * Nat.card (B ⊓ Subgroup.centralizer ({w} : Set Y) : Subgroup Y) := by
      rw [hker', mul_comm]

theorem isElemAbelian_sup_zpowers_and_exists_card [Finite Y] {p : ℕ} (hp : p.Prime)
    {B₀ : Subgroup Y} (hB₀ : IsElemAbelian p B₀) {w : Y} (hw : w ^ p = 1)
    (hwB : ∀ b ∈ B₀, b * w = w * b) (hwn : w ∉ B₀) :
    IsElemAbelian p (B₀ ⊔ Subgroup.zpowers w) ∧
      ∃ b a : ℕ, b < a ∧ Nat.card B₀ = p ^ b ∧
        Nat.card (B₀ ⊔ Subgroup.zpowers w : Subgroup Y) = p ^ a := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : B₀ ≤ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup Y) : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun b hb => hwB b hb)
  have hE := elementary_abelian_sup_of_commuting p hB₀ (isElemAbelian_zpowers hw) hcomm
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hB₀.isPGroup
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hE.isPGroup
  refine ⟨hE, b, a, ?_, hb, ha⟩
  have hle : B₀ ≤ B₀ ⊔ Subgroup.zpowers w := le_sup_left
  have hdvd : p ^ b ∣ p ^ a := hb ▸ ha ▸ Subgroup.card_dvd_of_le hle
  have hba : b ≤ a := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  refine lt_of_le_of_ne hba fun hab => hwn ?_
  have heq : B₀ = B₀ ⊔ Subgroup.zpowers w :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [ha, hb, hab])
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)

theorem isElemAbelian_zpowers_sup_zpowers_and_two_le_pRank [Finite Y] {p : ℕ} (hp : p.Prime)
    {z w : Y} (hz : orderOf z = p) (hw : w ^ p = 1) (hzw : z * w = w * z)
    (hwz : w ∉ Subgroup.zpowers z) :
    IsElemAbelian p (Subgroup.zpowers z ⊔ Subgroup.zpowers w) ∧
      2 ≤ pRank p (Subgroup.zpowers z ⊔ Subgroup.zpowers w) := by
  obtain ⟨hE, b, a, hba, hb, ha⟩ := isElemAbelian_sup_zpowers_and_exists_card hp
    (isElemAbelian_zpowers (hz ▸ pow_orderOf_eq_one z)) hw
    (fun n hn => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      exact (Commute.zpow_left (show Commute z w from hzw) k).eq) hwz
  have hb1 : b = 1 := by
    rw [Nat.card_zpowers, hz] at hb
    exact Nat.pow_right_injective hp.two_le (hb.symm.trans (pow_one p).symm)
  exact ⟨hE, by
    have := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE ha
    omega⟩

theorem mem_sylow_of_mem_of_commute_of_isSubnormal {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (R : Sylow p X) {K : Subgroup X} (hK : K.IsSubnormal) {v : X} (hvK : v ∈ K)
    (hvc : ∀ k ∈ K, k * v = v * k) (hvp : v ^ p = 1) : v ∈ (R : Subgroup X) := by
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hK
  let v' : K := ⟨v, hvK⟩
  haveI : (Subgroup.zpowers v').Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hg : Commute g v' := Subtype.ext (hvc g g.2)
    rw [(hg.zpow_right k).mul_inv_cancel]
    exact hn⟩
  have hNp : IsPGroup p (Subgroup.zpowers v') :=
    (isElemAbelian_zpowers (x := v') (p := p) (Subtype.ext hvp)).isPGroup
  have hNP : Subgroup.zpowers v' ≤ (P : Subgroup K) := hNp.le_sylow_of_normal P
  have hmem : v ∈ (P : Subgroup K).map K.subtype := ⟨v', hNP (Subgroup.mem_zpowers v'), rfl⟩
  rw [hP] at hmem
  exact hmem.1

end GL83.I243
