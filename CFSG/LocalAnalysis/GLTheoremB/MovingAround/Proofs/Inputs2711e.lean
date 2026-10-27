module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711d2
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.RankThree.Asc83Table.MatGroup
public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.ON
public import Certificates.Certificate271101
public import Certificates.Certificate271102

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section Lift

theorem conj_pow_left_of_central {G : Type*} [Group G] {x k z : G}
    (hz : z ∈ Subgroup.center G) (hxk : x * k * x⁻¹ = z * k) :
    ∀ n : ℕ, x ^ n * k * (x ^ n)⁻¹ = z ^ n * k
  | 0 => by simp
  | n + 1 => by
    have hc : x * z ^ n = z ^ n * x := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz n) x
    calc x ^ (n + 1) * k * (x ^ (n + 1))⁻¹ = x * (x ^ n * k * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ']; group
      _ = x * z ^ n * k * x⁻¹ := by rw [conj_pow_left_of_central hz hxk n]; group
      _ = z ^ n * (x * k * x⁻¹) := by rw [hc]; group
      _ = z ^ (n + 1) * k := by rw [hxk, pow_succ, mul_assoc]

theorem conj_pow_right_of_central {G : Type*} [Group G] {x k z : G}
    (hz : z ∈ Subgroup.center G) (hxk : x * k * x⁻¹ = z * k) (n : ℕ) :
    x * k ^ n * x⁻¹ = z ^ n * k ^ n := by
  rw [← conj_pow, hxk]
  exact (Commute.mul_pow (Subgroup.mem_center_iff.1 hz k).symm n)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem commute_of_barHom_commute (hp : p.Prime) {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (u : ↥B) (x : ↥L)
    (hc : Commute (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) (Inputs2711d.barHom hin u))
    {m : ℕ} (hm : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) ^ m = 1) (hpm : ¬ p ∣ m) :
    Commute (x : X) (u : X) := by
  rw [Inputs2711d.barHom_apply] at hc
  set k : ↥L := Inputs2711d.kOf hin u with hk
  have hck : ((k : ↥L) : X)⁻¹ * (u : X) ∈ Subgroup.centralizer (L : Set X) :=
    Inputs2711d.kOf_spec hin u
  set c : X := ((k : ↥L) : X)⁻¹ * (u : X) with hcdef
  have huc : (u : X) = (k : X) * c := by rw [hcdef]; group
  have hkc : (k : X) * c = c * (k : X) := Subgroup.mem_centralizer_iff.1 hck (k : X) k.2
  have hxc : (x : X) * c = c * (x : X) := Subgroup.mem_centralizer_iff.1 hck (x : X) x.2
  set z : ↥L := x * k * x⁻¹ * k⁻¹ with hzdef
  have hz : z ∈ Subgroup.center ↥L := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center ↥L)]
    simp only [hzdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hc.eq]
    group
  have hxk : x * k * x⁻¹ = z * k := by rw [hzdef]; group
  have hkp : k ^ p ∈ Subgroup.center ↥L := by
    apply Inputs2711d.mem_center_of_mem_centralizer
    have h1 : ((k : X) * c) ^ p = 1 := by rw [← huc]; exact hB.2 u u.2
    rw [(show Commute (k : X) c from hkc).mul_pow] at h1
    have h2 : (k : X) ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [Subgroup.coe_pow, h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hck p)
  have hzp : z ^ p = 1 := by
    have h1 := conj_pow_right_of_central hz hxk p
    have h2 : x * k ^ p * x⁻¹ = k ^ p := by
      rw [Subgroup.mem_center_iff.1 hkp x]
      group
    rw [h2] at h1
    exact mul_right_cancel (h1.symm.trans (one_mul (k ^ p)).symm)
  have hzm : z ^ m = 1 := by
    have hxm : x ^ m ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq_one_iff (N := Subgroup.center ↥L), QuotientGroup.mk_pow]
      exact hm
    have h1 := conj_pow_left_of_central hz hxk m
    have h2 : x ^ m * k * (x ^ m)⁻¹ = k := by
      rw [← Subgroup.mem_center_iff.1 hxm k]
      group
    rw [h2] at h1
    exact mul_right_cancel (h1.symm.trans (one_mul k).symm)
  have hz1 : z = 1 := by
    have h : z ^ p.gcd m = 1 := pow_gcd_eq_one.2 ⟨hzp, hzm⟩
    rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm), pow_one] at h
  have hxk' : x * k = k * x := by
    have h1 : x * k * x⁻¹ = k := by rw [hxk, hz1, one_mul]
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [h1]
  have hxk'' : (x : X) * (k : X) = (k : X) * (x : X) := by
    have := congrArg Subtype.val hxk'
    simpa using this
  show (x : X) * u = u * x
  rw [huc]
  calc (x : X) * ((k : X) * c) = ((x : X) * k) * c := by group
    _ = (k * x) * c := by rw [hxk'']
    _ = k * (x * c) := by group
    _ = k * (c * x) := by rw [hxc]
    _ = k * c * x := by group

end Lift

section Gamma

variable {X : Type} [Group X] {p : ℕ}

theorem eq_top_of_sup_center_of_perfect {G : Type*} [Group G] (hG : commutator G = ⊤)
    {M : Subgroup G} (h : M ⊔ Subgroup.center G = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← hG, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have hx : x ∈ M ⊔ Subgroup.center G := h ▸ Subgroup.mem_top x
  have hy : y ∈ M ⊔ Subgroup.center G := h ▸ Subgroup.mem_top y
  obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have h1 : ∀ g : G, z₁ * g = g * z₁ := fun g => (Subgroup.mem_center_iff.mp hz₁ g).symm
  have h2 : ∀ g : G, z₂ * g = g * z₂ := fun g => (Subgroup.mem_center_iff.mp hz₂ g).symm
  rw [commutatorElement_def]
  have hA : c₁ * z₁ * (c₂ * z₂) = c₁ * c₂ * (z₁ * z₂) :=
    Commute.mul_mul_mul_comm (h1 c₂) c₁ z₂
  have hB : c₂ * z₂ * (c₁ * z₁) = c₂ * c₁ * (z₂ * z₁) :=
    Commute.mul_mul_mul_comm (h2 c₁) c₂ z₁
  have hz : z₁ * z₂ = z₂ * z₁ := h1 z₂
  have e : c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
    calc c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ =
        (c₁ * z₁ * (c₂ * z₂)) * (c₂ * z₂ * (c₁ * z₁))⁻¹ := by group
      _ = (c₁ * c₂ * (z₁ * z₂)) * (c₂ * c₁ * (z₂ * z₁))⁻¹ := by rw [hA, hB]
      _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by rw [hz]; group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.mul_mem hc₁ hc₂) (M.inv_mem hc₁)) (M.inv_mem hc₂)

theorem eq_gammaTwo_of_gen [Finite X] (hp : p.Prime) {L B : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    {Q : Type} [Group Q] (τ : (↥L ⧸ Subgroup.center ↥L) ≃* Q) {S : Set Q}
    (hS : Subgroup.closure S = ⊤)
    (hSU : ∀ s ∈ S, ∃ U : Subgroup X, ∃ hUB : U ≤ B, 2 ≤ CFSG.Open.pRank p U ∧
      (∀ u : ↥U, Commute s (τ (Inputs2711d.barHom hin ⟨u, hUB u.2⟩))) ∧
      ∃ m, s ^ m = 1 ∧ ¬ p ∣ m) :
    L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X) := by
  set Γ := ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X) with hΓ
  have hΓL : Γ ≤ L := iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_left
  refine le_antisymm ?_ hΓL
  set H : Subgroup ↥L := Γ.subgroupOf L with hH
  have hmem : ∀ s ∈ S, τ.symm s ∈ H.map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    intro s hs
    obtain ⟨U, hUB, hU2, hcomm, m, hm, hpm⟩ := hSU s hs
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) (τ.symm s)
    refine ⟨x, ?_, hx⟩
    rw [SetLike.mem_coe, hH, Subgroup.mem_subgroupOf]
    have hx' : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = τ.symm s := hx
    have hxC : (x : X) ∈ Subgroup.centralizer (U : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hc : Commute (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L)
          (Inputs2711d.barHom hin ⟨u, hUB hu⟩) := by
        have h1 := (hcomm ⟨u, hu⟩).map τ.symm.toMonoidHom
        rw [hx']
        simpa using h1
      have hxm : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) ^ m = 1 := by
        rw [hx', ← map_pow, hm, map_one]
      exact (commute_of_barHom_commute hp hB hin ⟨u, hUB hu⟩ x hc hxm hpm).eq.symm
    have hxN : (x : X) ∈ Subgroup.normalizer (U : Set X) :=
      Subgroup.centralizer_le_normalizer (U : Set X) hxC
    have hle : L ⊓ Subgroup.normalizer (U : Set X) ≤ Γ :=
      le_iSup_of_le U (le_iSup_of_le hUB (le_iSup_of_le hU2 le_rfl))
    exact hle ⟨x.2, hxN⟩
  have hclos : Subgroup.closure (τ.symm '' S) = ⊤ := by
    have h1 := MonoidHom.map_closure τ.symm.toMonoidHom S
    rw [hS, Subgroup.map_top_of_surjective _ τ.symm.surjective] at h1
    exact h1.symm
  have htop : H.map (QuotientGroup.mk' (Subgroup.center ↥L)) = ⊤ := by
    rw [eq_top_iff, ← hclos, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact hmem s hs
  have hsup : H ⊔ Subgroup.center ↥L = ⊤ := by
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center ↥L)) H
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hHtop : H = ⊤ := eq_top_of_sup_center_of_perfect hLq.1 hsup
  intro y hy
  have hyH : (⟨y, hy⟩ : ↥L) ∈ H := hHtop ▸ Subgroup.mem_top _
  rwa [hH, Subgroup.mem_subgroupOf] at hyH

theorem exists_rankTwo_of_ne_bot [Finite X] (hp : p.Prime) {L B : Subgroup X}
    (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hB0 : B ⊓ Subgroup.centralizer (L : Set X) ≠ ⊥) (b : ↥B)
    (hb : Inputs2711d.barHom hin b ≠ 1) :
    ∃ U : Subgroup X, ∃ hUB : U ≤ B, 2 ≤ CFSG.Open.pRank p U ∧
      ∀ u : ↥U, Inputs2711d.barHom hin ⟨u, hUB u.2⟩ ∈
        Subgroup.zpowers (Inputs2711d.barHom hin b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB0
  have hzB : (z : X) ∈ B := (Subgroup.mem_inf.1 z.2).1
  have hzC : (z : X) ∈ Subgroup.centralizer (L : Set X) := (Subgroup.mem_inf.1 z.2).2
  have hz1' : (z : X) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hbC : (b : X) ∉ Subgroup.centralizer (L : Set X) := fun h =>
    hb ((Inputs2711d.barHom_eq_one_iff hin b).2 h)
  set U : Subgroup X := Subgroup.zpowers (b : X) ⊔ Subgroup.zpowers (z : X) with hU
  have hUB : U ≤ B := sup_le (Subgroup.zpowers_le.2 b.2) (Subgroup.zpowers_le.2 hzB)
  have hUel : IsElemAbelian p U := isElemAbelian_mono hB hUB
  have hb1 : (b : X) ≠ 1 := fun h => hbC (h ▸ Subgroup.one_mem _)
  have hord : ∀ {w : X}, w ∈ B → w ≠ 1 → Nat.card (Subgroup.zpowers w) = p := fun hw hw1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hB.2 _ hw) hw1
  have hinf : Subgroup.zpowers (b : X) ⊓ Subgroup.zpowers (z : X) = ⊥ := by
    rw [eq_bot_iff]
    intro w ⟨hwb, hwz⟩
    rw [Subgroup.mem_bot]
    by_contra hw1
    have hwB : w ∈ B := Subgroup.zpowers_le.2 b.2 hwb
    have h1 : Subgroup.zpowers w = Subgroup.zpowers (b : X) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwb)
        (by rw [hord b.2 hb1, hord hwB hw1])
    have h3 : Subgroup.zpowers (b : X) ≤ Subgroup.zpowers (z : X) :=
      h1 ▸ Subgroup.zpowers_le.2 hwz
    exact hbC (Subgroup.zpowers_le.2 hzC (h3 (Subgroup.mem_zpowers _)))
  have hcomm : ∀ a ∈ Subgroup.zpowers (b : X), ∀ c ∈ Subgroup.zpowers (z : X), a * c = c * a :=
    fun a ha c hc =>
      isElemAbelian_commute hB (Subgroup.zpowers_le.2 b.2 ha) (Subgroup.zpowers_le.2 hzB hc)
  have hUc : Nat.card U = p ^ 2 := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute _ _ hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, hord b.2 hb1, hord hzB hz1'] at h
    rw [hU, h, sq]
  refine ⟨U, hUB, (Inputs2711d.pRank_eq_two hp hUel hUc).ge, fun u => ?_⟩
  set K : Subgroup X :=
    ((Subgroup.zpowers (Inputs2711d.barHom hin b)).comap (Inputs2711d.barHom hin)).map B.subtype
    with hK
  have hUK : U ≤ K := by
    refine sup_le (Subgroup.zpowers_le.2 ⟨b, Subgroup.mem_zpowers _, rfl⟩)
      (Subgroup.zpowers_le.2 ⟨⟨z, hzB⟩, ?_, rfl⟩)
    rw [SetLike.mem_coe, Subgroup.mem_comap, (Inputs2711d.barHom_eq_one_iff hin ⟨z, hzB⟩).2 hzC]
    exact Subgroup.one_mem _
  obtain ⟨u', hu', hu'u⟩ := hUK u.2
  have : u' = ⟨u, hUB u.2⟩ := Subtype.ext hu'u
  rw [← this]
  exact hu'

theorem eq_gammaTwo_of_conj_rankOne [Finite X] (hp : p.Prime) {L B : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hB0 : B ⊓ Subgroup.centralizer (L : Set X) ≠ ⊥)
    {G : Type} [Group G] [Finite G] (τ₀ : (↥L ⧸ Subgroup.center ↥L) ≃* G) {W : Subgroup G}
    (hconj : ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card W ≤ Nat.card A →
      ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ W)
    (hWc : Nat.card W ≤ Nat.card (Inputs2711d.barHom hin).range) {S : Set G}
    (hS : Subgroup.closure S = ⊤)
    (hSW : ∀ s ∈ S, ∃ f ∈ W, f ≠ 1 ∧ Commute s f ∧ ∃ m, s ^ m = 1 ∧ ¬ p ∣ m) :
    L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X) := by
  set A : Subgroup G := (Inputs2711d.barHom hin).range.map τ₀.toMonoidHom with hA
  have hAel : IsElementaryAbelian p A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2
      (CFSG.SectionRank.isElemAbelian_map (Inputs2711d.isElemAbelian_range_barHom hB hin) _)
  have hAc : Nat.card A = Nat.card (Inputs2711d.barHom hin).range :=
    Subgroup.card_map_of_injective τ₀.injective
  obtain ⟨g, hg⟩ := hconj A hAel (hAc ▸ hWc)
  have hgeq : A.map (MulAut.conj g).toMonoidHom = W := by
    refine Subgroup.eq_of_le_of_card_ge hg ?_
    rw [CFSG.RankThree.Asc83Table.card_map_conj, hAc]
    exact hWc
  set τ : (↥L ⧸ Subgroup.center ↥L) ≃* G := τ₀.trans (MulAut.conj g) with hτdef
  have hτ : (Inputs2711d.barHom hin).range.map τ.toMonoidHom = W := by
    rw [← hgeq, hA, Subgroup.map_map]
    rfl
  refine eq_gammaTwo_of_gen hp hLq hB hin τ hS fun s hs => ?_
  obtain ⟨f, hfW, hf1, hsf, m, hm, hpm⟩ := hSW s hs
  rw [← hτ] at hfW
  obtain ⟨r, ⟨b, rfl⟩, hbr⟩ := hfW
  have hb1 : Inputs2711d.barHom hin b ≠ 1 := by
    intro h
    apply hf1
    rw [← hbr, h, map_one]
  obtain ⟨U, hUB, hU2, hU⟩ := exists_rankTwo_of_ne_bot hp hB hin hB0 b hb1
  refine ⟨U, hUB, hU2, fun u => ?_, m, hm, hpm⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hU u)
  rw [← hn, map_zpow]
  have hτb : τ (Inputs2711d.barHom hin b) = f := hbr
  rw [hτb]
  exact hsf.zpow_right n

theorem exists_rankTwo_of_pair [Finite X] (hp : p.Prime) {L B : Subgroup X}
    (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (b₁ b₂ : ↥B)
    (hb₁ : Inputs2711d.barHom hin b₁ ≠ 1)
    (hb₂ : Inputs2711d.barHom hin b₂ ∉ Subgroup.zpowers (Inputs2711d.barHom hin b₁)) :
    ∃ U : Subgroup X, ∃ hUB : U ≤ B, 2 ≤ CFSG.Open.pRank p U ∧
      ∀ u : ↥U, Inputs2711d.barHom hin ⟨u, hUB u.2⟩ ∈
        Subgroup.zpowers (Inputs2711d.barHom hin b₁) ⊔
          Subgroup.zpowers (Inputs2711d.barHom hin b₂) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hb₁' : (b₁ : X) ≠ 1 := fun h => hb₁ (by rw [show b₁ = 1 from Subtype.ext h, map_one])
  have hb₂' : (b₂ : X) ≠ 1 := fun h => hb₂ (by
    rw [show b₂ = 1 from Subtype.ext h, map_one]; exact Subgroup.one_mem _)
  set U : Subgroup X := Subgroup.zpowers (b₁ : X) ⊔ Subgroup.zpowers (b₂ : X) with hU
  have hUB : U ≤ B := sup_le (Subgroup.zpowers_le.2 b₁.2) (Subgroup.zpowers_le.2 b₂.2)
  have hUel : IsElemAbelian p U := isElemAbelian_mono hB hUB
  have hord : ∀ {w : X}, w ∈ B → w ≠ 1 → Nat.card (Subgroup.zpowers w) = p := fun hw hw1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hB.2 _ hw) hw1
  have hinf : Subgroup.zpowers (b₁ : X) ⊓ Subgroup.zpowers (b₂ : X) = ⊥ := by
    rw [eq_bot_iff]
    intro w ⟨hw₁, hw₂⟩
    rw [Subgroup.mem_bot]
    by_contra hw1
    have hwB : w ∈ B := Subgroup.zpowers_le.2 b₁.2 hw₁
    have h1 : Subgroup.zpowers w = Subgroup.zpowers (b₁ : X) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw₁)
        (by rw [hord b₁.2 hb₁', hord hwB hw1])
    have h2 : Subgroup.zpowers w = Subgroup.zpowers (b₂ : X) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw₂)
        (by rw [hord b₂.2 hb₂', hord hwB hw1])
    have h3 : (b₂ : X) ∈ Subgroup.zpowers (b₁ : X) := by
      rw [← h1, h2]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h3
    apply hb₂
    have hk' : b₁ ^ k = b₂ := Subtype.ext (by simpa using hk)
    rw [← hk', map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  have hcomm : ∀ a ∈ Subgroup.zpowers (b₁ : X), ∀ c ∈ Subgroup.zpowers (b₂ : X),
      a * c = c * a := fun a ha c hc =>
    isElemAbelian_commute hB (Subgroup.zpowers_le.2 b₁.2 ha) (Subgroup.zpowers_le.2 b₂.2 hc)
  have hUc : Nat.card U = p ^ 2 := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute _ _ hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, hord b₁.2 hb₁', hord b₂.2 hb₂'] at h
    rw [hU, h, sq]
  refine ⟨U, hUB, (Inputs2711d.pRank_eq_two hp hUel hUc).ge, fun u => ?_⟩
  set K : Subgroup X :=
    ((Subgroup.zpowers (Inputs2711d.barHom hin b₁) ⊔
      Subgroup.zpowers (Inputs2711d.barHom hin b₂)).comap (Inputs2711d.barHom hin)).map B.subtype
    with hK
  have hUK : U ≤ K := by
    refine sup_le (Subgroup.zpowers_le.2 ⟨b₁, ?_, rfl⟩) (Subgroup.zpowers_le.2 ⟨b₂, ?_, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨u', hu', hu'u⟩ := hUK u.2
  have : u' = ⟨u, hUB u.2⟩ := Subtype.ext hu'u
  rw [← this]
  exact hu'

theorem commute_of_mem_sup_zpowers {G : Type*} [Group G] {s f₁ f₂ : G} (h₁ : Commute s f₁)
    (h₂ : Commute s f₂) {y : G} (hy : y ∈ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) :
    Commute s y := by
  have hle : Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ≤
      Subgroup.centralizer ({s} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 h₁.eq.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 h₂.eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem eq_gammaTwo_of_two_lines [Finite X] (hp : p.Prime) {L B : Subgroup X}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hB4 : 4 ≤ CFSG.Open.pRank p B)
    (hC1 : CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1)
    {G : Type} [Group G] [Finite G] (τ₀ : (↥L ⧸ Subgroup.center ↥L) ≃* G) {T : Subgroup G}
    (hT4 : Nat.card T = p ^ 4)
    (hconj : ∀ A : Subgroup G, IsPGroup p A → ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ T)
    {S : Set G} (hS : Subgroup.closure S = ⊤)
    (hSl : ∀ s ∈ S, ∃ f₁ ∈ T, ∃ f₂ ∈ T, f₁ ^ p = 1 ∧ f₂ ^ p = 1 ∧ Commute f₁ f₂ ∧ f₁ ≠ 1 ∧
      f₂ ∉ Subgroup.zpowers f₁ ∧ Commute s f₁ ∧ Commute s f₂ ∧ ∃ m, s ^ m = 1 ∧ ¬ p ∣ m) :
    L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set R := (Inputs2711d.barHom hin).range with hRdef
  have hRel : IsElemAbelian p R := Inputs2711d.isElemAbelian_range_barHom hB hin
  set A : Subgroup G := R.map τ₀.toMonoidHom with hA
  have hAel : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hRel _
  obtain ⟨g, hg⟩ := hconj A (CFSG.Open.IsElemAbelian.isPGroup hAel)
  set τ : (↥L ⧸ Subgroup.center ↥L) ≃* G := τ₀.trans (MulAut.conj g) with hτdef
  have hτ : R.map τ.toMonoidHom = A.map (MulAut.conj g).toMonoidHom := by
    rw [hA, Subgroup.map_map]
    rfl
  set W : Subgroup G := R.map τ.toMonoidHom with hW
  have hWT : W ≤ T := by
    rw [hτ]
    exact hg
  have hWc : Nat.card W = Nat.card R := Subgroup.card_map_of_injective τ.injective
  have hRB := Inputs2711d.card_range_barHom_mul hin
  have hBc : p ^ 4 ≤ Nat.card B := by
    rw [Inputs27.card_eq_pow_pRank hp hB]
    exact Nat.pow_le_pow_right hp.pos hB4
  have hB₀el : IsElemAbelian p (B ⊓ Subgroup.centralizer (L : Set X)) :=
    isElemAbelian_mono hB inf_le_left
  refine eq_gammaTwo_of_gen hp hLq hB hin τ hS fun s hs => ?_
  obtain ⟨f₁, hf₁T, f₂, hf₂T, hf₁p, hf₂p, hf₁₂, hf₁, hf₂, hs₁, hs₂, m, hm, hpm⟩ := hSl s hs
  by_cases hB0 : B ⊓ Subgroup.centralizer (L : Set X) = ⊥
  ·
    have hRc : Nat.card R = Nat.card B := by
      rw [hB0, Subgroup.card_bot, mul_one] at hRB
      exact hRB
    have hWeq : W = T := Subgroup.eq_of_le_of_card_ge hWT (by rw [hWc, hRc, hT4]; exact hBc)
    have h₁ : f₁ ∈ W := hWeq ▸ hf₁T
    have h₂ : f₂ ∈ W := hWeq ▸ hf₂T
    obtain ⟨r₁, ⟨b₁, rfl⟩, hb₁⟩ := h₁
    obtain ⟨r₂, ⟨b₂, rfl⟩, hb₂⟩ := h₂
    have hτ₁ : τ (Inputs2711d.barHom hin b₁) = f₁ := hb₁
    have hτ₂ : τ (Inputs2711d.barHom hin b₂) = f₂ := hb₂
    have hb₁1 : Inputs2711d.barHom hin b₁ ≠ 1 := fun h => hf₁ (by rw [← hτ₁, h, map_one])
    have hb₂z : Inputs2711d.barHom hin b₂ ∉ Subgroup.zpowers (Inputs2711d.barHom hin b₁) := by
      intro h
      apply hf₂
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      rw [← hτ₂, ← hk, map_zpow, hτ₁]
      exact Subgroup.zpow_mem_zpowers _ k
    obtain ⟨U, hUB, hU2, hU⟩ := exists_rankTwo_of_pair hp hB hin b₁ b₂ hb₁1 hb₂z
    refine ⟨U, hUB, hU2, fun u => ?_, m, hm, hpm⟩
    have hmem := Subgroup.mem_map_of_mem τ.toMonoidHom (hU u)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmem
    exact commute_of_mem_sup_zpowers (hτ₁ ▸ hs₁) (hτ₂ ▸ hs₂) hmem
  ·
    have hB₀c : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = p := by
      have h1 := Inputs27.card_eq_pow_pRank hp hB₀el
      have h2 : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) ≠ 1 := fun h =>
        hB0 (Subgroup.card_eq_one.1 h)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hC1 with h | h
      · rw [h1, h, pow_zero] at h2
        exact absurd rfl h2
      · rw [h1, h, pow_one]
    have hR3 : p ^ 3 ≤ Nat.card R := by
      rw [hB₀c] at hRB
      have : p ^ 3 * p ≤ Nat.card R * p := by
        rw [hRB, ← pow_succ]
        exact hBc
      exact Nat.le_of_mul_le_mul_right this hp.pos
    set ℓ : Subgroup G := Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ with hℓ
    have hℓT : ℓ ≤ T := sup_le (Subgroup.zpowers_le.2 hf₁T) (Subgroup.zpowers_le.2 hf₂T)
    have hf₂1 : f₂ ≠ 1 := fun h => hf₂ (h ▸ Subgroup.one_mem _)
    have hord₁ : Nat.card (Subgroup.zpowers f₁) = p := by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime hf₁p hf₁
    have hord₂ : Nat.card (Subgroup.zpowers f₂) = p := by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime hf₂p hf₂1
    have hinf : Subgroup.zpowers f₁ ⊓ Subgroup.zpowers f₂ = ⊥ := by
      rw [eq_bot_iff]
      intro w ⟨hw₁, hw₂⟩
      rw [Subgroup.mem_bot]
      by_contra hw1
      have hwp : w ^ p = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw₁
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf₁p, one_zpow]
      have hw : Nat.card (Subgroup.zpowers w) = p := by
        rw [Nat.card_zpowers]; exact orderOf_eq_prime hwp hw1
      have h1 : Subgroup.zpowers w = Subgroup.zpowers f₁ :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw₁) (by rw [hord₁, hw])
      have h2 : Subgroup.zpowers w = Subgroup.zpowers f₂ :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw₂) (by rw [hord₂, hw])
      exact hf₂ (by rw [← h1, h2]; exact Subgroup.mem_zpowers _)
    have hℓc : Nat.card ℓ = p ^ 2 := by
      have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (Subgroup.zpowers f₁)
          (Subgroup.zpowers f₂) fun a ha c hc => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
        exact (hf₁₂.zpow_zpow i j).eq).1
      rw [hinf, Subgroup.card_bot, mul_one, hord₁, hord₂] at h
      rw [hℓ, h, sq]
    have hWℓ : W ⊓ ℓ ≠ ⊥ := by
      intro h0
      have e1 := Subgroup.relIndex_mul_card (H := W) (K := T)
      have e2 := Subgroup.relIndex_mul_card (H := ℓ) (K := T)
      have e3 := Subgroup.relIndex_mul_card (H := W ⊓ ℓ) (K := T)
      have hle := Subgroup.relIndex_inf_le (H := W) (K := ℓ) (L := T)
      rw [inf_eq_left.2 hWT, hWc] at e1
      rw [inf_eq_left.2 hℓT, hℓc] at e2
      have hc0 : Nat.card ↥(W ⊓ ℓ) = 1 := by rw [h0, Subgroup.card_bot]
      rw [inf_eq_left.2 (inf_le_left.trans hWT), hc0, mul_one, hT4] at e3
      rw [hT4] at e1 e2
      have hx : W.relIndex T ≤ p := by
        have : W.relIndex T * p ^ 3 ≤ p * p ^ 3 := by
          calc W.relIndex T * p ^ 3 ≤ W.relIndex T * Nat.card R := Nat.mul_le_mul_left _ hR3
            _ = p ^ 4 := e1
            _ = p * p ^ 3 := by ring
        exact Nat.le_of_mul_le_mul_right this (pow_pos hp.pos 3)
      have hy : ℓ.relIndex T = p ^ 2 := by
        have : ℓ.relIndex T * p ^ 2 = p ^ 2 * p ^ 2 := by rw [e2]; ring
        exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) this
      have : p ^ 4 ≤ p ^ 3 := by
        calc p ^ 4 = (W ⊓ ℓ).relIndex T := e3.symm
          _ ≤ W.relIndex T * ℓ.relIndex T := hle
          _ ≤ p * p ^ 2 := by rw [hy]; exact Nat.mul_le_mul_right _ hx
          _ = p ^ 3 := by ring
      exact absurd ((Nat.pow_le_pow_iff_right hp.one_lt).1 this) (by norm_num)
    obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hWℓ
    have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
    obtain ⟨r, ⟨b, rfl⟩, hbr⟩ := (Subgroup.mem_inf.1 hf).1
    have hτb : τ (Inputs2711d.barHom hin b) = f := hbr
    have hb1 : Inputs2711d.barHom hin b ≠ 1 := fun h => hf1' (by rw [← hτb, h, map_one])
    obtain ⟨U, hUB, hU2, hU⟩ := exists_rankTwo_of_ne_bot hp hB hin hB0 b hb1
    refine ⟨U, hUB, hU2, fun u => ?_, m, hm, hpm⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hU u)
    rw [← hn, map_zpow, hτb]
    exact (commute_of_mem_sup_zpowers hs₁ hs₂ (Subgroup.mem_inf.1 hf).2).zpow_right n

end Gamma

section Sound

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {p : ℕ} {sA sB : String} {D : GenData}

theorem genCheck_sound (h : genCheck O p sA sB D = true) :
    ∃ hC : mcertCheck O sA sB D.mcert = true,
      Subgroup.closure {u | ∃ g ∈ D.gens, u = regUnit Sp hC g.reg} = ⊤ ∧
      ∀ g ∈ D.gens, (∀ f ∈ g.fixes, Commute (regUnit Sp hC g.reg) (regUnit Sp hC f)) ∧
        regUnit Sp hC g.reg ^ g.ord = 1 ∧ ¬ p ∣ g.ord := by
  unfold genCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hC, hA⟩, hB⟩, hgens⟩, hder⟩, hw⟩ := h
  have hfacts : D.mcert.facts = D.facts := rfl
  have hgf : ∀ g ∈ D.gens, ∀ f ∈ GenItem.facts g, f ∈ D.mcert.facts := by
    intro g hg f hf
    simp only [hfacts, GenData.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨g, hg, hf⟩))
  have hgord : ∀ g ∈ D.gens, MFact.ord g.reg g.ord ∈ D.mcert.facts := fun g hg =>
    hgf g hg _ (by simp [GenItem.facts])
  refine ⟨hC, ?_, ?_⟩
  · have fordA : MFact.ord 0 D.oA ∈ D.mcert.facts := by simp [hfacts, GenData.facts]
    have fordB : MFact.ord 1 D.oB ∈ D.mcert.facts := by simp [hfacts, GenData.facts]
    have feA : MFact.eq [(0, 1)] D.wA ∈ D.mcert.facts := by simp [hfacts, GenData.facts]
    have feB : MFact.eq [(1, 1)] D.wB ∈ D.mcert.facts := by simp [hfacts, GenData.facts]
    set S := {u | ∃ g ∈ D.gens, u = regUnit Sp hC g.reg} with hSdef
    have hav : ∀ r ∈ D.gens.map (·.reg), regUnit Sp hC r ∈ Subgroup.closure S ∧
        ∃ e, MFact.ord r e ∈ D.mcert.facts := by
      intro r hr
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
      exact ⟨Subgroup.subset_closure ⟨g, hg, rfl⟩, g.ord, hgord g hg⟩
    have hderf : ∀ e ∈ D.der, ∀ f ∈ e.facts, f ∈ D.mcert.facts := by
      intro e he f hf
      simp only [hfacts, GenData.facts, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨e, he, hf⟩)
    have hderG := CFSG.AGLEmbedding.R3.der_mem Sp hC (Subgroup.closure S) D.der _ hderf hav hder
    have hletter : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC q.1 ∈ Subgroup.closure S ∧
        ∃ e, MFact.ord q.1 e ∈ D.mcert.facts := by
      intro q hq
      have hq' := List.all_eq_true.1 hw q hq
      rw [Bool.or_eq_true] at hq'
      rcases hq' with hq' | hq'
      · obtain ⟨g, hg, hgq⟩ := List.any_eq_true.1 hq'
        simp only [beq_iff_eq] at hgq
        rw [← hgq]
        exact ⟨Subgroup.subset_closure ⟨g, hg, rfl⟩, g.ord, hgord g hg⟩
      · obtain ⟨e, he, heq⟩ := List.any_eq_true.1 hq'
        simp only [beq_iff_eq] at heq
        rw [← heq]
        exact hderG e he
    have hA0 : 0 < D.mcert.nregs := (reg_pow Sp hC fordA).1
    have hB1 : 1 < D.mcert.nregs := (reg_pow Sp hC fordB).1
    have hvalA : valHom (certMonoid c d sA sB) (regUnit Sp hC 0) =
        NativeSporadic.decode c d 1 sA := by
      rw [val_regUnit Sp hC fordA, Sp.toMat_eq (reg_ok Sp hC hA0).1 (Sp.decode_wf sA) hA,
        Sp.toMat_decode]
    have hvalB : valHom (certMonoid c d sA sB) (regUnit Sp hC 1) =
        NativeSporadic.decode c d 1 sB := by
      rw [val_regUnit Sp hC fordB, Sp.toMat_eq (reg_ok Sp hC hB1).1 (Sp.decode_wf sB) hB,
        Sp.toMat_decode]
    have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top
      (certMonoid c d sA sB) rfl (regUnit Sp hC 0) (regUnit Sp hC 1) hvalA hvalB
    have hAw : regUnit Sp hC 0 = wordUnit Sp hC D.wA := by
      have := regUnit_eq Sp hC feA (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oA, fordA⟩)
        (fun q hq => (hletter q (List.mem_append.2 (Or.inl hq))).2)
      simpa [wordUnit] using this
    have hBw : regUnit Sp hC 1 = wordUnit Sp hC D.wB := by
      have := regUnit_eq Sp hC feB (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oB, fordB⟩)
        (fun q hq => (hletter q (List.mem_append.2 (Or.inr hq))).2)
      simpa [wordUnit] using this
    refine eq_top_iff.mpr ?_
    rw [← htop, Subgroup.closure_le]
    rintro u (rfl | rfl)
    · rw [hAw]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC _ D.wA fun q hq =>
        (hletter q (List.mem_append.2 (Or.inl hq))).1
    · rw [hBw]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC _ D.wB fun q hq =>
        (hletter q (List.mem_append.2 (Or.inr hq))).1
  · intro g hg
    have hord : MFact.ord g.reg g.ord ∈ D.mcert.facts := hgord g hg
    have hg' := List.all_eq_true.1 hgens g hg
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg'
    obtain ⟨hmod, hfix⟩ := hg'
    refine ⟨fun f hf => ?_, regUnit_pow Sp hC hord, fun hdvd => hmod (Nat.mod_eq_zero_of_dvd hdvd)⟩
    have hconj : MFact.conj g.reg [(f, 1)] [(f, 1)] ∈ D.mcert.facts :=
      hgf g hg _ (by simp [GenItem.facts, hf])
    obtain ⟨q, hq, hqf⟩ := List.any_eq_true.1 (List.all_eq_true.1 hfix f hf)
    simp only [beq_iff_eq] at hqf
    have hfo : MFact.ord f q.2 ∈ D.mcert.facts := by
      simp only [hfacts, GenData.facts, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, by rw [hqf]⟩)))
    have hu : HasOrd D.mcert [(f, 1)] := fun a ha => by
      simp only [List.mem_singleton] at ha; subst ha; exact ⟨q.2, hfo⟩
    have := regUnit_conj Sp hC hconj hord hu hu
    rw [wordUnit_one] at this
    exact mul_inv_eq_iff_eq_mul.1 this

end Sound

section PairJ3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

theorem phi_regUnit_eq_basisProd
    {hC : mcertCheck (ops2fr 80) NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 j3GenData.mcert =
      true} {r e : ℕ} (hord : MFact.ord r e ∈ j3GenData.mcert.facts) (a : Fin 3 → ZMod 3)
    {k : ℕ} (hk : J3.code a = k)
    (heq : (ops2fr 80).eq
      ((ops2fr 80).regsOf NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 j3GenData.nregs
        j3GenData.prog)[r]!
      (evalW (ops2fr 80)
        ((ops2fr 80).regsOf NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 J3.j3Cert.nregs
          J3.j3Cert.prog)
        (basisW J3.j3Cert.rb k)) = true) :
    J3.φ (regUnit (spec2fr 80) hC r) = basisProd J3.x a := by
  subst hk
  have hb : basisProd J3.x a = J3.XW J3.j3_check (basisW J3.j3Cert.rb (J3.code a)) :=
    J3.basisProd_eq J3.j3_check a
  rw [hb]
  apply Subtype.ext
  apply Units.ext
  rw [J3.coe_φ, J3.matrix_XW J3.j3_check (J3.hasOrd_basisW J3.hrb _)]
  have h1 : (regUnit (spec2fr 80) hC r).val.val =
      valHom (certMonoid 2 80 NativeSporadic.J3Seed1 NativeSporadic.J3Seed2)
        (regUnit (spec2fr 80) hC r) := rfl
  rw [h1, val_regUnit (spec2fr 80) hC hord]
  exact (spec2fr 80).toMat_eq (reg_ok (spec2fr 80) hC (reg_pow (spec2fr 80) hC hord).1).1
    (J3.wf_evalW J3.j3_check (J3.hasOrd_basisW J3.hrb _)) heq

theorem j3GenData_ord_fix {r : ℕ} (hr : r = 4 ∨ r = 5) : MFact.ord r 3 ∈ j3GenData.mcert.facts := by
  have hfix : j3GenData.fixOrd = [(4, 3), (5, 3)] := rfl
  have hfacts : j3GenData.mcert.facts = GenData.facts j3GenData := rfl
  rw [hfacts, GenData.facts, hfix]
  rcases hr with rfl | rfl <;> simp

theorem j3_gen_set :
    ∃ S : Set (CFSG.Sporadic.J3.J J3.D), Subgroup.closure S = ⊤ ∧
      ∀ s ∈ S, ∃ f ∈ Subgroup.closure (Set.range J3.x), f ≠ 1 ∧ Commute s f ∧
        ∃ m, s ^ m = 1 ∧ ¬ 3 ∣ m := by
  have h : j3GenCheck = true := Certificates.certificate271101
  unfold j3GenCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hgen, hcross⟩ := h
  obtain ⟨hC, hclos, hgens⟩ := genCheck_sound (spec2fr 80) hgen
  unfold j3GenCross at hcross
  rw [Bool.and_eq_true] at hcross
  obtain ⟨h4, h5⟩ := hcross
  have hf4 : J3.φ (regUnit (spec2fr 80) hC 4) = basisProd J3.x ![0, 0, 1] :=
    phi_regUnit_eq_basisProd (j3GenData_ord_fix (Or.inl rfl)) ![0, 0, 1] (k := 9) (by decide) h4
  have hf5 : J3.φ (regUnit (spec2fr 80) hC 5) = basisProd J3.x ![1, 0, 1] :=
    phi_regUnit_eq_basisProd (j3GenData_ord_fix (Or.inr rfl)) ![1, 0, 1] (k := 10) (by decide) h5
  have hmem : ∀ a : Fin 3 → ZMod 3, a ≠ 0 →
      basisProd J3.x a ∈ Subgroup.closure (Set.range J3.x) ∧ basisProd J3.x a ≠ 1 :=
    fun a ha => ⟨basisProd_mem J3.x_pow J3.x_comm a, J3.basisProd_ne_one J3.j3_check J3.hrb ha⟩
  refine ⟨(J3.φ : NativeSporadic.J3 →* CFSG.Sporadic.J3.J J3.D) ''
    {u | ∃ g ∈ j3GenData.gens, u = regUnit (spec2fr 80) hC g.reg}, ?_, ?_⟩
  · have h1 := MonoidHom.map_closure (J3.φ : NativeSporadic.J3 →* CFSG.Sporadic.J3.J J3.D)
      {u | ∃ g ∈ j3GenData.gens, u = regUnit (spec2fr 80) hC g.reg}
    have hsurj : Function.Surjective (J3.φ : NativeSporadic.J3 →* CFSG.Sporadic.J3.J J3.D) := by
      exact J3.φ.surjective
    rw [hclos, Subgroup.map_top_of_surjective _ hsurj] at h1
    exact h1.symm
  · rintro _ ⟨u, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨hcomm, hpow, hndvd⟩ := hgens g hg
    have hpow' : J3.φ (regUnit (spec2fr 80) hC g.reg) ^ g.ord = 1 := by
      rw [← map_pow, hpow, map_one]
    have hgl : j3GenData.gens = [⟨6, 5, [4]⟩, ⟨7, 4, [4]⟩, ⟨8, 4, [5]⟩, ⟨9, 5, [5]⟩] := rfl
    rw [hgl] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    show ∃ f ∈ Subgroup.closure (Set.range J3.x), f ≠ 1 ∧
      Commute (J3.φ (regUnit (spec2fr 80) hC g.reg)) f ∧ ∃ m, _ ^ m = 1 ∧ ¬ 3 ∣ m
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨_, (hmem ![0, 0, 1] (by decide)).1, (hmem ![0, 0, 1] (by decide)).2,
        hf4 ▸ (hcomm 4 (by simp)).map J3.φ, _, hpow', hndvd⟩
    · exact ⟨_, (hmem ![0, 0, 1] (by decide)).1, (hmem ![0, 0, 1] (by decide)).2,
        hf4 ▸ (hcomm 4 (by simp)).map J3.φ, _, hpow', hndvd⟩
    · exact ⟨_, (hmem ![1, 0, 1] (by decide)).1, (hmem ![1, 0, 1] (by decide)).2,
        hf5 ▸ (hcomm 5 (by simp)).map J3.φ, _, hpow', hndvd⟩
    · exact ⟨_, (hmem ![1, 0, 1] (by decide)).1, (hmem ![1, 0, 1] (by decide)).2,
        hf5 ▸ (hcomm 5 (by simp)).map J3.φ, _, hpow', hndvd⟩

theorem sporPairCase_J3_three_of_ne_bot
    (hBr : SporadicBridges) :
    Inputs2711d.SporPairCaseWith .J3 3
      fun X _ L B => ¬ B ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
  intro X _ _ hp _ L B hB0 _ hLq hB _ _ hrk4 _ _ _ hC1 hname hin _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨σ⟩ := hname
  obtain ⟨β⟩ := hBr .J3
  have hB₀el : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (L : Set X)) :=
    isElemAbelian_mono hB inf_le_left
  have hB₀c : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = 3 := by
    have h1 := Inputs27.card_eq_pow_pRank hp hB₀el
    have h2 : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) ≠ 1 := fun h =>
      hB0 (Subgroup.card_eq_one.1 h)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hC1 with h | h
    · rw [h1, h, pow_zero] at h2
      exact absurd rfl h2
    · rw [h1, h, pow_one]
  have hBc : 81 ≤ Nat.card B := by
    rw [Inputs27.card_eq_pow_pRank hp hB]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hrk4
  have hR := Inputs2711d.card_range_barHom_mul hin
  rw [hB₀c] at hR
  have hR27 : 27 ≤ Nat.card (Inputs2711d.barHom hin).range := by omega
  haveI : Finite (CFSG.Sporadic.J3.J J3.D) := Finite.of_equiv _ J3.φ.toEquiv
  obtain ⟨S, hS, hSf⟩ := j3_gen_set
  refine eq_gammaTwo_of_conj_rankOne (G := CFSG.Sporadic.J3.J J3.D)
    (W := Subgroup.closure (Set.range J3.x)) (S := S) hp hLq hB hin hB0 ?_ ?_ ?_ ?_ ?_
  · exact (σ.trans β.symm).trans J3.φ
  · exact fun A hA _ => exists_conj_le_basis J3.x_pow J3.x_comm J3.x_inj J3.h_conj
      J3.card_normalizer J3.omega_basis J3.factorization_card hA
  · rw [card_basis J3.x_pow J3.x_comm J3.x_inj]
    exact hR27
  · exact hS
  · exact hSf

end PairJ3

section PairON

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

theorem isElemAbelian_closure_of_basis {G : Type*} [Group G] {n : ℕ} {x : Fin n → G}
    (hx : ∀ i, x i ^ 3 = 1) (hc : ∀ i j, Commute (x i) (x j)) :
    IsElemAbelian 3 (Subgroup.closure (Set.range x)) := by
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range x)) :=
    Subgroup.isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  have hab : ∀ a ∈ Subgroup.closure (Set.range x), ∀ b ∈ Subgroup.closure (Set.range x),
      a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure (Set.range x)) ⟨b, hb⟩)
  refine ⟨hcomm, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    exact hx i
  | one => exact one_pow 3
  | mul a b ha hb h₁ h₂ => rw [(show Commute a b from hab a ha b hb).mul_pow, h₁, h₂, one_mul]
  | inv a _ h => rw [inv_pow, h, inv_one]

theorem basisProd_injective_of_ne_one {G : Type*} [Group G] {n : ℕ} {x : Fin n → G}
    (hx : ∀ i, x i ^ 3 = 1) (hc : ∀ i j, Commute (x i) (x j))
    (hne : ∀ a : Fin n → ZMod 3, a ≠ 0 → basisProd x a ≠ 1) :
    Function.Injective (basisProd x) := by
  intro a b hab
  have h1 : basisHom hx hc (Multiplicative.ofAdd a) = basisHom hx hc (Multiplicative.ofAdd b) :=
    Subtype.ext (by rw [coe_basisHom, coe_basisHom]; exact hab)
  have h2 : basisHom hx hc (Multiplicative.ofAdd (a - b)) = 1 := by
    rw [ofAdd_sub, map_div, h1, div_self']
  have h3 : basisProd x (a - b) = 1 := by
    have := congrArg Subtype.val h2
    rwa [coe_basisHom, toAdd_ofAdd] at this
  by_contra h
  exact hne _ (sub_ne_zero.2 h) h3

@[expose] def onBasisCode (a : Fin 4 → ZMod 3) : ℕ :=
  (a 0).val + 3 * (a 1).val + 9 * (a 2).val + 27 * (a 3).val

theorem onBasisW_onBasisCode (a : Fin 4 → ZMod 3) :
    onBasisW (onBasisCode a) =
      [(4, (a 0).val), (5, (a 1).val), (6, (a 2).val), (7, (a 3).val)] := by
  have h0 := (a 0).val_lt
  have h1 := (a 1).val_lt
  have h2 := (a 2).val_lt
  have h3 := (a 3).val_lt
  have e0 : onBasisCode a % 3 = (a 0).val := by unfold onBasisCode; omega
  have e1 : onBasisCode a / 3 % 3 = (a 1).val := by unfold onBasisCode; omega
  have e2 : onBasisCode a / 9 % 3 = (a 2).val := by unfold onBasisCode; omega
  have e3 : onBasisCode a / 27 % 3 = (a 3).val := by unfold onBasisCode; omega
  rw [onBasisW, e0, e1, e2, e3]

theorem onBasisCode_pos {a : Fin 4 → ZMod 3} (ha : a ≠ 0) : 0 < onBasisCode a := by
  by_contra h
  apply ha
  have h' : onBasisCode a = 0 := by omega
  unfold onBasisCode at h'
  funext i
  have h0 : (a 0).val = 0 := by omega
  have h1 : (a 1).val = 0 := by omega
  have h2 : (a 2).val = 0 := by omega
  have h3 : (a 3).val = 0 := by omega
  fin_cases i
  · exact (ZMod.val_eq_zero _).1 h0
  · exact (ZMod.val_eq_zero _).1 h1
  · exact (ZMod.val_eq_zero _).1 h2
  · exact (ZMod.val_eq_zero _).1 h3

theorem onBasisCode_lt (a : Fin 4 → ZMod 3) : onBasisCode a < 81 := by
  have h0 := (a 0).val_lt
  have h1 := (a 1).val_lt
  have h2 := (a 2).val_lt
  have h3 := (a 3).val_lt
  unfold onBasisCode
  omega

theorem mem_zpowers_of_pow_three {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  classical
  have hord : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hx⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hord] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  interval_cases k
  · exact Or.inl (pow_zero x)
  · exact Or.inr (Or.inl (pow_one x))
  · exact Or.inr (Or.inr rfl)

theorem on_gen_set :
    ∃ (T : Subgroup NativeSporadic.ON) (S : Set NativeSporadic.ON), IsElemAbelian 3 T ∧
      Nat.card T = 3 ^ 4 ∧ Subgroup.closure S = ⊤ ∧
      ∀ s ∈ S, ∃ f₁ ∈ T, ∃ f₂ ∈ T, f₁ ≠ 1 ∧ f₂ ∉ Subgroup.zpowers f₁ ∧ Commute s f₁ ∧
        Commute s f₂ ∧ ∃ m, s ^ m = 1 ∧ ¬ 3 ∣ m := by
  have h : onGenCheck = true := Certificates.certificate271102
  unfold onGenCheck at h
  obtain ⟨hC, hclos, hgens⟩ := genCheck_sound (spec3 154) h
  have hex : ∀ f ∈ onGenExtra, f ∈ onGenData.mcert.facts := fun f hf =>
    List.mem_append_right _ hf
  have hhead : ∀ f ∈ ([.ord 4 3, .ord 5 3, .ord 6 3, .ord 7 3,
      .eq [(4, 1), (5, 1)] [(5, 1), (4, 1)], .eq [(4, 1), (6, 1)] [(6, 1), (4, 1)],
      .eq [(4, 1), (7, 1)] [(7, 1), (4, 1)], .eq [(5, 1), (6, 1)] [(6, 1), (5, 1)],
      .eq [(5, 1), (7, 1)] [(7, 1), (5, 1)], .eq [(6, 1), (7, 1)] [(7, 1), (6, 1)],
      .eq [(12, 1)] [(4, 2), (5, 1), (6, 1), (7, 0)],
      .eq [(16, 1)] [(4, 1), (5, 1), (6, 1), (7, 2)],
      .eq [(21, 1)] [(4, 2), (5, 0), (6, 1), (7, 1)],
      .eq [(25, 1)] [(4, 0), (5, 0), (6, 0), (7, 1)],
      .ne [(12, 1)] [] 0, .ne [(16, 1)] [] 0, .ne [(16, 1)] [(12, 1)] 0, .ne [(16, 1)] [(12, 2)] 0,
      .ne [(21, 1)] [] 0, .ne [(25, 1)] [] 0, .ne [(25, 1)] [(21, 1)] 0,
      .ne [(25, 1)] [(21, 2)] 0] : List MFact), f ∈ onGenData.mcert.facts :=
    fun f hf => hex f (List.mem_append_left _ hf)
  have hfixo : ∀ r ∈ [12, 16, 21, 25], MFact.ord r 3 ∈ onGenData.mcert.facts := by
    intro r hr
    have hfix : onGenData.fixOrd = [(12, 3), (16, 3), (21, 3), (25, 3)] := rfl
    have hmem : MFact.ord r 3 ∈ onGenData.fixOrd.map (fun q => MFact.ord q.1 q.2) := by
      rw [hfix]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hmem)))
  have hord : ∀ r ∈ [4, 5, 6, 7, 12, 16, 21, 25], MFact.ord r 3 ∈ onGenData.mcert.facts := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hhead _ (by simp)
    · exact hhead _ (by simp)
    · exact hhead _ (by simp)
    · exact hhead _ (by simp)
    · exact hfixo _ (by simp)
    · exact hfixo _ (by simp)
    · exact hfixo _ (by simp)
    · exact hfixo _ (by simp)
  have hHO : ∀ w : Word, (∀ q ∈ w, q.1 ∈ [4, 5, 6, 7, 12, 16, 21, 25]) →
      HasOrd onGenData.mcert w := fun w hw q hq => ⟨3, hord _ (hw q hq)⟩
  have hHO1 : ∀ r ∈ [4, 5, 6, 7, 12, 16, 21, 25], HasOrd onGenData.mcert [(r, 1)] := by
    intro r hr
    refine hHO _ fun q hq => ?_
    rw [List.mem_singleton] at hq
    rw [hq]
    exact hr
  have hHO2 : ∀ r s : ℕ, r ∈ [4, 5, 6, 7, 12, 16, 21, 25] → s ∈ [4, 5, 6, 7, 12, 16, 21, 25] →
      HasOrd onGenData.mcert [(r, 1), (s, 1)] := by
    intro r s hr hs
    refine hHO _ fun q hq => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hr
    · exact hs
  have hcomm4 : ∀ r s : ℕ, MFact.eq [(r, 1), (s, 1)] [(s, 1), (r, 1)] ∈ onGenData.mcert.facts →
      r ∈ [4, 5, 6, 7, 12, 16, 21, 25] → s ∈ [4, 5, 6, 7, 12, 16, 21, 25] →
      Commute (regUnit (spec3 154) hC r) (regUnit (spec3 154) hC s) :=
    fun r s hf hr hs => regUnit_comm' (spec3 154) hC hf (hHO2 r s hr hs) (hHO2 s r hs hr)
  set t : Fin 4 → NativeSporadic.ON := ![regUnit (spec3 154) hC 4, regUnit (spec3 154) hC 5,
    regUnit (spec3 154) hC 6, regUnit (spec3 154) hC 7] with ht
  have hx : ∀ i, t i ^ 3 = 1 := by
    intro i
    fin_cases i
    · exact regUnit_pow (spec3 154) hC (hord 4 (by simp))
    · exact regUnit_pow (spec3 154) hC (hord 5 (by simp))
    · exact regUnit_pow (spec3 154) hC (hord 6 (by simp))
    · exact regUnit_pow (spec3 154) hC (hord 7 (by simp))
  have hc01 : Commute (t 0) (t 1) := hcomm4 4 5 (hhead _ (by simp)) (by simp) (by simp)
  have hc02 : Commute (t 0) (t 2) := hcomm4 4 6 (hhead _ (by simp)) (by simp) (by simp)
  have hc03 : Commute (t 0) (t 3) := hcomm4 4 7 (hhead _ (by simp)) (by simp) (by simp)
  have hc12 : Commute (t 1) (t 2) := hcomm4 5 6 (hhead _ (by simp)) (by simp) (by simp)
  have hc13 : Commute (t 1) (t 3) := hcomm4 5 7 (hhead _ (by simp)) (by simp) (by simp)
  have hc23 : Commute (t 2) (t 3) := hcomm4 6 7 (hhead _ (by simp)) (by simp) (by simp)
  have hc : ∀ i j, Commute (t i) (t j) := by
    intro i j
    fin_cases i <;> fin_cases j
    exacts [Commute.refl _, hc01, hc02, hc03, hc01.symm, Commute.refl _, hc12, hc13, hc02.symm,
      hc12.symm, Commute.refl _, hc23, hc03.symm, hc13.symm, hc23.symm, Commute.refl _]
  have hwb : ∀ a : Fin 4 → ZMod 3,
      basisProd t a = wordUnit (spec3 154) hC (onBasisW (onBasisCode a)) := by
    intro a
    rw [onBasisW_onBasisCode]
    simp [basisProd, wordUnit, List.ofFn_succ, t]
  have hne : ∀ a : Fin 4 → ZMod 3, a ≠ 0 → basisProd t a ≠ 1 := by
    intro a ha
    have hk := onBasisCode_pos ha
    have hk' := onBasisCode_lt a
    have hf : MFact.ne (onBasisW (onBasisCode a)) [] 0 ∈ onGenData.mcert.facts := by
      refine hex _ (List.mem_append_right _ (List.mem_map.2 ⟨onBasisCode a - 1, ?_, ?_⟩))
      · exact List.mem_range.2 (by omega)
      · rw [show onBasisCode a - 1 + 1 = onBasisCode a by omega]
    have hw : HasOrd onGenData.mcert (onBasisW (onBasisCode a)) := by
      rw [onBasisW_onBasisCode]
      refine hHO _ fun q hq => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp
    have h1 := regUnit_ne (spec3 154) hC hf hw (hasOrd_nil _)
    rw [wordUnit_nil] at h1
    rw [hwb]
    exact h1
  have hinj : Function.Injective (basisProd t) := basisProd_injective_of_ne_one hx hc hne
  set T : Subgroup NativeSporadic.ON := Subgroup.closure (Set.range t) with hT
  have hTc : Nat.card T = 3 ^ 4 := card_closure_basis hx hc hinj
  have hTel : IsElemAbelian 3 T := isElemAbelian_closure_of_basis hx hc
  have hu4 : ∀ r ∈ [4, 5, 6, 7], regUnit (spec3 154) hC r ∈ T := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
    · exact Subgroup.subset_closure ⟨2, rfl⟩
    · exact Subgroup.subset_closure ⟨3, rfl⟩
  have hline : ∀ r : ℕ, ∀ w : Word, MFact.eq [(r, 1)] w ∈ onGenData.mcert.facts →
      r ∈ [4, 5, 6, 7, 12, 16, 21, 25] → (∀ q ∈ w, q.1 ∈ [4, 5, 6, 7]) →
      regUnit (spec3 154) hC r ∈ T := by
    intro r w hf hr hw
    have hw' : HasOrd onGenData.mcert w := hHO _ fun q hq => by
      have h4 := hw q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h4 ⊢
      rcases h4 with h4 | h4 | h4 | h4 <;> simp [h4]
    rw [regUnit_eq' (spec3 154) hC hf (hHO1 r hr) hw']
    exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup (spec3 154) hC T w
      fun q hq => hu4 _ (hw q hq)
  have hT12 : regUnit (spec3 154) hC 12 ∈ T :=
    hline 12 [(4, 2), (5, 1), (6, 1), (7, 0)] (hhead _ (by simp)) (by simp) (by simp)
  have hT16 : regUnit (spec3 154) hC 16 ∈ T :=
    hline 16 [(4, 1), (5, 1), (6, 1), (7, 2)] (hhead _ (by simp)) (by simp) (by simp)
  have hT21 : regUnit (spec3 154) hC 21 ∈ T :=
    hline 21 [(4, 2), (5, 0), (6, 1), (7, 1)] (hhead _ (by simp)) (by simp) (by simp)
  have hT25 : regUnit (spec3 154) hC 25 ∈ T :=
    hline 25 [(4, 0), (5, 0), (6, 0), (7, 1)] (hhead _ (by simp)) (by simp) (by simp)
  have hpair : ∀ r s : ℕ, r ∈ [4, 5, 6, 7, 12, 16, 21, 25] → s ∈ [4, 5, 6, 7, 12, 16, 21, 25] →
      MFact.ne [(r, 1)] [] 0 ∈ onGenData.mcert.facts →
      MFact.ne [(s, 1)] [] 0 ∈ onGenData.mcert.facts →
      MFact.ne [(s, 1)] [(r, 1)] 0 ∈ onGenData.mcert.facts →
      MFact.ne [(s, 1)] [(r, 2)] 0 ∈ onGenData.mcert.facts →
      regUnit (spec3 154) hC r ≠ 1 ∧
        regUnit (spec3 154) hC s ∉ Subgroup.zpowers (regUnit (spec3 154) hC r) := by
    intro r s hr hs h1 h2 h3 h4
    have hr1 : regUnit (spec3 154) hC r ≠ 1 := regUnit_ne_one' (spec3 154) hC h1 (hHO1 r hr)
    refine ⟨hr1, fun hmem => ?_⟩
    have hr3 : regUnit (spec3 154) hC r ^ 3 = 1 := regUnit_pow (spec3 154) hC (hord r hr)
    have hHOr : ∀ e : ℕ, HasOrd onGenData.mcert [(r, e)] := fun e => hHO _ fun q hq => by
      rw [List.mem_singleton] at hq
      rw [hq]
      exact hr
    rcases mem_zpowers_of_pow_three hr3 hr1 hmem with h | h | h
    · exact regUnit_ne_one' (spec3 154) hC h2 (hHO1 s hs) h
    · exact regUnit_ne_pow' (spec3 154) hC h3 (hHO1 s hs) (hHOr 1) (h.trans (pow_one _).symm)
    · exact regUnit_ne_pow' (spec3 154) hC h4 (hHO1 s hs) (hHOr 2) h
  obtain ⟨h12, h16⟩ := hpair 12 16 (by simp) (by simp) (hhead _ (by simp)) (hhead _ (by simp))
    (hhead _ (by simp)) (hhead _ (by simp))
  obtain ⟨h21, h25⟩ := hpair 21 25 (by simp) (by simp) (hhead _ (by simp)) (hhead _ (by simp))
    (hhead _ (by simp)) (hhead _ (by simp))
  refine ⟨T, {v | ∃ g ∈ onGenData.gens, v = regUnit (spec3 154) hC g.reg}, hTel, hTc, hclos, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hcomm, hpow, hndvd⟩ := hgens g hg
  have hgl : onGenData.gens =
      [⟨8, 2, [12, 16]⟩, ⟨9, 2, [12, 16]⟩, ⟨10, 5, [21, 25]⟩, ⟨11, 5, [21, 25]⟩] := rfl
  rw [hgl] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨_, hT12, _, hT16, h12, h16, hcomm 12 (by simp), hcomm 16 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, hT12, _, hT16, h12, h16, hcomm 12 (by simp), hcomm 16 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, hT21, _, hT25, h21, h25, hcomm 21 (by simp), hcomm 25 (by simp), _, hpow, hndvd⟩
  · exact ⟨_, hT21, _, hT25, h21, h25, hcomm 21 (by simp), hcomm 25 (by simp), _, hpow, hndvd⟩

theorem sporPairCase_ONan_three
    (hBr : SporadicBridges) : Inputs2711c.SporPairCase .ONan 3 := by
  intro X _ _ hp _ L B _ hLq hB _ _ hrk4 _ _ _ hC1 hname hin _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨σ⟩ := hname
  obtain ⟨β⟩ := hBr .ONan
  haveI : Finite NativeSporadic.ON :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, S, hT, hT4, hS, hSl⟩ := on_gen_set
  have hP : Nat.card T = 3 ^ (Nat.card NativeSporadic.ON).factorization 3 := by
    rw [hT4, CFSG.Sporadic.ON.card_ON, factorization_eq_of_eq Nat.prime_three
      (show 460815505920 = 3 ^ 4 * 5689080320 by norm_num) (by norm_num)]
  refine eq_gammaTwo_of_two_lines (G := NativeSporadic.ON) (T := T) (S := S) hp hLq hB hin hrk4
    hC1 ?_ ?_ ?_ ?_ ?_
  · exact σ.trans β.symm
  · exact hT4
  · exact fun A hA => exists_map_conj_le hP hA
  · exact hS
  · intro s hs
    obtain ⟨f₁, hf₁, f₂, hf₂, h1, h2, h3, h4, h5⟩ := hSl s hs
    exact ⟨f₁, hf₁, f₂, hf₂, hT.2 f₁ hf₁, hT.2 f₂ hf₂, isElemAbelian_commute hT hf₁ hf₂, h1, h2,
      h3, h4, h5⟩

end PairON

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
