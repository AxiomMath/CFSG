module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sstarMax_layer_eq_three {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax 3 B x L) : GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) = L := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hess := IsSStarMax.essential h
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hLc : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L := IsSStarMax.component h
  have hxp : x ^ 3 = 1 := (IsSStarMax.bmax h).1.2 x hxB
  have hxL : x ∈ centModSubgroup 3 L := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLc.1 hl)
  apply le_antisymm
  · refine sSup_le fun J hJ => ?_
    by_cases hJL : J = L
    · exact hJL ▸ le_rfl
    exfalso
    have hJCm : J ≤ centModSubgroup 3 L := le_centModSubgroup_of_ne hp hJ hLc hJL
    obtain ⟨w, hwJ, hwp, k, hkJ, hkw⟩ := exists_pow_eq_one_noncomm_of_component hp hp2 hJ
    have hkx : Commute k x := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hkJ)
    have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hwJ)
    have hwnx : w ∉ Subgroup.zpowers x := by
      intro hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact hkw (hkx.zpow_right n).eq
    obtain ⟨hE, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hwx hwp hxp hx1 hwnx
    have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers x ≤ centModSubgroup 3 L :=
      sup_le (Subgroup.zpowers_le.2 (hJCm hwJ)) (Subgroup.zpowers_le.2 hxL)
    have hcycS : IsCyclic (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) :=
      IsSStarMax.cycMod h (Subgroup.zpowers w ⊔ Subgroup.zpowers x)
        (fun g hg => centMod_iff.2 (hle hg)) (isPGroup_of_isElemAbelian hE)
    have hdiv : Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) ≤ 3 :=
      card_le_of_isCyclic_of_pow hp hcycS (fun d hd => hE.2 d hd)
    rw [hcard] at hdiv
    omega
  · exact le_sSup hLc

theorem centralizer_le_normalizer_of_sstarMax {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax 3 B x L) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have h1 := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.le_normalizer_glaPLayer 3
    (Subgroup.centralizer ({x} : Set G))
  rwa [sstarMax_layer_eq_three h] at h1

theorem three_complement {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax 3 B x L)
    {c : G} (hcC : c ∈ Subgroup.centralizer (L : Set G)) (hc3 : c ^ 3 = 1) (hcx : c * x = x * c) :
    c ∈ Subgroup.zpowers x := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hess := IsSStarMax.essential h
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hLc : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L := IsSStarMax.component h
  have hxp : x ^ 3 = 1 := (IsSStarMax.bmax h).1.2 x hxB
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLc.1 hl)
  by_contra hn
  obtain ⟨hE, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hcx hc3 hxp hx1 hn
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers x ≤ centModSubgroup 3 L := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact centMod_iff.1 (centMod_of_mem_centralizer hcC)
    · exact centMod_iff.1 (centMod_of_mem_centralizer hxC)
  have hcycS : IsCyclic (Subgroup.zpowers c ⊔ Subgroup.zpowers x : Subgroup G) :=
    IsSStarMax.cycMod h (Subgroup.zpowers c ⊔ Subgroup.zpowers x)
      (fun g hg => centMod_iff.2 (hle hg)) (isPGroup_of_isElemAbelian hE)
  have hdiv : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers x : Subgroup G) ≤ 3 :=
    card_le_of_isCyclic_of_pow hp hcycS (fun d hd => hE.2 d hd)
  rw [hcard] at hdiv
  omega

theorem eq_one_of_mul_center {Q : Type*} [Group Q] (hQ : commutator Q = ⊤) (α : MulAut Q)
    (hα : ∀ y : Q, y⁻¹ * α y ∈ Subgroup.center Q) : α = 1 := by
  let F : Subgroup Q := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Q)
  have hcomm : commutator Q ≤ F := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro y₁ _ y₂ _
    have e1 : α y₁ = y₁ * (y₁⁻¹ * α y₁) := by group
    have e2 : α y₂ = y₂ * (y₂⁻¹ * α y₂) := by group
    show α ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆
    rw [map_commutatorElement, e1, e2, commutatorElement_mul_center_left (hα y₁),
      commutatorElement_mul_center_right (hα y₂)]
  rw [hQ] at hcomm
  ext y
  have : y ∈ F := hcomm (Subgroup.mem_top y)
  simpa [F] using this

theorem mem_centralizer_of_centMod {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hOz : ∀ o ∈ GLAPPrimeCoreOf 3 L, ∀ l ∈ L, l * o = o * l) {c : G}
    (hc : c ∈ centModSubgroup 3 L) : c ∈ Subgroup.centralizer (L : Set G) := by
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hc.1
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨c, hcN⟩
  have hαy : ∀ y : ↥L, (α y : G) = c * y * c⁻¹ := fun y => rfl
  have hQ : commutator ↥L = ⊤ := by
    rw [_root_.commutator_def]
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    simpa using hperf
  have hα : ∀ y : ↥L, y⁻¹ * α y ∈ Subgroup.center ↥L := by
    intro y
    have h1 : ⁅(y : G)⁻¹, c⁆ ∈ GLAPPrimeCoreOf 3 L := hc.2 _ (L.inv_mem y.2)
    have hyc : (y⁻¹ * α y : ↥L) = ⟨⁅(y : G)⁻¹, c⁆, ?_⟩ := ?_
    · rw [hyc, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hOz _ h1 g g.2)
    · have := Subgroup.map_subtype_le (GLAPPrimeCore 3 ↥L)
      exact this h1
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαy, commutatorElement_def]
      group
  have h1 := eq_one_of_mul_center hQ α hα
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := congrArg (fun φ : MulAut ↥L => (φ ⟨l, hl⟩ : G)) h1
  simp only [MulAut.one_apply, hαy] at this
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem exists_centMod_of_inducesInnerMod' {L : Subgroup G} {g : G} (h : InducesInnerMod 3 L g) :
    ∃ l ∈ L, l⁻¹ * g ∈ centModSubgroup 3 L := by
  have hg := S3.mem_normalizer_of_inducesInnerMod h
  obtain ⟨l, hl, hy⟩ := h
  refine ⟨l, hl, ?_⟩
  have h1 : g⁻¹ * l ∈ centModSubgroup 3 L := by
    refine ⟨mul_mem (inv_mem hg) (Subgroup.le_normalizer hl), fun y hy' => ?_⟩
    have := hy (l * y⁻¹ * l⁻¹) (L.mul_mem (L.mul_mem hl (L.inv_mem hy')) (L.inv_mem hl))
    have e : (l⁻¹ * (l * y⁻¹ * l⁻¹) * l)⁻¹ * (g⁻¹ * (l * y⁻¹ * l⁻¹) * g) = ⁅y, g⁻¹ * l⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at this
  have h2 := inv_mem h1
  simpa [mul_inv_rev] using h2

theorem exists_decomp_of_inner {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax 3 B x L)
    (hperf : ⁅L, L⁆ = L) (hOz : ∀ o ∈ GLAPPrimeCoreOf 3 L, ∀ l ∈ L, l * o = o * l)
    (hZ3 : ∀ z ∈ L, (∀ l ∈ L, l * z = z * l) → ¬ 3 ∣ orderOf z)
    (hinn : ∀ b ∈ B, InducesInnerMod 3 L b) :
    ∀ b ∈ B, ∃ a ∈ B ⊓ L, ∃ j : ℤ, b = a * x ^ j := by
  have hess := IsSStarMax.essential h
  have hxB : x ∈ B := hess.1
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax h).1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component h).1
  intro b hb
  obtain ⟨l, hl, hc⟩ := exists_centMod_of_inducesInnerMod' (hinn b hb)
  set c : G := l⁻¹ * b with hcdef
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := mem_centralizer_of_centMod hperf hOz hc
  have hbl : b = l * c := by rw [hcdef]; group
  have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.1 hcC l hl
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hcomm : Commute l c := hlc
  have hlc3 : l ^ 3 * c ^ 3 = 1 := by
    rw [← hcomm.mul_pow, ← hbl]; exact hb3
  have hz : l ^ 3 ∈ L := L.pow_mem hl 3
  have hzc : ∀ l' ∈ L, l' * l ^ 3 = l ^ 3 * l' := by
    intro l' hl'
    have h1 : c ^ 3 ∈ Subgroup.centralizer (L : Set G) := Subgroup.pow_mem _ hcC 3
    have h2 : l ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hlc3
    rw [h2]
    have h3 := Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ h1) l' hl'
    exact h3
  have hord := hZ3 (l ^ 3) hz hzc
  set r : ℕ := orderOf (l ^ 3) with hr
  set k : ℕ := r ^ 2 with hk
  have hk1 : k % 3 = 1 := by
    have : r % 3 = 1 ∨ r % 3 = 2 := by omega
    rw [hk, Nat.pow_mod]
    rcases this with h1 | h1 <;> rw [h1] <;> norm_num
  have hzk : (l ^ 3) ^ k = 1 := by
    have : r ∣ k := Dvd.intro_left _ (by rw [hk]; ring)
    obtain ⟨m, hm⟩ := this
    rw [hm, pow_mul, pow_orderOf_eq_one, one_pow]
  obtain ⟨q, hq⟩ : ∃ q, k = 3 * q + 1 := ⟨k / 3, by omega⟩
  have hbk : b ^ k = b := by rw [hq, pow_add, pow_mul, hb3, one_pow, one_mul, pow_one]
  have hbk' : b = l ^ k * c ^ k := by
    calc b = b ^ k := hbk.symm
      _ = (l * c) ^ k := by rw [← hbl]
      _ = l ^ k * c ^ k := hcomm.mul_pow k
  have hc3k : (c ^ k) ^ 3 = 1 := by
    have h2 : c ^ 3 = (l ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hlc3
    calc (c ^ k) ^ 3 = (c ^ 3) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [h2, inv_pow, hzk, inv_one]
  have hcxx : c * x = x * c := by
    have hlx : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
    have hbx : b * x = x * b := isElemAbelian_commute hBel hb hxB
    calc c * x = l⁻¹ * (b * x) := by rw [hcdef]; group
      _ = l⁻¹ * (x * b) := by rw [hbx]
      _ = (l⁻¹ * x) * b := by group
      _ = (x * l⁻¹) * b := by
        have : l⁻¹ * x = x * l⁻¹ := (show Commute l x from hlx).inv_left.eq
        rw [this]
      _ = x * (l⁻¹ * b) := by group
  have hckC : c ^ k ∈ Subgroup.centralizer (L : Set G) := Subgroup.pow_mem _ hcC k
  have hcomm_x : (c ^ k) * x = x * (c ^ k) := ((Commute.pow_left (show Commute c x from hcxx) k)).eq
  have hmemx : c ^ k ∈ Subgroup.zpowers x := three_complement h hckC hc3k hcomm_x
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmemx
  refine ⟨b * x ^ (-j), ⟨?_, ?_⟩, j, ?_⟩
  · exact B.mul_mem hb (B.zpow_mem hxB _)
  · have : b * x ^ (-j) = l ^ k := by
      rw [zpow_neg, hj, hbk']; group
    rw [this]
    exact L.pow_mem hl k
  · group

theorem zpowers_inf_eq_bot_of_not_mem {x : G} (hxp : x ^ 3 = 1) (hx1 : x ≠ 1) {M : Subgroup G} (hxM : x ∉ M) :
    Subgroup.zpowers x ⊓ M = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hord : orderOf x = 3 := orderOf_eq_prime hxp hx1
  have hyx : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy.1
  have hdvd : Nat.card (Subgroup.zpowers y) ∣ Nat.card (Subgroup.zpowers x) :=
    Subgroup.card_dvd_of_le hyx
  rw [Nat.card_zpowers, Nat.card_zpowers, hord] at hdvd
  have hyo : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hy1
    · exact h1
  have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hyo]
  have heq : Subgroup.zpowers y = Subgroup.zpowers x := Subgroup.eq_of_le_of_card_ge hyx hcard
  have hxy : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
  exact hxM ((Subgroup.zpowers_le.2 hy.2) hxy)

theorem card_sup_zpowers_of_not_mem {x : G} (hxp : x ^ 3 = 1) (hx1 : x ≠ 1) {A M : Subgroup G}
    (hAM : A ≤ M) (hxM : x ∉ M) (hxA : ∀ a ∈ A, a * x = x * a) :
    Nat.card (Subgroup.zpowers x ⊔ A : Subgroup G) = 3 * Nat.card A := by
  have hnorm : A ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hc : Commute a x := hxA a ha
    have hconj : ∀ w ∈ Subgroup.zpowers x, a * w * a⁻¹ = w := by
      intro w hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      have := (Commute.zpow_right hc i).eq
      rw [this]; group
    constructor
    · intro hy
      rw [hconj y hy]; exact hy
    · intro hy
      have h2 : a⁻¹ * (a * y * a⁻¹) * a = a * y * a⁻¹ := by
        have h3 := hconj _ hy
        calc a⁻¹ * (a * y * a⁻¹) * a = a⁻¹ * (a * (a * y * a⁻¹) * a⁻¹) * a := by rw [h3]
          _ = a * y * a⁻¹ := by group
      have h5 : y = a⁻¹ * (a * y * a⁻¹) * a := by group
      rw [h5, h2]
      exact hy
  have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
  have hbot : Subgroup.zpowers x ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ Subgroup.zpowers x ⊓ M := ⟨hy.1, hAM hy.2⟩
    rw [zpowers_inf_eq_bot_of_not_mem hxp hx1 hxM] at this
    exact this
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hxp hx1] at h1
  exact h1

theorem commutatorElement_mul_zpow {t a x : G} (htx : t * x = x * t) (j : ℤ) :
    ⁅t, a * x ^ j⁆ = (t * a * t⁻¹) * a⁻¹ := by
  have h1 : Commute t (x ^ j) := Commute.zpow_right (show Commute t x from htx) j
  have h2 : x ^ j * t⁻¹ = t⁻¹ * x ^ j := (Commute.inv_left h1).eq.symm
  rw [commutatorElement_def]
  calc t * (a * x ^ j) * t⁻¹ * (a * x ^ j)⁻¹ = t * a * (x ^ j * t⁻¹) * (x ^ j)⁻¹ * a⁻¹ := by group
    _ = t * a * (t⁻¹ * x ^ j) * (x ^ j)⁻¹ * a⁻¹ := by rw [h2]
    _ = (t * a * t⁻¹) * a⁻¹ := by group

theorem cover_core {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax 3 B x L)
    (hperf : ⁅L, L⁆ = L) (hOz : ∀ o ∈ GLAPPrimeCoreOf 3 L, ∀ l ∈ L, l * o = o * l)
    (hZ3 : ∀ z ∈ L, (∀ l ∈ L, l * z = z * l) → ¬ 3 ∣ orderOf z)
    (hinn : ∀ b ∈ B, InducesInnerMod 3 L b) :
    x ∉ L ∧ Nat.card B = 3 * Nat.card ↥(B ⊓ L) ∧
      ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
        ¬ T ≤ GLAPPrimeCoreOf 3 L := by
  have hess := IsSStarMax.essential h
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax h).1
  have hxp : x ^ 3 = 1 := hBel.2 x hxB
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component h).1
  have hLxc : ∀ l ∈ L, l * x = x * l := fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
  have hxnL : x ∉ L := by
    intro hxL
    exact hZ3 x hxL (fun l hl => hLxc l hl) (by rw [orderOf_eq_prime hxp hx1])
  have hdec := exists_decomp_of_inner h hperf hOz hZ3 hinn
  have hBeq : B = Subgroup.zpowers x ⊔ (B ⊓ L) := by
    refine le_antisymm (fun b hb => ?_) (sup_le (Subgroup.zpowers_le.2 hxB) inf_le_left)
    obtain ⟨a, ha, j, rfl⟩ := hdec b hb
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha)
      (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers x j))
  have hcard : Nat.card B = 3 * Nat.card ↥(B ⊓ L) := by
    have h1 := card_sup_zpowers_of_not_mem hxp hx1 (A := B ⊓ L) (M := L) inf_le_right hxnL
      (fun a ha => hLxc a ha.2)
    rw [← hBeq] at h1
    exact h1
  refine ⟨hxnL, hcard, ?_⟩
  obtain ⟨T, hTx, hT2, hBT, hTB, hT1⟩ := exists_two_group_comm_eq Nat.prime_three (by norm_num)
    (isPGroup_of_isElemAbelian hBel) hess
  have hTN : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set G) := fun t ht =>
    centralizer_le_normalizer_of_sstarMax h (hTx ht)
  have hTxc : ∀ t ∈ T, t * x = x * t := fun t ht => Subgroup.mem_centralizer_singleton_iff.1 (hTx ht)
  have hcommT : ∀ t ∈ T, ∀ b ∈ B, ∃ a ∈ L, ∃ j : ℤ, ⁅t, b⁆ = (t * a * t⁻¹) * a⁻¹ := by
    intro t ht b hb
    obtain ⟨a, ha, j, rfl⟩ := hdec b hb
    exact ⟨a, ha.2, j, commutatorElement_mul_zpow (hTxc t ht) j⟩
  have hTL : T ≤ L := by
    rw [← hTB, Subgroup.commutator_le]
    intro t ht b hb
    obtain ⟨a, ha, j, hj⟩ := hcommT t ht b hb
    rw [hj]
    have h1 : t * a * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTN t ht) a).1 ha
    exact L.mul_mem h1 (L.inv_mem ha)
  refine ⟨T, hTL, hT2, hT1, hBT, fun hTO => ?_⟩
  apply hT1
  rw [← hTB, eq_bot_iff, Subgroup.commutator_le]
  intro t ht b hb
  obtain ⟨a, ha, j, hj⟩ := hcommT t ht b hb
  rw [hj, Subgroup.mem_bot]
  have h1 : a * t = t * a := hOz t (hTO ht) a ha
  have h2 : t * a * t⁻¹ = a := by rw [← h1]; group
  rw [h2]; group

theorem three_mul_card_le {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax 3 B x L)
    (hxnL : x ∉ L) {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzL : z ∈ L)
    (hzc : ∀ l ∈ L, l * z = z * l) {E : Subgroup G} (hE : IsElemAbelian 3 E) (hEL : E ≤ L) :
    3 * Nat.card E ≤ Nat.card B := by
  have hess := IsSStarMax.essential h
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax h).1
  have hxp : x ^ 3 = 1 := hBel.2 x hxB
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component h).1
  have hLxc : ∀ l ∈ L, l * x = x * l := fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ((Commute.zpow_left (show Commute x b from (hLxc b (hEL hb)).symm) i)).eq
  have hE' : IsElemAbelian 3 (Subgroup.zpowers x ⊔ E) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hxp) hE hcomm
  have hcard := card_sup_zpowers_of_not_mem hxp hx1 hEL hxnL (fun a ha => hLxc a (hEL ha))
  have hxz : x * z = z * x := (hLxc z hzL).symm
  have hle : Subgroup.zpowers x ⊔ E ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 (CatB.mem_normalizer_zpowers_of_commute hxz)) ?_
    intro e he
    exact CatB.mem_normalizer_zpowers_of_commute (hzc e (hEL he))
  have hS : Subgroup.zpowers z ≠ ⊥ := by
    intro hbot
    apply hz1
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have hS2 : IsPGroup 2 (Subgroup.zpowers z) := CatB.isPGroup_zpowers_of_pow_eq_one hz2
  have h1 := card_le_pow_glaTwoLocalRank Nat.prime_three hE' hS hS2 hle
  rw [hcard, ← (IsSStarMax.bmax h).2.1] at h1
  exact h1

end CFSG.LocalAnalysis.GLTheoremA
