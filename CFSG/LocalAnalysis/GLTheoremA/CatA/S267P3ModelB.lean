module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelA
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def ModelB (X : Type) [Group X] (ψ : MulAut X) : Prop :=
  ψ ^ 3 = 1 ∧ ψ ∉ (MulAut.conj : X →* MulAut X).range ∧
  ∃ (A A₁ J : Subgroup X) (t : X), IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 ∧
    (∀ a ∈ A, ψ a = a) ∧ A₁ ≤ A ∧ Nat.card A₁ = 3 ∧
    GLAPComponent 3 (Subgroup.centralizer (A₁ : Set X)) J ∧
    A ≤ Subgroup.normalizer (J : Set X) ∧ J.map ψ.toMonoidHom = J ∧
    (∀ a ∈ A, ∀ k : ℕ, k < 3 →
      (∀ j ∈ J, j * (a * (ψ ^ k) j * a⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 J) → k = 0 ∧ a ∈ A₁) ∧
    GLAPLayer 3 (J ⊓ fixSubgroup ψ) ≠ ⊥ ∧
    t ≠ 1 ∧ t ^ 2 = 1 ∧ J ≤ Subgroup.centralizer ({t} : Set X) ∧
    A ≤ Subgroup.centralizer ({t} : Set X) ∧ ψ t = t

section Helpers

variable {G : Type*} [Group G]

theorem modelB_exists_pow_lt_three {g y : G} (hg : g ^ 3 = 1) (hy : y ∈ Subgroup.zpowers g) :
    ∃ k : ℕ, k < 3 ∧ g ^ k = y := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h3 : (0 : ℤ) ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  refine ⟨(n % 3).toNat, by omega, ?_⟩
  have e : n = 3 * (n / 3) + n % 3 := (Int.mul_ediv_add_emod n 3).symm
  have hz : (g ^ (n % 3).toNat : G) = g ^ (n % 3) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg h3]
  rw [hz]
  conv_rhs => rw [e]
  rw [zpow_add, zpow_mul, zpow_ofNat, hg, one_zpow, one_mul]

theorem modelB_mem_centralizer_sup {y : G} {H K : Subgroup G} (hH : ∀ h ∈ H, h * y = y * h)
    (hK : ∀ k ∈ K, k * y = y * k) : y ∈ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have hle : H ⊔ K ≤ Subgroup.centralizer ({y} : Set G) :=
    sup_le (fun h hh => Subgroup.mem_centralizer_singleton_iff.2 (hH h hh))
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hK k hk))
  exact Subgroup.mem_centralizer_iff.2 fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem modelB_mem_normalizer_of_comm {g : G} {K : Subgroup G} (hg : ∀ k ∈ K, g * k = k * g) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hg y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have e : g * (g * y * g⁻¹) = g * y := by rw [hg _ hy]; group
    rw [mul_left_cancel e] at hy
    exact hy

end Helpers

section Transport

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_modelB (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥) {X : Type} [Group X]
    [Finite X] (φ : X →* Ω) (hφ : Function.Injective φ) (hφS : φ.range = S) {ψ : MulAut X}
    {b' : Ω} (hb'3 : b' ^ 3 = 1) (hb'B₀ : ∀ b ∈ B ⊓ centModSubgroup 3 S, b' * b = b * b')
    (hb'φ : ∀ x, b' * φ x * b'⁻¹ = φ (ψ x)) (hM : ModelB X ψ) : S267ConcA 3 S B := by
  obtain ⟨hψ3, hψout, A, A₁, J, t, hA, hAc, hψA, h1, hA₁c, hJ, hAN, hJψ, hcent, hlay, ht1, ht2,
    hJt, hAt, hψt⟩ := hM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B₀ := B ⊓ centModSubgroup 3 S with hB₀
  have hmapS : ∀ (K : Subgroup X), K.map φ ≤ S := fun K => by
    rw [← hφS]
    exact Subgroup.map_le_range φ K
  have hB₀S : ∀ b ∈ B₀, ∀ s ∈ S, b * s = s * b := fun b hb s hs =>
    H.comm_of_mem_centMod hb.2 hs
  have hB₀el : IsElemAbelian 3 B₀ := H.elem.mono inf_le_left
  have hφmem : ∀ x : X, φ x ∈ S := fun x => hφS ▸ ⟨x, rfl⟩
  have hZX : ∀ a : X, (∀ x : X, a * x = x * a) → a = 1 := by
    intro a ha
    have h : (⟨φ a, hφmem a⟩ : ↥S) ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun g => by
      obtain ⟨x, hx⟩ := (show (g : Ω) ∈ φ.range from hφS ▸ g.2)
      apply Subtype.ext
      change (g : Ω) * φ a = φ a * g
      rw [← hx, ← map_mul, ← map_mul, ha x]
    rw [hZ, Subgroup.mem_bot] at h
    exact hφ ((congrArg Subtype.val h).trans (map_one φ).symm)
  have hψA' : ∀ k : ℕ, ∀ a ∈ A, (ψ ^ k) a = a := by
    intro k a ha
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hψA a ha, ih]
  have hψk : ∀ k : ℕ, k < 3 → k ≠ 0 → ψ ^ k ∉ (MulAut.conj : X →* MulAut X).range := by
    intro k hk hk0 hmem
    interval_cases k
    · exact hk0 rfl
    · rw [pow_one] at hmem
      exact hψout hmem
    · apply hψout
      have h2 : ψ = (ψ ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ']
        exact hψ3
      rw [h2]
      exact Subgroup.inv_mem _ hmem
  have hb'k : ∀ k : ℕ, ∀ x : X, b' ^ k * φ x * (b' ^ k)⁻¹ = φ ((ψ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      calc b' ^ (k + 1) * φ x * (b' ^ (k + 1))⁻¹ = b' ^ k * (b' * φ x * b'⁻¹) * (b' ^ k)⁻¹ := by
            rw [pow_succ]; group
        _ = φ ((ψ ^ (k + 1)) x) := by rw [hb'φ, ih, pow_succ, MulAut.mul_apply]
  have hconj : ∀ b₀ ∈ B₀, ∀ k : ℕ, ∀ a ∈ A, ∀ x : X,
      (b₀ * b' ^ k * φ a) * φ x * (b₀ * b' ^ k * φ a)⁻¹ = φ (a * (ψ ^ k) x * a⁻¹) := by
    intro b₀ hb₀ k a ha x
    have e1 : (b₀ * b' ^ k * φ a) * φ x * (b₀ * b' ^ k * φ a)⁻¹ =
        b₀ * (b' ^ k * φ (a * x * a⁻¹) * (b' ^ k)⁻¹) * b₀⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    have e2 : (ψ ^ k) (a * x * a⁻¹) = a * (ψ ^ k) x * a⁻¹ := by
      rw [map_mul, map_mul, map_inv, hψA' k a ha]
    rw [e1, hb'k, e2, hB₀S b₀ hb₀ _ (hφmem _), mul_inv_cancel_right]
  have hkey : ∀ b₀ ∈ B₀, ∀ k : ℕ, k < 3 → ∀ a ∈ A,
      (∀ x : X, (b₀ * b' ^ k * φ a) * φ x * (b₀ * b' ^ k * φ a)⁻¹ = φ x) → k = 0 ∧ a = 1 := by
    intro b₀ hb₀ k hk a ha hx
    have hx' : ∀ x : X, a * (ψ ^ k) x * a⁻¹ = x := fun x => hφ ((hconj b₀ hb₀ k a ha x).symm.trans (hx x))
    have hk0 : k = 0 := by
      by_contra hk0
      apply hψk k hk hk0
      refine ⟨a⁻¹, MulEquiv.ext fun x => ?_⟩
      rw [MulAut.conj_apply]
      have := hx' x
      calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * (ψ ^ k) x * a⁻¹) * a⁻¹⁻¹ := by rw [this]
        _ = (ψ ^ k) x := by group
    subst hk0
    refine ⟨rfl, hZX a fun x => ?_⟩
    have := hx' x
    rw [pow_zero, MulAut.one_apply] at this
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [this]
  set C := B₀ ⊔ Subgroup.zpowers b' with hC
  have hb'1 : b' ≠ 1 := by
    intro h
    apply hψout
    refine ⟨1, MulEquiv.ext fun x => hφ ?_⟩
    rw [map_one, MulAut.one_apply, ← hb'φ, h, one_mul, inv_one, mul_one]
  have hb'ord : orderOf b' = 3 := orderOf_eq_prime hb'3 hb'1
  have hzc : Nat.card (Subgroup.zpowers b') = 3 := by rw [Nat.card_zpowers, hb'ord]
  have hB₀b' : ∀ b ∈ B₀, ∀ y ∈ Subgroup.zpowers b', b * y = y * b := by
    intro b hb y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (hb'B₀ b hb) n).eq.symm
  have hb'A : ∀ a ∈ A, b' * φ a = φ a * b' := by
    intro a ha
    have h := hb'φ a
    rw [hψA a ha] at h
    calc b' * φ a = b' * φ a * b'⁻¹ * b' := by group
      _ = φ a * b' := by rw [h]
  have hCel : IsElemAbelian 3 C := by
    refine hB₀el.sup_of_commute ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩ hB₀b'
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
      simp only [Subgroup.coe_mul]
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb'3, one_zpow]
  have hCmem : ∀ c ∈ C, ∃ b₀ ∈ B₀, ∃ k : ℕ, k < 3 ∧ b₀ * b' ^ k = c := by
    intro c hc
    obtain ⟨b₀, hb₀, y, hy, rfl⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hB₀b' hc
    obtain ⟨k, hk, rfl⟩ := modelB_exists_pow_lt_three hb'3 hy
    exact ⟨b₀, hb₀, k, hk, rfl⟩
  have hCcomm : ∀ c ∈ C, ∀ y ∈ A.map φ, c * y = y * c := by
    intro c hc y hy
    obtain ⟨b₀, hb₀, k, -, rfl⟩ := hCmem c hc
    obtain ⟨a, ha, rfl⟩ := hy
    have hk : b' ^ k * φ a = φ a * b' ^ k := (Commute.pow_left (hb'A a ha) k).eq
    rw [mul_assoc, hk, ← mul_assoc, hB₀S b₀ hb₀ _ (hφmem a), mul_assoc]
  have hB₀z : B₀ ⊓ Subgroup.zpowers b' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy₀, hy⟩
    obtain ⟨k, hk, rfl⟩ := modelB_exists_pow_lt_three hb'3 hy
    have h := hkey 1 (Subgroup.one_mem _) k hk 1 (Subgroup.one_mem _) fun x => by
      rw [one_mul, map_one, mul_one]
      calc b' ^ k * φ x * (b' ^ k)⁻¹ = φ x * b' ^ k * (b' ^ k)⁻¹ := by
            rw [H.comm_of_mem_centMod hy₀.2 (hφmem x)]
        _ = φ x := by group
    rw [Subgroup.mem_bot, h.1, pow_zero]
  have hCc : Nat.card C = 3 ^ 2 := by
    rw [hC, CFSG.CGT.T75P.card_sup_of_commute hB₀b' hB₀z, H.cent, hzc]; norm_num
  have hCA : C ⊓ A.map φ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyC, ⟨a, ha, rfl⟩⟩
    obtain ⟨b₀, hb₀, k, hk, hy⟩ := hCmem _ hyC
    have h := hkey b₀ hb₀ k hk a⁻¹ (A.inv_mem ha) fun x => by
      rw [hy, map_inv, mul_inv_cancel, one_mul, inv_one, mul_one]
    rw [Subgroup.mem_bot]
    have : a = 1 := inv_eq_one.1 h.2
    rw [this, map_one]
  set B' := C ⊔ A.map φ with hB'
  set D := B₀ ⊔ A₁.map φ with hD
  set E := D ⊔ Subgroup.zpowers b' with hE
  set Jφ := J.map φ with hJφ
  have hAφ : IsElemAbelian 3 (A.map φ) := CFSG.SectionRank.isElemAbelian_map hA φ
  have hB'el : IsElemAbelian 3 B' := hCel.sup_of_commute hAφ hCcomm
  have hB'c : Nat.card B' = 3 ^ 4 := by
    rw [hB', CFSG.CGT.T75P.card_sup_of_commute hCcomm hCA, hCc,
      Subgroup.card_map_of_injective hφ, hAc]; norm_num
  have hDcomm : ∀ b ∈ B₀, ∀ a ∈ A₁.map φ, b * a = a * b := fun b hb a ha =>
    hB₀S b hb a (hmapS A₁ ha)
  have hDinf : B₀ ⊓ A₁.map φ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₀, hx⟩
    exact (Subgroup.mem_bot).2 (H.eq_one_of_mem_centMod hZ (hmapS A₁ hx) hx₀.2)
  have hDc : Nat.card D = 3 ^ 2 := by
    rw [hD, CFSG.CGT.T75P.card_sup_of_commute hDcomm hDinf, H.cent,
      Subgroup.card_map_of_injective hφ, hA₁c]; norm_num
  have hDB' : D ≤ B' :=
    sup_le (le_sup_left.trans le_sup_left) (le_sup_of_le_right (Subgroup.map_mono h1))
  have hzB' : Subgroup.zpowers b' ≤ B' := le_sup_right.trans le_sup_left
  have hEB' : E ≤ B' := sup_le hDB' hzB'
  have hDE : D ≤ E := le_sup_left
  have hDz : ∀ d ∈ D, ∀ y ∈ Subgroup.zpowers b', d * y = y * d := fun d hd y hy =>
    hB'el.comm (hDB' hd) (hzB' hy)
  have hDzinf : D ⊓ Subgroup.zpowers b' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hy⟩
    obtain ⟨b₀, hb₀, _, ⟨a, ha, rfl⟩, hyeq⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hDcomm hyD
    obtain ⟨k, hk, hk'⟩ := modelB_exists_pow_lt_three hb'3 hy
    have h := hkey b₀⁻¹ (B₀.inv_mem hb₀) k hk a⁻¹ (A.inv_mem (h1 ha)) fun x => by
      have e : b₀⁻¹ * b' ^ k * φ a⁻¹ = 1 := by
        rw [hk', ← hyeq, map_inv]
        group
      rw [e, one_mul, inv_one, mul_one]
    rw [Subgroup.mem_bot, ← hk', h.1, pow_zero]
  have hEc : Nat.card E = 3 ^ 3 := by
    rw [hE, CFSG.CGT.T75P.card_sup_of_commute hDz hDzinf, hDc, hzc]; norm_num
  have hJS : Jφ ≤ S := hmapS J
  have hJA₁ : J ≤ Subgroup.centralizer (A₁ : Set X) := hJ.1
  have htS : φ t ∈ S := hφmem t
  have hSD : S ⊓ Subgroup.centralizer (D : Set Ω) =
      (Subgroup.centralizer (A₁ : Set X)).map φ := by
    rw [map_centralizer_eq φ hφ, hφS]
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))
    · rintro y ⟨hyS, hyA⟩
      exact ⟨hyS, modelB_mem_centralizer_sup (fun b hb => hB₀S b hb y hyS)
        (fun k hk => Subgroup.mem_centralizer_iff.1 hyA k hk)⟩
  have hJE : Jφ ⊓ Subgroup.centralizer (E : Set Ω) = (J ⊓ fixSubgroup ψ).map φ := by
    apply le_antisymm
    · rintro y ⟨⟨j, hj, rfl⟩, hyE⟩
      refine ⟨j, ⟨hj, (show ψ j = j from ?_)⟩, rfl⟩
      apply hφ
      rw [← hb'φ]
      have hc := Subgroup.mem_centralizer_iff.1 hyE b' (Subgroup.mem_sup_right (Subgroup.mem_zpowers b'))
      rw [hc, mul_inv_cancel_right]
    · rintro _ ⟨j, ⟨hj, hjψ⟩, rfl⟩
      refine ⟨⟨j, hj, rfl⟩, ?_⟩
      have hjψ' : ψ j = j := hjψ
      have hb'j : b' * φ j = φ j * b' := by
        have h := hb'φ j
        rw [hjψ'] at h
        calc b' * φ j = b' * φ j * b'⁻¹ * b' := by group
          _ = φ j * b' := by rw [h]
      refine modelB_mem_centralizer_sup (modelB_mem_centralizer_sup
        (fun b hb => (hB₀S b hb _ (hφmem j)))
        (fun _ ha => ?_)) (fun y hy => ?_)
      · obtain ⟨a, ha, rfl⟩ := ha
        rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 (hJA₁ hj)) a ha]
      · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact (Commute.zpow_left hb'j n).eq
  have hb'N : b' ∈ Subgroup.normalizer (Jφ : Set Ω) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hb'φ]
      have hψj : ψ j ∈ J := by
        rw [← hJψ]
        exact ⟨j, hj, rfl⟩
      exact ⟨ψ j, hψj, rfl⟩
    · rintro ⟨j, hj, hjy⟩
      have hj' : j ∈ J.map ψ.toMonoidHom := hJψ.symm ▸ hj
      obtain ⟨j₀, hj₀, rfl⟩ := hj'
      have e : y = φ j₀ := by
        have h2 : b' * y * b'⁻¹ = b' * φ j₀ * b'⁻¹ := by rw [← hjy, hb'φ]; rfl
        exact mul_left_cancel (mul_right_cancel h2)
      rw [e]
      exact ⟨j₀, hj₀, rfl⟩
  have hB'N : B' ≤ Subgroup.normalizer (Jφ : Set Ω) := by
    refine sup_le (sup_le (fun b hb => modelB_mem_normalizer_of_comm fun k hk =>
      hB₀S b hb k (hJS hk)) (Subgroup.zpowers_le.2 hb'N)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.le_normalizer_map φ ⟨a, hAN ha, rfl⟩
  have hDcent : D ≤ Subgroup.centralizer (Jφ : Set Ω) := by
    refine sup_le (fun b hb => Subgroup.mem_centralizer_iff.2 fun j hj =>
      (hB₀S b hb j (hJS hj)).symm) ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 (hJA₁ hj)) a ha]
  have hcentD : ∀ b ∈ B', CentMod 3 Jφ b ↔ b ∈ D := by
    intro b hb
    constructor
    · intro hc
      obtain ⟨c, hcC, _, ⟨a, ha, rfl⟩, rfl⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hCcomm hb
      obtain ⟨b₀, hb₀, k, hk, rfl⟩ := hCmem c hcC
      have hj : ∀ j ∈ J, j * (a * (ψ ^ k) j * a⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 J := by
        intro j hj
        have hmem := hc.2 (Subgroup.commutator_mem_commutator (⟨j, hj, rfl⟩ : φ j ∈ Jφ)
          (Subgroup.mem_zpowers (b₀ * b' ^ k * φ a)))
        rw [hJφ, CFSG.LocalAnalysis.GLTheoremA.T123C.glaPPrimeCoreOf_map hφ] at hmem
        obtain ⟨w, hw, hwe⟩ := hmem
        have e : ⁅φ j, b₀ * b' ^ k * φ a⁆ = φ (j * (a * (ψ ^ k) j * a⁻¹)⁻¹) := by
          rw [commutatorElement_def, map_mul, map_inv, ← hconj b₀ hb₀ k a ha j]
          group
        rw [e] at hwe
        rw [hφ hwe] at hw
        exact hw
      obtain ⟨hk0, haA₁⟩ := hcent a ha k hk hj
      subst hk0
      rw [pow_zero, mul_one]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb₀)
        (Subgroup.mem_sup_right ⟨a, haA₁, rfl⟩)
    · intro hbD
      exact centMod_of_mem_centralizer (hDcent hbD)
  have hEl : GLAPLayer 3 (Jφ ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥ := by
    rw [hJE]
    exact CFSG.LocalAnalysis.GLTheoremA.I2611.glaPLayer_map_ne_bot Nat.prime_three φ hφ hlay
  have hB'C : B' ⊓ centModSubgroup 3 S = B₀ := by
    apply le_antisymm
    · rintro b ⟨hb, hbC⟩
      obtain ⟨c, hcC, _, ⟨a, ha, rfl⟩, rfl⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hCcomm hb
      obtain ⟨b₀, hb₀, k, hk, rfl⟩ := hCmem c hcC
      have h := hkey b₀ hb₀ k hk a ha fun x => by
        rw [H.comm_of_mem_centMod hbC (hφmem x), mul_inv_cancel_right]
      rw [h.1, h.2, pow_zero, mul_one, map_one, mul_one]
      exact hb₀
    · exact le_inf (le_sup_left.trans le_sup_left) inf_le_right
  have hb't : b' * φ t = φ t * b' := by
    have h := hb'φ t
    rw [hψt] at h
    calc b' * φ t = b' * φ t * b'⁻¹ * b' := by group
      _ = φ t * b' := by rw [h]
  have hB'cent : B' ≤ Subgroup.centralizer ({φ t} : Set Ω) := by
    refine sup_le (sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
      (hB₀S b hb _ htS)) ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 hb't
    · rintro _ ⟨a, ha, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.1 (hAt ha)]
  have htφ1 : φ t ≠ 1 := fun h => ht1 (hφ (h.trans (map_one φ).symm))
  have htφ2 : φ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hT2 : IsPGroup 2 (Subgroup.zpowers (φ t)) := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have hdvd : orderOf (x : Ω) ∣ 2 :=
      (orderOf_dvd_of_mem_zpowers x.2).trans (orderOf_dvd_of_pow_eq_one htφ2)
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd
  have hT1 : Subgroup.zpowers (φ t) ≠ ⊥ := fun h => htφ1 (by
    have := Subgroup.mem_zpowers (φ t)
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hB'T : B' ≤ Subgroup.normalizer ((Subgroup.zpowers (φ t) : Subgroup Ω) : Set Ω) := by
    intro b hb
    refine modelB_mem_normalizer_of_comm fun k hk => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hB'cent hb)) m).eq
  refine ⟨B', D, Jφ, hB'el, ⟨⟨hDB', by rw [hDc], by rw [hDc, hB'c]; norm_num⟩,
    ⟨by rw [hSD, hJφ, CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hφ]; exact hJ,
      hB'N, hcentD⟩,
    fun _ => ⟨E, hEB', hB'el.mono hEB', hEc, hDE, hEl⟩⟩,
    Or.inr ⟨by rw [H.card, hB'c], Subgroup.zpowers (φ t), hT1, hT2, hB'T⟩,
    by rw [hB'C, H.cent], φ t, htφ1, htφ2, fun d hd => ?_, fun j hj => ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.1 (hB'cent (hDB' hd))
  · obtain ⟨j', hj', rfl⟩ := hj
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hJt hj')]

end Transport

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
