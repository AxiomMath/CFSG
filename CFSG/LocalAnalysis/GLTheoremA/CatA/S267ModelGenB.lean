module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def ModelBGen (p n : ℕ) (X : Type) [Group X] (ψ : MulAut X) : Prop :=
  ψ ^ p = 1 ∧ ψ ∉ (MulAut.conj : X →* MulAut X).range ∧
  ∃ (A A₁ J : Subgroup X) (t : X), IsElemAbelian p A ∧ Nat.card A = p ^ n ∧
    (∀ a ∈ A, ψ a = a) ∧ A₁ ≤ A ∧ Nat.card A₁ = p ∧
    GLAPComponent p (Subgroup.centralizer (A₁ : Set X)) J ∧
    A ≤ Subgroup.normalizer (J : Set X) ∧ J.map ψ.toMonoidHom = J ∧
    (∀ a ∈ A, ∀ k : ℕ, k < p →
      (∀ j ∈ J, j * (a * (ψ ^ k) j * a⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p J) → k = 0 ∧ a ∈ A₁) ∧
    GLAPLayer p (J ⊓ fixSubgroup ψ) ≠ ⊥ ∧
    t ≠ 1 ∧ t ^ 2 = 1 ∧ J ≤ Subgroup.centralizer ({t} : Set X) ∧
    A ≤ Subgroup.centralizer ({t} : Set X) ∧ ψ t = t

theorem pow_not_mem_range_conj {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) {ψ : MulAut X}
    (hψp : ψ ^ p = 1) (hψout : ψ ∉ (MulAut.conj : X →* MulAut X).range) {k : ℕ} (hk : k < p)
    (hk0 : k ≠ 0) : ψ ^ k ∉ (MulAut.conj : X →* MulAut X).range := by
  intro hmem
  apply hψout
  have hcop : Nat.Coprime k p := (Nat.coprime_comm.mp
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk)))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have e : ψ = (ψ ^ k) ^ m := by
    rw [← pow_mul, pow_eq_pow_mod (k * m) hψp, hm, pow_one]
  rw [e]
  exact Subgroup.pow_mem _ hmem m

section Transport

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_modelBGen {n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (hSn : S.Normal)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hBn : Nat.card B ≤ p ^ (n + 2))
    {X : Type} [Group X] [Finite X] (φ : X →* Ω) (hφ : Function.Injective φ) (hφS : φ.range = S)
    {ψ : MulAut X} {b' : Ω} (hb'p : b' ^ p = 1)
    (hb'B₀ : ∀ b ∈ B ⊓ centModSubgroup p S, b' * b = b * b')
    (hb'φ : ∀ x, b' * φ x * b'⁻¹ = φ (ψ x)) (hM : ModelBGen p n X ψ) : S267ConcA p S B := by
  obtain ⟨hψp, hψout, A, A₁, J, t, hA, hAc, hψA, h1, hA₁c, hJ, hAN, hJψ, hcent, hlay, ht1, ht2,
    hJt, hAt, hψt⟩ := hM
  haveI : Fact p.Prime := ⟨hp⟩
  set B₀ := B ⊓ centModSubgroup p S with hB₀
  have hmapS : ∀ (K : Subgroup X), K.map φ ≤ S := fun K => by
    rw [← hφS]
    exact Subgroup.map_le_range φ K
  have hB₀S : ∀ b ∈ B₀, ∀ s ∈ S, b * s = s * b := fun b hb s hs =>
    comm_of_mem_centMod hSn hcore hb.2 hs
  have hB₀el : IsElemAbelian p B₀ := hB.mono inf_le_left
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
  have hkey : ∀ b₀ ∈ B₀, ∀ k : ℕ, k < p → ∀ a ∈ A,
      (∀ x : X, (b₀ * b' ^ k * φ a) * φ x * (b₀ * b' ^ k * φ a)⁻¹ = φ x) → k = 0 ∧ a = 1 := by
    intro b₀ hb₀ k hk a ha hx
    have hx' : ∀ x : X, a * (ψ ^ k) x * a⁻¹ = x := fun x =>
      hφ ((hconj b₀ hb₀ k a ha x).symm.trans (hx x))
    have hk0 : k = 0 := by
      by_contra hk0
      apply pow_not_mem_range_conj hp hψp hψout hk hk0
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
  have hb'ord : orderOf b' = p := orderOf_eq_prime hb'p hb'1
  have hzc : Nat.card (Subgroup.zpowers b') = p := by rw [Nat.card_zpowers, hb'ord]
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
  have hCel : IsElemAbelian p C := by
    refine hB₀el.sup_of_commute ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩ hB₀b'
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
      simp only [Subgroup.coe_mul]
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb'p, one_zpow]
  have hCmem : ∀ c ∈ C, ∃ b₀ ∈ B₀, ∃ k : ℕ, k < p ∧ b₀ * b' ^ k = c := by
    intro c hc
    obtain ⟨b₀, hb₀, y, hy, rfl⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hB₀b' hc
    obtain ⟨k, hk, rfl⟩ := exists_pow_lt_of_pow_eq_one hp.pos hb'p hy
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
    obtain ⟨k, hk, rfl⟩ := exists_pow_lt_of_pow_eq_one hp.pos hb'p hy
    have h := hkey 1 (Subgroup.one_mem _) k hk 1 (Subgroup.one_mem _) fun x => by
      rw [one_mul, map_one, mul_one]
      calc b' ^ k * φ x * (b' ^ k)⁻¹ = φ x * b' ^ k * (b' ^ k)⁻¹ := by
            rw [comm_of_mem_centMod hSn hcore hy₀.2 (hφmem x)]
        _ = φ x := by group
    rw [Subgroup.mem_bot, h.1, pow_zero]
  have hCc : Nat.card C = p ^ 2 := by
    rw [hC, CFSG.CGT.T75P.card_sup_of_commute hB₀b' hB₀z, hBC, hzc, sq]
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
  have hAφ : IsElemAbelian p (A.map φ) := CFSG.SectionRank.isElemAbelian_map hA φ
  have hB'el : IsElemAbelian p B' := hCel.sup_of_commute hAφ hCcomm
  have hB'c : Nat.card B' = p ^ (n + 2) := by
    rw [hB', CFSG.CGT.T75P.card_sup_of_commute hCcomm hCA, hCc,
      Subgroup.card_map_of_injective hφ, hAc]
    ring
  have hDcomm : ∀ b ∈ B₀, ∀ a ∈ A₁.map φ, b * a = a * b := fun b hb a ha =>
    hB₀S b hb a (hmapS A₁ ha)
  have hDinf : B₀ ⊓ A₁.map φ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₀, hx⟩
    exact (Subgroup.mem_bot).2 (eq_one_of_mem_centMod hSn hcore hZ (hmapS A₁ hx) hx₀.2)
  have hDc : Nat.card D = p ^ 2 := by
    rw [hD, CFSG.CGT.T75P.card_sup_of_commute hDcomm hDinf, hBC,
      Subgroup.card_map_of_injective hφ, hA₁c, sq]
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
    obtain ⟨k, hk, hk'⟩ := exists_pow_lt_of_pow_eq_one hp.pos hb'p hy
    have h := hkey b₀⁻¹ (B₀.inv_mem hb₀) k hk a⁻¹ (A.inv_mem (h1 ha)) fun x => by
      have e : b₀⁻¹ * b' ^ k * φ a⁻¹ = 1 := by
        rw [hk', ← hyeq, map_inv]
        group
      rw [e, one_mul, inv_one, mul_one]
    rw [Subgroup.mem_bot, ← hk', h.1, pow_zero]
  have hEc : Nat.card E = p ^ 3 := by
    rw [hE, CFSG.CGT.T75P.card_sup_of_commute hDz hDzinf, hDc, hzc]
    ring
  have hJS : Jφ ≤ S := hmapS J
  have hJA₁ : J ≤ Subgroup.centralizer (A₁ : Set X) := hJ.1
  have htS : φ t ∈ S := hφmem t
  have hSD : S ⊓ Subgroup.centralizer (D : Set Ω) =
      (Subgroup.centralizer (A₁ : Set X)).map φ := by
    rw [hD, inf_centralizer_sup_of_comm (fun b hb s hs => hB₀S b hb s hs),
      map_centralizer_of_injective φ hφ, hφS]
  have hJE : Jφ ⊓ Subgroup.centralizer (E : Set Ω) = (J ⊓ fixSubgroup ψ).map φ := by
    apply le_antisymm
    · rintro y ⟨⟨j, hj, rfl⟩, hyE⟩
      refine ⟨j, ⟨hj, (show ψ j = j from ?_)⟩, rfl⟩
      apply hφ
      rw [← hb'φ]
      have hc := Subgroup.mem_centralizer_iff.1 hyE b'
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b'))
      rw [hc, mul_inv_cancel_right]
    · rintro _ ⟨j, ⟨hj, hjψ⟩, rfl⟩
      refine ⟨⟨j, hj, rfl⟩, ?_⟩
      have hjψ' : ψ j = j := hjψ
      have hb'j : b' * φ j = φ j * b' := by
        have h := hb'φ j
        rw [hjψ'] at h
        calc b' * φ j = b' * φ j * b'⁻¹ * b' := by group
          _ = φ j * b' := by rw [h]
      refine mem_centralizer_sup_of_comm (mem_centralizer_sup_of_comm
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
    refine sup_le (sup_le (fun b hb => mem_normalizer_of_forall_comm fun k hk =>
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
  have hcentD : ∀ b ∈ B', CentMod p Jφ b ↔ b ∈ D := by
    intro b hb
    constructor
    · intro hc
      obtain ⟨c, hcC, _, ⟨a, ha, rfl⟩, rfl⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hCcomm hb
      obtain ⟨b₀, hb₀, k, hk, rfl⟩ := hCmem c hcC
      have hj : ∀ j ∈ J, j * (a * (ψ ^ k) j * a⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p J := by
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
  have hEl : GLAPLayer p (Jφ ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥ := by
    rw [hJE]
    exact CFSG.LocalAnalysis.GLTheoremA.I2611.glaPLayer_map_ne_bot hp φ hφ hlay
  have hB'C : B' ⊓ centModSubgroup p S = B₀ := by
    apply le_antisymm
    · rintro b ⟨hb, hbC⟩
      obtain ⟨c, hcC, _, ⟨a, ha, rfl⟩, rfl⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hCcomm hb
      obtain ⟨b₀, hb₀, k, hk, rfl⟩ := hCmem c hcC
      have h := hkey b₀ hb₀ k hk a ha fun x => by
        rw [comm_of_mem_centMod hSn hcore hbC (hφmem x), mul_inv_cancel_right]
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
  have hB'T : B' ≤ Subgroup.normalizer ((Subgroup.zpowers (φ t) : Subgroup Ω) : Set Ω) := by
    intro b hb
    refine mem_normalizer_of_forall_comm fun k hk => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hB'cent hb)) m).eq
  have h4 : p ^ 2 * p ^ 2 ≤ p ^ (n + 2) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  refine ⟨B', D, Jφ, hB'el, ⟨⟨hDB', by rw [hDc], by rw [hDc, hB'c]; exact h4⟩,
    ⟨by rw [hSD, hJφ, CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hφ]; exact hJ,
      hB'N, hcentD⟩,
    fun _ => ⟨E, hEB', hB'el.mono hEB', hEc, hDE, hEl⟩⟩,
    Or.inr ⟨by rw [hB'c]; exact hBn, Subgroup.zpowers (φ t), zpowers_ne_bot_of_ne_one htφ1,
      isPGroup_two_zpowers_of_sq htφ2, hB'T⟩,
    by rw [hB'C, hBC], φ t, htφ1, htφ2, fun d hd => ?_, fun j hj => ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.1 (hB'cent (hDB' hd))
  · obtain ⟨j', hj', rfl⟩ := hj
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hJt hj')]

end Transport

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
