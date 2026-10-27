module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.CGT.PushingUpLit.CGT6M.FiveTransfer
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.RankThree.PartOne.OutStructure
open CFSG.CGT.PushingUpLit.CGT6M (eq_of_map_eq_of_pow_eq_one exists_lift_of_pow_eq_one
  eq_one_of_pow_eq_one_of_mem_ker)

section Split

variable {p : ℕ} {Ω : Type*} [Group Ω] {S B : Subgroup Ω}

theorem conjNormal_mem_inner_iff [S.Normal] {x : Ω} :
    MulAut.conjNormal x ∈ Inn ↥S ↔ x ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  constructor
  · rintro ⟨s, hs⟩
    have hc : (s : Ω)⁻¹ * x ∈ Subgroup.centralizer (S : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := congrArg (fun α : MulAut ↥S => ((α ⟨g, hg⟩ : ↥S) : Ω)) hs
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc g * ((s : Ω)⁻¹ * x) = (s : Ω)⁻¹ * ((s : Ω) * g * (s : Ω)⁻¹) * x := by group
        _ = (s : Ω)⁻¹ * (x * g * x⁻¹) * x := by rw [h1]
        _ = (s : Ω)⁻¹ * x * g := by group
    have hx : x = (s : Ω) * ((s : Ω)⁻¹ * x) := by group
    rw [hx]
    exact Subgroup.mul_mem_sup s.2 hc
  · intro hx
    obtain ⟨s, hs, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    refine ⟨⟨s, hs⟩, MulEquiv.ext fun g => Subtype.ext ?_⟩
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    have hcg : (g : Ω) * c = c * g := (Subgroup.mem_centralizer_iff.1 hc) g g.2
    calc s * (g : Ω) * s⁻¹ = s * ((g : Ω) * c) * c⁻¹ * s⁻¹ := by group
      _ = s * (c * g) * c⁻¹ * s⁻¹ := by rw [hcg]
      _ = s * c * g * (s * c)⁻¹ := by group

theorem inner_split (hp : p.Prime) [S.Normal] (hB : IsElemAbelian p B) (hOut : OutPChain p ↥S) :
    B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
      ∃ b ∈ B, B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ := by
  set N := S ⊔ Subgroup.centralizer (S : Set Ω) with hN
  by_cases h : B ≤ N
  · exact Or.inl (inf_eq_left.2 h)
  right
  obtain ⟨b, hbB, hbN⟩ := Set.not_subset.1 h
  have hpow : ∀ x ∈ B, MulAut.conjNormal x ^ (p ^ 1) ∈ Inn ↥S := fun x hx => by
    rw [pow_one, ← map_pow, hB.2 x hx, map_one]
    exact one_mem _
  have hmemN : ∀ y : Ω, MulAut.conjNormal y ∈ Inn ↥S → y ∈ N := fun y hy =>
    conjNormal_mem_inner_iff.1 hy
  refine ⟨b, hbB, le_antisymm (fun x hx => ?_) (sup_le inf_le_left
    (Subgroup.zpowers_le.2 hbB)), ?_⟩
  · have hcomm : (MulAut.conjNormal x : MulAut ↥S) * MulAut.conjNormal b =
        MulAut.conjNormal b * MulAut.conjNormal x := by
      rw [← map_mul, ← map_mul, hB.comm hx hbB]
    rcases hOut.comparable hcomm (hpow x hx) (hpow b hbB) with ⟨m, hm⟩ | ⟨m, hm⟩
    ·
      rw [← map_zpow, ← map_mul] at hm
      have hx' : x = x * b ^ m * b ^ (-m) := by group
      rw [hx']
      exact Subgroup.mul_mem_sup ⟨B.mul_mem hx (B.zpow_mem hbB m), hmemN _ hm⟩
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _)
    ·
      rw [← map_zpow, ← map_mul] at hm
      have hn := hmemN _ hm
      have hxp : x ^ p = 1 := hB.2 x hx
      have hpm : ¬ (p : ℤ) ∣ m := by
        rintro ⟨k, rfl⟩
        apply hbN
        have h1 : x ^ ((p : ℤ) * k) = 1 := by rw [zpow_mul, zpow_natCast, hxp, one_zpow]
        rw [h1, mul_one] at hn
        exact hn
      obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 hpm)
      have hbx : b * x = x * b := hB.comm hbB hx
      have hcomm' : Commute b (x ^ m) := (Commute.zpow_right hbx m)
      have hxv : x = (x ^ m) ^ v := by
        have h1 : x = x ^ (u * (p : ℤ) + v * m) := by rw [huv, zpow_one]
        rw [zpow_add, mul_comm u (p : ℤ), zpow_mul, zpow_natCast, hxp, one_zpow, one_mul,
          mul_comm v m, zpow_mul] at h1
        exact h1
      have hxv' : x = (b * x ^ m) ^ v * b ^ (-v) := by
        rw [hcomm'.mul_zpow, (hcomm'.zpow_zpow v v).eq, mul_assoc, ← zpow_add, add_neg_cancel,
          zpow_zero, mul_one]
        exact hxv
      rw [hxv']
      exact Subgroup.mul_mem_sup ⟨B.zpow_mem (B.mul_mem hbB (B.zpow_mem hx m)) v,
        N.zpow_mem hn v⟩ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _)
  · rw [eq_bot_iff]
    rintro y ⟨hy, hyN⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [Subgroup.mem_bot]
    have hbp : b ^ p = 1 := hB.2 b hbB
    by_cases hpm : (p : ℤ) ∣ m
    · obtain ⟨k, rfl⟩ := hpm
      rw [zpow_mul, zpow_natCast, hbp, one_zpow]
    · exfalso
      obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 hpm)
      apply hbN
      have h1 : b = b ^ (u * (p : ℤ) + v * m) := by rw [huv, zpow_one]
      rw [zpow_add, mul_comm u (p : ℤ), zpow_mul, zpow_natCast, hbp, one_zpow, one_mul,
        mul_comm v m, zpow_mul] at h1
      rw [h1]
      exact N.zpow_mem hyN v

end Split

section Lift

variable {p : ℕ} {Ω : Type*} [Group Ω] {S B : Subgroup Ω}
variable {H : Type*} [Group H]

theorem commute_of_map_commute [Finite H] (φ : H →* Ω) (hker : φ.ker ≤ Subgroup.center H)
    (hp : p.Prime) (hC : ¬ p ∣ Nat.card φ.ker) {a b : H} (ha : a ^ p = 1)
    (hab : φ a * φ b = φ b * φ a) : a * b = b * a := by
  obtain ⟨k, hk⟩ : ∃ k : H, k = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hkK : k ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  have hkc : ∀ g : H, g * k = k * g := fun g => Subgroup.mem_center_iff.1 (hker hkK) g
  have hab' : a * b * a⁻¹ = k * b := by rw [hk]; group
  have hconj : ∀ n : ℕ, a ^ n * b * (a ^ n)⁻¹ = k ^ n * b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹ = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by group
        _ = a * (k ^ n * b) * a⁻¹ := by rw [ih]
        _ = k ^ n * (a * b * a⁻¹) := by
          rw [show a * (k ^ n * b) * a⁻¹ = (a * k ^ n) * b * a⁻¹ by group,
            (Commute.pow_right (hkc a) n).eq]
          group
        _ = k ^ n * (k * b) := by rw [hab']
        _ = k ^ (n + 1) * b := by rw [pow_succ, mul_assoc]
  have hkp : k ^ p = 1 := by
    have h1 := hconj p
    rw [ha, one_mul, inv_one, mul_one] at h1
    exact (mul_eq_right.1 h1.symm)
  have hk1 : a * b * a⁻¹ * b⁻¹ = 1 :=
    hk ▸ eq_one_of_pow_eq_one_of_mem_ker hp hC hkK hkp
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hk1, one_mul]

theorem conj_eq_of_inv_mul_mem_centralizer {s x : Ω}
    (h : s⁻¹ * x ∈ Subgroup.centralizer (S : Set Ω)) {g : Ω} (hg : g ∈ S) :
    x * g * x⁻¹ = s * g * s⁻¹ := by
  have hc : g * (s⁻¹ * x) = (s⁻¹ * x) * g := (Subgroup.mem_centralizer_iff.1 h) g hg
  calc x * g * x⁻¹ = s * ((s⁻¹ * x) * g) * (s⁻¹ * x)⁻¹ * s⁻¹ := by group
    _ = s * (g * (s⁻¹ * x)) * (s⁻¹ * x)⁻¹ * s⁻¹ := by rw [hc]
    _ = s * g * s⁻¹ := by group

variable [Finite H]

theorem exists_inner_lift [S.Normal] (hp : p.Prime) (hB : IsElemAbelian p B)
    (hZ : Subgroup.center ↥S = ⊥) (φ : H →* Ω) (hφS : φ.range = S)
    (hker : φ.ker ≤ Subgroup.center H) (hC : ¬ p ∣ Nat.card φ.ker) :
    ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →* H,
      (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
      IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
      ∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
  set C := Subgroup.centralizer (S : Set Ω) with hCdef
  set N := S ⊔ C with hN
  have hSC : ∀ s ∈ S, s ∈ C → s = 1 := by
    intro s hs hsC
    have h1 : (⟨s, hs⟩ : ↥S) ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 hsC) g g.2)
    rw [hZ, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hφmem : ∀ y : H, φ y ∈ S := fun y => hφS ▸ ⟨y, rfl⟩
  have hex : ∀ x : ↥(B ⊓ N), ∃ y : H, y ^ p = 1 ∧ (φ y)⁻¹ * (x : Ω) ∈ C := by
    intro x
    obtain ⟨s, hs, c, hc, hsc⟩ := Subgroup.mem_sup_of_normal_left.1 x.2.2
    have hxp : (x : Ω) ^ p = 1 := hB.2 _ x.2.1
    have hcs : Commute s c := (Subgroup.mem_centralizer_iff.1 hc) s hs
    have hsp : s ^ p = 1 := by
      have h1 : s ^ p * c ^ p = 1 := by rw [← hcs.mul_pow, hsc, hxp]
      have h2 : s ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
      apply hSC _ (S.pow_mem hs p)
      rw [h2]
      exact C.inv_mem (C.pow_mem hc p)
    have hCr : ¬ p ∣ Nat.card φ.rangeRestrict.ker := by rwa [MonoidHom.ker_rangeRestrict]
    obtain ⟨y, hys, hyp⟩ := exists_lift_of_pow_eq_one
      φ.rangeRestrict_surjective hp hCr (b := ⟨s, hφS ▸ hs⟩) (Subtype.ext (by simpa using hsp))
    have hys' : φ y = s := congrArg Subtype.val hys
    refine ⟨y, hyp, ?_⟩
    rw [hys', ← hsc, inv_mul_cancel_left]
    exact hc
  choose θf hθp hθc using hex
  have hmk : ∀ x : ↥(B ⊓ N), (QuotientGroup.mk (φ (θf x)) : Ω ⧸ C) = QuotientGroup.mk (x : Ω) :=
    fun x => QuotientGroup.eq.2 (hθc x)
  have huniq : ∀ (x : ↥(B ⊓ N)) (y : H), y ^ p = 1 → (φ y)⁻¹ * (x : Ω) ∈ C → y = θf x := by
    intro x y hy hyC
    refine eq_of_map_eq_of_pow_eq_one hker hp hC hy (hθp x) ?_
    have h1 : (QuotientGroup.mk (φ y) : Ω ⧸ C) = QuotientGroup.mk (φ (θf x)) := by
      rw [hmk, QuotientGroup.eq]
      exact hyC
    have h2 : (φ y)⁻¹ * φ (θf x) = 1 :=
      hSC _ (S.mul_mem (S.inv_mem (hφmem y)) (hφmem _)) (QuotientGroup.eq.1 h1)
    exact inv_mul_eq_one.1 h2
  have hcommS : ∀ x x' : ↥(B ⊓ N), φ (θf x) * φ (θf x') = φ (θf x') * φ (θf x) := by
    intro x x'
    have hxx : (x : Ω) * x' = x' * x := hB.comm x.2.1 x'.2.1
    have h1 : (QuotientGroup.mk (φ (θf x) * φ (θf x')) : Ω ⧸ C) =
        QuotientGroup.mk (φ (θf x') * φ (θf x)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hmk, hmk, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, hxx]
    have h2 := hSC _ (S.mul_mem (S.inv_mem (S.mul_mem (hφmem _) (hφmem _)))
      (S.mul_mem (hφmem _) (hφmem _))) (QuotientGroup.eq.1 h1)
    exact inv_mul_eq_one.1 h2
  have hcomm : ∀ x x' : ↥(B ⊓ N), θf x * θf x' = θf x' * θf x := fun x x' =>
    commute_of_map_commute φ hker hp hC (hθp x) (hcommS x x')
  have hmul : ∀ x x' : ↥(B ⊓ N), θf (x * x') = θf x * θf x' := by
    intro x x'
    refine (huniq (x * x') _ ?_ ?_).symm
    · rw [Commute.mul_pow (hcomm x x') p, hθp, hθp, one_mul]
    · rw [← QuotientGroup.eq, map_mul, QuotientGroup.mk_mul, hmk, hmk, ← QuotientGroup.mk_mul]
      rfl
  have hone : θf 1 = 1 :=
    (huniq 1 1 (one_pow p) (by rw [map_one, inv_one, one_mul]; exact C.one_mem)).symm
  let θ : ↥(B ⊓ N) →* H :=
    { toFun := θf
      map_one' := hone
      map_mul' := hmul }
  refine ⟨θ, hθc, ⟨⟨⟨fun y y' => ?_⟩⟩, ?_⟩, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨x, hx⟩ := y.2
    obtain ⟨x', hx'⟩ := y'.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hx']
    exact hcomm x x'
  · rintro _ ⟨x, rfl⟩
    exact hθp x
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    rw [Subgroup.mem_bot]
    refine eq_of_map_eq_of_pow_eq_one hker hp hC (hθp x) (one_pow p) ?_
    rw [map_one]
    exact hx
  · have h1 := hθc x
    change θf x = 1 at h
    rw [h, map_one, inv_one, one_mul] at h1
    exact h1
  · exact (huniq x 1 (one_pow p) (by rw [map_one, inv_one, one_mul]; exact h)).symm

theorem inner_lift_conj (φ : H →* Ω) (hφS : φ.range = S) {B₁ : Subgroup Ω} (θ : ↥B₁ →* H)
    (hθ : ∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) (x : ↥B₁) (h : H) :
    φ (θ x * h * (θ x)⁻¹) = (x : Ω) * φ h * (x : Ω)⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  exact (conj_eq_of_inv_mul_mem_centralizer (hθ x) (hφS ▸ ⟨h, rfl⟩)).symm

theorem card_range_mul_card_inf {B₁ : Subgroup Ω} (θ : ↥B₁ →* H)
    (hθ : ∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) :
    Nat.card θ.range * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (S : Set Ω)) = Nat.card B₁ := by
  have hker : θ.ker = (B₁ ⊓ Subgroup.centralizer (S : Set Ω)).subgroupOf B₁ := by
    ext x
    rw [MonoidHom.mem_ker, hθ, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have h1 : Nat.card θ.ker = Nat.card ↥(B₁ ⊓ Subgroup.centralizer (S : Set Ω)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h1, mul_comm]
  exact Subgroup.card_ker_mul_card_range θ

end Lift

section CentMod

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem inf_centMod_eq_inf_centralizer (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥) :
    B ⊓ centModSubgroup p S = B ⊓ Subgroup.centralizer (S : Set Ω) := by
  ext x
  refine ⟨fun ⟨hxB, hx⟩ => ⟨hxB, Subgroup.mem_centralizer_iff.2 fun s hs =>
    (comm_of_mem_centMod hSn hcore hx hs).symm⟩, fun ⟨hxB, hx⟩ => ⟨hxB, ?_⟩⟩
  exact centMod_iff.1 (centMod_of_mem_centralizer hx)

end CentMod

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
