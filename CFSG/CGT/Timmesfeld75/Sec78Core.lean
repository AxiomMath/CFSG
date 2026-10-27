module

public import CFSG.CGT.Timmesfeld75.Sec78Linear
public import CFSG.CGT.Timmesfeld75.Sec66Conj
public import CFSG.CGT.Timmesfeld75.Sec77Model

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

section Model

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] (M : TModel T T₁ n m)

include M

theorem TModel.comm_iff_data {e : G} (he : e ∈ normD T)
    {f : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)} {v : Fin n → GaloisField 2 m}
    (hv : v ≠ 0) (hdata : ∀ w, sact (ubar M.ε e) w = w + f w • v) {t : G} (ht : t ∈ T) :
    e * t = t * e ↔ f (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) = 0 := by
  have heH := M.mem_H he
  have hmem : e * t * e⁻¹ ∈ T := conj_mem_of_mem_normalizer he.2 ht
  have h1 := M.toAdd_phi_conj heH ht hmem
  rw [hdata] at h1
  constructor
  · intro hcomm
    have e1 : e * t * e⁻¹ = t := by rw [hcomm]; group
    have h2 : (⟨e * t * e⁻¹, hmem⟩ : ↥T) = ⟨t, ht⟩ := Subtype.ext e1
    rw [h2] at h1
    have h4 : Multiplicative.toAdd (M.φ ⟨t, ht⟩) + f (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) • v =
        Multiplicative.toAdd (M.φ ⟨t, ht⟩) + 0 := by rw [add_zero]; exact h1.symm
    have h3 := add_left_cancel h4
    exact (smul_eq_zero.1 h3).resolve_right hv
  · intro hf
    rw [hf, zero_smul, add_zero] at h1
    have h2 : (⟨e * t * e⁻¹, hmem⟩ : ↥T) = ⟨t, ht⟩ :=
      M.φ.injective (Multiplicative.toAdd.injective h1)
    have e1 : e * t * e⁻¹ = t := congrArg Subtype.val h2
    exact mul_inv_eq_iff_eq_mul.1 e1

end Model

section Core

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem Sec6Ctx.false_of_commuting_subgroup (hc : Sec6Ctx T T₁ n m) (M : TModel T T₁ n m)
    (hn : 2 ≤ n) {z δ : G} (hz : z ∈ normD T) (hδ : δ ∈ normD T)
    {B : Subgroup G} {s : G} (hBs : B ≤ conjSubgroup s T) (hsT : conjSubgroup s T ≠ T)
    (hBN : B ≤ Subgroup.normalizer (T : Set G)) (hBz : ∀ b ∈ B, b * z = z * b) (hδB : δ ∈ B)
    (hcard : Nat.card B = (2 ^ m) ^ (n - 1))
    {fδ fz : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    {vδ vz : Fin n → GaloisField 2 m} (hvδ : vδ ≠ 0) (hvz : vz ≠ 0)
    (hdδ : ∀ w, sact (ubar M.ε δ) w = w + fδ w • vδ)
    (hdz : ∀ w, sact (ubar M.ε z) w = w + fz w • vz)
    (hind : ∀ r t : GaloisField 2 m, r • fδ + t • fz = 0 → r = 0 ∧ t = 0) : False := by
  have := hc.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := hc.hy.pair
  have hTwc := hP.wc
  have hδ1 : δ ≠ 1 := ne_one_of_mem_classD hδ.1
  have hBD : ∀ b ∈ B, b ≠ 1 → b ∈ normD T ∧ b ∉ T := by
    intro b hb hb1
    refine ⟨⟨mem_classD_of_mem_conjSubgroup (hBs hb) hb1, hBN hb⟩, fun hbT => ?_⟩
    have hinf : T ⊓ conjSubgroup s T ≠ ⊥ := fun h0 => hb1 (by
      have h' : b ∈ T ⊓ conjSubgroup s T := ⟨hbT, hBs hb⟩
      rw [h0, Subgroup.mem_bot] at h'
      exact h')
    exact hsT (hTwc.conj_eq_of_inf_ne_bot hinf)
  have hBH : ∀ b ∈ B, b ∈ hSub T (normIn T₁ T) := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]
      exact Subgroup.one_mem _
    · exact M.mem_H (hBD b hb hb1).1
  have hzH : z ∈ hSub T (normIn T₁ T) := M.mem_H hz
  have hL₂ : normIn (conjSubgroup s T) T ≠ ⊥ := by
    intro h0
    have h' : δ ∈ normIn (conjSubgroup s T) T := mem_normIn.2 ⟨hBs hδB, hBN hδB⟩
    rw [h0, Subgroup.mem_bot] at h'
    exact hδ1 h'
  have hbot : normIn T (conjSubgroup s T) ≠ ⊥ := normIn_ne_bot_of_conj hTwc hsT hL₂
  have hS3 : Sec3 T (conjSubgroup s T) := hc.hS s hsT hbot
  have hker : ∀ b ∈ B, b ≠ 1 → ∀ t ∈ T, (b * t = t * b ↔ t ∈ normIn T (conjSubgroup s T)) := by
    intro b hb hb1 t ht
    have h := Subgroup.ext_iff.1 (hS3.cfg.inf_centralizer_eq_normIn
      (mem_normIn.2 ⟨hBs hb, hBN hb⟩) hb1) t
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at h
    constructor
    · intro hbt
      exact h.1 ⟨ht, hbt.symm⟩
    · intro htn
      exact (h.2 htn).2.symm
  have hkerEq : ∀ b ∈ B, b ≠ 1 → ∀ (f : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m))
      (v : Fin n → GaloisField 2 m), v ≠ 0 → (∀ w, sact (ubar M.ε b) w = w + f w • v) →
      ∀ w, f w = 0 ↔ fδ w = 0 := by
    intro b hb hb1 f v hv hd w
    obtain ⟨t, rfl⟩ : ∃ t : ↥T, Multiplicative.toAdd (M.φ t) = w :=
      ⟨M.φ.symm (Multiplicative.ofAdd w), by simp⟩
    have h1 := M.comm_iff_data (hBD b hb hb1).1 hv hd t.2
    have h2 := M.comm_iff_data hδ hvδ hdδ t.2
    simp only [Subtype.coe_eta] at h1 h2
    rw [← h1, ← h2, hker b hb hb1 t t.2, hker δ hδB hδ1 t t.2]
  obtain ⟨p, hp1, hp2⟩ := exists_vec_eq_one_zero hind
  have hΨ : ∀ b ∈ B, ∃ a : Fin n → GaloisField 2 m, fδ a = 0 ∧ fz a = 0 ∧
      ∀ w, sact (ubar M.ε b) w = w + fδ w • a := by
    intro b hb
    by_cases hb1 : b = 1
    · refine ⟨0, map_zero _, map_zero _, fun w => ?_⟩
      have h1 : ubar M.ε b = 1 := by
        rw [hb1]
        exact (ubar_eq_one_iff M.ε (Subgroup.one_mem _)).2 (Subgroup.one_mem T)
      rw [h1, sact_one, smul_zero, add_zero]
    · obtain ⟨f, v, hfv, hv, hf0, hd⟩ := M.exists_data (hBD b hb hb1).1 (hBD b hb hb1).2
      have hk := hkerEq b hb hb1 f v hv hd
      have hmul : ∀ w, f w = fδ w * f p :=
        apply_eq_mul_of_ker_le (fun w hw => (hk w).2 hw) hp1
      have hfp : f p ≠ 0 := by
        intro h0
        apply hf0
        refine LinearMap.ext fun w => ?_
        rw [LinearMap.zero_apply, hmul w, h0, mul_zero]
      have hδv : fδ v = 0 := (hk v).1 hfv
      have hcomm : ubar M.ε b * ubar M.ε z = ubar M.ε z * ubar M.ε b := by
        rw [← ubar_mul M.ε (hBH b hb) hzH, ← ubar_mul M.ε hzH (hBH b hb), hBz b hb]
      have hrel := transvection_comm_rel hd hdz hcomm p
      rw [hp2, zero_mul, zero_smul] at hrel
      have hzv : fz v = 0 := by
        have h5 : (f p * fz v) • vz = 0 := hrel.symm
        have h6 := (smul_eq_zero.1 h5).resolve_right hvz
        exact (mul_eq_zero.1 h6).resolve_left hfp
      refine ⟨f p • v, ?_, ?_, fun w => ?_⟩
      · rw [map_smul, hδv, smul_zero]
      · rw [map_smul, hzv, smul_zero]
      · rw [hd w, hmul w, smul_smul]
  choose! a ha1 ha2 ha3 using hΨ
  let Ψ : ↥B → {a : Fin n → GaloisField 2 m // fδ a = 0 ∧ fz a = 0} :=
    fun b => ⟨a b, ha1 b b.2, ha2 b b.2⟩
  have hinj : Function.Injective Ψ := by
    intro b b' hbb'
    have hab : a b = a b' := congrArg Subtype.val hbb'
    have hsact : ubar M.ε b = ubar M.ε b' := by
      apply eq_of_sact
      intro w
      rw [ha3 b b.2 w, ha3 b' b'.2 w, hab]
    have hmem : (b : G)⁻¹ * b' ∈ T := (ubar_eq_iff M.ε (hBH b b.2) (hBH b' b'.2)).1 hsact
    have hinfT : T ⊓ conjSubgroup s T = ⊥ := by
      by_contra hne
      exact hsT (hTwc.conj_eq_of_inf_ne_bot hne)
    have hBm : (b : G)⁻¹ * b' ∈ conjSubgroup s T := (conjSubgroup s T).mul_mem
      ((conjSubgroup s T).inv_mem (hBs b.2)) (hBs b'.2)
    have h1 : (b : G)⁻¹ * b' ∈ T ⊓ conjSubgroup s T := ⟨hmem, hBm⟩
    rw [hinfT, Subgroup.mem_bot] at h1
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  have hle := Nat.card_le_card_of_injective Ψ hinj
  have hW : Nat.card {a : Fin n → GaloisField 2 m // fδ a = 0 ∧ fz a = 0} =
      Nat.card (GaloisField 2 m) ^ (n - 2) := natCard_ker_pair hind
  have hm0 : m ≠ 0 := by
    have := hc.one_le_m
    omega
  have hq : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
  rw [hcard, hW, hq] at hle
  have h2m : 1 < 2 ^ m := Nat.one_lt_two_pow hm0
  have hlt : (2 ^ m) ^ (n - 2) < (2 ^ m) ^ (n - 1) := Nat.pow_lt_pow_right h2m (by omega)
  omega

end Core

end CFSG.CGT.Timmesfeld75
