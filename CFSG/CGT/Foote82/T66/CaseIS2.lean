module

public import CFSG.CGT.Foote82.T66.CaseIS
import CFSG.GH74.Uniqueness.SU.SU10Fusion
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

section Theta

variable {θ : ↥(NN G L) →* Perm (Fin (m + 6))}

theorem Hyp.mem_K_of_theta (h : Hyp G L z v H₁ m ψ)
    (hθ1 : ∀ x : ↥(NN G L), θ x = 1 ↔ ∀ a, (x : GLV V) * jL ψ a = jL ψ a * x)
    (x : ↥(NN G L)) (hx : θ x = 1) : (x : GLV V) ∈ KK G L := by
  refine ⟨x.2.1, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
  rw [← h.range_jL] at hl
  obtain ⟨a, rfl⟩ := hl
  exact ((hθ1 x).1 hx a).symm

theorem Hyp.theta_of_mem_K (h : Hyp G L z v H₁ m ψ)
    (hθ1 : ∀ x : ↥(NN G L), θ x = 1 ↔ ∀ a, (x : GLV V) * jL ψ a = jL ψ a * x)
    (x : ↥(NN G L)) (hx : (x : GLV V) ∈ KK G L) : θ x = 1 :=
  (hθ1 x).2 fun a => (Subgroup.mem_centralizer_iff.1 hx.2 _ (h.jL_mem a)).symm

theorem Hyp.jL_mem_N (h : Hyp G L z v H₁ m ψ) (a : alternatingGroup (Fin (m + 6))) :
    jL ψ a ∈ NN G L := h.L_le_N (h.jL_mem a)

theorem theta_jL
    (hθ3 : ∀ (x : ↥(NN G L)) (σ : Perm (Fin (m + 6))),
      (x : GLV V) = pe ψ (iota2 (m + 6) σ) → θ x = σ)
    (a : alternatingGroup (Fin (m + 6))) (hx : jL ψ a ∈ NN G L) :
    θ ⟨jL ψ a, hx⟩ = a := hθ3 _ _ rfl

end Theta

variable {S : Subgroup (GLV V)}

theorem SBad.embed (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) {hh : GLV V} (hhG : hh ∈ G)
    (hht : hh * z * hh⁻¹ = tt ψ) (θ : ↥(NN G L) →* Perm (Fin (m + 6)))
    (hθ1 : ∀ x : ↥(NN G L), θ x = 1 ↔ ∀ a, (x : GLV V) * jL ψ a = jL ψ a * x) :
    ∃ φ : ↥S →* Perm (Fin (m + 6)), Function.Injective φ ∧
      ∀ s : ↥S, φ s = θ ⟨hh⁻¹ * s * hh, hS.conj_mem_N h hhG hht s.2⟩ := by
  let f : ↥S →* ↥(NN G L) :=
    { toFun := fun s => ⟨hh⁻¹ * s * hh, hS.conj_mem_N h hhG hht s.2⟩
      map_one' := Subtype.ext (by
        show hh⁻¹ * ((1 : ↥S) : GLV V) * hh = 1
        simp)
      map_mul' := fun a b => Subtype.ext (by
        show hh⁻¹ * ((a : GLV V) * b) * hh = (hh⁻¹ * a * hh) * (hh⁻¹ * b * hh)
        group) }
  refine ⟨θ.comp f, ?_, fun s => rfl⟩
  rw [injective_iff_map_eq_one]
  intro s hs
  have hK := h.mem_K_of_theta hθ1 (f s) hs
  exact Subtype.ext (hS.eq_one_of_conj_mem_K h hhG hht s.2 hK)

theorem SBad.image_uniq (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S)
    {φ : ↥S →* Perm (Fin (m + 6))} (hφ : Function.Injective φ) :
    IsPGroup 2 φ.range ∧ orderOf (φ ⟨z, hS.z_mem⟩) = 2 ∧
      ∀ x ∈ φ.range, orderOf x = 2 → x = φ ⟨z, hS.z_mem⟩ := by
  refine ⟨hS.isP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective, ?_, ?_⟩
  · rw [orderOf_injective φ hφ, Subgroup.orderOf_mk]; exact h.std.orderOf_s
  · rintro _ ⟨s, rfl⟩ hs2
    rw [orderOf_injective φ hφ] at hs2
    congr 1
    exact Subtype.ext (hS.uniq h s.2 (by rw [Subgroup.orderOf_coe]; exact hs2))

theorem SBad.card_le (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) : Nat.card S ≤ m + 6 := by
  obtain ⟨θ, -, hθ1, -⟩ := h.exists_thetaL
  obtain ⟨hh, hhG, hht⟩ := hS.exists_hh h
  obtain ⟨φ, hφ, -⟩ := hS.embed h hhG hht θ hθ1
  obtain ⟨hQ2, hz2, huniq⟩ := hS.image_uniq h hφ
  have := card_le_of_unique_involution hQ2 hz2 huniq
  rw [Fintype.card_fin, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at this
  exact this

theorem SBad.exists_gen (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) (h4 : Nat.card S = 4) :
    ∃ s ∈ S, orderOf s = 4 ∧ s * s = z ∧ ∀ x ∈ S, x ∈ Subgroup.zpowers s := by
  classical
  obtain ⟨s, hsS, hs1, hsz⟩ : ∃ s ∈ S, s ≠ 1 ∧ s ≠ z := by
    by_contra hc
    push Not at hc
    have hle : Nat.card S ≤ 2 := by
      have hsub : ∀ x : ↥S, (x : GLV V) ∈ ({1, z} : Finset (GLV V)) := by
        intro x
        by_cases hx1 : (x : GLV V) = 1
        · simp [hx1]
        · simp [hc x x.2 hx1]
      have := Nat.card_le_card_of_injective
        (fun x : ↥S => (⟨x, hsub x⟩ : ({1, z} : Finset (GLV V))))
        (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
      refine this.trans ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact Finset.card_le_two
    omega
  have hdvd : orderOf s ∣ 4 := by
    have := Subgroup.orderOf_dvd_natCard S hsS
    rwa [h4] at this
  have hs4 : orderOf s = 4 := by
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf s ∣ 2 ^ 2 from hdvd)
    interval_cases j
    · exact absurd (orderOf_eq_one_iff.1 (by simpa using hj')) hs1
    · exact absurd (hS.uniq h hsS (by simpa using hj')) hsz
    · simpa using hj'
  refine ⟨s, hsS, hs4, ?_, ?_⟩
  · have hmem : s * s ∈ S := S.mul_mem hsS hsS
    refine hS.uniq h hmem ?_
    rw [← sq, orderOf_pow' s (by norm_num), hs4]
    norm_num
  · have hle : Subgroup.zpowers s ≤ S := Subgroup.zpowers_le.2 hsS
    have heq : Subgroup.zpowers s = S := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, hs4, h4])
    intro x hx
    rw [heq]
    exact hx

theorem eq_of_mem_zpowers_four {Γ : Type*} [Group Γ] {s x : Γ} (hs : orderOf s = 4)
    (hx : x ∈ Subgroup.zpowers s) : x = 1 ∨ x = s ∨ x = s * s ∨ x = s⁻¹ := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h4 : (orderOf s : ℤ) = 4 := by rw [hs]; rfl
  have hred : s ^ i = s ^ (i % 4) := by rw [← h4, zpow_mod_orderOf]
  have hs4 : s ^ (4 : ℕ) = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hlt : 0 ≤ i % 4 ∧ i % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num)⟩
  have hcases : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rw [hred]
  rcases hcases with h0 | h0 | h0 | h0 <;> rw [h0]
  · left; exact zpow_zero s
  · right; left; exact zpow_one s
  · right; right; left
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, sq]
  · right; right; right
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hs4

theorem SBad.y_inv (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) {s : GLV V} (hsS : s ∈ S)
    (hs4 : orderOf s = 4) (hgen : ∀ x ∈ S, x ∈ Subgroup.zpowers s) :
    yy ψ * s * (yy ψ)⁻¹ = s⁻¹ := by
  set u := yy ψ * s * (yy ψ)⁻¹ with hu
  have huS : u ∈ S := hS.y_norm s hsS
  have hu4 : orderOf u = 4 := by
    rw [hu, show yy ψ * s * (yy ψ)⁻¹ = (MulAut.conj (yy ψ)).toMonoidHom s from rfl,
      orderOf_injective _ (MulAut.conj (yy ψ)).injective, hs4]
  rcases eq_of_mem_zpowers_four hs4 (hgen u huS) with h1 | h1 | h1 | h1
  · rw [h1, orderOf_one] at hu4; exact absurd hu4 (by norm_num)
  · exfalso
    obtain ⟨r, hrS, hr⟩ := hS.exists_not_comm h
    apply hr
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen r hrS)
    have hc : s * yy ψ = yy ψ * s := by
      calc s * yy ψ = (yy ψ * s * (yy ψ)⁻¹) * yy ψ := by rw [← hu, h1]
        _ = yy ψ * s := by group
    exact ((Commute.zpow_left (show Commute s (yy ψ) from hc) i)).eq
  · have : orderOf (s * s) = 2 := by rw [← sq, orderOf_pow' s (by norm_num), hs4]; norm_num
    rw [h1, this] at hu4; exact absurd hu4 (by norm_num)
  · exact h1

theorem SBad.sign_eq_one (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) (h4 : Nat.card S = 4)
    {θ : ↥(NN G L) →* Perm (Fin (m + 6))}
    (hθ1 : ∀ x : ↥(NN G L), θ x = 1 ↔ ∀ a, (x : GLV V) * jL ψ a = jL ψ a * x)
    (hθ3 : ∀ (x : ↥(NN G L)) (σ : Perm (Fin (m + 6))),
      (x : GLV V) = pe ψ (iota2 (m + 6) σ) → θ x = σ)
    (x : ↥(NN G L)) (hxS : ∀ s ∈ S, (x : GLV V) * s = s * x) {k : ℕ}
    (hx2 : (x : GLV V) ^ (2 ^ k) = 1) : sign (θ x) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hsS, hs4, hss, hgen⟩ := hS.exists_gen h h4
  have hys := hS.y_inv h hsS hs4 hgen
  by_contra hodd
  have hodd' : sign (θ x) = -1 := by
    rcases Int.units_eq_one_or (sign (θ x)) with h1 | h1
    · exact absurd h1 hodd
    · exact h1
  set yN : ↥(NN G L) := ⟨yy ψ, h.yy_mem_N⟩ with hyN
  have hθy : θ yN = swap 0 1 := hθ3 yN _ yy_eq_pe_iota2
  set σ : Perm (Fin (m + 6)) := θ x * swap 0 1 with hσ
  have hσA : σ ∈ alternatingGroup (Fin (m + 6)) := by
    rw [Equiv.Perm.mem_alternatingGroup, hσ, map_mul, hodd', sign_swap ne01']; rfl
  set ℓN : ↥(NN G L) := ⟨jL ψ ⟨σ, hσA⟩, h.jL_mem_N _⟩ with hℓN
  have hθℓ : θ ℓN = σ := theta_jL hθ3 _ _
  set kN : ↥(NN G L) := ℓN⁻¹ * x * yN with hkN
  have hθk : θ kN = 1 := by
    rw [hkN, map_mul, map_mul, map_inv, hθℓ, hθy, hσ, mul_inv_rev, swap_inv]
    simp only [mul_assoc, inv_mul_cancel_left, swap_mul_self]
  set kk : GLV V := (kN : GLV V) with hkk
  have hkK : kk ∈ KK G L := h.mem_K_of_theta hθ1 kN hθk
  have hyy : yy ψ * yy ψ = 1 := mul_self_of_orderOf_two h.yy_orderOf
  have hℓs : (ℓN : GLV V) * s = s * ℓN :=
    (Subgroup.mem_centralizer_iff.1 (hS.le hsS).2 _ (h.jL_mem _))
  have hxeq : (x : GLV V) = ℓN * kk * yy ψ := by
    rw [hkk, hkN]
    show (x : GLV V) = ℓN * ((ℓN : GLV V)⁻¹ * x * yy ψ) * yy ψ
    calc (x : GLV V) = (x : GLV V) * (yy ψ * yy ψ) := by rw [hyy, mul_one]
      _ = ℓN * ((ℓN : GLV V)⁻¹ * x * yy ψ) * yy ψ := by group
  have hks : kk * s * kk⁻¹ = s⁻¹ := by
    have h1 := hxS s hsS
    rw [hxeq] at h1
    have h2 : kk * (yy ψ * s * (yy ψ)⁻¹) * kk⁻¹ = s := by
      have e : (ℓN : GLV V) * (kk * (yy ψ * s * (yy ψ)⁻¹) * kk⁻¹) =
          (ℓN : GLV V) * s := by
        calc (ℓN : GLV V) * (kk * (yy ψ * s * (yy ψ)⁻¹) * kk⁻¹)
            = (ℓN * kk * yy ψ * s) * (yy ψ)⁻¹ * kk⁻¹ := by group
          _ = (s * (ℓN * kk * yy ψ)) * (yy ψ)⁻¹ * kk⁻¹ := by rw [h1]
          _ = s * ℓN := by group
          _ = ℓN * s := hℓs.symm
      exact mul_left_cancel e
    rw [hys] at h2
    calc kk * s * kk⁻¹ = (kk * s⁻¹ * kk⁻¹)⁻¹ := by group
      _ = s⁻¹ := by rw [h2]
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos kk).ne'
  obtain ⟨c, rfl⟩ := hb
  obtain ⟨k', hk'⟩ : ∃ k', k' = kk ^ (2 * c + 1) := ⟨_, rfl⟩
  have hk'2 : k' ^ (2 ^ a) = 1 := by
    rw [hk', ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  have hk2s : kk ^ 2 * s * (kk ^ 2)⁻¹ = s := by
    calc kk ^ 2 * s * (kk ^ 2)⁻¹ = kk * (kk * s * kk⁻¹) * kk⁻¹ := by rw [sq]; group
      _ = kk * s⁻¹ * kk⁻¹ := by rw [hks]
      _ = (kk * s * kk⁻¹)⁻¹ := by group
      _ = s := by rw [hks, inv_inv]
  have hc2 : ∀ c' : ℕ, (kk ^ 2) ^ c' * s * ((kk ^ 2) ^ c')⁻¹ = s := by
    intro c'
    induction c' with
    | zero => simp
    | succ c' ih =>
      calc (kk ^ 2) ^ (c' + 1) * s * ((kk ^ 2) ^ (c' + 1))⁻¹
          = (kk ^ 2) ^ c' * (kk ^ 2 * s * (kk ^ 2)⁻¹) * ((kk ^ 2) ^ c')⁻¹ := by
            rw [pow_succ]; group
        _ = s := by rw [hk2s, ih]
  have hk's : k' * s * k'⁻¹ = s⁻¹ := by
    calc k' * s * k'⁻¹ = (kk ^ 2) ^ c * (kk * s * kk⁻¹) * ((kk ^ 2) ^ c)⁻¹ := by
          rw [hk', pow_succ, pow_mul]; group
      _ = ((kk ^ 2) ^ c * s * ((kk ^ 2) ^ c)⁻¹)⁻¹ := by rw [hks]; group
      _ = s⁻¹ := by rw [hc2]
  have hk'K : k' ∈ KK G L := by rw [hk']; exact (KK G L).pow_mem hkK _
  have hk'norm : Subgroup.zpowers k' ≤ Subgroup.normalizer (S : Set (GLV V)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    have h2 : k'⁻¹ * s * k' = s⁻¹ := by
      have e1 : s = k'⁻¹ * s⁻¹ * k' := by rw [← hk's]; group
      calc k'⁻¹ * s * k' = (k'⁻¹ * s⁻¹ * k')⁻¹ := by group
        _ = s⁻¹ := by rw [← e1]
    intro t
    constructor
    · intro ht
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen t ht)
      rw [← conj_zpow, hk's]
      exact S.zpow_mem (S.inv_mem hsS) i
    · intro ht
      have e : t = k'⁻¹ * (k' * t * k'⁻¹) * k' := by group
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hgen _ ht)
      rw [e, ← hi]
      have := conj_zpow (a := k'⁻¹) (b := s) (i := i)
      rw [inv_inv] at this
      rw [← this, h2]
      exact S.zpow_mem (S.inv_mem hsS) i
  have hk'p : IsPGroup 2 (Subgroup.zpowers k') := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨a, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk'2, one_zpow]
  have hbig : IsPGroup 2 (S ⊔ Subgroup.zpowers k' : Subgroup (GLV V)) :=
    IsPGroup.to_sup_of_normal_left' hS.isP hk'p hk'norm
  have hk'S : k' ∉ S := by
    intro hk'S
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen _ hk'S)
    have h1 : s ^ i * s * (s ^ i)⁻¹ = s := by group
    rw [hk's] at h1
    have h2 : s * s = 1 := by
      calc s * s = s * s⁻¹⁻¹ := by rw [inv_inv]
        _ = 1 := by rw [h1, mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one (show s ^ 2 = 1 by rw [sq]; exact h2)
    rw [hs4] at this
    exact absurd this (by norm_num)
  have hlt : S < S ⊔ Subgroup.zpowers k' := lt_of_le_of_ne le_sup_left fun he =>
    hk'S (he ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers k'))
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := hS.max _ (sup_le hS.le (Subgroup.zpowers_le.2 hk'K)) hbig
  omega

theorem Hyp.eq_z_of_mem (h : Hyp G L z v H₁ m ψ) {Q : Subgroup (GLV V)} (hQK : Q ≤ KK G L)
    (hQ : IsPGroup 2 Q) (hzQ : z ∈ Q) {a : GLV V} (ha : a ∈ Q) (ha2 : orderOf a = 2) : a = z :=
  CFSG.GH74.Uniqueness.SU.SU10.eq_of_orderOf_two_of_pRank_le_one hQ
    ((CFSG.SectionRank.pRank_mono Nat.one_lt_two hQK).trans h.rank.le) ha hzQ ha2
    h.std.orderOf_s

theorem mem_map_conj {g x : GLV V} {Q : Subgroup (GLV V)} :
    x ∈ Q.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem SBad.exists_comm_conj (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S)
    (h4 : Nat.card S = 4) {θ : ↥(NN G L) →* Perm (Fin (m + 6))}
    (hθ : ∀ (x : ↥(NN G L)) a,
      (x : GLV V) * jL ψ a * (x : GLV V)⁻¹ = jL ψ (CaseIAut.conjA (θ x) a))
    (hθ1 : ∀ x : ↥(NN G L), θ x = 1 ↔ ∀ a, (x : GLV V) * jL ψ a = jL ψ a * x)
    (hθ3 : ∀ (x : ↥(NN G L)) (σ : Perm (Fin (m + 6))),
      (x : GLV V) = pe ψ (iota2 (m + 6) σ) → θ x = σ)
    {hh : GLV V} (hhG : hh ∈ G) (hht : hh * z * hh⁻¹ = tt ψ) :
    ∃ c ∈ KK G L, (hh * c) * z * (hh * c)⁻¹ = tt ψ ∧
      ∀ s ∈ S, ∀ s' ∈ S,
        ((hh * c)⁻¹ * s * (hh * c)) * s' = s' * ((hh * c)⁻¹ * s * (hh * c)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hsS, hs4, hss, hgen⟩ := hS.exists_gen h h4
  have hz2 := h.std.orderOf_s
  have hzz : z * z = 1 := mul_self_of_orderOf_two hz2
  set Sc : Subgroup (GLV V) := S.map (MulAut.conj hh⁻¹).toMonoidHom with hSc
  have hmemSc : ∀ x, x ∈ Sc ↔ hh * x * hh⁻¹ ∈ S := fun x => by
    rw [hSc, mem_map_conj, inv_inv]
  have hScN : ∀ r ∈ Sc, r ∈ NN G L := by
    intro r hr
    have := hS.conj_mem_N h hhG hht ((hmemSc r).1 hr)
    simpa [mul_assoc] using this
  have hSc2 : IsPGroup 2 Sc := hS.isP.map _
  have hzt : z = hh⁻¹ * tt ψ * hh := by rw [← hht]; group
  have hScz : ∀ r ∈ Sc, r * z = z * r := by
    intro r hr
    have hs' := (hmemSc r).1 hr
    have hst : (hh * r * hh⁻¹) * tt ψ = tt ψ * (hh * r * hh⁻¹) :=
      (Subgroup.mem_centralizer_iff.1 (hS.le hs').2 _ h.tt_mem_L).symm
    rw [hzt]
    calc r * (hh⁻¹ * tt ψ * hh) = hh⁻¹ * ((hh * r * hh⁻¹) * tt ψ) * hh := by group
      _ = hh⁻¹ * (tt ψ * (hh * r * hh⁻¹)) * hh := by rw [hst]
      _ = hh⁻¹ * tt ψ * hh * r := by group
  set R : Subgroup (GLV V) := Sc ⊔ Subgroup.zpowers z with hR
  have hR2 : IsPGroup 2 R := by
    refine IsPGroup.to_sup_of_normal_right' hSc2
      (isPGroup_zpowers_of_mul_self hzz) ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (show Commute z r from (hScz r hr).symm) k)).eq
  have hRN : R ≤ Subgroup.normalizer ((KK G L : Subgroup (GLV V)) : Set (GLV V)) :=
    sup_le (fun r hr => h.N_le_normalizer_K (hScN r hr))
      (Subgroup.zpowers_le.2 (h.N_le_normalizer_K h.z_mem_N))
  obtain ⟨S₁, hS₁K, hS₁2, hRS₁, hnorm₁, hmax₁⟩ := exists_max_normalized (KK G L) R hR2 hRN
  have hzS₁ : z ∈ S₁ := hRS₁ ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers z), h.z_mem_K⟩
  have huniq₁ : ∀ a ∈ S₁, orderOf a = 2 → a = z := fun a ha ha2 =>
    h.eq_z_of_mem hS₁K hS₁2 hzS₁ ha ha2
  have hcomm₁ : ∀ x ∈ S₁, x * z = z * x := by
    intro x hx
    have hmem : x * z * x⁻¹ ∈ S₁ := S₁.mul_mem (S₁.mul_mem hx hzS₁) (S₁.inv_mem hx)
    have hord : orderOf (x * z * x⁻¹) = 2 := by
      rw [show x * z * x⁻¹ = (MulAut.conj x).toMonoidHom z from rfl,
        orderOf_injective _ (MulAut.conj x).injective]
      exact hz2
    have := huniq₁ _ hmem hord
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [this]
  obtain ⟨c, hcK, hc⟩ := exists_conj_of_max hS.le hS.isP hS.max hS₁K hS₁2 hmax₁
  set z' : GLV V := hh⁻¹ * z * hh with hz'
  have hz'Sc : z' ∈ Sc := (hmemSc z').2 (by rw [hz']; simpa [mul_assoc] using hS.z_mem)
  have hz'N : z' ∈ NN G L := hScN z' hz'Sc
  have hz'z' : z' * z' = 1 := by
    rw [hz']
    calc hh⁻¹ * z * hh * (hh⁻¹ * z * hh) = hh⁻¹ * (z * z) * hh := by group
      _ = 1 := by rw [hzz]; group
  set sN : ↥(NN G L) := ⟨hh⁻¹ * s * hh, hS.conj_mem_N h hhG hht hsS⟩ with hsN
  have hz'sq : (⟨z', hz'N⟩ : ↥(NN G L)) = sN * sN := Subtype.ext (by
    show hh⁻¹ * z * hh = hh⁻¹ * s * hh * (hh⁻¹ * s * hh)
    rw [← hss]; group)
  set τ := θ ⟨z', hz'N⟩ with hτ
  have hτA : τ ∈ alternatingGroup (Fin (m + 6)) := by
    rw [Equiv.Perm.mem_alternatingGroup, hτ, hz'sq, map_mul, map_mul]
    rcases Int.units_eq_one_or (sign (θ sN)) with h1 | h1 <;> rw [h1] <;> rfl
  set ℓ : GLV V := jL ψ ⟨τ, hτA⟩ with hℓ
  have hℓN : ℓ ∈ NN G L := h.jL_mem_N _
  have hθℓ : θ ⟨ℓ, hℓN⟩ = τ := theta_jL hθ3 _ _
  have hℓz' : z' * ℓ = ℓ * z' := by
    have h1 := hθ ⟨z', hz'N⟩ ⟨τ, hτA⟩
    have h2 : CaseIAut.conjA (θ ⟨z', hz'N⟩) ⟨τ, hτA⟩ = ⟨τ, hτA⟩ :=
      Subtype.ext (by rw [CaseIAut.coe_conjA, ← hτ]; group)
    rw [h2] at h1
    calc z' * ℓ = z' * ℓ * z'⁻¹ * z' := by group
      _ = ℓ * z' := by rw [show z' * ℓ * z'⁻¹ = ℓ from h1]
  have hℓℓ : ℓ * ℓ = 1 := by
    have hτ2 : τ * τ = 1 := by
      rw [hτ, ← map_mul, show (⟨z', hz'N⟩ : ↥(NN G L)) * ⟨z', hz'N⟩ = 1 from
        Subtype.ext hz'z', map_one]
    rw [hℓ, ← map_mul]
    have : (⟨τ, hτA⟩ : alternatingGroup (Fin (m + 6))) * ⟨τ, hτA⟩ = 1 := Subtype.ext hτ2
    rw [this, map_one]
  set k : GLV V := ℓ⁻¹ * z' with hk
  have hkK : k ∈ KK G L := by
    have hθk : θ (⟨ℓ, hℓN⟩⁻¹ * ⟨z', hz'N⟩) = 1 := by
      rw [map_mul, map_inv, hθℓ, ← hτ, inv_mul_cancel]
    exact h.mem_K_of_theta hθ1 _ hθk
  have hkk : k * k = 1 := by
    rw [hk]
    have hℓinv : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right hℓℓ
    rw [hℓinv]
    calc ℓ * z' * (ℓ * z') = ℓ * (z' * ℓ) * z' := by group
      _ = ℓ * (ℓ * z') * z' := by rw [hℓz']
      _ = (ℓ * ℓ) * (z' * z') := by group
      _ = 1 := by rw [hℓℓ, hz'z', one_mul]
  have hℓS₁ : ∀ x ∈ S₁, ℓ * x = x * ℓ := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (hS₁K hx).2 _ (h.jL_mem _))
  have hz'R : z' ∈ R := Subgroup.mem_sup_left hz'Sc
  have hknorm : ∀ x ∈ S₁, k * x * k⁻¹ ∈ S₁ := by
    intro x hx
    have h1 : z' * x * z'⁻¹ ∈ S₁ := hnorm₁ z' hz'R x hx
    have e : k * x * k⁻¹ = ℓ⁻¹ * (z' * x * z'⁻¹) * ℓ := by rw [hk]; group
    rw [e, show ℓ⁻¹ * (z' * x * z'⁻¹) * ℓ = z' * x * z'⁻¹ by
      rw [mul_assoc, (hℓS₁ _ h1).symm, inv_mul_cancel_left]]
    exact h1
  have hkS₁ : k ∈ S₁ := by
    by_contra hkS
    have hp : IsPGroup 2 (Subgroup.zpowers k) := isPGroup_zpowers_of_mul_self hkk
    have hnk : Subgroup.zpowers k ≤ Subgroup.normalizer (S₁ : Set (GLV V)) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro x
      have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hkk
      constructor
      · exact hknorm x
      · intro hx
        have := hknorm _ hx
        have e : k * (k * x * k⁻¹) * k⁻¹ = x := by
          rw [hkinv]
          calc k * (k * x * k) * k = (k * k) * x * (k * k) := by group
            _ = x := by rw [hkk]; group
        rwa [e] at this
    have hbig : IsPGroup 2 (S₁ ⊔ Subgroup.zpowers k : Subgroup (GLV V)) :=
      IsPGroup.to_sup_of_normal_left' hS₁2 hp hnk
    have hlt : S₁ < S₁ ⊔ Subgroup.zpowers k := lt_of_le_of_ne le_sup_left fun he =>
      hkS (he ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers k))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := hmax₁ _ (sup_le hS₁K (Subgroup.zpowers_le.2 hkK)) hbig
    omega
  have hkc : ∀ x ∈ S₁, k * x = x * k := by
    intro x hx
    by_cases hk1 : k = 1
    · rw [hk1, one_mul, mul_one]
    · have hk2 : orderOf k = 2 := orderOf_eq_prime (by rw [sq]; exact hkk) hk1
      rw [huniq₁ k hkS₁ hk2]
      exact (hcomm₁ x hx).symm
  have hz'S₁ : ∀ x ∈ S₁, z' * x = x * z' := by
    intro x hx
    have e : z' = ℓ * k := by rw [hk]; group
    rw [e]
    calc ℓ * k * x = ℓ * (k * x) := by group
      _ = ℓ * (x * k) := by rw [hkc x hx]
      _ = (ℓ * x) * k := by group
      _ = (x * ℓ) * k := by rw [hℓS₁ x hx]
      _ = x * (ℓ * k) := by group
  have hnotN : hh⁻¹ ∉ Subgroup.normalizer (L : Set (GLV V)) := fun hN =>
    h.hh_not_mem_N hhG hht (by simpa using Subgroup.inv_mem _ hN)
  have hodd := h.std.tight hh⁻¹ (G.inv_mem hhG) hnotN
  have hRS₁c : ∀ r ∈ Sc, ∀ x ∈ S₁, r * x = x * r := by
    intro r hr x hx
    set c₀ := r * x * r⁻¹ * x⁻¹ with hc₀
    have hc₀S₁ : c₀ ∈ S₁ :=
      S₁.mul_mem (hnorm₁ r (Subgroup.mem_sup_left hr) x hx) (S₁.inv_mem hx)
    have hxG : x ∈ G := (hS₁K hx).1
    have hx₀ : hh * x * hh⁻¹ ∈ NN G L := by
      refine h.centralizer_z_le (G.mul_mem (G.mul_mem hhG hxG) (G.inv_mem hhG)) ?_
      have := hz'S₁ x hx
      rw [hz'] at this
      calc hh * x * hh⁻¹ * z = hh * (x * (hh⁻¹ * z * hh)) * hh⁻¹ := by group
        _ = hh * ((hh⁻¹ * z * hh) * x) * hh⁻¹ := by rw [this]
        _ = z * (hh * x * hh⁻¹) := by group
    have hs₀ : hh * r * hh⁻¹ ∈ KK G L := hS.le ((hmemSc r).1 hr)
    have hc₀K' : hh * c₀ * hh⁻¹ ∈ KK G L := by
      have e : hh * c₀ * hh⁻¹ = (hh * r * hh⁻¹) *
          ((hh * x * hh⁻¹) * (hh * r * hh⁻¹)⁻¹ * (hh * x * hh⁻¹)⁻¹) := by rw [hc₀]; group
      rw [e]
      refine (KK G L).mul_mem hs₀ ?_
      exact (Subgroup.mem_normalizer_iff.1 (h.N_le_normalizer_K hx₀) _).1
        ((KK G L).inv_mem hs₀)
    have hmem : c₀ ∈ KK G L ⊓ (KK G L).map (MulAut.conj hh⁻¹).toMonoidHom :=
      ⟨hS₁K hc₀S₁, mem_map_conj.2 (by rwa [inv_inv])⟩
    have h1 := eq_one_of_isPGroup_of_odd hS₁2 hodd hc₀S₁ hmem
    rw [hc₀] at h1
    calc r * x = r * x * r⁻¹ * x⁻¹ * (x * r) := by group
      _ = x * r := by rw [h1, one_mul]
  refine ⟨c, hcK, ?_, ?_⟩
  · have hczS₁ : c * z * c⁻¹ ∈ S₁ := (hc _).2 (by simpa [mul_assoc] using hS.z_mem)
    have hord : orderOf (c * z * c⁻¹) = 2 := by
      rw [show c * z * c⁻¹ = (MulAut.conj c).toMonoidHom z from rfl,
        orderOf_injective _ (MulAut.conj c).injective]
      exact hz2
    have e := huniq₁ _ hczS₁ hord
    calc hh * c * z * (hh * c)⁻¹ = hh * (c * z * c⁻¹) * hh⁻¹ := by group
      _ = tt ψ := by rw [e, hht]
  · intro s₁ hs₁ s' hs'
    have hr : hh⁻¹ * s₁ * hh ∈ Sc := (hmemSc _).2 (by simpa [mul_assoc] using hs₁)
    have hx : c * s' * c⁻¹ ∈ S₁ := (hc _).2 (by simpa [mul_assoc] using hs')
    have h1 := hRS₁c _ hr _ hx
    calc (hh * c)⁻¹ * s₁ * (hh * c) * s' =
        c⁻¹ * ((hh⁻¹ * s₁ * hh) * (c * s' * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * s' * c⁻¹) * (hh⁻¹ * s₁ * hh)) * c := by rw [h1]
      _ = s' * ((hh * c)⁻¹ * s₁ * (hh * c)) := by group

end CaseIAux

end CFSG.CGT.Foote82
