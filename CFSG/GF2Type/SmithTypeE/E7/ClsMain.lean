module

public import CFSG.GF2Type.SmithTypeE.E7.ClsGeom
public import CFSG.GF2Type.SmithTypeE.DMod.Card

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod
open scoped Matrix

@[expose] def vv (A : M6) : Fin 6 → ZMod 2 := fun i => A i 5 + (if i = 5 then 1 else 0)

theorem vv_Tmat {v : Fin 6 → ZMod 2} : vv (Tmat v) = v := by
  funext i
  rw [vv, Tmat_apply]
  simp only [if_true]
  exact (by decide : ∀ a b : ZMod 2, a + b + a = b) _ _

theorem vec_dichotomy {S : Set ((Fin 6 → ZMod 2) × (Fin 6 → ZMod 2))}
    (hadd : ∀ p ∈ S, ∀ q ∈ S, p + q ∈ S)
    (h1 : ∀ p ∈ S, p.2 = 0 ∨ p.2 = p.1) :
    (∀ p ∈ S, p.2 = 0) ∨ (∀ p ∈ S, p.2 = p.1) := by
  by_cases hall : ∀ p ∈ S, p.2 = 0
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨p₁, hp₁, hne⟩ := hall
    have hp₁e : p₁.2 = p₁.1 := (h1 p₁ hp₁).resolve_left hne
    intro p hp
    rcases h1 p hp with h0 | h
    · by_cases h10 : p.1 = 0
      · rw [h0, h10]
      · exfalso
        rcases h1 (p + p₁) (hadd p hp p₁ hp₁) with h2 | h2
        · apply hne
          have : (p + p₁).2 = p.2 + p₁.2 := rfl
          rw [this, h0, zero_add] at h2
          exact h2
        · have e2 : (p + p₁).2 = p.2 + p₁.2 := rfl
          have e1 : (p + p₁).1 = p.1 + p₁.1 := rfl
          rw [e2, e1, h0, zero_add, hp₁e] at h2
          apply h10
          have h3 : p₁.1 = p.1 + p₁.1 := h2
          have h4 : p.1 + p₁.1 = 0 + p₁.1 := by rw [zero_add]; exact h3.symm
          exact add_right_cancel h4
    · exact h

section Cert

theorem nS_wedge_of_sq (x : Stab0) (hsq : x * x = 1) {v : Fin 6 → ZMod 2} (hv : v 5 = 0)
    (hA : ((alphaS x : GL6) : M6) = Tmat v) :
    ∀ i j, v i * nS x j 5 + nS x i 5 * v j = 0 := by
  have h1 : nS (x * x) = nS 1 := by rw [hsq]
  rw [nS_one, nS_mul, inv_eq_Tmat hv hA, Tmat_conj (nS_isAlt x) hv] at h1
  intro i j
  have h2 := congrFun (congrFun h1 i) j
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.zero_apply] at h2
  exact (by decide : ∀ a b : ZMod 2, a + b + a = 0 → b = 0) _ _ h2

theorem alphaS_nS_mul (x y : Stab0) {v w : Fin 6 → ZMod 2} (hv : v 5 = 0) (hw : w 5 = 0)
    (hA : ((alphaS x : GL6) : M6) = Tmat v) (hB : ((alphaS y : GL6) : M6) = Tmat w) :
    ((alphaS (x * y) : GL6) : M6) = Tmat (v + w) ∧
      ∀ i, nS (x * y) i 5 = nS x i 5 + nS y i 5 := by
  constructor
  · rw [map_mul, Units.val_mul, hA, hB, Tmat_mul hv hw]
  · intro i
    rw [nS_mul, inv_eq_Tmat hw hB, Tmat_conj (nS_isAlt x) hw]
    simp only [Matrix.add_apply, Matrix.of_apply]
    rw [(nS_isAlt x).2 5, hw]
    simp

theorem lemmaB_core (Xs : Subgroup ↥Stab0) (hsq : ∀ x ∈ Xs, x * x = 1)
    (hT : ∀ x ∈ Xs, InT ((alphaS x : GL6) : M6))
    (hN : ∀ x ∈ Xs, alphaS x = 1 → ∀ i, nS x i 5 = 0) :
    (∀ x ∈ Xs, ∀ i, nS x i 5 = 0) ∨
      (∀ x ∈ Xs, ∀ i, nS x i 5 = vv ((alphaS x : GL6) : M6) i) := by
  let S : Set ((Fin 6 → ZMod 2) × (Fin 6 → ZMod 2)) :=
    {p | ∃ x ∈ Xs, p = (vv ((alphaS x : GL6) : M6), fun i => nS x i 5)}
  have hA : ∀ x ∈ Xs, ((alphaS x : GL6) : M6) = Tmat (vv ((alphaS x : GL6) : M6)) ∧
      vv ((alphaS x : GL6) : M6) 5 = 0 := by
    intro x hx
    obtain ⟨v, hv5, hv⟩ := InT_iff.mp (hT x hx)
    rw [hv, vv_Tmat]
    exact ⟨rfl, hv5⟩
  have hadd : ∀ p ∈ S, ∀ q ∈ S, p + q ∈ S := by
    rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩
    refine ⟨x * y, Xs.mul_mem hx hy, ?_⟩
    obtain ⟨hAx, hv5⟩ := hA x hx
    obtain ⟨hAy, hw5⟩ := hA y hy
    obtain ⟨h1, h2⟩ := alphaS_nS_mul x y hv5 hw5 hAx hAy
    refine Prod.ext ?_ ?_
    · show vv _ + vv _ = vv _
      rw [h1, vv_Tmat]
    · funext i
      exact (h2 i).symm
  have h1 : ∀ p ∈ S, p.2 = 0 ∨ p.2 = p.1 := by
    rintro p ⟨x, hx, rfl⟩
    obtain ⟨hAx, hv5⟩ := hA x hx
    have hwedge := nS_wedge_of_sq x (hsq x hx) hv5 hAx
    rcases wedge_cases (v := vv ((alphaS x : GL6) : M6)) (h := fun j => nS x j 5) hwedge with
      hv0 | hh | hh
    · left
      have : alphaS x = 1 := Units.ext (by rw [hAx, hv0, Tmat_zero]; rfl)
      funext i
      exact hN x hx this i
    · left
      exact hh
    · right
      exact hh
  rcases vec_dichotomy hadd h1 with h | h
  · left
    intro x hx i
    exact congrFun (h _ ⟨x, hx, rfl⟩) i
  · right
    intro x hx i
    exact congrFun (h _ ⟨x, hx, rfl⟩) i

theorem kN_mul_self (N : M6) : kN N * kN N = 1 := by
  rw [kN_add, add_self_M6, kN_zero]

theorem conj_conj_inv (A : GL6) (M : M6) :
    ((A⁻¹ : GL6) : M6) * ((A : M6) * M * (A : M6)ᵀ) * ((A⁻¹ : GL6) : M6)ᵀ = M := by
  have h1 : ((A⁻¹ : GL6) : M6) * (A : M6) = 1 := Units.inv_mul A
  have h2 : (A : M6)ᵀ * ((A⁻¹ : GL6) : M6)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  calc ((A⁻¹ : GL6) : M6) * ((A : M6) * M * (A : M6)ᵀ) * ((A⁻¹ : GL6) : M6)ᵀ
      = (((A⁻¹ : GL6) : M6) * (A : M6)) * M * ((A : M6)ᵀ * ((A⁻¹ : GL6) : M6)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = M := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem sk_conj_kN (A : GL6) (N M : M6) :
    (sA A * kN N) * kN M * (sA A * kN N)⁻¹ = kN ((A : M6) * M * (A : M6)ᵀ) := by
  rw [mul_inv_eq_iff_eq_mul]
  have h1 : (sA A * kN N) * kN M = sA A * kN (N + M) := by rw [mul_assoc, kN_add]
  have h2 : kN ((A : M6) * M * (A : M6)ᵀ) * (sA A * kN N) = sA A * kN (M + N) := by
    rw [← mul_assoc, kN_mul_sA, conj_conj_inv, mul_assoc, kN_add]
  rw [h1, h2, add_comm]

@[expose] def NSub (Xs : Subgroup ↥Stab0) : AddSubgroup M6 where
  carrier := {N | IsAlt N ∧ ∃ y ∈ Xs, sig y.1 = kN N}
  add_mem' := by
    rintro N N' ⟨hN, y, hy, hyN⟩ ⟨hN', y', hy', hyN'⟩
    refine ⟨isAlt_add hN hN', y * y', Xs.mul_mem hy hy', ?_⟩
    show sig (y.1 * y'.1) = _
    rw [sig_mul, hyN, hyN', kN_add]
  zero_mem' := ⟨isAlt_zero, 1, Xs.one_mem, by
    show sig ((1 : Stab0) : TD6) = _
    rw [kN_zero]
    exact sig_one⟩
  neg_mem' := by
    rintro N ⟨hN, y, hy, hyN⟩
    exact ⟨isAlt_neg hN, y, hy, by rw [neg_eq_self_M6]; exact hyN⟩

theorem NSub_fixed {Xs : Subgroup ↥Stab0} (hab : ∀ x ∈ Xs, ∀ y ∈ Xs, x * y = y * x)
    {x : Stab0} (hx : x ∈ Xs) {N : M6} (hN : N ∈ NSub Xs) :
    ((alphaS x : GL6) : M6) * N * ((alphaS x : GL6) : M6)ᵀ = N := by
  obtain ⟨hNalt, y, hy, hyN⟩ := hN
  have hst : sig x.1 * sig y.1 = sig y.1 * sig x.1 := by
    rw [← sig_mul, ← sig_mul]
    exact congrArg (fun z : Stab0 => sig z.1) (hab x hx y hy)
  have hkF : FixesF (kN N) := fun b => by
    rw [kN_apply]
    simp
  have h1 := comm_AN (iso_sig x.1) (stab_F x.2) (iso_sig y.1) (by rw [hyN]; exact hkF) hst
  have hM : LinearMap.toMatrix' (Mlin (sig y.1)) = N := by
    refine Matrix.ext fun i j => ?_
    rw [LinearMap.toMatrix'_apply]
    show ent (sig y.1) i j = N i j
    rw [hyN, ent_kN]
  rw [hM] at h1
  exact h1

theorem NSub_comm_mem {Xs Ps : Subgroup ↥Stab0} (hPN : ∀ g ∈ Ps, ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs)
    (hK0P : ∀ k : Stab0, alphaS k = 1 → k ∈ Ps) {x : Stab0} (hx : x ∈ Xs) {M : M6}
    (hM : IsAlt M) :
    ((alphaS x : GL6) : M6) * M * ((alphaS x : GL6) : M6)ᵀ + M ∈ NSub Xs := by
  obtain ⟨k, hk, hkM⟩ := exists_K0_sig_kN hM
  let k' : Stab0 := ⟨k, K0_le_stab hk⟩
  have hk'1 : alphaS k' = 1 := (mem_K0_iff_alphaS k').mp hk
  have hk'P : k' ∈ Ps := hK0P k' hk'1
  have hc : x * k' * x⁻¹ * k'⁻¹ ∈ Xs := by
    have h1 : k' * x⁻¹ * k'⁻¹ ∈ Xs := hPN k' hk'P x⁻¹ (Xs.inv_mem hx)
    have h2 := Xs.mul_mem hx h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  refine ⟨isAlt_add (isAlt_conj hM _) hM, x * k' * x⁻¹ * k'⁻¹, hc, ?_⟩
  have hs : sig (x * k' * x⁻¹ * k'⁻¹ : Stab0).1 =
      sig x.1 * sig k * (sig x.1)⁻¹ * (sig k)⁻¹ := by
    have e : sig (x * k' * x⁻¹ * k'⁻¹ : Stab0).1 =
        sig x.1 * sig k * sig (x⁻¹ : Stab0).1 * sig (k'⁻¹ : Stab0).1 := by
      show sig (x.1 * k * x.1⁻¹ * k⁻¹) = _
      rw [sig_mul, sig_mul, sig_mul]
      rfl
    have e1 : sig (x⁻¹ : Stab0).1 = (sig x.1)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← sig_mul]
      show sig (x.1⁻¹ * x.1) = 1
      rw [inv_mul_cancel, sig_one]
    have e2 : sig (k'⁻¹ : Stab0).1 = (sig k)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← sig_mul]
      show sig (k⁻¹ * k) = 1
      rw [inv_mul_cancel, sig_one]
    rw [e, e1, e2]
  rw [hs, sig_eq_sA_kN x, hkM, sk_conj_kN]
  have hinv : (kN M)⁻¹ = kN M := inv_eq_of_mul_eq_one_right (kN_mul_self M)
  rw [hinv, kN_add]

@[expose] noncomputable def kerToNSub (Xs : Subgroup ↥Stab0)
    (y : ↥(alphaS.comp Xs.subtype).ker) : ↥(NSub Xs) :=
  ⟨nS y.1.1, nS_isAlt _, y.1.1, y.1.2, sig_eq_kN _ y.2⟩

theorem kerToNSub_bijective (Xs : Subgroup ↥Stab0) : Function.Bijective (kerToNSub Xs) := by
  constructor
  · intro y₁ y₂ h
    have h1 : nS y₁.1.1 = nS y₂.1.1 := congrArg (fun z : ↥(NSub Xs) => (z : M6)) h
    have h2 : sig y₁.1.1.1 = sig y₂.1.1.1 := by
      rw [sig_eq_kN y₁.1.1 y₁.2, sig_eq_kN y₂.1.1 y₂.2, h1]
    have h3 := sig_injective h2
    exact Subtype.ext (Subtype.ext (Subtype.ext h3))
  · rintro ⟨N, hNalt, y, hy, hyN⟩
    have h1 : sA (alphaS y) * kN (nS y) = sA 1 * kN N := by
      rw [← sig_eq_sA_kN y, hyN, sA_one, one_mul]
    obtain ⟨hy1, hyn⟩ := sk_inj h1
    have hker : (⟨y, hy⟩ : ↥Xs) ∈ (alphaS.comp Xs.subtype).ker := hy1
    exact ⟨⟨⟨y, hy⟩, hker⟩, Subtype.ext hyn⟩

theorem card_ker_eq_NSub (Xs : Subgroup ↥Stab0) :
    Nat.card ↥(alphaS.comp Xs.subtype).ker = Nat.card ↥(NSub Xs) :=
  Nat.card_congr (Equiv.ofBijective _ (kerToNSub_bijective Xs))

theorem card_Xs_eq (Xs : Subgroup ↥Stab0) :
    Nat.card ↥Xs = Nat.card ↥(alphaS.comp Xs.subtype).range * Nat.card ↥(NSub Xs) := by
  have h1 := Subgroup.card_mul_index (alphaS.comp Xs.subtype).ker
  rw [Subgroup.index_ker] at h1
  rw [← h1, card_ker_eq_NSub, mul_comm]

theorem lemmaB (Xs : Subgroup ↥Stab0) (hsq : ∀ x ∈ Xs, x * x = 1)
    (hcard : Nat.card ↥Xs = 2 ^ 15) (hT : ∀ x ∈ Xs, InT ((alphaS x : GL6) : M6))
    (hN : ∀ x ∈ Xs, alphaS x = 1 → ∀ i, nS x i 5 = 0) :
    Xs.map Stab0.subtype = UFix Wp ∨ Xs.map Stab0.subtype = UFix Cc := by
  have hmap : Nat.card ↥(Xs.map Stab0.subtype) = 2 ^ 15 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hcard]
  rcases lemmaB_core Xs hsq hT hN with h | h
  · left
    have hle : Xs.map Stab0.subtype ≤ UFix Wp := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨v, hv5, hAx⟩ := InT_iff.mp (hT x hx)
      exact (mem_UFix_Wp_iff x hv5 hAx).2 (h x hx)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hmap]; exact card_UFix_le Wp Wp_perp)
  · right
    have hle : Xs.map Stab0.subtype ≤ UFix Cc := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨v, hv5, hAx⟩ := InT_iff.mp (hT x hx)
      refine (mem_UFix_Cc_iff x hv5 hAx).2 fun i => ?_
      rw [h x hx i, hAx, vv_Tmat]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hmap]; exact card_UFix_le Cc Cc_perp)

theorem classification_normalized (Xs Ps : Subgroup ↥Stab0)
    (hsq : ∀ x ∈ Xs, x * x = 1) (hab : ∀ x ∈ Xs, ∀ y ∈ Xs, x * y = y * x)
    (hcard : Nat.card ↥Xs = 2 ^ 15) (hXP : Xs ≤ Ps)
    (hPN : ∀ g ∈ Ps, ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs)
    (hK0P : ∀ k : Stab0, alphaS k = 1 → k ∈ Ps)
    (hUT : ∀ g ∈ Ps, IsUT ((alphaS g : GL6) : M6))
    (hUTall : ∀ A : GL6, A ∈ UTsub → ∃ g ∈ Ps, alphaS g = A) :
    Xs.map Stab0.subtype = K0 ∨ Xs.map Stab0.subtype = UFix Wp ∨
      Xs.map Stab0.subtype = UFix Cc := by
  by_cases h1 : ∀ x ∈ Xs, alphaS x = 1
  · left
    have hle : Xs.map Stab0.subtype ≤ K0 := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_K0_iff_alphaS x).2 (h1 x hx)
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_K0, Subgroup.card_map_of_injective Subtype.val_injective, hcard])
  right
  push_neg at h1
  let 𝒜 : Subgroup GL6 := (alphaS.comp Xs.subtype).range
  have hmem𝒜 : ∀ A : GL6, A ∈ 𝒜 ↔ ∃ x ∈ Xs, alphaS x = A := by
    intro A
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨x₁, hx₁, hx₁τ⟩ := exists_tau0_mem hXP hPN hUT hUTall h1
  obtain ⟨hT𝒜, hN𝒩⟩ := lemmaA 𝒜
    (fun A hA => by
      obtain ⟨x, hx, rfl⟩ := (hmem𝒜 A).1 hA
      exact hUT x (hXP hx))
    (fun A hA => by
      obtain ⟨x, hx, rfl⟩ := (hmem𝒜 A).1 hA
      rw [← map_mul, hsq x hx, map_one])
    (fun A hA B hB => by
      obtain ⟨x, hx, rfl⟩ := (hmem𝒜 A).1 hA
      obtain ⟨y, hy, rfl⟩ := (hmem𝒜 B).1 hB
      rw [← map_mul, ← map_mul, hab x hx y hy])
    ⟨alphaS x₁, (hmem𝒜 _).2 ⟨x₁, hx₁, rfl⟩, hx₁τ⟩
    (NSub Xs) (fun N hN => hN.1)
    (fun A hA N hN => by
      obtain ⟨x, hx, rfl⟩ := (hmem𝒜 A).1 hA
      exact NSub_fixed hab hx hN)
    (fun A hA M hM => by
      obtain ⟨x, hx, rfl⟩ := (hmem𝒜 A).1 hA
      exact NSub_comm_mem hPN hK0P hx hM)
    (by
      have h := card_Xs_eq Xs
      rw [hcard] at h
      exact h.le)
  have hTx : ∀ x ∈ Xs, InT ((alphaS x : GL6) : M6) := fun x hx =>
    (hT𝒜 _).1 ((hmem𝒜 _).2 ⟨x, hx, rfl⟩)
  have hNx : ∀ x ∈ Xs, alphaS x = 1 → ∀ i, nS x i 5 = 0 := by
    intro x hx hx1 i
    have : nS x ∈ NSub Xs := ⟨nS_isAlt x, x, hx, sig_eq_kN x hx1⟩
    exact ((hN𝒩 _).1 this).2 i
  exact lemmaB Xs hsq hcard hTx hNx

theorem card_ker_alphaS (Ps : Subgroup ↥Stab0) (hK0 : K0 ≤ Ps.map Stab0.subtype) :
    Nat.card ↥(alphaS.comp Ps.subtype).ker = Nat.card ↥K0 := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => ⟨y.1.1.1, (mem_K0_iff_alphaS y.1.1).2 y.2⟩) ⟨?_, ?_⟩)
  · intro y₁ y₂ h
    have h' : y₁.1.1.1 = y₂.1.1.1 := congrArg (fun z : ↥K0 => (z : TD6)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext h'))
  · rintro ⟨g, hg⟩
    obtain ⟨y, hy, rfl⟩ := hK0 hg
    exact ⟨⟨⟨y, hy⟩, (mem_K0_iff_alphaS y).1 hg⟩, rfl⟩

theorem card_range_alphaS (Ps : Subgroup ↥Stab0) (hK0 : K0 ≤ Ps.map Stab0.subtype)
    (hcard : Nat.card ↥Ps = 2 ^ 30) : Nat.card ↥(alphaS.comp Ps.subtype).range = 2 ^ 15 := by
  have h1 := card_range_mul_card_ker (alphaS.comp Ps.subtype)
  rw [card_ker_alphaS Ps hK0, card_K0, hcard] at h1
  exact Nat.eq_of_mul_eq_mul_right (m := 2 ^ 15) (by norm_num) (by rw [← h1]; norm_num)

theorem exists_conj_eq_UTsub (S : Subgroup GL6) (hS : Nat.card ↥S = 2 ^ 15) :
    ∃ g : GL6, S.map (MulAut.conj g).toMonoidHom = UTsub := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_conj_isUT S (IsPGroup.of_card hS)
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact mem_UTsub.mpr (hg h hh)
  · rw [card_UTsub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hS]

theorem exists_normalization (P : Subgroup TD6) (hP : IsPGroup 2 P)
    (hmax : ∀ Q : Subgroup TD6, P ≤ Q → IsPGroup 2 Q → Q = P) (hcardP : Nat.card ↥P = 2 ^ 30) :
    ∃ c : TD6, P.map (MulAut.conj c).toMonoidHom ≤ Stab0 ∧
      K0 ≤ P.map (MulAut.conj c).toMonoidHom ∧
      (∀ g : Stab0, g.1 ∈ P.map (MulAut.conj c).toMonoidHom → IsUT ((alphaS g : GL6) : M6)) ∧
      (∀ A : GL6, A ∈ UTsub →
        ∃ g : Stab0, g.1 ∈ P.map (MulAut.conj c).toMonoidHom ∧ alphaS g = A) := by
  obtain ⟨i, hi⟩ := exists_fixed_plane P hP
  obtain ⟨g₀, hg₀⟩ := exists_smul_planes_eq i 0
  have hinv : g₀⁻¹ • (0 : Fin 75735) = i := by
    rw [inv_smul_eq_iff]
    exact hg₀.symm
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Subgroup TD6, P₁ = P.map (MulAut.conj g₀).toMonoidHom := ⟨_, rfl⟩
  have hP₁S : P₁ ≤ Stab0 := by
    rw [hP₁]
    rintro _ ⟨y, hy, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    show (g₀ * y * g₀⁻¹) • (0 : Fin 75735) = 0
    rw [mul_smul, mul_smul, hinv, hi y hy, hg₀]
  have hcard₁ : Nat.card ↥P₁ = 2 ^ 30 := by
    rw [hP₁, Subgroup.card_map_of_injective (MulAut.conj g₀).injective, hcardP]
  have hK0₁ : K0 ≤ P₁ := by
    have hP₁2 : IsPGroup 2 P₁ := by
      rw [hP₁]
      exact hP.map _
    have hmax₁ : ∀ Q : Subgroup TD6, P₁ ≤ Q → IsPGroup 2 Q → Q = P₁ := by
      rw [hP₁]
      exact isMax_map (MulAut.conj g₀) hmax
    exact le_of_normal_isPGroup_of_max K0_le_stab hP₁S (fun _ hg _ hn => K0_normal hg hn)
      isPGroup_K0 hP₁2 hmax₁
  obtain ⟨Ps₁, hPs₁⟩ : ∃ Ps₁ : Subgroup ↥Stab0, Ps₁ = P₁.subgroupOf Stab0 := ⟨_, rfl⟩
  have hPs₁map : Ps₁.map Stab0.subtype = P₁ := by
    rw [hPs₁]
    exact Subgroup.map_subgroupOf_eq_of_le hP₁S
  have hPs₁mem : ∀ x : Stab0, x ∈ Ps₁ ↔ x.1 ∈ P₁ := fun x => by
    rw [hPs₁]
    exact Subgroup.mem_subgroupOf
  have hcardPs₁ : Nat.card ↥Ps₁ = 2 ^ 30 := by
    rw [← hcard₁, ← hPs₁map, Subgroup.card_map_of_injective Subtype.val_injective]
  obtain ⟨S, hS⟩ : ∃ S : Subgroup GL6, S = (alphaS.comp Ps₁.subtype).range := ⟨_, rfl⟩
  have hcardS : Nat.card ↥S = 2 ^ 15 := by
    rw [hS]
    exact card_range_alphaS Ps₁ (by rw [hPs₁map]; exact hK0₁) hcardPs₁
  obtain ⟨g, hgS⟩ := exists_conj_eq_UTsub S hcardS
  obtain ⟨h, hh⟩ : ∃ h : Stab0, alphaS h = g := by
    obtain ⟨x, hx, hxg⟩ := exists_mem_stab0_Ablk_eq g
    exact ⟨⟨x, hx⟩, Units.ext hxg⟩
  have hmemS : ∀ x : Stab0, x.1 ∈ P₁ → alphaS x ∈ S := fun x hx => by
    rw [hS]
    exact ⟨⟨x, (hPs₁mem x).2 hx⟩, rfl⟩
  have hPc : P.map (MulAut.conj (h.1 * g₀)).toMonoidHom = P₁.map (MulAut.conj h.1).toMonoidHom := by
    rw [map_conj_mul_gen, hP₁]
  refine ⟨h.1 * g₀, ?_, ?_, ?_, ?_⟩
  · rw [hPc]
    rintro _ ⟨x, hx, rfl⟩
    exact Stab0.mul_mem (Stab0.mul_mem h.2 (hP₁S hx)) (Stab0.inv_mem h.2)
  · rw [hPc]
    intro k hk
    refine ⟨h.1⁻¹ * k * h.1, hK0₁ (K0_normal (Stab0.inv_mem h.2) hk), ?_⟩
    show h.1 * (h.1⁻¹ * k * h.1) * h.1⁻¹ = k
    group
  · rw [hPc]
    intro g' hg'
    obtain ⟨x, hx, hxg'⟩ := hg'
    have hxS : x ∈ Stab0 := hP₁S hx
    have e : g' = h * ⟨x, hxS⟩ * h⁻¹ := Subtype.ext hxg'.symm
    have hmem : alphaS g' ∈ UTsub := by
      rw [← hgS]
      refine ⟨alphaS ⟨x, hxS⟩, hmemS ⟨x, hxS⟩ hx, ?_⟩
      rw [e, map_mul, map_mul, map_inv, hh]
      rfl
    exact mem_UTsub.mp hmem
  · rw [hPc]
    intro A hA
    rw [← hgS] at hA
    obtain ⟨s, hs, hsA⟩ := hA
    rw [hS] at hs
    obtain ⟨x, hxs⟩ := hs
    refine ⟨h * x.1 * h⁻¹, ⟨x.1.1, (hPs₁mem x.1).1 x.2, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, hh]
    have hx : alphaS x.1 = s := hxs
    rw [hx]
    exact hsA

theorem card_sylow_TD6 (P : Sylow 2 TD6) : Nat.card ↥(P : Subgroup TD6) = 2 ^ 30 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : CFSG.Open.ordD 6 2 = 2 ^ 30 * 46591793325 := by decide +kernel
  have hfac : (2 ^ 30 * 46591793325 : ℕ).factorization 2 = 30 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply]
    rw [Nat.Prime.factorization_pow Nat.prime_two]
    have h2 : (46591793325 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [h2]
  rw [Sylow.card_eq_multiplicity, card_TD6, hord, hfac]

theorem elemAb_sylow_classification (X : Subgroup TD6) (hX : CFSG.IsElementaryAbelian 2 X)
    (hcard : Nat.card X = 2 ^ 15) (P : Sylow 2 TD6) (hXP : X ≤ P)
    (hPN : (P : Subgroup TD6) ≤ Subgroup.normalizer (X : Set TD6)) :
    ∃ c : TD6, X.map (MulAut.conj c).toMonoidHom = K0 ∨
      X.map (MulAut.conj c).toMonoidHom = UFix Wp ∨
      X.map (MulAut.conj c).toMonoidHom = UFix Cc := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hX
  obtain ⟨c, hcS, hK0c, hUTc, hUTallc⟩ := exists_normalization (P : Subgroup TD6) P.isPGroup'
    (fun Q hPQ hQ => P.is_maximal' hQ hPQ) (card_sylow_TD6 P)
  refine ⟨c, ?_⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂ : Subgroup TD6, P₂ = (P : Subgroup TD6).map (MulAut.conj c).toMonoidHom :=
    ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : Subgroup TD6, X₂ = X.map (MulAut.conj c).toMonoidHom := ⟨_, rfl⟩
  rw [← hP₂] at hcS hK0c hUTc hUTallc
  rw [← hX₂]
  have hX₂P₂ : X₂ ≤ P₂ := by
    rw [hX₂, hP₂]
    exact Subgroup.map_mono hXP
  haveI : CFSG.IsElementaryAbelian 2 X₂ := by
    rw [hX₂]
    exact CFSG.IsElementaryAbelian.map _
  have hcard₂ : Nat.card ↥X₂ = 2 ^ 15 := by
    rw [hX₂, Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard]
  have hPN₂ : ∀ g ∈ P₂, ∀ x ∈ X₂, g * x * g⁻¹ ∈ X₂ := by
    rw [hP₂, hX₂]
    rintro _ ⟨g', hg', rfl⟩ _ ⟨x', hx', rfl⟩
    refine ⟨g' * x' * g'⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hPN hg') x').1 hx'
    · show c * (g' * x' * g'⁻¹) * c⁻¹ = (c * g' * c⁻¹) * (c * x' * c⁻¹) * (c * g' * c⁻¹)⁻¹
      group
  have hsq : ∀ x ∈ X₂.subgroupOf Stab0, x * x = 1 := by
    intro x hx
    have h1 : x.1 ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian x.1
      (Subgroup.mem_subgroupOf.mp hx)
    apply Subtype.ext
    show x.1 * x.1 = 1
    rw [← pow_two]
    exact h1
  have hab : ∀ x ∈ X₂.subgroupOf Stab0, ∀ y ∈ X₂.subgroupOf Stab0, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    show x.1 * y.1 = y.1 * x.1
    have := (IsMulCommutative.is_comm (M := X₂)).comm ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩
      ⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩
    exact congrArg Subtype.val this
  have hcardXs : Nat.card ↥(X₂.subgroupOf Stab0) = 2 ^ 15 := by
    rw [← hcard₂]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hX₂P₂.trans hcS)).toEquiv
  have hres := classification_normalized (X₂.subgroupOf Stab0) (P₂.subgroupOf Stab0) hsq hab
    hcardXs (fun x hx => Subgroup.mem_subgroupOf.mpr (hX₂P₂ (Subgroup.mem_subgroupOf.mp hx)))
    (fun g hg x hx => Subgroup.mem_subgroupOf.mpr (hPN₂ g.1 (Subgroup.mem_subgroupOf.mp hg) x.1
      (Subgroup.mem_subgroupOf.mp hx)))
    (fun k hk => Subgroup.mem_subgroupOf.mpr (hK0c ((mem_K0_iff_alphaS k).2 hk)))
    (fun g hg => hUTc g (Subgroup.mem_subgroupOf.mp hg))
    (fun A hA => by
      obtain ⟨g, hg, hgA⟩ := hUTallc A hA
      exact ⟨g, Subgroup.mem_subgroupOf.mpr hg, hgA⟩)
  rw [Subgroup.map_subgroupOf_eq_of_le (hX₂P₂.trans hcS)] at hres
  exact hres

end Cert

end CFSG.GF2Type.SmithTypeE.E7
