module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma zmod_two_add_self (x : ZMod 2) : x + x = 0 :=
  CharTwo.add_self_eq_zero x

private lemma pi_zmod_two_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  ext i
  exact zmod_two_add_self (v i)

private lemma zmod_two_add_cancel_left {n : ℕ} (v w : Fin n → ZMod 2) : v + (v + w) = w := by
  rw [← add_assoc, pi_zmod_two_add_self v, zero_add]

private lemma isEvenVec_add {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

private lemma card_evenVec : Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v} = 16 := by
  have e : (Fin 4 → ZMod 2) ≃ {v : Fin 5 → ZMod 2 // IsEvenVec v} :=
    { toFun := fun w => ⟨Fin.snoc w (∑ j, w j), by
        rw [IsEvenVec, Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact zmod_two_add_self _
      ⟩
      invFun := fun v => fun i => v.1 i.castSucc
      left_inv := fun w => by
        funext i
        simp only [Fin.snoc_castSucc]
      right_inv := fun v => by
        apply Subtype.ext
        funext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]
        · simp only [Fin.snoc_last]
          have h1 : (∑ i : Fin 4, v.1 i.castSucc) + v.1 (Fin.last 4) = 0 := by
            simpa [IsEvenVec, Fin.sum_univ_castSucc] using v.2
          have h2 : (∑ i : Fin 4, v.1 i.castSucc) + (∑ i : Fin 4, v.1 i.castSucc) = 0 :=
            zmod_two_add_self _
          exact (add_left_cancel (a := ∑ i : Fin 4, v.1 i.castSucc) (by rw [h1, h2])).symm }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

private lemma conj_mem_of_normal {B V : Subgroup G} (hBleV : B ≤ V)
    (hBnorm : (B.subgroupOf V).Normal) {g b : G} (hg : g ∈ V) (hb : b ∈ B) :
    g * b * g⁻¹ ∈ B :=
  (normal_subgroupOf_iff hBleV).mp hBnorm b g hb hg

private lemma commutator_mem_of {B V : Subgroup G} (hBleV : B ≤ V)
    (hBnorm : (B.subgroupOf V).Normal) {g h b₁ b₂ : G} (hg : g ∈ V) (hh : h ∈ V)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hcomm : g * h * g⁻¹ * h⁻¹ ∈ B) :
    (g * b₁) * (h * b₂) * (g * b₁)⁻¹ * (h * b₂)⁻¹ ∈ B := by
  have key : (g * b₁) * (h * b₂) * (g * b₁)⁻¹ * (h * b₂)⁻¹ =
      (g * b₁ * g⁻¹) * (g * (h * b₂ * h⁻¹) * g⁻¹) * (g * h * g⁻¹ * h⁻¹) *
        (h * (g * b₁ * g⁻¹) * h⁻¹)⁻¹ * (h * b₂ * h⁻¹)⁻¹ := by group
  rw [key]
  exact B.mul_mem (B.mul_mem (B.mul_mem (B.mul_mem
    (conj_mem_of_normal hBleV hBnorm hg hb₁)
    (conj_mem_of_normal hBleV hBnorm hg (conj_mem_of_normal hBleV hBnorm hh hb₂))) hcomm)
    (B.inv_mem (conj_mem_of_normal hBleV hBnorm hh (conj_mem_of_normal hBleV hBnorm hg hb₁))))
    (B.inv_mem (conj_mem_of_normal hBleV hBnorm hh hb₂))

structure PrinceData (B V H : Subgroup G) (φ φ₀ : (Fin 5 → ZMod 2) → G) : Prop where
  mod : IsPermModuleMod (n := 5) IsEvenVec {0} φ V B H (alternatingGroup (Fin 5))
  via : IsPermModuleVia IsEvenVec φ₀ B H (alternatingGroup (Fin 5))
  compat : ∀ h ∈ H, ∀ σ ∈ alternatingGroup (Fin 5),
    (∀ v, IsEvenVec v → (h * φ v * h⁻¹)⁻¹ * φ (permVec σ v) ∈ B) →
      ∀ v, IsEvenVec v → h * φ₀ v * h⁻¹ = φ₀ (permVec σ v)

namespace PrinceData

variable {B V H : Subgroup G} {φ φ₀ : (Fin 5 → ZMod 2) → G}

theorem B_le (hP : PrinceData B V H φ φ₀) : B ≤ V :=
  hP.mod.1

theorem B_sq (hP : PrinceData B V H φ φ₀) {b : G} (hb : b ∈ B) : b * b = 1 := by
  obtain ⟨hadd, _, hmem, _, _⟩ := hP.via
  obtain ⟨v, hv, hvb⟩ := (hmem b).mp hb
  rw [← hvb]
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have hone : φ₀ 0 = 1 := by
    have h := hadd 0 0 h0 h0
    rw [zero_add] at h
    have h' : φ₀ 0 * 1 = φ₀ 0 * φ₀ 0 := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  have hvv : v + v = 0 := pi_zmod_two_add_self v
  have haddvv : φ₀ (v + v) = φ₀ v * φ₀ v := hadd v v hv hv
  rw [hvv, hone] at haddvv
  rw [← haddvv]

theorem sq_mem (hP : PrinceData B V H φ φ₀) {x : G} (hx : x ∈ V) : x * x ∈ B := by
  obtain ⟨hBleV, hBnorm, _, _, hφmemV, hφadd, hφB, hsurj, _, _⟩ := hP.mod
  obtain ⟨v, hv, hbv⟩ := hsurj x hx
  have hφvV : φ v ∈ V := hφmemV v hv
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have hφ0B : φ 0 ∈ B := (hφB 0 h0).mpr (by simp)
  have hvv : v + v = 0 := pi_zmod_two_add_self v
  have hφvvB : φ (v + v) ∈ B := by rw [hvv]; exact hφ0B
  have hsqB : φ v * φ v ∈ B := by
    have h1 : (φ v * φ v)⁻¹ * φ (v + v) ∈ B := hφadd v v hv hv
    have h2 : (φ v * φ v)⁻¹ ∈ B := by
      have h3 := B.mul_mem h1 (B.inv_mem hφvvB)
      simpa [mul_assoc] using h3
    simpa using B.inv_mem h2
  have hxeq : x = φ v * ((φ v)⁻¹ * x) := (mul_inv_cancel_left (φ v) x).symm
  rw [hxeq]
  have hconjb : (φ v)⁻¹ * ((φ v)⁻¹ * x) * φ v ∈ B := by
    simpa using conj_mem_of_normal hBleV hBnorm (V.inv_mem hφvV) hbv
  have hid : (φ v * ((φ v)⁻¹ * x)) * (φ v * ((φ v)⁻¹ * x)) =
      (φ v * φ v) * ((φ v)⁻¹ * ((φ v)⁻¹ * x) * φ v) * ((φ v)⁻¹ * x) := by group
  rw [hid]
  exact B.mul_mem (B.mul_mem hsqB hconjb) hbv

theorem comm_mem (hP : PrinceData B V H φ φ₀) {x y : G} (hx : x ∈ V) (hy : y ∈ V) :
    x * y * x⁻¹ * y⁻¹ ∈ B := by
  obtain ⟨hBleV, hBnorm, _, _, hφmemV, hφadd, _, hsurj, _, _⟩ := hP.mod
  obtain ⟨v, hv, hbv⟩ := hsurj x hx
  obtain ⟨w, hw, hbw⟩ := hsurj y hy
  have hφvV : φ v ∈ V := hφmemV v hv
  have hφwV : φ w ∈ V := hφmemV w hw
  have hcomm : φ v * φ w * (φ v)⁻¹ * (φ w)⁻¹ ∈ B := by
    have h1 : (φ v * φ w)⁻¹ * φ (v + w) ∈ B := hφadd v w hv hw
    have h2 : (φ w * φ v)⁻¹ * φ (w + v) ∈ B := hφadd w v hw hv
    rw [add_comm w v] at h2
    have hd : (φ v * φ w)⁻¹ * (φ w * φ v) ∈ B := by
      have h3 := B.mul_mem h1 (B.inv_mem h2)
      have hid : ((φ v * φ w)⁻¹ * φ (v + w)) * ((φ w * φ v)⁻¹ * φ (v + w))⁻¹ =
          (φ v * φ w)⁻¹ * (φ w * φ v) := by group
      rwa [hid] at h3
    have h4 := conj_mem_of_normal hBleV hBnorm (V.mul_mem hφvV hφwV) (B.inv_mem hd)
    have hid : (φ v * φ w) * ((φ v * φ w)⁻¹ * (φ w * φ v))⁻¹ * (φ v * φ w)⁻¹ =
        φ v * φ w * (φ v)⁻¹ * (φ w)⁻¹ := by group
    rwa [hid] at h4
  have hxeq : x = φ v * ((φ v)⁻¹ * x) := (mul_inv_cancel_left (φ v) x).symm
  have hyeq : y = φ w * ((φ w)⁻¹ * y) := (mul_inv_cancel_left (φ w) y).symm
  rw [hxeq, hyeq]
  exact commutator_mem_of (b₁ := (φ v)⁻¹ * x) (b₂ := (φ w)⁻¹ * y)
    hBleV hBnorm hφvV hφwV hbv hbw hcomm

theorem card_V [Finite G] (hP : PrinceData B V H φ φ₀) : Nat.card ↥V = 256 := by
  obtain ⟨hBleV, hBnorm, _, _, hφmemV, hφadd, hφB, hsurj, -, -⟩ := hP.mod
  haveI : (B.subgroupOf V).Normal := hBnorm
  obtain ⟨-, hφ₀inj, hφ₀mem, -, -⟩ := hP.via
  have h16 : Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v} = 16 := card_evenVec
  let φ₀' : {v : Fin 5 → ZMod 2 // IsEvenVec v} → ↥B :=
    fun v => ⟨φ₀ v.1, (hφ₀mem (φ₀ v.1)).mpr ⟨v.1, v.2, rfl⟩⟩
  have hinjB : Function.Injective φ₀' := by
    intro u v h
    apply Subtype.ext
    exact hφ₀inj u.1 v.1 u.2 v.2 (congrArg Subtype.val h)
  have hsurjB : Function.Surjective φ₀' := by
    intro x
    obtain ⟨v, hv, hvb⟩ := (hφ₀mem x.1).mp x.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvb⟩
  have hcardB : Nat.card ↥B = 16 := by
    rw [← Nat.card_congr (Equiv.ofBijective φ₀' ⟨hinjB, hsurjB⟩), h16]
  have hcardB' : Nat.card ↥(B.subgroupOf V) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleV).toEquiv, hcardB]
  let ψ : {v : Fin 5 → ZMod 2 // IsEvenVec v} → (↥V ⧸ B.subgroupOf V) :=
    fun v => QuotientGroup.mk' (B.subgroupOf V) ⟨φ v.1, hφmemV v.1 v.2⟩
  have hsurjψ : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf V) q
    obtain ⟨v, hv, hbv⟩ := hsurj x.1 x.2
    refine ⟨⟨v, hv⟩, ?_⟩
    show QuotientGroup.mk' (B.subgroupOf V) ⟨φ v, hφmemV v hv⟩ =
      QuotientGroup.mk' (B.subgroupOf V) x
    have hmem : ((⟨φ v, hφmemV v hv⟩ : ↥V)⁻¹ * x) ∈ B.subgroupOf V := by
      rw [mem_subgroupOf]
      simpa using hbv
    have h1 : QuotientGroup.mk' (B.subgroupOf V) ((⟨φ v, hφmemV v hv⟩ : ↥V)⁻¹ * x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    have h2 : (QuotientGroup.mk' (B.subgroupOf V) (⟨φ v, hφmemV v hv⟩ : ↥V))⁻¹ *
        QuotientGroup.mk' (B.subgroupOf V) x = 1 := by
      rw [← map_inv, ← map_mul]
      exact h1
    exact inv_mul_eq_one.mp h2
  have hinjψ : Function.Injective ψ := by
    intro u w h
    have h' : QuotientGroup.mk' (B.subgroupOf V) ⟨φ u.1, hφmemV u.1 u.2⟩ =
        QuotientGroup.mk' (B.subgroupOf V) ⟨φ w.1, hφmemV w.1 w.2⟩ := h
    have h1 : QuotientGroup.mk' (B.subgroupOf V)
        ((⟨φ u.1, hφmemV u.1 u.2⟩ : ↥V)⁻¹ * ⟨φ w.1, hφmemV w.1 w.2⟩) = 1 := by
      rw [map_mul, map_inv, h', inv_mul_cancel]
    have hmem : ((⟨φ u.1, hφmemV u.1 u.2⟩ : ↥V)⁻¹ *
        ⟨φ w.1, hφmemV w.1 w.2⟩) ∈ B.subgroupOf V :=
      (QuotientGroup.eq_one_iff _).mp h1
    have huw : (φ u.1)⁻¹ * φ w.1 ∈ B := by
      have h2 := (mem_subgroupOf).mp hmem
      simpa using h2
    have heven : IsEvenVec (u.1 + w.1) := isEvenVec_add u.2 w.2
    have hsum : u.1 + (u.1 + w.1) = w.1 := zmod_two_add_cancel_left u.1 w.1
    have hφw_mem : φ (u.1 + w.1) ∈ B := by
      have h2 : (φ u.1 * φ (u.1 + w.1))⁻¹ * φ (u.1 + (u.1 + w.1)) ∈ B :=
        hφadd u.1 (u.1 + w.1) u.2 heven
      rw [hsum] at h2
      have h3 : ((φ u.1 * φ (u.1 + w.1))⁻¹ * φ w.1) * ((φ u.1)⁻¹ * φ w.1)⁻¹ ∈ B :=
        B.mul_mem h2 (B.inv_mem huw)
      have hid : ((φ u.1 * φ (u.1 + w.1))⁻¹ * φ w.1) * ((φ u.1)⁻¹ * φ w.1)⁻¹ =
          (φ (u.1 + w.1))⁻¹ := by group
      rw [hid] at h3
      simpa using B.inv_mem h3
    have huw0 : u.1 + w.1 = 0 := by
      have h2 := (hφB (u.1 + w.1) heven).mp hφw_mem
      simpa using h2
    have huw' : w.1 = u.1 := by
      have huu : u.1 + u.1 = 0 := pi_zmod_two_add_self u.1
      exact add_left_cancel (a := u.1) (by rw [huw0, huu])
    exact Subtype.ext huw'.symm
  have hcardQ : Nat.card (↥V ⧸ B.subgroupOf V) = 16 := by
    rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinjψ, hsurjψ⟩), h16]
  have hidx : (B.subgroupOf V).index = 16 := by
    rw [Subgroup.index_eq_card, hcardQ]
  rw [← Subgroup.card_mul_index (B.subgroupOf V), hcardB', hidx]

end PrinceData

end CFSG.OddStandard.SmallF3.Omega
