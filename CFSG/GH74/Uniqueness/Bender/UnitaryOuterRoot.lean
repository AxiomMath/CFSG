module

public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible
public import CFSG.GH74.Uniqueness.Bender.Psl2Subgroups

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Squares

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.sq_mem_rootCenter_unitary
    {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K)
    {x : K} (hx : x ∈ (Q : Subgroup K)) : x * x ∈ rootCenter (Q : Subgroup K) := by
  classical
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hQ2 : IsPGroup 2 (Q : Subgroup K) := Q.isPGroup'
  let N : Subgroup K :=
    Subgroup.closure (↑(rootCenter (Q : Subgroup K)) ∪ {x | ∃ y ∈ (Q : Subgroup K), x = y * y})
  have hZN : rootCenter (Q : Subgroup K) ≤ N := fun z hz => Subgroup.subset_closure (Or.inl hz)
  have hNQ : N ≤ (Q : Subgroup K) := by
    rw [Subgroup.closure_le]
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact rootCenter_le _ hx
    · exact Q.mul_mem hy hy
  have hinv : ∀ d ∈ cartan (Q : Subgroup K) t, ∀ w ∈ N, d * w * d⁻¹ ∈ N := by
    intro d hd w hw
    have hdM : d ∈ borel (Q : Subgroup K) := cartan_le_borel _ _ hd
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact hZN (conj_mem_rootCenter hdM hx)
      · refine Subgroup.subset_closure (Or.inr ⟨d * y * d⁻¹, ?_, ?_⟩)
        · exact (Subgroup.mem_normalizer_iff.mp hdM y).mp hy
        · group
    | one => simp
    | mul x y _ _ hx hy =>
      have := N.mul_mem hx hy
      convert this using 1
      group
    | inv x _ hx =>
      have := N.inv_mem hx
      convert this using 1
      group
  rcases h.irreducible_unitary Q hc.sq_eq_one hc.not_mem N hZN hNQ hinv with hNZ | hNQ'
  · have : x * x ∈ N := Subgroup.subset_closure (Or.inr ⟨x, hx, rfl⟩)
    rw [hNZ] at this
    exact this
  · exfalso
    have hZQ : rootCenter (Q : Subgroup K) ≠ (Q : Subgroup K) := by
      intro heq
      have hcard := hc.card_eq
      rw [← heq, hc.card_center] at hcard
      have hn2 : 2 ≤ n := h.two_le.2
      have hq : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have h1 : 2 ^ n < (2 ^ n) ^ 3 := by
        calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
          _ < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    obtain ⟨M, hMQ, hMne, hZM, hsq⟩ := exists_index_two_of_ne hQ2 (rootCenter_le _) hZQ
    apply hMne
    apply le_antisymm hMQ
    rw [← hNQ']
    rw [Subgroup.closure_le]
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hZM hx
    · exact hsq y hy

end Squares


section Fixed

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.fixed_iff_rootCenter_unitary
    {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K)
    (α : MulAut K) (hα : α * α = 1) (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹)
    (hQ : ∀ x ∈ (Q : Subgroup K), α x ∈ (Q : Subgroup K)) {x : K} (hx : x ∈ (Q : Subgroup K)) :
    α x = x ↔ x ∈ rootCenter (Q : Subgroup K) := by
  classical
  have hn2 : 2 ≤ n := h.two_le.2
  obtain ⟨φ⟩ := h.fixed_unitary α hα hout
  have hL : BenderType (autFixed α) n 1 1 := BenderType.linear n hn2 φ
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hαsq : ∀ y, α (α y) = y := fun y => by
    have := congrArg (fun f : MulAut K => f y) hα
    simpa using this
  have hαZ : ∀ z ∈ rootCenter (Q : Subgroup K), α z ∈ rootCenter (Q : Subgroup K) := by
    intro z hz
    rw [mem_rootCenter_iff] at hz ⊢
    refine ⟨hQ z hz.1, fun p hp => ?_⟩
    have h1 := hz.2 (α p) (hQ p hp)
    have h2 := congrArg α h1
    rw [map_mul, map_mul, hαsq] at h2
    exact h2
  have hfixZ : ∀ y ∈ (Q : Subgroup K), α y = y → y ∈ rootCenter (Q : Subgroup K) := by
    intro y hyQ hyα
    have hsq : ∀ w ∈ (Q : Subgroup K) ⊓ autFixed α, w * w = 1 := by
      rintro w ⟨hwQ, hwL⟩
      obtain ⟨k, hk⟩ := Q.isPGroup' ⟨w, hwQ⟩
      have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hk'' : (⟨w, hwL⟩ : autFixed α) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      exact congrArg Subtype.val (BenderType.sq_eq_one_of_two_pow_linear hL hk'')
    have hle : (Q : Subgroup K) ⊓ autFixed α ≤ rootCenter (Q : Subgroup K) :=
      hc.elemAbelian_le_rootCenter inf_le_left hsq
    exact hle ⟨hyQ, hyα⟩
  have hfixall : ∀ z ∈ rootCenter (Q : Subgroup K), α z = z := by
    obtain ⟨z₀, hz₀Z, hz₀1, hz₀α⟩ : ∃ z ∈ rootCenter (Q : Subgroup K), z ≠ 1 ∧ α z = z := by
      by_contra hno
      let φZ : rootCenter (Q : Subgroup K) →* rootCenter (Q : Subgroup K) :=
        (α.toMonoidHom.comp (rootCenter (Q : Subgroup K)).subtype).codRestrict _
          (fun z => hαZ z z.2)
      have hfpf : MonoidHom.FixedPointFree φZ := by
        intro z hz
        by_contra hz1
        apply hno
        refine ⟨z, z.2, fun h1 => hz1 (Subtype.ext h1), ?_⟩
        exact congrArg Subtype.val hz
      have hinv : Function.Involutive φZ := fun z => Subtype.ext (hαsq z)
      have hodd := hfpf.odd_card_of_involutive hinv
      rw [hc.card_center] at hodd
      have heven : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    have hz₀sq : z₀ * z₀ = 1 := hc.center_sq z₀ hz₀Z
    obtain ⟨Q₁, t₁, hz₁, -, -, -, hZ₁L, -⟩ := h.exists_psl2_pair_of_mem φ
      (mem_autFixed_iff.mpr hz₀α) hz₀sq
    have hz₀1' : zpowers z₀ ≠ ⊥ := fun hbot => hz₀1 (by
      have : z₀ ∈ zpowers z₀ := Subgroup.mem_zpowers z₀
      rw [hbot, Subgroup.mem_bot] at this
      exact this)
    have hQ₁ : Q₁ = Q := hc.sylow_eq_of_ne_bot hz₀1'
      (Subgroup.zpowers_le.mpr (rootCenter_le _ hz₀Z))
      (Subgroup.zpowers_le.mpr (rootCenter_le _ hz₁))
    subst hQ₁
    intro z hz
    exact mem_autFixed_iff.mp (hZ₁L hz)
  constructor
  · exact hfixZ x hx
  · exact hfixall x

end Fixed


section Counting

variable {K : Type*} [Group K] [Finite K]

theorem ncard_le_mul_ncard_image {T : Set K} {Z : Subgroup K} (c : K → K)
    (hinj : ∀ x ∈ T, ∀ y ∈ T, c x = c y → x * y⁻¹ ∈ Z) :
    T.ncard ≤ Nat.card Z * (c '' T).ncard := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hTf : T.Finite := Set.toFinite T
  have hcard : T.ncard = hTf.toFinset.card := Set.ncard_eq_toFinset_card T hTf
  have himg : (c '' T).ncard = (hTf.toFinset.image c).card := by
    rw [← Set.ncard_coe_finset (hTf.toFinset.image c)]
    congr 1
    ext y
    simp
  rw [hcard, himg]
  apply Finset.card_le_mul_card_image hTf.toFinset (Nat.card Z)
  intro a ha
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp ha
  have hy₀T : y₀ ∈ T := hTf.mem_toFinset.mp hy₀
  have h1 : ((hTf.toFinset.filter fun x => c x = c y₀ : Finset K) : Set K).ncard ≤
      (Z : Set K).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun x => x * y₀⁻¹)
    · intro x hx
      rw [Finset.coe_filter] at hx
      exact hinj x (hTf.mem_toFinset.mp hx.1) y₀ hy₀T hx.2
    intro x _ y _ hxy
    exact mul_right_cancel hxy
  rw [Set.ncard_coe_finset] at h1
  rwa [← Nat.card_coe_set_eq] at h1

@[expose] def autComm (α : MulAut K) (x : K) : K := x⁻¹ * α x

@[expose] def commutatorAut (Q : Subgroup K) (α : MulAut K) : Subgroup K :=
  Subgroup.closure (autComm α '' (Q : Set K))

theorem commutatorAut_structure (Qs Z : Subgroup K) (α : MulAut K) (hαsq : ∀ y, α (α y) = y)
    (hQ : ∀ x ∈ Qs, α x ∈ Qs) (hZQ : Z ≤ Qs) (hZc : ∀ z ∈ Z, ∀ r ∈ Qs, z * r = r * z)
    (hsq : ∀ x ∈ Qs, x * x ∈ Z) (hZsq : ∀ z ∈ Z, z * z = 1)
    (hinv : ∀ x ∈ Qs, x * x = 1 → x ∈ Z) (hfix : ∀ x ∈ Qs, α x = x ↔ x ∈ Z) {q : ℕ}
    (hZcard : Nat.card Z = q) (hQcard : Nat.card Qs = q ^ 3) (hq : 0 < q) :
    commutatorAut Qs α ≤ Qs ∧ Z ≤ commutatorAut Qs α ∧ Nat.card (commutatorAut Qs α) = q ^ 2 ∧
      (∀ x ∈ commutatorAut Qs α, ∀ y ∈ commutatorAut Qs α, x * y = y * x) ∧
      (∀ w ∈ commutatorAut Qs α, α w = w⁻¹) ∧
      (∀ w ∈ commutatorAut Qs α, w * w ∈ Z) ∧
      (∀ w ∈ commutatorAut Qs α, (w * w = 1 ↔ w ∈ Z)) ∧
      (∀ z ∈ Z, ∃ w ∈ commutatorAut Qs α, w * w = z) ∧
      (∀ x ∈ Qs, autComm α x ∈ Z ↔ x ∈ commutatorAut Qs α) := by
  classical
  have hcQ : ∀ x ∈ Qs, autComm α x ∈ Qs := fun x hx => Qs.mul_mem (Qs.inv_mem hx) (hQ x hx)
  have hαc : ∀ x, α (autComm α x) = (autComm α x)⁻¹ := by
    intro x
    unfold autComm
    rw [map_mul, map_inv, hαsq, mul_inv_rev, inv_inv]
  have hαx : ∀ x, α x = x * autComm α x := by
    intro x
    unfold autComm
    group
  have hcinj : ∀ x ∈ Qs, ∀ y ∈ Qs, autComm α x = autComm α y → x * y⁻¹ ∈ Z := by
    intro x hx y hy hxy
    have h1 : α x = x * (y⁻¹ * α y) := by
      calc α x = x * (x⁻¹ * α x) := by group
        _ = x * (y⁻¹ * α y) := by rw [show x⁻¹ * α x = y⁻¹ * α y from hxy]
    have h2 : α (x * y⁻¹) = x * y⁻¹ := by
      rw [map_mul, map_inv, h1]
      group
    exact (hfix _ (Qs.mul_mem hx (Qs.inv_mem hy))).mp h2
  let C₁ : Subgroup K :=
    { carrier := {x | x ∈ Qs ∧ autComm α x ∈ Z}
      mul_mem' := by
        rintro x y ⟨hxQ, hxZ⟩ ⟨hyQ, hyZ⟩
        refine ⟨Qs.mul_mem hxQ hyQ, ?_⟩
        have hcomm : autComm α x * y = y * autComm α x := hZc _ hxZ y hyQ
        have hmul : autComm α (x * y) = autComm α x * autComm α y := by
          unfold autComm at hcomm ⊢
          rw [map_mul]
          calc (x * y)⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
            _ = y⁻¹ * ((x⁻¹ * α x) * y) * (y⁻¹ * α y) := by group
            _ = y⁻¹ * (y * (x⁻¹ * α x)) * (y⁻¹ * α y) := by rw [hcomm]
            _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by group
        rw [hmul]
        exact Z.mul_mem hxZ hyZ
      one_mem' := ⟨Qs.one_mem, by
        unfold autComm
        simp only [inv_one, map_one, mul_one]
        exact Z.one_mem⟩
      inv_mem' := by
        rintro x ⟨hxQ, hxZ⟩
        refine ⟨Qs.inv_mem hxQ, ?_⟩
        have hcomm : (autComm α x)⁻¹ * x = x * (autComm α x)⁻¹ := hZc _ (Z.inv_mem hxZ) x hxQ
        have hinv' : autComm α x⁻¹ = (autComm α x)⁻¹ := by
          have hx' : α x = x * autComm α x := hαx x
          have h0 : autComm α x⁻¹ = x * (α x)⁻¹ := by
            unfold autComm
            rw [map_inv, inv_inv]
          rw [h0, hx', mul_inv_rev]
          calc x * ((autComm α x)⁻¹ * x⁻¹) = (x * (autComm α x)⁻¹) * x⁻¹ := by group
            _ = ((autComm α x)⁻¹ * x) * x⁻¹ := by rw [← hcomm]
            _ = (autComm α x)⁻¹ := by group
        rw [hinv']
        exact Z.inv_mem hxZ }
  have hmemC₁ : ∀ x, x ∈ C₁ ↔ x ∈ Qs ∧ autComm α x ∈ Z := fun x => Iff.rfl
  have hSsub : autComm α '' (Qs : Set K) ⊆ (C₁ : Set K) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hcQ x hx, ?_⟩
    show (autComm α x)⁻¹ * α (autComm α x) ∈ Z
    rw [hαc x, ← mul_inv_rev]
    exact Z.inv_mem (hsq _ (hcQ x hx))
  have hSlow : q ^ 2 ≤ (autComm α '' (Qs : Set K)).ncard := by
    have h1 := ncard_le_mul_ncard_image (T := (Qs : Set K)) (Z := Z) (autComm α) hcinj
    have h2 : (Qs : Set K).ncard = q ^ 3 := by
      rw [← Nat.card_coe_set_eq]
      exact hQcard
    rw [h2, hZcard] at h1
    have : q * q ^ 2 ≤ q * (autComm α '' (Qs : Set K)).ncard := by
      calc q * q ^ 2 = q ^ 3 := by ring
        _ ≤ _ := h1
    exact Nat.le_of_mul_le_mul_left this hq
  have hC₁up : (C₁ : Set K).ncard ≤ q ^ 2 := by
    have h1 := ncard_le_mul_ncard_image (T := (C₁ : Set K)) (Z := Z) (autComm α)
      (fun x hx y hy hxy => hcinj x hx.1 y hy.1 hxy)
    have h2 : (autComm α '' (C₁ : Set K)).ncard ≤ q := by
      calc (autComm α '' (C₁ : Set K)).ncard ≤ (Z : Set K).ncard :=
            Set.ncard_le_ncard (by rintro _ ⟨x, hx, rfl⟩; exact hx.2) (Set.toFinite _)
        _ = q := by rw [← Nat.card_coe_set_eq]; exact hZcard
    calc (C₁ : Set K).ncard ≤ Nat.card Z * (autComm α '' (C₁ : Set K)).ncard := h1
      _ ≤ q * q := by rw [hZcard]; exact Nat.mul_le_mul_left _ h2
      _ = q ^ 2 := by ring
  have hSeq : autComm α '' (Qs : Set K) = (C₁ : Set K) :=
    Set.eq_of_subset_of_ncard_le hSsub (hC₁up.trans hSlow) (Set.toFinite _)
  have hW : commutatorAut Qs α = C₁ := by
    unfold commutatorAut
    rw [hSeq]
    exact Subgroup.closure_eq C₁
  have hC₁card : Nat.card C₁ = q ^ 2 := by
    have h1 : Nat.card C₁ = (C₁ : Set K).ncard := Nat.card_coe_set_eq (C₁ : Set K)
    rw [h1]
    apply le_antisymm hC₁up
    rw [← hSeq]
    exact hSlow
  have hinvW : ∀ w ∈ C₁, α w = w⁻¹ := by
    intro w hw
    have : w ∈ autComm α '' (Qs : Set K) := by rw [hSeq]; exact hw
    obtain ⟨x, -, rfl⟩ := this
    exact hαc x
  have habel : ∀ x ∈ C₁, ∀ y ∈ C₁, x * y = y * x := by
    intro x hx y hy
    have h1 := hinvW (x * y) (C₁.mul_mem hx hy)
    rw [map_mul, hinvW x hx, hinvW y hy, mul_inv_rev] at h1
    have h2 := congrArg (fun w => w⁻¹) h1
    simp only [mul_inv_rev, inv_inv] at h2
    exact h2.symm
  have hC₁Q : ∀ w ∈ C₁, w ∈ Qs := fun w hw => hw.1
  have hZC₁ : Z ≤ C₁ := by
    intro z hz
    refine ⟨hZQ hz, ?_⟩
    have : α z = z := (hfix z (hZQ hz)).mpr hz
    unfold autComm
    rw [this, inv_mul_cancel]
    exact Z.one_mem
  have hΩ : ∀ w ∈ C₁, (w * w = 1 ↔ w ∈ Z) := fun w hw =>
    ⟨fun h1 => hinv w (hC₁Q w hw) h1, fun h1 => hZsq w h1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW]
    exact fun w hw => hC₁Q w hw
  · rw [hW]
    exact hZC₁
  · rw [hW]
    exact hC₁card
  · rw [hW]
    exact habel
  · rw [hW]
    exact hinvW
  · rw [hW]
    exact fun w hw => hsq w (hC₁Q w hw)
  · rw [hW]
    exact hΩ
  ·
    rw [hW]
    have hsqinj : ∀ x ∈ (C₁ : Set K), ∀ y ∈ (C₁ : Set K),
        (fun w : K => w * w) x = (fun w : K => w * w) y → x * y⁻¹ ∈ Z := by
      intro x hx y hy hxy
      have hxy' : x * x = y * y := hxy
      have hcomm := habel x hx y hy
      have h1 : (x * y⁻¹) * (x * y⁻¹) = 1 := by
        have hyc : y⁻¹ * x = x * y⁻¹ := by
          have := habel x hx y⁻¹ (C₁.inv_mem hy)
          exact this.symm
        calc (x * y⁻¹) * (x * y⁻¹) = x * (y⁻¹ * x) * y⁻¹ := by group
          _ = x * (x * y⁻¹) * y⁻¹ := by rw [hyc]
          _ = (x * x) * (y⁻¹ * y⁻¹) := by group
          _ = (y * y) * (y⁻¹ * y⁻¹) := by rw [hxy']
          _ = 1 := by group
      exact (hΩ _ (C₁.mul_mem hx (C₁.inv_mem hy))).mp h1
    have h1 := ncard_le_mul_ncard_image (T := (C₁ : Set K)) (Z := Z) (fun w : K => w * w) hsqinj
    have hC₁n : (C₁ : Set K).ncard = q ^ 2 := by
      rw [← Nat.card_coe_set_eq]
      exact hC₁card
    rw [hC₁n, hZcard] at h1
    have h3 : q ≤ ((fun w : K => w * w) '' (C₁ : Set K)).ncard := by
      have : q * q ≤ q * ((fun w : K => w * w) '' (C₁ : Set K)).ncard := by
        calc q * q = q ^ 2 := by ring
          _ ≤ _ := h1
      exact Nat.le_of_mul_le_mul_left this hq
    have hsub : (fun w : K => w * w) '' (C₁ : Set K) ⊆ (Z : Set K) := by
      rintro _ ⟨w, hw, rfl⟩
      exact hsq w (hC₁Q w hw)
    have hZn : (Z : Set K).ncard = q := by
      rw [← Nat.card_coe_set_eq]
      exact hZcard
    have heq : (fun w : K => w * w) '' (C₁ : Set K) = (Z : Set K) :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hZn]; exact h3) (Set.toFinite _)
    intro z hz
    have : z ∈ (fun w : K => w * w) '' (C₁ : Set K) := by rw [heq]; exact hz
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨w, hw, rfl⟩
  · intro x hx
    rw [hW]
    exact ⟨fun h1 => ⟨hx, h1⟩, fun h1 => h1.2⟩

end Counting


section Main

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.lemma_3_4_d5_unitary
    {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K)
    (α : MulAut K) (hα : α * α = 1) (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹)
    (hQ : ∀ x ∈ (Q : Subgroup K), α x ∈ (Q : Subgroup K)) :
    commutatorAut (Q : Subgroup K) α ≤ (Q : Subgroup K) ∧
      rootCenter (Q : Subgroup K) ≤ commutatorAut (Q : Subgroup K) α ∧
      Nat.card (commutatorAut (Q : Subgroup K) α) = (2 ^ n) ^ 2 ∧
      (∀ x ∈ commutatorAut (Q : Subgroup K) α, ∀ y ∈ commutatorAut (Q : Subgroup K) α,
        x * y = y * x) ∧
      (∀ w ∈ commutatorAut (Q : Subgroup K) α, α w = w⁻¹) ∧
      (∀ w ∈ commutatorAut (Q : Subgroup K) α, w * w ∈ rootCenter (Q : Subgroup K)) ∧
      (∀ w ∈ commutatorAut (Q : Subgroup K) α,
        (w * w = 1 ↔ w ∈ rootCenter (Q : Subgroup K))) ∧
      (∀ z ∈ rootCenter (Q : Subgroup K), ∃ w ∈ commutatorAut (Q : Subgroup K) α, w * w = z) ∧
      (∀ x ∈ (Q : Subgroup K),
        x⁻¹ * α x ∈ rootCenter (Q : Subgroup K) ↔ x ∈ commutatorAut (Q : Subgroup K) α) := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hαsq : ∀ y, α (α y) = y := fun y => by
    have := congrArg (fun f : MulAut K => f y) hα
    simpa using this
  exact commutatorAut_structure (Q : Subgroup K) (rootCenter (Q : Subgroup K)) α hαsq hQ
    (rootCenter_le _) (fun z hz r hr => ((mem_rootCenter_iff.mp hz).2 r hr).symm)
    (fun x hx => h.sq_mem_rootCenter_unitary Q hx) (fun z hz => hc.center_sq z hz)
    (fun x hx hx2 => hc.mem_rootCenter_of_mul_self hx hx2)
    (fun x hx => h.fixed_iff_rootCenter_unitary Q α hα hout hQ hx) (q := 2 ^ n) hc.card_center
    hc.card_eq (by positivity)

end Main

end CFSG.GH74.Uniqueness.Bender
