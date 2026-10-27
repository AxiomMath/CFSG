module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltBasic

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement Pointwise

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltCent

open Equiv Equiv.Perm

theorem mem_stabilizer_swap_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (x : ↥(alternatingGroup (Fin m))) :
    x ∈ MulAction.stabilizer (alternatingGroup (Fin m)) ({i, j} : Set (Fin m)) ↔
      (x : Perm (Fin m)) * swap i j = swap i j * (x : Perm (Fin m)) := by
  have hset : x • ({i, j} : Set (Fin m)) = {(x : Perm (Fin m)) i, (x : Perm (Fin m)) j} := by
    rw [Set.smul_set_insert, Set.smul_set_singleton]
    rfl
  have hxij : (x : Perm (Fin m)) i ≠ (x : Perm (Fin m)) j := (x : Perm (Fin m)).injective.ne hij
  rw [MulAction.mem_stabilizer_iff, hset]
  have hconj : swap ((x : Perm (Fin m)) i) ((x : Perm (Fin m)) j) =
      (x : Perm (Fin m)) * swap i j * (x : Perm (Fin m))⁻¹ := swap_apply_apply _ _ _
  constructor
  · intro h
    have : swap ((x : Perm (Fin m)) i) ((x : Perm (Fin m)) j) = swap i j := by
      rcases Set.pair_eq_pair_iff.1 h with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · rw [h2, h3]
      · rw [h2, h3, swap_comm]
    rw [hconj] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · intro h
    have : swap ((x : Perm (Fin m)) i) ((x : Perm (Fin m)) j) = swap i j := by
      rw [hconj, mul_inv_eq_iff_eq_mul]; exact h
    have h1 := congrArg Perm.support this
    rw [support_swap hxij, support_swap hij] at h1
    have h2 := congrArg (fun s : Finset (Fin m) => (s : Set (Fin m))) h1
    simpa using h2

theorem isCoatom_stabilizer_pair {m : ℕ} (hm : 5 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    IsCoatom (MulAction.stabilizer (alternatingGroup (Fin m)) ({i, j} : Set (Fin m))) := by
  apply alternatingGroup.isCoatom_stabilizer
  · exact ⟨i, by simp⟩
  · have : ({i, j} : Set (Fin m)) ≠ Set.univ := by
      intro h
      have h3 := congrArg Set.ncard h
      rw [Set.ncard_pair hij, Set.ncard_univ] at h3
      simp at h3
      omega
    exact Set.nonempty_compl.2 this
  · rw [Set.ncard_pair hij]
    simp
    omega

section
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

theorem comm_a_mem_W {m : ℕ} {θ : ↥K →* ↥(alternatingGroup (Fin m))} {σ : Perm (Fin m)} {a : X}
    (hKa : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hθker : ∀ k : ↥K, θ k = 1 → (k : X) ∈ W)
    (hconj : ∀ k k' : ↥K, (k' : X) = a * (k : X) * a⁻¹ →
      ((θ k' : ↥(alternatingGroup (Fin m))) : Perm (Fin m)) =
        σ * ((θ k : ↥(alternatingGroup (Fin m))) : Perm (Fin m)) * σ⁻¹)
    (k : ↥K) (hcomm : ((θ k : ↥(alternatingGroup (Fin m))) : Perm (Fin m)) * σ =
      σ * ((θ k : ↥(alternatingGroup (Fin m))) : Perm (Fin m))) : ⁅(k : X), a⁆ ∈ W := by
  set k' : ↥K := ⟨a * k * a⁻¹, hKa k k.2⟩ with hk'
  have h1 := hconj k k' rfl
  have h2 : θ k' = θ k := by
    apply Subtype.ext
    rw [h1, ← hcomm]
    group
  have h3 : θ (k⁻¹ * k') = 1 := by rw [map_mul, map_inv, h2, inv_mul_cancel]
  have h4 := hθker _ h3
  have h5 : (k⁻¹ * k' : ↥K) = k⁻¹ * k' := rfl
  have h6 : ((k⁻¹ * k' : ↥K) : X) = (k : X)⁻¹ * (a * k * a⁻¹) := rfl
  rw [h6] at h4
  have h7 := Subgroup.Normal.conj_mem inferInstance _ h4 (k : X)
  have h8 : ⁅(k : X), a⁆ = (k * ((k : X)⁻¹ * (a * k * a⁻¹)) * (k : X)⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h8]
  exact W.inv_mem h7

variable [Finite X]

theorem centMax_core (h : Setup28 W K S) (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (haS : a ∈ S) (hna : a ∉ kerAct W K S) (hS2 : Nat.card ↥(indAut W K S) = 2)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) (hm : AltModel W K a U₁ U₂) : CentMax W K S a := by
  obtain ⟨m, θ, σ, hm5, hsurj, hkerW, hσ, hconj, -⟩ := hm
  obtain ⟨i, j, hij, rfl⟩ := hσ
  have hθker := AltBasic.theta_ker hR hZ hm5 θ hsurj hkerW
  have hNa := h.hN haS
  have hKa : ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun k hk => AltBasic.conj_mem_K hNa hk
  have hSc := AltBasic.S_cases_of_card_two h haS hna hS2
  have hW1 : W ≤ kerAct W K S := hR.w1_le
  have hnrm : ∀ n ∈ K ⊔ S, ∀ w ∈ kerAct W K S, n * w * n⁻¹ ∈ kerAct W K S := hR.w1_nrm
  have hKN : ∀ k ∈ K, k ∈ K ⊔ S := fun k hk => (le_sup_left : K ≤ K ⊔ S) hk
  have hSN : ∀ s ∈ S, s ∈ K ⊔ S := fun s hs => (le_sup_right : S ≤ K ⊔ S) hs
  have hmemC : ∀ k ∈ K, ⁅k, a⁆ ∈ W → ∀ s ∈ S, ⁅k, s⁆ ∈ kerAct W K S := by
    intro k hk hka s hs
    rcases hSc s hs with hs1 | hs1
    · have h1 : ⁅k, s⁆ = (k * s * k⁻¹) * s⁻¹ := by simp only [commutatorElement_def]
      rw [h1]
      exact (kerAct W K S).mul_mem (hnrm k (hKN k hk) s hs1) ((kerAct W K S).inv_mem hs1)
    · set w := a⁻¹ * s with hw
      have hs' : s = a * w := by rw [hw]; group
      have h1 : ⁅k, s⁆ = ⁅k, a⁆ * (a * ((k * w * k⁻¹) * w⁻¹) * a⁻¹) := by
        rw [hs']; simp only [commutatorElement_def]; group
      rw [h1]
      refine (kerAct W K S).mul_mem (hW1 hka) (hnrm a (hSN a haS) _ ?_)
      exact (kerAct W K S).mul_mem (hnrm k (hKN k hk) w hs1) ((kerAct W K S).inv_mem hs1)
  intro H hHK hC ⟨k₀, hk₀H, hk₀a⟩
  set L : Subgroup ↥(alternatingGroup (Fin m)) := (H.subgroupOf K).map θ with hL
  set Stab := MulAction.stabilizer (alternatingGroup (Fin m)) ({i, j} : Set (Fin m)) with hStab
  have hStabL : Stab ≤ L := by
    intro x hx
    obtain ⟨k₁, rfl⟩ := hsurj x
    have hcomm := (AltCent.mem_stabilizer_swap_iff hij (θ k₁)).1 hx
    have hk1a : ⁅(k₁ : X), a⁆ ∈ W := comm_a_mem_W hKa hθker hconj k₁ hcomm
    exact ⟨k₁, Subgroup.mem_subgroupOf.2 (hC k₁ k₁.2 (hmemC k₁ k₁.2 hk1a)), rfl⟩
  have hk₀L : θ ⟨k₀, hHK hk₀H⟩ ∈ L := ⟨⟨k₀, hHK hk₀H⟩, Subgroup.mem_subgroupOf.2 hk₀H, rfl⟩
  have hk₀nS : θ ⟨k₀, hHK hk₀H⟩ ∉ Stab := by
    intro hx
    have hcomm := (AltCent.mem_stabilizer_swap_iff hij _).1 hx
    exact hk₀a (hW1 (comm_a_mem_W hKa hθker hconj ⟨k₀, hHK hk₀H⟩ hcomm))
  have hlt : Stab < L := lt_of_le_of_ne hStabL (fun he => hk₀nS (he ▸ hk₀L))
  have hLtop : L = ⊤ := (isCoatom_stabilizer_pair hm5 hij).2 L hlt
  intro k hk
  have hkL : θ ⟨k, hk⟩ ∈ L := by rw [hLtop]; exact Subgroup.mem_top _
  obtain ⟨y, hyH, hy⟩ := hkL
  have hyH' : (y : X) ∈ H := Subgroup.mem_subgroupOf.1 hyH
  have hker1 : θ (y⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
  have hW' : ((y⁻¹ * ⟨k, hk⟩ : ↥K) : X) ∈ W := hθker _ hker1
  have hW'' : (y : X)⁻¹ * k ∈ W := hW'
  have hC' : (y : X)⁻¹ * k ∈ H := by
    apply hC _ (K.mul_mem (K.inv_mem y.2) hk)
    intro s hs
    have h1 : ⁅(y : X)⁻¹ * k, s⁆ = ((y : X)⁻¹ * k) * (s * ((y : X)⁻¹ * k)⁻¹ * s⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact (kerAct W K S).mul_mem (hW1 hW'') (hnrm s (hSN s hs) _ ((kerAct W K S).inv_mem (hW1 hW'')))
  have : k = (y : X) * ((y : X)⁻¹ * k) := by group
  rw [this]
  exact H.mul_mem hyH' hC'

theorem threeElt_core (h : Setup28 W K S) (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (haS : a ∈ S) (hZ : Subgroup.center ↥(bar W K) = ⊥) (hm : AltModel W K a U₁ U₂) :
    ThreeElt W K S a := by
  obtain ⟨m, θ, σ, hm5, hsurj, hkerW, hσ, hconj, -⟩ := hm
  obtain ⟨i, j, hij, rfl⟩ := hσ
  have hθker := AltBasic.theta_ker hR hZ hm5 θ hsurj hkerW
  have hNa := h.hN haS
  have hKa : ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun k hk => AltBasic.conj_mem_K hNa hk
  have hW1 : W ≤ kerAct W K S := hR.w1_le
  obtain ⟨l, hli, hlj⟩ : ∃ l : Fin m, l ≠ i ∧ l ≠ j := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun l _ => by
      by_cases hl : l = i
      · simp [hl]
      · simp [hcon l hl]
    have := Finset.card_le_card hsub
    simp at this
    have h2 : ({i, j} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    omega
  set x : Perm (Fin m) := swap i j * swap i l with hx
  have hx3 : x.IsThreeCycle := isThreeCycle_swap_mul_swap_same hij hli.symm hlj.symm
  have hxord : orderOf x = 3 := hx3.orderOf
  have hx1 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hxinv : swap i j * x * (swap i j)⁻¹ = x⁻¹ := by
    have e : swap i j * swap i j = 1 := swap_mul_self i j
    calc swap i j * x * (swap i j)⁻¹ = (swap i j * swap i j) * swap i l * swap i j := by
          rw [hx, swap_inv]; group
      _ = swap i l * swap i j := by rw [e, one_mul]
      _ = x⁻¹ := by rw [hx, mul_inv_rev, swap_inv, swap_inv]
  set xA : ↥(alternatingGroup (Fin m)) := ⟨x, Equiv.Perm.mem_alternatingGroup.2 hx3.sign⟩ with hxA
  obtain ⟨k₁, hk₁⟩ := hsurj xA
  have hk13 : θ (k₁ ^ 3) = 1 := by
    rw [map_pow, hk₁]
    exact Subtype.ext hx1
  have hk13W : ((k₁ ^ 3 : ↥K) : X) ∈ W := hθker _ hk13
  obtain ⟨e, he⟩ := h.hW ⟨((k₁ ^ 3 : ↥K) : X), hk13W⟩
  have he' : (((k₁ : X) ^ 3) ^ 2 ^ e) = 1 := congrArg Subtype.val he
  set pK : ↥K := k₁ ^ 4 ^ e with hpK
  have hpX : (pK : X) = (k₁ : X) ^ 4 ^ e := rfl
  have hp3 : ((pK : X)) ^ 3 = 1 := by
    have h4 : (4 : ℕ) ^ e = 2 ^ e * 2 ^ e := by rw [← mul_pow]; norm_num
    calc ((pK : X)) ^ 3 = ((k₁ : X) ^ 3) ^ 4 ^ e := by
          rw [hpX, ← pow_mul, mul_comm, pow_mul]
      _ = 1 := by rw [h4, pow_mul, he', one_pow]
  have hθp : θ pK = xA := by
    have h43 : 4 ^ e % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have h1 : x ^ (4 ^ e) = x := by rw [← pow_mod_orderOf, hxord, h43, pow_one]
    apply Subtype.ext
    rw [hpK, map_pow, hk₁, Subgroup.coe_pow]
    exact h1
  have hx1ne : x ≠ 1 := hx3.ne_one
  have hθpx : ((θ pK : ↥(alternatingGroup (Fin m))) : Perm (Fin m)) = x := by rw [hθp]
  set p' : ↥K := ⟨a * (pK : X) * a⁻¹, hKa _ pK.2⟩ with hp'
  have hθp' : ((θ p' : ↥(alternatingGroup (Fin m))) : Perm (Fin m)) = x⁻¹ := by
    rw [hconj pK p' rfl, hθpx, hxinv]
  refine ⟨(pK : X), pK.2, hp3, ?_, ?_, ?_, ?_⟩
  · intro hp
    have : (pK : X) ∈ K ⊓ kerAct W K S := ⟨pK.2, hp⟩
    rw [hR.k_w1] at this
    have h1 := hkerW pK this.2
    rw [h1] at hθpx
    exact hx1ne (by simpa using hθpx.symm)
  · have h1 : θ (p' * pK) = 1 := by
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, hθp', hθpx, inv_mul_cancel]
      rfl
    exact hW1 (hθker _ h1)
  · intro hp
    have hq : ⁅(pK : X), a⁆ = ((pK * p'⁻¹ : ↥K) : X) := by
      show _ = (pK : X) * (a * (pK : X) * a⁻¹)⁻¹
      simp only [commutatorElement_def]; group
    rw [hq] at hp
    have : ((pK * p'⁻¹ : ↥K) : X) ∈ K ⊓ kerAct W K S := ⟨(pK * p'⁻¹ : ↥K).2, hp⟩
    rw [hR.k_w1] at this
    have h1 := hkerW (pK * p'⁻¹) this.2
    have h2 := congrArg (fun y : ↥(alternatingGroup (Fin m)) => (y : Perm (Fin m))) h1
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hθp', hθpx, inv_inv,
      Subgroup.coe_one] at h2
    have h3 : x ^ 2 = 1 := by rw [pow_two]; exact h2
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hxord] at this
    omega
  · intro hz
    have hcen : xA ∈ Subgroup.center ↥(alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k', hk'⟩ := hsurj y
      have h1 : θ ⁅pK, k'⁆ = 1 := hkerW _ (by
        have := hz.2 (k' : X) k'.2
        exact this)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hk', hθp] at h1
      exact h1.symm
    have hm4 : 4 ≤ Nat.card (Fin m) := by simp; omega
    rw [alternatingGroup.center_eq_bot hm4, Subgroup.mem_bot] at hcen
    exact hx1ne (congrArg Subtype.val hcen)

end

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltCent
