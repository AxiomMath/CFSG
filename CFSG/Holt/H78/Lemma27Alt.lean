module

public import CFSG.Holt.H78.Lemma27Fibre
import CFSG.Holt.H78.AltModelSylow

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General Equiv
open scoped Pointwise

@[expose] def SocInvFixesBlocks {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
    (D : HoltData G Ω) : Prop :=
  ∀ v ∈ D.socPre, v * v = 1 → ∀ ω : Ω, v • ω ∈ orbit ↥(jOddCore G Ω) ω →
    ∀ ω' ∈ orbit ↥(jOddCore G Ω) ω, v • ω' = ω'

@[expose] def SocInvFixesBlocksStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω],
    IsStarGroup G Ω → HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1) →
      ∀ D : HoltData G Ω, SocInvFixesBlocks D

section Alternating

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

theorem exists_involution_alternatingGroup_fix_two_apply_eq (h6 : 6 ≤ Fintype.card Δ)
    {a b c c' : Δ} (hca : c ≠ a) (hcb : c ≠ b) (hc'a : c' ≠ a) (hc'b : c' ≠ b) (hcc' : c ≠ c') :
    ∃ σ ∈ alternatingGroup Δ, σ * σ = 1 ∧ σ a = a ∧ σ b = b ∧ σ c = c' := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, c'} : Finset Δ)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_four.trans_lt (by omega))
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, c', x} : Finset Δ)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_five.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  obtain ⟨hxa, hxb, hxc, hxc'⟩ := hx
  obtain ⟨hya, hyb, hyc, hyc', hyx⟩ := hy
  have hdisj : Perm.Disjoint (swap c c') (swap x y) := fun z => by
    by_cases hz : z = c ∨ z = c'
    · refine Or.inr (swap_apply_of_ne_of_ne ?_ ?_) <;> rcases hz with rfl | rfl <;>
        first | exact fun h => hxc h.symm | exact fun h => hxc' h.symm |
          exact fun h => hyc h.symm | exact fun h => hyc' h.symm
    · push Not at hz
      exact Or.inl (swap_apply_of_ne_of_ne hz.1 hz.2)
  refine ⟨swap c c' * swap x y, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hcc',
      Perm.sign_swap (Ne.symm hyx)]
    rfl
  · rw [show swap c c' * swap x y * (swap c c' * swap x y) =
        swap c c' * swap c c' * (swap x y * swap x y) by
      rw [mul_assoc, ← mul_assoc (swap x y), hdisj.commute.symm.eq]
      group, swap_mul_self, swap_mul_self, one_mul]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxa) (Ne.symm hya),
      swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hc'a)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxb) (Ne.symm hyb),
      swap_apply_of_ne_of_ne (Ne.symm hcb) (Ne.symm hc'b)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxc) (Ne.symm hyc), swap_apply_left]

private theorem exists_three_ne (h4 : 4 ≤ Fintype.card Δ) (c : Δ) :
    ∃ x y z : Δ, x ≠ c ∧ y ≠ c ∧ z ≠ c ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({c} : Finset Δ))
    (t := Finset.univ) (by rw [Finset.card_univ, Finset.card_singleton]; omega)
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({c, x} : Finset Δ))
    (t := Finset.univ) (by rw [Finset.card_univ]; exact Finset.card_le_two.trans_lt (by omega))
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({c, x, y} : Finset Δ))
    (t := Finset.univ) (by rw [Finset.card_univ]; exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy hz
  exact ⟨x, y, z, hx, hy.1, hz.1, Ne.symm hy.2, Ne.symm hz.2.1, Ne.symm hz.2.2⟩

theorem alternatingGroup_inf_stabilizer_le_closure (h6 : 6 ≤ Fintype.card Δ) (c : Δ) :
    (alternatingGroup Δ ⊓ stabilizer (Perm Δ) c : Subgroup (Perm Δ)) ≤ Subgroup.closure
      {σ | σ ∈ alternatingGroup Δ ⊓ stabilizer (Perm Δ) c ∧ σ * σ = 1} := by
  set W := (alternatingGroup Δ ⊓ stabilizer (Perm Δ) c : Subgroup (Perm Δ))
  set I := {σ | σ ∈ W ∧ σ * σ = 1}
  have := isSimpleGroup_alternatingGroup_inf_stabilizer h6 c
  have hconj : ∀ g ∈ W, ∀ x ∈ Subgroup.closure I, g * x * g⁻¹ ∈ Subgroup.closure I := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨W.mul_mem (W.mul_mem hg hx.1) (W.inv_mem hg), ?_⟩
      rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx.2]
      group
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx
  have hN : ((Subgroup.closure I).subgroupOf W).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (hconj g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.closure I).subgroupOf W) with h | h
  · exfalso
    obtain ⟨x, y, z, hxc, hyc, hzc, hxy, hxz, hyz⟩ := exists_three_ne (by omega) c
    obtain ⟨σ, hσA, hσ2, hσc, -, hσy⟩ := exists_involution_alternatingGroup_fix_two_apply_eq h6
      (a := c) (b := x) (c := y) (c' := z) hyc (Ne.symm hxy) hzc (Ne.symm hxz) hyz
    have hσ : (⟨σ, hσA, hσc⟩ : W) ∈ (Subgroup.closure I).subgroupOf W :=
      Subgroup.subset_closure ⟨⟨hσA, hσc⟩, hσ2⟩
    rw [h, Subgroup.mem_bot] at hσ
    have h1 : σ = 1 := congrArg Subtype.val hσ
    rw [h1] at hσy
    exact hyz hσy
  · intro w hw
    have hw' : (⟨w, hw⟩ : W) ∈ (Subgroup.closure I).subgroupOf W := h ▸ Subgroup.mem_top _
    exact hw'

end Alternating

section LemmaP

theorem eq_one_of_pow_two_pow_eq_one_of_odd_card {X : Type*} [Group X] [Finite X]
    (hX : Odd (Nat.card X)) {g : X} {a : ℕ} (hg : g ^ 2 ^ a = 1) : g = 1 := by
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg)
  have h2 : orderOf g ∣ Nat.card X := orderOf_dvd_natCard g
  rcases b with _ | b
  · exact orderOf_eq_one_iff.mp (by rw [hb, pow_zero])
  · rw [hb, pow_succ] at h2
    exact absurd (Nat.odd_iff.mp hX) (by have := (dvd_mul_left 2 _).trans h2; omega)

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

namespace HoltData

variable (D : HoltData G Ω)

theorem exists_mul_self_eq_one_rho_eq {k : D.ι} {σ : Perm (D.Ψc k)} (hσ : σ ∈ D.M k)
    (hσ2 : σ * σ = 1) : ∃ v : jHull G Ω, (v : G) ∈ D.L k ∧ v * v = 1 ∧ D.ρ k v = σ := by
  obtain ⟨y, hyL, hyσ⟩ := D.mem_M.mp hσ
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hρ : D.ρ k (y ^ m) = σ := by
    obtain ⟨j, rfl⟩ := hm
    rw [map_pow, hyσ, pow_succ, pow_mul, sq, hσ2, one_pow, one_mul]
  have hL : ((y ^ m : jHull G Ω) : G) ∈ D.L k := by
    rw [SubgroupClass.coe_pow]
    exact pow_mem hyL m
  refine ⟨y ^ m, hL, ?_, hρ⟩
  have hwL : ((y ^ m * y ^ m : jHull G Ω) : G) ∈ D.L k := by
    rw [Subgroup.coe_mul]
    exact mul_mem hL hL
  have hwO := D.mem_jOddCore_of_mem_L hwL (by rw [map_mul, hρ, hσ2])
  have hw2 : (y ^ m * y ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_add, ← pow_mul, show (m + m) * 2 ^ a = 2 * (2 ^ a * m) by ring, pow_mul, ← hn,
      pow_right_comm, pow_orderOf_eq_one, one_pow]
  have h1 := eq_one_of_pow_two_pow_eq_one_of_odd_card odd_card_jOddCore
    (g := ⟨_, hwO⟩) (a := a) (Subtype.ext (by
      show ((y ^ m * y ^ m : jHull G Ω) : G) ^ 2 ^ a = 1
      rw [← SubgroupClass.coe_pow, hw2, OneMemClass.coe_one]))
  have h2 : ((y ^ m * y ^ m : jHull G Ω) : G) = 1 := congrArg Subtype.val h1
  exact Subtype.ext h2

omit [Finite G] in
theorem smul_eq_of_mem_L_of_mul_self (h24 : SocInvFixesBlocks D) {k : D.ι} {v : jHull G Ω}
    (hvL : (v : G) ∈ D.L k) (hv2 : v * v = 1) {ω : Ω}
    (hω : D.ρ k v (D.coord ω k) = D.coord ω k) :
    ∀ ω' ∈ orbit ↥(jOddCore G Ω) ω, (v : G) • ω' = ω' := by
  classical
  refine h24 v (D.L_le_socPre k hvL) (congrArg Subtype.val hv2) ω
    ((D.coord_eq_iff ω _).mp (funext fun i => ?_))
  rw [D.coord_smul]
  by_cases hik : i = k
  · subst hik
    exact hω.symm
  · rw [D.rho_eq_one_of_mem_L (Ne.symm hik) hvL, Perm.one_apply]

theorem smul_eq_of_mem_L_of_pow_two_pow (h24 : SocInvFixesBlocks D) {k : D.ι}
    (hk : D.M k = alternatingGroup (D.Ψc k)) (h6 : 6 ≤ Fintype.card (D.Ψc k))
    {x : jHull G Ω} (hxL : (x : G) ∈ D.L k) {a : ℕ} (hxa : x ^ 2 ^ a = 1) {ω : Ω}
    (hxω : D.ρ k x (D.coord ω k) = D.coord ω k) : (x : G) • ω = ω := by
  set c := D.coord ω k
  set B := orbit ↥(jOddCore G Ω) ω
  have hOB : ∀ o ∈ jOddCore G Ω, ∀ ω' ∈ B, o • ω' ∈ B := fun o ho ω' hω' => by
    obtain ⟨p, rfl⟩ := hω'
    exact ⟨⟨o, ho⟩ * p, mul_smul _ _ _⟩
  have hcl : Subgroup.closure {σ | σ ∈ alternatingGroup (D.Ψc k) ⊓
      stabilizer (Perm (D.Ψc k)) c ∧ σ * σ = 1} ≤ alternatingGroup (D.Ψc k) :=
    (Subgroup.closure_le _).mpr fun σ hσ => hσ.1.1
  have hP : ∀ σ ∈ Subgroup.closure {σ | σ ∈ alternatingGroup (D.Ψc k) ⊓
      stabilizer (Perm (D.Ψc k)) c ∧ σ * σ = 1}, ∀ y : jHull G Ω, (y : G) ∈ D.L k →
      D.ρ k y = σ → ∃ o ∈ jOddCore G Ω, ∀ ω' ∈ B, (y : G) • ω' = o • ω' := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem σ hσ =>
      intro y hyL hyσ
      obtain ⟨v, hvL, hv2, hvσ⟩ :=
        D.exists_mul_self_eq_one_rho_eq (by rw [hk]; exact hσ.1.1) hσ.2
      have hoL : ((v⁻¹ * y : jHull G Ω) : G) ∈ D.L k := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact mul_mem (inv_mem hvL) hyL
      have hoO := D.mem_jOddCore_of_mem_L hoL (by rw [map_mul, map_inv, hvσ, hyσ, inv_mul_cancel])
      have hfix := D.smul_eq_of_mem_L_of_mul_self h24 hvL hv2 (ω := ω)
        (by rw [hvσ]; exact hσ.1.2)
      refine ⟨_, hoO, fun ω' hω' => ?_⟩
      calc (y : G) • ω' = (v : G) • ((v⁻¹ * y : jHull G Ω) : G) • ω' := by
            rw [← mul_smul, ← Subgroup.coe_mul, mul_inv_cancel_left]
        _ = ((v⁻¹ * y : jHull G Ω) : G) • ω' := hfix _ (hOB _ hoO ω' hω')
    | one =>
      intro y hyL hyσ
      exact ⟨y, D.mem_jOddCore_of_mem_L hyL hyσ, fun _ _ => rfl⟩
    | mul σ τ hσ _ ihσ ihτ =>
      intro y hyL hyστ
      obtain ⟨y₁, hy₁L, hy₁σ⟩ := D.mem_M.mp (by rw [hk]; exact hcl hσ)
      have hy₂L : ((y₁⁻¹ * y : jHull G Ω) : G) ∈ D.L k := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact mul_mem (inv_mem hy₁L) hyL
      obtain ⟨o₁, ho₁, h₁⟩ := ihσ y₁ hy₁L hy₁σ
      obtain ⟨o₂, ho₂, h₂⟩ := ihτ _ hy₂L (by rw [map_mul, map_inv, hy₁σ, hyστ, inv_mul_cancel_left])
      refine ⟨o₁ * o₂, mul_mem ho₁ ho₂, fun ω' hω' => ?_⟩
      calc (y : G) • ω' = (y₁ : G) • ((y₁⁻¹ * y : jHull G Ω) : G) • ω' := by
            rw [← mul_smul, ← Subgroup.coe_mul, mul_inv_cancel_left]
        _ = (o₁ * o₂) • ω' := by rw [h₂ ω' hω', h₁ _ (hOB o₂ ho₂ ω' hω'), mul_smul]
    | inv σ _ ihσ =>
      intro y hyL hyσ
      obtain ⟨o, ho, h⟩ := ihσ y⁻¹ (by rw [Subgroup.coe_inv]; exact inv_mem hyL)
        (by rw [map_inv, hyσ, inv_inv])
      refine ⟨o⁻¹, inv_mem ho, fun ω' hω' => ?_⟩
      have h' := h _ (hOB _ (inv_mem ho) ω' hω')
      rw [smul_inv_smul, Subgroup.coe_inv] at h'
      calc (y : G) • ω' = (y : G) • ((y : G)⁻¹ • o⁻¹ • ω') := by rw [h']
        _ = o⁻¹ • ω' := smul_inv_smul _ _
  have hxW : D.ρ k x ∈ alternatingGroup (D.Ψc k) ⊓ stabilizer (Perm (D.Ψc k)) c :=
    ⟨by rw [← hk]; exact D.rho_mem_M hxL, hxω⟩
  obtain ⟨o, ho, hxo⟩ := hP _ (alternatingGroup_inf_stabilizer_le_closure h6 c hxW) x hxL rfl
  have hpow : ∀ n : ℕ, ∀ ω' ∈ B, ((x ^ n : jHull G Ω) : G) • ω' = o ^ n • ω' := by
    intro n
    induction n with
    | zero => intro ω' _; rw [pow_zero, pow_zero, OneMemClass.coe_one, one_smul]
    | succ n ih =>
      intro ω' hω'
      rw [pow_succ, Subgroup.coe_mul, mul_smul, hxo ω' hω', ih _ (hOB o ho ω' hω'), ← mul_smul,
        ← pow_succ]
  have hωB : ω ∈ B := mem_orbit_self ω
  have h1 : o ^ 2 ^ a • ω = ω := by
    rw [← hpow _ ω hωB, hxa, OneMemClass.coe_one, one_smul]
  have hodd : Odd (orderOf o) := by
    rw [← Subgroup.orderOf_mk o ho]
    exact odd_card_jOddCore.of_dvd_nat (orderOf_dvd_natCard _)
  obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime (n := 2 ^ a) (x := o)
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd))
  have h3 : ∀ n : ℕ, (o ^ 2 ^ a) ^ n • ω = ω := fun n => by
    induction n with
    | zero => rw [pow_zero, one_smul]
    | succ n ih => rw [pow_succ, mul_smul, h1, ih]
  rw [hxo ω hωB, ← he, h3]

theorem exists_mem_L_fix_rho_apply_eq (h24 : SocInvFixesBlocks D) {k : D.ι}
    (hk : D.M k = alternatingGroup (D.Ψc k)) (h6 : 6 ≤ Fintype.card (D.Ψc k)) {α β : Ω}
    {C C' : D.Ψc k} (hCα : C ≠ D.coord α k) (hCβ : C ≠ D.coord β k) (hC'α : C' ≠ D.coord α k)
    (hC'β : C' ≠ D.coord β k) :
    ∃ v : jHull G Ω, (v : G) ∈ D.L k ∧ (v : G) • α = α ∧ (v : G) • β = β ∧
      D.ρ k v (D.coord β k) = D.coord β k ∧ D.ρ k v C = C' := by
  by_cases hCC' : C = C'
  · refine ⟨1, one_mem _, ?_, ?_, ?_, ?_⟩ <;>
      simp only [OneMemClass.coe_one, one_smul, map_one, Perm.one_apply, hCC']
  obtain ⟨σ, hσA, hσ2, hσα, hσβ, hσC⟩ := exists_involution_alternatingGroup_fix_two_apply_eq h6
    hCα hCβ hC'α hC'β hCC'
  obtain ⟨v, hvL, hv2, hvσ⟩ := D.exists_mul_self_eq_one_rho_eq (by rw [hk]; exact hσA) hσ2
  exact ⟨v, hvL, D.smul_eq_of_mem_L_of_mul_self h24 hvL hv2 (by rw [hvσ]; exact hσα) α
    (mem_orbit_self α), D.smul_eq_of_mem_L_of_mul_self h24 hvL hv2 (by rw [hvσ]; exact hσβ) β
    (mem_orbit_self β), by rw [hvσ]; exact hσβ, by rw [hvσ]; exact hσC⟩

theorem exists_isPGroup_fixSet_eq (h24 : SocInvFixesBlocks D) {k : D.ι}
    (hk : D.M k = alternatingGroup (D.Ψc k)) (h7 : 7 ≤ Fintype.card (D.Ψc k))
    {b₁ b₂ b₃ : D.Ψc k} (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ (S : Subgroup G) ≤ D.L k ∧
      fixSet Ω S = {ω | D.coord ω k = b₁ ∨ D.coord ω k = b₂ ∨ D.coord ω k = b₃} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hTA, hTfix, -⟩ := exists_isPGroup_fixSet_eq_triple (D.odd_card_Ψc k) h7 h12 h13 h23
  obtain ⟨P, -, hPL, hP, hPT⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le (D.ρ k)
    (H := (D.L k).subgroupOf (jHull G Ω)) hT (by rw [← hk] at hTA; exact hTA) IsPGroup.of_bot
    bot_le (by rw [Subgroup.map_bot]; exact bot_le)
  have hfixT : ∀ σ ∈ T, ∀ c, (c = b₁ ∨ c = b₂ ∨ c = b₃) → σ c = c := fun σ hσ c hc => by
    have hc' : c ∈ fixSet (D.Ψc k) T := by
      rw [hTfix]
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hc
    exact hc' σ hσ
  refine ⟨P.map (jHull G Ω).subtype, hP.map _, fun _ ⟨p, hp, hpg⟩ => hpg ▸ hPL hp, ?_⟩
  ext ω
  constructor
  · intro hω
    have hc : D.coord ω k ∈ fixSet (D.Ψc k) T := fun σ hσ => by
      rw [← hPT] at hσ
      obtain ⟨p, hp, rfl⟩ := hσ
      show D.ρ k p (D.coord ω k) = D.coord ω k
      rw [← D.coord_smul]
      exact congrArg (D.coord · k) (hω _ ⟨p, hp, rfl⟩)
    rw [hTfix] at hc
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq] using hc
  · intro hω _ ⟨p, hp, hpg⟩
    obtain ⟨n, hn⟩ := hP ⟨p, hp⟩
    rw [← hpg]
    exact D.smul_eq_of_mem_L_of_pow_two_pow h24 hk (by omega) (hPL hp)
      (a := n) (congrArg Subtype.val hn) (hfixT _ (hPT ▸ ⟨p, hp, rfl⟩) _ hω)

omit [Finite G] in
theorem mem_stabilizer_coord_fibres_iff {k : D.ι} {T : Set (D.Ψc k)} {h : jHull G Ω} :
    (h : G) ∈ stabilizer G {ω | D.coord ω k ∈ T} ↔ ∀ c, D.ρ k h c ∈ T ↔ c ∈ T := by
  rw [mem_stabilizer_iff]
  constructor
  · intro hh c
    obtain ⟨ω, rfl⟩ := D.exists_coord_apply_eq k c
    rw [← D.coord_smul]
    change (h : G) • ω ∈ {ω | D.coord ω k ∈ T} ↔ ω ∈ {ω | D.coord ω k ∈ T}
    conv_rhs => rw [← Set.smul_mem_smul_set_iff (a := (h : G)), hh]
  · intro hh
    ext ω
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← hh,
      ← D.coord_smul]
    rw [smul_inv_smul]

end HoltData

end LemmaP

section Parts

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem card_eq_mul_card_fibre_of_forall {A : Type*} [Finite A] {Δ : Type*} (f : A → Δ)
    {P : Set Δ} [Finite P] (hfP : ∀ a, f a ∈ P) {c₀ : Δ}
    (hmove : ∀ c ∈ P, ∃ e : A ≃ A, ∀ a, f (e a) = c₀ ↔ f a = c) :
    Nat.card A = Nat.card {a : A // f a = c₀} * Nat.card P := by
  rw [← card_preimage_eq_mul f fun c hc => ?_]
  · exact (Nat.card_congr (Equiv.subtypeUnivEquiv hfP)).symm
  · obtain ⟨e, he⟩ := hmove c hc
    exact Nat.card_congr (e.subtypeEquiv fun a => (he a).symm)

private def conjLongInvAt {α : Ω} {v : G} (hv : v • α = α) :
    longInvAt G Ω α ≃ longInvAt G Ω α where
  toFun s := ⟨v * s * v⁻¹, by simpa [hv] using conj_mem_longInvAt s.2 v⟩
  invFun s := ⟨v⁻¹ * s * v⁻¹⁻¹, by
    simpa [inv_smul_eq_iff.mpr hv.symm] using conj_mem_longInvAt s.2 v⁻¹⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])

private def conjLongInvSwap {α β : Ω} {v : G} (hvα : v • α = α) (hvβ : v • β = β) :
    longInvSwap G Ω α β ≃ longInvSwap G Ω α β where
  toFun s := ⟨v * s * v⁻¹, by simpa [hvα, hvβ] using conj_mem_longInvSwap s.2 v⟩
  invFun s := ⟨v⁻¹ * s * v⁻¹⁻¹, by
    simpa [inv_smul_eq_iff.mpr hvα.symm, inv_smul_eq_iff.mpr hvβ.symm] using
      conj_mem_longInvSwap s.2 v⁻¹⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])

end Parts

section PartsData

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

namespace HoltData

variable (D : HoltData G Ω)

theorem mem_stabilizer_iff_of_mem_longInvAt {k : D.ι} {α β : Ω} {b₃ : D.Ψc k}
    (hc : D.coord α k ≠ D.coord β k) {s : G} (hs : s ∈ longInvAt G Ω α) :
    s ∈ stabilizer G {ω | D.coord ω k ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k))} ↔
      D.ρ k ⟨s, mem_jHull_of_mem_longInv hs.1⟩ (D.coord β k) = b₃ := by
  set σ := D.ρ k ⟨s, mem_jHull_of_mem_longInv hs.1⟩
  have hσJ := D.rho_mem_longInvAt hs k
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [← Perm.mul_apply, mul_self_eq_one_of_mem_longInv hσJ.1, Perm.one_apply]
  have hσ1 : σ (D.coord α k) = D.coord α k := hσJ.2
  rw [D.mem_stabilizer_coord_fibres_iff (h := ⟨s, mem_jHull_of_mem_longInv hs.1⟩)]
  constructor
  · intro h
    have h2 := (h (D.coord β k)).mpr (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    rcases h2 with h2 | h2 | h2
    · exact absurd (σ.injective (h2.trans hσ1.symm)).symm hc
    · exact absurd ((apply_eq_self_iff_of_mem_longInvAt_perm hσJ).mp h2).symm hc
    · exact h2
  · intro h
    have hσT : ∀ c ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k)),
        σ c ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k)) := by
      rintro c (rfl | rfl | rfl)
      · rw [hσ1]; simp
      · rw [h]; simp
      · rw [← h, hσσ]; simp
    exact fun c => ⟨fun hc' => hσσ c ▸ hσT _ hc', hσT c⟩

omit [Finite G] in
theorem mem_stabilizer_iff_of_mem_longInvSwap {k : D.ι} {α β : Ω} {b₃ : D.Ψc k}
    (h13 : D.coord α k ≠ b₃) (h23 : D.coord β k ≠ b₃) {s : G} (hs : s ∈ longInvSwap G Ω α β) :
    s ∈ stabilizer G {ω | D.coord ω k ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k))} ↔
      D.ρ k ⟨s, mem_jHull_of_mem_longInv hs.1⟩ b₃ = b₃ := by
  set σ := D.ρ k ⟨s, mem_jHull_of_mem_longInv hs.1⟩
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [← Perm.mul_apply, ← map_mul,
      show (⟨s, mem_jHull_of_mem_longInv hs.1⟩ * ⟨s, mem_jHull_of_mem_longInv hs.1⟩ :
        jHull G Ω) = 1 from Subtype.ext (mul_self_eq_one_of_mem_longInv hs.1), map_one,
      Perm.one_apply]
  have hσ12 : σ (D.coord α k) = D.coord β k := by
    rw [← D.coord_smul]
    exact congrArg (D.coord · k) hs.2
  have hσ21 : σ (D.coord β k) = D.coord α k := by rw [← hσ12, hσσ]
  rw [D.mem_stabilizer_coord_fibres_iff (h := ⟨s, mem_jHull_of_mem_longInv hs.1⟩)]
  constructor
  · intro h
    have h2 := (h b₃).mpr (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    rcases h2 with h2 | h2 | h2
    · exact absurd (σ.injective (h2.trans hσ21.symm)) h23.symm
    · exact absurd (σ.injective (h2.trans hσ12.symm)) h13.symm
    · exact h2
  · intro h
    have hσT : ∀ c ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k)),
        σ c ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k)) := by
      rintro c (rfl | rfl | rfl)
      · rw [hσ12]; simp
      · rw [hσ21]; simp
      · rw [h]; simp
    exact fun c => ⟨fun hc' => hσσ c ▸ hσT _ hc', hσT c⟩

theorem card_longInvAt_eq_mul_of_alternating (h24 : SocInvFixesBlocks D) {k : D.ι}
    (hk : D.M k = alternatingGroup (D.Ψc k)) (h6 : 6 ≤ Fintype.card (D.Ψc k)) {α β : Ω}
    (hc : D.coord α k ≠ D.coord β k) {b₃ : D.Ψc k} (h13 : D.coord α k ≠ b₃)
    (h23 : D.coord β k ≠ b₃) :
    Nat.card (longInvAt G Ω α) = Nat.card ↥(longInvAt G Ω α ∩ (stabilizer G
      {ω | D.coord ω k ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k))} : Set G)) *
        Nat.card ↥({c | c ≠ D.coord α k ∧ c ≠ D.coord β k} : Set (D.Ψc k)) := by
  classical
  let f : longInvAt G Ω α → D.Ψc k := fun s =>
    D.ρ k ⟨s, mem_jHull_of_mem_longInv s.2.1⟩ (D.coord β k)
  have hfP : ∀ s, f s ∈ ({c | c ≠ D.coord α k ∧ c ≠ D.coord β k} : Set (D.Ψc k)) := fun s => by
    have hσJ := D.rho_mem_longInvAt s.2 k
    exact ⟨fun h => hc (((D.ρ k _).injective (h.trans hσJ.2.symm)).symm),
      fun h => hc ((apply_eq_self_iff_of_mem_longInvAt_perm hσJ).mp h).symm⟩
  have hmove : ∀ c ∈ ({c | c ≠ D.coord α k ∧ c ≠ D.coord β k} : Set (D.Ψc k)),
      ∃ e : longInvAt G Ω α ≃ longInvAt G Ω α, ∀ s, f (e s) = b₃ ↔ f s = c := by
    intro c hcP
    obtain ⟨v, -, hvα, -, hvb₂, hvc⟩ := D.exists_mem_L_fix_rho_apply_eq h24 hk h6 hcP.1 hcP.2
      (Ne.symm h13) (Ne.symm h23)
    refine ⟨conjLongInvAt hvα, fun s => ?_⟩
    have hfe : f (conjLongInvAt hvα s) = D.ρ k v (f s) := by
      show D.ρ k (v * ⟨s, mem_jHull_of_mem_longInv s.2.1⟩ * v⁻¹) (D.coord β k) = _
      rw [map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply,
        Perm.inv_eq_iff_eq.mpr hvb₂.symm]
    rw [hfe, ← hvc, (D.ρ k v).injective.eq_iff]
  rw [card_eq_mul_card_fibre_of_forall f hfP hmove]
  congr 1
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun s =>
    (D.mem_stabilizer_iff_of_mem_longInvAt hc s.2).symm).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _))

theorem card_longInvSwap_eq_mul_of_alternating (h24 : SocInvFixesBlocks D) {k : D.ι}
    (hk : D.M k = alternatingGroup (D.Ψc k)) (h6 : 6 ≤ Fintype.card (D.Ψc k)) {α β : Ω}
    (hc : D.coord α k ≠ D.coord β k) {b₃ : D.Ψc k} (h13 : D.coord α k ≠ b₃)
    (h23 : D.coord β k ≠ b₃) :
    Nat.card (longInvSwap G Ω α β) = Nat.card ↥(longInvSwap G Ω α β ∩ (stabilizer G
      {ω | D.coord ω k ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k))} : Set G)) *
        Nat.card ↥({c | c ≠ D.coord α k ∧ c ≠ D.coord β k} : Set (D.Ψc k)) := by
  classical
  let γ' : longInvSwap G Ω α β → Ω := fun s => (exists_mem_longInvAt s.2.1).choose
  have hγ' : ∀ s, (s : G) ∈ longInvAt G Ω (γ' s) :=
    fun s => (exists_mem_longInvAt s.2.1).choose_spec
  let g : longInvSwap G Ω α β → D.Ψc k := fun s => D.coord (γ' s) k
  have hg : ∀ s c, g s = c ↔ D.ρ k ⟨s, mem_jHull_of_mem_longInv s.2.1⟩ c = c := fun s c => by
    rw [apply_eq_self_iff_of_mem_longInvAt_perm (D.rho_mem_longInvAt (hγ' s) k), eq_comm]
  have hσ12 : ∀ s : longInvSwap G Ω α β,
      D.ρ k ⟨s, mem_jHull_of_mem_longInv s.2.1⟩ (D.coord α k) = D.coord β k := fun s => by
    rw [← D.coord_smul]
    exact congrArg (D.coord · k) s.2.2
  have hgP : ∀ s, g s ∈ ({c | c ≠ D.coord α k ∧ c ≠ D.coord β k} : Set (D.Ψc k)) := by
    intro s
    refine ⟨fun h => hc ?_, fun h => hc ?_⟩
    · rw [← (hg s _).mp h, hσ12]
    · exact (D.ρ k _).injective ((hσ12 s).trans ((hg s _).mp h).symm)
  have hmove : ∀ c ∈ ({c | c ≠ D.coord α k ∧ c ≠ D.coord β k} : Set (D.Ψc k)),
      ∃ e : longInvSwap G Ω α β ≃ longInvSwap G Ω α β, ∀ s, g (e s) = b₃ ↔ g s = c := by
    intro c hcP
    obtain ⟨v, -, hvα, hvβ, -, hvc⟩ := D.exists_mem_L_fix_rho_apply_eq h24 hk h6 hcP.1 hcP.2
      (Ne.symm h13) (Ne.symm h23)
    refine ⟨conjLongInvSwap hvα hvβ, fun s => ?_⟩
    have hγe : γ' (conjLongInvSwap hvα hvβ s) = (v : G) • γ' s :=
      eq_of_mem_longInvAt (hγ' _) (conj_mem_longInvAt (hγ' s) (v : G))
    have hge : g (conjLongInvSwap hvα hvβ s) = D.ρ k v (g s) := by
      show D.coord (γ' (conjLongInvSwap hvα hvβ s)) k = _
      rw [hγe, D.coord_smul]
    rw [hge, ← hvc, (D.ρ k v).injective.eq_iff]
  rw [card_eq_mul_card_fibre_of_forall g hgP hmove]
  congr 1
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun s => (hg s b₃).trans
    (D.mem_stabilizer_iff_of_mem_longInvSwap h13 h23 s.2).symm).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _))

end HoltData

end PartsData

section Case2a

variable {G : Type} [Group G] [Finite G] {Ω : Type}
  [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

omit [FaithfulSMul G Ω] in
theorem lemma27iAt_of_alternating (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1))
    (hIH : Lemma27iBelow (Nat.card G) (Nat.card Ω)) (D : HoltData G Ω)
    (h24 : SocInvFixesBlocks D) {k : D.ι} (hk : D.M k = alternatingGroup (D.Ψc k))
    (hk7 : 7 ≤ Fintype.card (D.Ψc k)) {α β : Ω} (hαβ : α ≠ β)
    (hc : D.coord α k ≠ D.coord β k) : Lemma27iAt G Ω α β := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := longInvSwap_nonempty hG α β
  obtain ⟨γ, hγ⟩ := exists_mem_longInvAt hu.1
  set b₃ := D.coord γ k
  have huJ := D.rho_mem_longInvAt hγ k
  have hu12 : D.ρ k ⟨u, mem_jHull_of_mem_longInv hu.1⟩ (D.coord α k) = D.coord β k := by
    rw [← D.coord_smul]
    exact congrArg (D.coord · k) hu.2
  have h13 : D.coord α k ≠ b₃ := fun h =>
    hc (by rw [← hu12, (apply_eq_self_iff_of_mem_longInvAt_perm huJ).mpr h])
  have h23 : D.coord β k ≠ b₃ := fun h =>
    hc ((D.ρ k _).injective (hu12.trans ((apply_eq_self_iff_of_mem_longInvAt_perm huJ).mpr h).symm))
  obtain ⟨S, hS, -, hSfix⟩ := D.exists_isPGroup_fixSet_eq h24 hk hk7 hc h13 h23
  set Γ := fixSet Ω S
  have hΓ : Γ = {ω | D.coord ω k ∈ ({D.coord α k, D.coord β k, b₃} : Set (D.Ψc k))} := by
    rw [hSfix]
    ext ω
    simp
  have hαΓ : α ∈ Γ := by rw [hΓ]; simp
  have hβΓ : β ∈ Γ := by rw [hΓ]; simp
  have hodd : Odd (Nat.card Γ) := hG.odd_card_fixSet hS
  have h3 : 3 ≤ Nat.card Γ := by
    have : Nontrivial Γ := ⟨⟨⟨α, hαΓ⟩, ⟨β, hβΓ⟩, fun h => hαβ (congrArg Subtype.val h)⟩⟩
    have h2 : 1 < Nat.card Γ := Finite.one_lt_card_iff_nontrivial.mpr this
    obtain ⟨j, hj⟩ := hodd
    omega
  have hS1 : S ≠ ⊥ := by
    intro hSbot
    obtain ⟨c, -, hcT⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({D.coord α k, D.coord β k, b₃} : Finset (D.Ψc k))) (t := Finset.univ)
      (by rw [Finset.card_univ]; exact Finset.card_le_three.trans_lt (by omega))
    obtain ⟨ω, hω⟩ := D.exists_coord_apply_eq k c
    have hωΓ : ω ∈ Γ := by
      show ω ∈ fixSet Ω S
      rw [hSbot, fixSet_bot]
      exact Set.mem_univ ω
    rw [hΓ] at hωΓ
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hω] at hωΓ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcT
    exact hcT hωΓ
  set X := Subgroup.centralizer (S : Set G)
  have hXN : X ≤ Subgroup.normalizer (S : Set G) := Subgroup.centralizer_le_normalizer _
  have hX : X ≤ stabilizer G Γ := hXN.trans (normalizer_le_stabilizer_fixSet S)
  have hY := isStarGroup_inducedPerm_fixSet hG hS h3 le_rfl hXN
  have hBY := hB.induced X Γ hX
  have hY27 := hIH _ _ (Or.inl (card_inducedPerm_fixSet_lt_card hS hS1 le_rfl hXN)) hY hBY
    ⟨α, hαΓ⟩ ⟨β, hβΓ⟩ fun h => hαβ (congrArg Subtype.val h)
  have hne : ∃ x ∈ X, x ∈ longInv G Ω := by
    obtain ⟨t, ht, htC⟩ := hG.star α S hS (mem_fixSet_iff_le_stabilizer.mp hαΓ) h3
    exact ⟨t, htC, ht.1⟩
  have hext : ∀ y ∈ longInv G Ω, y ∈ stabilizer G Γ →
      ∃ c ∈ longInv G Ω, c ∈ X ∧ ∀ γ ∈ Γ, c • γ = y • γ := fun y hy hyΓ =>
    exists_mem_longInv_centralizer_smul_eq hG (hB.of_le le_rfl (Nat.le_succ _)) h3 hS
      (fun s hs => (mem_fixingSubgroup_iff G).mpr fun ω hω => hω s hs) hy hyΓ
  have hsec := card_longInvSwap_inter_eq_of_section hG hodd h3 hX hY hBY hne hext hαΓ hβΓ hY27
  have h6 : 6 ≤ Fintype.card (D.Ψc k) := by omega
  have hA := D.card_longInvAt_eq_mul_of_alternating h24 hk h6 hc h13 h23
  have hW := D.card_longInvSwap_eq_mul_of_alternating h24 hk h6 hc h13 h23
  rw [← hΓ] at hA hW
  refine ⟨by rw [hW, hA, hsec], fun δ₀ hδ₀ => holtDelta'_eq_orbit_of_subset hδ₀ ?_⟩
  have hmove : ∀ δ ∈ holtDelta' G Ω α β, ∃ s ∈ longInvAt G Ω α, s ∈ stabilizer G Γ ∧
      ∃ g ∈ stabilizer G α ⊓ stabilizer G β, g • δ = s • β := by
    rintro _ ⟨s, hs, rfl⟩
    have hσJ := D.rho_mem_longInvAt hs k
    have hc1 : D.ρ k ⟨s, mem_jHull_of_mem_longInv hs.1⟩ (D.coord β k) ≠ D.coord α k :=
      fun h => hc (((D.ρ k _).injective (h.trans hσJ.2.symm)).symm)
    have hc2 : D.ρ k ⟨s, mem_jHull_of_mem_longInv hs.1⟩ (D.coord β k) ≠ D.coord β k :=
      fun h => hc ((apply_eq_self_iff_of_mem_longInvAt_perm hσJ).mp h).symm
    obtain ⟨v, -, hvα, hvβ, hvb₂, hvc⟩ := D.exists_mem_L_fix_rho_apply_eq h24 hk h6 hc1 hc2
      (Ne.symm h13) (Ne.symm h23)
    have hs' : (v : G) * s * (v : G)⁻¹ ∈ longInvAt G Ω α := by
      simpa [hvα] using conj_mem_longInvAt hs (v : G)
    refine ⟨_, hs', ?_, v, ⟨hvα, hvβ⟩, ?_⟩
    · rw [hΓ, D.mem_stabilizer_iff_of_mem_longInvAt hc hs']
      show D.ρ k (v * ⟨s, mem_jHull_of_mem_longInv hs.1⟩ * v⁻¹) (D.coord β k) = b₃
      rw [map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply,
        Perm.inv_eq_iff_eq.mpr hvb₂.symm]
      exact hvc
    · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hvβ.symm]
  intro δ hδ
  obtain ⟨s₁, hs₁, hs₁Γ, g₁, hg₁, hg₁δ⟩ := hmove δ hδ
  obtain ⟨s₂, hs₂, hs₂Γ, g₂, hg₂, hg₂δ⟩ := hmove δ₀ hδ₀
  obtain ⟨x, hx, hxs⟩ := exists_smul_eq_of_section hodd h3 hX hext hαΓ hβΓ hY27 hs₂ hs₂Γ hs₁ hs₁Γ
  refine ⟨⟨g₁⁻¹ * x * g₂, mul_mem (mul_mem (inv_mem hg₁) (Subgroup.mem_inf.mp hx).2) hg₂⟩, ?_⟩
  show (g₁⁻¹ * x * g₂) • δ₀ = δ
  rw [mul_smul, mul_smul, hg₂δ, hxs, ← hg₁δ, inv_smul_smul]

end Case2a

end CFSG.Holt.H78
