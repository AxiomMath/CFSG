module

public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped commutatorElement

namespace G312

open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

section Counting

variable {J : Type*} [Group J] [Finite J]

theorem false_of_three_cosets {C : Subgroup J} {α β ζ : J} (hαβ : α * β = β * α)
    (hCα : ∀ c ∈ C, c * α = α * c) (hCβ : ∀ c ∈ C, c * β = β * c)
    (hCC : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c)
    (hinv : ∀ u ∈ Subgroup.closure (insert α (insert β (C : Set J))), u ^ 2 = 1 →
      u = 1 ∨ u = ζ)
    (hα2 : α ^ 2 ∈ C) (hβ2 : β ^ 2 ∈ C) (hαC : α ∉ C) (hβC : β ∉ C) (hαβC : α * β ∉ C) :
    False := by
  classical
  set k : Set J := insert α (insert β (C : Set J)) with hk
  set R := Subgroup.closure k with hR
  have hpair : k.Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl | hx <;> rcases hy with rfl | rfl | hy
    · rfl
    · exact hαβ
    · exact (hCα y hy).symm
    · exact hαβ.symm
    · rfl
    · exact (hCβ y hy).symm
    · exact hCα x hx
    · exact hCβ x hx
    · exact hCC x hx y hy
  have hcomm : IsMulCommutative R := Subgroup.isMulCommutative_closure hpair
  have hRc : ∀ x y : R, x * y = y * x := fun x y => hcomm.is_comm.comm x y
  have hCR : C ≤ R := fun c hc => Subgroup.subset_closure (Or.inr (Or.inr hc))
  have hαR : α ∈ R := Subgroup.subset_closure (Or.inl rfl)
  have hβR : β ∈ R := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hsq : ∀ x ∈ R, x ^ 2 ∈ C := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | hx
      · exact hα2
      · exact hβ2
      · exact C.pow_mem hx 2
    | one => rw [one_pow]; exact C.one_mem
    | mul x y hx hy ihx ihy =>
      have h := congrArg Subtype.val (hRc ⟨x, hx⟩ ⟨y, hy⟩)
      simp only [Subgroup.coe_mul] at h
      rw [(Commute.mul_pow h 2)]
      exact C.mul_mem ihx ihy
    | inv x hx ihx => rw [inv_pow]; exact C.inv_mem ihx
  let s : R →* R :=
    { toFun := fun x => x ^ 2
      map_one' := one_pow 2
      map_mul' := fun x y => Commute.mul_pow (hRc x y) 2 }
  have hker : Nat.card s.ker ≤ 2 := by
    let f : s.ker → Bool := fun x => decide (x = 1)
    have hf : Function.Injective f := by
      intro x y hxy
      have hx2 : ((x : R) : J) ^ 2 = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker] at this
        simpa [s] using congrArg Subtype.val this
      have hy2 : ((y : R) : J) ^ 2 = 1 := by
        have := y.2
        rw [MonoidHom.mem_ker] at this
        simpa [s] using congrArg Subtype.val this
      by_cases hx1 : x = 1
      · by_cases hy1 : y = 1
        · rw [hx1, hy1]
        · simp [f, hx1, hy1] at hxy
      · by_cases hy1 : y = 1
        · simp [f, hx1, hy1] at hxy
        · have hx1' : ((x : R) : J) ≠ 1 := fun h => hx1 (Subtype.ext (Subtype.ext h))
          have hy1' : ((y : R) : J) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
          have hx' := (hinv _ (x : R).2 hx2).resolve_left hx1'
          have hy' := (hinv _ (y : R).2 hy2).resolve_left hy1'
          exact Subtype.ext (Subtype.ext (hx'.trans hy'.symm))
    calc Nat.card s.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  have hrange : Nat.card s.range ≤ Nat.card C := by
    let f : s.range → C := fun x => ⟨((x : R) : J), by
      obtain ⟨y, hy⟩ := x.2
      rw [← hy]
      exact hsq _ (y : R).2⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h : ((x : R) : J) = ((y : R) : J) := congrArg (fun z : C => (z : J)) hxy
      exact Subtype.ext (Subtype.ext h)
    exact Nat.card_le_card_of_injective f hf
  set C' : Subgroup R := C.subgroupOf R with hC'
  have hidx : 2 < C'.index := by
    rw [Subgroup.index]
    have : Finite (R ⧸ C') := inferInstance
    have : Fintype (R ⧸ C') := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    refine Fintype.two_lt_card_iff.mpr ⟨(1 : R ⧸ C'), QuotientGroup.mk (⟨α, hαR⟩ : R),
      QuotientGroup.mk (⟨β, hβR⟩ : R), ?_, ?_, ?_⟩
    · intro h
      rw [eq_comm, QuotientGroup.eq_one_iff, hC', Subgroup.mem_subgroupOf] at h
      exact hαC h
    · intro h
      rw [eq_comm, QuotientGroup.eq_one_iff, hC', Subgroup.mem_subgroupOf] at h
      exact hβC h
    · intro h
      rw [QuotientGroup.eq, hC', Subgroup.mem_subgroupOf] at h
      apply hαβC
      have h' : α⁻¹ * β ∈ C := by simpa using h
      have : α * β = α ^ 2 * (α⁻¹ * β) := by group
      rw [this]
      exact C.mul_mem hα2 h'
  have hcardC : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv
  have hC0 : 0 < Nat.card C := Nat.card_pos
  have h1 := C'.card_mul_index
  have h2 := Subgroup.card_ker_mul_card_range s
  rw [hcardC] at h1
  have h3 : 3 * Nat.card C ≤ Nat.card R := by
    rw [← h1]
    nlinarith
  have h4 : Nat.card R ≤ 2 * Nat.card C := by
    rw [← h2]
    exact Nat.mul_le_mul hker hrange
  omega

end Counting

section Lifts

variable {L : Type*} [Group L]

theorem commutator_sq_eq_one {a b : L} (hab : ⁅a, b⁆ ∈ Subgroup.center L)
    (hb : b ^ 2 ∈ Subgroup.center L) : ⁅a, b⁆ ^ 2 = 1 := by
  set c := ⁅a, b⁆ with hc
  have hcb : b * c = c * b := Subgroup.mem_center_iff.mp hab b
  have hab' : a * b * a⁻¹ = c * b := by rw [hc, commutatorElement_def]; group
  have h1 : a * b ^ 2 * a⁻¹ = b ^ 2 := by
    rw [Subgroup.mem_center_iff.mp hb a]
    group
  have h2 : a * b ^ 2 * a⁻¹ = c ^ 2 * b ^ 2 := by
    calc a * b ^ 2 * a⁻¹ = (a * b * a⁻¹) * (a * b * a⁻¹) := by
          rw [pow_two]; simp only [mul_assoc, inv_mul_cancel_left]
      _ = c * (b * c) * b := by rw [hab']; simp only [mul_assoc]
      _ = c ^ 2 * b ^ 2 := by rw [hcb, pow_two, pow_two]; simp only [mul_assoc]
  have h3 : c ^ 2 * b ^ 2 = 1 * b ^ 2 := by rw [← h2, h1, one_mul]
  exact mul_right_cancel h3

theorem commutator_mul_left {x y z : L} (hyz : ⁅y, z⁆ ∈ Subgroup.center L) :
    ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  have hx : x * ⁅y, z⁆ = ⁅y, z⁆ * x := Subgroup.mem_center_iff.mp hyz x
  calc ⁅x * y, z⁆ = (x * ⁅y, z⁆) * (z * x⁻¹ * z⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [hx]; simp only [commutatorElement_def]; group

variable {Q : Type*} [Group Q] [Finite Q] (ψ : L →* Q) {ζ : Q}

theorem map_commutator_eq (hker : ψ.ker ≤ Subgroup.center L)
    (hinv : ∀ u ∈ ψ.range, u ^ 2 = 1 → u = 1 ∨ u = ζ) {a b : L}
    (ha : a ^ 2 ∈ Subgroup.center L) (hb : b ^ 2 ∈ Subgroup.center L)
    (hab : ⁅a, b⁆ ∈ Subgroup.center L) (ha1 : a ∉ Subgroup.center L)
    (hb1 : b ∉ Subgroup.center L) (hab1 : a * b ∉ Subgroup.center L) : ψ ⁅a, b⁆ = ζ := by
  have hc2 : ψ ⁅a, b⁆ ^ 2 = 1 := by rw [← map_pow, commutator_sq_eq_one hab hb, map_one]
  rcases hinv _ ⟨_, rfl⟩ hc2 with h1 | h1
  · exfalso
    have hαβ : ψ a * ψ b = ψ b * ψ a := by
      have h : ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ = 1 := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← commutatorElement_def, h1]
      calc ψ a * ψ b = (ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹) * (ψ b * ψ a) := by group
        _ = ψ b * ψ a := by rw [h, one_mul]
    set C := (Subgroup.center L).map ψ with hC
    have hcen : ∀ c ∈ C, ∀ x : L, c * ψ x = ψ x * c := by
      rintro _ ⟨z, hz, rfl⟩ x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    have hnot : ∀ x : L, x ∉ Subgroup.center L → ψ x ∉ C := by
      rintro x hx ⟨z, hz, hzx⟩
      apply hx
      have hk : z⁻¹ * x ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzx, inv_mul_cancel]
      have : x = z * (z⁻¹ * x) := by group
      rw [this]
      exact (Subgroup.center L).mul_mem hz (hker hk)
    refine false_of_three_cosets (C := C) (ζ := ζ) hαβ (fun c hc => hcen c hc a)
      (fun c hc => hcen c hc b) ?_ ?_ ⟨_, ha, map_pow ψ a 2⟩ ⟨_, hb, map_pow ψ b 2⟩
      (hnot a ha1) (hnot b hb1) (by rw [← map_mul]; exact hnot _ hab1)
    · rintro c hc _ ⟨z, -, rfl⟩
      exact hcen c hc z
    · intro u hu hu2
      refine hinv u ?_ hu2
      refine (Subgroup.closure_le _).2 ?_ hu
      rintro x (rfl | rfl | ⟨z, -, rfl⟩)
      · exact ⟨a, rfl⟩
      · exact ⟨b, rfl⟩
      · exact ⟨z, rfl⟩
  · exact h1

end Lifts

section Types

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem exists_mem_not_mem {X : Type*} [Group X] {S : Subgroup X} [Finite S] (F : Finset X)
    (h : F.card < Nat.card S) : ∃ s ∈ S, s ∉ F := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun s : S => (⟨(s : X), hcon s s.2⟩ : F)) := by
    intro x y hxy
    exact Subtype.ext (Subtype.mk.inj hxy)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard] at this
  omega

theorem false_of_typeI
    {L : Type} [Group L] [Finite L] (hI : IsGoldTypeI L) (ψ : L →* Q)
    (hker : ψ.ker ≤ Subgroup.center L) {ζ : Q} (hζ1 : ζ ≠ 1)
    (hinv : ∀ u ∈ ψ.range, u ^ 2 = 1 → u = 1 ∨ u = ζ) : False := by
  classical
  set B := L ⧸ Subgroup.center L
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hBender : fusionIsBenderGroup B := by
    rcases hI with ⟨n, hn, he⟩ | ⟨n, hn, he⟩ | ⟨n, hn, he⟩
    · exact Or.inl ⟨n, by omega, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨n, hn, he⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Sylow 2 B := default
  obtain ⟨D, h⟩ := G3a.exists_borelSetup hBender T
  have hmemZ : ∀ y : L, y ∈ Subgroup.center L ↔ π y = 1 := fun y =>
    (QuotientGroup.eq_one_iff y).symm
  have key : ∀ y₁ y₂ : L, (π y₁) ^ 2 = 1 → (π y₂) ^ 2 = 1 → π y₁ * π y₂ = π y₂ * π y₁ →
      π y₁ ≠ 1 → π y₂ ≠ 1 → π y₁ * π y₂ ≠ 1 →
      ⁅y₁, y₂⁆ ∈ Subgroup.center L ∧ ψ ⁅y₁, y₂⁆ = ζ := by
    intro y₁ y₂ h1 h2 h12 hn1 hn2 hn12
    have hc : ⁅y₁, y₂⁆ ∈ Subgroup.center L := by
      rw [hmemZ, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h12]
      group
    refine ⟨hc, map_commutator_eq ψ hker hinv ?_ ?_ hc ?_ ?_ ?_⟩
    · rw [hmemZ, map_pow, h1]
    · rw [hmemZ, map_pow, h2]
    · rwa [hmemZ]
    · rwa [hmemZ]
    · rwa [hmemZ, map_mul]
  by_cases hab : IsMulCommutative (T : Subgroup B)
  ·
    have hZT : sylowCenter (T : Subgroup B) = T := by
      refine le_antisymm inf_le_left fun t ht => mem_sylowCenter.mpr ⟨ht, fun s hs => ?_⟩
      exact congrArg Subtype.val (hab.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    have hsq : ∀ t ∈ (T : Subgroup B), t ^ 2 = 1 := fun t ht => h.sq t (by rw [hZT]; exact ht)
    have h8 : 8 ≤ Nat.card (T : Subgroup B) := by
      rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      · rw [(h.orders_psl2 (by omega) e).1]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      · exfalso
        obtain ⟨hZ, hTc, -⟩ := h.orders_sz hn e
        rw [hZT, hTc, ← pow_mul] at hZ
        have := Nat.pow_right_injective (le_refl 2) hZ
        omega
      · exfalso
        obtain ⟨hZ, hTc, -⟩ := h.orders_psu3 hn e
        rw [hZT, hTc, ← pow_mul] at hZ
        have := Nat.pow_right_injective (le_refl 2) hZ
        omega
    obtain ⟨v₁, hv₁, hv₁1⟩ := exists_mem_not_mem (S := (T : Subgroup B)) {1}
      (by rw [Finset.card_singleton]; omega)
    obtain ⟨v₂, hv₂, hv₂1⟩ := exists_mem_not_mem (S := (T : Subgroup B)) {1, v₁}
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    obtain ⟨v₃, hv₃, hv₃1⟩ := exists_mem_not_mem (S := (T : Subgroup B)) {1, v₁, v₂, v₁ * v₂}
      (lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hv₁1 hv₂1 hv₃1
    have hcomm : ∀ x ∈ (T : Subgroup B), ∀ y ∈ (T : Subgroup B), x * y = y * x :=
      fun x hx y hy => congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hinvT : ∀ x ∈ (T : Subgroup B), x⁻¹ = x := fun x hx =>
      inv_eq_of_mul_eq_one_right (by rw [← pow_two, hsq x hx])
    obtain ⟨a₁, rfl⟩ := hπs v₁
    obtain ⟨a₂, rfl⟩ := hπs v₂
    obtain ⟨a₃, rfl⟩ := hπs v₃
    have hne12 : π a₁ * π a₂ ≠ 1 := fun h' => hv₂1.2 (by
      rw [← hinvT _ hv₁]; exact eq_inv_of_mul_eq_one_right h')
    have hne13 : π a₁ * π a₃ ≠ 1 := fun h' => hv₃1.2.1 (by
      rw [← hinvT _ hv₁]; exact eq_inv_of_mul_eq_one_right h')
    have hne23 : π a₂ * π a₃ ≠ 1 := fun h' => hv₃1.2.2.1 (by
      rw [← hinvT _ hv₂]; exact eq_inv_of_mul_eq_one_right h')
    have hne123 : π a₁ * π a₂ * π a₃ ≠ 1 := fun h' => hv₃1.2.2.2 (by
      rw [← hinvT _ ((T : Subgroup B).mul_mem hv₁ hv₂)]; exact eq_inv_of_mul_eq_one_right h')
    obtain ⟨-, h13⟩ := key a₁ a₃ (hsq _ hv₁) (hsq _ hv₃) (hcomm _ hv₁ _ hv₃) hv₁1 hv₃1.1 hne13
    obtain ⟨hc23, h23⟩ := key a₂ a₃ (hsq _ hv₂) (hsq _ hv₃) (hcomm _ hv₂ _ hv₃) hv₂1.1
      hv₃1.1 hne23
    obtain ⟨-, h123⟩ := key (a₁ * a₂) a₃
      (by rw [map_mul]; exact hsq _ ((T : Subgroup B).mul_mem hv₁ hv₂)) (hsq _ hv₃)
      (by rw [map_mul]; exact hcomm _ ((T : Subgroup B).mul_mem hv₁ hv₂) _ hv₃)
      (by rw [map_mul]; exact hne12) hv₃1.1 (by rw [map_mul]; exact hne123)
    rw [commutator_mul_left hc23, map_mul, h23, h13] at h123
    exact hζ1 (by simpa using h123)
  ·
    obtain ⟨t, ht, htZ⟩ : ∃ t ∈ (T : Subgroup B), t ∉ sylowCenter (T : Subgroup B) := by
      by_contra hcon
      push Not at hcon
      exact hab ⟨⟨fun x y => Subtype.ext ((mem_sylowCenter.mp (hcon y y.2)).2 x x.2)⟩⟩
    have ht2Z : t ^ 2 ∈ sylowCenter (T : Subgroup B) := h.sq_mem_center hab ht
    have ht21 : t ^ 2 ≠ 1 := fun h' => htZ (h.inv t ht h')
    have ht4 : (t ^ 2) ^ 2 = 1 := h.sq _ ht2Z
    obtain ⟨v, hvZ, hv1, hvt⟩ : ∃ v ∈ sylowCenter (T : Subgroup B), v ≠ 1 ∧ v ≠ t ^ 2 := by
      obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ :=
        GoldType.exists_ne_one_of_two_lt (S := sylowCenter (T : Subgroup B))
          (by have := h.four; omega)
      by_cases hxt : x = t ^ 2
      · exact ⟨y, hy, hy1, fun h' => hxy (hxt.trans h'.symm)⟩
      · exact ⟨x, hx, hx1, hxt⟩
    have hv2 : v ^ 2 = 1 := h.sq v hvZ
    obtain ⟨t', rfl⟩ := hπs t
    obtain ⟨v', rfl⟩ := hπs v
    have hvt' : π v' * π t' = π t' * π v' := ((mem_sylowCenter.mp hvZ).2 _ ht).symm
    obtain ⟨-, hψ⟩ := key (t' ^ 2) v' (by rw [map_pow]; exact ht4) hv2
      (by rw [map_pow]; exact ((mem_sylowCenter.mp hvZ).2 _ ((T : Subgroup B).pow_mem ht 2)))
      (by rwa [map_pow]) hv1
      (by
        rw [map_pow]
        intro h'
        apply hvt
        have h'' : π v' = (π t' ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h'
        rw [h'']
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, ht4]))
    have hc : ⁅t', v'⁆ ∈ Subgroup.center L := by
      rw [hmemZ, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← hvt']
      group
    have hv'2 : v' ^ 2 ∈ Subgroup.center L := by rw [hmemZ, map_pow, hv2]
    have hsq1 := commutator_sq_eq_one hc hv'2
    have hone : ⁅t' ^ 2, v'⁆ = 1 := by
      rw [pow_two, commutator_mul_left hc, ← pow_two, hsq1]
    rw [hone, map_one] at hψ
    exact hζ1 hψ.symm

theorem range_eq_bot_of_unique_involution
    {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) (htype : IsGoldTypeI L ∨ IsGoldTypeII L) (ψ : L →* Q) {ζ : Q}
    (hζc : ∀ x ∈ ψ.range, x * ζ = ζ * x)
    (hinv : ∀ u ∈ ψ.range, u ^ 2 = 1 → u = 1 ∨ u = ζ) : ψ.range = ⊥ := by
  classical
  by_contra hne
  have : Group.IsPerfect L := ⟨hL.1⟩
  have hperf : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have heven : 2 ∣ Nat.card ψ.range := by
    by_contra hodd
    have hodd' : Odd (Nat.card ψ.range) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    exact Group.IsPerfect.not_isSolvable ψ.range (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd')
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have hu2 : (u : Q) ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    simpa using congrArg Subtype.val this
  have hu1 : (u : Q) ≠ 1 := by
    intro h1
    have : u = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hu
    omega
  have hζ : (u : Q) = ζ := (hinv _ u.2 hu2).resolve_left hu1
  have hζ1 : ζ ≠ 1 := hζ ▸ hu1
  have hζ2 : ζ ^ 2 = 1 := hζ ▸ hu2
  have hkerne : ψ.ker ≠ ⊤ := by
    intro htop
    apply hne
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    have : x ∈ ψ.ker := htop ▸ Subgroup.mem_top x
    rw [MonoidHom.mem_ker] at this
    rw [this]
    exact Subgroup.one_mem _
  have hker : ψ.ker ≤ Subgroup.center L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL ψ.ker hkerne
  rcases htype with hI | hII
  · exact false_of_typeI hI ψ hker hζ1 hinv
  ·
    obtain ⟨l, hl⟩ : ∃ l : L, ψ l = ζ := by
      obtain ⟨l, hl⟩ := u.2
      exact ⟨l, hl.trans hζ⟩
    have hlZ : l ∈ Subgroup.center L := by
      have hcomap := CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
        ψ.rangeRestrict ψ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
      rw [← hcomap, Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict, hl]
      exact hζc _ y.2
    have hodd : Odd (orderOf l) := by
      have hdvd : orderOf l ∣ Nat.card (Subgroup.center L) := by
        rw [← Subgroup.orderOf_mk l hlZ]
        exact orderOf_dvd_natCard _
      exact Odd.of_dvd_nat hII.1 hdvd
    obtain ⟨k, hk⟩ := hodd
    have h1 : ζ ^ orderOf l = 1 := by rw [← hl, ← map_pow, pow_orderOf_eq_one, map_one]
    rw [hk, pow_succ, pow_mul, hζ2, one_pow, one_mul] at h1
    exact hζ1 h1

end Types

end G312

end CFSG.Goldschmidt
