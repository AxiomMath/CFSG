module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSLFourA8
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SporadicRefine

open Equiv Subgroup
open CFSG.QuasithinUnique.Vol2Native.L239.L42Insp (P0 p0L pm pn pone mem_P0 pn_mul pn_inj pn_one
  P0_le_A8 card_P0)

set_option maxRecDepth 100000 in
theorem p0_abelian_check :
    (p0L.filter fun a => decide (32 ≤ (p0L.filter fun b => pm a b == pm b a).length)).length
      ≤ 8 := by
  decide +kernel

theorem thirty_two_le_of_dvd_sixty_four {k : ℕ} (hk : k ∣ 64) (h16 : 16 < k) : 32 ≤ k := by
  have hk' : k ∈ Nat.divisors 64 := Nat.mem_divisors.2 ⟨hk, by norm_num⟩
  have hd : Nat.divisors 64 = {1, 2, 4, 8, 16, 32, 64} := by decide
  rw [hd] at hk'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
  omega

theorem card_le_sixteen_of_le_P0_of_commute {W : Subgroup (Perm (Fin 8))} (hW : W ≤ P0)
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : Nat.card W ≤ 16 := by
  classical
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card W ∣ 64 := card_P0 ▸ Subgroup.card_dvd_of_le hW
  have h32 : 32 ≤ Nat.card W := thirty_two_le_of_dvd_sixty_four hdvd hlt
  set L8 := p0L.filter fun a => decide (32 ≤ (p0L.filter fun b => pm a b == pm b a).length)
    with hL8
  have hmem : ∀ w : W, pn (w : Perm (Fin 8)) ∈ L8 := by
    intro w
    rw [hL8, List.mem_filter]
    refine ⟨mem_P0.1 (hW w.2), ?_⟩
    rw [decide_eq_true_eq]
    set l := p0L.filter fun b => pm (pn (w : Perm (Fin 8))) b == pm b (pn (w : Perm (Fin 8)))
      with hl
    have hmap : ∀ v : W, pn (v : Perm (Fin 8)) ∈ l := by
      intro v
      rw [hl, List.mem_filter]
      refine ⟨mem_P0.1 (hW v.2), ?_⟩
      rw [← pn_mul, ← pn_mul, hWc _ w.2 _ v.2, beq_self_eq_true]
    let f : W → {b // b ∈ l} := fun v => ⟨pn v, hmap v⟩
    have hf : Function.Injective f := fun a b hab =>
      Subtype.ext (pn_inj (congrArg Subtype.val hab))
    calc 32 ≤ Nat.card W := h32
      _ ≤ Nat.card {b // b ∈ l} := Nat.card_le_card_of_injective f hf
      _ ≤ l.length := card_subtype_mem_le_length l
  let f : W → {a // a ∈ L8} := fun w => ⟨pn w, hmem w⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (pn_inj (congrArg Subtype.val hab))
  have h1 := (Nat.card_le_card_of_injective f hf).trans (card_subtype_mem_le_length L8)
  have h8 : L8.length ≤ 8 := p0_abelian_check
  omega

theorem card_le_sixteen_of_alternating_of_commute {T : Subgroup (alternatingGroup (Fin 8))}
    (hT : IsPGroup 2 T) (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Nat.card T ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  set P : Sylow 2 (alternatingGroup (Fin 8)) :=
    Sylow.ofCard (P0.subgroupOf (alternatingGroup (Fin 8))) card_P0_eq_factorization with hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) P Q
  have hconj : ∀ x ∈ T, ((g⁻¹ * x * g : alternatingGroup (Fin 8)) : Perm (Fin 8)) ∈ P0 := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup (alternatingGroup (Fin 8))) := hTQ hx
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    have h1 : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      rw [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply]
    rw [h1, hP, Sylow.coe_ofCard] at hxQ
    exact mem_subgroupOf.1 hxQ
  set W₀ : Subgroup (Perm (Fin 8)) :=
    (T.map (MulAut.conj g⁻¹).toMonoidHom).map (alternatingGroup (Fin 8)).subtype with hW₀
  have hW₀P : W₀ ≤ P0 := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have h := hconj w hw
    simpa [MulAut.conj_apply] using h
  have hW₀c : ∀ a ∈ W₀, ∀ b ∈ W₀, a * b = b * a := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hTc a ha b hb]
  have hcard : Nat.card W₀ = Nat.card T := by
    rw [hW₀, card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  rw [← hcard]
  exact card_le_sixteen_of_le_P0_of_commute hW₀P hW₀c

theorem mul_comm_of_mul_self {X : Type*} [Group X] {E : Subgroup X}
    (hE : ∀ x ∈ E, x * x = 1) {a b : X} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have hab := hE (a * b) (E.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hE a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hE b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem isPGroup_two_of_mul_self {X : Type*} [Group X] {E : Subgroup X}
    (hE : ∀ x ∈ E, x * x = 1) : IsPGroup 2 E := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq, Subgroup.coe_one]; exact hE _ x.2)⟩

theorem card_le_sixteen_of_mulEquiv_alternating {X : Type*} [Group X]
    (φ : X ≃* alternatingGroup (Fin 8)) {E : Subgroup X} (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 16 := by
  have hE' : ∀ y ∈ E.map φ.toMonoidHom, y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, hE x hx, map_one]
  have h := card_le_sixteen_of_alternating_of_commute (isPGroup_two_of_mul_self hE')
    (fun a ha b hb => mul_comm_of_mul_self hE' ha hb)
  rwa [card_map_of_injective φ.injective] at h

section McL


theorem mcl_card_le_of_mul_self {S : Type} [Group S] [Finite S] (e : S ≃* CFSG.Blueprint.NativeSporadic.McL)
    {E : Subgroup S} (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 32 := by
  classical
  by_cases hE1 : E = ⊥
  · rw [hE1, card_bot]
    norm_num
  obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
  have hs : orderOf (s : S) = 2 := orderOf_eq_prime (by rw [sq]; exact hE _ s.2) (by
    intro h
    exact hs1 (Subtype.ext h))
  obtain ⟨-, -, ⟨φ⟩⟩ :=
    Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate ⟨e⟩ hs
  set C : Subgroup S := centralizer ({(s : S)} : Set S) with hC
  set s' : C := ⟨s, Sporadic.Recognition.McLCentralizer.self_mem_centralizer (s : S)⟩ with hs'
  have hEC : E ≤ C := by
    intro x hx
    rw [hC, mem_centralizer_singleton_iff]
    exact mul_comm_of_mul_self hE hx s.2
  set E' : Subgroup C := E.subgroupOf C with hE'
  have hE'card : Nat.card E' = Nat.card E := Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv
  set ψ : C →* alternatingGroup (Fin 8) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (zpowers s')) with hψ
  set f : E' →* alternatingGroup (Fin 8) := ψ.comp E'.subtype with hf
  have hker : Nat.card f.ker ≤ 2 := by
    have hle : f.ker.map E'.subtype ≤ zpowers s' := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : φ (QuotientGroup.mk' (zpowers s') ((x : E') : C)) = 1 := hx
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      exact hx'
    have h1 := Subgroup.card_le_of_le hle
    rw [card_map_of_injective E'.subtype_injective, Nat.card_zpowers] at h1
    have hos' : orderOf s' = 2 := by rw [hs', Subgroup.orderOf_mk, hs]
    rwa [hos'] at h1
  have hrange : Nat.card f.range ≤ 16 := by
    refine card_le_sixteen_of_mulEquiv_alternating (MulEquiv.refl _) ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have hx : (x : C) * x = 1 := Subtype.ext (hE _ (mem_subgroupOf.1 x.2))
    have hx' : x * x = 1 := Subtype.ext hx
    rw [hx', map_one]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hE'card] at h
  rw [← h]
  calc Nat.card f.ker * Nat.card f.range ≤ 2 * 16 := Nat.mul_le_mul hker hrange
    _ = 32 := by norm_num

end McL

end CFSG.SeitzReduction.SporadicRefine
