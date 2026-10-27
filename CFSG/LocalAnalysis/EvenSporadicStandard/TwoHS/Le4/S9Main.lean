module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Syl
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HUniq

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier
  Matrix

section Aux

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : G}

theorem conj_f_cases (hF : FourHyp G L f) {x : G} (hx : x * f ^ 2 = f ^ 2 * x) :
    x * f * x⁻¹ = f ∨ x * f * x⁻¹ = f⁻¹ := by
  have hxn : x ∈ normalizer (L : Set G) := by
    rw [← hF.norm]
    exact mem_centralizer_singleton_iff.2 hx
  have hmem : x * f * x⁻¹ ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have hl' : x⁻¹ * l * x⁻¹⁻¹ ∈ L := (mem_normalizer_iff.1 (inv_mem hxn) l).1 hl
    have hc := comm_f_of_mem hF hl'
    simp only [inv_inv] at hc
    calc l * (x * f * x⁻¹) = x * ((x⁻¹ * l * x) * f) * x⁻¹ := by group
      _ = x * (f * (x⁻¹ * l * x)) * x⁻¹ := by rw [hc]
      _ = x * f * x⁻¹ * l := by group
  rw [hF.cent] at hmem
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  have hsq : (x * f * x⁻¹) ^ 2 = f ^ 2 := by
    rw [conj_pow]
    calc x * f ^ 2 * x⁻¹ = (f ^ 2 * x) * x⁻¹ := by rw [hx]
      _ = f ^ 2 := by group
  rw [← hk] at hsq
  have h0 : f ^ (k * 2) = f ^ (2 : ℤ) := by
    rw [_root_.zpow_mul]
    simpa using hsq
  have h1 : f ^ (k * 2 - 2) = 1 := by
    rw [_root_.zpow_sub, h0, mul_inv_cancel]
  have h2 : ((orderOf f : ℕ) : ℤ) ∣ k * 2 - 2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hF.order] at h2
  have h3 : f ^ (k % 4) = f ^ k := by
    have := zpow_mod_orderOf f k
    rw [hF.order] at this
    simpa using this
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by
    push_cast at h2
    omega
  have h4 : f ^ (4 : ℤ) = 1 := by
    have := hF.pow_four
    exact_mod_cast this
  rw [← hk, ← h3]
  rcases hk4 with h | h
  · left
    rw [h, zpow_one]
  · right
    rw [h]
    have : f ^ (3 : ℤ) * f = 1 := by
      calc f ^ (3 : ℤ) * f = f ^ (4 : ℤ) := by rw [← _root_.zpow_add_one]; norm_num
        _ = 1 := h4
    exact eq_inv_of_mul_eq_one_left this

theorem exists_conj_fixing_f (hF : FourHyp G L f) {S₀ S₁ : Subgroup G}
    (hS₁c : ∀ x ∈ S₁, x * f ^ 2 = f ^ 2 * x) (hu : ∃ u ∈ S₁, u * f * u⁻¹ = f⁻¹) {g : G}
    (hgc : g * f ^ 2 = f ^ 2 * g) (hg : ∀ x, x ∈ S₁ ↔ g * x * g⁻¹ ∈ S₀) :
    ∃ g' : G, g' * f ^ 2 = f ^ 2 * g' ∧ g' * f * g'⁻¹ = f ∧
      ∀ x, x ∈ S₁ ↔ g' * x * g'⁻¹ ∈ S₀ := by
  rcases conj_f_cases hF hgc with h | h
  · exact ⟨g, hgc, h, hg⟩
  · obtain ⟨u, huS, huf⟩ := hu
    refine ⟨g * u, ?_, ?_, fun x => ?_⟩
    · calc g * u * f ^ 2 = g * (u * f ^ 2) := by rw [mul_assoc]
        _ = g * (f ^ 2 * u) := by rw [hS₁c u huS]
        _ = (g * f ^ 2) * u := by rw [mul_assoc]
        _ = f ^ 2 * (g * u) := by rw [hgc, mul_assoc]
    · calc g * u * f * (g * u)⁻¹ = g * (u * f * u⁻¹) * g⁻¹ := by group
        _ = g * f⁻¹ * g⁻¹ := by rw [huf]
        _ = (g * f * g⁻¹)⁻¹ := by group
        _ = f := by rw [h, inv_inv]
    · have e : g * u * x * (g * u)⁻¹ = g * (u * x * u⁻¹) * g⁻¹ := by group
      rw [e, ← hg]
      constructor
      · intro hx
        exact S₁.mul_mem (S₁.mul_mem huS hx) (S₁.inv_mem huS)
      · intro hx
        have h1 := S₁.mul_mem (S₁.mul_mem (S₁.inv_mem huS) hx) huS
        have e2 : u⁻¹ * (u * x * u⁻¹) * u = x := by group
        rwa [e2] at h1

end Aux

section Transport

variable {G : Type} [Group G] [Finite G]

theorem sect8Hyp_conj {C₁ : ECoord G} {f n : G} {S₀ : Subgroup G} (hLF : ListFacts)
    (hshat : ∀ A ∈ shatList, A ∈ q0List) (hf : f ∈ C₁.E) (hvec : C₁.vec f = fVec)
    (hcent : ∀ x : G, x * f ^ 2 = f ^ 2 * x → (∀ e ∈ C₁.E, x * e = e * x) → x ∈ C₁.E)
    (hactN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x ∈ normalizer (C₁.E : Set G) →
      C₁.mat x ∈ q0List)
    (hreal : ∀ A ∈ q0List, ∃ x : G, x * f ^ 2 = f ^ 2 * x ∧ x ∈ normalizer (C₁.E : Set G) ∧
      C₁.mat x = A)
    (hS₀c : ∀ x ∈ S₀, x * f ^ 2 = f ^ 2 * x) (hn : ∀ x : G, x ∈ S₀ ↔ n * x * n⁻¹ ∈ S₀)
    {c : G} (hcc : c * f ^ 2 = f ^ 2 * c) (hcf : c * f * c⁻¹ = f)
    (hc : ∀ x, x ∈ S1sub C₁ (f ^ 2) hLF ↔ c * x * c⁻¹ ∈ S₀) :
    Sect8Hyp (C₁.conj c) f n S₀ := by
  set C := C₁.conj c with hC
  set S₁ := S1sub C₁ (f ^ 2) hLF with hS₁
  have htE : f ^ 2 ∈ C₁.E := pow_mem hf 2
  have hEc : ∀ x, x ∈ C.E ↔ c⁻¹ * x * c ∈ C₁.E := C₁.mem_conj_E c
  have hcn : ∀ x, x ∈ normalizer (C.E : Set G) ↔ c⁻¹ * x * c ∈ normalizer (C₁.E : Set G) :=
    fun x => C₁.normalizer_conj c
  have hinv : ∀ x, x ∈ S₀ ↔ c⁻¹ * x * c ∈ S₁ := by
    intro x
    rw [hc, show c * (c⁻¹ * x * c) * c⁻¹ = x by group]
  have hN : ∀ x : G, x * f ^ 2 = f ^ 2 * x ↔ c⁻¹ * x * c * f ^ 2 = f ^ 2 * (c⁻¹ * x * c) := by
    have hcN : c ∈ centralizer ({f ^ 2} : Set G) := mem_centralizer_singleton_iff.2 hcc
    have hmem : ∀ x : G, x ∈ centralizer ({f ^ 2} : Set G) ↔
        c⁻¹ * x * c ∈ centralizer ({f ^ 2} : Set G) := by
      intro x
      constructor
      · intro hx
        exact mul_mem (mul_mem (inv_mem hcN) hx) hcN
      · intro hx
        have := mul_mem (mul_mem hcN hx) (inv_mem hcN)
        rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at this
    intro x
    rw [← mem_centralizer_singleton_iff, ← mem_centralizer_singleton_iff]
    exact hmem x
  have hfc : c⁻¹ * f * c = f := by
    calc c⁻¹ * f * c = c⁻¹ * (c * f * c⁻¹) * c := by rw [hcf]
      _ = f := by group
  have hE₁S : ∀ e ∈ C₁.E, e ∈ S₁ := by
    intro e he
    refine ⟨C₁.comm he htE, Subgroup.le_normalizer he, ?_⟩
    rw [(C₁.mat_eq_one_iff (Subgroup.le_normalizer he)).2 fun a ha => C₁.comm he ha]
    exact hLF.shat_one
  have hEle : C.E ≤ S₀ := fun x hx => (hinv x).2 (hE₁S _ ((hEc x).1 hx))
  have hSn : ∀ x ∈ S₀, x ∈ normalizer (C.E : Set G) := fun x hx => (hcn x).2 ((hinv x).1 hx).2.1
  have hmatS : ∀ x ∈ S₀, C.mat x ∈ shatList := by
    intro x hx
    have h1 := (hinv x).1 hx
    rw [hC, ECoord.mat_conj C₁ c h1.2.1]
    exact h1.2.2
  have hcentC : ∀ x : G, x * f ^ 2 = f ^ 2 * x → (∀ e ∈ C.E, x * e = e * x) → x ∈ C.E := by
    intro x hx hxe
    rw [hEc]
    refine hcent _ ((hN x).1 hx) fun e he => ?_
    have h1 := hxe (c * e * c⁻¹)
      ((hEc _).2 (by rw [show c⁻¹ * (c * e * c⁻¹) * c = e by group]; exact he))
    calc c⁻¹ * x * c * e = c⁻¹ * (x * (c * e * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * e * c⁻¹ * x) * c := by rw [h1]
      _ = e * (c⁻¹ * x * c) := by group
  refine
    { f_mem := (hEc f).2 (by rw [hfc]; exact hf)
      vec_f := ?_
      centN := hcentC
      E_le := hEle
      S₀_cent := hS₀c
      S₀_norm := hSn
      E_char := ?_
      actN := ?_
      actN' := ?_
      actS := hmatS
      actS' := ?_
      n_norm := hn }
  · have := C₁.vec_conj_of_mem c hf
    rw [hcf] at this
    rw [hC, this, hvec]
  · intro g hg
    refine C.mem_normalizer_of_conj_le S₀ hEle hSn hmatS ?_ hLF.Sub g hg
    intro x hx h1
    exact hcentC x (hS₀c x hx) ((C.mat_eq_one_iff (hSn x hx)).1 h1)
  · intro x hx hxn
    have hxn' := (hcn x).1 hxn
    rw [hC, ECoord.mat_conj C₁ c hxn']
    exact hactN _ ((hN x).1 hx) hxn'
  · intro A hA
    obtain ⟨x, hxc, hxn, hxA⟩ := hreal A hA
    have hxn' : c⁻¹ * (c * x * c⁻¹) * c ∈ normalizer (C₁.E : Set G) := by
      rw [show c⁻¹ * (c * x * c⁻¹) * c = x by group]
      exact hxn
    refine ⟨c * x * c⁻¹, ?_, (hcn _).2 hxn', ?_⟩
    · rw [hN, show c⁻¹ * (c * x * c⁻¹) * c = x by group]
      exact hxc
    · rw [hC, ECoord.mat_conj C₁ c hxn', show c⁻¹ * (c * x * c⁻¹) * c = x by group]
      exact hxA
  · intro A hA
    obtain ⟨x, hxc, hxn, hxA⟩ := hreal A (hshat A hA)
    have hxS : x ∈ S₁ := ⟨hxc, hxn, hxA ▸ hA⟩
    have hxn' : c⁻¹ * (c * x * c⁻¹) * c ∈ normalizer (C₁.E : Set G) := by
      rw [show c⁻¹ * (c * x * c⁻¹) * c = x by group]
      exact hxn
    refine ⟨c * x * c⁻¹, (hc x).1 hxS, ?_⟩
    rw [hC, ECoord.mat_conj C₁ c hxn', show c⁻¹ * (c * x * c⁻¹) * c = x by group]
    exact hxA

end Transport

section Main


theorem sect8InputA_of_hHN (hHN : HNCentralizerFacts) : Sect8InputA := by
  intro G _ _ L f s y S₀ n h
  have hF : FourHyp G L f := h.four
  obtain ⟨hΛ, ι, y₁, hy₁mem, hy₁L, hy₁sq, hy₁conj⟩ :=
    exists_model hHN hF h.yy h.y_not h.cent_eq h.quot
  let M : ModelData G L y := ⟨hΛ, ι, y₁, hy₁mem, hy₁L, hy₁sq, hy₁conj⟩
  have hLF : ListFacts := Certificates.certificate26753
  have hshat : ∀ A ∈ shatList, A ∈ q0List :=
    (Certificates.certificate26420 : Q0Facts).shat_sub
  obtain ⟨hactN, hcent⟩ := ModelData.count_core hF h.yy h.yf h.cent_eq M
  have hreal := ModelData.real_q0 hF h.yy h.yf h.cent_eq M
  have hf := f_mem_E M.hΛ hF M.ι
  have hvec := vec_f M.hΛ hF M.ι
  set C₁ := basisCoord M.hΛ hF M.ι with hC₁
  set S₁ := S1sub C₁ (f ^ 2) hLF with hS₁
  have hcard : Nat.card S₁ = 4096 :=
    card_S1sub C₁ hLF hshat hcent hreal (pow_mem hf 2)
  have hS₁N : S₁ ≤ centralizer ({f ^ 2} : Set G) := fun x hx => mem_centralizer_singleton_iff.2 hx.1
  have hS₁p : IsPGroup 2 S₁ := IsPGroup.of_card (n := 12) (by rw [hcard]; norm_num)
  have hLc : L ≤ centralizer ({f ^ 2} : Set G) := by
    intro l hl
    rw [mem_centralizer_singleton_iff]
    exact ((show Commute l f from comm_f_of_mem hF hl).pow_right 2).eq
  have hLN : L.relIndex (centralizer ({f ^ 2} : Set G)) ≤ 4 :=
    relindex_le_four_of_inv hLc (fun l hl => comm_f_of_mem hF hl) hF.sq_mem h.yy
      (y_mem_normalizer hF h.cent_eq) h.cent_eq h.yf
  have hL : Nat.card L = 88704000 := by
    rw [Nat.card_congr M.ι.toEquiv]
    exact M.hΛ.card_eq
  have hS₀card : Nat.card S₀ ≤ Nat.card S₁ := by
    rw [hcard]
    exact card_two_subgroup_le h.S₀_t h.pgroup hLN hL
  obtain ⟨g, hgN, hg⟩ := exists_conj_of_card_le h.S₀_t hS₁N h.pgroup h.rel hS₁p hS₀card
  have hneg : ∃ u ∈ S₁, u * f * u⁻¹ = f⁻¹ := by
    obtain ⟨A, hA, hA22⟩ := hLF.shat_neg
    obtain ⟨x, hxc, hxn, hxA⟩ := hreal A (hshat A hA)
    refine ⟨x, ⟨hxc, hxn, hxA ▸ hA⟩, ?_⟩
    rcases conj_f_cases hF hxc with h1 | h1
    · exfalso
      have h2 := C₁.vec_conj hxn hf
      rw [h1, hvec, hxA, fVec_eq, Matrix.mulVec_single_one] at h2
      have h3 := congrFun h2 2
      simp only [Matrix.col_apply, Pi.single_eq_same] at h3
      rw [hA22] at h3
      revert h3
      decide
    · exact h1
  obtain ⟨c, hcc, hcf, hc⟩ := exists_conj_fixing_f hF (S₀ := S₀) (S₁ := S₁)
    (fun x (hx : x ∈ S₁) => hx.1) hneg
    (mem_centralizer_singleton_iff.1 hgN) hg
  exact ⟨C₁.conj c, sect8Hyp_conj hLF hshat hf hvec hcent hactN hreal
    (fun x hx => mem_centralizer_singleton_iff.1 (h.S₀_t hx)) h.n_norm hcc hcf hc⟩

end Main

end CFSG.EvenSporadicStandard.TwoHS
