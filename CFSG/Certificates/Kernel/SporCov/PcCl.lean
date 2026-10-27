module

public import Certificates.Data.Kernel.SporCov.PcCl
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Certificates.Kernel.SporCov.CensusSound

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.StandardType.SporadicShape
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) : g ∈ Subgroup.normalizer (A : Set G) := by
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hfx : ∀ x, f x = g * x * g⁻¹ := fun x => rfl
  have hle : A.map f ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hfx]
    exact h x hx
  have hinj : Function.Injective f := (MulAut.conj g).injective
  have heq : A.map f = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective hinj])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, e⟩ := hx
  rw [hfx] at e
  have hyx : y = x := by simpa using e
  rwa [hyx] at hy

theorem isPGroup_pcSub [Finite G] {p k : ℕ} (hp : p.Prime) (g : ℕ → G)
    (hpow : ∀ i < k, ∃ e : ℕ → ℕ, (∀ t ≤ i, e t = 0) ∧ g i ^ p = nfG g e k 0)
    (hconj : ∀ i j, i < j → j < k → ∃ e : ℕ → ℕ, (∀ t ≤ i, e t = 0) ∧
      g j * g i = g i * nfG g e k 0) :
    IsPGroup p (pcSub (fun t : Fin k => (g t)⁻¹) 0) := by
  have : Fact p.Prime := ⟨hp⟩
  set q : Fin k → G := fun t => (g t)⁻¹ with hq
  have hp' : ∀ i : Fin k, q i ^ p ∈ pcSub q (i.val + 1) := by
    intro i
    obtain ⟨e, he, h⟩ := hpow i i.isLt
    rw [hq, inv_pow, h]
    exact Subgroup.inv_mem _ (nfG_mem_after g he)
  have hc : ∀ i j : Fin k, i < j → q i * q j * (q i)⁻¹ ∈ pcSub q (i.val + 1) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := hconj i j hij j.isLt
    have e1 : q i * q j * (q i)⁻¹ = ((g i)⁻¹ * g j * g i)⁻¹ := by
      rw [hq]
      group
    have e2 : (g i)⁻¹ * g j * g i = nfG g e k 0 := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e1, e2]
    exact Subgroup.inv_mem _ (nfG_mem_after g he)
  have key : ∀ m : ℕ, m ≤ k → IsPGroup p (pcSub q (k - m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, pcSub_n]
      exact IsPGroup.of_bot
    | succ m ih =>
      intro hm
      let i : Fin k := ⟨k - (m + 1), by omega⟩
      have hiv : i.val = k - (m + 1) := rfl
      have e1 : i.val + 1 = k - m := by omega
      have hA := ih (by omega)
      rw [← e1] at hA
      have hB : pcSub q (k - (m + 1)) = Subgroup.zpowers (q i) ⊔ pcSub q (i.val + 1) := by
        unfold pcSub
        rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
        congr 1
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨t, ht, rfl⟩
          by_cases h : t = i
          · exact Or.inl (by rw [h])
          · refine Or.inr ⟨t, ?_, rfl⟩
            have h' : t.val ≠ i.val := fun e => h (Fin.ext e)
            omega
        · rintro (rfl | ⟨t, ht, rfl⟩)
          · exact ⟨i, hiv.ge, rfl⟩
          · exact ⟨t, by omega, rfl⟩
      rw [hB]
      have hZ : IsPGroup p (Subgroup.zpowers (q i)) := by
        obtain ⟨n, hn⟩ := hA ⟨_, hp' i⟩
        have hn' : q i ^ (p ^ (n + 1)) = 1 := by
          have h := congrArg Subtype.val hn
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
          rw [pow_succ', pow_mul]
          exact h
        rintro ⟨x, hx⟩
        obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        refine ⟨n + 1, Subtype.ext ?_⟩
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn', one_zpow]
      refine hZ.to_sup_of_normal_right' hA ?_
      rw [Subgroup.zpowers_le]
      refine mem_normalizer_of_conj fun x hx => ?_
      refine Subgroup.closure_induction
        (p := fun x _ => q i * x * (q i)⁻¹ ∈ pcSub q (i.val + 1)) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, hj, rfl⟩
        exact hc i j (by rw [Fin.lt_def]; omega)
      · rw [mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · intro x y _ _ hx hy
        have e : q i * (x * y) * (q i)⁻¹ = q i * x * (q i)⁻¹ * (q i * y * (q i)⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hx hy
      · intro x _ hx
        have e : q i * x⁻¹ * (q i)⁻¹ = (q i * x * (q i)⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ hx
  have h := key k le_rfl
  rwa [Nat.sub_self] at h

namespace Model

variable {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} {ev : List ℕ → G}
variable (hM : Model L E ev)
include hM

theorem generating_of_pccOK [Finite G] {p k nL nE nR : ℕ} (hp : p.Prime) (hk : 2 ≤ k)
    (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true)
    {H Rl M Y Hc Yc C R : List (List ℕ)} {t : List ℕ} {K : List ℕ}
    (h : pccOK E L p k nL nE nR H Rl t M Y Hc Yc C R K = true)
    (htop : ∀ T : Subgroup G, (∀ k, ev (nthW R k) ∈ T) → T = ⊤) :
    orderOf (ev t) = p ∧ ∀ y, IsConj (ev t) y → SporKRestGenerating p y := by
  have : Fact p.Prime := ⟨hp⟩
  unfold pccOK pcAll at h
  simp only [Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨⟨oH, hR⟩, hpcl⟩, hpow⟩, hne⟩ := h
  have hR' : ∀ i < k, ∀ j < k, i ≤ j → pcR E p H Rl k i j = true := by
    intro i hi j hj hij
    have h := hR i hi j hj
    rwa [Nat.ble_eq_true_of_le hij, cond_true] at h
  obtain ⟨hpw, hcj⟩ := hM.pcR_facts oH hR'
  have hS := isPGroup_pcSub hp (fun t => ev (nthW H t)) hpw hcj
  have hmem : ∀ t < k, ev (nthW H t) ∈ pcSub (fun t : Fin k => (ev (nthW H t))⁻¹) 0 := by
    intro t ht
    have h := Subgroup.subset_closure (k := {x | ∃ s : Fin k, 0 ≤ s.val ∧
      (fun t : Fin k => (ev (nthW H t))⁻¹) s = x}) ⟨⟨t, ht⟩, Nat.zero_le _, rfl⟩
    have h' := Subgroup.inv_mem _ h
    rwa [inv_inv] at h'
  have hS₀ : IsPGroup p (Subgroup.closure ({ev (nthW H 0), ev (nthW H 1)} : Set G)) := by
    refine hS.to_le ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hmem 0 (by omega)
    · exact hmem 1 (by omega)
  obtain ⟨ot, hgen⟩ := hM.generating_of_pclOK hp hS₀ (chW_nthW oH 0) (chW_nthW oH 1) hpcl htop
  have e : ev t ^ p = 1 := by
    rw [← hM.repW_eq, hM.eq (chW_repW ot p) (chW_nil L) hpow, hM.nil]
  exact ⟨orderOf_eq_prime e (hM.ne_one hc ot hne), hgen⟩

end Model

end CFSG.KD.SporCov

end
