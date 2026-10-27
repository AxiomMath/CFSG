module

public import CFSG.GH74.GLS.SP.Local.SPLOrdSD
public import CFSG.CharacterTheory.Semidihedral.Local.ProperSubgroupFormsSupport

public section

open Subgroup DihedralGroup CFSG.Semidihedral.Local

namespace CFSG.GH74.GLS.SP.Local

section G5

variable {G : Type} [Group G]

theorem exists_dih_embedding {g z : G} {d : ℕ} [NeZero d] (hd2 : 2 ≤ d) (hg : orderOf g = d)
    (hzg : z ∉ zpowers g) (hz2 : z ^ 2 = 1) (hconj : z * g * z⁻¹ = g⁻¹) :
    ∃ ψ : DihedralGroup d →* G, Function.Injective ψ ∧ (∀ k : ZMod d, ψ (r k) = g ^ k.val) ∧
      (∀ k : ZMod d, ψ (sr k) = z * g ^ k.val) ∧ ψ.range = zpowers g ⊔ zpowers z := by
  have hgd : g ^ d = 1 := by rw [← hg, pow_orderOf_eq_one]
  have hmem : ∀ k : ℕ, g ^ k ∈ zpowers g := fun k => Subgroup.pow_mem _ (Subgroup.mem_zpowers g) k
  refine ⟨dihedralFormHom hgd hz2 hconj, ?_, fun k => rfl, fun k => rfl, ?_⟩
  · have hpowinj : ∀ i j : ZMod d, g ^ i.val = g ^ j.val → i = j := by
      intro i j hij
      rw [pow_inj_mod, hg, Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)]
        at hij
      exact ZMod.val_injective _ hij
    intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · have hab' : g ^ i.val = g ^ j.val := hab
      rw [hpowinj i j hab']
    · have hab' : g ^ i.val = z * g ^ j.val := hab
      exfalso
      apply hzg
      have : z = g ^ i.val * (g ^ j.val)⁻¹ := by rw [hab']; group
      rw [this]
      exact Subgroup.mul_mem _ (hmem _) (Subgroup.inv_mem _ (hmem _))
    · have hab' : z * g ^ i.val = g ^ j.val := hab
      exfalso
      apply hzg
      have : z = g ^ j.val * (g ^ i.val)⁻¹ := by rw [← hab']; group
      rw [this]
      exact Subgroup.mul_mem _ (hmem _) (Subgroup.inv_mem _ (hmem _))
    · have hab' : z * g ^ i.val = z * g ^ j.val := hab
      rw [mul_right_inj] at hab'
      rw [hpowinj i j hab']
  · have hg1 : g = dihedralFormHom hgd hz2 hconj (r 1) := by
      show g = g ^ (1 : ZMod d).val
      have hd1 : d ≠ 1 := by omega
      rw [ZMod.val_one'' hd1, pow_one]
    have hz1 : z = dihedralFormHom hgd hz2 hconj (sr 0) := by
      show z = z * g ^ (0 : ZMod d).val
      rw [ZMod.val_zero, pow_zero, mul_one]
    apply le_antisymm
    · rintro _ ⟨ρ, rfl⟩
      rcases ρ with k | k
      · exact Subgroup.mem_sup_left (hmem _)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers z))
          (Subgroup.mem_sup_left (hmem _))
    · refine sup_le ?_ ?_
      · rw [zpowers_le]
        exact ⟨r 1, hg1.symm⟩
      · rw [zpowers_le]
        exact ⟨sr 0, hz1.symm⟩

private theorem mem_sup_of_le_normalizer' {N H : Subgroup G} (h : H ≤ normalizer (N : Set G)) {g : G}
    (hg : g ∈ N ⊔ H) : ∃ n ∈ N, ∃ k ∈ H, g = n * k := by
  have hset := coe_mul_of_right_le_normalizer_left N H h
  have hg' : g ∈ (↑(N ⊔ H) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨n, hn, k, hk, hnk⟩ := Set.mem_mul.mp hg'
  exact ⟨n, hn, k, hk, hnk.symm⟩

theorem par_eq_val_mod_two {d : ℕ} [NeZero d] (hd : 2 ∣ d) (k : ZMod d) :
    par hd k = k.val % 2 := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  unfold par
  rw [map_natCast, ZMod.val_natCast]

theorem conj_pow_aut (I : Subgroup G) {g : G} (σ : MulAut ↥I)
    (hgI : ∀ i : ↥I, g * (i : G) * g⁻¹ = ((σ i : ↥I) : G)) (n : ℕ) (i : ↥I) :
    g ^ n * (i : G) * (g ^ n)⁻¹ = (((σ ^ n) i : ↥I) : G) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have e : g ^ (n + 1) * (i : G) * (g ^ (n + 1))⁻¹ = g ^ n * (g * (i : G) * g⁻¹) * (g ^ n)⁻¹ := by
      rw [pow_succ, mul_inv_rev]; group
    rw [e, hgI i, ih (σ i), pow_succ, MulAut.mul_apply]

theorem dihAct_cases {I : Type} [Group I] (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d]
    (hd : 2 ∣ d) (ρ : DihedralGroup d) : dihAct σ hσ hd ρ = 1 ∨ dihAct σ hσ hd ρ = σ := by
  rcases ρ with k | k
  · rw [dihAct_r, par_eq_val_mod_two hd]
    rcases Nat.mod_two_eq_zero_or_one k.val with h | h <;> simp [h]
  · rw [dihAct_sr, par_eq_val_mod_two hd]
    rcases Nat.mod_two_eq_zero_or_one k.val with h | h <;> simp [h]

theorem dih_conj_action (I : Subgroup G) {g z : G} {d : ℕ} [NeZero d] (hd : 2 ∣ d)
    (ψ : DihedralGroup d →* G) (hψr : ∀ k : ZMod d, ψ (r k) = g ^ k.val)
    (hψsr : ∀ k : ZMod d, ψ (sr k) = z * g ^ k.val) (σ : MulAut ↥I) (hσ : σ * σ = 1)
    (hgI : ∀ i : ↥I, g * (i : G) * g⁻¹ = ((σ i : ↥I) : G))
    (hzI : ∀ i ∈ I, z * i * z⁻¹ = i) (ρ : DihedralGroup d) (i : ↥I) :
    ψ ρ * (i : G) * (ψ ρ)⁻¹ = ((dihAct σ hσ hd ρ i : ↥I) : G) := by
  have hσ2 : σ ^ 2 = 1 := by rw [pow_two]; exact hσ
  have hσpow : ∀ n : ℕ, σ ^ n = σ ^ (n % 2) := fun n => pow_eq_pow_mod n hσ2
  rcases ρ with k | k
  · rw [hψr, dihAct_r, conj_pow_aut I σ hgI, hσpow, par_eq_val_mod_two hd]
  · rw [hψsr, dihAct_sr]
    have e : z * g ^ k.val * (i : G) * (z * g ^ k.val)⁻¹ =
        z * (g ^ k.val * (i : G) * (g ^ k.val)⁻¹) * z⁻¹ := by
      rw [mul_inv_rev]; group
    rw [e, conj_pow_aut I σ hgI, hσpow k.val, par_eq_val_mod_two hd]
    exact hzI _ (((σ ^ (k.val % 2)) i).2)

theorem exists_semidirect_iso (I : Subgroup G) {g z : G} {d : ℕ} [NeZero d] (hd : 2 ∣ d)
    (hd2 : 2 ≤ d) (hg : orderOf g = d) (hzg : z ∉ zpowers g) (hz2 : z ^ 2 = 1)
    (hconj : z * g * z⁻¹ = g⁻¹) (σ : MulAut ↥I) (hσ : σ * σ = 1)
    (hgI : ∀ i : ↥I, g * (i : G) * g⁻¹ = ((σ i : ↥I) : G))
    (hzI : ∀ i ∈ I, z * i * z⁻¹ = i) (hIinf : I ⊓ (zpowers g ⊔ zpowers z) = ⊥) :
    ∃ Φ : (↥I ⋊[dihAct σ hσ hd] DihedralGroup d) ≃* ↥(I ⊔ (zpowers g ⊔ zpowers z)),
      (∀ (i : ↥I) (k : ZMod d), (Φ ⟨i, r k⟩ : G) = i * g ^ k.val) ∧
        ∀ (i : ↥I) (k : ZMod d), (Φ ⟨i, sr k⟩ : G) = i * (z * g ^ k.val) := by
  obtain ⟨ψ, hψinj, hψr, hψsr, hψrange⟩ := exists_dih_embedding hd2 hg hzg hz2 hconj
  have hσσ : ∀ i : ↥I, σ (σ i) = i := fun i => by
    have := congrArg (fun f : MulAut ↥I => f i) hσ
    simpa using this
  have hz1 : z⁻¹ = z := by
    have : z * z = 1 := by rw [← pow_two]; exact hz2
    exact inv_eq_of_mul_eq_one_right this
  have hact := dih_conj_action I hd ψ hψr hψsr σ hσ hgI hzI
  let Φ₀ : (↥I ⋊[dihAct σ hσ hd] DihedralGroup d) →* G :=
    SemidirectProduct.lift I.subtype ψ (fun ρ => by
      ext i
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_subtype]
      exact (hact ρ i).symm)
  have hΦ₀ : ∀ a : ↥I ⋊[dihAct σ hσ hd] DihedralGroup d, Φ₀ a = (a.left : G) * ψ a.right :=
    fun a => rfl
  have hDt_norm : zpowers g ⊔ zpowers z ≤ normalizer (I : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_normalizer_iff]
      intro h
      constructor
      · intro hh; exact hgI ⟨h, hh⟩ ▸ (σ ⟨h, hh⟩).2
      · intro hh
        have h1 := hgI (σ ⟨g * h * g⁻¹, hh⟩)
        rw [hσσ] at h1
        have h1' : g * ((σ ⟨g * h * g⁻¹, hh⟩ : ↥I) : G) * g⁻¹ = g * h * g⁻¹ := h1
        have h2 : ((σ ⟨g * h * g⁻¹, hh⟩ : ↥I) : G) = h := by
          calc ((σ ⟨g * h * g⁻¹, hh⟩ : ↥I) : G)
              = g⁻¹ * (g * ((σ ⟨g * h * g⁻¹, hh⟩ : ↥I) : G) * g⁻¹) * g := by group
            _ = g⁻¹ * (g * h * g⁻¹) * g := by rw [h1']
            _ = h := by group
        rw [← h2]; exact (σ ⟨g * h * g⁻¹, hh⟩).2
    · rw [zpowers_le, mem_normalizer_iff]
      intro h
      constructor
      · intro hh; rw [hzI h hh]; exact hh
      · intro hh
        have := hzI _ hh
        have e : z * (z * h * z⁻¹) * z⁻¹ = h := by
          rw [hz1]
          calc z * (z * h * z) * z = (z * z) * h * (z * z) := by group
            _ = h := by
              have : z * z = 1 := by rw [← pow_two]; exact hz2
              rw [this]; group
        rw [← e, this]
        have hzz : z * h * z⁻¹ ∈ I := hh
        exact hzz
  have hrange : ∀ a, Φ₀ a ∈ I ⊔ (zpowers g ⊔ zpowers z) := by
    intro a
    rw [hΦ₀]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left a.left.2) (Subgroup.mem_sup_right ?_)
    rw [← hψrange]
    exact ⟨a.right, rfl⟩
  have hsurj : ∀ w ∈ I ⊔ (zpowers g ⊔ zpowers z), ∃ a, Φ₀ a = w := by
    intro w hw
    obtain ⟨i, hi, u, hu, rfl⟩ := mem_sup_of_le_normalizer' hDt_norm hw
    rw [← hψrange] at hu
    obtain ⟨ρ, rfl⟩ := hu
    exact ⟨⟨⟨i, hi⟩, ρ⟩, rfl⟩
  have hinj : Function.Injective Φ₀ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hΦ₀] at ha
    have hψa : ψ a.right = ((a.left)⁻¹ : ↥I) := by
      have : (a.left : G) * ψ a.right = 1 := ha
      exact eq_inv_of_mul_eq_one_right this
    have hmemI : ψ a.right ∈ I := by rw [hψa]; exact (a.left⁻¹).2
    have hmemD : ψ a.right ∈ zpowers g ⊔ zpowers z := by
      rw [← hψrange]; exact ⟨a.right, rfl⟩
    have h1 : ψ a.right = 1 := by
      have : ψ a.right ∈ I ⊓ (zpowers g ⊔ zpowers z) := ⟨hmemI, hmemD⟩
      rw [hIinf] at this
      exact Subgroup.mem_bot.mp this
    have hr : a.right = 1 := hψinj (by rw [h1, map_one])
    have hl : (a.left : G) = 1 := by
      rw [h1, mul_one] at ha
      exact ha
    exact SemidirectProduct.ext (Subtype.ext (by simpa using hl)) (by simpa using hr)
  let Φ₁ : (↥I ⋊[dihAct σ hσ hd] DihedralGroup d) →* ↥(I ⊔ (zpowers g ⊔ zpowers z)) :=
    Φ₀.codRestrict _ hrange
  have hΦ₁inj : Function.Injective Φ₁ := fun a b hab =>
    hinj (congrArg Subtype.val hab)
  have hΦ₁surj : Function.Surjective Φ₁ := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha⟩ := hsurj w hw
    exact ⟨a, Subtype.ext ha⟩
  refine ⟨MulEquiv.ofBijective Φ₁ ⟨hΦ₁inj, hΦ₁surj⟩, ?_, ?_⟩
  · intro i k
    show (i : G) * ψ (r k) = (i : G) * g ^ k.val
    rw [hψr]
  · intro i k
    show (i : G) * ψ (sr k) = (i : G) * (z * g ^ k.val)
    rw [hψsr]

end G5

end CFSG.GH74.GLS.SP.Local
