module

public import CFSG.CGT.PushingUpLit.BHS7.SymNested
public import CFSG.CGT.PushingUpLit.BHS6.SixEightGen
public import CFSG.CGT.PushingUpLit.BHS7.SymFrattini
public import CFSG.CGT.PushingUpLit.BHS7.SymPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {G T E F : Subgroup Γ} {m : ℕ}

@[expose] noncomputable def SymModel.vec (X : SymModel G T E m) (v : ↥(coreMod (2 * m + 1))) : Γ :=
  ((X.M.βe.symm v : ↥X.M.W) : Γ)

namespace SymModel

variable (X : SymModel G T E m)

theorem vec_mem (v : ↥(coreMod (2 * m + 1))) : X.vec v ∈ X.M.W := (X.M.βe.symm v).2

theorem vec_mul (u v : ↥(coreMod (2 * m + 1))) : X.vec (u * v) = X.vec u * X.vec v := by
  unfold vec
  rw [map_mul]
  rfl

theorem vec_injective : Function.Injective X.vec := fun u v h => by
  have h1 : X.M.βe.symm u = X.M.βe.symm v := Subtype.ext h
  exact X.M.βe.symm.injective h1

theorem conj_vec (e : ↥E) (v : ↥(coreMod (2 * m + 1))) :
    (e : Γ) * X.vec v * (e : Γ)⁻¹ = X.vec (coreAct (2 * m + 1) (X.M.Ψ e) v) := by
  have h1 := X.M.βe_conjW e (X.M.βe.symm v)
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : X.M.conjW e (X.M.βe.symm v) = X.M.βe.symm (coreAct (2 * m + 1) (X.M.Ψ e) v) := by
    rw [← h1, MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val h2

theorem conj_vec_baum (hE : IsBTBlock G T E) (b : ↥(baum T)) (v : ↥(coreMod (2 * m + 1))) :
    (b : Γ) * X.vec v * (b : Γ)⁻¹ = X.vec (coreAct (2 * m + 1) (X.S b) v) := by
  have hbW : (b : Γ) * X.vec v * (b : Γ)⁻¹ ∈ X.M.W :=
    (Subgroup.mem_normalizer_iff.mp (X.baum_le_normalizer_W hE b.2) _).mp (X.vec_mem v)
  have h1 := X.hS b (X.M.βe.symm v) (by
    have := (Subgroup.mem_normalizer_iff.mp (X.baum_le_normalizer_W hE b.2) _).mp
      (X.M.βe.symm v).2
    exact this)
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : (⟨(b : Γ) * ((X.M.βe.symm v : ↥X.M.W) : Γ) * (b : Γ)⁻¹, by
      exact (Subgroup.mem_normalizer_iff.mp (X.baum_le_normalizer_W hE b.2) _).mp
        (X.M.βe.symm v).2⟩ : ↥X.M.W) = X.M.βe.symm (coreAct (2 * m + 1) (X.S b) v) := by
    rw [← h1, MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val h2

theorem vec_one : X.vec 1 = 1 := by
  unfold vec
  rw [map_one]
  rfl

theorem vec_inv (v : ↥(coreMod (2 * m + 1))) : (X.vec v)⁻¹ = X.vec v := by
  have hvv : v * v = 1 := by
    calc v * v = v * v⁻¹ := by rw [coreMod_inv_eq]
      _ = 1 := mul_inv_cancel v
  have h : X.vec v * X.vec v = 1 := by rw [← X.vec_mul, hvv, X.vec_one]
  exact inv_eq_of_mul_eq_one_right h

theorem conj_vec_baum_pair (hE : IsBTBlock G T E) (b : ↥(baum T)) {t : Equiv.Perm (Fin (2 * m + 1))}
    (ht : t ∈ X.T') {a : Fin (2 * m + 1)} (ha : t a ≠ a) :
    (b : Γ) * X.vec (pairVec a (t a)) * (b : Γ)⁻¹ = X.vec (pairVec a (t a)) := by
  rw [X.conj_vec_baum hE b]
  congr 1
  have hfix := pairVec_swap_mem_fixV X.hs X.hc ht ha
  exact (mem_fixV.mp hfix) (coreAct (2 * m + 1) (X.S b)) ⟨X.S b, X.hSY b, rfl⟩

end SymModel

section Nested

variable [Finite Γ]

structure NestedData (X : SymModel G T E m) (F : Subgroup Γ) (hFE : F ≤ E) where
  Ω₀ : Finset (Fin (2 * m + 1))
  hcard : 3 ≤ Ω₀.card
  hfix : ∀ f : ↥F, ∀ y, y ∉ Ω₀ → X.M.Ψ ⟨f, hFE f.2⟩ y = y
  hgen : ∀ π ∈ altOn Ω₀, ∃ f : ↥F, X.M.Ψ ⟨f, hFE f.2⟩ = π
  hinv : ∀ t ∈ X.T', ∀ x, t x ∈ Ω₀ ↔ x ∈ Ω₀
  hcmem : X.c ∈ Ω₀

theorem nonempty_nestedData (h : MinCex G T) (hE : IsBTBlock G T E) (X : SymModel G T E m)
    {F : Subgroup Γ} (hF : IsBTBlock G T F) (hFE : F ≤ E) {r : ℕ} (hr : 1 ≤ r)
    (hFr : IsNaturalAltModule ↥F r) : Nonempty (NestedData X F hFE) := by
  classical
  have hn3 : 3 ≤ 2 * m + 1 := X.M.hn3
  obtain ⟨Ω₀, hcard, hmem, hgen, hmov⟩ := exists_altOn_nested h.charTwo h.sylow hE hn3
    (odd_two_mul_add_one m) X.hMW X.M.βe X.M.Ψ X.M.hΨ hF hFE hr hFr
  have hfix : ∀ f : ↥F, ∀ y, y ∉ Ω₀ → X.M.Ψ ⟨f, hFE f.2⟩ y = y := fun f y hy =>
    (mem_altOn.1 (hmem f)).1 y hy
  have hBF : baum T ≤ Subgroup.normalizer (F : Set Γ) := baum_le_normalizer_of_isBTBlock hF
  have hinvap : ∀ (g : Equiv.Perm (Fin (2 * m + 1))) (x : Fin (2 * m + 1)), g⁻¹ (g x) = x :=
    fun g x => by simp
  have hmapΩ : ∀ b : ↥(baum T), ∀ x ∈ Ω₀, X.S b x ∈ Ω₀ := by
    intro b x hx
    obtain ⟨f, hfx⟩ := (hmov x).1 hx
    have hbf : (b : Γ) * (f : Γ) * (b : Γ)⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (hBF b.2) _).mp f.2
    have key : X.M.Ψ ⟨((⟨(b : Γ) * (f : Γ) * (b : Γ)⁻¹, hbf⟩ : ↥F) : Γ), hFE hbf⟩ =
        X.S b * X.M.Ψ ⟨(f : Γ), hFE f.2⟩ * (X.S b)⁻¹ :=
      X.Ψ_conj_baum hE b ⟨(f : Γ), hFE f.2⟩ (hFE hbf)
    refine (hmov _).2 ⟨⟨(b : Γ) * (f : Γ) * (b : Γ)⁻¹, hbf⟩, ?_⟩
    rw [key, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinvap]
    intro hx'
    exact hfx ((X.S b).injective hx')
  have hinv : ∀ t ∈ X.T', ∀ x, t x ∈ Ω₀ ↔ x ∈ Ω₀ := by
    intro t ht x
    obtain ⟨y₀, hy₀⟩ := X.hy₀ t ht
    constructor
    · intro htx
      have := hmapΩ y₀⁻¹ (t x) htx
      rwa [map_inv, hy₀, hinvap] at this
    · intro hx
      have := hmapΩ y₀ x hx
      rwa [hy₀] at this
  have hcmem : X.c ∈ Ω₀ := by
    by_contra hcn
    have hev := even_card_of_invariant X.hs X.hc X.hcuniq hinv hcn
    rw [hcard] at hev
    obtain ⟨k, hk⟩ := hev
    omega
  exact ⟨⟨Ω₀, by omega, hfix, hgen, hinv, hcmem⟩⟩

theorem NestedData.vec_pairVec_mem_blockW (h : MinCex G T) (hE : IsBTBlock G T E)
    (X : SymModel G T E m) {F : Subgroup Γ} (hF : IsBTBlock G T F) (hFE : F ≤ E)
    (N : NestedData X F hFE) {a b : Fin (2 * m + 1)} (ha : a ∈ N.Ω₀) (hb : b ∈ N.Ω₀)
    (hab : a ≠ b) : X.vec (pairVec a b) ∈ blockW F := by
  classical
  have hF' : F ∈ btBlocksG G T := mem_btBlocksG_of_isBTBlock hF
  obtain ⟨c', hc'Ω, hc'⟩ : ∃ c' ∈ N.Ω₀, c' ∉ ({a, b} : Finset (Fin (2 * m + 1))) := by
    have hlt : ({a, b} : Finset (Fin (2 * m + 1))).card < N.Ω₀.card := by
      have := Finset.card_le_two (a := a) (b := b)
      have h3 := N.hcard
      omega
    obtain ⟨c', hc'1, hc'2⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨c', hc'1, hc'2⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
  obtain ⟨hac, hbc⟩ := hc'
  have hac' : a ≠ c' := fun e => hac e.symm
  have hbc' : b ≠ c' := fun e => hbc e.symm
  have hπ : cyc a b c' ∈ altOn N.Ω₀ := cyc_mem_altOn ha hb hc'Ω hab hac' hbc'
  obtain ⟨f, hf⟩ := N.hgen _ hπ
  set u : Γ := X.vec (pairVec a c') with hu
  have huW : u ∈ pCoreOf 2 E := by
    rw [← X.hMW]
    exact X.vec_mem _
  have hcomm : ⁅(f : Γ), u⁆ ∈ (⁅F, pCoreOf 2 E⁆ : Subgroup Γ) :=
    Subgroup.commutator_mem_commutator f.2 huW
  rw [commutator_eq_pCoreOf_nested h.charTwo h.sylow hE hF' hFE, ← blockW_eq_pCoreOf hF] at hcomm
  have hfu : (f : Γ) * u * (f : Γ)⁻¹ = X.vec (pairVec c' b) := by
    have := X.conj_vec ⟨(f : Γ), hFE f.2⟩ (pairVec a c')
    rw [hf, coreAct_pairVec, cyc_apply_first hac' hbc', cyc_apply_third] at this
    exact this
  have hid : ⁅(f : Γ), u⁆ = X.vec (pairVec a b) := by
    have e1 : ⁅(f : Γ), u⁆ = ((f : Γ) * u * (f : Γ)⁻¹) * u⁻¹ := rfl
    rw [e1, hfu, hu, X.vec_inv, ← X.vec_mul, pairVec_comm a c', pairVec_mul c' b a,
      pairVec_comm b a]
  rw [← hid]
  exact hcomm

end Nested

end CFSG.CGT.PushingUpLit.BHS7
