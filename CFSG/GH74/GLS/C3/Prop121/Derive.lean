module

public import CFSG.GH74.GLS.C3.Prop121.Defs
public import CFSG.GH74.GLS.C3.Prop121.Coord
public import CFSG.GH74.GLS.C3.Layer2.InvolutionExt
public import CFSG.GH74.GLS.C3.Prop121.CosetIso

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2

namespace Derive

section Commutators

variable {G : Type} [Group G]

theorem comm_of_central {A B l₁ l₂ : G} (hA₁ : A * l₁ = l₁ * A) (hA₂ : A * l₂ = l₂ * A)
    (hB₁ : B * l₁ = l₁ * B) (hB₂ : B * l₂ = l₂ * B) (hAB : A * B = B * A) :
    (A * l₁) * (B * l₂) * (A * l₁)⁻¹ * (B * l₂)⁻¹ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by
  have cA1 : Commute A l₁ := hA₁
  have cA2 : Commute A l₂ := hA₂
  have cB1 : Commute B l₁ := hB₁
  have cB2 : Commute B l₂ := hB₂
  have cAB : Commute A B := hAB
  have e1 : (A * l₁) * (B * l₂) = (A * B) * (l₁ * l₂) := by
    calc (A * l₁) * (B * l₂) = A * (l₁ * B) * l₂ := by group
      _ = A * (B * l₁) * l₂ := by rw [cB1.eq]
      _ = (A * B) * (l₁ * l₂) := by group
  have e2 : (B * l₂) * (A * l₁) = (A * B) * (l₂ * l₁) := by
    calc (B * l₂) * (A * l₁) = B * (l₂ * A) * l₁ := by group
      _ = B * (A * l₂) * l₁ := by rw [cA2.eq]
      _ = (B * A) * (l₂ * l₁) := by group
      _ = (A * B) * (l₂ * l₁) := by rw [cAB.eq]
  have hP1 : Commute (A * B) l₁ := cA1.mul_left cB1
  have hP2 : Commute (A * B) l₂ := cA2.mul_left cB2
  have hPK : Commute (A * B) (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) :=
    (((hP1.mul_right hP2).mul_right hP1.inv_right).mul_right hP2.inv_right)
  calc (A * l₁) * (B * l₂) * (A * l₁)⁻¹ * (B * l₂)⁻¹
      = ((A * l₁) * (B * l₂)) * ((B * l₂) * (A * l₁))⁻¹ := by group
    _ = (A * B) * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * (A * B)⁻¹ := by rw [e1, e2]; group
    _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [hPK.eq]; group

variable {L : Subgroup G} {t : G}

theorem comm_mem_L (hLt : ∀ l ∈ L, l * t = t * l)
    (hC : ∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l)
    {c₁ c₂ : G} (h₁ : c₁ * t = t * c₁) (h₂ : c₂ * t = t * c₂) :
    c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ L := by
  obtain ⟨i, l₁, hl₁, rfl⟩ := hC c₁ h₁
  obtain ⟨j, l₂, hl₂, rfl⟩ := hC c₂ h₂
  have hz : ∀ l ∈ L, ∀ k : ℤ, t ^ k * l = l * t ^ k := fun l hl k =>
    (Commute.zpow_left (show Commute t l from (hLt l hl).symm) k).eq
  rw [comm_of_central (hz l₁ hl₁ i) (hz l₂ hl₂ i) (hz l₁ hl₁ j) (hz l₂ hl₂ j)
    (Commute.zpow_zpow_self t i j).eq]
  exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)

theorem le_of_perfect {K : Subgroup G} (hK : K ≤ ⁅K, K⁆) (hKt : ∀ k ∈ K, k * t = t * k)
    (hLt : ∀ l ∈ L, l * t = t * l)
    (hC : ∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) : K ≤ L := by
  refine hK.trans ?_
  rw [Subgroup.commutator_le]
  intro k₁ hk₁ k₂ hk₂
  rw [commutatorElement_def]
  exact comm_mem_L hLt hC (hKt k₁ hk₁) (hKt k₂ hk₂)

theorem conj_mem_of_inv {u : G} (hL : L ≤ ⁅L, L⁆) (hu : u * t * u⁻¹ = t⁻¹)
    (hLt : ∀ l ∈ L, l * t = t * l)
    (hC : ∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) :
    ∀ l ∈ L, u * l * u⁻¹ ∈ L := by
  intro l hl
  have h2 : u * l * u⁻¹ ∈ Subgroup.map (MulAut.conj u).toMonoidHom ⁅L, L⁆ :=
    ⟨l, hL hl, by simp [MulAut.conj_apply]⟩
  rw [Subgroup.map_commutator] at h2
  have h3' : u * t⁻¹ * u⁻¹ = t := by
    have := congrArg (fun z => z⁻¹) hu
    simpa [mul_assoc] using this
  have hut : u⁻¹ * t * u = t⁻¹ := by
    calc u⁻¹ * t * u = u⁻¹ * (u * t⁻¹ * u⁻¹) * u := by rw [h3']
      _ = t⁻¹ := by group
  have hcomm : ∀ l₁ ∈ L, (u * l₁ * u⁻¹) * t = t * (u * l₁ * u⁻¹) := by
    intro l₁ hl₁
    have h4 : l₁ * t⁻¹ = t⁻¹ * l₁ := (Commute.inv_right (show Commute l₁ t from hLt l₁ hl₁)).eq
    calc (u * l₁ * u⁻¹) * t = u * l₁ * (u⁻¹ * t * u) * u⁻¹ := by group
      _ = u * (l₁ * t⁻¹) * u⁻¹ := by rw [hut]; group
      _ = u * (t⁻¹ * l₁) * u⁻¹ := by rw [h4]
      _ = (u * t⁻¹ * u⁻¹) * (u * l₁ * u⁻¹) := by group
      _ = t * (u * l₁ * u⁻¹) := by rw [h3']
  have h3 : ⁅Subgroup.map (MulAut.conj u).toMonoidHom L,
      Subgroup.map (MulAut.conj u).toMonoidHom L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    rintro a ⟨l₁, hl₁, rfl⟩ b ⟨l₂, hl₂, rfl⟩
    rw [commutatorElement_def]
    exact comm_mem_L hLt hC (by simpa [MulAut.conj_apply] using hcomm l₁ hl₁)
      (by simpa [MulAut.conj_apply] using hcomm l₂ hl₂)
  exact h3 h2

end Commutators

structure Setup {G : Type} [Group G] (n : ℕ) (K L : Subgroup G) (u : G) : Type where
  lam : ↥L ≃* alternatingGroup (Fin (n + 1))
  hn : 2 ≤ n
  hKL : K ≤ L
  huL : ∀ l ∈ L, u * l * u⁻¹ ∈ L
  huK : ∀ k ∈ K, u * k * u⁻¹ ∈ K
  hu2 : u * u = 1
  hstab : ∀ l : ↥L, (l : G) ∈ K ↔ ((lam l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) 0 = 0

namespace Setup

variable {G : Type} [Group G] {n : ℕ} {K L : Subgroup G} {u : G} (S : Setup n K L u)

@[expose] def lamP (l : ↥L) : Perm (Fin (n + 1)) := ((S.lam l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1)))

theorem lamP_mul (a b : ↥L) : S.lamP (a * b) = S.lamP a * S.lamP b := by
  simp [lamP]

theorem lamP_one : S.lamP 1 = 1 := by simp [lamP]

theorem lamP_inv (a : ↥L) : S.lamP a⁻¹ = (S.lamP a)⁻¹ := by simp [lamP]

theorem lamP_injective : Function.Injective S.lamP := by
  intro a b h
  apply S.lam.injective
  exact Subtype.ext h

theorem sign_lamP (l : ↥L) : Equiv.Perm.sign (S.lamP l) = 1 :=
  Equiv.Perm.mem_alternatingGroup.1 (S.lam l).2

theorem hstab' (l : ↥L) : (l : G) ∈ K ↔ S.lamP l 0 = 0 := S.hstab l

@[expose] def cu (l : ↥L) : ↥L := ⟨u * l * u⁻¹, S.huL l l.2⟩

theorem cu_coe (l : ↥L) : ((S.cu l : ↥L) : G) = u * l * u⁻¹ := rfl

theorem cu_mul (a b : ↥L) : S.cu (a * b) = S.cu a * S.cu b := by
  apply Subtype.ext
  show u * ((a : G) * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹)
  group

theorem cu_one : S.cu 1 = 1 := by
  apply Subtype.ext
  show u * (1 : G) * u⁻¹ = 1
  group

theorem cu_cu (l : ↥L) : S.cu (S.cu l) = l := by
  apply Subtype.ext
  show u * (u * (l : G) * u⁻¹) * u⁻¹ = l
  have h1 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, S.hu2, inv_one]
  calc u * (u * (l : G) * u⁻¹) * u⁻¹ = (u * u) * l * (u⁻¹ * u⁻¹) := by group
    _ = l := by rw [S.hu2, h1]; group

theorem cu_inv (a : ↥L) : S.cu a⁻¹ = (S.cu a)⁻¹ := by
  have := S.cu_mul a⁻¹ a
  rw [inv_mul_cancel, S.cu_one] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem exists_pre (ω : Fin (n + 1)) : ∃ l : ↥L, S.lamP l 0 = ω := by
  by_cases hω : ω = 0
  · exact ⟨1, by simp [S.lamP_one, hω]⟩
  · obtain ⟨a, ha0, haω⟩ : ∃ a : Fin (n + 1), a ≠ 0 ∧ a ≠ ω := by
      by_cases h1 : ω = ⟨1, by have := S.hn; omega⟩
      · exact ⟨⟨2, by have := S.hn; omega⟩, by simp [Fin.ext_iff], by rw [h1]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨1, by have := S.hn; omega⟩, by simp [Fin.ext_iff], fun h => h1 h.symm⟩
    set σ : Perm (Fin (n + 1)) := swap 0 ω * swap ω a with hσ
    have hsign : Equiv.Perm.sign σ = 1 := by
      rw [hσ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hω),
        Equiv.Perm.sign_swap (Ne.symm haω)]
      decide
    have hσ0 : σ 0 = ω := by
      rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hω) (Ne.symm ha0), swap_apply_left]
    refine ⟨S.lam.symm ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩, ?_⟩
    simp [lamP, hσ0]

@[expose] noncomputable def pre (ω : Fin (n + 1)) : ↥L := Classical.choose (S.exists_pre ω)

theorem pre_spec (ω : Fin (n + 1)) : S.lamP (S.pre ω) 0 = ω := Classical.choose_spec (S.exists_pre ω)

@[expose] noncomputable def tauFun (ω : Fin (n + 1)) : Fin (n + 1) := S.lamP (S.cu (S.pre ω)) 0

theorem tauFun_lamP (l : ↥L) : S.tauFun (S.lamP l 0) = S.lamP (S.cu l) 0 := by
  set l' := S.pre (S.lamP l 0) with hl'
  have h1 : S.lamP l' 0 = S.lamP l 0 := S.pre_spec _
  have h2 : ((l'⁻¹ * l : ↥L) : G) ∈ K := by
    rw [S.hstab', S.lamP_mul, S.lamP_inv]
    simp only [Perm.mul_apply]
    rw [← h1]
    simp
  have h3 : ((S.cu (l'⁻¹ * l) : ↥L) : G) ∈ K := by
    rw [S.cu_coe]
    exact S.huK _ h2
  rw [S.hstab', S.cu_mul, S.lamP_mul, S.cu_inv, S.lamP_inv] at h3
  simp only [Perm.mul_apply] at h3
  have h4 : S.lamP (S.cu l) 0 = S.lamP (S.cu l') 0 := by
    have := (Equiv.Perm.inv_eq_iff_eq).1 h3
    simpa using this
  show S.lamP (S.cu l') 0 = S.lamP (S.cu l) 0
  exact h4.symm

theorem tauFun_invol : Function.Involutive S.tauFun := by
  intro ω
  obtain ⟨l, hl⟩ := S.exists_pre ω
  rw [← hl, S.tauFun_lamP l, S.tauFun_lamP (S.cu l), S.cu_cu]

@[expose] noncomputable def tau : Perm (Fin (n + 1)) := S.tauFun_invol.toPerm _

theorem tau_apply (ω : Fin (n + 1)) : S.tau ω = S.tauFun ω := rfl

theorem tau_lamP (l : ↥L) : S.tau (S.lamP l 0) = S.lamP (S.cu l) 0 := S.tauFun_lamP l

theorem tau_zero : S.tau 0 = 0 := by
  have := S.tau_lamP 1
  simpa [S.lamP_one, S.cu_one] using this

theorem tau_mul_tau : S.tau * S.tau = 1 := by
  ext ω
  simp [Perm.mul_apply, tau_apply, S.tauFun_invol ω]

theorem tau_conj (l : ↥L) : S.tau * S.lamP l = S.lamP (S.cu l) * S.tau := by
  refine Equiv.ext fun ω => ?_
  obtain ⟨l', hl'⟩ := S.exists_pre ω
  rw [← hl']
  have e1 : S.lamP l (S.lamP l' 0) = S.lamP (l * l') 0 := by rw [S.lamP_mul]; rfl
  have e2 : S.lamP (S.cu l) (S.lamP (S.cu l') 0) = S.lamP (S.cu (l * l')) 0 := by
    rw [S.cu_mul, S.lamP_mul]; rfl
  show S.tau (S.lamP l (S.lamP l' 0)) = S.lamP (S.cu l) (S.tau (S.lamP l' 0))
  rw [e1, S.tau_lamP, S.tau_lamP, e2]

theorem sign_tau (hout : ∀ k₀ ∈ K, ∃ k ∈ K, u * k * u⁻¹ ≠ k₀ * k * k₀⁻¹) :
    Equiv.Perm.sign S.tau = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign S.tau) with h | h
  · exfalso
    have hτ : S.tau ∈ alternatingGroup (Fin (n + 1)) := Equiv.Perm.mem_alternatingGroup.2 h
    set l₀ : ↥L := S.lam.symm ⟨S.tau, hτ⟩ with hl₀
    have hl₀P : S.lamP l₀ = S.tau := by simp [lamP, hl₀]
    have hl₀K : (l₀ : G) ∈ K := by
      rw [S.hstab', hl₀P]; exact S.tau_zero
    obtain ⟨k, hk, hne⟩ := hout l₀ hl₀K
    apply hne
    have h1 := S.tau_conj ⟨k, S.hKL hk⟩
    rw [← hl₀P, ← S.lamP_mul, ← S.lamP_mul] at h1
    have h2 := S.lamP_injective h1
    have h3 := congrArg (fun z : ↥L => (z : G)) h2
    simp only [Subgroup.coe_mul, cu_coe] at h3
    calc u * k * u⁻¹ = (u * k * u⁻¹ * l₀) * (l₀ : G)⁻¹ := by group
      _ = (l₀ : G) * k * (l₀ : G)⁻¹ := by rw [← h3]
  · exact h

variable (tau : Perm (Fin (n + 1)))

open Classical in
@[expose] noncomputable def thetaFun (y : G) : Perm (Fin (n + 1)) :=
  if h : y ∈ L then S.lamP ⟨y, h⟩
  else if h' : y * u⁻¹ ∈ L then S.lamP ⟨y * u⁻¹, h'⟩ * tau else 1

theorem thetaFun_of_mem {y : G} (h : y ∈ L) : S.thetaFun tau y = S.lamP ⟨y, h⟩ := by
  simp [thetaFun, h]

theorem thetaFun_of_not_mem {y : G} (h : y ∉ L) (h' : y * u⁻¹ ∈ L) :
    S.thetaFun tau y = S.lamP ⟨y * u⁻¹, h'⟩ * tau := by
  simp [thetaFun, h, h']

theorem thetaFun_mul (htau_conj : ∀ l : ↥L, tau * S.lamP l = S.lamP (S.cu l) * tau)
    (htau_sq : tau * tau = 1) {y y' : G} (hy : y ∈ L ∨ y * u⁻¹ ∈ L)
    (hy' : y' ∈ L ∨ y' * u⁻¹ ∈ L) :
    S.thetaFun tau (y * y') = S.thetaFun tau y * S.thetaFun tau y' := by
  by_cases h1 : y ∈ L <;> by_cases h2 : y' ∈ L
  · have h12 : y * y' ∈ L := L.mul_mem h1 h2
    rw [S.thetaFun_of_mem tau h12, S.thetaFun_of_mem tau h1, S.thetaFun_of_mem tau h2]
    exact S.lamP_mul ⟨y, h1⟩ ⟨y', h2⟩
  · have h2' : y' * u⁻¹ ∈ L := hy'.resolve_left h2
    have h12 : y * y' ∉ L := fun h => h2 (by simpa using L.mul_mem (L.inv_mem h1) h)
    have h12' : (y * y') * u⁻¹ ∈ L := by rw [mul_assoc]; exact L.mul_mem h1 h2'
    rw [S.thetaFun_of_not_mem tau h12 h12', S.thetaFun_of_mem tau h1,
      S.thetaFun_of_not_mem tau h2 h2']
    have : (⟨(y * y') * u⁻¹, h12'⟩ : ↥L) = ⟨y, h1⟩ * ⟨y' * u⁻¹, h2'⟩ := by
      apply Subtype.ext; show (y * y') * u⁻¹ = y * (y' * u⁻¹); group
    rw [this, S.lamP_mul, mul_assoc]
  · have h1' : y * u⁻¹ ∈ L := hy.resolve_left h1
    have h12 : y * y' ∉ L := fun h => h1 (by simpa using L.mul_mem h (L.inv_mem h2))
    have h12' : (y * y') * u⁻¹ ∈ L := by
      have : (y * y') * u⁻¹ = (y * u⁻¹) * (u * y' * u⁻¹) := by group
      rw [this]; exact L.mul_mem h1' (S.huL y' h2)
    rw [S.thetaFun_of_not_mem tau h12 h12', S.thetaFun_of_not_mem tau h1 h1',
      S.thetaFun_of_mem tau h2]
    have : (⟨(y * y') * u⁻¹, h12'⟩ : ↥L) = ⟨y * u⁻¹, h1'⟩ * S.cu ⟨y', h2⟩ := by
      apply Subtype.ext; show (y * y') * u⁻¹ = (y * u⁻¹) * (u * y' * u⁻¹); group
    rw [this, S.lamP_mul, mul_assoc, mul_assoc, htau_conj ⟨y', h2⟩]
  · have h1' : y * u⁻¹ ∈ L := hy.resolve_left h1
    have h2' : y' * u⁻¹ ∈ L := hy'.resolve_left h2
    have e : y * y' = (y * u⁻¹) * (u * (y' * u⁻¹) * u⁻¹) := by
      calc y * y' = (y * u⁻¹) * (u * (y' * u⁻¹) * u⁻¹) * (u * u) := by group
        _ = (y * u⁻¹) * (u * (y' * u⁻¹) * u⁻¹) := by rw [S.hu2, mul_one]
    have h12 : y * y' ∈ L := by rw [e]; exact L.mul_mem h1' (S.huL _ h2')
    rw [S.thetaFun_of_mem tau h12, S.thetaFun_of_not_mem tau h1 h1',
      S.thetaFun_of_not_mem tau h2 h2']
    have : (⟨y * y', h12⟩ : ↥L) = ⟨y * u⁻¹, h1'⟩ * S.cu ⟨y' * u⁻¹, h2'⟩ := by
      apply Subtype.ext; exact e
    rw [this, S.lamP_mul]
    calc S.lamP ⟨y * u⁻¹, h1'⟩ * S.lamP (S.cu ⟨y' * u⁻¹, h2'⟩)
        = S.lamP ⟨y * u⁻¹, h1'⟩ * S.lamP (S.cu ⟨y' * u⁻¹, h2'⟩) * (tau * tau) := by
          rw [htau_sq, mul_one]
      _ = S.lamP ⟨y * u⁻¹, h1'⟩ * (S.lamP (S.cu ⟨y' * u⁻¹, h2'⟩) * tau) * tau := by group
      _ = S.lamP ⟨y * u⁻¹, h1'⟩ * (tau * S.lamP ⟨y' * u⁻¹, h2'⟩) * tau := by
          rw [htau_conj ⟨y' * u⁻¹, h2'⟩]
      _ = S.lamP ⟨y * u⁻¹, h1'⟩ * tau * (S.lamP ⟨y' * u⁻¹, h2'⟩ * tau) := by group

theorem exists_theta (htau_conj : ∀ l : ↥L, tau * S.lamP l = S.lamP (S.cu l) * tau)
    (htau_sq : tau * tau = 1) (htau0 : tau 0 = 0) (hsign : Equiv.Perm.sign tau = -1)
    (hu : u ∉ L) (hY : ∀ y, y ∈ L ⊔ zpowers u ↔ y ∈ L ∨ y * u⁻¹ ∈ L)
    (hYK : ∀ y, y ∈ K ⊔ zpowers u ↔ y ∈ K ∨ y * u⁻¹ ∈ K) :
    ∃ Θ : ↥(L ⊔ zpowers u) ≃* Perm (Fin (n + 1)),
      (∀ y : ↥(L ⊔ zpowers u), (y : G) ∈ L ↔ Equiv.Perm.sign (Θ y) = 1) ∧
      (∀ y : ↥(L ⊔ zpowers u), (y : G) ∈ K ⊔ zpowers u ↔ Θ y 0 = 0) ∧
      (∀ (l : G) (h : l ∈ L) (h' : l ∈ L ⊔ zpowers u), Θ ⟨l, h'⟩ = S.lamP ⟨l, h⟩) := by
  let θ : ↥(L ⊔ zpowers u) →* Perm (Fin (n + 1)) :=
    { toFun := fun y => S.thetaFun tau y
      map_one' := by
        show S.thetaFun tau (1 : G) = 1
        rw [S.thetaFun_of_mem tau (L.one_mem)]
        exact S.lamP_one
      map_mul' := fun a b => S.thetaFun_mul tau htau_conj htau_sq ((hY a).1 a.2) ((hY b).1 b.2) }
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    have h : S.thetaFun tau a = 1 := ha
    by_cases h1 : (a : G) ∈ L
    · rw [S.thetaFun_of_mem tau h1] at h
      have : (⟨a, h1⟩ : ↥L) = 1 := S.lamP_injective (by rw [h, S.lamP_one])
      exact congrArg (fun z : ↥L => (z : G)) this
    · have h1' := ((hY a).1 a.2).resolve_left h1
      rw [S.thetaFun_of_not_mem tau h1 h1'] at h
      have := congrArg Equiv.Perm.sign h
      rw [Equiv.Perm.sign_mul, S.sign_lamP, hsign, one_mul, map_one] at this
      exact absurd this (by decide)
  have hsurj : Function.Surjective θ := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · refine ⟨⟨((S.lam.symm ⟨σ, Equiv.Perm.mem_alternatingGroup.2 h⟩ : ↥L) : G),
        (hY _).2 (Or.inl (SetLike.coe_mem _))⟩, ?_⟩
      show S.thetaFun tau _ = σ
      rw [S.thetaFun_of_mem tau (SetLike.coe_mem _)]
      simp [lamP]
    · have h' : Equiv.Perm.sign (σ * tau) = 1 := by
        rw [Equiv.Perm.sign_mul, h, hsign]; decide
      set l₁ : ↥L := S.lam.symm ⟨σ * tau, Equiv.Perm.mem_alternatingGroup.2 h'⟩ with hl₁def
      have hl₁ : S.lamP l₁ = σ * tau := by simp [lamP, l₁]
      have hy1 : ((l₁ : G) * u) * u⁻¹ ∈ L := by simp
      have hy0 : (l₁ : G) * u ∉ L := fun h => hu (by simpa using L.mul_mem (L.inv_mem l₁.2) h)
      refine ⟨⟨(l₁ : G) * u, (hY _).2 (Or.inr hy1)⟩, ?_⟩
      show S.thetaFun tau ((l₁ : G) * u) = σ
      rw [S.thetaFun_of_not_mem tau hy0 hy1]
      have : (⟨(l₁ : G) * u * u⁻¹, hy1⟩ : ↥L) = l₁ := Subtype.ext (by group)
      rw [this, hl₁, mul_assoc, htau_sq, mul_one]
  refine ⟨MulEquiv.ofBijective θ ⟨hinj, hsurj⟩, ?_, ?_, ?_⟩
  · intro y
    show (y : G) ∈ L ↔ Equiv.Perm.sign (S.thetaFun tau y) = 1
    by_cases h1 : (y : G) ∈ L
    · rw [S.thetaFun_of_mem tau h1, S.sign_lamP]
      exact iff_of_true h1 rfl
    · have h1' := ((hY y).1 y.2).resolve_left h1
      rw [S.thetaFun_of_not_mem tau h1 h1', Equiv.Perm.sign_mul, S.sign_lamP, hsign, one_mul]
      exact iff_of_false h1 (by decide)
  · intro y
    show (y : G) ∈ K ⊔ zpowers u ↔ S.thetaFun tau y 0 = 0
    rw [hYK]
    by_cases h1 : (y : G) ∈ L
    · rw [S.thetaFun_of_mem tau h1]
      have : (y : G) * u⁻¹ ∈ K ↔ False := by
        constructor
        · intro h
          exfalso
          apply hu
          have h2 := S.hKL h
          have h3 : u⁻¹ ∈ L := by simpa using L.mul_mem (L.inv_mem h1) h2
          simpa using L.inv_mem h3
        · exact False.elim
      rw [this, or_false]
      exact S.hstab' ⟨y, h1⟩
    · have h1' := ((hY y).1 y.2).resolve_left h1
      rw [S.thetaFun_of_not_mem tau h1 h1', Perm.mul_apply, htau0]
      have : (y : G) ∈ K ↔ False := ⟨fun h => h1 (S.hKL h), False.elim⟩
      rw [this, false_or]
      exact S.hstab' ⟨(y : G) * u⁻¹, h1'⟩
  · intro l h h'
    show S.thetaFun tau l = _
    rw [S.thetaFun_of_mem tau h]

end Setup


end Derive

@[expose] def S_lemma123_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G ≤ 4 → ∀ n ∈ ({5, 6, 7} : Finset ℕ),
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfig n x K T Q S a →
      IsApproxTo G (alternatingGroup (Fin (n + 4))) →
        ∀ t u g : G, Stage3Loc n x K Q t u g →
          ∃ (L : Subgroup G) (lam : ↥L ≃* alternatingGroup (Fin (n + 1))),
            (∀ l ∈ L, l * t = t * l) ∧
            (∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) ∧
            (∀ i : ℤ, t ^ i ∈ L → t ^ i = 1) ∧
            (n ≠ 5 → ∀ h : g * t * g⁻¹ ∈ L,
              ((lam ⟨g * t * g⁻¹, h⟩ : alternatingGroup (Fin (n + 1))) :
                Equiv.Perm (Fin (n + 1))).IsThreeCycle)

theorem out_of_config {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G}
    {a : G} {t u : G} (h : IsAConfig n x K T Q S a) (hS : Stage3Base n x K Q t u) :
    ∀ k₀ ∈ K, ∃ k ∈ K, u * k * u⁻¹ ≠ k₀ * k * k₀⁻¹ := by
  intro k₀ hk₀
  by_contra hcon
  push Not at hcon
  have hk₀x : k₀ * x = x * k₀ := mem_centralizer_singleton_iff.1 (h.K_le_C hk₀)
  have hz : k₀⁻¹ * u ∈ Q := by
    rw [h.mem_Q_iff]
    refine ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have h1 : k₀⁻¹ * x = x * k₀⁻¹ := (Commute.inv_left (show Commute k₀ x from hk₀x)).eq
      calc k₀⁻¹ * u * x = k₀⁻¹ * (u * x) := by group
        _ = k₀⁻¹ * (x * u) := by rw [hS.u_comm_x]
        _ = (k₀⁻¹ * x) * u := by group
        _ = (x * k₀⁻¹) * u := by rw [h1]
        _ = x * (k₀⁻¹ * u) := by group
    · intro k hk
      have h1 : u * k = k₀ * k * k₀⁻¹ * u := by rw [← hcon k hk]; group
      calc k * (k₀⁻¹ * u) = k₀⁻¹ * (k₀ * k * k₀⁻¹ * u) := by group
        _ = k₀⁻¹ * (u * k) := by rw [h1]
        _ = (k₀⁻¹ * u) * k := by group
  exact hS.u_not_KQ k₀ hk₀ _ hz (by group)

theorem exists_threeLocal_of_centralizer
    {G : Type} [Group G] {n : ℕ} {x : G} {K Q : Subgroup G} {t u g : G}
    (hS : Stage3Loc n x K Q t u g) (hn : 5 ≤ n)
    (L : Subgroup G) (lam₀ : ↥L ≃* alternatingGroup (Fin (n + 1)))
    (hLt : ∀ l ∈ L, l * t = t * l)
    (hC' : ∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l)
    (hZ : ∀ i : ℤ, t ^ i ∈ L → t ^ i = 1)
    (hthree₀ : n ≠ 5 → ∀ h : g * t * g⁻¹ ∈ L,
      ((lam₀ ⟨g * t * g⁻¹, h⟩ : alternatingGroup (Fin (n + 1))) :
        Equiv.Perm (Fin (n + 1))).IsThreeCycle)
    (hout : ∀ k₀ ∈ K, ∃ k ∈ K, u * k * u⁻¹ ≠ k₀ * k * k₀⁻¹) :
    ∃ Θ : ↥(L ⊔ zpowers u) ≃* Equiv.Perm (Fin (n + 1)),
      ThreeLocal n K t u g L Θ := by
  have hn5 : 5 ≤ n := hn
  obtain ⟨eK⟩ := hS.K_alt
  have hKperf : K ≤ ⁅K, K⁆ := Coord.le_commutator_of_equiv hn5 eK
  have hLperf : L ≤ ⁅L, L⁆ := Coord.le_commutator_of_equiv (by omega : 5 ≤ n + 1) lam₀
  have hKL : K ≤ L := Derive.le_of_perfect hKperf (fun k hk => (hS.t_comm_K k hk).symm) hLt hC'
  obtain ⟨lam, hstab⟩ := CosetIso.exists_stab_iso hn5 hKL lam₀ eK
    (Coord.commutator_eq_top_of_equiv (by omega : 5 ≤ n + 1) lam₀)
  have hAut : n ≠ 5 → ∀ α : MulAut (alternatingGroup (Fin (n + 1))),
      ∃ σ : Perm (Fin (n + 1)), ∀ a : alternatingGroup (Fin (n + 1)),
        ((α a : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) = σ * a * σ⁻¹ := by
    intro h5 α
    obtain ⟨σ, hσ⟩ :=
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj (n + 1) (by omega)
        (by omega)).2 α
    exact ⟨σ, fun a => by rw [← hσ]; exact MulAut.conjNormal_apply σ a⟩
  have hgtL : g * t * g⁻¹ ∈ L := hKL hS.gt_K
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have hl3 : (⟨g * t * g⁻¹, hgtL⟩ : ↥L) ^ 3 = 1 :=
    Subtype.ext (by show (g * t * g⁻¹) ^ 3 = 1; rw [conj_pow, ht3]; group)
  have hl1 : (⟨g * t * g⁻¹, hgtL⟩ : ↥L) ≠ 1 := by
    intro h1
    have h2 : g * t * g⁻¹ = 1 := congrArg (fun z : ↥L => (z : G)) h1
    have h3 : t = 1 := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    have := hS.t_order
    rw [h3, orderOf_one] at this
    omega
  have hthree : ((lam ⟨g * t * g⁻¹, hgtL⟩ : alternatingGroup (Fin (n + 1))) :
      Perm (Fin (n + 1))).IsThreeCycle :=
    CosetIso.threeCycle_transfer hAut lam₀ lam ⟨g * t * g⁻¹, hgtL⟩ hl3 hl1
      (fun h5 => hthree₀ h5 hgtL) ((hstab _).1 hS.gt_K)
  have huL : ∀ l ∈ L, u * l * u⁻¹ ∈ L := Derive.conj_mem_of_inv hLperf hS.u_inv_t hLt hC'
  have hu2 : u * u = 1 := by rw [← sq]; exact hS.u_sq
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have huNL : u ∉ L := by
    intro huL'
    have h1 : u * t = t * u := hLt u huL'
    have h2 : u * t * u⁻¹ = t := by rw [h1]; group
    rw [hS.u_inv_t] at h2
    have h3 : t * t = 1 := mul_eq_one_iff_eq_inv.2 h2.symm
    have h4 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h3)
    rw [hS.t_order] at h4
    omega
  let D : Derive.Setup n K L u := ⟨lam, by omega, hKL, huL, hS.u_norm_K, hu2, hstab⟩
  obtain ⟨Θ, hΘalt, hΘstab, hΘL⟩ := D.exists_theta D.tau D.tau_conj D.tau_mul_tau D.tau_zero
    (D.sign_tau hout) huNL
    (fun y => mem_sup_zpowers_iff huL hS.u_sq) (fun y => mem_sup_zpowers_iff hS.u_norm_K hS.u_sq)
  have hgtY : g * t * g⁻¹ ∈ L ⊔ zpowers u := mem_sup_left hgtL
  refine ⟨Θ, ⟨⟨hKL, huL, huNL, hLt, hC', hZ, ?_⟩, hΘalt, hΘstab, ⟨hgtY, ?_⟩⟩⟩
  · intro w hw
    have e1 : w * u * t * (w * u)⁻¹ = t := by
      calc w * u * t * (w * u)⁻¹ = w * (u * t * u⁻¹) * w⁻¹ := by group
        _ = w * t⁻¹ * w⁻¹ := by rw [hS.u_inv_t]
        _ = (w * t * w⁻¹)⁻¹ := by group
        _ = t := by rw [hw, inv_inv]
    have hwu : (w * u) * t = t * (w * u) := mul_inv_eq_iff_eq_mul.1 e1
    obtain ⟨i, l, hl, hc⟩ := hC' (w * u) hwu
    refine ⟨i, l, hl, ?_⟩
    calc w = (w * u) * u⁻¹ := by group
      _ = t ^ i * l * u := by rw [hc, hinv]
  · rw [hΘL _ hgtL hgtY]
    exact hthree

theorem s_lemma123_of_core (hB : S_lemma123_core) : S_lemma123 := by
  intro G _ _ hC n hn x K T Q S a h hap t u g hS
  obtain ⟨L, lam₀, hLt, hC', hZ, hthree₀⟩ := hB G hC n hn x K T Q S a h hap t u g hS
  have hn5 : 5 ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  exact ⟨L, exists_threeLocal_of_centralizer hS hn5 L lam₀ hLt hC' hZ hthree₀
    (out_of_config h hS.toStage3Base)⟩

end CFSG.GH74.GLS.C3.Prop121
