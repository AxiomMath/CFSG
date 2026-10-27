module

public import CFSG.LargeExtraspecial.S111BDefs
public import CFSG.LargeExtraspecial.S111CNorm
public import CFSG.LargeExtraspecial.S111ATrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

theorem Cfg111.map_conj_eq_of_commute_Lbar (C : Cfg111 S g A) {k : G}
    (hk : k * S.z * k⁻¹ ∈ A) (hkz : k * S.z * k⁻¹ ≠ S.z) {σ : S.O} (hσ : σ ∈ S.Lbar k)
    (hσ1 : σ ≠ 1) {t : S.M} (hc : S.ρ t * σ = σ * S.ρ t) :
    A.map (MulAut.conj (t : G)).toMonoidHom = A := by
  have hkQ := C.inc.le_QG hk
  have hσt : σ ∈ S.Lbar ((t : G) * k) := by
    rw [mem_Lbar_mul_iff, mul_assoc, ← hc, inv_mul_cancel_left]
    exact hσ
  have hne : S.Lbar k ⊓ S.Lbar ((t : G) * k) ≠ ⊥ := fun h0 => by
    have hmem : σ ∈ S.Lbar k ⊓ S.Lbar ((t : G) * k) := ⟨hσ, hσt⟩
    rw [h0] at hmem
    exact hσ1 ((Subgroup.mem_bot).mp hmem)
  have h1 := C.mem_of_Lbar_inf_ne_bot hk hkz (conj_mem_QG' S t.2 hkQ) (conj_ne_z' S t.2 hkz) hne
  rw [mul_conj_z] at h1
  exact C.map_eq_of_conj_mem t.2 hk hkz h1

omit [Finite G] in
theorem commute_or_commute_or_commute {x a b : G} (hx : x ∈ S.QG) (ha : a ∈ S.QG)
    (hb : b ∈ S.QG) : x * a = a * x ∨ x * b = b * x ∨ x * (a * b) = a * b * x := by
  rcases S.mul_comm_or hx ha with h1 | h1
  · exact Or.inl h1
  rcases S.mul_comm_or hx hb with h2 | h2
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  have hza : a * S.z = S.z * a := S.z_comm_QG ha
  calc x * (a * b) = (x * a) * b := by rw [mul_assoc]
    _ = S.z * (a * x) * b := by rw [h1]
    _ = S.z * a * (x * b) := by simp only [mul_assoc]
    _ = S.z * a * (S.z * (b * x)) := by rw [h2]
    _ = S.z * (a * S.z) * (b * x) := by simp only [mul_assoc]
    _ = S.z * (S.z * a) * (b * x) := by rw [hza]
    _ = (S.z * S.z) * (a * (b * x)) := by simp only [mul_assoc]
    _ = a * b * x := by rw [S.z_mul_z, one_mul, mul_assoc]

omit [Finite G] in
theorem cl_conj_eq_of_comm_mem {x s : G} (hx : x ∈ S.QG)
    (hc : x * s * x⁻¹ * s⁻¹ ∈ zpowers S.z) : S.cl (s * x * s⁻¹) = S.cl x := by
  have e : s * x * s⁻¹ = (x * s * x⁻¹ * s⁻¹)⁻¹ * x := by group
  rcases (Setting.mem_zpowers_iff_of_mul_self S.z_mul_z).mp hc with h1 | h1
  · rw [e, h1, inv_one, one_mul]
  · rw [e, h1, S.z_inv, ← S.z_comm_QG hx, S.cl_mul_z hx]

variable {h k k' : G}

theorem Pair111.cl_conj_eq_of_commute (P : Pair111 S g A h k k') {j : G}
    (hj : j * S.z * j⁻¹ ∈ A) (hjz : j * S.z * j⁻¹ ≠ S.z) {s : G} (hs : s ∈ S.Qa j)
    (hsA : (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj s).toMonoidHom =
      A.map (MulAut.conj h).toMonoidHom)
    {x : G} (hx : x ∈ A.map (MulAut.conj h).toMonoidHom)
    (hxe : x * (j * S.z * j⁻¹) = j * S.z * j⁻¹ * x) :
    S.cl (s * x * s⁻¹) = S.cl x := by
  have hxQ : x ∈ S.QG := (P.cfg.inc.map_conj P.hM).le_QG hx
  refine cl_conj_eq_of_comm_mem hxQ (P.inf_Qa_le hj hjz ⟨?_, ?_⟩)
  · have h1 : s * x⁻¹ * s⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom :=
      conj_mem_of_map_eq hsA (inv_mem hx)
    have e : x * s * x⁻¹ * s⁻¹ = x * (s * x⁻¹ * s⁻¹) := by group
    rw [e]
    exact mul_mem hx h1
  · have hxM : x ∈ (S.conjBy j).M := mem_centralizer_singleton_iff.mpr hxe
    have h1 : x * s * x⁻¹ ∈ S.Qa j := (S.conjBy j).conj_mem_QG hxM hs
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hs)

theorem Pair111.mem_normalizer_of_commute (P : Pair111 S g A h k k') {σ τ : S.O}
    (hσ : σ ∈ S.Lbar k) (hσ1 : σ ≠ 1) (hτ : τ ∈ S.Lbar k') (hτ1 : τ ≠ 1)
    (hc : σ * τ = τ * σ) : τ ∈ normalizer (S.Lbar k : Set S.O) := by
  obtain ⟨t, htL, rfl⟩ := (mem_Lbar S).mp hτ
  have hkQ := P.memQ
  have hAt : A.map (MulAut.conj (t : G)).toMonoidHom = A :=
    P.cfg.map_conj_eq_of_commute_Lbar P.mem P.ne hσ hσ1 hc.symm
  have hsA : ∀ s : S.M, S.ρ s = σ → (A.map (MulAut.conj h).toMonoidHom).map
      (MulAut.conj (s : G)).toMonoidHom = A.map (MulAut.conj h).toMonoidHom := fun s hs =>
    P.swap.cfg.map_conj_eq_of_commute_Lbar P.mem' P.ne' hτ hτ1 (by rw [hs]; exact hc)
  by_contra hN
  have hα'A : (t : G) * k * S.z * ((t : G) * k)⁻¹ ∈ A := by
    rw [mul_conj_z]; exact conj_mem_of_map_eq hAt P.mem
  have hLt : S.Lbar ((t : G) * k) = (S.Lbar k).map (MulAut.conj (S.ρ t)).toMonoidHom :=
    Lbar_mul S t k
  have hne1 : (t : G) * k * S.z * ((t : G) * k)⁻¹ ≠ k * S.z * k⁻¹ := fun e => hN
    (mem_normalizer_of_map_conj_eq (by rw [← hLt]; exact Lbar_eq_of_conj_eq S e))
  have hne2 : (t : G) * k * S.z * ((t : G) * k)⁻¹ ≠ k * S.z * k⁻¹ * S.z := fun e => hN
    (mem_normalizer_of_map_conj_eq
      (by rw [← hLt]; exact Lbar_eq_of_conj_eq_mul_z S hkQ P.ne e))
  have hσt : σ ∈ S.Lbar ((t : G) * k) := by
    rw [mem_Lbar_mul_iff, mul_assoc, hc, inv_mul_cancel_left]
    exact hσ
  have hαα : k * S.z * k⁻¹ * (k * S.z * k⁻¹) = 1 := P.cfg.inc.mul_self P.mem
  have hαα'1 : k * S.z * k⁻¹ * ((t : G) * k * S.z * ((t : G) * k)⁻¹) ≠ 1 := fun e =>
    hne1 ((eq_inv_of_mul_eq_one_right e).trans (inv_eq_of_mul_eq_one_right hαα))
  have hαα'z : k * S.z * k⁻¹ * ((t : G) * k * S.z * ((t : G) * k)⁻¹) ≠ S.z := fun e => hne2 (by
    calc (t : G) * k * S.z * ((t : G) * k)⁻¹
        = (k * S.z * k⁻¹)⁻¹ * (k * S.z * k⁻¹ * ((t : G) * k * S.z * ((t : G) * k)⁻¹)) := by
          group
      _ = k * S.z * k⁻¹ * S.z := by rw [e, inv_eq_of_mul_eq_one_right hαα])
  obtain ⟨k'', hk''⟩ := P.cfg.inc.conj _ (mul_mem P.mem hα'A) hαα'1
  have hk''A : k'' * S.z * k''⁻¹ ∈ A := hk'' ▸ mul_mem P.mem hα'A
  have hk''z : k'' * S.z * k''⁻¹ ≠ S.z := hk'' ▸ hαα'z
  have hσk'' : σ ∈ S.Lbar k'' :=
    Lbar_inf_le_Lbar_mul (P.cfg.inc.le_QG hα'A) (conj_ne_z' S t.2 P.ne) P.ne
      (P.cfg.inc.le_Qa _ hα'A P.mem) hne1 hne2 hk''.symm ⟨hσ, hσt⟩
  have hfix : ∀ x ∈ A.map (MulAut.conj h).toMonoidHom,
      ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x := by
    intro x hx
    have hxQ : x ∈ S.QG := (P.cfg.inc.map_conj P.hM).le_QG hx
    have key : ∀ j : G, j * S.z * j⁻¹ ∈ A → j * S.z * j⁻¹ ≠ S.z → σ ∈ S.Lbar j →
        x * (j * S.z * j⁻¹) = j * S.z * j⁻¹ * x →
        ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x := by
      intro j hj hjz hσj hxj
      obtain ⟨s, hsL, hs⟩ := (mem_Lbar S).mp hσj
      rw [← hs, S.ρ_cl s hxQ]
      exact P.cl_conj_eq_of_commute hj hjz (Subgroup.mem_inf.mp hsL).1 (hsA s hs) hx hxj
    rcases commute_or_commute_or_commute hxQ hkQ (P.cfg.inc.le_QG hα'A) with h1 | h1 | h1
    · exact key k P.mem P.ne hσ h1
    · exact key _ hα'A (conj_ne_z' S t.2 P.ne) hσt h1
    · exact key k'' hk''A hk''z hσk'' (by rw [← hk'']; exact h1)
  obtain ⟨s₀, hs₀L, hs₀⟩ := (mem_Lbar S).mp hσ
  have hs₀Q : (s₀ : G) ∉ S.QG := fun hq => hσ1 (by rw [← hs₀]; exact (S.ρ_eq_one_iff s₀).mpr hq)
  have hfixβ := hfix _ P.mem'
  rw [← hs₀, S.ρ_cl s₀ P.memQ'] at hfixβ
  have hcomm : k * S.z * k⁻¹ * (k' * S.z * k'⁻¹) = k' * S.z * k'⁻¹ * (k * S.z * k⁻¹) :=
    commute_of_fix rfl rfl hkQ P.ne P.memQ' hs₀L hs₀Q
      ((S.cl_eq_cl_iff P.memQ' (S.conj_mem_QG s₀.2 P.memQ')).mp hfixβ.symm)
  have htQ : (t : G) ∈ S.Qa k' := (Subgroup.mem_inf.mp htL).1
  have hαM : k * S.z * k⁻¹ ∈ (S.conjBy k').M := mem_centralizer_singleton_iff.mpr hcomm
  have hcm : k * S.z * k⁻¹ * t * (k * S.z * k⁻¹)⁻¹ * (t : G)⁻¹ ∈ zpowers S.z := by
    refine P.inf_Qa_le' ⟨?_, ?_⟩
    · have h1 : (t : G) * (k * S.z * k⁻¹)⁻¹ * (t : G)⁻¹ ∈ A :=
        conj_mem_of_map_eq hAt (inv_mem P.mem)
      have e : k * S.z * k⁻¹ * t * (k * S.z * k⁻¹)⁻¹ * (t : G)⁻¹ =
          k * S.z * k⁻¹ * ((t : G) * (k * S.z * k⁻¹)⁻¹ * (t : G)⁻¹) := by group
      rw [e]
      exact mul_mem P.mem h1
    · exact Subgroup.mul_mem _ ((S.conjBy k').conj_mem_QG hαM htQ) (Subgroup.inv_mem _ htQ)
  have e : (t : G) * k * S.z * ((t : G) * k)⁻¹ =
      (k * S.z * k⁻¹ * t * (k * S.z * k⁻¹)⁻¹ * (t : G)⁻¹)⁻¹ * (k * S.z * k⁻¹) := by group
  rcases (Setting.mem_zpowers_iff_of_mul_self S.z_mul_z).mp hcm with h1 | h1
  · exact hne1 (by rw [e, h1, inv_one, one_mul])
  · exact hne2 (by rw [e, h1, S.z_inv, ← S.z_comm_QG hkQ])

theorem Pair111.mem_normalizer_of_commute' (P : Pair111 S g A h k k') {σ τ : S.O}
    (hσ : σ ∈ S.Lbar k) (hσ1 : σ ≠ 1) (hτ : τ ∈ S.Lbar k') (hτ1 : τ ≠ 1)
    (hc : σ * τ = τ * σ) : σ ∈ normalizer (S.Lbar k' : Set S.O) :=
  P.swap.mem_normalizer_of_commute hτ hτ1 hσ hσ1 hc.symm

theorem Pair111.mem_Ebar_of_commute (P : Pair111 S g A h k k') {σ τ : S.O}
    (hσ : σ ∈ S.Lbar k) (hσ1 : σ ≠ 1) (hτ : τ ∈ S.Lbar k') (hτ1 : τ ≠ 1)
    (hc : σ * τ = τ * σ) : σ ∈ Ebar S k k' ∧ τ ∈ Ebar S k' k :=
  ⟨⟨hσ, P.mem_normalizer_of_commute' hσ hσ1 hτ hτ1 hc⟩,
    ⟨hτ, P.mem_normalizer_of_commute hσ hσ1 hτ hτ1 hc⟩⟩

end CFSG.LargeExtraspecial.S11
