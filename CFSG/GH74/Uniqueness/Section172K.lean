module

public import CFSG.GH74.Uniqueness.Section161
public import CFSG.GH74.Uniqueness.Section12BenderDict
public import CFSG.GH74.Uniqueness.Section12Stmts
public import CFSG.GH74.Uniqueness.Section171Invol

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

namespace Sec172

section Klein

variable {X : Type} [Group X]

omit [Group X] in
theorem klein_sq {G : Type} [Group G] {t u : G} (ht : t * t = 1) (hu : u * u = 1)
    (htu : t * u = u * t) : (t * u) * (t * u) = 1 := by
  calc (t * u) * (t * u) = t * (u * t) * u := by group
    _ = t * (t * u) * u := by rw [← htu]
    _ = (t * t) * (u * u) := by group
    _ = 1 := by rw [ht, hu, one_mul]

def klein (t u : X) (ht : t * t = 1) (hu : u * u = 1) (htu : t * u = u * t) : Subgroup X where
  carrier := {x | x = 1 ∨ x = t ∨ x = u ∨ x = t * u}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h1 : t * (t * u) = u := by rw [← mul_assoc, ht, one_mul]
    have h3 : u * (t * u) = t := by rw [htu, ← mul_assoc, hu, one_mul]
    have h4 : (t * u) * t = u := by rw [htu, mul_assoc, ht, mul_one]
    have h5 : (t * u) * u = t := by rw [mul_assoc, hu, mul_one]
    have h6 : (t * u) * (t * u) = 1 := klein_sq ht hu htu
    have htu' : u * t = t * u := htu.symm
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, ht, hu, htu', h1, h3, h4, h5, h6, true_or, or_true]
  inv_mem' := by
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    have htu' : (t * u)⁻¹ = t * u := inv_eq_of_mul_eq_one_right (klein_sq ht hu htu)
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> simp [ht', hu', htu']

theorem mem_klein {t u : X} {ht : t * t = 1} {hu : u * u = 1} {htu : t * u = u * t} {x : X} :
    x ∈ klein t u ht hu htu ↔ x = 1 ∨ x = t ∨ x = u ∨ x = t * u := Iff.rfl

theorem card_klein {t u : X} (ht : t * t = 1) (hu : u * u = 1) (htu : t * u = u * t)
    (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu' : t ≠ u) : Nat.card ↥(klein t u ht hu htu) = 4 := by
  have hne1 : t * u ≠ 1 := by
    intro h
    exact htu' ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hu))
  have hset : ((klein t u ht hu htu : Subgroup X) : Set X) = {1, t, u, t * u} := by
    ext x
    simp [mem_klein]
  have hcard : Nat.card ↥(klein t u ht hu htu) = ((klein t u ht hu htu : Subgroup X) : Set X).ncard :=
    Nat.card_coe_set_eq _ |>.symm
  rw [hcard, hset]
  have h1 : (1 : X) ∉ ({t, u, t * u} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ht1.symm, hu1.symm, hne1.symm⟩
  have h2 : t ∉ ({u, t * u} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨htu', fun h => hu1 ?_⟩
    have : t * u = t * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have h3 : u ∉ ({t * u} : Set X) := by
    simp only [Set.mem_singleton_iff]
    intro h
    apply ht1
    have : t * u = 1 * u := by rw [one_mul]; exact h.symm
    exact mul_right_cancel this
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_insert_of_notMem h3,
    Set.ncard_singleton]

end Klein

section K

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem kGrp_le_pPrimeCoreIn (hZ : IsInvariantInvolutionSet Z) {t : X} (ht : t ∈ Z) :
    kGrp M t ≤ pPrimeCoreIn (M ⊓ conjugate M t) := by
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have hTO : zpowers t ≤ normalizer (pPrimeCoreIn (M ⊓ conjugate M t) : Set X) :=
    zpowers_le.mpr (mem_normalizer_pPrimeCoreIn (mem_normalizer_inf_conjugate ht2))
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp hTO

theorem kGrp_le_D (hZ : IsInvariantInvolutionSet Z) {t : X} (ht : t ∈ Z) :
    kGrp M t ≤ M ⊓ conjugate M t :=
  (kGrp_le_pPrimeCoreIn hZ ht).trans (pPrimeCoreIn_le _)

omit [Finite X] in
theorem conj_mem_kGrp {t g : X} (hgt : g * t = t * g)
    (hgO : ∀ b ∈ pPrimeCoreIn (M ⊓ conjugate M t), g * b * g⁻¹ ∈ pPrimeCoreIn (M ⊓ conjugate M t))
    {y : X} (hy : y ∈ kGrp M t) : g * y * g⁻¹ ∈ kGrp M t := by
  have hle : kGrp M t ≤ (kGrp M t).comap (MulAut.conj g).toMonoidHom := by
    rw [kGrp, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcomm : g * t ^ n * g⁻¹ = t ^ n := by
      have : Commute g (t ^ n) := (Commute.zpow_right (show Commute g t from hgt) n)
      rw [this.eq]
      group
    have e : (MulAut.conj g).toMonoidHom ⁅t ^ n, b⁆ = ⁅t ^ n, g * b * g⁻¹⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      calc g * (t ^ n * b * (t ^ n)⁻¹ * b⁻¹) * g⁻¹
          = (g * t ^ n * g⁻¹) * (g * b * g⁻¹) * (g * t ^ n * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
        _ = t ^ n * (g * b * g⁻¹) * (t ^ n)⁻¹ * (g * b * g⁻¹)⁻¹ := by rw [hcomm]
    rw [e]
    exact Subgroup.commutator_mem_commutator ha (hgO b hb)
  have := hle hy
  simpa using this

theorem u_mem_normalizer_kGrp (c : Conf16 Z M) : c.u ∈ normalizer (kGrp M c.t : Set X) := by
  have hu : c.u ∈ c.D := c.hu
  have hn : ∀ b ∈ pPrimeCoreIn c.D, c.u * b * c.u⁻¹ ∈ pPrimeCoreIn c.D := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp (pPrimeCoreIn_normalizes c.D hu) b).mp hb
  have hn' : ∀ b ∈ pPrimeCoreIn c.D, c.u⁻¹ * b * c.u⁻¹⁻¹ ∈ pPrimeCoreIn c.D := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp (pPrimeCoreIn_normalizes c.D (c.D.inv_mem hu)) b).mp hb
  have hcomm : c.u * c.t = c.t * c.u := c.t_mul_u_comm.symm
  have hcomm' : c.u⁻¹ * c.t = c.t * c.u⁻¹ := by
    calc c.u⁻¹ * c.t = c.u⁻¹ * (c.t * c.u) * c.u⁻¹ := by group
      _ = c.u⁻¹ * (c.u * c.t) * c.u⁻¹ := by rw [c.t_mul_u_comm]
      _ = c.t * c.u⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => conj_mem_kGrp hcomm hn hy
  · intro hy
    have := conj_mem_kGrp hcomm' hn' hy
    simpa [mul_assoc] using this

omit [Finite X] in
theorem mem_cenHull_conj (hZ : IsInvariantInvolutionSet Z) {v x : X} (g : X)
    (hx : x ∈ cenHull Z v) : g * x * g⁻¹ ∈ cenHull Z (g * v * g⁻¹) := by
  have hle : cenHull Z v ≤ (cenHull Z (g * v * g⁻¹)).comap (MulAut.conj g).toMonoidHom := by
    rw [cenHull, zHull, Subgroup.closure_le]
    rintro y ⟨hyZ, hyC⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := by simp
    rw [e]
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · have := hZ.2 y hyZ g⁻¹
      rwa [inv_inv] at this
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      calc g * y * g⁻¹ * (g * v * g⁻¹) = g * (y * v) * g⁻¹ := by group
        _ = g * (v * y) * g⁻¹ := by rw [hyC]
        _ = _ := by group
  have := hle hx
  simpa using this

theorem u_mul_z_comm (h164 : Lemma164Stmt Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M (cenHull Z c.u) n i e) : c.u * c.z = c.z * c.u := by
  have h1 := ((h164 c n i e hB).2.1).1
  have hcl : omegaOneSub (centerIn c.T1) ≤ centerIn c.T1 := by
    rw [omegaOneSub, Subgroup.closure_le]
    exact fun x hx => hx.1
  have hu : c.u ∈ centerIn c.T1 := hcl (h1 (Subgroup.subset_closure (Set.mem_insert _ _)))
  have hz : c.z ∈ centerIn c.T1 :=
    hcl (h1 (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have huT : c.u ∈ c.T1 := (Subgroup.mem_inf.mp hu).1
  have hzc : c.z ∈ centralizer (c.T1 : Set X) := (Subgroup.mem_inf.mp hz).2
  exact Subgroup.mem_centralizer_iff.mp hzc c.u huT

end K


end Sec172

section ClaimX

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

open Sec172 in
theorem ZDSetup.exists_not_comm_of_tu
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M)
    (h161 : Lemma161Stmt Z M) (c : Conf16 Z M) (hzu : c.u * c.z = c.z * c.u) :
    ∃ x ∈ kGrp M c.t, x * (c.t * c.u) = (c.t * c.u) * x ∧ x * c.t ≠ c.t * x := by
  by_contra hcon
  push Not at hcon
  have ht2 := S.conf_t_sq c
  have hu2 := c.u_sq
  have htu := c.t_mul_u_comm
  have ht1 : c.t ≠ 1 := by
    intro h
    have := S.invariant.1 c.t c.ht
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hu1 : c.u ≠ 1 := by
    intro h
    have := c.hu2
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have htne : c.t ≠ c.u := by
    intro h
    exact c.htM (h ▸ (Subgroup.mem_inf.mp c.hu).1)
  set W := klein c.t c.u ht2 hu2 htu with hW
  have hW4 : Nat.card ↥W = 4 := card_klein ht2 hu2 htu ht1 hu1 htne
  have hW2 : ∀ w ∈ W, w * w = 1 := by
    intro w hw
    rcases mem_klein.mp hw with h | h | h | h
    · rw [h, one_mul]
    · rw [h]
      exact ht2
    · rw [h]
      exact hu2
    · rw [h]
      exact klein_sq ht2 hu2 htu
  have hKt := commutator_zpowers_kGrp M S.invariant c.ht
  have hWN : W ≤ normalizer (kGrp M c.t : Set X) := by
    intro w hw
    rcases mem_klein.mp hw with h | h | h | h
    · rw [h]
      exact (normalizer _).one_mem
    · rw [h]
      exact hKt.2.1
    · rw [h]
      exact u_mem_normalizer_kGrp c
    · rw [h]
      exact (normalizer _).mul_mem hKt.2.1 (u_mem_normalizer_kGrp c)
  have hWt : W ≤ centralizer ({c.t} : Set X) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases mem_klein.mp hw with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
    · rw [h]
      exact htu.symm
    · rw [h, mul_assoc, ← htu]
  have key := h161 c.toCtx16 W hW4 hW2 hWN hWt
  have hK : kGrp M c.t ≤ centralizer ({c.u} : Set X) := by
    rw [key]
    refine iSup₂_le fun w hw => ?_
    rcases mem_klein.mp hw.1 with h | h | h | h
    · exact absurd h hw.2
    · rw [h]
      have : ⁅zpowers c.t, centralizer ({c.t} : Set X) ⊓ kGrp M c.t⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
          Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).1
      rw [this]
      exact bot_le
    · rw [h, Subgroup.commutator_le]
      intro a ha b hb
      have hau : a ∈ centralizer ({c.u} : Set X) := (Subgroup.zpowers_le.mpr c.ht_B) ha
      have hbu : b ∈ centralizer ({c.u} : Set X) := (Subgroup.mem_inf.mp hb).1
      rw [commutatorElement_def]
      exact (centralizer _).mul_mem ((centralizer _).mul_mem ((centralizer _).mul_mem hau hbu)
        ((centralizer _).inv_mem hau)) ((centralizer _).inv_mem hbu)
    · rw [h]
      have : ⁅zpowers c.t, centralizer ({c.t * c.u} : Set X) ⊓ kGrp M c.t⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
          Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
        exact hcon y hy2 (Subgroup.mem_centralizer_singleton_iff.mp hy1)
      rw [this]
      exact bot_le
  have hz' : c.z ∈ centralizer ({c.u} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzu.symm
  have hL : lSubgroup M c.z c.t ≤ centralizer ({c.u} : Set X) := by
    refine sup_le (sup_le ?_ ?_) hK
    · exact Subgroup.zpowers_le.mpr hz'
    · exact Subgroup.zpowers_le.mpr c.ht_B
  rw [h121 c.t c.z c.ht c.htM c.hz c.hzM c.hD] at hL
  have hcentral : c.u ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hL (Subgroup.mem_top g))
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · rw [h, Subgroup.mem_bot] at hcentral
    exact hu1 hcentral
  · apply S.exists_not_commute
    intro a b
    have hb : b ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a

end ClaimX

end CFSG.GH74.Uniqueness
