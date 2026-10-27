module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem pCoreOf_two_le (N : Subgroup G) : CFSG.Open.pCoreOf 2 N ≤ N := Subgroup.map_subtype_le _

theorem pCoreOf_two_isPGroup (N : Subgroup G) : IsPGroup 2 (CFSG.Open.pCoreOf 2 N) := by
  rw [CFSG.Open.pCoreOf]
  exact CFSG.pCore_isPGroup.map _

theorem pCoreOf_two_conj_mem {N : Subgroup G} {g : G} (hg : g ∈ N) {q : G}
    (hq : q ∈ CFSG.Open.pCoreOf 2 N) : g * q * g⁻¹ ∈ CFSG.Open.pCoreOf 2 N := by
  rw [CFSG.Open.pCoreOf] at hq ⊢
  obtain ⟨o', ho', rfl⟩ := hq
  exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

theorem le_pCoreOf_two {N Q : Subgroup G} (hQN : Q ≤ N)
    (hnorm : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) (hQ : IsPGroup 2 Q) :
    Q ≤ CFSG.Open.pCoreOf 2 N := by
  have hnormal : (Q.subgroupOf N).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hnorm g g.2 x hx
  have hp : IsPGroup 2 (Q.subgroupOf N) := hQ.comap_subtype
  have hcore : Q.subgroupOf N ≤ CFSG.pCore 2 ↥N := le_sSup ⟨hnormal, hp⟩
  rw [CFSG.Open.pCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hQN]
  exact Subgroup.map_mono hcore

theorem n4_fix_iff (h : L41GPh3 t L S x₁ x₂ lam rho) (n : G) :
    (∀ x ∈ t • (fourGrp x₁ x₂ : Set G), n * x * n⁻¹ = x) ↔
      n ∈ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
  have ht2 : t * t = 1 := t_mul_self h.hyp
  constructor
  · intro hfix
    have hfixt : n * t * n⁻¹ = t := hfix t (n4_t_mem_omega t x₁ x₂)
    have hfixf : ∀ f ∈ fourGrp x₁ x₂, n * f * n⁻¹ = f := fun f hf =>
      n4_fix_of_fix_mul ht2 hfixt (hfix (t * f) (n4_mem_smul_iff.mpr ⟨f, hf, rfl⟩))
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hA : ctxE t x₁ x₂ ≤ centralizer ({n} : Set G) := by
      refine (Subgroup.closure_le _).mpr fun g hg => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg | hg
      · rw [hg]
        exact n4_comm_of_conj_eq hfixt
      · rw [hg]
        exact n4_comm_of_conj_eq (hfixf _ (n4_y_mem_four x₁ x₂))
      · rw [hg]
        exact n4_comm_of_conj_eq (hfixf _ (n4_z_mem_four x₁ x₂))
    exact (Subgroup.mem_centralizer_singleton_iff).mp (hA ha)
  · intro hn x hx
    obtain ⟨f, hf, rfl⟩ := n4_mem_smul_iff.mp hx
    have hxA : t * f ∈ ctxE t x₁ x₂ :=
      Subgroup.mul_mem _ (n4_t_mem_A t x₁ x₂) (n4_four_le_A t x₁ x₂ hf)
    exact n4_conj_eq_of_comm (Subgroup.mem_centralizer_iff.mp hn _ hxA)

theorem n4_ker (h : L41GPh3 t L S x₁ x₂ lam rho) :
    (conjAct (l41N t x₁ x₂) (t • (fourGrp x₁ x₂ : Set G)) (n4_omega_inv h)).ker =
      (ctxW t x₁ x₂).subgroupOf (l41N t x₁ x₂) := by
  ext n
  rw [MonoidHom.mem_ker, conjAct_eq_one_iff, Subgroup.mem_subgroupOf, ← h.basic.cent_A]
  exact n4_fix_iff h (n : G)

theorem n4_W_le_N (h : L41GPh1 t L S x₁ x₂ lam rho) : ctxW t x₁ x₂ ≤ l41N t x₁ x₂ := by
  intro w hw
  rw [← h.basic.cent_A] at hw
  refine mem_normalizer_of_conj_mem (fun a ha => ?_)
  rw [n4_conj_eq_of_comm (n := w) (g := a) (Subgroup.mem_centralizer_iff.mp hw a ha)]
  exact ha

theorem n4_conj_W (h : L41GPh1 t L S x₁ x₂ lam rho) {n : G} (hn : n ∈ l41N t x₁ x₂) {w : G}
    (hw : w ∈ ctxW t x₁ x₂) : n * w * n⁻¹ ∈ ctxW t x₁ x₂ := by
  rw [← h.basic.cent_A] at hw ⊢
  rw [Subgroup.mem_centralizer_iff] at hw ⊢
  intro a ha
  have ha' : n⁻¹ * a * n ∈ ctxE t x₁ x₂ := (Subgroup.mem_normalizer_iff''.mp hn a).mp ha
  have h1 := hw _ ha'
  calc a * (n * w * n⁻¹) = n * ((n⁻¹ * a * n) * w) * n⁻¹ := by group
    _ = n * (w * (n⁻¹ * a * n)) * n⁻¹ := by rw [h1]
    _ = (n * w * n⁻¹) * a := by group

theorem n4_quot_N (h : L41GPh3 t L S x₁ x₂ lam rho) :
    Sec4SectionIso (l41N t x₁ x₂) (ctxW t x₁ x₂) (Equiv.Perm (Fin 4)) :=
  exists_perm_four_section (n4_omega_inv h) (n4_card_omega h.toCtx0)
    (surjective_of_exists_conj (n4_omega_inv h) (n4_exists_conj_omega h)) (n4_ker h)

theorem n4_card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem n4_card_N (h : L41GPh3 t L S x₁ x₂ lam rho) :
    Nat.card (l41N t x₁ x₂) = 24 * Nat.card (ctxW t x₁ x₂) := by
  obtain ⟨φ, hs, hker⟩ := n4_quot_N h
  have := card_eq_mul_of_section (n4_W_le_N h.toL41GPh1) φ hs hker
  rw [n4_card_perm_four] at this
  exact this

theorem n4_card_N_C (h : L41GPh3 t L S x₁ x₂ lam rho) :
    Nat.card (l41N t x₁ x₂) =
      6 * Nat.card ↥(l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)) := by
  have hX : ∀ n ∈ l41N t x₁ x₂, ∀ x ∈ nonid (fourGrp x₁ x₂),
      n * x * n⁻¹ ∈ nonid (fourGrp x₁ x₂) := conj_mem_nonid (n4_normal_F2 h).2
  have hsurj : Function.Surjective (conjAct (l41N t x₁ x₂) (nonid (fourGrp x₁ x₂)) hX) :=
    surjective_of_exists_conj hX fun σ => by
      obtain ⟨k, hk, hkσ⟩ := n4_exists_conj_F h σ
      exact ⟨k, n4_K_le_N h.toL41GPh1 hk, hkσ⟩
  have := card_eq_six_mul hX (card_nonid (n4_card_four h.toCtx0)) hsurj
  rwa [centralizer_nonid] at this

theorem n4_conj_C (h : L41GPh3 t L S x₁ x₂ lam rho) {n : G} (hn : n ∈ l41N t x₁ x₂) {c : G}
    (hc : c ∈ l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)) :
    n * c * n⁻¹ ∈ l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  refine Subgroup.mem_inf.mpr
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn (Subgroup.mem_inf.mp hc).1) (Subgroup.inv_mem _ hn),
      ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hf' : n⁻¹ * f * n ∈ fourGrp x₁ x₂ := by
    have := (n4_normal_F2 h).2 n⁻¹ (Subgroup.inv_mem _ hn) f hf
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _ hf'
  calc f * (n * c * n⁻¹) = n * ((n⁻¹ * f * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * f * n)) * n⁻¹ := by rw [h1]
    _ = (n * c * n⁻¹) * f := by group

theorem n4_isPGroup_C (h : L41GPh3 t L S x₁ x₂ lam rho) :
    IsPGroup 2 ↥(l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)) := by
  have hC6 := n4_card_N_C h
  have hN24 := n4_card_N h
  have hWp : IsPGroup 2 ↥(ctxW t x₁ x₂) := h.isPGroup.to_le h.basic.normal_W.1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hWp
  have hCW : Nat.card ↥(l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)) =
      2 ^ (k + 2) := by
    rw [pow_add]
    omega
  exact IsPGroup.of_card hCW

theorem n4_O2_eq (h : L41GPh3 t L S x₁ x₂ lam rho) :
    l41O2 t x₁ x₂ = l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hX : ∀ n ∈ l41N t x₁ x₂, ∀ x ∈ nonid (fourGrp x₁ x₂),
      n * x * n⁻¹ ∈ nonid (fourGrp x₁ x₂) := conj_mem_nonid (n4_normal_F2 h).2
  have hy : x₁ ^ 2 ∈ nonid (fourGrp x₁ x₂) :=
    ⟨n4_y_mem_four x₁ x₂, (y_mul_self_ne_one h.wreath).2⟩
  have hρN : rho ∈ l41N t x₁ x₂ := n4_K_le_N h.toL41GPh1 (Subgroup.subset_closure (by simp))
  apply le_antisymm
  · intro q hq
    have hqN : q ∈ l41N t x₁ x₂ := pCoreOf_two_le _ hq
    refine Subgroup.mem_inf.mpr ⟨hqN, ?_⟩
    have hc := centralizes_of_normal_two (N := l41N t x₁ x₂) (Q := l41O2 t x₁ x₂) hX
      (card_nonid (n4_card_four h.toCtx0)) (pCoreOf_two_le _)
      (fun n hn q' hq' => pCoreOf_two_conj_mem hn hq') (pCoreOf_two_isPGroup _) hρN
      (n4_rho_cube h.toCtx0) ⟨x₁ ^ 2, hy, n4_rho_moves h.toCtx0 hy.1 hy.2⟩
    rw [← centralizer_nonid, Subgroup.mem_centralizer_iff]
    intro x hx
    exact n4_comm_of_conj_eq (hc q hq x hx)
  · exact le_pCoreOf_two inf_le_left (fun n hn c hc => n4_conj_C h hn hc) (n4_isPGroup_C h)

theorem n4_card_O2 (h : L41GPh3 t L S x₁ x₂ lam rho) :
    Nat.card (l41O2 t x₁ x₂) = 4 * Nat.card (ctxW t x₁ x₂) := by
  rw [n4_O2_eq h]
  have h1 := n4_card_N_C h
  have h2 := n4_card_N h
  omega

theorem n4_N_eq (h : L41GPh3 t L S x₁ x₂ lam rho) :
    l41N t x₁ x₂ = l41O2 t x₁ x₂ ⊔ closure {rho, lam} := by
  have hX : ∀ n ∈ l41N t x₁ x₂, ∀ x ∈ nonid (fourGrp x₁ x₂),
      n * x * n⁻¹ ∈ nonid (fourGrp x₁ x₂) := conj_mem_nonid (n4_normal_F2 h).2
  apply le_antisymm
  · intro n hn
    obtain ⟨k, hk, hnk⟩ := exists_mul_centralizes (K := closure {rho, lam}) hX
      (fun σ => n4_exists_conj_F h σ) hn
    have hnkC : n * k ∈ l41O2 t x₁ x₂ := by
      rw [n4_O2_eq h]
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hn (n4_K_le_N h.toL41GPh1 hk), ?_⟩
      rw [← centralizer_nonid, Subgroup.mem_centralizer_iff]
      intro x hx
      exact n4_comm_of_conj_eq (hnk x hx)
    have hmem := Subgroup.mul_mem _ (Subgroup.mem_sup_left hnkC)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ hk) : k⁻¹ ∈ l41O2 t x₁ x₂ ⊔ closure {rho, lam})
    rwa [mul_inv_cancel_right] at hmem
  · exact sup_le (pCoreOf_two_le _) (n4_K_le_N h.toL41GPh1)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
