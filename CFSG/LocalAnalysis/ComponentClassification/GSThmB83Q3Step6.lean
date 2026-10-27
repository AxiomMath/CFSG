module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step5c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Conf

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

theorem card_perm_six : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

end Eight

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

structure Q3Data.LClass (d : Q3Data H) where
  C : Set X
  sub : C ⊆ d.E
  not_mem : ∀ x ∈ C, x ∉ d.E0
  inv : ∀ n ∈ d.NE, ∀ x ∈ C, n * x * n⁻¹ ∈ C
  gen : closure C = d.E
  ι : Fin 6 ≃ ↥C

namespace Q3Data

variable {d : Q3Data H}

theorem eq_one_of_fixed (d : Q3Data H) {w : MulAut (h.K ⧸ pPrimeCore 2 h.K)} (hw : w ∈ d.E0hat)
    (hfix : ∀ y ∈ d.NE0hat, y⁻¹ * w * y = w) : w = 1 := by
  have horb : ∀ u, w ∈ Cat8.conjOrbit d.NE0hat u → Cat8.conjOrbit d.NE0hat u = {w} := by
    rintro u ⟨y₀, hy₀, rfl⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Set.mem_singleton_iff.mpr ?_
      rw [show y⁻¹ * u * y = (y₀⁻¹ * y)⁻¹ * (y₀⁻¹ * u * y₀) * (y₀⁻¹ * y) by group]
      exact hfix _ (mul_mem (inv_mem hy₀) hy)
    · rintro rfl
      exact ⟨y₀, hy₀, rfl⟩
  have hone : ∀ u, w ∈ Cat8.conjOrbit d.NE0hat u →
      Nat.card (Cat8.conjOrbit d.NE0hat u) = 1 := fun u hu => by
    rw [horb u hu, Nat.card_unique]
  rcases d.E0hat_cases hw with h1 | h1 | h1
  · exact h1
  · have h2 := hone _ h1
    exfalso
    rcases d.E0hat_card_cases with ⟨-, h3, -⟩ | ⟨-, h3, -⟩ <;> omega
  · have h2 := hone _ h1
    exfalso
    rcases d.E0hat_card_cases with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ <;> omega

theorem mul_mem_E0_of_not_mem (d : Q3Data H) {x y : X} (hx : x ∈ d.E) (hy : y ∈ d.E)
    (hx0 : x ∉ d.E0) (hy0 : y ∉ d.E0) : x * y ∈ d.E0 := by
  obtain ⟨e, he, rfl | rfl⟩ := d.mem_E_cases hx
  · exact absurd he hx0
  obtain ⟨e', he', rfl | rfl⟩ := d.mem_E_cases hy
  · exact absurd he' hy0
  have hb := d.b_comm_E0 he'
  rw [show e * d.b * (e' * d.b) = e * (d.b * e') * d.b by group, ← hb,
    show e * (e' * d.b) * d.b = e * e' * (d.b * d.b) by group, d.b_mul_self, mul_one]
  exact mul_mem he he'

theorem nonempty_LClass (d : Q3Data H) (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    Nonempty d.LClass := by
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := d.exists_class hq hF
  have h6 : Nat.card ↥C = 6 := by rw [Nat.card_coe_set_eq, h3]
  exact ⟨⟨C, h1, h2, h4, h5, (Finite.equivFinOfCardEq h6).symm⟩⟩

namespace LClass

variable (L : d.LClass)

abbrev c (i : Fin 6) : X := (L.ι i : X)

theorem c_mem_E (i : Fin 6) : L.c i ∈ d.E := L.sub (L.ι i).2

theorem c_not_mem_E0 (i : Fin 6) : L.c i ∉ d.E0 := L.not_mem _ (L.ι i).2

theorem c_injective : Function.Injective L.c := fun _ _ hij =>
  L.ι.injective (Subtype.ext hij)

theorem range_c : Set.range L.c = L.C := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (L.ι i).2
  · intro hx
    exact ⟨L.ι.symm ⟨x, hx⟩, by simp [c]⟩

theorem Eof_eq : Eight.Eof L.c = d.E := by
  show closure (Set.range L.c) = d.E
  rw [L.range_c, L.gen]

@[expose] noncomputable def actC : ↥d.NE →* Equiv.Perm ↥L.C where
  toFun n :=
    { toFun := fun x => ⟨(n : X) * x * (n : X)⁻¹, L.inv n n.2 x x.2⟩
      invFun := fun x => ⟨(n : X)⁻¹ * x * n, by
        have := L.inv _ (inv_mem n.2) x x.2
        rwa [inv_inv] at this⟩
      left_inv := fun x => Subtype.ext (by
        show (n : X)⁻¹ * ((n : X) * x * (n : X)⁻¹) * n = x
        group)
      right_inv := fun x => Subtype.ext (by
        show (n : X) * ((n : X)⁻¹ * x * n) * (n : X)⁻¹ = x
        group) }
  map_one' := Equiv.ext fun x => Subtype.ext (by
    show ((1 : ↥d.NE) : X) * x * ((1 : ↥d.NE) : X)⁻¹ = x
    simp)
  map_mul' m n := Equiv.ext fun x => Subtype.ext (by
    show ((m * n : ↥d.NE) : X) * x * ((m * n : ↥d.NE) : X)⁻¹ =
      (m : X) * ((n : X) * x * (n : X)⁻¹) * (m : X)⁻¹
    simp only [Subgroup.coe_mul]
    group)

@[expose] noncomputable def πN : ↥d.NE →* Equiv.Perm (Fin 6) :=
  (L.ι.symm.permCongrHom : Equiv.Perm ↥L.C ≃* Equiv.Perm (Fin 6)).toMonoidHom.comp L.actC

theorem πN_apply (n : ↥d.NE) (i : Fin 6) :
    L.πN n i = L.ι.symm ⟨(n : X) * L.c i * (n : X)⁻¹, L.inv n n.2 _ (L.ι i).2⟩ := rfl

theorem conj_c (n : ↥d.NE) (i : Fin 6) : (n : X) * L.c i * (n : X)⁻¹ = L.c (L.πN n i) := by
  rw [L.πN_apply]
  simp only [LClass.c, Equiv.apply_symm_apply]

theorem πN_eq_one_iff (n : ↥d.NE) : L.πN n = 1 ↔ ∀ e ∈ d.E, e * (n : X) = (n : X) * e := by
  constructor
  · intro h1 e he
    have hC : L.C ⊆ centralizer ({(n : X)} : Set X) := by
      intro x hx
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      have h2 := L.conj_c n (L.ι.symm ⟨x, hx⟩)
      rw [h1, Equiv.Perm.one_apply] at h2
      have h3 : (n : X) * x * (n : X)⁻¹ = x := by simpa [LClass.c] using h2
      calc x * (n : X) = (n : X) * x * (n : X)⁻¹ * n := by rw [h3]
        _ = (n : X) * x := by group
    rw [← L.gen] at he
    exact mem_centralizer_singleton_iff.mp ((closure_le _).mpr hC he)
  · intro h1
    refine Equiv.ext fun i => ?_
    have h2 := L.conj_c n i
    rw [← h1 _ (L.c_mem_E i), mul_inv_cancel_right] at h2
    exact (L.c_injective h2).symm

theorem card_ker_πN : Nat.card L.πN.ker = Nat.card d.CNE := by
  have heq : L.πN.ker.map d.NE.subtype = d.CNE := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨n.2, mem_centralizer_iff.mpr ?_⟩
      exact (L.πN_eq_one_iff n).mp hn
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      exact ⟨⟨x, hx1⟩, (L.πN_eq_one_iff ⟨x, hx1⟩).mpr (mem_centralizer_iff.mp hx2), rfl⟩
  rw [← card_map_of_injective d.NE.subtype_injective, heq]

theorem πN_surjective (hq : h.IsQ3) (hF : Cat8.Q3Facts) : Function.Surjective L.πN := by
  have h1 := Subgroup.card_ker_mul_card_range L.πN
  have h2 := d.card_NE_ge hq hF
  rw [← L.card_ker_πN, ← h1] at h2
  have hpos : 0 < Nat.card L.πN.ker := Nat.card_pos
  have hge : 720 ≤ Nat.card L.πN.range :=
    Nat.le_of_mul_le_mul_left (by rw [mul_comm]; exact h2) hpos
  have hle : Nat.card L.πN.range ≤ 720 := by
    rw [← Eight.card_perm_six]
    exact card_le_card_group _
  have heq : L.πN.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [Eight.card_perm_six]; omega)
  exact MonoidHom.range_eq_top.mp heq

theorem prod_eq_one (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    L.c 0 * L.c 1 * L.c 2 * L.c 3 * L.c 4 * L.c 5 = 1 := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hOut := hF.out
  have hpair : ∀ i j, L.c i * L.c j ∈ d.E0 := fun i j =>
    d.mul_mem_E0_of_not_mem (L.c_mem_E i) (L.c_mem_E j) (L.c_not_mem_E0 i)
      (L.c_not_mem_E0 j)
  have hp0 : L.c 0 * L.c 1 * L.c 2 * L.c 3 * L.c 4 * L.c 5 ∈ d.E0 := by
    rw [show L.c 0 * L.c 1 * L.c 2 * L.c 3 * L.c 4 * L.c 5 =
      (L.c 0 * L.c 1) * (L.c 2 * L.c 3) * (L.c 4 * L.c 5) by group]
    exact mul_mem (mul_mem (hpair 0 1) (hpair 2 3)) (hpair 4 5)
  have hlist : (List.ofFn L.c).prod = L.c 0 * L.c 1 * L.c 2 * L.c 3 * L.c 4 * L.c 5 := by
    simp [List.ofFn_succ, mul_assoc]
  have hfixN : ∀ (n : X) (hn : n ∈ d.NE), n * (L.c 0 * L.c 1 * L.c 2 * L.c 3 * L.c 4 * L.c 5) *
      n⁻¹ = L.c 0 * L.c 1 * L.c 2 * L.c 3 * L.c 4 * L.c 5 := by
    intro n hn
    rw [← hlist]
    have h1 : n * (List.ofFn L.c).prod * n⁻¹ = (List.ofFn (L.c ∘ L.πN ⟨n, hn⟩)).prod := by
      have h2 := map_list_prod (MulAut.conj n).toMonoidHom (List.ofFn L.c)
      rw [List.map_ofFn] at h2
      have h3 : ((MulAut.conj n).toMonoidHom : X → X) ∘ L.c = L.c ∘ L.πN ⟨n, hn⟩ := by
        funext i
        exact L.conj_c ⟨n, hn⟩ i
      rw [h3] at h2
      exact h2
    rw [h1]
    refine List.Perm.prod_eq' (Equiv.Perm.ofFn_comp_perm _ _) ?_
    exact List.pairwise_ofFn.mpr fun i j _ =>
      d.E_comm hCF1 hCF2 (L.c_mem_E _) (L.c_mem_E _)
  have hfix : ∀ y ∈ d.NE0hat, y⁻¹ * d.rh _ (d.E0_le_RM hp0) * y = d.rh _ (d.E0_le_RM hp0) := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := d.exists_lift_NE0hat hq hCF1 hCF2 hOut hy
    refine (d.conj_eq_iff hCF1 hCF2 hm hp0 hp0).mp ?_
    have := hfixN m⁻¹ (inv_mem (d.NME0_le_NE hm))
    rwa [inv_inv] at this
  have h1 := d.eq_one_of_fixed (d.rh_mem_E0hat hp0) hfix
  exact d.rho_inj hCF1 hCF2 (d.E0_le_RM hp0) (one_mem _) (h1.trans d.rh_one.symm)

theorem c_five (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    L.c 5 = L.c 0 * L.c 1 * L.c 2 * L.c 3 * L.c 4 := by
  have h1 := L.prod_eq_one hq hF
  rw [eq_inv_of_mul_eq_one_right h1]
  have hmem : L.c 0 * L.c 1 * L.c 2 * L.c 3 * L.c 4 ∈ d.E :=
    mul_mem (mul_mem (mul_mem (mul_mem (L.c_mem_E 0) (L.c_mem_E 1)) (L.c_mem_E 2))
      (L.c_mem_E 3)) (L.c_mem_E 4)
  exact inv_eq_of_mul_eq_one_right (d.E_sq hF.simple hF.inner hmem)

theorem normalizer_Eof : normalizer ((Eight.Eof L.c : Subgroup X) : Set X) = d.NE := by
  rw [L.Eof_eq]

@[expose] noncomputable def base (hq : h.IsQ3) (hF : Cat8.Q3Facts) : Eight.E32Base X where
  c := L.c
  c_sq i := d.E_sq hF.simple hF.inner (L.c_mem_E i)
  c_comm i j := d.E_comm hF.simple hF.inner (L.c_mem_E i) (L.c_mem_E j)
  c_five := L.c_five hq hF
  card_E := by rw [L.Eof_eq]; exact d.card_E hF.simple hF.inner
  π := L.πN.comp (inclusion (le_of_eq L.normalizer_Eof))
  π_conj n i := L.conj_c (inclusion (le_of_eq L.normalizer_Eof) n) i

@[expose] def relabel (τ : Equiv.Perm (Fin 6)) : d.LClass :=
  { L with ι := τ.trans L.ι }

theorem relabel_c (τ : Equiv.Perm (Fin 6)) (i : Fin 6) : (L.relabel τ).c i = L.c (τ i) := rfl

theorem relabel_πN (τ : Equiv.Perm (Fin 6)) (n : ↥d.NE) :
    (L.relabel τ).πN n = τ⁻¹ * L.πN n * τ := by
  refine Equiv.ext fun i => (L.relabel τ).c_injective ?_
  rw [← (L.relabel τ).conj_c]
  simp only [relabel_c, L.conj_c, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
    Equiv.apply_symm_apply]

end LClass

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
