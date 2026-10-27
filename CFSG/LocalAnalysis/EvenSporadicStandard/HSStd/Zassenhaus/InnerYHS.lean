module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerYCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONanProps
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique

theorem pgl29_center_trivial (z : ↥A6Models.pgl29) (hz : ∀ g : ↥A6Models.pgl29, g * z = z * g) :
    z = 1 := by
  have hA : A6Models.tAdd ∈ A6Models.pgl29 :=
    Out21.A6.psl29_le_pgl29 Out21.A6.tAdd_mem_psl29
  have hI : A6Models.tInv ∈ A6Models.pgl29 :=
    Out21.A6.psl29_le_pgl29 Out21.A6.tInv_mem_psl29
  have hM : A6Models.tMul ∈ A6Models.pgl29 := Out21.A6.tMul_mem_pgl29
  have key : ∀ g ∈ A6Models.pgl29, ∀ x : Fin 10, (z : Equiv.Perm (Fin 10)) (g x) =
      g ((z : Equiv.Perm (Fin 10)) x) := by
    intro g hg x
    have := congrArg (fun p : ↥A6Models.pgl29 => (p : Equiv.Perm (Fin 10)) x) (hz ⟨g, hg⟩)
    simpa using this.symm
  have hs2 : A6Models.tInv * A6Models.tAdd * A6Models.tInv ∈ A6Models.pgl29 :=
    mul_mem (mul_mem hI hA) hI
  have h0 : (z : Equiv.Perm (Fin 10)) 0 = 0 := by
    have e1 := key _ hM 0
    have e2 := key _ hs2 0
    have c1 : A6Models.tMul 0 = 0 := by decide
    have c2 : (A6Models.tInv * A6Models.tAdd * A6Models.tInv) 0 = 0 := by decide
    rw [c1] at e1
    rw [c2] at e2
    have d1 : ∀ j : Fin 10, j = A6Models.tMul j → j = 0 ∨ j = 9 := by decide
    have d2 : ∀ j : Fin 10, j = (A6Models.tInv * A6Models.tAdd * A6Models.tInv) j → j ≠ 9 := by
      decide
    rcases d1 _ e1 with h | h
    · exact h
    · exact absurd h (d2 _ e2)
  have hw : ∀ i : Fin 10, ∃ w ∈ A6Models.pgl29, w 0 = i := by
    have hM2 := mul_mem hM hM
    have hM3 := mul_mem hM2 hM
    have hM4 := mul_mem hM3 hM
    have hM5 := mul_mem hM4 hM
    have hM6 := mul_mem hM5 hM
    have hM7 := mul_mem hM6 hM
    have hA2 := mul_mem hA hA
    have l : ∀ i : Fin 10, ∃ w ∈ [(1 : Equiv.Perm (Fin 10)), A6Models.tAdd,
        A6Models.tAdd * A6Models.tAdd, A6Models.tMul * A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul *
          A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul *
          A6Models.tMul * A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul *
          A6Models.tMul * A6Models.tMul * A6Models.tAdd, A6Models.tInv], w 0 = i := by decide
    intro i
    obtain ⟨w, hw, hwi⟩ := l i
    refine ⟨w, ?_, hwi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hA
    · exact hA2
    · exact mul_mem hM hA
    · exact mul_mem hM2 hA
    · exact mul_mem hM3 hA
    · exact mul_mem hM5 hA
    · exact mul_mem hM6 hA
    · exact mul_mem hM7 hA
    · exact hI
  apply Subtype.ext
  refine Equiv.ext fun i => ?_
  obtain ⟨w, hwm, rfl⟩ := hw i
  have := key w hwm 0
  rw [h0] at this
  simpa using this

namespace InnerD8ConfigC

section KGroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} (c : InnerD8ConfigC L t)

theorem isKGroupCat_Yq (hStd : StdHyp G L) : CFSG.SectionRank.IsKGroupCat c.Yq := by
  have hu₁Zc : c.u₁ ∈ c.Zc := mem_sup_right (mem_zpowers _)
  have hJle : c.Jc ≤ centralizer ({c.u₁} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.2 hu₁Zc)
  exact ((hStd.isKGroupCat_centralizer_of_orderOf (n := 2) le_rfl c.u₁_ord).of_injective
    (Subgroup.inclusion hJle) (Subgroup.inclusion_injective hJle)).quotient _

end KGroup

section Config

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

variable (c : InnerD8ConfigC L t)

theorem Zc_le_centralizer_u : c.Zc ≤ centralizer ({c.u} : Set G) := by
  refine sup_le ?_ ?_
  · exact (inf_le_left : c.X3 ≤ c.L₁).trans c.pair.K_le
  · exact zpowers_le.2 c.u₁_mem.1.1

theorem u_mem_Jc : c.u ∈ c.Jc := by
  refine mem_centralizer_iff.2 fun h hh => ?_
  exact mem_centralizer_singleton_iff.1 (c.Zc_le_centralizer_u hh)

theorem u_not_mem_Zc : c.u ∉ c.Zc := by
  intro h
  have hu2 : c.u * c.u = 1 := by
    have := pow_orderOf_eq_one c.u
    rwa [c.u_ord, pow_two] at this
  have hu1 : c.u ≠ 1 := by
    intro h1
    have := c.u_ord
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨a, ha, w, hw, hauw⟩ := c.mem_Zc_iff.1 h
  have ha3 := c.X_cube ha
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self c.u₁_sq hw with rfl | rfl
  · rw [mul_one] at hauw
    subst hauw
    apply hu1
    have : c.u ^ 3 = c.u := by rw [pow_succ, pow_two, hu2, one_mul]
    rw [← this, ha3]
  · have hc : Commute a c.u₁ := (c.cm_X_u₁.comm ha (mem_zpowers _) : a * c.u₁ = c.u₁ * a)
    have h2 : a ^ 2 = 1 := by
      have := hc.mul_pow 2
      rw [← hauw, pow_two c.u, hu2, pow_two c.u₁, c.u₁_sq, mul_one] at this
      exact this.symm
    have ha1 : a = 1 := by
      have : a ^ 3 = a := by rw [pow_succ, h2, one_mul]
      rw [← this, ha3]
    rw [ha1, one_mul] at hauw
    have h3 := c.u₁_conj
    rw [← hauw, hu2] at h3
    exact hu1 (by simpa using h3)

noncomputable def ubar : c.Yq := c.mkY ⟨c.u, c.u_mem_Jc⟩

theorem orderOf_ubar : orderOf c.ubar = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [ubar, ← map_pow, ← map_one c.mkY]
    congr 1
    apply Subtype.ext
    have := pow_orderOf_eq_one c.u
    rwa [c.u_ord] at this
  · rw [ubar]
    intro h
    exact c.u_not_mem_Zc ((c.mkY_eq_one_iff _).1 h)

theorem conjSub_le_centralizer_u : conjSub t c.L₁ ≤ centralizer ({c.u} : Set G) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_conjSub.1 hb
  exact mul_mem (mul_mem c.t_mem_P (c.pair.K_le ha)) (inv_mem c.t_mem_P)

theorem cm_conjL₁_Zc : Cm (conjSub t c.L₁) c.Zc := by
  have h1 : Cm (conjSub t c.L₁) c.L₁ := fun b hb =>
    mem_centralizer_iff.2 fun a ha => (c.comm_L₁_conj ha hb).eq
  have h2 : Cm (conjSub t c.L₁) (zpowers c.u₁) :=
    (cm_zpowers_left fun b hb => (c.u₁_comm_L₁t hb).symm).symm
  exact Cm.sup_right (h1.mono le_rfl inf_le_left) h2

theorem cm_zpowers_g_Zc {g : G} (hgu₁ : g * c.u₁ = c.u₁ * g)
    (hgL₁ : ∀ l ∈ c.L₁, g * l = l * g) : Cm (zpowers g) c.Zc :=
  Cm.sup_right (cm_zpowers_left fun b hb => hgL₁ b hb.1) (cm_zpowers_zpowers hgu₁)

theorem isSporadic_Yq (hρ : c.rho.range = ⊤) (hψ : c.PsiCrit)
    (hKY : CFSG.SectionRank.IsKGroupCat c.Yq) (hON : ONan77S5) (hIn : ONanInspection)
    (g : G) (hg : g * g = 1) (hgu : g * c.u = c.u * g) (hgu₁ : g * c.u₁ = c.u₁ * g)
    (hgL₁ : ∀ l ∈ c.L₁, g * l = l * g)
    (hgH : Nonempty (↥(conjSub t c.L₁ ⊔ zpowers g) ≃*
      ↥CFSG.QuasithinUnique.A6Models.pgl29)) :
    IsSporadic c.Yq .HS := by
  have _ := hg
  have hcent : ∀ a ∈ c.Pbar, a ≠ 1 → Nonempty (↥(centralizer ({a} : Set c.Yq)) ≃*
      Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) :=
    fun a ha ha1 => c.centralizer_equiv_of_mem_Pbar hρ hψ ha ha1
  obtain ⟨N, hN, hNc, hNL⟩ := hON c.Yq hKY (c.eq_bot_of_normal hρ hψ) c.Pbar c.Pbar_comm
    c.Pbar_cube c.card_Pbar hcent
  refine hIn c.Yq N hN hNc hNL c.Pbar c.Pbar_comm c.Pbar_cube c.card_Pbar ?_ ?_
  · intro a ha ha1
    obtain ⟨e⟩ := hcent a ha ha1
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · obtain ⟨e⟩ := hgH
    have hcmH : Cm (conjSub t c.L₁ ⊔ zpowers g) c.Zc :=
      Cm.sup_left c.cm_conjL₁_Zc (c.cm_zpowers_g_Zc hgu₁ hgL₁)
    have hHJ : conjSub t c.L₁ ⊔ zpowers g ≤ c.Jc := hcmH
    let Hs : Subgroup ↥c.Jc := (conjSub t c.L₁ ⊔ zpowers g).subgroupOf c.Jc
    let φ : ↥Hs →* c.Yq := c.mkY.comp Hs.subtype
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨⟨h, hJ⟩, hH⟩ hφ1
      have hZ : h ∈ c.Zc := (c.mkY_eq_one_iff ⟨h, hJ⟩).1 hφ1
      have hH' : h ∈ conjSub t c.L₁ ⊔ zpowers g := hH
      have hzc : ∀ k : ↥(conjSub t c.L₁ ⊔ zpowers g), k * ⟨h, hH'⟩ = ⟨h, hH'⟩ * k := by
        intro k
        apply Subtype.ext
        exact (mem_centralizer_iff.1 (hHJ k.2) h hZ).symm
      have hez : e ⟨h, hH'⟩ = 1 := by
        apply pgl29_center_trivial
        intro q
        obtain ⟨k, rfl⟩ := e.surjective q
        rw [← map_mul, ← map_mul, hzc k]
      have h1 : (⟨h, hH'⟩ : ↥(conjSub t c.L₁ ⊔ zpowers g)) = 1 := by
        apply e.injective
        rw [hez, map_one]
      have h2 : h = 1 := congrArg Subtype.val h1
      subst h2
      rfl
    refine ⟨c.ubar, c.orderOf_ubar, φ.range, ?_, ?_⟩
    · rintro y ⟨⟨⟨h, hJ⟩, hH⟩, rfl⟩
      have hH' : h ∈ conjSub t c.L₁ ⊔ zpowers g := hH
      have hhu : h * c.u = c.u * h := by
        have : h ∈ centralizer ({c.u} : Set G) :=
          (sup_le c.conjSub_le_centralizer_u
            (zpowers_le.2 (mem_centralizer_singleton_iff.2 hgu))) hH'
        exact mem_centralizer_singleton_iff.1 this
      rw [mem_centralizer_singleton_iff]
      show c.mkY ⟨h, hJ⟩ * c.mkY ⟨c.u, c.u_mem_Jc⟩ = c.mkY ⟨c.u, c.u_mem_Jc⟩ * c.mkY ⟨h, hJ⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hhu
    · exact ⟨((MonoidHom.ofInjective hφ).symm.trans
        (subgroupOfEquivOfLe hHJ)).trans e⟩

end Config

end InnerD8ConfigC

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
