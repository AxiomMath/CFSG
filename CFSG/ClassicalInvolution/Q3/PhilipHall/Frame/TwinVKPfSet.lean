module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.PairInfCenter
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217
public import CFSG.ClassicalInvolution.Q3.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open scoped MatrixGroups
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Factor

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_factor_iSup (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x ∈ H i, ∀ y ∈ H j, x * y = y * x) {n : G}
    (hn : n ∈ ⨆ i, H i) :
    ∃ f : ι → G, (∀ i, f i ∈ H i) ∧ (∀ S : Subgroup G, (∀ i, f i ∈ S) → n ∈ S) ∧
      ∀ i₀, ∃ r : G, n = f i₀ * r ∧
        ∀ y : G, (∀ j, j ≠ i₀ → ∀ x ∈ H j, y * x = x * y) → y * r = r * y := by
  have hc : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y :=
    fun i j hij x y hx hy => hcomm hij x hx y hy
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hc)] at hn
  obtain ⟨u, rfl⟩ := hn
  refine ⟨fun i => (u i : G), fun i => (u i).2, ?_, ?_⟩
  · intro S hS
    rw [Subgroup.noncommPiCoprod_apply]
    exact Finset.noncommProd_induction _ _ _ (fun x => x ∈ S) (fun a b ha hb => S.mul_mem ha hb)
      S.one_mem (fun i _ => hS i)
  · intro i₀
    rw [Subgroup.noncommPiCoprod_apply]
    refine ⟨(Finset.univ.erase i₀).noncommProd (fun i => (u i : G)) (fun a ha b hb hab =>
      hc hab _ _ (u a).2 (u b).2), ?_, ?_⟩
    · exact (Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i₀)
        (fun i => (u i : G)) _).symm
    · intro y hy
      exact (Finset.noncommProd_commute _ _ _ y (fun j hj =>
        (hy j (Finset.ne_of_mem_erase hj) _ (u j).2 : y * (u j : G) = (u j : G) * y))).eq

end Factor

section Sets

variable {G : Type} [Group G]

theorem iSup_mem_eq_iSup_subtype (V : Set (Subgroup G)) (F : Subgroup G → Subgroup G) :
    (⨆ J ∈ V, F J) = ⨆ i : V, F (i : Subgroup G) := by
  rw [iSup_subtype]

structure LiftSetData (X : Subgroup G) (z : G) (V : Set (Subgroup G)) (Λ A : Subgroup G → Subgroup G) :
    Prop where
  side : ∀ J ∈ V, Lift217Side X J (Λ J) (A J) z
  card8 : ∀ J ∈ V, Nat.card J = 8
  card24 : ∀ J ∈ V, Nat.card (Λ J) = 24
  comm : ∀ J ∈ V, ∀ J' ∈ V, J ≠ J' → ∀ x ∈ Λ J, ∀ y ∈ Λ J', x * y = y * x
  norm : ∀ J ∈ V, Λ J ≤ Subgroup.normalizer (X : Set G)

variable {X : Subgroup G} {z : G} {V : Set (Subgroup G)} {Λ A : Subgroup G → Subgroup G}

theorem LiftSetData.nonempty_equiv (h : LiftSetData X z V Λ A) {J : Subgroup G} (hJ : J ∈ V) :
    Nonempty (↥(Λ J) ≃* SL(2, ZMod 3)) :=
  nonempty_mulEquiv_sl23_of_card (h.card24 J hJ) (h.side J hJ).quotient

theorem setInfCenter [Finite V] (h : LiftSetData X z V Λ A) :
    (⨆ J ∈ V, J) ⊓ X ≤ Subgroup.zpowers z := by
  classical
  have : Fintype V := Fintype.ofFinite V
  intro n hn
  obtain ⟨hnP, hnX⟩ := Subgroup.mem_inf.mp hn
  rw [iSup_mem_eq_iSup_subtype V (fun J => J)] at hnP
  have hcJ : ∀ i j : V, i ≠ j → ∀ x ∈ (i : Subgroup G), ∀ y ∈ (j : Subgroup G), x * y = y * x :=
    fun i j hij x hx y hy => h.comm i i.2 j j.2 (fun e => hij (Subtype.ext e)) x
      ((h.side i i.2).le hx) y ((h.side j j.2).le hy)
  obtain ⟨f, hf, hS, hr⟩ := exists_factor_iSup (fun i : V => (i : Subgroup G)) hcJ hnP
  refine hS (Subgroup.zpowers z) fun i₀ => ?_
  obtain ⟨r, hnr, hrc⟩ := hr i₀
  have hside := h.side i₀ i₀.2
  obtain ⟨ψ⟩ := h.nonempty_equiv i₀.2
  have hrcent : r ∈ Subgroup.centralizer ((Λ i₀ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    refine hrc y fun j hj x hx => ?_
    exact h.comm i₀ i₀.2 j j.2 (fun e => hj (Subtype.ext e.symm)) y hy x ((h.side j j.2).le hx)
  have hP : Nat.card ((i₀ : Subgroup G).subgroupOf (Λ i₀)) = 8 := by
    rw [← h.card8 i₀ i₀.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hside.le).toEquiv
  have hcore := PairInf.pair_inf_core (L := Λ i₀) (Ls := Subgroup.centralizer ((Λ i₀ : Subgroup G) : Set G))
    (K := (i₀ : Subgroup G)) (Ks := Subgroup.centralizer ((Λ i₀ : Subgroup G) : Set G)) (X := X)
    (z := z) ψ (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy x hx)
    hside.le (fun a ha k hk => conj_mem_of_subgroupOf_normal hside.le hside.normal ha hk) le_rfl
    (fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (h.norm _ i₀.2 ha) x).mp hx)
    (fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (hside.centralizes hx) y hy).symm)
    hside.involution hP
  exact hcore (f i₀) (hf i₀) r hrcent (hnr ▸ hnX)

theorem setNormalExact [Finite V] (h : LiftSetData X z V Λ A) :
    (⨆ J ∈ V, Λ J) ⊓ X ≤ ⨆ J ∈ V, J := by
  classical
  have : Fintype V := Fintype.ofFinite V
  intro n hn
  obtain ⟨hnN, hnX⟩ := Subgroup.mem_inf.mp hn
  rw [iSup_mem_eq_iSup_subtype V Λ] at hnN
  have hcL : ∀ i j : V, i ≠ j → ∀ x ∈ Λ (i : Subgroup G), ∀ y ∈ Λ (j : Subgroup G), x * y = y * x :=
    fun i j hij x hx y hy => h.comm i i.2 j j.2 (fun e => hij (Subtype.ext e)) x hx y hy
  obtain ⟨f, hf, hS, hr⟩ := exists_factor_iSup (fun i : V => Λ (i : Subgroup G)) hcL hnN
  refine hS (⨆ J ∈ V, J) fun i₀ => ?_
  obtain ⟨r, hnr, hrc⟩ := hr i₀
  have hside := h.side i₀ i₀.2
  obtain ⟨ψ⟩ := h.nonempty_equiv i₀.2
  have hrcent : r ∈ Subgroup.centralizer ((Λ i₀ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    refine hrc y fun j hj x hx => ?_
    exact h.comm i₀ i₀.2 j j.2 (fun e => hj (Subtype.ext e.symm)) y hy x hx
  have hKP : (i₀ : Subgroup G) ≤ ⨆ J ∈ V, J := le_iSup₂_of_le (i₀ : Subgroup G) i₀.2 le_rfl
  by_cases hl : f i₀ ∈ (i₀ : Subgroup G)
  · exact hKP hl
  · exfalso
    have hzL : z ∈ Λ i₀ := hside.le hside.involution.mem
    exact one_side_false (A := Λ i₀) (B := Subgroup.centralizer ((Λ i₀ : Subgroup G) : Set G))
      (K := (i₀ : Subgroup G)) (X := X) (z := z) (n := n) (l := f i₀) (m := r)
      (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy x hx) hside.le
      (fun a ha k hk => conj_mem_of_subgroupOf_normal hside.le hside.normal ha hk)
      (hside.le.trans (h.norm _ i₀.2))
      (fun g hgX _ hgK => setInfCenter h ⟨hKP hgK, hgX⟩)
      (exact_hfin ψ hside.le (h.card8 _ i₀.2) hzL hside.involution.ne_one hside.involution.sq)
      hnX (hnr ▸ Subgroup.mul_mem_sup (hf i₀) hrcent) hnr (hf i₀) hrcent hl

theorem transport217Set [Finite G] [Finite V] {t : G} (h : LiftSetData X z V Λ A) (h1520 : Model1520 X t)
    (hCX : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (X : Set G)) (htX : t ∈ X)
    (hLN : Subgroup.centralizer ({t, z} : Set G) ≤
      Subgroup.normalizer ((⨆ J ∈ V, Λ J : Subgroup G) : Set G)) :
    ∀ J ∈ V, IsClassicalMember3 (Λ J) z := by
  intro J₀ hJ₀
  set N : Subgroup G := ⨆ J ∈ V, Λ J with hN
  have hLN' : ∀ J ∈ V, Λ J ≤ N := fun J hJ => le_iSup₂_of_le J hJ le_rfl
  have hz := (h.side J₀ hJ₀).involution
  have hKK := setInfCenter h
  have hNX : N ⊓ X ≤ Subgroup.zpowers z := (le_inf (setNormalExact h) inf_le_right).trans hKK
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp ((h.side J₀ hJ₀).centralizes hz.mem) x hx)
  have hLz : ∀ J ∈ V, Λ J ≤ Subgroup.centralizer ({z} : Set G) := fun J hJ => (h.side J hJ).le_centralizer
  have hAX : ∀ J ∈ V, A J ≤ Subgroup.centralizer (X : Set G) := by
    intro J hJ
    have hs := h.side J hJ
    exact le_centralizer_of_transport217 hz.sq ((hs.le_A.trans (hLz J hJ)).trans hCX)
      (hs.le_A.trans (hLz J hJ)) (hs.le_A.trans (hLN' J hJ)) hLN hXz hNX hs.threeGroup h1520
  have hLXc : ∀ J ∈ V, Λ J ≤ Subgroup.centralizer (X : Set G) := fun J hJ =>
    (h.side J hJ).sup_eq.le.trans (sup_le (h.side J hJ).centralizes (hAX J hJ))
  set M : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (X : Set G)
    with hM
  have hNM : N ≤ M := iSup₂_le fun J hJ => le_inf (hLz J hJ) (hLXc J hJ)
  have hMn : M ≤ Subgroup.normalizer (N : Set G) := by
    intro m hm
    apply hLN
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hm).2 x htX
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hm).1).symm
  have hNnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMn
  have hsub : IsSubnormal (Λ J₀) M := by
    have hLn : ((Λ J₀).subgroupOf N).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hLN' J₀ hJ₀)]
      refine iSup₂_le fun J hJ => ?_
      by_cases hJJ : J = J₀
      · subst hJJ; exact Subgroup.le_normalizer
      · intro y hy
        exact mem_normalizer_of_forall_commute fun x hx =>
          (h.comm J₀ hJ₀ J hJ (Ne.symm hJJ) x hx y hy)
    exact IsSubnormal.step (hLN' J₀ hJ₀) hLn (IsSubnormal.step hNM hNnorm (IsSubnormal.refl M))
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  exact ⟨hord, (h.side J₀ hJ₀).le hz.mem, isSubnormal_of_centralizer_inf hCX hsub,
    (h.side J₀ hJ₀).quotient⟩

end Sets

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
