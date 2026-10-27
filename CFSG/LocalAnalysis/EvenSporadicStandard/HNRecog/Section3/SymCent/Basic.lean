module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped Nat

theorem symCent_mulEquiv_of_isConj {M : Type} [Group M] {g h : M} (hgh : IsConj g h) :
    Nonempty (↥(Subgroup.centralizer ({g} : Set M)) ≃* ↥(Subgroup.centralizer ({h} : Set M))) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hgh
  exact ⟨centralizerMulEquiv (MulAut.conj c) (by simpa using hc)⟩

theorem symCent_mulEquiv_of_injective {X M : Type} [Group X] [Group M] [Finite M] (f : X →* M)
    (hf : Function.Injective f) {g : M} (hfg : ∀ x, f x ∈ Subgroup.centralizer ({g} : Set M))
    (hcard : Nat.card X = Nat.card ↥(Subgroup.centralizer ({g} : Set M))) :
    Nonempty (↥(Subgroup.centralizer ({g} : Set M)) ≃* X) := by
  let C : Subgroup M := Subgroup.centralizer ({g} : Set M)
  haveI : Nonempty C := ⟨⟨1, C.one_mem⟩⟩
  have hCne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hCne)
  let f' : X →* C := f.codRestrict C hfg
  have hf' : Function.Injective f' := (MonoidHom.injective_codRestrict f C hfg).mpr hf
  have hbij : Function.Bijective f' :=
    hf'.bijective_of_nat_card_le (le_of_eq hcard.symm)
  exact ⟨(MulEquiv.ofBijective f' hbij).symm⟩

private def symCentFinLastEquiv (n k : ℕ) :
    Fin k ≃ {i : Fin (n + k) // n ≤ i.1} where
  toFun j := ⟨Fin.natAdd n j, Fin.le_coe_natAdd n j⟩
  invFun i := ⟨i.1.1 - n, by have h1 := i.1.2; have h2 := i.2; omega⟩
  left_inv j := by
    ext
    simp only [Fin.val_natAdd]
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_mk]
    have h := i.2
    omega

private def symCentFinFirstEquiv (n k : ℕ) :
    Fin n ≃ {i : Fin (n + k) // i.1 < n} where
  toFun j := ⟨Fin.castAdd k j, by simpa using j.2⟩
  invFun i := ⟨i.1.1, i.2⟩
  left_inv j := by ext; rfl
  right_inv i := by apply Subtype.ext; apply Fin.ext; rfl

theorem symCent_extend (n k : ℕ) {τ : Sym k} (hτ : τ.cycleType.sum = k) {σ : Sym (n + k)}
    (hσ : σ.cycleType = τ.cycleType) :
    Nonempty (↥(Subgroup.centralizer ({σ} : Set (Sym (n + k)))) ≃*
      ↥(Subgroup.centralizer ({τ} : Set (Sym k))) × Sym n) := by
  classical
  let eL := symCentFinLastEquiv n k
  let eF := symCentFinFirstEquiv n k
  let fτ : Sym k →* Sym (n + k) := Equiv.Perm.extendDomainHom eL
  let fF : Sym n →* Sym (n + k) := Equiv.Perm.extendDomainHom eF
  let τ' : Sym (n + k) := Equiv.Perm.extendDomain τ eL
  have hτ'cyc : τ'.cycleType = τ.cycleType := Equiv.Perm.cycleType_extendDomain eL
  have hconj : IsConj σ τ' := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq]
    exact hσ.trans hτ'cyc.symm
  let Cτ : Subgroup (Sym k) := Subgroup.centralizer ({τ} : Set (Sym k))
  let Cτ' : Subgroup (Sym (n + k)) := Subgroup.centralizer ({τ'} : Set (Sym (n + k)))
  have hdisj : ∀ (c : Sym k) (h : Sym n), Equiv.Perm.Disjoint (fτ c) (fF h) := by
    intro c h i
    by_cases hi : i.1 < n
    · left
      exact Equiv.Perm.extendDomain_apply_not_subtype c eL (Nat.not_le.mpr hi)
    · right
      exact Equiv.Perm.extendDomain_apply_not_subtype h eF hi
  let F : ↥Cτ × Sym n →* Sym (n + k) :=
    (fτ.comp (Subgroup.subtype Cτ)).noncommCoprod fF
      (fun c h => (hdisj (c : Sym k) h).commute)
  have hF : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : fτ (a.1 : Sym k) * fF a.2 = 1 := ha
    obtain ⟨h1, h2⟩ := (hdisj (a.1 : Sym k) a.2).mul_eq_one_iff.mp ha'
    exact Prod.ext (Subtype.ext (Equiv.Perm.extendDomain_eq_one_iff.mp h1))
      (Equiv.Perm.extendDomain_eq_one_iff.mp h2)
  have hfg : ∀ x : ↥Cτ × Sym n, F x ∈ Cτ' := by
    rintro ⟨c, h⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (fτ (c : Sym k) * fF h) * τ' = τ' * (fτ (c : Sym k) * fF h)
    have hc : Commute (fτ (c : Sym k)) (fτ τ) := by
      show fτ (c : Sym k) * fτ τ = fτ τ * fτ (c : Sym k)
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp c.2]
    have hh : Commute (fF h) (fτ τ) := (hdisj τ h).commute.symm
    exact (hc.mul_left hh).eq
  have hcardτ : Nat.card ↥Cτ =
      τ.cycleType.prod * ∏ m ∈ τ.cycleType.toFinset, (τ.cycleType.count m)! := by
    have h := Equiv.Perm.nat_card_centralizer (α := Fin k) τ
    simp only [Fintype.card_fin] at h
    change Nat.card (Subgroup.centralizer ({τ} : Set (Sym k))) =
      τ.cycleType.prod * ∏ m ∈ τ.cycleType.toFinset, (τ.cycleType.count m)!
    rw [h, hτ, Nat.sub_self, Nat.factorial_zero, one_mul]
  have hcardτ' : Nat.card ↥Cτ' =
      n ! * (τ.cycleType.prod * ∏ m ∈ τ.cycleType.toFinset, (τ.cycleType.count m)!) := by
    have h := Equiv.Perm.nat_card_centralizer (α := Fin (n + k)) τ'
    simp only [Fintype.card_fin] at h
    change Nat.card (Subgroup.centralizer ({τ'} : Set (Sym (n + k)))) =
      n ! * (τ.cycleType.prod * ∏ m ∈ τ.cycleType.toFinset, (τ.cycleType.count m)!)
    rw [h, hτ'cyc, hτ, Nat.add_sub_cancel]
    ring
  have hcardPerm : Nat.card (Sym n) = n ! := by
    rw [Nat.card_perm, Nat.card_fin]
  have hcard : Nat.card (↥Cτ × Sym n) = Nat.card ↥Cτ' := by
    rw [Nat.card_prod, hcardPerm, hcardτ, hcardτ']
    ring
  obtain ⟨e1⟩ := symCent_mulEquiv_of_isConj hconj
  obtain ⟨e2⟩ := symCent_mulEquiv_of_injective F hF hfg hcard
  exact ⟨e1.trans e2⟩

theorem symCent_prod {n : ℕ} (ε : Z 2) (σ : Sym n) :
    Nonempty (↥(Subgroup.centralizer ({((ε, σ) : Z 2 × Sym n)} : Set (Z 2 × Sym n))) ≃*
      Z 2 × ↥(Subgroup.centralizer ({σ} : Set (Sym n)))) := by
  refine ⟨{
    toFun := fun x => (x.1.1, ⟨x.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩)
    invFun := fun y => ⟨(y.1, (y.2 : Sym n)), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    left_inv := fun x => Subtype.ext (Prod.ext rfl rfl)
    right_inv := fun y => Prod.ext rfl (Subtype.ext rfl)
    map_mul' := fun x y => Prod.ext rfl (Subtype.ext rfl) }⟩
  · exact (Prod.ext_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp x.2)).2
  · exact Prod.ext (mul_comm _ _) (Subgroup.mem_centralizer_singleton_iff.mp y.2.2)

theorem symCent_elem2 (X : Type) [Group X] :
    Nonempty ((Z 2 × (Z 2 × X)) ≃* (Elem2 2 × X)) := by
  have e : Z 2 × Z 2 ≃* Elem2 2 := {
    toFun := fun u => Multiplicative.ofAdd ![Multiplicative.toAdd u.1, Multiplicative.toAdd u.2]
    invFun := fun w => (Multiplicative.ofAdd (Multiplicative.toAdd w 0),
                        Multiplicative.ofAdd (Multiplicative.toAdd w 1))
    left_inv := by
      intro u
      ext <;> simp
    right_inv := by
      intro w
      ext i
      fin_cases i <;> simp
    map_mul' := by
      intro u v
      ext i
      fin_cases i <;> simp [toAdd_mul] }
  exact ⟨(MulEquiv.prodAssoc (M := Z 2) (N := Z 2) (P := X)).symm.trans
    (MulEquiv.prodCongr e (MulEquiv.refl X))⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
