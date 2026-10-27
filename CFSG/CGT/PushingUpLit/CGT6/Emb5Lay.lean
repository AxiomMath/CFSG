module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5CompY
public import CFSG.CGT.PushingUpLit.CGT6.Emb5FourT
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG

section Fitting

variable {X : Type*} [Group X] [Finite X]

theorem fitting_eq_pCore_sup (p : ℕ) [Fact p.Prime] :
    fittingSubgroup X = pCore p X ⊔
      (pPrimeCore p ↥(fittingSubgroup X)).map (fittingSubgroup X).subtype := by
  set F := fittingSubgroup X with hF
  apply le_antisymm
  · have h1 : (⊤ : Subgroup ↥F) ≤ pCore p ↥F ⊔ pPrimeCore p ↥F :=
      nilpotent_top_le_pCore_sup_pPrimeCore inferInstance
    have h2 : (⊤ : Subgroup ↥F).map F.subtype ≤
        (pCore p ↥F).map F.subtype ⊔ (pPrimeCore p ↥F).map F.subtype := by
      rw [← Subgroup.map_sup]
      exact Subgroup.map_mono h1
    have h4 : (pCore p ↥F).map F.subtype ≤ pCore p X :=
      map_pCore_le_pCore_of_isSubnormal' (Subgroup.Normal.isSubnormal inferInstance)
    intro x hx
    have hxm : x ∈ (⊤ : Subgroup ↥F).map F.subtype := ⟨⟨x, hx⟩, trivial, rfl⟩
    exact (sup_le_sup_right h4 _) (h2 hxm)
  · exact sup_le (pCore_le_fitting X p) (Subgroup.map_subtype_le _)

theorem odd_card_fitting (h : pCore 2 X = ⊥) : Odd (Nat.card ↥(fittingSubgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := fittingSubgroup X with hF
  have h4 : (pCore 2 ↥F).map F.subtype ≤ pCore 2 X :=
    map_pCore_le_pCore_of_isSubnormal' (Subgroup.Normal.isSubnormal inferInstance)
  have hbot : pCore 2 ↥F = ⊥ := by
    rw [h, le_bot_iff] at h4
    exact (Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective).mp h4
  have h1 : (⊤ : Subgroup ↥F) ≤ pCore 2 ↥F ⊔ pPrimeCore 2 ↥F :=
    nilpotent_top_le_pCore_sup_pPrimeCore inferInstance
  rw [hbot, bot_sup_eq] at h1
  have htop : pPrimeCore 2 ↥F = ⊤ := top_le_iff.mp h1
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥F)
  rw [htop, Subgroup.card_top] at hcop
  exact Nat.coprime_two_left.mp hcop

theorem exists_fitting_decomp (h2 : pCore 2 X = ⊥) :
    ∃ M : Subgroup X, M.Characteristic ∧ Nat.Coprime (Nat.card ↥M) 6 ∧
      fittingSubgroup X = pCore 3 X ⊔ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := fittingSubgroup X with hF
  have hFn : F.Normal := inferInstance
  have hM' : (pPrimeCore 3 ↥F).map F.subtype ≤ pPrimeCore 3 X ⊓ F := by
    refine le_inf ?_ (Subgroup.map_subtype_le _)
    have hnormal : ((pPrimeCore 3 ↥F).map F.subtype).Normal :=
      ⟨fun n hn g => conj_mem_map_of_characteristic' (X := F) (D := pPrimeCore 3 ↥F)
        ((Subgroup.normalizer_eq_top_iff.mpr hFn).symm ▸ Subgroup.mem_top g) hn⟩
    have hcop : Nat.Coprime 3 (Nat.card ↥((pPrimeCore 3 ↥F).map F.subtype)) := by
      rw [Subgroup.card_map_of_injective F.subtype_injective]
      exact pPrimeCore_coprime_card
    exact le_sSup ⟨hnormal, hcop⟩
  refine ⟨pPrimeCore 3 X ⊓ F, inferInstance, ?_, ?_⟩
  · have h3 : Nat.Coprime 3 (Nat.card ↥(pPrimeCore 3 X)) := pPrimeCore_coprime_card
    have hodd : Odd (Nat.card ↥F) := odd_card_fitting h2
    have hd1 : Nat.card ↥(pPrimeCore 3 X ⊓ F) ∣ Nat.card ↥(pPrimeCore 3 X) :=
      Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(pPrimeCore 3 X ⊓ F) ∣ Nat.card ↥F := Subgroup.card_dvd_of_le inf_le_right
    have hc3 : Nat.Coprime (Nat.card ↥(pPrimeCore 3 X ⊓ F)) 3 :=
      Nat.Coprime.coprime_dvd_left hd1 h3.symm
    have hc2 : Nat.Coprime (Nat.card ↥(pPrimeCore 3 X ⊓ F)) 2 :=
      Nat.Coprime.coprime_dvd_left hd2 (Nat.coprime_two_left.mpr hodd).symm
    exact Nat.Coprime.mul_right hc2 hc3
  · apply le_antisymm
    · calc F = pCore 3 X ⊔ (pPrimeCore 3 ↥F).map F.subtype := fitting_eq_pCore_sup 3
        _ ≤ pCore 3 X ⊔ (pPrimeCore 3 X ⊓ F) := sup_le_sup_left hM' _
    · exact sup_le (pCore_le_fitting X 3) inf_le_right

end Fitting

section Layer

variable {A Γ : Type*} [Group A] [Group Γ]

theorem isComponent_map_of_normal_range (f : A →* Γ) (hf : Function.Injective f)
    (hn : f.range.Normal) {K : Subgroup A} (hK : CFSG.IsComponent K) :
    CFSG.IsComponent (K.map f) := by
  refine ⟨isQuasisimple_of_mulEquiv (K.equivMapOfInjective f hf) hK.1, ?_⟩
  have h1 : (K.map f.rangeRestrict).IsSubnormal :=
    hK.2.map (f := f.rangeRestrict) f.rangeRestrict_surjective
  have h2 := Subgroup.IsSubnormal.trans' h1 hn.isSubnormal
  rwa [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2

theorem layer_eq_bot (f : A →* Γ) (hf : Function.Injective f) (hn : f.range.Normal)
    (hcent : ∀ L : Subgroup Γ, CFSG.IsComponent L → ∀ a : A, ∀ l ∈ L, f a * l = l * f a) :
    CFSG.layer A = ⊥ := by
  refine sSup_eq_bot.mpr fun K hK => ?_
  exfalso
  have hKc := isComponent_map_of_normal_range f hf hn hK
  obtain ⟨a, b, hab⟩ := exists_not_comm_of_isQuasisimple hK.1
  apply hab
  apply Subtype.ext
  apply hf
  have := hcent _ hKc (b : A) (f a) ⟨a, a.2, rfl⟩
  simp only [Subgroup.coe_mul, map_mul]
  exact this.symm

end Layer

end CFSG.CGT.PushingUpLit.CGT6
