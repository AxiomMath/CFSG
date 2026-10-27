module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdArith
public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.SuzOddCore.SmallAut

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CFSG.Sporadic.SmallOddCore

theorem pow_dvd_card_inf_centralizer {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {X : Type*} [Group X] [Finite X]
    (S : Subgroup X) [S.Normal] (θ : S ≃* P) (hC : centralizer (S : Set X) = ⊥) (t : X)
    {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ^ n ∣ Nat.card (centralizer ({t} : Set X))) :
    q ^ n ∣ Nat.card ↥(P ⊓ centralizer ({h.embed S θ t} : Set M)) := by
  have : Fact q.Prime := ⟨hq⟩
  have hinj := h.embed_injective S θ hC
  have hX : Nat.card X ≤ 2 * Nat.card S := by
    have h1 : Nat.card X = Nat.card (h.embed S θ).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have h2 : (h.embed S θ).range ≤ R := by
      rintro _ ⟨x, rfl⟩
      exact h.embed_mem S θ x
    rw [h1, Nat.card_congr θ.toEquiv]
    exact (Subgroup.card_le_of_le h2).trans hidx
  set C := centralizer ({t} : Set X)
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime q hdvd
  have hQ' : Nat.card (Q.map C.subtype) = q ^ n := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hQ]
  have hQodd : Odd (Nat.card (Q.map C.subtype)) := by
    rw [hQ']
    exact (hq.odd_of_ne_two hq2).pow
  have hQS : Q.map C.subtype ≤ S := odd_card_map_le_of_index_le_two S hX hQodd
  have hQC : Q.map C.subtype ≤ C := map_subtype_le _
  have hdvd' : q ^ n ∣ Nat.card ↥(S ⊓ C) := hQ' ▸ Subgroup.card_dvd_of_le (le_inf hQS hQC)
  rwa [Nat.card_congr (h.centralizerEquiv S θ hC t).toEquiv] at hdvd'

theorem card_inf_centralizer_conj_normalizing {M : Type*} [Group M] {A : Subgroup M} {g : M}
    (hg : ∀ y ∈ A, g * y * g⁻¹ ∈ A) (hg' : ∀ y ∈ A, g⁻¹ * y * g ∈ A) (v : M) :
    Nat.card ↥(A ⊓ centralizer ({g * v * g⁻¹} : Set M)) =
      Nat.card ↥(A ⊓ centralizer ({v} : Set M)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y.1 * g, ?_⟩
      invFun := fun y => ⟨g * y.1 * g⁻¹, ?_⟩
      left_inv := fun y => by apply Subtype.ext; show g * (g⁻¹ * y.1 * g) * g⁻¹ = y.1; group
      right_inv := fun y => by apply Subtype.ext; show g⁻¹ * (g * y.1 * g⁻¹) * g = y.1; group }
  · obtain ⟨y, hyA, hyv⟩ := y
    have hyv' := mem_centralizer_singleton_iff.mp hyv
    refine ⟨hg' y hyA, mem_centralizer_singleton_iff.mpr ?_⟩
    calc g⁻¹ * y * g * v = g⁻¹ * (y * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * y) * g := by rw [hyv']
      _ = v * (g⁻¹ * y * g) := by group
  · obtain ⟨y, hyA, hyv⟩ := y
    have hyv' := mem_centralizer_singleton_iff.mp hyv
    refine ⟨hg y hyA, mem_centralizer_singleton_iff.mpr ?_⟩
    calc g * y * g⁻¹ * (g * v * g⁻¹) = g * (y * v) * g⁻¹ := by group
      _ = g * (v * y) * g⁻¹ := by rw [hyv']
      _ = (g * v * g⁻¹) * (g * y * g⁻¹) := by group

theorem card_bar_of_lieModel {X : Type} [Group X] {p f Q : ℕ} (hQ : Odd Q) (hpf : p ^ f = Q ^ 2)
    (hK : Blueprint.LieModel X .PSL 2 p f) : Nat.card X = ordL2sq Q := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := OddClassSelector.statedClassicalModel_of_lieModel hK
    (by simp [Blueprint.chevalleyExceptionalTags]) (by simp [Blueprint.reeTitsTags]) (by decide)
  rw [Nat.card_congr e.toEquiv]
  exact card_PSL2_sq hQ (by rw [hF, hpf])

section He

open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

theorem heAutModelStd :
    AutModel heP heAutGroup where
  le := heP_le_heAutGroup
  conj_mem := fun x hx p hp => by
    have := (heConjR ⟨x, hx⟩ ⟨p, hp⟩).2
    rwa [heConjR_apply] at this
  surj := fun α => by
    obtain ⟨t, ht⟩ := ctbh_full_automorphism_permutation_model.1.2 α
    refine ⟨t, t.2, fun p => ?_⟩
    rw [← ht, heConjR_apply]
    rfl
  inj := fun x hx hc => by
    have h1 : heConjR ⟨x, hx⟩ = heConjR 1 := by
      refine MulEquiv.ext fun m => Subtype.ext ?_
      rw [heConjR_apply, map_one, MulAut.one_apply]
      show x * (m : Equiv.Perm (Fin 8330)) * x⁻¹ = m
      rw [hc m m.2]
      group
    exact congrArg Subtype.val (heConjR_injective h1)

theorem card_heP_inf_centralizer_of_involution
    {x : Equiv.Perm (Fin 8330)} (hxR : x ∈ heAutGroup)
    (hx2 : orderOf x = 2) :
    Nat.card ↥(heP ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 8330)))) = 161280 ∨
      Nat.card ↥(heP ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 8330)))) = 21504 ∨
      Nat.card ↥(heP ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 8330)))) = 15120 := by
  by_cases hxP : x ∈ heP
  · rcases involution_conj_cases hxP hx2 with ⟨g, hg, hgx⟩ | ⟨g, hg, hgx⟩
    · left
      rw [hgx, Nat.card_congr (infCentralizerConjEquiv hg _).toEquiv]
      exact card_heP_cent0
    · right; left
      rw [hgx, Nat.card_congr (infCentralizerConjEquiv hg _).toEquiv]
      exact card_heP_cent1
  · right; right
    obtain ⟨-, hcl, hu⟩ := ctbh_outer_involution_class_exhaustion
    have hxI : x ∈ {x : Equiv.Perm (Fin 8330) | x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2} :=
      ⟨hxR, hxP, hx2⟩
    rw [hcl] at hxI
    obtain ⟨g, hg, hgx⟩ := hxI
    rw [hgx, Nat.card_congr (infCentralizerConjEquiv hg _).toEquiv]
    exact hu

theorem heL2Input :
    HeL2Input := by
  intro H _ _ _ hC hs b hb K hKC _ hK
  classical
  have hKbar : Nat.card (K ⧸ pPrimeCore 2 K) = 58800 := by
    rw [card_bar_of_lieModel (Q := 7) (by decide) (by norm_num) hK]
    rfl
  have h25 : 5 ^ 2 ∣ Nat.card (centralizer ({b} : Set H)) := by
    have h1 : 5 ^ 2 ∣ Nat.card K :=
      (show 5 ^ 2 ∣ 58800 by norm_num).trans (hKbar ▸ Subgroup.card_quotient_dvd_card _)
    exact h1.trans (Subgroup.card_dvd_of_le hKC)
  have : (generalizedFitting H).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  let θ : ↥(generalizedFitting H) ≃* heP := (Classical.choice hs).trans heEquivP
  have hM := heAutModelStd
  have hidx : Nat.card heAutGroup ≤ 2 * Nat.card heP := by rw [card_heAutGroup, card_heP]
  have hdvd := pow_dvd_card_inf_centralizer hM hidx _ θ hC b Nat.prime_five (by norm_num) h25
  have hx2 : orderOf (hM.embed (generalizedFitting H) θ b) = 2 := by
    rw [orderOf_injective _ (hM.embed_injective _ θ hC) b, hb]
  have hxR := hM.embed_mem (generalizedFitting H) θ b
  generalize hM.embed (generalizedFitting H) θ b = x at hdvd hx2 hxR
  rcases card_heP_inf_centralizer_of_involution hxR hx2 with h | h | h <;>
    rw [h] at hdvd <;> exact absurd hdvd (by decide)

end He

section Suz

open CFSG.Sporadic.SuzOddCore

theorem suzAutModelStd :
    AutModel suzM suzT where
  le := suzM_le_suzT
  conj_mem := fun _ hx _ hp => suzT_conj_mem_suzM hx hp
  surj := fun α => by
    obtain ⟨t, ht⟩ := suzConjT_bijective.2 α
    refine ⟨t, t.2, fun p => ?_⟩
    rw [← ht, suzConjT_apply]
  inj := fun x hx hc => by
    have h1 : suzConjT ⟨x, hx⟩ = suzConjT 1 := by
      refine MulEquiv.ext fun m => Subtype.ext ?_
      rw [suzConjT_apply, map_one, MulAut.one_apply]
      show x * (m : Equiv.Perm (Fin 1782)) * x⁻¹ = m
      rw [hc m m.2]
      group
    exact congrArg Subtype.val (suzConjT_injective h1)

theorem card_suzM_inf_centralizer_of_involution
    {x : Equiv.Perm (Fin 1782)} (hxT : x ∈ suzT)
    (hx2 : orderOf x = 2) : ∃ i < 4,
      Nat.card ↥(suzM ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1782)))) =
        invInnerOrders.getD i 0 := by
  obtain ⟨i, ⟨hi, c, hc, hcx⟩, -⟩ := suzT_involution_class hxT hx2
  refine ⟨i, hi, ?_⟩
  rw [← hcx, card_inf_centralizer_conj_normalizing (fun m hm => suzT_conj_mem_suzM hc hm)
    (fun m hm => by simpa only [inv_inv] using suzT_conj_mem_suzM (suzT.inv_mem hc) hm),
    inf_comm, ← card_invE hi, invE_eq_centM hi]
  rfl

theorem suzL2Input :
    SuzL2Input := by
  intro H _ _ _ hC hs b hb K hKC _ hK
  classical
  have hKbar : Nat.card (K ⧸ pPrimeCore 2 K) = 7800 := by
    rw [card_bar_of_lieModel (Q := 5) (by decide) (by norm_num) hK]
    rfl
  have h13 : 13 ^ 1 ∣ Nat.card (centralizer ({b} : Set H)) := by
    have h1 : 13 ^ 1 ∣ Nat.card K :=
      (show 13 ^ 1 ∣ 7800 by norm_num).trans (hKbar ▸ Subgroup.card_quotient_dvd_card _)
    exact h1.trans (Subgroup.card_dvd_of_le hKC)
  have : (generalizedFitting H).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  let θ : ↥(generalizedFitting H) ≃* suzM := (Classical.choice hs).trans suzEquivM
  have hM := suzAutModelStd
  have hidx : Nat.card suzT ≤ 2 * Nat.card suzM := by rw [suzT_card, suzM_card_chain]
  have hdvd := pow_dvd_card_inf_centralizer hM hidx _ θ hC b (by norm_num) (by norm_num) h13
  have hx2 : orderOf (hM.embed (generalizedFitting H) θ b) = 2 := by
    rw [orderOf_injective _ (hM.embed_injective _ θ hC) b, hb]
  have hxT := hM.embed_mem (generalizedFitting H) θ b
  generalize hM.embed (generalizedFitting H) θ b = x at hdvd hx2 hxT
  obtain ⟨i, hi, h⟩ := card_suzM_inf_centralizer_of_involution hxT hx2
  rw [h] at hdvd
  interval_cases i <;> exact absurd hdvd (by decide)

end Suz

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
