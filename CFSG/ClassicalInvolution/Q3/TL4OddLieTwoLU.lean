module

public import CFSG.ClassicalInvolution.Q3.TL4OddLieEdge
public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge
public import CFSG.ClassicalInvolution.ModelFacts.TG3Common

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Two

theorem exists_conj_commutes_triple {K : Type} [Group K] {𝓕 : Set (Subgroup K)}
    (hsingle : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, ∃ g : K, B = conjSub g A) {A B C R₀ : Subgroup K}
    (hA : A ∈ 𝓕) (hB : B ∈ 𝓕) (hC : C ∈ 𝓕) (hR₀ : R₀ ∈ 𝓕) :
    ∃ a g h : K, R₀ = conjSub a A ∧ conjSub g R₀ = conjSub a B ∧ conjSub h R₀ = conjSub a C := by
  obtain ⟨a, rfl⟩ := hsingle A hA R₀ hR₀
  obtain ⟨b, rfl⟩ := hsingle A hA B hB
  obtain ⟨c, rfl⟩ := hsingle A hA C hC
  refine ⟨a, a * b * a⁻¹, a * c * a⁻¹, rfl, ?_, ?_⟩ <;>
    rw [← conjSub_mul, ← conjSub_mul, inv_mul_cancel_right]

theorem isUniqueInvolution_map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {R : Subgroup G} {r : G} (h : IsUniqueInvolution R r) :
    IsUniqueInvolution (R.map e.toMonoidHom) (e r) where
  mem := Subgroup.mem_map_of_mem _ h.mem
  ne_one := fun h1 => h.ne_one (e.injective (h1.trans (map_one e).symm))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    rintro _ ⟨s, hs, rfl⟩ hy
    have hss : s * s = 1 := e.injective (by rw [map_mul, ← MulEquiv.coe_toMonoidHom, hy, map_one])
    rcases h.unique s hs hss with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1]; rfl)

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem exists_two_nbrs_of_triple (hR : TypeRFam 3 Φ) {K : Type} [Group K] (ψ : K →* X)
    {𝓕 : Set (Subgroup K)} (hsingle : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, ∃ g : K, B = conjSub g A)
    {A B C : Subgroup K} (hA : A ∈ 𝓕) (hB : B ∈ 𝓕) (hC : C ∈ 𝓕) (hAB : Commutes A B)
    (hAC : Commutes A C) (hBC : Commutes B C) {L : Subgroup X} (hL : L ∈ Φ) {R₀ : Subgroup K}
    (hR₀ : R₀ ∈ 𝓕) (hLR : IsSylow2In L (R₀.map ψ)) :
    ∃ M ∈ omegaNbr Φ L, ∃ M' ∈ omegaNbr Φ L, M ≠ M' := by
  obtain ⟨a, g, h, rfl, hg, hh⟩ := exists_conj_commutes_triple hsingle hA hB hC hR₀
  have c1 : Commutes (conjSub a A) (conjSub g (conjSub a A)) := by
    rw [hg]; exact commutes_conjSub_conjSub hAB a
  have c2 : Commutes (conjSub a A) (conjSub h (conjSub a A)) := by
    rw [hh]; exact commutes_conjSub_conjSub hAC a
  have c3 : Commutes (conjSub g (conjSub a A)) (conjSub h (conjSub a A)) := by
    rw [hg, hh]; exact commutes_conjSub_conjSub hBC a
  refine ⟨_, conjSub_mem_omegaNbr_of_commutes hR ψ hL hLR c1, _,
    conjSub_mem_omegaNbr_of_commutes hR ψ hL hLR c2, fun he => ?_⟩
  have hcomm := commutes_conjSub_of_commutes ψ hLR.1 c3
  rw [he] at hcomm
  exact not_commutes_self_of_isPGroup hR.hyp (hR.hyp.conjInvariant _ _ hL)
    (hLR.2.1.map (MulAut.conj (ψ h)).toMonoidHom) hcomm

theorem exists_two_nbrs_of_sep (hR : TypeRFam 3 Φ) {K : Type} [Group K] (ψ : K →* X)
    {𝓕 : Set (Subgroup K)} (hsingle : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, ∃ g : K, B = conjSub g A)
    (hZ : ∀ R ∈ 𝓕, ∀ x ∈ R, ψ x = 1 → x = 1) {A B C D : Subgroup K} (hA : A ∈ 𝓕) (hB : B ∈ 𝓕)
    (hC : C ∈ 𝓕) (hD : D ∈ 𝓕) (hAB : Commutes A B) (hAC : Commutes A C) {b c : K}
    (hb : IsUniqueInvolution B b) (hc : IsUniqueInvolution C c) (hbcD : b * c⁻¹ ∈ D)
    (hbc1 : b * c⁻¹ ≠ 1) {L : Subgroup X} (hL : L ∈ Φ) {R₀ : Subgroup K} (hR₀ : R₀ ∈ 𝓕)
    (hLR : IsSylow2In L (R₀.map ψ)) :
    ∃ M ∈ omegaNbr Φ L, ∃ M' ∈ omegaNbr Φ L, M ≠ M' := by
  obtain ⟨a, g, h, rfl, hg, hh⟩ := exists_conj_commutes_triple hsingle hA hB hC hR₀
  have c1 : Commutes (conjSub a A) (conjSub g (conjSub a A)) := by
    rw [hg]; exact commutes_conjSub_conjSub hAB a
  have c2 : Commutes (conjSub a A) (conjSub h (conjSub a A)) := by
    rw [hh]; exact commutes_conjSub_conjSub hAC a
  refine ⟨_, conjSub_mem_omegaNbr_of_commutes hR ψ hL hLR c1, _,
    conjSub_mem_omegaNbr_of_commutes hR ψ hL hLR c2, fun he => ?_⟩
  obtain ⟨⟨z, hz⟩, -⟩ := hR.hyp.omega1 _ (hR.hyp.conjInvariant (ψ g) L hL)
  have hzB : z ∈ (conjSub a B).map ψ := by
    have h1 := conjSub_le_map_conjSub ψ hLR.1 g hz.mem
    rwa [hg] at h1
  have hzC : z ∈ (conjSub a C).map ψ := by
    have h1 := conjSub_le_map_conjSub ψ hLR.1 h (he ▸ hz.mem : z ∈ conjSub (ψ h) L)
    rwa [hh] at h1
  have hZc : ∀ {R : Subgroup K}, R ∈ 𝓕 → ∀ y ∈ conjSub a R, ψ y = 1 → y = 1 := by
    intro R hR' y hy hy1
    rw [mem_conjSub_iff] at hy
    have h1 := hZ R hR' _ hy (by simp only [map_mul, map_inv, hy1, mul_one, inv_mul_cancel])
    calc y = a * (a⁻¹ * y * a) * a⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨y, hy, rfl⟩ := hzB
  obtain ⟨y', hy', hyy'⟩ := hzC
  have hy2 : y * y = 1 := hZc hB _ ((conjSub a B).mul_mem hy hy) (by rw [map_mul]; exact hz.sq)
  have hy1 : y ≠ 1 := fun h1 => hz.ne_one (by rw [h1, map_one])
  have hy'2 : y' * y' = 1 :=
    hZc hC _ ((conjSub a C).mul_mem hy' hy') (by rw [map_mul, hyy']; exact hz.sq)
  have hy'1 : y' ≠ 1 := fun h1 => hz.ne_one (by rw [← hyy', h1, map_one])
  have e1 := ((hb.conj a).unique y hy hy2).resolve_left hy1
  have e2 := ((hc.conj a).unique y' hy' hy'2).resolve_left hy'1
  apply hbc1
  refine hZ D hD _ hbcD ?_
  have hx : ψ (a * (b * c⁻¹) * a⁻¹) = 1 := by
    rw [show a * (b * c⁻¹) * a⁻¹ = y * y'⁻¹ by rw [e1, e2]; group, map_mul, map_inv, hyy',
      mul_inv_cancel]
  have h1 : ψ (b * c⁻¹) = (ψ a)⁻¹ * ψ (a * (b * c⁻¹) * a⁻¹) * ψ a := by
    simp only [map_mul, map_inv]
    group
  rw [h1, hx, mul_one, inv_mul_cancel]

end Two

section Models5

@[expose] def pair5 (i j : Fin 5) (h : i ≠ j) : Models.Pair 5 :=
  ⟨{i, j}, Finset.card_pair h⟩

theorem zMat_pair5 {K : Type} [Field K] :
    Models.zMat K 5 (pair5 2 3 (by decide)).1 * Models.zMat K 5 (pair5 2 4 (by decide)).1 =
      Models.zMat K 5 (pair5 3 4 (by decide)).1 := by
  simp only [pair5, Models.zMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> simp


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twoNbrs_psl5 (hR : TypeRFam 3 Φ) (hgen : omegaGen Φ = ⊤)
    (ψ : (CompData.model .PSL 5).G →* X) (hker : ψ.ker ≤ Subgroup.center (CompData.model .PSL 5).G)
    (hfund : ∀ L ∈ Φ, ∃ R ∈ (CompData.model .PSL 5).fund, IsSylow2In L (R.map ψ)) :
    ∃ L ∈ Φ, ∃ M ∈ omegaNbr Φ L, ∃ M' ∈ omegaNbr Φ L, M ≠ M' := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have h2 := ModelFacts.TG3.two_ne_zero_three
  have hn : 2 ≤ 4 + 1 := by norm_num
  have hfeq : (CompData.model .PSL 5).fund = Models.longRootSet (K := GaloisField 3 1) hn :=
    RouteD.Exotic.fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := 4) (by norm_num)
  have hmem : ∀ T : Models.Pair 5, Models.Lc (GaloisField 3 1) T ∈ (CompData.model .PSL 5).fund :=
    fun T => by rw [hfeq]; exact Models.Lc_mem_longRootSet h2 hn T
  have hZ : ∀ R ∈ (CompData.model .PSL 5).fund, ∀ x ∈ R, ψ x = 1 → x = 1 := fun R hR' x hx h1 =>
    ModelFacts.eq_one_of_mem_center_of_easy .PSL 5 3 1 Nat.prime_three trivial hadm (by decide)
      (by decide) (by decide) (by decide) (by decide) hR' hx (hker (MonoidHom.mem_ker.mpr h1))
  have hbc : Models.zElt (GaloisField 3 1) (pair5 2 3 (by decide)) *
      (Models.zElt (GaloisField 3 1) (pair5 2 4 (by decide)))⁻¹ =
        Models.zElt (GaloisField 3 1) (pair5 3 4 (by decide)) := by
    rw [Models.inv_eq_self_of_mem (Models.zElt_mem_signGroup _)]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Models.coe_zElt, Models.coe_zElt, Models.coe_zElt,
      zMat_pair5]
  obtain ⟨L, hL⟩ := nonempty_of_lieLinkSection hgen hker
    (Q3W.not_commutes_self_modelFund3 (t := .PSL) (n := 5) trivial hadm (by decide) (by decide)
      (hmem (pair5 0 1 (by decide))))
  obtain ⟨R₀, hR₀, hLR⟩ := hfund L hL
  refine ⟨L, hL, exists_two_nbrs_of_sep hR ψ
    (ModelFacts.fundamentalSingleClass .PSL 5 3 1 Nat.prime_three trivial hadm (by decide)
      (by decide)) hZ (hmem (pair5 0 1 (by decide))) (hmem (pair5 2 3 (by decide)))
    (hmem (pair5 2 4 (by decide))) (hmem (pair5 3 4 (by decide)))
    (Models.commutes_Lc_of_disjoint h2 (by decide)) (Models.commutes_Lc_of_disjoint h2 (by decide))
    (Models.isUniqueInvolution_Lc h2 hn _) (Models.isUniqueInvolution_Lc h2 hn _) ?_ ?_ hL hR₀
    hLR⟩
  · have h := (Models.isUniqueInvolution_Lc h2 hn (pair5 3 4 (by decide))).mem
    rw [← hbc] at h
    exact h
  · have h := Models.zElt_ne_one h2 (K := GaloisField 3 1) (pair5 3 4 (by decide))
    rw [← hbc] at h
    exact h

theorem twoNbrs_psu5 (hR : TypeRFam 3 Φ) (hgen : omegaGen Φ = ⊤)
    (ψ : (CompData.model .PSU 5).G →* X) (hker : ψ.ker ≤ Subgroup.center (CompData.model .PSU 5).G)
    (hfund : ∀ L ∈ Φ, ∃ R ∈ (CompData.model .PSU 5).fund, IsSylow2In L (R.map ψ)) :
    ∃ L ∈ Φ, ∃ M ∈ omegaNbr Φ L, ∃ M' ∈ omegaNbr Φ L, M ≠ M' := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨e, he⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have h2 : (2 : GaloisField 3 (2 * 1)) ≠ 0 :=
    Models.two_ne_zero_of_charP_ne_two (p := 3) (by norm_num)
  have hn : 2 ≤ 5 := by norm_num
  have hmem : ∀ T : Models.Pair 5, (Models.LcU (GaloisField 3 (2 * 1)) 3 1 T).map
      e.symm.toMonoidHom ∈ (CompData.model .PSU 5).fund := fun T =>
    (he _).mpr (by rw [Asc77.muTab_map_equiv_symm_map]; exact Models.LcU_mem_longRootSetU h2 hn T)
  have hinv : ∀ T : Models.Pair 5, IsUniqueInvolution
      ((Models.LcU (GaloisField 3 (2 * 1)) 3 1 T).map e.symm.toMonoidHom)
      (e.symm (Models.zEltU (GaloisField 3 (2 * 1)) 3 1 T)) := fun T =>
    isUniqueInvolution_map_mulEquiv e.symm (Models.isUniqueInvolution_LcU hK (by norm_num) hn T)
  have hcomm : ∀ {T T' : Models.Pair 5}, Disjoint T.1 T'.1 →
      Commutes ((Models.LcU (GaloisField 3 (2 * 1)) 3 1 T).map e.symm.toMonoidHom)
        ((Models.LcU (GaloisField 3 (2 * 1)) 3 1 T').map e.symm.toMonoidHom) := fun hd =>
    ih8_commutes_map e.symm.toMonoidHom (Models.commutes_LcU_of_disjoint h2 hd)
  have hZ : ∀ R ∈ (CompData.model .PSU 5).fund, ∀ x ∈ R, ψ x = 1 → x = 1 := fun R hR' x hx h1 =>
    ModelFacts.eq_one_of_mem_center_PSU (p := 3) 5 1 trivial hadm R hR' x hx
      (hker (MonoidHom.mem_ker.mpr h1))
  have hbc : Models.zEltU (GaloisField 3 (2 * 1)) 3 1 (pair5 2 3 (by decide)) *
      (Models.zEltU (GaloisField 3 (2 * 1)) 3 1 (pair5 2 4 (by decide)))⁻¹ =
        Models.zEltU (GaloisField 3 (2 * 1)) 3 1 (pair5 3 4 (by decide)) := by
    rw [inv_eq_of_mul_eq_one_right (Models.zEltU_mul_self _)]
    apply Models.suMat_injective
    rw [Models.suMat_mul, Models.suMat_zEltU, Models.suMat_zEltU, Models.suMat_zEltU, zMat_pair5]
  have hbc' : e.symm (Models.zEltU (GaloisField 3 (2 * 1)) 3 1 (pair5 2 3 (by decide))) *
      (e.symm (Models.zEltU (GaloisField 3 (2 * 1)) 3 1 (pair5 2 4 (by decide))))⁻¹ =
        e.symm (Models.zEltU (GaloisField 3 (2 * 1)) 3 1 (pair5 3 4 (by decide))) := by
    rw [← map_inv, ← map_mul, hbc]
  obtain ⟨L, hL⟩ := nonempty_of_lieLinkSection hgen hker
    (Q3W.not_commutes_self_modelFund3 (t := .PSU) (n := 5) trivial hadm (by decide) (by decide)
      (hmem (pair5 0 1 (by decide))))
  obtain ⟨R₀, hR₀, hLR⟩ := hfund L hL
  refine ⟨L, hL, exists_two_nbrs_of_sep hR ψ
    (ModelFacts.fundamentalSingleClass .PSU 5 3 1 Nat.prime_three trivial hadm (by decide)
      (by decide)) hZ (hmem (pair5 0 1 (by decide))) (hmem (pair5 2 3 (by decide)))
    (hmem (pair5 2 4 (by decide))) (hmem (pair5 3 4 (by decide))) (hcomm (by decide))
    (hcomm (by decide)) (hinv _) (hinv _) ?_ ?_ hL hR₀ hLR⟩
  · have h := (hinv (pair5 3 4 (by decide))).mem
    rw [← hbc'] at h
    exact h
  · have h : e.symm (Models.zEltU (GaloisField 3 (2 * 1)) 3 1 (pair5 3 4 (by decide))) ≠ 1 :=
      fun h => Models.zEltU_ne_one h2 _ (e.symm.injective (h.trans (map_one _).symm))
    rw [← hbc'] at h
    exact h

end Models5

end CFSG.ClassicalInvolution.Q3.TL4
