module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigBoundA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem commute_of_mem_fixAlt {n : ℕ} {τ : Perm (Fin n)} {b : alternatingGroup (Fin n)}
    (hb : b ∈ fixAlt τ) : (b : Perm (Fin n)) * τ = τ * b := by
  have hd : (b : Perm (Fin n)).Disjoint τ := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    exact Disjoint.mono_left (mem_fixAlt.mp hb) disjoint_compl_left
  exact hd.commute.eq

variable {X : Type} [Group X]

@[expose] def IsPermAction {M : Subgroup X} {r : ℕ}
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r))
    (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)) : Prop :=
  ∀ (g : ↥(normalizer (M : Set X))) (m : ↥M),
    ((θ ((M.normalizerMonoidHom g m : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin r)) :
      Perm (Fin r)) = ρ g * (θ (m : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) * (ρ g)⁻¹

theorem exists_isPermAction {M : Subgroup X} {r : ℕ} (hr5 : 5 ≤ r) (hr6 : r ≠ 6)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)) :
    ∃ ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r), IsPermAction θ ρ := by
  classical
  set O := pPrimeCore 2 ↥M with hOdef
  have hO : ∀ c : MulAut ↥M, O.map (c : ↥M →* ↥M) = O := fun c => by
    have h := Subgroup.characteristic_iff_map_eq.mp (inferInstance : O.Characteristic) c
    exact h
  let A : ↥(normalizer (M : Set X)) →* MulAut (↥M ⧸ O) :=
    { toFun := fun g => QuotientGroup.congr O O (M.normalizerMonoidHom g) (hO _)
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H m => rw [QuotientGroup.congr_mk, map_one]; rfl
      map_mul' := by
        intro g h
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H m =>
          rw [QuotientGroup.congr_mk, map_mul]
          change _ = QuotientGroup.congr O O (M.normalizerMonoidHom g) (hO _)
            (QuotientGroup.congr O O (M.normalizerMonoidHom h) (hO _) (m : ↥M ⧸ O))
          rw [QuotientGroup.congr_mk, QuotientGroup.congr_mk]
          rfl }
  let B : MulAut (↥M ⧸ O) ≃* MulAut (alternatingGroup (Fin r)) := MulAut.congr θ
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj r hr5 hr6
  let C : Perm (Fin r) ≃* MulAut (alternatingGroup (Fin r)) := MulEquiv.ofBijective _ hbij
  refine ⟨C.symm.toMonoidHom.comp (B.toMonoidHom.comp A), fun g m => ?_⟩
  have h1 : C (C.symm (B (A g))) = B (A g) := C.apply_symm_apply _
  have h2 : B (A g) (θ (m : ↥M ⧸ O)) = θ ((M.normalizerMonoidHom g m : ↥M) : ↥M ⧸ O) := by
    change θ (A g (θ.symm (θ (m : ↥M ⧸ O)))) = _
    rw [MulEquiv.symm_apply_apply]
    change θ (QuotientGroup.congr O O (M.normalizerMonoidHom g) (hO _) (m : ↥M ⧸ O)) = _
    rw [QuotientGroup.congr_mk]
  rw [← h2, ← h1]
  rfl

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.apply_of_mem (hρ : IsPermAction θ ρ) (hr : 4 ≤ r) (m : ↥M) :
    ρ ⟨m, le_normalizer m.2⟩ = (θ (m : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) := by
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup r hr
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨q, rfl⟩ := θ.surjective a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change ρ _ * _ * (ρ _)⁻¹ = (θ (m : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) *
    (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) * (θ (m : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r))⁻¹
  rw [← hρ]
  have h1 : (M.normalizerMonoidHom ⟨m, le_normalizer m.2⟩ x : ↥M) = m * x * m⁻¹ :=
    Subtype.ext (by simp)
  rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv]
  rfl

theorem IsPermAction.mem_coreActionKernel (hρ : IsPermAction θ ρ) {g : X}
    (hg : g ∈ normalizer (M : Set X)) (h1 : ρ ⟨g, hg⟩ = 1) :
    g ∈ UnbalancedLayer.coreActionKernel M := by
  refine ⟨hg, fun j hj => ?_⟩
  have h2 : ρ (⟨g, hg⟩⁻¹ : ↥(normalizer (M : Set X))) = 1 := by rw [map_inv, h1, inv_one]
  have h3 := hρ (⟨g, hg⟩⁻¹ : ↥(normalizer (M : Set X))) ⟨j, hj⟩
  rw [h2, one_mul, inv_one, mul_one] at h3
  have h4 : ((M.normalizerMonoidHom (⟨g, hg⟩⁻¹ : ↥(normalizer (M : Set X))) ⟨j, hj⟩ : ↥M) :
      ↥M ⧸ pPrimeCore 2 ↥M) = ((⟨j, hj⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) :=
    θ.injective (Subtype.ext h3)
  have h5 := QuotientGroup.eq.mp h4.symm
  refine ⟨_, h5, ?_⟩
  simp [mul_assoc]

theorem IsPermAction.exists_lift (hρ : IsPermAction θ ρ) [Finite X] {a : X}
    (ha : a ∈ normalizer (M : Set X)) (ha2 : a * a = 1) {b : alternatingGroup (Fin r)}
    (hb : (b : Perm (Fin r)) * ρ ⟨a, ha⟩ = ρ ⟨a, ha⟩ * b) :
    ∃ x : ↥M, (x : X) ∈ Subgroup.centralizer ({a} : Set X) ∧
      θ (x : ↥M ⧸ pPrimeCore 2 ↥M) = b := by
  set c := M.normalizerMonoidHom ⟨a, ha⟩ with hcdef
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hc : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcdef, normalizerMonoidHom_apply_apply_coe, normalizerMonoidHom_apply_apply_coe]
    change a * (a * (x : X) * a⁻¹) * a⁻¹ = x
    rw [hainv]
    calc a * (a * (x : X) * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2]; group
  obtain ⟨q, hq⟩ := θ.surjective b
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hw : ((c w₀ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = (w₀ : ↥M ⧸ pPrimeCore 2 ↥M) := by
    apply θ.injective
    apply Subtype.ext
    rw [hcdef, hρ ⟨a, ha⟩ w₀, hq, ← hb, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨w, hwc, hww⟩ := exists_fixed_of_mk_eq c hc hw
  refine ⟨w, ?_, by rw [hww, hq]⟩
  have h := congrArg Subtype.val hwc
  rw [hcdef, normalizerMonoidHom_apply_apply_coe] at h
  change a * (w : X) * a⁻¹ = w at h
  rw [mem_centralizer_singleton_iff]
  calc (w : X) * a = a * w * a⁻¹ * a := by rw [h]
    _ = a * w := by group

theorem IsPermAction.le_coreActionKernel (hρ : IsPermAction θ ρ) [Finite X] {a : X}
    (ha : a ∈ normalizer (M : Set X)) (ha2 : a * a = 1) (h4 : (ρ ⟨a, ha⟩).support.card ≤ 4)
    (h5 : 5 ≤ r - (ρ ⟨a, ha⟩).support.card) {Y : Subgroup X} (hYN : Y ≤ normalizer (M : Set X))
    (hYO : Y ≤ (pPrimeCore 2 (centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype) :
    Y ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  set σ := ρ ⟨a, ha⟩ with hσdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  set Oa := (pPrimeCore 2 ↥Ca).map Ca.subtype with hOadef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have : (⟨a, ha⟩ : ↥(normalizer (M : Set X))) * ⟨a, ha⟩ = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hOaodd : Odd (Nat.card Oa) := by
    rw [hOadef, card_map_of_injective Ca.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOaCa : Oa ≤ Ca := map_subtype_le _
  have hOanorm : ∀ g ∈ Ca, ∀ z ∈ Oa, g * z * g⁻¹ ∈ Oa := fun g hg z hz =>
    (mem_normalizer_iff.mp (Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Ca) hg) z).mp hz
  set π : ↥M →* alternatingGroup (Fin r) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥M)) with hπdef
  have hπ : ∀ x : ↥M, π x = θ (x : ↥M ⧸ pPrimeCore 2 ↥M) := fun _ => rfl
  have hconj : ∀ x : ↥M, (x : X) ∈ Ca → (π x : Perm (Fin r)) * σ = σ * π x := by
    intro x hx
    have hxa : M.normalizerMonoidHom ⟨a, ha⟩ x = x := by
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_apply_coe]
      change a * (x : X) * a⁻¹ = x
      have h1 : (x : X) * a = a * x := mem_centralizer_singleton_iff.mp hx
      rw [← h1]
      group
    have h1 := hρ ⟨a, ha⟩ x
    rw [hxa] at h1
    rw [hπ]
    calc (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) * σ =
        (σ * (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) * σ⁻¹) * σ := by rw [← h1]
      _ = σ * (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) := by group
  set K : Subgroup ↥M := (Ca ⊓ Oa).subgroupOf M with hKdef
  set N : Subgroup (alternatingGroup (Fin r)) := K.map π with hNdef
  have hNodd : Odd (Nat.card N) := by
    have h1 : Nat.card N ∣ Nat.card K := K.card_map_dvd π
    let f : K →* Oa :=
      { toFun := fun x => ⟨((x : ↥M) : X), (mem_subgroupOf.mp x.2).2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun x y h => by
      have h' : ((x : ↥M) : X) = ((y : ↥M) : X) := congrArg (fun z : Oa => (z : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (hOaodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)).of_dvd_nat h1
  have hNc : ∀ g ∈ N, (g : Perm (Fin r)) * σ = σ * g := by
    rintro _ ⟨k, hk, rfl⟩
    exact hconj k (mem_subgroupOf.mp hk).1
  have hNn : ∀ b ∈ fixAlt σ, ∀ g ∈ N, b * g * b⁻¹ ∈ N := by
    rintro b hb _ ⟨k, hk, rfl⟩
    obtain ⟨xb, hxbCa, hxbθ⟩ := hρ.exists_lift ha ha2 (commute_of_mem_fixAlt hb)
    have hk' := mem_subgroupOf.mp hk
    refine ⟨xb * k * xb⁻¹, ?_, ?_⟩
    · refine mem_subgroupOf.mpr ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_inf.mpr
        ⟨mul_mem (mul_mem hxbCa hk'.1) (inv_mem hxbCa), hOanorm _ hxbCa _ hk'.2⟩
    · rw [map_mul, map_mul, map_inv, hπ xb, hxbθ]
  have hN : N = ⊥ := eq_bot_of_odd_of_commute hσ2 h4 h5 hNodd hNc hNn
  intro y hy
  have hyN := hYN hy
  have hyOa := hYO hy
  have hyCa : y ∈ Ca := hOaCa hyOa
  set ρy := ρ ⟨y, hyN⟩ with hρydef
  have hyodd : Odd (orderOf ρy) := by
    have h1 : orderOf ρy ∣ orderOf (⟨y, hyN⟩ : ↥(normalizer (M : Set X))) := orderOf_map_dvd ρ _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf y ∣ Nat.card Oa := by
      have := orderOf_dvd_natCard (⟨y, hyOa⟩ : Oa)
      rwa [Subgroup.orderOf_mk] at this
    exact (hOaodd.of_dvd_nat h2).of_dvd_nat h1
  have hyc : ρy * σ = σ * ρy := by
    rw [hρydef, hσdef, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp hyCa
  have hfix : ∀ x ∈ σ.support, ρy x = x := fun x hx =>
    apply_eq_of_odd_commute hσ2 h4 hyc hyodd hx
  have hcomm : ∀ b ∈ fixAlt σ, ρy * (b : Perm (Fin r)) = (b : Perm (Fin r)) * ρy := by
    intro b hb
    obtain ⟨xb, hxbCa, hxbθ⟩ := hρ.exists_lift ha ha2 (commute_of_mem_fixAlt hb)
    set z : ↥M := M.normalizerMonoidHom ⟨y, hyN⟩ xb * xb⁻¹ with hzdef
    have hzK : z ∈ K := by
      rw [mem_subgroupOf]
      have hz : (z : X) = y * xb * y⁻¹ * (xb : X)⁻¹ := by
        rw [hzdef, Subgroup.coe_mul, normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
      rw [hz]
      refine Subgroup.mem_inf.mpr
        ⟨mul_mem (mul_mem (mul_mem hyCa hxbCa) (inv_mem hyCa)) (inv_mem hxbCa), ?_⟩
      have h1 : (xb : X) * y⁻¹ * (xb : X)⁻¹ ∈ Oa := hOanorm _ hxbCa _ (inv_mem hyOa)
      have h2 := mul_mem hyOa h1
      simpa [mul_assoc] using h2
    have hπz : π z = 1 := by
      have h1 : π z ∈ N := ⟨z, hzK, rfl⟩
      rw [hN] at h1
      exact h1
    rw [hzdef, map_mul, map_inv, hπ, hπ] at hπz
    have h2 : θ ((M.normalizerMonoidHom ⟨y, hyN⟩ xb : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        θ (xb : ↥M ⧸ pPrimeCore 2 ↥M) := mul_inv_eq_one.mp hπz
    have h1 := hρ ⟨y, hyN⟩ xb
    rw [h2, hxbθ] at h1
    calc ρy * (b : Perm (Fin r)) = (ρy * (b : Perm (Fin r)) * ρy⁻¹) * ρy := by group
      _ = (b : Perm (Fin r)) * ρy := by rw [← h1]
  have hρy : ρy = 1 := eq_one_of_commute_fixAlt hfix (by omega) hcomm
  exact hρ.mem_coreActionKernel hyN hρy

end CFSG.ComponentClassification.SolMax
