module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtraspecialAb
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.Sporadic.Bridge.ThSurj
public import Certificates.Certificate129003
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Blueprint
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

theorem card_le_eight_of_card_support {F : Subgroup (Equiv.Perm (Fin 9))}
    (hcomm : ∀ σ ∈ F, ∀ τ ∈ F, σ * τ = τ * σ)
    (hsupp : ∀ σ ∈ F, σ ≠ 1 → σ.support.card = 8) : Nat.card F ≤ 8 := by
  by_cases hF : F = ⊥
  · rw [hF, Subgroup.card_bot]
    norm_num
  obtain ⟨⟨σ₀, hσ₀F⟩, hσ₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF
  have hσ₀1 : σ₀ ≠ 1 := fun h => hσ₀ (Subtype.ext h)
  have hcard : (Finset.univ \ σ₀.support).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hsupp σ₀ hσ₀F hσ₀1]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hcard
  have hfix : ∀ i, σ₀ i = i ↔ i = p := by
    intro i
    have : i ∈ Finset.univ \ σ₀.support ↔ σ₀ i = i := by
      simp [Equiv.Perm.mem_support]
    rw [← this, hp, Finset.mem_singleton]
  have hFp : ∀ τ ∈ F, τ p = p := by
    intro τ hτ
    apply (hfix (τ p)).1
    have h := congrArg (fun f : Equiv.Perm (Fin 9) => f p) (hcomm σ₀ hσ₀F τ hτ)
    simp only [Equiv.Perm.mul_apply, (hfix p).2 rfl] at h
    exact h
  obtain ⟨q, hqp⟩ : ∃ q : Fin 9, q ≠ p := by
    by_cases h : p = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, Ne.symm h⟩
  have hfree : ∀ τ ∈ F, τ q = q → τ = 1 := by
    intro τ hτ hτq
    by_contra hτ1
    have h8 := hsupp τ hτ hτ1
    have hsub : τ.support ⊆ (Finset.univ.erase p).erase q := by
      intro i hi
      rw [Equiv.Perm.mem_support] at hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hi (by rw [h]; exact hτq), fun h => hi (by rw [h]; exact hFp τ hτ)⟩
    have h7 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simpa using hqp), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin] at h7
    omega
  let f : F → {i : Fin 9 // i ≠ p} := fun τ =>
    ⟨(τ : Equiv.Perm (Fin 9)) q, fun h => hqp (by
      have h' : (τ : Equiv.Perm (Fin 9)) q = (τ : Equiv.Perm (Fin 9)) p := by rw [h, hFp τ τ.2]
      exact (τ : Equiv.Perm (Fin 9)).injective h')⟩
  have hf : Function.Injective f := by
    intro τ τ' h
    have h1 : (τ : Equiv.Perm (Fin 9)) q = (τ' : Equiv.Perm (Fin 9)) q := congrArg Subtype.val h
    have h2 := hfree ((τ' : Equiv.Perm (Fin 9))⁻¹ * τ) (F.mul_mem (F.inv_mem τ'.2) τ.2)
      (by rw [Equiv.Perm.mul_apply, h1]; exact (τ' : Equiv.Perm (Fin 9)).symm_apply_apply q)
    exact Subtype.ext (inv_mul_eq_one.1 h2).symm
  have h8 : Nat.card {i : Fin 9 // i ≠ p} = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_subtype_eq]
  exact (Nat.card_le_card_of_injective f hf).trans h8.le

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {z w : G} (hz : z * z = 1)
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz]
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · exact Or.inl (zpow_zero z)
  · exact Or.inr (zpow_one z)

@[expose] noncomputable def thPermHom :
    ↥M →* Equiv.Perm (Fin 9) :=
  (alternatingGroup (Fin 9)).subtype.comp (kappa.toMonoidHom.comp AltQuot.proj)

theorem thPermHom_apply
    (m : ↥M) :
    thPermHom m = ((kappa (AltQuot.proj m) : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) :=
  rfl

theorem thPermHom_eq_one_iff
    {m : ↥M} : thPermHom m = 1 ↔ (m : J) ∈ Q := by
  rw [thPermHom_apply, ← AltQuot.proj_eq_one_iff, ← map_eq_one_iff _ kappa.injective]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

theorem card_support_aPerm : aPerm.support.card = 8 := by decide

theorem card_support_thPermHom
    {m : ↥M}
    (hm2 : (m : J) * m = 1) (hmQ : (m : J) ∉ Q) : (thPermHom m).support.card = 8 := by
  have hm1 : (m : J) ≠ 1 := fun h => hmQ (h ▸ Q.one_mem)
  have hord : orderOf (m : J) = 2 := orderOf_eq_prime (by rw [sq]; exact hm2) hm1
  obtain ⟨g, hgM, hg⟩ := max3_involution_representatives (m : J) m.2 hord
  rcases hg with h | h | h
  · exfalso
    apply hmQ
    have := AltQuot.conj_mem_Q_of_mem_M (M.inv_mem hgM) (h ▸ z_mem_Q :
      g * (m : J) * g⁻¹ ∈ Q)
    simpa [mul_assoc] using this
  · exfalso
    apply hmQ
    have := AltQuot.conj_mem_Q_of_mem_M (M.inv_mem hgM) (h ▸ q_mem_Q 0 :
      g * (m : J) * g⁻¹ ∈ Q)
    simpa [mul_assoc] using this
  · have hx : (⟨g, hgM⟩ : ↥M) * m * (⟨g, hgM⟩ : ↥M)⁻¹ = ⟨x, x_mem_M⟩ := Subtype.ext h
    have hxp : thPermHom ⟨x, x_mem_M⟩ = aPerm := kappa_mk_x
    have e : thPermHom m = (thPermHom ⟨g, hgM⟩)⁻¹ * aPerm * ((thPermHom ⟨g, hgM⟩)⁻¹)⁻¹ := by
      rw [← hxp, ← hx, map_mul, map_mul, map_inv]
      group
    rw [e, Equiv.Perm.card_support_conj, card_support_aPerm]

theorem card_le_of_le_M
    {E : Subgroup J} (hEM : E ≤ M)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ 8 := by
  let ψ : ↥E →* Equiv.Perm (Fin 9) :=
    thPermHom.comp (Subgroup.inclusion hEM)
  have hψ : ∀ e : ↥E, ψ e = thPermHom ⟨(e : J), hEM e.2⟩ := fun _ => rfl
  have hker : Nat.card ψ.ker ≤ 32 := by
    have hk : ψ.ker = Q.subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, hψ, thPermHom_eq_one_iff, Subgroup.mem_subgroupOf]
    rw [hk, ← Subgroup.card_map_of_injective (f := E.subtype) E.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    refine CFSG.Quasithin.D4Hex.card_abelian_le_32 (z := z) card_Q ?_ ?_ inf_le_left
      (fun x hx y hy => hcomm x hx.2 y hy.2)
    · intro x hx y hy
      have h := AltQuot.comm_mem_zpowers hx hy
      rw [commutatorElement_def] at h
      exact eq_one_or_eq_of_mem_zpowers z_mul_self h
    · intro w hw hcent
      have hc : (⟨w, hw⟩ : ↥Q) ∈ Subgroup.center Q :=
        Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcent g g.2)
      rw [center_Q, Subgroup.mem_subgroupOf] at hc
      exact eq_one_or_eq_of_mem_zpowers z_mul_self hc
  have hrange : Nat.card ψ.range ≤ 8 := by
    refine card_le_eight_of_card_support ?_ ?_
    · rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
      have hee : e * e' = e' * e := Subtype.ext (hcomm _ e.2 _ e'.2)
      calc ψ e * ψ e' = ψ (e * e') := (ψ.map_mul e e').symm
        _ = ψ (e' * e) := by rw [hee]
        _ = ψ e' * ψ e := ψ.map_mul e' e
    · rintro _ ⟨e, rfl⟩ he
      rw [hψ] at he ⊢
      exact card_support_thPermHom (hsq _ e.2) fun hQ => he (thPermHom_eq_one_iff.2 hQ)
  calc Nat.card E = Nat.card ψ.range * Nat.card ψ.ker := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
          Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    _ ≤ 8 * 32 := Nat.mul_le_mul hrange hker
    _ = 2 ^ 8 := by norm_num

theorem th_elemAbelian_le_J :
    ∀ B : Subgroup J, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ 8 := by
  intro B hcomm hsq
  by_cases hB : B = ⊥
  · rw [hB, Subgroup.card_bot]
    norm_num
  obtain ⟨⟨e, heB⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have hord : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hsq e heB) he1'
  obtain ⟨g, hg⟩ := isConj_iff.1 (all_involutions_conjugate e hord)
  set B' : Subgroup J := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
  have hcard : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hmem : ∀ w ∈ B', ∃ v ∈ B, g⁻¹ * v * g = w := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨v, hv, by simp⟩
  have haB' : a ∈ B' := ⟨e, heB, by simp [← hg, mul_assoc]⟩
  have hB'comm : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := hmem x hx
    obtain ⟨v', hv', rfl⟩ := hmem y hy
    have h := hcomm v hv v' hv'
    calc g⁻¹ * v * g * (g⁻¹ * v' * g) = g⁻¹ * (v * v') * g := by group
      _ = g⁻¹ * (v' * v) * g := by rw [h]
      _ = g⁻¹ * v' * g * (g⁻¹ * v * g) := by group
  have hB'sq : ∀ x ∈ B', x * x = 1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hmem x hx
    calc g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
      _ = 1 := by rw [hsq v hv]; group
  have hB'M : B' ≤ M := by
    intro w hw
    rw [← CFSG.Sporadic.Th.Kernel.centralizer_a_eq_M CFSG.Sporadic.Th.th_kernel_facts,
      Subgroup.mem_centralizer_singleton_iff]
    exact hB'comm w hw a haB'
  rw [← hcard]
  exact card_le_of_le_M hB'M hB'comm hB'sq

@[expose] noncomputable def thDihC : J :=
  AllConj.abProd thDihWord

theorem thDih_parts :
    eqRows (powRows (thDihRows ()) 19) idRows = true ∧ eqRows (thDihRows ()) idRows = false := by
  have h := Certificates.certificate129003
  unfold thDihCheck at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact h

theorem isRows_thDih :
    IsRows (thDihRows ()) (a * (thDihC * a * thDihC⁻¹)) :=
  isRows_a.mul (((AllConj.isRows_abProd thDihWord).mul isRows_a).mul
    (AllConj.isRows_abProd_inv thDihWord))

theorem orderOf_thDih :
    orderOf (a * (thDihC * a * thDihC⁻¹)) = 19 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨h1, h2⟩ := thDih_parts
  exact orderOf_eq_prime ((isRows_thDih.pow 19).eq_of_eqRows IsRows.one h1)
    (isRows_thDih.ne_of_eqRows IsRows.one h2)

theorem th_dihedral_J :
    ∀ t : J, t * t = 1 → t ≠ 1 → ∃ c : J, orderOf (t * (c * t * c⁻¹)) = 19 := by
  intro t ht2 ht1
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  obtain ⟨h, hh⟩ := isConj_iff.1 (all_involutions_conjugate t hord)
  refine ⟨h * thDihC * h⁻¹, ?_⟩
  have e : t * ((h * thDihC * h⁻¹) * t * (h * thDihC * h⁻¹)⁻¹) =
      MulAut.conj h (a * (thDihC * a * thDihC⁻¹)) := by
    rw [MulAut.conj_apply, ← hh]
    group
  rw [e, MulEquiv.orderOf_eq, orderOf_thDih]

@[expose] noncomputable def thImgJ
    (B : Subgroup NativeSporadic.Th) : Subgroup J where
  carrier := thEquivJ '' (B : Set NativeSporadic.Th)
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, B.mul_mem hx hy, map_mul _ _ _⟩
  one_mem' := ⟨1, B.one_mem, map_one _⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, B.inv_mem hx, map_inv _ _⟩

theorem th_autInner :
    ∀ φ : NativeSporadic.Th ≃* NativeSporadic.Th, ∃ s : NativeSporadic.Th,
      ∀ x, φ x = s * x * s⁻¹ := by
  intro φ
  have htop := CFSG.Sporadic.ThSchreier.inner_Th
  have h : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Th := by
    rw [htop]; trivial
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun x => by rw [← hs, MulAut.conj_apply]⟩

theorem th_elemAbelian_le :
    ∀ B : Subgroup NativeSporadic.Th, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 8 := by
  intro B hcomm hsq
  have hcomm' : ∀ x ∈ thImgJ B, ∀ y ∈ thImgJ B, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := congrArg thEquivJ (hcomm x hx y hy)
    rwa [map_mul, map_mul] at h
  have hsq' : ∀ x ∈ thImgJ B, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h := congrArg thEquivJ (hsq x hx)
    rwa [map_mul, map_one] at h
  have h := th_elemAbelian_le_J _ hcomm' hsq'
  have hc : Nat.card (thImgJ B) = Nat.card B :=
    Nat.card_image_of_injective thEquivJ.injective _
  rwa [hc] at h

theorem th_dihedral :
    ∀ t : NativeSporadic.Th, t * t = 1 → t ≠ 1 →
      ∃ c : NativeSporadic.Th, orderOf (t * (c * t * c⁻¹)) = 19 := by
  intro t ht2 ht1
  have hu2 : thEquivJ t * thEquivJ t = 1 := by rw [← map_mul, ht2, map_one]
  have hu1 : thEquivJ t ≠ 1 := fun h => ht1 (thEquivJ.injective (by rw [h, map_one]))
  obtain ⟨c, hc⟩ := th_dihedral_J (thEquivJ t) hu2 hu1
  refine ⟨thEquivJ.symm c, ?_⟩
  have e : thEquivJ (t * (thEquivJ.symm c * t * (thEquivJ.symm c)⁻¹)) =
      thEquivJ t * (c * thEquivJ t * c⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [← e, MulEquiv.orderOf_eq] at hc
  exact hc

theorem sporadicExclusion_Th :
    QuasithinUnique.Setup.X1.SporadicExclusion .Th := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact QuasithinUnique.Setup.X1.exclusion_of_autInner hW hq.1 hirr hE hEne hEel e th_autInner
    (r := 8) (ρ := 9) (by norm_num) th_elemAbelian_le
    (QuasithinUnique.Setup.X1.rank_of_dihedral hW hirr e (ρ := 9) (p := 19) (by norm_num)
      (by rw [QuasithinUnique.Setup.X1.orderOf_two_zmod_19]; norm_num) th_dihedral)

theorem noIrrFFOffender_Th :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Th).Group :=
  Proving.noIrrFFOffender_of_exclusion sporadicExclusion_Th CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_Th :
    GF2NoFFSporadicFor .Th :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_Th

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
