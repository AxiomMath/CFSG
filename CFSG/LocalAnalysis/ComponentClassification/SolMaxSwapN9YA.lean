module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCaseTwoW1
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9A

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Helpers

private def ya_g₀ : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

private def ya_c₃ : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩

private theorem ya_g₀_sq : ya_g₀ * ya_g₀ = 1 := by decide

private theorem ya_g₀_supp :
    ((ya_g₀ : alternatingGroup (Fin 5)) : Perm (Fin 5)).support.card = 4 := by
  decide

private theorem ya_g₀_c₃ : ya_g₀ * ya_c₃ ≠ ya_c₃ * ya_g₀ := by decide

private theorem ya_alt5_eq_one_of_mem_center {z : alternatingGroup (Fin 5)}
    (hz : z ∈ Subgroup.center (alternatingGroup (Fin 5))) : z = 1 := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (alternatingGroup (Fin 5))) with h | h
  · rw [h] at hz
    exact Subgroup.mem_bot.mp hz
  · exfalso
    have hall : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by
      intro a b
      have : a ∈ Subgroup.center (alternatingGroup (Fin 5)) := by rw [h]; exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp this) b).symm
    have hne : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := ⟨ya_g₀, ya_c₃, ya_g₀_c₃⟩
    obtain ⟨a, b, hab⟩ := hne
    exact hab (hall a b)

private theorem ya_odd_orderOf_of_mem {K : Subgroup X} (hK : Odd (Nat.card K)) {x : X}
    (hx : x ∈ K) : Odd (orderOf x) := by
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : K)
  rw [Subgroup.orderOf_mk] at h
  exact hK.of_dvd_nat h

private theorem ya_odd_card_core [Finite X] (R : Subgroup X) :
    Odd (Nat.card ((pPrimeCore 2 ↥R).map R.subtype)) := by
  rw [Subgroup.card_map_of_injective R.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

private theorem ya_false_of_involution_mem_core [Finite X] {R : Subgroup X} {a : X}
    (ha : a ∈ (pPrimeCore 2 ↥R).map R.subtype) (ha2 : a * a = 1) (ha1 : a ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have h3 := ya_odd_orderOf_of_mem (ya_odd_card_core R) ha
  rw [h2] at h3
  exact absurd h3 (by decide)

private theorem ya_mem_core_of_mem_coreActionKernel [Finite X] {V R : Subgroup X} (hRV : R ≤ V)
    (χ : ↥R ⧸ pPrimeCore 2 ↥R ≃* alternatingGroup (Fin 5)) {a : X} (haR : a ∈ R)
    (ha : a ∈ UnbalancedLayer.coreActionKernel V) :
    a ∈ (pPrimeCore 2 ↥R).map R.subtype := by
  set za : ↥R ⧸ pPrimeCore 2 ↥R := ((⟨a, haR⟩ : ↥R) : ↥R ⧸ pPrimeCore 2 ↥R) with hzadef
  have hcomm : ∀ q : ↥R ⧸ pPrimeCore 2 ↥R, za * q = q * za := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H v =>
      rw [hzadef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h1 := (UnbalancedLayer.mem_coreActionKernel.mp ha).2 (v : X) (hRV v.2)
      have h2 : (v : X)⁻¹ * a⁻¹ * (v : X) * a ∈ R :=
        mul_mem (mul_mem (mul_mem (inv_mem v.2) (inv_mem haR)) v.2) haR
      obtain ⟨y, hy, hyv⟩ := inf_pPrimeCore_le hRV ⟨h2, h1⟩
      have hyv' : (y : X) = (v : X)⁻¹ * a⁻¹ * (v : X) * a := hyv
      have h3 : (⟨a, haR⟩ * v)⁻¹ * (v * ⟨a, haR⟩) = y := by
        apply Subtype.ext
        rw [hyv']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3]
      exact hy
  have hz1 : za = 1 := by
    have h1 : χ za ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := χ.surjective g
      rw [← map_mul, ← map_mul, hcomm q]
    have h2 := ya_alt5_eq_one_of_mem_center h1
    rw [← map_one χ] at h2
    exact χ.injective h2
  rw [hzadef, QuotientGroup.eq_one_iff] at hz1
  exact ⟨_, hz1, rfl⟩

private theorem ya_mem_of_mul_odd {K : Subgroup X} {a g o : X} (ha : a * a = 1)
    (hconj : a * g * a⁻¹ ∈ K) (hg : g ∈ K) (hgo : g = a * o) (ho : Odd (orderOf o)) : a ∈ K := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hoa : o = a * g := by
    rw [hgo, ← mul_assoc, ha, one_mul]
  have ho2 : o * o ∈ K := by
    have h1 : o * o = (a * g * a⁻¹) * g := by
      rw [hainv]
      calc o * o = (a * g) * (a * g) := by rw [← hoa]
        _ = a * g * a * g := by simp only [mul_assoc]
    rw [h1]
    exact mul_mem hconj hg
  obtain ⟨m, hm⟩ := ho
  have hpow : o ^ (2 * m + 1) = 1 := by
    rw [← hm]
    exact pow_orderOf_eq_one o
  have hoK : o ∈ K := by
    have h1 : o = (o * o) ^ (m + 1) := by
      calc o = o ^ (2 * m + 1) * o := by rw [hpow, one_mul]
        _ = o ^ (2 * (m + 1)) := by
          rw [← pow_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
        _ = (o * o) ^ (m + 1) := by rw [pow_mul, sq]
    rw [h1]
    exact pow_mem ho2 (m + 1)
  have h1 : a = g * o⁻¹ := by
    rw [hgo]
    group
  rw [h1]
  exact mul_mem hg (inv_mem hoK)

private theorem ya_mem_core_of_theta_eq_one {M : Subgroup X} {m : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)} {g : ↥M}
    (h : θ (g : ↥M ⧸ pPrimeCore 2 ↥M) = 1) : (g : X) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
  have h1 : (g : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
    apply θ.injective
    rw [h, map_one]
  rw [QuotientGroup.eq_one_iff] at h1
  exact ⟨g, h1, rfl⟩

private theorem ya_fixA_le (M : Subgroup X) (e₀ r : X) : fixA M e₀ r ≤ M :=
  ((GSLit.fixedLayer_le_inf _ (zpowers r)).trans inf_le_left).trans
    ((GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left)

end Helpers

section MSide

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin 9)} {r : X}

private theorem ya_exists_involution_fixA (hs : Setting t J 9 e E D M)
    (hd : Data t J 9 e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) :
    ∃ (S : Finset (Fin 9)) (σ : Perm (Fin 9)) (a : X) (haA : a ∈ fixA M e₀ r),
      4 < S.card ∧ σ * σ = 1 ∧ σ.support.card = 4 ∧ σ.support ⊆ S ∧ a * a = 1 ∧
      ρ ⟨a, le_normalizer (ya_fixA_le M e₀ r haA)⟩ = σ ∧
      ∀ b : alternatingGroup (Fin 9), (∀ ω ∉ S, (b : Perm (Fin 9)) ω = ω) →
        ∃ (x : X) (hx : x ∈ fixA M e₀ r),
          θ ((⟨x, ya_fixA_le M e₀ r hx⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hs.le hs.pc hs.swap hs.diag
  obtain ⟨π, hπ⟩ := S.exists_perm_compat_of_swap hs.cent hs.le hs.pc hs.swap hs.diag hρ
  have he₀J : e₀ ∈ J := S.le hd.e₀E
  have he₀N : e₀ ∈ normalizer (M : Set X) := hJN he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
    rw [hπ e₀ he₀J he₀N, Perm.card_support_conj]
    exact S.card_support_coreImage_E hd.e₀E hd.e₀1
  obtain ⟨hAle, hApc, ⟨χA⟩⟩ :=
    fixedLayer_facts_of_perm hs.le hs.pc hρ he₀N he₀2 he₀4.le (by omega)
  set A := GSLit.fixedLayer M (zpowers e₀) with hAdef
  have hAM : A ≤ M := (GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left
  have hAe : A ≤ centralizer ({e₀} : Set X) := hAle.trans inf_le_right
  have hAMe : A ≤ M ⊓ centralizer ({e₀} : Set X) := le_inf hAM hAe
  have hApcM : IsPComponent 2 (A.subgroupOf (M ⊓ centralizer ({e₀} : Set X))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hAMe (inf_le_inf_right _ hs.le) hApc
  obtain ⟨-, hAres, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAMe).mp hApcM
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hre₀ : r ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀
  have hrA : r ∈ normalizer (A : Set X) := by
    refine GSLit.mem_normalizer_fixedLayer hrK.1 (centralizer_le_normalizer _ ?_)
    rw [centralizer_zpowers_eq' e₀]
    exact hre₀
  have hrKA : r ∈ UnbalancedLayer.coreActionKernel A := mem_coreActionKernel_of_le hAM hrK hrA
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hArA : fixA M e₀ r ≤ A := (GSLit.fixedLayer_le_inf A (zpowers r)).trans inf_le_left
  have hArM : fixA M e₀ r ≤ M := hArA.trans hAM
  obtain ⟨Φ, hΦ⟩ := exists_fixedLayer_coreQuot_equiv hAq (zpowers_le.mpr hrKA) hR2
  have hcardA : Fintype.card ↥((ρ ⟨e₀, he₀N⟩).supportᶜ : Finset (Fin 9)) = 9 - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, he₀4]
  obtain ⟨τM, hτM, ψM, hψM⟩ := exists_image_equiv_of_component (M := M) (Je := A) (by omega)
    (by omega) (by omega) θ hρ (hAM.trans le_normalizer) hAres hcardA χA
    (exists_rho_ne_one (by omega) hρ hAM (LocalCores.isQuasisimple_nontrivial hAq))
    he₀N he₀2 hAM hAe hApcM
  obtain ⟨⟨χr⟩, -, -⟩ := pump_holds X t J 9 e E D M hs e₀ F DF r hd he₀H
  let χ5 : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin 5) := χr
  let ψ5 : alternatingGroup (Fin 5) ≃* fixAlt τM := (χ5.symm.trans Φ).trans ψM
  have hlift : ∀ g : alternatingGroup (Fin 5), ∃ (x : X) (hx : x ∈ fixA M e₀ r),
      θ ((⟨x, hArM hx⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        ((ψ5 g : fixAlt τM) : alternatingGroup (Fin 9)) := by
    intro g
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (χ5.symm g)
    refine ⟨x, x.2, ?_⟩
    have h1 := hΦ x (hArA x.2)
    have h2 := hψM ⟨x, hArA x.2⟩
    have h3 := hρ.apply_of_mem (by omega) ⟨x, hArM x.2⟩
    have h4 : ψ5 g =
        ψM (Φ ((x : ↥(fixA M e₀ r)) : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r))) := by
      show ψM (Φ (χ5.symm g)) = _
      rw [← hx]
    apply Subtype.ext
    rw [h4, h1]
    exact h3.symm.trans h2.symm
  obtain ⟨x₀, hx₀A, hx₀⟩ := hlift ya_g₀
  have hψ2 : ψ5 ya_g₀ * ψ5 ya_g₀ = 1 := by rw [← map_mul, ya_g₀_sq, map_one]
  set σ : Perm (Fin 9) :=
    (((ψ5 ya_g₀ : fixAlt τM) : alternatingGroup (Fin 9)) : Perm (Fin 9)) with hσdef
  have hσ2 : σ * σ = 1 := by
    have h := congrArg (fun z : fixAlt τM => ((z : alternatingGroup (Fin 9)) : Perm (Fin 9))) hψ2
    simpa using h
  have hσ4 : σ.support.card = 4 := by
    have h := card_support_of_le_fixAlt_five (r := 9) (k := 9 - 4) (by omega) (by omega) hτM
      (le_refl (fixAlt τM)) (β := Fin 5) (by simp) ψ5 ya_g₀
    rw [ya_g₀_supp] at h
    exact h
  have hσS : σ.support ⊆ τM.supportᶜ := mem_fixAlt.mp (ψ5 ya_g₀).2
  have hS5 : 4 < (τM.supportᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hker : ∀ g ∈ fixA M e₀ r, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g) := by
    intro g hg hgK
    have h1 := hρ.eq_one_of_mem_coreActionKernel (by omega) hgK
    have h2 := hρ.apply_of_mem (by omega) ⟨g, hArM hg⟩
    have h3 : θ ((⟨g, hArM hg⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
      apply Subtype.ext
      rw [← h2]
      exact h1
    exact ya_odd_orderOf_of_mem (ya_odd_card_core M) (ya_mem_core_of_theta_eq_one h3)
  have hρx₀ : ρ ⟨x₀, le_normalizer (hArM hx₀A)⟩ = σ := by
    rw [hρ.apply_of_mem (by omega) ⟨x₀, hArM hx₀A⟩, hx₀]
  obtain ⟨k, -, hkk, hρk⟩ := hρ.exists_pow_involution (H := fixA M e₀ r)
    (hArM.trans le_normalizer) hker hx₀A (by rw [hρx₀]; exact hσ2)
  refine ⟨τM.supportᶜ, σ, x₀ ^ k, pow_mem hx₀A k, hS5, hσ2, hσ4, hσS, hkk, hρk.trans hρx₀, ?_⟩
  intro b hb
  have hbF : b ∈ fixAlt τM := by
    rw [mem_fixAlt]
    intro ω hω
    by_contra hωF
    exact (Perm.mem_support.mp hω) (hb ω hωF)
  obtain ⟨g, hg⟩ := ψ5.surjective ⟨b, hbF⟩
  obtain ⟨x, hx, hxg⟩ := hlift g
  refine ⟨x, hx, ?_⟩
  rw [hxg, hg]

end MSide

section Exotic

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X} {N₁ : Subgroup X}

theorem Setting.exists_a9_action (hs : Setting t J n e E D M) (hn : n = 9)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hP : PumpData M e₀ r N₁) (hfix : conjBy N₁ e₀ = N₁) :
    ∃ G : Subgroup X, G ≤ normalizer (N₁ : Set X) ∧
      ∃ φ : ↥G →* alternatingGroup (Fin 9), Function.Surjective φ ∧
        ∀ g : ↥G, (g : X) ∈ UnbalancedLayer.coreActionKernel N₁ → φ g = 1 := by
  classical
  subst hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  obtain ⟨S₀, σ, a, haA, hS5, hσ2, hσ4, hσS, ha2, hρa, hlift⟩ :=
    ya_exists_involution_fixA hs hd he₀H hρ
  have hArM : fixA M e₀ r ≤ M := ya_fixA_le M e₀ r
  have haM : a ∈ M := hArM haA
  have haN : a ∈ normalizer (M : Set X) := le_normalizer haM
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h1 : σ = 1 := by rw [← hρa]; exact map_one ρ
    rw [h1, Perm.support_one, Finset.card_empty] at hσ4
    exact absurd hσ4 (by decide)
  have ha2' : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have haP : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2', pow_one])
  obtain ⟨⟨χr⟩, ⟨hArle, -⟩, -⟩ := pump_holds X t J 9 e E D M hs e₀ F DF r hd he₀H
  let χ5 : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin 5) := χr
  have hAN : fixA M e₀ r ≤ N₁ := by
    have h := hP.cover
    rwa [hfix, sup_idem] at h
  have haK : a ∉ UnbalancedLayer.coreActionKernel N₁ := fun h =>
    ya_false_of_involution_mem_core (ya_mem_core_of_mem_coreActionKernel hAN χ5 haA h) ha2 ha1
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hrN : r ∈ normalizer (M : Set X) := hrK.1
  have hρr : ρ ⟨r, hrN⟩ = 1 := hρ.eq_one_of_mem_coreActionKernel (by omega) hrK
  have har : a * r = r * a := mem_centralizer_singleton_iff.mp (hArle haA).1
  set C : Subgroup X := M ⊓ centralizer ({a} : Set X) ⊓ centralizer ({r} : Set X) with hCdef
  have hCN : C ≤ normalizer (N₁ : Set X) := by
    intro k hk
    have hkr : k ∈ centralizer ({r} : Set X) := hk.2
    have hka : k ∈ centralizer ({a} : Set X) := hk.1.2
    obtain ⟨hN₂Y, hN₂pc⟩ := isPComponent_conj hP.le hP.pc hkr
    by_cases hconj : conjBy N₁ k = N₁
    · exact mem_normalizer_iff_map_conj_eq.mpr hconj
    · exfalso
      have hK := GSThmB.B5a.le_coreActionKernel_of_ne hP.le hN₂Y hP.pc hN₂pc (Ne.symm hconj)
      have haN₂ : a ∈ conjBy N₁ k := by
        refine ⟨a, hAN haA, ?_⟩
        have h1 : k * a = a * k := mem_centralizer_singleton_iff.mp hka
        change k * a * k⁻¹ = a
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
      exact haK (hK haN₂)
  set G : Subgroup X := fixA M e₀ r ⊔ C with hGdef
  have hGM : G ≤ M := sup_le hArM (inf_le_left.trans inf_le_left)
  have hGN : G ≤ normalizer (N₁ : Set X) := sup_le (hAN.trans le_normalizer) hCN
  let π : ↥M →* alternatingGroup (Fin 9) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥M))
  let φ : ↥G →* alternatingGroup (Fin 9) := π.comp (Subgroup.inclusion hGM)
  have hφ : ∀ (x : X) (hx : x ∈ G),
      φ ⟨x, hx⟩ = θ ((⟨x, hGM hx⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := fun _ _ => rfl
  have hsurj : Function.Surjective φ := by
    have htop : φ.range = ⊤ := by
      refine alt_sup_centralizer_eq_top (m := 9) (S := S₀) (σ := σ) (by decide) hσ2 hσ4 hσS hS5
        ?_ ?_
      · intro b hb
        obtain ⟨x, hx, hxb⟩ := hlift b hb
        exact ⟨⟨x, mem_sup_left hx⟩, by rw [hφ]; exact hxb⟩
      · intro b hb
        have hbσ : (b : Perm (Fin 9)) * ρ ⟨a, haN⟩ = ρ ⟨a, haN⟩ * b := by rw [hρa]; exact hb
        have hbr : (b : Perm (Fin 9)) * ρ ⟨r, hrN⟩ = ρ ⟨r, hrN⟩ * b := by
          rw [hρr, mul_one, one_mul]
        obtain ⟨x, hxa, hxr, hxb⟩ :=
          hρ.exists_lift_of_two_two haN haP hrN hd.r2 har hbσ hbr
        have hxG : (x : X) ∈ G := mem_sup_right ⟨⟨x.2, hxa⟩, hxr⟩
        exact ⟨⟨x, hxG⟩, by rw [hφ]; exact hxb⟩
    exact MonoidHom.range_eq_top.mp htop
  refine ⟨G, hGN, φ, hsurj, ?_⟩
  intro g hgK
  set K₁ := UnbalancedLayer.coreActionKernel N₁ with hK₁def
  have hnorm : ∀ y ∈ normalizer (N₁ : Set X), ∀ z ∈ K₁, y * z * y⁻¹ ∈ K₁ := fun y hy z hz =>
    (mem_normalizer_iff.mp (mem_normalizer_coreActionKernel hy) z).mp hz
  have hKn : (K₁.subgroupOf G).Normal := ⟨fun k hk g => hnorm g (hGN g.2) k hk⟩
  haveI hTn : ((K₁.subgroupOf G).map φ).Normal := hKn.map φ hsurj
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K₁.subgroupOf G).map φ) with hT | hT
  · have h1 : φ g ∈ (K₁.subgroupOf G).map φ := ⟨g, hgK, rfl⟩
    rw [hT] at h1
    exact Subgroup.mem_bot.mp h1
  · exfalso
    have haG : a ∈ G := mem_sup_left haA
    have h1 : φ ⟨a, haG⟩ ∈ (K₁.subgroupOf G).map φ := by rw [hT]; exact Subgroup.mem_top _
    obtain ⟨g', hg'K, hg'⟩ := h1
    set o : ↥G := (⟨a, haG⟩ : ↥G)⁻¹ * g' with hodef
    have hφo : φ o = 1 := by rw [hodef, map_mul, map_inv, hg', inv_mul_cancel]
    have hoO : (o : X) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
      have h2 : θ ((⟨(o : X), hGM o.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := hφo
      exact ya_mem_core_of_theta_eq_one h2
    have hogo : (g' : X) = a * (o : X) := by
      rw [hodef]
      simp
    exact haK (ya_mem_of_mul_odd ha2 (hnorm a (hGN haG) _ hg'K) hg'K hogo
      (ya_odd_orderOf_of_mem (ya_odd_card_core M) hoO))

end Exotic

end CFSG.ComponentClassification.SolMax.SwapP2
