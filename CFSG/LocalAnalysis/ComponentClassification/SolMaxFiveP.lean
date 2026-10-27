module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveO
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveM

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem swap_apply_commute {n : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1) (x : Fin n) :
    swap x (σ x) * σ = σ * swap x (σ x) := by
  have h1 : σ (σ x) = x := by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  rw [Equiv.mul_swap_eq_swap_mul σ x (σ x), h1, swap_comm (σ x) x]

theorem apply_mem_support_iff_of_commute {n : ℕ} {σ π : Perm (Fin n)} (h : π * σ = σ * π)
    (v : Fin n) : π v ∈ σ.support ↔ v ∈ σ.support := by
  rw [Perm.mem_support, Perm.mem_support]
  have h1 : σ (π v) = π (σ v) := by rw [← Perm.mul_apply, ← h, Perm.mul_apply]
  rw [h1]
  exact π.injective.ne_iff

variable {X : Type} [Group X]

theorem IsPermAction.apply_eq_coreImage_of_acts {J : Subgroup X} {n : ℕ}
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction θ ρJ) (hn : 4 ≤ n)
    {g e : X} (hgN : g ∈ normalizer (J : Set X)) (he : e ∈ J)
    (hge : g * e⁻¹ ∈ UnbalancedLayer.coreActionKernel J) : ρJ ⟨g, hgN⟩ = coreImage θ he := by
  have h1 := hρJ.eq_one_of_mem_coreActionKernel hn hge
  have h2 : (⟨g, hgN⟩ : ↥(normalizer (J : Set X))) =
      ⟨g * e⁻¹, hge.1⟩ * ⟨e, le_normalizer he⟩ := Subtype.ext (by simp)
  rw [h2, map_mul, h1, one_mul]
  exact hρJ.apply_of_mem hn ⟨e, he⟩

theorem mem_cak_of_forall_commute {L : Subgroup X} {g : X}
    (h : ∀ z ∈ L, g * z = z * g) : g ∈ UnbalancedLayer.coreActionKernel L := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [h z hz, mul_inv_cancel_right]
      exact hz
    · intro hz
      have h1 : g * (g * z * g⁻¹) = (g * z * g⁻¹) * g := h _ hz
      have h2 : g * z * g⁻¹ = z := by
        have h3 : g * (g * z * g⁻¹) = g * z := by rw [h1]; group
        exact mul_left_cancel h3
      rw [← h2]
      exact hz
  · have h1 : j⁻¹ * g⁻¹ * j * g = 1 := by
      have h2 := h j hj
      calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
        _ = j⁻¹ * g⁻¹ * (g * j) := by rw [h2]
        _ = 1 := by group
    rw [h1]
    exact one_mem _

theorem exists_odd_of_four [Finite X] {J Jc M E₀ : Subgroup X} {t c e₀ a : X}
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin 9)} (hρJ : IsPermAction θ ρJ)
    (he₀ : e₀ ∈ J) (hcN : c ∈ normalizer (J : Set X))
    (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) (hJCt : J ≤ centralizer ({t} : Set X))
    (hCtN : centralizer ({t} : Set X) ≤ normalizer (J : Set X))
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤)
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx)
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) (hJcM : Jc ≤ M)
    (hJcperf : ⁅Jc, Jc⁆ = Jc) (hJcq : Nontrivial (↥Jc ⧸ pPrimeCore 2 ↥Jc))
    {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 7)} (hρ : IsPermAction θM ρ)
    {τ : Perm (Fin 7)} (hτ5 : 7 - τ.support.card = 5)
    (hJcτ : ∀ (z : X) (hz : z ∈ Jc), ρ ⟨z, le_normalizer (hJcM hz)⟩ ∈
      (fixAlt τ).map (alternatingGroup (Fin 7)).subtype)
    (hsurj : ∀ b ∈ fixAlt τ, ∃ (z : X) (hz : z ∈ Jc),
      ρ ⟨z, le_normalizer (hJcM hz)⟩ = (b : Perm (Fin 7)))
    (hO : ∀ (z : X) (hz : z ∈ Jc), z ∈ coreNOf Jc → ρ ⟨z, le_normalizer (hJcM hz)⟩ = 1)
    (htM : t ∈ normalizer (M : Set X)) (ht2 : t * t = 1)
    (htJc : Jc ≤ centralizer ({t} : Set X)) (hρt1 : ρ ⟨t, htM⟩ ≠ 1) (haJc : a ∈ Jc)
    (ha2 : a * a = 1) (hat : a * t = t * a)
    (haM : a ∈ normalizer (M : Set X)) (h3 : (ρ ⟨a, haM⟩).supportᶜ.card = 3)
    (hE₀ : E₀ ≤ J ⊓ centralizer ({c} : Set X) ⊓ centralizer ({a} : Set X))
    (hE₀k : Nonempty (E₀ ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hE₀s : ∀ (x : X) (hx : x ∈ J), x ∈ E₀ →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).support) :
    ∃ g : X, g ∈ M ∧ g * t = t * g ∧ g * a = a * g ∧
      ∃ hgJ : g ∈ normalizer (J : Set X), Perm.sign (ρJ ⟨g, hgJ⟩) = -1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcC : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hJcN : Jc ≤ normalizer (M : Set X) := fun z hz => le_normalizer (hJcM hz)
  have hE₀J : E₀ ≤ J := hE₀.trans (inf_le_left.trans inf_le_left)
  have hE₀c : E₀ ≤ centralizer ({c} : Set X) := hE₀.trans (inf_le_left.trans inf_le_right)
  have hE₀a : E₀ ≤ centralizer ({a} : Set X) := hE₀.trans inf_le_right
  have hE₀t : E₀ ≤ centralizer ({t} : Set X) := hE₀J.trans hJCt
  have haJ : a ∈ J := hJcJ' haJc
  have hρJc : ρJ ⟨c, hcN⟩ = coreImage θ he₀ :=
    hρJ.apply_eq_coreImage_of_acts (by norm_num) hcN he₀ hce
  have hρJa : ρJ ⟨a, le_normalizer haJ⟩ = coreImage θ haJ :=
    hρJ.apply_of_mem (by norm_num) ⟨a, haJ⟩
  obtain ⟨haJ', haF'⟩ := hsubP a haJc
  have haF : (coreImage θ haJ).support ⊆ (coreImage θ he₀).supportᶜ := haF'
  have hτle : τ.support.card ≤ 7 := by
    have := Finset.card_le_univ τ.support
    rwa [Fintype.card_fin] at this
  have hτ2 : τ.support.card = 2 := by omega
  have hfix : ∀ {w : X} (hwN : w ∈ normalizer (M : Set X)),
      w ∈ UnbalancedLayer.coreActionKernel Jc → (ρ ⟨w, hwN⟩).support ⊆ τ.support := by
    intro w hwN hwK v hv
    by_contra hvτ
    exact (Perm.mem_support.mp hv)
      (apply_eq_of_mem_cak_of_onto hJcN (by omega) hsurj hO hwN hwK hvτ)
  have htK : t ∈ UnbalancedLayer.coreActionKernel Jc := mem_cak_of_forall_commute
    fun z hz => (mem_centralizer_singleton_iff.mp (htJc hz)).symm
  have hρts := hfix htM htK
  have hE₀K : ∀ e ∈ E₀, e ∈ normalizer (Jc : Set X) ∧
      e ∈ UnbalancedLayer.coreActionKernel Jc := by
    intro e he
    refine mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv hsubP χ hχ
      (le_normalizer (hE₀J he)) (mem_centralizer_singleton_iff.mp (hE₀c he)) ?_
    rw [hρJ.apply_of_mem (by norm_num) ⟨e, hE₀J he⟩]
    exact hE₀s e (hE₀J he) he
  have hE₀N : E₀ ≤ normalizer (M : Set X) := fun e he =>
    mem_normalizer_of_mem_normalizer_Jc hMC hMpc hJcM hJcperf hJcq (hE₀c he) (hE₀K e he).1
  have hρe : ∀ (e : X) (he : e ∈ E₀), ρ ⟨e, hE₀N he⟩ = 1 ∨ ρ ⟨e, hE₀N he⟩ = ρ ⟨t, htM⟩ := by
    intro e he
    by_cases h1 : ρ ⟨e, hE₀N he⟩ = 1
    · exact Or.inl h1
    · exact Or.inr (eq_of_support_subset_pair hτ2 (hfix _ (hE₀K e he).2) hρts h1 hρt1)
  obtain ⟨hE4, hE2⟩ := card_sq_of_klein hE₀k
  obtain ⟨V, hV4, hVsq, hVsupp, hVmem⟩ := exists_klein_on hs4
  let fE : ↥E₀ →* alternatingGroup (Fin 9) :=
    (θ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))).comp (inclusion hE₀J)
  have hfE : ∀ e : ↥E₀, ((fE e : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
      coreImage θ (hE₀J e.2) := fun _ => rfl
  have hfEinj : Function.Injective fE := by
    rw [injective_iff_map_eq_one]
    intro e he1
    have h1 : θ ((inclusion hE₀J e : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := he1
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    have hodd : Odd (orderOf (e : X)) := by
      have h2 := orderOf_dvd_natCard (⟨_, h1⟩ : ↥(pPrimeCore 2 ↥J))
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h2
      exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h2
    have h2 : orderOf (e : X) ∣ 2 := orderOf_dvd_of_pow_eq_one (hE2 _ e.2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact Subtype.ext (orderOf_eq_one_iff.mp h)
    · rw [h] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)
  have hfEV : fE.range ≤ V := by
    rintro _ ⟨e, rfl⟩
    refine hVmem _ (Subtype.ext ?_) fun ω hω => ?_
    · change ((fE e * fE e : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 1
      rw [← map_mul]
      have : e * e = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact hE2 _ e.2)
      rw [this, map_one, Subgroup.coe_one]
    · rw [hfE]
      by_contra hc
      exact hω (hE₀s _ (hE₀J e.2) e.2 (Perm.mem_support.mpr hc))
  have hfEeq : fE.range = V := by
    refine Subgroup.eq_of_le_of_card_ge hfEV ?_
    rw [hV4, ← hE4]
    exact (Nat.card_congr (MonoidHom.ofInjective hfEinj).toEquiv).le
  have hEV : ∀ u : alternatingGroup (Fin 9), u * u = 1 →
      (∀ ω ∉ (coreImage θ he₀).support, (u : Perm (Fin 9)) ω = ω) →
      ∃ (e : X) (he : e ∈ E₀), coreImage θ (hE₀J he) = (u : Perm (Fin 9)) := by
    intro u hu2 huD
    have h1 : u ∈ fE.range := by rw [hfEeq]; exact hVmem u hu2 huD
    obtain ⟨e, he⟩ := h1
    exact ⟨e, e.2, by rw [← hfE e, he]⟩
  have hρa2 : ρ ⟨a, haM⟩ * ρ ⟨a, haM⟩ = 1 := by
    rw [← map_mul]
    convert map_one ρ
    exact Subtype.ext ha2
  have hasupp : (ρ ⟨a, haM⟩).support.card = 4 := by
    have h1 : (ρ ⟨a, haM⟩).supportᶜ.card = 7 - (ρ ⟨a, haM⟩).support.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have h2 : (ρ ⟨a, haM⟩).support.card ≤ 7 := by
      have := Finset.card_le_univ (ρ ⟨a, haM⟩).support
      rwa [Fintype.card_fin] at this
    omega
  obtain ⟨x₁, hx₁⟩ : (ρ ⟨a, haM⟩).support.Nonempty := by
    rw [← Finset.card_pos, hasupp]
    norm_num
  set κ : Perm (Fin 7) := swap x₁ (ρ ⟨a, haM⟩ x₁) with hκdef
  have hx₁ne : x₁ ≠ ρ ⟨a, haM⟩ x₁ := fun h => (Perm.mem_support.mp hx₁) h.symm
  have hκsign : Perm.sign κ = -1 := Perm.sign_swap hx₁ne
  have hκa : κ * ρ ⟨a, haM⟩ = ρ ⟨a, haM⟩ * κ := swap_apply_commute hρa2 x₁
  obtain ⟨ba, hba, hbae⟩ := hJcτ a haJc
  have hasτ : (ρ ⟨a, haM⟩).support ⊆ τ.supportᶜ := by
    have h1 : ρ ⟨a, haM⟩ = (ba : Perm (Fin 7)) := hbae.symm
    rw [h1]
    exact mem_fixAlt.mp hba
  have hκsupp : κ.support ⊆ τ.supportᶜ := by
    rw [hκdef, Perm.support_swap hx₁ne]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h
    · rw [h]
      exact hasτ hx₁
    · rw [h]
      exact hasτ (Perm.apply_mem_support.mpr hx₁)
  have hdisj : ∀ {σ : Perm (Fin 7)}, σ.support ⊆ τ.supportᶜ → σ * ρ ⟨t, htM⟩ = ρ ⟨t, htM⟩ * σ := by
    intro σ hσ
    refine (Perm.Disjoint.commute ?_).eq
    rw [Perm.disjoint_iff_disjoint_support]
    exact Finset.disjoint_of_subset_left hσ
      (Finset.disjoint_of_subset_right hρts disjoint_compl_left)
  have hκt := hdisj hκsupp
  have hat' := hdisj hasτ
  have hρtsign : Perm.sign (ρ ⟨t, htM⟩) = -1 := by
    have h1 : (ρ ⟨t, htM⟩).support.card = 2 := by
      have h2 := Finset.card_le_card hρts
      have h0 : (ρ ⟨t, htM⟩).support.card ≠ 0 := fun h =>
        hρt1 (Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h))
      have h1' := Perm.card_support_ne_one (ρ ⟨t, htM⟩)
      omega
    exact (Perm.card_support_eq_two.mp h1).sign_eq
  have hbA : κ * ρ ⟨t, htM⟩ ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, hκsign, hρtsign, Int.units_mul_self]
  set b : alternatingGroup (Fin 7) := ⟨κ * ρ ⟨t, htM⟩, hbA⟩ with hbdef
  have hbt : (b : Perm (Fin 7)) * ρ ⟨t, htM⟩ = ρ ⟨t, htM⟩ * b := by
    change κ * ρ ⟨t, htM⟩ * ρ ⟨t, htM⟩ = ρ ⟨t, htM⟩ * (κ * ρ ⟨t, htM⟩)
    rw [← mul_assoc, ← hκt]
  have hba' : (b : Perm (Fin 7)) * ρ ⟨a, haM⟩ = ρ ⟨a, haM⟩ * b := by
    change κ * ρ ⟨t, htM⟩ * ρ ⟨a, haM⟩ = ρ ⟨a, haM⟩ * (κ * ρ ⟨t, htM⟩)
    rw [mul_assoc, ← hat', ← mul_assoc, hκa, mul_assoc]
  set B : Subgroup X := E₀ ⊔ zpowers t ⊔ zpowers a with hBdef
  have hBN : B ≤ normalizer (M : Set X) :=
    sup_le (sup_le hE₀N (zpowers_le.mpr htM)) (zpowers_le.mpr haM)
  have hE₀2 : IsPGroup 2 E₀ := IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num)
  have hB1 : IsPGroup 2 (E₀ ⊔ zpowers t : Subgroup X) :=
    hE₀2.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self ht2) fun e he =>
      mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp (hE₀t he)).symm
  have hB2 : IsPGroup 2 B := by
    refine hB1.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self ha2) ?_
    refine sup_le (fun e he =>
      mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp (hE₀a he)).symm) ?_
    rw [zpowers_le]
    exact mem_normalizer_zpowers_of_commute hat
  set S : Subgroup X := ((centralizer ({(b : Perm (Fin 7))} : Set (Perm (Fin 7)))).comap ρ).map
    (normalizer (M : Set X)).subtype with hSdef
  have hmemS : ∀ (g : X) (hg : g ∈ normalizer (M : Set X)),
      (b : Perm (Fin 7)) * ρ ⟨g, hg⟩ = ρ ⟨g, hg⟩ * b → g ∈ S := by
    intro g hg h
    exact ⟨⟨g, hg⟩, mem_centralizer_singleton_iff.mpr h.symm, rfl⟩
  have hBS : B ≤ S := by
    refine sup_le (sup_le (fun e he => hmemS e (hE₀N he) ?_) ?_) ?_
    · rcases hρe e he with h | h
      · rw [h, mul_one, one_mul]
      · rw [h]
        exact hbt
    · rw [zpowers_le]
      exact hmemS t htM hbt
    · rw [zpowers_le]
      exact hmemS a haM hba'
  have hbB : ∀ (g : X) (hg : g ∈ B), (b : Perm (Fin 7)) * ρ ⟨g, hBN hg⟩ = ρ ⟨g, hBN hg⟩ * b := by
    intro g hg
    obtain ⟨w, hw, hwg⟩ := hBS hg
    have hw' : ρ w * (b : Perm (Fin 7)) = b * ρ w := mem_centralizer_singleton_iff.mp hw
    have h1 : w = ⟨g, hBN hg⟩ := Subtype.ext hwg
    rw [← h1]
    exact hw'.symm
  obtain ⟨x, hxB, hxb⟩ := hρ.exists_lift_of_isPGroup hBN hB2 hbB
  have hρx : ρ ⟨x, le_normalizer x.2⟩ = κ * ρ ⟨t, htM⟩ := by
    rw [hρ.apply_of_mem (by norm_num) x, hxb, hbdef]
  have hxcomm : ∀ g ∈ B, (x : X) * g = g * x := fun g hg =>
    (mem_centralizer_iff.mp hxB g hg).symm
  have hxt : (x : X) * t = t * x := hxcomm t (mem_sup_left (mem_sup_right (mem_zpowers t)))
  have hxa : (x : X) * a = a * x := hxcomm a (mem_sup_right (mem_zpowers a))
  have hxe : ∀ e ∈ E₀, (x : X) * e = e * x := fun e he => hxcomm e (mem_sup_left (mem_sup_left he))
  have hxc : (x : X) * c = c * x := mem_centralizer_singleton_iff.mp (hMC x.2)
  have hgJ : (x : X) ∈ normalizer (J : Set X) := hCtN (mem_centralizer_singleton_iff.mpr hxt)
  set π := ρJ ⟨x, hgJ⟩ with hπdef
  have hcommJ : ∀ {w : X} (hw : w ∈ normalizer (J : Set X)), (x : X) * w = w * x →
      π * ρJ ⟨w, hw⟩ = ρJ ⟨w, hw⟩ * π := by
    intro w hw hxw
    rw [hπdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxw
  have hπc : π * coreImage θ he₀ = coreImage θ he₀ * π := by
    rw [← hρJc]
    exact hcommJ hcN hxc
  have hπu : ∀ u : alternatingGroup (Fin 9), u * u = 1 →
      (∀ ω ∉ (coreImage θ he₀).support, (u : Perm (Fin 9)) ω = ω) →
      π * (u : Perm (Fin 9)) = (u : Perm (Fin 9)) * π := by
    intro u hu2 huD
    obtain ⟨e, he, heu⟩ := hEV u hu2 huD
    have h1 : ρJ ⟨e, le_normalizer (hE₀J he)⟩ = (u : Perm (Fin 9)) := by
      rw [← heu]
      exact hρJ.apply_of_mem (by norm_num) ⟨e, hE₀J he⟩
    rw [← h1]
    exact hcommJ (le_normalizer (hE₀J he)) (hxe e he)
  have hπD : ∀ v, π v ∈ (coreImage θ he₀).support ↔ v ∈ (coreImage θ he₀).support :=
    apply_mem_support_iff_of_commute hπc
  obtain ⟨σD, σF, hπsplit, hσD1, hσF1, hσD2, hσF2⟩ := exists_split _ hπD
  have hσDsign : Perm.sign σD = 1 := by
    refine sign_eq_one_of_commute_klein hs4 hσD1 fun u hu2 huD => Equiv.ext fun v => ?_
    have huv : ∀ v, v ∈ (coreImage θ he₀).support → (u : Perm (Fin 9)) v ∈
        (coreImage θ he₀).support := by
      intro v hv
      by_contra hc
      have h2 := huD _ hc
      have h3 : (u : Perm (Fin 9)) ((u : Perm (Fin 9)) v) = v := by
        rw [← Perm.mul_apply]
        exact congrArg (fun σ : alternatingGroup (Fin 9) => (σ : Perm (Fin 9)) v) hu2
      rw [h2] at h3
      rw [h3] at hc
      exact hc hv
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hv : v ∈ (coreImage θ he₀).support
    · rw [hσD2 _ (huv v hv), hσD2 v hv]
      have h1 := congrArg (fun σ : Perm (Fin 9) => σ v) (hπu u hu2 huD)
      simpa [Perm.mul_apply] using h1
    · rw [huD v hv, hσD1 v hv, huD v hv]
  have hσFsign : Perm.sign σF = -1 := by
    rcases Int.units_eq_one_or (Perm.sign σF) with h | h
    swap
    · exact h
    exfalso
    have hσFfix : (⟨σF, h⟩ : alternatingGroup (Fin 9)) ∈ fixAlt (coreImage θ he₀) := by
      rw [mem_fixAlt]
      intro v hv
      rw [Finset.mem_compl]
      intro hvD
      exact (Perm.mem_support.mp hv) (hσF1 v hvD)
    obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv (coreImage θ he₀)
    obtain ⟨q, hq⟩ := χ.surjective (φ.symm ⟨_, hσFfix⟩)
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hl : coreImage θ (hJcJ' l.2) = σF := by
      rw [← hχ l (hJcJ' l.2), hq]
      have h2 := hφ (φ.symm ⟨_, hσFfix⟩)
      rw [MulEquiv.apply_symm_apply] at h2
      exact h2.symm
    have hlJ : (l : X) ∈ J := hJcJ' l.2
    have hwN : (x : X) * (l : X)⁻¹ ∈ normalizer (J : Set X) :=
      mul_mem hgJ (inv_mem (le_normalizer hlJ))
    have hwc : (x : X) * (l : X)⁻¹ * c = c * ((x : X) * (l : X)⁻¹) := by
      have hlc : (l : X) * c = c * l := mem_centralizer_singleton_iff.mp (hJcC l.2)
      have hlc' : (l : X)⁻¹ * c = c * (l : X)⁻¹ := by
        calc (l : X)⁻¹ * c = (l : X)⁻¹ * (c * l) * (l : X)⁻¹ := by group
          _ = (l : X)⁻¹ * (l * c) * (l : X)⁻¹ := by rw [hlc]
          _ = c * (l : X)⁻¹ := by group
      calc (x : X) * (l : X)⁻¹ * c = (x : X) * ((l : X)⁻¹ * c) := by group
        _ = (x : X) * (c * (l : X)⁻¹) := by rw [hlc']
        _ = ((x : X) * c) * (l : X)⁻¹ := by group
        _ = (c * x) * (l : X)⁻¹ := by rw [hxc]
        _ = c * ((x : X) * (l : X)⁻¹) := by group
    have hρJw : ρJ ⟨_, hwN⟩ = σD := by
      have h1 : (⟨(x : X) * (l : X)⁻¹, hwN⟩ : ↥(normalizer (J : Set X))) =
          ⟨x, hgJ⟩ * (⟨l, le_normalizer hlJ⟩ : ↥(normalizer (J : Set X)))⁻¹ := rfl
      rw [h1, map_mul, map_inv, ← hπdef, hρJ.apply_of_mem (by norm_num) ⟨l, hlJ⟩]
      change π * (coreImage θ hlJ)⁻¹ = σD
      rw [hl, hπsplit]
      group
    have hwD : (ρJ ⟨_, hwN⟩).support ⊆ (coreImage θ he₀).support := by
      rw [hρJw]
      intro v hv
      by_contra hvD
      exact (Perm.mem_support.mp hv) (hσD1 v hvD)
    obtain ⟨-, hwK⟩ := mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv hsubP χ hχ
      hwN hwc hwD
    have hwM : (x : X) * (l : X)⁻¹ ∈ normalizer (M : Set X) :=
      mul_mem (le_normalizer x.2) (inv_mem (hJcN l.2))
    have hwfix : ∀ v ∉ τ.support, ρ ⟨_, hwM⟩ v = v := fun v hv =>
      apply_eq_of_mem_cak_of_onto hJcN (by omega) hsurj hO hwM hwK hv
    have hρw : ρ ⟨_, hwM⟩ = κ * ρ ⟨t, htM⟩ * (ρ ⟨l, hJcN l.2⟩)⁻¹ := by
      have h1 : (⟨(x : X) * (l : X)⁻¹, hwM⟩ : ↥(normalizer (M : Set X))) =
          ⟨x, le_normalizer x.2⟩ * (⟨l, hJcN l.2⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
      rw [h1, map_mul, map_inv, hρx]
    obtain ⟨bl, hbl, hble⟩ := hJcτ l l.2
    have hlsupp : (ρ ⟨l, hJcN l.2⟩).support ⊆ τ.supportᶜ := by
      have h1 : ρ ⟨l, hJcN l.2⟩ = (bl : Perm (Fin 7)) := hble.symm
      rw [h1]
      exact mem_fixAlt.mp hbl
    have hκl : κ = ρ ⟨l, hJcN l.2⟩ := by
      refine Equiv.ext fun v => ?_
      by_cases hv : v ∈ τ.support
      · have h1 : v ∉ κ.support := fun h' => (Finset.mem_compl.mp (hκsupp h')) hv
        have h2 : v ∉ (ρ ⟨l, hJcN l.2⟩).support := fun h' =>
          (Finset.mem_compl.mp (hlsupp h')) hv
        rw [Perm.notMem_support.mp h1, Perm.notMem_support.mp h2]
      · have hu : ρ ⟨l, hJcN l.2⟩ v ∉ τ.support := by
          intro hu
          have h1 : ρ ⟨l, hJcN l.2⟩ (ρ ⟨l, hJcN l.2⟩ v) = ρ ⟨l, hJcN l.2⟩ v := by
            by_contra h'
            exact (Finset.mem_compl.mp (hlsupp (Perm.mem_support.mpr h'))) hu
          have h2 := (ρ ⟨l, hJcN l.2⟩).injective h1
          rw [h2] at hu
          exact hv hu
        have h1 := hwfix _ hu
        have h0 : (ρ ⟨l, hJcN l.2⟩)⁻¹ (ρ ⟨l, hJcN l.2⟩ v) = v := Perm.inv_eq_iff_eq.mpr rfl
        rw [hρw, Perm.mul_apply, Perm.mul_apply, h0] at h1
        have h3 : ρ ⟨t, htM⟩ v = v := by
          by_contra h'
          exact hv (hρts (Perm.mem_support.mpr h'))
        rw [h3] at h1
        exact h1
    have hlA : Perm.sign (ρ ⟨l, hJcN l.2⟩) = 1 := by
      have h1 : ρ ⟨l, hJcN l.2⟩ = (bl : Perm (Fin 7)) := hble.symm
      rw [h1]
      exact Perm.mem_alternatingGroup.mp bl.2
    rw [← hκl, hκsign] at hlA
    exact absurd hlA (by decide)
  refine ⟨x, x.2, hxt, hxa, hgJ, ?_⟩
  rw [← hπdef, hπsplit, Perm.sign_mul, hσDsign, hσFsign, one_mul]

end CFSG.ComponentClassification.SolMax
