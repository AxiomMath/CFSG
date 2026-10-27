module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32F

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

section perm

variable {n : ℕ}

theorem apply_eq_of_commute_fixAlt {τ y : Perm (Fin n)} (h4 : 4 ≤ n - τ.support.card)
    (hc : ∀ b ∈ fixAlt τ, y * (b : Perm (Fin n)) = (b : Perm (Fin n)) * y) {x : Fin n}
    (hx : x ∉ τ.support) : y x = x := by
  classical
  · have hcard : 2 < ((τ.supportᶜ).erase x).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_compl.mpr hx), Finset.card_compl,
        Fintype.card_fin]
      omega
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp hcard
    rw [Finset.mem_erase, Finset.mem_compl] at ha hb hd
    have hcyc : ∀ u v : Fin n, u ≠ x → v ≠ x → u ≠ v → u ∉ τ.support → v ∉ τ.support →
        y x = x ∨ y x = u ∨ y x = v := by
      intro u v hux hvx huv hu hv
      have hnd : [x, u, v].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
          not_or, List.nodup_nil, and_true, not_false_eq_true]
        exact ⟨⟨hux.symm, hvx.symm⟩, huv⟩
      set c : Perm (Fin n) := swap x u * swap u v with hcdef
      have hcs : c.support = {x, u, v} := Perm.support_swap_mul_swap hnd
      have hcA : c ∈ alternatingGroup (Fin n) := by
        rw [Perm.mem_alternatingGroup, hcdef, Perm.sign_mul, Perm.sign_swap hux.symm,
          Perm.sign_swap huv]
        rfl
      have hcF : (⟨c, hcA⟩ : alternatingGroup (Fin n)) ∈ fixAlt τ := by
        rw [mem_fixAlt]
        change c.support ⊆ τ.supportᶜ
        rw [hcs]
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [Finset.mem_compl]
        rcases hz with rfl | rfl | rfl
        · exact hx
        · exact hu
        · exact hv
      have hyc := hc _ hcF
      change y * c = c * y at hyc
      have hxc : x ∈ c.support := by rw [hcs]; simp
      have hyxc : y x ∈ c.support := by
        rw [Perm.mem_support] at hxc ⊢
        intro h
        apply hxc
        apply y.injective
        rw [← Perm.mul_apply, hyc, Perm.mul_apply, h]
      rw [hcs] at hyxc
      simpa using hyxc
    rcases hcyc a b ha.1 hb.1 hab ha.2 hb.2 with h1 | h1 | h1
    · exact h1
    · rcases hcyc b d hb.1 hd.1 hbd hb.2 hd.2 with h2 | h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hab
      · exact absurd (h1.symm.trans h2) had
    · rcases hcyc a d ha.1 hd.1 had ha.2 hd.2 with h2 | h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) (Ne.symm hab)
      · exact absurd (h1.symm.trans h2) hbd


end perm

variable {X : Type} [Group X]

theorem exists_image_equiv [Finite X] {M Je : Subgroup X} {r k : ℕ} (hk : 7 ≤ k)
    (hkr : k ≤ r) (hr6 : r ≠ 6) (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ)
    (hJeN : Je ≤ normalizer (M : Set X)) (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Je = ⊤)
    (hJeperf : ⁅Je, Je⁆ = Je) {β : Type*} [Fintype β] [DecidableEq β] (hβ : Fintype.card β = k)
    (χ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup β)
    (hne : ∃ x : ↥Je, ρ ⟨x, hJeN x.2⟩ ≠ 1)
    (hcase : r = k ∨ ∃ t : X, t ∈ normalizer (M : Set X) ∧ t * t = 1 ∧ Je ≤ M ∧
      Je ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (Je.subgroupOf (M ⊓ centralizer ({t} : Set X)))) :
    ∃ τ : Perm (Fin r), r - τ.support.card = k ∧
      ∃ ψ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* fixAlt τ, ∀ x : ↥Je,
        (((ψ (x : ↥Je ⧸ pPrimeCore 2 ↥Je) : fixAlt τ) : alternatingGroup (Fin r)) :
          Perm (Fin r)) = ρ ⟨x, hJeN x.2⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eJe : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup (Fin k) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨x₀, hx₀⟩ := hne
  rcases hcase with hrk | ⟨t, htM, htt, hJeM, hJeC, hJepc⟩
  · subst hrk
    have hA : ∀ x : ↥Je, ρ (inclusion hJeN x) ∈ alternatingGroup (Fin r) := by
      intro x
      have hperf : Group.IsPerfect ↥Je := (Subgroup.isPerfect_iff).mpr hJeperf
      have h1 := Abelianization.commutator_subset_ker
        (Perm.sign.comp (ρ.comp (inclusion hJeN)))
      rw [Group.IsPerfect.commutator_eq_top] at h1
      exact h1 (mem_top x)
    let φ : ↥Je →* alternatingGroup (Fin r) :=
      (ρ.comp (inclusion hJeN)).codRestrict (alternatingGroup (Fin r)) hA
    have hφ : φ x₀ ≠ 1 := by
      intro h
      apply hx₀
      exact congrArg Subtype.val h
    have hQ : ∀ x, φ x ∈ fixAlt (1 : Perm (Fin r)) := by
      intro x
      rw [mem_fixAlt]
      simp
    have hQc : Nat.card (fixAlt (1 : Perm (Fin r))) ≤ r.factorial / 2 := by
      rw [card_fixAlt (by simp; omega)]
      simp
    obtain ⟨ψ, hψ⟩ := exists_coreQuot_equiv_of_hom hres (by omega) eJe φ ⟨x₀, hφ⟩ hQ hQc
    exact ⟨1, by simp, ψ, fun x => by rw [hψ x]; rfl⟩
  · set π : ↥M →* alternatingGroup (Fin r) :=
      θM.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥M)) with hπdef
    obtain ⟨τ, hP, hτk⟩ := exists_perm_of_fixed_component htM htt hJeM hJeC hJepc (by omega)
      (by omega) hr6 eJe θM
    let φ : ↥Je →* alternatingGroup (Fin r) := π.comp (inclusion hJeM)
    have hρin : ∀ x : ↥Je, ρ ⟨x, hJeN x.2⟩ = ((φ x : alternatingGroup (Fin r)) : Perm (Fin r)) :=
      fun x => hρ.apply_of_mem (by omega) (inclusion hJeM x)
    have hφ : φ x₀ ≠ 1 := by
      intro h
      apply hx₀
      rw [hρin, h]
      rfl
    have hQ : ∀ x, φ x ∈ fixAlt τ := fun x => hP ⟨inclusion hJeM x, x.2, rfl⟩
    have hQc : Nat.card (fixAlt τ) ≤ k.factorial / 2 := by
      rw [card_fixAlt (by omega), hτk]
    obtain ⟨ψ, hψ⟩ := exists_coreQuot_equiv_of_hom hres (by omega) eJe φ ⟨x₀, hφ⟩ hQ hQc
    exact ⟨τ, hτk, ψ, fun x => by rw [hψ x, hρin]⟩

theorem card_support_le_of_cak [Finite X] {M Je : Subgroup X} {r k : ℕ} (hk : 7 ≤ k)
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}
    (hJeN : Je ≤ normalizer (M : Set X)) {β : Type*} [Fintype β] [DecidableEq β]
    (hβ : Fintype.card β = k) (χ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup β)
    {τ : Perm (Fin r)} (hτk : r - τ.support.card = k)
    (ψ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* fixAlt τ)
    (hψ : ∀ x : ↥Je, (((ψ (x : ↥Je ⧸ pPrimeCore 2 ↥Je) : fixAlt τ) :
      alternatingGroup (Fin r)) : Perm (Fin r)) = ρ ⟨x, hJeN x.2⟩)
    {a : X} (ha : a ∈ normalizer (M : Set X)) {j : X} (hj : j ∈ Je)
    (haj : a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel Je) :
    (ρ ⟨a, ha⟩).support.card ≤ (r - k) +
      ((χ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je) : alternatingGroup β) :
        Perm β).support.card := by
  classical
  set c := a * j⁻¹ with hcdef
  have hcN : c ∈ normalizer (M : Set X) := mul_mem ha (inv_mem (hJeN hj))
  set g := ρ ⟨c, hcN⟩ with hgdef
  have hρO : ∀ o : ↥Je, o ∈ pPrimeCore 2 ↥Je → ρ ⟨o, hJeN o.2⟩ = 1 := by
    intro o ho
    rw [← hψ o, (QuotientGroup.eq_one_iff o).mpr ho, map_one]
    rfl
  have hgx : ∀ x : ↥Je, g * ρ ⟨x, hJeN x.2⟩ = ρ ⟨x, hJeN x.2⟩ * g := by
    intro x
    have hcinv := inv_mem haj
    obtain ⟨hcJ, hcK⟩ := UnbalancedLayer.mem_coreActionKernel.mp hcinv
    obtain ⟨o, ho, hoeq⟩ := hcK x x.2
    rw [inv_inv] at hoeq
    have hoeq' : (o : X) = (x : X)⁻¹ * c * x * c⁻¹ := hoeq
    have hcx : c * x * c⁻¹ = (x : X) * o := by
      rw [hoeq']
      group
    have h1 : (⟨c, hcN⟩ : ↥(normalizer (M : Set X))) * ⟨x, hJeN x.2⟩ * ⟨c, hcN⟩⁻¹ =
        ⟨x, hJeN x.2⟩ * ⟨o, hJeN o.2⟩ := Subtype.ext hcx
    have h2 := congrArg ρ h1
    rw [map_mul, map_mul, map_inv, map_mul, hρO o ho, mul_one] at h2
    calc g * ρ ⟨x, hJeN x.2⟩ = (g * ρ ⟨x, hJeN x.2⟩ * g⁻¹) * g := by group
      _ = ρ ⟨x, hJeN x.2⟩ * g := by rw [hgdef, h2]
  have hgF : ∀ b ∈ fixAlt τ, g * (b : Perm (Fin r)) = (b : Perm (Fin r)) * g := by
    intro b hb
    obtain ⟨q, hq⟩ := ψ.surjective ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (b : Perm (Fin r)) = ρ ⟨x, hJeN x.2⟩ := by
      rw [← hψ x, hq]
    rw [h1]
    exact hgx x
  have hτc : τ.support.card ≤ r := by
    have := Finset.card_le_univ τ.support
    rwa [Fintype.card_fin] at this
  have hgfix : ∀ v ∉ τ.support, g v = v := fun v hv =>
    apply_eq_of_commute_fixAlt (by omega) hgF hv
  have hsplit : ρ ⟨a, ha⟩ = g * ρ ⟨j, hJeN hj⟩ := by
    rw [hgdef, ← map_mul]
    congr 1
    apply Subtype.ext
    change a = a * j⁻¹ * j
    group
  have hρj := hψ ⟨j, hj⟩
  have hjF : ((ψ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je) : fixAlt τ) :
      alternatingGroup (Fin r)) ∈ fixAlt τ := (ψ _).2
  rw [mem_fixAlt, hρj] at hjF
  have hsub : (ρ ⟨a, ha⟩).support ⊆ τ.support ∪ (ρ ⟨j, hJeN hj⟩).support := by
    intro v hv
    by_contra hvn
    rw [Finset.mem_union, not_or] at hvn
    apply Perm.mem_support.mp hv
    rw [hsplit, Perm.mul_apply, Perm.notMem_support.mp hvn.2, hgfix v hvn.1]
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsupj : (ρ ⟨j, hJeN hj⟩).support.card =
      ((χ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je) : alternatingGroup β) :
        Perm β).support.card := by
    have h1 := card_support_of_le_fixAlt hk hτk le_rfl hβ (χ.symm.trans ψ)
      (χ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je))
    have h2 : (χ.symm.trans ψ) (χ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je)) =
        ψ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je) := by
      change ψ (χ.symm (χ _)) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h2, hρj] at h1
    exact h1
  omega

end CFSG.ComponentClassification.SolMax
