module

public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.Eigen

public section

namespace CFSG.UnitaryInvolutionIndex

open Module Module.End

variable {k : Type*} [Field k] {G : Type*} [Group G]

section Scalar

variable {V : Type*} [AddCommGroup V] [Module k V]

def scalarSubgroup (ρ : G →* End k V) : Subgroup G where
  carrier := {g | ∃ c : k, ρ g = c • 1}
  one_mem' := ⟨1, by rw [map_one, one_smul]⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, by rw [map_mul, hc, hd, smul_mul_smul_comm, one_mul]⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    have h1 : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [hc, mul_smul_comm, mul_one] at h1
    by_cases h0 : c = 0
    · rw [h0, zero_smul] at h1
      exact ⟨0, (subsingleton_of_zero_eq_one h1).elim _ _⟩
    · exact ⟨c⁻¹, by rw [← h1, smul_smul, inv_mul_cancel₀ h0, one_smul]⟩

instance (ρ : G →* End k V) : (scalarSubgroup ρ).Normal where
  conj_mem g := by
    rintro ⟨c, hc⟩ h
    refine ⟨c, ?_⟩
    rw [map_mul, map_mul, hc, mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel,
      map_one]

theorem eq_zero_of_apply_eq_zero (ρ : G →* End k V) (g : G) {w : V} (hw : ρ g w = 0) : w = 0 := by
  have h : ρ g⁻¹ (ρ g w) = w := by rw [← mul_apply, ← map_mul, inv_mul_cancel, map_one, one_apply]
  rw [← h, hw, map_zero]

theorem nontrivial_of_notMem_scalarSubgroup {ρ : G →* End k V} {x : G}
    (hx : x ∉ scalarSubgroup ρ) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hx ⟨0, Subsingleton.elim (h := inferInstance) _ _⟩

theorem exists_mul_eq_smul_of_ne_top [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (ρ : G →* End k V) (hN : scalarSubgroup ρ ≠ ⊤) :
    ∃ x ∉ scalarSubgroup ρ, ∀ g, ∃ c : k, ρ g * ρ x = c • (ρ x * ρ g) := by
  have : Nontrivial (G ⧸ scalarSubgroup ρ) := QuotientGroup.nontrivial_iff.mpr hN
  have := (hG.to_quotient (scalarSubgroup ρ)).center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (G ⧸ scalarSubgroup ρ))
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (z : G ⧸ scalarSubgroup ρ)
  refine ⟨x, fun hxN => hz (Subtype.ext ?_), fun g => ?_⟩
  · rw [← hx, Subgroup.coe_one]
    exact (QuotientGroup.eq_one_iff x).mpr hxN
  · have hmem : g * x * g⁻¹ * x⁻¹ ∈ scalarSubgroup ρ := by
      rw [← QuotientGroup.eq_one_iff]
      have hcomm := Subgroup.mem_center_iff.mp z.2 (g : G ⧸ scalarSubgroup ρ)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx]
      rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    calc ρ g * ρ x = ρ (g * x * g⁻¹ * x⁻¹) * (ρ x * ρ g) := by
          rw [← map_mul, ← map_mul, ← map_mul]
          congr 1
          group
      _ = c • (ρ x * ρ g) := by rw [hc, smul_mul_assoc, one_mul]

theorem ne_zero_of_mul_eq_smul (ρ : G →* End k V) {x g : G} {c : k}
    (hc : ρ g * ρ x = c • (ρ x * ρ g)) [Nontrivial V] : c ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  rw [zero_smul] at hc
  have h := congrArg (fun T : End k V => T v) hc
  simp only [mul_apply] at h
  exact hv (eq_zero_of_apply_eq_zero ρ x (eq_zero_of_apply_eq_zero ρ g h))

theorem hasEigenvector_apply_of_mul_eq_smul (ρ : G →* End k V) {x g : G} {c : k}
    (hc : ρ g * ρ x = c • (ρ x * ρ g)) (hc0 : c ≠ 0) {μ : k} {v : V}
    (hv : (ρ x).HasEigenvector μ v) : (ρ x).HasEigenvector (c⁻¹ * μ) (ρ g v) := by
  refine ⟨mem_eigenspace_iff.mpr ?_, fun h => hv.2 (eq_zero_of_apply_eq_zero ρ g h)⟩
  have h := congrArg (fun T : End k V => T v) hc
  simp only [mul_apply, LinearMap.smul_apply, hv.apply_eq_smul, map_smul] at h
  rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end Scalar

section Restrict

variable {V : Type*} [AddCommGroup V] [Module k V]

@[expose] def restrictRep (ρ : G →* End k V) (W : Submodule k V) (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) :
    G →* End k W where
  toFun g := (ρ g).restrict (hW g)
  map_one' := by
    ext v
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext v
    simp [LinearMap.restrict_apply]

theorem restrictRep_apply (ρ : G →* End k V) (W : Submodule k V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) (g : G) (v : W) :
    (restrictRep ρ W hW g v : V) = ρ g v :=
  rfl

theorem commute_of_sup_eq_top {E F : Submodule k V} (hEF : E ⊔ F = ⊤) {g h : End k V}
    (hE : ∀ v ∈ E, g (h v) = h (g v)) (hF : ∀ v ∈ F, g (h v) = h (g v)) : Commute g h := by
  show g * h = h * g
  refine LinearMap.ext fun v => ?_
  obtain ⟨e, he, w, hw, rfl⟩ := Submodule.mem_sup.mp (hEF ▸ Submodule.mem_top : v ∈ E ⊔ F)
  simp only [mul_apply, map_add, hE e he, hF w hw]

theorem apply_apply_comm_of_commute_restrictRep (ρ : G →* End k V) (W : Submodule k V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) {g h : G}
    (hc : Commute (restrictRep ρ W hW g) (restrictRep ρ W hW h)) (v : V) (hv : v ∈ W) :
    ρ g (ρ h v) = ρ h (ρ g v) := by
  have := congrArg (fun T : End k W => (T ⟨v, hv⟩ : V)) hc.eq
  simpa only [mul_apply, restrictRep_apply] using this

theorem apply_mem_eigenspace_of_commute {f g : End k V} (hg : Commute g f) {μ : k} {v : V}
    (hv : v ∈ f.eigenspace μ) : g v ∈ f.eigenspace μ := by
  rw [mem_eigenspace_iff] at hv ⊢
  rw [← mul_apply, ← hg.eq, mul_apply, hv, map_smul]

theorem exists_split_of_ne_smul_one [FiniteDimensional k V] {f : End k V}
    (hf : ⨆ μ, f.eigenspace μ = ⊤) {μ : k} (hμ : f.HasEigenvalue μ) (hne : f ≠ μ • 1) :
    ∃ E F : Submodule k V, E ⊔ F = ⊤ ∧ finrank k E < finrank k V ∧
      finrank k F < finrank k V ∧
      ∀ g : End k V, Commute g f → (∀ v ∈ E, g v ∈ E) ∧ (∀ v ∈ F, g v ∈ F) := by
  set E := f.eigenspace μ
  set F := ⨆ (ν : k) (_ : ν ≠ μ), f.eigenspace ν
  have hdisj : Disjoint E F := f.eigenspaces_iSupIndep μ
  have hsup : E ⊔ F = ⊤ := by
    rw [eq_top_iff, ← hf]
    refine iSup_le fun ν => ?_
    by_cases hν : ν = μ
    · rw [hν]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le ν hν le_rfl)
  have hEtop : E ≠ ⊤ := by
    intro hE
    apply hne
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ E := hE ▸ Submodule.mem_top
    rw [mem_eigenspace_iff] at hv
    rw [hv, LinearMap.smul_apply, one_apply]
  have hFtop : F ≠ ⊤ := by
    intro hF
    rw [hF, disjoint_top] at hdisj
    exact hμ hdisj
  refine ⟨E, F, hsup, Submodule.finrank_lt hEtop, Submodule.finrank_lt hFtop,
    fun g hg => ⟨fun v hv =>
      apply_mem_eigenspace_of_commute hg hv, fun v hv => ?_⟩⟩
  have hle : F ≤ F.comap g := iSup₂_le fun ν hν w hw =>
    le_iSup₂_of_le (f := fun (ν : k) (_ : ν ≠ μ) => f.eigenspace ν) ν hν le_rfl
      (apply_mem_eigenspace_of_commute hg hw)
  exact hle hv

end Restrict

variable {p : ℕ} [Fact p.Prime]

theorem natCast_card_ne_zero [Finite G] (hpk : (p : k) ≠ 0) (hG : IsPGroup p G) :
    ((Nat.card G : ℕ) : k) ≠ 0 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  rw [hn, Nat.cast_pow]
  exact pow_ne_zero n hpk

section Representation

variable {V : Type*} [AddCommGroup V] [Module k V]

theorem rep_pow_card_eq_one (ρ : G →* End k V) (g : G) : ρ g ^ Nat.card G = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

variable [Finite G]

theorem hasEigenvector_pow_of_mul_eq_smul (hG : IsPGroup p G) (ρ : G →* End k V) {x g₀ : G}
    {c₀ : k} (hc₀ : ρ g₀ * ρ x = c₀ • (ρ x * ρ g₀)) (hc₀1 : c₀ ≠ 1) {μ : k} {v : V}
    (hv : (ρ x).HasEigenvector μ v) :
    (∀ i : ℕ, (ρ x).HasEigenvector ((c₀ ^ i)⁻¹ * μ) (ρ (g₀ ^ i) v)) ∧
      Function.Injective fun i : Fin p => (c₀ ^ (i : ℕ))⁻¹ * μ := by
  have : Nontrivial V := ⟨⟨v, 0, hv.2⟩⟩
  have hc₀0 := ne_zero_of_mul_eq_smul ρ hc₀
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have h := hv.apply_eq_smul
    rw [zero_smul] at h
    exact hv.2 (eq_zero_of_apply_eq_zero ρ x h)
  have hpow : ∀ i : ℕ, ρ (g₀ ^ i) * ρ x = c₀ ^ i • (ρ x * ρ (g₀ ^ i)) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, map_mul, mul_assoc, hc₀, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc,
        smul_smul, pow_succ, mul_comm (c₀ ^ i), mul_assoc, ← map_mul]
  have heig : ∀ i : ℕ, (ρ x).HasEigenvector ((c₀ ^ i)⁻¹ * μ) (ρ (g₀ ^ i) v) := fun i =>
    hasEigenvector_apply_of_mul_eq_smul ρ (hpow i) (pow_ne_zero i hc₀0) hv
  refine ⟨heig, fun i j hij => ?_⟩
  have hcard : c₀ ^ Nat.card G = 1 := by
    have h := congrArg (fun T : End k V => T v) (hpow (Nat.card G))
    simp only [pow_card_eq_one', map_one, one_mul, mul_one, LinearMap.smul_apply,
      hv.apply_eq_smul] at h
    have h0 : (c₀ ^ Nat.card G - 1) • (μ • v) = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right (smul_ne_zero hμ0 hv.2))
  have hord : p ≤ orderOf c₀ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
    rw [hn] at hcard
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hcard)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hm'
      exact hc₀1 hm'
    rw [hm']
    exact Nat.le_self_pow hm0 p
  have h' : c₀ ^ (i : ℕ) = c₀ ^ (j : ℕ) := by
    have := mul_right_cancel₀ hμ0 hij
    exact inv_injective this
  exact Fin.ext (pow_injOn_Iio_orderOf (lt_of_lt_of_le i.2 hord) (lt_of_lt_of_le j.2 hord) h')

theorem exists_split_of_commute [IsAlgClosed k] (hpk : (p : k) ≠ 0) (hG : IsPGroup p G)
    (ρ : G →* End k V)
    [FiniteDimensional k V] {x : G} (hx : x ∉ scalarSubgroup ρ)
    (hall : ∀ g, Commute (ρ g) (ρ x)) :
    ∃ E F : Submodule k V, E ⊔ F = ⊤ ∧ finrank k E < finrank k V ∧
      finrank k F < finrank k V ∧ (∀ g, ∀ v ∈ E, ρ g v ∈ E) ∧ (∀ g, ∀ v ∈ F, ρ g v ∈ F) := by
  have : Nontrivial V := nontrivial_of_notMem_scalarSubgroup hx
  obtain ⟨μ, hμ⟩ := exists_eigenvalue (ρ x)
  have hss := iSup_eigenspace_eq_top_of_pow_eq_one (natCast_card_ne_zero hpk hG)
    (rep_pow_card_eq_one ρ x)
  obtain ⟨E, F, hEF, hE, hF, hinv⟩ :=
    exists_split_of_ne_smul_one hss hμ fun h => hx ⟨μ, h⟩
  exact ⟨E, F, hEF, hE, hF, fun g => (hinv (ρ g) (hall g)).1,
    fun g => (hinv (ρ g) (hall g)).2⟩

end Representation

variable [IsAlgClosed k] [Finite G]

theorem commute_of_finrank_lt_aux (hpk : (p : k) ≠ 0) (hG : IsPGroup p G) (n : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : G →* End k V),
      finrank k V = n → n < p → ∀ g h, Commute (ρ g) (ρ h) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn hnp g h
  by_cases hN : scalarSubgroup ρ = ⊤
  · obtain ⟨c, hc⟩ : g ∈ scalarSubgroup ρ := hN ▸ Subgroup.mem_top g
    rw [hc]
    exact (Commute.one_left _).smul_left c
  obtain ⟨x, hx, hc⟩ := exists_mul_eq_smul_of_ne_top hG ρ hN
  by_cases hall : ∀ g, Commute (ρ g) (ρ x)
  · obtain ⟨E, F, hEF, hE, hF, hEi, hFi⟩ := exists_split_of_commute hpk hG ρ hx hall
    refine commute_of_sup_eq_top hEF (fun v hv => ?_) (fun v hv => ?_)
    · exact apply_apply_comm_of_commute_restrictRep ρ E hEi
        (ih _ (hn ▸ hE) E (restrictRep ρ E hEi) rfl (by omega) g h) v hv
    · exact apply_apply_comm_of_commute_restrictRep ρ F hFi
        (ih _ (hn ▸ hF) F (restrictRep ρ F hFi) rfl (by omega) g h) v hv
  · exfalso
    push Not at hall
    obtain ⟨g₀, hg₀⟩ := hall
    obtain ⟨c₀, hc₀⟩ := hc g₀
    have hc₀1 : c₀ ≠ 1 := by
      rintro rfl
      rw [one_smul] at hc₀
      exact hg₀ hc₀
    have : Nontrivial V := nontrivial_of_notMem_scalarSubgroup hx
    obtain ⟨μ, hμ⟩ := exists_eigenvalue (ρ x)
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    obtain ⟨heig, hinj⟩ := hasEigenvector_pow_of_mul_eq_smul hG ρ hc₀ hc₀1 hv
    have hle := card_le_finrank_of_hasEigenvector (ρ x) hinj (v := fun i : Fin p =>
      ρ (g₀ ^ (i : ℕ)) v) fun i => heig i
    rw [Fintype.card_fin] at hle
    omega

theorem commute_of_finrank_lt (hpk : (p : k) ≠ 0) (hG : IsPGroup p G) {V : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : G →* End k V)
    (hV : finrank k V < p) (g h : G) : Commute (ρ g) (ρ h) :=
  commute_of_finrank_lt_aux hpk hG _ V ρ rfl hV g h

theorem exists_normal_index_le_commute_of_finrank_eq (hpk : (p : k) ≠ 0) (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : G →* End k V)
    (hV : finrank k V = p) :
    ∃ A : Subgroup G, A.Normal ∧ A.index ≤ p ∧ ∀ g ∈ A, ∀ h ∈ A, Commute (ρ g) (ρ h) := by
  have hp := (Fact.out : p.Prime)
  have htop : (∀ g h, Commute (ρ g) (ρ h)) →
      ∃ A : Subgroup G, A.Normal ∧ A.index ≤ p ∧ ∀ g ∈ A, ∀ h ∈ A, Commute (ρ g) (ρ h) :=
    fun hc => ⟨⊤, inferInstance, by rw [Subgroup.index_top]; exact hp.one_lt.le,
      fun g _ h _ => hc g h⟩
  by_cases hN : scalarSubgroup ρ = ⊤
  · refine htop fun g h => ?_
    obtain ⟨c, hc⟩ : g ∈ scalarSubgroup ρ := hN ▸ Subgroup.mem_top g
    rw [hc]
    exact (Commute.one_left _).smul_left c
  obtain ⟨x, hx, hc⟩ := exists_mul_eq_smul_of_ne_top hG ρ hN
  by_cases hall : ∀ g, Commute (ρ g) (ρ x)
  · refine htop fun g h => ?_
    obtain ⟨E, F, hEF, hE, hF, hEi, hFi⟩ := exists_split_of_commute hpk hG ρ hx hall
    refine commute_of_sup_eq_top hEF (fun v hv => ?_) (fun v hv => ?_)
    · exact apply_apply_comm_of_commute_restrictRep ρ E hEi
        (commute_of_finrank_lt hpk hG (restrictRep ρ E hEi) (hV ▸ hE) g h) v hv
    · exact apply_apply_comm_of_commute_restrictRep ρ F hFi
        (commute_of_finrank_lt hpk hG (restrictRep ρ F hFi) (hV ▸ hF) g h) v hv
  push Not at hall
  obtain ⟨g₀, hg₀⟩ := hall
  have : Nontrivial V := nontrivial_of_notMem_scalarSubgroup hx
  obtain ⟨μ, hμ⟩ := exists_eigenvalue (ρ x)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  choose c hc using hc
  have hc₀1 : c g₀ ≠ 1 := by
    intro h1
    have := hc g₀
    rw [h1, one_smul] at this
    exact hg₀ this
  obtain ⟨heig, hinj⟩ := hasEigenvector_pow_of_mul_eq_smul hG ρ (hc g₀) hc₀1 hv
  have hcardι : Fintype.card (Fin p) = finrank k V := by rw [Fintype.card_fin, hV]
  have heig' : ∀ i : Fin p, (ρ x).HasEigenvector ((c g₀ ^ (i : ℕ))⁻¹ * μ)
      (ρ (g₀ ^ (i : ℕ)) v) := fun i => heig i
  have huniq : ∀ g d, ρ g * ρ x = d • (ρ x * ρ g) → d = c g := by
    intro g d hd
    have hw : (ρ x * ρ g) v ≠ 0 := fun h0 =>
      hv.2 (eq_zero_of_apply_eq_zero ρ g (eq_zero_of_apply_eq_zero ρ x h0))
    have h := congrArg (fun T : End k V => T v) (hd.symm.trans (hc g))
    exact smul_left_injective k hw h
  let χ : G →* k :=
    { toFun := c
      map_one' := (huniq 1 1 (by simp)).symm
      map_mul' := fun g h => (huniq (g * h) (c g * c h) (by
        rw [map_mul, mul_assoc, hc h, mul_smul_comm, ← mul_assoc, hc g, smul_mul_assoc,
          smul_smul, mul_comm (c h), mul_assoc])).symm }
  have hχ : ∀ g, χ g = c g := fun _ => rfl
  refine ⟨χ.toHomUnits.ker, inferInstance, ?_, fun g hg h hh => ?_⟩
  · rw [Subgroup.index_ker]
    have hmem : ∀ u : χ.toHomUnits.range, ∃ i : Fin p, ((u : kˣ) : k) = c g₀ ^ (i : ℕ) := by
      rintro ⟨u, g, rfl⟩
      have hcg0 : c g ≠ 0 := ne_zero_of_mul_eq_smul ρ (hc g)
      obtain ⟨i, hi⟩ := exists_eq_of_hasEigenvector hinj heig' hcardι
        (hasEigenvector_apply_of_mul_eq_smul ρ (hc g) hcg0 hv)
      refine ⟨i, ?_⟩
      have h' := mul_right_cancel₀ (show μ ≠ 0 from ?_) hi
      · simpa [MonoidHom.coe_toHomUnits, hχ] using inv_injective h'
      · rintro rfl
        have h0 := hv.apply_eq_smul
        rw [zero_smul] at h0
        exact hv.2 (eq_zero_of_apply_eq_zero ρ x h0)
    choose idx hidx using hmem
    have hidx_inj : Function.Injective idx := by
      intro u u' h
      apply Subtype.ext
      apply Units.ext
      rw [hidx u, hidx u', h]
    calc Nat.card χ.toHomUnits.range ≤ Nat.card (Fin p) :=
          Nat.card_le_card_of_injective idx hidx_inj
      _ = p := Nat.card_fin p
  · have hcomm : ∀ g ∈ χ.toHomUnits.ker, Commute (ρ g) (ρ x) := by
      intro g hg
      have h1 : c g = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
        simpa [MonoidHom.coe_toHomUnits, hχ] using this
      have := hc g
      rw [h1, one_smul] at this
      exact this
    exact commute_of_commute_of_card_eq_finrank hinj heig' hcardι (hcomm g hg) (hcomm h hh)

end CFSG.UnitaryInvolutionIndex
