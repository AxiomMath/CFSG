module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3ACent
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ALift
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.GLTheoremB

section Core

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {Y : Type} [Group Y] [Finite Y]

theorem centMod_mul_scalar {L : Subgroup (GL (Fin 3) K)} {x z : GL (Fin 3) K}
    (hz : z ∈ StatedScalars (Fin 3) K) : centMod L (x * z) = centMod L x := by
  have hc := commute_of_mem_statedScalars hz
  have key : ∀ x z : GL (Fin 3) K, z ∈ StatedScalars (Fin 3) K →
      centMod L x ≤ centMod L (x * z) := by
    intro x z hz l hl
    obtain ⟨hlL, w, hw, hwx⟩ := mem_centMod_iff_scalar.mp hl
    refine mem_centMod_iff_scalar.mpr ⟨hlL, w, hw, ?_⟩
    have hc := commute_of_mem_statedScalars hz
    calc l * (x * z) * l⁻¹ = (l * x * l⁻¹) * (l * z * l⁻¹) := by group
      _ = (w * x) * z := by rw [hwx, hc l, mul_inv_cancel_right]
      _ = w * (x * z) := by rw [mul_assoc]
  refine le_antisymm ?_ (key x z hz)
  have h := key (x * z) z⁻¹ (inv_mem hz)
  rwa [mul_assoc, mul_inv_cancel, mul_one] at h

theorem centralizer_mul_scalar {x z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K) :
    Subgroup.centralizer ({x * z} : Set (GL (Fin 3) K)) = Subgroup.centralizer {x} := by
  ext l
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hc := commute_of_mem_statedScalars hz l
  constructor
  · intro h
    calc l * x = (l * (x * z)) * z⁻¹ := by group
      _ = ((x * z) * l) * z⁻¹ := by rw [h]
      _ = x * (z * l) * z⁻¹ := by group
      _ = x * (l * z) * z⁻¹ := by rw [← hc]
      _ = x * l := by group
  · intro h
    calc l * (x * z) = (l * x) * z := by group
      _ = (x * l) * z := by rw [h]
      _ = x * (l * z) := by group
      _ = x * (z * l) := by rw [hc]
      _ = (x * z) * l := by group

theorem false_of_isSolvable_quotient {J : Type*} [Group J] [Finite J]
    (hQ : CFSG.Open.IsQuasisimple (J ⧸ CFSG.Open.GLAPPrimeCore 3 J)) (hs : Group.IsSolvable J) : False :=
  false_of_quasisimple_of_solvable hQ
    (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.Open.GLAPPrimeCore 3 J)))

@[expose] noncomputable def liftHom (ν : ↥(slPi π 3 (p ^ f) K) →* Y) (J : Subgroup Y) :
    ↥(J.comap ν) →* GL (Fin 3) K :=
  (slPi π 3 (p ^ f) K).subtype.comp (J.comap ν).subtype

omit [Finite Y] in
theorem liftHom_injective (ν : ↥(slPi π 3 (p ^ f) K) →* Y) (J : Subgroup Y) :
    Function.Injective (liftHom ν J) :=
  Subtype.val_injective.comp Subtype.val_injective

omit [Finite Y] in
theorem mem_centMod_of_nu_eq {ν : ↥(slPi π 3 (p ^ f) K) →* Y}
    (hνker : ∀ s ∈ ν.ker, ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {g : GL (Fin 3) K} {s : ↥(slPi π 3 (p ^ f) K)}
    (t : ↥(slPi π 3 (p ^ f) K)) (ht : (t : GL (Fin 3) K) = g * s * g⁻¹) (h : ν s = ν t) :
    ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ centMod (slPi π 3 (p ^ f) K) g := by
  have h2 : ν (s⁻¹ * t) = 1 := by rw [map_mul, map_inv, ← h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := hνker _ (MonoidHom.mem_ker.2 h2)
  have hc' : (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) =
      (s : GL (Fin 3) K)⁻¹ * (g * s * g⁻¹) := by
    rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, ht]
  rw [mem_centMod_iff_scalar]
  refine ⟨s.2, (Matrix.GeneralLinearGroup.scalar (Fin 3) c)⁻¹, inv_mem ⟨c, rfl⟩, ?_⟩
  have hcc := commute_of_mem_statedScalars (⟨c, rfl⟩ : (Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    ∈ StatedScalars (Fin 3) K) (s : GL (Fin 3) K)
  rw [eq_inv_mul_iff_mul_eq]
  calc Matrix.GeneralLinearGroup.scalar (Fin 3) c * ((s : GL (Fin 3) K) * g * (s : GL (Fin 3) K)⁻¹)
      = (Matrix.GeneralLinearGroup.scalar (Fin 3) c * (s : GL (Fin 3) K)) * g *
          (s : GL (Fin 3) K)⁻¹ := by group
    _ = ((s : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) c) * g *
          (s : GL (Fin 3) K)⁻¹ := by rw [← hcc]
    _ = g := by rw [hc']; group

theorem false_of_inner (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (ν : ↥(slPi π 3 (p ^ f) K) →* Y)
    (hνker : ∀ s ∈ ν.ker, ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {x : GL (Fin 3) K} (hx : x ∈ glPi π 3 (p ^ f) K) (hxZ : x ∉ zPi π 3 (p ^ f) K)
    (hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K) (J : Subgroup Y) (hJν : J ≤ ν.range) (β : MulAut Y)
    (hνβ : ∀ s t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = x * s * x⁻¹ → β (ν s) = ν t)
    (hJβ : ∀ j ∈ J, β j = j)
    (hQ : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J))
    (hE9 : ∃ E : Subgroup (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9) : False := by
  have hπ0 : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hJx : ∀ s : ↥(slPi π 3 (p ^ f) K), ν s ∈ J →
      ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ centMod (slPi π 3 (p ^ f) K) x := by
    intro s hs
    refine mem_centMod_of_nu_eq hνker
      ⟨x * s * x⁻¹, conj_mem_slPi hπ0 hx s.2⟩ rfl ?_
    rw [← hνβ s ⟨x * s * x⁻¹, conj_mem_slPi hπ0 hx s.2⟩ rfl, hJβ _ hs]
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨y, ⟨z, hz, hyz⟩, hcases⟩ := rank3II_4_10_one hK hq hτ hτ1 hx hxZ hx3
  have hzS : z ∈ StatedScalars (Fin 3) K := by
    rw [zPi_eq hπ (fun h => by subst h; exact hq) hτ hτ1] at hz
    exact (Subgroup.mem_inf.1 hz).2
  have hcm : ∀ s : ↥(slPi π 3 (p ^ f) K), ν s ∈ J →
      ((s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ centMod (slPi π 3 (p ^ f) K) y := by
    intro s hs
    rw [hyz, centMod_mul_scalar hzS]
    exact hJx s hs
  have hsolv : Group.IsSolvable ↥(centMod (slPi π 3 (p ^ f) K) y) → False := by
    intro hM
    have hA : Group.IsSolvable ↥(J.comap ν) := by
      let ψ : ↥(J.comap ν) →* ↥(centMod (slPi π 3 (p ^ f) K) y) :=
        { toFun := fun a => ⟨(a.1 : GL (Fin 3) K), hcm a.1 a.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact Group.isSolvable_of_isSolvable_injective (f := ψ) (fun a b h => Subtype.ext
        (Subtype.ext (congrArg (fun m : ↥(centMod (slPi π 3 (p ^ f) K) y) =>
          (m : GL (Fin 3) K)) h)))
    let ν' : ↥(J.comap ν) →* ↥J := (ν.comp (J.comap ν).subtype).codRestrict J (fun a => a.2)
    have hν' : Function.Surjective ν' := by
      intro j
      obtain ⟨s, hs⟩ := hJν j.2
      exact ⟨⟨s, by change ν s ∈ J; rw [hs]; exact j.2⟩, Subtype.ext hs⟩
    exact false_of_isSolvable_quotient hQ (Group.isSolvable_of_surjective hν')
  rcases hcases with ⟨-, ⟨e⟩, -⟩ | ⟨⟨g, hg, e, he, hge⟩, ⟨e'⟩, hcen⟩ | ⟨-, -, -, hcyc, -, -⟩
  ·
    refine hsolv (isSolvable_centMod _ _ ?_)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  ·
    have hτ2 : τ ^ 2 ≠ 1 := by
      intro h
      apply hτ1
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, h, div_one]
    have he1 : e ≠ 1 := by
      intro h1
      have h1' : (e : K) = 1 := by rw [h1]; rfl
      rcases he with h | h
      · exact hτ1 (h.symm.trans h1')
      · exact hτ2 (h.symm.trans h1')
    set A := ↥(J.comap ν) with hAdef
    set φ0 := liftHom ν J with hφ0
    have hWL : φ0.range ≤ slPi π 3 (p ^ f) K := by
      rintro _ ⟨a, rfl⟩
      exact a.1.2
    have hWy : φ0.range ≤ Subgroup.centralizer {y} := by
      rintro _ ⟨a, rfl⟩
      have := hcm a.1 a.2
      rw [hcen] at this
      exact (Subgroup.mem_inf.1 this).2
    obtain ⟨hscal, hrank⟩ := typeII_commutator hK hq he1 hg hge hWL hWy
    have hcommmem : ∀ a ∈ commutator A, φ0 a ∈ ⁅φ0.range, φ0.range⁆ := by
      intro a ha
      have h1 : φ0 a ∈ (commutator A).map φ0 := ⟨a, ha, rfl⟩
      have h2 : (commutator A).map φ0 = ⁅φ0.range, φ0.range⁆ := by
        change ((⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ : Subgroup A)).map φ0 = _
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map]
      rwa [h2] at h1
    let ν' : A →* ↥J := (ν.comp (J.comap ν).subtype).codRestrict J (fun a => a.2)
    have hν'surj : Function.Surjective ν' := by
      intro j
      obtain ⟨s, hs⟩ := hJν j.2
      exact ⟨⟨s, by change ν s ∈ J; rw [hs]; exact j.2⟩, Subtype.ext hs⟩
    have hν'inj : ∀ a ∈ commutator A, ν' a = 1 → a = 1 := by
      intro a ha h1
      have h2 : ν (a : ↥(slPi π 3 (p ^ f) K)) = 1 := congrArg Subtype.val h1
      obtain ⟨ω, hω⟩ := hνker a.1 (MonoidHom.mem_ker.2 h2)
      have h3 : φ0 a = Matrix.GeneralLinearGroup.scalar (Fin 3) ω := hω.symm
      have h4 := hscal ω (h3 ▸ hcommmem a ha)
      apply liftHom_injective ν J
      rw [map_one, h3, h4, map_one]
    let ρ0 : A →* ↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J := (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 3 ↥J)).comp ν'
    have hρ0 : Function.Surjective ρ0 :=
      (QuotientGroup.mk'_surjective (CFSG.Open.GLAPPrimeCore 3 ↥J)).comp hν'surj
    let ρ : ↥(commutator A) →* ↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J := ρ0.comp (commutator A).subtype
    have hρ : Function.Surjective ρ := by
      intro q
      have hq1 : q ∈ commutator (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J) := hQ.1 ▸ Subgroup.mem_top q
      have h2 : (commutator A).map ρ0 = commutator (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J) := by
        change ((⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ : Subgroup A)).map ρ0 =
          ⁅(⊤ : Subgroup (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J)),
            (⊤ : Subgroup (↥J ⧸ CFSG.Open.GLAPPrimeCore 3 ↥J))⁆
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hρ0]
      rw [← h2] at hq1
      obtain ⟨a, ha, rfl⟩ := hq1
      exact ⟨⟨a, ha⟩, rfl⟩
    have hker : Nat.Coprime 3 (Nat.card ρ.ker) := by
      let χ : ρ.ker →* ↥(CFSG.Open.GLAPPrimeCore 3 ↥J) :=
        { toFun := fun h => ⟨ν' h.1.1, (QuotientGroup.eq_one_iff _).1 h.2⟩
          map_one' := Subtype.ext (map_one ν')
          map_mul' := fun a b => Subtype.ext (map_mul ν' a.1.1 b.1.1) }
      have hχ : Function.Injective χ := by
        intro a b h
        have h1 : ν' a.1.1 = ν' b.1.1 := congrArg Subtype.val h
        have h2 : a.1.1⁻¹ * b.1.1 = 1 := by
          apply hν'inj _ (mul_mem (inv_mem a.1.2) b.1.2)
          rw [map_mul, map_inv, h1, inv_mul_cancel]
        rw [inv_mul_eq_one] at h2
        exact Subtype.ext (Subtype.ext h2)
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective χ hχ)
        (coprime_card_gLAPPrimeCore_aux 3 ↥J)
    obtain ⟨E, hEa, hEc⟩ := hE9
    obtain ⟨E', hE'a, hE'c, -⟩ := exists_elemAbelian_nine_lift ρ hρ hker E hEa hEc
    set ι : ↥(commutator A) →* GL (Fin 3) K := φ0.comp (commutator A).subtype with hι
    have hιinj : Function.Injective ι :=
      (liftHom_injective ν J).comp Subtype.val_injective
    have hle : E'.map ι ≤ ⁅φ0.range, φ0.range⁆ := by
      rintro _ ⟨h, -, rfl⟩
      exact hcommmem h.1 h.2
    have h9 := hrank _ hle (isElemAbelian_map ι hE'a)
    rw [Subgroup.card_map_of_injective hιinj, hE'c] at h9
    omega
  ·
    refine hsolv (isSolvable_centMod _ _ ?_)
    have := hcyc
    exact inferInstance

end Core

end CFSG.HardMathSupport.Solomon.Coordinator
