module

public import CFSG.RankThree.Classical2.TwistedE6Phi3Transport
public import CFSG.HardMathSupport.Malle.SeitzCube.Landing

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Malle.SeitzCube

section Abstract


theorem map_conj_eq_of_forall_mem {G : Type*} [Group G] (S E : Subgroup G)
    (h : ∀ x ∈ E, ∀ y ∈ S, x * y * x⁻¹ ∈ S) :
    ∀ x ∈ E, S.map (MulAut.conj x).toMonoidHom = S := by
  intro x hx
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h x hx y hy
  · intro hz
    refine ⟨x⁻¹ * z * x, ?_, ?_⟩
    · simpa using h x⁻¹ (inv_mem hx) z hz
    · simp [MulAut.conj_apply, mul_assoc]

theorem exists_plane_normalizing_of_twisted_torus {τ : Tag} {C : Type} [Group C] {L : Type}
    [Field L] (ι : C →* ModGL τ L) (hι : Function.Injective ι) (Φ : ModGL τ L →* ModGL τ L)
    (n g0 : ModGL τ L) (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n) {p r : ℕ}
    (hp : p.Prime) {N m : ℕ} (hN : N ≠ 0)
    (hrat : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Φ x = x) → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P → P ≤ ι.range)
    (hcomm : IsMulCommutative (twistedTorusOf n Φ))
    (hcard : Nat.card (twistedTorusOf n Φ) = N)
    (htors : Nat.card (torsionSubgroup (twistedTorusOf n Φ) hcomm p) = p ^ m)
    (Y : Subgroup (ModGL τ L)) (hYne : Y ≠ ⊥) (hYr : IsPGroup r Y)
    (hYrange : Y.map (MulAut.conj g0).toMonoidHom ≤ ι.range)
    (hYnorm : ∀ t ∈ twistedTorusOf n Φ, Y.map (MulAut.conj t).toMonoidHom = Y) :
    ∃ E R : Subgroup C, IsElemAbelian p E ∧ Nat.card E = p ^ m ∧ R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hT0fin : Finite (twistedTorusOf n Φ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  let cg : ModGL τ L →* ModGL τ L := (MulAut.conj g0).toMonoidHom
  have hcg : Function.Injective cg := (MulAut.conj g0).injective
  have hcg_apply : ∀ x, cg x = g0 * x * g0⁻¹ := fun x => rfl
  have hT0C := twistedTorusOf_le_adjointGroup n Φ
  set X : Subgroup (ModGL τ L) := (twistedTorusOf n Φ).map cg with hX
  have hXfin : Finite X :=
    Finite.of_surjective (cg.subgroupMap (twistedTorusOf n Φ))
      (cg.subgroupMap_surjective (twistedTorusOf n Φ))
  have hXC : X ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (hT0C hx)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Φ x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := (mem_twistedTorusOf.1 hx).2
    rw [hcg_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Φ x * (g0 * n)⁻¹ = g0 * (n * Φ x * n⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  have hXcomm : IsMulCommutative X := isMulCommutative_map cg hcomm
  have hpg := hrat X hXC hXF
  set V : Subgroup (ModGL τ L) := torsionSubgroup X hXcomm p with hV
  have hVX : V ≤ X := fun x hx => hx.1
  have hVp : IsPGroup p V := fun x => ⟨1, by
    have : (x : ModGL τ L) ^ p = 1 := x.2.2
    apply Subtype.ext
    simpa using this⟩
  have hVrange : V ≤ ι.range := hpg V hVX hVp
  have hVcard : Nat.card V = p ^ m := by
    have hVmap : V = (torsionSubgroup (twistedTorusOf n Φ) hcomm p).map cg := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hxp⟩
        refine ⟨y, ⟨hy, hcg ?_⟩, rfl⟩
        rw [map_pow, hxp, map_one]
      · rintro ⟨y, ⟨hy, hyp⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, ?_⟩
        rw [← map_pow, hyp, map_one]
    rw [hVmap, Subgroup.card_map_of_injective hcg, htors]
  have hcommE : IsMulCommutative (V.comap ι) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    apply hι
    have := hXcomm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact setLike_mul_comm (hVX a.2) (hVX b.2)
  have hexpE : ∀ x ∈ V.comap ι, x ^ p = 1 := fun x hx => by
    apply hι
    rw [map_pow, map_one]
    exact hx.2
  have hmap : (V.comap ι).map ι = V := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hVrange
  set R : Subgroup C := (Y.map cg).comap ι with hR
  have hmapR : R.map ι = Y.map cg := by
    rw [hR, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hYrange
  have hRne : R ≠ ⊥ := fun h => by
    have h1 : Y.map cg = ⊥ := by rw [← hmapR, h, Subgroup.map_bot]
    exact hYne ((Subgroup.map_eq_bot_iff_of_injective _ hcg).1 h1)
  have hRp : IsPGroup r R :=
    (hYr.map cg).of_injective (ι.subgroupComap (Y.map cg)) fun x y h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (hι h')
  have hnorm : ∀ x ∈ V.comap ι, ∀ y ∈ R, x * y * x⁻¹ ∈ R := by
    intro x hx y hy
    obtain ⟨t, ht, hxt⟩ := hVX hx
    obtain ⟨y₀, hy₀, hyy⟩ : ι y ∈ Y.map cg := hy
    have hmem : ι (x * y * x⁻¹) ∈ Y.map cg := by
      rw [map_mul, map_mul, map_inv, ← hxt, ← hyy]
      have hty : t * y₀ * t⁻¹ ∈ Y := by
        rw [← hYnorm t ht]
        exact ⟨y₀, hy₀, rfl⟩
      refine ⟨t * y₀ * t⁻¹, hty, ?_⟩
      simp only [hcg_apply]
      group
    exact hmem
  exact ⟨V.comap ι, R, ⟨hcommE, hexpE⟩, by
    rw [← Subgroup.card_map_of_injective hι, hmap, hVcard], hRne, hRp,
    map_conj_eq_of_forall_mem R _ hnorm⟩

end Abstract

section RootSingle

set_option linter.unusedSectionVars false


theorem exists_rootSingle_fixed_twistedE6 {L : Type} [Field L] [IsAlgClosed L] {r : ℕ}
    [Fact r.Prime] [CharP L r] (Fr : L →+* L) {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hργ : permLattice TwistTag.E6.perm γ = γ)
    (hvγ : v • γ = γ) :
    ∃ R : Subgroup (ModGL TwistTag.E6.tag L),
      R ≤ adjointGroup TwistTag.E6.tag L ∧
      (∀ y ∈ R, canonicalRep (coxeterSystem TwistTag.E6.tag) L v * twistHom TwistTag.E6 L Fr y *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ = y) ∧
      R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ t ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
          (twistHom TwistTag.E6 L Fr), R.map (MulAut.conj t).toMonoidHom = R := by
  classical
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) L v with hn
  set Φ := twistHom TwistTag.E6 L Fr with hΦ
  let ψ : Multiplicative L →* ModGL TwistTag.E6.tag L :=
    { toFun := fun x => pinnedX TwistTag.E6.tag L γ x.toAdd
      map_one' := by simp [pinnedX_zero]
      map_mul' := fun x y => by simp [pinnedX_add] }
  have hX : ∀ a, pinnedX TwistTag.E6.tag L γ a ∈ ψ.range := fun a => ⟨Multiplicative.ofAdd a, rfl⟩
  have hmem : ∀ x, x ∈ ψ.range ↔ ∃ a, x = pinnedX TwistTag.E6.tag L γ a := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.toAdd, rfl⟩
    · rintro ⟨a, rfl⟩
      exact hX a
  obtain ⟨ε₁, hε₁, hΦx⟩ := exists_twistHom_pinnedX TwistTag.E6 Fr hγ
  obtain ⟨ε₂, hε₂, hn₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L v hγ
  rw [hvγ] at hn₁
  rw [hργ] at hΦx
  have hR0t : ∀ t ∈ torusGroup TwistTag.E6.tag L, ∀ x ∈ ψ.range, t * x * t⁻¹ ∈ ψ.range := by
    intro t ht x hx
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    obtain ⟨a, rfl⟩ := (hmem x).1 hx
    rw [rootDiagUnit_conj_pinnedX l hγ a]
    exact hX _
  set S : Subgroup (ModGL TwistTag.E6.tag L) :=
    ((MulAut.conj n).toMonoidHom.comp Φ).eqLocus (MonoidHom.id _) with hS
  have hmemS : ∀ y, y ∈ S ↔ n * Φ y * n⁻¹ = y := fun y => Iff.rfl
  set R : Subgroup (ModGL TwistTag.E6.tag L) := ψ.range ⊓ S with hR
  have hRadj : R ≤ adjointGroup TwistTag.E6.tag L := by
    intro x hx
    obtain ⟨a, rfl⟩ := (hmem x).1 hx.1
    exact pinnedX_mem_adjointGroup _ _
  have hstep : ∀ t ∈ torusGroup TwistTag.E6.tag L, n * Φ t * n⁻¹ = t → ∀ x ∈ R,
      t * x * t⁻¹ ∈ R := by
    intro t ht htf x hx
    refine ⟨hR0t t ht x hx.1, (hmemS _).2 ?_⟩
    have hxf := (hmemS x).1 hx.2
    calc n * Φ (t * x * t⁻¹) * n⁻¹ = (n * Φ t * n⁻¹) * (n * Φ x * n⁻¹) * (n * Φ t * n⁻¹)⁻¹ := by
          simp only [map_mul, map_inv]; group
      _ = t * x * t⁻¹ := by rw [htf, hxf]
  have hq1 : 0 < q - 1 := by omega
  obtain ⟨a₀, ha₀⟩ := IsAlgClosed.exists_pow_nat_eq (ε₂ * ε₁) hq1
  have hε0 : ε₂ * ε₁ ≠ 0 := by
    intro h
    have h1 : (ε₂ * ε₁) * (ε₂ * ε₁) = 1 := by linear_combination (ε₂ * ε₂) * hε₁ + hε₂
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hε : (ε₂ * ε₁) * (ε₂ * ε₁) = 1 := by linear_combination (ε₂ * ε₂) * hε₁ + hε₂
  have ha0ne : a₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hq1.ne'] at ha₀
    exact hε0 ha₀.symm
  have hfix : ε₂ * (ε₁ * Fr a₀) = a₀ := by
    have hq' : a₀ ^ q = (ε₂ * ε₁) * a₀ := by
      rw [show q = (q - 1) + 1 by omega, pow_succ, ha₀]
    rw [hFr, hq']
    calc ε₂ * (ε₁ * ((ε₂ * ε₁) * a₀)) = ((ε₂ * ε₁) * (ε₂ * ε₁)) * a₀ := by ring
      _ = a₀ := by rw [hε, one_mul]
  have hxfix : n * Φ (pinnedX TwistTag.E6.tag L γ a₀) * n⁻¹ = pinnedX TwistTag.E6.tag L γ a₀ := by
    rw [hΦx, hn₁, hfix]
  have hx0 : pinnedX TwistTag.E6.tag L γ a₀ ∈ R := ⟨hX a₀, (hmemS _).2 hxfix⟩
  refine ⟨R, hRadj, fun y hy => (hmemS y).1 hy.2, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.mem_bot] at hx0
    exact ha0ne (pinnedX_injective TwistTag.E6.tag L γ (by rw [hx0, pinnedX_zero]))
  · intro g
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := g.2.1
    refine Subtype.ext ?_
    have hyr : y ^ r = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      simp [nsmul_eq_mul, CharP.cast_eq_zero]
    change (g : ModGL TwistTag.E6.tag L) ^ r ^ 1 = 1
    rw [pow_one, ← hy, ← map_pow, hyr, map_one]
  · intro t ht
    obtain ⟨htt, htf⟩ := mem_twistedTorusOf.1 ht
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hstep t htt htf x hx
    · intro hy
      refine ⟨t⁻¹ * y * t, ?_, ?_⟩
      · have htf' : n * Φ t⁻¹ * n⁻¹ = t⁻¹ := by
          calc n * Φ t⁻¹ * n⁻¹ = (n * Φ t * n⁻¹)⁻¹ := by simp only [map_inv]; group
            _ = t⁻¹ := by rw [htf]
        simpa using hstep t⁻¹ (inv_mem htt) htf' y hy
      · simp [MulAut.conj_apply, mul_assoc]

end RootSingle

end CFSG.HardMathSupport.Lang.SeitzPlane
