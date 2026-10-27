module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS5

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

structure PiData (L : Subgroup G) where
  β : ↥(blockU L) ≃* Multiplicative (evenWeight 5)
  π : ↥(Subgroup.normalizer (L : Set G)) →* Perm (Fin 5)
  hcomp : ∀ (y : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
    (u' : G) = (y : G) * (u : G) * (y : G)⁻¹ →
    Multiplicative.toAdd (β u') = vact (π y) (Multiplicative.toAdd (β u))
  hker : ∀ y : ↥(Subgroup.normalizer (L : Set G)),
    π y = 1 ↔ ∀ u ∈ blockU L, (y : G) * u * (y : G)⁻¹ = u

namespace PiData

variable {L : Subgroup G} (D : PiData L)

@[expose] def im (K : Subgroup G) : Subgroup (Perm (Fin 5)) :=
  (K.subgroupOf (Subgroup.normalizer (L : Set G))).map D.π

omit [Finite G] in
theorem mem_im {K : Subgroup G} {g : Perm (Fin 5)} :
    g ∈ D.im K ↔ ∃ y : ↥(Subgroup.normalizer (L : Set G)), (y : G) ∈ K ∧ D.π y = g := by
  unfold im
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem im_mono {K K' : Subgroup G} (h : K ≤ K') : D.im K ≤ D.im K' := by
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
  exact (D.mem_im).2 ⟨y, h hy, rfl⟩

omit [Finite G] in
theorem pi_mem_im {K : Subgroup G} {y : ↥(Subgroup.normalizer (L : Set G))} (hy : (y : G) ∈ K) :
    D.π y ∈ D.im K :=
  (D.mem_im).2 ⟨y, hy, rfl⟩

omit [Finite G] in
theorem card_im_mul {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (D.im A) * Nat.card ↥(A ⊓ Subgroup.centralizer (blockU L : Set G)) =
      Nat.card A := by
  set N := Subgroup.normalizer (L : Set G) with hN
  set K' := A.subgroupOf N with hK'
  have h1 := Subgroup.card_ker_mul_card_range (D.π.domRestrict K')
  rw [MonoidHom.domRestrict_range] at h1
  have h2 : Nat.card K' = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have h3 : Nat.card (D.π.domRestrict K').ker =
      Nat.card ↥(A ⊓ Subgroup.centralizer (blockU L : Set G)) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨(y.1.1 : G), y.1.2, Subgroup.mem_centralizer_iff.2 fun u hu => by
          have := (D.hker y.1.1).1 y.2 u hu
          calc u * (y.1.1 : G) = ((y.1.1 : G) * u * (y.1.1 : G)⁻¹) * (y.1.1 : G) := by rw [this]
            _ = (y.1.1 : G) * u := by group⟩
        invFun := fun k => ⟨⟨⟨k, hAN k.2.1⟩, Subgroup.mem_subgroupOf.2 k.2.1⟩, by
          show D.π ⟨k, hAN k.2.1⟩ = 1
          rw [D.hker]
          intro u hu
          have := Subgroup.mem_centralizer_iff.1 k.2.2 u hu
          calc (k : G) * u * (k : G)⁻¹ = (u * (k : G)) * (k : G)⁻¹ := by rw [this]
            _ = u := by group⟩
        left_inv := fun y => rfl
        right_inv := fun k => rfl }
  rw [← h2, ← h1, h3]
  show Nat.card (Subgroup.map D.π K') * _ = _
  ring

omit [Finite G] in
theorem card_fix {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) = Nat.card (FixΔ (D.im A)) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨Multiplicative.toAdd (D.β ⟨u.1, u.2.1⟩), fun σ hσ => by
        obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hσ
        have hc := Subgroup.mem_centralizer_iff.1 u.2.2 y hy
        have h := D.hcomp y ⟨u.1, u.2.1⟩ ⟨u.1, u.2.1⟩ (by
          show (u : G) = (y : G) * (u : G) * (y : G)⁻¹
          rw [hc]; group)
        exact h.symm⟩
      invFun := fun w => ⟨((D.β.symm (Multiplicative.ofAdd w.1) : ↥(blockU L)) : G),
        (D.β.symm (Multiplicative.ofAdd w.1)).2, Subgroup.mem_centralizer_iff.2 fun a ha => by
          set u := D.β.symm (Multiplicative.ofAdd w.1) with hu
          have hmem : (a : G) * (u : G) * (a : G)⁻¹ ∈ blockU L := by
            have := C1.mem_normalizer_blockU (L := L) (hAN ha)
            exact (Subgroup.mem_normalizer_iff.mp this u).mp u.2
          have h := D.hcomp ⟨a, hAN ha⟩ u ⟨_, hmem⟩ rfl
          have hw : vact (D.π ⟨a, hAN ha⟩) (Multiplicative.toAdd (D.β u)) =
              Multiplicative.toAdd (D.β u) := by
            have := w.2 (D.π ⟨a, hAN ha⟩) (D.pi_mem_im (K := A) ha)
            simpa [hu] using this
          rw [hw] at h
          have h2 : (⟨_, hmem⟩ : ↥(blockU L)) = u := D.β.injective (Multiplicative.toAdd.injective h)
          have h3 : (a : G) * (u : G) * (a : G)⁻¹ = (u : G) := congrArg Subtype.val h2
          calc (a : G) * u = ((a : G) * (u : G) * (a : G)⁻¹) * a := by group
            _ = (u : G) * a := by rw [h3]⟩
      left_inv := fun u => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        simp }

end PiData

theorem card_evenWeight : Nat.card (evenWeight 5) = 16 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : Fin 5 → ZMod 2 => mem_evenWeight_iff x))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

namespace PiData

variable {L : Subgroup G} (D : PiData L)

omit [Finite G] in
include D in
theorem card_blockU : Nat.card ↥(blockU L) = 16 := by
  rw [Nat.card_congr D.β.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5),
    card_evenWeight]

theorem ff_ineq {S A : Subgroup G} (hU : IsElemAbelian 2 (blockU L)) (hUS : blockU L ≤ S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hA : IsMaxElemAbelian S A) :
    16 ≤ Nat.card (D.im A) * Nat.card (FixΔ (D.im A)) := by
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hA.1.trans hSN
  set K := A ⊓ Subgroup.centralizer (blockU L : Set G) with hK
  have hKe : IsElemAbelian 2 K := B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hcomm : ∀ k ∈ K, ∀ u ∈ blockU L, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hB1e := B2F.isElemAbelian_sup_of_commute hKe hU hcomm
  have hB1S : K ⊔ blockU L ≤ S := sup_le (inf_le_left.trans hA.1) hUS
  have h1 : Nat.card ↥(K ⊔ blockU L) ≤ Nat.card A := hA.2.2 _ hB1S hB1e
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : Nat.card ↥(K ⊓ blockU L) ≤
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA.2.1 ha hx.1.1
  have h4 := D.card_im_mul hAN
  have h5 := D.card_fix hAN
  have h6 := D.card_blockU
  have hkpos : 0 < Nat.card ↥K := Nat.card_pos
  rw [h5] at h3
  set p := Nat.card (D.im A)
  set f := Nat.card (FixΔ (D.im A))
  have h7 : Nat.card ↥K * 16 ≤ Nat.card ↥K * (p * f) := by
    calc Nat.card ↥K * 16 = Nat.card ↥(K ⊔ blockU L) * Nat.card ↥(K ⊓ blockU L) := by
          rw [h2, h6]
      _ ≤ Nat.card A * f := Nat.mul_le_mul h1 h3
      _ = Nat.card ↥K * (p * f) := by rw [← h4]; ring
  exact Nat.le_of_mul_le_mul_left h7 hkpos

omit [Finite G] in
theorem im_elemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    (∀ g ∈ D.im A, g * g = 1) ∧ ∀ g ∈ D.im A, ∀ h ∈ D.im A, g * h = h * g := by
  constructor
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
    have : y * y = 1 := Subtype.ext (by simpa [pow_two] using hA.2 _ hy)
    rw [← map_mul, this, map_one]
  · intro g hg h hh
    obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
    obtain ⟨z, hz, rfl⟩ := (D.mem_im).1 hh
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (B2F.isElemAbelian_comm hA hy hz)

theorem swapGen_im {S A : Subgroup G} (hU : IsElemAbelian 2 (blockU L)) (hUS : blockU L ≤ S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hA : IsMaxElemAbelian S A) :
    ∀ g ∈ D.im A, g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ D.im A ∧ s.IsSwap} :=
  swapGen_of_ff (D.im A) (D.im_elemAbelian hA.2.1).1 (D.im_elemAbelian hA.2.1).2
    (D.ff_ineq hU hUS hSN hA)

end PiData

structure A5Pi (L : Subgroup G) extends PiData L where
  α : ↥L →* alternatingGroup (Fin 5)
  hα : Function.Surjective α
  hαk : α.ker = CFSG.pCore 2 L
  hπα : ∀ (ℓ : G) (hℓ : ℓ ∈ L),
    π ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = ((α ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5))

theorem exists_a5pi {L : Subgroup G} (hL : IsShort2 L) (h5 : IsAltType L 5)
    (α : ↥L →* alternatingGroup (Fin 5)) (hα : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 L) : ∃ P : A5Pi L, P.α = α := by
  obtain ⟨β, π, -, hcomp, hπα, hker⟩ := exists_pi_normalizer hL h5 α hα hαk
  let D : PiData L := { β := β, π := π, hcomp := hcomp, hker := hker }
  exact ⟨{ toPiData := D, α := α, hα := hα, hαk := hαk, hπα := hπα }, rfl⟩

end CFSG.QuasithinUnique.AppC
