module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnD4b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinComm
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 (Sp8Class q2)
open CFSG.RankThree.Classical (spSupported spEnd)
open CFSG.RankThree.PartOne.KCPrimary (primaryMultiplicity)

abbrev SpGL : Type := GL (Fin 4 ⊕ Fin 4) (ZMod 2)

@[expose] def OmInSp (Ω : Subgroup SpGL) : Subgroup ↥(StatedSp 4 (ZMod 2)) :=
  Ω.subgroupOf (StatedSp 4 (ZMod 2))

theorem mem_OmInSp {Ω : Subgroup SpGL} {x : ↥(StatedSp 4 (ZMod 2))} :
    x ∈ OmInSp Ω ↔ ((x : SpGL)) ∈ Ω :=
  Subgroup.mem_subgroupOf

@[expose] def OmegaUnitaryInOm8 (Ω : Subgroup SpGL) : Prop :=
  ∀ t : ↥(StatedSp 4 (ZMod 2)), t ^ 3 = 1 → t ≠ 1 → t ∈ OmInSp Ω → spSupported t {q2} ≤ OmInSp Ω

@[expose] def OmegaOrthRank2Solvable (Ω : Subgroup SpGL) : Prop :=
  ∀ t : ↥(StatedSp 4 (ZMod 2)), t ^ 3 = 1 → t ≠ 1 → t ∈ OmInSp Ω → primaryMultiplicity (spEnd t) q2 = 2 →
    Group.IsSolvable ↥(spSupported t {(Polynomial.X - 1 : Polynomial (ZMod 2))} ⊓ OmInSp Ω)

@[expose] def OmegaOrthRank1U4 (Ω : Subgroup SpGL) : Prop :=
  ∀ t : ↥(StatedSp 4 (ZMod 2)), t ^ 3 = 1 → t ≠ 1 → t ∈ OmInSp Ω → primaryMultiplicity (spEnd t) q2 = 1 →
    ∀ K : Subgroup ↥(StatedSp 4 (ZMod 2)),
      IsComponentOf K (spSupported t {(Polynomial.X - 1 : Polynomial (ZMod 2))} ⊓ OmInSp Ω) →
      catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU4two

theorem isSolvable_of_le_of_solvable {G : Type} [Group G] {X A : Subgroup G} (hle : X ≤ A)
    (hA : Group.IsSolvable ↥A) : Group.IsSolvable ↥X :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem exists_mul_of_mem_sup_of_commute {G : Type} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (Commute.inv_inv (show Commute a b from hc a ha b hb)).eq.symm }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩) (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem omegaCentDecompOf_gen (Ω : Subgroup SpGL) (hΩ : Ω ≤ StatedSp 4 (ZMod 2))
    (hZ : Subgroup.center ↥Ω = ⊥) (hU : OmegaUnitaryInOm8 Ω) (h2 : OmegaOrthRank2Solvable Ω)
    (h1 : OmegaOrthRank1U4 Ω) :
    ∀ s : ↥Ω, (MulAut.conj s) ^ 3 = 1 → MulAut.conj s ≠ 1 →
      ∃ (k : ℕ) (A₀ A₁ : Subgroup ↥Ω), 1 ≤ k ∧ k ≤ 4 ∧
        Subgroup.centralizer ({s} : Set ↥Ω) = A₀ ⊔ A₁ ∧
        (∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a) ∧ A₀ ⊓ A₁ = ⊥ ∧
        (∃ (E : Type) (_ : Field E) (hE : UnitaryFieldData 2 1 E) (W : Type) (_ : AddCommGroup W)
          (_ : Module E W) (_ : FiniteDimensional E W) (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E),
          Hf.IsSymm ∧ Hf.SeparatingLeft ∧ Module.finrank E W = k ∧ Nonempty (↥A₁ ≃* sesqUnitaryGroup Hf)) ∧
        (∀ K : Subgroup ↥Ω, IsComponentOf K A₀ → catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU4two) := by
  intro s hs3 hs1
  have hs3' : s ^ 3 = 1 := by
    have hc : s ^ 3 ∈ Subgroup.center ↥Ω := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hpow : MulAut.conj (s ^ 3) = 1 := by
        rw [map_pow, hs3]
      have hg := congrArg (fun φ : MulAut ↥Ω => φ g) hpow
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * s ^ 3 = (s ^ 3 * g * (s ^ 3)⁻¹) * s ^ 3 := by rw [hg]
        _ = s ^ 3 * g := by rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [hZ] at hc
    exact Subgroup.mem_bot.mp hc
  have hs1' : s ≠ 1 := by
    intro h
    apply hs1
    rw [h, map_one]
  let incl : ↥Ω →* ↥(StatedSp 4 (ZMod 2)) := Subgroup.inclusion hΩ
  have hincl : Function.Injective incl := Subgroup.inclusion_injective hΩ
  have ht3 : incl s ^ 3 = 1 := by rw [← map_pow, hs3', map_one]
  have ht1 : incl s ≠ 1 := fun h => hs1' (hincl (by rw [h, map_one]))
  obtain ⟨s₀, hC⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8.exists_class_spSupported ht3 ht1
  have hmem : incl s ∈ OmInSp Ω := mem_OmInSp.mpr s.2
  have hA₁ := hU _ ht3 ht1 hmem
  have h1' := h1 _ ht3 ht1 hmem
  have h2' := h2 _ ht3 ht1 hmem
  generalize primaryMultiplicity (spEnd (incl s)) q2 = m at hC h1' h2'
  generalize spSupported (incl s) {(Polynomial.X - 1 : Polynomial (ZMod 2))} = A₀ at hC h1' h2'
  generalize spSupported (incl s) {q2} = A₁ at hC hA₁
  have hrange : incl.range = OmInSp Ω := by
    ext x
    rw [MonoidHom.mem_range, mem_OmInSp]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨(x : SpGL), hx⟩, rfl⟩
  have hA₁le : A₁ ≤ incl.range := by
    rw [hrange]
    exact hA₁
  let A₀' : Subgroup ↥Ω := A₀.comap incl
  let A₁' : Subgroup ↥Ω := A₁.comap incl
  have hcent : Subgroup.centralizer ({s} : Set ↥Ω) = A₀' ⊔ A₁' := by
    apply le_antisymm
    · intro x hx
      have hx' : incl s * incl x = incl x * incl s := by
        have := (Subgroup.mem_centralizer_iff.mp hx) s (Set.mem_singleton s)
        rw [← map_mul, ← map_mul, this]
      have hxC : incl x ∈ A₀ ⊔ A₁ := by
        rw [← hC.centralizer_eq]
        refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hx'
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hC.commute hxC
      have hbO : b ∈ OmInSp Ω := hA₁ hb
      have haO : a ∈ OmInSp Ω := by
        have hae : a = incl x * b⁻¹ := by rw [hab, mul_inv_cancel_right]
        rw [hae]
        exact (OmInSp Ω).mul_mem (mem_OmInSp.mpr x.2) ((OmInSp Ω).inv_mem hbO)
      have ha' : (⟨(a : SpGL), mem_OmInSp.mp haO⟩ : ↥Ω) ∈ A₀' := ha
      have hb' : (⟨(b : SpGL), mem_OmInSp.mp hbO⟩ : ↥Ω) ∈ A₁' := hb
      have hxe : x = (⟨(a : SpGL), mem_OmInSp.mp haO⟩ : ↥Ω) * ⟨(b : SpGL), mem_OmInSp.mp hbO⟩ := by
        apply hincl
        rw [map_mul]
        exact hab
      rw [hxe]
      exact Subgroup.mul_mem_sup ha' hb'
    · refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        apply hincl
        rw [map_mul, map_mul]
        have hcen : incl a ∈ A₀ ⊔ A₁ := Subgroup.mem_sup_left (show incl a ∈ A₀ from ha)
        rw [← hC.centralizer_eq] at hcen
        exact Subgroup.mem_centralizer_iff.mp hcen (incl s) (Set.mem_singleton _)
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        apply hincl
        rw [map_mul, map_mul]
        have hcen : incl b ∈ A₀ ⊔ A₁ := Subgroup.mem_sup_right (show incl b ∈ A₁ from hb)
        rw [← hC.centralizer_eq] at hcen
        exact Subgroup.mem_centralizer_iff.mp hcen (incl s) (Set.mem_singleton _)
  have hcomm : ∀ a ∈ A₀', ∀ b ∈ A₁', a * b = b * a := by
    intro a ha b hb
    apply hincl
    rw [map_mul, map_mul]
    exact hC.commute _ ha _ hb
  have hdisj : A₀' ⊓ A₁' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply hincl
    have hx1 : incl x ∈ A₀ ⊓ A₁ := hx
    rw [hC.disjoint] at hx1
    rw [map_one]
    exact Subgroup.mem_bot.mp hx1
  have hcomp : ∀ K : Subgroup ↥Ω, IsComponentOf K A₀' →
      catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU4two := by
    intro K hK
    have hK'' : IsComponentOf (K.map incl) (A₀ ⊓ OmInSp Ω) := by
      have h := isComponentOf_map_of_injective incl hincl hK
      have hmap : A₀'.map incl = A₀ ⊓ OmInSp Ω := by
        rw [show A₀' = A₀.comap incl from rfl, Subgroup.map_comap_eq, hrange, inf_comm]
      rwa [hmap] at h
    have hm := hC.sum_eq
    have hone := hC.one_le
    rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 by omega) with rfl | rfl | rfl | rfl
    ·
      have h := h1' rfl (K.map incl) hK''
      let eK : ↥K ≃* ↥(K.map incl) := Subgroup.equivMapOfInjective K incl hincl
      exact catalogIs_of_mulEquiv
        (QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥(K.map incl)) eK
          (Subgroup.map_center_eq eK)).symm h
    · exact (not_isComponentOf_of_solvable (h2' rfl) hK'').elim
    ·
      have hs0 : s₀ = 1 := by omega
      have hsolv : Group.IsSolvable ↥(A₀ ⊓ OmInSp Ω) := by
        rcases hC.fixed with ⟨h0, -⟩ | ⟨-, ⟨e⟩⟩
        · omega
        · haveI := sp1_solvable
          rw [hs0] at e
          have hA₀ : Group.IsSolvable ↥A₀ :=
            Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
          exact isSolvable_of_le_of_solvable inf_le_left hA₀
      exact (not_isComponentOf_of_solvable hsolv hK'').elim
    ·
      have hs0 : s₀ = 0 := by omega
      have hbot : A₀ = ⊥ := by
        rcases hC.fixed with ⟨-, h⟩ | ⟨h0, -⟩
        · exact h
        · omega
      have hsolv : Group.IsSolvable ↥(A₀ ⊓ OmInSp Ω) := by
        rw [hbot, bot_inf_eq]
        infer_instance
      exact (not_isComponentOf_of_solvable hsolv hK'').elim
  refine ⟨m, A₀', A₁', hC.one_le, by have := hC.sum_eq; omega, hcent, hcomm, hdisj, ?_, hcomp⟩
  obtain ⟨E, hEf, hE, W, hWa, hWm, hWf, Hf, hsymm, hsep, hfr, ⟨eA1⟩⟩ := hC.unitary
  obtain ⟨eA1'⟩ := comap_equiv_of_injective_le_range incl hincl A₁ hA₁le
  exact ⟨E, hEf, hE, W, hWa, hWm, hWf, Hf, hsymm, hsep, hfr, ⟨eA1'.trans eA1⟩⟩

theorem omegaCentDecomp_of_gaps (hZ : Subgroup.center ↥CFSG.AGLEmbedding.Om8 = ⊥)
    (hU : OmegaUnitaryInOm8 CFSG.AGLEmbedding.Om8) (h2 : OmegaOrthRank2Solvable CFSG.AGLEmbedding.Om8)
    (h1 : OmegaOrthRank1U4 CFSG.AGLEmbedding.Om8) : OmegaCentDecomp :=
  omegaCentDecompOf_gen CFSG.AGLEmbedding.Om8 CFSG.LocalAnalysis.GLTheoremA.CatB.om8_le_sp8 hZ hU h2 h1

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
