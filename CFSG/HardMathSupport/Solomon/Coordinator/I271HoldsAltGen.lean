module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Orbits
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Equiv Equiv.Perm MulAction CFSG.Open GL83 GL83.CompFam GL83.PiGen

section PermGen

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {p : ℕ} [Fact p.Prime]

theorem i271h_perm_gen (hp3 : 3 ≤ p) {R : Subgroup (Perm Ω)} (hR : IsPGroup p R)
    (hnp : ¬ p ∣ Fintype.card Ω) (h3 : 3 ≤ Fintype.card Ω)
    (horb : ∀ ω : Ω, Nat.card (orbit R ω) ≤ p) :
    alternatingGroup Ω ≤ ⨆ (E : {E : Subgroup (Perm Ω) // E ≤ R ∧ Nat.card R ≤ p * Nat.card E}),
      altOn (fixSet E.1) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hmod : ∀ E : Subgroup (Perm Ω), E ≤ R →
      Fintype.card Ω ≡ Nat.card (fixSet E) [MOD p] := by
    intro E hE
    have := card_fixSet_modEq (p := p) (hR.to_le hE)
    rwa [Nat.card_eq_fintype_card] at this
  have hω₀ : ∃ ω₀, ω₀ ∈ fixSet R := by
    by_contra h
    have h' : ∀ ω, ω ∉ fixSet R := fun ω hω => h ⟨ω, hω⟩
    have hempty : fixSet R = ∅ := Set.eq_empty_of_forall_notMem h'
    have hm := hmod R le_rfl
    have h0 : Nat.card (fixSet R) = 0 := by rw [hempty]; simp
    rw [h0] at hm
    exact hnp ((Nat.modEq_zero_iff_dvd).1 hm)
  let P : Subgroup (Perm Ω) → Prop := fun E =>
    E ≤ R ∧ Nat.card R ≤ p * Nat.card E ∧ 3 ≤ Nat.card (fixSet E)
  have hgood : ∀ ω : Ω, ω ∉ fixSet R → P (stabIn R ω) ∧ ω ∈ fixSet (stabIn R ω) := by
    intro ω hω
    refine ⟨⟨stabIn_le R ω, ?_, ?_⟩, mem_fixSet_stabIn R ω⟩
    · rw [card_mul_card_stabIn R ω]
      exact Nat.mul_le_mul_right _ (horb ω)
    · have hsub : fixSet R ⊆ fixSet (stabIn R ω) := fixSet_anti (stabIn_le R ω)
      have hss : fixSet R ⊂ fixSet (stabIn R ω) :=
        ⟨hsub, fun h => hω (h (mem_fixSet_stabIn R ω))⟩
      have hlt : Nat.card (fixSet R) < Nat.card (fixSet (stabIn R ω)) := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        exact Set.ncard_lt_ncard hss
      have h1 := hmod R le_rfl
      have h2 := hmod (stabIn R ω) (stabIn_le R ω)
      have h3' : Nat.card (fixSet R) ≡ Nat.card (fixSet (stabIn R ω)) [MOD p] := h1.symm.trans h2
      have h4 := (Nat.modEq_iff_dvd' hlt.le).1 h3'
      have h5' : p ≤ Nat.card (fixSet (stabIn R ω)) - Nat.card (fixSet R) :=
        Nat.le_of_dvd (by omega) h4
      omega
  have hcover : ∀ ω : Ω, ∃ E, P E ∧ ω ∈ fixSet E := by
    intro ω
    by_cases hnt : ∃ ω', ω' ∉ fixSet R
    · by_cases hω : ω ∈ fixSet R
      · obtain ⟨ω', hω'⟩ := hnt
        exact ⟨stabIn R ω', (hgood ω' hω').1, fixSet_anti (stabIn_le R ω') hω⟩
      · exact ⟨stabIn R ω, (hgood ω hω).1, (hgood ω hω).2⟩
    · have hall : ∀ ω', ω' ∈ fixSet R := fun ω' => by_contra fun h => hnt ⟨ω', h⟩
      have hfix : fixSet R = Set.univ := Set.eq_univ_of_forall hall
      refine ⟨R, ⟨le_rfl, ?_, ?_⟩, hall ω⟩
      · have : 1 ≤ p := hp.one_lt.le
        nlinarith [Nat.card_pos (α := R)]
      · rw [hfix, Nat.card_univ, Nat.card_eq_fintype_card]
        exact h3
  obtain ⟨ω₀, hω₀R⟩ := hω₀
  have : Nonempty Ω := ⟨ω₀⟩
  let ι : Type _ := {E : Subgroup (Perm Ω) // P E}
  have hS3 : ∀ E : ι, 3 ≤ (fixSet E.1).ncard := fun E => by
    have := E.2.2.2
    rwa [Nat.card_coe_set_eq] at this
  have hcov : (⋃ E : ι, fixSet E.1) = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    obtain ⟨E, hE, hωE⟩ := hcover ω
    exact Set.mem_iUnion.2 ⟨⟨E, hE⟩, hωE⟩
  have hconn : ∀ i j : ι,
      Relation.ReflTransGen (fun a b : ι => (fixSet a.1 ∩ fixSet b.1).Nonempty) i j :=
    fun i j => Relation.ReflTransGen.single
      ⟨ω₀, fixSet_anti i.2.1 hω₀R, fixSet_anti j.2.1 hω₀R⟩
  have hgen := iSup_altOn_eq_alternatingGroup (S := fun E : ι => fixSet E.1) hS3 hcov hconn
  rw [← hgen]
  exact iSup_le fun E => le_iSup_of_le ⟨E.1, E.2.1, E.2.2.1⟩ le_rfl

end PermGen

section Transfer

variable {X : Type*} [Group X] [Finite X] {K A : Subgroup X}

theorem i271h_le_centGenI_of_alt {p n : ℕ} [Group.IsPerfect K]
    (hA : A ≤ Subgroup.normalizer (K : Set X)) (hZ : Subgroup.center K = ⊥) (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hgen : alternatingGroup (Fin n) ≤ ⨆ (E : {E : Subgroup (Perm (Fin n)) //
      E ≤ (permHom hA hn hn6 e).range ∧
        Nat.card (permHom hA hn hn6 e).range ≤ p * Nat.card E}), altOn (fixSet E.1)) :
    K ≤ centGenI p A K := by
  classical
  set π := permHom hA hn hn6 e with hπ
  set R := π.range with hR
  have hinj : Function.Injective
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) := by
    intro x y hxy
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = QuotientGroup.mk y :=
      e.injective hxy
    have h2 := QuotientGroup.eq.1 h1
    rw [hZ, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.1 h2
  have hsurj : Function.Surjective
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  let φ : K ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have hφ : ∀ k : K, φ k = e (QuotientGroup.mk k) := fun k => rfl
  let f : ↥(alternatingGroup (Fin n)) →* X := K.subtype.comp φ.symm.toMonoidHom
  have hfx : ∀ x : ↥(alternatingGroup (Fin n)), e (QuotientGroup.mk (φ.symm x)) = x := fun x => by
    rw [← hφ]
    exact φ.apply_symm_apply x
  let ι := {E : Subgroup (Perm (Fin n)) // E ≤ R ∧ Nat.card R ≤ p * Nat.card E}
  let Etil : ι → Subgroup X := fun E => (E.1.comap π).map A.subtype
  have hEtle : ∀ E : ι, Etil E ≤ A := fun E => Subgroup.map_subtype_le _
  have hEtcard : ∀ E : ι, Nat.card A ≤ p * Nat.card (Etil E) := by
    intro E
    obtain ⟨hER, hEi⟩ := E.2
    let E' : Subgroup A := E.1.comap π
    have h1 : Nat.card E' * E'.index = Nat.card A := Subgroup.card_mul_index E'
    have h2 : E'.index = E.1.relIndex R := Subgroup.index_comap E.1 π
    have h3 : E.1.relIndex R * Nat.card E.1 = Nat.card R := by
      have := Subgroup.relIndex_mul_card (H := E.1) (K := R)
      rwa [inf_eq_left.2 hER] at this
    have h4 : E.1.relIndex R ≤ p := by
      have hpos : 0 < Nat.card E.1 := Nat.card_pos
      by_contra hlt
      have : p * Nat.card E.1 < E.1.relIndex R * Nat.card E.1 :=
        Nat.mul_lt_mul_of_pos_right (not_le.1 hlt) hpos
      omega
    show Nat.card A ≤ p * Nat.card ((E.1.comap π).map A.subtype)
    rw [Subgroup.card_map_of_injective A.subtype_injective, ← h1, h2]
    calc Nat.card E' * E.1.relIndex R ≤ Nat.card E' * p := Nat.mul_le_mul_left _ h4
      _ = p * Nat.card E' := mul_comm _ _
  have hT : ∀ E : ι, ∀ x : ↥(alternatingGroup (Fin n)),
      (x : Perm (Fin n)) ∈ altOn (fixSet E.1) →
        f x ∈ K ⊓ Subgroup.centralizer (Etil E : Set X) := by
    intro E x hx
    refine ⟨(φ.symm x).2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨a, haE, rfl⟩ := hg
    obtain ⟨y, hy, hspec⟩ := permHom_spec hA hn hn6 e a (φ.symm x)
    rw [hfx x] at hspec
    have hdisj : (π a).Disjoint (x : Perm (Fin n)) := by
      intro ω
      by_cases hω : ω ∈ fixSet E.1
      · exact Or.inl (hω (π a) haE)
      · exact Or.inr ((mem_altOn.1 hx).2 ω hω)
    have hcomm : π a * (x : Perm (Fin n)) * (π a)⁻¹ = (x : Perm (Fin n)) := by
      rw [hdisj.commute.eq]
      group
    rw [hcomm] at hspec
    have h1 : (e (QuotientGroup.mk y) : alternatingGroup (Fin n)) = e (QuotientGroup.mk (φ.symm x)) := by
      rw [hfx x]
      exact (Subtype.ext hspec).symm
    have h2 : (QuotientGroup.mk y : K ⧸ Subgroup.center K) = QuotientGroup.mk (φ.symm x) :=
      e.injective h1
    have h3 := QuotientGroup.eq.1 h2
    rw [hZ, Subgroup.mem_bot] at h3
    have h4 : y = φ.symm x := inv_mul_eq_one.1 h3
    have h5 : (a : X) * ((φ.symm x : K) : X) * (a : X)⁻¹ = ((φ.symm x : K) : X) := by
      rw [← hy, h4]
    show (a : X) * f x = f x * (a : X)
    calc (a : X) * f x = ((a : X) * f x * (a : X)⁻¹) * a := by group
      _ = f x * a := by
        have : f x = ((φ.symm x : K) : X) := rfl
        rw [this, h5]
  have key : f.range ≤ ⨆ E : ι, K ⊓ Subgroup.centralizer (Etil E : Set X) :=
    range_le_iSup_of_le_iSup (S := fun E : ι => altOn (fixSet E.1)) (fun E => inf_le_left) hgen f
      (T := fun E : ι => K ⊓ Subgroup.centralizer (Etil E : Set X)) hT
  have hK : K ≤ f.range := fun k hk => ⟨φ ⟨k, hk⟩, by simp [f]⟩
  exact hK.trans (key.trans (iSup_le fun E => le_centGenI (hEtle E) (hEtcard E)))

end Transfer

section InGOne

variable {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem i271h_pRank_sub_one_le {B E : Subgroup X} (hB : IsElemAbelian p B) (hEB : E ≤ B)
    (hE : Nat.card B ≤ p * Nat.card E) :
    CFSG.Open.pRank p B - 1 ≤ CFSG.Open.pRank p E := by
  have hp := (Fact.out : p.Prime)
  have hEel : IsElemAbelian p E := elem_mono hB hEB
  obtain ⟨j, hj⟩ := exists_card_eq_pow hEel
  have hjr : j ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEel hj
  have h1 : p ^ CFSG.Open.pRank p B ≤ p ^ (j + 1) := by
    calc p ^ CFSG.Open.pRank p B = Nat.card B := (card_eq_pow_pRank hB).symm
      _ ≤ p * Nat.card E := hE
      _ = p ^ (j + 1) := by rw [hj, pow_succ, mul_comm]
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  omega

theorem i271h_isInGOne_of_centGenI {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (h4 : 4 ≤ CFSG.Open.pRank p B)
    (hgen : K ≤ centGenI p (stab B K) K) : IsInGOne p B K := by
  have hstab : stab B K = B := inf_of_le_left hBN
  rw [hstab] at hgen
  refine i271h_isInGOne_of_le hBN (hgen.trans (iSup_le fun E => ?_))
  have hE3 : 3 ≤ CFSG.Open.pRank p E.1 := by
    have := i271h_pRank_sub_one_le hB E.2.1 E.2.2
    omega
  exact i271h_le_coreIn_of_le_centralizer E.2.1 hE3 le_rfl

end InGOne

end CFSG.HardMathSupport.Solomon.Coordinator
