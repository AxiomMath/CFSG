module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2Sl3
public import CFSG.ClassicalInvolution.Balance.QNineShape
public import CFSG.LieType.Ree.ExceptionalAutomorphism

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits

section Carry

theorem leviBlockImage_of_map_equiv {p f : ℕ} [Fact p.Prime] (hq : 5 ≤ p ^ f) {K : Type}
    [Group K] (φ : K ≃* K) {U : Subgroup K} (h : LeviBlockImage p f (U.map φ.toMonoidHom)) :
    LeviBlockImage p f U := by
  have hker : φ.symm.toMonoidHom.ker ≤ Subgroup.center K := fun x hx => by
    have hx' : φ.symm x = 1 := hx
    have : x = 1 := by simpa using congrArg φ hx'
    rw [this]
    exact Subgroup.one_mem _
  have h2 := LeviBlockImage.map hq h φ.symm.toMonoidHom hker
  rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id K from
    MonoidHom.ext fun x => by simp, Subgroup.map_id] at h2

end Carry

section Long

section Datum

variable (F : Type) [Field F]

theorem g2Datum_weylAction_zero :
    weylAction (g2Datum F).isFiniteType (simple .G2 g2Short) (g2Hex 0) = g2Hex 2 :=
  (simple_smul (τ := .G2) g2Short (g2Hex 0)).trans g2Hex_reflect_zero

theorem g2Datum_isLongest_hex_two (h0 : ModelFacts.IsLongestRoot (g2Datum F) (g2Hex 0)) :
    ModelFacts.IsLongestRoot (g2Datum F) (g2Hex 2) := by
  have h := ModelFacts.IsLongest.map_weylAction h0 (simple .G2 g2Short)
  rwa [g2Datum_weylAction_zero] at h

theorem g2Datum_isPartner_hex :
    ModelFacts.IsPartner (g2Datum F).isFiniteType (g2Hex 0) (g2Hex 2) := by
  have h := ModelFacts.isPartner_single_reflection (hA := (g2Datum F).isFiniteType)
    (i := g2Long) (j := g2Short)
    (by show Tag.G2.cartan g2Long g2Short * Tag.G2.cartan g2Short g2Long = 3; decide)
  rwa [← g2Hex_zero, g2Datum_weylAction_zero] at h

end Datum

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_standardPair_partner_g2 {n f : ℕ} (hadm : StatedLieAdmissible .G2 n p f)
    {γ : Fin (modelUniv .G2 n p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .G2 n p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .G2 n p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .G2 n p f hp.out).D δ ∧
      ModelFacts.IsPartner (modelUniv .G2 n p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .G2 n p f hp.out).D.rootGroup γ ⊔
          (modelUniv .G2 n p f hp.out).D.rootGroup (-γ))
        ((modelUniv .G2 n p f hp.out).D.rootGroup δ ⊔
          (modelUniv .G2 n p f hp.out).D.rootGroup (-δ)) := by
  obtain ⟨_, _, hct, -⟩ := ModelFacts.hasBruhatDatum .G2 n p f hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := ModelFacts.cartanOK .G2 n p f hp.out trivial hadm
  have h0 : ModelFacts.IsLongestRoot (g2Datum (GaloisField p f)) (g2Hex 0) := by
    rw [g2Hex_zero]
    exact ModelFacts.isLongestRoot_single .G2 n p f hp.out trivial hadm g2Long rfl
  exact ModelFacts.exists_standardPair_partner hct hirr hratio h0 (g2Datum_isLongest_hex_two _ h0)
    (g2Datum_isPartner_hex _) g2_standardPair_base hγ

end Long

section Short

variable {K : Type} [Field K]

theorem mem_rootGroup_single_g2 (i : Fin Tag.G2.rank) {x : ↥(adjointGroup .G2 K)} :
    x ∈ (g2Datum K).rootGroup (Pi.single i 1) ↔ ∃ c : K, x = xElement i c := by
  change x ∈ rootGroup (rootOperatorFamily .G2) K _ ↔ _
  rw [mem_rootGroup_g2_iff (isRoot_single .G2 i)]
  exact exists_congr fun c => by
    rw [show (⟨pinnedX .G2 K (Pi.single i 1) c, pinnedX_mem_adjointGroup _ c⟩ :
      ↥(adjointGroup .G2 K)) = xElement i c from Subtype.ext (pinnedX_single .G2 K i c)]

theorem mem_rootGroup_neg_single_g2 (i : Fin Tag.G2.rank) {x : ↥(adjointGroup .G2 K)} :
    x ∈ (g2Datum K).rootGroup (-Pi.single i 1) ↔ ∃ c : K, x = yElement i c := by
  change x ∈ rootGroup (rootOperatorFamily .G2) K _ ↔ _
  rw [mem_rootGroup_g2_iff (isRoot_neg_single .G2 i)]
  exact exists_congr fun c => by
    rw [show (⟨pinnedX .G2 K (-Pi.single i 1) c, pinnedX_mem_adjointGroup _ c⟩ :
      ↥(adjointGroup .G2 K)) = yElement i c from Subtype.ext (pinnedX_neg_single .G2 K i c)]

theorem g2_exists_aut_map_rankOne [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 3 ^ e) :
    ∃ φ : MulAut ↥(adjointGroup .G2 K),
      ((g2Datum K).rootGroup (Pi.single g2Short 1) ⊔
        (g2Datum K).rootGroup (-Pi.single g2Short 1)).map φ.toMonoidHom =
        (g2Datum K).rootGroup (Pi.single g2Long 1) ⊔
          (g2Datum K).rootGroup (-Pi.single g2Long 1) := by
  obtain ⟨φ, hφ, -, -⟩ := CFSG.LieType.Ree.finite_exceptional_automorphism_existence .G2 e he K
    (by simpa [CFSG.LieType.Ree.ReeTag.prime] using hK)
  have hsurj : ∀ d : K, ∃ c : K, c ^ 3 = d := by
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 3 := charP_of_card_eq_prime_pow (f := e) (by
      rw [← Nat.card_eq_fintype_card, hK])
    intro d
    obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.1 (frobenius_inj K 3) d
    exact ⟨c, by simpa [frobenius_def] using hc⟩
  have hperm : CFSG.LieType.Ree.ReeTag.perm .G2 g2Short = g2Long := by
    show (Equiv.swap (0 : Fin 2) 1) (1 : Fin 2) = (0 : Fin 2)
    decide
  have hexp : CFSG.LieType.Ree.ReeTag.exponent .G2 g2Short = 3 := by
    show (if (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) then 1 else 3) = 3
    decide
  refine ⟨φ, ?_⟩
  rw [Subgroup.map_sup]
  congr 1
  · ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := (mem_rootGroup_single_g2 g2Short).1 hx
      have h := (hφ g2Short c).1
      rw [hperm, hexp] at h
      exact (mem_rootGroup_single_g2 g2Long).2 ⟨c ^ 3, h⟩
    · intro hy
      obtain ⟨d, rfl⟩ := (mem_rootGroup_single_g2 g2Long).1 hy
      obtain ⟨c, rfl⟩ := hsurj d
      refine ⟨xElement g2Short c, (mem_rootGroup_single_g2 g2Short).2 ⟨c, rfl⟩, ?_⟩
      have h := (hφ g2Short c).1
      rw [hperm, hexp] at h
      exact h
  · ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := (mem_rootGroup_neg_single_g2 g2Short).1 hx
      have h := (hφ g2Short c).2
      rw [hperm, hexp] at h
      exact (mem_rootGroup_neg_single_g2 g2Long).2 ⟨c ^ 3, h⟩
    · intro hy
      obtain ⟨d, rfl⟩ := (mem_rootGroup_neg_single_g2 g2Long).1 hy
      obtain ⟨c, rfl⟩ := hsurj d
      refine ⟨yElement g2Short c, (mem_rootGroup_neg_single_g2 g2Short).2 ⟨c, rfl⟩, ?_⟩
      have h := (hφ g2Short c).2
      rw [hperm, hexp] at h
      exact h

end Short

section Main

theorem map_map_conj_equiv {K : Type} [Group K] (φ : K ≃* K) (x : K) (U : Subgroup K) :
    (U.map (MulAut.conj x).toMonoidHom).map φ.toMonoidHom =
      (U.map φ.toMonoidHom).map (MulAut.conj (φ x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp

theorem leviBlockImage_conj_rankOne_short_g2 {p e : ℕ} [Fact p.Prime] (hp3 : p = 3)
    (hq : 5 ≤ p ^ e) (he : 1 ≤ e)
    (hlong : ∀ g : ↥(adjointGroup .G2 (GaloisField p e)),
      LeviBlockImage p e (conjSub g ((g2Datum (GaloisField p e)).rootGroup (Pi.single g2Long 1) ⊔
        (g2Datum (GaloisField p e)).rootGroup (-Pi.single g2Long 1))))
    (g : ↥(adjointGroup .G2 (GaloisField p e))) (w : WeylGroup .G2) :
    LeviBlockImage p e (conjSub g ((g2Datum (GaloisField p e)).rootGroup (w • Pi.single g2Short 1) ⊔
      (g2Datum (GaloisField p e)).rootGroup (-(w • Pi.single g2Short 1)))) := by
  obtain ⟨h, hh⟩ := ModelFacts.exists_map_conj_rankOne (g2_isCTGroupDatum (GaloisField p e)) w
  have hb : (Pi.single g2Short 1 : Fin Tag.G2.rank → ℤ) ∈ (g2Datum (GaloisField p e)).roots :=
    mem_adjDatum_roots.2 (isRoot_single .G2 g2Short)
  have h1 := hh _ hb
  have hK : Nat.card (GaloisField p e) = 3 ^ e := by
    rw [GaloisField.card p e (by omega), hp3]
  obtain ⟨φ, hφ⟩ := g2_exists_aut_map_rankOne (K := GaloisField p e) he hK
  refine leviBlockImage_of_map_equiv hq φ ?_
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := MonoidHom.ext fun y => by simp [mul_assoc]
  have h2 : (conjSub g ((g2Datum (GaloisField p e)).rootGroup (w • Pi.single g2Short 1) ⊔
      (g2Datum (GaloisField p e)).rootGroup (-(w • Pi.single g2Short 1)))).map φ.toMonoidHom =
      conjSub (φ (g * h)) ((g2Datum (GaloisField p e)).rootGroup (Pi.single g2Long 1) ⊔
        (g2Datum (GaloisField p e)).rootGroup (-Pi.single g2Long 1)) := by
    unfold conjSub
    rw [← show weylAction (g2Datum (GaloisField p e)).isFiniteType w (Pi.single g2Short 1) =
      w • Pi.single g2Short 1 from rfl, ← h1,
      Subgroup.map_map _ (MulAut.conj g).toMonoidHom (MulAut.conj h).toMonoidHom, hcomp,
      map_map_conj_equiv, hφ]
  rw [h2]
  exact hlong _

variable {p : ℕ} [hp : Fact p.Prime]

theorem leviBlockImage_conj_rankOne_g2 {n e : ℕ} (hadm : StatedLieAdmissible .G2 n p e)
    {γ : Fin (modelUniv .G2 n p e hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .G2 n p e hp.out).D γ)
    (g : (modelUniv .G2 n p e hp.out).K) :
    LeviBlockImage p e (conjSub g ((modelUniv .G2 n p e hp.out).D.rootGroup γ ⊔
      (modelUniv .G2 n p e hp.out).D.rootGroup (-γ))) := by
  obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_g2 hadm hγ
  exact Or.inl ⟨_, _, ModelFacts.linearBlockStandardPair_map_conj hW g⟩

theorem fundamental_leviBlockImage_of_g2 {t : StatedLieTag} {n e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .G2) (hp3 : p = 3) (hq : 5 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, LeviBlockImage p e R := by
  subst ht
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have he : 1 ≤ e := hadm.2.1
  have hγroot : IsRoot .G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hγroot
  have h0 : ModelFacts.IsLongestRoot (modelUniv .G2 n p e hp.out).D (Pi.single g2Long 1) :=
    ModelFacts.isLongestRoot_single .G2 n p e hp.out trivial hadm g2Long rfl
  by_cases hj : j = g2Long
  · subst hj
    have hlong : ModelFacts.IsLongestRoot (modelUniv .G2 n p e hp.out).D γ := by
      rw [← hw]
      exact ModelFacts.IsLongest.map_weylAction h0 w
    exact leviBlockImage_conj_rankOne_g2 hadm hlong g
  · have hj' : j = g2Short := by
      fin_cases j
      · exact absurd rfl hj
      · rfl
    subst hj'
    subst hw
    exact leviBlockImage_conj_rankOne_short_g2 hp3 hq he
      (fun g' => leviBlockImage_conj_rankOne_g2 hadm h0 g') g w

end Main

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_member_leviBlockImage_of_g2 (hq : 5 ≤ p ^ f) (hp3 : p = 3)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card)
    (ht : D.tag i = .G2) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      cases h
  exact exists_member_leviBlockImage_of_model hq D i hexp
    (fundamental_leviBlockImage_of_g2 (D.admissible i) ht hp3 (by rw [hexp]; exact hq))

end Component

end CFSG.ClassicalInvolution.Balance
