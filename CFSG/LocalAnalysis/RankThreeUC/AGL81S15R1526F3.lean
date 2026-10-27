module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section Row28One

theorem not_isPSolvable_barO2_of_pComponent_aux1 {A B : Type} [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hA : CFSG.HallHigman.IsPSolvable 7 A) :
    CFSG.HallHigman.IsPSolvable 7 B := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hT : CFSG.HallHigman.IsPSolvable 7 ↥(⊤ : Subgroup A) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      Subgroup.topEquiv.symm hA
  have h := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map f hT
  rw [Subgroup.map_top_of_surjective f hf] at h
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    Subgroup.topEquiv h

theorem not_isPSolvable_barO2_of_pComponent_aux2 {Q : Type} [Group Q] [Finite Q]
    (hq : CFSG.IsQuasisimple Q) (h7 : 7 ∣ Nat.card (Q ⧸ Subgroup.center Q)) :
    ¬ CFSG.HallHigman.IsPSolvable 7 Q := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro hps
  obtain ⟨-, hsimple, a, b, hab⟩ := hq
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hsimple
  have hps2 : CFSG.HallHigman.IsPSolvable 7 (Q ⧸ Subgroup.center Q) :=
    not_isPSolvable_barO2_of_pComponent_aux1 (QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective _) hps
  let e : (↥(⊤ : Subgroup (Q ⧸ Subgroup.center Q)) ⧸
      (⊥ : Subgroup ↥(⊤ : Subgroup (Q ⧸ Subgroup.center Q)))) ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.trans Subgroup.topEquiv
  haveI : IsSimpleGroup (↥(⊤ : Subgroup (Q ⧸ Subgroup.center Q)) ⧸
      (⊥ : Subgroup ↥(⊤ : Subgroup (Q ⧸ Subgroup.center Q)))) := MulEquiv.isSimpleGroup e
  have h := hps2 ⊤ Subgroup.IsSubnormal.top ⊥ inferInstance
  rw [Subgroup.index_bot, Subgroup.card_top] at h
  rcases h with h | h
  · haveI : IsCyclic (Q ⧸ Subgroup.center Q) := isCyclic_of_prime_card (p := 7) h
    exact hab (mul_comm a b)
  · exact absurd (Nat.Coprime.eq_one_of_dvd h h7) (by norm_num)

theorem not_isPSolvable_barO2_of_pComponent_aux3 {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : CFSG.IsPComponent 7 L) :
    ¬ CFSG.HallHigman.IsPSolvable 7 (↥L ⧸ CFSG.pPrimeCore 7 ↥L) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hq := CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple
    7 L hL
  exact not_isPSolvable_barO2_of_pComponent_aux2 hq
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_dvd_card_center_quotient_of_corefree_quasisimple
      7 hq (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 7))

variable {X : Type} [Group X] [Finite X]

theorem not_isPSolvable_barO2_of_pComponent_aux4 {C : Subgroup X} {L : Subgroup ↥C} {x : ↥L}
    (hx : (((x : ↥L) : ↥C) : X) ∈ CFSG.pCore 2 X) : x ∈ CFSG.pPrimeCore 7 ↥L := by
  let ι : ↥L →* X := C.subtype.comp L.subtype
  have hι : Function.Injective ι := C.subtype_injective.comp L.subtype_injective
  let A : Subgroup ↥L := (CFSG.pCore 2 X).comap ι
  have hAn : A.Normal := Subgroup.Normal.comap inferInstance ι
  have hcop : Nat.Coprime 7 (Nat.card A) := by
    have h1 : Nat.card (A.map ι) = Nat.card A := Subgroup.card_map_of_injective hι
    have h2 : A.map ι ≤ CFSG.pCore 2 X := Subgroup.map_comap_le ι _
    have h3 : Nat.card (A.map ι) ∣ Nat.card (CFSG.pCore 2 X) := Subgroup.card_dvd_of_le h2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := X))
    rw [← h1]
    rw [hk] at h3
    exact Nat.Coprime.coprime_dvd_right h3 (Nat.Coprime.pow_right k (by norm_num))
  have hle : A ≤ CFSG.pPrimeCore 7 ↥L := le_sSup ⟨hAn, hcop⟩
  exact hle (show x ∈ A from hx)

theorem not_isPSolvable_barO2_of_pComponent {C I : Subgroup X} (hIC : I ≤ C)
    (hIc : CFSG.IsPComponent 7 (I.subgroupOf C)) (hI1 : CFSG.Open.pRank 7 I = 1) :
    ¬ CFSG.HallHigman.IsPSolvable 7 ↥(barO2 I) := by
  have _ := hI1
  intro hps
  let g : ↥I →* ↥(I.subgroupOf C) :=
    { toFun := fun x => ⟨⟨x.1, hIC x.2⟩, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hg : Function.Surjective g := by
    rintro ⟨⟨c, hcC⟩, hcI⟩
    exact ⟨⟨c, hcI⟩, rfl⟩
  let φ₀ : ↥I →* (↥(I.subgroupOf C) ⧸ CFSG.pPrimeCore 7 ↥(I.subgroupOf C)) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 7 ↥(I.subgroupOf C))).comp g
  have hφ₀ : Function.Surjective φ₀ := (QuotientGroup.mk'_surjective _).comp hg
  let r : ↥I →* ↥(barO2 I) := (QuotientGroup.mk' (CFSG.pCore 2 X)).subgroupMap I
  have hr : Function.Surjective r :=
    (QuotientGroup.mk' (CFSG.pCore 2 X)).subgroupMap_surjective I
  have hker : r.ker ≤ φ₀.ker := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) (x : X) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : (x : X) ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff _).1 h1
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (CFSG.pPrimeCore 7 ↥(I.subgroupOf C)) (g x) = 1
    exact (QuotientGroup.eq_one_iff _).2
      (not_isPSolvable_barO2_of_pComponent_aux4 (L := I.subgroupOf C) (x := g x) h2)
  let ψ : ↥(barO2 I) →* (↥(I.subgroupOf C) ⧸ CFSG.pPrimeCore 7 ↥(I.subgroupOf C)) :=
    (MonoidHom.liftOfSurjective r hr) ⟨φ₀, hker⟩
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := hφ₀ q
    exact ⟨r x, MonoidHom.liftOfRightInverse_comp_apply r _ _ ⟨φ₀, hker⟩ x⟩
  exact not_isPSolvable_barO2_of_pComponent_aux3 hIc
    (not_isPSolvable_barO2_of_pComponent_aux1 ψ hψ hps)

end Row28One

section Row28Two

variable {G : Type} [Group G] [Finite G]

theorem transfer_centralizer_aux1 (M : Subgroup G) (Q : Subgroup ↥M) :
    (Subgroup.centralizer (Q : Set ↥M)).map M.subtype =
      M ⊓ Subgroup.centralizer ((Q.map M.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy d hd)
  · intro hx
    obtain ⟨hxM, hx⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show (⟨x, hxM⟩ : ↥M) ∈ Subgroup.centralizer (Q : Set ↥M)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx _ ⟨d, hd, rfl⟩)

theorem transfer_centralizer {M : Subgroup G} (Q : Subgroup ↥M) {n : ℕ}
    (h : n ≤ CFSG.Open.pRank 7 (Subgroup.centralizer (Q : Set ↥M)))
    (hns : ¬ CFSG.HallHigman.IsPSolvable 7 ↥(Subgroup.centralizer (Q : Set ↥M))) :
    n ≤ CFSG.Open.pRank 7 (M ⊓ Subgroup.centralizer ((Q.map M.subtype : Subgroup G) : Set G)) ∧
      ¬ CFSG.HallHigman.IsPSolvable 7
        ↥(M ⊓ Subgroup.centralizer ((Q.map M.subtype : Subgroup G) : Set G)) := by
  have hC := transfer_centralizer_aux1 M Q
  refine ⟨?_, ?_⟩
  · rw [← hC, CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 7
      M.subtype_injective]
    exact h
  · intro hB
    apply hns
    let e : ↥(Subgroup.centralizer (Q : Set ↥M)) ≃*
        ↥(M ⊓ Subgroup.centralizer ((Q.map M.subtype : Subgroup G) : Set G)) :=
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).trans
        (MulEquiv.subgroupCongr hC)
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      e.symm hB

end Row28Two

end CFSG.LocalAnalysis.RankThreeUC.S15
