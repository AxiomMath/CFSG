module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_10Reduced
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs710
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement
open CFSG.Open

section TypeLevel

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem i1810_centralizer_le (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hΛ : CFSG.Open.IsKGroup Λ) {p : ℕ} (hp : p.Prime)
    (hQS : CFSG.IsQuasisimple (Λ ⧸ GLAPPrimeCore p Λ))
    (hmin : ∀ M : Subgroup Λ, M.Normal → M ⊔ GLAPPrimeCore p Λ = ⊤ → M = ⊤)
    {q : ℕ} (hq : q.Prime) (Q : Subgroup Λ)
    (hQX : Q ≤ ⁅(⊤ : Subgroup Λ), GLAPPrimeCore p Λ⁆) (hQq : IsPGroup q Q)
    (hQi : ¬ q ∣ Q.relIndex ⁅(⊤ : Subgroup Λ), GLAPPrimeCore p Λ⁆)
    (hqX : q ∣ Nat.card (⁅(⊤ : Subgroup Λ), GLAPPrimeCore p Λ⁆ : Subgroup Λ)) :
    Subgroup.centralizer (Q : Set Λ) ≤
      (CFSG.Open.pCore p (Λ ⧸ GLAPPrimeCore p Λ)).comap
        (QuotientGroup.mk' (GLAPPrimeCore p Λ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set V : Subgroup Λ := GLAPPrimeCore p Λ with hVdef
  set π : Λ →* Λ ⧸ V := QuotientGroup.mk' V with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective V
  have hker : π.ker = V := QuotientGroup.ker_mk' V
  have hVp : Nat.Coprime p (Nat.card V) := CFSG.pPrimeCore_coprime_card (p := p) (G := Λ)
  have hcomm : ∀ a b : Λ, ⁅a, b⁆ ∈ V ↔ π a * π b = π b * π a := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    change π ⁅a, b⁆ = 1 ↔ _
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  have hqs : ∀ M : Subgroup Λ, M.Normal → V ≤ M → M = ⊤ ∨ ⁅M, (⊤ : Subgroup Λ)⁆ ≤ V := by
    intro M hM hVM
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQS (hM.map π hπ) with h | h
    · left
      have h' := congrArg (Subgroup.comap π) h
      rwa [Subgroup.comap_map_eq, hker, sup_eq_left.2 hVM, Subgroup.comap_top] at h'
    · right
      rw [Subgroup.commutator_le]
      intro m hm g _
      rw [hcomm]
      exact (Subgroup.mem_center_iff.1 (h ⟨m, hm, rfl⟩) (π g)).symm
  have hperf : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊤ := by
    apply hmin _ (Subgroup.commutator_normal ⊤ ⊤)
    have h1 : (⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ : Subgroup Λ).map π = ⊤ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ, ← commutator_def]
      exact hQS.1.commutator_eq_top
    have h' := congrArg (Subgroup.comap π) h1
    rwa [Subgroup.comap_map_eq, hker, Subgroup.comap_top] at h'
  have hpp : ∀ M : Subgroup Λ, M.Normal → ¬ p ∣ M.index → M = ⊤ := by
    intro M hM hidx
    have hM'n : (M ⊔ V).Normal := Subgroup.sup_normal M V
    rcases hqs (M ⊔ V) hM'n le_sup_right with h | h
    · exact hmin M hM h
    · exfalso
      set Z : Subgroup (Λ ⧸ V) := (M ⊔ V).map π with hZdef
      have hZn : Z.Normal := hM'n.map π hπ
      have hZc : Z ≤ Subgroup.center (Λ ⧸ V) := by
        rintro _ ⟨m, hm, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨g, rfl⟩ := hπ y
        have hc : ⁅m, g⁆ ∈ V := h (Subgroup.commutator_mem_commutator hm (Subgroup.mem_top g))
        exact ((hcomm m g).1 hc).symm
      have hZi : ¬ p ∣ Z.index := by
        rw [hZdef, Subgroup.index_map_eq _ hπ (hker.le.trans le_sup_right)]
        exact fun hd => hidx (hd.trans (Subgroup.index_dvd_of_le le_sup_left))
      obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p (Λ ⧸ V)))
      have hSZ : (S : Subgroup (Λ ⧸ V)) ≤ Z := i1810_le_of_not_dvd_index S.isPGroup' hZi
      have : Group.IsPerfect (Λ ⧸ V) := hQS.1
      have hS1 := i1810_card_sylow_eq_one_of_le_center S (hSZ.trans hZc)
      have hnd : ¬ p ∣ Nat.card (Λ ⧸ V) := by
        have h1 := S.not_dvd_index
        have h2 := Subgroup.card_mul_index (S : Subgroup (Λ ⧸ V))
        rw [hS1, one_mul] at h2
        rwa [h2] at h1
      have hVtop : V = ⊤ := by
        refine eq_top_iff.2 (le_sSup ⟨Subgroup.normal_top, ?_⟩)
        rw [Subgroup.card_top, Subgroup.card_eq_card_quotient_mul_card_subgroup V]
        exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd) hVp
      have h1 : ∀ y : Λ ⧸ V, y = 1 := by
        intro y
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
        refine (QuotientGroup.eq_one_iff g).2 ?_
        rw [hVtop]
        exact Subgroup.mem_top g
      obtain ⟨a, b, hab⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hQS).exists_pair_ne
      exact hab (by rw [h1 a, h1 b])
  have hmain := i1810_main hSch hΛ hp hq V hVp hmin hperf hpp hqs Q hQX hQq hQi hqX
  have hpc : CFSG.pPrimeCore p (Λ ⧸ V) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hK hKc
    have hle : K.comap π ≤ V :=
      le_sSup ⟨hK.comap π, by rw [i1810_card_comap_mk V K]; exact Nat.Coprime.mul_right hVp hKc⟩
    rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective hπ K]
    exact (Subgroup.map_mono hle).trans (le_of_eq ((Subgroup.map_eq_bot_iff V).2 hker.ge))
  have hZp : Subgroup.center (Λ ⧸ V) ≤ CFSG.Open.pCore p (Λ ⧸ V) := by
    exact le_sSup ⟨inferInstance,
      CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hpc⟩
  intro c hc
  rw [Subgroup.mem_comap]
  apply hZp
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨g, rfl⟩ := hπ y
  have h1 : ⁅c, g⁆ ∈ V :=
    hmain (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hc) (Subgroup.mem_top g))
  exact ((hcomm c g).1 h1).symm

end TypeLevel

theorem input18_10_of_schreier (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_10 := by
  intro G _ _ L hK p hp hLL q hq Q hqX hQX hQq hQi
  set V : Subgroup L := GLAPPrimeCore p L with hVdef
  obtain ⟨-, -, hcomp, hmin0⟩ := hLL
  have hA : (L.subgroupOf L).map (QuotientGroup.mk' V) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hq0 := hcomp.2.2
  rw [hA] at hq0
  have hq1 : CFSG.IsQuasisimple ↥(⊤ : Subgroup (L ⧸ V)) :=
    ⟨⟨hq0.1⟩, hq0.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq0⟩
  have hQS : CFSG.IsQuasisimple (L ⧸ V) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hq1
  have hmin : ∀ M : Subgroup L, M.Normal → M ⊔ V = ⊤ → M = ⊤ := by
    intro M hM hMV
    by_contra hne
    have hJsub : (M.map L.subtype).subgroupOf L = M :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective M
    have hJL : M.map L.subtype < L := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le M) fun h => hne ?_
      rw [← hJsub, h, Subgroup.subgroupOf_self]
    have hJsn : IsSubnormal (M.map L.subtype) L :=
      IsSubnormal.step (Subgroup.map_subtype_le M) (by rw [hJsub]; exact hM) (IsSubnormal.refl L)
    apply hmin0 _ hJL hJsn
    rw [hJsub, Subgroup.subgroupOf_self]
    have h := congrArg (Subgroup.map (QuotientGroup.mk' V)) hMV
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h
  have hXG : ⁅L, GLAPPrimeCoreOf p L⁆ = (⁅(⊤ : Subgroup L), V⁆ : Subgroup L).map L.subtype := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have hXGL : ⁅L, GLAPPrimeCoreOf p L⁆ ≤ L := by
    rw [hXG]
    exact Subgroup.map_subtype_le _
  have hXL : (⁅(⊤ : Subgroup L), V⁆ : Subgroup L) = (⁅L, GLAPPrimeCoreOf p L⁆).subgroupOf L := by
    rw [hXG]
    exact (Subgroup.comap_map_eq_self_of_injective L.subtype_injective _).symm
  have hQL : Q ≤ L := hQX.trans hXGL
  have key := i1810_centralizer_le hSch hK hp hQS hmin hq (Q.subgroupOf L)
    (by rw [hXL]; exact Subgroup.comap_mono hQX)
    (hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQL).symm)
    (by rw [hXL, Subgroup.relIndex_subgroupOf hXGL]; exact hQi)
    (by rw [hXG, Subgroup.card_map_of_injective L.subtype_injective] at hqX; exact hqX)
  intro x hx
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxC' : (⟨x, hxL⟩ : L) ∈ Subgroup.centralizer ((Q.subgroupOf L : Subgroup L) : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC y (Subgroup.mem_subgroupOf.1 hy))
  exact ⟨⟨x, hxL⟩, key hxC', rfl⟩

theorem input18_10_holds :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_10 :=
  input18_10_of_schreier CFSG.AGLEmbedding.kFactCatalogSchreier

end CFSG.HardMathSupport.Solomon.Coordinator
