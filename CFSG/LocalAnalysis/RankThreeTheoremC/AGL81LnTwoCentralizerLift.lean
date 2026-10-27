module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveOneOf
import CFSG.HardMathSupport.Cooperstein.Proving.PCoreSup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

namespace LnTwoLift

section Abstract

theorem isQuasisimple_of_surjective {E Q : Type*} [Group E] [Group Q]
    (hE : CFSG.Open.IsQuasisimple E) (f : E →* Q) (hf : Function.Surjective f) [Nontrivial Q] :
    CFSG.Open.IsQuasisimple Q := by
  haveI : Group.IsPerfect E := ⟨hE.1⟩
  haveI : IsSimpleGroup (E ⧸ Subgroup.center E) := hE.2
  have hperf : Group.IsPerfect Q := Group.IsPerfect.ofSurjective hf
  have hcenter : ∀ z ∈ Subgroup.center E, f z ∈ Subgroup.center Q := by
    intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨e, rfl⟩ := hf g
    rw [← map_mul, ← map_mul, hz e]
  let g : E ⧸ Subgroup.center E →* Q ⧸ Subgroup.center Q :=
    QuotientGroup.map _ _ f (fun z hz => hcenter z hz)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) y
    obtain ⟨e, rfl⟩ := hf q
    exact ⟨QuotientGroup.mk' (Subgroup.center E) e, rfl⟩
  have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := by
    by_contra hne
    rw [not_nontrivial_iff_subsingleton] at hne
    have hcomm : ∀ x : Q, x ∈ Subgroup.center Q := fun x => by
      have : (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).1 this
    have hle : commutator Q ≤ ⊥ := by
      refine Subgroup.commutator_le.2 fun x _ y _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.1 (hcomm y) x
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    have hx' : x ∈ commutator Q := by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top x
    exact hx (Subgroup.mem_bot.1 (hle hx'))
  exact ⟨hperf.commutator_eq_top, IsSimpleGroup.isSimpleGroup_of_surjective g hg⟩

theorem isQuasisimple_quotient_pCore_of_surjective {J E : Type*} [Group J] [Finite J] [Group E]
    (hE : CFSG.Open.IsQuasisimple E) (θ : J →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ CFSG.pCore 2 J) (h3 : 3 ∣ Nat.card J) :
    CFSG.Open.IsQuasisimple (J ⧸ CFSG.pCore 2 J) := by
  haveI : Nontrivial (J ⧸ CFSG.pCore 2 J) := by
    by_contra hne
    rw [not_nontrivial_iff_subsingleton] at hne
    have htop : CFSG.pCore 2 J = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : (QuotientGroup.mk x : J ⧸ CFSG.pCore 2 J) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).1 this
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := J)).exists_card_eq
    rw [htop, Subgroup.card_top] at hn
    rw [hn] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  let f : E →* J ⧸ CFSG.pCore 2 J :=
    (MonoidHom.liftOfSurjective θ hθ) ⟨QuotientGroup.mk' _, by
      rw [QuotientGroup.ker_mk']
      exact hker⟩
  have hfθ : ∀ x, f (θ x) = QuotientGroup.mk' (CFSG.pCore 2 J) x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply θ _ (Function.rightInverse_surjInv hθ) _ x
  refine isQuasisimple_of_surjective hE f fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 J) y
  exact ⟨θ x, hfθ x⟩

theorem exists_perfect_isSubnormal_map_eq {X Y : Type*} [Group X] [Finite X] [Group Y]
    (f : X →* Y) (D₀ : Subgroup X) (hD : ⁅D₀.map f, D₀.map f⁆ = D₀.map f) :
    ∃ I : Subgroup X, I ≤ D₀ ∧ CFSG.Open.IsSubnormal I D₀ ∧ ⁅I, I⁆ = I ∧
      I.map f = D₀.map f := by
  let S : Set (Subgroup X) :=
    {J | J ≤ D₀ ∧ CFSG.Open.IsSubnormal J D₀ ∧ J.map f = D₀.map f}
  obtain ⟨I, hI, hmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min S
    ⟨D₀, le_rfl, .refl _, rfl⟩
  obtain ⟨hID, hIs, hIm⟩ := hI
  have hle : ⁅I, I⁆ ≤ I := Subgroup.commutator_le_self I
  have hnorm : (⁅I, I⁆.subgroupOf I).Normal := by
    have h : ⁅I, I⁆.subgroupOf I = commutator ↥I := by
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.comap_map_eq_self_of_injective I.subtype_injective _
    rw [h]
    infer_instance
  have hmem : ⁅I, I⁆ ∈ S := by
    refine ⟨hle.trans hID, .step hle hnorm hIs, ?_⟩
    rw [Subgroup.map_commutator, hIm]
    exact hD
  have hnlt : ¬ ⁅I, I⁆ < I := hmin _ hmem
  have heq : ⁅I, I⁆ = I := by
    by_contra hne
    exact hnlt (lt_of_le_of_ne hle hne)
  exact ⟨I, hID, hIs, heq, hIm⟩

end Abstract

section Lift

variable {G : Type} [Group G] [Finite G]

theorem mul_mul_inv_mem_pCoreOf_of_mem {M : Subgroup G} {g x : G} (hg : g ∈ M)
    (hx : x ∈ pCoreOf 2 M) : g * x * g⁻¹ ∈ pCoreOf 2 M :=
  CFSG.HardMathSupport.Cooperstein.Proving.conj_mem_pCoreOf (Subgroup.le_normalizer hg) hx

theorem mk'_eq_of_inv_mul_mem {M : Subgroup G} {x y : G} (hx : x ∈ M) (hy : y ∈ M)
    (h : x⁻¹ * y ∈ pCoreOf 2 M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩ = QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩ := by
  obtain ⟨z, hz, hzv⟩ := CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.1 h
  have hzz : z = (⟨x, hx⟩ : ↥M)⁻¹ * ⟨y, hy⟩ := Subtype.ext hzv
  exact QuotientGroup.eq.2 (hzz ▸ hz)

theorem inv_mul_mem_of_mk'_eq {M : Subgroup G} {x y : G} (hx : x ∈ M) (hy : y ∈ M)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩) : x⁻¹ * y ∈ pCoreOf 2 M :=
  CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.2 ⟨_, QuotientGroup.eq.1 h, rfl⟩

theorem exists_centralizer_lift {M L : Subgroup G} (hLM : L ≤ M) {b : G} (hbM : b ∈ M)
    (hbn : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : orderOf b = 3) {l : G} (hl : l ∈ L)
    (hcomm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩) :
    ∃ (x : G) (hx : x ∈ M), x ∈ L ∧ x ∈ Subgroup.centralizer ({b} : Set G) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩ := by
  classical
  set N : Subgroup G := L ⊓ pCoreOf 2 M with hN
  set T : Subgroup G := L ⊔ Subgroup.zpowers b with hT
  have hbT : b ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hlT : l ∈ T := Subgroup.mem_sup_left hl
  have hTM : T ≤ M := sup_le hLM ((Subgroup.zpowers_le).2 hbM)
  have hNT : N ≤ T := inf_le_left.trans le_sup_left
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hbn)
  have hnormN : ∀ n g : G, n ∈ N → g ∈ T → g * n * g⁻¹ ∈ N := fun n g hn hg =>
    ⟨(Subgroup.mem_normalizer_iff.1 (hTL hg) n).1 hn.1,
      mul_mul_inv_mem_pCoreOf_of_mem (hTM hg) hn.2⟩
  haveI : (N.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff hNT).2 hnormN
  have hNp : IsPGroup 2 N := by
    have h2 : IsPGroup 2 (pCoreOf 2 M) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype
    exact h2.to_le inf_le_right
  have hcop : Nat.Coprime 3 (Nat.card (N.subgroupOf T)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv]
    obtain ⟨n, hn⟩ := hNp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hordT : orderOf (⟨b, hbT⟩ : T) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hb3
  have hA : IsPGroup 3 (Subgroup.zpowers (⟨b, hbT⟩ : T)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordT, pow_one])
  have key := comap_centralizer_map_le_sup Nat.prime_three (N.subgroupOf T) hcop hA
  have hcN : (l * b)⁻¹ * (b * l) ∈ N := by
    have hcomm' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l * b, M.mul_mem (hLM hl) hbM⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b * l, M.mul_mem hbM (hLM hl)⟩ := by
      have h := hcomm
      rw [← map_mul, ← map_mul] at h
      exact h
    have hc := inv_mul_mem_of_mk'_eq _ _ hcomm'
    refine ⟨?_, hc⟩
    have e : (l * b)⁻¹ * (b * l) = (b⁻¹ * l⁻¹ * b) * l := by group
    rw [e]
    have h1 := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (L : Set G)).inv_mem hbn)
      l⁻¹).1 (L.inv_mem hl)
    rw [inv_inv] at h1
    exact L.mul_mem h1 hl
  have hx : (⟨l, hlT⟩ : T) ∈ (Subgroup.centralizer
      ((((Subgroup.zpowers (⟨b, hbT⟩ : T)).map (QuotientGroup.mk' (N.subgroupOf T)) :
        Subgroup (T ⧸ N.subgroupOf T))) : Set (T ⧸ N.subgroupOf T))).comap
      (QuotientGroup.mk' (N.subgroupOf T)) := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hc : QuotientGroup.mk' (N.subgroupOf T) ⟨l, hlT⟩ *
        QuotientGroup.mk' (N.subgroupOf T) ⟨b, hbT⟩ =
        QuotientGroup.mk' (N.subgroupOf T) ⟨b, hbT⟩ *
        QuotientGroup.mk' (N.subgroupOf T) ⟨l, hlT⟩ := by
      rw [← map_mul, ← map_mul]
      exact QuotientGroup.eq.2 (by rw [Subgroup.mem_subgroupOf]; exact hcN)
    have hc' : Commute (QuotientGroup.mk' (N.subgroupOf T) ⟨b, hbT⟩)
        (QuotientGroup.mk' (N.subgroupOf T) ⟨l, hlT⟩) := hc.symm
    rw [map_zpow]
    exact (hc'.zpow_left k).eq
  have hy := key hx
  have hy' : (⟨l, hlT⟩ : T) ∈ ((N.subgroupOf T ⊔ Subgroup.centralizer
      ((Subgroup.zpowers (⟨b, hbT⟩ : T) : Subgroup T) : Set T) : Subgroup T) : Set T) := hy
  rw [Subgroup.normal_mul, Set.mem_mul] at hy'
  obtain ⟨m, hm, g, hg, hmg⟩ := hy'
  have hmN : (m : G) ∈ N := Subgroup.mem_subgroupOf.1 hm
  have hmg' : (m : G) * (g : G) = l := congrArg Subtype.val hmg
  have hgv : (g : G) = (m : G)⁻¹ * l := by rw [← hmg']; group
  have hgM : (g : G) ∈ M := hTM g.2
  refine ⟨g, hgM, ?_, ?_, ?_⟩
  · rw [hgv]
    exact L.mul_mem (L.inv_mem hmN.1) hl
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := Subgroup.mem_centralizer_iff.1 hg ⟨h, hbT⟩ (Subgroup.mem_zpowers _)
    exact congrArg Subtype.val this
  · refine mk'_eq_of_inv_mul_mem hgM (hLM hl) ?_
    rw [hgv, mul_inv_rev, inv_inv]
    have := mul_mul_inv_mem_pCoreOf_of_mem (M := M) (g := (hLM hl) |> fun _ => l⁻¹) (x := (m : G))
      (inv_mem (hLM hl)) hmN.2
    simpa [mul_assoc] using this

theorem mem_barM_iff {M L : Subgroup G} {y : ↥M ⧸ CFSG.pCore 2 ↥M} :
    y ∈ barM M L ↔ ∃ (l : G) (hl : l ∈ M), l ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hl⟩ = y := by
  unfold barM
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, x.2, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  · rintro ⟨l, hl, hlL, rfl⟩
    exact ⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.2 hlL, rfl⟩

theorem barM_self_eq_top' (X : Subgroup G) : barM X X = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) y
  exact mem_barM_iff.2 ⟨x.1, x.2, x.2, rfl⟩

theorem conj_mem_barM {M L : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgn : g ∈ Subgroup.normalizer (L : Set G)) {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hy : y ∈ barM M L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ * y *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩)⁻¹ ∈ barM M L := by
  obtain ⟨l, hl, hlL, rfl⟩ := mem_barM_iff.1 hy
  refine mem_barM_iff.2 ⟨g * l * g⁻¹, M.mul_mem (M.mul_mem hgM hl) (M.inv_mem hgM),
    (Subgroup.mem_normalizer_iff.1 hgn l).1 hlL, ?_⟩
  simp only [← map_inv, ← map_mul]
  rfl

theorem mem_normalizer_barM {M L : Subgroup G} {b : G} (hbM : b ∈ M)
    (hbn : b ∈ Subgroup.normalizer (L : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ ∈
      Subgroup.normalizer ((barM M L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hbn' : b⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).inv_mem hbn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_barM hbM hbn, fun h => ?_⟩
  have h2 := conj_mem_barM (M := M) (L := L) (M.inv_mem hbM) hbn' h
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b⁻¹, M.inv_mem hbM⟩ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e] at h2
  simpa [mul_assoc] using h2

theorem commutator_zpowers_le_pCoreOf_of_le_centralizer {M L : Subgroup G} (hLM : L ≤ M) {b : G}
    (hbM : b ∈ M) (hbz : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G))
    (hle : barM M L ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ⁅Subgroup.zpowers b, L⁆ ≤ pCoreOf 2 L := by
  set P := CFSG.pCore 2 ↥M with hP
  set π := QuotientGroup.mk' P with hπ
  set z := π ⟨b, hbM⟩ with hz
  refine Subgroup.commutator_le.2 fun g hg l hl => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hgM : b ^ k ∈ M := zpow_mem hbM k
  have hlM' : l ∈ M := hLM hl
  have hgn : b ^ k ∈ Subgroup.normalizer (L : Set G) := hbz hg
  have hyL : π ⟨l, hlM'⟩ ∈ barM M L := LnTwoLift.mem_barM_iff.2 ⟨l, hlM', hl, rfl⟩
  have hcz : Commute z (π ⟨l, hlM'⟩) := Subgroup.mem_centralizer_iff.1 (hle hyL) z rfl
  have hgz : π ⟨b ^ k, hgM⟩ = z ^ k := by
    rw [hz, ← map_zpow]
    rfl
  have hcomm : π ⟨b ^ k, hgM⟩ * π ⟨l, hlM'⟩ = π ⟨l, hlM'⟩ * π ⟨b ^ k, hgM⟩ := by
    rw [hgz]
    exact (hcz.zpow_left k).eq
  have hker : ((⟨b ^ k, hgM⟩ : ↥M) * ⟨l, hlM'⟩ * (⟨b ^ k, hgM⟩ : ↥M)⁻¹ * (⟨l, hlM'⟩ : ↥M)⁻¹)
      ∈ P := by
    rw [← QuotientGroup.ker_mk' P, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    have key : ∀ a c : ↥M ⧸ P, a * c = c * a → a * c * a⁻¹ * c⁻¹ = 1 := fun a c h => by
      rw [h]
      group
    exact key _ _ hcomm
  have hmem : b ^ k * l * (b ^ k)⁻¹ * l⁻¹ ∈ pCoreOf 2 M :=
    CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.2 ⟨_, hker, rfl⟩
  have hmemL : b ^ k * l * (b ^ k)⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.1 hgn l).1 hl) (L.inv_mem hl)
  rw [commutatorElement_def]
  exact inf_pCoreOf_le hLM ⟨hmemL, hmem⟩

theorem exists_twoPrimeComponent_of_isComponentOf {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) {b : G} (hbM : b ∈ M)
    (hbn : b ∈ Subgroup.normalizer (L : Set G)) (hord : orderOf b = 3)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hD : CFSG.Open.IsComponentOf D (barM M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M))))
    (hD3 : 3 ∣ Nat.card D) :
    ∃ I : Subgroup G, IsTwoPrimeComponent (Subgroup.centralizer ({b} : Set G) ⊓ M) I ∧
      3 ∣ Nat.card I := by
  have hLM : L ≤ M := hL.le
  set P := CFSG.pCore 2 ↥M with hP
  set π := QuotientGroup.mk' P with hπ
  set z := π ⟨b, hbM⟩ with hz
  obtain ⟨hDF, hDsub, hDqs⟩ := hD
  set S₁ : Subgroup ↥M := L.subgroupOf M ⊓ Subgroup.centralizer ({(⟨b, hbM⟩ : ↥M)} : Set ↥M)
    with hS₁
  have hcent : ∀ x : ↥M, x ∈ Subgroup.centralizer ({(⟨b, hbM⟩ : ↥M)} : Set ↥M) ↔
      x.1 ∈ Subgroup.centralizer ({b} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact congrArg Subtype.val (hx ⟨w, hbM⟩ rfl)
    · intro hx w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact Subtype.ext (hx b rfl)
  have hS₁π : S₁.map π ≤ barM M L ⊓ Subgroup.centralizer ({z} : Set (↥M ⧸ P)) := by
    rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩
    refine ⟨LnTwoLift.mem_barM_iff.2 ⟨x.1, x.2, Subgroup.mem_subgroupOf.1 hxL, rfl⟩, ?_⟩
    show π x ∈ Subgroup.centralizer ({z} : Set (↥M ⧸ P))
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have := Subgroup.mem_centralizer_iff.1 hxc ⟨b, hbM⟩ rfl
    rw [hz, ← map_mul, ← map_mul, this]
  have hFS : barM M L ⊓ Subgroup.centralizer ({z} : Set (↥M ⧸ P)) ≤ S₁.map π := by
    rintro d ⟨hdY, hdc⟩
    obtain ⟨l, hlM', hlL, rfl⟩ := LnTwoLift.mem_barM_iff.1 hdY
    have hcomm : π ⟨l, hlM'⟩ * z = z * π ⟨l, hlM'⟩ :=
      (Subgroup.mem_centralizer_iff.1 hdc z rfl).symm
    obtain ⟨x, hxM, hxL, hxc, hπx⟩ := LnTwoLift.exists_centralizer_lift hLM hbM hbn hord hlL hcomm
    exact ⟨⟨x, hxM⟩, ⟨Subgroup.mem_subgroupOf.2 hxL, (hcent _).2 hxc⟩, hπx⟩
  set D₀ : Subgroup ↥M := D.comap π ⊓ S₁ with hD₀
  have hD₀S : D₀ ≤ S₁ := inf_le_right
  have hD₀map : D₀.map π = D := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, ⟨hxD, _⟩, rfl⟩
      exact hxD
    · intro d hd
      obtain ⟨x, hxS, hxd⟩ := hFS (hDF hd)
      exact ⟨x, ⟨(show π x ∈ D from hxd ▸ hd), hxS⟩, hxd⟩
  have hsub1 : CFSG.Open.IsSubnormal D₀ S₁ := by
    have h1 := (CFSG.Open.IsSubnormal.comap π hDsub).inf S₁
    have hS₁le : S₁ ≤ (barM M L ⊓ Subgroup.centralizer ({z} : Set (↥M ⧸ P))).comap π :=
      fun x hx => hS₁π ⟨x, hx, rfl⟩
    rwa [inf_eq_right.2 hS₁le] at h1
  have hDperf : ⁅D, D⁆ = D := by
    rw [← Subgroup.map_subtype_commutator, hDqs.1, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨I₁, hI₁D, hI₁sub, hI₁perf, hI₁map⟩ :=
    LnTwoLift.exists_perfect_isSubnormal_map_eq π D₀ (by rw [hD₀map]; exact hDperf)
  have hI₁D' : I₁.map π = D := hI₁map.trans hD₀map
  set I : Subgroup G := I₁.map M.subtype with hI
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) ⊓ M with hC
  have hS₁map : S₁.map M.subtype = L ⊓ Subgroup.centralizer ({b} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyL, hyc⟩, rfl⟩
      exact ⟨Subgroup.mem_subgroupOf.1 hyL, (hcent y).1 hyc⟩
    · rintro ⟨hxL, hxc⟩
      exact ⟨⟨x, hLM hxL⟩, ⟨Subgroup.mem_subgroupOf.2 hxL, (hcent ⟨x, hLM hxL⟩).2 hxc⟩, rfl⟩
  have hIsub : CFSG.Open.IsSubnormal I C := by
    have h1 : CFSG.Open.IsSubnormal I (S₁.map M.subtype) :=
      (hI₁sub.trans hsub1).map M.subtype
    rw [hS₁map] at h1
    have h2 := hL.subnormal.inf (Subgroup.centralizer ({b} : Set G))
    rw [inf_comm M] at h2
    exact h1.trans h2
  have hIperf : ⁅I, I⁆ = I := by
    rw [hI, ← Subgroup.map_commutator, hI₁perf]
  have hIC : I ≤ C := by
    rintro _ ⟨y, hy, rfl⟩
    have hyS : y ∈ S₁ := hD₀S (hI₁D hy)
    exact ⟨(hcent y).1 hyS.2, y.2⟩
  have hIM : I ≤ M := hIC.trans inf_le_right
  let θ0 : ↥I →* ↥M ⧸ P := π.comp (Subgroup.inclusion hIM)
  have hθD : ∀ x : ↥I, θ0 x ∈ D := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.2
    have e : θ0 x = π y := by
      show π ⟨x.1, hIM x.2⟩ = π y
      congr 1
      exact Subtype.ext hyx.symm
    rw [e, ← hI₁D']
    exact ⟨y, hy, rfl⟩
  let θ : ↥I →* ↥D := θ0.codRestrict D hθD
  have hθs : Function.Surjective θ := by
    rintro ⟨d, hd⟩
    rw [← hI₁D'] at hd
    obtain ⟨y, hy, rfl⟩ := hd
    exact ⟨⟨y.1, y, hy, rfl⟩, rfl⟩
  have hker : θ.ker ≤ CFSG.pCore 2 ↥I := by
    intro x hx
    have h1 : π ⟨x.1, hIM x.2⟩ = 1 := congrArg Subtype.val hx
    have h2 : (⟨x.1, hIM x.2⟩ : ↥M) ∈ P := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : x.1 ∈ pCoreOf 2 M :=
      CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.2 ⟨_, h2, rfl⟩
    obtain ⟨y, hy, hyx⟩ := CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.1
      (inf_pCoreOf_le hIM ⟨x.2, h3⟩)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have h3I : 3 ∣ Nat.card ↥I := hD3.trans (Subgroup.card_dvd_of_surjective hθs)
  have hqsI : CFSG.Open.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I) :=
    LnTwoLift.isQuasisimple_quotient_pCore_of_surjective hDqs θ hθs hker h3I
  have hII : IsTwoPrimeComponent I I :=
    { le := le_rfl
      subnormal := .refl I
      perfect := hIperf
      component := ⟨le_top, by rw [LnTwoLift.barM_self_eq_top']; exact .refl _, by
        rw [LnTwoLift.barM_self_eq_top']
        exact CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hqsI⟩ }
  exact ⟨I, isTwoPrimeComponent_of_self hII hIC hIsub, h3I⟩

end Lift

end LnTwoLift

@[expose] def KFactLnTwoCentralizerAbs : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (Y : Subgroup Z) (z : Z) (r : ℕ),
    IsLieOver ↥Y (.A r) 2 1 → z ∈ Subgroup.normalizer (Y : Set Z) → z ^ 3 = 1 →
    ¬ Y ≤ Subgroup.centralizer ({z} : Set Z) →
    ∃ D : Subgroup Z, CFSG.Open.IsComponentOf D (Y ⊓ Subgroup.centralizer ({z} : Set Z)) ∧
      3 ∣ Nat.card D

section Main

variable {G : Type} [Group G] [Finite G]

theorem kFactLnTwoCentralizer_of (h : KFactLnTwoCentralizerAbs) : KFactLnTwoCentralizer G := by
  intro M L b r hL _ hLie hbM hbz hord hnot
  have hLM : L ≤ M := hL.le
  have hbn : b ∈ Subgroup.normalizer (L : Set G) := hbz (Subgroup.mem_zpowers b)
  set P := CFSG.pCore 2 ↥M with hP
  set π := QuotientGroup.mk' P with hπ
  set z := π ⟨b, hbM⟩ with hz
  have hz3 : z ^ 3 = 1 := by
    rw [hz, ← map_pow]
    have : (⟨b, hbM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (hord ▸ pow_orderOf_eq_one b)
    rw [this, map_one]
  have hnotc : ¬ barM M L ≤ Subgroup.centralizer ({z} : Set (↥M ⧸ P)) := fun hle =>
    hnot (LnTwoLift.commutator_zpowers_le_pCoreOf_of_le_centralizer hLM hbM hbz hle)
  obtain ⟨D, hD, hD3⟩ :=
    h (↥M ⧸ P) (barM M L) z r hLie (LnTwoLift.mem_normalizer_barM hbM hbn) hz3 hnotc
  exact LnTwoLift.exists_twoPrimeComponent_of_isComponentOf hL hbM hbn hord hD hD3

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC
