module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma33
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.SolStdInL

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def IsLS (S : List TauCeti.SporadicName) (X : Type) [Group X] : Prop :=
  ∃ s ∈ S, CFSG.IsQuasisimple X ∧ Odd (Nat.card (center X)) ∧ IsSporadic (X ⧸ center X) s

theorem isLS_iff {S : List TauCeti.SporadicName} {H : Type} [Group H] {M : Subgroup H} :
    IsLS S ↥M ↔ ∃ s ∈ S, OddCover s M := Iff.rfl

section KChains

variable {H : Type} [Group H] [Finite H] {IsK : GroupClass} {N : Subgroup H}

theorem isKChain_lt_card {m : ℕ} (h : IsKChain IsK N m) : m < Nat.card (Subgroup H) := by
  obtain ⟨L, T, s, hch, -⟩ := h
  have : Finite (Subgroup H) :=
    Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective
  have hinj : Function.Injective (fun i : Fin (m + 1) => L i) := fun a b hab =>
    Fin.ext (hch.inj a (by omega) b (by omega) hab)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem exists_isMaxKChain {m₀ : ℕ} (h : IsKChain IsK N m₀) : ∃ n, IsMaxKChain IsK N n := by
  classical
  have hlt := isKChain_lt_card h
  exact ⟨Nat.findGreatest (fun m => IsKChain IsK N m) (Nat.card (Subgroup H)),
    Nat.findGreatest_spec (P := fun m => IsKChain IsK N m) hlt.le h,
    fun m hm => Nat.le_findGreatest (isKChain_lt_card hm).le hm⟩

end KChains

section Relation

variable {H : Type} [Group H]

theorem centralizer_zpowers_eq (u : H) :
    centralizer ((zpowers u : Subgroup H) : Set H) = centralizer ({u} : Set H) := by
  ext x
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    exact h g (hg ▸ mem_zpowers u)
  · intro h g hg
    have hle : zpowers u ≤ centralizer ({x} : Set H) := by
      rw [Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.2 (h u rfl)
    exact mem_centralizer_singleton_iff.1 (hle hg)

theorem centralizer_sup_zpowers_eq (u t : H) :
    centralizer ((zpowers u ⊔ zpowers t : Subgroup H) : Set H) =
      centralizer ({u} : Set H) ⊓ centralizer ({t} : Set H) := by
  ext x
  rw [mem_inf, mem_centralizer_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨(h u (mem_sup_left (mem_zpowers u))).symm, (h t (mem_sup_right (mem_zpowers t))).symm⟩
  · rintro ⟨hu, hs⟩ g hg
    have hle : zpowers u ⊔ zpowers t ≤ centralizer ({x} : Set H) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact mem_centralizer_singleton_iff.2 hu.symm
      · rw [Subgroup.zpowers_le]
        exact mem_centralizer_singleton_iff.2 hs.symm
    exact mem_centralizer_singleton_iff.1 (hle hg)

theorem isPGroup_zpowers_of_orderOf_two {u : H} (hu : orderOf u = 2) :
    IsPGroup 2 ↥(zpowers u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)

theorem lt_of_le_sup_conj [Finite H] {K M : Subgroup H} {t u : H} (hu : orderOf u = 2)
    (ht : orderOf t = 2) (hcomm : u * t = t * u)
    (hK : IsCompIn K (centralizer ({u} : Set H) ⊓ centralizer ({t} : Set H)))
    (hM : IsCompIn M (centralizer ({u} : Set H))) (hKM : K ≤ M ⊔ CFSG.conjugate M t) : Lt K M := by
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; omega
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  have hTp : IsPGroup 2 ↥(zpowers u) := isPGroup_zpowers_of_orderOf_two hu
  have hts : t ∈ normalizer ((zpowers u : Subgroup H) : Set H) := by
    refine Subgroup.centralizer_le_normalizer ((zpowers u : Subgroup H) : Set H) ?_
    rw [centralizer_zpowers_eq]
    exact mem_centralizer_singleton_iff.2 hcomm.symm
  have ht2 : t ^ 2 ∈ zpowers u := by
    have h1 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht] at this
    rw [h1]
    exact one_mem _
  have hSp : IsPGroup 2 ↥(zpowers u ⊔ zpowers t) := isPGroup_sup_zpowers hTp hts ht2
  refine ⟨zpowers u ⊔ zpowers t, zpowers u, ?_, ?_, hSp, hTp, ?_, ?_, ?_, ?_⟩
  · intro hb
    apply hu1
    have : u ∈ (⊥ : Subgroup H) := hb ▸ mem_sup_left (mem_zpowers u)
    exact Subgroup.mem_bot.1 this
  · intro hb
    apply hu1
    have : u ∈ (⊥ : Subgroup H) := hb ▸ mem_zpowers u
    exact Subgroup.mem_bot.1 this
  · have : ⁅zpowers u ⊔ zpowers t, zpowers u⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact mem_centralizer_singleton_iff.2 rfl
      · rw [Subgroup.zpowers_le]
        exact mem_centralizer_singleton_iff.2 hcomm.symm
    rw [this]
    exact bot_le
  · rw [centralizer_sup_zpowers_eq]
    exact hK
  · rw [centralizer_zpowers_eq]
    exact hM
  · refine hKM.trans (sup_le ?_ ?_)
    · refine le_iSup₂_of_le 1 (one_mem _) ?_
      intro x hx
      exact ⟨x, hx, by simp⟩
    · refine le_iSup₂_of_le t⁻¹ (Subgroup.inv_mem _ (mem_sup_right (mem_zpowers t))) ?_
      exact le_rfl

end Relation

section FStar

variable {H : Type} [Group H] {N : Subgroup H}

theorem FStarSimple.isQuasisimple (hN : FStarSimple N) : CFSG.IsQuasisimple ↥N := by
  have := hN.isSimpleGroup
  have hnonab := hN.nonabelian
  have hc : center ↥N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥N) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (mem_center_iff.1 (h1 ▸ mem_top b) a)
  have hperf : Group.IsPerfect ↥N := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup ↥N), (⊤ : Subgroup ↥N)⁆ with
        h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
      exact hab (mem_centralizer_iff.1 (hcen (mem_top a)) b (mem_top b)).symm
    · exact h1
  let e : (↥N ⧸ center ↥N) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨hperf, MulEquiv.isSimpleGroup e, ?_⟩
  obtain ⟨a, b, hab⟩ := hnonab
  refine ⟨QuotientGroup.mk a, QuotientGroup.mk b, fun h => hab ?_⟩
  have h1 := congrArg e h
  have he : ∀ x : ↥N, e (QuotientGroup.mk x) = x := fun x => rfl
  rwa [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, he, he] at h1

theorem FStarSimple.eq_bot_of_isCompIn [Finite H] (hN : FStarSimple N) {T : Subgroup H}
    (hT : IsCompIn N (centralizer (T : Set H))) : T = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxC : x ∈ centralizer (N : Set H) := mem_centralizer_iff.2 fun m hm =>
    (mem_centralizer_iff.1 (hT.1 hm) x hx).symm
  have hxN : x ∈ N := hN.centralizer_le hxC
  have hz : (⟨x, hxN⟩ : ↥N) ∈ center ↥N := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hxC g g.2)
  have hc : center ↥N = ⊥ := by
    have h1 : centerIn N = ⊥ := hN.centerIn_eq_bot
    unfold centerIn at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 h1
  rw [hc, Subgroup.mem_bot] at hz
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)

end FStar

theorem KLike.of_isK {H : Type} [Group H] {IsK : GroupClass} {X : Subgroup H} (h : IsK ↥X) :
    KLike IsK X :=
  ⟨↥X, inferInstance, MonoidHom.id _, Function.surjective_id, by simp, h⟩

section Standard

variable {H : Type} [Group H] [Finite H]

theorem solStd_of_inL_stdBare {L : Subgroup H} (hL : InL L) (hstd : StdBare L) : SolStd L :=
  hL.solStd hstd

end Standard

end CFSG.EvenSporadicStandard.Induction
