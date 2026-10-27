module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Lift
public import CFSG.Open.LocalVocabulary
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration

open CFSG.Open Subgroup
open scoped commutatorElement

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ center G := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem conj_injective_of_center_eq_bot {G : Type*} [Group G] (h : center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : g ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 : g * y * g⁻¹ = y := by
      simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut G => φ y) hg
    calc y * g = g * y * g⁻¹ * g := by rw [h2]
      _ = g * y := by group
  rw [h] at hc
  exact hc

theorem exists_noncomm_center_quotient {G : Type*} [Group G] (hperf : commutator G = ⊤)
    [IsSimpleGroup (G ⧸ center G)] : ∃ a b : G ⧸ center G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hle : commutator G ≤ center G := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h1 : (QuotientGroup.mk' (center G)) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcon _ _)
    exact (QuotientGroup.eq_one_iff _).1 h1
  rw [hperf, top_le_iff] at hle
  have hcomm : ∀ a b : G, a * b = b * a := fun a b =>
    Subgroup.mem_center_iff.1 (hle ▸ Subgroup.mem_top b) a
  have hbot : commutator G = ⊥ := by
    rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm x y)
  rw [hperf] at hbot
  have hsub : Subsingleton G := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  haveI : Subsingleton (G ⧸ center G) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  exact not_subsingleton (G ⧸ center G) inferInstance

theorem isCyclic_sylow_of_pRank_le_one {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (h : Open.pRank p (⊤ : Subgroup K) ≤ 1) (T : Sylow p K) :
    IsCyclic (T : Subgroup K) := by
  by_contra hnc
  haveI : Fact (IsPGroup p (T : Subgroup K)) := ⟨T.isPGroup'⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hel : IsElemAbelian p S :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).1 hSel
  have hel' : IsElemAbelian p (S.map (T : Subgroup K).subtype) :=
    CFSG.SectionRank.isElemAbelian_map hel _
  have hcard : Nat.card (S.map (T : Subgroup K).subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (T : Subgroup K).subtype_injective, hScard]
  have := GH74.Uniqueness.SU.SU1.le_pRank (Fact.out : p.Prime).one_lt le_top hel' hcard
  omega

variable {X : Type*} [Group X] [Finite X]

theorem exists_outer_plane {p : ℕ} [Fact p.Prime] {K : Subgroup X} [K.Normal]
    (hperf : commutator ↥K = ⊤) [IsSimpleGroup (K ⧸ center K)]
    {A : Subgroup X} (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hcen : Nat.card ↥(A ⊓ centralizer (K : Set X)) ≤ p)
    (hrk : Open.pRank p (⊤ : Subgroup (K ⧸ center K)) ≤ 1) :
    ∃ E : Subgroup (MulAut (K ⧸ center K)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ¬ E ≤ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range ∧
      E ≤ A.map (barAct K) := by
  classical
  have hp : p.Prime := Fact.out
  set φ := barAct K with hφ
  set F : Subgroup (MulAut (K ⧸ center K)) := A.map φ with hF
  have hFel : IsElemAbelian p F := CFSG.SectionRank.isElemAbelian_map hA φ
  have hker : φ.ker ⊓ A ≤ A ⊓ centralizer (K : Set X) := by
    intro x hx
    refine ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    exact (commute_of_barAct_eq_one hperf (MonoidHom.mem_ker.1 hx.1) k hk).symm
  have hkc : Nat.card ↥(φ.ker ⊓ A) ≤ p :=
    (Subgroup.card_le_of_le hker).trans hcen
  have hmul : Nat.card F * Nat.card ↥(φ.ker ⊓ A) = p ^ 3 := by
    rw [← hAcard, ← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]
  have hFcard : p ^ 2 ≤ Nat.card F := by
    have h3 : p ^ 2 * p ≤ Nat.card F * p := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ = Nat.card F * Nat.card ↥(φ.ker ⊓ A) := hmul.symm
        _ ≤ Nat.card F * p := Nat.mul_le_mul_left _ hkc
    exact Nat.le_of_mul_le_mul_right h3 hp.pos
  have hcenter : center (K ⧸ center K) = ⊥ :=
    center_eq_bot_of_simple (exists_noncomm_center_quotient hperf)
  have hFnot : ¬ F ≤ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range := by
    intro hle
    have hinj := conj_injective_of_center_eq_bot hcenter
    set F' : Subgroup (K ⧸ center K) := F.comap (MulAut.conj : (K ⧸ center K) →* _) with hF'
    have hmap : F'.map (MulAut.conj : (K ⧸ center K) →* _) = F := Subgroup.map_comap_eq_self hle
    have hF'card : Nat.card F' = Nat.card F := by
      have := Subgroup.card_map_of_injective (K := F') hinj
      rw [hmap] at this
      exact this.symm
    have hF'el : IsElemAbelian p F' := hFel.comap hinj
    obtain ⟨k, hk⟩ := GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hF'el
    have hk2 : 2 ≤ k := by
      rw [hk] at hF'card
      have : p ^ 2 ≤ p ^ k := hF'card ▸ hFcard
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
    have := GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_top hF'el hk
    omega
  obtain ⟨f, hfF, hfInn⟩ := Set.not_subset.1 hFnot
  have hfp : f ^ p = 1 := hFel.2 f hfF
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact hfInn (Subgroup.one_mem _)
  have hfo : orderOf f = p := orderOf_eq_prime hfp hf1
  have hex : ∃ f' ∈ F, f' ∉ zpowers f := by
    by_contra hcon
    push Not at hcon
    have hle : F ≤ zpowers f := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hfo] at h1
    have h2 : p < p ^ 2 := by
      have := hp.one_lt
      nlinarith
    omega
  obtain ⟨f', hf'F, hf'ne⟩ := hex
  obtain ⟨hEel, hEcard⟩ := GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp hfp
    (hFel.2 f' hf'F) hf1 hf'ne (hFel.comm hfF hf'F)
  refine ⟨zpowers f ⊔ zpowers f', hEel, hEcard, fun hle => hfInn (hle ?_), ?_⟩
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers f)
  · exact sup_le (Subgroup.zpowers_le.2 hfF) (Subgroup.zpowers_le.2 hf'F)

theorem exists_outer_plane_of_elt {p : ℕ} [Fact p.Prime] {K : Subgroup X} [K.Normal]
    (hperf : commutator ↥K = ⊤) (hZ : ¬ p ∣ Nat.card (center ↥K)) {g z : X} (hgp : g ^ p = 1)
    (hgK : g ∉ K ⊔ centralizer (K : Set X)) (hzK : z ∈ K) (hzp : orderOf z = p)
    (hgz : g * z = z * g) :
    ∃ E : Subgroup (MulAut (K ⧸ center K)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ¬ E ≤ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range ∧
      E ≤ (zpowers g ⊔ zpowers z).map (barAct K) := by
  have hp : p.Prime := Fact.out
  set φ := barAct K with hφ
  set Inn : Subgroup (MulAut (K ⧸ center K)) := (MulAut.conj : (K ⧸ center K) →* _).range
    with hInn
  have hgInn : φ g ∉ Inn := by
    rintro ⟨kb, hkb⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
    have h1 : φ ((k : X)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, barAct_of_mem, ← hkb, inv_mul_cancel]
    have h2 := commute_of_barAct_eq_one hperf h1
    apply hgK
    have : g = (k : X) * ((k : X)⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup k.2 (Subgroup.mem_centralizer_iff.2 fun y hy => (h2 y hy).symm)
  have hzInn : φ z ∈ Inn := by
    refine ⟨QuotientGroup.mk ⟨z, hzK⟩, ?_⟩
    exact (barAct_of_mem K ⟨z, hzK⟩).symm
  have hz1 : φ z ≠ 1 := by
    intro h1
    have h2 := commute_of_barAct_eq_one hperf h1
    have hmem : (⟨z, hzK⟩ : K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (h2 k k.2).symm
    have := Subgroup.orderOf_dvd_natCard (center ↥K) hmem
    rw [Subgroup.orderOf_mk, hzp] at this
    exact hZ this
  have hfp : φ g ^ p = 1 := by rw [← map_pow, hgp, map_one]
  have hf1 : φ g ≠ 1 := fun h => hgInn (h ▸ Subgroup.one_mem _)
  have hfo : orderOf (φ g) = p := orderOf_eq_prime hfp hf1
  have hzp' : φ z ^ p = 1 := by
    rw [← map_pow, ← hzp, pow_orderOf_eq_one, map_one]
  have hzo : orderOf (φ z) = p := orderOf_eq_prime hzp' hz1
  have hne : φ z ∉ zpowers (φ g) := by
    intro hc
    have hle : zpowers (φ z) ≤ zpowers (φ g) := Subgroup.zpowers_le.2 hc
    have heq : zpowers (φ z) = zpowers (φ g) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hfo, hzo])
    have hmem : φ g ∈ zpowers (φ z) := heq ▸ Subgroup.mem_zpowers (φ g)
    exact hgInn (Subgroup.zpowers_le.2 hzInn hmem)
  obtain ⟨hEel, hEcard⟩ := GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp hfp hzp' hf1
    hne (by rw [← map_mul, ← map_mul, hgz])
  refine ⟨zpowers (φ g) ⊔ zpowers (φ z), hEel, hEcard, fun hle => hgInn (hle ?_), ?_⟩
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_sup_left (Subgroup.mem_zpowers g), rfl⟩
    · exact Subgroup.mem_map.2 ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z), rfl⟩

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration
