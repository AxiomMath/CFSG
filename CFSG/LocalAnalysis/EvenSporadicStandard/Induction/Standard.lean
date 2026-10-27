module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G]

theorem mem_normalizer_centralizer_of_mem_normalizer {T : Subgroup G} {s : G}
    (hs : s ∈ normalizer (T : Set G)) :
    s ∈ normalizer ((centralizer (T : Set G) : Subgroup G) : Set G) :=
  GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup T hs

theorem two_dvd_card_of_isPGroup [Finite G] {T : Subgroup G} (h2 : IsPGroup 2 T) (hT : T ≠ ⊥) :
    2 ∣ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h2.card_eq_or_dvd with h | h
  · exact absurd (Subgroup.card_eq_one.1 h) hT
  · exact h

theorem map_conj_inv_of_eq {L M : Subgroup G} {s : G} (h : L = M.map (MulAut.conj s).toMonoidHom) :
    M = L.map (MulAut.conj s⁻¹).toMonoidHom := by
  rw [h, map_conj_map_conj, inv_mul_cancel]
  ext y
  simp

theorem not_forall_commute_of_isQuasisimple {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) :
    ¬ ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
  intro h
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext (h a' a'.2 b' b'.2))

theorem exists_eq_of_normal [Finite G] {P L : Subgroup G} {ι : Type*} {Q : ι → Subgroup G}
    (hP : P = ⨆ i, Q i) (hQ : ∀ i, IsCompIn (Q i) P) (hLP : L ≤ P)
    (hLn : (L.subgroupOf P).Normal) (hLq : CFSG.IsQuasisimple ↥L) : ∃ i, L = Q i := by
  have hLcomp : IsCompIn L P := isCompIn_of_normal hLP hLq hLn
  by_contra hcon
  push Not at hcon
  have hPC : P ≤ centralizer (L : Set G) := by
    rw [hP]
    refine iSup_le fun i y hy => ?_
    exact mem_centralizer_iff.2 fun l hl =>
      (hLcomp.commute_of_ne (hQ i) (hcon i) l hl y hy)
  exact not_forall_commute_of_isQuasisimple hLq fun a ha b hb =>
    mem_centralizer_iff.1 (hPC (hLP hb)) a ha

theorem lt_conj_of_stdBare [Finite G] {L M : Subgroup G} (hL : StdBare L) (h : Lt L M) :
    ∃ s : G, L = M.map (MulAut.conj s).toMonoidHom := by
  obtain ⟨S, T, -, hT, -, hT2, hST, hLS, hMT, hLle⟩ := h
  have hLq : CFSG.IsQuasisimple ↥L := hLS.isQuasisimple
  have hSN : S ≤ normalizer (T : Set G) := by
    intro s hs
    have key : ∀ y ∈ S, ∀ t ∈ T, y * t * y⁻¹ ∈ T := fun y hy t ht => by
      have h1 : y * t * y⁻¹ * t⁻¹ ∈ T := (hST (Subgroup.commutator_mem_commutator hy ht)).2
      have : y * t * y⁻¹ = (y * t * y⁻¹ * t⁻¹) * t := by group
      rw [this]
      exact mul_mem h1 ht
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact key s hs t
    · intro ht
      have := key s⁻¹ (S.inv_mem hs) _ ht
      simpa [mul_assoc] using this
  have hMg : ∀ g ∈ S, IsCompIn (M.map (MulAut.conj g).toMonoidHom) (centralizer (T : Set G)) :=
    fun g hg => isCompIn_map_conj_of_mem_normalizer hMT
      (mem_normalizer_centralizer_of_mem_normalizer (hSN hg))
  set P : Subgroup G := conjClosure M S with hP
  have hPle : P ≤ centralizer (T : Set G) := iSup₂_le fun g hg => (hMg g hg).1
  have hLP : L ≤ P := hLle
  have hTL : T ≤ centralizer (L : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun l hl => (mem_centralizer_iff.1 (hPle (hLP hl)) x hx).symm
  have hev : 2 ∣ Nat.card T := two_dvd_card_of_isPGroup hT2 hT
  have hA : ∀ g ∈ S, ∀ y ∈ M.map (MulAut.conj g).toMonoidHom, y ∈ normalizer (L : Set G) := by
    intro g hg y hy
    by_contra hyN
    have hodd := hL.2 y hyN
    have hyc : ∀ x ∈ T, x * y = y * x := mem_centralizer_iff.1 ((hMg g hg).1 hy)
    have hsub : T ≤ centralizer (L : Set G) ⊓
        (centralizer (L : Set G)).map (MulAut.conj y).toMonoidHom := by
      intro x hx
      refine ⟨hTL hx, ⟨x, hTL hx, ?_⟩⟩
      show y * x * y⁻¹ = x
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [hyc x hx]
        _ = x := by group
    have hdvd := Subgroup.card_dvd_of_le hsub
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (hev.trans hdvd))
  have hPN : P ≤ normalizer (L : Set G) := iSup₂_le fun g hg y hy => hA g hg y hy
  have hLn : (L.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLP).2 hPN
  have hLcomp : IsCompIn L P := isCompIn_of_normal hLP hLq hLn
  have hMgP : ∀ g ∈ S, IsCompIn (M.map (MulAut.conj g).toMonoidHom) P := by
    intro g hg
    have hle : M.map (MulAut.conj g).toMonoidHom ≤ P := le_iSup₂_of_le g hg le_rfl
    have hPN' : P ≤ normalizer ((M.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      refine iSup₂_le fun g' hg' y hy => ?_
      by_cases heq : M.map (MulAut.conj g').toMonoidHom = M.map (MulAut.conj g).toMonoidHom
      · rw [heq] at hy
        exact Subgroup.le_normalizer hy
      · refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun b hb => ?_)
        exact ((hMg g' hg').commute_of_ne (hMg g hg) heq y hy b hb).symm
    exact isCompIn_of_normal hle (hMg g hg).isQuasisimple
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hPN')
  have hPeq : P = ⨆ g : S, M.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [hP, conjClosure, iSup_subtype']
  obtain ⟨g, hg⟩ := exists_eq_of_normal (Q := fun g : S => M.map (MulAut.conj (g : G)).toMonoidHom)
    hPeq (fun g => hMgP g g.2) hLP hLn hLq
  exact ⟨g, hg⟩

theorem maximal_of_stdBare [Finite G] {L : Subgroup G} (hL : InL L) (hstd : StdBare L) :
    Maximal L := by
  refine ⟨hL, fun M hM => ?_⟩
  have key : ∃ g : G, M = L.map (MulAut.conj g).toMonoidHom := by
    induction hM with
    | single h =>
      obtain ⟨s, hs⟩ := lt_conj_of_stdBare hstd h
      exact ⟨s⁻¹, map_conj_inv_of_eq hs⟩
    | tail _ hbc ih =>
      obtain ⟨g, hg⟩ := ih
      have hb : StdBare _ := hg ▸ hstd.map_conj g
      obtain ⟨s, hs⟩ := lt_conj_of_stdBare hb hbc
      refine ⟨s⁻¹ * g, ?_⟩
      rw [map_conj_inv_of_eq hs, hg, map_conj_map_conj]
  obtain ⟨g, rfl⟩ := key
  let e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    MulEquiv.subgroupMap (MulAut.conj g) L
  exact ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

end CFSG.EvenSporadicStandard.Induction
