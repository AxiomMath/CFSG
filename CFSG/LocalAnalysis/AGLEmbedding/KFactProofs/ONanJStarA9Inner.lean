module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SpFourEightRank
import CFSG.Permutation.FiveTransitive.SimpleIndexBound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem JStarElimDataOf.exists_inner_onto {L₀ T : Type} [Group L₀] [Finite L₀] [Group T]
    {p B : ℕ} (hZ : Subgroup.center L₀ = ⊥) (hperf : commutator T = ⊤)
    (hOut : Group.IsSolvable (Outer L₀)) (h : JStarElimDataOf L₀ p B T) :
    ∃ (N : Subgroup L₀) (ψ : N →* T), Function.Surjective ψ := by
  obtain ⟨A, J, -, -, -, φ, hφ, -⟩ := h
  let ψ₀ : J →* Outer L₀ := (QuotientGroup.mk' (inner L₀)).comp J.subtype
  obtain ⟨n, hn⟩ := hOut.solvable
  have h1 : derivedSeries J n ≤ ψ₀.ker := by
    have := map_derivedSeries_le_derivedSeries ψ₀ n
    rw [hn] at this
    exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp this)
  have hTn : ∀ m, derivedSeries T m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero T
    | succ m ih => rw [derivedSeries_succ, ih]; exact hperf
  have h2 : (ψ₀.ker.map φ) = ⊤ := by
    rw [eq_top_iff, ← hTn n, ← map_derivedSeries_eq hφ n]
    exact Subgroup.map_mono h1
  have hinj := conj_injective_of_center_eq_bot hZ
  let χ : ψ₀.ker →* inner L₀ :=
    (J.subtype.comp ψ₀.ker.subtype).codRestrict (inner L₀) fun x =>
      (QuotientGroup.eq_one_iff (N := inner L₀) _).mp (MonoidHom.mem_ker.mp x.2)
  have hχ : Function.Injective χ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : inner L₀ => (z : MulAut L₀)) hxy
  let θ : L₀ ≃* inner L₀ := MonoidHom.ofInjective hinj
  let κ : ψ₀.ker →* L₀ := θ.symm.toMonoidHom.comp χ
  have hκ : Function.Injective κ := θ.symm.injective.comp hχ
  let e : ψ₀.ker ≃* κ.range := MonoidHom.ofInjective hκ
  refine ⟨κ.range, (φ.comp ψ₀.ker.subtype).comp e.symm.toMonoidHom, fun t => ?_⟩
  have ht : t ∈ ψ₀.ker.map φ := h2 ▸ Subgroup.mem_top t
  obtain ⟨k, hk, rfl⟩ := ht
  exact ⟨e ⟨k, hk⟩, by simp⟩

theorem not_inner_onto_of_card {L₀ T : Type} [Group L₀] [Finite L₀] [IsSimpleGroup L₀] [Group T]
    [Finite T] (hL₀ : Nat.card L₀ = 1451520) (hT : Nat.card T = 181440) (N : Subgroup L₀)
    (ψ : N →* T) (hψ : Function.Surjective ψ) : False := by
  have hdvd : Nat.card T ∣ Nat.card N := Subgroup.card_dvd_of_surjective hψ
  have hN181 : 181440 ≤ Nat.card N := hT ▸ Nat.le_of_dvd Nat.card_pos hdvd
  by_cases hN : N = ⊤
  · subst hN
    let ψ' : L₀ →* T := ψ.comp Subgroup.topEquiv.symm.toMonoidHom
    have hψ' : Function.Surjective ψ' := hψ.comp Subgroup.topEquiv.symm.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ'.ker with h0 | h1
    · have hinj := (MonoidHom.ker_eq_bot_iff ψ').mp h0
      have := Nat.card_le_card_of_injective ψ' hinj
      omega
    · have hall : ∀ t : T, t = 1 := by
        intro t
        obtain ⟨y, rfl⟩ := hψ' t
        exact MonoidHom.mem_ker.mp (h1 ▸ Subgroup.mem_top y)
      have hsub : Subsingleton T := ⟨fun a b => (hall a).trans (hall b).symm⟩
      have := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
      omega
  · have hcard := CFSG.FiveTransitive.SimpleIndexBound.card_le_factorial_index L₀ N hN
    have hmul : N.index * Nat.card N = Nat.card L₀ := Subgroup.index_mul_card N
    have hidx : N.index ≤ 8 := by
      by_contra hc
      have : 9 * 181440 ≤ N.index * Nat.card N :=
        Nat.mul_le_mul (by omega) hN181
      omega
    have := Nat.factorial_le hidx
    have h8 : Nat.factorial 8 = 40320 := by decide
    omega

theorem not_jStarElimDataOf_of_card_eight_mul {L₀ T : Type} [Group L₀] [Finite L₀]
    [IsSimpleGroup L₀] [Group T] [Finite T] {p B : ℕ} (hL₀ : Nat.card L₀ = 1451520)
    (hT : Nat.card T = 181440) (hperf : commutator T = ⊤) (hZ : Subgroup.center L₀ = ⊥)
    (hOut : Group.IsSolvable (Outer L₀)) (h : JStarElimDataOf L₀ p B T) : False := by
  obtain ⟨N, ψ, hψ⟩ := h.exists_inner_onto hZ hperf hOut
  exact not_inner_onto_of_card hL₀ hT N ψ hψ

theorem exists_inj_sylow_of_card {L₀ T : Type} [Group L₀] [Finite L₀] [Group T] [Finite T]
    (hTc : JStarTargetCard 3 4 (3 ^ 4) T) (hZ : Subgroup.center L₀ = ⊥)
    (hs : 3 ^ 4 ∣ Nat.card L₀) (h : JStarElimDataOf L₀ 3 (3 ^ 4) T) :
    ∃ (U : Sylow 3 T) (ι : (U : Subgroup T) →* L₀), Function.Injective ι := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U, D, D₀, hDU, ⟨eD⟩, hcard⟩ := h.exists_inner_copy (s := 4) hZ hs
  have hUcard : Nat.card (U : Subgroup T) = 3 ^ 4 := hTc.sylow_card U
  have hD : 3 ^ 4 ≤ Nat.card D := by
    rw [hUcard] at hcard
    have h1 : 3 ^ 4 * 3 ^ 4 ∣ 3 ^ 4 * Nat.card D := hcard
    exact Nat.le_of_dvd Nat.card_pos (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1)
  have hDU' : D = U := Subgroup.eq_of_le_of_card_ge hDU (by rw [hUcard]; exact hD)
  let f : (U : Subgroup T) ≃* D₀ := (MulEquiv.subgroupCongr hDU').symm.trans eD.symm
  exact ⟨U, D₀.subtype.comp f.toMonoidHom, Subtype.val_injective.comp f.injective⟩

theorem exists_orderOf_nine_sylow {T : Type} [Group T] [Finite T]
    (e : T ≃* alternatingGroup (Fin (3 * 3))) (U : Sylow 3 T) :
    ∃ g ∈ (U : Subgroup T), orderOf g = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : (finRotate (3 * 3)) ∈ alternatingGroup (Fin (3 * 3)) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_finRotate]
    norm_num
  let r : alternatingGroup (Fin (3 * 3)) := ⟨finRotate (3 * 3), hmem⟩
  have hr : orderOf r = 9 := by
    rw [Subgroup.orderOf_mk, (isCycle_finRotate_of_le (by norm_num)).orderOf,
      support_finRotate_of_le (by norm_num), Finset.card_univ, Fintype.card_fin]
  set g₀ : T := e.symm r with hg₀def
  have hg₀ : orderOf g₀ = 9 := by rw [hg₀def, MulEquiv.orderOf_eq]; exact hr
  have hpg : IsPGroup 3 (Subgroup.zpowers g₀) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg₀]; norm_num)
  obtain ⟨c, hc⟩ := exists_conj_map_le_sylow U hpg
  refine ⟨c * g₀ * c⁻¹, hc ⟨g₀, Subgroup.mem_zpowers g₀, by simp⟩, ?_⟩
  have := MulEquiv.orderOf_eq (MulAut.conj c) g₀
  rw [MulAut.conj_apply] at this
  rw [this, hg₀]

theorem not_jStarElimDataOf_spFourEight {L₀ T : Type} [Group L₀] [Finite L₀] [Group T] [Finite T]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSpFourEightIndex d) (e₀ : L₀ ≃* CatGroup d)
    (hT : JStarTarget 3 (3 ^ 4) T) (hTc : JStarTargetCard 3 4 (3 ^ 4) T)
    (hZ : Subgroup.center L₀ = ⊥) (hs : 3 ^ 4 ∣ Nat.card L₀)
    (h : JStarElimDataOf L₀ 3 (3 ^ 4) T) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U, ι, hι⟩ := exists_inj_sylow_of_card hTc hZ hs h
  obtain ⟨E, hEU, hE, hEc⟩ := hT.exists_elem_le_sylow U
  have hEabel : IsElemAbelian 3 (E.subgroupOf (U : Subgroup T)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := hE.1.is_comm.comm ⟨a.1, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨b.1, Subgroup.mem_subgroupOf.mp b.2⟩
      simpa using congrArg Subtype.val this
    · exact Subtype.ext (hE.2 _ (Subgroup.mem_subgroupOf.mp hx))
  have hE'abel : IsElemAbelian 3 ((E.subgroupOf (U : Subgroup T)).map ι) :=
    CFSG.SectionRank.isElemAbelian_map hEabel ι
  have hE'card : Nat.card ((E.subgroupOf (U : Subgroup T)).map ι) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective hι, ← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEU).toEquiv
  have := card_le_nine_of_elemAbelian_spFourEight hd e₀ hE'abel
  rw [hE'card] at this
  norm_num at this

theorem not_jStarElimDataOf_of_elemAbelian_sylow {Y L₀ T : Type} [Group Y] [Group L₀] [Finite L₀]
    [Group T] [Finite T] (φ : Y ≃* L₀)
    (hE : ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) {m : ℕ}
    (hN : Nat.card L₀ = 3 ^ 4 * m) (hm : ¬ 3 ∣ m) (e : T ≃* alternatingGroup (Fin (3 * 3)))
    (hTc : JStarTargetCard 3 4 (3 ^ 4) T) (hZ : Subgroup.center L₀ = ⊥)
    (h : JStarElimDataOf L₀ 3 (3 ^ 4) T) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs : 3 ^ 4 ∣ Nat.card L₀ := ⟨m, hN⟩
  obtain ⟨U, ι, hι⟩ := exists_inj_sylow_of_card hTc hZ hs h
  obtain ⟨g, hgU, hg9⟩ := exists_orderOf_nine_sylow e U
  obtain ⟨E, hE, hEc⟩ := hE
  have hE'abel : IsElemAbelian 3 (E.map φ.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hE'card : Nat.card (E.map φ.toMonoidHom) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective φ.injective, hEc]
  obtain ⟨S, hES⟩ := (IsPGroup.of_card hE'card).exists_le_sylow
  have hScard : Nat.card (S : Subgroup L₀) = 3 ^ 4 := card_sylow_eq_pow_of_card_eq hN hm S
  have hES' : E.map φ.toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hES (by rw [hScard, hE'card])
  set g' : L₀ := ι ⟨g, hgU⟩ with hg'def
  have hg'9 : orderOf g' = 9 := by
    rw [hg'def, orderOf_injective ι hι, Subgroup.orderOf_mk, hg9]
  have hpg : IsPGroup 3 (Subgroup.zpowers g') :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg'9]; norm_num)
  obtain ⟨c, hc⟩ := exists_conj_map_le_sylow S hpg
  have hmem : c * g' * c⁻¹ ∈ (S : Subgroup L₀) := hc ⟨g', Subgroup.mem_zpowers g', by simp⟩
  rw [← hES'] at hmem
  have h3 : (c * g' * c⁻¹) ^ 3 = 1 := hE'abel.2 _ hmem
  have h3' : g' ^ 3 = 1 := by
    rw [conj_pow, mul_inv_eq_one] at h3
    simpa using h3
  have := orderOf_dvd_of_pow_eq_one h3'
  rw [hg'9] at this
  norm_num at this

end CFSG.AGLEmbedding
