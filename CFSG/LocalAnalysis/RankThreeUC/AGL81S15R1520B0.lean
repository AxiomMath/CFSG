module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_sylow_le_normalizer_aux_mem {S : Subgroup Y} (y s : Y) :
    s ∈ S.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * s * y ∈ S := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem exists_sylow_le_normalizer_aux_index {S : Subgroup Y} :
    (Subgroup.normalizer (S : Set Y)).index =
      {S' : Subgroup Y | ∃ y : Y, S' = S.map (MulAut.conj y).toMonoidHom}.ncard := by
  let g : Y → Subgroup Y := fun y => S.map (MulAut.conj y).toMonoidHom
  have hg : ∀ a b : Y, a⁻¹ * b ∈ Subgroup.normalizer (S : Set Y) → g a = g b := by
    intro a b hab
    ext s
    show s ∈ S.map (MulAut.conj a).toMonoidHom ↔ s ∈ S.map (MulAut.conj b).toMonoidHom
    rw [exists_sylow_le_normalizer_aux_mem, exists_sylow_le_normalizer_aux_mem]
    have hz := Subgroup.mem_normalizer_iff.mp (inv_mem hab) (a⁻¹ * s * a)
    have e : (a⁻¹ * b)⁻¹ * (a⁻¹ * s * a) * (a⁻¹ * b)⁻¹⁻¹ = b⁻¹ * s * b := by group
    rw [e] at hz
    exact hz
  have hinj_aux : ∀ a b : Y, g a = g b → a⁻¹ * b ∈ Subgroup.normalizer (S : Set Y) := by
    intro a b hab
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have key : ∀ s : Y, a⁻¹ * s * a ∈ S ↔ b⁻¹ * s * b ∈ S := by
      intro s
      have hs : s ∈ g a ↔ s ∈ g b := by rw [hab]
      exact (exists_sylow_le_normalizer_aux_mem a s).symm.trans
        (hs.trans (exists_sylow_le_normalizer_aux_mem b s))
    have hk := key (b * h * b⁻¹)
    have e1 : b⁻¹ * (b * h * b⁻¹) * b = h := by group
    have e2 : a⁻¹ * (b * h * b⁻¹) * a = (a⁻¹ * b) * h * (a⁻¹ * b)⁻¹ := by group
    rw [e1, e2] at hk
    exact hk.symm
  let Φ : Y ⧸ Subgroup.normalizer (S : Set Y) → Subgroup Y :=
    Quotient.lift g (fun a b hab => hg a b (QuotientGroup.leftRel_apply.mp hab))
  have hΦinj : Function.Injective Φ := by
    intro u v huv
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
    exact QuotientGroup.eq.mpr (hinj_aux a b huv)
  have hrange : Set.range Φ = Set.range g := by
    ext T
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨QuotientGroup.mk a, rfl⟩
  rw [Subgroup.index_eq_card, ← Set.ncard_range_of_injective hΦinj, hrange]
  congr 1
  ext T
  simp only [Set.mem_range, Set.mem_setOf_eq]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

theorem exists_sylow_le_normalizer {p : ℕ} (hp : p.Prime) {S : Subgroup Y} {k : ℕ} (hk : k < p)
    (hconj : {S' : Subgroup Y | ∃ y : Y, S' = S.map (MulAut.conj y).toMonoidHom}.ncard ≤ k) :
    ∃ P : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf p P ⊤ ∧ P ≤ Subgroup.normalizer (S : Set Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hidx := exists_sylow_le_normalizer_aux_index (S := S)
  have hpos : (Subgroup.normalizer (S : Set Y)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hndvd : ¬ p ∣ (Subgroup.normalizer (S : Set Y)).index := by
    intro h
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) h
    rw [hidx] at h1
    omega
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (Subgroup.normalizer (S : Set Y))
  obtain ⟨hQN, hQp, hQdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hQ
  refine ⟨Q, CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hQp, ?_⟩, hQN⟩
  rw [← Subgroup.relIndex_mul_relIndex Q (Subgroup.normalizer (S : Set Y)) ⊤ hQN le_top]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
  · exact hQdvd h1
  · rw [Subgroup.relIndex_top_right] at h2
    exact hndvd h2

theorem mem_sup_centralizer_of_outTwo {S : Subgroup Y} (hOut : OutTwoGroup ↥S) {x : Y}
    (hx : x ∈ Subgroup.normalizer (S : Set Y)) (hodd : Odd (orderOf x)) :
    x ∈ S ⊔ Subgroup.centralizer (S : Set Y) := by
  have hφodd : Odd (orderOf (S.normalizerMonoidHom ⟨x, hx⟩)) := by
    have hdvd := orderOf_map_dvd S.normalizerMonoidHom ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨k, hk⟩ := hOut (S.normalizerMonoidHom ⟨x, hx⟩)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hφodd))
  have hmem : S.normalizerMonoidHom ⟨x, hx⟩ ∈ (MulAut.conj : S →* MulAut S).range := by
    rw [← hj]
    exact pow_mem hk j
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hmem
  have hl' : MulAut.conj l = S.normalizerMonoidHom ⟨x, hx⟩ := hl
  have hkey : ∀ s : S, (l : Y) * (s : Y) * (l : Y)⁻¹ = x * (s : Y) * x⁻¹ := by
    intro s
    have := congrArg (fun ψ : MulAut S => ((ψ s : S) : Y)) hl'
    simpa [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  have hc : ∀ h ∈ (S : Set Y), h * ((l : Y)⁻¹ * x) = (l : Y)⁻¹ * x * h := by
    intro h hh
    have e : (l : Y) * h * (l : Y)⁻¹ = x * h * x⁻¹ := hkey ⟨h, hh⟩
    calc h * ((l : Y)⁻¹ * x) = (l : Y)⁻¹ * ((l : Y) * h * (l : Y)⁻¹) * x := by group
      _ = (l : Y)⁻¹ * (x * h * x⁻¹) * x := by rw [e]
      _ = (l : Y)⁻¹ * x * h := by group
  have hgc : (l : Y)⁻¹ * x ∈ Subgroup.centralizer (S : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr hc
  have hlS : (l : Y) ∈ S := l.2
  have key := mul_mem ((le_sup_left : S ≤ S ⊔ Subgroup.centralizer (S : Set Y)) hlS)
    ((le_sup_right : Subgroup.centralizer (S : Set Y) ≤ S ⊔ Subgroup.centralizer (S : Set Y)) hgc)
  rwa [mul_inv_cancel_left] at key

theorem pElement_mem_sup_centralizer (hK : K7145) (hYK : CFSG.Open.IsKGroup Y) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S : Subgroup Y} [S.Normal] (hq : CFSG.Open.IsQuasisimple ↥S)
    (hS : CFSG.Open.pRank p S ≤ 1) (hno : ∀ N : Subgroup Y, N.Normal → N.index ≠ p) {x : Y}
    (hx : ∃ k : ℕ, orderOf x = p ^ k) : x ∈ S ⊔ Subgroup.centralizer (S : Set Y) := by
  by_contra hcon
  obtain ⟨N, hNn, hNi⟩ := hK Y hYK p hp hp2 S inferInstance hq hS x hx hcon
  exact hno N hNn hNi

end CFSG.LocalAnalysis.RankThreeUC.S15
