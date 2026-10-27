module

public import CFSG.CGT.Foote82.Lemma61
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.PreuniquenessRankFour.HyperplaneGeneration
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Quasithin.Background.G11Basic
import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

instance instFiniteGLVFoote : Finite (GLV V) :=
  Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

structure Conf62 (G S L K : Subgroup (GLV V)) : Prop where
  setup : Setup6 G S L
  K_le : K ≤ G
  odd : Odd (Nat.card K)
  S_le : S ≤ Subgroup.normalizer (K : Set (GLV V))
  L_le : L ≤ Subgroup.normalizer (K : Set (GLV V))

@[expose] def Min62 (S L K : Subgroup (GLV V)) : Prop :=
  ∀ K' : Subgroup (GLV V), K' < K → S ≤ Subgroup.normalizer (K' : Set (GLV V)) →
    L ≤ Subgroup.normalizer (K' : Set (GLV V)) → ⁅K', L⁆ = ⊥

abbrev frat (K : Subgroup (GLV V)) : Subgroup (GLV V) :=
  (frattini ↥K).map K.subtype

theorem frat_le (K : Subgroup (GLV V)) : frat K ≤ K :=
  Subgroup.map_subtype_le _

private theorem conj_mem_frat {K : Subgroup (GLV V)} {g : GLV V}
    (hg : g ∈ Subgroup.normalizer (K : Set (GLV V))) {h : GLV V} (hh : h ∈ frat K) :
    g * h * g⁻¹ ∈ frat K := by
  obtain ⟨k, hk, rfl⟩ := hh
  set φ : MulAut ↥K := K.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have hφk : (φ k : GLV V) = g * (k : GLV V) * g⁻¹ := rfl
  have hchar : (frattini ↥K).comap φ.toMonoidHom = frattini ↥K :=
    Subgroup.characteristic_iff_comap_eq.1 inferInstance φ
  have hmem : φ k ∈ frattini ↥K := by
    have : k ∈ (frattini ↥K).comap φ.toMonoidHom := by rwa [hchar]
    exact this
  exact ⟨φ k, hmem, hφk⟩

theorem normalizer_le_normalizer_frat (K : Subgroup (GLV V)) :
    Subgroup.normalizer (K : Set (GLV V)) ≤ Subgroup.normalizer (frat K : Set (GLV V)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_frat hg hh, fun hh => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set (GLV V)) :=
    (Subgroup.normalizer (K : Set (GLV V))).inv_mem hg
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  have := conj_mem_frat hg' hh
  rwa [e] at this

theorem commutator_le_frat {p : ℕ} [Fact p.Prime] {K : Subgroup (GLV V)} (hK : IsPGroup p K) :
    ⁅K, K⁆ ≤ frat K := by
  haveI : Fact (IsPGroup p ↥K) := ⟨hK⟩
  rw [Subgroup.commutator_le]
  intro a ha b hb
  set a' : ↥K := ⟨a, ha⟩
  set b' : ↥K := ⟨b, hb⟩
  have hc : ⁅a', b'⁆ ∈ commutator ↥K := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b')
  exact ⟨⁅a', b'⁆, CFSG.commutator_le_frattini_of_isPGroup (p := p) (R := ↥K) hc, rfl⟩

theorem pow_mem_frat {p : ℕ} [Fact p.Prime] {K : Subgroup (GLV V)} (hK : IsPGroup p K)
    {k : GLV V} (hk : k ∈ K) : k ^ p ∈ frat K := by
  haveI : Fact (IsPGroup p ↥K) := ⟨hK⟩
  exact ⟨(⟨k, hk⟩ : ↥K) ^ p, CFSG.pth_power_mem_frattini_of_isPGroup (p := p) (R := ↥K) _, rfl⟩

theorem frat_lt {p : ℕ} [Fact p.Prime] {K : Subgroup (GLV V)} (hK : IsPGroup p K) (hne : K ≠ ⊥) :
    frat K < K := by
  refine lt_of_le_of_ne (frat_le K) fun h => hne ?_
  have htop : frattini ↥K = ⊤ := by
    refine Subgroup.map_injective K.subtype_injective ?_
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact h
  have hbot : (⊥ : Subgroup ↥K) = ⊤ :=
    frattini_nongenerating (K := (⊥ : Subgroup ↥K)) (by rw [htop, bot_sup_eq])
  refine Subgroup.eq_bot_iff_forall _ |>.2 fun k hk => ?_
  have hk1 : (⟨k, hk⟩ : ↥K) ∈ (⊥ : Subgroup ↥K) := by rw [hbot]; exact Subgroup.mem_top _
  simpa using congrArg Subtype.val ((Subgroup.mem_bot).1 hk1)

theorem eq_of_sup_frat {H K : Subgroup (GLV V)} (hHK : H ≤ K) (h : H ⊔ frat K = K) : H = K := by
  have hsup : H.subgroupOf K ⊔ frattini ↥K = ⊤ := by
    refine Subgroup.map_injective K.subtype_injective ?_
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype]
    have : (H.subgroupOf K).map K.subtype = H := Subgroup.subgroupOf_map_subtype H K ▸
      (inf_eq_left.2 hHK)
    rw [this]
    exact h
  have htop := frattini_nongenerating hsup
  refine le_antisymm hHK fun x hx => ?_
  have : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
  exact this

private theorem commSub_eq_commSpace_top (K : Subgroup (GLV V)) :
    CFSG.SignalizerFunctorTheorem.Quadratic.commSub K = commSpace K ⊤ := by
  unfold CFSG.SignalizerFunctorTheorem.Quadratic.commSub commSpace
  congr 1
  ext w
  constructor
  · rintro ⟨x, hx, u, rfl⟩
    exact ⟨x, hx, u, trivial, rfl⟩
  · rintro ⟨x, hx, u, -, rfl⟩
    exact ⟨x, hx, u, rfl⟩

private theorem neg_eq_self_of_zmod_two (v : V) : -v = v := by
  have hvv : v + v = 0 := by
    have h2v : (2 : ZMod 2) • v = 0 := by
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, zero_smul]
    rwa [two_smul] at h2v
  exact neg_eq_of_add_eq_zero_right hvv

private theorem sub_eq_add_of_zmod_two (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, neg_eq_self_of_zmod_two]

theorem isCompl_fixedSpace_commSpace {K : Subgroup (GLV V)} (hK : Odd (Nat.card K)) :
    IsCompl (fixedSpace K) (commSpace K ⊤) := by
  have h := CFSG.SignalizerFunctorTheorem.Quadratic.isCompl_fixSub_commSub (p := 2) (V := V)
    (Q := K) (Nat.coprime_two_left.2 hK)
  rw [commSub_eq_commSpace_top] at h
  exact h

theorem exists_eq_sub_of_inverts {B : Subgroup (GLV V)} {s : GLV V} {W : Submodule (ZMod 2) V}
    (hB : Odd (Nat.card B)) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hs : s ^ 2 = 1)
    (hinv : ∀ b ∈ B, s * b * s⁻¹ = b⁻¹) (hWB : Invariant B W) (hWs : ∀ w ∈ W, s w ∈ W)
    (hfix : fixedSpace B ⊓ W = ⊥) : ∀ w ∈ W, s w = w → ∃ u ∈ W, w = s u - u := by
  intro w hw hsw
  classical
  haveI : Fintype B := Fintype.ofFinite B
  obtain ⟨ι, hι⟩ := Countable.exists_injective_nat ↥B
  have hne : ∀ b : B, b ≠ 1 → b ≠ b⁻¹ := by
    intro b hb1 hbb
    apply hb1
    have h2 : b ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hbb]
      exact inv_mul_cancel b
    have hd1 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hd2 : orderOf b ∣ Nat.card B := orderOf_dvd_natCard b
    have hcop : Nat.Coprime 2 (Nat.card B) := Nat.coprime_two_left.2 hB
    have h1 := Nat.dvd_gcd hd1 hd2
    rw [hcop.gcd_eq_one] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have hsb : ∀ (b : B) (x : V), s ((b : GLV V) x) = ((b⁻¹ : B) : GLV V) (s x) := by
    intro b x
    have h1 : s * (b : GLV V) = (b : GLV V)⁻¹ * s := by
      have := hinv b b.2
      rwa [mul_inv_eq_iff_eq_mul] at this
    have := congrArg (fun f : GLV V => f x) h1
    simpa using this
  have hsum : ∑ b : B, (b : GLV V) w = 0 := by
    have hmemW : ∑ b : B, (b : GLV V) w ∈ W := Submodule.sum_mem _ fun b _ => hWB b b.2 w hw
    have hmemF : ∑ b : B, (b : GLV V) w ∈ fixedSpace B := by
      intro c hc
      rw [map_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft (⟨c, hc⟩ : B)) _ _ fun b => ?_
      rfl
    have : ∑ b : B, (b : GLV V) w ∈ fixedSpace B ⊓ W := ⟨hmemF, hmemW⟩
    rwa [hfix, Submodule.mem_bot] at this
  let g : B → V := fun b => if ι b < ι b⁻¹ then (b : GLV V) w else 0
  let g' : B → V := fun b => if ι b⁻¹ < ι b then (b : GLV V) w else 0
  have hs_g : ∀ b : B, s (g b) = g' (b⁻¹) := by
    intro b
    simp only [g, g', inv_inv]
    split_ifs
    · rw [hsb, hsw]
    · simp
  have hu : ∑ b, g b ∈ W := Submodule.sum_mem _ fun b _ => by
    dsimp only [g]
    split_ifs
    · exact hWB b b.2 w hw
    · exact W.zero_mem
  refine ⟨∑ b, g b, hu, ?_⟩
  have hsu : s (∑ b, g b) = ∑ b, g' b := by
    rw [map_sum]
    calc ∑ b, s (g b) = ∑ b, g' (b⁻¹) := Finset.sum_congr rfl fun b _ => hs_g b
      _ = ∑ b, g' b := Fintype.sum_equiv (Equiv.inv B) _ _ fun b => rfl
  have hpt : ∀ b : B, g' b + g b + (if b = 1 then w else 0) = (b : GLV V) w := by
    intro b
    by_cases hb : b = 1
    · subst hb
      simp [g, g']
    · have hlt : ι b ≠ ι b⁻¹ := fun h => hne b hb (hι h)
      rcases lt_or_gt_of_ne hlt with h | h
      · simp [g, g', hb, h, not_lt.2 h.le]
      · simp [g, g', hb, h, not_lt.2 h.le]
  have hall : ∑ b : B, (g' b + g b + (if b = 1 then w else 0)) = 0 :=
    (Finset.sum_congr rfl fun b _ => hpt b).trans hsum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hall
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hall
  rw [hsu, sub_eq_add_of_zmod_two]
  have h3 : ∑ b, g' b + ∑ b, g b = -w := eq_neg_of_add_eq_zero_left hall
  rw [h3, neg_eq_self_of_zmod_two]

private theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) :
    Nontrivial Q := by
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨x, y, hxy⟩ := hsimple.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨a, b, fun hab => hxy (by rw [hab])⟩

theorem Setup6.false_of_inverts {G S L B : Subgroup (GLV V)} (h : Setup6 G S L) {s : GLV V}
    (hsS : s ∈ S) (hs : s ^ 2 = 1) (hB : Odd (Nat.card B)) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hinv : ∀ b ∈ B, s * b * s⁻¹ = b⁻¹) (hfix : fixedSpace B = ⊥) : False := by
  have h61 := h.lemma61 hsS
  have hperf : ⁅L, L⁆ = L :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 h.component.2.2.1)
  have hfree : ∀ w : V, s w = w → w ∈ commSpace (Subgroup.zpowers s) ⊤ := by
    intro w hw
    obtain ⟨u, -, rfl⟩ := exists_eq_sub_of_inverts hB hab hs hinv (invariant_top B)
      (fun _ _ => Submodule.mem_top) (by rw [hfix, bot_inf_eq]) w Submodule.mem_top hw
    exact sub_mem_commSpace (Subgroup.mem_zpowers s) Submodule.mem_top
  have hLfix : ∀ w ∈ commSpace L ⊤, ∀ l ∈ L, l w = w := by
    intro w hw l hl
    have hsw : s w = w := h61.2 hw s (Subgroup.mem_zpowers s)
    exact h61.1 l hl w (hfree w hsw)
  have h0 : commSpace L (commSpace L ⊤) = ⊥ :=
    commSpace_eq_bot_iff.2 fun l hl w hw => hLfix w hw l hl
  have h1 : commSpace L ⊤ = ⊥ := by
    rw [← commSpace_commSpace_top_of_perfect hperf]
    exact h0
  have hL1 : ∀ l ∈ L, l = 1 := fun l hl => by
    ext v
    simpa using commSpace_eq_bot_iff.1 h1 l hl v Submodule.mem_top
  obtain ⟨a, b, hab⟩ := (nontrivial_of_isQuasisimple h.component.2.2).exists_pair_ne
  exact hab (Subtype.ext ((hL1 a a.2).trans (hL1 b b.2).symm))

theorem iSup_fixedSpace_eq_top {E : Subgroup (GLV V)} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ e ∈ E, e ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    ⨆ (H : Subgroup (GLV V)) (_ : H ≤ E) (_ : Nat.card H = p), fixedSpace H = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }
  have hodd : Odd (Nat.card ↥E) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  haveI : NeZero ((Nat.card ↥E : ℕ) : ZMod 2) :=
    ⟨fun h => (Nat.not_even_iff_odd.2 hodd) (ZMod.natCast_eq_zero_iff_even.1 h)⟩
  let ρ : Representation (ZMod 2) ↥E V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)).comp E.subtype
  have hρ : ∀ (x : ↥E) (v : V), ρ x v = (x : GLV V) v := fun x v => rfl
  have hpow : ∀ x : ↥E, x ^ p = 1 := fun x => Subtype.ext (hexp x x.2)
  have hsSup := CFSG.PreuniquenessRankFour.Helpers.coprime_abelian_representation_prime_fixedSpaces
    (coefficient := ZMod 2) (space := V) (acting := ↥E) p ρ hpow
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p
    (by rw [hcard]; exact dvd_pow_self p two_ne_zero)
  refine top_le_iff.1 ?_
  rw [← hsSup]
  refine sSup_le fun F hF => ?_
  obtain ⟨k, hk, hkF⟩ := hF
  rcases hk with hk1 | hkp
  · have hktop : k = ⊤ := Subgroup.index_eq_one.1 hk1
    have hH₀E : Subgroup.zpowers (x₀ : GLV V) ≤ E := Subgroup.zpowers_le.2 x₀.2
    have hH₀c : Nat.card (Subgroup.zpowers (x₀ : GLV V)) = p := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx₀]
    have hFH₀ : F ≤ fixedSpace (Subgroup.zpowers (x₀ : GLV V)) := fun v hv h hh => by
      have hx : (⟨h, hH₀E hh⟩ : ↥E) ∈ k := by rw [hktop]; exact Subgroup.mem_top _
      exact (hρ _ v).symm.trans (hkF _ hx v hv)
    exact hFH₀.trans (le_iSup_of_le _ (le_iSup_of_le hH₀E (le_iSup_of_le hH₀c le_rfl)))
  · have hHE : k.map E.subtype ≤ E := Subgroup.map_subtype_le k
    have hHc : Nat.card (k.map E.subtype) = p := by
      rw [Subgroup.card_subtype]
      have h2 := Subgroup.card_mul_index k
      rw [hkp, hcard] at h2
      refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
      rw [h2, pow_two]
    have hFH : F ≤ fixedSpace (k.map E.subtype) := fun v hv h hh => by
      obtain ⟨x, hx, rfl⟩ := hh
      exact (hρ x v).symm.trans (hkF x hx v hv)
    exact hFH.trans (le_iSup_of_le _ (le_iSup_of_le hHE (le_iSup_of_le hHc le_rfl)))

private theorem commSpace_commSpace_of_perfect {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    {X : Submodule (ZMod 2) V} (hX : Invariant L X) :
    commSpace L (commSpace L X) = commSpace L X := by
  have hconj : ∀ k' ∈ L, ∀ k ∈ L, k' * k * k'⁻¹ ∈ L := fun k' hk' k hk =>
    L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk')
  refine le_antisymm (commSpace_le_of_invariant (invariant_commSpace hconj hX)) ?_
  set M : Submodule (ZMod 2) V := commSpace L (commSpace L X) with hM
  let K : Subgroup (GLV V) :=
    { carrier := {k | k ∈ L ∧ ∀ v ∈ X, k v - v ∈ M}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨L.mul_mem ha.1 hb.1, fun v hv => ?_⟩
        have h := M.add_mem (ha.2 (b v) (hX b hb.1 v hv)) (hb.2 v hv)
        rwa [sub_add_sub_cancel] at h
      one_mem' := ⟨L.one_mem, fun v _ => by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨L.inv_mem ha.1, fun v hv => ?_⟩
        have h := M.neg_mem (ha.2 (a⁻¹ v) (hX a⁻¹ (L.inv_mem ha.1) v hv))
        simpa using h }
  have hcomm : ⁅L, L⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨L.mul_mem (L.mul_mem (L.mul_mem hg hh) (L.inv_mem hg)) (L.inv_mem hh),
      fun v hv => ?_⟩
    have key : ∀ u ∈ X, (g * h * g⁻¹ * h⁻¹) (h (g u)) - h (g u) ∈ M := by
      intro u hu
      have e1 : (g * h * g⁻¹ * h⁻¹) (h (g u)) = g (h u) := by simp
      have e2 : g (h u) - h (g u) = (g (h u - u) - (h u - u)) - (h (g u - u) - (g u - u)) := by
        simp only [map_sub]
        abel
      rw [e1, e2]
      exact M.sub_mem (sub_mem_commSpace hg (sub_mem_commSpace hh hu))
        (sub_mem_commSpace hh (sub_mem_commSpace hg hu))
    have hu : g⁻¹ (h⁻¹ v) ∈ X := hX g⁻¹ (L.inv_mem hg) _ (hX h⁻¹ (L.inv_mem hh) v hv)
    have e : h (g (g⁻¹ (h⁻¹ v))) = v := by simp
    have := key _ hu
    rw [e] at this
    exact this
  rw [hperf] at hcomm
  exact commSpace_le_iff.2 fun l hl v hv => (hcomm hl).2 v hv

private theorem trivial_of_commSpace_le_fixedSpace {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    {X : Submodule (ZMod 2) V} (hX : Invariant L X) (h : commSpace L X ≤ fixedSpace L) :
    ∀ l ∈ L, ∀ x ∈ X, l x = x := by
  have h0 : commSpace L (commSpace L X) = ⊥ :=
    commSpace_eq_bot_iff.2 fun l hl w hw => h hw l hl
  rw [commSpace_commSpace_of_perfect hperf hX] at h0
  exact commSpace_eq_bot_iff.1 h0

theorem trivial_on_summand {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L) (hirr : HasIrrTildeV L)
    {X Y : Submodule (ZMod 2) V} (hXY : IsCompl X Y) (hX : Invariant L X) (hY : Invariant L Y) :
    (∀ l ∈ L, ∀ x ∈ X, l x = x) ∨ (∀ l ∈ L, ∀ y ∈ Y, l y = y) := by
  have hconj : ∀ k' ∈ L, ∀ k ∈ L, k' * k * k'⁻¹ ∈ L := fun k' hk' k hk =>
    L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk')
  obtain ⟨-, hmin⟩ : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hirr
  have hXW : commSpace L X ≤ commSpace L ⊤ := commSpace_mono le_rfl le_top
  have hCinv : Invariant L (fixedSpace L ⊓ commSpace L ⊤) := fun l hl u hu => by
    rw [hu.1 l hl]
    exact hu
  have hJinv : Invariant L (fixedSpace L ⊓ commSpace L ⊤ ⊔ commSpace L X) :=
    hCinv.sup (invariant_commSpace hconj hX)
  rcases hmin _ hJinv le_sup_left (sup_le inf_le_right hXW) with hJ | hJ
  · left
    refine trivial_of_commSpace_le_fixedSpace hperf hX fun w hw => ?_
    have : w ∈ fixedSpace L ⊓ commSpace L ⊤ := by
      rw [← hJ]
      exact Submodule.mem_sup_right hw
    exact this.1
  · right
    refine trivial_of_commSpace_le_fixedSpace hperf hY fun w hw => ?_
    have hwY : w ∈ Y := commSpace_le_of_invariant hY hw
    have hwJ : w ∈ fixedSpace L ⊓ commSpace L ⊤ ⊔ commSpace L X := by
      rw [hJ]
      exact commSpace_mono le_rfl le_top hw
    obtain ⟨c, hc, x', hx', rfl⟩ := Submodule.mem_sup.1 hwJ
    intro l hl
    have hx'X : x' ∈ X := commSpace_le_of_invariant hX hx'
    have h1 : l x' - x' ∈ X := X.sub_mem (hX l hl x' hx'X) hx'X
    have h2 : l (c + x') - (c + x') ∈ Y := Y.sub_mem (hY l hl _ hwY) hwY
    have h3 : l (c + x') - (c + x') = l x' - x' := by
      rw [map_add, hc.1 l hl]
      abel
    have h4 : l (c + x') - (c + x') ∈ X ⊓ Y := ⟨h3 ▸ h1, h2⟩
    rw [hXY.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at h4
    exact h4

theorem fixes_of_commutator {K L : Subgroup (GLV V)} {X : Submodule (ZMod 2) V}
    (hKX : Invariant K X) (hL : ∀ l ∈ L, ∀ x ∈ X, l x = x) :
    ∀ g ∈ ⁅K, L⁆, ∀ x ∈ X, g x = x := by
  have hle : ⁅K, L⁆ ≤ centralizerOn ⊤ X := by
    rw [Subgroup.commutator_le]
    intro k hk l hl
    refine ⟨Subgroup.mem_top _, fun x hx => ?_⟩
    have h1 : (l⁻¹ : GLV V) x = x := hL l⁻¹ (L.inv_mem hl) x hx
    have h2 : (k⁻¹ : GLV V) x ∈ X := hKX k⁻¹ (K.inv_mem hk) x hx
    have h3 : l ((k⁻¹ : GLV V) x) = (k⁻¹ : GLV V) x := hL l hl _ h2
    show k (l ((k⁻¹ : GLV V) ((l⁻¹ : GLV V) x))) = x
    rw [h1, h3]
    exact LinearEquiv.apply_symm_apply k x
  exact fun g hg x hx => (hle hg).2 x hx

theorem Setup6.commutator_eq_bot_of_le_centralizer {G S L K : Subgroup (GLV V)}
    (h : Setup6 G S L) (hK : Odd (Nat.card K)) (hKC : K ≤ G ⊓ Subgroup.centralizer (S : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V))) : ⁅K, L⁆ = ⊥ := by
  have hLC : L ≤ G ⊓ Subgroup.centralizer (S : Set (GLV V)) := h.component.1
  have hAC : K ⊔ L ≤ G ⊓ Subgroup.centralizer (S : Set (GLV V)) := sup_le hKC hLC
  have hLA : L ≤ K ⊔ L := le_sup_right
  have hKA : K ≤ K ⊔ L := le_sup_left
  have hAN : K ⊔ L ≤ Subgroup.normalizer (K : Set (GLV V)) :=
    sup_le Subgroup.le_normalizer hLK
  have hcompA : CFSG.Assembly.IsComponentOf L (K ⊔ L) :=
    (CFSG.Assembly.isComponentOf_iff_open.2 h.component).of_le_of_le hLA hAC
  have hcomp : CFSG.IsComponent (L.subgroupOf (K ⊔ L)) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLA).1 hcompA
  have hKn : (K.subgroupOf (K ⊔ L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).2 hAN
  rcases CFSG.LocalCores.component_normal_subgroup hcomp hKn with h1 | h1
  · exfalso
    have hLK' : L ≤ K := CFSG.LocalCores.le_of_subgroupOf_le hLA h1
    have hoddL : Odd (Nat.card L) := hK.of_dvd_nat (Subgroup.card_dvd_of_le hLK')
    have hq : CFSG.Open.IsQuasisimple ↥L := h.component.2.2
    haveI : Nontrivial ↥L := nontrivial_of_isQuasisimple hq
    haveI : Group.IsPerfect ↥L := Group.isPerfect_def.2 hq.1
    exact Group.IsPerfect.not_isSolvable ↥L (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddL)
  · have h2 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hLA h1
    rw [inf_of_le_left hKA] at h2
    rw [Subgroup.commutator_comm]
    exact h2

end CFSG.CGT.Foote82
