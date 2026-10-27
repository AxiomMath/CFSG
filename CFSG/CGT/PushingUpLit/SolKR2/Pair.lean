module

public import CFSG.CGT.PushingUpLit.SolKR2.Setting
public import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n (conjSubgroup_mul conjSubgroup_eq_self_iff isTI_conjSubgroup
  conjSubgroup_eq_of_isTI exists_mul_of_mem_sup inSubgroup_pCore_two mem_normalizer_inf
  mem_normalizer_centralizer)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

namespace Pair

section Basic

variable (h : R2 M B)
include h

omit [Finite G] in
theorem card_U : Nat.card ↥(omegaTwoSub B) = 16 := by
  obtain ⟨e⟩ := h.c4c4
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  simp

omit [Finite G] in
theorem B0_le_U : omegaOneSub B ≤ omegaTwoSub B := by
  have h1 := CFSG.RankThree.PartTwo.omegaOneSub_le (omegaTwoSub B)
  rwa [h.omegaOne_omegaTwo] at h1

omit [Finite G] in
theorem B0_ne_U : omegaOneSub B ≠ omegaTwoSub B := by
  intro heq
  have h4 := h.card4
  rw [heq, card_U h] at h4
  omega

omit [Finite G] in
theorem sq_B0 {x : G} (hx : x ∈ omegaOneSub B) : x * x = 1 :=
  ((mem_omegaOneSub_iff h.H.comm).1 hx).2

omit [Finite G] in
theorem comm_U : ∀ x ∈ omegaTwoSub B, ∀ y ∈ omegaTwoSub B, x * y = y * x :=
  comm_omegaTwoSub h.H.comm

theorem exists_sq_ne : ∃ x ∈ omegaTwoSub B, x ^ 2 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hle : omegaTwoSub B ≤ omegaOneSub B := fun x hx =>
    (mem_omegaOneSub_iff h.H.comm).2 ⟨omegaTwoSub_le B hx, by rw [← sq]; exact hcon x hx⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [card_U h, h.card4] at h1
  omega

theorem isPGroup_U : IsPGroup 2 ↥(omegaTwoSub B) := h.H.two.to_le (omegaTwoSub_le B)

omit [Finite G] in
theorem le_normalizer_B0 : M ≤ Subgroup.normalizer (omegaOneSub B : Set G) :=
  h.H.le_normalizer_omegaOne

omit [Finite G] in
theorem le_normalizer_U : M ≤ Subgroup.normalizer (omegaTwoSub B : Set G) :=
  h.H.le_normalizer_omegaTwo

omit [Finite G] in
theorem omegaOne_conj_U (g : G) :
    omegaOneSub (conjSubgroup g (omegaTwoSub B)) = conjSubgroup g (omegaOneSub B) := by
  rw [omegaOneSub_conj (comm_U h), h.omegaOne_omegaTwo]

omit [Finite G] in
theorem conj_B0_le_U (g : G) :
    conjSubgroup g (omegaOneSub B) ≤ conjSubgroup g (omegaTwoSub B) := by
  rw [← omegaOne_conj_U h g]
  exact CFSG.RankThree.PartTwo.omegaOneSub_le _

omit [Finite G] in
theorem card_conj_B0 (g : G) : Nat.card ↥(conjSubgroup g (omegaOneSub B)) = 4 := by
  rw [card_conjSubgroup, h.card4]

omit [Finite G] in
theorem card_conj_U (g : G) : Nat.card ↥(conjSubgroup g (omegaTwoSub B)) = 16 := by
  rw [card_conjSubgroup, card_U h]

omit [Finite G] in
theorem conj_B0_ne_bot (g : G) : conjSubgroup g (omegaOneSub B) ≠ ⊥ := by
  intro hbot
  have := card_conj_B0 h g
  rw [hbot, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem sq_conj_B0 {g x : G} (hx : x ∈ conjSubgroup g (omegaOneSub B)) : x * x = 1 := by
  have h1 := sq_B0 h (mem_conjSubgroup.mp hx)
  calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_sq_ne_conj (g : G) : ∃ x ∈ conjSubgroup g (omegaTwoSub B), x ^ 2 ≠ 1 := by
  obtain ⟨u, hu, hu2⟩ := exists_sq_ne h
  refine ⟨g * u * g⁻¹, ?_, fun h' => hu2 ?_⟩
  · rw [mem_conjSubgroup, show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    exact hu
  · rw [conj_pow] at h'
    calc u ^ 2 = g⁻¹ * (g * u ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group

omit [Finite G] in
theorem pow_four_conj (g : G) : ∀ y ∈ conjSubgroup g (omegaTwoSub B), y ^ 4 = 1 := by
  intro y hy
  have h4 := pow_four_of_mem_omegaTwoSub h.H.comm (mem_conjSubgroup.mp hy)
  rw [show (g⁻¹ * y * g) ^ 4 = g⁻¹ * y ^ 4 * g by
    simpa using conj_pow (a := g⁻¹) (b := y) (i := 4)] at h4
  calc y ^ 4 = g * (g⁻¹ * y ^ 4 * g) * g⁻¹ := by group
    _ = 1 := by rw [h4]; group

omit [Finite G] in
theorem comm_conj_U (g : G) :
    ∀ x ∈ conjSubgroup g (omegaTwoSub B), ∀ y ∈ conjSubgroup g (omegaTwoSub B), x * y = y * x :=
  comm_conj (comm_U h) g

theorem setup210_conj (g g' : G)
    (hne : conjSubgroup g (omegaTwoSub B) ⊓
      Subgroup.normalizer (conjSubgroup g' (omegaTwoSub B) : Set G) ≠ ⊥) :
    Setup210 (conjSubgroup g (omegaTwoSub B)) (conjSubgroup g' (omegaTwoSub B)) where
  comm := comm_conj_U h g
  two := (isPGroup_U h).map (MulAut.conj g).toMonoidHom
  exp_ne := exists_sq_ne_conj h g
  ti := isTI_conjSubgroup h.s3hyp.ti g
  conj := ⟨g' * g⁻¹, by rw [← conjSubgroup_mul, inv_mul_cancel_right]⟩
  ne_bot := hne

theorem mem_normalizer_conj_U {g' c x : G} (hx : x ∈ conjSubgroup g' (omegaOneSub B))
    (hx1 : x ≠ 1) (hcx : c * x = x * c) :
    c ∈ Subgroup.normalizer (conjSubgroup g' (omegaTwoSub B) : Set G) :=
  CFSG.RankThree.GF2n.Tim77.mem_normalizer_of_commute_of_isTI
    (isTI_conjSubgroup h.s3hyp.ti g') (conj_B0_le_U h g' hx) hx1 hcx

end Basic

section NoCert

variable (hW : R2Weak) (h : R2 M B)
include hW h

theorem ncpair_of_commute {g g' : G}
    (hcomm : ∀ a ∈ conjSubgroup g (omegaOneSub B), ∀ b ∈ conjSubgroup g' (omegaOneSub B),
      a * b = b * a)
    (hne : conjSubgroup g (omegaOneSub B) ≠ conjSubgroup g' (omegaOneSub B)) :
    NCPair (conjSubgroup g (omegaTwoSub B)) (conjSubgroup g' (omegaTwoSub B)) := by
  have hset : Setup210 (conjSubgroup g (omegaTwoSub B)) (conjSubgroup g' (omegaTwoSub B)) := by
    refine Pair.setup210_conj h g g' ?_
    intro hbot
    apply Pair.conj_B0_ne_bot h g
    rw [eq_bot_iff, ← hbot]
    refine le_inf (Pair.conj_B0_le_U h g) (fun x hx => ?_)
    obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Pair.conj_B0_ne_bot h g')
    exact Pair.mem_normalizer_conj_U h hf (fun e => hf1 (Subtype.ext e)) (hcomm x hx f hf)
  refine ⟨hset, Pair.pow_four_conj h g, fun hc => hne ?_⟩
  have hle : conjSubgroup (g⁻¹ * g') (omegaTwoSub B) ≤
      Subgroup.centralizer (omegaTwoSub B : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hx' : g * x * g⁻¹ ∈ conjSubgroup g' (omegaTwoSub B) := by
      rw [mem_conjSubgroup] at hx ⊢
      rwa [show g'⁻¹ * (g * x * g⁻¹) * g' = (g⁻¹ * g')⁻¹ * x * (g⁻¹ * g') by group]
    have hu' : g * u * g⁻¹ ∈ conjSubgroup g (omegaTwoSub B) := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * u * g⁻¹) * g = u by group]
      exact hu
    have e := hc _ hu' _ hx'
    calc u * x = g⁻¹ * ((g * u * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * u * g⁻¹)) * g := by rw [e]
      _ = x * u := by group
  have hU1 := hW G M B h (g⁻¹ * g') hle
  have hB1 : conjSubgroup (g⁻¹ * g') (omegaOneSub B) = omegaOneSub B := by
    rw [← h.omegaOne_omegaTwo, ← omegaOneSub_conj (Pair.comm_U h), hU1]
  calc conjSubgroup g (omegaOneSub B)
      = conjSubgroup g (conjSubgroup (g⁻¹ * g') (omegaOneSub B)) := by rw [hB1]
    _ = conjSubgroup g' (omegaOneSub B) := by
        rw [← conjSubgroup_mul, mul_inv_cancel_left]

end NoCert

section CertOnly

open CFSG.Timmesfeld

theorem comm_of_commute (h : R2 M B) {t x k : G} (ht : t ∈ omegaOneSub B) (ht1 : t ≠ 1)
    (hx : x ∈ conjSubgroup k (omegaOneSub B)) (hx1 : x ≠ 1) (hc : t * x = x * t) :
    ∀ a ∈ omegaOneSub B, ∀ b ∈ conjSubgroup k (omegaOneSub B), a * b = b * a := by
  have := comm_of_commute_conj h.root (g := 1) (h := k) (x := t) (y := x)
    (by rw [conjSubgroup_one]; exact ht) ht1 hx hx1 hc
  intro a ha b hb
  exact this a (by rw [conjSubgroup_one]; exact ha) b hb

theorem exists_lam_of_commute (h : R2 M B) {t τ : G} (ht : t ∈ omegaOneSub B) (ht1 : t ≠ 1)
    (hτ : IsConj t τ) (hc : τ * t = t * τ) : ∃ F ∈ Lam M B, τ ∈ F := by
  obtain ⟨k, hk⟩ := isConj_iff.mp hτ
  have hτF : τ ∈ conjSubgroup k (omegaOneSub B) := by
    rw [mem_conjSubgroup, ← hk, show k⁻¹ * (k * t * k⁻¹) * k = t by group]
    exact ht
  have hτ1 : τ ≠ 1 := by
    intro e
    apply ht1
    rw [e] at hk
    calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
      _ = 1 := by rw [hk]; group
  refine ⟨conjSubgroup k (omegaOneSub B), ⟨k, rfl, ?_⟩, hτF⟩
  intro x hx
  have hcomm := comm_of_commute h ht ht1 hτF hτ1 hc.symm t ht x hx
  rw [← h.normalizer_B0]
  exact CFSG.RankThree.GF2n.Tim77.mem_normalizer_of_commute_of_isTI h.isTI_B0 ht ht1
    hcomm.symm

theorem rootGroup_eq_of (h : R2 M B)
    (hconj : ∀ x ∈ omegaOneSub B, ∀ y ∈ omegaOneSub B, x ≠ 1 → y ≠ 1 → IsConj x y)
    {t : G} (ht : t ∈ omegaOneSub B) (ht1 : t ≠ 1) :
    rootGroup (CorB.cls t) t = omegaOneSub B := by
  have hclass : ∃ d₀ : G, CorB.cls t = {g | IsConj d₀ g} := ⟨t, rfl⟩
  have htt : t * t = 1 := Pair.sq_B0 h ht
  have hB0D : ∀ x ∈ omegaOneSub B, x ≠ 1 → x ∈ CorB.cls t := fun x hx hx1 =>
    hconj t ht x hx ht1 hx1
  have hiff : ∀ x ∈ omegaOneSub B, x ≠ 1 → ∀ f ∈ CorB.cls t, Commute x f ↔ Commute t f := by
    intro x hx hx1 f hf
    obtain ⟨k, hk⟩ := isConj_iff.mp hf
    have hfk : f ∈ conjSubgroup k (omegaOneSub B) := by
      rw [mem_conjSubgroup, ← hk, show k⁻¹ * (k * t * k⁻¹) * k = t by group]
      exact ht
    have hf1 : f ≠ 1 := by
      intro e
      apply ht1
      rw [e] at hk
      calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
        _ = 1 := by rw [hk]; group
    constructor
    · intro hc
      exact comm_of_commute h hx hx1 hfk hf1 hc t ht f hfk
    · intro hc
      exact comm_of_commute h ht ht1 hfk hf1 hc x hx f hfk
  have hrs : ∀ x ∈ omegaOneSub B, x ≠ 1 → x ∈ rootSet (CorB.cls t) t := fun x hx hx1 =>
    ⟨hB0D x hx hx1, fun f hf => hiff x hx hx1 f hf⟩
  have hnorm : ∀ k : G, k * t * k⁻¹ ∈ rootSet (CorB.cls t) t →
      k ∈ Subgroup.normalizer (rootGroup (CorB.cls t) t : Set G) := by
    intro k hk
    rw [← conjSubgroup_eq_self_iff]
    have := rootGroup_conj hclass k t
    rw [rootGroup_eq_of_mem hk] at this
    exact this.symm
  have hMA : M ≤ Subgroup.normalizer (rootGroup (CorB.cls t) t : Set G) := by
    intro m hm
    apply hnorm
    apply hrs
    · exact (Subgroup.mem_normalizer_iff.mp (Pair.le_normalizer_B0 h hm) t).mp ht
    · intro e
      apply ht1
      calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
        _ = 1 := by rw [e]; group
  have hA1 : rootGroup (CorB.cls t) t ≠ ⊥ := by
    intro hbot
    have : t ∈ rootGroup (CorB.cls t) t := rootSet_subset_rootGroup _ _ (hrs t ht ht1)
    rw [hbot, Subgroup.mem_bot] at this
    exact ht1 this
  have hsq : ∀ s ∈ rootSet (CorB.cls t) t, s * s = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := isConj_iff.mp hs.1
    rw [← hk]
    calc k * t * k⁻¹ * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hA2 : IsPGroup 2 (rootGroup (CorB.cls t) t) :=
    isPGroup_closure_of_pairwise (pairwise_commute_rootSet (CorB.mem_cls_self t)) hsq
  have hNA : Subgroup.normalizer (rootGroup (CorB.cls t) t : Set G) = M :=
    h.s3hyp.normalizer_eq_of hA1 hA2 hMA
  apply le_antisymm
  · rw [rootGroup, Subgroup.closure_le]
    intro e he
    obtain ⟨k, hk⟩ := isConj_iff.mp he.1
    have hkN : k ∈ Subgroup.normalizer (rootGroup (CorB.cls t) t : Set G) := by
      apply hnorm
      rw [hk]
      exact he
    rw [hNA] at hkN
    rw [← hk]
    exact (Subgroup.mem_normalizer_iff.mp (Pair.le_normalizer_B0 h hkN) t).mp ht
  · intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact (rootGroup (CorB.cls t) t).one_mem
    · exact rootSet_subset_rootGroup _ _ (hrs x hx hx1)

theorem rootGroup_eq (h : R2 M B)
    (hconj : ∀ x ∈ omegaOneSub B, ∀ y ∈ omegaOneSub B, x ≠ 1 → y ≠ 1 → IsConj x y) :
    ∀ t ∈ omegaOneSub B, t ≠ 1 → rootGroup (CorB.cls t) t = omegaOneSub B :=
  fun _ ht ht1 => rootGroup_eq_of h hconj ht ht1

theorem conjCent_mem_lam (h : R2 M B) :
    ∀ t ∈ omegaOneSub B, t ≠ 1 → ∀ τ : G, τ * t = t * τ → IsConj t τ →
      ∃ A ∈ Lam M B, τ ∈ A :=
  fun _ ht ht1 _ hc hτ => exists_lam_of_commute h ht ht1 hτ hc

theorem ncpair_of_comm_ne (hW : R2Weak) (h : R2 M B) {F : Subgroup G} (hF : F ∈ Lam M B)
    (hne : F ≠ omegaOneSub B) :
    ∃ g : G, F = conjSubgroup g (omegaOneSub B) ∧
      NCPair (omegaTwoSub B) (conjSubgroup g (omegaTwoSub B)) := by
  obtain ⟨g, hg, hFM⟩ := hF
  refine ⟨g, hg, ?_⟩
  have := ncpair_of_commute hW h (g := 1) (g' := g)
    (fun a ha b hb => by
      rw [conjSubgroup_one] at ha
      exact (R2.comm_B0 h ⟨g, hg, hFM⟩ b (by rw [hg]; exact hb) a ha).symm)
    (by rw [conjSubgroup_one, ← hg]; exact fun e => hne e.symm)
  rwa [conjSubgroup_one] at this

end CertOnly

section Cert

variable
  (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
include hCen hU

theorem exists_conj_mul {U V : Subgroup G} (P : NCPair U V)
    (hV16 : Nat.card ↥V = 16) (hV4 : Nat.card ↥(omegaOneSub V) = 4)
    {t τ : G} (ht : t ∈ omegaOneSub U) (ht1 : t ≠ 1) (hτ : τ ∈ omegaOneSub V) :
    ∃ y ∈ V, y * t * y⁻¹ = τ * t := by
  have hVc := P.setup.comm₁
  have hUV : U ⊓ V = ⊥ := P.setup.inf_eq_bot P.ne
  have htN : t ∈ omegaOneSub V ⊔ omegaOneSub U := Subgroup.mem_sup_right ht
  have hmem : ∀ y : ↥V, (y : G) * t * (y : G)⁻¹ * t⁻¹ ∈ omegaOneSub V := fun y =>
    P.symm.comm_mem hCen hU y.2 htN
  let ψ : ↥V →* ↥(omegaOneSub V) :=
    { toFun := fun y => ⟨(y : G) * t * (y : G)⁻¹ * t⁻¹, hmem y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a : G) * b) * t * ((a : G) * b)⁻¹ * t⁻¹ =
          ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹)
        have e1 : ((a : G) * b) * t * ((a : G) * b)⁻¹ * t⁻¹ =
            ((a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G)⁻¹) *
              ((a : G) * t * (a : G)⁻¹ * t⁻¹) := by group
        have hb' : (b : G) * t * (b : G)⁻¹ * t⁻¹ ∈ V := omegaOneSub_le V (hmem b)
        have ha' : (a : G) * t * (a : G)⁻¹ * t⁻¹ ∈ V := omegaOneSub_le V (hmem a)
        have e2 : (a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G)⁻¹ =
            (b : G) * t * (b : G)⁻¹ * t⁻¹ := by
          rw [hVc a a.2 _ hb']
          group
        rw [e1, e2]
        exact hVc _ hb' _ ha' }
  have hψ : ∀ y : ↥V, ((ψ y : ↥(omegaOneSub V)) : G) = (y : G) * t * (y : G)⁻¹ * t⁻¹ :=
    fun _ => rfl
  have hker : ψ.ker = (omegaOneSub V).subgroupOf V := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      by_contra hyV
      have h1 : (y : G) * t * (y : G)⁻¹ * t⁻¹ = 1 := by
        rw [← hψ y, hy]
        rfl
      have hcomm : (y : G) * t = t * y := by
        rw [mul_inv_eq_one] at h1
        rwa [mul_inv_eq_iff_eq_mul] at h1
      have h2 := P.symm.cent hCen hU y.2 hyV htN hcomm
      have h3 : t ∈ U ⊓ V :=
        ⟨omegaOneSub_le U ht, omegaOneSub_le V h2⟩
      rw [hUV, Subgroup.mem_bot] at h3
      exact ht1 h3
    · intro hy
      apply Subtype.ext
      show (y : G) * t * (y : G)⁻¹ * t⁻¹ = 1
      have hc := P.comm_N hCen hU (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left ht)
      rw [hc]
      group
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hkc : Nat.card ψ.ker = 4 := by
    rw [hker, ← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (omegaOneSub_le V)).toEquiv
  rw [hkc, hV16] at hcard
  have hr : Nat.card ψ.range = 4 := by omega
  have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hr, hV4])
  have hmemr : (⟨τ, hτ⟩ : ↥(omegaOneSub V)) ∈ ψ.range := by rw [htop]; trivial
  obtain ⟨y, hy⟩ := hmemr
  refine ⟨y, y.2, ?_⟩
  have h1 := congrArg Subtype.val hy
  rw [hψ y] at h1
  simp only at h1
  calc (y : G) * t * (y : G)⁻¹ = ((y : G) * t * (y : G)⁻¹ * t⁻¹) * t := by group
    _ = τ * t := by rw [h1]

theorem inf_centralizer_eq_bot (hW : R2Weak) (h : R2 M B) {F : Subgroup G} (hF : F ∈ Lam M B)
    (hne : F ≠ omegaOneSub B) : F ⊓ Subgroup.centralizer (omegaTwoSub B : Set G) = ⊥ := by
  obtain ⟨g, hg, P⟩ := ncpair_of_comm_ne hW h hF hne
  by_contra hbot
  obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨hfF, hfC⟩ := Subgroup.mem_inf.mp hf
  have hfg : f ∈ conjSubgroup g (omegaOneSub B) := hg ▸ hfF
  have hf1' : f ≠ 1 := fun e => hf1 (Subtype.ext e)
  have hUN : omegaTwoSub B ≤ Subgroup.normalizer (conjSubgroup g (omegaTwoSub B) : Set G) := by
    intro u hu
    exact Pair.mem_normalizer_conj_U h hfg hf1' ((Subgroup.mem_centralizer_iff.mp hfC) u hu)
  have hnrm := P.nrm_eq hCen hU
  have hle : omegaTwoSub B ≤ nrm (omegaTwoSub B) (conjSubgroup g (omegaTwoSub B)) :=
    le_inf le_rfl hUN
  rw [hnrm, h.omegaOne_omegaTwo] at hle
  exact Pair.B0_ne_U h (le_antisymm (Pair.B0_le_U h) hle)

theorem exists_conj_mul_of_lam (hW : R2Weak) (h : R2 M B) {F : Subgroup G} (hF : F ∈ Lam M B)
    (hne : F ≠ omegaOneSub B) {t τ : G} (ht : t ∈ omegaOneSub B) (ht1 : t ≠ 1) (hτ : τ ∈ F) :
    ∃ y : G, y * t * y⁻¹ = τ * t := by
  obtain ⟨g, hg, P⟩ := ncpair_of_comm_ne hW h hF hne
  have hΩ := Pair.omegaOne_conj_U h g
  obtain ⟨y, -, hy⟩ := Pair.exists_conj_mul hCen hU P (Pair.card_conj_U h g)
    (by rw [hΩ]; exact Pair.card_conj_B0 h g) (t := t) (τ := τ)
    (by rw [h.omegaOne_omegaTwo]; exact ht) ht1 (by rw [hΩ, ← hg]; exact hτ)
  exact ⟨y, hy⟩

theorem fusion_lam (hW : R2Weak) (h : R2 M B) :
    ∀ F ∈ Lam M B, F ≠ omegaOneSub B → ∀ t ∈ omegaOneSub B, t ≠ 1 → ∀ τ ∈ F, τ ≠ 1 →
      IsConj t (t * τ) := by
  intro F hF hne t ht ht1 τ hτ _
  obtain ⟨y, hy⟩ := exists_conj_mul_of_lam hCen hU hW h hF hne ht ht1 hτ
  have hcomm : τ * t = t * τ := R2.comm_B0 h hF τ hτ t ht
  exact isConj_iff.mpr ⟨y, by rw [hy, hcomm]⟩

theorem isConj_B0_of_exists (hW : R2Weak) (h : R2 M B)
    (hex : ∃ F ∈ Lam M B, F ≠ omegaOneSub B) :
    ∀ x ∈ omegaOneSub B, ∀ y ∈ omegaOneSub B, x ≠ 1 → y ≠ 1 → IsConj x y := by
  obtain ⟨F, hF, hne⟩ := hex
  obtain ⟨g, hg, P⟩ := ncpair_of_comm_ne hW h hF hne
  have hΩ := Pair.omegaOne_conj_U h g
  obtain ⟨⟨τ, hτ⟩, hτ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (show F ≠ ⊥ from hg ▸ Pair.conj_B0_ne_bot h g)
  have hτ1' : τ ≠ 1 := fun e => hτ1 (Subtype.ext e)
  have key : ∀ x ∈ omegaOneSub B, x ≠ 1 → IsConj x τ := by
    intro x hx hx1
    obtain ⟨y₁, -, hy₁⟩ := Pair.exists_conj_mul hCen hU P (Pair.card_conj_U h g)
      (by rw [hΩ]; exact Pair.card_conj_B0 h g) (t := x) (τ := τ)
      (by rw [h.omegaOne_omegaTwo]; exact hx) hx1 (by rw [hΩ, ← hg]; exact hτ)
    obtain ⟨y₂, -, hy₂⟩ := Pair.exists_conj_mul hCen hU P.symm (Pair.card_U h)
      (by rw [h.omegaOne_omegaTwo]; exact h.card4) (t := τ) (τ := x)
      (by rw [hΩ, ← hg]; exact hτ) hτ1' (by rw [h.omegaOne_omegaTwo]; exact hx)
    have hcomm : x * τ = τ * x := (R2.comm_B0 h hF τ hτ x hx).symm
    refine (isConj_iff.mpr ⟨y₁, hy₁⟩).trans ?_
    rw [← hcomm]
    exact (isConj_iff.mpr ⟨y₂, hy₂⟩).symm
  intro x hx y hy hx1 hy1
  exact (key x hx hx1).trans (key y hy hy1).symm

theorem mul_mem_B0_of_commute (hW : R2Weak) (h : R2 M B) {F E : Subgroup G} (hF : F ∈ Lam M B)
    (hE : E ∈ Lam M B) (hFE : F ≠ E)
    (hcomm : ∀ f ∈ F, ∀ e ∈ E, f * e = e * f) {f e : G} (hf : f ∈ F) (he : e ∈ E)
    (hC : f * e ∈ Subgroup.centralizer (omegaTwoSub B : Set G)) : f * e ∈ omegaOneSub B := by
  by_cases hf1 : f = 1
  · subst hf1
    by_cases hEB : E = omegaOneSub B
    · rw [one_mul, ← hEB]
      exact he
    · have h1 : e ∈ E ⊓ Subgroup.centralizer (omegaTwoSub B : Set G) :=
        ⟨he, by simpa using hC⟩
      rw [inf_centralizer_eq_bot hCen hU hW h hE hEB, Subgroup.mem_bot] at h1
      rw [h1, mul_one]
      exact (omegaOneSub B).one_mem
  obtain ⟨g, hg, hFM⟩ := hF
  obtain ⟨g', hg', hEM⟩ := hE
  have P := ncpair_of_commute hW h (g := g) (g' := g') (by rw [← hg, ← hg']; exact hcomm)
    (by rw [← hg, ← hg']; exact hFE)
  have hΩ := Pair.omegaOne_conj_U h g
  have hΩ' := Pair.omegaOne_conj_U h g'
  obtain ⟨y, hy, hye⟩ := Pair.exists_conj_mul hCen hU P (Pair.card_conj_U h g')
    (by rw [hΩ']; exact Pair.card_conj_B0 h g') (t := f) (τ := e)
    (by rw [hΩ, ← hg]; exact hf) hf1 (by rw [hΩ', ← hg']; exact he)
  have hyX : y ∈ conjSubgroup g (omegaTwoSub B) ⊔ conjSubgroup g' (omegaTwoSub B) :=
    Subgroup.mem_sup_right hy
  have hFle : F ≤ omegaOneSub (conjSubgroup g (omegaTwoSub B)) ⊔
      omegaOneSub (conjSubgroup g' (omegaTwoSub B)) := by
    rw [hΩ, ← hg]
    exact le_sup_left
  have hF'' : conjSubgroup y F ∈ Lam M B := by
    refine ⟨y * g, by rw [hg, conjSubgroup_mul], ?_⟩
    intro x hx
    rw [mem_conjSubgroup] at hx
    have hxN := P.conj_mem_N hCen hU hyX (hFle hx)
    rw [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at hxN
    have hNM : omegaOneSub (conjSubgroup g (omegaTwoSub B)) ⊔
        omegaOneSub (conjSubgroup g' (omegaTwoSub B)) ≤ M := by
      rw [hΩ, hΩ', ← hg, ← hg']
      exact sup_le hFM hEM
    exact hNM hxN
  have hz : f * e ∈ conjSubgroup y F := by
    rw [mem_conjSubgroup]
    have : f * e = y * f * y⁻¹ := by
      rw [hye, ← hcomm f hf e he]
    rw [this, show y⁻¹ * (y * f * y⁻¹) * y = f by group]
    exact hf
  by_cases hB : conjSubgroup y F = omegaOneSub B
  · rw [← hB]
    exact hz
  · have h2 : f * e ∈ conjSubgroup y F ⊓ Subgroup.centralizer (omegaTwoSub B : Set G) :=
      ⟨hz, hC⟩
    rw [inf_centralizer_eq_bot hCen hU hW h hF'' hB, Subgroup.mem_bot] at h2
    rw [h2]
    exact (omegaOneSub B).one_mem

end Cert

end Pair

end CFSG.CGT.PushingUpLit.SolKR2
