module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EBridgeIso
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EAbs65
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EAbs66
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EGModel

public section

set_option linter.unusedSectionVars false

open CFSG.Open

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

section Transfer
variable {G : Type} [Group G] {B : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [Finite V] (e : ↥B ≃* Multiplicative V)
variable {W Q : Subgroup (MulAut ↥B)} {A F : Subgroup ↥B}

theorem glHom_injective : Function.Injective (glHom e) := (glHom e).injective

theorem mem_normalizer_gmap {H : Subgroup (MulAut ↥B)} {g : MulAut ↥B} :
    glHom e g ∈ Subgroup.normalizer (gmap e H : Set (V ≃ₗ[ZMod 3] V)) ↔
      g ∈ Subgroup.normalizer (H : Set (MulAut ↥B)) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg k
    have := hg (glHom e k)
    rwa [glHom_mem_gmap, ← map_mul, ← map_inv, ← map_mul, glHom_mem_gmap] at this
  · intro hg y
    obtain ⟨k, rfl⟩ := (glHom e).surjective y
    rw [glHom_mem_gmap, ← map_mul, ← map_inv, ← map_mul, glHom_mem_gmap]
    exact hg k

theorem gmap_normalizer (H : Subgroup (MulAut ↥B)) :
    gmap e (Subgroup.normalizer (H : Set (MulAut ↥B))) =
      Subgroup.normalizer (gmap e H : Set (V ≃ₗ[ZMod 3] V)) := by
  ext y
  rw [mem_gmap]
  have := mem_normalizer_gmap e (H := H) (g := (glHom e).symm y)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem conjSub_gmap (x : MulAut ↥B) (H : Subgroup (MulAut ↥B)) :
    Datum.conjSub (glHom e x) (gmap e H) = gmap e (conjAutW x H) := by
  ext y
  rw [Datum.conjSub, Subgroup.mem_map, mem_gmap, conjAutW, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨k, hk, rfl⟩ := gmap_elim e hh
    refine ⟨k, hk, ?_⟩
    apply (glHom e).injective
    simp [map_mul, map_inv]
  · rintro ⟨k, hk, hk'⟩
    refine ⟨glHom e k, (glHom_mem_gmap e).2 hk, ?_⟩
    apply (glHom e).symm.injective
    rw [← hk']
    simp [map_mul, map_inv]


theorem gmap_inf (H K : Subgroup (MulAut ↥B)) : gmap e (H ⊓ K) = gmap e H ⊓ gmap e K :=
  Subgroup.map_inf H K _ (glHom_injective e)

theorem gmap_sup (H K : Subgroup (MulAut ↥B)) : gmap e (H ⊔ K) = gmap e H ⊔ gmap e K :=
  Subgroup.map_sup H K _

theorem gmap_eq_bot {H : Subgroup (MulAut ↥B)} : gmap e H = ⊥ ↔ H = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ (glHom_injective e)

theorem card_gmap (H : Subgroup (MulAut ↥B)) : Nat.card (gmap e H) = Nat.card H :=
  Subgroup.card_map_of_injective (glHom_injective e)

theorem transfer64 (h : Setup W Q A F) (hD : (h.datum e).Lemma64Concl)
    (X : Subgroup (MulAut ↥B)) (hXW : X ≤ W) (hodd : Odd (Nat.card X))
    (hQX : ∀ q ∈ Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X) : ∀ q ∈ Q, ∀ x ∈ X, q * x = x * q := by
  intro q hq x hx
  have hXD : gmap e X ∈ (h.datum e).NWQ2 := by
    refine ⟨gmap_mono e hXW, by rwa [card_gmap], ?_⟩
    intro q' hq' x' hx'
    obtain ⟨q0, hq0, rfl⟩ := gmap_elim e hq'
    obtain ⟨x0, hx0, rfl⟩ := gmap_elim e hx'
    rw [← map_mul, ← map_inv, ← map_mul, glHom_mem_gmap]
    exact hQX q0 hq0 x0 hx0
  have hq' : glHom e q ∈ (h.datum e).Q := (glHom_mem_gmap e).2 hq
  have := Subgroup.mem_centralizer_iff.1 (hD hq') (glHom e x)
    (le_sSup hXD ((glHom_mem_gmap e).2 hx))
  rw [← map_mul, ← map_mul] at this
  exact ((glHom_injective e) this).symm


@[expose] def Concl65 (W Q : Subgroup (MulAut ↥B)) (A F : Subgroup ↥B) : Prop :=
  (W ≤ Subgroup.normalizer (Q : Set (MulAut ↥B))) ∨
  ∃ x ∈ W,
    (Q ⊓ conjAutW x Q = ⊥ ∧ ∀ q ∈ Q, ∀ q' ∈ conjAutW x Q, q * q' = q' * q) ∧
    x * x ∈ Subgroup.normalizer (Q : Set (MulAut ↥B)) ∧
    (imgB x A = F ∧ imgB x F = A) ∧
    (∀ g ∈ W ⊓ Subgroup.normalizer ((Q ⊔ conjAutW x Q : Subgroup (MulAut ↥B)) :
        Set (MulAut ↥B)), permutesAF A F g) ∧
    (W ≤ Subgroup.normalizer ((Q ⊔ conjAutW x Q : Subgroup (MulAut ↥B)) : Set (MulAut ↥B)) ∨
      ((W ⊓ Subgroup.normalizer ((Q ⊔ conjAutW x Q : Subgroup (MulAut ↥B)) :
          Set (MulAut ↥B))).relIndex W = 5 ∧
        ∀ u v : ↥B, u ≠ 1 → v ≠ 1 → ∃ w ∈ W, w u = v))

theorem toSub_imgB (x : MulAut ↥B) (S : Subgroup ↥B) :
    toSub e (imgB x S) = Datum.img (glHom e x)⁻¹ (toSub e S) := by
  rw [imgB, ← map_inv, ← toSub_map]

theorem transfer65 (h : Setup W Q A F) (hD : (h.datum e).Lemma65Concl) : Concl65 W Q A F := by
  unfold Datum.Lemma65Concl Datum.NW at hD
  simp only [Setup.datum_Q, Setup.datum_W, Setup.datum_A, Setup.datum_F] at hD
  rcases hD with hα | ⟨x, hxW, ⟨hint, hcomm⟩, hxx, ⟨hA, hF⟩, hperm, hlast⟩
  · left
    rw [Subgroup.le_normalizer_iff]
    intro w hw k hk
    have := hα (glHom e w) ((glHom_mem_gmap e).2 hw) (glHom e k) ((glHom_mem_gmap e).2 hk)
    rwa [← map_mul, ← map_inv, ← map_mul, glHom_mem_gmap] at this
  · obtain ⟨x', hx', rfl⟩ := gmap_elim e hxW
    right
    refine ⟨x', hx', ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← gmap_eq_bot e, gmap_inf, ← conjSub_gmap]
      exact hint
    · intro q hq q' hq'
      have := hcomm (glHom e q) ((glHom_mem_gmap e).2 hq) (glHom e q')
        (by rw [conjSub_gmap]; exact (glHom_mem_gmap e).2 hq')
      rw [← map_mul, ← map_mul] at this
      exact glHom_injective e this
    · rw [← mem_normalizer_gmap e, map_mul]; exact hxx
    · rw [← toSub_eq_iff e, toSub_imgB]; exact hA
    · rw [← toSub_eq_iff e, toSub_imgB]; exact hF
    · intro g hg
      have hN : gmap e W ⊓ Subgroup.normalizer ((gmap e Q ⊔ Datum.conjSub (glHom e x') (gmap e Q) :
          Subgroup (V ≃ₗ[ZMod 3] V)) : Set (V ≃ₗ[ZMod 3] V)) =
          gmap e (W ⊓ Subgroup.normalizer ((Q ⊔ conjAutW x' Q : Subgroup (MulAut ↥B)) :
            Set (MulAut ↥B))) := by
        rw [conjSub_gmap, ← gmap_sup, ← gmap_normalizer, ← gmap_inf]
      have := hperm (glHom e g) (by rw [hN]; exact (glHom_mem_gmap e).2 hg)
      unfold Datum.PermutesAF at this
      simp only [Setup.datum_A, Setup.datum_F] at this
      unfold permutesAF
      simp only [← toSub_eq_iff e, toSub_map]
      exact this
    · rw [conjSub_gmap, ← gmap_sup, ← gmap_normalizer] at hlast
      rcases hlast with hl | ⟨hl, htrans⟩
      · left
        intro w hw
        have := hl ((glHom_mem_gmap e).2 hw)
        rwa [glHom_mem_gmap] at this
      · right
        refine ⟨?_, ?_⟩
        · rw [← gmap_inf] at hl
          unfold gmap at hl
          rwa [Subgroup.relIndex_map_map_of_injective (f := (glHom e).toMonoidHom) _ _ (glHom_injective e)] at hl
        · intro u v hu hv
          have hu' : ev e u ≠ 0 := fun h0 => hu ((ev_eq_zero e).1 h0)
          have hv' : ev e v ≠ 0 := fun h0 => hv ((ev_eq_zero e).1 h0)
          obtain ⟨w, hw, hwuv⟩ := htrans (ev e u) (ev e v) hu' hv'
          obtain ⟨w', hw', rfl⟩ := gmap_elim e hw
          rw [glHom_ev] at hwuv
          exact ⟨w', hw', ev_injective e hwuv⟩


theorem ev_mem_fixSub (P : Subgroup (MulAut ↥B)) (b : ↥B) :
    ev e b ∈ fixSub (gmap e P) ↔ b ∈ fixB P := by
  constructor
  · intro hb p hp
    have := hb (glHom e p) ((glHom_mem_gmap e).2 hp)
    rw [glHom_ev] at this
    exact ev_injective e this
  · intro hb u hu
    obtain ⟨p, hp, rfl⟩ := gmap_elim e hu
    rw [glHom_ev, hb p hp]

theorem ev_mem_commSub (P : Subgroup (MulAut ↥B)) (y : ↥B) :
    ev e y ∈ commSub (gmap e P) ↔ y ∈ commB P := by
  constructor
  · intro hy
    have hle : commSub (gmap e P) ≤ toAddSub e (commB P) := by
      refine AddSubgroup.closure_le _ |>.2 ?_
      rintro _ ⟨u, hu, m, rfl⟩
      obtain ⟨p, hp, rfl⟩ := gmap_elim e hu
      obtain ⟨b, rfl⟩ := exists_ev e m
      have : glHom e p (ev e b) - ev e b = ev e (p b * b⁻¹) := by
        rw [glHom_ev]; simp [sub_eq_add_neg]
      rw [SetLike.mem_coe, this, ev_mem_toAddSub]
      exact Subgroup.subset_closure ⟨p, hp, b, rfl⟩
    exact (ev_mem_toAddSub e).1 (hle hy)
  · intro hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, b, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨glHom e p, (glHom_mem_gmap e).2 hp, ev e b, ?_⟩
      rw [glHom_ev]; simp [sub_eq_add_neg]
    | one => rw [ev_one]; exact AddSubgroup.zero_mem _
    | mul x y _ _ hx hy => rw [ev_mul]; exact AddSubgroup.add_mem _ hx hy
    | inv x _ hx => rw [ev_inv]; exact AddSubgroup.neg_mem _ hx


theorem card_commB (P : Subgroup (MulAut ↥B)) :
    Nat.card (commB P) = Nat.card (commSub (gmap e P)) :=
  card_of_iff e _ _ fun x => (ev_mem_commSub e P x).symm

theorem index_fixB (P : Subgroup (MulAut ↥B)) :
    (fixB P).index = (fixSub (gmap e P)).index := by
  have : Finite ↥B := Finite.of_equiv V (evEquiv e).symm
  have hV : Nat.card V = Nat.card ↥B := (Nat.card_congr (evEquiv e)).symm
  have h1 := Subgroup.card_mul_index (fixB P)
  have h2 := AddSubgroup.card_mul_index (fixSub (gmap e P))
  have hc : Nat.card (fixB P) = Nat.card (fixSub (gmap e P)) :=
    card_of_iff e _ _ fun x => (ev_mem_fixSub e P x).symm
  rw [← hc, hV] at h2
  have hpos : 0 < Nat.card (fixB P) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

theorem mem_map_subtype_center {M : Type*} [Group M] (Q : Subgroup M) (τ : M) :
    τ ∈ (Subgroup.center Q).map Q.subtype ↔ τ ∈ Q ∧ ∀ q ∈ Q, q * τ = τ * q := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun q hq => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨q, hq⟩
    exact congrArg Subtype.val this
  · rintro ⟨hτ, hc⟩
    refine ⟨⟨τ, hτ⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2), rfl⟩

theorem datum_T (h : Setup W Q A F) : (h.datum e).T = gmap e (centerSub Q) := by
  ext τ
  unfold Datum.T centerSub
  rw [mem_map_subtype_center]
  constructor
  · rintro ⟨hτ, hc⟩
    obtain ⟨τ', hτ', rfl⟩ := gmap_elim e hτ
    rw [glHom_mem_gmap, mem_map_subtype_center]
    refine ⟨hτ', fun q hq => ?_⟩
    have := hc (glHom e q) ((glHom_mem_gmap e).2 hq)
    rw [← map_mul, ← map_mul] at this
    exact glHom_injective e this
  · intro hτ
    obtain ⟨τ', hτ', rfl⟩ := gmap_elim e hτ
    rw [glHom_mem_gmap, mem_map_subtype_center] at hτ
    refine ⟨(glHom_mem_gmap e).2 hτ.1, fun q hq => ?_⟩
    obtain ⟨q', hq', rfl⟩ := gmap_elim e hq
    rw [← map_mul, ← map_mul, hτ.2 q' hq']


@[expose] def Concl66 (W Q : Subgroup (MulAut ↥B)) (A F : Subgroup ↥B) (P : Subgroup (MulAut ↥B)) :
    Prop :=
  (∃ w ∈ W, ∀ τ ∈ centerSub Q, ∀ p ∈ P, (w⁻¹ * p * w) * τ = τ * (w⁻¹ * p * w)) ∧
  (Nat.card P ≤ 9 ∧ IsElemAbelian 3 P) ∧
  (∀ y ∈ commB P, ∀ p ∈ P, p y = y) ∧
  ((fixB P).index = Nat.card (commB P) ∧ (Nat.card P = 9 → Nat.card (commB P) = 9)) ∧
  ((∀ τ ∈ centerSub Q, ∀ p ∈ P, p * τ = τ * p) → Nat.card (commB P) = 3 →
    ((commB P ≤ F ∧ A ≤ fixB P) ∨ (commB P ≤ A ∧ F ≤ fixB P)))

theorem transfer66 (h : Setup W Q A F) (P : Subgroup (MulAut ↥B))
    (hD : (h.datum e).Lemma66Concl (gmap e P)) : Concl66 W Q A F P := by
  unfold Datum.Lemma66Concl at hD
  simp only [Setup.datum_W, Setup.datum_A, Setup.datum_F, datum_T e h] at hD
  obtain ⟨⟨w, hw, hw1⟩, ⟨hcard, hexp, hcomm⟩, hcomm2, ⟨hidx, hcard9⟩, hv⟩ := hD
  obtain ⟨w', hw', rfl⟩ := gmap_elim e hw
  refine ⟨⟨w', hw', ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro τ hτ p hp
    have := hw1 (glHom e τ) ((glHom_mem_gmap e).2 hτ) (glHom e p) ((glHom_mem_gmap e).2 hp)
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at this
    exact glHom_injective e this
  · rwa [← card_gmap e]
  · exact ⟨⟨fun a b => Subtype.ext (glHom_injective e (by
      have := hcomm (glHom e a) ((glHom_mem_gmap e).2 a.2) (glHom e b) ((glHom_mem_gmap e).2 b.2)
      simpa [map_mul] using this))⟩⟩
  · intro p hp
    have := hexp (glHom e p) ((glHom_mem_gmap e).2 hp)
    rw [← map_pow, ← map_one (glHom e)] at this
    exact glHom_injective e this
  · intro y hy p hp
    have := hcomm2 (ev e y) ((ev_mem_commSub e P y).2 hy) (glHom e p) ((glHom_mem_gmap e).2 hp)
    rw [glHom_ev] at this
    exact ev_injective e this
  · rw [index_fixB e, card_commB e]; exact hidx
  · intro h9
    rw [card_commB e]
    exact hcard9 (by rwa [card_gmap e])
  · intro hτ h3
    have hτ' : ∀ τ ∈ gmap e (centerSub Q), ∀ p ∈ gmap e P, p * τ = τ * p := by
      intro τ hτ0 p hp
      obtain ⟨τ', hτ'', rfl⟩ := gmap_elim e hτ0
      obtain ⟨p', hp', rfl⟩ := gmap_elim e hp
      rw [← map_mul, ← map_mul, hτ τ' hτ'' p' hp']
    rcases hv hτ' (by rwa [← card_commB e]) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨fun y hy => ?_, fun a ha => ?_⟩
      · exact (ev_mem_toSub e).1 (h1 _ ((ev_mem_commSub e P y).2 hy))
      · exact (ev_mem_fixSub e P a).1 (h2 _ ((ev_mem_toSub e).2 ha))
    · right
      refine ⟨fun y hy => ?_, fun a ha => ?_⟩
      · exact (ev_mem_toSub e).1 (h1 _ ((ev_mem_commSub e P y).2 hy))
      · exact (ev_mem_fixSub e P a).1 (h2 _ ((ev_mem_toSub e).2 ha))

end Transfer

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open Sec6E CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem bridge_facts {G : Type} [Group G] [Finite G] (hC : GLCaseFour G 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G} (hw : IsExtremalWitness B b L A) :
    Nat.card ↥B = 81 ∧ (∀ x : ↥B, x ^ 3 = 1) ∧ (∀ x y : ↥B, x * y = y * x) ∧
      Nat.card ↥(inB B A) = 9 ∧ Nat.card ↥(inB B (B ⊓ L)) = 9 := by
  obtain ⟨⟨⟨hcomm, hexp⟩, hcard, -⟩, -⟩ := hB
  obtain ⟨hL9, ⟨hAB, -, hA9⟩, -⟩ := hw.2.2.2.2.2.1
  refine ⟨?_, fun x => Subtype.ext (hexp x.1 x.2), fun x y => Subtype.ext ?_, ?_, ?_⟩
  · rw [hcard, hC.2.1]; norm_num
  · exact setLike_mul_comm (s := B) x.2 y.2
  · rw [inB, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hA9]; norm_num
  · rw [inB, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B ⊓ L ≤ B)).toEquiv, hL9]

section GSide
variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {A F : Subgroup ↥B}
  {Q : Subgroup (MulAut ↥B)}

theorem exists_model (hexp : ∀ x : ↥B, x ^ 3 = 1) (hcomm : ∀ x y : ↥B, x * y = y * x) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : Finite V),
      Nonempty (↥B ≃* Multiplicative V) := by
  obtain ⟨V, i1, i2, ⟨e⟩⟩ := exists_vec ↥B hcomm hexp
  exact ⟨V, i1, i2, Finite.of_equiv ↥B e.toEquiv, ⟨e⟩⟩

theorem GSideK.setup (hK : GSideK B A F Q) (hB : Nat.card ↥B = 81) (hA : Nat.card A = 9)
    (hF : Nat.card F = 9) (hQ8 : Nonempty (Q ≃* QuaternionGroup 2)) :
    Setup (autIn B ⊤) Q A F :=
  ⟨hB, hA, hF, hK.Q_le_W, hK.Q_fix_A, hK.Q_mem_F, hK.Q_faith_F, hQ8⟩

theorem lemma64_of_gSide (hB : Nat.card ↥B = 81) (hexp : ∀ x : ↥B, x ^ 3 = 1)
    (hcomm : ∀ x y : ↥B, x * y = y * x) (hA : Nat.card A = 9) (hF : Nat.card F = 9)
    (hQ8 : Nonempty (Q ≃* QuaternionGroup 2)) (hK : GSideK B A F Q) :
    Q ≤ Subgroup.centralizer ((sSup (NWQ2 B Q) : Subgroup (MulAut ↥B)) : Set (MulAut ↥B)) := by
  obtain ⟨V, _, _, _, ⟨e⟩⟩ := exists_model hexp hcomm
  have h := hK.setup hB hA hF hQ8
  have hD := (h.datum e).lemma64_abs (hasKa_of e h hK.hasKa)
  have key := transfer64 e h hD
  have hle : sSup (NWQ2 B Q) ≤ Subgroup.centralizer (Q : Set (MulAut ↥B)) :=
    sSup_le fun X hX x hx => by
      rw [Subgroup.mem_centralizer_iff]
      exact fun q hq => key X hX.1 hX.2.1 hX.2.2 q hq x hx
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact ((Subgroup.mem_centralizer_iff.1 (hle hs)) q hq).symm

theorem lemma65_of_gSide (hB : Nat.card ↥B = 81) (hexp : ∀ x : ↥B, x ^ 3 = 1)
    (hcomm : ∀ x y : ↥B, x * y = y * x) (hA : Nat.card A = 9) (hF : Nat.card F = 9)
    (hQ8 : Nonempty (Q ≃* QuaternionGroup 2)) (hK : GSideK B A F Q) (hJ : GSideJ B A F Q) :
    Concl65 (autIn B ⊤) Q A F := by
  obtain ⟨V, _, _, _, ⟨e⟩⟩ := exists_model hexp hcomm
  have h := hK.setup hB hA hF hQ8
  exact transfer65 e h ((h.datum e).lemma65_abs (hasKa_of e h hK.hasKa) (hasJ_of e h hJ))

theorem lemma66_of_gSide (hB : Nat.card ↥B = 81) (hexp : ∀ x : ↥B, x ^ 3 = 1)
    (hcomm : ∀ x y : ↥B, x * y = y * x) (hA : Nat.card A = 9) (hF : Nat.card F = 9)
    (hQ8 : Nonempty (Q ≃* QuaternionGroup 2)) (hK : GSideK B A F Q) (hJ : GSideJ B A F Q)
    (P : Subgroup (MulAut ↥B)) (hPW : P ≤ autIn B ⊤) (hP : IsPGroup 3 P) :
    Concl66 (autIn B ⊤) Q A F P := by
  obtain ⟨V, _, _, _, ⟨e⟩⟩ := exists_model hexp hcomm
  have h := hK.setup hB hA hF hQ8
  have h65 := (h.datum e).lemma65_abs (hasKa_of e h hK.hasKa) (hasJ_of e h hJ)
  exact transfer66 e h P
    ((h.datum e).lemma66_abs h65 (gmap e P) (gmap_mono e hPW) (hP.map _))

end GSide
end CFSG.HardMathSupport.Solomon.UniquenessMaximal
