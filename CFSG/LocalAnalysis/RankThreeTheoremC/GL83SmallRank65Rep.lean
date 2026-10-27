module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65GLTwo
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

private noncomputable def gl65rep_lin {f : ℕ} {A : Type*} [CommGroup A]
    [Module (ZMod f) (Additive A)] : MulAut A →* (Additive A ≃ₗ[ZMod f] Additive A) :=
  MonoidHom.mk' (fun φ => (MulEquiv.toAdditive φ).toLinearEquiv
    (fun c x => ZMod.map_smul (MulEquiv.toAdditive φ) c x))
    (fun _ _ => LinearEquiv.ext fun _ => rfl)

private theorem gl65rep_lin_injective {f : ℕ} {A : Type*} [CommGroup A]
    [Module (ZMod f) (Additive A)] : Function.Injective (gl65rep_lin (f := f) (A := A)) :=
  fun _ _ h => MulEquiv.ext fun a => LinearEquiv.congr_fun h (Additive.ofMul a)

private theorem gl65rep_comm_aux {f : ℕ} (hf : f.Prime) {A : Type*} [CommGroup A] [Finite A]
    [Module (ZMod f) (Additive A)] (hcard : Nat.card A ≤ f ^ 2) {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup 3 R) (ρ : R →* MulAut A) (r s : R) : ρ r * ρ s = ρ s * ρ r := by
  have : Fact f.Prime := ⟨hf⟩
  have hV : Module.finrank (ZMod f) (Additive A) ≤ 2 := by
    have h1 := FiniteField.pow_finrank_eq_natCard f (Additive A)
    have h2 : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.toMul
    rw [h2] at h1
    have h3 : f ^ Module.finrank (ZMod f) (Additive A) ≤ f ^ 2 := h1 ▸ hcard
    exact (Nat.pow_le_pow_iff_right hf.one_lt).1 h3
  let ρ' : R →* (Additive A ≃ₗ[ZMod f] Additive A) := (gl65rep_lin (f := f) (A := A)).comp ρ
  have hsurj : Function.Surjective ρ'.rangeRestrict := ρ'.rangeRestrict_surjective
  have : Finite ρ'.range := Finite.of_surjective _ hsurj
  have hS : IsPGroup 3 ρ'.range := hR.of_surjective _ hsurj
  have h := gl65_commute_of_isPGroup_three hV _ hS (ρ' r) (ρ' s) ⟨r, rfl⟩ ⟨s, rfl⟩
  exact gl65rep_lin_injective (f := f) (A := A) (by simpa [ρ'] using h)

private theorem gl65rep_comm_of_aut {f : ℕ} (hf : f.Prime) {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ f = 1)
    (hcard : Nat.card A ≤ f ^ 2) {R : Type*} [Group R] [Finite R] (hR : IsPGroup 3 R)
    (ρ : R →* MulAut A) (r s : R) : ρ r * ρ s = ρ s * ρ r := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  have : Fact f.Prime := ⟨hf⟩
  let _ : Module (ZMod f) (Additive A) := AddCommGroup.zmodModule (n := f) fun x => by
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl, ← ofMul_pow, hexp, ofMul_one]
  exact gl65rep_comm_aux hf hcard hR ρ r s

private theorem gl65rep_closure_comm {G : Type*} [Group G] {S : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := by
  have h1 : closure S ≤ centralizer S := (closure_le _).2 fun a ha =>
    mem_centralizer_iff.2 fun b hb => h b hb a ha
  intro a ha b hb
  have h2 := h1 ha
  rw [← centralizer_closure] at h2
  exact (mem_centralizer_iff.1 h2 b hb).symm

private def gl65rep_commHom {G : Type*} [Group G] (hcl : ∀ a b : G, ⁅a, b⁆ ∈ center G) (v : G) :
    G →* center G :=
  MonoidHom.mk' (fun g => ⟨⁅v, g⁆, hcl v g⟩) fun a b => Subtype.ext <| by
    have hc : a * ⁅v, b⁆ = ⁅v, b⁆ * a := mem_center_iff.1 (hcl v b) a
    change ⁅v, a * b⁆ = ⁅v, a⁆ * ⁅v, b⁆
    have h : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h, hc]; simp

private theorem gl65rep_mem_ker_commHom {G : Type*} [Group G]
    (hcl : ∀ a b : G, ⁅a, b⁆ ∈ center G) (v g : G) :
    g ∈ (gl65rep_commHom hcl v).ker ↔ v * g = g * v := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm

private theorem gl65rep_card_quotient_center_le {G : Type*} [Group G] [Finite G] {f : ℕ}
    (hf : f.Prime) (hexp : ∀ g : G, g ^ f = 1) (hcl : ∀ a b : G, ⁅a, b⁆ ∈ center G)
    (hE : ∀ E : Subgroup G, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ f ^ 2) :
    Nat.card (G ⧸ center G) ≤ f ^ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  have : Fact f.Prime := ⟨hf⟩
  have hf1 : 1 < f := hf.one_lt
  have hGp : IsPGroup f G := fun g => ⟨1, by simpa using hexp g⟩
  obtain ⟨v, hv⟩ : ∃ v : G, v ∉ center G := by
    by_contra h
    have h1 : center G = ⊤ :=
      eq_top_iff.2 fun x _ => by by_contra hx; exact h ⟨x, hx⟩
    have h2 : Nat.card (G ⧸ center G) = 1 := by
      rw [h1]; simp
    rw [h2] at hlt
    exact absurd hlt (not_lt.2 (Nat.one_le_pow _ _ hf.pos))
  have hK : Nat.card (G ⧸ center G) ≤ Nat.card (gl65rep_commHom hcl v).ker := by
    have h1 := Subgroup.card_mul_index (gl65rep_commHom hcl v).ker
    rw [Subgroup.index_ker] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center G)
    have h3 : Nat.card (gl65rep_commHom hcl v).range ≤ Nat.card (center G) :=
      Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card (center G) := Nat.card_pos
    have h4 : Nat.card (G ⧸ center G) * Nat.card (center G) ≤
        Nat.card (gl65rep_commHom hcl v).ker * Nat.card (center G) :=
      calc Nat.card (G ⧸ center G) * Nat.card (center G) = Nat.card G := h2.symm
        _ = Nat.card (gl65rep_commHom hcl v).ker * Nat.card (gl65rep_commHom hcl v).range :=
          h1.symm
        _ ≤ Nat.card (gl65rep_commHom hcl v).ker * Nat.card (center G) :=
          Nat.mul_le_mul_left _ h3
    exact Nat.le_of_mul_le_mul_right h4 hpos
  let B : Subgroup G := closure (insert v (center G : Set G))
  have hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    refine gl65rep_closure_comm fun a ha b hb => ?_
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact mem_center_iff.1 hb _
    · exact (mem_center_iff.1 ha _).symm
    · exact (mem_center_iff.1 ha _).symm
  obtain ⟨w, hwK, hwB⟩ : ∃ w ∈ (gl65rep_commHom hcl v).ker, w ∉ B := by
    by_contra h
    have hle : (gl65rep_commHom hcl v).ker ≤ B := fun w hw => by
      by_contra hwB; exact h ⟨w, hw, hwB⟩
    have := Subgroup.card_le_of_le hle
    have := hE B hB
    omega
  have hvw : v * w = w * v := (gl65rep_mem_ker_commHom hcl v w).1 hwK
  let A : Subgroup G := closure (insert w (insert v (center G : Set G)))
  have hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    refine gl65rep_closure_comm fun a ha b hb => ?_
    rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
    · rfl
    · exact hvw.symm
    · exact mem_center_iff.1 hb _
    · exact hvw
    · rfl
    · exact mem_center_iff.1 hb _
    · exact (mem_center_iff.1 ha _).symm
    · exact (mem_center_iff.1 ha _).symm
    · exact (mem_center_iff.1 ha _).symm
  have hvB : v ∈ B := subset_closure (Set.mem_insert _ _)
  have hwA : w ∈ A := subset_closure (Set.mem_insert _ _)
  have hZB : center G ≤ B := fun z hz => subset_closure (Set.mem_insert_of_mem _ hz)
  have hBA : B ≤ A := closure_mono (Set.subset_insert _ _)
  have hlt1 : Nat.card (center G) < Nat.card B :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hZB fun h => hv (h ▸ hvB))
  have hlt2 : Nat.card B < Nat.card A :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hBA fun h => hwB (h ▸ hwA))
  have hZ1 : 1 < Nat.card (center G) := by
    obtain ⟨g, hg⟩ : ∃ g : G, g * v ≠ v * g := by
      by_contra h
      exact hv (mem_center_iff.2 fun g => by by_contra hg; exact h ⟨g, hg⟩)
    have hne : ⁅v, g⁆ ≠ 1 := fun h => hg (commutatorElement_eq_one_iff_mul_comm.1 h).symm
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    apply hne
    have := hcl v g
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hGp.to_subgroup (center G))
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 (hGp.to_subgroup B)
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.1 (hGp.to_subgroup A)
  rw [ha, hb] at hlt1
  rw [hb, hc] at hlt2
  rw [ha] at hZ1
  have hab : a < b := (Nat.pow_lt_pow_iff_right hf1).1 hlt1
  have hbc : b < c := (Nat.pow_lt_pow_iff_right hf1).1 hlt2
  have ha1 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h] at hZ1; simp at hZ1
    · exact h
  have hAcard := hE A hA
  rw [hc] at hAcard
  have : c ≤ 2 := (Nat.pow_le_pow_iff_right hf1).1 hAcard
  omega

private theorem gl65rep_aut_mem_center {G : Type*} [Group G] (φ : MulAut G) {z : G}
    (hz : z ∈ center G) : φ z ∈ center G := by
  rw [mem_center_iff] at hz ⊢
  intro g
  obtain ⟨h, rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz h]

private def gl65rep_centerAut {G : Type*} [Group G] (φ : MulAut G) : MulAut (center G) where
  toFun z := ⟨φ z, gl65rep_aut_mem_center φ z.2⟩
  invFun z := ⟨φ.symm z, gl65rep_aut_mem_center φ.symm z.2⟩
  left_inv z := Subtype.ext (φ.symm_apply_apply z)
  right_inv z := Subtype.ext (φ.apply_symm_apply z)
  map_mul' x y := Subtype.ext (map_mul φ (x : G) (y : G))

private def gl65rep_centerAct {G : Type*} [Group G] {R : Type*} [Group R] (ρ : R →* MulAut G) :
    R →* MulAut (center G) :=
  MonoidHom.mk' (fun r => gl65rep_centerAut (ρ r)) fun a b =>
    MulEquiv.ext fun z => Subtype.ext <| by
      change (ρ (a * b)) (z : G) = (ρ a) ((ρ b) (z : G))
      rw [map_mul]; rfl

private def gl65rep_quotAut {G : Type*} [Group G] (φ : MulAut G) : MulAut (G ⧸ center G) :=
  QuotientGroup.congr (center G) (center G) φ (map_center_eq φ)

private def gl65rep_quotAct {G : Type*} [Group G] {R : Type*} [Group R] (ρ : R →* MulAut G) :
    R →* MulAut (G ⧸ center G) :=
  MonoidHom.mk' (fun r => gl65rep_quotAut (ρ r)) fun a b =>
    MulEquiv.ext fun q => QuotientGroup.induction_on q fun g => by
      change (((ρ (a * b)) g : G) : G ⧸ center G) = (((ρ a) ((ρ b) g) : G) : G ⧸ center G)
      rw [map_mul]; rfl

private theorem gl65rep_aut_eq_one {G : Type*} [Group G] {f n : ℕ} (hcop : Nat.Coprime n f)
    (hexp : ∀ z ∈ center G, z ^ f = 1) (φ : MulAut G) (hφ : φ ^ n = 1)
    (hZ : ∀ z ∈ center G, φ z = z) (hQ : ∀ g : G, g⁻¹ * φ g ∈ center G) : φ = 1 := by
  ext g
  set ζ : G := g⁻¹ * φ g with hζ
  have hζz : ζ ∈ center G := hQ g
  have hφg : φ g = g * ζ := by rw [hζ]; group
  have key : ∀ k : ℕ, (φ ^ k) g = g * ζ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' φ k, MulAut.mul_apply, ih, map_mul, map_pow, hZ ζ hζz, hφg, pow_succ' ζ k,
        mul_assoc]
  have h1 : g * ζ ^ n = g := by rw [← key n, hφ]; rfl
  have h2 : ζ ^ n = 1 := by simpa using h1
  have h3 : ζ = 1 := by
    have := pow_gcd_eq_one.2 ⟨h2, hexp ζ hζz⟩
    rwa [hcop, pow_one] at this
  change φ g = g
  rw [hφg, h3, mul_one]

private theorem gl65rep_abstract {G : Type*} [Group G] [Finite G] {f : ℕ} (hf : f.Prime)
    (hf3 : f ≠ 3) (hexp : ∀ g : G, g ^ f = 1) (hcl : ∀ a b : G, ⁅a, b⁆ ∈ center G)
    (hE : ∀ E : Subgroup G, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ f ^ 2)
    {R : Type*} [Group R] [Finite R] (hR : IsPGroup 3 R) (ρ : R →* MulAut G) (a b : R) :
    ρ ⁅a, b⁆ = 1 := by
  have hexpZ : ∀ z : center G, z ^ f = 1 := fun z => Subtype.ext (by simpa using hexp z)
  have hZ1 : gl65rep_centerAct ρ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.2 (gl65rep_comm_of_aut hf ?_ hexpZ ?_ hR
      (gl65rep_centerAct ρ) a b)
    · exact fun x y => Subtype.ext (mem_center_iff.1 y.2 x)
    · exact hE (center G) fun x hx y _ => (mem_center_iff.1 hx y).symm
  have hQcomm : ∀ x y : G ⧸ center G, x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x fun g => QuotientGroup.induction_on y fun h => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have e : (g * h)⁻¹ * (h * g) = ⁅h⁻¹, g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hcl h⁻¹ g⁻¹
  have hQexp : ∀ x : G ⧸ center G, x ^ f = 1 := fun x =>
    QuotientGroup.induction_on x fun g => by
      rw [← QuotientGroup.mk_pow, hexp g, QuotientGroup.mk_one]
  have hQ1 : gl65rep_quotAct ρ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (gl65rep_comm_of_aut hf hQcomm hQexp
      (gl65rep_card_quotient_center_le hf hexp hcl hE) hR (gl65rep_quotAct ρ) a b)
  obtain ⟨k, hk⟩ := hR ⁅a, b⁆
  have hcop : Nat.Coprime (3 ^ k) f :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_three hf).2 (Ne.symm hf3))
  refine gl65rep_aut_eq_one hcop (fun z _ => hexp z) (ρ ⁅a, b⁆) ?_ ?_ ?_
  · rw [← map_pow, hk, map_one]
  · intro z hz
    exact congrArg (fun e : MulAut (center G) => (e ⟨z, hz⟩ : G)) hZ1
  · intro g
    have h1 := congrArg (fun e : MulAut (G ⧸ center G) => e (g : G ⧸ center G)) hQ1
    have h2 : (((ρ ⁅a, b⁆) g : G) : G ⧸ center G) = (g : G ⧸ center G) := h1
    exact QuotientGroup.eq.1 h2.symm

private def gl65rep_conjAut {X : Type*} [Group X] (D : Subgroup X) (r : X)
    (hr : r ∈ normalizer (D : Set X)) : MulAut D where
  toFun d := ⟨r * d * r⁻¹, (mem_normalizer_iff.1 hr d).1 d.2⟩
  invFun d := ⟨r⁻¹ * d * r, by simpa using (mem_normalizer_iff.1 (inv_mem hr) d).1 d.2⟩
  left_inv d := Subtype.ext (by simp [mul_assoc])
  right_inv d := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private def gl65rep_conjAct {X : Type*} [Group X] (D R : Subgroup X)
    (hRD : R ≤ normalizer (D : Set X)) : R →* MulAut D :=
  MonoidHom.mk' (fun r => gl65rep_conjAut D r (hRD r.2)) fun a b =>
    MulEquiv.ext fun d => Subtype.ext <| by simp [gl65rep_conjAut, mul_assoc]

private theorem gl65rep_card_comm_le {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : f.Prime)
    {D : Subgroup X} (hD : IsPGroup f D) (hexp : ∀ d ∈ D, d ^ f = 1)
    (hrk : CFSG.Open.pRank f D ≤ 2) (E : Subgroup D) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    Nat.card E ≤ f ^ 2 := by
  have : Fact f.Prime := ⟨hf⟩
  have hel : IsElemAbelian f E :=
    ⟨⟨⟨fun a b => Subtype.ext (hE a a.2 b b.2)⟩⟩, fun x _ => Subtype.ext (hexp x x.2)⟩
  have hel' : IsElemAbelian f (E.map D.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hel D.subtype
  have hED : E.map D.subtype ≤ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcard : Nat.card (E.map D.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective Subtype.val_injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hD.to_le hED)
  have hk2 : k ≤ 2 := (CFSG.SectionRank.le_pRank hf.one_lt hED hel' hk).trans hrk
  rw [← hcard, hk]
  exact Nat.pow_le_pow_right hf.pos hk2

theorem gl65_commutator_le_centralizer_of_exponent {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : f.Prime) (hf2 : f ≠ 2) (hf3 : f ≠ 3) {D R : Subgroup X} (hD : IsPGroup f D)
    (hexp : ∀ d ∈ D, d ^ f = 1) (hcl : ⁅D, D⁆ ≤ centralizer (D : Set X)) (hR : IsPGroup 3 R)
    (hRD : R ≤ normalizer (D : Set X)) (hrk : CFSG.Open.pRank f D ≤ 2) :
    ⁅R, R⁆ ≤ centralizer (D : Set X) := by
  have _ := hf2
  have hcl' : ∀ x y : D, ⁅x, y⁆ ∈ center D := fun x y => by
    rw [mem_center_iff]
    intro g
    have h1 : ⁅(x : X), (y : X)⁆ ∈ centralizer (D : Set X) :=
      hcl (commutator_mem_commutator x.2 y.2)
    exact Subtype.ext (mem_centralizer_iff.1 h1 g g.2)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have key := gl65rep_abstract (G := D) hf hf3 (fun g => Subtype.ext (hexp g g.2)) hcl'
    (fun E hE => gl65rep_card_comm_le hf hD hexp hrk E hE) hR (gl65rep_conjAct D R hRD)
    ⟨a, ha⟩ ⟨b, hb⟩
  rw [mem_centralizer_iff]
  intro d hd
  have h := congrArg (fun e : MulAut D => ((e ⟨d, hd⟩ : D) : X)) key
  change ⁅a, b⁆ * d * ⁅a, b⁆⁻¹ = d at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

end CFSG.LocalAnalysis.RankThreeTheoremC
