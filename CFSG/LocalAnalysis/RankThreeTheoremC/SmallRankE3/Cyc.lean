module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.GLTwoSL
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open scoped commutatorElement


private noncomputable def r10h5_lin {f : ℕ} {A : Type*} [CommGroup A]
    [Module (ZMod f) (Additive A)] : MulAut A →* (Additive A ≃ₗ[ZMod f] Additive A) :=
  MonoidHom.mk' (fun φ => (MulEquiv.toAdditive φ).toLinearEquiv
    (fun c x => ZMod.map_smul (MulEquiv.toAdditive φ) c x))
    (fun _ _ => LinearEquiv.ext fun _ => rfl)

private theorem r10h5_lin_injective {f : ℕ} {A : Type*} [CommGroup A]
    [Module (ZMod f) (Additive A)] : Function.Injective (r10h5_lin (f := f) (A := A)) :=
  fun _ _ h => MulEquiv.ext fun a => LinearEquiv.congr_fun h (Additive.ofMul a)

private theorem r10h5_relIndex_eq {Y G : Type*} [Group Y] [Group G] (ψ : Y →* G)
    (E : Subgroup Y) : (E ⊓ ψ.ker).relIndex E = Nat.card (E.map ψ) := by
  have h1 : (E ⊓ ψ.ker).subgroupOf E = (ψ.comp E.subtype).ker := by
    ext x
    simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have h2 : (ψ.comp E.subtype).range = E.map ψ := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  rw [Subgroup.relIndex, h1, Subgroup.index_ker, h2]

private theorem r10h5_relIndex_anti {Y : Type} [Group Y] [Finite Y] {H H' E : Subgroup Y}
    (h : H ≤ H') : H'.relIndex E ≤ H.relIndex E :=
  Subgroup.relIndex_le_of_le_left h (by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite)

private theorem r10h5_relIndex_lin {f : ℕ} (hf : f.Prime) (hf3 : f ≠ 3) {A : Type} [CommGroup A]
    [Finite A] [Module (ZMod f) (Additive A)] (hV : Module.finrank (ZMod f) (Additive A) ≤ 2)
    {Y : Type} [Group Y] [Finite Y] (ρA : Y →* MulAut A)
    (hY : ∀ N : Subgroup Y, N.Normal → N.index ≠ 3) (E : Subgroup Y)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    (E ⊓ ρA.ker).relIndex E ≤ 3 := by
  have : Fact f.Prime := ⟨hf⟩
  have hK : (3 : ZMod f) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod f) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hf3 ((Nat.prime_dvd_prime_iff_eq hf Nat.prime_three).1 h')
  have hk : ((r10h5_lin (f := f) (A := A)).comp ρA).ker = ρA.ker :=
    MonoidHom.ker_comp_of_injective ρA (r10h5_lin (f := f) (A := A))
      (r10h5_lin_injective (f := f) (A := A))
  have hcardE : Nat.card (E.map ((r10h5_lin (f := f) (A := A)).comp ρA)) ≤ 3 :=
    elemAbelian_image_card_le_three hK hV _ hY E hE3 hEc
  rw [← hk, r10h5_relIndex_eq]
  exact hcardE

private theorem r10h5_relIndex_comm {f : ℕ} (hf : f.Prime) (hf3 : f ≠ 3) {A : Type} [Group A]
    [Finite A] (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ f = 1)
    (hcard : Nat.card A ≤ f ^ 2) {Y : Type} [Group Y] [Finite Y] (ρA : Y →* MulAut A)
    (hY : ∀ N : Subgroup Y, N.Normal → N.index ≠ 3) (E : Subgroup Y)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    (E ⊓ ρA.ker).relIndex E ≤ 3 := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  have : Fact f.Prime := ⟨hf⟩
  let _ : Module (ZMod f) (Additive A) := AddCommGroup.zmodModule (n := f) fun x => by
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl, ← ofMul_pow, hexp, ofMul_one]
  have hV : Module.finrank (ZMod f) (Additive A) ≤ 2 := by
    have h1 := FiniteField.pow_finrank_eq_natCard f (Additive A)
    have h2 : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.toMul
    rw [h2] at h1
    have h3 : f ^ Module.finrank (ZMod f) (Additive A) ≤ f ^ 2 := h1 ▸ hcard
    exact (Nat.pow_le_pow_iff_right hf.one_lt).1 h3
  exact r10h5_relIndex_lin hf hf3 hV ρA hY E hE3 hEc

private theorem r10h5_closure_comm {G : Type*} [Group G] {S : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := by
  have h1 : closure S ≤ centralizer S := (closure_le _).2 fun a ha =>
    mem_centralizer_iff.2 fun b hb => h b hb a ha
  intro a ha b hb
  have h2 := h1 ha
  rw [← centralizer_closure] at h2
  exact (mem_centralizer_iff.1 h2 b hb).symm

private def r10h5_commHom {G : Type*} [Group G] (hcl : ∀ a b : G, ⁅a, b⁆ ∈ center G) (v : G) :
    G →* center G :=
  MonoidHom.mk' (fun g => ⟨⁅v, g⁆, hcl v g⟩) fun a b => Subtype.ext <| by
    have hc : a * ⁅v, b⁆ = ⁅v, b⁆ * a := mem_center_iff.1 (hcl v b) a
    change ⁅v, a * b⁆ = ⁅v, a⁆ * ⁅v, b⁆
    have h : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h, hc]; simp

private theorem r10h5_mem_ker_commHom {G : Type*} [Group G]
    (hcl : ∀ a b : G, ⁅a, b⁆ ∈ center G) (v g : G) :
    g ∈ (r10h5_commHom hcl v).ker ↔ v * g = g * v := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm

private theorem r10h5_card_quotient_center_le {G : Type*} [Group G] [Finite G] {f : ℕ}
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
  have hK : Nat.card (G ⧸ center G) ≤ Nat.card (r10h5_commHom hcl v).ker := by
    have h1 := Subgroup.card_mul_index (r10h5_commHom hcl v).ker
    rw [Subgroup.index_ker] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center G)
    have h3 : Nat.card (r10h5_commHom hcl v).range ≤ Nat.card (center G) :=
      Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card (center G) := Nat.card_pos
    have h4 : Nat.card (G ⧸ center G) * Nat.card (center G) ≤
        Nat.card (r10h5_commHom hcl v).ker * Nat.card (center G) :=
      calc Nat.card (G ⧸ center G) * Nat.card (center G) = Nat.card G := h2.symm
        _ = Nat.card (r10h5_commHom hcl v).ker * Nat.card (r10h5_commHom hcl v).range :=
          h1.symm
        _ ≤ Nat.card (r10h5_commHom hcl v).ker * Nat.card (center G) :=
          Nat.mul_le_mul_left _ h3
    exact Nat.le_of_mul_le_mul_right h4 hpos
  let B : Subgroup G := closure (insert v (center G : Set G))
  have hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    refine r10h5_closure_comm fun a ha b hb => ?_
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact mem_center_iff.1 hb _
    · exact (mem_center_iff.1 ha _).symm
    · exact (mem_center_iff.1 ha _).symm
  obtain ⟨w, hwK, hwB⟩ : ∃ w ∈ (r10h5_commHom hcl v).ker, w ∉ B := by
    by_contra h
    have hle : (r10h5_commHom hcl v).ker ≤ B := fun w hw => by
      by_contra hwB; exact h ⟨w, hw, hwB⟩
    have := Subgroup.card_le_of_le hle
    have := hE B hB
    omega
  have hvw : v * w = w * v := (r10h5_mem_ker_commHom hcl v w).1 hwK
  let A : Subgroup G := closure (insert w (insert v (center G : Set G)))
  have hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    refine r10h5_closure_comm fun a ha b hb => ?_
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

private theorem r10h5_card_center_le {G : Type*} [Group G] [Finite G] {f : ℕ} (hf : f.Prime)
    (hexp : ∀ g : G, g ^ f = 1)
    (hE : ∀ S : Subgroup G, (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) → Nat.card S ≤ f ^ 2)
    {v : G} (hv : v ∉ center G) : Nat.card (center G) ≤ f := by
  have : Fact f.Prime := ⟨hf⟩
  have hGp : IsPGroup f G := fun g => ⟨1, by simpa using hexp g⟩
  let B : Subgroup G := closure (insert v (center G : Set G))
  have hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    refine r10h5_closure_comm fun a ha b hb => ?_
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact mem_center_iff.1 hb _
    · exact (mem_center_iff.1 ha _).symm
    · exact (mem_center_iff.1 ha _).symm
  have hvB : v ∈ B := subset_closure (Set.mem_insert _ _)
  have hZB : center G ≤ B := fun z hz => subset_closure (Set.mem_insert_of_mem _ hz)
  have hlt : Nat.card (center G) < Nat.card B :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hZB fun h => hv (h ▸ hvB))
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hGp.to_subgroup (center G))
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 (hGp.to_subgroup B)
  rw [ha, hb] at hlt
  have hab : a < b := (Nat.pow_lt_pow_iff_right hf.one_lt).1 hlt
  have hBcard := hE B hB
  rw [hb] at hBcard
  have hb2 : b ≤ 2 := (Nat.pow_le_pow_iff_right hf.one_lt).1 hBcard
  calc Nat.card (center G) = f ^ a := ha
    _ ≤ f ^ 1 := Nat.pow_le_pow_right hf.pos (by omega)
    _ = f := pow_one f

private theorem r10h5_commutator_central_mul {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ center G) (hw : w ∈ center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hzb : ∀ g : G, g * z = z * g := mem_center_iff.1 hz
  have hwb : ∀ g : G, g * w = w * g := mem_center_iff.1 hw
  have h1 : a * z * (b * w) = a * b * (z * w) := by
    rw [show a * z * (b * w) = a * (z * b) * w by group, ← hzb b]
    group
  have h2 : b * w * (a * z) = b * a * (z * w) := by
    rw [show b * w * (a * z) = b * (w * a) * z by group, ← hwb a, hwb z]
    group
  rw [commutatorElement_def, commutatorElement_def]
  have e : a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
      a * z * (b * w) * (b * w * (a * z))⁻¹ := by
    group
  rw [e, h1, h2]
  group

private def r10h5_quotAut {G : Type*} [Group G] (φ : MulAut G) : MulAut (G ⧸ center G) :=
  QuotientGroup.congr (center G) (center G) φ (map_center_eq φ)

private def r10h5_quotAct {G : Type*} [Group G] {R : Type*} [Group R] (ρ : R →* MulAut G) :
    R →* MulAut (G ⧸ center G) :=
  MonoidHom.mk' (fun r => r10h5_quotAut (ρ r)) fun a b =>
    MulEquiv.ext fun q => QuotientGroup.induction_on q fun g => by
      change (((ρ (a * b)) g : G) : G ⧸ center G) = (((ρ a) ((ρ b) g) : G) : G ⧸ center G)
      rw [map_mul]; rfl

private theorem r10h5_quot_mem {G : Type*} [Group G] (φ : MulAut G)
    (h : r10h5_quotAut φ = 1) (g : G) : g⁻¹ * φ g ∈ center G := by
  have h1 := congrArg (fun e : MulAut (G ⧸ center G) => e (g : G ⧸ center G)) h
  have h2 : ((φ g : G) : G ⧸ center G) = (g : G ⧸ center G) := h1
  exact QuotientGroup.eq.1 h2.symm

private theorem r10h5_aut_eq_one {G : Type*} [Group G] {f n : ℕ} (hcop : Nat.Coprime n f)
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

private theorem r10h5_aut_trivial {D : Type} [Group D] [Finite D] {f : ℕ} (hf : f.Prime)
    (hf3 : f ≠ 3) (hexp : ∀ g : D, g ^ f = 1) (hcl : ∀ a b : D, ⁅a, b⁆ ∈ center D)
    (hE : ∀ S : Subgroup D, (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) → Nat.card S ≤ f ^ 2)
    (hnc : ¬∀ a b : D, a * b = b * a) (φ : MulAut D) (hφ : φ ^ 3 = 1)
    (hQ : ∀ g : D, g⁻¹ * φ g ∈ center D) : φ = 1 := by
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨v, hv⟩ : ∃ v : D, v ∉ center D := by
    by_contra h
    exact hnc fun a b => mem_center_iff.1 (Classical.byContradiction fun hb => h ⟨b, hb⟩) a
  obtain ⟨a₀, b₀, hab⟩ : ∃ a b : D, a * b ≠ b * a :=
    Classical.byContradiction fun h => hnc fun a b =>
      Classical.byContradiction fun hab => h ⟨a, b, hab⟩
  have hz0 : ⁅a₀, b₀⁆ ∈ center D := hcl a₀ b₀
  have hz0ne : ⁅a₀, b₀⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hZle : Nat.card (center D) ≤ f := r10h5_card_center_le hf hexp hE hv
  have hord : orderOf ⁅a₀, b₀⁆ = f := orderOf_eq_prime (hexp ⁅a₀, b₀⁆) hz0ne
  have hZeq : Subgroup.zpowers ⁅a₀, b₀⁆ = center D := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz0) ?_
    rw [Nat.card_zpowers, hord]
    exact hZle
  have hφz0 : φ ⁅a₀, b₀⁆ = ⁅a₀, b₀⁆ := by
    obtain ⟨z₁, hz₁, h₁⟩ : ∃ z ∈ center D, φ a₀ = a₀ * z :=
      ⟨a₀⁻¹ * φ a₀, hQ a₀, (mul_inv_cancel_left a₀ (φ a₀)).symm⟩
    obtain ⟨z₂, hz₂, h₂⟩ : ∃ z ∈ center D, φ b₀ = b₀ * z :=
      ⟨b₀⁻¹ * φ b₀, hQ b₀, (mul_inv_cancel_left b₀ (φ b₀)).symm⟩
    rw [map_commutatorElement, h₁, h₂]
    exact r10h5_commutator_central_mul hz₁ hz₂
  have hZ : ∀ z ∈ center D, φ z = z := by
    intro z hz
    have hz' : z ∈ Subgroup.zpowers ⁅a₀, b₀⁆ := by
      rw [hZeq]
      exact hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz'
    rw [← hk, map_zpow, hφz0]
  have hcop : Nat.Coprime 3 f := (Nat.coprime_primes Nat.prime_three hf).2 (Ne.symm hf3)
  exact r10h5_aut_eq_one hcop (fun z _ => hexp z) φ hφ hZ hQ

theorem relIndex_le_three_of_action {D : Type} [Group D] [Finite D] {f : ℕ} (hf : f.Prime)
    (hf3 : f ≠ 3) (hexp : ∀ g : D, g ^ f = 1) (hcl : ∀ a b : D, ⁅a, b⁆ ∈ center D)
    (hE : ∀ S : Subgroup D, (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) → Nat.card S ≤ f ^ 2)
    {Y : Type} [Group Y] [Finite Y] (ρ : Y →* MulAut D)
    (hY : ∀ N : Subgroup Y, N.Normal → N.index ≠ 3)
    (E : Subgroup Y) (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    (E ⊓ ρ.ker).relIndex E ≤ 3 := by
  by_cases hcomm : ∀ a b : D, a * b = b * a
  ·
    have hcard : Nat.card D ≤ f ^ 2 := by
      have h := hE ⊤ fun a _ b _ => hcomm a b
      rwa [Subgroup.card_top] at h
    exact r10h5_relIndex_comm hf hf3 hcomm hexp hcard ρ hY E hE3 hEc
  ·
    have hQcomm : ∀ x y : D ⧸ center D, x * y = y * x := by
      intro x y
      refine QuotientGroup.induction_on x fun g => QuotientGroup.induction_on y fun h => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have e : (g * h)⁻¹ * (h * g) = ⁅h⁻¹, g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hcl h⁻¹ g⁻¹
    have hQexp : ∀ x : D ⧸ center D, x ^ f = 1 := fun x =>
      QuotientGroup.induction_on x fun g => by
        rw [← QuotientGroup.mk_pow, hexp g, QuotientGroup.mk_one]
    have hQcard : Nat.card (D ⧸ center D) ≤ f ^ 2 :=
      r10h5_card_quotient_center_le hf hexp hcl hE
    have hres := r10h5_relIndex_comm hf hf3 hQcomm hQexp hQcard (r10h5_quotAct ρ) hY E hE3 hEc
    have hmono : E ⊓ (r10h5_quotAct ρ).ker ≤ E ⊓ ρ.ker := by
      intro x hx
      obtain ⟨hxE, hxk⟩ := Subgroup.mem_inf.1 hx
      have hq : r10h5_quotAut (ρ x) = 1 := MonoidHom.mem_ker.1 hxk
      have h3 : ρ x ^ 3 = 1 := by rw [← map_pow, hE3 x hxE, map_one]
      exact Subgroup.mem_inf.2 ⟨hxE, MonoidHom.mem_ker.2
        (r10h5_aut_trivial hf hf3 hexp hcl hE hcomm (ρ x) h3 (r10h5_quot_mem (ρ x) hq))⟩
    exact (r10h5_relIndex_anti hmono).trans hres


private theorem r10h6_mem_centralizer_of_fixing {X : Type} [Group X] {f : ℕ} (hf : f.Prime)
    (hf3 : f ≠ 3) {F : Subgroup X} {D : Subgroup F}
    (hfix : IsPGroup f (fixingSubgroup (MulAut F) (D : Set F))) {r : X}
    (hrN : r ∈ normalizer (F : Set X)) (hr3 : ∃ m : ℕ, r ^ 3 ^ m = 1)
    (hrD : ∀ d ∈ D, (d : X) * r = r * (d : X)) : r ∈ centralizer (F : Set X) := by
  set φ : MulAut F := F.normalizerMonoidHom ⟨r, hrN⟩ with hφ
  have hφapp : ∀ g : F, ((φ g : F) : X) = r * g * r⁻¹ := fun _ => rfl
  have hmem : φ ∈ fixingSubgroup (MulAut F) (D : Set F) := by
    rw [mem_fixingSubgroup_iff (MulAut F)]
    intro d hd
    apply Subtype.ext
    change ((φ d : F) : X) = d
    rw [hφapp, ← hrD d hd, mul_inv_cancel_right]
  obtain ⟨n, hn⟩ := hfix ⟨φ, hmem⟩
  have hn' : φ ^ f ^ n = 1 := congrArg Subtype.val hn
  obtain ⟨m, hm⟩ := hr3
  have hm' : φ ^ 3 ^ m = 1 := by
    have h1 : (⟨r, hrN⟩ : normalizer (F : Set X)) ^ 3 ^ m = 1 :=
      Subtype.ext (by simpa using hm)
    rw [hφ, ← map_pow, h1, map_one]
  have hcop : Nat.Coprime (f ^ n) (3 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hf Nat.prime_three).2 hf3)
  have hφ1 : φ = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hn')
      (orderOf_dvd_of_pow_eq_one hm')
  rw [mem_centralizer_iff]
  intro x hx
  have h2 : ((φ ⟨x, hx⟩ : F) : X) = x := by rw [hφ1]; rfl
  rw [hφapp] at h2
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

private theorem r10h6_conj_mem_map {X : Type} [Group X] {F : Subgroup X}
    {D : Subgroup F} (hD : D.Characteristic) {r : X} (hrN : r ∈ normalizer (F : Set X)) {k : X}
    (hk : k ∈ D.map F.subtype) : r * k * r⁻¹ ∈ D.map F.subtype := by
  obtain ⟨d, hd, rfl⟩ := mem_map.1 hk
  exact mem_map.2 ⟨F.normalizerMonoidHom ⟨r, hrN⟩ d,
    characteristic_iff_le_comap.mp hD (F.normalizerMonoidHom ⟨r, hrN⟩) hd, rfl⟩

private theorem r10h6_comm_le_centralizer {X : Type} [Group X] {F : Subgroup X}
    {D : Subgroup F} (hDcomm : ⁅D, (⊤ : Subgroup F)⁆ ≤ D ⊓ centralizer (D : Set F)) :
    ⁅D.map F.subtype, D.map F.subtype⁆ ≤
      centralizer ((D.map F.subtype : Subgroup X) : Set X) := by
  rw [commutator_le]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨c, hc, rfl⟩
  have h1 : F.subtype ⁅a, b⁆ = ⁅F.subtype a, F.subtype b⁆ :=
    map_commutatorElement F.subtype a b
  have h2 : ⁅a, b⁆ ∈ centralizer (D : Set F) :=
    (hDcomm (commutator_mem_commutator ha (mem_top b))).2
  rw [← h1, ← map_mul, ← map_mul, mem_centralizer_iff.1 h2 c hc]

private theorem r10h6_comm_center {X : Type} [Group X] {D' : Subgroup X}
    (h : ⁅D', D'⁆ ≤ centralizer (D' : Set X)) (a b : D') : ⁅a, b⁆ ∈ center D' := by
  rw [mem_center_iff]
  intro g
  have h1 : ⁅(a : X), (b : X)⁆ ∈ centralizer (D' : Set X) :=
    h (commutator_mem_commutator a.2 b.2)
  exact Subtype.ext (mem_centralizer_iff.1 h1 g g.2)

private theorem r10h6_card_comm_le {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : f.Prime)
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

private def r10h6_conjAut {X : Type*} [Group X] (D : Subgroup X) (r : X)
    (hr : r ∈ normalizer (D : Set X)) : MulAut D where
  toFun d := ⟨r * d * r⁻¹, (mem_normalizer_iff.1 hr d).1 d.2⟩
  invFun d := ⟨r⁻¹ * d * r, by simpa using (mem_normalizer_iff.1 (inv_mem hr) d).1 d.2⟩
  left_inv d := Subtype.ext (by simp [mul_assoc])
  right_inv d := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private def r10h6_conjAct {X : Type*} [Group X] (D R : Subgroup X)
    (hRD : R ≤ normalizer (D : Set X)) : R →* MulAut D :=
  MonoidHom.mk' (fun r => r10h6_conjAut D r (hRD r.2)) fun a b =>
    MulEquiv.ext fun d => Subtype.ext <| by simp [r10h6_conjAut, mul_assoc]

private theorem r10h6_inter_eq {X : Type} [Group X] {f : ℕ} (hf : f.Prime) (hf3 : f ≠ 3)
    {F : Subgroup X} {D : Subgroup F}
    (hfix : IsPGroup f (fixingSubgroup (MulAut F) (D : Set F)))
    {Y : Subgroup X} (hYF : Y ≤ normalizer (F : Set X)) {E : Subgroup X} (hEY : E ≤ Y)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) {ρ : Y →* MulAut ↥(D.map F.subtype)}
    (hρ : ∀ (y : Y) (d : ↥(D.map F.subtype)),
      ((ρ y d : ↥(D.map F.subtype)) : X) = (y : X) * (d : X) * (y : X)⁻¹) :
    E ⊓ centralizer (F : Set X) = ((E.subgroupOf Y) ⊓ ρ.ker).map Y.subtype := by
  ext x
  constructor
  · rintro ⟨hxE, hxC⟩
    have hxY : x ∈ Y := hEY hxE
    refine mem_map.2 ⟨⟨x, hxY⟩, ⟨mem_subgroupOf.2 hxE, MonoidHom.mem_ker.2 ?_⟩, rfl⟩
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    have hdx : (d : X) * x = x * (d : X) := mem_centralizer_iff.1 hxC d (map_subtype_le D d.2)
    have hgoal : x * (d : X) * x⁻¹ = (d : X) := by
      rw [← hdx, mul_inv_cancel_right]
    exact (hρ ⟨x, hxY⟩ d).trans hgoal
  · rintro ⟨y, ⟨hyE, hyK⟩, rfl⟩
    have hyK' : ρ y = 1 := MonoidHom.mem_ker.1 hyK
    refine ⟨mem_subgroupOf.1 hyE, ?_⟩
    show (y : X) ∈ centralizer (F : Set X)
    refine r10h6_mem_centralizer_of_fixing hf hf3 hfix (hYF y.2) ⟨1, ?_⟩ ?_
    · simpa using hE3 _ (mem_subgroupOf.1 hyE)
    · intro d hd
      have hdD : F.subtype d ∈ D.map F.subtype := mem_map_of_mem F.subtype hd
      have h1 : ρ y ⟨F.subtype d, hdD⟩ = ⟨F.subtype d, hdD⟩ := by
        rw [hyK', MulAut.one_apply]
      have h2 : (y : X) * (d : X) * (y : X)⁻¹ = (d : X) :=
        (hρ y ⟨F.subtype d, hdD⟩).symm.trans (congrArg Subtype.val h1)
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm

theorem cyc_relIndex_le_three {X : Type} [Group X] [Finite X] {f : ℕ} (hf : f.Prime)
    (hf2 : f ≠ 2) (hf3 : f ≠ 3) {F : Subgroup X} (hF : IsPGroup f F)
    (hrk : CFSG.Open.pRank f F ≤ 2)
    {Y : Subgroup X} (hYF : Y ≤ normalizer (F : Set X))
    (hY : ∀ N : Subgroup X, N ≤ Y → (N.subgroupOf Y).Normal → (N.subgroupOf Y).index ≠ 3)
    {E : Subgroup X} (hEY : E ≤ Y) (hE : IsElemAbelian 3 E) :
    (E ⊓ centralizer (F : Set X)).relIndex E ≤ 3 := by
  by_cases hbot : F = ⊥
  · subst hbot
    have hc : E ⊓ centralizer ((⊥ : Subgroup X) : Set X) = E := by
      refine inf_eq_left.2 ?_
      intro x _
      rw [mem_centralizer_iff]
      intro h hh
      rw [Subgroup.mem_bot.1 hh, one_mul, mul_one]
    rw [hc, relIndex_self]
    norm_num
  · have : Fact f.Prime := ⟨hf⟩
    have : Nontrivial F := (nontrivial_iff_ne_bot F).2 hbot
    obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hf2 hF
    obtain ⟨hcomm, hexp3⟩ := hE
    have hD'F : D.map F.subtype ≤ F := map_subtype_le D
    have hPD : IsPGroup f (D.map F.subtype) := hF.to_le hD'F
    have hexpD : ∀ d ∈ D.map F.subtype, d ^ f = 1 := by
      intro d hd
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hd
      rw [subtype_apply, ← coe_pow, hDexp y hy, coe_one]
    have hrkD : CFSG.Open.pRank f (D.map F.subtype) ≤ 2 :=
      (CFSG.SectionRank.pRank_mono hf.one_lt hD'F).trans hrk
    have hYD : Y ≤ normalizer ((D.map F.subtype : Subgroup X) : Set X) := by
      rw [le_normalizer_iff]
      intro r hr k hk
      exact r10h6_conj_mem_map hDchar (hYF hr) hk
    have hcl : ∀ a b : ↥(D.map F.subtype), ⁅a, b⁆ ∈ center ↥(D.map F.subtype) :=
      r10h6_comm_center (r10h6_comm_le_centralizer hDcomm)
    have hexpS : ∀ g : ↥(D.map F.subtype), g ^ f = 1 := fun g =>
      Subtype.ext (hexpD g g.2)
    have hES : ∀ S : Subgroup ↥(D.map F.subtype), (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) →
        Nat.card S ≤ f ^ 2 := fun S hS => r10h6_card_comm_le hf hPD hexpD hrkD S hS
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Y →* MulAut ↥(D.map F.subtype),
        ∀ (y : Y) (d : ↥(D.map F.subtype)),
          ((ρ y d : ↥(D.map F.subtype)) : X) = (y : X) * (d : X) * (y : X)⁻¹ :=
      ⟨r10h6_conjAct (D.map F.subtype) Y hYD, fun _ _ => rfl⟩
    have hY' : ∀ N : Subgroup Y, N.Normal → N.index ≠ 3 := by
      intro N hN
      have hNe : (N.map Y.subtype).subgroupOf Y = N :=
        Subgroup.comap_map_eq_self_of_injective (f := Y.subtype) (Subgroup.subtype_injective Y) N
      have hN' : ((N.map Y.subtype).subgroupOf Y).Normal := by
        rw [hNe]
        exact hN
      have h3 := hY (N.map Y.subtype) (map_subtype_le N) hN'
      rw [hNe] at h3
      exact h3
    have hEcX : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      have h := hcomm.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩
      exact congrArg Subtype.val h
    have hEc : ∀ a ∈ E.subgroupOf Y, ∀ b ∈ E.subgroupOf Y, a * b = b * a := fun a ha b hb =>
      Subtype.ext (hEcX (a : X) (mem_subgroupOf.1 ha) (b : X) (mem_subgroupOf.1 hb))
    have hE3' : ∀ e ∈ E.subgroupOf Y, e ^ 3 = 1 := fun e he =>
      Subtype.ext (hexp3 _ (mem_subgroupOf.1 he))
    have habs := relIndex_le_three_of_action (D := ↥(D.map F.subtype)) (Y := ↥Y) hf hf3
      hexpS hcl hES ρ hY' (E.subgroupOf Y) hE3' hEc
    have hkey := r10h6_inter_eq hf hf3 hDfix hYF hEY hexp3 hρ
    have hEE : (E.subgroupOf Y).map Y.subtype = E := map_subgroupOf_eq_of_le hEY
    have h1 := relIndex_map_map_of_injective (f := Y.subtype) (E.subgroupOf Y ⊓ ρ.ker)
      (E.subgroupOf Y) (Subgroup.subtype_injective Y)
    rw [hEE, ← hkey] at h1
    rw [h1]
    exact habs

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
