module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

theorem ne_bot_of_isQuasisimple {G : Type*} [Group G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) : L ≠ ⊥ := by
  intro h
  have hsub : Subsingleton ↥L := ⟨fun x y => Subtype.ext
    ((Subgroup.mem_bot.1 (h ▸ x.2)).trans (Subgroup.mem_bot.1 (h ▸ y.2)).symm)⟩
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (congrArg QuotientGroup.mk (Subsingleton.elim _ _))

section Irr

variable {W : Type} [CommGroup W]

theorem fixV_eq_bot_of_irr {L : Subgroup (MulAut W)} (hirr : IsIrrOn L) (hL : L ≠ ⊥) :
    fixV L = ⊥ := by
  rcases hirr.2 (fixV L) (fun g hg u hu => by rw [hu g hg]; exact hu) with h | h
  · exact h
  · exfalso
    apply hL
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext w
    have : w ∈ fixV L := by rw [h]; trivial
    exact this g hg

theorem eq_one_of_commutes_of_sq_eq_one (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) {c : MulAut W} (hc : ∀ l ∈ L, l * c = c * l) (hc2 : c * c = 1) :
    c = 1 := by
  have hinv : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers c), g u ∈ fixV (Subgroup.zpowers c) := by
    intro g hg u hu
    rw [mem_fixV_zpowers] at hu ⊢
    have := congrArg (fun z : MulAut W => z u) (hc g hg)
    simp only [MulAut.mul_apply] at this
    rw [← this, hu]
  rcases hirr.2 _ hinv with h | h
  · ext w
    have hmem : c w * w⁻¹ ∈ fixV (Subgroup.zpowers c) := by
      rw [mem_fixV_zpowers, map_mul, map_inv]
      have h1 : c (c w) = w := by
        have := congrArg (fun z : MulAut W => z w) hc2
        simpa only [MulAut.mul_apply, MulAut.one_apply] using this
      rw [h1]
      have h2 : (c w)⁻¹ = c w := inv_eq_of_mul_eq_one_right (hW (c w))
      have h3 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW w)
      rw [h2, h3, mul_comm]
    rw [h, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.1 hmem
  · ext w
    have : w ∈ fixV (Subgroup.zpowers c) := by rw [h]; trivial
    exact mem_fixV_zpowers.1 this

theorem odd_orderOf_of_commutes [Finite W] (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) {c : MulAut W} (hc : ∀ l ∈ L, l * c = c * l) : Odd (orderOf c) := by
  rcases Nat.even_or_odd (orderOf c) with ⟨k, hk⟩ | h
  · exfalso
    have hpos : 0 < orderOf c := orderOf_pos c
    have hk0 : 0 < k := by omega
    have hne : c ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0.ne' (by omega)
    apply hne
    refine eq_one_of_commutes_of_sq_eq_one hW hirr (fun l hl => ?_) ?_
    · exact (Commute.pow_right (hc l hl) k)
    · rw [← pow_add, ← two_mul]
      have : orderOf c = 2 * k := by omega
      rw [← this]
      exact pow_orderOf_eq_one c
  · exact h

theorem centralizer_inf_le [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E) :
    (L ⊔ E) ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≤ L := by
  intro c hc
  obtain ⟨hcH, hcC⟩ := hc
  have hcomm : ∀ l ∈ L, l * c = c * l := by
    intro l hl
    exact Subgroup.mem_centralizer_iff.1 hcC l hl
  have hodd := odd_orderOf_of_commutes hW hirr hcomm
  have hmem : c ∈ ((L : Set (MulAut W)) * (E : Set (MulAut W))) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L E hE]
    exact hcH
  obtain ⟨l, hl, e, he, rfl⟩ := hmem
  have he2 : e * e = 1 := by
    have := hEel.2 e he
    rwa [sq] at this
  have hl' : e * l * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hE he) l).1 hl
  have hsq : (l * e) * (l * e) ∈ L := by
    have : (l * e) * (l * e) = l * (e * l * e⁻¹) := by
      have : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
      rw [this]
      calc l * e * (l * e) = l * (e * l * e) := by group
        _ = l * (e * l * e) := rfl
    rw [this]
    exact L.mul_mem hl hl'
  obtain ⟨m, hm⟩ := hodd
  have hpow : (l * e) ^ (2 * m + 1) = 1 := by
    rw [← hm]
    exact pow_orderOf_eq_one _
  have : l * e = ((l * e) * (l * e)) ^ (m + 1) := by
    rw [← sq, ← pow_mul]
    have h1 : (l * e) ^ (2 * (m + 1)) = (l * e) ^ (2 * m + 1) * (l * e) := by
      rw [← pow_succ]
      congr 1
    rw [h1, hpow, one_mul]
  show l * e ∈ L
  rw [this]
  exact L.pow_mem hsq _

end Irr

section Lift

variable {W : Type} [CommGroup W]

@[expose] def conjAut (L : Subgroup (MulAut W)) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) : ↥L ≃* ↥L where
  toFun x := ⟨b * x * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb x).1 x.2⟩
  invFun x := ⟨b⁻¹ * x * b, by
    have hb' : b⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hb
    have := (Subgroup.mem_normalizer_iff.1 hb' x).1 x.2
    simpa using this⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem coe_conjAut (L : Subgroup (MulAut W)) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (x : ↥L) :
    ((conjAut L hb x : ↥L) : MulAut W) = b * x * b⁻¹ := rfl

theorem le_of_autInner [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) : E ≤ L := by
  intro b hbE
  have hbN : b ∈ Subgroup.normalizer (L : Set (MulAut W)) := hE hbE
  let ψ : CQ L ≃* CQ L :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjAut L hbN)
      (Subgroup.map_center_eq (conjAut L hbN))
  obtain ⟨s, hs⟩ := hAut (e.symm.trans (ψ.trans e))
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center ↥L) (e.symm s)
  have hψ : ∀ q : CQ L, ψ q = QuotientGroup.mk l * q * (QuotientGroup.mk l)⁻¹ := by
    intro q
    have h1 := hs (e q)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    have h2 : e (ψ q) = e (QuotientGroup.mk l * q * (QuotientGroup.mk l)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hl, h1]
      simp
    exact e.injective h2
  set c : MulAut W := (l : MulAut W)⁻¹ * b with hc
  have hlN : (l : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.le_normalizer l.2
  have hcN : c ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normalizer (L : Set (MulAut W))).mul_mem
      ((Subgroup.normalizer (L : Set (MulAut W))).inv_mem hlN) hbN
  have hθ : ∀ x : ↥L, conjAut L hcN x = l⁻¹ * conjAut L hbN x * l := by
    intro x
    apply Subtype.ext
    show c * (x : MulAut W) * c⁻¹ = ((l : MulAut W)⁻¹) * (b * x * b⁻¹) * (l : MulAut W)
    rw [hc]
    group
  have hcentral : ∀ x : ↥L, x⁻¹ * conjAut L hcN x ∈ Subgroup.center ↥L := by
    intro x
    rw [← QuotientGroup.eq, hθ]
    have h3 : (QuotientGroup.mk (conjAut L hbN x) : CQ L) = ψ (QuotientGroup.mk x) := rfl
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h3, hψ]
    group
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    MonoidHom.mk' (fun x => ⟨x⁻¹ * conjAut L hcN x, hcentral x⟩) (by
      intro x y
      apply Subtype.ext
      have hz := Subgroup.mem_center_iff.1 (hcentral x) y⁻¹
      show (x * y)⁻¹ * conjAut L hcN (x * y) = (x⁻¹ * conjAut L hcN x) * (y⁻¹ * conjAut L hcN y)
      calc (x * y)⁻¹ * conjAut L hcN (x * y) = y⁻¹ * (x⁻¹ * conjAut L hcN x) * conjAut L hcN y := by
            rw [map_mul]; group
        _ = (x⁻¹ * conjAut L hcN x) * y⁻¹ * conjAut L hcN y := by rw [hz]
        _ = (x⁻¹ * conjAut L hcN x) * (y⁻¹ * conjAut L hcN y) := by group)
  have hfker : (⊤ : Subgroup ↥L) ≤ f.ker := by
    rw [← hperf.commutator_eq_top, commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (f g₁).2 (f g₂)).symm)
  have hcomm : ∀ x ∈ L, x * c = c * x := by
    intro x hx
    have h1 := f.mem_ker.1 (hfker (Subgroup.mem_top ⟨x, hx⟩))
    have h2 := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : MulAut W)) h1
    simp only [Subgroup.coe_one] at h2
    have h3 : (x : MulAut W)⁻¹ * (c * x * c⁻¹) = 1 := h2
    have h5 : c * x * c⁻¹ = x := (inv_mul_eq_one.1 h3).symm
    calc x * c = (c * x * c⁻¹) * c := by rw [h5]
      _ = c * x := by group
  have hcC : c ∈ Subgroup.centralizer (L : Set (MulAut W)) := Subgroup.mem_centralizer_iff.2 hcomm
  have hcH : c ∈ L ⊔ E := Subgroup.mul_mem_sup (L.inv_mem l.2) hbE
  have hcL : c ∈ L := centralizer_inf_le hW hirr hE hEel ⟨hcH, hcC⟩
  have hbc : b = (l : MulAut W) * c := by rw [hc]; group
  rw [hbc]
  exact L.mul_mem l.2 hcL

theorem card_le_two_pow_of_le [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) (hEL : E ≤ L) (hEel : IsElemAbelian2 E) {S : Type} [Group S]
    (e : CQ L ≃* S) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) : Nat.card E ≤ 2 ^ r := by
  let ι : ↥E →* S :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hEL))
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (QuotientGroup.mk (Subgroup.inclusion hEL x) : CQ L) = 1 := by
      apply e.injective
      simpa [ι] using hx
    rw [QuotientGroup.eq_one_iff] at h1
    have hcomm : ∀ l ∈ L, l * (x : MulAut W) = (x : MulAut W) * l := fun l hl => by
      have := Subgroup.mem_center_iff.1 h1 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hodd := odd_orderOf_of_commutes hW hirr hcomm
    have hx2 : (x : MulAut W) ^ 2 = 1 := hEel.2 x x.2
    have hdvd : orderOf (x : MulAut W) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have h1' : orderOf (x : MulAut W) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact Subtype.ext (orderOf_eq_one_iff.1 h1')
  have hB : Nat.card ι.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hB]
  refine hr ι.range ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEel.1 a a.2 b b.2)
  · rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 a a.2)
    rw [this, map_one]

end Lift


end CFSG.QuasithinUnique.Setup.X1
