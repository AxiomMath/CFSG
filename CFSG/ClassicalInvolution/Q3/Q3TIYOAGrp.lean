module

public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Stable

variable {Y : Type} [Group Y]

theorem commutatorElement_mul_central_left {x w c : Y} (hc : ∀ g : Y, g * c = c * g) :
    ⁅x * c, w⁆ = ⁅x, w⁆ := by
  have h1 : c * w * c⁻¹ = w := by
    calc c * w * c⁻¹ = w * c * c⁻¹ := by rw [← hc w]
      _ = w := by group
  calc ⁅x * c, w⁆ = x * (c * w * c⁻¹) * x⁻¹ * w⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅x, w⁆ := by rw [h1, commutatorElement_def]

theorem commutatorElement_mul_central_right {x y c : Y} (hc : ∀ g : Y, g * c = c * g) :
    ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have h1 : c * x⁻¹ * c⁻¹ = x⁻¹ := by
    calc c * x⁻¹ * c⁻¹ = x⁻¹ * c * c⁻¹ := by rw [← hc x⁻¹]
      _ = x⁻¹ := by group
  calc ⁅x, y * c⁆ = x * y * (c * x⁻¹ * c⁻¹) * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ := by rw [h1, commutatorElement_def]

theorem commutator_centralizer_le {Q A : Subgroup Y} [Q.Normal]
    (hQA : ∀ q ∈ Q, ∀ a ∈ A, q * a = a * q) (hgen : Q ⊔ A = ⊤) :
    ⁅Subgroup.centralizer (A : Set Y), Subgroup.centralizer (A : Set Y)⁆ ≤ Q := by
  set C : Subgroup Y := Subgroup.centralizer (A : Set Y) with hC
  have hQC : Q ≤ C := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => (hQA q hq a ha).symm
  have hdec : ∀ x ∈ C, ∃ q ∈ Q, ∃ a : Y, q * a = x ∧ ∀ g : Y, g * a = a * g := by
    intro x hx
    have hxs : x ∈ Q ⊔ A := hgen ▸ Subgroup.mem_top x
    obtain ⟨q, hq, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxs
    refine ⟨q, hq, a, rfl, ?_⟩
    have haC : a ∈ C := by
      have := C.mul_mem (C.inv_mem (hQC hq)) hx
      simpa using this
    have hmem : (⊤ : Subgroup Y) ≤ Subgroup.centralizer ({a} : Set Y) := by
      rw [← hgen]
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hQA g hg a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp haC g hg)
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hmem (Subgroup.mem_top g))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨q₁, hq₁, a₁, rfl, hc₁⟩ := hdec x hx
  obtain ⟨q₂, hq₂, a₂, rfl, hc₂⟩ := hdec y hy
  rw [commutatorElement_mul_central_left hc₁, commutatorElement_mul_central_right hc₂,
    commutatorElement_def]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem hq₁ hq₂) (Q.inv_mem hq₁)) (Q.inv_mem hq₂)

theorem apply_mem_of_perfect_of_fixed {Q A : Subgroup Y} [Q.Normal]
    (hQA : ∀ q ∈ Q, ∀ a ∈ A, q * a = a * q) (hgen : Q ⊔ A = ⊤) (hperf : ⁅Q, Q⁆ = Q)
    (α : MulAut Y) (hfix : ∀ a ∈ A, α a = a) : ∀ q ∈ Q, α q ∈ Q := by
  set C : Subgroup Y := Subgroup.centralizer (A : Set Y) with hC
  have hQC : Q ≤ C := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => (hQA q hq a ha).symm
  have hαC : ∀ y ∈ C, α y ∈ C := by
    intro y hy
    rw [hC, Subgroup.mem_centralizer_iff]
    intro a ha
    have h3 : a * y = y * a := Subgroup.mem_centralizer_iff.mp hy a ha
    calc a * α y = α a * α y := by rw [hfix a ha]
      _ = α (a * y) := (map_mul α a y).symm
      _ = α (y * a) := by rw [h3]
      _ = α y * α a := map_mul α y a
      _ = α y * a := by rw [hfix a ha]
  have hcc := commutator_centralizer_le hQA hgen
  intro q hq
  have h1 : q ∈ ⁅Q, Q⁆ := by rw [hperf]; exact hq
  have h2 : α q ∈ ⁅Q.map (α : Y →* Y), Q.map (α : Y →* Y)⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem (α : Y →* Y) h1
  have h3 : Q.map (α : Y →* Y) ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact hαC x (hQC hx)
  exact hcc (Subgroup.commutator_mono h3 h3 h2)

theorem commutator_subgroup_eq_self {Q : Subgroup Y} (h : commutator Q = ⊤) : ⁅Q, Q⁆ = Q := by
  have h1 : (⊤ : Subgroup Q).map Q.subtype = Q := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  calc ⁅Q, Q⁆ = ⁅(⊤ : Subgroup Q).map Q.subtype, (⊤ : Subgroup Q).map Q.subtype⁆ := by rw [h1]
    _ = (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆).map Q.subtype := (Subgroup.map_commutator _ _ _).symm
    _ = (⊤ : Subgroup Q).map Q.subtype := by rw [← commutator_def, h]
    _ = Q := h1

end Stable

section Restrict

variable {Y : Type} [Group Y]

@[expose] def restrictHom (Q : Subgroup Y) (α : MulAut Y) (h : ∀ q ∈ Q, α q ∈ Q) : Q →* Q where
  toFun q := ⟨α (q : Y), h q q.2⟩
  map_one' := Subtype.ext (map_one α)
  map_mul' _ _ := Subtype.ext (map_mul α _ _)

theorem restrictHom_injective (Q : Subgroup Y) (α : MulAut Y) (h : ∀ q ∈ Q, α q ∈ Q) :
    Function.Injective (restrictHom Q α h) := fun _ _ hab =>
  Subtype.ext (α.injective (congrArg Subtype.val hab))

@[expose] noncomputable def restrictAut [Finite Y] (Q : Subgroup Y) (α : MulAut Y)
    (h : ∀ q ∈ Q, α q ∈ Q) : MulAut Q :=
  MulEquiv.ofBijective (restrictHom Q α h)
    ⟨restrictHom_injective Q α h, Finite.surjective_of_injective (restrictHom_injective Q α h)⟩

theorem restrictAut_apply [Finite Y] (Q : Subgroup Y) (α : MulAut Y) (h : ∀ q ∈ Q, α q ∈ Q)
    (q : Q) : ((restrictAut Q α h q : Q) : Y) = α (q : Y) := rfl

theorem restrictAut_pow_apply [Finite Y] (Q : Subgroup Y) (α : MulAut Y) (h : ∀ q ∈ Q, α q ∈ Q)
    (n : ℕ) (q : Q) : (((restrictAut Q α h ^ n) q : Q) : Y) = (α ^ n) (q : Y) := by
  induction n generalizing q with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
    exact ih (restrictAut Q α h q)

theorem restrictAut_pow_eq_one [Finite Y] (Q : Subgroup Y) (α : MulAut Y)
    (h : ∀ q ∈ Q, α q ∈ Q) {n : ℕ} (hn : α ^ n = 1) : restrictAut Q α h ^ n = 1 := by
  ext q
  rw [restrictAut_pow_apply, hn]
  rfl

end Restrict

section CenterQuot

variable {Q : Type} [Group Q]

theorem apply_mem_center_iff (β : MulAut Q) (x : Q) :
    β x ∈ Subgroup.center Q ↔ x ∈ Subgroup.center Q := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply β.injective
    rw [map_mul, map_mul]
    exact h (β g)
  · intro h g
    obtain ⟨g', rfl⟩ := β.surjective g
    rw [← map_mul, ← map_mul, h g']

theorem map_center_eq (β : MulAut Q) :
    (Subgroup.center Q).map (β : Q →* Q) = Subgroup.center Q := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (apply_mem_center_iff β y).mpr hy
  · intro hx
    obtain ⟨y, rfl⟩ := β.surjective x
    exact ⟨y, (apply_mem_center_iff β y).mp hx, rfl⟩

@[expose] noncomputable def centerQuotAut (β : MulAut Q) : MulAut (Q ⧸ Subgroup.center Q) :=
  QuotientGroup.congr (Subgroup.center Q) (Subgroup.center Q) β (map_center_eq β)

theorem centerQuotAut_mk (β : MulAut Q) (q : Q) :
    centerQuotAut β (QuotientGroup.mk' (Subgroup.center Q) q) =
      QuotientGroup.mk' (Subgroup.center Q) (β q) := rfl

theorem centerQuotAut_pow_mk (β : MulAut Q) (n : ℕ) (q : Q) :
    (centerQuotAut β ^ n) (QuotientGroup.mk' (Subgroup.center Q) q) =
      QuotientGroup.mk' (Subgroup.center Q) ((β ^ n) q) := by
  induction n generalizing q with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, centerQuotAut_mk]
    exact ih (β q)

theorem centerQuotAut_pow_eq_one (β : MulAut Q) {n : ℕ} (hn : β ^ n = 1) :
    centerQuotAut β ^ n = 1 := by
  ext x
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
  have := centerQuotAut_pow_mk β n q
  rw [hn] at this
  exact this

end CenterQuot

section Cocycle

variable {Q : Type} [Group Q]

theorem odd_natCard_of_forall_odd_orderOf {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : ∀ x ∈ H, Odd (orderOf x)) : Odd (Nat.card H) := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne))
  have h1 := h x x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact absurd h1 (by decide)

@[expose] def cocycle (β : MulAut Q) (c : Q) : Q := c⁻¹ * β c

theorem cocycle_mul (β : MulAut Q) (c d : Q) :
    cocycle β (c * d) = (d⁻¹ * cocycle β c * d) * cocycle β d := by
  simp only [cocycle, map_mul]
  group

theorem central_of_mk_commute {c z : Q}
    (h : QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c) :
    z⁻¹ * (c * z * c⁻¹) ∈ Subgroup.center Q := by
  rw [← QuotientGroup.eq]
  have h1 : (QuotientGroup.mk (c * z * c⁻¹) : Q ⧸ Subgroup.center Q) =
      QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z *
        (QuotientGroup.mk' (Subgroup.center Q) c)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [h1, h, mul_inv_cancel_right]
  rfl

theorem cocycle_facts (β : MulAut Q) {m : ℕ} (hβm : β ^ m = 1) {z : Q}
    (hfix : ∀ c : Q, c * z = z * c → β c = c) {c : Q}
    (hc : QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c) :
    cocycle β c * z = z * cocycle β c ∧
      (∀ i : Q, i * z = z * i → cocycle β c * i = i * cocycle β c) ∧ cocycle β c ^ m = 1 := by
  have hζc := central_of_mk_commute hc
  set ζ : Q := z⁻¹ * (c * z * c⁻¹) with hζdef
  have hζ : c * z * c⁻¹ = z * ζ := by rw [hζdef]; group
  have hζcomm : ∀ g : Q, g * ζ = ζ * g := Subgroup.mem_center_iff.mp hζc
  have hζinv : ∀ g : Q, g * ζ⁻¹ = ζ⁻¹ * g :=
    Subgroup.mem_center_iff.mp ((Subgroup.center Q).inv_mem hζc)
  have hβz : β z = z := hfix z rfl
  have hβζ : β ζ = ζ := hfix ζ (hζcomm z).symm
  have h1 : β c * z * (β c)⁻¹ = c * z * c⁻¹ := by
    calc β c * z * (β c)⁻¹ = β (c * z * c⁻¹) := by rw [map_mul, map_mul, map_inv, hβz]
      _ = β (z * ζ) := by rw [hζ]
      _ = z * ζ := by rw [map_mul, hβz, hβζ]
      _ = c * z * c⁻¹ := hζ.symm
  have h2 : β c * z = c * z * c⁻¹ * β c := by
    calc β c * z = (β c * z * (β c)⁻¹) * β c := by group
      _ = c * z * c⁻¹ * β c := by rw [h1]
  have hez : cocycle β c * z = z * cocycle β c := by
    show c⁻¹ * β c * z = z * (c⁻¹ * β c)
    calc c⁻¹ * β c * z = c⁻¹ * (β c * z) := by rw [mul_assoc]
      _ = c⁻¹ * (c * z * c⁻¹ * β c) := by rw [h2]
      _ = z * (c⁻¹ * β c) := by group
  have hβe : β (cocycle β c) = cocycle β c := hfix _ hez
  refine ⟨hez, ?_, ?_⟩
  · intro i hi
    have hcζ : c⁻¹ * ζ * c = ζ := by
      calc c⁻¹ * ζ * c = ζ * c⁻¹ * c := by rw [hζcomm c⁻¹]
        _ = ζ := by group
    have h5 : (c⁻¹ * z * c) * ζ = z := by
      calc (c⁻¹ * z * c) * ζ = (c⁻¹ * z * c) * (c⁻¹ * ζ * c) := by rw [hcζ]
        _ = c⁻¹ * (z * ζ) * c := by group
        _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hζ]
        _ = z := by group
    have hw : c⁻¹ * z * c = z * ζ⁻¹ := by
      calc c⁻¹ * z * c = (c⁻¹ * z * c * ζ) * ζ⁻¹ := by group
        _ = z * ζ⁻¹ := by rw [h5]
    have hiw : i * (c⁻¹ * z * c) = (c⁻¹ * z * c) * i := by
      rw [hw]
      calc i * (z * ζ⁻¹) = (i * z) * ζ⁻¹ := by rw [mul_assoc]
        _ = (z * i) * ζ⁻¹ := by rw [hi]
        _ = z * (i * ζ⁻¹) := by rw [mul_assoc]
        _ = z * (ζ⁻¹ * i) := by rw [hζinv i]
        _ = (z * ζ⁻¹) * i := by rw [mul_assoc]
    have hj : (c * i * c⁻¹) * z = z * (c * i * c⁻¹) := by
      calc (c * i * c⁻¹) * z = c * (i * (c⁻¹ * z * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * z * c) * i) * c⁻¹ := by rw [hiw]
        _ = z * (c * i * c⁻¹) := by group
    have hβj : β (c * i * c⁻¹) = c * i * c⁻¹ := hfix _ hj
    have hβi : β i = i := hfix i hi
    have h6 : β c * i * (β c)⁻¹ = c * i * c⁻¹ := by
      calc β c * i * (β c)⁻¹ = β (c * i * c⁻¹) := by rw [map_mul, map_mul, map_inv, hβi]
        _ = c * i * c⁻¹ := hβj
    have h7 : β c * i = c * i * c⁻¹ * β c := by
      calc β c * i = (β c * i * (β c)⁻¹) * β c := by group
        _ = c * i * c⁻¹ * β c := by rw [h6]
    show c⁻¹ * β c * i = i * (c⁻¹ * β c)
    calc c⁻¹ * β c * i = c⁻¹ * (β c * i) := by rw [mul_assoc]
      _ = c⁻¹ * (c * i * c⁻¹ * β c) := by rw [h7]
      _ = i * (c⁻¹ * β c) := by group
  · have hβc : β c = c * cocycle β c := by simp only [cocycle]; group
    have hpow : ∀ n : ℕ, (β ^ n) c = c * cocycle β c ^ n := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, mul_one]; rfl
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hβe, hβc, pow_succ', mul_assoc]
    have h8 := hpow m
    rw [hβm, MulAut.one_apply] at h8
    exact (mul_eq_left.mp h8.symm)

theorem cocycle_mem_oddCoreIn [Finite Q] (β : MulAut Q) {m : ℕ} (hm : Odd m) (hβm : β ^ m = 1)
    {z : Q} (hfix : ∀ c : Q, c * z = z * c → β c = c) (c : Q)
    (hc : QuotientGroup.mk' (Subgroup.center Q) c ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (Subgroup.center Q) z} : Set (Q ⧸ Subgroup.center Q))) :
    (QuotientGroup.mk' (Subgroup.center Q) c)⁻¹ *
        centerQuotAut β (QuotientGroup.mk' (Subgroup.center Q) c) ∈
      oddCoreIn (Subgroup.centralizer
        ({QuotientGroup.mk' (Subgroup.center Q) z} : Set (Q ⧸ Subgroup.center Q))) := by
  set π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q) with hπ
  set M : Subgroup (Q ⧸ Subgroup.center Q) :=
    Subgroup.centralizer ({π z} : Set (Q ⧸ Subgroup.center Q)) with hM
  set E : Set (Q ⧸ Subgroup.center Q) := {x | ∃ d : Q, π d ∈ M ∧ x = π (cocycle β d)} with hE
  set B : Subgroup (Q ⧸ Subgroup.center Q) := Subgroup.closure E with hB
  have hfacts : ∀ d : Q, π d ∈ M → cocycle β d * z = z * cocycle β d ∧
      (∀ i : Q, i * z = z * i → cocycle β d * i = i * cocycle β d) ∧ cocycle β d ^ m = 1 :=
    fun d hd => cocycle_facts β hβm hfix (Subgroup.mem_centralizer_singleton_iff.mp hd)
  have hgen : ∀ d : Q, π d ∈ M → π (cocycle β d) ∈ B := fun d hd =>
    Subgroup.subset_closure ⟨d, hd, rfl⟩
  have hEM : E ⊆ (M : Set (Q ⧸ Subgroup.center Q)) := by
    rintro x ⟨d, hd, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [← map_mul, ← map_mul, (hfacts d hd).1])
  have hBM : B ≤ M := (Subgroup.closure_le M).mpr hEM
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, Commute x y := by
    rintro _ ⟨d₁, hd₁, rfl⟩ _ ⟨d₂, hd₂, rfl⟩
    have h1 : cocycle β d₁ * cocycle β d₂ = cocycle β d₂ * cocycle β d₁ :=
      (hfacts d₁ hd₁).2.1 _ (hfacts d₂ hd₂).1
    show π (cocycle β d₁) * π (cocycle β d₂) = π (cocycle β d₂) * π (cocycle β d₁)
    rw [← map_mul, ← map_mul, h1]
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => Commute x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hx hy
    · intro x y hx hy
      exact hEcomm x hx y hy
    · intro x _
      exact Commute.one_left x
    · intro x _
      exact Commute.one_right x
    · intro x y z _ _ _ hxz hyz
      exact hxz.mul_left hyz
    · intro y z x _ _ _ hxy hxz
      exact hxy.mul_right hxz
    · intro x y _ _ h
      exact h.inv_left
    · intro x y _ _ h
      exact h.inv_right
  have hBpow : ∀ x ∈ B, x ^ m = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ m = 1) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow, (hfacts d hd).2.2, map_one]
    · exact one_pow m
    · intro x y hx hy hxm hym
      rw [(hBcomm x hx y hy).mul_pow, hxm, hym, one_mul]
    · intro x _ hxm
      rw [inv_pow, hxm, inv_one]
  have hBodd : Odd (Nat.card B) :=
    odd_natCard_of_forall_odd_orderOf B fun x hx =>
      Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one (hBpow x hx))
  have hconj : ∀ d : Q, π d ∈ M → ∀ x ∈ B, π d * x * (π d)⁻¹ ∈ B := by
    intro d hd x hx
    refine Subgroup.closure_induction (p := fun x _ => π d * x * (π d)⁻¹ ∈ B) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨c', hc', rfl⟩
      have hd' : π d⁻¹ ∈ M := by rw [map_inv]; exact M.inv_mem hd
      have hcd : π (c' * d⁻¹) ∈ M := by
        rw [map_mul, map_inv]; exact M.mul_mem hc' (M.inv_mem hd)
      have key : d * cocycle β c' * d⁻¹ = cocycle β (c' * d⁻¹) * (cocycle β d⁻¹)⁻¹ := by
        simp only [cocycle, map_mul, map_inv]; group
      have h1 : π d * π (cocycle β c') * (π d)⁻¹ =
          π (cocycle β (c' * d⁻¹)) * (π (cocycle β d⁻¹))⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, key, map_mul, map_inv]
      rw [h1]
      exact B.mul_mem (hgen _ hcd) (B.inv_mem (hgen _ hd'))
    · simp
    · intro x y _ _ hx hy
      have : π d * (x * y) * (π d)⁻¹ = (π d * x * (π d)⁻¹) * (π d * y * (π d)⁻¹) := by group
      rw [this]
      exact B.mul_mem hx hy
    · intro x _ hx
      have : π d * x⁻¹ * (π d)⁻¹ = (π d * x * (π d)⁻¹)⁻¹ := by group
      rw [this]
      exact B.inv_mem hx
  have hnorm : M ≤ Subgroup.normalizer (B : Set (Q ⧸ Subgroup.center Q)) := by
    intro d' hd'
    obtain ⟨d, hdd⟩ := QuotientGroup.mk_surjective d'
    have hdπ : d' = π d := hdd.symm
    subst hdπ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj d hd' x hx
    · intro hx
      have hd'' : π d⁻¹ ∈ M := by rw [map_inv]; exact M.inv_mem hd'
      have h1 := hconj d⁻¹ hd'' _ hx
      have e : π d⁻¹ * (π d * x * (π d)⁻¹) * (π d⁻¹)⁻¹ = x := by rw [map_inv]; group
      rw [e] at h1
      exact h1
  have hBle : B ≤ oddCoreIn M := le_oddCoreIn_of_normalizes hBM hnorm hBodd
  apply hBle
  have e : (π c)⁻¹ * centerQuotAut β (π c) = π (cocycle β c) := by
    rw [centerQuotAut_mk, ← map_inv, ← map_mul]
    rfl
  rw [e]
  exact hgen c hc

end Cocycle

theorem eq_one_of_perfect_of_central_ratio {Q : Type} [Group Q] (hperf : commutator Q = ⊤)
    (β : MulAut Q) (h : ∀ q : Q, q⁻¹ * β q ∈ Subgroup.center Q) : β = 1 := by
  have hc : ∀ a b : Q, β ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    have ha : β a = a * (a⁻¹ * β a) := by group
    have hb : β b = b * (b⁻¹ * β b) := by group
    rw [map_commutatorElement β a b, ha, hb,
      commutatorElement_mul_central_right (Subgroup.mem_center_iff.mp (h b)),
      commutatorElement_mul_central_left (Subgroup.mem_center_iff.mp (h a))]
  have hS : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤
      MonoidHom.eqLocus (β : Q →* Q) (MonoidHom.id Q) := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact hc a b
  ext q
  have hq : q ∈ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
    rw [← commutator_def, hperf]
    trivial
  exact hS hq

end CFSG.ClassicalInvolution.Q3.Q3TIY
