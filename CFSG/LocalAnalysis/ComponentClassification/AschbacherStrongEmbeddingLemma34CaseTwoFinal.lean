module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34CaseTwoInvolution

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
theorem inf_centralizer_mul_left (hc : ⁅A₁, A₂⁆ = ⊥) {e₁ e₂ : G} (he₂ : e₂ ∈ A₂) :
    A₁ ⊓ Subgroup.centralizer ({e₁ * e₂} : Set G) =
      A₁ ⊓ Subgroup.centralizer ({e₁} : Set G) := by
  ext b
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hb => ?_
  have hbe₂ : b * e₂ = e₂ * b := (commute_of_comm hc hb he₂).eq
  constructor
  · intro hbe
    apply mul_right_cancel (b := e₂)
    calc b * e₁ * e₂ = e₁ * e₂ * b := by rw [mul_assoc, hbe]
      _ = e₁ * b * e₂ := by rw [mul_assoc, ← hbe₂, mul_assoc]
  · intro hbe
    calc b * (e₁ * e₂) = e₁ * b * e₂ := by rw [← mul_assoc, hbe]
      _ = e₁ * e₂ * b := by rw [mul_assoc, hbe₂, ← mul_assoc]

omit [Finite G] in
theorem inf_centralizer_mul_right (hc : ⁅A₁, A₂⁆ = ⊥) {e₁ e₂ : G} (he₁ : e₁ ∈ A₁) :
    A₂ ⊓ Subgroup.centralizer ({e₁ * e₂} : Set G) =
      A₂ ⊓ Subgroup.centralizer ({e₂} : Set G) := by
  ext b
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hb => ?_
  have hbe₁ : b * e₁ = e₁ * b := (commute_of_comm hc he₁ hb).eq.symm
  constructor
  · intro hbe
    apply mul_left_cancel (a := e₁)
    calc e₁ * (b * e₂) = b * (e₁ * e₂) := by rw [← mul_assoc, ← hbe₁, mul_assoc]
      _ = e₁ * (e₂ * b) := by rw [hbe, mul_assoc]
  · intro hbe
    calc b * (e₁ * e₂) = e₁ * (b * e₂) := by rw [← mul_assoc, hbe₁, mul_assoc]
      _ = e₁ * e₂ * b := by rw [hbe, mul_assoc]

omit [Finite G] in
theorem not_dihedralCase_of_central {K : Subgroup G} (P : Subgroup K) {e : G}
    (he : e ∈ A₁ ⊓ K) (hcen : ∀ b ∈ A₁ ⊓ K, Commute e b) (he2 : e ^ 2 ≠ 1) :
    ¬ DihedralCase P (A₁.subgroupOf K) (A₂.subgroupOf K) := by
  rintro ⟨-, hd, -⟩
  have e' : A₁.subgroupOf K ≃* (A₁ ⊓ K : Subgroup G) :=
    (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right A₁ K).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right)
  exact he2 (sq_eq_one_of_commute_of_dihedral (dihedral_of_mulEquiv e' hd) he hcen)

theorem Hyp.centralizer_mul_le (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (IH : Statement (Nat.card G - 1)) {y e₁ e₂ : G} (hy : y = e₁ * e₂) (he₁ : e₁ ∈ A₁)
    (he₂ : e₂ ∈ A₂) (hK : Subgroup.centralizer ({y} : Set G) ≠ ⊤)
    (P : Sylow 2 (Subgroup.centralizer ({y} : Set G)))
    (hP : (P : Subgroup _) = (S : Subgroup G).subgroupOf (Subgroup.centralizer ({y} : Set G)))
    (hr₁ : 2 ≤ CFSG.Open.pRank 2 (A₁ ⊓ Subgroup.centralizer ({e₁} : Set G)))
    (hr₂ : 2 ≤ CFSG.Open.pRank 2 (A₂ ⊓ Subgroup.centralizer ({e₂} : Set G)))
    (hn₁ : ¬ A₁ ⊓ Subgroup.centralizer ({e₁} : Set G) ≤ A₂)
    (hn₂ : ¬ A₂ ⊓ Subgroup.centralizer ({e₂} : Set G) ≤ A₁)
    (h3 : ¬ DihedralCase (P : Subgroup _) (A₁.subgroupOf (Subgroup.centralizer ({y} : Set G)))
      (A₂.subgroupOf (Subgroup.centralizer ({y} : Set G)))) :
    Subgroup.centralizer ({y} : Set G) ≤ overlapClosure A₁ A₂ := by
  subst hy
  have hl := inf_centralizer_mul_left h.comm (e₁ := e₁) he₂
  have hr := inf_centralizer_mul_right h.comm (e₂ := e₂) he₁
  exact h.le_overlapClosure_of_statement h12 h21 IH hK P hP (hl ▸ hr₁) (hr ▸ hr₂)
    (hl ▸ hn₁) (hr ▸ hn₂) h3

omit [Finite G] in
theorem mem_inf_centralizer_mul (hc : ⁅A₁, A₂⁆ = ⊥) {e₁ e₂ : G} (he₁ : e₁ ∈ A₁)
    (he₂ : e₂ ∈ A₂) :
    e₁ ∈ A₁ ⊓ Subgroup.centralizer ({e₁ * e₂} : Set G) ∧
      ∀ b ∈ A₁ ⊓ Subgroup.centralizer ({e₁ * e₂} : Set G), Commute e₁ b := by
  rw [inf_centralizer_mul_left hc he₂]
  refine ⟨⟨he₁, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, fun b hb => ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp hb.2).symm

namespace CaseTwo

variable {a t z : G} (c : CaseTwo S A₁ A₂ a t z)
include c

@[expose] def twistHom : A₁ →* G where
  toFun b := twist t b
  map_one' := by
    change 1 * (t * 1 * t) = 1
    rw [one_mul, mul_one, c.t_mul_self]
  map_mul' b d := c.twist_mul b.2 d.2

theorem twistHom_apply (b : A₁) : c.twistHom b = twist t b := rfl

theorem mem_twistHom_range {y : G} (hy : y ∈ c.twistHom.range) :
    ∃ u ∈ A₁, twist t u = y := by
  obtain ⟨b, rfl⟩ := hy
  exact ⟨b, b.2, rfl⟩

theorem twistHom_range_le_sylow : c.twistHom.range ≤ (S : Subgroup G) := by
  rintro _ ⟨b, rfl⟩
  exact c.twist_mem_sylow b.2

theorem twistHom_range_le_centralizer :
    c.twistHom.range ≤ Subgroup.centralizer ({t} : Set G) := by
  rintro _ ⟨b, rfl⟩
  exact c.twist_mem_centralizer b.2

theorem mem_inf_of_twist_eq_one {b : G} (hb : b ∈ A₁) (h1 : twist t b = 1) :
    b ∈ A₁ ⊓ A₂ := by
  refine ⟨hb, ?_⟩
  have hinv : t * b * t = b⁻¹ := eq_inv_of_mul_eq_one_right h1
  have := A₂.inv_mem (c.conj_mem_two hb)
  rwa [hinv, inv_inv] at this

theorem eq_one_or_eq_z_of_card (hI2 : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) {b : G}
    (hb : b ∈ A₁ ⊓ A₂) : b = 1 ∨ b = z := by
  by_contra hcon
  rw [not_or] at hcon
  have := three_le_card_of_mem c.inf_mem hb c.ne_one hcon.1 (Ne.symm hcon.2)
  omega

theorem twist_z : twist t z = 1 := by
  change z * (t * z * t) = 1
  rw [c.conj_z, c.mul_self]

theorem eight_le_card (hnd : ¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁)) :
    8 ≤ Nat.card A₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := four_le_card_of_two_le_pRank c.hyp.rank_one
  have hA2 : IsPGroup 2 A₁ := S.isPGroup'.to_le c.hyp.le_one
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hne : Nat.card A₁ ≠ 4 := fun h4' =>
    hnd (Or.inl (isDihedral_of_card_four hA2 h4' c.hyp.rank_one))
  rw [hk] at h4 hne ⊢
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k <;> simp_all
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3

theorem four_le_card_range (hI2 : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (hnd : ¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁)) :
    4 ≤ Nat.card c.twistHom.range := by
  have h8 := c.eight_le_card hnd
  have hker : Nat.card c.twistHom.ker ≤ 2 := by
    rw [← hI2, ← Subgroup.card_map_of_injective A₁.subtype_injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨b, hb, rfl⟩
    exact c.mem_inf_of_twist_eq_one b.2 hb
  have hmul := Subgroup.card_ker_mul_card_range c.twistHom
  have hpos : 0 < Nat.card c.twistHom.ker := Nat.card_pos
  by_contra hcon
  have : Nat.card c.twistHom.ker * Nat.card c.twistHom.range ≤ 2 * 3 :=
    Nat.mul_le_mul hker (by omega)
  omega

theorem twist_one : twist t 1 = 1 := c.twistHom.map_one

theorem mul_self_of_mem_inf (hI2 : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) {b : G}
    (hb : b ∈ A₁ ⊓ A₂) : b * b = 1 := by
  rcases c.eq_one_or_eq_z_of_card hI2 hb with rfl | rfl
  · exact mul_one 1
  · exact c.mul_self

theorem not_mem_inf_of_mul_self (hI2 : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) {b : G}
    (hbb : b * b = z) : b ∉ A₁ ⊓ A₂ := fun hb => c.ne_one (hbb ▸ c.mul_self_of_mem_inf hI2 hb)

theorem orderOf_eq_four_of_mul_self {b : G} (hbb : b * b = z) : orderOf b = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := b)
    (by rw [pow_one, sq, hbb]; exact c.ne_one)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, sq b, hbb, sq, c.mul_self])
  rw [h]
  norm_num

theorem false_of_twist_order_four (IH : Statement (Nat.card G - 1))
    (hH : overlapClosure A₁ A₂ ≠ ⊤) (hI2 : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (hnd : ¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁)) {u : G} (hu : u ∈ A₁)
    (huu : u * u = z) {g : G} (hg : EscapeChoice A₁ A₂ a t g)
    (hYN : twist t u ∈ Subgroup.normalizer (rightConjugate A₁ g : Set G)) : False := by
  have h := c.hyp
  have h12 := c.not_le₁₂
  have h21 := c.not_le₂₁
  have hnd₂ := c.not_dihedral_two hnd
  have hA₁2 : IsPGroup 2 A₁ := S.isPGroup'.to_le h.le_one
  have hA₂2 : IsPGroup 2 A₂ := S.isPGroup'.to_le h.le_two
  have hSH := h.sylow_le_overlapClosure h12 h21
  have huA : u ∉ A₂ := fun h' => c.not_mem_inf_of_mul_self hI2 huu ⟨hu, h'⟩
  obtain ⟨w, hw⟩ : ∃ w, t * u * t = w := ⟨_, rfl⟩
  have hwA : w ∈ A₂ := hw ▸ c.conj_mem_two hu
  have hww : w * w = z := by
    rw [← hw, ← c.conj_z, ← huu]
    calc t * u * t * (t * u * t) = t * u * (t * t) * u * t := by group
      _ = t * (u * u) * t := by rw [c.t_mul_self, mul_one, mul_assoc t u u]
  have hwA₁ : w ∉ A₁ := fun h' => c.not_mem_inf_of_mul_self hI2 hww ⟨h', hwA⟩
  have hu4 := c.orderOf_eq_four_of_mul_self huu
  have hw4 := c.orderOf_eq_four_of_mul_self hww
  have hYw : twist t u = u * w := by rw [twist, hw]
  have hYY : twist t u * twist t u = 1 := by
    rw [c.twist_mul_self_eq hu, huu, c.conj_z, c.mul_self]
  have hY1 : twist t u ≠ 1 := c.twist_ne_one hu huA
  have hY2 : orderOf (twist t u) = 2 := orderOf_eq_prime (by rw [sq]; exact hYY) hY1
  have hYA₁ : twist t u ∉ A₁ := by
    intro hY
    apply hwA₁
    have := A₁.mul_mem (A₁.inv_mem hu) hY
    rwa [hYw, inv_mul_cancel_left] at this
  have hYA₂ : twist t u ∉ A₂ := c.twist_not_mem hu huA
  have h8 := c.eight_le_card hnd
  by_cases hYc : twist t u ∈ Subgroup.center G
  · have hn₁ : ¬ A₁ ≤ A₂ ⊔ Subgroup.zpowers (twist t u) := fun hle => by
      have := card_le_two_mul_inf_of_le_sup_zpowers hYc hYY hle
      omega
    have hn₂ : ¬ A₂ ⊔ ⊥ ≤ A₁ ⊔ Subgroup.zpowers (twist t u) := fun hle => by
      rw [sup_bot_eq] at hle
      have := card_le_two_mul_inf_of_le_sup_zpowers hYc hYY hle
      rw [inf_comm, hI2, c.card_two] at this
      omega
    rw [sup_bot_eq] at hn₂
    rcases h.quotient_central h12 h21 IH hYc hYY hYA₁ hYA₂ hn₁ hn₂ with htop | ⟨hd, -⟩
    · exact hH htop
    · exact hnd hd
  have hCY : Subgroup.centralizer ({twist t u} : Set G) ≤ overlapClosure A₁ A₂ := by
    set X := A₁ ⊓ Subgroup.centralizer ({u} : Set G) with hX
    have hr := two_le_pRank_inf_centralizer_of_orderOf_four hA₁2 h.rank_one hnd hu hu4
    have hX4 := four_le_card_of_two_le_pRank hr
    have hXU : (X : Set G) ⊆ (A₁ : Set G) ∪ A₂ := fun x hx => Or.inl hx.1
    have hXS : X ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({twist t u} : Set G) := by
      intro x hx
      have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hxw : x * w = w * x := (c.commute_one_two hx.1 hwA).eq
      refine Subgroup.mem_inf.mpr ⟨h.le_one hx.1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hYw]
      rw [← mul_assoc, hxu, mul_assoc, hxw, ← mul_assoc]
    have hXf := h.fixesOnly_of_card h12 h21 hXU hX4
    obtain ⟨k, hk, ⟨P, hP⟩, hconj⟩ := h.exists_conj_sylow_inf hSH hXS hXf
    have huC : u ∈ Subgroup.centralizer ({twist t u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, hYw, mul_assoc u w u,
        ← (c.commute_one_two hu hwA).eq]
    have hwC : w ∈ Subgroup.centralizer ({twist t u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, hYw, ← mul_assoc,
        ← (c.commute_one_two hu hwA).eq]
    have hu' := hconj u (Or.inl hu) huC
    have hw' := hconj w (Or.inr hwA) hwC
    have hYk : k⁻¹ * twist t u * k = (k⁻¹ * u * k) * (k⁻¹ * w * k) := by rw [hYw]; group
    have hconj4 : ∀ {b : G}, orderOf b = 4 → orderOf (k⁻¹ * b * k) = 4 := fun hb => by
      rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]; exact hb
    have hYk2 : orderOf (k⁻¹ * twist t u * k) = 2 := by
      rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]; exact hY2
    have hKne : Subgroup.centralizer ({k⁻¹ * twist t u * k} : Set G) ≠ ⊤ := by
      intro htop
      apply hYc
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : k⁻¹ * x * k ∈ Subgroup.centralizer ({k⁻¹ * twist t u * k} : Set G) :=
        htop ▸ Subgroup.mem_top _
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      have := congrArg (fun q => k * q * k⁻¹) hx
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at this
      exact this
    have hnotI : ∀ {b : G}, orderOf b = 4 → b ∈ A₁ → b ∉ A₂ := fun hb hb₁ hb₂ => by
      have := c.mul_self_of_mem_inf hI2 ⟨hb₁, hb₂⟩
      rw [← sq, ← orderOf_dvd_iff_pow_eq_one, hb] at this
      norm_num at this
    have hnotI₂ : ∀ {b : G}, orderOf b = 4 → b ∈ A₂ → b ∉ A₁ := fun hb hb₂ hb₁ =>
      hnotI hb hb₁ hb₂
    have hsq4 : ∀ {b : G}, orderOf b = 4 → b ^ 2 ≠ 1 := fun hb h1 => by
      rw [← orderOf_dvd_iff_pow_eq_one, hb] at h1
      norm_num at h1
    suffices hK : Subgroup.centralizer ({k⁻¹ * twist t u * k} : Set G) ≤ overlapClosure A₁ A₂ by
      rw [centralizer_conj_eq] at hK
      intro x hx
      have hx' := hK (mem_rightConjugate_conj (g := k) hx)
      have := (overlapClosure A₁ A₂).mul_mem
        ((overlapClosure A₁ A₂).mul_mem hk hx') ((overlapClosure A₁ A₂).inv_mem hk)
      simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using this
    have hpr : ∀ {B : Subgroup G}, IsPGroup 2 B → 2 ≤ CFSG.Open.pRank 2 B →
        ¬ (IsDihedralTwoGroup B ∨ IsSemidihedralTwoGroup B) → ∀ {b : G}, b ∈ B →
          orderOf b = 4 → 2 ≤ CFSG.Open.pRank 2 (B ⊓ Subgroup.centralizer ({b} : Set G)) :=
      fun hB hBr hBd _ hb hb4 => two_le_pRank_inf_centralizer_of_orderOf_four hB hBr hBd hb hb4
    have hself : ∀ {B : Subgroup G} {b : G}, b ∈ B →
        b ∈ B ⊓ Subgroup.centralizer ({b} : Set G) := fun hb =>
      ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    rcases hu' with hu₁ | hu₂ <;> rcases hw' with hw₁ | hw₂
    · exact h.centralizer_le_of_involution h12 h21 IH hH (Or.inr ⟨hnd, hnd₂⟩)
        (Or.inl (hYk ▸ A₁.mul_mem hu₁ hw₁)) hYk2
    · have hu4' := hconj4 hu4
      have hw4' := hconj4 hw4
      obtain ⟨hmem, hcen⟩ := mem_inf_centralizer_mul h.comm hu₁ hw₂
      exact h.centralizer_mul_le h12 h21 IH hYk hu₁ hw₂ hKne P hP
        (hpr hA₁2 h.rank_one hnd hu₁ hu4') (hpr hA₂2 h.rank_two hnd₂ hw₂ hw4')
        (fun hle => hnotI hu4' hu₁ (hle (hself hu₁)))
        (fun hle => hnotI₂ hw4' hw₂ (hle (hself hw₂)))
        (not_dihedralCase_of_central (P : Subgroup _) (hYk ▸ hmem) (hYk ▸ hcen) (hsq4 hu4'))
    · have hu4' := hconj4 hu4
      have hw4' := hconj4 hw4
      have hYk' : k⁻¹ * twist t u * k = (k⁻¹ * w * k) * (k⁻¹ * u * k) := by
        rw [hYk, (c.commute_one_two hw₁ hu₂).eq]
      obtain ⟨hmem, hcen⟩ := mem_inf_centralizer_mul h.comm hw₁ hu₂
      exact h.centralizer_mul_le h12 h21 IH hYk' hw₁ hu₂ hKne P hP
        (hpr hA₁2 h.rank_one hnd hw₁ hw4') (hpr hA₂2 h.rank_two hnd₂ hu₂ hu4')
        (fun hle => hnotI hw4' hw₁ (hle (hself hw₁)))
        (fun hle => hnotI₂ hu4' hu₂ (hle (hself hu₂)))
        (not_dihedralCase_of_central (P : Subgroup _) (hYk' ▸ hmem) (hYk' ▸ hcen) (hsq4 hw4'))
    · exact h.centralizer_le_of_involution h12 h21 IH hH (Or.inr ⟨hnd, hnd₂⟩)
        (Or.inr (hYk ▸ A₂.mul_mem hu₂ hw₂)) hYk2
  have hB := h.conj g
  have hsmall : Nat.card (rightConjugate A₁ g ⊓ Subgroup.centralizer ({twist t u} : Set G) :
      Subgroup G) ≤ 2 := by
    refine card_le_two_of_lt_four ((conjSylow S g).isPGroup'.to_le (inf_le_left.trans
      hB.le_one)) ?_
    by_contra hcon
    exact h.choice_not_le_conj h12 h21 hg (fun x hx => Or.inl (Subgroup.mem_inf.mp hx).1)
      (not_lt.mp hcon) (fun x hx => hCY (Subgroup.mem_inf.mp hx).2)
  have hdB := isDihedral_of_involution_small_centralizer
    ((conjSylow S g).isPGroup'.to_le hB.le_one) hB.rank_one hYY hYN hsmall
  exact hnd (dihedral_of_mulEquiv (rightConjugateEquiv A₁ g).symm (Or.inl hdB))

theorem false (hD : ¬ DihedralCase (S : Subgroup G) A₁ A₂) (IH : Statement (Nat.card G - 1))
    (hH : overlapClosure A₁ A₂ ≠ ⊤) : False := by
  obtain ⟨v, hv, hvA, hvv⟩ := c.exists_involution
  have hI2 := c.card_inf_eq_two hv hvA hvv
  have hnd := c.not_dihedral hD hv hvA hvv
  have hxR : twist t v ∈ c.twistHom.range := ⟨⟨v, hv⟩, rfl⟩
  have hxx : twist t v * twist t v = 1 := c.twist_mul_self hv (by rw [hvv]; exact A₂.one_mem)
  have hx1 : twist t v ≠ 1 := c.twist_ne_one hv hvA
  have hx2 : orderOf (twist t v) = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  have hRp : IsPGroup 2 c.twistHom.range := S.isPGroup'.to_le c.twistHom_range_le_sylow
  have hsq : ∀ r ∈ c.twistHom.range, r * r ≠ twist t v := fun r hr =>
    c.twist_not_sq hv hvA hvv (c.twistHom_range_le_centralizer hr)
  obtain ⟨y, hyR, hy2, hyx, hxy⟩ :=
    exists_involution_commute_of_not_sq hRp hxR hx2 hsq (c.four_le_card_range hI2 hnd)
  obtain ⟨u, hu, rfl⟩ := c.mem_twistHom_range hyR
  have hyy : twist t u * twist t u = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hy2).1
  have hy1 : twist t u ≠ 1 := (orderOf_eq_prime_iff.mp hy2).2
  have hVS : Subgroup.zpowers (twist t v) ⊔ Subgroup.zpowers (twist t u) ≤ (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr (c.twist_mem_sylow hv))
      (Subgroup.zpowers_le.mpr (c.twist_mem_sylow hu))
  have hVC : Subgroup.zpowers (twist t v) ⊔ Subgroup.zpowers (twist t u) ≤
      Subgroup.centralizer ({t} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (c.twist_mem_centralizer hv))
      (Subgroup.zpowers_le.mpr (c.twist_mem_centralizer hu))
  obtain ⟨g, hg, hVT⟩ := c.rechoice _ (S.isPGroup'.to_le hVS) hVC
  have hxT : twist t v ∈ rightConjugate (S : Subgroup G) g :=
    hVT (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hyT : twist t u ∈ rightConjugate (S : Subgroup G) g :=
    hVT (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hxs : rightConjugate (rightConjugate A₂ g) (twist t v) = rightConjugate A₁ g := by
    rcases c.mem_pairStabilizer hxT with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact absurd ((rightConjugate_eq_self_iff _ _).mp h₁)
        (c.twist_not_mem_normalizer hv hvA hvv hg hxT)
    · exact h₂
  obtain ⟨u', hu', hYT, hYN, hY1, hYY⟩ : ∃ u' ∈ A₁,
      twist t u' ∈ rightConjugate (S : Subgroup G) g ∧
      twist t u' ∈ Subgroup.normalizer (rightConjugate A₁ g : Set G) ∧
      twist t u' ≠ 1 ∧ twist t u' * twist t u' = 1 := by
    rcases c.mem_pairStabilizer hyT with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact ⟨u, hu, hyT, (rightConjugate_eq_self_iff _ _).mp h₁, hy1, hyy⟩
    · refine ⟨u * v, A₁.mul_mem hu hv, ?_, ?_, ?_, ?_⟩
      · rw [c.twist_mul hu hv]
        exact Subgroup.mul_mem _ hyT hxT
      · rw [c.twist_mul hu hv, ← rightConjugate_eq_self_iff, ← rightConjugate_mul, h₁, hxs]
      · rw [c.twist_mul hu hv]
        intro h1
        apply hyx
        rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_left hxx]
      · rw [c.twist_mul hu hv]
        calc twist t u * twist t v * (twist t u * twist t v)
            = twist t u * (twist t v * twist t u) * twist t v := by group
          _ = twist t u * (twist t u * twist t v) * twist t v := by rw [hxy.eq]
          _ = twist t u * twist t u * (twist t v * twist t v) := by group
          _ = 1 := by rw [hyy, hxx, one_mul]
  have hu'A : u' ∉ A₂ := by
    intro h'
    apply hY1
    rcases c.eq_one_or_eq_z_of_card hI2 ⟨hu', h'⟩ with rfl | rfl
    · exact c.twist_one
    · exact c.twist_z
  have hu'u' : u' * u' = z := by
    have h1 : twist t (u' * u') = 1 := by rw [c.twist_mul hu' hu', hYY]
    rcases c.eq_one_or_eq_z_of_card hI2
        (c.mem_inf_of_twist_eq_one (A₁.mul_mem hu' hu') h1) with h2 | h2
    · exact absurd hYN (c.twist_not_mem_normalizer hu' hu'A h2 hg hYT)
    · exact h2
  exact c.false_of_twist_order_four IH hH hI2 hnd hu' hu'u' hg hYN

end CaseTwo

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
