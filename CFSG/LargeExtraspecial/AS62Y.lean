module

public import CFSG.LargeExtraspecial.AS62Frame2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup AS62.Sem

namespace AS62

section Words

variable {G : Type*} [Group G]

theorem lift_mk_liftWord (z t e x y : G) (w : List (Fin 4 × Bool)) :
    FreeGroup.lift ![z, t, e, x, y] (FreeGroup.mk (liftWord w)) =
      FreeGroup.lift ![z, t, e, x] (FreeGroup.mk w) := by
  induction w with
  | nil => simp only [liftWord, List.map_nil, FreeGroup.lift_mk, List.prod_nil]
  | cons a w ih =>
    simp only [liftWord, List.map_cons, Sem.lift_mk_cons] at ih ⊢
    rw [ih, Frame.gens2_castSucc]

theorem lift_rels1_eq_one {z t e x y : G}
    (hB : ∀ r ∈ relsB, FreeGroup.lift ![z, t, e, x] (FreeGroup.mk r) = 1)
    (hz : z * z = 1) (he : e * e = 1) (h1 : y * y * y = 1) (h2 : x * y = y * x)
    (h3 : t * y * t * y = 1) (h4 : y * (t * e * t * e) * y⁻¹ = z * e) :
    ∀ r ∈ rels1, FreeGroup.lift ![z, t, e, x, y] (FreeGroup.mk r) = 1 := by
  intro r hr
  rw [rels1, List.mem_append] at hr
  rcases hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk_liftWord]
    exact hB w hw
  · simp only [rels1Extra, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Bool.cond_true, Bool.cond_false, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, mul_one]
    · rw [← mul_assoc]
      exact h1
    · rw [← mul_assoc, ← mul_assoc, h2, mul_inv_cancel_right, mul_inv_cancel]
    · rw [← mul_assoc, ← mul_assoc]
      exact h3
    · have h5 : y * (t * (e * (t * (e * y⁻¹)))) = z * e := by
        rw [← h4]
        group
      rw [show y * (t * (e * (t * (e * (y⁻¹ * (e * z)))))) =
        y * (t * (e * (t * (e * y⁻¹)))) * (e * z) by group, h5, mul_assoc, ← mul_assoc e e, he,
        one_mul, hz]

theorem forall_mem_setOf_map_mk {n : ℕ} {f : Fin n → G} {ws : List (List (Fin n × Bool))}
    (h : ∀ r ∈ ws, FreeGroup.lift f (FreeGroup.mk r) = 1) :
    ∀ r ∈ {r : FreeGroup (Fin n) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift f r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact h w hw

end Words

namespace YCon

section Group

variable {G : Type*} [Group G]

theorem commute_of_conj_eq {m m' u : G} (h : m * u * m⁻¹ = m' * u * m'⁻¹) :
    m'⁻¹ * m * u = u * (m'⁻¹ * m) :=
  calc m'⁻¹ * m * u = m'⁻¹ * (m * u * m⁻¹) * m := by group
    _ = m'⁻¹ * (m' * u * m'⁻¹) * m := by rw [h]
    _ = u * (m'⁻¹ * m) := by group

theorem cube_mul_mul_eq {a c : G} (hac : a * c = c * a) (ha : a * a * a = 1) (hc : c * c = 1) :
    a * a * c * (a * a * c) * (a * a * c) = c := by
  have h : Commute a c := hac
  calc a * a * c * (a * a * c) * (a * a * c) = (a * a * c) ^ 3 := (pow_three' _).symm
    _ = (a * a) ^ 3 * c ^ 3 := (h.mul_left h).mul_pow 3
    _ = a * a * a * (a * a * a) * (c * c * c) := by
        rw [pow_three', pow_three']
        simp only [mul_assoc]
    _ = c := by rw [ha, hc, one_mul, one_mul, one_mul]

end Group

section Data

variable {G : Type*} [Group G] {F : Frame G} {z t e x : G}

theorem commute_of_rep {g h : G} {dg dh : ℕ × ℕ} (hg : F.Rep g dg) (hh : F.Rep h dh)
    (hd : dmul dg dh = dmul dh dg) : g * h = h * g :=
  F.eq_of_rep (F.rep_mul hg hh) (F.rep_congr (F.rep_mul hh hg) hd.symm)

theorem mul_self_of_rep_tD (ht : F.Rep t tD) : t * t = 1 :=
  F.eq_one_of_rep (F.rep_congr (F.rep_mul ht ht) (by decide +kernel))

theorem mul_self_of_rep_eD (he : F.Rep e eD) : e * e = 1 :=
  F.eq_one_of_rep (F.rep_congr (F.rep_mul he he) (by decide +kernel))

theorem cube_of_rep_xD (hx : F.Rep x xD) : x * x * x = 1 :=
  F.eq_one_of_rep (F.rep_congr (F.rep_mul (F.rep_mul hx hx) hx) (by decide +kernel))

theorem ne_one_of_rep_xD (hx : F.Rep x xD) : x ≠ 1 := by
  rintro rfl
  exact absurd (F.rep_unique hx F.rep_one) (by decide +kernel)

theorem ne_one_of_rep_tD (ht : F.Rep t tD) : t ≠ 1 := by
  rintro rfl
  exact absurd (F.rep_unique ht F.rep_one) (by decide +kernel)

theorem ne_of_rep_zD_tD (hz : F.Rep z zD) (ht : F.Rep t tD) : z ≠ t := by
  rintro rfl
  exact absurd (F.rep_unique hz ht) (by decide +kernel)

theorem t_mul_b1_mul_t (ht : F.Rep t tD) (he : F.Rep e eD) :
    t * (t * e * t * e) * t = t * e * t * e :=
  F.eq_of_rep (F.rep_congr (F.rep_mul (F.rep_mul ht (F.rep_b1 ht he)) ht) (by decide +kernel))
    (F.rep_b1 ht he)

end Data

end YCon

variable {G : Type} [Group G] [Finite G]

theorem card_M_eq_card_QG_mul (S : Setting G) :
    Nat.card S.M = Nat.card S.QG * Nat.card S.Mbar := by
  rw [card_eq_card_quotient_mul_card_subgroup S.ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange S.ρ).toEquiv, S.ker_ρ, mul_comm,
    S.card_QG_eq_card_Q]
  rfl

theorem ConfHyp.card_M_of_card_Mbar {S : Setting G} {H : Subgroup G} (hc : ConfHyp S H)
    (h18 : Nat.card S.Mbar = 18) : Nat.card S.M = 576 := by
  rw [card_M_eq_card_QG_mul, hc.card_QG, h18]

namespace YCon

variable {S : Setting G} {H : Subgroup G} {F : Frame G}

theorem b1_mem_QG (hF : IsFrameOf S H F) (hc : ConfHyp S H) {t e : G} (ht : F.Rep t tD)
    (he : F.Rep e eD) : t * e * t * e ∈ S.QG := by
  have htM : t ∈ S.M := S.mem_M_iff.mpr (commute_of_rep ht hF.rep_z (by decide +kernel))
  have heQ := hF.mem_QG_of_rep_eD hc he
  have h1 := S.conj_mem_QG htM heQ
  rw [inv_eq_of_mul_eq_one_right (mul_self_of_rep_tD ht)] at h1
  exact S.QG.mul_mem h1 heQ

theorem eq_one_or_z_of_commute_gens (hF : IsFrameOf S H F) (hc : ConfHyp S H) {t e x g : G}
    (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) (hgM : g ∈ S.M)
    (h₁ : g * (t * e * t * e) = t * e * t * e * g) (h₂ : g * e = e * g)
    (h₃ : g * x = x * g) : g = 1 ∨ g = S.z := by
  have hQ : ∀ q ∈ S.QG, g * q = q * g := fun q hq =>
    hF.commute_QG_of_commute hc ht he hx h₁ h₂ h₃ (S.mem_M_iff.mp hgM) hq
  exact S.eq_one_or_z_of_commute (S.mem_QG_of_commute hgM hQ) hQ

theorem eq_or_eq_mul_z (hF : IsFrameOf S H F) (hc : ConfHyp S H) {t e x : G}
    (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) {m m₀ : G} (hm : m ∈ S.M)
    (hmx : m * x = x * m) (hm₀ : m₀ ∈ S.M) (hm₀x : m₀ * x = x * m₀)
    (h₁ : m * (t * e * t * e) * m⁻¹ = m₀ * (t * e * t * e) * m₀⁻¹)
    (h₂ : m * e * m⁻¹ = m₀ * e * m₀⁻¹) : m = m₀ ∨ m = m₀ * S.z := by
  have hx₀ : m₀⁻¹ * x = x * m₀⁻¹ :=
    calc m₀⁻¹ * x = m₀⁻¹ * (x * m₀) * m₀⁻¹ := by group
      _ = m₀⁻¹ * (m₀ * x) * m₀⁻¹ := by rw [hm₀x]
      _ = x * m₀⁻¹ := by group
  have hgx : m₀⁻¹ * m * x = x * (m₀⁻¹ * m) :=
    calc m₀⁻¹ * m * x = m₀⁻¹ * (m * x) := by group
      _ = m₀⁻¹ * (x * m) := by rw [hmx]
      _ = m₀⁻¹ * x * m := by group
      _ = x * (m₀⁻¹ * m) := by rw [hx₀]; group
  rcases eq_one_or_z_of_commute_gens hF hc ht he hx (mul_mem (inv_mem hm₀) hm)
      (commute_of_conj_eq h₁) (commute_of_conj_eq h₂) hgx with h | h
  · exact Or.inl (inv_mul_eq_one.mp h).symm
  · exact Or.inr (inv_mul_eq_iff_eq_mul.mp h)

theorem le_card_centralizer (hF : IsFrameOf S H F) (hc : ConfHyp S H)
    (hMbar : Nat.card S.Mbar = 18 ∨ Nat.card S.Mbar = 36) {t x : G} (ht : F.Rep t tD)
    (hx : F.Rep x xD) :
    36 ≤ Nat.card ↥(S.M ⊓ centralizer ({x} : Set G)) := by
  have hM : Nat.card S.M = 576 ∨ Nat.card S.M = 1152 := by
    rw [card_M_eq_card_QG_mul, hc.card_QG]
    rcases hMbar with h | h <;> rw [h] <;> simp
  have hz := hF.rep_z
  have hxM : x ∈ S.M := hF.mem_M_of_rep_xD hx
  have hxz : x * S.z = S.z * x := S.mem_M_iff.mp hxM
  have hxt : x * t = t * x := commute_of_rep hx ht (by decide +kernel)
  have htz : t * S.z = S.z * t := commute_of_rep ht hz (by decide +kernel)
  have htM : t ∈ S.M := S.mem_M_iff.mpr htz
  have h9 : 9 ∣ Nat.card ↥(S.M ⊓ centralizer ({x} : Set G)) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hx3 : (⟨x, hxM⟩ : S.M) ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, pow_three']
      exact cube_of_rep_xD hx)
    have hx1 : (⟨x, hxM⟩ : S.M) ≠ 1 := fun h => ne_one_of_rep_xD hx (congrArg Subtype.val h)
    have hXp : IsPGroup 3 (zpowers (⟨x, hxM⟩ : S.M)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
    obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hd1 : 3 ^ 2 ∣ 3 ^ n := by
      rw [← hn]
      exact P.pow_dvd_card_of_pow_dvd_card (by rcases hM with h | h <;> rw [h] <;> norm_num)
    have hd2 : 3 ^ n ∣ 1152 := by
      have h := card_subgroup_dvd_card (P : Subgroup S.M)
      rw [hn] at h
      rcases hM with hM | hM <;> rw [hM] at h
      · exact h.trans (by norm_num)
      · exact h
    have hn2 : n = 2 := by
      have h1 : 2 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd1
      have h2 : n < 3 := by
        by_contra hn3
        have h27 := (Nat.pow_dvd_pow 3 (not_lt.mp hn3)).trans hd2
        norm_num at h27
      omega
    rw [hn2] at hn
    have hcomm : ∀ a b : ↥(P : Subgroup S.M), a * b = b * a :=
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hn).is_comm.comm
    have hle : (P : Subgroup S.M).map S.M.subtype ≤ S.M ⊓ centralizer ({x} : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      refine mem_inf.mpr ⟨p.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h := hcomm ⟨p, hp⟩ ⟨⟨x, hxM⟩, hXP (mem_zpowers _)⟩
      exact congrArg (fun q : ↥(P : Subgroup S.M) => ((q : S.M) : G)) h
    have hcard : Nat.card ↥((P : Subgroup S.M).map S.M.subtype) = 9 := by
      rw [card_map_of_injective S.M.subtype_injective, hn]
      norm_num
    rw [← hcard]
    exact card_dvd_of_le hle
  have h4 : 4 ∣ Nat.card ↥(S.M ⊓ centralizer ({x} : Set G)) := by
    have hzC : S.z ∈ S.M ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨S.z_mem_M, mem_centralizer_singleton_iff.mpr hxz.symm⟩
    have htC : t ∈ S.M ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨htM, mem_centralizer_singleton_iff.mpr hxt.symm⟩
    have hK : kleinSub S.z t S.z_mul_z (mul_self_of_rep_tD ht) htz.symm ≤
        S.M ⊓ centralizer ({x} : Set G) := by
      intro g hg
      rcases mem_kleinSub.mp hg with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hzC
      · exact htC
      · exact mul_mem hzC htC
    rw [← card_kleinSub (ha := S.z_mul_z) (hb := mul_self_of_rep_tD ht) (hab := htz.symm)
      S.z_ne_one (ne_one_of_rep_tD ht) (ne_of_rep_zD_tD hz ht)]
    exact card_dvd_of_le hK
  have h36 := Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h4)
  omega

open Classical in
noncomputable def dataOf (F : Frame G) (h : G) : ℕ × ℕ :=
  if hh : h ∈ F.H then Classical.choose (F.rep_exists hh) else (0, 0)

omit [Finite G] in
theorem rep_dataOf (F : Frame G) {h : G} (hh : h ∈ F.H) : F.Rep h (dataOf F h) := by
  rw [dataOf, dite_eq_left hh]
  exact Classical.choose_spec (F.rep_exists hh)

theorem exists_conj_alpha0 (hF : IsFrameOf S H F) (hc : ConfHyp S H)
    (hMbar : Nat.card S.Mbar = 18 ∨ Nat.card S.Mbar = 36) {t e x : G} (ht : F.Rep t tD)
    (he : F.Rep e eD) (hx : F.Rep x xD) :
    ∃ y ∈ S.M, y * x = x * y ∧ y * (t * e * t * e) * y⁻¹ = S.z * e ∧
      y * e * y⁻¹ = t * e * t := by
  classical
  have hz := hF.rep_z
  have heQ := hF.mem_QG_of_rep_eD hc he
  have hbQ := b1_mem_QG hF hc ht he
  have hH : ∀ {m u : G}, m ∈ S.M → u ∈ S.QG → m * u * m⁻¹ ∈ F.H := fun hm hu =>
    hF.H_eq ▸ hc.QG_le (S.conj_mem_QG hm hu)
  set s := (Set.toFinite ((S.M ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G)).toFinset
    with hs
  have hmem : ∀ {m : G}, m ∈ s ↔ m ∈ S.M ∧ m * x = x * m := by
    intro m
    rw [hs, Set.Finite.mem_toFinset, SetLike.mem_coe, mem_inf]
    exact ⟨fun h => ⟨h.1, mem_centralizer_singleton_iff.mp h.2⟩,
      fun h => ⟨h.1, mem_centralizer_singleton_iff.mpr h.2⟩⟩
  have hcard : 36 ≤ s.card := by
    rw [hs, ← Nat.card_eq_card_finite_toFinset]
    exact le_card_centralizer hF hc hMbar ht hx
  let f : G → (ℕ × ℕ) × (ℕ × ℕ) := fun m =>
    (dataOf F (m * (t * e * t * e) * m⁻¹), dataOf F (m * e * m⁻¹))
  by_contra hne
  have hmaps : ∀ m ∈ s, f m ∈ sol18.toFinset.erase (zeD, tetD) := by
    intro m hm
    obtain ⟨hmM, hmx⟩ := hmem.mp hm
    have hu := rep_dataOf F (hH hmM hbQ)
    have hv := rep_dataOf F (hH hmM heQ)
    refine Finset.mem_erase.mpr ⟨fun hfm => hne ⟨m, hmM, hmx, ?_, ?_⟩, List.mem_toFinset.mpr ?_⟩
    · exact F.eq_of_rep hu (F.rep_congr (F.rep_ze hz he) (congrArg Prod.fst hfm).symm)
    · exact F.eq_of_rep hv (F.rep_congr (F.rep_tet ht he) (congrArg Prod.snd hfm).symm)
    · exact F.mem_sol18_of_relsOKG hx hz hu hv (hF.mem_k1Codes hc (S.conj_mem_QG hmM hbQ) hu)
        (hF.mem_k1Codes hc (S.conj_mem_QG hmM heQ) hv)
        ((F.relsOKG_b1_e hz ht he hx).conj hmx (S.mem_M_iff.mp hmM))
  have hfib : ∀ b ∈ sol18.toFinset.erase (zeD, tetD), (s.filter fun m => f m = b).card ≤ 2 := by
    intro b _
    by_cases hb : ∃ m₀ ∈ s, f m₀ = b
    · obtain ⟨m₀, hm₀, rfl⟩ := hb
      obtain ⟨hm₀M, hm₀x⟩ := hmem.mp hm₀
      refine (Finset.card_le_card fun m hm => ?_).trans
        (Finset.card_le_two (a := m₀) (b := m₀ * S.z))
      obtain ⟨hm, hfm⟩ := Finset.mem_filter.mp hm
      obtain ⟨hmM, hmx⟩ := hmem.mp hm
      have h₁ : m * (t * e * t * e) * m⁻¹ = m₀ * (t * e * t * e) * m₀⁻¹ :=
        F.eq_of_rep (rep_dataOf F (hH hmM hbQ))
          (F.rep_congr (rep_dataOf F (hH hm₀M hbQ)) (congrArg Prod.fst hfm).symm)
      have h₂ : m * e * m⁻¹ = m₀ * e * m₀⁻¹ :=
        F.eq_of_rep (rep_dataOf F (hH hmM heQ))
          (F.rep_congr (rep_dataOf F (hH hm₀M heQ)) (congrArg Prod.snd hfm).symm)
      rcases eq_or_eq_mul_z hF hc ht he hx hmM hmx hm₀M hm₀x h₁ h₂ with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun m hm hfm =>
        hb ⟨m, hm, hfm⟩)]
      norm_num
  have h1 := Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib
  have h17 : (sol18.toFinset.erase (zeD, tetD)).card = 17 := by
    have h0 : (zeD, tetD) ∈ sol18 := alpha0_mem_sol18
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr h0),
      List.toFinset_card_of_nodup nodup_sol18, length_sol18]
  omega

end YCon

end AS62

end CFSG.LargeExtraspecial
