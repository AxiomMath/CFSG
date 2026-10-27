module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Ext4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem diag_two_mul_card_dvd_sup_zpowers {G : Type} [Group G] [Finite G] {M : Subgroup G}
    {s : G} (hs : s * s = 1) (hn : s ∈ normalizer (M : Set G)) (hsM : s ∉ M) :
    2 * Nat.card M ∣ Nat.card ↥(M ⊔ zpowers s) := by
  have hMK : M ≤ M ⊔ zpowers s := le_sup_left
  have hsK : s ∈ M ⊔ zpowers s := mem_sup_right (mem_zpowers s)
  have hKN : M ⊔ zpowers s ≤ normalizer (M : Set G) :=
    sup_le M.le_normalizer ((zpowers_le).2 hn)
  have : (M.subgroupOf (M ⊔ zpowers s)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hMK).2 hKN
  set q : ↥(M ⊔ zpowers s) ⧸ M.subgroupOf (M ⊔ zpowers s) :=
    QuotientGroup.mk (⟨s, hsK⟩ : ↥(M ⊔ zpowers s)) with hq
  have hq2 : q ^ 2 = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simp [pow_two, hs]
  have hq1 : q ≠ 1 := by
    rw [hq, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hsM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (↥(M ⊔ zpowers s) ⧸ M.subgroupOf (M ⊔ zpowers s)) := by
    rw [← orderOf_eq_prime hq2 hq1]
    exact _root_.orderOf_dvd_natCard q
  have h3 := (M.subgroupOf (M ⊔ zpowers s)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hMK).toEquiv] at h3
  obtain ⟨k, hk⟩ := h2
  refine ⟨k, ?_⟩
  rw [← h3, Subgroup.index, hk]
  ring

theorem diag_card_mul_card_dvd_of_central {G : Type} [Group G] [Finite G] {A Z : Subgroup G}
    (hZ : Z ≤ center G) {K : Type} [Group K] (ψ : ↥A →* K) (hψ : Function.Surjective ψ)
    (hker : ∀ c : ↥A, (c : G) ∈ Z → ψ c = 1) :
    Nat.card K * Nat.card Z ∣ Nat.card G := by
  have hc : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := fun a _ z hz =>
    (Subgroup.mem_center_iff.1 (hZ hz)) a
  have hprod := card_sup_mul_card_inf hc
  have h1 : Nat.card ψ.ker * Nat.card K = Nat.card A :=
    Subgroup.card_ker_mul_card_of_surjective hψ
  have h2 : Nat.card ↥(A ⊓ Z) ∣ Nat.card ψ.ker := by
    have hle : (A ⊓ Z).subgroupOf A ≤ ψ.ker := fun c hc =>
      (MonoidHom.mem_ker).2 (hker c (mem_inf.1 (mem_subgroupOf.1 hc)).2)
    rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A ⊓ Z ≤ A)).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨r, hr⟩ := h2
  have hpos : 0 < Nat.card ↥(A ⊓ Z) := Nat.card_pos
  have h3 : Nat.card ↥(A ⊔ Z) = r * Nat.card K * Nat.card Z := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card ↥(A ⊔ Z) * Nat.card ↥(A ⊓ Z) = Nat.card A * Nat.card Z := hprod
      _ = (Nat.card ψ.ker * Nat.card K) * Nat.card Z := by rw [h1]
      _ = r * Nat.card K * Nat.card Z * Nat.card ↥(A ⊓ Z) := by rw [hr]; ring
  have h4 : Nat.card K * Nat.card Z ∣ Nat.card ↥(A ⊔ Z) :=
    ⟨r, by rw [h3]; ring⟩
  exact h4.trans (Subgroup.card_subgroup_dvd_card _)

theorem diag_card_mul_card_center_dvd {G₀ H : Type} [Group G₀] [Finite G₀] [Group H]
    (δ : G₀ →* H) {Mb : Subgroup H} (hsd : Mb ≤ δ.range) {K : Type} [Group K]
    (e : ↥Mb ⧸ center ↥Mb ≃* K) :
    Nat.card K * Nat.card (center G₀) ∣ Nat.card G₀ := by
  let φ : ↥(Mb.comap δ) →* ↥Mb := δ.subgroupComap Mb
  have hφ : Function.Surjective φ := fun m => by
    obtain ⟨l, hl⟩ := hsd m.2
    exact ⟨⟨l, by rw [mem_comap, hl]; exact m.2⟩, Subtype.ext hl⟩
  let ψ : ↥(Mb.comap δ) →* K :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (center ↥Mb)).comp φ)
  have hψ : Function.Surjective ψ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hφ)
  refine diag_card_mul_card_dvd_of_central le_rfl ψ hψ fun c hc => ?_
  have hψc : ψ c = e (QuotientGroup.mk (φ c)) := rfl
  rw [hψc, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, mem_center_iff]
  intro m
  obtain ⟨l, hl⟩ := hsd m.2
  apply Subtype.ext
  have hlc : l * c = c * l := mem_center_iff.1 hc l
  show (m : H) * δ c = δ c * (m : H)
  rw [← hl, ← map_mul, ← map_mul, hlc]

theorem diag_mem_conjSub {G : Type*} [Group G] {g x : G} {K : Subgroup G} :
    x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem diag_normalizer_sup_zpowers {G : Type*} [Group G] {t w : G} {N : Subgroup G}
    (htn : t ∈ normalizer (N : Set G)) (hw : w ∈ center G) :
    t ∈ normalizer ((N ⊔ zpowers w : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at htn ⊢
  have hcw : (MulAut.conj t) w = w := by
    rw [MulAut.conj_apply, mem_center_iff.1 hw t, mul_inv_cancel_right]
  rw [Subgroup.map_sup, htn, MonoidHom.map_zpowers]
  simp [hcw]

section Geometry

variable {H : Type} [Group H] {t : H} {L : Subgroup H}

theorem diag_mem_normalizer_sup (ht : t * t = 1) :
    t ∈ normalizer ((L ⊔ conjSub t⁻¹ L : Subgroup H) : Set H) := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hLL : conjSub t⁻¹ (conjSub t⁻¹ L) = L := by
    have := conjSub_inv_conjSub t L
    rw [ht'] at this ⊢
    exact this
  have h : t⁻¹ ∈ normalizer ((L ⊔ conjSub t⁻¹ L : Subgroup H) : Set H) := by
    rw [mem_normalizer_iff_map_conj_eq]
    have h1 : conjSub t⁻¹ (L ⊔ conjSub t⁻¹ L) = conjSub t⁻¹ L ⊔ conjSub t⁻¹ (conjSub t⁻¹ L) :=
      Subgroup.map_sup _ _ _
    change conjSub t⁻¹ (L ⊔ conjSub t⁻¹ L) = L ⊔ conjSub t⁻¹ L
    rw [h1, hLL, sup_comm]
  have h' := inv_mem h
  rw [inv_inv] at h'
  exact h'

theorem diag_sup_le_normalizer (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥) :
    L ⊔ conjSub t⁻¹ L ≤ normalizer (L : Set H) :=
  sup_le L.le_normalizer fun _ hy => centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun _ hh => commute_of_commutator_conj_eq_bot hAB hh hy)

theorem diag_not_mem_normalizer (hne : conjSub t⁻¹ L ≠ L) : t ∉ normalizer (L : Set H) := by
  intro h
  exact hne (mem_normalizer_iff_map_conj_eq.1 (inv_mem h))

theorem diag_card_inf_dvd (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥) :
    Nat.card ↥(L ⊓ conjSub t⁻¹ L) ∣ Nat.card (center ↥L) := by
  have hle : (L ⊓ conjSub t⁻¹ L).subgroupOf L ≤ center ↥L := fun x hx =>
    mem_center_iff.2 fun y =>
      Subtype.ext (commute_of_commutator_conj_eq_bot hAB y.2 (mem_inf.1 (mem_subgroupOf.1 hx)).2)
  rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : L ⊓ conjSub t⁻¹ L ≤ L)).toEquiv]
  exact Subgroup.card_dvd_of_le hle

theorem diag_orderOf_dvd_center {a : H} (ha : a ∈ L) (hc : ∀ x ∈ L, x * a = a * x) :
    orderOf a ∣ Nat.card (center ↥L) := by
  have hmem : (⟨a, ha⟩ : ↥L) ∈ center ↥L := mem_center_iff.2 fun y => Subtype.ext (hc y y.2)
  have h := Subgroup.orderOf_dvd_natCard (center ↥L) hmem
  rw [Subgroup.orderOf_mk] at h
  exact h

theorem diag_w_not_mem_sup {w : H} (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥)
    (hw : w ∈ center H) (hw2 : orderOf w = 2) (hZ : Odd (Nat.card (center ↥L))) :
    w ∉ L ⊔ conjSub t⁻¹ L := by
  intro hwN
  rw [← SetLike.mem_coe, coe_sup_conjSub hAB] at hwN
  obtain ⟨a, ha, b, hb, hab⟩ := hwN
  have hcomm : ∀ x ∈ L, ∀ y ∈ conjSub t⁻¹ L, x * y = y * x := fun x hx y hy =>
    commute_of_commutator_conj_eq_bot hAB hx hy
  have hwc : ∀ x : H, x * w = w * x := fun x => mem_center_iff.1 hw x
  have haZ : ∀ x ∈ L, x * a = a * x := by
    intro x hx
    have ha' : a = w * b⁻¹ := by rw [← hab]; group
    rw [ha']
    calc x * (w * b⁻¹) = (x * w) * b⁻¹ := by rw [mul_assoc]
      _ = w * (x * b⁻¹) := by rw [hwc x, mul_assoc]
      _ = w * (b⁻¹ * x) := by rw [hcomm x hx b⁻¹ (inv_mem hb)]
      _ = w * b⁻¹ * x := by rw [mul_assoc]
  have hbZ : ∀ y ∈ conjSub t⁻¹ L, y * b = b * y := by
    intro y hy
    have hb' : b = a⁻¹ * w := by rw [← hab]; group
    rw [hb']
    calc y * (a⁻¹ * w) = (y * a⁻¹) * w := by rw [mul_assoc]
      _ = (a⁻¹ * y) * w := by rw [← hcomm a⁻¹ (inv_mem ha) y hy]
      _ = a⁻¹ * (y * w) := by rw [mul_assoc]
      _ = a⁻¹ * (w * y) := by rw [hwc y]
      _ = a⁻¹ * w * y := by rw [mul_assoc]
  have hb0L : t * b * t⁻¹ ∈ L := by
    have h := (diag_mem_conjSub (g := t⁻¹)).1 hb
    rw [inv_inv] at h
    exact h
  have hb0 : ∀ x ∈ L, x * (t * b * t⁻¹) = (t * b * t⁻¹) * x := by
    intro x hx
    have hy := hbZ (t⁻¹ * x * t) (conj_mem_conjSub hx)
    calc x * (t * b * t⁻¹) = t * ((t⁻¹ * x * t) * b) * t⁻¹ := by group
      _ = t * (b * (t⁻¹ * x * t)) * t⁻¹ := by rw [hy]
      _ = (t * b * t⁻¹) * x := by group
  have hoa : orderOf a ∣ Nat.card (center ↥L) := diag_orderOf_dvd_center ha haZ
  have hob : orderOf b ∣ Nat.card (center ↥L) := by
    have h := diag_orderOf_dvd_center hb0L hb0
    have hord : orderOf (t * b * t⁻¹) = orderOf b := by
      have h' := MulEquiv.orderOf_eq (MulAut.conj t) b
      simpa [MulAut.conj_apply] using h'
    rw [hord] at h
    exact h
  have hcab : Commute a b := hcomm a ha b hb
  have h1 : a ^ (orderOf a * orderOf b) = 1 := by rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have h2 : b ^ (orderOf a * orderOf b) = 1 := by
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hpow : w ^ (orderOf a * orderOf b) = 1 := by
    rw [← hab, hcab.mul_pow, h1, h2, mul_one]
  have h2' : 2 ∣ orderOf a * orderOf b := hw2 ▸ orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2' with h | h
  · exact (Nat.not_even_iff_odd.2 (hZ.of_dvd_nat hoa)) (even_iff_two_dvd.2 h)
  · exact (Nat.not_even_iff_odd.2 (hZ.of_dvd_nat hob)) (even_iff_two_dvd.2 h)

end Geometry

theorem diag_false {H : Type} [Group H] [Finite H] {t w : H} (ht : t * t = 1) (hw : w ∈ center H)
    (hw2 : orderOf w = 2) (h8 : ¬ 2 ^ 8 ∣ Nat.card H) {L : Subgroup H}
    (hne : conjSub t⁻¹ L ≠ L) (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥) {Mb : Subgroup H}
    (hMb : ⁅Mb, Mb⁆ = Mb) (hsd : Mb ≤ (swapDiag hAB).range)
    (hA7 : Nonempty (↥Mb ⧸ center ↥Mb ≃* alternatingGroup (Fin 7)))
    (hZodd : Odd (Nat.card (center ↥Mb))) : False := by
  have _ := And.intro hMb hZodd
  obtain ⟨e⟩ := hA7
  have hcard7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h1 := diag_card_mul_card_center_dvd (swapDiag hAB) hsd e
  rw [hcard7] at h1
  have h8Z : 8 * Nat.card (center ↥L) ∣ Nat.card ↥L :=
    (mul_dvd_mul_right (by norm_num : 8 ∣ 2520) _).trans h1
  have hprod := card_sup_mul_card_inf
    (fun a ha b hb => commute_of_commutator_conj_eq_bot hAB ha hb)
  rw [card_conjSub] at hprod
  have hq : 0 < Nat.card ↥(L ⊓ conjSub t⁻¹ L) := Nat.card_pos
  have h64 : 64 * Nat.card (center ↥L) ∣ Nat.card ↥(L ⊔ conjSub t⁻¹ L) := by
    apply Nat.dvd_of_mul_dvd_mul_right hq
    rw [hprod]
    calc 64 * Nat.card (center ↥L) * Nat.card ↥(L ⊓ conjSub t⁻¹ L)
        ∣ 64 * Nat.card (center ↥L) * Nat.card (center ↥L) :=
          mul_dvd_mul_left _ (diag_card_inf_dvd hAB)
      _ = (8 * Nat.card (center ↥L)) * (8 * Nat.card (center ↥L)) := by ring
      _ ∣ Nat.card ↥L * Nat.card ↥L := mul_dvd_mul h8Z h8Z
  have htN : t ∉ L ⊔ conjSub t⁻¹ L := fun h =>
    diag_not_mem_normalizer hne (diag_sup_le_normalizer hAB h)
  have htnorm := diag_mem_normalizer_sup (L := L) ht
  rcases Nat.even_or_odd (Nat.card (center ↥L)) with hev | hodd
  · have h128 : 128 ∣ Nat.card ↥(L ⊔ conjSub t⁻¹ L) :=
      (mul_dvd_mul_left 64 (even_iff_two_dvd.1 hev) :
        64 * 2 ∣ 64 * Nat.card (center ↥L)).trans h64
    have h256 : 2 * 128 ∣ Nat.card H :=
      (mul_dvd_mul_left 2 h128).trans
        ((diag_two_mul_card_dvd_sup_zpowers ht htnorm htN).trans
          (Subgroup.card_subgroup_dvd_card _))
    exact h8 (by norm_num; exact h256)
  · have hwN : w ∉ L ⊔ conjSub t⁻¹ L := diag_w_not_mem_sup hAB hw hw2 hodd
    have hw1 : w * w = 1 := by rw [← sq, ← hw2]; exact pow_orderOf_eq_one w
    have hwn : w ∈ normalizer ((L ⊔ conjSub t⁻¹ L : Subgroup H) : Set H) :=
      center_le_normalizer _ hw
    have hA := diag_two_mul_card_dvd_sup_zpowers hw1 hwn hwN
    have htL1 : t ∉ (L ⊔ conjSub t⁻¹ L) ⊔ zpowers w := fun h =>
      diag_not_mem_normalizer hne
        ((sup_le (diag_sup_le_normalizer hAB) ((zpowers_le).2 (center_le_normalizer _ hw))) h)
    have hB := diag_two_mul_card_dvd_sup_zpowers ht (diag_normalizer_sup_zpowers htnorm hw) htL1
    have h64' : 64 ∣ Nat.card ↥(L ⊔ conjSub t⁻¹ L) := (dvd_mul_right 64 _).trans h64
    have h256 : 4 * 64 ∣ Nat.card H := by
      refine (mul_dvd_mul_left 4 h64').trans ?_
      calc 4 * Nat.card ↥(L ⊔ conjSub t⁻¹ L)
          = 2 * (2 * Nat.card ↥(L ⊔ conjSub t⁻¹ L)) := by ring
        _ ∣ 2 * Nat.card ↥((L ⊔ conjSub t⁻¹ L) ⊔ zpowers w) := mul_dvd_mul_left 2 hA
        _ ∣ Nat.card ↥(((L ⊔ conjSub t⁻¹ L) ⊔ zpowers w) ⊔ zpowers t) := hB
        _ ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
    exact h8 (by norm_num; exact h256)

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
