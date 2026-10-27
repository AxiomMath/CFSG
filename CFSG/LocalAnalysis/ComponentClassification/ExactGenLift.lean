module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9Defs

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv
open scoped commutatorElement

section ZStar

variable {P : Type} [Group P]

private theorem mem_zStar_iff (z : P) :
    z ∈ Open.fusionZStar P ↔ ∀ p : P, (p * z)⁻¹ * (z * p) ∈ pPrimeCore 2 P := by
  rw [Sol78.fusionZStar_eq_comap, mem_comap, Subgroup.mem_center_iff]
  constructor
  · intro h p
    have := h (QuotientGroup.mk p)
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at this
    exact this
  · intro h q
    induction q using QuotientGroup.induction_on with
    | H p =>
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq]
      exact h p

private theorem apply_mem_pPrimeCore (x : MulAut P) {a : P} (ha : a ∈ pPrimeCore 2 P) :
    x a ∈ pPrimeCore 2 P :=
  Subgroup.characteristic_iff_le_comap.mp
    (pPrimeCore_characteristic (p := 2) (G := P)) x ha

private theorem mem_zStar_map (x : MulAut P) {z : P} (hz : z ∈ Open.fusionZStar P) :
    x z ∈ Open.fusionZStar P := by
  rw [mem_zStar_iff] at hz ⊢
  intro p
  have h := apply_mem_pPrimeCore x (hz (x.symm p))
  convert h using 1
  simp

private theorem map_zStar_eq (x : MulAut P) :
    (Open.fusionZStar P).map (x : P →* P) = Open.fusionZStar P := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact mem_zStar_map x hz
  · intro z hz
    exact ⟨x.symm z, mem_zStar_map x.symm hz, by simp⟩

private noncomputable def zBar (x : MulAut P) : MulAut (P ⧸ Open.fusionZStar P) :=
  QuotientGroup.congr (Open.fusionZStar P) (Open.fusionZStar P) x (map_zStar_eq x)

private theorem zBar_mk (x : MulAut P) (p : P) :
    zBar x (QuotientGroup.mk p) = QuotientGroup.mk (x p) :=
  QuotientGroup.congr_mk _ _ x _ p

private theorem zBar_sq (x : MulAut P) (hx : x * x = 1) : zBar x * zBar x = 1 := by
  ext g
  induction g using QuotientGroup.induction_on with
  | H p =>
    show zBar x (zBar x (QuotientGroup.mk p)) = QuotientGroup.mk p
    rw [zBar_mk, zBar_mk]
    have := DFunLike.congr_fun hx p
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [this]

private theorem zBar_conj_mul (u : P) (x : MulAut P) :
    zBar (MulAut.conj u * x) =
      MulAut.conj (QuotientGroup.mk u : P ⧸ Open.fusionZStar P) * zBar x := by
  ext g
  induction g using QuotientGroup.induction_on with
  | H p =>
    show zBar (MulAut.conj u * x) (QuotientGroup.mk p) =
      MulAut.conj (QuotientGroup.mk u : P ⧸ Open.fusionZStar P) (zBar x (QuotientGroup.mk p))
    rw [zBar_mk, zBar_mk]
    simp [MulAut.conj_apply]

private theorem lift_fixed [Finite P] (x : MulAut P) (hx : x * x = 1) (g₁ : P)
    (hfix : (QuotientGroup.mk (x g₁) : P ⧸ Open.fusionZStar P) = QuotientGroup.mk g₁)
    (hodd : Odd (orderOf (QuotientGroup.mk g₁ : P ⧸ Open.fusionZStar P))) :
    ∃ h : P, (QuotientGroup.mk h : P ⧸ Open.fusionZStar P) = QuotientGroup.mk g₁ ∧
      x h = h := by
  classical
  have hxx : ∀ p : P, x (x p) = p := fun p => by
    have := DFunLike.congr_fun hx p
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ Open.fusionZStar P, x g₁ = g₁ * z := by
    refine ⟨g₁⁻¹ * x g₁, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hfix,
      inv_mul_cancel]
  set O := pPrimeCore 2 P with hO
  have hcen : ∀ y : P ⧸ O, y * QuotientGroup.mk' O z = QuotientGroup.mk' O z * y := by
    have h := hzZ
    rw [Sol78.fusionZStar_eq_comap, mem_comap] at h
    exact Subgroup.mem_center_iff.mp h
  have hcomm : ∀ y : P ⧸ O, Commute y (QuotientGroup.mk' O z) := hcen
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₁).ne'
  have hzpow : (QuotientGroup.mk' O z) ^ (orderOf g₁) = 1 := by
    have h1 : (QuotientGroup.mk' O (x g₁)) ^ (orderOf g₁) = 1 := by
      rw [← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
    rw [hz, map_mul, (hcomm _).mul_pow, ← map_pow, pow_orderOf_eq_one, map_one, one_mul] at h1
    exact h1
  have hz2 : (QuotientGroup.mk' O z) ^ (2 ^ k) = 1 := by
    have hfin : Finite (P ⧸ O) := inferInstance
    have hpg : IsPGroup 2 (center (P ⧸ O)) :=
      Sol78.center_isPGroup_two (pPrimeCore_quotient_eq_bot Nat.prime_two)
    have hwc : (QuotientGroup.mk' O z) ^ (2 ^ k) ∈ center (P ⧸ O) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact ((hcomm y).pow_right (2 ^ k)).eq
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hpg) ⟨_, hwc⟩
    have hdvd : orderOf ((QuotientGroup.mk' O z) ^ (2 ^ k)) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, ← hkm]
      exact hzpow
    have hj' : orderOf ((QuotientGroup.mk' O z) ^ (2 ^ k)) = 2 ^ j := by
      rw [← hj, Subgroup.orderOf_mk]
    rw [hj'] at hdvd
    have hj0 : j = 0 := by
      by_contra hne
      have : 2 ∣ m := (dvd_pow_self 2 hne).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr this)
    rw [hj0, pow_zero] at hj'
    exact orderOf_eq_one_iff.mp hj'
  have hcop : Nat.Coprime (2 ^ k) (orderOf (QuotientGroup.mk g₁ : P ⧸ Open.fusionZStar P)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨c, hc0, hc1⟩ := Nat.chineseRemainder hcop 0 1
  obtain ⟨c', hc'⟩ : 2 ^ k ∣ c := (Nat.modEq_zero_iff_dvd.mp hc0)
  set g₂ : P := g₁ ^ c with hg₂
  have hg₂mk : (QuotientGroup.mk g₂ : P ⧸ Open.fusionZStar P) = QuotientGroup.mk g₁ := by
    rw [hg₂, QuotientGroup.mk_pow]
    have := (pow_eq_pow_iff_modEq (x := (QuotientGroup.mk g₁ : P ⧸ Open.fusionZStar P))
      (n := c) (m := 1)).mpr hc1
    rwa [pow_one] at this
  have hzc : (QuotientGroup.mk' O z) ^ c = 1 := by
    rw [hc', pow_mul, hz2, one_pow]
  have ho₀ : g₂⁻¹ * x g₂ ∈ O := by
    rw [← QuotientGroup.eq]
    show QuotientGroup.mk' O g₂ = QuotientGroup.mk' O (x g₂)
    rw [hg₂, map_pow, map_pow, hz, map_pow, map_mul, (hcomm _).mul_pow, hzc, mul_one]
  set o₀ : P := g₂⁻¹ * x g₂ with ho₀def
  have hxo₀ : o₀ * x o₀ = 1 := by
    rw [ho₀def, map_mul, map_inv, hxx]
    group
  let φ : ↥O → ↥O := fun o => ⟨o₀ * x o, O.mul_mem ho₀ (apply_mem_pPrimeCore x o.2)⟩
  have hφ : Function.Involutive φ := by
    intro o
    apply Subtype.ext
    show o₀ * x (o₀ * x o) = o
    rw [map_mul, hxx, ← mul_assoc, hxo₀, one_mul]
  have hOdd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := P))
  haveI : Fintype ↥O := Fintype.ofFinite _
  have hσ : (hφ.toPerm φ) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact Equiv.ext fun o => hφ o
  obtain ⟨o, ho⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
    (by rw [← Nat.card_eq_fintype_card]; exact hOdd.not_two_dvd_nat) hσ
  have ho' : o₀ * x o = o := congrArg Subtype.val ho
  refine ⟨g₂ * o, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, hg₂mk]
    have : (QuotientGroup.mk (o : P) : P ⧸ Open.fusionZStar P) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Sol78.pPrimeCore_le_fusionZStar P o.2)
    rw [this, mul_one]
  · have h1 : x g₂ = g₂ * o₀ := by rw [ho₀def]; group
    rw [map_mul, h1, mul_assoc, ho']

end ZStar

section Involution

private theorem exists_invol_not_ker {H : Type} [Group H] [Finite H]
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (hker : ∀ v : H, q v = 1 → Odd (orderOf v)) :
    ∃ u : H, u * u = 1 ∧ q u ≠ 1 := by
  classical
  have hdvd : 2 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; decide
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 2 hdvd
  have hx₀sq : x₀ ^ 2 = 1 := by rw [← hx₀]; exact pow_orderOf_eq_one x₀
  have hx₀ne : x₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hx₀; omega
  obtain ⟨l, hl⟩ := hq x₀
  obtain ⟨k, m, hm, hlm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  have hu₀k : (l ^ m) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hlm, pow_orderOf_eq_one]
  have hqu₀ : q (l ^ m) = x₀ := by
    rw [map_pow, hl, pow_eq_pow_mod m hx₀sq, Nat.odd_iff.mp hm, pow_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu₀k)
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
    cases j with
    | zero =>
      exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hj
      apply hx₀ne
      rw [← hqu₀, hj, map_one]
    | succ j' => exact ⟨j', rfl⟩
  rcases Nat.eq_zero_or_pos j' with hj0 | hj0
  · subst hj0
    refine ⟨l ^ m, ?_, by rw [hqu₀]; exact hx₀ne⟩
    have hj2 : orderOf (l ^ m) = 2 := by simpa using hj
    have h := pow_orderOf_eq_one (l ^ m)
    rw [hj2] at h
    rw [← sq]
    exact h
  · exfalso
    obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
    set u : H := (l ^ m) ^ (2 ^ (j'' + 1)) with hu
    have hu2 : u ^ 2 = 1 := by
      rw [hu, ← pow_mul, ← pow_succ]
      rw [← hj]
      exact pow_orderOf_eq_one _
    have hune : u ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
      rw [hj]
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
    have hqu : q u = 1 := by
      rw [hu, map_pow, hqu₀, pow_succ', pow_mul, hx₀sq, one_pow]
    have hord : orderOf u = 2 := orderOf_eq_prime hu2 hune
    have := hker u hqu
    rw [hord] at this
    exact (by decide : ¬ Odd 2) this

private theorem exists_good_involution {P : Type} [Group P] [Finite P] {L : Subgroup P}
    (hLA : Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 5))) :
    ∃ u : P, u ∈ L ∧ u * u = 1 ∧ u ∉ Open.fusionZStar P := by
  classical
  obtain ⟨e⟩ := hLA
  set q : ↥L →* alternatingGroup (Fin 5) :=
    (e : _ →* _).comp (QuotientGroup.mk' (pPrimeCore 2 ↥L)) with hq
  have hqsurj : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : ∀ v : ↥L, q v = 1 ↔ v ∈ pPrimeCore 2 ↥L := by
    intro v
    show e (QuotientGroup.mk v) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hker : ∀ v : ↥L, q v = 1 → Odd (orderOf v) := by
    intro v hv
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥L))
    exact hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ((hqker v).mp hv))
  obtain ⟨u, hu2, hu1⟩ := exists_invol_not_ker q hqsurj hker
  refine ⟨u, u.2, by simpa using congrArg Subtype.val hu2, ?_⟩
  intro huZ
  apply hu1
  have hR : (pPrimeCore 2 P).comap L.subtype ≤ pPrimeCore 2 ↥L := by
    apply le_pPrimeCore_of_normal_coprime
    · exact Subgroup.Normal.comap inferInstance L.subtype
    · have hd := Subgroup.card_comap_dvd_of_injective (pPrimeCore 2 P) L.subtype
        L.subtype_injective
      exact Nat.Coprime.coprime_dvd_right hd (pPrimeCore_coprime_card (p := 2) (G := P))
  have hcen : q u ∈ center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨l, rfl⟩ := hqsurj b
    have hc : (l * u)⁻¹ * (u * l) ∈ pPrimeCore 2 ↥L := by
      apply hR
      rw [Subgroup.mem_comap]
      have := (mem_zStar_iff _).mp huZ (l : P)
      simpa using this
    have h1 := (hqker _).mpr hc
    rw [map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h1
    exact h1
  rw [alternatingGroup.center_eq_bot (by simp)] at hcen
  exact Subgroup.mem_bot.mp hcen

end Involution

section Generation

@[expose] def ExactCore (S : Type) [Group S] : Prop :=
  ∀ (τ : MulAut S), τ * τ = 1 → ∀ ε : S, ε * ε = 1 → ε ≠ 1 → ∀ E : Subgroup S, ⁅E, E⁆ = E →
    (∀ e ∈ E, τ e = e) → ε ∈ E → ∀ Ghat : Subgroup S,
    (∀ g : S, τ g = g → Odd (orderOf g) → g ∈ Ghat) →
    (∀ g : S, (MulAut.conj ε * τ) g = g → Odd (orderOf g) → g ∈ Ghat) → Ghat = ⊤

private theorem comm_mul_central {Q : Type*} [Group Q] {a b c d : Q}
    (hc : ∀ y, c * y = y * c) (hd : ∀ y, d * y = y * d) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹ =
      a * (c * (b * d) * c⁻¹) * a⁻¹ * (b * d)⁻¹ := by group
  have e2 : c * (b * d) * c⁻¹ = b * d := by rw [hc (b * d)]; group
  have e3 : a * (b * d) * a⁻¹ * (b * d)⁻¹ = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by group
  have e4 : d * a⁻¹ * d⁻¹ = a⁻¹ := by rw [hd a⁻¹]; group
  rw [e1, e2, e3, e4]

private theorem eq_top_of_map_eq_top {P : Type} [Group P] [Group.IsPerfect P] (G : Subgroup P)
    (hO : pPrimeCore 2 P ≤ G)
    (hG : G.map (QuotientGroup.mk' (Open.fusionZStar P)) = ⊤) : G = ⊤ := by
  have dec : ∀ p : P, ∃ g ∈ G, ∃ z ∈ Open.fusionZStar P, p = g * z := by
    intro p
    have hp : QuotientGroup.mk' (Open.fusionZStar P) p ∈
        G.map (QuotientGroup.mk' (Open.fusionZStar P)) := by
      rw [hG]; exact mem_top _
    obtain ⟨g, hg, hgp⟩ := Subgroup.mem_map.mp hp
    refine ⟨g, hg, g⁻¹ * p, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have : (QuotientGroup.mk g : P ⧸ Open.fusionZStar P) = QuotientGroup.mk p := hgp
    rw [this, inv_mul_cancel]
  have hcen : ∀ z ∈ Open.fusionZStar P, ∀ y : P ⧸ pPrimeCore 2 P,
      QuotientGroup.mk' (pPrimeCore 2 P) z * y = y * QuotientGroup.mk' (pPrimeCore 2 P) z := by
    intro z hz y
    rw [Sol78.fusionZStar_eq_comap, mem_comap] at hz
    exact (Subgroup.mem_center_iff.mp hz y).symm
  have hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ G := by
    rw [Subgroup.commutator_le]
    intro p₁ _ p₂ _
    obtain ⟨g₁, hg₁, z₁, hz₁, rfl⟩ := dec p₁
    obtain ⟨g₂, hg₂, z₂, hz₂, rfl⟩ := dec p₂
    have key : QuotientGroup.mk' (pPrimeCore 2 P) ⁅g₁ * z₁, g₂ * z₂⁆ =
        QuotientGroup.mk' (pPrimeCore 2 P) ⁅g₁, g₂⁆ := by
      rw [map_commutatorElement, map_commutatorElement, map_mul, map_mul]
      exact comm_mul_central (hcen z₁ hz₁) (hcen z₂ hz₂)
    have hmem : (⁅g₁, g₂⁆)⁻¹ * ⁅g₁ * z₁, g₂ * z₂⁆ ∈ pPrimeCore 2 P :=
      QuotientGroup.eq.mp key.symm
    have hg : ⁅g₁, g₂⁆ ∈ G := by
      rw [commutatorElement_def]
      exact G.mul_mem (G.mul_mem (G.mul_mem hg₁ hg₂) (G.inv_mem hg₁)) (G.inv_mem hg₂)
    have : ⁅g₁ * z₁, g₂ * z₂⁆ = ⁅g₁, g₂⁆ * ((⁅g₁, g₂⁆)⁻¹ * ⁅g₁ * z₁, g₂ * z₂⁆) := by group
    rw [this]
    exact G.mul_mem hg (hO hmem)
  rw [eq_top_iff]
  have h : ⁅(⊤ : Subgroup P), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top (G := P)
  rw [← h]
  exact hcomm

private theorem gen_of_core {P : Type} [Group P] [Finite P] [Group.IsPerfect P]
    (hcore : ExactCore (P ⧸ Open.fusionZStar P))
    (x₁ : MulAut P) (hx₁ : x₁ * x₁ = 1)
    (L : Subgroup P) (hLp : ⁅L, L⁆ = L) (hLfix : ∀ l ∈ L, x₁ l = l)
    (hLA : Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 5)))
    (G : Subgroup P) (hO : pPrimeCore 2 P ≤ G)
    (hG : ∀ u ∈ L, u * u = 1 → ∀ h : P, u * x₁ h * u⁻¹ = h → h ∈ G) : G = ⊤ := by
  obtain ⟨u, huL, huu, huZ⟩ := exists_good_involution (P := P) hLA
  have hxx₁ : ∀ p : P, x₁ (x₁ p) = p := fun p => by
    have := DFunLike.congr_fun hx₁ p
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hx₂sq : (MulAut.conj u * x₁) * (MulAut.conj u * x₁) = 1 := by
    have key : ∀ q : P, (MulAut.conj u * x₁) ((MulAut.conj u * x₁) q) = q := by
      intro q
      have h1 : ∀ r : P, (MulAut.conj u * x₁) r = u * x₁ r * u⁻¹ := fun r => rfl
      rw [h1, h1, map_mul, map_mul, hLfix u huL, hxx₁, map_inv, hLfix u huL, hui]
      calc u * (u * q * u) * u = (u * u) * q * (u * u) := by group
        _ = q := by rw [huu]; simp
    ext q
    exact key q
  have hE : ⁅L.map (QuotientGroup.mk' (Open.fusionZStar P)),
      L.map (QuotientGroup.mk' (Open.fusionZStar P))⁆ =
      L.map (QuotientGroup.mk' (Open.fusionZStar P)) := by
    rw [← Subgroup.map_commutator, hLp]
  have hGhat : (G.map (QuotientGroup.mk' (Open.fusionZStar P))) = ⊤ := by
    refine hcore (zBar x₁) (zBar_sq x₁ hx₁) (QuotientGroup.mk u) ?_ ?_
      (L.map (QuotientGroup.mk' (Open.fusionZStar P))) hE ?_ ?_
      (G.map (QuotientGroup.mk' (Open.fusionZStar P))) ?_ ?_
    · rw [← QuotientGroup.mk_mul, huu, QuotientGroup.mk_one]
    · exact fun h => huZ ((QuotientGroup.eq_one_iff u).mp h)
    · rintro _ ⟨l, hl, rfl⟩
      show zBar x₁ (QuotientGroup.mk l) = QuotientGroup.mk l
      rw [zBar_mk, hLfix l hl]
    · exact ⟨u, huL, rfl⟩
    · intro g hg hodd
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective g
      rw [zBar_mk] at hg
      obtain ⟨h, hh1, hh2⟩ := lift_fixed x₁ hx₁ p hg hodd
      refine ⟨h, hG 1 (one_mem L) (mul_one 1) h (by simpa using hh2), hh1⟩
    · intro g hg hodd
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective g
      have h2 : zBar (MulAut.conj u * x₁) (QuotientGroup.mk p) = QuotientGroup.mk p := by
        rw [zBar_conj_mul]; exact hg
      rw [zBar_mk] at h2
      obtain ⟨h, hh1, hh2⟩ := lift_fixed (MulAut.conj u * x₁) hx₂sq p h2 hodd
      refine ⟨h, hG u huL huu h ?_, hh1⟩
      simpa only [MulAut.mul_apply, MulAut.conj_apply] using hh2
  exact eq_top_of_map_eq_top G hO hGhat

private noncomputable def invAut {X : Type} [Group X] (N : Subgroup X) (t : X) (htt : t * t = 1)
    (hN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) : MulAut ↥N where
  toFun n := ⟨t * n * t⁻¹, hN n n.2⟩
  invFun n := ⟨t * n * t⁻¹, hN n n.2⟩
  left_inv n := by
    apply Subtype.ext
    have h : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    show t * (t * (n : X) * t⁻¹) * t⁻¹ = n
    rw [h]
    calc t * (t * (n : X) * t) * t = (t * t) * n * (t * t) := by group
      _ = n := by rw [htt]; simp
  right_inv n := by
    apply Subtype.ext
    have h : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    show t * (t * (n : X) * t⁻¹) * t⁻¹ = n
    rw [h]
    calc t * (t * (n : X) * t) * t = (t * t) * n * (t * t) := by group
      _ = n := by rw [htt]; simp
  map_mul' a b := by
    apply Subtype.ext
    show t * ((a : X) * (b : X)) * t⁻¹ = t * (a : X) * t⁻¹ * (t * (b : X) * t⁻¹)
    group

private theorem invAut_sq {X : Type} [Group X] (N : Subgroup X) (t : X) (htt : t * t = 1)
    (hN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) : invAut N t htt hN * invAut N t htt hN = 1 := by
  ext n
  have h : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  show t * (t * (n : X) * t⁻¹) * t⁻¹ = n
  rw [h]
  calc t * (t * (n : X) * t) * t = (t * t) * n * (t * t) := by group
    _ = n := by rw [htt]; simp

theorem exactGenerationInput_of_core
    (hU : ∀ (S : Type) [Group S] [Finite S], Blueprint.LieModel S .PSU 3 5 1 → ExactCore S)
    (hP : ∀ (S : Type) [Group S] [Finite S], Blueprint.LieModel S .PSp 2 5 1 → ExactCore S)
    (hJ : ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .J2) → ExactCore S) :
    ExactGenerationInput := by
  intro X _ _ Y N L t hNY hNpc htY hto hNt hLN hLC hLpc hLA _ _ hout G hGN hcG hLG hcent
  have ht2 : t ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one t
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have hExact : ExactCore (↥N ⧸ Open.fusionZStar ↥N) := by
    rcases hout with h | h | h
    · exact hU _ h
    · exact hP _ h
    · exact hJ _ h
  haveI : Group.IsPerfect ↥N := GSThmB.B5a.isPerfect_of_isPComponent_subgroupOf hNY hNpc
  have htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    intro n hn
    have h : (MulAut.conj t) n ∈ conjBy N t := Subgroup.mem_map_of_mem _ hn
    rw [hNt] at h
    simpa [MulAut.conj_apply] using h
  have hLperf : Group.IsPerfect ↥L :=
    GSThmB.B5a.isPerfect_of_isPComponent_subgroupOf (le_inf (hLN.trans hNY) hLC) hLpc
  have hperfL' : ⁅L.subgroupOf N, L.subgroupOf N⁆ = L.subgroupOf N := by
    have : Group.IsPerfect ↥(L.subgroupOf N) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLN).symm.toMonoidHom)
        (subgroupOfEquivOfLe hLN).symm.surjective
    exact Subgroup.isPerfect_iff.mp this
  have hLA' : Nonempty (↥(L.subgroupOf N) ⧸ pPrimeCore 2 ↥(L.subgroupOf N) ≃*
      alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := hLA
    exact ⟨(Sol78.coreQuotCongr (subgroupOfEquivOfLe hLN)).trans e⟩
  have hfix : ∀ l ∈ L.subgroupOf N, invAut N t htt htN l = l := by
    intro l hl
    have hl' : (l : X) ∈ L := hl
    have hc : (l : X) * t = t * (l : X) := mem_centralizer_singleton_iff.mp (hLC hl')
    apply Subtype.ext
    show t * (l : X) * t⁻¹ = l
    rw [← hc, mul_inv_cancel_right]
  have hOG : pPrimeCore 2 ↥N ≤ G.subgroupOf N := by
    intro o ho
    exact hcG ⟨o, ho, rfl⟩
  have hG' : ∀ u ∈ L.subgroupOf N, u * u = 1 → ∀ h : ↥N,
      u * invAut N t htt htN h * u⁻¹ = h → h ∈ G.subgroupOf N := by
    intro u hu huu h hh
    have hu' : (u : X) ∈ L := hu
    have huu' : (u : X) * (u : X) = 1 := by simpa using congrArg Subtype.val huu
    have hh' : (u : X) * (t * (h : X) * t⁻¹) * (u : X)⁻¹ = (h : X) := congrArg Subtype.val hh
    have hcomm : (h : X) * ((u : X) * t) = ((u : X) * t) * (h : X) := by
      calc (h : X) * ((u : X) * t)
          = ((u : X) * (t * (h : X) * t⁻¹) * (u : X)⁻¹) * ((u : X) * t) := by rw [hh']
        _ = ((u : X) * t) * (h : X) := by group
    exact hcent (u : X) hu' huu' (h : X) h.2 (mem_centralizer_singleton_iff.mpr hcomm)
  have hfinal := gen_of_core hExact (invAut N t htt htN) (invAut_sq N t htt htN)
    (L.subgroupOf N) hperfL' hfix hLA' (G.subgroupOf N) hOG hG'
  refine le_antisymm hGN fun n hn => ?_
  have hmem : (⟨n, hn⟩ : ↥N) ∈ G.subgroupOf N := by rw [hfinal]; exact mem_top _
  exact hmem

end Generation

end CFSG.ComponentClassification.SolMax.SwapP2
