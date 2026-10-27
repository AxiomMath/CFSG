module

public import CFSG.ClassicalInvolution.Asc77.AscE189Bar
public import CFSG.ClassicalInvolution.Asc77.AscE189CaseA
public import CFSG.ClassicalInvolution.Asc77.AscE189Sect
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section Lift

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
  {N : Subgroup Y} [N.Normal]

theorem eq_of_map_eq_of_involution (hΛ : HypOmegaMod p f Λ) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hN : Odd (Nat.card N)) {L L' : Subgroup Y} (hL : L ∈ Λ) (hL' : L' ∈ Λ) {w : Y}
    (hw : IsUniqueInvolution L w) (hw' : IsUniqueInvolution L' w)
    (himg : L.map (QuotientGroup.mk' N) = L'.map (QuotientGroup.mk' N)) : L = L' := by
  by_contra hne
  exact map_ne_of_twin hp hq hΛ hN hL' ⟨hL, w, hw', hw⟩ hne himg

omit [Fact p.Prime] [Finite Y] in
theorem mem_normalizer_of_forall_commute {H : Subgroup Y} {g : Y} (hc : ∀ h ∈ H, h * g = g * h) :
    g ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : g * h * g⁻¹ = h := by
      rw [← hc h hh]
      group
    rw [this]
    exact hh
  · intro hh
    have e : g * h = g * (g * h * g⁻¹) := by
      calc g * h = (g * h * g⁻¹) * g := by group
        _ = g * (g * h * g⁻¹) := hc _ hh
    have e' : h = g * h * g⁻¹ := mul_left_cancel e
    rw [e']
    exact hh

omit [Fact p.Prime] [Finite Y] in
theorem conjSub_eq_of_forall_commute {L : Subgroup Y} {g : Y} (hc : ∀ h ∈ L, h * g = g * h) :
    conjSub g L = L :=
  mem_normalizer_iff_conjSub_eq.mp (mem_normalizer_of_forall_commute hc)

theorem commutes_of_normalizes_sylow (hN : Odd (Nat.card N)) {R : Subgroup Y} (hR : IsPGroup 2 R)
    {a : Y} (haR : conjSub a R = R)
    (hc : ∀ r ∈ R, QuotientGroup.mk' N r * QuotientGroup.mk' N a =
      QuotientGroup.mk' N a * QuotientGroup.mk' N r) : ∀ r ∈ R, r * a = a * r := by
  intro r hr
  have hr' : a * r⁻¹ * a⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := a) (R.inv_mem hr)
    rwa [haR] at this
  have hcR : r * (a * r⁻¹ * a⁻¹) ∈ R := R.mul_mem hr hr'
  have hcN : r * (a * r⁻¹ * a⁻¹) ∈ N := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show QuotientGroup.mk' N _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc QuotientGroup.mk' N r * (QuotientGroup.mk' N a * (QuotientGroup.mk' N r)⁻¹ *
        (QuotientGroup.mk' N a)⁻¹)
        = (QuotientGroup.mk' N r * QuotientGroup.mk' N a) * (QuotientGroup.mk' N r)⁻¹ *
          (QuotientGroup.mk' N a)⁻¹ := by group
      _ = 1 := by rw [hc r hr]; group
  have hRN : R ⊓ N = ⊥ := AscQuot.inf_eq_bot_of_isPGroup_of_odd N hR le_rfl (odd_natCard_inf hN R)
  have h0 : r * (a * r⁻¹ * a⁻¹) ∈ R ⊓ N := ⟨hcR, hcN⟩
  rw [hRN, Subgroup.mem_bot] at h0
  calc r * a = (r * (a * r⁻¹ * a⁻¹)) * (a * r) := by group
    _ = a * r := by rw [h0, one_mul]

theorem exists_conj_isPGroup_sup (hN : Odd (Nat.card N)) {R₁ R₂ : Subgroup Y} (hR₁ : IsPGroup 2 R₁)
    (hR₂ : IsPGroup 2 R₂)
    (hc : Commutes (R₁.map (QuotientGroup.mk' N)) (R₂.map (QuotientGroup.mk' N))) :
    ∃ m ∈ N, IsPGroup 2 ↥(R₁ ⊔ conjSub m R₂) := by
  set mk := QuotientGroup.mk' N with hmk
  have hS₁ : IsSylow2In R₂ (R₂ ⊔ N) := isSylow2In_sup_of_odd hN hR₂
  have hperm : ∀ x ∈ R₁, ∃ n ∈ N, conjSub x R₂ = conjSub n R₂ := by
    intro x hx
    have hxb : conjSub (mk x) (R₂.map mk) = R₂.map mk :=
      conjSub_eq_of_mem_of_commutes (Subgroup.mem_map_of_mem _ hx) hc
    have hmapx : (conjSub x R₂).map mk = R₂.map mk := by rw [AscQuot.map_conjSub, hxb]
    have hxle : conjSub x R₂ ≤ R₂ ⊔ N := by
      intro y hy
      have hy' : mk y ∈ R₂.map mk := hmapx ▸ Subgroup.mem_map_of_mem _ hy
      obtain ⟨r, hr, hry⟩ := hy'
      have hrn : r⁻¹ * y ∈ N := by
        have : QuotientGroup.mk' N (r⁻¹ * y) = 1 := by
          rw [map_mul, map_inv, hry, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp this
      have : y = r * (r⁻¹ * y) := by group
      rw [this]
      exact (R₂ ⊔ N).mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hrn)
    have hS₂ : IsSylow2In (conjSub x R₂) (R₂ ⊔ N) :=
      hS₁.of_natCard_le (hR₂.map _) hxle (by
        rw [Nat.card_congr (Subgroup.equivMapOfInjective R₂ (MulAut.conj x).toMonoidHom
          (MulAut.conj x).injective).toEquiv]
        rfl)
    obtain ⟨p', hp', hpx⟩ := exists_conjSub_eq_of_isSylow2In hS₁ hS₂
    obtain ⟨r, hr, n, hn, hrn⟩ := Subgroup.mem_sup_of_normal_right.mp hp'
    refine ⟨r * n * r⁻¹, ‹N.Normal›.conj_mem n hn r, ?_⟩
    rw [← hpx, ← hrn]
    calc conjSub (r * n) R₂ = conjSub ((r * n * r⁻¹) * r) R₂ := by congr 1; group
      _ = conjSub (r * n * r⁻¹) (conjSub r R₂) := conjSub_mul _ _ _
      _ = conjSub (r * n * r⁻¹) R₂ := by rw [conjSub_eq_self_of_mem hr]
  obtain ⟨m, hm, hmN⟩ := exists_conj_normalizer_of_perm hN R₂ hR₁ hperm
  exact ⟨m, hm, hR₁.to_sup_of_normal_right' (hR₂.map _) hmN⟩

theorem e189_lift_a (hΛ : HypOmegaMod p f Λ) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hN : Odd (Nat.card N)) {K : Subgroup Y} {z t : Y} (hK : K ∈ Λ) (hz : IsUniqueInvolution K z)
    (ht2 : t * t = 1) (hzt : z * t = t * z) {K'' : Subgroup (Y ⧸ N)}
    (hK'' : K'' ∈ twinSet (quotFamily Λ N) (K.map (QuotientGroup.mk' N)))
    (hne : K'' ≠ K.map (QuotientGroup.mk' N)) {Rb₁ Rb₂ : Subgroup (Y ⧸ N)}
    (hRb₁ : IsSylow2In Rb₁ (K.map (QuotientGroup.mk' N))) (hRb₂ : IsSylow2In Rb₂ K'')
    (hRbc : Commutes Rb₁ Rb₂) {ub xb : Y ⧸ N} (hu : ub ∈ Rb₁ ⊔ Rb₂) (hu1 : ub ≠ 1)
    (hu2 : ub * ub = 1) (hux : xb * ub * xb⁻¹ = QuotientGroup.mk' N z * QuotientGroup.mk' N t) :
    ∃ K₃ ∈ twinSet Λ K, K₃ ≠ K ∧ ∃ R₁ R₃ : Subgroup Y, IsSylow2In R₁ K ∧ IsSylow2In R₃ K₃ ∧
      Commutes R₁ R₃ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₃ ∧ u ≠ 1 ∧ u * u = 1 ∧
        x * u * x⁻¹ = z * t := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨L, hLtw, hLmap⟩ := exists_lift_twin hp hq hΛ hN hK hK''
  obtain ⟨hLΛ, z₀, hz₀K, hz₀L⟩ := hLtw
  have hz₀ : z₀ = z := hz₀K.eq hz
  have hzL : IsUniqueInvolution L z := hz₀ ▸ hz₀L
  obtain ⟨R₁, hR₁, hR₁map⟩ := exists_lift_sylow hN hRb₁
  have hRb₂' : IsSylow2In Rb₂ (L.map mk) := by
    rw [hLmap]
    exact hRb₂
  obtain ⟨R₂, hR₂, hR₂map⟩ := exists_lift_sylow hN hRb₂'
  have hR₁2 : IsPGroup 2 R₁ := hR₁.2.1
  have hR₂2 : IsPGroup 2 R₂ := hR₂.2.1
  obtain ⟨m, hm, hP⟩ := exists_conj_isPGroup_sup hN hR₁2 hR₂2 (by rw [hR₁map, hR₂map]; exact hRbc)
  have hmk1 : mk m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
  set L' : Subgroup Y := conjSub m L with hL'
  set R₃ : Subgroup Y := conjSub m R₂ with hR₃
  have hL'Λ : L' ∈ Λ := hΛ.conjInvariant m L hLΛ
  have hL'img : L'.map mk = K'' := by
    rw [hL', AscQuot.map_conjSub, hmk1, conjSub_one, hLmap]
  have hR₃syl : IsSylow2In R₃ L' := hR₂.conj m
  have hR₃img : R₃.map mk = Rb₂ := by
    rw [hR₃, AscQuot.map_conjSub, hmk1, conjSub_one, hR₂map]
  have hL'ne : L' ≠ K := by
    intro h
    apply hne
    rw [← hL'img, h]
  have hR₁Ω : R₁ ∈ RSet Λ := mem_RSet_of_isSylow2In hK hR₁
  have hR₃Ω : R₃ ∈ RSet Λ := mem_RSet_of_isSylow2In hL'Λ hR₃syl
  have h8₁ := hΛ.eight_le_of_mem_RSet hp hR₁Ω
  have h8₃ := hΛ.eight_le_of_mem_RSet hp hR₃Ω
  have hRne : R₁ ≠ R₃ := by
    intro h
    exact hL'ne (hΛ.eq_of_le_of_le hL'Λ hK hR₃syl.2.1 (by omega) hR₃syl.1 (h ▸ hR₁.1))
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hcomm : Commutes R₁ R₃ :=
    l6_7_proved p f hp hq Y Λ hΛ S R₁ hR₁Ω R₃ hR₃Ω (le_sup_left.trans hS) (le_sup_right.trans hS)
      hRne
  have hzR₁ : z ∈ R₁ := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR₁.1 hR₁2 (by omega)
  have hz'L' : IsUniqueInvolution L' (m * z * m⁻¹) := hzL.conj m
  have hz'R₃ : m * z * m⁻¹ ∈ R₃ :=
    AscL62.mem_of_uniqueInvolution_of_pGroup hz'L' hR₃syl.1 hR₃syl.2.1 (by omega)
  have hzz' : z * (m * z * m⁻¹) = (m * z * m⁻¹) * z := hcomm z hzR₁ _ hz'R₃
  have hzz'1 : z * (m * z * m⁻¹) = 1 := by
    have hsq : (z * (m * z * m⁻¹)) * (z * (m * z * m⁻¹)) = 1 := by
      calc (z * (m * z * m⁻¹)) * (z * (m * z * m⁻¹))
          = z * ((m * z * m⁻¹) * z) * (m * z * m⁻¹) := by group
        _ = z * (z * (m * z * m⁻¹)) * (m * z * m⁻¹) := by rw [← hzz']
        _ = (z * z) * ((m * z * m⁻¹) * (m * z * m⁻¹)) := by group
        _ = 1 := by rw [hz.sq, hz'L'.sq, one_mul]
    have hmem : z * (m * z * m⁻¹) ∈ N := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show mk _ = 1
      rw [map_mul, map_mul, map_mul, map_inv, hmk1, one_mul, inv_one, mul_one, ← map_mul, hz.sq,
        map_one]
    have hdvd : orderOf (z * (m * z * m⁻¹)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    have hodd : Odd (orderOf (z * (m * z * m⁻¹))) :=
      hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hmem)
    have h1 : orderOf (z * (m * z * m⁻¹)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1
  have hz'z : m * z * m⁻¹ = z := by
    have := eq_inv_of_mul_eq_one_right hzz'1
    rw [this, inv_eq_of_mul_eq_one_right hz.sq]
  have hL'tw : L' ∈ twinSet Λ K := ⟨hL'Λ, z, hz, hz'z ▸ hz'L'⟩
  refine ⟨L', hL'tw, hL'ne, R₁, R₃, hR₁, hR₃syl, hcomm, ?_⟩
  have haP : ub ∈ (R₁ ⊔ R₃).map mk := by
    rw [Subgroup.map_sup, hR₁map, hR₃img]
    exact hu
  obtain ⟨u, huP, hu1', hu2', hmku⟩ := exists_involution_lift_of_isPGroup hN hP haP hu1 hu2
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective N xb
  have hw2 : (x₀ * u * x₀⁻¹) * (x₀ * u * x₀⁻¹) = 1 := by
    calc (x₀ * u * x₀⁻¹) * (x₀ * u * x₀⁻¹) = x₀ * (u * u) * x₀⁻¹ := by group
      _ = 1 := by rw [hu2']; group
  have hzt2 : (z * t) * (z * t) = 1 := mul_involution_of_commute hz.sq ht2 hzt
  have hmkw : mk (z * t) = mk (x₀ * u * x₀⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, hmku, hx₀, ← hux]
  obtain ⟨m', hm', hmw⟩ := exists_conj_eq_of_map_eq hN hzt2 hw2 hmkw
  refine ⟨u, m' * x₀, huP, hu1', hu2', ?_⟩
  calc (m' * x₀) * u * (m' * x₀)⁻¹ = m' * (x₀ * u * x₀⁻¹) * m'⁻¹ := by group
    _ = z * t := hmw

theorem e189_lift_b (hΛ : HypOmegaMod p f Λ) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hN : Odd (Nat.card N)) {K : Subgroup Y} {z t : Y} (hK : K ∈ Λ) (ht2 : t * t = 1)
    (hz : IsUniqueInvolution K z) (hzt : z * t = t * z) (ha1 : z * t ≠ 1) {xb : Y ⧸ N}
    {Mb : Subgroup (Y ⧸ N)}
    (hM : Mb ∈ twinSet (quotFamily Λ N) (conjSub xb (K.map (QuotientGroup.mk' N))))
    (hMne : Mb ≠ conjSub xb (K.map (QuotientGroup.mk' N)))
    (hcomm : ∀ w ∈ conjSub xb (K.map (QuotientGroup.mk' N)) ⊔ Mb,
      w * (QuotientGroup.mk' N z * QuotientGroup.mk' N t) =
        (QuotientGroup.mk' N z * QuotientGroup.mk' N t) * w) :
    ∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
      ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  set mk := QuotientGroup.mk' N with hmk
  set a := z * t with ha
  have ha2 : a * a = 1 := mul_involution_of_commute hz.sq ht2 hzt
  have hmka : mk a = mk z * mk t := map_mul _ _ _
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective N xb
  set K₁ := conjSub x₀ K with hK₁
  have hK₁Λ : K₁ ∈ Λ := hΛ.conjInvariant x₀ K hK
  have hK₁img : K₁.map mk = conjSub xb (K.map mk) := by
    rw [hK₁, AscQuot.map_conjSub, hx₀]
  have hcomm1 : ∀ w ∈ K₁.map mk, w * mk a = mk a * w := fun w hw => by
    rw [hmka]
    exact hcomm w (Subgroup.mem_sup_left (hK₁img ▸ hw))
  have hcommM : ∀ w ∈ Mb, w * mk a = mk a * w := fun w hw => by
    rw [hmka]
    exact hcomm w (Subgroup.mem_sup_right hw)
  have hU2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_involution ha1 ha2
  have hUN : ∀ u ∈ Subgroup.zpowers a, mk u ∈
      Subgroup.normalizer ((K₁.map mk : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine mem_normalizer_of_forall_commute fun w hw => ?_
    rw [map_zpow]
    exact ((show Commute w (mk a) from hcomm1 w hw).zpow_right k).eq
  obtain ⟨n, hn, hUn⟩ := exists_conj_normalizer hp hq hΛ hN hK₁Λ hU2 hUN
  set K₁' := conjSub n K₁ with hK₁'
  have hK₁'Λ : K₁' ∈ Λ := hΛ.conjInvariant n K₁ hK₁Λ
  have hmkn : mk n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hK₁'img : K₁'.map mk = K₁.map mk := by
    rw [hK₁', AscQuot.map_conjSub, hmkn, conjSub_one]
  have haK₁' : a ∈ Subgroup.normalizer (K₁' : Set Y) := hUn (Subgroup.mem_zpowers a)
  obtain ⟨R₁, hR₁, hR₁a⟩ := AscL62.exists_sylow_normalized hU2 hUn
  have hR₁a' : conjSub a R₁ = R₁ := hR₁a a (Subgroup.mem_zpowers a)
  have hR₁c : ∀ r ∈ R₁, r * a = a * r :=
    commutes_of_normalizes_sylow hN hR₁.2.1 hR₁a' fun r hr =>
      hcomm1 _ (hK₁'img ▸ Subgroup.mem_map_of_mem _ (hR₁.1 hr))
  obtain ⟨z₁', hz₁'⟩ := hΛ.exists_uniqueInvolution hp hq hK₁'Λ
  have hR₁Ω : R₁ ∈ RSet Λ := mem_RSet_of_isSylow2In hK₁'Λ hR₁
  have h8₁ := hΛ.eight_le_of_mem_RSet hp hR₁Ω
  have hz₁'R₁ : z₁' ∈ R₁ :=
    AscL62.mem_of_uniqueInvolution_of_pGroup hz₁' hR₁.1 hR₁.2.1 (by omega)
  have hz₁'a : a * z₁' * a⁻¹ = z₁' := by
    rw [← hR₁c z₁' hz₁'R₁]
    group
  obtain ⟨hMΛ', z', hz'K, hz'M⟩ := hM
  obtain ⟨M₂, hM₂, hM₂img0⟩ := hMΛ'
  have hM₂img : M₂.map mk = Mb := hM₂img0
  obtain ⟨z₂, hz₂⟩ := hΛ.exists_uniqueInvolution hp hq hM₂
  have hz₂img : IsUniqueInvolution (M₂.map mk) (mk z₂) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN M₂) hz₂
  have hz₁'img : IsUniqueInvolution (K₁'.map mk) (mk z₁') :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K₁') hz₁'
  have hz₁'img' : IsUniqueInvolution (conjSub xb (K.map mk)) (mk z₁') := by
    rw [← hK₁img, ← hK₁'img]
    exact hz₁'img
  have h1 : mk z₁' = z' := hz₁'img'.eq hz'K
  have h2 : mk z₂ = z' := (hM₂img ▸ hz₂img).eq hz'M
  obtain ⟨m, hm, hmz⟩ := exists_conj_eq_of_map_eq hN hz₁'.sq hz₂.sq (h1.trans h2.symm)
  set M' := conjSub m M₂ with hM'
  have hM'Λ : M' ∈ Λ := hΛ.conjInvariant m M₂ hM₂
  have hmkm : mk m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
  have hM'img : M'.map mk = Mb := by
    rw [hM', AscQuot.map_conjSub, hmkm, conjSub_one, hM₂img]
  have hM'z : IsUniqueInvolution M' z₁' := by
    have := hz₂.conj m
    rwa [hmz] at this
  have hM'ne : M' ≠ K₁' := by
    intro h
    apply hMne
    rw [← hM'img, h, hK₁'img, hK₁img]
  have haM' : conjSub a M' = M' := by
    have hM''Λ : conjSub a M' ∈ Λ := hΛ.conjInvariant a M' hM'Λ
    have hM''z : IsUniqueInvolution (conjSub a M') z₁' := by
      have := hM'z.conj a
      rwa [hz₁'a] at this
    have himg : (conjSub a M').map mk = M'.map mk := by
      rw [AscQuot.map_conjSub, hM'img, conjSub_eq_of_forall_commute (fun w hw => hcommM w hw)]
    exact eq_of_map_eq_of_involution hΛ hp hq hN hM''Λ hM'Λ hM''z hM'z himg
  have haM'N : a ∈ Subgroup.normalizer (M' : Set Y) := mem_normalizer_iff_conjSub_eq.mpr haM'
  have hK₁'M' : K₁' ≤ Subgroup.normalizer (M' : Set Y) :=
    hΛ.le_normalizer_of_twin hK₁'Λ hM'Λ (Ne.symm hM'ne) hz₁' hM'z
  have hR₁U : IsPGroup 2 ↥(R₁ ⊔ Subgroup.zpowers a) :=
    hR₁.2.1.to_sup_of_normal_left' hU2 fun w hw => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      refine mem_normalizer_iff_conjSub_eq.mpr ?_
      refine conjSub_eq_of_forall_commute fun r hr => ?_
      exact ((show Commute r a from hR₁c r hr).zpow_right k).eq
  have hWN : R₁ ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (M' : Set Y) :=
    sup_le (fun r hr => hK₁'M' (hR₁.1 hr))
      (fun w hw => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact Subgroup.zpow_mem _ haM'N k)
  obtain ⟨R₂, hR₂, hR₂W⟩ := AscL62.exists_sylow_normalized hR₁U hWN
  have hR₂a' : conjSub a R₂ = R₂ := hR₂W a (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hR₂c : ∀ r ∈ R₂, r * a = a * r :=
    commutes_of_normalizes_sylow hN hR₂.2.1 hR₂a' fun r hr =>
      hcommM _ (hM'img ▸ Subgroup.mem_map_of_mem _ (hR₂.1 hr))
  have hR₁R₂N : R₁ ≤ Subgroup.normalizer (R₂ : Set Y) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₂W w (Subgroup.mem_sup_left hw))
  have hR₁₂ : IsPGroup 2 ↥(R₁ ⊔ R₂) := hR₁.2.1.to_sup_of_normal_right' hR₂.2.1 hR₁R₂N
  have hcommR : Commutes R₁ R₂ :=
    hΛ.commutes_of_twin_of_isPGroup hK₁'Λ hM'Λ (Ne.symm hM'ne) hz₁' hM'z hR₁.1 hR₂.1 hR₁₂
  refine ⟨n * x₀, M', ⟨hM'Λ, z₁', ?_, hM'z⟩, ?_, R₁, R₂, ?_, hR₂, hcommR, ?_⟩
  · rw [conjSub_mul]
    exact hz₁'
  · rw [conjSub_mul]
    exact hM'ne
  · rw [conjSub_mul]
    exact hR₁
  · intro w hw
    have hle : R₁ ⊔ R₂ ≤ Subgroup.centralizer ({a} : Set Y) :=
      sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hR₁c k hk))
        (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hR₂c k hk))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

end Lift

section Assembly

variable {p f : ℕ} [Fact p.Prime]

theorem e189Sect_of_model (hmodel : E189Model p f) : E189Sect p f := by
  intro hp hq n hbelow Y _ _ hcard Λ hΛ hgen hA K hK J hJ z t hz ht hzt hne
  set N₀ : Subgroup Y := CFSG.Open.classicalInvolutionOddCore Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card Y
  set mk := QuotientGroup.mk' N₀ with hmk
  have hΛ' : HypOmegaMod p f (quotFamily Λ N₀) := oddQuotHyp p f hp hq Y Λ hΛ N₀ hN₀odd
  have hAΛ' : ∀ M ∈ quotFamily Λ N₀, AEmpty (quotFamily Λ N₀) M :=
    aEmpty_quotFamily hp hq hΛ hΛ' hN₀odd hA
  have hOq : CFSG.Open.classicalInvolutionOddCore (Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hcard' : Nat.card (Y ⧸ N₀) < n := by
    have h1 : Nat.card (Y ⧸ N₀) ≤ Nat.card Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hgen' : (⨆ L ∈ quotFamily Λ N₀, L) = ⊤ := by
    have h1 : (⨆ L ∈ Λ, L).map mk = ⨆ L ∈ Λ, L.map mk := by
      rw [Subgroup.map_iSup]
      congr 1
      funext L
      rw [Subgroup.map_iSup]
    have h2 : (⊤ : Subgroup Y).map mk = ⊤ :=
      Subgroup.map_top_of_surjective mk (QuotientGroup.mk'_surjective N₀)
    apply top_le_iff.mp
    rw [← h2, ← hgen, h1]
    exact iSup₂_le fun L hL => le_iSup₂ (f := fun L' (_ : L' ∈ quotFamily Λ N₀) => L')
      (L.map mk) (map_mem_quotFamily hL)
  have hzb : IsUniqueInvolution (K.map mk) (mk z) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd K) hz
  have htb : IsUniqueInvolution (J.map mk) (mk t) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd J) ht
  have hzt' : mk z * mk t = mk t * mk z := by rw [← map_mul, ← map_mul, hzt]
  have hne' : conjSub (mk t) (K.map mk) ≠ K.map mk := by
    intro h
    have hzK' : IsUniqueInvolution (conjSub t K) z := by
      have := hz.conj t
      rwa [show t * z * t⁻¹ = z by rw [← hzt]; group] at this
    have hK' : conjSub t K ∈ twinSet Λ K := ⟨hΛ.conjInvariant t K hK, z, hz, hzK'⟩
    exact map_ne_of_twin hp hq hΛ hN₀odd hK hK' hne (by rw [AscQuot.map_conjSub]; exact h)
  rcases e189_bar hmodel hp hq hbelow hcard' hOq hΛ' hgen' hAΛ' (map_mem_quotFamily hK)
    (map_mem_quotFamily hJ) hzb htb hzt' hne' with
    ⟨K'', hK''tw, hK''ne, Rb₁, Rb₂, hRb₁, hRb₂, hRbc, ub, xb, hu, hu1, hu2, hux⟩ |
      ⟨xb, Mb, hM, hMne, hcomm⟩
  · left
    exact e189_lift_a hΛ hp hq hN₀odd hK hz ht.sq hzt hK''tw hK''ne hRb₁ hRb₂ hRbc hu hu1 hu2
      hux
  · right
    exact e189_lift_b hΛ hp hq hN₀odd hK ht.sq hz hzt (e189_mul_ne_one hz hne) hM hMne hcomm

end Assembly

end CFSG.ClassicalInvolution.Asc77
