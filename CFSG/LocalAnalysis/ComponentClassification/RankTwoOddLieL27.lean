module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieReduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2Seven

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b
open scoped MatrixGroups

private theorem d8_four_aux : ∀ x y w : DihedralGroup 4, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 →
    y ≠ 1 → x ≠ y → x * y = y * x → w ^ 2 = 1 → w * x = x * w → w * y = y * w →
    w = 1 ∨ w = x ∨ w = y ∨ w = x * y := by
  decide

private theorem d8_normalizer_aux : ∀ x y : DihedralGroup 4, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 →
    y ≠ 1 → x ≠ y → x * y = y * x →
    ∃ a : DihedralGroup 4, a ^ 2 = 1 ∧ ¬ (a * x = x * a ∧ a * y = y * a) ∧
      (a * x * a⁻¹ = x ∨ a * x * a⁻¹ = y ∨ a * x * a⁻¹ = x * y) ∧
      (a * y * a⁻¹ = x ∨ a * y * a⁻¹ = y ∨ a * y * a⁻¹ = x * y) := by
  decide

theorem exists_two_ne_one_of_four_le {P : Type*} [Group P] {V : Subgroup P}
    (h4 : 4 ≤ Nat.card V) : ∃ x ∈ V, ∃ y ∈ V, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype V := Fintype.ofFinite V
  have h3 : 2 < (Finset.univ.erase (1 : V)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.1 (by omega : 1 < (Finset.univ.erase (1 : V)).card)
  rw [Finset.mem_erase] at ha hb
  exact ⟨a, a.2, b, b.2, fun h => ha.1 (Subtype.ext h), fun h => hb.1 (Subtype.ext h),
    fun h => hab (Subtype.ext h)⟩

theorem elemAbelian_le_dihedral {P : Type*} [Group P] {S V : Subgroup P}
    (φ : S ≃* DihedralGroup 4) (hVS : V ≤ S) (hV : IsElemAbelian 2 V) (h4 : 4 ≤ Nat.card V) :
    Nat.card V = 4 ∧ ∃ a ∈ S, a ^ 2 = 1 ∧ a ∈ normalizer (V : Set P) ∧
      a ∉ centralizer (V : Set P) := by
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_two_ne_one_of_four_le h4
  have hcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have himg_sq : ∀ v (hv : v ∈ V), (φ ⟨v, hVS hv⟩) ^ 2 = 1 := by
    intro v hv
    rw [← map_pow, show (⟨v, hVS hv⟩ : S) ^ 2 = 1 from Subtype.ext (by simpa using hV.2 v hv),
      map_one]
  have himg_ne : ∀ v (hv : v ∈ V), v ≠ 1 → φ ⟨v, hVS hv⟩ ≠ 1 := by
    intro v hv hv1 h
    exact hv1 (congrArg Subtype.val (φ.injective (h.trans (map_one φ).symm)))
  have himg_comm : ∀ v (hv : v ∈ V) w (hw : w ∈ V),
      φ ⟨v, hVS hv⟩ * φ ⟨w, hVS hw⟩ = φ ⟨w, hVS hw⟩ * φ ⟨v, hVS hv⟩ := by
    intro v hv w hw
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hcomm v hv w hw))
  have hx'y' : φ ⟨x, hVS hx⟩ ≠ φ ⟨y, hVS hy⟩ := fun h =>
    hxy (congrArg Subtype.val (φ.injective h))
  have hmem : ∀ v ∈ V, v = 1 ∨ v = x ∨ v = y ∨ v = x * y := by
    intro v hv
    rcases d8_four_aux (φ ⟨x, hVS hx⟩) (φ ⟨y, hVS hy⟩) (φ ⟨v, hVS hv⟩) (himg_sq x hx)
        (himg_sq y hy) (himg_ne x hx hx1) (himg_ne y hy hy1) hx'y' (himg_comm x hx y hy)
        (himg_sq v hv) (himg_comm v hv x hx) (himg_comm v hv y hy) with h | h | h | h
    · exact Or.inl (congrArg Subtype.val (φ.injective (h.trans (map_one φ).symm)))
    · exact Or.inr (Or.inl (congrArg Subtype.val (φ.injective h)))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val (φ.injective h))))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have : φ ⟨v, hVS hv⟩ = φ (⟨x, hVS hx⟩ * ⟨y, hVS hy⟩) := by rw [map_mul]; exact h
      exact congrArg Subtype.val (φ.injective this)
  have hcard : Nat.card V ≤ 4 := by
    classical
    have hsub : (V : Set P) ⊆ ((({1, x, y, x * y} : Finset P)) : Set P) := by
      intro v hv
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact hmem v hv
    calc Nat.card V = (V : Set P).ncard := Nat.card_coe_set_eq (V : Set P)
      _ ≤ ((({1, x, y, x * y} : Finset P)) : Set P).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({1, x, y, x * y} : Finset P).card := Set.ncard_coe_finset _
      _ ≤ 4 := Finset.card_le_four
  refine ⟨le_antisymm hcard h4, ?_⟩
  obtain ⟨a', ha'2, hna, hax, hay⟩ := d8_normalizer_aux _ _ (himg_sq x hx) (himg_sq y hy)
    (himg_ne x hx hx1) (himg_ne y hy hy1) hx'y' (himg_comm x hx y hy)
  set a : S := φ.symm a' with ha_def
  have hφa : φ a = a' := MulEquiv.apply_symm_apply φ a'
  have ha2 : a ^ 2 = 1 := by
    apply φ.injective
    rw [map_pow, hφa, ha'2, map_one]
  have hconj : ∀ s : S, φ (a * s * a⁻¹) = a' * φ s * a'⁻¹ := fun s => by
    rw [map_mul, map_mul, map_inv, hφa]
  have hxyV : x * y ∈ V := mul_mem hx hy
  have himgV : ∀ s : S, (φ s = φ ⟨x, hVS hx⟩ ∨ φ s = φ ⟨y, hVS hy⟩ ∨
      φ s = φ ⟨x, hVS hx⟩ * φ ⟨y, hVS hy⟩) → (s : P) ∈ V := by
    intro s hs
    rcases hs with h | h | h
    · rw [φ.injective h]; exact hx
    · rw [φ.injective h]; exact hy
    · rw [← map_mul] at h
      rw [φ.injective h]
      exact hxyV
  have haxV : (a : P) * x * (a : P)⁻¹ ∈ V := by
    have := himgV (a * ⟨x, hVS hx⟩ * a⁻¹) (by rw [hconj]; exact hax)
    simpa using this
  have hayV : (a : P) * y * (a : P)⁻¹ ∈ V := by
    have := himgV (a * ⟨y, hVS hy⟩ * a⁻¹) (by rw [hconj]; exact hay)
    simpa using this
  have hfwd : ∀ v ∈ V, (a : P) * v * (a : P)⁻¹ ∈ V := by
    intro v hv
    rcases hmem v hv with rfl | rfl | rfl | rfl
    · simp
    · exact haxV
    · exact hayV
    · have e : (a : P) * (x * y) * (a : P)⁻¹ =
          ((a : P) * x * (a : P)⁻¹) * ((a : P) * y * (a : P)⁻¹) := by group
      rw [e]
      exact mul_mem haxV hayV
  have hainv : (a : P)⁻¹ = a := by
    have h2 : (a : P) ^ 2 = 1 := by simpa using congrArg Subtype.val ha2
    rw [inv_eq_iff_mul_eq_one, ← sq, h2]
  refine ⟨a, a.2, by simpa using congrArg Subtype.val ha2, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro v
    refine ⟨hfwd v, fun hv => ?_⟩
    have := hfwd _ hv
    rwa [hainv, show (a : P) * ((a : P) * v * a) * a = ((a : P) * a) * v * ((a : P) * a) by group,
      ← sq, show (a : P) ^ 2 = 1 by simpa using congrArg Subtype.val ha2, one_mul,
      mul_one] at this
  · intro haC
    apply hna
    have h1 : (a : P) * x = x * a := ((mem_centralizer_iff.mp haC) x hx).symm
    have h2 : (a : P) * y = y * a := ((mem_centralizer_iff.mp haC) y hy).symm
    constructor
    · rw [← hφa, ← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext h1)
    · rw [← hφa, ← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext h2)

theorem isOddPrimePower_card_zmod_seven :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) :=
  ⟨7, 1, by norm_num, by decide, le_rfl, by simp⟩

theorem card_psl27 : Nat.card PSL(2, ZMod 7) = 168 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [CFSG.GorensteinWalter.psl2_card_formula (ZMod 7) isOddPrimePower_card_zmod_seven,
    Nat.card_zmod]
  norm_num

theorem psl27_exists_le_dihedral (V : Subgroup PSL(2, ZMod 7)) (hV : IsPGroup 2 V) :
    ∃ S : Subgroup PSL(2, ZMod 7), V ≤ S ∧ Nonempty (S ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_card_zmod_seven
  have hcard := card_psl27
  obtain ⟨S, hVS⟩ := hV.exists_le_sylow
  obtain ⟨m, -, ⟨φ⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (ZMod 7) hodd S
  have hS : Nat.card S = 2 ^ (m + 1) := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card, pow_succ']
  have h8 : 2 ^ 3 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by rw [hcard]; decide)
  have h168 : Nat.card S ∣ 168 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hm : m = 2 := by
    rw [hS] at h8 h168
    have h1 : 3 ≤ m + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h8
    have h2 : m + 1 ≤ 3 := by
      by_contra hcon
      have : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 (by omega)).trans h168
      exact absurd this (by decide)
    omega
  subst hm
  exact ⟨S, hVS, ⟨φ⟩⟩

theorem psl27_elemAbelian {V : Subgroup PSL(2, ZMod 7)} (hV : IsElemAbelian 2 V)
    (h4 : 4 ≤ Nat.card V) :
    IsKleinFour V ∧ ∃ a : PSL(2, ZMod 7), a ^ 2 = 1 ∧ a ∈ normalizer (V : Set PSL(2, ZMod 7)) ∧
      a ∉ centralizer (V : Set PSL(2, ZMod 7)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one]; exact Subtype.ext (hV.2 v v.2)⟩
  obtain ⟨S, hVS, ⟨φ⟩⟩ := psl27_exists_le_dihedral V hp
  obtain ⟨hcard, a, -, ha2, haN, haC⟩ := elemAbelian_le_dihedral φ hVS hV h4
  refine ⟨⟨hcard, ?_⟩, a, ha2, haN, haC⟩
  have : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  exact orderOf_eq_prime (Subtype.ext (hV.2 g g.2)) hg

theorem mem_sup_centralizer_of_psl27 {G : Type} [Group G] [Finite G] {B R : Subgroup G}
    (hB : commutator B = ⊤) (e : B ⧸ center B ≃* PSL(2, ZMod 7))
    (hZ : Odd (Nat.card (center B))) (hRB : R ≤ B) (hR : IsElemAbelian 2 R)
    (h4 : 4 ≤ Nat.card R) {a : G} (ha : a ∈ normalizer (B : Set G))
    (haR : ∀ r ∈ R, a * r = r * a) : a ∈ B ⊔ centralizer (B : Set G) := by
  have haB : ∀ b ∈ B, a * b * a⁻¹ ∈ B := fun b hb => (mem_normalizer_iff.mp ha b).mp hb
  have haB' : ∀ b ∈ B, a⁻¹ * b * a ∈ B := fun b hb => by
    simpa using (mem_normalizer_iff.mp (inv_mem ha) b).mp hb
  let σ : ↥B ≃* ↥B :=
    { toFun := fun b => ⟨a * b * a⁻¹, haB b b.2⟩
      invFun := fun b => ⟨a⁻¹ * b * a, haB' b b.2⟩
      left_inv := fun b => Subtype.ext (by simp [mul_assoc])
      right_inv := fun b => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun b c => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hσ : ∀ b : B, ((σ b : B) : G) = a * b * a⁻¹ := fun b => rfl
  let π : ↥B →* PSL(2, ZMod 7) := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  let σbar : B ⧸ center B ≃* B ⧸ center B :=
    QuotientGroup.congr (center B) (center B) σ (map_center_mulEquiv σ)
  let β : MulAut PSL(2, ZMod 7) := e.symm.trans (σbar.trans e)
  have hπ : ∀ b : B, π b = e (QuotientGroup.mk' (center B) b) := fun b => rfl
  have hβ : ∀ b : B, β (π b) = π (σ b) := fun b => by
    rw [hπ, hπ]
    show e (σbar (e.symm (e (QuotientGroup.mk' (center B) b)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hinj : ∀ m : B, (m : G) ∈ R → π m = 1 → m = 1 := by
    intro m hmR hm1
    have hmZ : m ∈ center B := by
      have : QuotientGroup.mk' (center B) m = 1 := e.injective (hm1.trans (map_one e).symm)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have h2 : orderOf m ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hR.2 _ hmR))
    have hodd : Odd (orderOf m) := by
      have := orderOf_dvd_natCard (⟨m, hmZ⟩ : center B)
      rw [Subgroup.orderOf_mk] at this
      exact hZ.of_dvd_nat this
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  have hVcard : Nat.card (imgIn π R) = Nat.card R := card_imgIn π hRB hinj
  obtain ⟨hK4, -⟩ := psl27_elemAbelian (isElemAbelian_imgIn π hR) (by rw [hVcard]; exact h4)
  have hfix : ∀ v ∈ imgIn π R, β v = v := by
    intro v hv
    obtain ⟨r, hrR, rfl⟩ := mem_imgIn.mp hv
    rw [hβ]
    congr 1
    exact Subtype.ext (by rw [hσ, haR _ hrR, mul_inv_cancel_right])
  obtain ⟨v₀, hv₀, hβv₀⟩ :=
    CFSG.QuasithinUnique.DoubleA3.psl27_aut_conj_of_fixes_kleinFour (imgIn π R) hK4 β hfix
  obtain ⟨r₀, -, rfl⟩ := mem_imgIn.mp hv₀
  have hz : ∀ b : B, (σ b)⁻¹ * (r₀ * b * r₀⁻¹) ∈ center B := by
    intro b
    have h1 : π (σ b) = π (r₀ * b * r₀⁻¹) := by
      rw [← hβ, hβv₀, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have h2 : QuotientGroup.mk' (center B) (σ b) =
        QuotientGroup.mk' (center B) (r₀ * b * r₀⁻¹) := e.injective h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
  have hkey : ∀ u z : B, z ∈ center B → u⁻¹ * z * u = z := fun u z hzc => by
    rw [mul_assoc, ← (Subgroup.mem_center_iff.mp hzc u), inv_mul_cancel_left]
  have hc : (r₀ : G)⁻¹ * a ∈ centralizer (B : Set G) := by
    refine mem_centralizer_of_perfect hB (mul_mem (inv_mem (Subgroup.le_normalizer r₀.2)) ha)
      fun b hb b' hb' => ?_
    set w : B := (σ ⟨b, hb⟩)⁻¹ * (r₀ * ⟨b, hb⟩ * r₀⁻¹) with hw_def
    have hw : w ∈ center B := hz ⟨b, hb⟩
    have hσb : σ ⟨b, hb⟩ = r₀ * ⟨b, hb⟩ * r₀⁻¹ * w⁻¹ := by
      rw [hw_def]
      group
    have hB1 : r₀⁻¹ * σ ⟨b, hb⟩ * r₀ * (⟨b, hb⟩ : B)⁻¹ = w⁻¹ := by
      rw [hσb]
      calc r₀⁻¹ * (r₀ * ⟨b, hb⟩ * r₀⁻¹ * w⁻¹) * r₀ * (⟨b, hb⟩ : B)⁻¹
          = (⟨b, hb⟩ : B)⁻¹⁻¹ * (r₀⁻¹ * w⁻¹ * r₀) * (⟨b, hb⟩ : B)⁻¹ := by group
        _ = w⁻¹ := by rw [hkey r₀ _ (inv_mem hw), hkey _ _ (inv_mem hw)]
    have hG : (r₀ : G)⁻¹ * a * b * ((r₀ : G)⁻¹ * a)⁻¹ * b⁻¹ = ((w⁻¹ : B) : G) := by
      rw [← hB1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ]
      group
    rw [hG]
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp (inv_mem hw) ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul] at this
    exact this.symm
  have e2 : a = (r₀ : G) * ((r₀ : G)⁻¹ * a) := by group
  rw [e2]
  exact mul_mem (mem_sup_left r₀.2) (mem_sup_right hc)

end CFSG.ComponentClassification.RankTwoOddLie
