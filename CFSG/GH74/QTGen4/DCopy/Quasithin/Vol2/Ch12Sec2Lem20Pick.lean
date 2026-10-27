module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Pick
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20B68
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

@[expose] def CoprimePick_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P : Subgroup G) (p : ℕ), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
    p.Prime → p ≠ 2 → IsPGroup p ↥P → P ≤ H → ¬ p ∣ P.relIndex H → H = P ⊔ T →
    P ⊓ Subgroup.normalizer (L : Set G) = (frattini ↥P).map P.subtype →
      ∃ h v : G, h ∈ P ∧ h ∉ Subgroup.normalizer (L : Set G) ∧ h ^ p = 1 ∧ v ∈ V ∧
        v * h * v⁻¹ = h⁻¹ ∧ v ∉ Subgroup.normalizer (CFSG.conjugate V h : Set G) ∧
        (V ⊓ Subgroup.normalizer (CFSG.conjugate V h : Set G)).relIndex V = 2

open Lem20Pick in

theorem pre12_2_21_of_inv_F4 (h1222 : Stmt12_2_2_F4) (h1216 : Stmt12_2_16_F4)
    (hI62 : ASInputs.AS_I_6_2_twoCases) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V) {h v : G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hhM : h ∉ Subgroup.normalizer (L : Set G)) (hhp : h ^ p = 1) (hvV : v ∈ V)
    (hvh : v * h * v⁻¹ = h⁻¹) (hvN : v ∉ Subgroup.normalizer (CFSG.conjugate V h : Set G))
    (hidx : (V ⊓ Subgroup.normalizer (CFSG.conjugate V h : Set G)).relIndex V = 2) :
    ∃ U I : Subgroup G, I = V ⊔ CFSG.conjugate V h ∧ U = pCoreOf 2 I ∧
      U = (U ⊓ V) ⊔ (U ⊓ CFSG.conjugate V h) ∧ (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) = ⊥ ∧
      IsElemAbelian 2 U ∧ U = ⁅U, oTwoUpper I⁆ ∧
      (∃ _ : (U.subgroupOf I).Normal, Nonempty (↥I ⧸ U.subgroupOf I ≃* DihedralGroup p)) ∧
      (U ⊓ V).relIndex V = 2 ∧
      (∃ _ : IsMulCommutative ↥V, autOn U V = transvAxis ((U ⊓ V).subgroupOf V)) ∧
      U ⊓ V = V ⊓ Subgroup.normalizer (CFSG.conjugate V h : Set G) ∧
      (∀ y ∈ U, h * y * h⁻¹ = y → y = 1) ∧ h ∈ I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hpodd : Odd p := hp.odd_of_ne_two hp2

  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by
    simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hinv2 : ∀ {y : G}, y ^ 2 = 1 → y⁻¹ = y := fun hy =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hy])
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (hinv2 (hV2 _ (V.mul_mem hx hy))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv2 (hV2 y hy), hinv2 (hV2 x hx)]
  have hcV : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVc a a.2 b b.2)⟩⟩
  have hVe : IsElemAbelian 2 V := ⟨hcV, hV2⟩
  have hv2 : v ^ 2 = 1 := hV2 v hvV
  have hvinv : v⁻¹ = v := hinv2 hv2

  set A := CFSG.conjugate V h with hAdef
  have hAmem : ∀ y : G, y ∈ A ↔ h * y * h⁻¹ ∈ V := fun y => Lem21Post.mem_conjugate_iff
  have hA2 : ∀ y ∈ A, y ^ 2 = 1 := fun y hy => by
    have := hV2 _ ((hAmem y).mp hy)
    rw [conj_pow] at this
    simpa using this
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h1 := hVc _ ((hAmem x).mp hx) _ ((hAmem y).mp hy)
    have h2 : h * (x * y) * h⁻¹ = h * (y * x) * h⁻¹ := by
      calc h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
        _ = (h * y * h⁻¹) * (h * x * h⁻¹) := h1
        _ = h * (y * x) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hAe : IsElemAbelian 2 A := ⟨⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩, hA2⟩
  have hcard : Nat.card V = Nat.card A :=
    (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm

  have hTI := h1216 G T L V hyp hNE
  have hTIV : IsTISetIn V ⊤ := by
    refine ⟨le_top, fun g _ hg => ?_⟩
    rcases hTI g with h1 | h1
    · exact absurd (mem_normalizer_of_conjugate_eq h1) hg
    · exact h1
  have hAV : A ≠ V := fun h1 => hvN (h1 ▸ Subgroup.le_normalizer hvV)
  have hVA : V ⊓ A = ⊥ := (hTI h).resolve_left hAV
  have hTIA : IsTISetIn A ⊤ := by
    refine ⟨le_top, fun g _ hg => ?_⟩
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rw [mem_conjSubgroup_iff] at hx2
    have hy1 : h * x * h⁻¹ ∈ V := (hAmem x).mp hx1
    have hy2 : h * (g * x * g⁻¹) * h⁻¹ ∈ V := (hAmem _).mp hx2
    have hk : ∀ y : G, (h * g * h⁻¹) * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ =
        h * (g * y * g⁻¹) * h⁻¹ := fun y => by group
    have hy2' : h * x * h⁻¹ ∈ CFSG.conjugate V (h * g * h⁻¹) := by
      rw [Lem21Post.mem_conjugate_iff, hk]
      exact hy2
    rcases hTI (h * g * h⁻¹) with h1 | h1
    · exfalso
      apply hg
      have hkN := mem_normalizer_of_conjugate_eq h1
      rw [Subgroup.mem_normalizer_iff] at hkN ⊢
      intro y
      rw [hAmem, hAmem, ← hk]
      exact hkN _
    · have : h * x * h⁻¹ ∈ V ⊓ CFSG.conjugate V (h * g * h⁻¹) := ⟨hy1, hy2'⟩
      rw [h1, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (by simpa using this)
  have hcross : ∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥ := by
    intro g hne
    have e : conjSubgroup A g = CFSG.conjugate V (h * g) := conjSubgroup_conjSubgroup V h g
    rw [e, inf_comm]
    exact (hTI (h * g)).resolve_left fun h1 => hne (e.trans h1).symm

  have hV2card : Nat.card V ≠ 2 := by
    intro hc
    apply (hyp.irrPlus.2.2.2.2.1).ne
    refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := conj_eq_of_card_two hc (hyp.irrPlus.2.2.1 hl) hx
    calc l * x = (l * x * l⁻¹) * l := by group
      _ = x * l := by rw [this]
  have hU0ne : ASInputs.tiU V A ≠ ⊥ := by
    intro h0
    apply hV2card
    have := hidx
    rw [show V ⊓ Subgroup.normalizer (CFSG.conjugate V h : Set G) = ⊥ from h0,
      Subgroup.relIndex_bot_left] at this
    exact this
  have hU0lt : ASInputs.tiU V A < V := by
    refine lt_of_le_of_ne inf_le_left fun h0 => hvN ?_
    have : v ∈ ASInputs.tiU V A := by rw [h0]; exact hvV
    exact this.2

  obtain ⟨⟨hUB, hUBc, hXN, hYv⟩, hYn, -⟩ :=
    hI62 G V A hVe hAe hcard hTIV hTIA hcross hU0ne hU0lt
  set U₀ := ASInputs.tiU V A with hU₀
  set B := ASInputs.tiB V A with hB
  set Y := ASInputs.tiY V A with hY
  set X := ASInputs.tiX V A with hX
  have hU₀V : U₀ ≤ V := inf_le_left
  have hBA : B ≤ A := inf_le_left
  have hVX : V ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hYX : Y ≤ X := sup_le (hU₀V.trans hVX) (hBA.trans hAX)
  have hvX : v ∈ X := hVX hvV
  have hvU₀ : v ∉ U₀ := fun h0 => hvN h0.2
  obtain ⟨hU₀Y, hU₀Yv⟩ := hYv v hvV hvU₀

  have hUBcomm : ∀ a ∈ U₀, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have : ⁅a, b⁆ ∈ ⁅U₀, B⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hUBc, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hYdec : ∀ y ∈ Y, ∃ a ∈ U₀, ∃ b ∈ B, a * b = y := fun y hy =>
    Sec121Thm.exists_mul_of_mem_sup hUBcomm hy
  have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hYdec x hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hYdec y hy
    have e1 := hVc a (hU₀V ha) c (hU₀V hc)
    have e2 := hAc b (hBA hb) d (hBA hd)
    have e3 := hUBcomm a ha d hd
    have e4 := hUBcomm c hc b hb
    calc a * b * (c * d) = a * (b * c) * d := by group
      _ = a * (c * b) * d := by rw [e4]
      _ = (a * c) * (b * d) := by group
      _ = (c * a) * (d * b) := by rw [e1, e2]
      _ = c * (a * d) * b := by group
      _ = c * (d * a) * b := by rw [e3]
      _ = c * d * (a * b) := by group
  have hY2 : ∀ y ∈ Y, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hYdec y hy
    rw [pow_two, show a * b * (a * b) = (a * a) * (b * b) by
      rw [mul_assoc, ← mul_assoc b a b, ← hUBcomm a ha b hb]; group, ← pow_two, ← pow_two,
      hV2 a (hU₀V ha), hA2 b (hBA hb), one_mul]
  have hYp : IsPGroup 2 ↥Y := fun y => ⟨1, Subtype.ext (by simpa using hY2 y y.2)⟩

  have hVY : ∀ y ∈ V, y ∈ Y → y ∈ U₀ := by
    intro y hyV hyY
    have : y ∈ Y ⊓ Subgroup.centralizer ({v} : Set G) :=
      ⟨hyY, Subgroup.mem_centralizer_singleton_iff.mpr (hVc y hyV v hvV)⟩
    rwa [← hU₀Y] at this
  have hAY : ∀ y ∈ A, y ∈ Y → y ∈ B := by
    intro y hyA hyY
    obtain ⟨a, ha, b, hb, rfl⟩ := hYdec y hyY
    have haA : a ∈ A := by
      have := A.mul_mem hyA (A.inv_mem (hBA hb))
      rwa [mul_inv_cancel_right] at this
    have : a ∈ V ⊓ A := ⟨hU₀V ha, haA⟩
    rw [hVA, Subgroup.mem_bot] at this
    rw [this, one_mul]
    exact hb

  have hhinvA : h⁻¹ * v * h ∈ A := by
    rw [hAmem]
    have e : h * (h⁻¹ * v * h) * h⁻¹ = v := by group
    rw [e]
    exact hvV
  have hvh' : v * h⁻¹ * v = h := by
    have h1 : (v * h * v⁻¹)⁻¹ = h := by rw [hvh, inv_inv]
    calc v * h⁻¹ * v = v * h⁻¹ * v⁻¹ := by rw [hvinv]
      _ = (v * h * v⁻¹)⁻¹ := by group
      _ = h := h1
  have hh2X : h ^ 2 ∈ X := by
    have : v * (h⁻¹ * v * h) = h ^ 2 := by
      calc v * (h⁻¹ * v * h) = (v * h⁻¹ * v) * h := by group
        _ = h * h := by rw [hvh']
        _ = h ^ 2 := (pow_two h).symm
    rw [← this]
    exact X.mul_mem hvX (hAX hhinvA)
  have hhX : h ∈ X := by
    obtain ⟨k, hk⟩ := hpodd
    have e : h = (h ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      calc h = h ^ (p + 1) := by rw [pow_succ, hhp, one_mul]
        _ = h ^ (2 * (k + 1)) := by rw [hk]; ring_nf
    rw [e]
    exact X.pow_mem hh2X _
  have hhY : h ∉ Y := by
    intro hhY'
    have h1 := hY2 h hhY'
    have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hhp)
    rw [(Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)] at h2
    exact hh1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2))
  have hvY : v ∉ Y := fun h0 => hvU₀ (hVY v hvV h0)
  have hoh : orderOf h = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hhp hh1

  have hVp : IsPGroup 2 ↥V := fun y => ⟨1, Subtype.ext (by simpa using hV2 y y.2)⟩
  have hhN : h ∈ Subgroup.normalizer (Y : Set G) := hXN hhX
  have hvNY : v ∈ Subgroup.normalizer (Y : Set G) := hXN hvX
  have hCYh : ∀ y ∈ Y, h * y * h⁻¹ = y → y = 1 := by
    set W := Y ⊓ Subgroup.centralizer ({h} : Set G) with hW
    have hvW : v ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hvNY, mem_normalizer_centralizer_of_inv hvh⟩
    have hWp : IsPGroup 2 ↥W := hYp.to_le inf_le_left
    have hvp : IsPGroup 2 ↥(Subgroup.zpowers v) := hVp.to_le (Subgroup.zpowers_le.mpr hvV)
    have hP2 : IsPGroup 2 ↥(W ⊔ Subgroup.zpowers v) :=
      IsPGroup.to_sup_of_normal_left' hWp hvp (Subgroup.zpowers_le.mpr hvW)
    have hWbot : W = ⊥ := by
      by_contra hne
      obtain ⟨w, hwW, hw1, hwc⟩ := exists_ne_one_mem_centralizer hP2 le_sup_left
        (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hvW)) hne
      have hwv : w * v = v * w :=
        ((Subgroup.mem_centralizer_iff.mp hwc) v
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))).symm
      have hwU : w ∈ U₀ := hU₀Y ▸ ⟨hwW.1, Subgroup.mem_centralizer_singleton_iff.mpr hwv⟩
      have hwh : h * w * h⁻¹ = w := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hwW.2
        rw [← this, mul_inv_cancel_right]
      have hwA : w ∈ A := by
        rw [hAmem, hwh]
        exact hU₀V hwU
      have : w ∈ V ⊓ A := ⟨hU₀V hwU, hwA⟩
      rw [hVA, Subgroup.mem_bot] at this
      exact hw1 this
    intro y hy hyh
    have : y ∈ W := ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc y * h = (h * y * h⁻¹) * h := by rw [hyh]
        _ = h * y := by group)⟩
    rw [hWbot, Subgroup.mem_bot] at this
    exact this

  have hhO : h ∈ oTwoUpper X := mem_oTwoUpper_of_odd hhX (by rw [hoh]; exact hpodd)
  have hmemY : ∀ y ∈ Y, ⁅y, h⁆ ∈ Y := by
    intro y hy
    have h1 : h * y⁻¹ * h⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hhN y⁻¹).mp (Y.inv_mem hy)
    have e : ⁅y, h⁆ = y * (h * y⁻¹ * h⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Y.mul_mem hy h1
  have hYcomm : Y = ⁅Y, oTwoUpper X⁆ := by
    have hcl : ⁅oTwoUpper X, Y⁆ ≤ Y := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN (oTwoUpper_le X ha)) b).mp hb)
        (Y.inv_mem hb)
    refine le_antisymm ?_ ((Subgroup.commutator_comm _ _).le.trans hcl)
    let f : ↥Y → ↥Y := fun y => ⟨⁅(y : G), h⁆, hmemY y y.2⟩
    have hinj : Function.Injective f := by
      intro y₁ y₂ hy
      have h1 : ⁅(y₁ : G), h⁆ = ⁅(y₂ : G), h⁆ := congrArg Subtype.val hy
      rw [commutatorElement_def, commutatorElement_def] at h1
      have h2 : (y₂ : G)⁻¹ * y₁ = h * ((y₂ : G)⁻¹ * y₁) * h⁻¹ := by
        calc (y₂ : G)⁻¹ * y₁ =
            (y₂ : G)⁻¹ * (y₁ * h * (y₁ : G)⁻¹ * h⁻¹) * (h * y₁ * h⁻¹) := by group
          _ = (y₂ : G)⁻¹ * (y₂ * h * (y₂ : G)⁻¹ * h⁻¹) * (h * y₁ * h⁻¹) := by rw [h1]
          _ = h * ((y₂ : G)⁻¹ * y₁) * h⁻¹ := by group
      have h3 := hCYh _ (Y.mul_mem (Y.inv_mem y₂.2) y₁.2) h2.symm
      exact Subtype.ext (inv_mul_eq_one.mp h3).symm
    intro y hy
    obtain ⟨y', hy'⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨y, hy⟩
    have : ⁅(y' : G), h⁆ = y := congrArg Subtype.val hy'
    rw [← this]
    exact Subgroup.commutator_mem_commutator y'.2 hhO

  have hYXn : (Y.subgroupOf X).Normal := hYn
  set π := QuotientGroup.mk' (Y.subgroupOf X) with hπ
  have hπ1 : ∀ y : ↥X, π y = 1 ↔ (y : G) ∈ Y := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set xb := π ⟨h, hhX⟩ with hxb
  set sb := π ⟨v, hvX⟩ with hsb
  have hxbp : xb ^ p = 1 := by
    rw [hxb, ← map_pow, hπ1]
    show h ^ p ∈ Y
    rw [hhp]
    exact Y.one_mem
  have hxb1 : xb ≠ 1 := fun h0 => hhY ((hπ1 _).mp h0)
  have hsb2 : sb ^ 2 = 1 := by
    rw [hsb, ← map_pow, hπ1]
    show v ^ 2 ∈ Y
    rw [hv2]
    exact Y.one_mem
  have hsb1 : sb ≠ 1 := fun h0 => hvY ((hπ1 _).mp h0)
  have hsbx : sb * xb * sb⁻¹ = xb⁻¹ := by
    rw [hsb, hxb, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext hvh
  have hVK : V.subgroupOf X ≤ (Subgroup.closure ({xb, sb} : Set (↥X ⧸ Y.subgroupOf X))).comap π
      := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_comap]
    by_cases hyU : (y : G) ∈ U₀
    · rw [(hπ1 y).mpr (Subgroup.mem_sup_left hyU)]
      exact Subgroup.one_mem _
    · have h1 : (⟨y, hy⟩ : ↥V) * ⟨v, hvV⟩ ∈ U₀.subgroupOf V :=
        (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hyU hvU₀)
      have h2 : π (y * ⟨v, hvX⟩) = 1 :=
        (hπ1 _).mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp h1))
      rw [map_mul] at h2
      rw [eq_inv_of_mul_eq_one_left h2]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hAK : A.subgroupOf X ≤ (Subgroup.closure ({xb, sb} : Set (↥X ⧸ Y.subgroupOf X))).comap π
      := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    have hw : h * y * h⁻¹ ∈ V := (hAmem _).mp hy
    have hy' : y = (⟨h, hhX⟩ : ↥X)⁻¹ * ⟨h * y * h⁻¹, hVX hw⟩ * ⟨h, hhX⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [Subgroup.mem_comap, hy', map_mul, map_mul, map_inv]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.subset_closure (Set.mem_insert _ _))) ?_)
      (Subgroup.subset_closure (Set.mem_insert _ _))
    exact hVK (Subgroup.mem_subgroupOf.mpr hw)
  have hgen : Subgroup.closure ({xb, sb} : Set (↥X ⧸ Y.subgroupOf X)) = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf X) q
    have hy : y ∈ V.subgroupOf X ⊔ A.subgroupOf X := by
      rw [InternalSec.sup_subgroupOf_eq_top hVX hAX rfl]
      exact Subgroup.mem_top _
    exact (sup_le hVK hAK) hy
  obtain ⟨e⟩ := nonempty_mulEquiv_dihedral hp hp2 hxbp hxb1 hsb2 hsb1 hsbx hgen

  have hO2 : pCoreOf 2 X = Y := by
    refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYX hXN hYp)
    have hNX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
    have hNn : ((pCoreOf 2 X).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
    have hNp : IsPGroup 2 ↥((pCoreOf 2 X).subgroupOf X) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_equiv
        (Subgroup.subgroupOfEquivOfLe hNX).symm
    have hKn : ((((pCoreOf 2 X).subgroupOf X).map π).map e.toMonoidHom).Normal :=
      (hNn.map π (QuotientGroup.mk'_surjective _)).map e.toMonoidHom e.surjective
    have hKp : IsPGroup 2 ↥((((pCoreOf 2 X).subgroupOf X).map π).map e.toMonoidHom) :=
      (hNp.map π).map e.toMonoidHom
    have hK := eq_bot_of_isPGroup_two hp hp2 hKp
    intro n hn
    have h1 : e (π ⟨n, hNX hn⟩) ∈ (((pCoreOf 2 X).subgroupOf X).map π).map e.toMonoidHom :=
      ⟨_, ⟨⟨n, hNX hn⟩, hn, rfl⟩, rfl⟩
    rw [hK, Subgroup.mem_bot, map_eq_one_iff _ e.injective] at h1
    exact (hπ1 _).mp h1

  have hYNV : Y ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hU₀V.trans Subgroup.le_normalizer) inf_le_right
  have hYCV : Y ⊓ Subgroup.centralizer (V : Set G) = U₀ := by
    refine le_antisymm (fun y hy => ?_) (le_inf le_sup_left fun u hu =>
      Subgroup.mem_centralizer_iff.mpr fun g hg => hVc g hg u (hU₀V hu))
    rw [hU₀Y]
    exact ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hy.2 v hvV).symm)⟩
  have hv1 : v ≠ 1 := fun h0 => hvU₀ (h0 ▸ U₀.one_mem)
  have hov : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  let gh : ↥Y →* G :=
    { toFun := fun y => ⁅(y : G), v⁆
      map_one' := by simp
      map_mul' := fun y₁ y₂ => by
        simp only [Subgroup.coe_mul, commutatorElement_def]
        have hc1 : v * (y₁ : G)⁻¹ * v⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp hvNY _).mp (Y.inv_mem y₁.2)
        have hc2 : v * (y₂ : G)⁻¹ * v⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp hvNY _).mp (Y.inv_mem y₂.2)
        have e1 := hYc _ hc1 _ y₂.2
        have e2 := hYc _ y₁.2 _ y₂.2
        have e3 : ((y₁ : G) * y₂)⁻¹ = (y₁ : G)⁻¹ * (y₂ : G)⁻¹ := by rw [e2, mul_inv_rev]
        calc (y₁ : G) * y₂ * v * ((y₁ : G) * y₂)⁻¹ * v⁻¹ =
            y₁ * (y₂ * (v * (y₁ : G)⁻¹ * v⁻¹)) * (v * (y₂ : G)⁻¹ * v⁻¹) := by
              rw [e3]; group
          _ = y₁ * ((v * (y₁ : G)⁻¹ * v⁻¹) * y₂) * (v * (y₂ : G)⁻¹ * v⁻¹) := by rw [e1]
          _ = y₁ * v * (y₁ : G)⁻¹ * v⁻¹ * (y₂ * v * (y₂ : G)⁻¹ * v⁻¹) := by group }
  have hker : gh.ker = U₀.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hU₀Y]
    show ⁅(y : G), v⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h1 => ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr h1⟩,
      fun h1 => Subgroup.mem_centralizer_singleton_iff.mp h1.2⟩
  have hrange : gh.range = U₀ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      rw [hU₀Yv]
      exact Subgroup.commutator_mem_commutator y.2 (Subgroup.mem_zpowers v)
    · rw [hU₀Yv, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_mod_orderOf, hov, Nat.cast_ofNat]
      rcases Int.emod_two_eq_zero_or_one k with hk | hk
      · rw [hk, zpow_zero, commutatorElement_one_right]
        exact Subgroup.one_mem _
      · rw [hk, zpow_one]
        exact ⟨⟨a, ha⟩, rfl⟩
  have hcardA : Nat.card (autOn Y V) = Nat.card U₀ := by
    rw [card_autOn_eq_relIndex hYNV, hYCV]
    show (U₀.subgroupOf Y).index = _
    rw [← hker, Subgroup.index_ker, hrange]
  have hle : autOn Y V ≤ transvAxis (U₀.subgroupOf V) := by
    intro c hc
    obtain ⟨⟨g, hg⟩, rfl⟩ := (A4.mem_autOn_iff hYNV).mp hc
    refine ⟨fun a ha => Subtype.ext ?_, fun w => ?_⟩
    · rw [A4.actionOn_apply_coe]
      have := hYc g hg a (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))
      rw [this, mul_inv_cancel_right]
    · rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, A4.actionOn_apply_coe, Subgroup.coe_inv]
      by_cases hw : (w : G) ∈ U₀
      · have := hYc g hg w (Subgroup.mem_sup_left hw)
        rw [this, mul_inv_cancel_right, mul_inv_cancel]
        exact U₀.one_mem
      · have h1 : (w : G) * v ∈ U₀ := Subgroup.mem_subgroupOf.mp
          ((Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hw hvU₀) :
            w * ⟨v, hvV⟩ ∈ U₀.subgroupOf V)
        have hwu : (w : G) = (w * v) * v := by rw [mul_assoc, ← pow_two, hv2, mul_one]
        have hgu : g * ((w : G) * v) = ((w : G) * v) * g := hYc g hg _ (Subgroup.mem_sup_left h1)
        have hgv : ⁅g, v⁆ ∈ U₀ := hU₀Yv ▸ Subgroup.commutator_mem_commutator hg
          (Subgroup.mem_zpowers v)
        have hgvV : ⁅g, v⁆ ∈ V := hU₀V hgv
        have huc := hVc _ (hU₀V h1) _ hgvV
        rw [commutatorElement_def] at hgv huc
        have e : g * (w : G) * g⁻¹ * (w : G)⁻¹ = g * v * g⁻¹ * v⁻¹ := by
          calc g * (w : G) * g⁻¹ * (w : G)⁻¹ =
              g * ((w : G) * v * v) * g⁻¹ * ((w : G) * v * v)⁻¹ := by rw [← hwu]
            _ = (g * ((w : G) * v)) * v * g⁻¹ * v⁻¹ * ((w : G) * v)⁻¹ := by group
            _ = ((w : G) * v) * (g * v * g⁻¹ * v⁻¹) * ((w : G) * v)⁻¹ := by rw [hgu]; group
            _ = (g * v * g⁻¹ * v⁻¹) * ((w : G) * v) * ((w : G) * v)⁻¹ := by rw [huc]
            _ = g * v * g⁻¹ * v⁻¹ := by group
        rw [e]
        exact hgv
  have htr : autOn Y V = transvAxis (U₀.subgroupOf V) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardA]
    calc Nat.card ↥(transvAxis (U₀.subgroupOf V)) ≤ Nat.card ↥(U₀.subgroupOf V) :=
          card_transvAxis_le hidx (w₀ := ⟨v, hvV⟩) hvU₀
      _ = Nat.card U₀ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀V).toEquiv

  have hYV : Y ⊓ V = U₀ :=
    le_antisymm (fun y hy => hVY y hy.2 hy.1) (le_inf le_sup_left hU₀V)
  have hYA : Y ⊓ A = B :=
    le_antisymm (fun y hy => hAY y hy.2 hy.1) (le_inf le_sup_right hBA)
  refine ⟨Y, X, rfl, hO2.symm, ?_, ?_, ?_, hYcomm, ⟨hYn, ⟨e⟩⟩, ?_, ⟨hcV, ?_⟩, hYV, hCYh, hhX⟩
  · rw [hYV, hYA]
  · rw [hYV, hYA]
    exact hUB
  · exact ⟨⟨⟨fun a b => Subtype.ext (hYc a a.2 b b.2)⟩⟩, hY2⟩
  · rw [hYV]
    exact hidx
  · rw [hYV]
    exact htr

theorem lem12220Choice_of_F4 (h1222 : Stmt12_2_2_F4) (h1216 : Stmt12_2_16_F4)
    (hI62 : ASInputs.AS_I_6_2_twoCases) (hcp : CoprimePick_F4) : Lem12220Choice_F4 := by
  intro G _ _ T L V H P p hyp hNE hHs hsolv hp hp2 hPp hPH hPi hHPT hΦ
  obtain ⟨h, v, hhP, hhM, hhp, hvV, hvh, hvN, hidx⟩ :=
    hcp G T L V H P p hyp hNE hHs hsolv hp hp2 hPp hPH hPi hHPT hΦ
  obtain ⟨U, I, hI, hU, hUdec, hUinf, hUe, hUc, hD, hidx', htr, -⟩ :=
    pre12_2_21_of_inv_F4 h1222 h1216 hI62 hyp hNE hp hp2 hhM hhp hvV hvh hvN hidx
  exact ⟨U, I, h, hhP, hhM, hI, hU, hUdec, hUinf, hUe, hUc, hD, hidx', htr⟩

theorem lem12220PickFull_of_pick_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h1216 : Stmt12_2_16_F4)
    (hI62 : ASInputs.AS_I_6_2_twoCases) (hcp : CoprimePick_F4) : Lem12220PickFull_F4 :=
  lem12220PickFull_of_F4 h331 (lem12220Choice_of_F4 h1222 h1216 hI62 hcp)

end CFSG.Quasithin.H13
