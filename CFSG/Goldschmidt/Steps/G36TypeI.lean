module

public import CFSG.Goldschmidt.Steps.G36Basic
import CFSG.Walter.Bender1970.S38.AbelianNormal
import CFSG.Walter.PSL2Facts.Even
import CFSG.Walter.W67.Section4.Cor44A
public import CFSG.Goldschmidt.StatementsG
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.Goldschmidt

open CFSG.Open

variable {L : Type} [Group L] [Finite L] {A₀ : Subgroup L} {T₀ : Sylow 2 L}

structure G36Borel (L : Type*) [Group L] (A₀ : Subgroup L) (T₀ : Sylow 2 L)
    (Tb D : Subgroup (L ⧸ Subgroup.center L)) (y : L) : Prop where
  tb_eq : Tb = (T₀ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L))
  odd : Odd (orderOf y)
  zpowers_eq : Subgroup.zpowers (y : L ⧸ Subgroup.center L) = D
  le_normalizer : D ≤ Subgroup.normalizer (Tb : Set (L ⧸ Subgroup.center L))
  inf_eq : Tb ⊓ D = ⊥
  sup_eq : Tb ⊔ D = Subgroup.normalizer (Tb : Set (L ⧸ Subgroup.center L))
  map_eq : A₀.map (QuotientGroup.mk' (Subgroup.center L)) =
    Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L))
  not_fixed : ∀ a ∈ Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L)), a ≠ 1 →
    (y : L ⧸ Subgroup.center L) * a * (y : L ⧸ Subgroup.center L)⁻¹ ≠ a
  trans : ∀ a ∈ Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L)),
    ∀ b ∈ Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L)), a ≠ 1 → b ≠ 1 →
      ∃ k : ℕ, ((y : L ⧸ Subgroup.center L) ^ k)⁻¹ * a * (y : L ⧸ Subgroup.center L) ^ k = b
  normalizer_iff : ∀ n : L, n ∈ Subgroup.normalizer (A₀ : Set L) ↔
    (n : L ⧸ Subgroup.center L) ∈ Subgroup.normalizer (Tb : Set (L ⧸ Subgroup.center L))
  irred : ¬ IsMulCommutative Tb → ∀ X : Subgroup (L ⧸ Subgroup.center L),
    Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L)) ≤ X → X ≤ Tb →
    D ≤ Subgroup.normalizer (X : Set (L ⧸ Subgroup.center L)) →
    X = Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L)) ∨ X = Tb
  comm_eq : ⁅Tb, D⁆ = Tb
  sz : ∀ n : ℕ, 1 ≤ n → Nonempty (L ⧸ Subgroup.center L ≃* Sz n) →
    Nat.card (Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L)) :
      Subgroup (L ⧸ Subgroup.center L)) = 2 ^ (2 * n + 1) ∧
    Nat.card Tb = 2 ^ (2 * (2 * n + 1)) ∧ Nat.card D = 2 ^ (2 * n + 1) - 1

theorem isGoldTypeI_quotient_center {Q : Type*} [Group Q]
    (hZ : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥) (hI : IsGoldTypeI Q) :
    IsGoldTypeI (Q ⧸ Subgroup.center Q) := by
  let e₀ : (Q ⧸ Subgroup.center Q) ⧸ Subgroup.center (Q ⧸ Subgroup.center Q) ≃*
      Q ⧸ Subgroup.center Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e₀.trans e⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e₀.trans e⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, ⟨e₀.trans e⟩⟩)

omit [Group L] [Finite L] in
theorem normalizer_le_normalizer_inf_centralizer {Q : Type*} [Group Q] [Finite Q]
    (T : Subgroup Q) :
    Subgroup.normalizer (T : Set Q) ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (T : Set Q) : Subgroup Q) : Set Q) := by
  intro x hx
  apply mem_normalizer_of_conj_mem
  intro z hz
  obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hx z).mp hzT, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have ht' : x⁻¹ * t * x ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (T : Set Q)).inv_mem hx) t).mp ht
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hzC _ ht'
  calc t * (x * z * x⁻¹) = x * ((x⁻¹ * t * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * t * x)) * x⁻¹ := by rw [hc]
    _ = x * z * x⁻¹ * t := by group

theorem exists_g36Borel (h32 : S_G32) (h : G36Hyp L A₀ T₀) (hI : IsGoldTypeI L) :
    ∃ D : Subgroup (L ⧸ Subgroup.center L), ∃ y : L,
      G36Borel L A₀ T₀ ((T₀ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L))) D y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center L with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have : IsSimpleGroup (L ⧸ Z) := h.quasisimple.2
  have hnab : ∃ a b : L ⧸ Z, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L
      h.quasisimple
  have hZb : Subgroup.center (L ⧸ Z) = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot (L ⧸ Z) hnab
  have hI' : IsGoldTypeI (L ⧸ Z) := isGoldTypeI_quotient_center hZb hI
  set Tb := (T₀ : Subgroup L).map π with hTbdef
  set Tb' : Sylow 2 (L ⧸ Z) := T₀.mapSurjective hπs with hTb'
  have hTbcoe : (Tb' : Subgroup (L ⧸ Z)) = Tb := Sylow.coe_mapSurjective _ _
  obtain ⟨D, hDN, hDcyc, hDodd, hTD, hTDsup, -, hTDcomm, hΩ, htransD, hnab', hPSL, hSz, hU,
    -, -, -, -, hmax⟩ := h32 (L ⧸ Z) hI' Tb'
  rw [hTbcoe] at hDN hTD hTDsup hTDcomm hΩ htransD hnab' hPSL hSz hU hmax
  set Zb := Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Z)) with hZbdef
  have hZb4 : 4 ≤ Nat.card Zb := by
    rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    ·
      have hab : Zb = Tb := by
        apply le_antisymm inf_le_left
        intro t ht
        refine ⟨ht, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
        set S' : Sylow 2 _ := Tb'.mapSurjective (f := e.toMonoidHom) e.surjective with hS'
        have hS'coe : (S' : Subgroup _) = (Tb' : Subgroup (L ⧸ Z)).map e.toMonoidHom :=
          Sylow.coe_mapSurjective _ _
        rw [hTbcoe] at hS'coe
        obtain ⟨hel, -⟩ := CFSG.Walter.psl2_even_sylow_two (by omega) S'
        have hc := hel.toIsMulCommutative.is_comm.comm
          (⟨e s, by rw [hS'coe]; exact ⟨s, hs, rfl⟩⟩ : (S' : Subgroup _))
          ⟨e t, by rw [hS'coe]; exact ⟨t, ht, rfl⟩⟩
        apply e.injective
        rw [map_mul, map_mul]
        exact congrArg Subtype.val hc
      rw [hab, (hPSL n hn ⟨e⟩).1]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [(hSz n hn ⟨e⟩).1]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [(hU n hn ⟨e⟩).1]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨a₀, ha₀A, ha₀Z⟩ : ∃ a ∈ A₀, a ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact h.not_le_center hcon
  have ha₀1 : π a₀ ≠ 1 := by
    rw [hπdef, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact ha₀Z
  have hAΩ : A₀.map π ≤ Omega1 Tb := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.subset_closure ⟨⟨a, h.le ha, rfl⟩, by rw [← map_pow, h.sq_eq_one ha, map_one]⟩
  have hmap : A₀.map π = Zb := by
    rw [← hΩ]
    refine le_antisymm hAΩ ?_
    rw [Omega1, Subgroup.closure_le]
    rintro t ⟨htT, ht2⟩
    by_cases ht1 : t = 1
    · rw [ht1]
      exact (A₀.map π).one_mem
    obtain ⟨d, hdD, hd⟩ := htransD (π a₀) (hAΩ ⟨a₀, ha₀A, rfl⟩) t
      (Subgroup.subset_closure ⟨htT, ht2⟩) ha₀1 ht1
    obtain ⟨g, rfl⟩ := hπs d
    have hgT : g⁻¹ * a₀ * g ∈ (T₀ : Subgroup L) := by
      refine h.mem_sylow_of_mk_mem (k := 1) ?_ ?_
      · rw [pow_one, sq, show g⁻¹ * a₀ * g * (g⁻¹ * a₀ * g) = g⁻¹ * (a₀ * a₀) * g by group,
          ← sq, h.sq_eq_one ha₀A, mul_one, inv_mul_cancel]
      · change π (g⁻¹ * a₀ * g) ∈ Tb
        rw [map_mul, map_mul, map_inv, hd]
        exact htT
    refine ⟨g⁻¹ * a₀ * g, h.closed a₀ ha₀A g hgT, ?_⟩
    rw [map_mul, map_mul, map_inv, hd]
  obtain ⟨yb, hyb⟩ := IsCyclic.exists_generator (α := D)
  have hDyb : D = Subgroup.zpowers (yb : L ⧸ Z) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hyb ⟨x, hx⟩)
      have hj' : (yb : L ⧸ Z) ^ j = x := by
        have := congrArg Subtype.val hj
        rwa [Subgroup.coe_zpow] at this
      rw [← hj']
      exact Subgroup.zpow_mem_zpowers _ j
    · exact (Subgroup.zpowers_le).mpr yb.2
  obtain ⟨g, hg⟩ := hπs yb
  have hgodd : Odd (orderOf (π g)) := by
    rw [hg, Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hDodd (orderOf_dvd_natCard yb)
  obtain ⟨k, hkodd, hkz⟩ := exists_odd_pow g
  set y := g ^ k with hy
  have hyD : Subgroup.zpowers (y : L ⧸ Z) = D := by
    change Subgroup.zpowers (π y) = D
    rw [hkz π hgodd, hg]
    exact hDyb.symm
  have hnf : ∀ a ∈ Zb, a ≠ 1 → (y : L ⧸ Z) * a * (y : L ⧸ Z)⁻¹ ≠ a := by
    intro a ha ha1 hfix
    obtain ⟨b, hb, hb1, hba⟩ := CFSG.Walter.exists_mem_ne_one_ne (Q := Zb) (by omega) a
    obtain ⟨d, hdD, hd⟩ := htransD a (by rw [hΩ]; exact ha) b (by rw [hΩ]; exact hb) ha1 hb1
    rw [← hyD] at hdD
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hdD
    have hc : Commute (y : L ⧸ Z) a := by
      show (y : L ⧸ Z) * a = a * (y : L ⧸ Z)
      calc (y : L ⧸ Z) * a = (y : L ⧸ Z) * a * (y : L ⧸ Z)⁻¹ * (y : L ⧸ Z) := by group
        _ = a * (y : L ⧸ Z) := by rw [hfix]
    have hcj : Commute ((y : L ⧸ Z) ^ j) a := hc.zpow_left j
    have : ((y : L ⧸ Z) ^ j)⁻¹ * a * (y : L ⧸ Z) ^ j = a := by
      rw [hcj.inv_left.eq, inv_mul_cancel_right]
    exact hba (hd.symm.trans this)
  have htr : ∀ a ∈ Zb, ∀ b ∈ Zb, a ≠ 1 → b ≠ 1 →
      ∃ k : ℕ, ((y : L ⧸ Z) ^ k)⁻¹ * a * (y : L ⧸ Z) ^ k = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨d, hdD, hd⟩ := htransD a (by rw [hΩ]; exact ha) b (by rw [hΩ]; exact hb) ha1 hb1
    rw [← hyD] at hdD
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers.mpr hdD : d ∈ Submonoid.powers _)
    refine ⟨m, ?_⟩
    have hm' : (y : L ⧸ Z) ^ m = d := hm
    rw [hm']
    exact hd
  have ha₀Zb : π a₀ ∈ Zb := hmap ▸ ⟨a₀, ha₀A, rfl⟩
  have hNZ : Subgroup.normalizer (Zb : Set (L ⧸ Z)) ≤ Subgroup.normalizer (Tb : Set (L ⧸ Z)) := by
    apply hmax
    · intro t ht
      apply mem_normalizer_of_conj_mem
      intro x hx
      have hxc := Subgroup.mem_centralizer_iff.mp hx.2 t ht
      rw [hxc, mul_inv_cancel_right]
      exact hx
    · intro htop
      have : Zb.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Zb with hbot | htop'
      · rw [hbot, Subgroup.mem_bot] at ha₀Zb
        exact ha₀1 ha₀Zb
      · obtain ⟨a, b, hab⟩ := hnab
        have ha : a ∈ Zb := htop' ▸ Subgroup.mem_top a
        have hb : b ∈ Zb := htop' ▸ Subgroup.mem_top b
        exact hab (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
  have hnorm : ∀ n : L, n ∈ Subgroup.normalizer (A₀ : Set L) ↔
      (n : L ⧸ Z) ∈ Subgroup.normalizer (Tb : Set (L ⧸ Z)) := by
    intro n
    constructor
    · intro hn
      apply hNZ
      rw [← hmap]
      exact Subgroup.le_normalizer_map π ⟨n, hn, rfl⟩
    · intro hn
      apply mem_normalizer_of_conj_mem
      intro a ha
      have h1 : π (n * a * n⁻¹) ∈ Zb := by
        rw [map_mul, map_mul, map_inv]
        have hnZ := normalizer_le_normalizer_inf_centralizer Tb hn
        have hpa : π a ∈ Zb := hmap ▸ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hnZ (π a)).mp hpa
      have h2 : n * a * n⁻¹ ∈ (T₀ : Subgroup L) := by
        refine h.mem_sylow_of_mk_mem (k := 1) ?_ h1.1
        rw [pow_one, conj_pow, h.sq_eq_one ha, mul_one, mul_inv_cancel]
      have := h.closed a ha n⁻¹ (by rwa [inv_inv])
      rwa [inv_inv] at this
  exact ⟨D, y, ⟨rfl, hkodd, hyD, hDN, hTD, hTDsup, hmap, hnf, htr, hnorm,
    fun hnc => (hnab' hnc).2.2, hTDcomm, hSz⟩⟩

namespace G36Borel

variable {Tb D : Subgroup (L ⧸ Subgroup.center L)} {y : L}

omit [Finite L] in
theorem mem_normalizer (hB : G36Borel L A₀ T₀ Tb D y) :
    y ∈ Subgroup.normalizer (A₀ : Set L) :=
  (hB.normalizer_iff y).mpr (hB.le_normalizer (hB.zpowers_eq ▸ Subgroup.mem_zpowers _))

omit [Finite L] in
theorem mem_center_of_commute (hB : G36Borel L A₀ T₀ Tb D y) {a : L} (ha : a ∈ A₀)
    (hay : a * y = y * a) : a ∈ Subgroup.center L := by
  by_contra haZ
  have ha1 : (a : L ⧸ Subgroup.center L) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have haZb : (a : L ⧸ Subgroup.center L) ∈
      Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L)) :=
    hB.map_eq ▸ ⟨a, ha, rfl⟩
  apply hB.not_fixed _ haZb ha1
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← hay,
    mul_inv_cancel_right]

theorem trans_commutator (h : G36Hyp L A₀ T₀) (hB : G36Borel L A₀ T₀ Tb D y) :
    ∀ b ∈ ⁅A₀, Subgroup.zpowers y⁆, ∀ c ∈ ⁅A₀, Subgroup.zpowers y⁆, b ≠ 1 → c ≠ 1 →
      ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyN := hB.mem_normalizer
  have hcop : Nat.Coprime (Nat.card A₀) (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]
    obtain ⟨n, hn⟩ := (T₀.isPGroup'.to_le h.le).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hB.odd)
  obtain ⟨hdisj, -, hle, -⟩ := CFSG.Walter.W67.coprime_decomp (A := A₀)
    (E := Subgroup.zpowers y) (fun x hx z hz => h.mul_comm hx hz) rfl hyN hcop
  set W := ⁅A₀, Subgroup.zpowers y⁆ with hWdef
  have hWcomm : ⁅Subgroup.zpowers y, A₀⁆ = W := Subgroup.commutator_comm _ _
  rw [hWcomm] at hdisj hle
  have hWZ : ∀ w ∈ W, w ∈ Subgroup.center L → w = 1 := by
    intro w hw hwZ
    have : w ∈ A₀ ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set L) ⊓ W :=
      ⟨⟨hle hw, Subgroup.mem_centralizer_iff.mpr fun g _ => (Subgroup.mem_center_iff.mp hwZ g)⟩,
        hw⟩
    rw [hdisj] at this
    exact this
  have hbar : ∀ w ∈ W, w ≠ 1 → (w : L ⧸ Subgroup.center L) ∈
      Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Subgroup.center L)) ∧
        (w : L ⧸ Subgroup.center L) ≠ 1 := by
    intro w hw hw1
    refine ⟨hB.map_eq ▸ ⟨w, hle hw, rfl⟩, fun h1 => hw1 (hWZ w hw ?_)⟩
    exact (QuotientGroup.eq_one_iff w).mp h1
  intro b hb c hc hb1 hc1
  obtain ⟨hbZ, hb1'⟩ := hbar b hb hb1
  obtain ⟨hcZ, hc1'⟩ := hbar c hc hc1
  obtain ⟨k, hk⟩ := hB.trans _ hbZ _ hcZ hb1' hc1'
  refine ⟨k, ?_⟩
  have hyW : (y ^ k)⁻¹ ∈ Subgroup.normalizer (W : Set L) :=
    Subgroup.normalizer_commutator_ge_right A₀ (Subgroup.zpowers y)
      ((Subgroup.zpowers y).inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) k))
  have hb'W : (y ^ k)⁻¹ * b * y ^ k ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp hyW b).mp hb
    rwa [inv_inv] at this
  have hb'c : (((y ^ k)⁻¹ * b * y ^ k : L) : L ⧸ Subgroup.center L) = c := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
    exact hk
  have := hWZ _ (W.mul_mem (W.inv_mem hb'W) hc) (by rw [← QuotientGroup.eq]; exact hb'c)
  rw [inv_mul_eq_one] at this
  exact this

omit [Finite L] in
theorem exists_eq_mul (hB : G36Borel L A₀ T₀ Tb D y) {z : L}
    (hz : z ∈ Subgroup.normalizer (A₀ : Set L)) :
    ∃ t ∈ (T₀ : Subgroup L), ∃ c ∈ Subgroup.center L, ∃ j : ℤ, z = t * c * y ^ j := by
  have hzN := (hB.normalizer_iff z).mp hz
  rw [← hB.sup_eq] at hzN
  have hzN' : (z : L ⧸ Subgroup.center L) ∈ ((Tb ⊔ D : Subgroup _) : Set _) := hzN
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Tb D hB.le_normalizer] at hzN'
  obtain ⟨tb, htb, d, hd, htd⟩ := Set.mem_mul.mp hzN'
  rw [← hB.zpowers_eq] at hd
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  rw [hB.tb_eq] at htb
  obtain ⟨t, ht, htt⟩ := htb
  refine ⟨t, ht, t⁻¹ * z * (y ^ j)⁻¹, ?_, j, by group⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, ← htd]
  have htt' : (t : L ⧸ Subgroup.center L) = tb := htt
  rw [htt']
  group

omit [Finite L] in
theorem mem_sup_of_commute (hB : G36Borel L A₀ T₀ Tb D y)
    (hc : ∀ t ∈ (T₀ : Subgroup L), ∀ a ∈ A₀, t * a = a * t) {z : L}
    (hz : z ∈ Subgroup.normalizer (A₀ : Set L)) :
    z ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A₀ : Set L) := by
  obtain ⟨t, ht, c, hcZ, j, rfl⟩ := hB.exists_eq_mul hz
  have htC : t ∈ Subgroup.centralizer (A₀ : Set L) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => (hc t ht a ha).symm
  have hcC : c ∈ Subgroup.centralizer (A₀ : Set L) :=
    Subgroup.mem_centralizer_iff.mpr fun a _ => (Subgroup.mem_center_iff.mp hcZ a)
  exact Subgroup.mul_mem _ (le_sup_right (a := Subgroup.zpowers y) (Subgroup.mul_mem _ htC hcC))
    (le_sup_left (b := Subgroup.centralizer (A₀ : Set L)) (Subgroup.zpow_mem_zpowers y j))

theorem g36Local_of_commute (h : G36Hyp L A₀ T₀) (hB : G36Borel L A₀ T₀ Tb D y)
    (hc : ∀ t ∈ (T₀ : Subgroup L), ∀ a ∈ A₀, t * a = a * t) : G36Local L A₀ :=
  ⟨y, hB.mem_normalizer, hB.odd, hB.trans_commutator h,
    fun _ ha hay => hB.mem_center_of_commute ha hay,
    Or.inl ⟨0, by rw [pow_zero]; exact Subgroup.one_mem _,
      fun _ hz _ => hB.mem_sup_of_commute hc hz⟩⟩

end G36Borel

end CFSG.Goldschmidt
