module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Cyc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415NotSylow
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBTheta

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem mem_zpowers_of_orderOf_eq {G : Type*} [Group G] [Finite G] {ρ x y : G}
    (hx : x ∈ zpowers ρ) (hy : y ∈ zpowers ρ) (hxy : orderOf x = orderOf y) :
    x ∈ zpowers y := by
  have hxC : zpowers x ≤ zpowers ρ := zpowers_le.mpr hx
  have hyC : zpowers y ≤ zpowers ρ := zpowers_le.mpr hy
  have h1 : (zpowers x).subgroupOf (zpowers ρ) = (zpowers y).subgroupOf (zpowers ρ) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_congr (subgroupOfEquivOfLe hxC).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hyC).toEquiv, Nat.card_zpowers, Nat.card_zpowers, hxy]
  have h2 : (⟨x, hx⟩ : ↥(zpowers ρ)) ∈ (zpowers x).subgroupOf (zpowers ρ) :=
    mem_subgroupOf.mpr (mem_zpowers x)
  rw [h1] at h2
  exact mem_subgroupOf.mp h2

theorem exists_four {G : Type*} [Group G] [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hshape : IsCyclic ↥Q ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥Q ≃* DihedralGroup (2 ^ k)))
    {b : G} (hbQ : b ∈ Q) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hbc : ∀ x ∈ Q, x * b = b * x) {q : G} (hqQ : q ∈ Q) (hq : q * q ≠ 1) :
    ∃ v ∈ Q, orderOf v = 4 ∧ v ^ 2 = b ∧ ∀ x ∈ Q, orderOf x = 4 → x ∈ zpowers v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρQ, hρ, hbρ⟩ : ∃ ρ ∈ Q, (∀ x ∈ Q, x * x ≠ 1 → x ∈ zpowers ρ) ∧
      b ∈ zpowers ρ := by
    rcases hshape with hcyc | ⟨k, hk, ⟨e⟩⟩
    · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Q)
      have hall : ∀ x ∈ Q, x ∈ zpowers (g : G) := by
        intro x hx
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
        rw [mem_zpowers_iff]
        exact ⟨n, by rw [← Subgroup.coe_zpow, hn]⟩
      exact ⟨g, g.2, fun x hx _ => hall x hx, hall b hbQ⟩
    · have hrot : ∀ x : ↥Q, (∃ i, e x = DihedralGroup.r i) →
          (x : G) ∈ zpowers ((e.symm (DihedralGroup.r 1) : ↥Q) : G) := by
        rintro x ⟨i, hi⟩
        rw [mem_zpowers_iff]
        refine ⟨(i.val : ℤ), ?_⟩
        rw [← Subgroup.coe_zpow, ← map_zpow, DihedralGroup.r_one_zpow]
        congr 1
        apply e.injective
        rw [MulEquiv.apply_symm_apply, hi]
        congr 1
        simp
      refine ⟨_, (e.symm (DihedralGroup.r 1)).2, fun x hx hx2 => ?_, ?_⟩
      · refine hrot ⟨x, hx⟩ ?_
        rcases h : e ⟨x, hx⟩ with i | i
        · exact ⟨i, rfl⟩
        · exfalso
          apply hx2
          have h1 : (⟨x, hx⟩ : ↥Q) * ⟨x, hx⟩ = 1 := by
            apply e.injective
            rw [map_mul, h, DihedralGroup.sr_mul_self, map_one]
          exact congrArg Subtype.val h1
      ·
        refine hrot ⟨b, hbQ⟩ ?_
        rcases h : e ⟨b, hbQ⟩ with i | i
        · exact ⟨i, rfl⟩
        · exfalso
          have hc : e ⟨b, hbQ⟩ * DihedralGroup.r 1 = DihedralGroup.r 1 * e ⟨b, hbQ⟩ := by
            have h1 : (⟨b, hbQ⟩ : ↥Q) * e.symm (DihedralGroup.r 1) =
                e.symm (DihedralGroup.r 1) * ⟨b, hbQ⟩ :=
              Subtype.ext (hbc _ (e.symm (DihedralGroup.r 1)).2).symm
            have h2 := congrArg e h1
            rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
          rw [h, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq] at hc
          have h4 : (2 : ZMod (2 ^ k)) = 0 := by linear_combination hc
          have h5 : 4 ≤ 2 ^ k ∨ 2 ^ k = 2 := by
            rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
            · right; norm_num
            · left
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
          rcases h5 with h5 | h5
          · have h6 : ((2 : ℕ) : ZMod (2 ^ k)) = 0 := by exact_mod_cast h4
            rw [ZMod.natCast_eq_zero_iff] at h6
            have := Nat.le_of_dvd (by norm_num) h6
            omega
          ·
            exfalso
            apply hq
            have h7 : ∀ y : DihedralGroup (2 ^ k), y * y = 1 := by
              rw [h5]
              decide
            have h8 : (⟨q, hqQ⟩ : ↥Q) * ⟨q, hqQ⟩ = 1 := by
              apply e.injective
              rw [map_mul, h7, map_one]
            exact congrArg Subtype.val h8
  have hqρ : q ∈ zpowers ρ := hρ q hqQ hq
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨q, hqQ⟩
  rw [Subgroup.orderOf_mk] at ha
  have ha2 : 2 ≤ a := by
    by_contra hlt
    push Not at hlt
    apply hq
    have h1 : q ^ 2 = 1 := by
      have h2 : orderOf q ∣ 2 := by
        rw [ha]
        interval_cases a <;> norm_num
      exact orderOf_dvd_iff_pow_eq_one.mp h2
    rw [← sq]
    exact h1
  have h4 : 4 ∣ orderOf q := by
    rw [ha, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 ha2
  set v := q ^ (orderOf q / 4) with hv
  have hvo : orderOf v = 4 := by
    rw [hv, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos q) h4) (by norm_num)).ne'
      (Nat.div_dvd_of_dvd h4), Nat.div_div_self h4 (orderOf_pos q).ne']
  have hvρ : v ∈ zpowers ρ := pow_mem hqρ _
  have hvQ : v ∈ Q := pow_mem hqQ _
  refine ⟨v, hvQ, hvo, ?_, fun x hx hx4 => ?_⟩
  ·
    have hv2o : orderOf (v ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hvo]; norm_num), hvo]
    have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
    have h1 := mem_zpowers_of_orderOf_eq hbρ (pow_mem hvρ 2) (hbo.trans hv2o.symm)
    have hv4 : v ^ 2 * v ^ 2 = 1 := by
      rw [← pow_add, show 2 + 2 = 4 by norm_num, ← hvo, pow_orderOf_eq_one]
    rcases mem_zpowers_two hv4 h1 with h2 | h2
    · exact absurd h2 hb1
    · exact h2.symm
  · have hx2 : x * x ≠ 1 := by
      intro h1
      have h2 : x ^ 2 = 1 := by rw [sq]; exact h1
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hx4] at this
      norm_num at this
    exact mem_zpowers_of_orderOf_eq (hρ x hx hx2) hvρ (hx4.trans hvo.symm)

theorem normalizer_le_of_not_elem {X : Type} [Group X] [Finite X] {β t : X}
    (htM : t ∈ centralizer ({β} : Set X)) (ht2 : t * t = 1) {Kb₁ Kb₂ : Subgroup (MBar β)}
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, htM⟩))
    {W : Subgroup X} (hW : IsSylowOf 2 W (centralizer {β})) (htW : t ∈ W) (hβW : β ∈ W)
    (hβ2 : β * β = 1) (hA : AutPSL2RCentralizerInput) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlie : Blueprint.LieModel ↥Kb₁ .PSL 2 p n)
    (h8 : 4 < Nat.card ↥(barOf (centralizer {β}) W ⊓ Kb₁))
    (hQC : centralizer ((layer (MBar β) : Subgroup (MBar β)) : Set (MBar β)) ≤
      pCore 2 (MBar β))
    (hQt : pCore 2 (MBar β) ⊓ centralizer {(QuotientGroup.mk ⟨t, htM⟩ : MBar β)} =
      zpowers (betaBar β))
    (hshape : IsCyclic ↥(pCore 2 (MBar β)) ∨
      ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥(pCore 2 (MBar β)) ≃* DihedralGroup (2 ^ k)))
    (hβ1 : betaBar β ≠ 1) (hq : ∃ q ∈ pCore 2 (MBar β), q * q ≠ 1) :
    normalizer (W : Set X) ≤ centralizer {β} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({β} : Set X) with hMdef
  have hWM : W ≤ M := hW.le
  have hWp := hW.isPGroup
  have hE : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  set tb : MBar β := QuotientGroup.mk ⟨t, htM⟩ with htb
  have htb2 : tb * tb = 1 := by
    rw [htb, ← QuotientGroup.mk_mul]
    have : (⟨t, htM⟩ : ↥M) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
    rw [this, QuotientGroup.mk_one]
  have hWb : IsSylowOf 2 (barOf M W) ⊤ := isSylowOf_barOf hW
  have htbW : tb ∈ barOf M W := mk_mem_barOf htM htW
  have hQn : (pCore 2 (MBar β)).Normal := pCore_normal
  have hQp : IsPGroup 2 ↥(pCore 2 (MBar β)) := pCore_isPGroup
  have hβM : β ∈ M := mem_centralizer_singleton_iff.mpr rfl
  have hbbQ : betaBar β ∈ pCore 2 (MBar β) := by
    have : betaBar β ∈ pCore 2 (MBar β) ⊓ centralizer {tb} := hQt ▸ mem_zpowers _
    exact (mem_inf.mp this).1
  have hbb2 : betaBar β * betaBar β = 1 := by
    rw [betaBar, ← QuotientGroup.mk_mul]
    have : (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥M) *
        ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ = 1 := Subtype.ext hβ2
    rw [this, QuotientGroup.mk_one]
  have hbbc : ∀ x ∈ pCore 2 (MBar β), x * betaBar β = betaBar β * x := fun x _ =>
    (mem_center_iff.mp (betaBar_mem_center β) x)
  obtain ⟨q, hqQ, hq'⟩ := hq
  obtain ⟨vb, hvbQ, hvbo, hvb2, hvb4⟩ := exists_four hQp hshape hbbQ hbb2 hβ1 hbbc hqQ hq'
  have hQW : pCore 2 (MBar β) ≤ barOf M W := by
    have h1 : IsPGroup 2 ↥(barOf M W ⊔ pCore 2 (MBar β)) :=
      hWb.isPGroup.to_sup_of_normal_right hQp
    have h2 := hWb.eq_of_le le_sup_left le_top h1
    rw [← h2]
    exact le_sup_right
  have hinj : ∀ {x y : X} (hx : x ∈ W) (hy : y ∈ W),
      (QuotientGroup.mk ⟨x, hWM hx⟩ : MBar β) = QuotientGroup.mk ⟨y, hWM hy⟩ → x = y :=
    fun hx hy h1 => mk_injOn hWM hWp hx hy h1
  have hord : ∀ {y : X} (hy : y ∈ W),
      orderOf (QuotientGroup.mk ⟨y, hWM hy⟩ : MBar β) = orderOf y := by
    intro y hy
    have h1 := orderOf_injective (barHom hWM) (barHom_injective hWM hWp) ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at h1
    exact h1
  have hzpow : ∀ {y g : X} (hy : y ∈ W) (hg : g ∈ W), g * y * g⁻¹ ∈ zpowers y →
      (QuotientGroup.mk ⟨g, hWM hg⟩ : MBar β) * QuotientGroup.mk ⟨y, hWM hy⟩ *
        (QuotientGroup.mk ⟨g, hWM hg⟩)⁻¹ ∈ zpowers (QuotientGroup.mk ⟨y, hWM hy⟩ : MBar β) := by
    intro y g hy hg h1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    rw [mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk
  have key : ∀ y ∈ W, orderOf y = 4 → (∀ g ∈ W, g * y * g⁻¹ ∈ zpowers y) → y ^ 2 = β := by
    intro y hyW hy4 hyn
    set yb : MBar β := QuotientGroup.mk ⟨y, hWM hyW⟩ with hyb
    have hybo : orderOf yb = 4 := (hord hyW).trans hy4
    have hybn : ∀ g ∈ barOf M W, g * yb * g⁻¹ ∈ zpowers yb := by
      rintro _ ⟨g, hg, rfl⟩
      have hg' : (g : X) ∈ W := hg
      exact hzpow hyW hg' (hyn g hg')
    have h1 := hprod.sq_comm_of_cyclic hE hA hp hp2 hlie hWb h8 htbW htb2 hybo hybn
    have h2 : yb ^ 2 ∈ pCore 2 (MBar β) :=
      hQC (mem_centralizer_iff.mpr fun e he => (h1 e he).symm)
    have h3 : yb ^ 2 ∈ centralizer {tb} := by
      rw [mem_centralizer_singleton_iff]
      have h4 := hybn tb htbW
      have h5 : (tb * yb * tb⁻¹) ^ 2 = yb ^ 2 := IsProd.sq_eq_of_mem_zpowers hybo h4 (by
        have := MulEquiv.orderOf_eq (MulAut.conj tb) yb
        simp only [MulAut.conj_apply] at this
        rw [this, hybo])
      have h6 : tb * yb ^ 2 * tb⁻¹ = yb ^ 2 := by
        calc tb * yb ^ 2 * tb⁻¹ = (tb * yb * tb⁻¹) ^ 2 := by rw [sq, sq]; group
          _ = yb ^ 2 := h5
      calc yb ^ 2 * tb = (tb * yb ^ 2 * tb⁻¹) * tb := by rw [h6]
        _ = tb * yb ^ 2 := by group
    have h6 : yb ^ 2 ∈ zpowers (betaBar β) := hQt ▸ mem_inf.mpr ⟨h2, h3⟩
    rcases mem_zpowers_two hbb2 h6 with h7 | h7
    · exfalso
      have := orderOf_dvd_of_pow_eq_one h7
      rw [hybo] at this
      norm_num at this
    · apply hinj (pow_mem hyW 2) hβW
      rw [show (⟨y ^ 2, hWM (pow_mem hyW 2)⟩ : ↥M) = ⟨y, hWM hyW⟩ ^ 2 from rfl,
        QuotientGroup.mk_pow, ← hyb, h7]
      rfl
  obtain ⟨v', hv'W, hv'eq⟩ := mem_barOf.mp (hQW hvbQ)
  have hv'W' : (v' : X) ∈ W := hv'W
  have hvo : orderOf (v' : X) = 4 := by
    rw [← hord hv'W', show (⟨(v' : X), hWM hv'W'⟩ : ↥M) = v' from rfl, hv'eq, hvbo]
  have hvn : ∀ g ∈ W, g * (v' : X) * g⁻¹ ∈ zpowers (v' : X) := by
    intro g hg
    have h1 : (QuotientGroup.mk ⟨g, hWM hg⟩ : MBar β) * vb * (QuotientGroup.mk ⟨g, hWM hg⟩)⁻¹ ∈
        zpowers vb := hvb4 _ (hQn.conj_mem vb hvbQ _) (by
          have := MulEquiv.orderOf_eq (MulAut.conj (QuotientGroup.mk ⟨g, hWM hg⟩ : MBar β)) vb
          simp only [MulAut.conj_apply] at this
          rw [this, hvbo])
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    rw [mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have hgv : g * (v' : X) * g⁻¹ ∈ W := mul_mem (mul_mem hg hv'W') (inv_mem hg)
    apply hinj (zpow_mem hv'W' k) hgv
    rw [show (⟨(v' : X) ^ k, hWM (zpow_mem hv'W' k)⟩ : ↥M) = v' ^ k from Subtype.ext rfl,
      QuotientGroup.mk_zpow, hv'eq, hk]
    rw [← hv'eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hv2 := key _ hv'W' hvo hvn
  intro n hn
  rw [mem_centralizer_singleton_iff]
  have hnv : n * (v' : X) * n⁻¹ ∈ W := (mem_normalizer_iff.mp hn _).mp hv'W'
  have hnvo : orderOf (n * (v' : X) * n⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n) (v' : X)
    simp only [MulAut.conj_apply] at this
    rw [this, hvo]
  have hnvn : ∀ g ∈ W, g * (n * (v' : X) * n⁻¹) * g⁻¹ ∈ zpowers (n * (v' : X) * n⁻¹) := by
    intro g hg
    have hg' : n⁻¹ * g * n ∈ W := by
      have := (mem_normalizer_iff.mp (inv_mem hn) g).mp hg
      rwa [inv_inv] at this
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hvn _ hg')
    rw [mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [conj_zpow, hk]
    group
  have h1 := key _ hnv hnvo hnvn
  have h3 : n * β * n⁻¹ = β := by
    calc n * β * n⁻¹ = n * (v' : X) ^ 2 * n⁻¹ := by rw [hv2]
      _ = (n * (v' : X) * n⁻¹) ^ 2 := conj_pow.symm
      _ = β := h1
  calc n * β = n * β * n⁻¹ * n := by group
    _ = β * n := by rw [h3]

end L415

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem eight_le_card_inf
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    8 ≤ Nat.card ↥(barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓ Kb₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have hS₁ := hc.prod.isSylowOf_inf_K₁ hE (isSylowOf_barOf hc.isSylowOf_W)
  obtain ⟨e₁⟩ := hc.equiv₁
  obtain ⟨m, hm, ⟨e⟩⟩ := hs.setup.dihedral
  rw [hS₁.card_eq, Nat.card_congr e₁.toEquiv, hs.factorization_card_KBar h412 e]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem pCore_sq [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    ∀ q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), q * q = 1 := by
  by_contra hcon
  push Not at hcon
  have hσ := hs.setup
  obtain ⟨e₁⟩ := hc.equiv₁
  have hlie := GSThmB.OddQuot.lieModel_of_equiv e₁.symm (hs.lieModel_KBar h412)
  have hQC : centralizer ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≤
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [h412.pCore_eq.1, h412.pCore_eq.2]
  have hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ W := hc.T_le_W (hσ.X_le_T hs.beta.mem_X)
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) = 1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have hN := L415.normalizer_le_of_not_elem (hc.isSylowOf_W.le hc.t_mem_W)
    (by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]) hc.prod hc.isSylowOf_W
    hc.t_mem_W hβW hβ2 hA hs.prime_p hs.p_ne_two hlie
    (by have := hc.eight_le_card_inf h412; omega) hQC h412.pCore_inf_centralizer
    h412.pCore_shape hs.betaBar_ne_one hcon
  exact hc.not_isSylowOf hnab hKC (EndB.isSylowOf_top_of_normalizer_le hc.isSylowOf_W hN)

end Config415

end CFSG.ComponentClassification.HarrisLit
