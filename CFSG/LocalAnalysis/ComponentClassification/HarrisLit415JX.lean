module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415J
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Q
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd DihedralGroup

namespace L415

theorem barOf_commutator {X : Type} [Group X] {M A : Subgroup X} (hAM : A ≤ M) :
    barOf M ⁅A, A⁆ = ⁅barOf M A, barOf M A⁆ := by
  have h1 : ⁅A, A⁆.subgroupOf M = ⁅A.subgroupOf M, A.subgroupOf M⁆ := by
    apply Subgroup.map_injective M.subtype_injective
    have hAA : ⁅A, A⁆ ≤ A := commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    rw [subgroupOf_map_subtype, map_commutator, subgroupOf_map_subtype,
      inf_of_le_left hAM, inf_of_le_left (hAA.trans hAM)]
  rw [barOf, h1, map_commutator]
  rfl

theorem eq_of_mem_zpowers_sq {G : Type*} [Group G] [Finite G] {g c : G} {m : ℕ} (hm : 1 ≤ m)
    (hg : orderOf g = 2 ^ m) (hc : c ∈ zpowers g) (hc2 : c ^ 2 = 1) :
    c = 1 ∨ c = g ^ (2 ^ (m - 1)) := by
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  have hco : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  have hgo : orderOf (g ^ (2 ^ (m - 1))) = 2 := by
    rw [orderOf_pow' g (by positivity), hg, Nat.gcd_eq_right (pow_dvd_pow 2 (Nat.sub_le m 1)),
      Nat.pow_div (Nat.sub_le m 1) (by norm_num), show m - (m - 1) = 1 by omega, pow_one]
  have h1 := mem_zpowers_of_orderOf_eq hc (pow_mem (mem_zpowers g) _) (hco.trans hgo.symm)
  have hgg : g ^ (2 ^ (m - 1)) * g ^ (2 ^ (m - 1)) = 1 := by
    have := pow_orderOf_eq_one (g ^ 2 ^ (m - 1))
    rw [hgo] at this
    rw [← sq]
    exact this
  rcases mem_zpowers_two hgg h1 with h2 | h2
  · exact absurd h2 hc1
  · exact h2

theorem symm_r_pow_half {G : Type*} [Group G] [Finite G] {D : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (eD : ↥D ≃* DihedralGroup (2 ^ m)) {z : G} (hzD : z ∈ D) (hzc : ∀ d ∈ D, z * d = d * z)
    (hz1 : z ≠ 1) : ((eD.symm (r 1) : ↥D) : G) ^ (2 ^ (m - 1)) = z := by
  have hj : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
    rw [← Nat.cast_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m),
      ZMod.natCast_self]
  have hcen : (eD.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : ↥D) ∈ center ↥D :=
    mem_center_iff.mpr fun g => (comm_of_r_double eD hj g).symm
  have hzc' : (⟨z, hzD⟩ : ↥D) ∈ center ↥D :=
    mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
  have hne : eD.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) ≠ 1 := by
    intro h1
    have h2 := congrArg eD h1
    rw [MulEquiv.apply_symm_apply, map_one, one_def, r.injEq, ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by positivity) h2
    have h3 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
    have h4 : 0 < 2 ^ (m - 1) := by positivity
    omega
  rcases eq_of_mem_center_dihedral eD hm hzc' (fun h1 => hz1 (congrArg Subtype.val h1))
    hcen with h1 | h1
  · exact absurd h1 hne
  · rw [← Subgroup.coe_pow, ← map_pow, r_one_pow, h1]

theorem conj_mem_of_normalizer_of {X : Type} [Group X] [Finite X] {β t z₁ z x : X}
    {Kb₁ Kb₂ : Subgroup (MBar β)} (htM : t ∈ centralizer ({β} : Set X)) (ht2 : t * t = 1)
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, htM⟩))
    {W : Subgroup X} (hW : IsSylowOf 2 W (centralizer {β})) (htW : t ∈ W) (hz₁W : z₁ ∈ W)
    (hz₁2 : z₁ ^ 2 = 1) (hz₁ne : z₁ ≠ t * z₁ * t⁻¹) (hzz : z = z₁ * (t * z₁ * t⁻¹))
    (hmk : ∀ hz₁ : z₁ ∈ centralizer ({β} : Set X),
      (QuotientGroup.mk ⟨z₁, hz₁⟩ : MBar β) ∈ Kb₁)
    (hcomm : ∀ y ∈ W, ∀ hy : y ∈ centralizer ({β} : Set X), y * z₁ = z₁ * y ↔
      Kb₁.map (MulAut.conj (QuotientGroup.mk ⟨y, hy⟩ : MBar β)).toMonoidHom = Kb₁)
    (hmul : ∀ y ∈ W, y * z₁ ≠ z₁ * y → y * t * z₁ = z₁ * (y * t))
    {Ds : Subgroup X} (hDsW : Ds ≤ W)
    (hDsyl : IsSylowOf 2 (barOf (centralizer {β}) Ds)
      (layer (MBar β) ⊓ centralizer {(QuotientGroup.mk ⟨t, htM⟩ : MBar β)}))
    {m : ℕ} (hm : 2 ≤ m) (eDs : ↥Ds ≃* DihedralGroup (2 ^ m)) (hzDs : z ∈ Ds)
    (hzc : ∀ d ∈ Ds, z * d = d * z) (hxW : x ∈ W) (hx2 : x * x = 1) (hxt : x * t = t * x)
    (hxDs : ∀ d ∈ Ds, x * d * x⁻¹ ∈ Ds) (hxC : ∀ d ∈ Ds, d * x = x * d → d = 1 ∨ d = z)
    (hA : AutPSL2RDerivedInput) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlie : Blueprint.LieModel ↥Kb₁ .PSL 2 p n)
    (h8 : 8 ≤ Nat.card ↥(barOf (centralizer {β}) W ⊓ Kb₁))
    (hQC : centralizer ((layer (MBar β) : Subgroup (MBar β)) : Set (MBar β)) ≤
      pCore 2 (MBar β))
    (hQ2 : ∀ q ∈ pCore 2 (MBar β), q * q = 1) {g : X}
    (hg : g ∈ normalizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X)) :
    g * z₁ * g⁻¹ = z₁ ∨ g * z₁ * g⁻¹ = t * z₁ * t⁻¹ ∨ g * z₁ * g⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({β} : Set X) with hMdef
  have hWM : W ≤ M := hW.le
  have hWp := hW.isPGroup
  have hE : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  set s : MBar β := QuotientGroup.mk ⟨t, htM⟩ with hsdef
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs2 : s * s = 1 := by
    rw [hsdef, ← QuotientGroup.mk_mul]
    have : (⟨t, htM⟩ : ↥M) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
    rw [this, QuotientGroup.mk_one]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  set P := barOf M W with hPdef
  have hP : IsSylowOf 2 P ⊤ := isSylowOf_barOf hW
  have hsP : s ∈ P := mk_mem_barOf htM htW
  have hDsM : Ds ≤ M := hDsW.trans hWM
  have hDsp : IsPGroup 2 Ds := hWp.to_le hDsW
  set D := barOf M Ds with hDdef
  have hDP : D ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hDsW hy, rfl⟩
  set eD : ↥D ≃* DihedralGroup (2 ^ m) := (barEquiv hDsM hDsp).symm.trans eDs with heD
  have hz₁M : z₁ ∈ M := hWM hz₁W
  set zb₁ : MBar β := QuotientGroup.mk ⟨z₁, hz₁M⟩ with hzb₁
  have hzb₁P : zb₁ ∈ P ⊓ Kb₁ := mem_inf.mpr ⟨mk_mem_barOf hz₁M hz₁W, hmk hz₁M⟩
  have hzM : z ∈ M := hDsM hzDs
  have hzb : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) = zb₁ * (s⁻¹ * zb₁ * s) := by
    rw [hsi]
    have : (⟨z, hzM⟩ : ↥M) = ⟨z₁, hz₁M⟩ * (⟨t, htM⟩ * ⟨z₁, hz₁M⟩ * ⟨t, htM⟩) :=
      Subtype.ext (by show z = z₁ * (t * z₁ * t); rw [hzz, hti])
    rw [this]
    simp only [QuotientGroup.mk_mul]
    rfl
  have hzbD : ∀ d ∈ D, zb₁ * (s⁻¹ * zb₁ * s) * d = d * (zb₁ * (s⁻¹ * zb₁ * s)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hzb]
    show (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk ⟨z, hzM⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hzc y hy)
  have hz₂2 : (t * z₁ * t⁻¹) * (t * z₁ * t⁻¹) = 1 := by
    rw [show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ ^ 2) * t⁻¹ by rw [sq]; group, hz₁2]
    group
  have hz1 : z ≠ 1 := by
    intro h1
    rw [hzz] at h1
    apply hz₁ne
    calc z₁ = (t * z₁ * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = t * z₁ * t⁻¹ := inv_eq_of_mul_eq_one_right hz₂2
  have hzb1 : zb₁ * (s⁻¹ * zb₁ * s) ≠ 1 := by
    rw [← hzb]
    intro h1
    exact hz1 (mk_injOn hWM hWp (hDsW hzDs) (one_mem W) (h1.trans rfl))
  have hxM : x ∈ M := hWM hxW
  set xb : MBar β := QuotientGroup.mk ⟨x, hxM⟩ with hxb
  have hxb2 : xb * xb = 1 := by
    rw [hxb, ← QuotientGroup.mk_mul]
    have : (⟨x, hxM⟩ : ↥M) * ⟨x, hxM⟩ = 1 := Subtype.ext hx2
    rw [this, QuotientGroup.mk_one]
  have hxbs : xb * s = s * xb := by
    rw [hxb, hsdef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hxt
  have hxbD : ∀ d ∈ D, xb * d * xb⁻¹ ∈ D := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨x, hxM⟩ * y * (⟨x, hxM⟩ : ↥M)⁻¹, hxDs y hy, ?_⟩
    simp only [hxb, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rfl
  have hxbC : ∀ y ∈ D, y * xb = xb * y → y = 1 ∨ y = zb₁ * (s⁻¹ * zb₁ * s) := by
    rintro _ ⟨y, hy, rfl⟩ hyx
    have hy' : (y : X) ∈ Ds := hy
    have hyx' : (y : X) * x = x * y := by
      refine mk_injOn hWM hWp (mul_mem (hDsW hy') hxW) (mul_mem hxW (hDsW hy')) ?_
      have h1 : (⟨(y : X) * x, hWM (mul_mem (hDsW hy') hxW)⟩ : ↥M) = y * ⟨x, hxM⟩ := rfl
      have h2 : (⟨x * (y : X), hWM (mul_mem hxW (hDsW hy'))⟩ : ↥M) = ⟨x, hxM⟩ * y := rfl
      rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hyx
    rcases hxC y hy' hyx' with h1 | h1
    · left
      have : y = 1 := Subtype.ext h1
      rw [QuotientGroup.mk'_apply, this, QuotientGroup.mk_one]
    · right
      rw [← hzb, QuotientGroup.mk'_apply]
      congr 1
      exact Subtype.ext h1
  obtain ⟨α, hαW, hαz, hα⟩ : ∃ α ∈ W, α * z₁ = z₁ * α ∧ (α = x ∨ α = x * t) := by
    by_cases hxz : x * z₁ = z₁ * x
    · exact ⟨x, hxW, hxz, Or.inl rfl⟩
    · exact ⟨x * t, mul_mem hxW htW, hmul x hxW hxz, Or.inr rfl⟩
  have hαM := hWM hαW
  set ab : MBar β := QuotientGroup.mk ⟨α, hαM⟩ with hab'
  have hab : ab = xb ∨ ab = xb * s := by
    rcases hα with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have habK : Kb₁.map (MulAut.conj ab).toMonoidHom = Kb₁ := (hcomm α hαW hαM).mp hαz
  obtain ⟨d, hd, hdz⟩ := hprod.exists_sq_commutator hE hP hs2 hsP hDsyl hDP hm eD hzb₁P hzbD
    hzb1 hxb2 hxbs hxbD hxbC hab habK
  have hPD : P ⊓ (layer (MBar β) ⊓ centralizer {s}) = D :=
    hDsyl.eq_of_le (le_inf hDP hDsyl.le) inf_le_right (hP.isPGroup.to_le inf_le_left)
  set δ : ↥D := eD.symm (r 1) with hδ
  have hδ' : (δ : MBar β) ∈ P ⊓ (layer (MBar β) ⊓ centralizer {s}) := by rw [hPD]; exact δ.2
  obtain ⟨δ₁, hδ₁, hδδ⟩ := hprod.exists_diag hE hP hs2 ⟨hδ'.1, hδ'.2.1⟩
    (mem_centralizer_singleton_iff.mp hδ'.2.2).symm
  have hδo : orderOf (δ : MBar β) = 2 ^ m := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq eD, hδ, MulEquiv.apply_symm_apply,
      orderOf_r_one]
  have hδ₁o' : orderOf δ₁ = 2 ^ m := by
    have h1 := orderOf_injective hprod.diag hprod.diag_injective ⟨δ₁, (mem_inf.mp hδ₁).2⟩
    rw [Subgroup.orderOf_mk, IsProd.diag_apply, ← hδδ, hδo] at h1
    exact h1.symm
  have hcardD : Nat.card ↥(P ⊓ Kb₁) = Nat.card ↥D := by
    refine Nat.card_eq_of_bijective (fun c => ⟨hprod.diag ⟨c, (mem_inf.mp c.2).2⟩,
      hprod.diag_mem hs2 hsP hPD c.2⟩) ⟨fun a b hab => ?_, fun y => ?_⟩
    · have h1 := congrArg Subtype.val hab
      have h2 := hprod.diag_injective h1
      have h3 : ((a : ↥(P ⊓ Kb₁)) : MBar β) = b := congrArg (fun k : ↥Kb₁ => (k : MBar β)) h2
      exact Subtype.ext h3
    · have hy' : (y : MBar β) ∈ P ⊓ (layer (MBar β) ⊓ centralizer {s}) := by
        rw [hPD]; exact y.2
      obtain ⟨k, hk, hky⟩ := hprod.exists_diag hE hP hs2 ⟨hy'.1, hy'.2.1⟩
        (mem_centralizer_singleton_iff.mp hy'.2.2).symm
      exact ⟨⟨k, hk⟩, Subtype.ext (by
        show hprod.diag ⟨k, (mem_inf.mp hk).2⟩ = (y : MBar β)
        rw [IsProd.diag_apply, ← hky])⟩
  have hcardD' : Nat.card ↥D = 2 * 2 ^ m := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hδ₁o : 2 * orderOf δ₁ = Nat.card ↥(P ⊓ Kb₁) := by rw [hcardD, hcardD', hδ₁o']
  have hδpow : (δ : MBar β) ^ (2 ^ (m - 1)) = zb₁ * (s⁻¹ * zb₁ * s) :=
    symm_r_pow_half hm eD (hprod.diag_mem hs2 hsP hPD hzb₁P) hzbD hzb1
  have hz₁δ : ∀ c ∈ zpowers δ₁, c ^ 2 = 1 → c = 1 ∨ c = zb₁ := by
    intro c hc hc2
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    have hcK : δ₁ ^ k ∈ Kb₁ := zpow_mem (mem_inf.mp hδ₁).2 k
    have hdc : hprod.diag ⟨δ₁ ^ k, hcK⟩ = (δ : MBar β) ^ k := by
      rw [show (⟨δ₁ ^ k, hcK⟩ : ↥Kb₁) = ⟨δ₁, (mem_inf.mp hδ₁).2⟩ ^ k from Subtype.ext (by simp),
        map_zpow, IsProd.diag_apply, ← hδδ]
    have hdc2 : ((δ : MBar β) ^ k) ^ 2 = 1 := by
      rw [← hdc, ← map_pow]
      have : (⟨δ₁ ^ k, hcK⟩ : ↥Kb₁) ^ 2 = 1 := Subtype.ext (by simpa using hc2)
      rw [this, map_one]
    rcases eq_of_mem_zpowers_sq (by omega : 1 ≤ m) hδo (zpow_mem (mem_zpowers _) k) hdc2 with
      h1 | h1
    · left
      have : (⟨δ₁ ^ k, hcK⟩ : ↥Kb₁) = 1 := hprod.diag_injective (by rw [hdc, h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨δ₁ ^ k, hcK⟩ : ↥Kb₁) = ⟨zb₁, (mem_inf.mp hzb₁P).2⟩ :=
        hprod.diag_injective (by rw [hdc, h1, hδpow, IsProd.diag_apply])
      exact congrArg Subtype.val this
  set δ₂ := s⁻¹ * δ₁ * s with hδ₂def
  have hδ₂ : δ₂ ∈ P ⊓ Kb₂ := mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hsP) (mem_inf.mp hδ₁).1) hsP,
    hprod.conj_mem_K₂ (mem_inf.mp hδ₁).2⟩
  have hcard₂ : Nat.card ↥(P ⊓ Kb₂) = Nat.card ↥(P ⊓ Kb₁) := by
    rw [(hprod.isSylowOf_inf_K₁ hE hP).card_eq, (hprod.isSylowOf_inf_K₂ hE hP).card_eq,
      ← Nat.card_congr hprod.equivK₂.toEquiv]
  have hδ₂o : 2 * orderOf δ₂ = Nat.card ↥(P ⊓ Kb₂) := by
    have := MulEquiv.orderOf_eq (MulAut.conj s⁻¹) δ₁
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [hcard₂, ← hδ₁o, hδ₂def, this]
  have hz₂δ : ∀ c ∈ zpowers δ₂, c ^ 2 = 1 → c = 1 ∨ c = s⁻¹ * zb₁ * s := by
    intro c hc hc2
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    have hk : δ₂ ^ k = s⁻¹ * δ₁ ^ k * s := by
      rw [hδ₂def, show s⁻¹ * δ₁ * s = s⁻¹ * δ₁ * s⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
    have hc'' : (δ₁ ^ k) ^ 2 = 1 := by
      calc (δ₁ ^ k) ^ 2 = s * (s⁻¹ * δ₁ ^ k * s) ^ 2 * s⁻¹ := by rw [sq, sq]; group
        _ = 1 := by rw [← hk, hc2]; group
    rcases hz₁δ (δ₁ ^ k) (zpow_mem (mem_zpowers _) k) hc'' with h1 | h1
    · left
      rw [hk, h1]
      group
    · right
      rw [hk, h1]
  set W₀ := W ⊓ centralizer ({z₁} : Set X) with hW₀def
  have hW₀M : W₀ ≤ M := inf_le_left.trans hWM
  have hAA : ⁅W₀, W₀⁆ ≤ W₀ := commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hP₀ : barOf M W₀ = P ⊓ normalizer (Kb₁ : Set (MBar β)) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : (y : X) ∈ W ⊓ centralizer {z₁} := hy
      refine mem_inf.mpr ⟨⟨y, (mem_inf.mp hy').1, rfl⟩, ?_⟩
      rw [IsProd.mem_normalizer_iff_map]
      exact (hcomm y (mem_inf.mp hy').1 y.2).mp
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hy').2)
    · rintro _ ⟨⟨y, hy, rfl⟩, hyN⟩
      have hy' : (y : X) ∈ W := hy
      refine ⟨y, mem_inf.mpr ⟨hy', mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
      exact (hcomm y hy' y.2).mpr ((IsProd.mem_normalizer_iff_map _ _).mp hyN)
  have hcomm' : barOf M ⁅W₀, W₀⁆ = ⁅P ⊓ normalizer (Kb₁ : Set (MBar β)),
      P ⊓ normalizer (Kb₁ : Set (MBar β))⁆ := by
    rw [barOf_commutator hW₀M, hP₀]
  have hdP₀ : d ∈ P ⊓ normalizer (Kb₁ : Set (MBar β)) :=
    mem_inf.mpr ⟨(mem_inf.mp hd).1, le_normalizer (mem_inf.mp hd).2⟩
  have habP₀ : ab ∈ P ⊓ normalizer (Kb₁ : Set (MBar β)) :=
    mem_inf.mpr ⟨mk_mem_barOf hαM hαW, (IsProd.mem_normalizer_iff_map _ _).mpr habK⟩
  have hγb : d * ab * d⁻¹ * ab⁻¹ ∈ barOf M ⁅W₀, W₀⁆ := by
    rw [hcomm']
    exact commutator_mem_commutator hdP₀ habP₀
  obtain ⟨γ, hγ, hγeq⟩ := mem_barOf.mp hγb
  have hγW : (γ : X) ∈ W := (mem_inf.mp (hAA hγ)).1
  have hγ2 : (γ : X) ^ 2 = z₁ := by
    apply mk_injOn hWM hWp (pow_mem hγW 2) hz₁W
    rw [show (⟨(γ : X) ^ 2, hWM (pow_mem hγW 2)⟩ : ↥M) = γ ^ 2 from rfl, QuotientGroup.mk_pow,
      hγeq, hdz]
  have hgγ : g * γ * g⁻¹ ∈ ⁅W₀, W₀⁆ := by
    have h1 : (⁅W₀, W₀⁆).map (MulAut.conj g).toMonoidHom = ⁅W₀, W₀⁆ := by
      rw [map_commutator, (IsProd.mem_normalizer_iff_map _ _).mp hg]
    rw [← h1]
    exact ⟨γ, hγ, rfl⟩
  have hgγW : g * γ * g⁻¹ ∈ W := (mem_inf.mp (hAA hgγ)).1
  have hgz : g * z₁ * g⁻¹ = (g * γ * g⁻¹) ^ 2 := by rw [conj_pow, hγ2]
  have hgzW : g * z₁ * g⁻¹ ∈ W := hgz ▸ pow_mem hgγW 2
  have hb : (QuotientGroup.mk ⟨g * γ * g⁻¹, hWM hgγW⟩ : MBar β) ∈
      ⁅P ⊓ normalizer (Kb₁ : Set (MBar β)), P ⊓ normalizer (Kb₁ : Set (MBar β))⁆ := by
    rw [← hcomm']
    exact ⟨⟨_, hWM hgγW⟩, hgγ, rfl⟩
  have hb2 : (QuotientGroup.mk ⟨g * γ * g⁻¹, hWM hgγW⟩ : MBar β) ^ 2 =
      QuotientGroup.mk ⟨g * z₁ * g⁻¹, hWM hgzW⟩ := by
    rw [← QuotientGroup.mk_pow]
    congr 1
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hgz.symm)
  have hb4 : ((QuotientGroup.mk ⟨g * γ * g⁻¹, hWM hgγW⟩ : MBar β) ^ 2) ^ 2 = 1 := by
    rw [hb2, ← QuotientGroup.mk_pow]
    have : (⟨g * z₁ * g⁻¹, hWM hgzW⟩ : ↥M) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, conj_pow, hz₁2, mul_one, mul_inv_cancel]; rfl)
    rw [this, QuotientGroup.mk_one]
  have hz₂W : t * z₁ * t⁻¹ ∈ W := mul_mem (mul_mem htW hz₁W) (inv_mem htW)
  have hz₂b : (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hWM hz₂W⟩ : MBar β) = s⁻¹ * zb₁ * s := by
    rw [hsi]
    have : (⟨t * z₁ * t⁻¹, hWM hz₂W⟩ : ↥M) = ⟨t, htM⟩ * ⟨z₁, hz₁M⟩ * ⟨t, htM⟩ :=
      Subtype.ext (by show t * z₁ * t⁻¹ = t * z₁ * t; rw [hti])
    rw [this]
    simp only [QuotientGroup.mk_mul]
    rfl
  rcases hprod.sq_mem_of_mem_commutator hE hP hA hp hp2 hlie h8 hQC hQ2 hδ₁ hδ₁o hδ₂ hδ₂o
    hz₁δ hz₂δ hb hb4 with h5 | h5 | h5 | h5 <;> rw [hb2] at h5
  · exfalso
    have h6 : g * z₁ * g⁻¹ = 1 := mk_injOn hWM hWp hgzW (one_mem W) (by
      rw [h5]
      rfl)
    apply hz₁ne
    have h7 : z₁ = 1 := by
      calc z₁ = g⁻¹ * (g * z₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h6]; group
    rw [h7]
    group
  · exact Or.inl (mk_injOn hWM hWp hgzW hz₁W h5)
  · exact Or.inr (Or.inl (mk_injOn hWM hWp hgzW hz₂W (h5.trans hz₂b.symm)))
  · exact Or.inr (Or.inr (mk_injOn hWM hWp hgzW (hDsW hzDs) (h5.trans hzb.symm)))

end L415

end CFSG.ComponentClassification.HarrisLit
