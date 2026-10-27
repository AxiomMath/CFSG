module

public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Quot
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Generation
public import CFSG.Goldschmidt.Steps.G75Basic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DSylow
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem card_eq_one_of_arith {n c q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) (hc : 0 < c)
    (hn : n = c ^ 2) (h4c : n ≤ 4 * c) (hmod : n ≡ 1 [MOD q]) : n = 1 := by
  subst hn
  have hc4 : c ≤ 4 := by nlinarith
  have hdvd : q ∣ c ^ 2 - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hc)).1 hmod.symm
  interval_cases c
  · rfl
  · exfalso
    have h : q ∣ 3 := by simpa using hdvd
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · exfalso
    have h : q ∣ 8 := by simpa using hdvd
    have := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> first | omega | exact absurd hq (by norm_num)
  · exfalso
    have h : q ∣ 15 := by simpa using hdvd
    have := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> first | omega | exact absurd hq (by norm_num)

private theorem card_le_sq {W : Subgroup G} (hW : IsElemAbelian 2 W) {e : G}
    (he : e ∈ Subgroup.normalizer (W : Set G)) (he2 : e * e = 1) :
    Nat.card W ≤ Nat.card (W ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) ^ 2 := by
  have hcomm : ∀ a b : ↥W, a * b = b * a := fun a b => Subtype.ext (hW.comm a.2 b.2)
  have hconj : ∀ w : ↥W, (MulAut.conj e).toMonoidHom (w : G) ∈ W := fun w => by
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 he w).1 w.2
  let c : ↥W →* ↥W :=
    MonoidHom.codRestrict ((MulAut.conj e).toMonoidHom.comp W.subtype) W hconj
  let φ : ↥W →* ↥W := MonoidHom.mk' (fun w => w⁻¹ * c w) (fun a b => by
    simp only [map_mul, mul_inv_rev]
    calc b⁻¹ * a⁻¹ * (c a * c b) = a⁻¹ * b⁻¹ * (c a * c b) := by rw [hcomm b⁻¹ a⁻¹]
      _ = a⁻¹ * (b⁻¹ * c a) * c b := by group
      _ = a⁻¹ * (c a * b⁻¹) * c b := by rw [hcomm b⁻¹ (c a)]
      _ = a⁻¹ * c a * (b⁻¹ * c b) := by group)
  have hφ : ∀ w : ↥W, ((φ w : ↥W) : G) = (w : G)⁻¹ * (e * (w : G) * e⁻¹) := fun w => rfl
  set D : Subgroup ↥W := (W ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G).subgroupOf W with hD
  have hDcard : Nat.card D = Nat.card (W ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hker : φ.ker ≤ D := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw
    have h1 : (w : G)⁻¹ * (e * (w : G) * e⁻¹) = 1 := by rw [← hφ, hw]; rfl
    have h2 : e * (w : G) * e⁻¹ = w := by
      have := inv_mul_eq_one.1 h1
      exact this.symm
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨w.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc h * (w : G) = (h * (w : G) * h⁻¹) * h := by group
      _ = (w : G) * h := by rw [h2]
  have hrange : φ.range ≤ D := by
    rintro _ ⟨w, rfl⟩
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨(φ w).2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    set a : G := (w : G) with ha
    set b : G := h * a * h⁻¹ with hb
    have hbW : b ∈ W := (Subgroup.mem_normalizer_iff.1 he a).1 w.2
    have hvW : a⁻¹ * b ∈ W := mul_mem (inv_mem w.2) hbW
    have hv2 : (a⁻¹ * b) * (a⁻¹ * b) = 1 := hW.mul_self_eq_one hvW
    have hvinv : (a⁻¹ * b)⁻¹ = a⁻¹ * b := inv_eq_of_mul_eq_one_right hv2
    have hconj2 : h * (a⁻¹ * b) * h⁻¹ = (a⁻¹ * b)⁻¹ := by
      calc h * (a⁻¹ * b) * h⁻¹ = (h * a * h⁻¹)⁻¹ * ((h * h) * a * (h * h)⁻¹) := by
            rw [hb]; group
        _ = b⁻¹ * a := by rw [he2, ← hb]; simp
        _ = (a⁻¹ * b)⁻¹ := by group
    have hφw : ((φ w : ↥W) : G) = a⁻¹ * b := hφ w
    rw [hφw]
    calc h * (a⁻¹ * b) = (h * (a⁻¹ * b) * h⁻¹) * h := by group
      _ = (a⁻¹ * b) * h := by rw [hconj2, hvinv]
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card W := by
    have := Subgroup.card_mul_index φ.ker
    rwa [Subgroup.index_ker] at this
  rw [← h1, sq, ← hDcard]
  exact Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)

private theorem card_sq_le {W : Subgroup G} (hW : IsElemAbelian 2 W) {e y : G}
    (hy : y ∈ Subgroup.normalizer (W : Set G)) (hyodd : Odd (orderOf y))
    (hey : ∀ w ∈ W, (e * y * e⁻¹) * w * (e * y * e⁻¹)⁻¹ = y⁻¹ * w * y)
    (hfix : ∀ w ∈ W, y * w = w * y → w = 1) :
    Nat.card (W ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) ^ 2 ≤ Nat.card W := by
  set Ce : Subgroup G := W ⊓ Subgroup.centralizer ({e} : Set G) with hCe
  set Cf : Subgroup G := Ce.map (MulAut.conj y⁻¹).toMonoidHom with hCf
  have hCeW : Ce ≤ W := inf_le_left
  have hCfW : Cf ≤ W := by
    rintro _ ⟨c, hc, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 (inv_mem hy) c).1 (hCeW hc)
  have hcomm : ∀ x ∈ Ce, ∀ z ∈ Cf, x * z = z * x := fun x hx z hz =>
    hW.comm (hCeW hx) (hCfW hz)
  have hinf : Ce ⊓ Cf = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwCe, c, hc, hcw⟩ := Subgroup.mem_inf.1 hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hcw
    have hwW : w ∈ W := hCeW hwCe
    have hwe : e * w = w * e :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hwCe).2 e (Set.mem_singleton e)
    have hce : e * c = c * e :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 e (Set.mem_singleton e)
    have hcy : c = y * w * y⁻¹ := by rw [← hcw]; group
    have hew : e * w * e⁻¹ = w := by
      rw [hwe]; group
    have hec : e * c * e⁻¹ = c := by
      rw [hce]; group
    have h1 : y * w * y⁻¹ = y⁻¹ * w * y := by
      calc y * w * y⁻¹ = c := hcy.symm
        _ = e * c * e⁻¹ := hec.symm
        _ = (e * y * e⁻¹) * (e * w * e⁻¹) * (e * y * e⁻¹)⁻¹ := by rw [hcy]; group
        _ = (e * y * e⁻¹) * w * (e * y * e⁻¹)⁻¹ := by rw [hew]
        _ = y⁻¹ * w * y := hey w hwW
    have h2 : (y * y) * w * (y * y)⁻¹ = w := by
      calc (y * y) * w * (y * y)⁻¹ = y * (y * w * y⁻¹) * y⁻¹ := by group
        _ = y * (y⁻¹ * w * y) * y⁻¹ := by rw [h1]
        _ = w := by group
    have h3 : Commute (y * y) w := mul_inv_eq_iff_eq_mul.1 h2
    obtain ⟨k, hk⟩ := hyodd
    have hy1 : y = (y * y) ^ (k + 1) := by
      have h : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
      calc y = y ^ (2 * k + 1) * y := by rw [h, one_mul]
        _ = y ^ (2 * (k + 1)) := by rw [← pow_succ]; exact congrArg (y ^ ·) (by omega)
        _ = (y * y) ^ (k + 1) := by rw [pow_mul, sq]
    have h4 : y * w = w * y := by
      have := (h3.pow_left (k + 1)).eq
      rwa [← hy1] at this
    exact Subgroup.mem_bot.2 (hfix w hwW h4)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Ce Cf hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  have hCfcard : Nat.card Cf = Nat.card Ce :=
    Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
  rw [hCfcard] at hcard
  have hle : Nat.card (Ce ⊔ Cf : Subgroup G) ≤ Nat.card W :=
    Subgroup.card_le_of_le (sup_le hCeW hCfW)
  rw [sq, ← hcard]
  exact hle

private theorem card_modEq_one {W : Subgroup G} {y : G} {q : ℕ} [Fact q.Prime]
    (hy : y ∈ Subgroup.normalizer (W : Set G)) (hyq : IsPGroup q (Subgroup.zpowers y))
    (hfix : ∀ w ∈ W, y * w = w * y → w = 1) :
    Nat.card W ≡ 1 [MOD q] := by
  classical
  let _ : MulDistribMulAction (Subgroup.zpowers y) W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (Subgroup.zpowers y) W
      (Subgroup.zpowers_le.2 hy)
  have hmod := hyq.card_modEq_card_fixedPoints ↥W
  have hone : Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) ↥W) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, fun g => by simp⟩⟩⟩
    have key : ∀ a : MulAction.fixedPoints (Subgroup.zpowers y) ↥W,
        a = ⟨1, fun g => by simp⟩ := by
      rintro ⟨w, hw⟩
      have h1 := MulAction.mem_fixedPoints.1 hw ⟨y, Subgroup.mem_zpowers y⟩
      have h2 : y * (w : G) * y⁻¹ = (w : G) := congrArg Subtype.val h1
      have h3 : y * (w : G) = (w : G) * y := by
        calc y * (w : G) = y * (w : G) * y⁻¹ * y := by group
          _ = (w : G) * y := by rw [h2]
      have h4 := hfix w w.2 h3
      exact Subtype.ext (Subtype.ext h4)
    rw [key a, key b]
  rw [hone] at hmod
  exact hmod

private theorem card_le_four_mul {W X : Subgroup G} (hWX : W ≤ X) (hX : IsElemAbelian 2 X) {e : G}
    (h4 : Nat.card X ≤ 4 * Nat.card (X ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G)) :
    Nat.card W ≤ 4 * Nat.card (W ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) := by
  set K : Subgroup G := X ⊓ Subgroup.centralizer ({e} : Set G) with hK
  have hKX : K ≤ X := inf_le_left
  have hWK : W ⊓ Subgroup.centralizer ({e} : Set G) = W ⊓ K :=
    le_antisymm (le_inf inf_le_left (le_inf (inf_le_left.trans hWX) inf_le_right))
      (inf_le_inf_left W inf_le_right)
  have hcomm : ∀ a ∈ W, ∀ b ∈ K, a * b = b * a := fun a ha b hb => hX.comm (hWX ha) (hKX hb)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W K hcomm).1
  have hsup : Nat.card (W ⊔ K : Subgroup G) ≤ Nat.card X :=
    Subgroup.card_le_of_le (sup_le hWX hKX)
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hmul : Nat.card W * Nat.card K ≤ (4 * Nat.card (W ⊓ K : Subgroup G)) * Nat.card K := by
    calc Nat.card W * Nat.card K
        = Nat.card (W ⊔ K : Subgroup G) * Nat.card (W ⊓ K : Subgroup G) := hcard.symm
      _ ≤ Nat.card X * Nat.card (W ⊓ K : Subgroup G) := Nat.mul_le_mul hsup le_rfl
      _ ≤ (4 * Nat.card K) * Nat.card (W ⊓ K : Subgroup G) := Nat.mul_le_mul h4 le_rfl
      _ = (4 * Nat.card (W ⊓ K : Subgroup G)) * Nat.card K := by ring
  rw [hWK]
  exact Nat.le_of_mul_le_mul_right hmul hKpos

private theorem eq_bot_of_transvection {W X : Subgroup G} (hWX : W ≤ X) (hX : IsElemAbelian 2 X)
    {e y : G} {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) (hyq : IsPGroup q (Subgroup.zpowers y))
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) (heW : e ∈ Subgroup.normalizer (W : Set G))
    (hee : e * e = 1)
    (hey : ∀ w ∈ W, (e * y * e⁻¹) * w * (e * y * e⁻¹)⁻¹ = y⁻¹ * w * y)
    (hfix : ∀ w ∈ W, y * w = w * y → w = 1)
    (h4 : Nat.card X ≤ 4 * Nat.card (X ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G)) :
    W = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hW : IsElemAbelian 2 W := hX.mono hWX
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hyodd : Odd (orderOf y) := by
    obtain ⟨n, hn⟩ := hyq.exists_card_eq
    rw [Nat.card_zpowers] at hn
    rw [hn]
    exact hqodd.pow
  have hA := card_le_sq hW heW hee
  have hB := card_sq_le hW hyW hyodd hey hfix
  have hC := card_modEq_one hyW hyq hfix
  have hD := card_le_four_mul hWX hX h4
  have hcpos : 0 < Nat.card (W ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
    Nat.card_pos
  have hn : Nat.card W = Nat.card (W ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) ^ 2 :=
    le_antisymm hA hB
  exact Subgroup.eq_bot_of_card_eq W (card_eq_one_of_arith hq hq7 hcpos hn hD hC)

private theorem mem_normalizer_of_conj_mem_fin {V : Subgroup G} {b : G}
    (h : ∀ v ∈ V, b * v * b⁻¹ ∈ V) : b ∈ Subgroup.normalizer (V : Set G) := by
  have hle : V.map (MulAut.conj b).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj b).injective).ge)

private theorem conj_eq_of_mul_inv_mem {U : Subgroup G} {g g' : G}
    (hg' : g' ∈ Subgroup.normalizer (U : Set G))
    (h : g * g'⁻¹ ∈ Subgroup.centralizer (U : Set G)) {u : G} (hu : u ∈ U) :
    g * u * g⁻¹ = g' * u * g'⁻¹ := by
  have hv : g' * u * g'⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hg' u).1 hu
  have hc := Subgroup.mem_centralizer_iff.1 h _ hv
  calc g * u * g⁻¹ = (g * g'⁻¹) * (g' * u * g'⁻¹) * (g * g'⁻¹)⁻¹ := by group
    _ = (g' * u * g'⁻¹) * (g * g'⁻¹) * (g * g'⁻¹)⁻¹ := by rw [← hc]
    _ = g' * u * g'⁻¹ := by group

private theorem pow_conj_eq {U : Subgroup G} {g y' : G}
    (hy'U : y' ∈ Subgroup.normalizer (U : Set G))
    (h : ∀ u ∈ U, g * u * g⁻¹ = y' * u * y'⁻¹) :
    ∀ n : ℕ, ∀ u ∈ U, g ^ n * u * (g ^ n)⁻¹ = y' ^ n * u * (y' ^ n)⁻¹ := by
  intro n
  induction n with
  | zero => intro u hu; simp
  | succ n ih =>
    intro u hu
    have hv : y' ^ n * u * (y' ^ n)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (pow_mem hy'U n) u).1 hu
    calc g ^ (n + 1) * u * (g ^ (n + 1))⁻¹
        = g * (g ^ n * u * (g ^ n)⁻¹) * g⁻¹ := by group
      _ = g * (y' ^ n * u * (y' ^ n)⁻¹) * g⁻¹ := by rw [ih u hu]
      _ = y' * (y' ^ n * u * (y' ^ n)⁻¹) * y'⁻¹ := h _ hv
      _ = y' ^ (n + 1) * u * (y' ^ (n + 1))⁻¹ := by group

private theorem mem_normalizer_commutator_zpowers {A U : Subgroup G} (hAU : A ≤ U) {t y y' : G}
    (ht : t ∈ Subgroup.normalizer (A : Set G)) (hyU : y ∈ Subgroup.normalizer (U : Set G))
    (hy' : y' ∈ Subgroup.zpowers y)
    (h : ∀ u ∈ U, (t * y * t⁻¹) * u * (t * y * t⁻¹)⁻¹ = y' * u * y'⁻¹) :
    t ∈ Subgroup.normalizer ((⁅A, Subgroup.zpowers y⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem_fin
  intro w hw
  have hmem : t * w * t⁻¹ ∈
      (⁅A, Subgroup.zpowers y⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom :=
    ⟨w, hw, by simp [MulAut.conj_apply]⟩
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at hmem
  refine (?_ : ⁅A.map (MulAut.conj t).toMonoidHom,
    Subgroup.zpowers ((MulAut.conj t).toMonoidHom y)⁆ ≤ ⁅A, Subgroup.zpowers y⁆) hmem
  rw [Subgroup.commutator_le]
  intro v hv z hz
  obtain ⟨a, ha, rfl⟩ := hv
  have hz' : z ∈ Subgroup.zpowers (t * y * t⁻¹) := by
    simpa [MulAut.conj_apply] using hz
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hz')
  have hvA : t * a * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 ht a).1 ha
  have hy'U : y' ∈ Subgroup.normalizer (U : Set G) := Subgroup.zpowers_le.2 hyU hy'
  have hpow := pow_conj_eq hy'U h n
  have hvU : (t * a * t⁻¹)⁻¹ ∈ U := inv_mem (hAU hvA)
  have key : ⁅t * a * t⁻¹, (t * y * t⁻¹) ^ n⁆ = ⁅t * a * t⁻¹, y' ^ n⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc t * a * t⁻¹ * (t * y * t⁻¹) ^ n * (t * a * t⁻¹)⁻¹ * ((t * y * t⁻¹) ^ n)⁻¹
        = (t * a * t⁻¹) * ((t * y * t⁻¹) ^ n * (t * a * t⁻¹)⁻¹ * ((t * y * t⁻¹) ^ n)⁻¹) := by
          group
      _ = (t * a * t⁻¹) * (y' ^ n * (t * a * t⁻¹)⁻¹ * (y' ^ n)⁻¹) := by rw [hpow _ hvU]
      _ = t * a * t⁻¹ * y' ^ n * (t * a * t⁻¹)⁻¹ * (y' ^ n)⁻¹ := by group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [key]
  exact Subgroup.commutator_mem_commutator hvA (pow_mem hy' n)

private theorem core_contradiction {S U E₀ : Subgroup G} {e y : G} {q m : ℕ}
    (hUS : U ≤ S) (hU : IsElemAbelian 2 U) (hE₀S : E₀ ≤ S) (hE₀ : IsElemAbelian 2 E₀)
    (hUe : e ∈ Subgroup.normalizer (U : Set G)) (hUy : y ∈ Subgroup.normalizer (U : Set G))
    (hUa : ∀ a ∈ E₀, a ∈ Subgroup.normalizer (U : Set G))
    (hee : e * e = 1) (hE₀e : ∀ a ∈ E₀, a * e = e * a)
    (hE₀y : ∀ a ∈ E₀, a * y * a⁻¹ * y⁻¹ ∈ Subgroup.centralizer (U : Set G))
    (hey : e * y * e⁻¹ * y ∈ Subgroup.centralizer (U : Set G))
    (hq : q.Prime) (hq7 : 7 ≤ q) (hyq : IsPGroup q (Subgroup.zpowers y))
    (hyU : ¬ ∀ u ∈ U, y * u = u * y)
    (hm : ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A → Nat.card A ≤ 2 ^ m)
    (hE₀card : 2 ^ m ≤ 4 * Nat.card E₀) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hyodd : Odd (orderOf y) := by
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨n, hn⟩ := hyq.exists_card_eq
    rw [Nat.card_zpowers] at hn
    rw [hn]
    exact hqodd.pow
  set X₀ : Subgroup G := U ⊓ Subgroup.centralizer (E₀ : Set G) with hX₀
  have hX₀U : X₀ ≤ U := inf_le_left
  have hX₀ab : IsElemAbelian 2 X₀ := hU.mono hX₀U
  have hmemX₀ : ∀ x, x ∈ X₀ ↔ x ∈ U ∧ ∀ a ∈ E₀, a * x = x * a := fun x => by
    rw [hX₀, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hact : ∀ a ∈ E₀, ∀ u ∈ U, (a * y * a⁻¹) * u * (a * y * a⁻¹)⁻¹ = y * u * y⁻¹ :=
    fun a ha u hu => conj_eq_of_mul_inv_mem hUy (hE₀y a ha) hu
  have hactE : ∀ u ∈ U, (e * y * e⁻¹) * u * (e * y * e⁻¹)⁻¹ = y⁻¹ * u * y := by
    intro u hu
    have h1 : (e * y * e⁻¹) * u * (e * y * e⁻¹)⁻¹ = y⁻¹ * u * y⁻¹⁻¹ :=
      conj_eq_of_mul_inv_mem (inv_mem hUy) (by simpa using hey) hu
    rw [h1, inv_inv]
  have hyX₀ : y ∈ Subgroup.normalizer (X₀ : Set G) := by
    apply mem_normalizer_of_conj_mem_fin
    intro x hx
    obtain ⟨hxU, hxE⟩ := (hmemX₀ x).1 hx
    refine (hmemX₀ _).2 ⟨(Subgroup.mem_normalizer_iff.1 hUy x).1 hxU, fun a ha => ?_⟩
    have h1 : a * (y * x * y⁻¹) * a⁻¹ = y * x * y⁻¹ := by
      calc a * (y * x * y⁻¹) * a⁻¹
          = (a * y * a⁻¹) * (a * x * a⁻¹) * (a * y * a⁻¹)⁻¹ := by group
        _ = (a * y * a⁻¹) * x * (a * y * a⁻¹)⁻¹ := by
          rw [show a * x * a⁻¹ = x by rw [hxE a ha]; group]
        _ = y * x * y⁻¹ := hact a ha x hxU
    calc a * (y * x * y⁻¹) = (a * (y * x * y⁻¹) * a⁻¹) * a := by group
      _ = (y * x * y⁻¹) * a := by rw [h1]
  have heX₀ : e ∈ Subgroup.normalizer (X₀ : Set G) := by
    apply mem_normalizer_of_conj_mem_fin
    intro x hx
    obtain ⟨hxU, hxE⟩ := (hmemX₀ x).1 hx
    refine (hmemX₀ _).2 ⟨(Subgroup.mem_normalizer_iff.1 hUe x).1 hxU, fun a ha => ?_⟩
    have hae : Commute a e := hE₀e a ha
    have hax : Commute a x := hxE a ha
    exact ((hae.mul_right hax).mul_right hae.inv_right).eq
  set W : Subgroup G := ⁅X₀, Subgroup.zpowers y⁆ with hW
  have hWX : W ≤ X₀ := CFSG.Goldschmidt.G75.commutator_zpowers_le_self hyX₀
  have hyW : y ∈ Subgroup.normalizer (W : Set G) :=
    mem_normalizer_commutator_zpowers hX₀U hyX₀ hUy (Subgroup.mem_zpowers y)
      (fun u _ => by group)
  have heW : e ∈ Subgroup.normalizer (W : Set G) :=
    mem_normalizer_commutator_zpowers hX₀U heX₀ hUy (inv_mem (Subgroup.mem_zpowers y))
      (fun u hu => by rw [hactE u hu, inv_inv])
  have hbot : ⁅X₀, Subgroup.zpowers y⁆ ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ :=
    CFSG.Goldschmidt.G75.commutator_inf_centralizer_eq_bot hX₀ab hyX₀ hyodd
  have hfixW : ∀ w ∈ W, y * w = w * y → w = 1 := by
    intro w hw hyw
    have hwc : w ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hyw
    have : w ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_inf.2 ⟨hw, hwc⟩
    exact Subgroup.mem_bot.1 this
  have h4 : Nat.card X₀ ≤ 4 * Nat.card (X₀ ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) := by
    have hcomm : ∀ a ∈ E₀, ∀ x ∈ X₀, a * x = x * a := fun a ha x hx => ((hmemX₀ x).1 hx).2 a ha
    have hEX : IsElemAbelian 2 (E₀ ⊔ X₀) := hE₀.sup_of_commute hX₀ab hcomm
    have hle : Nat.card (E₀ ⊔ X₀ : Subgroup G) ≤ 2 ^ m :=
      hm _ (sup_le hE₀S (hX₀U.trans hUS)) hEX
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₀ X₀ hcomm).1
    have hinf : Nat.card (E₀ ⊓ X₀ : Subgroup G) ≤
        Nat.card (X₀ ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) := by
      refine Subgroup.card_le_of_le (le_inf inf_le_right ?_)
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hE₀e a (Subgroup.mem_inf.1 ha).1).symm
    have hpos : 0 < Nat.card E₀ := Nat.card_pos
    have hmul : Nat.card E₀ * Nat.card X₀ ≤ Nat.card E₀ *
        (4 * Nat.card (X₀ ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G)) := by
      calc Nat.card E₀ * Nat.card X₀
          = Nat.card (E₀ ⊔ X₀ : Subgroup G) * Nat.card (E₀ ⊓ X₀ : Subgroup G) := hcard.symm
        _ ≤ 2 ^ m * Nat.card (X₀ ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
          Nat.mul_le_mul hle hinf
        _ ≤ (4 * Nat.card E₀) *
            Nat.card (X₀ ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
          Nat.mul_le_mul hE₀card le_rfl
        _ = Nat.card E₀ *
            (4 * Nat.card (X₀ ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G)) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hpos
  have hWbot : W = ⊥ :=
    eq_bot_of_transvection hWX hX₀ab hq hq7 hyq hyW heW hee
      (fun w hw => hactE w (hX₀U (hWX hw))) hfixW h4
  have hcommy : ∀ u ∈ U, ⁅u, y⁆ = 1 → y * u = u * y := by
    intro u _ h
    rw [commutatorElement_def] at h
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)).symm
  have hX₀y : ∀ x ∈ X₀, y * x = x * y := by
    intro x hx
    have h1 : ⁅x, y⁆ ∈ W := Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers y)
    rw [hWbot] at h1
    exact hcommy x (hX₀U hx) (Subgroup.mem_bot.1 h1)
  set W₂ : Subgroup G := ⁅U, Subgroup.zpowers y⁆ with hW₂
  have hW₂U : W₂ ≤ U := CFSG.Goldschmidt.G75.commutator_zpowers_le_self hUy
  have hW₂ne : W₂ ≠ ⊥ := by
    intro h
    apply hyU
    intro u hu
    have h1 : ⁅u, y⁆ ∈ W₂ := Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers y)
    rw [h] at h1
    exact hcommy u hu (Subgroup.mem_bot.1 h1)
  have hE₀W₂ : E₀ ≤ Subgroup.normalizer (W₂ : Set G) := fun a ha =>
    mem_normalizer_commutator_zpowers le_rfl (hUa a ha) hUy (Subgroup.mem_zpowers y)
      (hact a ha)
  obtain ⟨v, hvW, hv1, hvcomm⟩ := exists_fixed_ne_one (p := 2) (P := E₀) (N := W₂)
    hE₀.isPGroup hE₀W₂ hW₂ne (hU.mono hW₂U).isPGroup
  have hvX₀ : v ∈ X₀ := (hmemX₀ v).2 ⟨hW₂U hvW, fun a ha => hvcomm a ha⟩
  have hbot2 : ⁅U, Subgroup.zpowers y⁆ ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ :=
    CFSG.Goldschmidt.G75.commutator_inf_centralizer_eq_bot hU hUy hyodd
  have hvc : v ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hX₀y v hvX₀
  have : v ∈ (⊥ : Subgroup G) := hbot2 ▸ Subgroup.mem_inf.2 ⟨hvW, hvc⟩
  exact hv1 (Subgroup.mem_bot.1 this)

private theorem exists_transvection_data {Q : Type} [Group Q] [Finite Q] {X Eb : Subgroup Q}
    (hEb : IsElemAbelian 2 Eb) (hEbX : Eb ≤ Subgroup.normalizer (X : Set Q))
    (hX : Odd (Nat.card X)) {x₀ e₀ : Q} (hx₀ : x₀ ∈ X) (he₀ : e₀ ∈ Eb) (hne : e₀ * x₀ ≠ x₀ * e₀) :
    ∃ (F : Subgroup Q) (e y : Q) (q : ℕ), q.Prime ∧ F ≤ Eb ∧ Nat.card Eb ≤ 2 * Nat.card F ∧
      e ∈ Eb ∧ y ∈ X ∧ orderOf y = q ∧ (∀ f ∈ F, f * y = y * f) ∧ e * y * e⁻¹ = y⁻¹ := by
  have hgen := le_iSup_centralizer_index_two hEb hEbX hX
  obtain ⟨F, hFE, hFcard, x, hxX, hxF, hxe⟩ : ∃ F : Subgroup Q, F ≤ Eb ∧
      Nat.card Eb ≤ 2 * Nat.card F ∧ ∃ x ∈ X, (∀ f ∈ F, f * x = x * f) ∧ e₀ * x ≠ x * e₀ := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hle : X ≤ Subgroup.centralizer ({e₀} : Set Q) := by
      refine hgen.trans (iSup_le fun F => iSup_le fun hF => iSup_le fun hcard => ?_)
      intro x hx
      obtain ⟨hxX, hxF⟩ := Subgroup.mem_inf.1 hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcon F hF hcard x hxX (Subgroup.mem_centralizer_iff.1 hxF)
    exact Subgroup.mem_centralizer_iff.1 (hle hx₀) e₀ (Set.mem_singleton e₀)
  have hee : e₀ * e₀ = 1 := hEb.mul_self_eq_one he₀
  set c : Q := x⁻¹ * (e₀ * x * e₀⁻¹) with hc
  have hcX : c ∈ X := mul_mem (inv_mem hxX) ((Subgroup.mem_normalizer_iff.1 (hEbX he₀) x).1 hxX)
  have hcF : ∀ f ∈ F, f * c = c * f := by
    intro f hf
    have hfx : Commute f x := hxF f hf
    have hfe : Commute f e₀ := hEb.comm (hFE hf) he₀
    exact (hfx.inv_right.mul_right ((hfe.mul_right hfx).mul_right hfe.inv_right)).eq
  have hc1 : c ≠ 1 := by
    intro h1
    apply hxe
    have h2 : e₀ * x * e₀⁻¹ = x := (inv_mul_eq_one.1 h1).symm
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hec : e₀ * c * e₀⁻¹ = c⁻¹ := by
    calc e₀ * c * e₀⁻¹ = (e₀ * x * e₀⁻¹)⁻¹ * ((e₀ * e₀) * x * (e₀ * e₀)⁻¹) := by rw [hc]; group
      _ = (e₀ * x * e₀⁻¹)⁻¹ * x := by rw [hee]; simp
      _ = c⁻¹ := by rw [hc]; group
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (show orderOf c ≠ 1 from
    mt orderOf_eq_one_iff.1 hc1)
  refine ⟨F, e₀, c ^ (orderOf c / q), q, hq, hFE, hFcard, he₀, pow_mem hcX _,
    orderOf_pow_orderOf_div (orderOf_pos c).ne' hqdvd, fun f hf => ?_, ?_⟩
  · exact (Commute.pow_right (show Commute f c from hcF f hf) _).eq
  · rw [← conj_pow, hec, inv_pow]

private theorem normal_centralizer_subgroupOf {R U : Subgroup G}
    (hUn : R ≤ Subgroup.normalizer (U : Set G)) :
    ((Subgroup.centralizer (U : Set G)).subgroupOf R).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : G) ∈ Subgroup.normalizer (U : Set G) := hUn g.2
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro u hu
  have hv : (g : G)⁻¹ * u * g ∈ U := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) u).1 hu
    simpa using this
  have key := hn _ hv
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc u * ((g : G) * n * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * u * g) * n) * (g : G)⁻¹ := by group
    _ = (g : G) * (n * ((g : G)⁻¹ * u * g)) * (g : G)⁻¹ := by rw [key]
    _ = (g : G) * n * (g : G)⁻¹ * u := by group

private theorem card_bar_eq' {R K X : Subgroup G} [(K.subgroupOf R).Normal] (hXR : X ≤ R) :
    Nat.card (bar R K X) = K.relIndex X := by
  let f : ↥X →* ↥(bar R K X) :=
    MonoidHom.codRestrict ((QuotientGroup.mk' (K.subgroupOf R)).comp (Subgroup.inclusion hXR))
      (bar R K X) (fun x => mk_mem_bar (r := Subgroup.inclusion hXR x) x.2)
  have hsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨(r : G), Subgroup.mem_subgroupOf.mp hr⟩, rfl⟩
  have hone : ∀ r : ↥R, QuotientGroup.mk' (K.subgroupOf R) r = 1 ↔ (r : G) ∈ K :=
    fun r => (QuotientGroup.eq_one_iff r).trans Subgroup.mem_subgroupOf.symm
  have hker : f.ker = K.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (hone (Subgroup.inclusion hXR x)).mp (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext ((hone (Subgroup.inclusion hXR x)).mpr hx)
  have h5 : ((⊥ : Subgroup ↥(bar R K X)).comap f).index = (⊥ : Subgroup ↥(bar R K X)).index :=
    Subgroup.index_comap_of_surjective (⊥ : Subgroup ↥(bar R K X)) hsurj
  have h4 : (K.subgroupOf X).index = Nat.card (bar R K X) := by
    rw [← hker]
    exact h5.trans Subgroup.index_bot
  exact h4.symm

private theorem barPre_le_aux {R K : Subgroup G} [(K.subgroupOf R).Normal] (A : Subgroup G)
    (E : Subgroup (↥R ⧸ K.subgroupOf R)) : barPre R K A E ≤ A :=
  fun _ ha => (mem_barPre_iff.1 ha).1

private theorem exists_two_pow_eq_one_of_mem_bar {R K S : Subgroup G} [(K.subgroupOf R).Normal]
    (hS : IsPGroup 2 S) {g : ↥R ⧸ K.subgroupOf R} (hg : g ∈ bar R K S) :
    ∃ n : ℕ, g ^ (2 ^ n) = 1 := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨n, hn⟩ := hS ⟨(s : G), Subgroup.mem_subgroupOf.1 hs⟩
  refine ⟨n, ?_⟩
  have hs1 : s ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
  rw [← map_pow, hs1, map_one]

private theorem exists_comm_not_mem {R S L C E : Subgroup G} [(C.subgroupOf R).Normal]
    (hSR : S ≤ R) (hS : IsPGroup 2 S) (hLR : L ≤ R) (hLn : R ≤ Subgroup.normalizer (L : Set G))
    (hRLS : (L : Set G) * (S : Set G) = (R : Set G))
    (hCred : ∀ K : Subgroup G, K ≤ R → R ≤ Subgroup.normalizer (K : Set G) →
      (∀ k ∈ K, ∃ n : ℕ, k ^ (2 ^ n) ∈ C) → K ≤ C)
    (hES : E ≤ S) (hEC : ¬ E ≤ C) :
    ∃ e₀ ∈ E, ∃ l ∈ L, e₀ * l * e₀⁻¹ * l⁻¹ ∉ C := by
  by_contra hcon
  push Not at hcon
  apply hEC
  set Sb : Subgroup (↥R ⧸ C.subgroupOf R) := bar R C S with hSb
  set Lb : Subgroup (↥R ⧸ C.subgroupOf R) := bar R C L with hLb
  set Kb : Subgroup (↥R ⧸ C.subgroupOf R) :=
    Sb ⊓ Subgroup.centralizer (Lb : Set (↥R ⧸ C.subgroupOf R)) with hKb
  have hSbN : Sb ≤ Subgroup.normalizer (Lb : Set (↥R ⧸ C.subgroupOf R)) :=
    bar_le_normalizer hSR hLR (fun x hx => hLn (hSR hx))
  have hKbS : ∀ σ ∈ Sb, ∀ n ∈ Kb, σ * n * σ⁻¹ ∈ Kb := by
    intro σ hσ n hn
    obtain ⟨hnS, hnC⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hσ hnS) (inv_mem hσ), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hnC ⊢
    intro p hp
    have hp' : σ⁻¹ * p * σ ∈ Lb := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hSbN hσ)) p).1 hp
      simpa using this
    have hpn := hnC _ hp'
    calc p * (σ * n * σ⁻¹) = σ * ((σ⁻¹ * p * σ) * n) * σ⁻¹ := by group
      _ = σ * (n * (σ⁻¹ * p * σ)) * σ⁻¹ := by rw [hpn]
      _ = σ * n * σ⁻¹ * p := by group
  have hKbn : Kb.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf R) g
    obtain ⟨l, hl, s, hs, hls⟩ := Set.mem_mul.1
      (show (r : G) ∈ (L : Set G) * (S : Set G) by rw [hRLS]; exact r.2)
    have hr : r = ⟨l, hLR hl⟩ * ⟨s, hSR hs⟩ := Subtype.ext hls.symm
    have hσ : QuotientGroup.mk' (C.subgroupOf R) ⟨s, hSR hs⟩ ∈ Sb :=
      mk_mem_bar (r := ⟨s, hSR hs⟩) hs
    have hℓ : QuotientGroup.mk' (C.subgroupOf R) ⟨l, hLR hl⟩ ∈ Lb :=
      mk_mem_bar (r := ⟨l, hLR hl⟩) hl
    have h1 := hKbS _ hσ n hn
    have h2 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 h1).2 _ hℓ
    rw [hr, map_mul]
    set ℓ := QuotientGroup.mk' (C.subgroupOf R) ⟨l, hLR hl⟩
    set σ := QuotientGroup.mk' (C.subgroupOf R) ⟨s, hSR hs⟩
    have h3 : ℓ * σ * n * (ℓ * σ)⁻¹ = σ * n * σ⁻¹ := by
      calc ℓ * σ * n * (ℓ * σ)⁻¹ = ℓ * (σ * n * σ⁻¹) * ℓ⁻¹ := by group
        _ = (σ * n * σ⁻¹ * ℓ) * ℓ⁻¹ := by rw [h2]
        _ = σ * n * σ⁻¹ := by group
    rw [h3]
    exact h1
  set K : Subgroup G := (Kb.comap (QuotientGroup.mk' (C.subgroupOf R))).map R.subtype with hK
  have hKR : K ≤ R := Subgroup.map_subtype_le _
  have hKn : R ≤ Subgroup.normalizer (K : Set G) := by
    have hN : (Kb.comap (QuotientGroup.mk' (C.subgroupOf R))).Normal := hKbn.comap _
    have key : ∀ r : ↥R, ∀ y ∈ K, (r : G) * y * (r : G)⁻¹ ∈ K := by
      rintro r _ ⟨k, hk, rfl⟩
      exact ⟨r * k * r⁻¹, hN.conj_mem k hk r, by simp⟩
    intro r hr
    exact Sec7.mem_normalizer_of_conj_mem (key ⟨r, hr⟩)
      (fun y hy => by simpa using key ⟨r, hr⟩⁻¹ y hy)
  have hKp : ∀ k ∈ K, ∃ n : ℕ, k ^ (2 ^ n) ∈ C := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : QuotientGroup.mk' (C.subgroupOf R) x ∈ Kb := hx
    have hxS : QuotientGroup.mk' (C.subgroupOf R) x ∈ Sb := (Subgroup.mem_inf.1 hx').1
    obtain ⟨n, hn⟩ := exists_two_pow_eq_one_of_mem_bar hS hxS
    refine ⟨n, ?_⟩
    have h1 : QuotientGroup.mk' (C.subgroupOf R) (x ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact hn
    have := (mk_eq_one_iff _).1 h1
    simpa using this
  have hKC := hCred K hKR hKn hKp
  intro e he
  apply hKC
  have heR : e ∈ R := hSR (hES he)
  refine ⟨⟨e, heR⟩, ?_, rfl⟩
  refine Subgroup.mem_inf.2 ⟨mk_mem_bar (r := ⟨e, heR⟩) (hES he), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.1 hp
  have hlL : (l' : G) ∈ L := Subgroup.mem_subgroupOf.1 hl'
  exact ((mk_commute_iff ⟨e, heR⟩ l').2 (hcon e he l' hlL)).symm

theorem jOneOf_le_centralizer_of_reduced {R S L H U : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card R) (h5 : ¬ 5 ∣ Nat.card R) (hSR : S ≤ R) (hS : IsPGroup 2 S)
    (hLR : L ≤ R) (hLn : R ≤ Subgroup.normalizer (L : Set G)) (hH : H = S ⊓ L)
    (hLodd : ¬ 2 ∣ H.relIndex L) (hRLS : (L : Set G) * (S : Set G) = (R : Set G))
    (hUR : U ≤ R) (hUn : R ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U)
    (hUH : U ≤ H) (hHU : H ≤ Subgroup.centralizer (U : Set G))
    (hUred : ∀ K : Subgroup G, K ≤ R → R ≤ Subgroup.normalizer (K : Set G) →
      (∀ k ∈ K, ∃ n : ℕ, k ^ (2 ^ n) ∈ Subgroup.centralizer (U : Set G)) →
      K ≤ Subgroup.centralizer (U : Set G)) :
    jOneOf S ≤ Subgroup.centralizer (U : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hCN := normal_centralizer_subgroupOf hUn
  refine iSup₂_le fun E hE => ?_
  obtain ⟨hES, hEab, hEcard⟩ := hE
  have hmax : ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A →
      Nat.card A ≤ 2 ^ CFSG.Open.pRank 2 S := by
    intro A hAS hA
    obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (CFSG.SectionRank.le_pRank Nat.one_lt_two hAS hA hk)
  generalize CFSG.Open.pRank 2 S = m at hEcard hmax
  by_contra hEC
  obtain ⟨e₀, he₀, l₀, hl₀, hne⟩ := exists_comm_not_mem hSR hS hLR hLn hRLS hUred hES hEC
  have hER : E ≤ R := hES.trans hSR
  have hl₀R : l₀ ∈ R := hLR hl₀
  have he₀R : e₀ ∈ R := hER he₀
  have hHS : H ≤ S := hH ▸ inf_le_left
  have hXodd : Odd (Nat.card (bar R (Subgroup.centralizer (U : Set G)) L)) := by
    rw [card_bar_eq' hLR]
    have h1 : (Subgroup.centralizer (U : Set G)).relIndex L ∣ H.relIndex L :=
      Subgroup.relIndex_dvd_of_le_left L hHU
    have h2 : ¬ 2 ∣ (Subgroup.centralizer (U : Set G)).relIndex L := fun h => hLodd (h.trans h1)
    exact Nat.odd_iff.mpr (by omega)
  have hEb : IsElemAbelian 2 (bar R (Subgroup.centralizer (U : Set G)) E) :=
    isElemAbelian_bar hEab
  have hEbX : bar R (Subgroup.centralizer (U : Set G)) E ≤
      Subgroup.normalizer ((bar R (Subgroup.centralizer (U : Set G)) L : Subgroup _) : Set _) :=
    bar_le_normalizer hER hLR (fun x hx => hLn (hER hx))
  obtain ⟨F, eb, yb, q, hq, hFE, hFcard, heb, hyb, hyord, hyF, heyb⟩ :=
    exists_transvection_data hEb hEbX hXodd
      (x₀ := QuotientGroup.mk' ((Subgroup.centralizer (U : Set G)).subgroupOf R) ⟨l₀, hl₀R⟩)
      (e₀ := QuotientGroup.mk' ((Subgroup.centralizer (U : Set G)).subgroupOf R) ⟨e₀, he₀R⟩)
      (mk_mem_bar (r := ⟨l₀, hl₀R⟩) hl₀) (mk_mem_bar (r := ⟨e₀, he₀R⟩) he₀)
      (fun h => hne ((mk_commute_iff ⟨e₀, he₀R⟩ ⟨l₀, hl₀R⟩).1 h))
  have hqX : q ∣ Nat.card (bar R (Subgroup.centralizer (U : Set G)) L) := by
    rw [← hyord]
    exact Subgroup.orderOf_dvd_natCard _ hyb
  have hqR : q ∣ Nat.card R :=
    hqX.trans ((card_bar_dvd hLR).trans (Subgroup.card_dvd_of_le hLR))
  have hq2 : q ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 (h ▸ hqX))
  have hq3 : q ≠ 3 := fun h => h3 (h ▸ hqR)
  have hq5 : q ≠ 5 := fun h => h5 (h ▸ hqR)
  have hq7 : 7 ≤ q := by
    by_contra hlt
    have h2 := hq.two_le
    interval_cases q <;> first | omega | exact absurd hq (by norm_num)
  obtain ⟨y, hyL, hyP, hyπ⟩ := exists_pPow_lift hLR hq hyb hyord
  obtain ⟨e, heE, heπ⟩ : ∃ e : ↥R, (e : G) ∈ E ∧
      QuotientGroup.mk' ((Subgroup.centralizer (U : Set G)).subgroupOf R) e = eb := by
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp heb
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, hxe⟩
  have hE₀y : ∀ a ∈ barPre R (Subgroup.centralizer (U : Set G)) E F,
      a * (y : G) * a⁻¹ * (y : G)⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro a ha
    obtain ⟨haE, haR, haF⟩ := mem_barPre_iff.1 ha
    have h1 := hyF _ haF
    rw [← hyπ] at h1
    exact (mk_commute_iff ⟨a, haR⟩ y).1 h1
  have hey : (e : G) * (y : G) * (e : G)⁻¹ * (y : G) ∈ Subgroup.centralizer (U : Set G) := by
    have h1 : QuotientGroup.mk' ((Subgroup.centralizer (U : Set G)).subgroupOf R)
        (e * y * e⁻¹ * y) = 1 := by
      simp only [map_mul, map_inv, heπ, hyπ]
      rw [heyb]
      simp
    have h2 := (mk_eq_one_iff _).1 h1
    simpa using h2
  have hyU : ¬ ∀ u ∈ U, (y : G) * u = u * y := by
    intro hall
    have hyC : (y : G) ∈ Subgroup.centralizer (U : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun u hu => (hall u hu).symm
    have h1 := (mk_eq_one_iff y).2 hyC
    rw [hyπ] at h1
    rw [h1, orderOf_one] at hyord
    exact hq.one_lt.ne' hyord.symm
  have hE₀card : 2 ^ m ≤
      4 * Nat.card (barPre R (Subgroup.centralizer (U : Set G)) E F) := by
    have h1 := card_le_two_mul_card_barPre hER hFE hFcard
    have h2 : 2 ^ m ≤ 2 * 2 ^ (m - 1) := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h]; norm_num
      · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [hk]; simp [pow_succ, mul_comm]
    omega
  exact core_contradiction (S := S) (U := U)
    (E₀ := barPre R (Subgroup.centralizer (U : Set G)) E F) (e := (e : G)) (y := (y : G))
    (q := q) (m := m) (hUH.trans hHS) hU ((barPre_le_aux _ _).trans hES)
    (hEab.mono (barPre_le_aux _ _)) (hUn e.2) (hUn y.2)
    (fun a ha => hUn (hSR (hES (barPre_le_aux _ _ ha)))) (hEab.mul_self_eq_one heE)
    (fun a ha => hEab.comm (barPre_le_aux _ _ ha) heE) hE₀y hey hq hq7 hyP hyU hmax hE₀card

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
