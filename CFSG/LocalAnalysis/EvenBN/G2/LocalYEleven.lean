module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTen
public import CFSG.LocalAnalysis.EvenBN.G2.AutomorphismsTorus

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

theorem exists_mem_normalizer_not_mem_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P Q : Subgroup G} (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ normalizer (P : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (P : Set G)).subgroupOf Q := by
    rw [subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact mem_subgroupOf.mp hy

theorem three_le_of_card_eq {K : Type*} {f : ℕ} (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    3 ≤ f := by
  by_contra hf
  have : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem normalizer_yamadaC₁_le (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaD₁ d t : Set G) ∧
      normalizer (yamadaD₁ d t : Set G) ≤ normalizer (yamadaU₁ d t : Set G) := by
  have h2 := normalizer_le_normalizer_thompsonSubgroup (yamadaC₁ d t)
  rw [h.yamada_5_11_2 d hK hD] at h2
  have h3 := normalizer_le_normalizer_center (yamadaD₁ d t)
  rw [← (hD.yamada_5_10_3).1] at h3
  exact ⟨h2, h3⟩

theorem yamadaR₂_le_normalizer_yamadaC₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₂ d t ≤ normalizer (yamadaC₁ d t : Set G) := by
  have := (h.yamada_5_15_6 d hK hD).2.2.1
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaC₁ d t).subgroupOf (yamadaR₂ d t))
  rw [map_subgroupOf_eq_of_le (h.yamadaC₁_le_yamadaR₂ d hK)] at h1
  exact le_normalizer.trans h1

theorem exists_conj_t_eq (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ normalizer (yamadaC₁ d t : Set G)) :
    ∃ δ ∈ yamadaD₁ d t, x * t * x⁻¹ = t * δ := by
  have hxD₁ := (h.normalizer_yamadaC₁_le d hK hD).1 hx
  have hc : x * t * x⁻¹ ∈ yamadaC₁ d t := (mem_normalizer_iff.1 hx t).1 (h.t_mem_yamadaC₁ d hK)
  have htN : zpowers t ≤ normalizer (yamadaD₁ d t : Set G) :=
    (zpowers_le).2 (h.yamadaC₁_le_normalizer_yamadaD₁ d hK (h.t_mem_yamadaC₁ d hK))
  rw [(h.yamada_5_8_1 d hK).2.1, sup_comm] at hc
  obtain ⟨τ, hτ, δ, hδ, e⟩ := Common.exists_mul_of_le_normalizer' htN _ hc
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  rcases h.zpow_eq_one_or_eq k with h1 | h1
  · exfalso
    rw [h1, one_mul] at e
    refine h.t_not_mem_yamadaD₁ d hK ?_
    have := (mem_normalizer_iff.1 (inv_mem hxD₁) _).1 (e ▸ hδ : x * t * x⁻¹ ∈ yamadaD₁ d t)
    simpa [mul_assoc] using this
  · exact ⟨δ, hδ, by rw [e, h1]⟩

theorem exists_conj_t_mul_mul (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {z w : G} (hz : z ∈ yamadaU₁ d t) (hw : w ∈ d.U) :
    ∃ y ∈ yamadaU₁ d t, y * (t * (z * w)) * y⁻¹ = t * z := by
  obtain ⟨-, hUU₁, -⟩ := hD.spec
  obtain ⟨x, hx, hxw⟩ := hD.exists_mem_crossed hK hw
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.1
    (((d.image_le _).trans h.L_le_centralizer) hw)
  have hww : w * w = 1 := (h.cosetData_tU d hK).mul_self_of_mem hw
  have hxt : x⁻¹ * t * x = w * t := by
    calc x⁻¹ * t * x = x⁻¹ * t * x * t * t := by rw [mul_assoc _ t t, h.t_mul_t, mul_one]
      _ = w * t := by rw [hxw]
  have hxz : x * (z * w) = (z * w) * x :=
    hD.mul_comm hx (mul_mem hz (hUU₁ hw))
  have hzw : z * w = w * z := hD.mul_comm hz (hUU₁ hw)
  have hxz' : x⁻¹ * (z * w) * x = z * w := by rw [mul_assoc, ← hxz, inv_mul_cancel_left]
  refine ⟨x⁻¹, inv_mem hx, ?_⟩
  calc x⁻¹ * (t * (z * w)) * x⁻¹⁻¹ = x⁻¹ * t * x * (x⁻¹ * (z * w) * x) := by group
    _ = x⁻¹ * t * x * (z * w) := by rw [hxz']
    _ = t * w * (w * z) := by rw [hxt, hwt, hzw]
    _ = t * z := by rw [mul_assoc, ← mul_assoc w, hww, one_mul]

theorem forall_conj_t_mul (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {u₀ g : G} (hu₀ : u₀ ∈ yamadaU₁ d t) (hu₀U : u₀ ∉ d.U)
    (hg : g * t * g⁻¹ = t * u₀) {v : G} (hv : v ∈ yamadaU₁ d t) :
    ∃ g' : G, g' * t * g'⁻¹ = t * v := by
  obtain ⟨ν, hνmul, -, -, hνscal, hκU, hκker⟩ := hD.exists_coords hK
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ := h.yamadaU₁_le_yamadaC₁ d hK hD
  have hV : ∀ {x : G}, x ∈ yamadaU₁ d t → x ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.U : Set G) := fun hx =>
    ⟨yamadaC₁_le d t (hU₁C₁ hx), hC₁U (hU₁C₁ hx)⟩
  have hν1 : ν 1 = 0 := by
    have := hνmul (one_mem d.U) (one_mem d.U)
    rwa [mul_one, left_eq_add] at this
  set θ : G → K := fun x => ν (x⁻¹ * t * x * t) with hθdef
  have hθmul : ∀ {x y : G}, x ∈ yamadaU₁ d t → y ∈ yamadaU₁ d t → θ (x * y) = θ x + θ y :=
    fun hx hy => by
      simp only [hθdef]
      rw [hc₁.crossed_mul_of_mem (hV hx) (hV hy), hνmul (hκU hx) (hκU hy)]
  have hθker : ∀ {x : G}, x ∈ yamadaU₁ d t → (θ x = 0 ↔ x ∈ d.U) := fun hx => by
    rw [← hν1]
    exact hκker hx
  suffices hsuff : ∃ g₁ : G, ∃ w ∈ d.U, g₁ * t * g₁⁻¹ = t * (v * w) by
    obtain ⟨g₁, w, hw, hg₁⟩ := hsuff
    obtain ⟨y, -, hy⟩ := h.exists_conj_t_mul_mul d hK hD hv hw
    refine ⟨y * g₁, ?_⟩
    calc y * g₁ * t * (y * g₁)⁻¹ = y * (g₁ * t * g₁⁻¹) * y⁻¹ := by group
      _ = t * v := by rw [hg₁, hy]
  by_cases hθv : θ v = 0
  · exact ⟨1, v⁻¹, inv_mem ((hθker hv).1 hθv), by group⟩
  · have hθu₀ : θ u₀ ≠ 0 := fun e => hu₀U ((hθker hu₀).1 e)
    obtain ⟨j, hj, hjν⟩ := hνscal (θ v * (θ u₀)⁻¹) (mul_ne_zero hθv (inv_ne_zero hθu₀))
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
      (h.L_le_centralizer (d.J₃_le_inf_normalizer_U hj).1)
    have hz := hD.conj_mem hK hj hu₀
    have hθz : θ (j * u₀ * j⁻¹) = θ v := by
      show ν ((j * u₀ * j⁻¹)⁻¹ * t * (j * u₀ * j⁻¹) * t) = θ v
      rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hjt, hjν _ (hκU hu₀)]
      change θ v * (θ u₀)⁻¹ * θ u₀ = θ v
      rw [inv_mul_cancel_right₀ hθu₀]
    have hw : v⁻¹ * (j * u₀ * j⁻¹) ∈ d.U := by
      refine (hθker (mul_mem (inv_mem hv) hz)).1 ?_
      have h1 := hθmul (inv_mem hv) hv
      rw [inv_mul_cancel, (hθker (one_mem _)).2 (one_mem _)] at h1
      rw [hθmul (inv_mem hv) hz, hθz]
      exact h1.symm
    refine ⟨j * g, v⁻¹ * (j * u₀ * j⁻¹), hw, ?_⟩
    calc j * g * t * (j * g)⁻¹ = j * (g * t * g⁻¹) * j⁻¹ := by group
      _ = j * t * u₀ * j⁻¹ := by rw [hg]; group
      _ = t * (j * u₀ * j⁻¹) := by rw [hjt]; group
      _ = t * (v * (v⁻¹ * (j * u₀ * j⁻¹))) := by group

theorem commutator_mem_yamadaU₁_of_mem_yamadaY₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {y δ : G} (hy : y ∈ yamadaY₂ d t)
    (hδ : δ ∈ yamadaD₁ d t) : y * δ * y⁻¹ * δ⁻¹ ∈ yamadaU₁ d t := by
  obtain ⟨-, -, -, -, -, -, -, hDS, -⟩ := d.inclusions
  have hU₁N : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
    (h.yamadaU₁_le_yamadaC₁ d hK hD).trans (h.yamadaC₁_le_normalizer_D d hK)
  rw [hD.D₁_eq] at hδ
  obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁N δ hδ
  have hby : b * y⁻¹ = y⁻¹ * b :=
    h.yamadaY₂_mul_comm d hK hD (yamadaU₁_le_yamadaY₂ d t hb) (inv_mem hy)
  have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by
    calc y * (a * b) * y⁻¹ * (a * b)⁻¹ = y * a * (b * y⁻¹) * b⁻¹ * a⁻¹ := by group
      _ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by rw [hby]; group
  rw [e]
  exact inv_mem (h.commutator_mem_yamadaU₁_of_mem_S d hK hD (hDS ha) hy)

theorem exists_conj_t_eq_mul_of_mem_D (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {δ : G} (hδ : δ ∈ d.D) :
    ∃ x ∈ normalizer (yamadaC₁ d t : Set G),
      (∀ y ∈ yamadaD₁ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaU₁ d t) ∧
        ∃ u ∈ yamadaU₁ d t, x * t * x⁻¹ = t * δ * u := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hBD₁, hD₁U₁⟩ := h.normalizer_yamadaC₁_le d hK hD
  obtain ⟨hU₁D₁, hUU₁, -⟩ := hD.spec
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  obtain ⟨hNU, hND, -, -⟩ := d.yamada_3_13_2_G
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  have hK₀ : ∀ g ∈ normalizer (yamadaC₁ d t : Set G), ∀ y ∈ yamadaD₁ d t,
      g * y * g⁻¹ ∈ yamadaD₁ d t := fun g hg y hy => (mem_normalizer_iff.1 (hBD₁ hg) y).1 hy
  have hB : ∀ g ∈ normalizer (yamadaC₁ d t : Set G), ∀ b ∈ yamadaU₁ d t,
      g * b * g⁻¹ ∈ yamadaU₁ d t := fun g hg b hb =>
    (mem_normalizer_iff.1 (hD₁U₁ (hBD₁ hg)) b).1 hb
  have hD₁N : ∀ {a : G}, a ∈ yamadaD₁ d t → ∀ {z : G}, z ∈ yamadaU₁ d t →
      a * z * a⁻¹ ∈ yamadaU₁ d t := fun ha z hz =>
    (mem_normalizer_iff.1 (hD₁U₁ (le_normalizer ha)) z).1 hz
  set V := Common.centralizerMod (normalizer (yamadaC₁ d t : Set G)) (yamadaD₁ d t)
    (yamadaU₁ d t) hK₀ hB with hVdef
  let W : Subgroup G :=
    { carrier := {a | a ∈ yamadaD₁ d t ∧ ∃ x ∈ V, ∃ u ∈ yamadaU₁ d t, x * t * x⁻¹ = t * a * u}
      mul_mem' := by
        rintro a b ⟨ha, x, hx, u, hu, hxa⟩ ⟨hb, y, hy, v, hv, hyb⟩
        obtain ⟨hxB, hxc⟩ := Common.mem_centralizerMod.1 hx
        refine ⟨mul_mem ha hb, x * y, mul_mem hx hy,
          b⁻¹ * (u * (x * b * x⁻¹ * b⁻¹)) * b⁻¹⁻¹ * (x * v * x⁻¹),
          mul_mem (hD₁N (inv_mem hb) (mul_mem hu (hxc b hb))) (hB x hxB v hv), ?_⟩
        calc x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
          _ = x * t * x⁻¹ * (x * b * x⁻¹) * (x * v * x⁻¹) := by rw [hyb]; group
          _ = t * a * u * (x * b * x⁻¹) * (x * v * x⁻¹) := by rw [hxa]
          _ = t * (a * b) * (b⁻¹ * (u * (x * b * x⁻¹ * b⁻¹)) * b⁻¹⁻¹ * (x * v * x⁻¹)) := by
              group
      one_mem' := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by group⟩
      inv_mem' := by
        rintro a ⟨ha, x, hx, u, hu, hxa⟩
        obtain ⟨hxB, -⟩ := Common.mem_centralizerMod.1 hx
        obtain ⟨-, hxc'⟩ := Common.mem_centralizerMod.1 (inv_mem hx)
        refine ⟨inv_mem ha, x⁻¹, inv_mem hx,
          a * ((x⁻¹ * u⁻¹ * x⁻¹⁻¹) * (x⁻¹ * a⁻¹ * x⁻¹⁻¹ * a⁻¹⁻¹)) * a⁻¹,
          hD₁N ha (mul_mem (hB x⁻¹ (inv_mem hxB) u⁻¹ (inv_mem hu)) (hxc' a⁻¹ (inv_mem ha))), ?_⟩
        calc x⁻¹ * t * x⁻¹⁻¹ = x⁻¹ * (t * a * u) * (u⁻¹ * a⁻¹) * x := by group
          _ = x⁻¹ * (x * t * x⁻¹) * (u⁻¹ * a⁻¹) * x := by rw [hxa]
          _ = t * a⁻¹ * (a * ((x⁻¹ * u⁻¹ * x⁻¹⁻¹) * (x⁻¹ * a⁻¹ * x⁻¹⁻¹ * a⁻¹⁻¹)) * a⁻¹) := by
              group }
  have hW : ∀ {a : G}, a ∈ W ↔
      a ∈ yamadaD₁ d t ∧ ∃ x ∈ V, ∃ u ∈ yamadaU₁ d t, x * t * x⁻¹ = t * a * u := Iff.rfl
  have hY₂V : yamadaY₂ d t ≤ V := fun y hy =>
    Common.mem_centralizerMod.2 ⟨h.yamadaR₂_le_normalizer_yamadaC₁ d hK hD
      (h.yamadaY₂_le_yamadaR₂ d hK hD hy),
      fun δ hδ => h.commutator_mem_yamadaU₁_of_mem_yamadaY₂ d hK hD hy hδ⟩
  obtain ⟨u, hu, huU⟩ := h.exists_mem_yamadaU₁_not_mem_U d hK hD
  obtain ⟨hcU, hce⟩ := h.crossed_mem_of_mem_yamadaU₁ d hK hD hu
  set c := d.wb * (u⁻¹ * t * u * t) * d.wb⁻¹ with hcdef
  have hcY : c ∈ d.Y := (mem_normalizer_iff.1 d.wb_mem_normalizer.1.2 _).1 (hUY hcU)
  have hcD : c ∈ d.D := hFD (hXF (hYX hcY))
  have hcU' : c ∉ d.U := fun hc => huU (h.mem_U_of_crossed_eq_one d hK hD hu
    (d.eq_one_of_wb_conj_mem_U hcU hc))
  have hcW : c ∈ W := by
    set v := d.wb * u * d.wb⁻¹ with hvdef
    have hvV : v ∈ V := hY₂V (mem_sup_right ⟨u, hu, rfl⟩)
    have hct : c * t = t * c := mem_centralizer_singleton_iff.1
      (((d.image_le _).trans h.L_le_centralizer) hcY)
    refine ⟨hDD₁ hcD, v⁻¹, inv_mem hvV, 1, one_mem _, ?_⟩
    calc v⁻¹ * t * v⁻¹⁻¹ = v⁻¹ * t * v * t * t := by
          rw [inv_inv, mul_assoc _ t t, h.t_mul_t, mul_one]
      _ = c * t := by rw [hce]
      _ = t * c * 1 := by rw [hct, mul_one]
  have hNW : L ⊓ normalizer (d.U : Set G) ≤ normalizer ((W ⊓ d.D : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun n hn z hz => ?_
    obtain ⟨hzW, hzD⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨hz₁, x, hx, w, hw, hxz⟩ := hW.1 hzW
    have hnB := h.inf_normalizer_U_le_normalizer_yamadaC₁ d hn
    have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hn.1)
    have hnt' : n⁻¹ * t * n = t := by rw [mul_assoc, ← hnt, inv_mul_cancel_left]
    have hnD : n ∈ L ⊓ normalizer (d.D : Set G) := by rw [hND, ← hNU]; exact hn
    refine Subgroup.mem_inf.2 ⟨hW.2 ⟨hK₀ n hnB z hz₁, n * x * n⁻¹,
      Common.conj_mem_centralizerMod hnB hx, n * w * n⁻¹, hB n hnB w hw, ?_⟩,
      (mem_normalizer_iff.1 hnD.2 z).1 hzD⟩
    calc n * x * n⁻¹ * t * (n * x * n⁻¹)⁻¹ = n * x * (n⁻¹ * t * n) * x⁻¹ * n⁻¹ := by group
      _ = n * (x * t * x⁻¹) * n⁻¹ := by rw [hnt']; group
      _ = n * t * n⁻¹ * (n * z * n⁻¹) * (n * w * n⁻¹) := by rw [hxz]; group
      _ = t * (n * z * n⁻¹) * (n * w * n⁻¹) := by rw [hnt, mul_inv_cancel_right]
  have hUW : d.U ≤ W ⊓ d.D := le_inf (fun z hz => hW.2 ⟨hU₁D₁ (hUU₁ hz), 1, one_mem _, z⁻¹,
    inv_mem (hUU₁ hz), by group⟩) (hUY.trans (hYX.trans (hXF.trans hFD)))
  rcases (d.yamada_3_16_1_G (by omega) hUW inf_le_right).1 hNW with e | e
  · exact absurd (e ▸ Subgroup.mem_inf.2 ⟨hcW, hcD⟩ : c ∈ d.U) hcU'
  · have hδW : δ ∈ W := by
      have : δ ∈ W ⊓ d.D := by rw [e]; exact hδ
      exact this.1
    obtain ⟨-, x, hx, w, hw, hxδ⟩ := hW.1 hδW
    exact ⟨x, (Common.mem_centralizerMod.1 hx).1, (Common.mem_centralizerMod.1 hx).2, w, hw, hxδ⟩

theorem conj_t_ne_mul (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {u₀ g : G} (hu₀ : u₀ ∈ yamadaU₁ d t) (hu₀U : u₀ ∉ d.U) :
    g * t * g⁻¹ ≠ t * u₀ := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  intro hg
  obtain ⟨δ, hδ, hδ2⟩ : ∃ δ ∈ d.D, δ * δ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 := (d.yamada_3_12_mho (by omega)).1
    have h2 : closure {z | ∃ g ∈ d.D, z = g ^ 2} = ⊥ := by
      rw [eq_bot_iff, closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, mem_bot, sq]
      exact hcon g hg
    have h3 := d.cards.1
    rw [← h1, h2, card_bot] at h3
    omega
  obtain ⟨x, hx, -, u, hu, hxt⟩ := h.exists_conj_t_eq_mul_of_mem_D d hK hD hδ
  have hxU₁ := (h.normalizer_yamadaC₁_le d hK hD).2 ((h.normalizer_yamadaC₁_le d hK hD).1 hx)
  have hv : x⁻¹ * u⁻¹ * x ∈ yamadaU₁ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hxU₁) u⁻¹).1 (inv_mem hu)
    rwa [inv_inv] at this
  obtain ⟨g', hg'⟩ := h.forall_conj_t_mul d hK hD hu₀ hu₀U hg hv
  have e : (x * g') * t * (x * g')⁻¹ = t * δ := by
    calc (x * g') * t * (x * g')⁻¹ = x * (g' * t * g'⁻¹) * x⁻¹ := by group
      _ = x * t * x⁻¹ * (x * (x⁻¹ * u⁻¹ * x) * x⁻¹) := by rw [hg']; group
      _ = t * δ := by rw [hxt]; group
  have hδt : δ * t = t * δ := mem_centralizer_singleton_iff.1
    (((d.image_le _).trans h.L_le_centralizer) hδ)
  have h1 : (t * δ) * (t * δ) = 1 := by
    rw [← e]
    calc x * g' * t * (x * g')⁻¹ * (x * g' * t * (x * g')⁻¹) =
        x * g' * (t * t) * (x * g')⁻¹ := by group
      _ = 1 := by rw [h.t_mul_t, mul_one, mul_inv_cancel]
  have h2 : (t * δ) * (t * δ) = δ * δ := by
    calc t * δ * (t * δ) = t * (δ * t) * δ := by group
      _ = t * (t * δ) * δ := by rw [hδt]
      _ = δ * δ := by rw [← mul_assoc, h.t_mul_t, one_mul]
  exact hδ2 (h2 ▸ h1)

theorem t_mem_normalizer_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : t ∈ normalizer (yamadaU₁ d t : Set G) ∧ t ∉ yamadaU₁ d t :=
  ⟨h.yamadaR₂_le_normalizer_yamadaU₁ d hK hD
    (mem_sup_left (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t)))),
    fun ht => h.t_not_mem_yamadaD₁ d hK ((hD.spec).1 ht)⟩

theorem mem_yamadaU₁_sup_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} :
    x ∈ yamadaU₁ d t ⊔ zpowers t ↔ x ∈ yamadaU₁ d t ∨ ∃ u ∈ yamadaU₁ d t, x = u * t := by
  constructor
  · intro hx
    obtain ⟨u, hu, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer
      ((zpowers_le).2 (h.t_mem_normalizer_yamadaU₁ d hK hD).1) x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with e | e
    · rw [e, mul_one]
      exact Or.inl hu
    · exact Or.inr ⟨u, hu, by rw [e]⟩
  · rintro (hx | ⟨u, hu, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))

theorem card_yamadaU₁_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    Nat.card (yamadaU₁ d t ⊔ zpowers t : Subgroup G) = 2 * Nat.card (yamadaU₁ d t) := by
  obtain ⟨htN, htU₁⟩ := h.t_mem_normalizer_yamadaU₁ d hK hD
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaU₁ d t) (B := zpowers t)
    ((zpowers_le).2 htN)
  have h2 : yamadaU₁ d t ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx₂
    rcases h.zpow_eq_one_or_eq k with e | e
    · rw [e]
      exact one_mem _
    · rw [e] at hx₁
      exact absurd hx₁ htU₁
  rw [h2, card_bot, mul_one, h.card_zpowers_t, mul_comm] at h1
  exact h1

theorem card_le_two_mul_card_inf_yamadaU₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {X : Subgroup G}
    (hX : X ≤ yamadaU₁ d t ⊔ zpowers t) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ yamadaU₁ d t : Subgroup G) := by
  obtain ⟨htN, -⟩ := h.t_mem_normalizer_yamadaU₁ d hK hD
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaU₁ d t) (B := X)
    (hX.trans (sup_le le_normalizer ((zpowers_le).2 htN)))
  have h2 : Nat.card (yamadaU₁ d t ⊔ X : Subgroup G) ≤ 2 * Nat.card (yamadaU₁ d t) := by
    rw [← h.card_yamadaU₁_sup d hK hD]
    exact Subgroup.card_le_of_le (sup_le le_sup_left hX)
  have hpos : 0 < Nat.card (yamadaU₁ d t) := Nat.card_pos
  rw [inf_comm] at h1
  have h3 : Nat.card (yamadaU₁ d t) * Nat.card X ≤
      Nat.card (yamadaU₁ d t) * (2 * Nat.card (X ⊓ yamadaU₁ d t : Subgroup G)) := by
    rw [← h1]
    calc Nat.card (yamadaU₁ d t ⊔ X : Subgroup G) * Nat.card (X ⊓ yamadaU₁ d t : Subgroup G) ≤
        2 * Nat.card (yamadaU₁ d t) * Nat.card (X ⊓ yamadaU₁ d t : Subgroup G) :=
          Nat.mul_le_mul_right _ h2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h3 hpos

theorem le_yamadaU₁_of_mul_comm (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {X : Subgroup G} (hX : X ≤ yamadaU₁ d t ⊔ zpowers t)
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hXc : Nat.card (yamadaU₁ d t) ≤ Nat.card X) : X ≤ yamadaU₁ d t := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  by_contra hn
  obtain ⟨x, hxX, hxU₁⟩ := Set.not_subset.1 hn
  obtain hx | ⟨u, hu, rfl⟩ := (h.mem_yamadaU₁_sup_iff d hK hD).1 (hX hxX)
  · exact hxU₁ hx
  have hXU : X ⊓ yamadaU₁ d t ≤ d.U := by
    intro y hy
    obtain ⟨hyX, hyU₁⟩ := Subgroup.mem_inf.1 hy
    rw [← hD.inf_centralizer]
    refine ⟨hyU₁, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hXab y hyX _ hxX
    have h2 : y * u = u * y := hD.mul_comm hyU₁ hu
    have h3 : u * (y * t) = u * (t * y) := by
      calc u * (y * t) = y * (u * t) := by rw [← mul_assoc, ← h2, mul_assoc]
        _ = u * t * y := h1
        _ = u * (t * y) := by rw [mul_assoc]
    exact mul_left_cancel h3
  have h1 := h.card_le_two_mul_card_inf_yamadaU₁ d hK hD hX
  have h2 := Subgroup.card_le_of_le hXU
  rw [d.cards.1] at h2
  rw [(hD.yamada_5_10_1).2.2] at hXc
  have : 2 * Nat.card K < Nat.card K ^ 2 := by
    rw [sq]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  omega

theorem normalizer_yamadaU₁_sup_le (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    normalizer ((yamadaU₁ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaU₁ d t : Set G) := by
  intro g hg
  have hle : (yamadaU₁ d t).map (MulAut.conj g).toMonoidHom ≤ yamadaU₁ d t := by
    refine h.le_yamadaU₁_of_mul_comm d hK hD ?_ ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact (mem_normalizer_iff.1 hg u).1 (mem_sup_left hu)
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ by group,
        hD.mul_comm hu hv]
      group
    · rw [card_map_of_injective (MulAut.conj g).injective]
  exact mem_normalizer_of_conj_mem fun u hu => hle ⟨u, hu, rfl⟩

theorem yamada_5_17_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    normalizer ((yamadaU₁ d t ⊔ zpowers t : Subgroup G) : Set G) =
      normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) := by
  obtain ⟨htN, htU₁⟩ := h.t_mem_normalizer_yamadaU₁ d hK hD
  obtain ⟨-, hUU₁, -⟩ := hD.spec
  have htt := h.t_mul_t
  apply le_antisymm
  · intro g hg
    have hgU₁ := h.normalizer_yamadaU₁_sup_le d hK hD hg
    have hgt : g * t * g⁻¹ ∈ yamadaU₁ d t ⊔ zpowers t :=
      (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
    obtain ⟨u', hu', hgu⟩ : ∃ u' ∈ d.U, g * t * g⁻¹ = t * u' := by
      rcases (h.mem_yamadaU₁_sup_iff d hK hD).1 hgt with h1 | ⟨u, hu, e⟩
      · exfalso
        refine htU₁ ?_
        have := (mem_normalizer_iff.1 (inv_mem hgU₁) _).1 h1
        rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
      · have hu'' : t * u * t ∈ yamadaU₁ d t := by
          have := (mem_normalizer_iff.1 htN u).1 hu
          rwa [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htt] at this
        have e' : g * t * g⁻¹ = t * (t * u * t) := by
          rw [e, ← mul_assoc, ← mul_assoc, htt, one_mul]
        by_cases hU : t * u * t ∈ d.U
        · exact ⟨_, hU, e'⟩
        · exact absurd e' (h.conj_t_ne_mul d hK hD hu'' hU)
    have hu'U₁ := hUU₁ hu'
    have hgU : g ∈ normalizer (d.U : Set G) := by
      refine mem_normalizer_of_conj_mem fun w hw => ?_
      have hz : g * w * g⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 hgU₁ w).1 (hUU₁ hw)
      have hwt : w * t = t * w := mem_centralizer_singleton_iff.1
        (((d.image_le _).trans h.L_le_centralizer) hw)
      have h1 : g * w * g⁻¹ * (t * u') = t * u' * (g * w * g⁻¹) := by
        rw [← hgu]
        calc g * w * g⁻¹ * (g * t * g⁻¹) = g * (w * t) * g⁻¹ := by group
          _ = g * (t * w) * g⁻¹ := by rw [hwt]
          _ = g * t * g⁻¹ * (g * w * g⁻¹) := by group
      have h2 : g * w * g⁻¹ * u' = u' * (g * w * g⁻¹) := hD.mul_comm hz hu'U₁
      rw [← hD.inf_centralizer]
      refine ⟨hz, mem_centralizer_singleton_iff.2 ?_⟩
      have h3 : g * w * g⁻¹ * t * u' = t * (g * w * g⁻¹) * u' := by
        calc g * w * g⁻¹ * t * u' = g * w * g⁻¹ * (t * u') := by rw [mul_assoc]
          _ = t * u' * (g * w * g⁻¹) := h1
          _ = t * (u' * (g * w * g⁻¹)) := by rw [mul_assoc]
          _ = t * (g * w * g⁻¹ * u') := by rw [h2]
          _ = t * (g * w * g⁻¹) * u' := by rw [← mul_assoc]
      exact mul_right_cancel h3
    have htU : zpowers t ≤ normalizer (d.U : Set G) := (zpowers_le).2
      (mem_normalizer_of_conj_mem fun y hy => by
        rw [← mem_centralizer_singleton_iff.1 (((d.image_le _).trans h.L_le_centralizer) hy),
          mul_inv_cancel_right]
        exact hy)
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨w, hw, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htU x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rw [show g * (w * t ^ k) * g⁻¹ = g * w * g⁻¹ * (g * t * g⁻¹) ^ k by
      rw [conj_zpow]; group, hgu]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hgU w).1 hw))
      (zpow_mem (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hu')) k)
  · intro g hg
    have hgU₁ := (h.normalizer_yamadaC₁_le d hK hD).2 ((h.normalizer_yamadaC₁_le d hK hD).1
      (le_normalizer_yamadaC₁ d t hg))
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨u, hu, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htN) x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    have hgt : g * t * g⁻¹ ∈ yamadaU₁ d t ⊔ zpowers t :=
      sup_le_sup_right hUU₁ _ ((mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t)))
    rw [show g * (u * t ^ k) * g⁻¹ = g * u * g⁻¹ * (g * t * g⁻¹) ^ k by
      rw [conj_zpow]; group]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hgU₁ u).1 hu)) (zpow_mem hgt k)

theorem card_leviC (_h : Setup G L f t) (d : G2Data L K) (h8 : 8 ≤ Nat.card K) :
    Nat.card d.leviC = Nat.card K * (Nat.card K ^ 2 - 1) := by
  obtain ⟨-, -, -, ⟨e⟩⟩ := d.yamada_3_10_J₁_G h8
  rw [← Nat.card_congr e.toEquiv]
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem centralizer_J₁_inf_le (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) :
    centralizer (d.J₁ : Set G) ⊓ centralizer ({t} : Set G) ≤ (d.leviC ⊔ d.J₁) ⊔ zpowers t := by
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  have h322 := (d.yamada_3_22_G hK (three_le_of_card_eq hK h8)).1
    (Subgroup.mem_inf.2 ⟨h.centralizer_le_normalizer hx₂, hx₁⟩)
  have hCN : centralizer (L : Set G) ≤
      normalizer ((L ⊓ centralizer (d.J₁ : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun c hc y hy => by
      rw [← mem_centralizer_iff.1 hc y hy.1, mul_inv_cancel_right]
      exact hy
  obtain ⟨a, ha, c, hc, rfl⟩ := Common.exists_mul_of_le_normalizer hCN x h322
  have hcT : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hc, ?_⟩
    rw [show c = a⁻¹ * (a * c) by group]
    exact mul_mem (inv_mem (h.L_le_centralizer ha.1)) hx₂
  rw [h.centralizer_L_inf] at hcT
  rw [(d.yamada_3_10_J₁_G h8).1] at ha
  exact mul_mem (mem_sup_left ha) (mem_sup_right hcT)

theorem card_le_of_isPGroup_of_le_centralizer_J₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPJ : P ≤ centralizer (d.J₁ : Set G)) (hPt : P ≤ centralizer ({t} : Set G)) :
    Nat.card P ≤ 2 * Nat.card K := by
  have hPM := (le_inf hPJ hPt).trans (h.centralizer_J₁_inf_le d hK h8)
  obtain ⟨-, hCJ, hCJ₁, -⟩ := d.yamada_3_10_J₁_G h8
  have hJN : d.J₁ ≤ normalizer (d.leviC : Set G) := le_normalizer_of_conj_mem fun j hj y hy => by
    rw [mem_centralizer_iff.1 (hCJ hy) j hj, mul_inv_cancel_right]
    exact hy
  have h1 := Common.card_sup_mul_card_inf_eq (A := d.leviC) (B := d.J₁) hJN
  rw [hCJ₁, card_bot, mul_one, h.card_leviC d h8, d.card_J₁] at h1
  have hML : d.leviC ⊔ d.J₁ ≤ L := sup_le (d.image_le _) (d.image_le _)
  have htN : zpowers t ≤ normalizer ((d.leviC ⊔ d.J₁ : Subgroup G) : Set G) :=
    (zpowers_le).2 (le_normalizer_of_conj_mem (S := zpowers t) (fun c hc y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      have hyt : y * t ^ k = t ^ k * y :=
        (Commute.zpow_right (mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hML hy))) k)
      rw [← hyt, mul_inv_cancel_right]
      exact hy) (mem_zpowers t))
  have h2 := Common.card_sup_mul_card_inf_eq (A := d.leviC ⊔ d.J₁) (B := zpowers t) htN
  rw [inf_comm, h.zpowers_inf_L hML, card_bot, mul_one, h.card_zpowers_t, h1] at h2
  have h3 : Nat.card P ∣ Nat.card ((d.leviC ⊔ d.J₁) ⊔ zpowers t : Subgroup G) :=
    Subgroup.card_dvd_of_le hPM
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  rw [h2, hk, hK] at h3
  have hodd : Odd (((2 ^ f) ^ 2 - 1) * (2 ^ f - 1)) := by
    have hf : f ≠ 0 := by have := three_le_of_card_eq hK h8; omega
    refine Nat.odd_mul.2 ⟨?_, odd_two_pow_sub_one (by omega)⟩
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  have h4 : 2 ^ k ∣ 2 * 2 ^ f := by
    have h5 : 2 ^ k ∣ (2 * 2 ^ f) * (((2 ^ f) ^ 2 - 1) * (2 ^ f - 1)) := by
      rw [show 2 * 2 ^ f * (((2 ^ f) ^ 2 - 1) * (2 ^ f - 1)) =
        2 ^ f * ((2 ^ f) ^ 2 - 1) * (2 ^ f - 1) * 2 by ring]
      exact h3
    exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)).dvd_of_dvd_mul_right h5
  rw [hk, hK]
  exact Nat.le_of_dvd (by positivity) h4

theorem eq_yamadaU₁_sup_of_isPGroup (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPJ : P ≤ centralizer (d.J₁ : Set G)) (hTP : yamadaU₁ d t ⊔ zpowers t ≤ P) :
    P = yamadaU₁ d t ⊔ zpowers t := by
  have hD := h.doublingFacts_of_eight d hK h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := yamadaU₁ d t ⊔ zpowers t with hTdef
  by_contra hne
  obtain ⟨x, hxP, hxT, hxN⟩ :=
    exists_mem_normalizer_not_mem_of_isPGroup hP (lt_of_le_of_ne hTP (Ne.symm hne))
  obtain ⟨-, hUU₁, -⟩ := h.yamadaU₁_spec d h8
  set P' := P ⊓ normalizer (T : Set G) with hP'def
  have hTP' : T ≤ P' := le_inf hTP le_normalizer
  have hP'N : P' ≤ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [← h.yamada_5_17_1 d hK hD]
    exact inf_le_right
  have hP'U₁ : P' ≤ normalizer (yamadaU₁ d t : Set G) :=
    inf_le_right.trans (h.normalizer_yamadaU₁_sup_le d hK hD)
  set C' := P' ⊓ centralizer ({t} : Set G) with hC'def
  have hU₁T : yamadaU₁ d t ≤ T := le_sup_left
  have hdec : P' ≤ yamadaU₁ d t ⊔ C' := by
    intro y hy
    have hw := (h.cosetData_tU d hK).crossed_mem y⁻¹ (hP'N (inv_mem hy))
    rw [inv_inv] at hw
    obtain ⟨z, hz, hzw⟩ := h.exists_mem_yamadaU₁_crossed d hK h8 hw
    have htt := h.t_mul_t
    have hzy : z * y ∈ C' := by
      refine ⟨mul_mem (hTP' (hU₁T hz)) hy, mem_centralizer_singleton_iff.2 ?_⟩
      have e1 : y * t * y⁻¹ = z⁻¹ * t * z := by
        have e2 : z⁻¹ * t * z * t = y * t * y⁻¹ * t := hzw
        exact (mul_right_cancel e2).symm
      calc z * y * t = z * (y * t * y⁻¹) * y := by group
        _ = z * (z⁻¹ * t * z) * y := by rw [e1]
        _ = t * (z * y) := by group
    rw [show y = z⁻¹ * (z * y) by group]
    exact mul_mem (mem_sup_left (inv_mem hz)) (mem_sup_right hzy)
  have hC'N : C' ≤ normalizer (yamadaU₁ d t : Set G) := inf_le_left.trans hP'U₁
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaU₁ d t) (B := C') hC'N
  have hinf : yamadaU₁ d t ⊓ C' = d.U := by
    refine le_antisymm ?_ (le_inf hUU₁ (le_inf (hUU₁.trans (hU₁T.trans hTP'))
      ((d.image_le _).trans h.L_le_centralizer)))
    rw [← h.yamadaU₁_inf_centralizer d hK h8]
    exact inf_le_inf_left _ inf_le_right
  rw [hinf, d.cards.1, (h.yamada_5_10_1 d hK h8).2.2] at h1
  have hC'card : Nat.card C' ≤ 2 * Nat.card K :=
    h.card_le_of_isPGroup_of_le_centralizer_J₁ d hK h8 (hP.to_le (inf_le_left.trans inf_le_left))
      (inf_le_left.trans (inf_le_left.trans hPJ)) inf_le_right
  have hP'card : Nat.card P' ≤ Nat.card T := by
    rw [hTdef, h.card_yamadaU₁_sup d hK hD, (h.yamada_5_10_1 d hK h8).2.2]
    have h2 : Nat.card P' ≤ Nat.card (yamadaU₁ d t ⊔ C' : Subgroup G) := Subgroup.card_le_of_le hdec
    have hq : 0 < Nat.card K := Nat.card_pos
    have h3 : Nat.card (yamadaU₁ d t ⊔ C' : Subgroup G) * Nat.card K ≤
        2 * Nat.card K ^ 2 * Nat.card K := by
      rw [h1]
      calc Nat.card K ^ 2 * Nat.card C' ≤ Nat.card K ^ 2 * (2 * Nat.card K) :=
            Nat.mul_le_mul_left _ hC'card
        _ = 2 * Nat.card K ^ 2 * Nat.card K := by ring
    exact h2.trans (Nat.le_of_mul_le_mul_right h3 hq)
  have heq : P' = T := (Subgroup.eq_of_le_of_card_ge hTP' hP'card).symm
  exact hxT (heq ▸ (⟨hxP, hxN⟩ : x ∈ P'))

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
