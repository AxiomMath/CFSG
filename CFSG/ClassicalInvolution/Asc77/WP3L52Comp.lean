module

public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.LocalCores CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

namespace Lemma52Proof

section Components

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem conjSub_eq_of_centralizes {L : Subgroup Q} {d : Q} (h : ∀ x ∈ L, d * x = x * d) :
    conjSub d L = L := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have h1 : d * (d⁻¹ * y * d) = (d⁻¹ * y * d) * d := h _ hy
    have h2 : y = d⁻¹ * y * d := by
      calc y = d * (d⁻¹ * y * d) * d⁻¹ := by group
        _ = (d⁻¹ * y * d) * d * d⁻¹ := by rw [h1]
        _ = d⁻¹ * y * d := by group
    rw [h2]
    exact hy
  · intro hy
    have h1 : d * y = y * d := h y hy
    have e : d⁻¹ * y * d = y := by
      calc d⁻¹ * y * d = d⁻¹ * (y * d) := by group
        _ = d⁻¹ * (d * y) := by rw [h1]
        _ = y := by group
    rwa [e]

theorem normalizes_component_of_mem_involutionOddCore {L : Subgroup Q} (hL : IsComponent L)
    {t d : Q} (ht : t * t = 1) (hd : d ∈ involutionOddCore t) : conjSub d L = L := by
  by_cases htL : conjSub t L = L
  · exact conjSub_eq_of_mem_involutionOddCore hL ht htL hd
  · exact conjSub_eq_of_centralizes (commute_of_moved hL ht htL hd)

theorem centralizes_of_centralizes_involution {L : Subgroup Q} (hL : IsComponent L) {t d : Q}
    (hd : d ∈ involutionOddCore t) (ht : ∀ x ∈ L, t * x = x * t) : ∀ x ∈ L, d * x = x * d := by
  have hLC : L ≤ Subgroup.centralizer ({t} : Set Q) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (ht x hx).symm
  exact commute_of_isComponent_centralizer hd hLC (component_overgroup hL hLC)

theorem exists_component_moved (hO : CFSG.pPrimeCore 2 Q = ⊥) {t : Q} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) {D : Subgroup Q} (hD : D ≤ involutionOddCore t) (hD0 : D ≠ ⊥) :
    ∃ K : Subgroup Q, IsComponent K ∧ ∃ x ∈ D, ∃ y ∈ K, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  apply hD0
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hodd : Odd (Nat.card D) :=
    (odd_card_oddCoreIn (Subgroup.centralizer ({t} : Set Q))).of_dvd_nat
      (Subgroup.card_dvd_of_le hD)
  have hQ : D ≤ Subgroup.centralizer (CFSG.pCore 2 Q : Set Q) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := commute_pCore_of_mem_involutionOddCore hord (hD hd) q hq
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  refine eq_bot_of_centralizes_pCore_of_centralizes_components hO hodd hQ ?_
  intro K hK x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hcon K hK x hx y hy).symm

omit [Finite Q] in
theorem commutator_centralizes_of_centralizes {L : Subgroup Q} {x e : Q} (hx : conjSub x L = L)
    (he : ∀ k ∈ L, e * k = k * e) : ∀ k ∈ L, ⁅x, e⁆ * k = k * ⁅x, e⁆ := by
  intro k hk
  have hk' : x⁻¹ * k * x ∈ L := by
    have h1 : k ∈ conjSub x L := by rw [hx]; exact hk
    exact mem_conjSub_iff.mp h1
  have h2 : e * (x⁻¹ * k * x) = (x⁻¹ * k * x) * e := he _ hk'
  have h3 : e * k = k * e := he k hk
  have e3 : e⁻¹ * k * e = k := by
    calc e⁻¹ * k * e = e⁻¹ * (k * e) := by group
      _ = e⁻¹ * (e * k) := by rw [h3]
      _ = k := by group
  have h4 : e * (x⁻¹ * k * x) * e⁻¹ = x⁻¹ * k * x := by rw [h2]; group
  have key : ⁅x, e⁆ * k * ⁅x, e⁆⁻¹ = k := by
    calc ⁅x, e⁆ * k * ⁅x, e⁆⁻¹
        = x * (e * (x⁻¹ * (e⁻¹ * k * e) * x) * e⁻¹) * x⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = x * (e * (x⁻¹ * k * x) * e⁻¹) * x⁻¹ := by rw [e3]
      _ = x * (x⁻¹ * k * x) * x⁻¹ := by rw [h4]
      _ = k := by group
  calc ⁅x, e⁆ * k = (⁅x, e⁆ * k * ⁅x, e⁆⁻¹) * ⁅x, e⁆ := by group
    _ = k * ⁅x, e⁆ := by rw [key]

end Components

section Induced

variable {Q : Type} [Group Q]

theorem toInducedAutOn_mem_inducedImage (L B : Subgroup Q) {b : Q} (hbB : b ∈ B)
    (hbN : b ∈ Subgroup.normalizer (L : Set Q)) :
    toInducedAutOn L ⟨b, hbN⟩ ∈ inducedImage L B :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbB)

theorem exists_of_mem_inducedImage {L B : Subgroup Q} {z : ↥(inducedAutOn L)}
    (hz : z ∈ inducedImage L B) :
    ∃ (b : Q) (hbN : b ∈ Subgroup.normalizer (L : Set Q)), b ∈ B ∧
      toInducedAutOn L ⟨b, hbN⟩ = z := by
  obtain ⟨⟨b, hbN⟩, hb, rfl⟩ := Subgroup.mem_map.mp hz
  exact ⟨b, hbN, Subgroup.mem_subgroupOf.mp hb, rfl⟩

theorem commute_of_toInducedAutOn_eq_one (L : Subgroup Q) {x : Q}
    (hx : x ∈ Subgroup.normalizer (L : Set Q)) (h : toInducedAutOn L ⟨x, hx⟩ = 1) :
    ∀ y ∈ L, x * y = y * x := by
  intro y hy
  have h1 : conjOnNormalizer L ⟨x, hx⟩ = 1 := congrArg Subtype.val h
  have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨y, hy⟩ : ↥L) : Q)) h1
  have h3 : x * y * x⁻¹ = y := h2
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem toInducedAutOn_eq_one_of_commute (L : Subgroup Q) {x : Q}
    (hx : x ∈ Subgroup.normalizer (L : Set Q)) (h : ∀ y ∈ L, x * y = y * x) :
    toInducedAutOn L ⟨x, hx⟩ = 1 := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  show x * (y : Q) * x⁻¹ = y
  rw [h y y.2]
  group

theorem toInducedAutOn_ne_one_of_moved (L : Subgroup Q) {x : Q}
    (hx : x ∈ Subgroup.normalizer (L : Set Q)) {y : Q} (hy : y ∈ L) (hxy : x * y ≠ y * x) :
    toInducedAutOn L ⟨x, hx⟩ ≠ 1 :=
  fun h => hxy (commute_of_toInducedAutOn_eq_one L hx h y hy)

end Induced

section Image

variable {Q : Type} [Group Q] [Finite Q]

theorem toInducedAutOn_mem_involutionOddCore (L : Subgroup Q) {t d : Q} (ht : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (L : Set Q)) (hdN : d ∈ Subgroup.normalizer (L : Set Q))
    (hd : d ∈ involutionOddCore t) :
    toInducedAutOn L ⟨d, hdN⟩ ∈ involutionOddCore (toInducedAutOn L ⟨t, htN⟩) := by
  set m : ↥(Subgroup.normalizer (L : Set Q)) := ⟨t, htN⟩ with hm
  have h1 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (L : Set Q))) ∈ involutionOddCore m :=
    subgroupOf_involutionOddCore_le m (Subgroup.mem_subgroupOf.mpr hd)
  have h2 : IsPGroup 2 (Subgroup.zpowers m) :=
    CFSG.ClassicalInvolution.Balance.isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext ht)
  exact map_involutionOddCore_le (toInducedAutOn L) (MonoidHom.rangeRestrict_surjective _) h2
    ⟨_, h1, rfl⟩

end Image

end Lemma52Proof

section Alpha

variable {H : Type} [Group H]

theorem commutator_le_alphaOf (A : Subgroup H) {a : H} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ⁅involutionOddCore a, A⁆ ≤ alphaOf A := by
  refine le_trans ?_ le_sup_left
  refine le_trans ?_ (le_iSup₂ (f := fun a (_ : a ∈ A) =>
    ⨆ (_ : a ≠ 1), ⁅oddCoreOf (Subgroup.centralizer ({a} : Set H)), A⁆) a ha)
  exact le_iSup (fun _ : a ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({a} : Set H)), A⁆) ha1

theorem iInf_le_alphaOf (A : Subgroup H) :
    (⨅ a ∈ A, ⨅ (_ : a ≠ 1), involutionOddCore a) ≤ alphaOf A :=
  le_sup_right

theorem alphaOf_eq_bot_iff (A : Subgroup H) :
    alphaOf A = ⊥ ↔ (∀ a ∈ A, a ≠ 1 → ⁅involutionOddCore a, A⁆ = ⊥) ∧
      (⨅ a ∈ A, ⨅ (_ : a ≠ 1), involutionOddCore a) = ⊥ := by
  constructor
  · intro h
    refine ⟨fun a ha ha1 => ?_, ?_⟩
    · exact le_bot_iff.mp (h ▸ commutator_le_alphaOf A ha ha1)
    · exact le_bot_iff.mp (h ▸ iInf_le_alphaOf A)
  · rintro ⟨h1, h2⟩
    refine le_bot_iff.mp (sup_le ?_ h2.le)
    refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    exact (h1 a ha ha1).le

theorem alphaOf_le_alphaCore (F : Subgroup H) : alphaOf F ≤ Bootstrap.alphaCore F := by
  refine le_trans (sup_le ?_ le_sup_right) (le_normalClosureIn (Bootstrap.uCore F)
    (⁅Bootstrap.uCore F, F⁆ ⊔ deltaCore F))
  refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
  exact (Subgroup.commutator_mono (Bootstrap.involutionOddCore_le_uCore ha ha1) le_rfl).trans
    le_sup_left

theorem alphaOf_eq_bot_of_alphaCore_eq_bot {F : Subgroup H} (h : Bootstrap.alphaCore F = ⊥) :
    alphaOf F = ⊥ :=
  le_bot_iff.mp ((alphaOf_le_alphaCore F).trans h.le)

end Alpha

end CFSG.ClassicalInvolution.Asc77
