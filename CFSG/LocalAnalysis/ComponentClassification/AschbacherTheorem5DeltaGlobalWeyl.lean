module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem weyl_mul_self {u₁ v₁ : G} (hu : u₁ * u₁ = 1) (hv : v₁ * v₁ = 1) :
    (u₁ * v₁ * u₁) * (u₁ * v₁ * u₁) = 1 := by
  calc (u₁ * v₁ * u₁) * (u₁ * v₁ * u₁) = u₁ * v₁ * (u₁ * u₁) * v₁ * u₁ := by group
    _ = 1 := by rw [hu, mul_one, mul_assoc u₁ v₁ v₁, hv, mul_one, hu]

omit [Finite G] in
theorem weyl_conj_aux {U V : Subgroup G} {u₁ v₁ : G} (hv : v₁ * v₁ = 1)
    (hu₁V : ∀ y ∈ V, u₁ * y = y * u₁) (hspread : rightConjugate U u₁ = rightConjugate V v₁)
    {x : G} (hx : x ∈ U) :
    v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁ ∈ V ∧
      (u₁ * v₁ * u₁)⁻¹ * x * (u₁ * v₁ * u₁) = v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁ := by
  have hv' : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv
  have hb : v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁ ∈ V := by
    have h1 : u₁⁻¹ * x * u₁ ∈ rightConjugate U u₁ := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hx
    rw [hspread, mem_rightConjugate_iff, hv'] at h1
    rw [hv']
    exact h1
  refine ⟨hb, ?_⟩
  have hc := hu₁V _ hb
  calc (u₁ * v₁ * u₁)⁻¹ * x * (u₁ * v₁ * u₁)
      = u₁⁻¹ * (v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁) * u₁ := by group
    _ = u₁⁻¹ * (u₁ * (v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁)) := by rw [mul_assoc, ← hc]
    _ = v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁ := by group

omit [Finite G] in
theorem weyl_conj_mem_V {U V : Subgroup G} {u₁ v₁ : G} (hv : v₁ * v₁ = 1)
    (hu₁V : ∀ y ∈ V, u₁ * y = y * u₁) (hspread : rightConjugate U u₁ = rightConjugate V v₁)
    {x : G} (hx : x ∈ U) : (u₁ * v₁ * u₁)⁻¹ * x * (u₁ * v₁ * u₁) ∈ V := by
  obtain ⟨h1, h2⟩ := weyl_conj_aux hv hu₁V hspread hx
  rw [h2]
  exact h1

omit [Finite G] in
theorem weyl_conj_mem_U {U V : Subgroup G} {u₁ v₁ : G} (hu : u₁ * u₁ = 1)
    (hu₁V : ∀ y ∈ V, u₁ * y = y * u₁) (hspread : rightConjugate U u₁ = rightConjugate V v₁)
    {y : G} (hy : y ∈ V) : (u₁ * v₁ * u₁)⁻¹ * y * (u₁ * v₁ * u₁) ∈ U := by
  have hu' : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hu
  have hb : u₁ * (v₁⁻¹ * y * v₁) * u₁⁻¹ ∈ U := by
    have h1 : v₁⁻¹ * y * v₁ ∈ rightConjugate V v₁ := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hy
    rw [← hspread, mem_rightConjugate_iff] at h1
    exact h1
  have hc := hu₁V y hy
  have e : (u₁ * v₁ * u₁)⁻¹ * y * (u₁ * v₁ * u₁) = u₁ * (v₁⁻¹ * y * v₁) * u₁⁻¹ := by
    calc (u₁ * v₁ * u₁)⁻¹ * y * (u₁ * v₁ * u₁)
        = u₁⁻¹ * v₁⁻¹ * (u₁⁻¹ * (y * u₁)) * v₁ * u₁ := by group
      _ = u₁⁻¹ * (v₁⁻¹ * y * v₁) * u₁ := by rw [← hc]; group
      _ = u₁ * (v₁⁻¹ * y * v₁) * u₁⁻¹ := by rw [hu']
  rw [e]
  exact hb

omit [Finite G] in
theorem weyl_conj_eq {U V : Subgroup G} {u₁ v₁ : G} (hv : v₁ * v₁ = 1)
    (hu₁V : ∀ y ∈ V, u₁ * y = y * u₁) (hv₁U : ∀ x ∈ U, v₁ * x = x * v₁)
    (hspread : rightConjugate U u₁ = rightConjugate V v₁)
    (hUq : ∀ x ∈ U, x⁻¹ * u₁⁻¹ * x * u₁ ∈ V) (hVq : ∀ y ∈ V, y⁻¹ * v₁⁻¹ * y * v₁ ∈ U)
    (hcomm : ∀ x ∈ U, ∀ y ∈ V, x * y = y * x) (hUV : U ⊓ V = ⊥) {x : G} (hx : x ∈ U) :
    (u₁ * v₁ * u₁)⁻¹ * x * (u₁ * v₁ * u₁) = x⁻¹ * u₁⁻¹ * x * u₁ := by
  obtain ⟨hb, e1⟩ := weyl_conj_aux hv hu₁V hspread hx
  set y₁ := x⁻¹ * u₁⁻¹ * x * u₁ with hy₁def
  have hy₁ : y₁ ∈ V := hUq x hx
  set x₁ := y₁⁻¹ * v₁⁻¹ * y₁ * v₁ with hx₁def
  have hx₁ : x₁ ∈ U := hVq y₁ hy₁
  have e2 : v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁ = x * x₁ * y₁ := by
    have hxv : v₁⁻¹ * x * v₁ = x := by
      calc v₁⁻¹ * x * v₁ = v₁⁻¹ * (v₁ * x) := by rw [mul_assoc, hv₁U x hx]
        _ = x := by group
    calc v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁ = v₁⁻¹ * (x * y₁) * v₁ := by rw [hy₁def]; group
      _ = (v₁⁻¹ * x * v₁) * (y₁ * x₁) := by rw [hx₁def]; group
      _ = x * (x₁ * y₁) := by rw [hxv, hcomm x₁ hx₁ y₁ hy₁]
      _ = x * x₁ * y₁ := by group
  have hxx : x * x₁ = 1 := by
    have hmem : x * x₁ ∈ U ⊓ V := by
      refine ⟨U.mul_mem hx hx₁, ?_⟩
      have : x * x₁ = (v₁⁻¹ * (u₁⁻¹ * x * u₁) * v₁) * y₁⁻¹ := by rw [e2]; group
      rw [this]
      exact V.mul_mem hb (V.inv_mem hy₁)
    rw [hUV, Subgroup.mem_bot] at hmem
    exact hmem
  rw [e1, e2, hxx, one_mul]

theorem exists_conj_eq_of_spread {U V U₁ : Subgroup G} (hU₁2 : ∀ u₁ ∈ U₁, u₁ * u₁ = 1)
    (hcomm : ∀ x ∈ U, ∀ y ∈ V, x * y = y * x) (hUV : U ⊓ V = ⊥)
    (hV : 1 < Nat.card V) (hcard : Nat.card V ≤ Nat.card U₁)
    (hreg : ∀ x ∈ U, x ≠ 1 → ∀ u₁ ∈ U₁, u₁⁻¹ * x * u₁ = x → u₁ = 1)
    (hUq : ∀ u₁ ∈ U₁, ∀ x ∈ U, x⁻¹ * u₁⁻¹ * x * u₁ ∈ V)
    (hU₁V : ∀ u₁ ∈ U₁, ∀ y ∈ V, u₁ * y = y * u₁)
    (hpartner : ∀ u₁ ∈ U₁, u₁ ≠ 1 → ∃ v₁ : G, v₁ * v₁ = 1 ∧ (∀ x ∈ U, v₁ * x = x * v₁) ∧
      (∀ y ∈ V, y⁻¹ * v₁⁻¹ * y * v₁ ∈ U) ∧ rightConjugate U u₁ = rightConjugate V v₁)
    {x₀ : G} (hx₀ : x₀ ∈ U) (hx₀1 : x₀ ≠ 1) {x' : G} (hx' : x' ∈ U) (hx'1 : x' ≠ 1) :
    ∃ h : G, (∀ x ∈ U, h⁻¹ * x * h ∈ U) ∧ (∀ y ∈ V, h⁻¹ * y * h ∈ V) ∧
      h⁻¹ * x₀ * h = x' := by
  let f : U₁ → V := fun u => ⟨x₀⁻¹ * (u : G)⁻¹ * x₀ * u, hUq u u.2 x₀ hx₀⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : x₀⁻¹ * (a : G)⁻¹ * x₀ * a = x₀⁻¹ * (b : G)⁻¹ * x₀ * b := congrArg Subtype.val hab
    have h2 : ((a : G) * (b : G)⁻¹)⁻¹ * x₀ * ((a : G) * (b : G)⁻¹) = x₀ := by
      have h3 : (a : G)⁻¹ * x₀ * a = (b : G)⁻¹ * x₀ * b := by
        have := congrArg (fun t => x₀ * t) h1
        simpa [mul_assoc] using this
      calc ((a : G) * (b : G)⁻¹)⁻¹ * x₀ * ((a : G) * (b : G)⁻¹)
          = (b : G) * ((a : G)⁻¹ * x₀ * a) * (b : G)⁻¹ := by group
        _ = (b : G) * ((b : G)⁻¹ * x₀ * b) * (b : G)⁻¹ := by rw [h3]
        _ = x₀ := by group
    have h4 := hreg x₀ hx₀ hx₀1 _ (U₁.mul_mem a.2 (U₁.inv_mem b.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h4)
  have hfsurj := (hfinj.bijective_of_nat_card_le hcard).2
  have hU₁1 : U₁ ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot U₁).mp (hV.trans_le hcard)
  obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU₁1
  have hu₀1' : u₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  obtain ⟨v₀, hv₀, -, -, hsp₀⟩ := hpartner u₀ hu₀ hu₀1'
  set w₀ := u₀ * v₀ * u₀ with hw₀def
  have hw₀ : w₀ * w₀ = 1 := weyl_mul_self (hU₁2 u₀ hu₀) hv₀
  have hw₀' : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀
  have hy' : w₀⁻¹ * x' * w₀ ∈ V := weyl_conj_mem_V hv₀ (hU₁V u₀ hu₀) hsp₀ hx'
  obtain ⟨⟨u₁, hu₁⟩, hfu₁⟩ := hfsurj ⟨w₀⁻¹ * x' * w₀, hy'⟩
  have hfu₁' : x₀⁻¹ * u₁⁻¹ * x₀ * u₁ = w₀⁻¹ * x' * w₀ := congrArg Subtype.val hfu₁
  have hu₁1 : u₁ ≠ 1 := by
    rintro rfl
    apply hx'1
    have h1 : w₀⁻¹ * x' * w₀ = 1 := by rw [← hfu₁']; group
    calc x' = w₀ * (w₀⁻¹ * x' * w₀) * w₀⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨v₁, hv₁, hv₁U, hv₁q, hsp₁⟩ := hpartner u₁ hu₁ hu₁1
  set w := u₁ * v₁ * u₁ with hwdef
  have hwx : w⁻¹ * x₀ * w = x₀⁻¹ * u₁⁻¹ * x₀ * u₁ :=
    weyl_conj_eq hv₁ (hU₁V u₁ hu₁) hv₁U hsp₁ (hUq u₁ hu₁) hv₁q hcomm hUV hx₀
  refine ⟨w * w₀, fun x hx => ?_, fun y hy => ?_, ?_⟩
  · have h1 : w⁻¹ * x * w ∈ V := weyl_conj_mem_V hv₁ (hU₁V u₁ hu₁) hsp₁ hx
    have h2 := weyl_conj_mem_U (hU₁2 u₀ hu₀) (hU₁V u₀ hu₀) hsp₀ h1
    have e : (w * w₀)⁻¹ * x * (w * w₀) = w₀⁻¹ * (w⁻¹ * x * w) * w₀ := by group
    rw [e]
    exact h2
  · have h1 : w⁻¹ * y * w ∈ U := weyl_conj_mem_U (hU₁2 u₁ hu₁) (hU₁V u₁ hu₁) hsp₁ hy
    have h2 := weyl_conj_mem_V hv₀ (hU₁V u₀ hu₀) hsp₀ h1
    have e : (w * w₀)⁻¹ * y * (w * w₀) = w₀⁻¹ * (w⁻¹ * y * w) * w₀ := by group
    rw [e]
    exact h2
  · calc (w * w₀)⁻¹ * x₀ * (w * w₀) = w₀⁻¹ * (w⁻¹ * x₀ * w) * w₀ := by group
      _ = w₀⁻¹ * (w₀⁻¹ * x' * w₀) * w₀ := by rw [hwx, hfu₁']
      _ = (w₀ * w₀)⁻¹ * x' * (w₀ * w₀) := by group
      _ = x' := by rw [hw₀, inv_one, one_mul, mul_one]

theorem transitive_inf_of_odd {J N : Subgroup G} {Ω : Set G} (hodd : Odd Ω.ncard)
    (hJΩ : ∀ j ∈ J, ∀ x ∈ Ω, j⁻¹ * x * j ∈ Ω)
    (htrans : ∀ x ∈ Ω, ∀ x' ∈ Ω, ∃ j ∈ J, j⁻¹ * x * j = x')
    (hidx : ∀ j ∈ J, ∀ k ∈ J, j ∉ N → k ∉ N → j * k ∈ N)
    {x₀ : G} (hx₀ : x₀ ∈ Ω) {x' : G} (hx' : x' ∈ Ω) :
    ∃ j ∈ J ⊓ N, j⁻¹ * x₀ * j = x' := by
  by_contra hne
  push Not at hne
  obtain ⟨j, hjJ, hjx⟩ := htrans x₀ hx₀ x' hx'
  have hjN : j ∉ N := fun h => hne j ⟨hjJ, h⟩ hjx
  have hjN' : j⁻¹ ∉ N := fun h => hjN (by simpa using N.inv_mem h)
  have hjJ' : j⁻¹ ∈ J := J.inv_mem hjJ
  set O : Set G := {y | ∃ a ∈ J ⊓ N, a⁻¹ * x₀ * a = y} with hOdef
  set O' : Set G := {y | ∃ a ∈ J ⊓ N, a⁻¹ * x' * a = y} with hO'def
  have hΩ : Ω = O ∪ O' := by
    refine Set.Subset.antisymm (fun y hy => ?_) (Set.union_subset ?_ ?_)
    · obtain ⟨k, hkJ, hky⟩ := htrans x₀ hx₀ y hy
      by_cases hkN : k ∈ N
      · exact Or.inl ⟨k, ⟨hkJ, hkN⟩, hky⟩
      · refine Or.inr ⟨j⁻¹ * k, ⟨J.mul_mem hjJ' hkJ, hidx _ hjJ' _ hkJ hjN' hkN⟩, ?_⟩
        rw [← hky, ← hjx]
        group
    · rintro y ⟨a, ⟨haJ, -⟩, rfl⟩
      exact hJΩ a haJ x₀ hx₀
    · rintro y ⟨a, ⟨haJ, -⟩, rfl⟩
      exact hJΩ a haJ x' hx'
  have hdisj : Disjoint O O' := by
    rw [Set.disjoint_left]
    rintro y ⟨a, ⟨haJ, haN⟩, rfl⟩ ⟨b, ⟨hbJ, hbN⟩, hb⟩
    refine hne (a * b⁻¹) ⟨J.mul_mem haJ (J.inv_mem hbJ), N.mul_mem haN (N.inv_mem hbN)⟩ ?_
    calc (a * b⁻¹)⁻¹ * x₀ * (a * b⁻¹) = b * (a⁻¹ * x₀ * a) * b⁻¹ := by group
      _ = b * (b⁻¹ * x' * b) * b⁻¹ := by rw [hb]
      _ = x' := by group
  have himg : (fun y => j⁻¹ * y * j) '' O = O' := by
    refine Set.Subset.antisymm ?_ (fun y' hy' => ?_)
    · rintro _ ⟨y, ⟨a, ⟨haJ, haN⟩, rfl⟩, rfl⟩
      have hajN : a * j ∉ N := fun h => hjN (by
        have := N.mul_mem (N.inv_mem haN) h
        simpa using this)
      refine ⟨j⁻¹ * (a * j), ⟨J.mul_mem hjJ' (J.mul_mem haJ hjJ),
        hidx _ hjJ' _ (J.mul_mem haJ hjJ) hjN' hajN⟩, ?_⟩
      simp only
      rw [← hjx]
      group
    · obtain ⟨b, ⟨hbJ, hbN⟩, rfl⟩ := hy'
      have hbjN : b * j⁻¹ ∉ N := fun h => hjN' (by
        have := N.mul_mem (N.inv_mem hbN) h
        simpa using this)
      refine ⟨(j * (b * j⁻¹))⁻¹ * x₀ * (j * (b * j⁻¹)), ⟨j * (b * j⁻¹), ⟨J.mul_mem hjJ
        (J.mul_mem hbJ hjJ'), hidx _ hjJ _ (J.mul_mem hbJ hjJ') hjN hbjN⟩, rfl⟩, ?_⟩
      simp only
      rw [← hjx]
      group
  have hinj : Function.Injective (fun y : G => j⁻¹ * y * j) := fun y z h => by
    simpa using h
  have hcard : Ω.ncard = 2 * O.ncard := by
    rw [hΩ, Set.ncard_union_eq hdisj, ← himg, Set.ncard_image_of_injective _ hinj]
    ring
  exact (Nat.not_even_iff_odd.mpr hodd) ⟨O.ncard, by rw [hcard]; ring⟩

theorem exists_mul_mem_normalizer {R Y : Subgroup G} (hR : IsSylowOf 2 R Y) {j : G}
    (hj : j ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ c ∈ Y, j * c ∈ Subgroup.normalizer (R : Set G) := by
  have hRj : IsSylowOf 2 (rightConjugate R j) Y := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hR j
    rwa [(rightConjugate_eq_self_iff Y j).mpr hj] at h1
  obtain ⟨c, hcY, hc⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hR hRj
  refine ⟨c, hcY, (rightConjugate_eq_self_iff R (j * c)).mp ?_⟩
  rw [← rightConjugate_mul]
  exact hc

omit [Finite G] in
theorem comm_mem_of_mem_sup {X Q : Subgroup G} (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hX : ∀ x ∈ X, ∀ x' ∈ X, x * x' = x' * x) {z : G} (hz : z ∈ Q ⊔ X) {x : G}
    (hx : x ∈ X) : x⁻¹ * z⁻¹ * x * z ∈ Q := by
  have hz' : z ∈ ((X ⊔ Q : Subgroup G) : Set G) := by rw [sup_comm]; exact hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Q hXQ] at hz'
  obtain ⟨x', hx', q, hq, rfl⟩ := Set.mem_mul.mp hz'
  have h1 : x⁻¹ * q⁻¹ * x ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXQ hx)) q⁻¹).mp (Q.inv_mem hq)
    simpa [mul_assoc] using this
  have e : x⁻¹ * (x' * q)⁻¹ * x * (x' * q) = x⁻¹ * q⁻¹ * x * q := by
    calc x⁻¹ * (x' * q)⁻¹ * x * (x' * q) = x⁻¹ * q⁻¹ * (x'⁻¹ * (x * x')) * q := by group
      _ = x⁻¹ * q⁻¹ * (x'⁻¹ * (x' * x)) * q := by rw [hX x hx x' hx']
      _ = x⁻¹ * q⁻¹ * x * q := by group
  rw [e]
  exact Q.mul_mem h1 hq

omit [Finite G] in
theorem sup_inf_le_of_inf_eq_bot {X Y Q : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hYQ : Y ≤ Q) (hXQ : X ⊓ Q = ⊥) : (X ⊔ Y) ⊓ Q ≤ Y := by
  rintro k ⟨hk, hkQ⟩
  have hk' : k ∈ ((X ⊔ Y : Subgroup G) : Set G) := hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXY] at hk'
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hk'
  have hxQ : x ∈ X ⊓ Q := by
    refine ⟨hx, ?_⟩
    have : x = (x * y) * y⁻¹ := by group
    rw [this]
    exact Q.mul_mem hkQ (Q.inv_mem (hYQ hy))
  rw [hXQ, Subgroup.mem_bot] at hxQ
  rw [hxQ, one_mul]
  exact hy

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
