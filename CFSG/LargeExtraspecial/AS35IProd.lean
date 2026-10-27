module

public import CFSG.LargeExtraspecial.AS35IOmega

public section

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup Asc77
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] {N U P : Subgroup G} {z : G}

namespace Hyp

variable (h : Hyp N U P z)
include h

omit h in
theorem commutator_le_V [Finite G] {X : Subgroup G} (hXN : X ≤ N) :
    ⁅genV N z, X⁆ ≤ genV N z := by
  rw [commutator_le]
  intro v hv x hx
  rw [commutatorElement_def, show v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) by group]
  exact mul_mem hv (conj_mem_genV (hXN hx) (inv_mem hv))

theorem z_mem_commutator_sup [Finite G] :
    z ∈ ⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N := by
  classical
  have := h.isMulComm_V
  let _ : Fintype (conjIn z N) := Fintype.ofFinite _
  obtain ⟨a, ha, haK⟩ := h.exists_not_mem_kerV
  have haN := h.sup_le_N ha
  let f : conjIn z N → genV N z := fun t => ⟨t, subset_closure t.2⟩
  let z₀ : conjIn z N := ⟨z, self_mem_conjIn z N⟩
  let σ : Equiv.Perm (conjIn z N) := conjAct z N ⟨a, haN⟩
  have hσ : ∀ t, ((σ t : conjIn z N) : G) = a * t * a⁻¹ := fun t => conjAct_apply _ _
  have ha2 : a * a ∈ kerV N z := h.sq_mem_kerV ha
  have hσσ : ∀ t, σ (σ t) = t := by
    intro t
    apply Subtype.ext
    rw [hσ, hσ]
    have hc := (mem_kerV_iff (N.mul_mem haN haN)).1 ha2 t t.2
    calc a * (a * (t : G) * a⁻¹) * a⁻¹ = (a * a) * t * (a * a)⁻¹ := by group
      _ = t := by rw [← hc]; group
  have hσz : σ z₀ = z₀ := Subtype.ext (by
    rw [hσ]
    change a * z * a⁻¹ = z
    rw [h.comm_sup ha]
    group)
  have hσne : ∀ t, t ≠ z₀ → σ t ≠ t := fun t ht h1 =>
    h.conj_ne_of_ne ha haK t.2 (fun h2 => ht (Subtype.ext h2)) (by rw [← hσ, h1])
  have hmemφ : ∀ v : genV N z, (v : G) * a * (v : G)⁻¹ * a⁻¹ ∈ genV N z := fun v => by
    rw [show (v : G) * a * (v : G)⁻¹ * a⁻¹ = v * (a * (v : G)⁻¹ * a⁻¹) by group]
    exact mul_mem v.2 (conj_mem_genV haN (inv_mem v.2))
  let φ : genV N z →* genV N z :=
    { toFun := fun v => ⟨(v : G) * a * (v : G)⁻¹ * a⁻¹, hmemφ v⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun v w => Subtype.ext (by
        have hX : (w : G) * (a * (w : G)⁻¹ * a⁻¹) ∈ genV N z :=
          mul_mem w.2 (conj_mem_genV haN (inv_mem w.2))
        have hY : a * (v : G)⁻¹ * a⁻¹ ∈ genV N z := conj_mem_genV haN (inv_mem v.2)
        change ((v : G) * w) * a * ((v : G) * w)⁻¹ * a⁻¹ =
          ((v : G) * a * (v : G)⁻¹ * a⁻¹) * ((w : G) * a * (w : G)⁻¹ * a⁻¹)
        calc ((v : G) * w) * a * ((v : G) * w)⁻¹ * a⁻¹
            = v * ((w * (a * (w : G)⁻¹ * a⁻¹)) * (a * (v : G)⁻¹ * a⁻¹)) := by group
          _ = v * ((a * (v : G)⁻¹ * a⁻¹) * (w * (a * (w : G)⁻¹ * a⁻¹))) := by
            rw [h.comm_V hX hY]
          _ = ((v : G) * a * (v : G)⁻¹ * a⁻¹) * ((w : G) * a * (w : G)⁻¹ * a⁻¹) := by
            group) }
  set S := (Finset.univ : Finset (conjIn z N)).erase z₀ with hSdef
  have hSφ : (∏ t ∈ S, f t) ∈ φ.range := by
    rw [← QuotientGroup.eq_one_iff (N := φ.range), ← QuotientGroup.mk'_apply, map_prod]
    refine Finset.prod_involution (fun t _ => σ t) (fun t _ => ?_) (fun t ht _ => ?_)
      (fun t ht => ?_) (fun t _ => hσσ t)
    · have hft : QuotientGroup.mk' φ.range (f (σ t)) = QuotientGroup.mk' φ.range (f t) := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        refine ⟨f t, Subtype.ext ?_⟩
        change (t : G) * a * (t : G)⁻¹ * a⁻¹ = ((σ t : conjIn z N) : G)⁻¹ * t
        rw [hσ]
        have e1 : (a * (t : G) * a⁻¹)⁻¹ = a * (t : G)⁻¹ * a⁻¹ := by group
        rw [e1]
        have hcomm := h.comm_V (conjIn_subset_genV t.2)
          (conj_mem_genV haN (inv_mem (conjIn_subset_genV t.2)))
        calc (t : G) * a * (t : G)⁻¹ * a⁻¹ = (t : G) * (a * (t : G)⁻¹ * a⁻¹) := by group
          _ = (a * (t : G)⁻¹ * a⁻¹) * t := hcomm
      rw [hft, ← map_mul, show f t * f t = 1 from Subtype.ext (h.mul_self_V (f t).2), map_one]
    · exact hσne t (Finset.ne_of_mem_erase ht)
    · rw [Finset.mem_erase]
      refine ⟨fun h1 => Finset.ne_of_mem_erase ht ?_, Finset.mem_univ _⟩
      rw [← hσσ t, h1, hσz]
  have hSc : ((∏ t ∈ S, f t : genV N z) : G) ∈ ⁅genV N z, U ⊔ P⁆ := by
    obtain ⟨v, hv⟩ := hSφ
    rw [← hv]
    exact commutator_mem_commutator v.2 ha
  have hconj : ∀ n ∈ N, n * ((∏ t, f t : genV N z) : G) * n⁻¹ = ((∏ t, f t : genV N z) : G) := by
    intro n hn
    let cn : genV N z →* genV N z :=
      { toFun := fun v => ⟨n * v * n⁻¹, conj_mem_genV hn v.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun v w => Subtype.ext (by
          change n * ((v : G) * w) * n⁻¹ = (n * v * n⁻¹) * (n * w * n⁻¹)
          group) }
    have hcn : ∀ t, cn (f t) = f (conjAct z N ⟨n, hn⟩ t) := fun t =>
      Subtype.ext (by rw [conjAct_apply]; rfl)
    have : cn (∏ t, f t) = ∏ t, f t := by
      rw [map_prod]
      simp_rw [hcn]
      exact Equiv.prod_comp (conjAct z N ⟨n, hn⟩) f
    exact congrArg Subtype.val this
  have hΩC : ((∏ t, f t : genV N z) : G) ∈ Asc77.centerIn z N := by
    refine mem_inf.2 ⟨(∏ t, f t).2, mem_centralizer_iff.2 fun n hn => ?_⟩
    calc n * ((∏ t, f t : genV N z) : G)
        = n * ((∏ t, f t : genV N z) : G) * n⁻¹ * n := by group
      _ = ((∏ t, f t : genV N z) : G) * n := by rw [hconj n hn]
  have hsplit : ((∏ t, f t : genV N z) : G) = z * ((∏ t ∈ S, f t : genV N z) : G) := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ z₀)]
    rfl
  have hsQ : ((∏ t ∈ S, f t : genV N z) : G) ∈ U ⊔ P :=
    (mem_inf.1 (h.commutator_le_inf hSc)).1
  have hscen : ∀ y ∈ U ⊔ P,
      ((∏ t ∈ S, f t : genV N z) : G) * y = y * ((∏ t ∈ S, f t : genV N z) : G) := by
    intro y hy
    have hs : ((∏ t ∈ S, f t : genV N z) : G) = z⁻¹ * ((∏ t, f t : genV N z) : G) := by
      rw [hsplit]
      group
    have hyz := h.comm_sup hy
    have hyΩ := mem_centralizer_iff.1 (mem_inf.1 hΩC).2 y (h.sup_le_N hy)
    rw [hs]
    calc z⁻¹ * ((∏ t, f t : genV N z) : G) * y = z⁻¹ * (y * ((∏ t, f t : genV N z) : G)) := by
          rw [mul_assoc, ← hyΩ]
      _ = (z⁻¹ * y) * ((∏ t, f t : genV N z) : G) := by group
      _ = (y * z⁻¹) * ((∏ t, f t : genV N z) : G) := by
          rw [show z⁻¹ * y = y * z⁻¹ by
            calc z⁻¹ * y = z⁻¹ * (y * z) * z⁻¹ := by group
              _ = z⁻¹ * (z * y) * z⁻¹ := by rw [hyz]
              _ = y * z⁻¹ := by group]
      _ = y * (z⁻¹ * ((∏ t, f t : genV N z) : G)) := by group
  obtain ⟨u, hu, hsu | hsu⟩ := h.exists_of_central hsQ hscen
  · exfalso
    apply h.notcen
    intro n hn
    rw [mem_centralizer_singleton_iff]
    have hz : z = ((∏ t, f t : genV N z) : G) * u⁻¹ := by
      rw [hsplit, hsu]
      group
    have hnΩ := mem_centralizer_iff.1 (mem_inf.1 hΩC).2 n hn
    have hnu : n * u⁻¹ = u⁻¹ * n := (h.Ucen u⁻¹ (U.inv_mem hu) n hn).symm
    rw [hz]
    calc n * (((∏ t, f t : genV N z) : G) * u⁻¹) = (n * ((∏ t, f t : genV N z) : G)) * u⁻¹ := by
          group
      _ = (((∏ t, f t : genV N z) : G) * n) * u⁻¹ := by rw [hnΩ]
      _ = ((∏ t, f t : genV N z) : G) * (n * u⁻¹) := by group
      _ = ((∏ t, f t : genV N z) : G) * (u⁻¹ * n) := by rw [hnu]
      _ = ((∏ t, f t : genV N z) : G) * u⁻¹ * n := by group
  · have huV : u ∈ genV N z := by
      have : u = ((∏ t ∈ S, f t : genV N z) : G) * z⁻¹ := by rw [hsu]; group
      rw [this]
      exact mul_mem (∏ t ∈ S, f t).2 (inv_mem z_mem_V)
    have huC := h.inf_le_centerIn (mem_inf.2 ⟨hu, huV⟩)
    have hz : u⁻¹ * ((∏ t ∈ S, f t : genV N z) : G) = z := by rw [hsu]; group
    have hmem : u⁻¹ * ((∏ t ∈ S, f t : genV N z) : G) ∈
        ⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N :=
      mul_mem (mem_sup_right (inv_mem huC)) (mem_sup_left hSc)
    rwa [hz] at hmem

omit h in
theorem map_conj_genV {g : G} (hg : g ∈ N) :
    (genV N z).map (MulAut.conj g).toMonoidHom = genV N z := by
  ext v
  rw [mem_map_conj]
  constructor
  · intro hv
    have := conj_mem_genV hg hv
    simpa [mul_assoc] using this
  · intro hv
    simpa using conj_mem_genV (N.inv_mem hg) hv

omit h in
theorem map_conj_centerIn {g : G} (hg : g ∈ N) :
    (Asc77.centerIn z N).map (MulAut.conj g).toMonoidHom = Asc77.centerIn z N := by
  ext c
  rw [mem_map_conj]
  constructor
  · intro hc
    have h1 := mem_centralizer_iff.1 (mem_inf.1 hc).2 g hg
    have : g⁻¹ * c * g = c := by
      have h2 : g * (g⁻¹ * c * g) = c * g := by group
      rw [h1] at h2
      exact mul_right_cancel (h2.trans (by group))
    rwa [this] at hc
  · intro hc
    have h1 := mem_centralizer_iff.1 (mem_inf.1 hc).2 g hg
    have : g⁻¹ * c * g = c := by
      calc g⁻¹ * c * g = g⁻¹ * (c * g) := by group
        _ = g⁻¹ * (g * c) := by rw [h1]
        _ = c := by group
    rwa [this]

theorem le_normalizer_of_le_V [Finite G] {A B : Subgroup G} (hA : A ≤ genV N z)
    (hB : B ≤ genV N z) : B ≤ normalizer (A : Set G) := by
  intro b hb
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have := h.comm_V (hB hb) (hA ha)
    rwa [this, mul_inv_cancel_right]
  · intro ha
    have hc := h.comm_V (hB hb) (hA ha)
    have hx : b⁻¹ * (b * a * b⁻¹) * b = b * a * b⁻¹ := by
      calc b⁻¹ * (b * a * b⁻¹) * b = b⁻¹ * ((b * a * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [hc]
        _ = b * a * b⁻¹ := by group
    have : a = b⁻¹ * (b * a * b⁻¹) * b := by group
    rw [this, hx]
    exact ha

theorem card_genV_mul_le [Finite G] {g : G} (hg : g ∈ N) (hgM : g ∉ cenM N z) :
    Nat.card (genV N z) * Nat.card (Asc77.centerIn z N) ≤
      Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) *
        Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) := by
  set Qg := (U ⊔ P).map (MulAut.conj g).toMonoidHom with hQg
  set A := ⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N with hA
  set B := ⁅genV N z, Qg⁆ ⊔ Asc77.centerIn z N with hB
  have hQgN : Qg ≤ N := by
    rintro _ ⟨q, hq, rfl⟩
    exact N.mul_mem (N.mul_mem hg (h.sup_le_N hq)) (N.inv_mem hg)
  have hCV : Asc77.centerIn z N ≤ genV N z := inf_le_left
  have hAV : A ≤ genV N z := sup_le (commutator_le_V h.sup_le_N) hCV
  have hBV : B ≤ genV N z := sup_le (commutator_le_V hQgN) hCV
  have hVle : genV N z ≤ A ⊔ B := by
    have hWV : A ⊔ B ≤ genV N z := sup_le hAV hBV
    have hnorm : ∀ X : Subgroup G, ⁅genV N z, X⁆ ≤ A ⊔ B →
        X ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
      intro X hXW x hx
      have key : ∀ y ∈ X, ∀ w ∈ A ⊔ B, y * w * y⁻¹ ∈ A ⊔ B := by
        intro y hy w hw
        have hc : ⁅w⁻¹, y⁆ ∈ A ⊔ B := hXW (commutator_mem_commutator (inv_mem (hWV hw)) hy)
        rw [commutatorElement_def] at hc
        rw [show y * w * y⁻¹ = w * (w⁻¹ * y * w⁻¹⁻¹ * y⁻¹) by group]
        exact mul_mem hw hc
      rw [mem_normalizer_iff]
      intro w
      refine ⟨key x hx w, fun hw => ?_⟩
      have := key x⁻¹ (inv_mem hx) _ hw
      simpa [mul_assoc] using this
    have hN : N ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
      (h.le_sup_conj hg hgM).trans (sup_le (hnorm _ (le_sup_left.trans le_sup_left))
        (hnorm _ (le_sup_left.trans le_sup_right)))
    have hzW : z ∈ A ⊔ B := mem_sup_left h.z_mem_commutator_sup
    rw [genV, closure_le]
    rintro _ ⟨n, hn, rfl⟩
    exact (mem_normalizer_iff.1 (hN hn) z).1 hzW
  have hBA : B = A.map (MulAut.conj g).toMonoidHom := by
    rw [hA, hB, Subgroup.map_sup, map_commutator, map_conj_genV hg, map_conj_centerIn hg]
  have hcardB : Nat.card B = Nat.card A := by
    rw [hBA]
    exact card_map_of_injective (MulAut.conj g).injective
  have hpf := card_sup_mul_card_inf (h.le_normalizer_of_le_V hAV hBV)
  have hCAB : Asc77.centerIn z N ≤ A ⊓ B := le_inf le_sup_right le_sup_right
  calc Nat.card (genV N z) * Nat.card (Asc77.centerIn z N)
      ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) :=
        Nat.mul_le_mul (card_le_of_le hVle) (card_le_of_le hCAB)
    _ = Nat.card A * Nat.card B := hpf
    _ = Nat.card A * Nat.card A := by rw [hcardB]

theorem card_genV_le_of_transitive [Finite G] {t₁ : G} (ht₁ : t₁ ∈ conjIn z N)
    (htr : ∀ t ∈ conjIn z N, t ≠ z → ∃ a ∈ U ⊔ P, a * t₁ * a⁻¹ = t) :
    Nat.card (genV N z) ≤ 2 * Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) := by
  set A := ⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N with hA
  have hCV : Asc77.centerIn z N ≤ genV N z := inf_le_left
  have hAV : A ≤ genV N z := sup_le (commutator_le_V h.sup_le_N) hCV
  have ht₁V : t₁ ∈ genV N z := subset_closure ht₁
  have hVW : genV N z ≤ zpowers t₁ ⊔ A := by
    rw [genV, closure_le]
    intro t ht
    by_cases htz : t = z
    · rw [htz]
      exact mem_sup_right h.z_mem_commutator_sup
    · obtain ⟨a, ha, rfl⟩ := htr t ht htz
      have hc : ⁅t₁⁻¹, a⁆ ∈ ⁅genV N z, U ⊔ P⁆ := commutator_mem_commutator (inv_mem ht₁V) ha
      rw [show a * t₁ * a⁻¹ = t₁ * ⁅t₁⁻¹, a⁆ by rw [commutatorElement_def]; group]
      exact mul_mem (mem_sup_left (mem_zpowers t₁)) (mem_sup_right (mem_sup_left hc))
  have hpf := card_sup_mul_card_inf (h.le_normalizer_of_le_V (zpowers_le.2 ht₁V) hAV)
  have hz2 : Nat.card (zpowers t₁) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (by rw [pow_two, h.mul_self_V ht₁V])
  have hpos : 0 < Nat.card ↥(zpowers t₁ ⊓ A) := Nat.card_pos
  calc Nat.card (genV N z) ≤ Nat.card ↥(zpowers t₁ ⊔ A) := card_le_of_le hVW
    _ ≤ Nat.card ↥(zpowers t₁ ⊔ A) * Nat.card ↥(zpowers t₁ ⊓ A) := Nat.le_mul_of_pos_right _ hpos
    _ = Nat.card (zpowers t₁) * Nat.card A := hpf
    _ ≤ 2 * Nat.card A := Nat.mul_le_mul_right _ hz2

theorem commutator_le_of_card_two [Finite G] (h2 : Nat.card (barOf N z (U ⊔ P)) = 2) :
    ⁅genV N z, U ⊔ P⁆ ≤ zpowers z ⊔ Asc77.centerIn z N := by
  rw [commutator_le]
  intro v hv q hq
  have hqN := h.sup_le_N hq
  have hcQV := h.commutator_le_inf (commutator_mem_commutator hv hq)
  have hcen : ∀ q' ∈ U ⊔ P, ⁅v, q⁆ * q' = q' * ⁅v, q⁆ := by
    intro q' hq'
    have hq'N := h.sup_le_N hq'
    by_cases hqK : q ∈ kerV N z
    · have hvq := mem_centralizer_iff.1 (mem_inf.1 hqK).2 v hv
      have hc1 : ⁅v, q⁆ = 1 := by
        rw [commutatorElement_def, hvq]
        group
      rw [hc1, one_mul, mul_one]
    · have hq1 : piK N z ⟨q, hqN⟩ ≠ 1 := fun h1 => hqK (piK_eq_one.1 h1)
      have hcases : q' ∈ kerV N z ∨ q⁻¹ * q' ∈ kerV N z := by
        by_cases hq'1 : piK N z ⟨q', hq'N⟩ = 1
        · exact Or.inl (piK_eq_one.1 hq'1)
        · right
          obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : barOf N z (U ⊔ P))).1 h2
          have e1 := hyu ⟨_, piK_mem_barOf hq⟩ (fun h' => hq1 (congrArg Subtype.val h'))
          have e2 := hyu ⟨_, piK_mem_barOf hq'⟩ (fun h' => hq'1 (congrArg Subtype.val h'))
          have : piK N z ⟨q, hqN⟩ = piK N z ⟨q', hq'N⟩ := congrArg Subtype.val (e1.trans e2.symm)
          simpa using piK_eq_iff.1 this
      have hq2v : (q * q) * v⁻¹ = v⁻¹ * (q * q) :=
        (mem_centralizer_iff.1 (mem_inf.1 (h.sq_mem_kerV hq)).2 v⁻¹ (inv_mem hv)).symm
      have hwV : q * v * q⁻¹ ∈ genV N z := conj_mem_genV hqN hv
      have hcomm := h.comm_V hwV (inv_mem hv)
      have hqc : q * ⁅v, q⁆ * q⁻¹ = ⁅v, q⁆ := by
        rw [commutatorElement_def]
        calc q * (v * q * v⁻¹ * q⁻¹) * q⁻¹ = (q * v * q⁻¹) * ((q * q) * v⁻¹ * (q * q)⁻¹) := by
              group
          _ = (q * v * q⁻¹) * (v⁻¹ * (q * q) * (q * q)⁻¹) := by rw [hq2v]
          _ = (q * v * q⁻¹) * v⁻¹ := by group
          _ = v⁻¹ * (q * v * q⁻¹) := hcomm
          _ = v * (q * v * q⁻¹)⁻¹ := by rw [h.inv_V hwV, h.inv_V hv]
          _ = v * q * v⁻¹ * q⁻¹ := by group
      have hcq : ⁅v, q⁆ * q = q * ⁅v, q⁆ := by
        calc ⁅v, q⁆ * q = q * ⁅v, q⁆ * q⁻¹ * q := by rw [hqc]
          _ = q * ⁅v, q⁆ := by group
      rcases hcases with hk | hk
      · exact (mem_centralizer_iff.1 (mem_inf.1 hk).2 _ (mem_inf.1 hcQV).2)
      · have hkc := mem_centralizer_iff.1 (mem_inf.1 hk).2 _ (mem_inf.1 hcQV).2
        have hq' : q' = q * (q⁻¹ * q') := by group
        rw [hq']
        calc ⁅v, q⁆ * (q * (q⁻¹ * q')) = (⁅v, q⁆ * q) * (q⁻¹ * q') := by group
          _ = (q * ⁅v, q⁆) * (q⁻¹ * q') := by rw [hcq]
          _ = q * (⁅v, q⁆ * (q⁻¹ * q')) := by group
          _ = q * ((q⁻¹ * q') * ⁅v, q⁆) := by rw [hkc]
          _ = q * (q⁻¹ * q') * ⁅v, q⁆ := by group
  obtain ⟨u, hu, hcu | hcu⟩ := h.exists_of_central (mem_inf.1 hcQV).1 hcen
  · have huV : u ∈ genV N z := hcu ▸ (mem_inf.1 hcQV).2
    rw [hcu]
    exact mem_sup_right (h.inf_le_centerIn (mem_inf.2 ⟨hu, huV⟩))
  · have huV : u ∈ genV N z := by
      have : u = ⁅v, q⁆ * z⁻¹ := by rw [hcu]; group
      rw [this]
      exact mul_mem (mem_inf.1 hcQV).2 (inv_mem z_mem_V)
    rw [hcu]
    exact mul_mem (mem_sup_right (h.inf_le_centerIn (mem_inf.2 ⟨hu, huV⟩)))
      (mem_sup_left (mem_zpowers z))

theorem card_commutator_sup_le_of_card_two [Finite G]
    (h2 : Nat.card (barOf N z (U ⊔ P)) = 2) :
    Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) ≤ 2 * Nat.card (Asc77.centerIn z N) := by
  have hle : ⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N ≤ zpowers z ⊔ Asc77.centerIn z N :=
    sup_le (h.commutator_le_of_card_two h2) le_sup_right
  have hCV : Asc77.centerIn z N ≤ genV N z := inf_le_left
  have hpf := card_sup_mul_card_inf (h.le_normalizer_of_le_V (zpowers_le.2 z_mem_V) hCV)
  have hz2 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, h.orderOf_z]
  have hpos : 0 < Nat.card ↥(zpowers z ⊓ Asc77.centerIn z N) := Nat.card_pos
  calc Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N)
      ≤ Nat.card ↥(zpowers z ⊔ Asc77.centerIn z N) := card_le_of_le hle
    _ ≤ Nat.card ↥(zpowers z ⊔ Asc77.centerIn z N) *
        Nat.card ↥(zpowers z ⊓ Asc77.centerIn z N) := Nat.le_mul_of_pos_right _ hpos
    _ = 2 * Nat.card (Asc77.centerIn z N) := by rw [hpf, hz2]

end Hyp

end CFSG.LargeExtraspecial.Asc22
