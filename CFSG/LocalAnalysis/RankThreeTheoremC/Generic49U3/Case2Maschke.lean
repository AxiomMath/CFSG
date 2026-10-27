module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.RepresentationTheory.Maschke

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup

private theorem exists_invariant_complement_field {k : Type} [Field k] {Y : Type} [Group Y] [Finite Y]
    (K : Subgroup Y) [K.Normal] (hK : (Nat.card (Y ⧸ K) : k) ≠ 0)
    {E : Type} [AddCommGroup E] [Module k E]
    (ρ : Representation k Y E) (hKρ : ∀ g ∈ K, ρ g = 1)
    (W : Submodule k E) (hW : ∀ g : Y, ∀ w ∈ W, ρ g w ∈ W) :
    ∃ W' : Submodule k E, (∀ g : Y, ∀ w ∈ W', ρ g w ∈ W') ∧ IsCompl W W' := by
  classical
  let ρ' : Representation k (Y ⧸ K) E := QuotientGroup.lift K ρ (fun g hg => hKρ g hg)
  have hρ' : ∀ (g : Y) (e : E), ρ' (g : Y ⧸ K) e = ρ g e := fun g e => rfl
  haveI : NeZero (Nat.card (Y ⧸ K) : k) := ⟨hK⟩
  let σ : Subrepresentation ρ' :=
    ⟨W, fun g v hv => by
      induction g using QuotientGroup.induction_on with
      | H z => rw [hρ']; exact hW z v hv⟩
  obtain ⟨σ', hσ'⟩ := ComplementedLattice.exists_isCompl σ
  refine ⟨σ'.toSubmodule, fun g w hw => ?_, ?_⟩
  · have := σ'.apply_mem_toSubmodule (g : Y ⧸ K) hw
    rwa [hρ'] at this
  · constructor
    · rw [disjoint_iff]
      have := disjoint_iff.1 hσ'.1
      exact congrArg Subrepresentation.toSubmodule this
    · rw [codisjoint_iff]
      have := codisjoint_iff.1 hσ'.2
      exact congrArg Subrepresentation.toSubmodule this

private theorem exists_invariant_complement {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    (S : Sylow p Y) {E : Type} [AddCommGroup E] [Module (ZMod p) E]
    (ρ : Representation (ZMod p) Y E) (hS : ∀ s ∈ (S : Subgroup Y), ρ s = 1)
    (W : Submodule (ZMod p) E) (hW : ∀ g : Y, ∀ w ∈ W, ρ g w ∈ W) :
    ∃ W' : Submodule (ZMod p) E, (∀ g : Y, ∀ w ∈ W', ρ g w ∈ W') ∧ IsCompl W W' := by
  classical
  have hSK : (S : Subgroup Y) ≤ ρ.ker := fun s hs => hS s hs
  have hdvd : ¬ p ∣ Nat.card (Y ⧸ ρ.ker) := by
    have h1 : (ρ.ker).index ∣ (S : Subgroup Y).index := Subgroup.index_dvd_of_le hSK
    have h2 : ¬ p ∣ (S : Subgroup Y).index := S.not_dvd_index
    exact fun h => h2 (h.trans h1)
  have hK : ((Nat.card (Y ⧸ ρ.ker) : ℕ) : ZMod p) ≠ 0 :=
    fun h => hdvd ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hker : ∀ g ∈ ρ.ker, ρ g = 1 := fun g hg => MonoidHom.mem_ker.1 hg
  exact exists_invariant_complement_field (k := ZMod p) ρ.ker hK ρ hker W hW

private theorem exists_quotient_module {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y]
    (V Z : Subgroup Y) (hV : V.Normal) (hZ : Z.Normal)
    (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b * a⁻¹ * b⁻¹ ∈ Z) (hVexp : ∀ v ∈ V, v ^ p = 1) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module (ZMod p) E)
      (π : Y → E) (ρ : Representation (ZMod p) Y E),
      (∀ a ∈ V, ∀ b ∈ V, π (a * b) = π a + π b) ∧
      (∀ v ∈ V, (π v = 0 ↔ v ∈ Z)) ∧
      (∀ e : E, ∃ v ∈ V, π v = e) ∧
      (∀ g : Y, ∀ v ∈ V, π (g * v * g⁻¹) = ρ g (π v)) := by
  classical
  haveI := hZ
  haveI := hV
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let E₀ : Subgroup (Y ⧸ Z) := V.map (QuotientGroup.mk' Z)
  haveI : E₀.Normal := Subgroup.Normal.map hV (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hcomm : ∀ x y : E₀, x * y = y * x := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show (QuotientGroup.mk' Z a) * (QuotientGroup.mk' Z b) = (QuotientGroup.mk' Z b) * (QuotientGroup.mk' Z a)
    have h := hVcomm b⁻¹ (V.inv_mem hb) a⁻¹ (V.inv_mem ha)
    simp only [inv_inv] at h
    show ((a : Y) : Y ⧸ Z) * (b : Y ⧸ Z) = (b : Y ⧸ Z) * (a : Y ⧸ Z)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    simpa [mul_assoc] using h
  letI : CommGroup E₀ := { (inferInstance : Group E₀) with mul_comm := hcomm }
  have hexp : ∀ x : Additive E₀, p • x = 0 := by
    intro x
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (Additive.toMul x).2
    have h1 : (Additive.toMul x) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hay, ← map_pow, hVexp a ha, map_one]
      rfl
    apply Additive.toMul.injective
    rw [toMul_nsmul, h1]
    rfl
  haveI : Module (ZMod p) (Additive E₀) := AddCommGroup.zmodModule hexp
  let ρ₀ : Y →* MulAut E₀ := MulAut.conjNormal.comp (QuotientGroup.mk' Z)
  let lin : MulAut E₀ →* (Additive E₀ →ₗ[ZMod p] Additive E₀) :=
    { toFun := fun σ => AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive σ.toMonoidHom)
      map_one' := by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  let ρ : Representation (ZMod p) Y (Additive E₀) := lin.comp ρ₀
  let π : Y → Additive E₀ := fun y =>
    if h : y ∈ V then Additive.ofMul (⟨QuotientGroup.mk' Z y, Subgroup.mem_map_of_mem _ h⟩ : E₀)
    else 0
  refine ⟨Additive E₀, inferInstance, inferInstance, π, ρ, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    have hab : a * b ∈ V := V.mul_mem ha hb
    simp only [π, dif_pos ha, dif_pos hb, dif_pos hab]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp
  · intro v hv
    have key : (⟨QuotientGroup.mk' Z v, Subgroup.mem_map_of_mem _ hv⟩ : E₀) = 1 ↔ v ∈ Z := by
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff v
    simp only [π, dif_pos hv, ofMul_eq_zero]
    exact key
  · intro e
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (Additive.toMul e).2
    refine ⟨a, ha, ?_⟩
    simp only [π, dif_pos ha]
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa using hay
  · intro g v hv
    have hgv : g * v * g⁻¹ ∈ V := hV.conj_mem v hv g
    simp only [π, dif_pos hv, dif_pos hgv]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [ρ, ρ₀, lin, MulAut.conjNormal_apply]

theorem exists_normal_complement {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (S : Sylow p Y) (V Λ Z : Subgroup Y) (hV : V.Normal) (hΛ : Λ.Normal) (hZ : Z.Normal)
    (hΛV : Λ ≤ V) (hZV : Z ≤ V) (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hVexp : ∀ v ∈ V, v ^ p = 1) (hSV : ∀ s ∈ (S : Subgroup Y), ∀ v ∈ V, s * v * s⁻¹ * v⁻¹ ∈ Z)
    (hΛcard : Nat.card Λ = p) (hΛZ : Λ ⊓ Z = ⊥) :
    ∃ T' : Subgroup Y, T'.Normal ∧ Z ≤ T' ∧ T' ≤ V ∧ T' ⊓ Λ = ⊥ ∧ T' ⊔ Λ = V := by
  classical
  have _ := hΛcard
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, _, _, π, ρ, h1, h2, h3, h4⟩ := exists_quotient_module hp V Z hV hZ hVcomm hVexp
  have hπ1 : π 1 = 0 := by
    have := h1 1 V.one_mem 1 V.one_mem
    rw [mul_one] at this
    simpa using this
  have hπinv : ∀ a ∈ V, π a⁻¹ = - π a := by
    intro a ha
    have := h1 a ha a⁻¹ (V.inv_mem ha)
    rw [mul_inv_cancel, hπ1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  let W₀ : AddSubgroup E :=
    { carrier := {e | ∃ l ∈ Λ, π l = e}
      zero_mem' := ⟨1, Λ.one_mem, hπ1⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, Λ.mul_mem ha hb, h1 a (hΛV ha) b (hΛV hb)⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, Λ.inv_mem ha, hπinv a (hΛV ha)⟩ }
  let W : Submodule (ZMod p) E := AddSubgroup.toZModSubmodule p W₀
  have hWmem : ∀ e, e ∈ W ↔ ∃ l ∈ Λ, π l = e := fun e => Iff.rfl
  have hS : ∀ s ∈ (S : Subgroup Y), ρ s = 1 := by
    intro s hs
    ext e
    obtain ⟨v, hv, rfl⟩ := h3 e
    rw [← h4 s v hv]
    have hz := hSV s hs v hv
    have hzV : s * v * s⁻¹ * v⁻¹ ∈ V := hZV hz
    have := h1 _ hzV v hv
    rw [inv_mul_cancel_right, (h2 _ hzV).2 hz, zero_add] at this
    exact this
  have hWinv : ∀ g : Y, ∀ w ∈ W, ρ g w ∈ W := by
    intro g w hw
    obtain ⟨l, hl, rfl⟩ := (hWmem w).1 hw
    exact (hWmem _).2 ⟨g * l * g⁻¹, hΛ.conj_mem l hl g, h4 g l (hΛV hl)⟩
  obtain ⟨W', hW'inv, hW'⟩ := exists_invariant_complement S ρ hS W hWinv
  let T' : Subgroup Y :=
    { carrier := {y | y ∈ V ∧ π y ∈ W'}
      one_mem' := ⟨V.one_mem, by rw [hπ1]; exact W'.zero_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, haW⟩ ⟨hb, hbW⟩
        exact ⟨V.mul_mem ha hb, by rw [h1 a ha b hb]; exact W'.add_mem haW hbW⟩
      inv_mem' := by
        rintro a ⟨ha, haW⟩
        exact ⟨V.inv_mem ha, by rw [hπinv a ha]; exact W'.neg_mem haW⟩ }
  refine ⟨T', ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun n hn g => ⟨hV.conj_mem n hn.1 g, ?_⟩⟩
    rw [h4 g n hn.1]
    exact hW'inv g _ hn.2
  · intro z hz
    exact ⟨hZV hz, by rw [(h2 z (hZV hz)).2 hz]; exact W'.zero_mem⟩
  · intro y hy
    exact hy.1
  · rw [eq_bot_iff]
    rintro x ⟨⟨hxV, hxW'⟩, hxΛ⟩
    have hxW : π x ∈ W := (hWmem _).2 ⟨x, hxΛ, rfl⟩
    have h0 : π x = 0 := by
      have : π x ∈ W ⊓ W' := ⟨hxW, hxW'⟩
      rw [hW'.inf_eq_bot] at this
      simpa using this
    have hxZ : x ∈ Z := (h2 x hxV).1 h0
    have : x ∈ Λ ⊓ Z := ⟨hxΛ, hxZ⟩
    rw [hΛZ] at this
    exact this
  · apply le_antisymm
    · exact sup_le (fun y hy => hy.1) hΛV
    · intro v hv
      have hvtop : π v ∈ W ⊔ W' := by rw [hW'.sup_eq_top]; trivial
      obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.1 hvtop
      obtain ⟨l, hl, rfl⟩ := (hWmem w).1 hw
      have hy : l⁻¹ * v ∈ T' := by
        refine ⟨V.mul_mem (V.inv_mem (hΛV hl)) hv, ?_⟩
        rw [h1 l⁻¹ (V.inv_mem (hΛV hl)) v hv, hπinv l (hΛV hl), ← hsum]
        simpa using hw'
      have hv' : v = l * (l⁻¹ * v) := by group
      rw [hv', sup_comm]
      exact Subgroup.mul_mem_sup hl hy

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
