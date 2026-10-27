module

public import CFSG.FeitThompson.Representations.ConjTransitiveAbelianCharsCentralChar
public import Mathlib.RepresentationTheory.Irreducible
import CFSG.FeitThompson.OddOrder.CliffordConjugateDirectSumBasis
import CFSG.FeitThompson.Representations.ExtraspecialQuotientAlternatingForm
import CFSG.FeitThompson.Representations.CoprimeAbelianWeightDecomposition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.ExtraspecialWeight

open CFSG.FeitThompson CFSG.FeitThompson.Representation

universe u v w

variable {p n : ℕ} {P : Type u} [Group P] {B : Subgroup P} {k : Type v} [Field k]
  {V : Type w} [AddCommGroup V] [Module k V] {ρ : Representation k P V} {lam : ↥B →* kˣ} {v : V}

theorem char_apply_congr (lam : ↥B →* kˣ) {x y : P} (hx : x ∈ B) (hy : y ∈ B) (h : x = y) :
    lam ⟨x, hx⟩ = lam ⟨y, hy⟩ := by subst h; rfl

theorem isMulCommutative_of_centralizer_eq (hCB : Subgroup.centralizer (B : Set P) = B) :
    IsMulCommutative ↥B := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : (x : P) ∈ Subgroup.centralizer (B : Set P) := by rw [hCB]; exact x.2
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hx (y : P) y.2).symm)

theorem nontrivial_of_isIrreducible (hirr : ρ.IsIrreducible) : Nontrivial V := by
  have h : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  have hb : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
  have ht : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
  have h2 : (⊥ : Submodule k V) ≠ ⊤ := fun hc => h (Subrepresentation.ext (by rw [hb, ht, hc]))
  rcases subsingleton_or_nontrivial V with hs | hn
  · exact absurd (Subsingleton.elim _ _) h2
  · exact hn

theorem finiteDimensional_of_isIrreducible [Finite P] (hirr : ρ.IsIrreducible) :
    FiniteDimensional k V := by
  have := nontrivial_of_isIrreducible hirr
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  set W : Submodule k V := Submodule.span k (Set.range fun g : P => ρ g x) with hW
  have hmem : x ∈ W := Submodule.subset_span ⟨1, by simp⟩
  have htop : W = ⊤ := by
    refine eq_top_of_isIrreducible_of_map_le hirr (fun g => ?_) (fun hc => hx ?_)
    · rw [hW, Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro y ⟨z, ⟨h, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      change ρ (g * h) x = ρ g (ρ h x)
      rw [map_mul]; rfl
    · rw [hc] at hmem; simpa using hmem
  have hfin : Module.Finite k W := by
    rw [hW]; exact Module.Finite.span_of_finite k (Set.finite_range _)
  rw [htop] at hfin
  exact Module.Finite.equiv Submodule.topEquiv

theorem apply_ne_zero (t : P) (hv : v ≠ 0) : ρ t v ≠ 0 := by
  intro h
  refine hv ?_
  have h2 : ρ t⁻¹ (ρ t v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← h2, h, map_zero]

theorem exists_weightVector_centerChar_eq (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hBab : IsMulCommutative ↥B) [IsAlgClosed k] (hp : (p : k) ≠ 0) (hirr : ρ.IsIrreducible)
    (zeta : ↥(Subgroup.center P) →* kˣ)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w) :
    ∃ (lam : ↥B →* kˣ) (v : V), v ≠ 0 ∧ (∀ b : ↥B, ρ (b : P) v = (lam b : k) • v) ∧
      centerChar hZB lam = zeta := by
  have hfin := hP.finite
  have hfd := finiteDimensional_of_isIrreducible hirr
  have hnt := nontrivial_of_isIrreducible hirr
  let _ : CommGroup ↥B := IsMulCommutative.instCommGroup
  have hcard : (Nat.card ↥B : k) ≠ 0 := by
    have := Fact.mk hP.prime
    obtain ⟨m, hm⟩ := (hP.isPGroup.to_subgroup B).exists_card_eq
    rw [hm]; push_cast; exact pow_ne_zero _ hp
  have hsup := iSup_characterSpace_eq_top (MonoidHom.comp ρ B.subtype) hcard
  have hex : ∃ χ : ↥B →* kˣ, characterSpace (MonoidHom.comp ρ B.subtype) χ ≠ ⊥ := by
    by_contra hc
    push Not at hc
    rw [show (⨆ χ : ↥B →* kˣ, characterSpace (MonoidHom.comp ρ B.subtype) χ) = ⊥ from
      iSup_eq_bot.2 hc] at hsup
    exact absurd hsup.symm (by simp)
  obtain ⟨lam, hlam⟩ := hex
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hlam
  rw [mem_characterSpace_iff] at hv
  refine ⟨lam, v, hv0, fun b => hv b, MonoidHom.ext fun z => Units.ext ?_⟩
  have key : ((centerChar hZB lam z : kˣ) : k) • v = ((zeta z : kˣ) : k) • v := by
    rw [centerChar_apply, ← hz z v, ← hv ⟨(z : P), hZB z.2⟩]
    rfl
  exact smul_left_injective k hv0 key

def weightConj (hBn : B.Normal) (lam : ↥B →* kˣ) (t : P) : ↥B →* kˣ :=
  lam.comp (conjHom hBn t)

theorem weightConj_apply_mk (hBn : B.Normal) (lam : ↥B →* kˣ) (t : P) {b : P} (hb : b ∈ B)
    (hb' : t⁻¹ * b * t ∈ B) : weightConj hBn lam t ⟨b, hb⟩ = lam ⟨t⁻¹ * b * t, hb'⟩ :=
  congrArg lam (Subtype.ext (coe_conjHom_apply hBn t ⟨b, hb⟩))

@[simp]
theorem weightConj_one (hBn : B.Normal) (lam : ↥B →* kˣ) : weightConj hBn lam 1 = lam := by
  refine MonoidHom.ext fun b => ?_
  rw [weightConj_apply_mk hBn lam 1 b.2 (by simp)]
  exact char_apply_congr lam _ b.2 (by group)

theorem weightConj_inv_mul_of_eq (hBn : B.Normal) {t s : P}
    (h : weightConj hBn lam t = weightConj hBn lam s) :
    weightConj hBn lam (s⁻¹ * t) = lam := by
  refine MonoidHom.ext fun b => ?_
  set c : P := s * (b : P) * s⁻¹ with hcdef
  have hc : c ∈ B := hBn.conj_mem (b : P) b.2 s
  have h1 : t⁻¹ * c * t ∈ B := hBn.conj_mem' c hc t
  have h2 : s⁻¹ * c * s ∈ B := hBn.conj_mem' c hc s
  have hkey : weightConj hBn lam t ⟨c, hc⟩ = weightConj hBn lam s ⟨c, hc⟩ :=
    DFunLike.congr_fun h ⟨c, hc⟩
  rw [weightConj_apply_mk hBn lam t hc h1, weightConj_apply_mk hBn lam s hc h2,
    char_apply_congr lam h2 b.2 (by rw [hcdef]; group)] at hkey
  rw [weightConj_apply_mk hBn lam (s⁻¹ * t) b.2 (hBn.conj_mem' _ b.2 _),
    char_apply_congr lam (hBn.conj_mem' _ b.2 (s⁻¹ * t)) h1 (by rw [hcdef]; group), hkey]

theorem weightConj_eq_self_iff_mem (hP : IsExtraspecial p P) {hZB : Subgroup.center P ≤ B}
    (hBn : B.Normal) (hCB : Subgroup.centralizer (B : Set P) = B)
    (hnt : centerChar hZB lam ≠ 1) {t : P} : weightConj hBn lam t = lam ↔ t ∈ B := by
  have hstab := setOf_forall_conj_apply_eq_eq_coe (hZB := hZB) (lam := lam) hP hCB hnt
  have hiff : t ∈ {t : P | ∀ (b : P) (hb : b ∈ B) (hb' : t⁻¹ * b * t ∈ B),
      lam ⟨t⁻¹ * b * t, hb'⟩ = lam ⟨b, hb⟩} ↔ t ∈ (B : Set P) := by rw [hstab]
  rw [← SetLike.mem_coe, ← hiff]
  refine ⟨fun h b hb hb' => ?_, fun h => MonoidHom.ext fun b => ?_⟩
  · rw [← weightConj_apply_mk hBn lam t hb hb', h]
  · rw [weightConj_apply_mk hBn lam t b.2 (hBn.conj_mem' _ b.2 t)]
    exact h (b : P) b.2 (hBn.conj_mem' _ b.2 t)

theorem linearIndependent_translate (hP : IsExtraspecial p P) {hZB : Subgroup.center P ≤ B}
    (hCB : Subgroup.centralizer (B : Set P) = B) (hnt : centerChar hZB lam ≠ 1)
    (hv0 : v ≠ 0) (hv : ∀ b : ↥B, ρ (b : P) v = (lam b : k) • v) {ι : Type*} (T : ι → P)
    (hT : Function.Injective fun i => (QuotientGroup.mk (T i) : P ⧸ B)) :
    LinearIndependent k fun i => ρ (T i) v := by
  have hcl := hP.commutator_le_center
  have hBn := normal_of_commutator_le_center hcl hZB
  have hBab := isMulCommutative_of_centralizer_eq hCB
  let _ : CommGroup ↥B := IsMulCommutative.instCommGroup
  have hwinj : Function.Injective fun i => weightConj hBn lam (T i) := by
    intro i j hij
    refine hT ?_
    have h2 : (T j)⁻¹ * T i ∈ B :=
      (weightConj_eq_self_iff_mem hP (hZB := hZB) hBn hCB hnt).1
        (weightConj_inv_mul_of_eq hBn hij)
    exact (QuotientGroup.eq.2 h2).symm
  refine linearIndependent_of_mem_characterSpace (MonoidHom.comp ρ B.subtype) hwinj
    (fun i => ?_) (fun i => apply_ne_zero _ hv0)
  rw [mem_characterSpace_iff]
  intro b
  have h1 : ((MonoidHom.comp ρ B.subtype) b) (ρ (T i) v) = ρ ((b : P) * T i) v := by
    change ρ (b : P) (ρ (T i) v) = _
    rw [map_mul]; rfl
  rw [h1, show (b : P) * T i = T i * ((T i)⁻¹ * (b : P) * T i) by group, map_mul]
  change ρ (T i) (ρ ((T i)⁻¹ * (b : P) * T i) v) = _
  rw [hv ⟨(T i)⁻¹ * (b : P) * T i, hBn.conj_mem' _ b.2 _⟩, map_smul,
    weightConj_apply_mk hBn lam (T i) b.2 (hBn.conj_mem' _ b.2 _)]

theorem mem_span_translate {ι : Type*} (T : ι → P)
    (hTs : Function.Surjective fun i => (QuotientGroup.mk (T i) : P ⧸ B))
    (hv : ∀ b : ↥B, ρ (b : P) v = (lam b : k) • v) (g : P) :
    ρ g v ∈ Submodule.span k (Set.range fun i => ρ (T i) v) := by
  obtain ⟨i, hi⟩ := hTs (QuotientGroup.mk g)
  have hb : (T i)⁻¹ * g ∈ B := QuotientGroup.eq.1 hi
  have key : ρ g v = (lam ⟨(T i)⁻¹ * g, hb⟩ : k) • ρ (T i) v := by
    have hg : ρ g = (ρ (T i) : Module.End k V) * ρ ((T i)⁻¹ * g) := by
      rw [← map_mul]; congr 1; group
    rw [hg, Module.End.mul_apply, hv ⟨(T i)⁻¹ * g, hb⟩, map_smul]
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem span_translate_eq_top (hirr : ρ.IsIrreducible) {ι : Type*} (T : ι → P)
    (hTs : Function.Surjective fun i => (QuotientGroup.mk (T i) : P ⧸ B))
    (hv0 : v ≠ 0) (hv : ∀ b : ↥B, ρ (b : P) v = (lam b : k) • v) [Nonempty ι] :
    Submodule.span k (Set.range fun i => ρ (T i) v) = ⊤ := by
  set W : Submodule k V := Submodule.span k (Set.range fun i => ρ (T i) v) with hW
  refine eq_top_of_isIrreducible_of_map_le hirr (fun g => ?_) ?_
  · rw [hW, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
    have h : (ρ g) ((fun i => ρ (T i) v) i) = ρ (g * T i) v := by
      change ρ g (ρ (T i) v) = _
      rw [map_mul]; rfl
    rw [h]
    exact mem_span_translate T hTs hv _
  · intro hc
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h1 : ρ (T i) v ∈ W := Submodule.subset_span ⟨i, rfl⟩
    rw [hc] at h1
    exact apply_ne_zero (T i) hv0 (by simpa using h1)

noncomputable def cosetBasis (hP : IsExtraspecial p P) {hZB : Subgroup.center P ≤ B}
    (hCB : Subgroup.centralizer (B : Set P) = B) (hnt : centerChar hZB lam ≠ 1)
    (hirr : ρ.IsIrreducible) (hv0 : v ≠ 0) (hv : ∀ b : ↥B, ρ (b : P) v = (lam b : k) • v)
    {ι : Type*} (T : ι → P)
    (hT : Function.Bijective fun i => (QuotientGroup.mk (T i) : P ⧸ B)) :
    Module.Basis ι k V :=
  have : Nonempty ι := ⟨(hT.surjective (QuotientGroup.mk 1)).choose⟩
  Module.Basis.mk (linearIndependent_translate hP hCB hnt hv0 hv T hT.injective)
    (span_translate_eq_top hirr T hT.surjective hv0 hv).ge

@[simp]
theorem cosetBasis_apply (hP : IsExtraspecial p P) {hZB : Subgroup.center P ≤ B}
    (hCB : Subgroup.centralizer (B : Set P) = B) (hnt : centerChar hZB lam ≠ 1)
    (hirr : ρ.IsIrreducible) (hv0 : v ≠ 0) (hv : ∀ b : ↥B, ρ (b : P) v = (lam b : k) • v)
    {ι : Type*} (T : ι → P)
    (hT : Function.Bijective fun i => (QuotientGroup.mk (T i) : P ⧸ B)) (i : ι) :
    cosetBasis hP hCB hnt hirr hv0 hv T hT i = ρ (T i) v := by
  rw [cosetBasis, Module.Basis.mk_apply]

theorem finrank_eq_index (hP : IsExtraspecial p P) {hZB : Subgroup.center P ≤ B}
    (hCB : Subgroup.centralizer (B : Set P) = B) (hnt : centerChar hZB lam ≠ 1)
    (hirr : ρ.IsIrreducible) (hv0 : v ≠ 0) (hv : ∀ b : ↥B, ρ (b : P) v = (lam b : k) • v) :
    Module.finrank k V = B.index := by
  have hT : Function.Bijective fun q : P ⧸ B => (QuotientGroup.mk (Quotient.out q) : P ⧸ B) := by
    have hid : (fun q : P ⧸ B => (QuotientGroup.mk (Quotient.out q) : P ⧸ B)) = id := by
      funext q; simp [QuotientGroup.mk]
    rw [hid]; exact Function.bijective_id
  rw [Module.finrank_eq_nat_card_basis
    (cosetBasis hP hCB hnt hirr hv0 hv (fun q : P ⧸ B => Quotient.out q) hT),
    Subgroup.index_eq_card]

theorem finrank_eq_pow (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    [IsAlgClosed k] (hp : (p : k) ≠ 0) (hirr : ρ.IsIrreducible)
    (zeta : ↥(Subgroup.center P) →* kˣ) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w) :
    Module.finrank k V = p ^ n := by
  obtain ⟨lam, v, hv0, hv, hlam⟩ := exists_weightVector_centerChar_eq hP hZB
    (isMulCommutative_of_centralizer_eq hCB) hp hirr zeta hz
  rw [finrank_eq_index hP hCB (lam := lam) (hlam ▸ hzeta) hirr hv0 hv, hPB]

end CFSG.FeitThompson.ExtraspecialWeight
