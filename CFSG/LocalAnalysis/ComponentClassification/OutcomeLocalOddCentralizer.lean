module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup

section Images

variable {F A : Type*} [Group F] [Group A]

theorem map_conjugate (η : F →* A) (H : Subgroup F) (g : F) :
    (CFSG.conjugate H g).map η = CFSG.conjugate (H.map η) (η g) := by
  unfold CFSG.conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem conjugate_le_of_le_normal {W H : Subgroup F} [hW : W.Normal] (hHW : H ≤ W) (g : F) :
    CFSG.conjugate H g ≤ W := by
  rintro _ ⟨h, hh, rfl⟩
  simpa using hW.conj_mem h (hHW hh) g⁻¹

variable {η : F →* A}

theorem eq_of_inf_ker_eq_bot {W : Subgroup F} (hWK : W ⊓ η.ker = ⊥) {x y : F} (hx : x ∈ W)
    (hy : y ∈ W) (hxy : η x = η y) : x = y := by
  have h : x⁻¹ * y ∈ W ⊓ η.ker := mem_inf.mpr
    ⟨mul_mem (inv_mem hx) hy, by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]⟩
  rw [hWK, mem_bot] at h
  exact inv_mul_eq_one.mp h

theorem comap_centralizer_map {W L : Subgroup F} [hW : W.Normal] (hWK : W ⊓ η.ker = ⊥)
    (hLW : L ≤ W) : (centralizer (L.map η : Set A)).comap η = centralizer (L : Set F) := by
  ext f
  rw [mem_comap, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hf l hl
    have h1 : η l * η f = η f * η l := hf (η l) ⟨l, hl, rfl⟩
    have h2 : f * l * f⁻¹ = l := eq_of_inf_ker_eq_bot hWK (hW.conj_mem l (hLW hl) f) (hLW hl)
      (by rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right])
    calc l * f = f * l * f⁻¹ * f := by rw [h2]
      _ = f * l := by group
  · rintro hf _ ⟨l, hl, rfl⟩
    rw [← map_mul, hf l hl, map_mul]

theorem comap_normalizer_map {W L : Subgroup F} [hW : W.Normal] (hWK : W ⊓ η.ker = ⊥)
    (hLW : L ≤ W) : (normalizer (L.map η : Set A)).comap η = normalizer (L : Set F) := by
  refine le_antisymm (fun f hf => ?_) (fun f hf => le_normalizer_map η ⟨f, hf, rfl⟩)
  rw [mem_comap, mem_normalizer_iff] at hf
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨l, hl, hle⟩ := (hf (η h)).mp ⟨h, hh, rfl⟩
    have : l = f * h * f⁻¹ := eq_of_inf_ker_eq_bot hWK (hLW hl) (hW.conj_mem h (hLW hh) f)
      (by rw [hle, map_mul, map_mul, map_inv])
    exact this ▸ hl
  · intro hh
    obtain ⟨l, hl, hle⟩ := (hf (η h)).mpr ⟨f * h * f⁻¹, hh, by rw [map_mul, map_mul, map_inv]⟩
    have hhW : h ∈ W := by
      have := hW.conj_mem _ (hLW hh) f⁻¹
      rwa [inv_inv, show f⁻¹ * (f * h * f⁻¹) * f = h by group] at this
    exact (eq_of_inf_ker_eq_bot hWK (hLW hl) hhW hle) ▸ hl

theorem comap_normalizer_map_of_ker_le {H : Subgroup F} (hη : Function.Surjective η)
    (hK : η.ker ≤ H) : (normalizer (H.map η : Set A)).comap η = normalizer (H : Set F) := by
  rw [comap_normalizer_eq_of_surjective _ hη, comap_map_eq, sup_eq_left.mpr hK]

theorem map_inf_of_ker_le {X Y : Subgroup F} (hη : Function.Surjective η) (hX : η.ker ≤ X)
    (hY : η.ker ≤ Y) : (X ⊓ Y).map η = X.map η ⊓ Y.map η := by
  rw [← map_comap_eq_self_of_surjective hη (X.map η ⊓ Y.map η), comap_inf, comap_map_eq,
    comap_map_eq, sup_eq_left.mpr hX, sup_eq_left.mpr hY]

theorem exists_mulEquiv_map_of_inf_ker_eq_bot {L : Subgroup F} (hLK : L ⊓ η.ker = ⊥) :
    ∃ e : L ≃* L.map η, ∀ x : L, (e x : A) = η x := by
  have hinj : Function.Injective (η.comp L.subtype) := fun x y hxy =>
    Subtype.ext (eq_of_inf_ker_eq_bot hLK x.2 y.2 hxy)
  have hrange : (η.comp L.subtype).range = L.map η := by
    rw [MonoidHom.range_comp, range_subtype]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun x => rfl⟩

end Images

section Semisimple

variable {F : Type*} [Group F] {ι : Type*} {S : ι → Subgroup F}

theorem iSup_le_normalizer
    (hcomm : Pairwise fun i j => ∀ x y : F, x ∈ S i → y ∈ S j → Commute x y) (i : ι) :
    (⨆ j, S j) ≤ normalizer (S i : Set F) := by
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    exact le_normalizer
  · exact le_trans (fun y hy => mem_centralizer_iff.mpr fun h hh => (hcomm hji y h hy hh).eq.symm)
      (centralizer_le_normalizer _)

theorem isComponent_factor (hS : ∀ i, IsSimpleGroup (S i))
    (hSab : ∀ i, ∃ a b : S i, a * b ≠ b * a)
    (hcomm : Pairwise fun i j => ∀ x y : F, x ∈ S i → y ∈ S j → Commute x y)
    [hW : (⨆ j, S j).Normal] (i : ι) : CFSG.IsComponent (S i) := by
  have := hS i
  refine ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (hSab i)).1,
    IsSubnormal.step (S i) (⨆ j, S j) (le_iSup S i) hW.isSubnormal ?_⟩
  exact (normal_subgroupOf_iff_le_normalizer (le_iSup S i)).mpr (iSup_le_normalizer hcomm i)

theorem le_centralizer_iSup {X : Subgroup F} (h : ∀ i, ⁅S i, X⁆ = ⊥) :
    X ≤ centralizer ((⨆ i, S i : Subgroup F) : Set F) :=
  le_centralizer_iff.mpr (iSup_le fun i => commutator_eq_bot_iff_le_centralizer.mp (h i))

theorem iSup_inf_centralizer_eq_bot [Finite ι] (hS : ∀ i, IsSimpleGroup (S i))
    (hSab : ∀ i, ∃ a b : S i, a * b ≠ b * a)
    (hcomm : Pairwise fun i j => ∀ x y : F, x ∈ S i → y ∈ S j → Commute x y)
    (hind : iSupIndep S) :
    (⨆ i, S i) ⊓ centralizer ((⨆ i, S i : Subgroup F) : Set F) = ⊥ := by
  classical
  obtain ⟨e, he⟩ := CFSG.LocalCores.exists_mulEquiv_pi_iSup S hcomm hind
  rw [eq_bot_iff]
  rintro w ⟨hw, hwc⟩
  rw [mem_bot]
  obtain ⟨x, hx⟩ := e.surjective ⟨w, hw⟩
  have hxw : (e x : F) = w := congrArg Subtype.val hx
  have hxi : ∀ i, x i = 1 := by
    intro i
    have := hS i
    have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (hSab i)).2
    have hc : x i ∈ center (S i) := by
      rw [mem_center_iff]
      intro s
      have h1 : (e (Pi.mulSingle i s) : F) = s := by
        rw [he i (Pi.mulSingle i s) (fun j hj => by simp [hj]), Pi.mulSingle_eq_same]
      have h2 : (s : F) * w = w * s := (mem_centralizer_iff.mp hwc) s (mem_iSup_of_mem i s.2)
      have h3 : e (Pi.mulSingle i s * x) = e (x * Pi.mulSingle i s) := by
        apply Subtype.ext
        rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, h1, hxw]
        exact h2
      have h4 := congrFun (e.injective h3) i
      simpa using h4
    rw [hZ, mem_bot] at hc
    exact hc
  rw [← hxw, show x = 1 from funext hxi, map_one, Subgroup.coe_one]

end Semisimple

section Involutions

variable {F : Type*} [Group F]

theorem exists_mul_mem_centralizer_of_odd {K : Subgroup F} [K.Normal] (hK : Odd (Nat.card K))
    {a f : F} (ha : a ^ 2 = 1) (hf : f * a * f⁻¹ * a⁻¹ ∈ K) :
    ∃ k ∈ K, k * f ∈ centralizer ({a} : Set F) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha])
  set a' := f * a * f⁻¹ with ha'
  set k₁ := a⁻¹ * a' with hk₁
  have hk₁K : k₁ ∈ K := by
    have := (inferInstance : K.Normal).conj_mem _ hf a⁻¹
    rwa [show a⁻¹ * (f * a * f⁻¹ * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * a' by rw [ha']; group] at this
  have ha'sq : a' * a' = 1 := by
    rw [ha', show f * a * f⁻¹ * (f * a * f⁻¹) = f * (a * a) * f⁻¹ by group, ← sq, ha, mul_one,
      mul_inv_cancel]
  have hinv : a * k₁ * a⁻¹ = k₁⁻¹ := by
    have h : a * k₁ * (a * k₁) = 1 := by
      rw [hk₁, mul_inv_cancel_left]
      exact ha'sq
    have h' : a * k₁ * a * k₁ = 1 := by rw [← h]; group
    rw [hainv]
    exact mul_eq_one_iff_eq_inv.mp h'
  have hodd : Odd (orderOf k₁) := Odd.of_dvd_nat hK (Subgroup.orderOf_dvd_natCard K hk₁K)
  obtain ⟨t, ht⟩ := hodd
  set c := k₁ ^ (t + 1) with hc
  have hcK : c ∈ K := pow_mem hk₁K _
  have hcc : c * c = k₁ := by
    rw [hc, ← pow_add, show t + 1 + (t + 1) = orderOf k₁ + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hac : a * c * a⁻¹ = c⁻¹ := by
    rw [hc, ← conj_pow, hinv, inv_pow]
  refine ⟨c, hcK, ?_⟩
  rw [mem_centralizer_singleton_iff]
  have hkey : c * a' * c⁻¹ = a := by
    have : a' = a * (c * c) := by rw [hcc, hk₁]; group
    rw [this]
    calc c * (a * (c * c)) * c⁻¹ = c * (a * c * a⁻¹) * a := by group
      _ = a := by rw [hac]; group
  calc c * f * a = c * a' * c⁻¹ * (c * f) := by rw [ha']; group
    _ = a * (c * f) := by rw [hkey]

end Involutions

section Standard

variable {F : Type*} [Group F]

theorem isStandardSubgroup_map {K W L : Subgroup F} [hKn : K.Normal] [hWn : W.Normal]
    (hKodd : Odd (Nat.card K)) (hWK : W ⊓ K = ⊥) (hKW : K ≤ centralizer (W : Set F))
    (hLW : L ≤ W) (hL : CFSG.IsStandardSubgroup L) :
    CFSG.IsStandardSubgroup (L.map (QuotientGroup.mk' K)) := by
  set η := QuotientGroup.mk' K with hη
  have hηs : Function.Surjective η := QuotientGroup.mk'_surjective K
  have hker : η.ker = K := QuotientGroup.ker_mk' K
  have hWK' : W ⊓ η.ker = ⊥ := by rw [hker]; exact hWK
  obtain ⟨hq, heven, hodd, hnorm, hcomm⟩ := hL
  set CL := centralizer (L : Set F) with hCL
  have hKCL : K ≤ CL := hKW.trans (centralizer_le hLW)
  have hKCL' : η.ker ≤ CL := by rw [hker]; exact hKCL
  have hpre : (centralizer (L.map η : Set (F ⧸ K))).comap η = CL := comap_centralizer_map hWK' hLW
  have hC0 : centralizer (L.map η : Set (F ⧸ K)) = CL.map η := by
    rw [← hpre, map_comap_eq_self_of_surjective hηs]
  have hNC : (normalizer (CL.map η : Set (F ⧸ K))).comap η = normalizer (CL : Set F) :=
    comap_normalizer_map_of_ker_le hηs hKCL'
  have hNL : (normalizer (L.map η : Set (F ⧸ K))).comap η = normalizer (L : Set F) :=
    comap_normalizer_map hWK' hLW
  obtain ⟨e, -⟩ := exists_mulEquiv_map_of_inf_ker_eq_bot
    (eq_bot_iff.mpr ((inf_le_inf_right _ hLW).trans hWK'.le))
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_, ?_, ?_⟩
  ·
    rw [hC0]
    have hcard : Nat.card (K.subgroupOf CL) * Nat.card (CL.map η) = Nat.card CL := by
      have h1 := (η.comp CL.subtype).ker.card_mul_index
      have h2 : (η.comp CL.subtype).ker = K.subgroupOf CL := by
        rw [← MonoidHom.comap_ker, hker]
        rfl
      rw [Subgroup.index_ker, MonoidHom.range_comp, range_subtype, h2] at h1
      exact h1
    rw [← hcard, Nat.card_congr (subgroupOfEquivOfLe hKCL).toEquiv] at heven
    rcases Nat.even_mul.mp heven with h | h
    · exact absurd hKodd (Nat.not_odd_iff_even.mpr h)
    · exact h
  · intro g₀ hg₀
    obtain ⟨g, rfl⟩ := hηs g₀
    rw [hC0] at hg₀ ⊢
    have hg : g ∉ normalizer (CL : Set F) := fun hg => hg₀ (by
      rw [← hNC] at hg
      exact hg)
    have hKg : η.ker ≤ CFSG.conjugate CL g := by
      rw [hker]
      intro k hk
      refine ⟨g * k * g⁻¹, hKCL (hKn.conj_mem k hk g), ?_⟩
      simp [mul_assoc]
    rw [← map_conjugate, ← map_inf_of_ker_le hηs hKCL' hKg]
    exact Odd.of_dvd_nat (hodd g hg) (card_map_dvd _ _)
  · rw [hC0]
    apply comap_injective hηs
    rw [hNC, hNL, hnorm]
  · intro g₀ hbot
    obtain ⟨g, rfl⟩ := hηs g₀
    rw [← map_conjugate, ← map_commutator, Subgroup.map_eq_bot_iff, hker] at hbot
    have hcW : ⁅L, CFSG.conjugate L g⁆ ≤ W :=
      (commutator_mono hLW (conjugate_le_of_le_normal hLW g)).trans (commutator_le_left W W)
    exact hcomm g (eq_bot_iff.mpr ((le_inf hcW hbot).trans hWK.le))

end Standard

section Main

variable {F : Type*} [Group F] [Finite F]

theorem odd_centralizer_semisimple_layer_faithful_standard_quotient {ι : Type*} [Finite ι]
    (S : ι → Subgroup F) (hS : ∀ i, IsSimpleGroup (S i)) (hSab : ∀ i, ∃ a b : S i, a * b ≠ b * a)
    (hcomm : Pairwise fun i j => ∀ x y : F, x ∈ S i → y ∈ S j → Commute x y)
    (hind : iSupIndep S) {W : Subgroup F} (hSW : ⨆ i, S i = W) [hWn : W.Normal] (hW1 : W ≠ ⊥)
    (hodd : Odd (Nat.card (centralizer (W : Set F)))) :
    CFSG.pPrimeCore 2 F = centralizer (W : Set F) ∧ W ⊓ CFSG.pPrimeCore 2 F = ⊥ ∧
    CFSG.layer F = W ∧ CFSG.pCore 2 F = ⊥ ∧
    (∃ e : W ≃* W.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)),
      ∀ w : W, (e w : F ⧸ CFSG.pPrimeCore 2 F) = QuotientGroup.mk' (CFSG.pPrimeCore 2 F) w) ∧
    centralizer (W.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) :
      Set (F ⧸ CFSG.pPrimeCore 2 F)) = ⊥ ∧
    CFSG.layer (F ⧸ CFSG.pPrimeCore 2 F) = W.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) ∧
    CFSG.generalizedFitting (F ⧸ CFSG.pPrimeCore 2 F) =
      W.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) ∧
    CFSG.fittingSubgroup (F ⧸ CFSG.pPrimeCore 2 F) = ⊥ ∧
    CFSG.pPrimeCore 2 (F ⧸ CFSG.pPrimeCore 2 F) = ⊥ ∧
    CFSG.pCore 2 (F ⧸ CFSG.pPrimeCore 2 F) = ⊥ ∧
    (MulAut.conjNormal : F →* MulAut W).ker = CFSG.pPrimeCore 2 F ∧
    (MulAut.conj : W →* MulAut W).range ≤ (MulAut.conjNormal : F →* MulAut W).range ∧
    (∃ e : F ⧸ CFSG.pPrimeCore 2 F ≃* (MulAut.conjNormal : F →* MulAut W).range,
      ∀ f : F, (e (QuotientGroup.mk' (CFSG.pPrimeCore 2 F) f) : MulAut W) =
        MulAut.conjNormal f) ∧
    (∀ L : Subgroup F, L ≤ W →
      (centralizer (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) :
          Set (F ⧸ CFSG.pPrimeCore 2 F))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) =
        centralizer (L : Set F) ∧
      (normalizer (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) :
          Set (F ⧸ CFSG.pPrimeCore 2 F))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) =
        normalizer (L : Set F)) ∧
    (∀ L : Subgroup F, L ≤ W →
      ∃ e : L ≃* L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)),
        (∀ x : L, (e x : F ⧸ CFSG.pPrimeCore 2 F) = QuotientGroup.mk' (CFSG.pPrimeCore 2 F) x) ∧
        ∃ e' : L ⧸ center L ≃* L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) ⧸
            center (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F))),
          ∀ x : L, e' (x : L ⧸ center L) = ((e x : L.map (QuotientGroup.mk' _)) :
            L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) ⧸
              center (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F))))) ∧
    (∀ L : Subgroup F, L ≤ W → CFSG.IsStandardSubgroup L →
      CFSG.IsStandardSubgroup (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)))) ∧
    (∀ L : Subgroup F, L ≤ W → ∀ a : F, a ∈ centralizer (L : Set F) → orderOf a = 2 →
      CFSG.IsComponent (L.subgroupOf (centralizer ({a} : Set F))) →
      orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 2 F) a) = 2 ∧
      centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 2 F) a} : Set (F ⧸ CFSG.pPrimeCore 2 F)) =
        (centralizer ({a} : Set F)).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) ∧
      CFSG.IsComponent ((L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F))).subgroupOf
        (centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 2 F) a} :
          Set (F ⧸ CFSG.pPrimeCore 2 F))))) ∧
    ∀ L : Subgroup F, L ≤ W → (⨆ (e : F) (_ : e ∈ CFSG.layer F), CFSG.conjugate L e) = W →
      (⨆ f : F, CFSG.conjugate L f) = W ∧
      (⨆ g : F ⧸ CFSG.pPrimeCore 2 F,
        CFSG.conjugate (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F))) g) =
        W.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 F)) := by
  subst hSW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := ⨆ i, S i with hWdef
  set K := CFSG.pPrimeCore 2 F with hKdef
  set η := QuotientGroup.mk' K with hηdef
  have hηs : Function.Surjective η := QuotientGroup.mk'_surjective K
  have hker : η.ker = K := QuotientGroup.ker_mk' K
  set C := centralizer (W : Set F) with hCdef
  have hcomp : ∀ i, CFSG.IsComponent (S i) := isComponent_factor hS hSab hcomm
  have hSW : ∀ i, S i ≤ W := le_iSup S
  have hS1 : ∀ i, S i ≠ ⊥ := fun i h => by
    have := hS i
    have : Nontrivial (S i) := IsSimpleGroup.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot (S i)).mp this h
  have hsolv : ∀ R : Subgroup F, R.Normal → Group.IsSolvable R → R ≤ C := fun R hRn hRs =>
    le_centralizer_iSup fun i =>
      (CFSG.LocalCores.component_solvable_centralizer hRs hRn.isSubnormal).1 _ (hcomp i)
  have hKodd : Odd (Nat.card K) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hCK : C ≤ K := le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩
  have hKC : K ≤ C := hsolv K inferInstance (CFSG.Milestones.odd_order_solvable hKodd)
  have hKeq : K = C := le_antisymm hKC hCK
  have hWK : W ⊓ K = ⊥ := by
    rw [hKeq]
    exact iSup_inf_centralizer_eq_bot hS hSab hcomm hind
  have hWK' : W ⊓ η.ker = ⊥ := by rw [hker]; exact hWK
  have hCsolv : Group.IsSolvable C := CFSG.Milestones.odd_order_solvable hodd
  have hnotC : ∀ Q : Subgroup F, CFSG.IsComponent Q → ¬ Q ≤ C := fun Q hQ hQC => by
    have : Group.IsSolvable Q :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hQC)
    have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ.1
    have : Group.IsPerfect Q := hQ.1.1
    exact Group.IsPerfect.not_isSolvable Q inferInstance
  have hlayer : CFSG.layer F = W := by
    refine le_antisymm (sSup_le fun Q hQ => ?_) (iSup_le fun i => CFSG.LocalCores.component_le_layer
      (hcomp i))
    by_contra hQW
    have hc : ∀ i, ⁅S i, Q⁆ = ⊥ := fun i =>
      ((CFSG.LocalCores.distinct_components_commute (hcomp i) hQ).resolve_left fun h =>
        hQW (h ▸ hSW i))
    exact hnotC Q hQ (le_centralizer_iSup hc)
  have hO2 : CFSG.pCore 2 F = ⊥ := by
    have hp : IsPGroup 2 (CFSG.pCore 2 F) := CFSG.pCore_isPGroup
    have : Group.IsNilpotent (CFSG.pCore 2 F) := hp.isNilpotent
    have hle : CFSG.pCore 2 F ≤ C := hsolv _ CFSG.pCore_normal inferInstance
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [← Subgroup.card_eq_one, hn]
    cases n with
    | zero => rfl
    | succ n =>
      exfalso
      have hdvd : 2 ∣ Nat.card C := (dvd_pow_self 2 n.succ_ne_zero).trans
        (hn ▸ Subgroup.card_dvd_of_le hle)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  obtain ⟨eW, heW⟩ := exists_mulEquiv_map_of_inf_ker_eq_bot hWK'
  have hcent : ∀ L : Subgroup F, L ≤ W →
      (centralizer (L.map η : Set (F ⧸ K))).comap η = centralizer (L : Set F) :=
    fun L hLW => comap_centralizer_map hWK' hLW
  have hnorm : ∀ L : Subgroup F, L ≤ W →
      (normalizer (L.map η : Set (F ⧸ K))).comap η = normalizer (L : Set F) :=
    fun L hLW => comap_normalizer_map hWK' hLW
  have hCA : centralizer (W.map η : Set (F ⧸ K)) = ⊥ := by
    rw [← map_comap_eq_self_of_surjective hηs (centralizer (W.map η : Set (F ⧸ K))),
      hcent W le_rfl, ← hCdef, ← hKeq, hηdef, QuotientGroup.map_mk'_self]
  have hcompA : ∀ i, CFSG.IsComponent ((S i).map η) := fun i =>
    CFSG.LocalAnalysis.ComponentInitial.component_quotient_image (hcomp i) fun h =>
      hS1 i (eq_bot_iff.mpr ((le_inf (hSW i) h).trans hWK.le))
  have hW0 : W.map η = ⨆ i, (S i).map η := by rw [hWdef, Subgroup.map_iSup]
  have hsolvA : ∀ R : Subgroup (F ⧸ K), R.Normal → Group.IsSolvable R → R = ⊥ :=
    fun R hRn hRs => by
      rw [eq_bot_iff, ← hCA, hW0]
      exact le_centralizer_iSup fun i =>
        (CFSG.LocalCores.component_solvable_centralizer hRs hRn.isSubnormal).1 _ (hcompA i)
  have hlayerA : CFSG.layer (F ⧸ K) = W.map η := by
    refine le_antisymm (sSup_le fun Q hQ => ?_)
      (hW0 ▸ iSup_le fun i => CFSG.LocalCores.component_le_layer (hcompA i))
    by_contra hQW
    have hc : ∀ i, ⁅(S i).map η, Q⁆ = ⊥ := fun i =>
      ((CFSG.LocalCores.distinct_components_commute (hcompA i) hQ).resolve_left fun h =>
        hQW (h ▸ map_mono (hSW i)))
    have hQbot : Q ≤ ⊥ := hCA ▸ hW0 ▸ le_centralizer_iSup hc
    have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ.1
    exact (Subgroup.nontrivial_iff_ne_bot Q).mp this (le_bot_iff.mp hQbot)
  have hfitA : CFSG.fittingSubgroup (F ⧸ K) = ⊥ :=
    hsolvA _ CFSG.fittingSubgroup_normal inferInstance
  have hαker : (MulAut.conjNormal : F →* MulAut W).ker = K := by
    rw [hKeq]
    ext f
    rw [MonoidHom.mem_ker, mem_centralizer_iff]
    constructor
    · intro hf w hw
      have h := congrArg Subtype.val (MulEquiv.congr_fun hf ⟨w, hw⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc w * f = f * w * f⁻¹ * f := by rw [h]
        _ = f * w := by group
    · intro hf
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [MulAut.conjNormal_apply, MulAut.one_apply, ← hf w w.2, mul_inv_cancel_right]
  refine ⟨hKeq, hWK, hlayer, hO2, ⟨eW, heW⟩, hCA, hlayerA, ?_, hfitA, ?_, ?_, hαker, ?_, ?_,
    fun L hLW => ⟨hcent L hLW, hnorm L hLW⟩, ?_, ?_, ?_, ?_⟩
  ·
    rw [CFSG.generalizedFitting, hfitA, hlayerA, bot_sup_eq]
  ·
    have hodd' : Odd (Nat.card (CFSG.pPrimeCore 2 (F ⧸ K))) :=
      Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
    exact hsolvA _ CFSG.pPrimeCore_normal (CFSG.Milestones.odd_order_solvable hodd')
  ·
    have hp : IsPGroup 2 (CFSG.pCore 2 (F ⧸ K)) := CFSG.pCore_isPGroup
    have : Group.IsNilpotent (CFSG.pCore 2 (F ⧸ K)) := hp.isNilpotent
    exact hsolvA _ CFSG.pCore_normal inferInstance
  ·
    rintro _ ⟨w, rfl⟩
    exact ⟨(w : F), MulEquiv.ext fun x => Subtype.ext (by
      rw [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv])⟩
  ·
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
      (QuotientGroup.quotientKerEquivRange _), fun f => rfl⟩
  ·
    intro L hLW
    obtain ⟨e, he⟩ := exists_mulEquiv_map_of_inf_ker_eq_bot
      (eq_bot_iff.mpr ((inf_le_inf_right _ hLW).trans hWK'.le))
    exact ⟨e, he, QuotientGroup.congr _ _ e (map_center_eq e), fun x => rfl⟩
  ·
    intro L hLW hL
    exact isStandardSubgroup_map hKodd hWK (hKeq ▸ le_rfl) hLW hL
  ·
    intro L hLW a haL ha2 hLa
    have ha2' : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
    have haK : a ∉ K := fun haK => by
      have := Subgroup.orderOf_dvd_natCard K haK
      rw [ha2] at this
      exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr this)
    have hηa : orderOf (η a) = 2 := by
      apply orderOf_eq_prime
      · rw [← map_pow, ha2', map_one]
      · rw [hηdef, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
        exact haK
    have hCa : centralizer ({η a} : Set (F ⧸ K)) = (centralizer ({a} : Set F)).map η := by
      refine le_antisymm (fun y hy => ?_) (map_le_iff_le_comap.mpr fun x hx => ?_)
      · obtain ⟨f, rfl⟩ := hηs y
        rw [mem_centralizer_singleton_iff] at hy
        have hf : f * a * f⁻¹ * a⁻¹ ∈ K := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hy]
          group
        obtain ⟨k, hk, hkf⟩ := exists_mul_mem_centralizer_of_odd hKodd ha2' hf
        refine ⟨k * f, hkf, ?_⟩
        have hk' : k ∈ η.ker := by rw [hker]; exact hk
        rw [map_mul, MonoidHom.mem_ker.mp hk', one_mul]
      · rw [mem_comap, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          (mem_centralizer_singleton_iff.mp hx)]
    refine ⟨hηa, hCa, ?_⟩
    set Ca := centralizer ({a} : Set F) with hCa'
    set φ : Ca →* centralizer ({η a} : Set (F ⧸ K)) :=
      (MulEquiv.subgroupCongr hCa.symm).toMonoidHom.comp (η.subgroupMap Ca) with hφ
    have hφs : Function.Surjective φ :=
      (MulEquiv.subgroupCongr hCa.symm).surjective.comp (η.subgroupMap_surjective Ca)
    have hLCa : L ≤ Ca := fun l hl => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp haL) l hl)
    have hLφ : ¬ L.subgroupOf Ca ≤ φ.ker := fun h => by
      have : Nontrivial (L.subgroupOf Ca) := CFSG.LocalCores.isQuasisimple_nontrivial hLa.1
      refine (Subgroup.nontrivial_iff_ne_bot _).mp this (eq_bot_iff.mpr fun x hx => ?_)
      have hx1 : η x = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp (h hx))
        exact this
      have : (x : F) ∈ W ⊓ η.ker := ⟨hLW (mem_subgroupOf.mp hx), hx1⟩
      rw [hWK', mem_bot] at this
      exact mem_bot.mpr (Subtype.ext this)
    have hmap : (L.subgroupOf Ca).map φ = (L.map η).subgroupOf (centralizer ({η a} : Set _)) := by
      ext y
      rw [mem_map, mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, mem_subgroupOf.mp hx, rfl⟩
      · rintro ⟨l, hl, hly⟩
        exact ⟨⟨l, hLCa hl⟩, mem_subgroupOf.mpr hl, Subtype.ext hly⟩
    rw [← hmap]
    exact ⟨CFSG.LocalCores.isQuasisimple_map hLa.1 φ hLφ, hLa.2.map hφs⟩
  ·
    intro L hLW hgen
    have hF : (⨆ f : F, CFSG.conjugate L f) = W := by
      refine le_antisymm (iSup_le fun f => conjugate_le_of_le_normal hLW f) ?_
      calc W = ⨆ (e : F) (_ : e ∈ CFSG.layer F), CFSG.conjugate L e := hgen.symm
        _ ≤ ⨆ f : F, CFSG.conjugate L f :=
          iSup₂_le fun e _ => le_iSup (fun f => CFSG.conjugate L f) e
    refine ⟨hF, ?_⟩
    calc (⨆ g : F ⧸ K, CFSG.conjugate (L.map η) g)
        = ⨆ f : F, CFSG.conjugate (L.map η) (η f) := (hηs.iSup_comp _).symm
      _ = ⨆ f : F, (CFSG.conjugate L f).map η := iSup_congr fun f => (map_conjugate η L f).symm
      _ = (⨆ f : F, CFSG.conjugate L f).map η := (Subgroup.map_iSup η _).symm
      _ = W.map η := by rw [hF]

end Main

end CFSG.ComponentClassification.OutcomeLocal
