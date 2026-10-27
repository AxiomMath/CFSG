module

public import CFSG.ClassicalInvolution.Asc77.AscCX9
public import CFSG.ClassicalInvolution.Asc77.AscCX9T

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Pair

variable {G : Type} [Group G]

theorem centralizer_pair_mul (a b : G) :
    Subgroup.centralizer ({a, a * b} : Set G) = Subgroup.centralizer ({a, b} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨ha, hab⟩
    refine ⟨ha, ?_⟩
    calc b * g = a⁻¹ * (a * b * g) := by group
      _ = a⁻¹ * (g * (a * b)) := by rw [hab]
      _ = a⁻¹ * (g * a) * b := by group
      _ = a⁻¹ * (a * g) * b := by rw [ha]
      _ = g * b := by group
  · rintro ⟨ha, hb⟩
    refine ⟨ha, ?_⟩
    calc a * b * g = a * (b * g) := by group
      _ = a * (g * b) := by rw [hb]
      _ = a * g * b := by group
      _ = g * a * b := by rw [ha]
      _ = g * (a * b) := by group

theorem centralizer_pair_comm (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) = Subgroup.centralizer ({b, a} : Set G) := by
  rw [Set.pair_comm]

end Pair

section Face

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem refl_edge (h6 : Layer6Twin p f) (h2 : Om6ReflDiag p f)
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {w x y : G}
    (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (htyp : LayerOrthType p f Ω w 5 true ∨ LayerOrthType p f Ω w 6 (!piSign p f))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hy : y ∈ Subgroup.centralizer ({w} : Set G))
    (hyx : y = x * w * z) (hzY : z ∈ exactLayer Ω w)
    (hbx : z ∉ zStarOf (Subgroup.centralizer ({w, x} : Set G)))
    (hby : z ∉ zStarOf (Subgroup.centralizer ({w, y} : Set G))) :
    actW hyp.std.setting.stand.hyp.conjInvariant w ⟨y, hy⟩ =
        actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ *
          MulAut.conj (T7H.toBar Ω w z hzY) ∧
      ∃ (hA : T7H.exactImg Ω w K ≤ Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩)))
        (hA' : T7H.exactImg Ω w K' ≤ Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩)))
        (hB : T7H.exactImg Ω w K ≤ Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ *
            MulAut.conj (T7H.toBar Ω w z hzY))))
        (hB' : T7H.exactImg Ω w K' ≤ Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ *
            MulAut.conj (T7H.toBar Ω w z hzY)))),
        IsOm5 p f (centTG _ _ _ hA hA') ∧ IsOm5 p f (centTG _ _ _ hB hB') ∧
          ¬ DiagRel p (centTG _ _ _ hA hA') (centTG _ _ _ hB hB') := by
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hc := hyp.std.setting.stand.hyp.conjInvariant
  obtain ⟨hzY', hK₂, hK₂', -, hO, hO', -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  have hz : z ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS w hwA.1).symm
  have hwC : w ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hyeq : actW hc w ⟨y, hy⟩ = actW hc w ⟨x, hx⟩ * MulAut.conj (T7H.toBar Ω w z hzY) := by
    have e : (⟨y, hy⟩ : ↥(Subgroup.centralizer ({w} : Set G))) = ⟨x, hx⟩ * ⟨w, hwC⟩ * ⟨z, hz⟩ :=
      Subtype.ext hyx
    rw [e, map_mul, map_mul, actW_self, mul_one, actW_eq_conj hc hz hzY]
  have hβz : actW hc w ⟨x, hx⟩ ≠ MulAut.conj (T7H.toBar Ω w z hzY) := fun h =>
    hbx ((good_iff_actW h6 hyp hwA hw2 hw1 hwbad hxA hx hzY).mpr h)
  have hβ1 : actW hc w ⟨x, hx⟩ ≠ 1 := by
    intro h
    apply hby
    refine (good_iff_actW h6 hyp hwA hw2 hw1 hwbad hyA hy hzY).mpr ?_
    rw [hyeq, h, one_mul]
  obtain ⟨hu₁Y, hu₂Y, hOm⟩ :=
    om6mData_of_actW h6 hyp hwA hw2 hw1 hwbad htyp hxA hx hzY hβ1 hβz
  obtain ⟨hfixK, hfixK'⟩ := actW_fix hyp hw2 hK₂ hK₂' hO hO' hxA hx
  have hββ := actW_mul_self h6 hyp hwA hw2 hw1 hwbad hxA hx
  exact ⟨hyeq, h2 _ _ _ _ _ _ _ hOm _ hfixK hfixK' hββ hβ1 hβz⟩

theorem false_of_face (h6 : Layer6Twin p f) (h1 : DiagThree p f) (h2 : Om6ReflDiag p f)
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {w₁ w₂ w₃ : G}
    (hA₁ : w₁ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hA₂ : w₂ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hA₃ : w₃ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hs₁ : w₁ * w₁ = 1) (hs₂ : w₂ * w₂ = 1) (hs₃ : w₃ * w₃ = 1)
    (hn₁ : w₁ ≠ 1) (hn₂ : w₂ ≠ 1) (hn₃ : w₃ ≠ 1)
    (h₁₂ : w₁ * w₂ = w₂ * w₁) (h₁₃ : w₁ * w₃ = w₃ * w₁) (h₂₃ : w₂ * w₃ = w₃ * w₂)
    (hprod : w₁ * w₂ * w₃ = z)
    (hb₁ : z ∉ zStarOf (Subgroup.centralizer ({w₁} : Set G)))
    (hb₂ : z ∉ zStarOf (Subgroup.centralizer ({w₂} : Set G)))
    (hb₃ : z ∉ zStarOf (Subgroup.centralizer ({w₃} : Set G)))
    (ht₁ : LayerOrthType p f Ω w₁ 5 true ∨ LayerOrthType p f Ω w₁ 6 (!piSign p f))
    (ht₂ : LayerOrthType p f Ω w₂ 5 true ∨ LayerOrthType p f Ω w₂ 6 (!piSign p f))
    (ht₃ : LayerOrthType p f Ω w₃ 5 true ∨ LayerOrthType p f Ω w₃ 6 (!piSign p f))
    (hF₁₂ : z ∉ zStarOf (Subgroup.centralizer ({w₁, w₂} : Set G)))
    (hF₁₃ : z ∉ zStarOf (Subgroup.centralizer ({w₁, w₃} : Set G)))
    (hF₂₃ : z ∉ zStarOf (Subgroup.centralizer ({w₂, w₃} : Set G))) : False := by
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hC : ∀ {a b : G}, a * b = b * a → b ∈ Subgroup.centralizer ({a} : Set G) := fun h =>
    Subgroup.mem_centralizer_singleton_iff.mpr h.symm
  have hC₁₂ := hC h₁₂
  have hC₂₁ := hC h₁₂.symm
  have hC₁₃ := hC h₁₃
  have hC₃₁ := hC h₁₃.symm
  have hC₂₃ := hC h₂₃
  have hC₃₂ := hC h₂₃.symm
  have e₁ : w₃ = w₂ * w₁ * z := by
    calc w₃ = w₂ * (w₁ * w₁) * w₂ * w₃ := by rw [hs₁, mul_one, hs₂, one_mul]
      _ = w₂ * w₁ * (w₁ * w₂ * w₃) := by group
      _ = w₂ * w₁ * z := by rw [hprod]
  have e₂ : w₃ = w₁ * w₂ * z := by rw [e₁, h₁₂]
  have e₃ : w₂ = w₁ * w₃ * z := by
    calc w₂ = (w₁ * w₁) * w₂ * (w₃ * w₃) := by rw [hs₁, hs₃, one_mul, mul_one]
      _ = w₁ * (w₁ * w₂ * w₃) * w₃ := by group
      _ = w₁ * w₃ * z := by rw [hprod, mul_assoc, (hzS w₃ hA₃.1).symm, ← mul_assoc]
  have P₁ := layerPkg_of_bad h6 hyp hA₁ hs₁ hn₁ hb₁
  have P₂ := layerPkg_of_bad h6 hyp hA₂ hs₂ hn₂ hb₂
  have P₃ := layerPkg_of_bad h6 hyp hA₃ hs₃ hn₃ hb₃
  obtain ⟨q₁, hA₁₂, hA₁₂', hB₁₃, hB₁₃', h5₁₂, h5₁₃, hnd₁⟩ := refl_edge h6 h2 hyp hA₁ hs₁ hn₁ hb₁
    ht₁ hA₂ hA₃ hC₁₂ hC₁₃ e₁ P₁.zY hF₁₂ hF₁₃
  obtain ⟨q₂, hA₂₁, hA₂₁', hB₂₃, hB₂₃', h5₂₁, h5₂₃, hnd₂⟩ := refl_edge h6 h2 hyp hA₂ hs₂ hn₂ hb₂
    ht₂ hA₁ hA₃ hC₂₁ hC₂₃ e₂ P₂.zY (by rw [centralizer_pair_comm]; exact hF₁₂) hF₂₃
  obtain ⟨q₃, hA₃₁, hA₃₁', hB₃₂, hB₃₂', h5₃₁, h5₃₂, hnd₃⟩ := refl_edge h6 h2 hyp hA₃ hs₃ hn₃ hb₃
    ht₃ hA₁ hA₂ hC₃₁ hC₃₂ e₃ P₃.zY (by rw [centralizer_pair_comm]; exact hF₁₃)
    (by rw [centralizer_pair_comm]; exact hF₂₃)
  have I₁₂ := twinIso_vtx hyp hA₁ hA₂ hs₁ hs₂ hC₁₂ hC₂₁ P₁ P₂ rfl rfl hA₁₂ hA₁₂' hA₂₁ hA₂₁'
    h5₁₂ h5₂₁
  have I₁₃ := twinIso_vtx hyp hA₁ hA₃ hs₁ hs₃ hC₁₃ hC₃₁ P₁ P₃ q₁.symm rfl hB₁₃ hB₁₃' hA₃₁ hA₃₁'
    h5₁₃ h5₃₁
  have I₂₃ := twinIso_vtx hyp hA₂ hA₃ hs₂ hs₃ hC₂₃ hC₃₂ P₂ P₃ q₂.symm q₃.symm hB₂₃ hB₂₃' hB₃₂
    hB₃₂' h5₂₃ h5₃₂
  rcases h1 _ _ (vtx P₁ _ hA₁₂ hA₁₂') (vtx P₁ _ hB₁₃ hB₁₃') (vtx P₂ _ hB₂₃ hB₂₃') h5₁₂ h5₁₃ h5₂₃
    with d | d | d
  · exact hnd₁ ((diagRel_rebase_iff _ _).mp d)
  · exact hnd₂ ((diagRel_rebase_iff _ _).mp (I₁₂.symm.trans_diagRel d))
  · exact hnd₃ ((diagRel_rebase_iff _ _).mp (I₁₃.symm.trans_diagRel (d.trans_twinIso I₂₃)))

theorem centralizer_pair_eq_of {a b c : G} (h : c = a * b) :
    Subgroup.centralizer ({a, c} : Set G) = Subgroup.centralizer ({a, b} : Set G) := by
  rw [h]
  exact centralizer_pair_mul a b

theorem parityE4_of (h1 : DiagThree p f) (h2 : Om6ReflDiag p f) : ParityE4 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp d₁ d₂ hd₁A hd₂A hs₁ hs₂ hc₁₂ hn₁ hn₂ hne hz₁ hz₂
    hz₁₂ hD₀ hbad htyp
  have h6 := layer6Twin_proved p f
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have m₁ : d₁ ∈ ({d₁, d₂, d₁ * d₂} : Set G) := Set.mem_insert _ _
  have m₂ : d₂ ∈ ({d₁, d₂, d₁ * d₂} : Set G) := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have m₃ : d₁ * d₂ ∈ ({d₁, d₂, d₁ * d₂} : Set G) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have C₁ : Commute d₁ z := hzS d₁ hd₁A.1
  have C₂ : Commute d₂ z := hzS d₂ hd₂A.1
  have C₁₂ : Commute d₁ d₂ := hc₁₂
  have cm : ∀ {x w : G}, Commute x w → x ∈ Subgroup.centralizer ({w} : Set G) := fun h =>
    Subgroup.mem_centralizer_singleton_iff.mpr h.eq
  have hA₃ := Subgroup.mul_mem _ hd₁A hd₂A
  have hB₁ := Subgroup.mul_mem _ hd₁A hzA
  have hB₂ := Subgroup.mul_mem _ hd₂A hzA
  have hB₃ := Subgroup.mul_mem _ hA₃ hzA
  have sq : ∀ {a b : G}, Commute a b → a * a = 1 → b * b = 1 → a * b * (a * b) = 1 :=
    fun {a b} h ha hb => by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [h.eq]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
  have sa₃ : d₁ * d₂ * (d₁ * d₂) = 1 := sq C₁₂ hs₁ hs₂
  have sb₁ : d₁ * z * (d₁ * z) = 1 := sq C₁ hs₁ hz2
  have sb₂ : d₂ * z * (d₂ * z) = 1 := sq C₂ hs₂ hz2
  have sb₃ : d₁ * d₂ * z * (d₁ * d₂ * z) = 1 := sq (C₁.mul_left C₂) sa₃ hz2
  have ne : ∀ {a b : G}, a * a = 1 → a ≠ b → a * b ≠ 1 := fun {a b} ha hab h => by
    apply hab
    calc a = a * (a * b) := by rw [h, mul_one]
      _ = b := by rw [← mul_assoc, ha, one_mul]
  have na₃ : d₁ * d₂ ≠ 1 := ne hs₁ hne
  have nb₁ : d₁ * z ≠ 1 := ne hs₁ (Ne.symm hz₁)
  have nb₂ : d₂ * z ≠ 1 := ne hs₂ (Ne.symm hz₂)
  have nb₃ : d₁ * d₂ * z ≠ 1 := ne sa₃ (Ne.symm hz₁₂)
  obtain ⟨bd₁, bb₁⟩ := hbad d₁ m₁
  obtain ⟨bd₂, bb₂⟩ := hbad d₂ m₂
  obtain ⟨ba₃, bb₃⟩ := hbad _ m₃
  obtain ⟨td₁, tb₁⟩ := htyp d₁ m₁
  obtain ⟨td₂, tb₂⟩ := htyp d₂ m₂
  obtain ⟨ta₃, tb₃⟩ := htyp _ m₃
  have L₁ := not_good_and_good h6 hyp hB₁ sb₁ nb₁ bb₁ hd₂A (cm (C₁₂.symm.mul_right C₂))
  have L₂ := not_good_and_good h6 hyp hB₂ sb₂ nb₂ bb₂ hd₁A (cm (C₁₂.mul_right C₁))
  have L₃ := not_good_and_good h6 hyp hB₃ sb₃ nb₃ bb₃ hd₁A
    (cm (((Commute.refl d₁).mul_right C₁₂).mul_right C₁))
  rw [centralizer_pair_comm (d₂ * z), centralizer_pair_comm (d₂ * z)] at L₂
  have r₁ : d₁ * d₂ * z = d₁ * (d₂ * z) := mul_assoc _ _ _
  have r₂ : d₁ * d₂ * z = d₁ * z * d₂ := by
    rw [mul_assoc d₁ z, ← C₂.eq, ← mul_assoc]
  rw [centralizer_pair_comm (d₁ * d₂ * z), centralizer_pair_comm (d₁ * d₂ * z),
    centralizer_pair_eq_of r₁, centralizer_pair_eq_of r₂] at L₃
  by_cases G1 : z ∈ zStarOf (Subgroup.centralizer ({d₁, d₂ * z} : Set G))
  · have nG2 := fun h => L₃ ⟨G1, h⟩
    have nG3 := fun h => L₂ ⟨G1, h⟩
    have r₃ : d₁ * d₂ = d₁ * z * (d₂ * z) := by
      calc d₁ * d₂ = d₁ * d₂ * (z * z) := by rw [hz2, mul_one]
        _ = d₁ * (d₂ * z) * z := by group
        _ = d₁ * (z * d₂) * z := by rw [C₂.eq]
        _ = d₁ * z * (d₂ * z) := by group
    refine false_of_face h6 h1 h2 hyp hd₂A hA₃ hB₁ hs₂ sa₃ sb₁ hn₂ na₃ nb₁
      (C₁₂.symm.mul_right (Commute.refl d₂)).eq (C₁₂.symm.mul_right C₂).eq
      (Commute.mul_left ((Commute.refl d₁).mul_right C₁) (C₁₂.symm.mul_right C₂)).eq ?_
      bd₂ ba₃ bb₁ td₂ ta₃ tb₁ ?_ ?_ ?_
    · calc d₂ * (d₁ * d₂) * (d₁ * z) = d₂ * (d₂ * d₁) * (d₁ * z) := by rw [C₁₂.eq]
        _ = (d₂ * d₂) * (d₁ * d₁) * z := by group
        _ = z := by rw [hs₂, hs₁, one_mul, one_mul]
    · rw [centralizer_pair_eq_of C₁₂.eq, centralizer_pair_comm]
      exact hD₀
    · rw [centralizer_pair_comm]
      exact nG2
    · rw [centralizer_pair_comm, centralizer_pair_eq_of r₃]
      exact nG3
  · by_cases G2 : z ∈ zStarOf (Subgroup.centralizer ({d₁ * z, d₂} : Set G))
    · have nG3 := fun h => L₁ ⟨G2, h⟩
      have r₄ : d₁ * d₂ = d₂ * z * (d₁ * z) := by
        calc d₁ * d₂ = d₂ * d₁ * (z * z) := by rw [hz2, mul_one, C₁₂.eq]
          _ = d₂ * (d₁ * z) * z := by group
          _ = d₂ * (z * d₁) * z := by rw [C₁.eq]
          _ = d₂ * z * (d₁ * z) := by group
      refine false_of_face h6 h1 h2 hyp hd₁A hA₃ hB₂ hs₁ sa₃ sb₂ hn₁ na₃ nb₂
        ((Commute.refl d₁).mul_right C₁₂).eq (C₁₂.mul_right C₁).eq
        (Commute.mul_left (C₁₂.mul_right C₁) ((Commute.refl d₂).mul_right C₂)).eq ?_
        bd₁ ba₃ bb₂ td₁ ta₃ tb₂ ?_ G1 ?_
      · calc d₁ * (d₁ * d₂) * (d₂ * z) = (d₁ * d₁) * (d₂ * d₂) * z := by group
          _ = z := by rw [hs₁, hs₂, one_mul, one_mul]
      · rw [centralizer_pair_mul]
        exact hD₀
      · rw [centralizer_pair_comm, centralizer_pair_eq_of r₄, centralizer_pair_comm]
        exact nG3
    · have r₅ : d₁ * d₂ * z = d₂ * (d₁ * z) := by rw [C₁₂.eq, mul_assoc]
      refine false_of_face h6 h1 h2 hyp hd₁A hd₂A hB₃ hs₁ hs₂ sb₃ hn₁ hn₂ nb₃ C₁₂.eq
        (((Commute.refl d₁).mul_right C₁₂).mul_right C₁).eq
        ((C₁₂.symm.mul_right (Commute.refl d₂)).mul_right C₂).eq ?_
        bd₁ bd₂ bb₃ td₁ td₂ tb₃ hD₀ ?_ ?_
      · calc d₁ * d₂ * (d₁ * d₂ * z) = d₁ * (d₂ * d₁) * d₂ * z := by group
          _ = d₁ * (d₁ * d₂) * d₂ * z := by rw [← C₁₂.eq]
          _ = (d₁ * d₁) * (d₂ * d₂) * z := by group
          _ = z := by rw [hs₁, hs₂, one_mul, one_mul]
      · rw [centralizer_pair_eq_of r₁]
        exact G1
      · rw [centralizer_pair_eq_of r₅, centralizer_pair_comm]
        exact G2

end Face

end CFSG.ClassicalInvolution.Asc77.CX
