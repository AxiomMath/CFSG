module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearGen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix Polynomial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.CTP

section Chain

variable {M : Type*} [Group M]

theorem isSubnormal_subgroupOf_of_chain {A B D C : Subgroup M} (hAB : A ≤ B) (hBD : B ≤ D)
    (_hDC : D ≤ C) (h1 : ∀ y ∈ B, ∀ x ∈ A, y * x * y⁻¹ ∈ A)
    (h2 : ∀ y ∈ D, ∀ x ∈ B, y * x * y⁻¹ ∈ B) (h3 : ∀ y ∈ C, ∀ x ∈ D, y * x * y⁻¹ ∈ D) :
    (A.subgroupOf C).IsSubnormal := by
  have hD : (D.subgroupOf C).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa [Subgroup.mem_subgroupOf] using h3 g.1 g.2 n.1 hn
  have hB : (B.subgroupOf C).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ _ (fun z hz => hBD hz) hD ?_
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : (n : ↥C).1 ∈ B := hn
    simpa [Subgroup.mem_subgroupOf] using h2 g.1.1 g.2 (n : ↥C).1 hn'
  refine Subgroup.IsSubnormal.step _ _ (fun z hz => hAB hz) hB ?_
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (n : ↥C).1 ∈ A := hn
  simpa [Subgroup.mem_subgroupOf] using h1 g.1.1 g.2 (n : ↥C).1 hn'



theorem conj_mem_centralizer_of_central {G : Type*} [Group G] {a u z c : G}
    (hz : z ∈ Subgroup.center G) (hua : u * a * u⁻¹ = z * a) (hc : c * a = a * c) :
    (u * c * u⁻¹) * a = a * (u * c * u⁻¹) := by
  have e1 : u * a = z * a * u := by
    calc u * a = u * a * u⁻¹ * u := by group
      _ = z * a * u := by rw [hua]
  have e2 : a * u = z⁻¹ * (u * a) := by
    rw [e1, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
  apply mul_right_cancel (b := u)
  calc u * c * u⁻¹ * a * u = u * c * u⁻¹ * (a * u) := by group
    _ = u * c * u⁻¹ * (z⁻¹ * (u * a)) := by rw [e2]
    _ = z⁻¹ * (u * (c * a)) := by
      have hzi : u * c * u⁻¹ * z⁻¹ = z⁻¹ * (u * c * u⁻¹) :=
        (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hz)) (u * c * u⁻¹)
      calc u * c * u⁻¹ * (z⁻¹ * (u * a)) = (u * c * u⁻¹ * z⁻¹) * (u * a) := by group
        _ = z⁻¹ * (u * c * u⁻¹) * (u * a) := by rw [hzi]
        _ = z⁻¹ * (u * (c * a)) := by group
    _ = z⁻¹ * (u * (a * c)) := by rw [hc]
    _ = z⁻¹ * ((u * a) * c) := by group
    _ = z⁻¹ * ((z * a * u) * c) := by rw [e1]
    _ = a * u * c := by
      have : z⁻¹ * (z * a * u * c) = a * u * c := by group
      exact this
    _ = a * (u * c * u⁻¹) * u := by group

end Chain

section PSL

variable {n : ℕ} {F : Type} [Field F] [Finite F]

instance finite_SL : Finite (SpecialLinearGroup (Fin n) F) :=
  Finite.of_injective (Subtype.val : SpecialLinearGroup (Fin n) F → Matrix (Fin n) (Fin n) F)
    Subtype.val_injective

@[expose] noncomputable def toPSL (n : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))

omit [Finite F] in
theorem toPSL_surjective : Function.Surjective (toPSL n F) := QuotientGroup.mk'_surjective _

omit [Finite F] in
theorem toPSL_eq_one_iff {s : SpecialLinearGroup (Fin n) F} :
    toPSL n F s = 1 ↔ s ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) :=
  QuotientGroup.eq_one_iff s

omit [Finite F] in
theorem ker_toPSL : (toPSL n F).ker = Subgroup.center (SpecialLinearGroup (Fin n) F) :=
  QuotientGroup.ker_mk' _

@[expose] noncomputable def blockPSL (a : SpecialLinearGroup (Fin n) F)
    (hsq : Squarefree (minpoly F (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))))
    (h : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))) :
    Subgroup (ProjectiveSpecialLinearGroup (Fin n) F) :=
  ((blockImage hsq h).comap SpecialLinearGroup.toGL).map (toPSL n F)

section Facts

variable {a : SpecialLinearGroup (Fin n) F}
  {hsq : Squarefree (minpoly F (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F)))}
  {h : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))}

omit [Finite F] in
theorem range_commutant_eq_centralizer (a : SpecialLinearGroup (Fin n) F) :
    (commutantUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))).range =
      Subgroup.centralizer ({SpecialLinearGroup.toGL a} : Set (GL (Fin n) F)) :=
  range_commutantUnitsToGL_eq_centralizer (x := Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))
    (SpecialLinearGroup.toGL a) rfl

omit [Finite F] in
theorem commute_of_mem_blockImage {s : SpecialLinearGroup (Fin n) F}
    (hs : SpecialLinearGroup.toGL s ∈ blockImage hsq h) : s * a = a * s := by
  have h1 := blockImage_le_range hsq h hs
  rw [range_commutant_eq_centralizer a, Subgroup.mem_centralizer_singleton_iff] at h1
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul]
  exact h1

omit [Finite F] in
theorem conj_mem_blockImage_of_commute {c s : SpecialLinearGroup (Fin n) F} (hc : c * a = a * c)
    (hs : SpecialLinearGroup.toGL s ∈ blockImage hsq h) :
    SpecialLinearGroup.toGL (c * s * c⁻¹) ∈ blockImage hsq h := by
  have hcg : SpecialLinearGroup.toGL c ∈ (commutantUnitsToGL (Matrix.toLin'
      (a : Matrix (Fin n) (Fin n) F))).range := by
    rw [range_commutant_eq_centralizer a, Subgroup.mem_centralizer_singleton_iff]
    apply congrArg SpecialLinearGroup.toGL at hc
    rw [map_mul, map_mul] at hc
    exact hc
  have := conj_mem_blockImage hsq h hcg hs
  rwa [← map_inv, ← map_mul, ← map_mul] at this

end Facts

section Component

open CFSG.RankThree.PartOne.KCLinPlane

variable {a : SpecialLinearGroup (Fin n) F}
  {hsq : Squarefree (minpoly F (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F)))}
  {h : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))}

local notation "PSLn" => ProjectiveSpecialLinearGroup (Fin n) F

omit [Finite F] in
theorem conj_commute_of_commute {u v : SpecialLinearGroup (Fin n) F} (huv : u * v = v * u) :
    (MulAut.conj (toPSL n F u) : MulAut PSLn) * MulAut.conj (toPSL n F v) =
      MulAut.conj (toPSL n F v) * MulAut.conj (toPSL n F u) := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, huv]

omit [Finite F] in
theorem blockPSL_conj_le {H : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) :
    (blockPSL a hsq h).map (MulAut.conj : PSLn →* MulAut PSLn) ≤
      H ⊓ Subgroup.centralizer ({MulAut.conj (toPSL n F a)} : Set (MulAut PSLn)) := by
  rintro _ ⟨t, ⟨s, hs, rfl⟩, rfl⟩
  refine Subgroup.mem_inf.2 ⟨hH ⟨toPSL n F s, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact conj_commute_of_commute (commute_of_mem_blockImage hs)

omit [Finite F] in
theorem blockImage_comap_isQuasisimple (hgood : GoodBlock h) :
    CFSG.IsQuasisimple ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) := by
  have hrange := blockImage_le_range_toGL_of_good hsq h hgood
  let e0 : ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) ≃*
        blockImage hsq h :=
    (Subgroup.equivMapOfInjective _ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →*
      GL (Fin n) F) SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hrange))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e0.symm
    (isQuasisimple_blockImage_of_good hsq h hgood)

noncomputable def blockToPSL (a : SpecialLinearGroup (Fin n) F)
    (hsq : Squarefree (minpoly F (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))))
    (h : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))) :
    ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) →*
        blockPSL a hsq h :=
  ((toPSL n F).comp ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)).subtype).codRestrict
    (blockPSL a hsq h) (fun x => ⟨x, x.2, rfl⟩)

omit [Finite F] in
theorem blockToPSL_surjective : Function.Surjective (blockToPSL a hsq h) := by
  rintro ⟨_, s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, rfl⟩

omit [Finite F] in
theorem ker_blockToPSL_le_center :
    (blockToPSL a hsq h).ker ≤ Subgroup.center ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) := by
  intro x hx
  have h1 : toPSL n F (x : SpecialLinearGroup (Fin n) F) = 1 := congrArg Subtype.val hx
  have h2 := toPSL_eq_one_iff.1 h1
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext ((Subgroup.mem_center_iff.1 h2 (y : SpecialLinearGroup (Fin n) F)))

omit [Finite F] in
theorem blockPSL_isQuasisimple (hgood : GoodBlock h) :
    CFSG.IsQuasisimple (blockPSL a hsq h) :=
  CFSG.LocalCores.isQuasisimple_of_surjective (blockImage_comap_isQuasisimple hgood) _
    blockToPSL_surjective ker_blockToPSL_le_center

omit [Finite F] in
theorem conj_toPSL_conj (c s : SpecialLinearGroup (Fin n) F) :
    (MulAut.conj (toPSL n F c) : MulAut PSLn) * MulAut.conj (toPSL n F s) *
      (MulAut.conj (toPSL n F c))⁻¹ = MulAut.conj (toPSL n F (c * s * c⁻¹)) := by
  simp [map_mul, map_inv]

theorem blockPSL_isComponent
    (hinj : Function.Injective (MulAut.conj : PSLn →* MulAut PSLn))
    {H : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) (hgood : GoodBlock h) :
    CFSG.IsComponent (((blockPSL a hsq h).map (MulAut.conj : PSLn →* MulAut PSLn)).subgroupOf
      (H ⊓ Subgroup.centralizer ({MulAut.conj (toPSL n F a)} : Set (MulAut PSLn)))) := by
  have hTcC := blockPSL_conj_le (a := a) (hsq := hsq) (h := h) hH
  refine ⟨?_, ?_⟩
  · have e1 := (blockPSL a hsq h).equivMapOfInjective (MulAut.conj : PSLn →* MulAut PSLn) hinj
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e1.trans (Subgroup.subgroupOfEquivOfLe hTcC).symm) (blockPSL_isQuasisimple hgood)
  · set e : MulAut PSLn := MulAut.conj (toPSL n F a) with he
    set C0 : Subgroup (SpecialLinearGroup (Fin n) F) :=
      Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin n) F)) with hC0
    refine isSubnormal_subgroupOf_of_chain
      (B := (C0.map (toPSL n F)).map (MulAut.conj : PSLn →* MulAut PSLn))
      (D := innerAut PSLn ⊓ Subgroup.centralizer ({e} : Set (MulAut PSLn))) ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨t, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨_, ⟨s, Subgroup.mem_centralizer_singleton_iff.2
        (commute_of_mem_blockImage hs), rfl⟩, rfl⟩
    · rintro _ ⟨t, ⟨c, hc, rfl⟩, rfl⟩
      refine Subgroup.mem_inf.2 ⟨⟨toPSL n F c, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact conj_commute_of_commute (Subgroup.mem_centralizer_singleton_iff.1 hc)
    · intro y hy
      exact Subgroup.mem_inf.2 ⟨hH (Subgroup.mem_inf.1 hy).1, (Subgroup.mem_inf.1 hy).2⟩
    · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩ _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      rw [conj_toPSL_conj]
      exact ⟨_, ⟨c * s * c⁻¹, conj_mem_blockImage_of_commute
        (Subgroup.mem_centralizer_singleton_iff.1 hc) hs, rfl⟩, rfl⟩
    · rintro y ⟨⟨k, rfl⟩, hy⟩ _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      obtain ⟨u, rfl⟩ := toPSL_surjective k
      have hcomm : toPSL n F u * toPSL n F a = toPSL n F a * toPSL n F u := by
        apply hinj
        rw [map_mul, map_mul]
        exact Subgroup.mem_centralizer_singleton_iff.1 hy
      have hz : u * a * u⁻¹ * a⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
        rw [← ker_toPSL, MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [hcomm]
        group
      have hua : u * a * u⁻¹ = (u * a * u⁻¹ * a⁻¹) * a := by group
      have hc' := conj_mem_centralizer_of_central hz hua
        (Subgroup.mem_centralizer_singleton_iff.1 hc)
      refine ⟨toPSL n F (u * c * u⁻¹), ⟨u * c * u⁻¹, Subgroup.mem_centralizer_singleton_iff.2
        hc', rfl⟩, ?_⟩
      simp [map_mul, map_inv]
    · intro y hy x hx
      obtain ⟨⟨k, rfl⟩, hxe⟩ := Subgroup.mem_inf.1 hx
      have hye := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
      have hxe' := Subgroup.mem_centralizer_singleton_iff.1 hxe
      refine Subgroup.mem_inf.2 ⟨⟨(y : MulAut PSLn) k, ?_⟩, ?_⟩
      · rw [← mul_conj_mul_inv]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (((Commute.mul_left (show Commute y e from hye) (show Commute _ e from hxe')).mul_left
          (show Commute y⁻¹ e from (show Commute y e from hye).inv_left)).eq)

omit [Finite F] in
theorem card_comap_blockImage (hgood : GoodBlock h) :
    Nat.card ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) =
      Nat.card (blockImage hsq h) := by
  have hrange := blockImage_le_range_toGL_of_good hsq h hgood
  let e0 : ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) ≃*
        blockImage hsq h :=
    (Subgroup.equivMapOfInjective _ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →*
      GL (Fin n) F) SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hrange))
  exact Nat.card_congr e0.toEquiv

omit [Finite F] in
theorem blockPSL_not_coprime {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F))) (hgood : GoodBlock h)
    (hpd : p ∣ Nat.card (blockImage hsq h)) :
    ¬ Nat.Coprime p (Nat.card (blockPSL a hsq h)) := by
  set ψ := blockToPSL a hsq h with hψ
  have hsplit : Nat.card ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) =
      Nat.card (blockPSL a hsq h) * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ blockToPSL_surjective).toEquiv]
  have hker : Nat.card ψ.ker ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) := by
    have hle : ψ.ker.map ((blockImage hsq h).comap
        (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)).subtype ≤
        Subgroup.center (SpecialLinearGroup (Fin n) F) := by
      rintro _ ⟨x, hx, rfl⟩
      exact toPSL_eq_one_iff.1 (congrArg Subtype.val hx)
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact Subgroup.card_dvd_of_le hle
  have hpT0 : p ∣ Nat.card ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) := by
    rw [card_comap_blockImage hgood]; exact hpd
  rw [hsplit] at hpT0
  intro hcop
  rcases (Nat.Prime.dvd_mul hp).1 hpT0 with h1 | h1
  · exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop h1
  · exact hZ (h1.trans hker)

theorem blockPSL_le_fixSub {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : PSLn →* MulAut PSLn))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)))
    {H E : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) {g : MulAut PSLn}
    (hg : g ∈ localDeltaIn p H E) (he : MulAut.conj (toPSL n F a) ∈ E) (he1 : toPSL n F a ≠ 1)
    (hgood : GoodBlock h) (hpd : p ∣ Nat.card (blockImage hsq h)) :
    blockPSL a hsq h ≤ fixSub g :=
  le_fixSub_of_component hp hinj hg he (fun h' => he1 (hinj (by rw [h', map_one])))
    (blockPSL_conj_le hH) (blockPSL_isComponent hinj hH hgood)
    (blockPSL_not_coprime hp hZ hgood hpd)

omit [Finite F] in
theorem exists_sl_lift {p : ℕ} [Fact p.Prime]
    [Finite F] (hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)))
    (E₁ : Subgroup PSLn) (hE₁ : IsElemAbelian p E₁) (hc : Nat.card E₁ = p ^ 2) :
    ∃ E₀ : Subgroup (SpecialLinearGroup (Fin n) F), E₀.map (toPSL n F) = E₁ ∧
      Disjoint E₀ (toPSL n F).ker ∧ IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 := by
  have hEp : IsPGroup p E₁ := fun x => ⟨1, Subtype.ext (by simpa using hE₁.2 x x.2)⟩
  obtain ⟨E', hmap, hdis⟩ := SeitzToral.exists_lift_of_coprime_ker (toPSL n F) toPSL_surjective
    (by rwa [ker_toPSL]) E₁ hEp
  have hmem : ∀ x ∈ E', toPSL n F x ∈ E₁ := fun x hx => hmap ▸ ⟨x, hx, rfl⟩
  have hcomm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hcm : a * b * a⁻¹ * b⁻¹ ∈ E' :=
      E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha)) (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ (toPSL n F).ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have hab : toPSL n F a * toPSL n F b = toPSL n F b * toPSL n F a :=
        congrArg Subtype.val (hE₁.1.is_comm.comm ⟨_, hmem a ha⟩ ⟨_, hmem b hb⟩)
      rw [hab]
      group
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.disjoint_def.mp hdis hcm hk)
  have hexp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ (toPSL n F).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hE₁.2 _ (hmem a ha)
    exact Subgroup.disjoint_def.mp hdis (E'.pow_mem ha p) hk
  let fπ : E' →* E₁ := ((toPSL n F).comp E'.subtype).codRestrict E₁ (fun x => hmem x.1 x.2)
  have hsurj : Function.Surjective fπ := by
    intro e
    have : (e : PSLn) ∈ E'.map (toPSL n F) := hmap ▸ e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hinj' : Function.Injective fπ := by
    intro x y hxy
    have h1 : toPSL n F x.1 = toPSL n F y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ (toPSL n F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 :=
      Subgroup.disjoint_def.mp hdis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  refine ⟨E', hmap, hdis, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp⟩, ?_⟩
  rw [Nat.card_congr (Equiv.ofBijective fπ ⟨hinj', hsurj⟩), hc]

omit [Finite F] in
theorem eq_one_of_fixSub_toPSL {g : MulAut PSLn}
    (h : (fixSub g).comap (toPSL n F) = ⊤) : g = 1 := by
  rw [← fixSub_eq_top_iff]
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨s, rfl⟩ := toPSL_surjective y
  have : s ∈ (fixSub g).comap (toPSL n F) := h ▸ Subgroup.mem_top s
  exact this

theorem localDeltaIn_eq_bot_psl_nonsplit {p : ℕ} (hp : p.Prime) (hp4 : 3 < p ∨ 4 ≤ Nat.card F)
    (hpF : ¬ p ∣ Nat.card F) (hpq : ¬ p ∣ Nat.card F - 1) (hn : 1 ≤ n)
    (hinj : Function.Injective (MulAut.conj : PSLn →* MulAut PSLn))
    (E₁ : Subgroup PSLn) (hE₁ : IsElemAbelian p E₁) (hc : Nat.card E₁ = p ^ 2)
    {H : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) :
    localDeltaIn p H (E₁.map (MulAut.conj : PSLn →* MulAut PSLn)) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) := fun hd =>
    hpq (hd.trans ((CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd hn F).trans
      (Nat.gcd_dvd_right _ _)))
  obtain ⟨E₀, hmap, hdis, hE₀, hc₀⟩ := exists_sl_lift hZ E₁ hE₁ hc
  have : CFSG.IsElementaryAbelian p E₀ :=
    { toIsMulCommutative := hE₀.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE₀.2 x x.2) }
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  refine eq_one_of_fixSub_toPSL (eq_top_of_good_blocks_le' hp hp4
    (natCast_ne_zero_of_not_dvd_card hp hpF) hpF hpq E₀ hc₀ _ ?_)
  intro a ha ha1 hsq h hgood hpd x hx
  obtain ⟨s, hs⟩ := blockImage_le_range_toGL_of_good hsq h hgood hx
  rw [← hs] at hx ⊢
  refine ⟨s, ?_, rfl⟩
  have hπa : toPSL n F a ∈ E₁ := hmap ▸ ⟨a, ha, rfl⟩
  have hπ1 : toPSL n F a ≠ 1 := fun h1 => ha1 (Subgroup.disjoint_def.mp hdis ha
    (MonoidHom.mem_ker.2 h1))
  exact blockPSL_le_fixSub hp hinj hZ hH hg ⟨_, hπa, rfl⟩ hπ1 hgood hpd ⟨s, hx, rfl⟩

end Component

end PSL

section Transvection

open Module

variable {n : ℕ} {F : Type} [Field F]

theorem single_mul_diagonal_comm {i j : Fin n} (d : Fin n → F) (hd : d i = d j) (c : F) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.diagonal d * Matrix.single i j c := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [hd, mul_comm]
  · simp [h]

theorem transvection_data (a : SpecialLinearGroup (Fin n) F) (P : GL (Fin n) F)
    (hdiag : ∀ k l, k ≠ l →
      ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l = 0)
    (k : Fin n) :
    ∃ u : Fin n → F, u ≠ 0 ∧ (a : Matrix (Fin n) (Fin n) F).mulVec u =
      ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k k • u ∧
      (P : Matrix (Fin n) (Fin n) F).mulVec u = Pi.single k 1 := by
  set D : Matrix (Fin n) (Fin n) F :=
    ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hDdef
  have hD : D = Matrix.diagonal (fun k => D k k) := by
    ext r s
    by_cases h : r = s
    · subst h; simp
    · simp [hdiag r s h, Matrix.diagonal_apply_ne _ h]
  have hPP : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin n) (Fin n) F) *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA : (a : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * D := by
    have hcoe : ((SpecialLinearGroup.toGL a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = a := rfl
    simp only [hDdef, Units.val_mul, hcoe]
    calc (a : Matrix (Fin n) (Fin n) F) * ↑P⁻¹
        = ↑P⁻¹ * ↑P * ↑a * ↑P⁻¹ := by rw [hPP, Matrix.one_mul]
      _ = ↑P⁻¹ * (↑P * ↑a * ↑P⁻¹) := by simp only [Matrix.mul_assoc]
  refine ⟨((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single k 1), ?_, ?_, ?_⟩
  · intro h0
    have := congrArg (fun v => (P : Matrix (Fin n) (Fin n) F).mulVec v) h0
    simp only [Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have h1 := congrFun this k
    simp at h1
  · have hDk : D.mulVec (Pi.single k 1) = D k k • (Pi.single k 1 : Fin n → F) := by
      ext r
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      by_cases hr : r = k
      · subst hr
        rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb])
          (fun h => absurd (Finset.mem_univ r) h)]
      · simp [hdiag r k hr, Pi.single_apply, hr]
    rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hDk, Matrix.mulVec_smul]
  · rw [Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec]


theorem single_mulVec {i j : Fin n} (c : F) (w : Fin n → F) :
    (Matrix.single i j c).mulVec w = Pi.single i (c * w j) := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply]
  by_cases hr : r = i
  · subst hr
    simp
  · simp [hr, Ne.symm hr]

theorem transvection_mem_blockImage (a : SpecialLinearGroup (Fin n) F) (P : GL (Fin n) F)
    (hdiag : ∀ k l, k ≠ l →
      ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l = 0)
    {i j : Fin n} (hij : i ≠ j)
    (hd : ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i =
      ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j)
    (c : F) (hsq : Squarefree (minpoly F (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F)))) :
    ∃ hX : (X - C (((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i i) : F[X]) ∈ primaryFactors
        (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F)),
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F))
          ⟨X - C (((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) F) i i), hX⟩ ∧
      ∀ s : SpecialLinearGroup (Fin n) F,
        (s : Matrix (Fin n) (Fin n) F) =
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 + Matrix.single i j c) *
            (P : Matrix (Fin n) (Fin n) F) →
        SpecialLinearGroup.toGL s ∈ blockImage hsq ⟨X - C (((P * SpecialLinearGroup.toGL a * P⁻¹ :
          GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i), hX⟩ := by
  classical
  set D : Matrix (Fin n) (Fin n) F :=
    ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hDdef
  set μ : F := D i i with hμ
  set x : Module.End F (Fin n → F) := Matrix.toLin' (a : Matrix (Fin n) (Fin n) F) with hx
  obtain ⟨ui, hui0, hAui, hPui⟩ := transvection_data a P hdiag i
  obtain ⟨uj, huj0, hAuj, hPuj⟩ := transvection_data a P hdiag j
  have hAui' : (a : Matrix (Fin n) (Fin n) F).mulVec ui = μ • ui := hAui
  have hAuj' : (a : Matrix (Fin n) (Fin n) F).mulVec uj = μ • uj := by rw [hd]; exact hAuj
  have hmemi : ui ∈ primaryComponent x (X - C μ) := by
    rw [mem_primaryComponent]
    simp [hx, Matrix.toLin'_apply, hAui']
  have hmemj : uj ∈ primaryComponent x (X - C μ) := by
    rw [mem_primaryComponent]
    simp [hx, Matrix.toLin'_apply, hAuj']
  have hX : (X - C μ : F[X]) ∈ primaryFactors x :=
    mem_primaryFactors_of_ne_zero (irreducible_X_sub_C μ) (monic_X_sub_C μ) hui0 hmemi
  have : Fact (Irreducible (X - C μ : F[X])) := ⟨irreducible_X_sub_C μ⟩
  have hmult2 : 2 ≤ mult x ⟨X - C μ, hX⟩ := by
    have hli : LinearIndependent F ![ui, uj] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (fun v => (P : Matrix (Fin n) (Fin n) F).mulVec v) hst
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hPui, hPuj, Matrix.mulVec_zero] at h1
      have hi := congrFun h1 i
      have hj := congrFun h1 j
      simp [hij, Ne.symm hij] at hi hj
      exact ⟨hi, hj⟩
    have hspan : Submodule.span F (Set.range ![ui, uj]) ≤ primaryComponent x (X - C μ) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      fin_cases t
      · exact hmemi
      · exact hmemj
    have h2 : 2 ≤ finrank F (primaryComponent x (X - C μ)) := by
      have h4 := finrank_span_eq_card hli
      rw [Fintype.card_fin] at h4
      calc 2 = _ := h4.symm
        _ ≤ _ := Submodule.finrank_mono hspan
    have h3 := finrank_primaryComponent x (X - C μ)
    rw [natDegree_X_sub_C, one_mul] at h3
    change 2 ≤ finrank (AdjoinRoot (X - C μ)) (primaryComponent x (X - C μ))
    omega
  refine ⟨hX, hmult2, ?_⟩
  intro s hs
  have hPP : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin n) (Fin n) F) *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP'' : ∀ M : Matrix (Fin n) (Fin n) F, (P : Matrix (Fin n) (Fin n) F) *
      (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hPP', Matrix.one_mul]
  have hPP''' : ∀ M : Matrix (Fin n) (Fin n) F,
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((P : Matrix (Fin n) (Fin n) F) * M) =
        M := fun M => by
    rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hDdiag : D = Matrix.diagonal (fun k => D k k) := by
    ext r s'
    by_cases h : r = s'
    · subst h; simp
    · simp [hdiag r s' h, Matrix.diagonal_apply_ne _ h]
  have hAD : (a : Matrix (Fin n) (Fin n) F) =
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (D * (P : Matrix (Fin n) (Fin n) F)) := by
    have hcoe : ((SpecialLinearGroup.toGL a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = a := rfl
    simp only [hDdef, Units.val_mul, hcoe, Matrix.mul_assoc, hPP'', hPP''']
    rw [hPP, Matrix.mul_one]
  set E : Matrix (Fin n) (Fin n) F := Matrix.single i j c with hE
  set Bm : Matrix (Fin n) (Fin n) F := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
    (E * (P : Matrix (Fin n) (Fin n) F)) with hBm
  have hED : E * D = D * E := by
    have := single_mul_diagonal_comm (i := i) (j := j) (fun k => D k k) hd c
    rwa [← hDdiag] at this
  have hcommM : Bm * (a : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) * Bm := by
    rw [hAD]
    simp only [hBm, Matrix.mul_assoc, hPP'', hPP''']
    rw [← Matrix.mul_assoc E, ← Matrix.mul_assoc D, hED]
  have hBB : Bm * Bm = 0 := by
    simp only [hBm, Matrix.mul_assoc, hPP'', hPP''']
    rw [← Matrix.mul_assoc E, hE, Matrix.single_mul_single_of_ne c i j i hij.symm c,
      Matrix.zero_mul,
      Matrix.mul_zero]
  set β : Module.End F (Fin n → F) := Matrix.toLin' Bm with hβdef
  have hcomm : β * x = x * β := by
    rw [hβdef, hx, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← Matrix.toLin'_mul, hcommM]
  have hβ : β ∈ commutant x := (mem_commutant x).2 hcomm
  have hββ : β * β = 0 := by
    rw [hβdef, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hBB, map_zero]
  have hβv : ∀ v, β v = (c * (P : Matrix (Fin n) (Fin n) F).mulVec v j) • ui := by
    intro v
    have hui : ui = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single i 1) := by
      rw [← hPui, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
    rw [hβdef, Matrix.toLin'_apply, hBm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hE,
      single_mulVec, hui, ← Matrix.mulVec_smul]
    congr 1
    ext r
    simp [Pi.single_apply]
  have hkill : ∀ k ∈ primaryFactors x, k ≠ (⟨X - C μ, hX⟩ : primaryFactors x).1 →
      ∀ v ∈ primaryComponent x k, β v = 0 := by
    intro k hk hkne v hv
    have h1 : β v ∈ primaryComponent x k := apply_mem_primaryComponent hcomm hv
    have h2 : β v ∈ primaryComponent x (X - C μ) := by
      rw [hβv]; exact Submodule.smul_mem _ _ hmemi
    exact eq_zero_of_mem_primaryComponent_ne hk hX hkne h1 h2
  have hdet : LinearMap.det (1 + commutantRestrict (X - C μ) ⟨β, hβ⟩) = 1 := by
    apply det_eq_one_of_restrictScalars (natDegree_X_sub_C μ)
    have hmaps : ∀ w ∈ primaryComponent x (X - C μ), β w ∈ primaryComponent x (X - C μ) :=
      fun w hw => apply_mem_primaryComponent hcomm hw
    have hrs : ((1 + commutantRestrict (X - C μ) ⟨β, hβ⟩ :
        Module.End (AdjoinRoot (X - C μ)) (primaryComponent x (X - C μ))).restrictScalars F) =
        1 + β.restrict hmaps := rfl
    rw [hrs]
    refine det_one_add_of_range_le_ker (β.restrict hmaps)
      (Submodule.span F {(⟨ui, hmemi⟩ : primaryComponent x (X - C μ))}) ?_ ?_
    · intro w
      refine Submodule.mem_span_singleton.2 ⟨c * (P : Matrix (Fin n) (Fin n) F).mulVec w j, ?_⟩
      apply Subtype.ext
      exact (hβv w).symm
    · intro w hw
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul]
      have : (β.restrict hmaps) ⟨ui, hmemi⟩ = 0 := by
        apply Subtype.ext
        change β ui = 0
        rw [hβv, hPui]
        simp [Ne.symm hij]
      rw [this, smul_zero]
  obtain ⟨gb, hgb, hgbv⟩ := exists_mem_blockImage_one_add hsq (a0 := SpecialLinearGroup.toGL a)
    rfl ⟨X - C μ, hX⟩ β hβ hββ hkill hdet
  have hsm : (s : Matrix (Fin n) (Fin n) F) = 1 + Bm := by
    rw [hs, hBm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP, Matrix.mul_assoc]
  have hgs : SpecialLinearGroup.toGL s = gb := by
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [hgbv v]
    change Matrix.toLin' (s : Matrix (Fin n) (Fin n) F) v = v + β v
    rw [hsm, Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec, hβdef, Matrix.toLin'_apply]
  rw [hgs]
  exact hgb


end Transvection

section Split

open Module CFSG.RankThree.PartOne.CTP.SeitzToral

variable {n : ℕ} {F : Type} [Field F] [Finite F]

local notation "PSLn" => ProjectiveSpecialLinearGroup (Fin n) F

theorem localDeltaIn_eq_bot_psl_split {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpq : p ∣ Nat.card F - 1) (hpn : ¬ p ∣ n) (hn : 1 ≤ n)
    (hinj : Function.Injective (MulAut.conj : PSLn →* MulAut PSLn))
    (E₁ : Subgroup PSLn) (hE₁ : IsElemAbelian p E₁) (hc : Nat.card E₁ = p ^ 2)
    {H : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) :
    localDeltaIn p H (E₁.map (MulAut.conj : PSLn →* MulAut PSLn)) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hF4 : 4 ≤ Nat.card F := by
    have := Nat.le_of_dvd (by
      have : 1 < Nat.card F := Finite.one_lt_card
      omega) hpq
    omega
  have hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) := fun hd =>
    hpn (hd.trans ((CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd hn F).trans
      (Nat.gcd_dvd_left _ _)))
  obtain ⟨E₀, hmap, hdis, hE₀, hc₀⟩ := exists_sl_lift hZ E₁ hE₁ hc
  have : CFSG.IsElementaryAbelian p E₀ :=
    { toIsMulCommutative := hE₀.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE₀.2 x x.2) }
  have hnc : ¬ IsCyclic E₀ := CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hc₀
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let E'' : Subgroup (GL (Fin n) F) := E₀.map SpecialLinearGroup.toGL
  have hE''comm : ∀ x ∈ E'', ∀ y ∈ E'', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hE''exp : ∀ x ∈ E'', x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE₀.2 a ha, map_one]
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime
    (exists_primitiveRoot_of_dvd hp hpq) E'' hE''comm hE''exp
  let Dg : Subgroup (GL (Fin n) F) := E''.map (MulAut.conj P).toMonoidHom
  have hDdiag : ∀ x ∈ Dg, ∀ i j : Fin n, i ≠ j → (x : Matrix (Fin n) (Fin n) F) i j = 0 := by
    rintro _ ⟨y, hy, rfl⟩ i j hij
    exact hP y hy i j hij
  have hDfin : Finite Dg := inferInstance
  let f : E₀ →* Dg :=
    (((MulAut.conj P).toMonoidHom.comp SpecialLinearGroup.toGL).comp E₀.subtype).codRestrict
      Dg (fun x => ⟨_, ⟨x.1, x.2, rfl⟩, rfl⟩)
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : (P * SpecialLinearGroup.toGL x.1 * P⁻¹ : GL (Fin n) F) =
        P * SpecialLinearGroup.toGL y.1 * P⁻¹ := congrArg Subtype.val hxy
    have h2 : SpecialLinearGroup.toGL x.1 = SpecialLinearGroup.toGL y.1 := by simpa using h1
    exact Subtype.ext (SpecialLinearGroup.toGL_injective h2)
  have hDnc : ¬ IsCyclic Dg := fun hDc => hnc (isCyclic_of_injective f hfinj)
  have hpair : ∀ i j : Fin n, ∃ a ∈ E₀, a ≠ 1 ∧
      ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i =
        ((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j := by
    intro i j
    obtain ⟨x, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, hx1, hxij⟩ := exists_ne_one_diag_eq Dg hDdiag hDnc i j
    refine ⟨a, ha, fun h1 => hx1 ?_, hxij⟩
    change P * SpecialLinearGroup.toGL a * P⁻¹ = 1
    rw [h1, map_one, mul_one, mul_inv_cancel]
  have hpF : ¬ p ∣ Nat.card F := by
    intro hd'
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub hd' hpq
      have e : Nat.card F - (Nat.card F - 1) = 1 := by
        have : 1 < Nat.card F := Finite.one_lt_card
        omega
      rwa [e] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  apply eq_one_of_fixSub_toPSL
  set 𝒢 : Subgroup (SpecialLinearGroup (Fin n) F) := (fixSub g).comap (toPSL n F) with h𝒢
  have hall : (⊤ : Subgroup (SpecialLinearGroup (Fin n) F)) ≤ 𝒢.comap (conjSL P⁻¹) := by
    rw [← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n)
      (K := F), Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    obtain ⟨a, ha, ha1, hd⟩ := hpair t.i t.j
    have hpax : (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F)) ^ p = 1 := by
      have h1 : (a : Matrix (Fin n) (Fin n) F) ^ p = 1 := by
        have := congrArg (fun z : SpecialLinearGroup (Fin n) F => (z : Matrix (Fin n) (Fin n) F))
          (hE₀.2 a ha)
        simpa using this
      rw [← Matrix.toLin'_pow, h1, Matrix.toLin'_one]
      rfl
    have hsq := squarefree_minpoly_of_pow_eq_one (natCast_ne_zero_of_not_dvd_card hp hpF) hpax
    obtain ⟨hX, hmult, hmem⟩ := transvection_mem_blockImage a P
      (fun k l hkl => hP _ ⟨a, ha, rfl⟩ k l hkl) t.hij hd t.c hsq
    set h' : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F)) :=
      ⟨X - C (((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) t.i t.i), hX⟩ with hh'
    have hcardE : Nat.card (Efac (Matrix.toLin' (a : Matrix (Fin n) (Fin n) F)) h') =
        Nat.card F := by
      have : Fact (Irreducible (X - C (((P * SpecialLinearGroup.toGL a * P⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) t.i t.i) : F[X])) := ⟨irreducible_X_sub_C _⟩
      change Nat.card (AdjoinRoot (X - C _)) = _
      rw [natCard_adjoinRoot, natDegree_X_sub_C, pow_one]
    have hgood : GoodBlock h' := Or.inr ⟨hmult, by rw [hcardE]; omega⟩
    have hpd : p ∣ Nat.card (blockImage hsq h') :=
      dvd_card_blockImage_of_sub_one hp hsq h' hmult (by rw [hcardE]; exact hpq)
    have hπa : toPSL n F a ∈ E₁ := hmap ▸ ⟨a, ha, rfl⟩
    have hπ1 : toPSL n F a ≠ 1 := fun h1 => ha1 (Subgroup.disjoint_def.mp hdis ha
      (MonoidHom.mem_ker.2 h1))
    set s : SpecialLinearGroup (Fin n) F := conjSL P⁻¹ t.toSpecialLinearGroup with hsdef
    have hsmat : (s : Matrix (Fin n) (Fin n) F) =
        ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 + Matrix.single t.i t.j t.c) *
          (P : Matrix (Fin n) (Fin n) F) := by
      rw [hsdef, conjSL_coe, inv_inv]
      rfl
    have := blockPSL_le_fixSub hp hinj hZ hH hg ⟨_, hπa, rfl⟩ hπ1 hgood hpd
      ⟨s, hmem s hsmat, rfl⟩
    exact this
  rw [eq_top_iff]
  intro k _
  have h1 := hall (Subgroup.mem_top (conjSL P k))
  rw [Subgroup.mem_comap] at h1
  have h2 : conjSL P⁻¹ (conjSL P k) = k := by
    apply Subtype.ext
    rw [conjSL_coe, conjSL_coe, inv_inv]
    exact conj_cancel (G := (P : Matrix (Fin n) (Fin n) F))
      (Gi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) (unit_inv_mul P) _
  rw [h2] at h1
  exact h1

end Split

end CFSG.HardMathSupport.Timmesfeld.CrossChar
