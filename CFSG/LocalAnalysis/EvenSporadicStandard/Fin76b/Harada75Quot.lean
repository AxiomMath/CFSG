module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Four

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem quotConj_map {S : Type} [Group S] (K E : Subgroup S) [K.Normal] [E.Normal] (s : S) :
    (E.subgroupOf K).map ((MulAut.conjNormal s : MulAut K) : K →* K) = E.subgroupOf K := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_subgroupOf]
    change s * (y : S) * s⁻¹ ∈ E
    exact (inferInstance : E.Normal).conj_mem _ hy s
  · intro hx
    refine ⟨(MulAut.conjNormal s : MulAut K).symm x, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change s⁻¹ * (x : S) * s⁻¹⁻¹ ∈ E
      exact (inferInstance : E.Normal).conj_mem _ (Subgroup.mem_subgroupOf.mp hx) s⁻¹
    · exact (MulAut.conjNormal s : MulAut K).apply_symm_apply x

@[expose] def quotConj {S : Type} [Group S] (K E : Subgroup S) [K.Normal] [E.Normal] (s : S) :
    (K ⧸ E.subgroupOf K) ≃* (K ⧸ E.subgroupOf K) :=
  QuotientGroup.congr (E.subgroupOf K) (E.subgroupOf K) (MulAut.conjNormal s : MulAut K)
    (quotConj_map K E s)

theorem quotConj_mk {S : Type} [Group S] (K E : Subgroup S) [K.Normal] [E.Normal] (s : S)
    (k : K) :
    quotConj K E s (QuotientGroup.mk k) = QuotientGroup.mk (MulAut.conjNormal s k) :=
  QuotientGroup.congr_mk _ _ _ _ _

@[expose] def quotConjHom {S : Type} [Group S] (K E : Subgroup S) [K.Normal] [E.Normal] :
    S →* MulAut (K ⧸ E.subgroupOf K) :=
  MonoidHom.mk' (quotConj K E) (fun s t => by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.mul_apply, quotConj_mk, quotConj_mk, quotConj_mk]
      congr 1
      apply Subtype.ext
      simp [MulAut.conjNormal_apply, mul_assoc])

theorem quotFixD_comm {S : Type} [Group S] (g x : S) (hgg : g * g = 1) (hginv : g⁻¹ = g)
    (ha2 : (x⁻¹ * (g * x * g⁻¹)) * (x⁻¹ * (g * x * g⁻¹)) = 1) :
    (x⁻¹ * (g * x * g⁻¹)) * g = g * (x⁻¹ * (g * x * g⁻¹)) := by
  have hainv : (x⁻¹ * (g * x * g⁻¹))⁻¹ = x⁻¹ * (g * x * g⁻¹) := inv_eq_of_mul_eq_one_right ha2
  have hinv_expr : (x⁻¹ * (g * x * g⁻¹))⁻¹ = g * x⁻¹ * g⁻¹ * x := by group
  have h1 : x⁻¹ * (g * x * g⁻¹) = g * x⁻¹ * g⁻¹ * x := hainv.symm.trans hinv_expr
  have hL : (x⁻¹ * (g * x * g⁻¹)) * g = x⁻¹ * g * x := by group
  have hR : g * (x⁻¹ * (g * x * g⁻¹)) = x⁻¹ * g * x := by
    rw [h1]
    calc g * (g * x⁻¹ * g⁻¹ * x) = (g * g) * x⁻¹ * g⁻¹ * x := by group
      _ = x⁻¹ * g * x := by rw [hgg, hginv, one_mul]
  rw [hL, hR]

theorem quotFixD_ker_comm {S : Type} [Group S] (g x : S)
    (h : x⁻¹ * (g * x * g⁻¹) = 1) : x * g = g * x := by
  have h1 : x = g * x * g⁻¹ := inv_mul_eq_one.mp h
  exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm

theorem quotFixD_aux {S : Type} [Group S] (g x y : S)
    (hcomm : (x⁻¹ * (g * x * g⁻¹)) * y⁻¹ = y⁻¹ * (x⁻¹ * (g * x * g⁻¹))) :
    (x * y)⁻¹ * (g * (x * y) * g⁻¹) = (x⁻¹ * (g * x * g⁻¹)) * (y⁻¹ * (g * y * g⁻¹)) := by
  have key : (x * y)⁻¹ * (g * (x * y) * g⁻¹) = y⁻¹ * (x⁻¹ * (g * x * g⁻¹)) * (g * y * g⁻¹) := by
    group
  rw [key, ← hcomm]
  simp only [mul_assoc]

@[expose] def quotFixD {S : Type} [Group S] (K E : Subgroup S) [K.Normal] [E.Normal] (g : S) :
    Subgroup K :=
  (fourFix (quotConj K E g)).comap (QuotientGroup.mk' (E.subgroupOf K))

theorem mem_quotFixD {S : Type} [Group S] (K E : Subgroup S) [K.Normal] [E.Normal] (g : S)
    (k : K) : k ∈ quotFixD K E g ↔ (k : S)⁻¹ * (g * (k : S) * g⁻¹) ∈ E := by
  unfold quotFixD
  rw [Subgroup.mem_comap]
  change quotConj K E g (QuotientGroup.mk k) = QuotientGroup.mk k ↔ _
  rw [quotConj_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
  rw [show (k : S)⁻¹ * (g * (k : S) * g⁻¹) = ((g * (k : S) * g⁻¹)⁻¹ * (k : S))⁻¹ by group,
    Subgroup.inv_mem_iff]

theorem card_quotFixD {S : Type} [Group S] [Finite S] (K E : Subgroup S) [K.Normal] [E.Normal]
    (hEK : E ≤ K) (hE8 : Nat.card E = 8) (g : S) :
    Nat.card (quotFixD K E g) = 8 * Nat.card {q : K ⧸ E.subgroupOf K // quotConj K E g q = q} := by
  classical
  let m : quotFixD K E g →* K ⧸ E.subgroupOf K :=
    (QuotientGroup.mk' (E.subgroupOf K)).comp (quotFixD K E g).subtype
  have hmker : m.ker.map (quotFixD K E g).subtype = E.subgroupOf K := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : (QuotientGroup.mk (y : K) : K ⧸ E.subgroupOf K) = 1 := MonoidHom.mem_ker.mp hy
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro hx
      have hxD : x ∈ quotFixD K E g := by
        unfold quotFixD
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
        exact Subgroup.one_mem _
      exact ⟨⟨x, hxD⟩, MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff x).mpr hx), rfl⟩
  have hkerN : Nat.card m.ker = 8 := by
    rw [← Subgroup.card_map_of_injective (quotFixD K E g).subtype_injective, hmker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE8]
  have hrange : m.range = fourFix (quotConj K E g) := by
    ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_comap.mp y.2
    · intro hx
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
      have hk : k ∈ quotFixD K E g := by
        unfold quotFixD
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
        exact hx
      exact ⟨⟨k, hk⟩, rfl⟩
  have hcard : Nat.card m.range = Nat.card {q : K ⧸ E.subgroupOf K // quotConj K E g q = q} := by
    rw [hrange]
    rfl
  have hsplit := card_eq_ker_mul_range m
  rw [hkerN, hcard] at hsplit
  exact hsplit

theorem card_quotFixD_le {S : Type} [Group S] [Finite S] (K E : Subgroup S) [K.Normal]
    [E.Normal] (hEc : ∀ x ∈ E, ∀ k ∈ K, x * k = k * x) (hEexp : ∀ x ∈ E, x * x = 1)
    {g : S} (hgg : g * g = 1)
    (hCK : Nat.card (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) ≤ 4)
    (hCE : Nat.card (E ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) ≤ 4) :
    Nat.card (quotFixD K E g) ≤ 16 := by
  classical
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  obtain ⟨c, hc⟩ : ∃ c : quotFixD K E g →* S, ∀ d : quotFixD K E g,
      c d = ((d : K) : S)⁻¹ * (g * ((d : K) : S) * g⁻¹) :=
    ⟨MonoidHom.mk' (fun d : quotFixD K E g => ((d : K) : S)⁻¹ * (g * ((d : K) : S) * g⁻¹))
      (fun d1 d2 => by
        have ha := (mem_quotFixD K E g _).mp d1.2
        have hk : ((d2 : K) : S)⁻¹ ∈ K := K.inv_mem (d2 : K).2
        have hcomm := hEc _ ha _ hk
        simp only [Subgroup.coe_mul]
        exact quotFixD_aux g _ _ hcomm), fun d => rfl⟩
  have hcE : ∀ d : quotFixD K E g, c d ∈ E := by
    intro d
    rw [hc]
    exact (mem_quotFixD K E g _).mp d.2
  have hcC : ∀ d : quotFixD K E g, c d * g = g * c d := by
    intro d
    rw [hc]
    exact quotFixD_comm g _ hgg hginv (hEexp _ ((mem_quotFixD K E g _).mp d.2))
  let f1 : c.ker → ↥(K ⊓ Subgroup.centralizer ({g} : Set S)) := fun x =>
    ⟨x.1.1.1, Subgroup.mem_inf.mpr ⟨x.1.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (quotFixD_ker_comm g _ (by
        have h : c x.1 = 1 := MonoidHom.mem_ker.mp x.2
        rw [hc] at h
        exact h))⟩⟩
  have hinj : Function.Injective f1 := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact h
  have hkerC : Nat.card c.ker ≤ 4 :=
    le_trans (Nat.card_le_card_of_injective f1 hinj) hCK
  have hrangeC : c.range ≤ E ⊓ Subgroup.centralizer ({g} : Set S) := by
    intro y hy
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
    exact Subgroup.mem_inf.mpr ⟨hcE d, Subgroup.mem_centralizer_singleton_iff.mpr (hcC d)⟩
  have hrangeC' : Nat.card c.range ≤ 4 := le_trans (Subgroup.card_le_of_le hrangeC) hCE
  have hsplit := card_eq_ker_mul_range c
  calc Nat.card (quotFixD K E g) = Nat.card c.ker * Nat.card c.range := hsplit
    _ ≤ 4 * 4 := Nat.mul_le_mul hkerC hrangeC'
    _ = 16 := by norm_num

theorem card_fixed_le_two {S : Type} [Group S] [Finite S] (K E : Subgroup S) [K.Normal]
    [E.Normal] (hEK : E ≤ K) (hEc : ∀ x ∈ E, ∀ k ∈ K, x * k = k * x)
    (hEexp : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8) {g : S} (hgg : g * g = 1)
    (hCK : Nat.card (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) ≤ 4)
    (hCE : Nat.card (E ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) ≤ 4) :
    Nat.card {q : K ⧸ E.subgroupOf K // quotConj K E g q = q} ≤ 2 := by
  have h1 := card_quotFixD K E hEK hE8 g
  have h2 := card_quotFixD_le K E hEc hEexp hgg hCK hCE
  omega

theorem card_le_sixteen_of_fourGroup {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {K E F : Subgroup S} (hKn : K.Normal) (hEn : E.Normal) (hEK : E ≤ K)
    (hEc : ∀ x ∈ E, ∀ k ∈ K, x * k = k * x) (hEexp : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8)
    (hFexp : ∀ f ∈ F, f * f = 1) (hF4 : Nat.card F = 4)
    (hCK : ∀ f ∈ F, f ≠ 1 → Nat.card (K ⊓ Subgroup.centralizer ({f} : Set S) : Subgroup S) ≤ 4)
    (hCE : ∀ f ∈ F, f ≠ 1 → Nat.card (E ⊓ Subgroup.centralizer ({f} : Set S) : Subgroup S) ≤ 4) :
    Nat.card K ≤ 16 := by
  classical
  have := hKn
  have := hEn
  have hQ : IsPGroup 2 (K ⧸ E.subgroupOf K) := (hS.to_subgroup K).to_quotient (E.subgroupOf K)
  have hF2 : IsPGroup 2 F := hS.to_subgroup F
  have hfix : ∀ f : F, f ≠ 1 →
      Nat.card {q : K ⧸ E.subgroupOf K // ((quotConjHom K E).comp F.subtype f) q = q} ≤ 2 := by
    intro f hf
    have hf1 : (f : S) ≠ 1 := fun h => hf (Subtype.ext h)
    exact card_fixed_le_two K E hEK hEc hEexp hE8 (hFexp (f : S) f.2) (hCK (f : S) f.2 hf1)
      (hCE (f : S) f.2 hf1)
  have hQle := card_le_two_of_fourGroup hQ hF2 (le_of_eq hF4.symm)
    ((quotConjHom K E).comp F.subtype) hfix
  have hidx := Subgroup.card_mul_index (E.subgroupOf K)
  rw [Subgroup.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE8]
    at hidx
  omega

end CFSG.EvenSporadicStandard.Fin76b
