module

public import CFSG.CGT.Foote81L6.Normalizer.GroupAux
public import CFSG.Adapters.Involutions
public import CFSG.HardMathSupport.Foote.E27.LieTwo.SylowNormal
public import CFSG.CGT.Foote81L6.Normalizer.Hyp
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

namespace TvHyp

variable {V X : Type} [CommGroup V] [Group X] [Finite X] {ρ : X →* MulAut V} {D : Sylow 2 X}
  {d₀ d₁ : X}

theorem exists_conj_mem_normalClosure (h : TvHyp ρ D d₀ d₁)
    (hnc : ¬ HasNormalPComplement 2 X) :
    ∃ x ∈ Subgroup.normalClosure ({d₀} : Set X), x * d₀ * x⁻¹ = d₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hbad
  push Not at hbad
  set X₀ := Subgroup.normalClosure ({d₀} : Set X) with hX₀
  have hd₀X₀ : d₀ ∈ X₀ := Subgroup.subset_normalClosure rfl
  have hconjX₀ : ∀ g : X, g * d₀ * g⁻¹ ∈ X₀ := fun g =>
    Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨d₀, rfl, isConj_iff.mpr ⟨g, rfl⟩⟩)
  have hisoX₀ : ∀ t : X, IsConj d₀ t → t ∈ X₀ := fun t ht => by
    obtain ⟨g, rfl⟩ := isConj_iff.mp ht
    exact hconjX₀ g
  have hDmem : ∀ {a b : X}, a ∈ (D : Subgroup X) → b ∈ (D : Subgroup X) →
      a * b * a⁻¹ ∈ (D : Subgroup X) := fun ha hb =>
    (D : Subgroup X).mul_mem ((D : Subgroup X).mul_mem ha hb) ((D : Subgroup X).inv_mem ha)
  have hfix₀ : ∀ x ∈ X₀, x * d₀ * x⁻¹ ∈ (D : Subgroup X) → x * d₀ * x⁻¹ = d₀ := by
    intro x hx hxD
    rcases h.conj_eq hxD with h1 | h1
    · exact h1
    · exact absurd h1 (hbad x hx)
  obtain ⟨hcomm01, -, -, -, -, -, hcent, -⟩ := h.dihedral_facts
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq X₀ D
  have hPD : ∀ s : X₀, s ∈ (P : Subgroup X₀) → (s : X) ∈ (D : Subgroup X) := fun s hs => by
    rw [hP] at hs
    exact hs
  have hd₀P : (⟨d₀, hd₀X₀⟩ : X₀) ∈ (P : Subgroup X₀) := by
    rw [hP]
    exact h.mem₀
  set z : (P : Subgroup X₀) := ⟨⟨d₀, hd₀X₀⟩, hd₀P⟩
  have hzZ : z ∈ Subgroup.center (P : Subgroup X₀) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hsD := hPD s s.2
    have h1 := hfix₀ _ (s : X₀).2 (hDmem hsD h.mem₀)
    apply Subtype.ext; apply Subtype.ext
    show ((s : X₀) : X) * d₀ = d₀ * ((s : X₀) : X)
    calc ((s : X₀) : X) * d₀ = ((s : X₀) : X) * d₀ * ((s : X₀) : X)⁻¹ * ((s : X₀) : X) := by
          group
      _ = d₀ * ((s : X₀) : X) := by rw [h1]
  have hz2 : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.sq₀) h.ne_one₀
  have hwc : ∀ g : X₀, g⁻¹ * (z : X₀) * g ∈ (P : Subgroup X₀) → g⁻¹ * (z : X₀) * g = z := by
    intro g hg
    have hgD := hPD _ hg
    have h1 := hfix₀ _ (X₀.inv_mem g.2) (by simpa using hgD)
    apply Subtype.ext
    simpa using h1
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar P z hzZ hz2 hwc
  set O := pPrimeCore 2 X with hO
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hle : CFSG.oddCore X₀ ≤ (π.comp X₀.subtype).ker := by
    rw [oddCore_eq_pPrimeCore_two]
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact map_pPrimeCore_le ⟨k, hk, rfl⟩
  set ψ₀ : X₀ ⧸ CFSG.oddCore X₀ →* X ⧸ O := QuotientGroup.lift _ (π.comp X₀.subtype) hle
  have hcomm₀ : ∀ g ∈ X₀, π g * π d₀ = π d₀ * π g := by
    intro g hg
    have := congrArg ψ₀ (Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk ⟨g, hg⟩))
    simpa [ψ₀, map_mul] using this
  have hcommt : ∀ t : X, IsConj d₀ t → ∀ g ∈ X₀, π g * π t = π t * π g := by
    intro t ht g hg
    obtain ⟨c, rfl⟩ := isConj_iff.mp ht
    have hg' : c⁻¹ * g * c ∈ X₀ := by
      have := (Subgroup.normalClosure_normal (s := ({d₀} : Set X))).conj_mem g hg c⁻¹
      simpa using this
    have h1 := hcomm₀ _ hg'
    have e1 : π g * π (c * d₀ * c⁻¹) = π c * (π (c⁻¹ * g * c) * π d₀) * (π c)⁻¹ := by
      simp only [map_mul, map_inv]; group
    have e2 : π (c * d₀ * c⁻¹) * π g = π c * (π d₀ * π (c⁻¹ * g * c)) * (π c)⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [e1, e2, h1]
  have hcls : ∀ t : X, IsConj d₀ t → π t = π d₀ ∨ π t = π d₁ := by
    intro t ht
    have htX₀ := hisoX₀ t ht
    have ht2 : t * t = 1 := by
      obtain ⟨c, rfl⟩ := isConj_iff.mp ht
      calc c * d₀ * c⁻¹ * (c * d₀ * c⁻¹) = c * (d₀ * d₀) * c⁻¹ := by group
        _ = 1 := by rw [h.sq₀, mul_one, mul_inv_cancel]
    obtain ⟨x, hx⟩ := exists_conj_mem_sylow_two P (t := ⟨t, htX₀⟩) (Subtype.ext ht2)
    have hxD : (x : X) * t * (x : X)⁻¹ ∈ (D : Subgroup X) := by simpa using hPD _ hx
    have hxt : IsConj d₀ ((x : X) * t * (x : X)⁻¹) := ht.trans (isConj_iff.mpr ⟨x, rfl⟩)
    have hpi : ∀ d : X, IsConj d₀ d → (x : X) * t * (x : X)⁻¹ = d → π t = π d := by
      intro d hd hxd
      have ht' : t = (x : X)⁻¹ * d * x := by rw [← hxd]; group
      have hc := hcommt d hd x x.2
      rw [ht', map_mul, map_mul, map_inv]
      calc (π x)⁻¹ * π d * π x = (π x)⁻¹ * (π d * π x) := by group
        _ = (π x)⁻¹ * (π x * π d) := by rw [hc]
        _ = π d := by group
    rcases (h.fusion _ hxD).mp hxt with h1 | h1
    · exact Or.inl (hpi d₀ (IsConj.refl d₀) h1)
    · exact Or.inr (hpi d₁ h.isConj₁ h1)
  have hne : π d₀ ≠ π d₁ := fun h1 => h.ne (eq_of_mk_eq_of_mem_sylow D h.mem₀ h.mem₁ h1)
  have hodd₀ : ∀ y : X ⧸ O, Odd (orderOf y) → y * π d₀ * y⁻¹ = π d₀ ∧ y * π d₁ * y⁻¹ = π d₁ := by
    intro y hy
    obtain ⟨g, rfl⟩ := hπs y
    have ha : π g * π d₀ * (π g)⁻¹ = π d₀ ∨ π g * π d₀ * (π g)⁻¹ = π d₁ := by
      have := hcls (g * d₀ * g⁻¹) (isConj_iff.mpr ⟨g, rfl⟩)
      simpa [map_mul, map_inv] using this
    have hb : π g * π d₁ * (π g)⁻¹ = π d₀ ∨ π g * π d₁ * (π g)⁻¹ = π d₁ := by
      have := hcls (g * d₁ * g⁻¹) (h.isConj₁.trans (isConj_iff.mpr ⟨g, rfl⟩))
      simpa [map_mul, map_inv] using this
    refine ⟨conj_fix_of_odd hy hne ha hb, conj_fix_of_odd hy hne.symm hb.symm ha.symm⟩
  set Xh₀ : Subgroup (X ⧸ O) := X₀.map π with hXh₀
  have : Xh₀.Normal := Subgroup.Normal.map inferInstance π hπs
  set C : Subgroup (X ⧸ O) := Subgroup.centralizer (Xh₀ : Set (X ⧸ O)) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hmemC : ∀ y : X ⧸ O, y * π d₀ = π d₀ * y → y * π d₁ = π d₁ * y → y ∈ C := by
    intro y hy0 hy1
    rw [hC, Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    refine Subgroup.closure_induction (p := fun a _ => π a * y = y * π a) ?_ ?_ ?_ ?_ ha
    · intro c hc
      obtain ⟨b, hb, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hc
      rw [Set.mem_singleton_iff] at hb
      rw [hb] at hconj
      rcases hcls c hconj with h1 | h1
      · rw [h1]; exact hy0.symm
      · rw [h1]; exact hy1.symm
    · simp
    · intro a b _ _ ha hb
      rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    · intro a _ ha
      rw [map_inv]
      calc (π a)⁻¹ * y = (π a)⁻¹ * (y * π a) * (π a)⁻¹ := by group
        _ = (π a)⁻¹ * (π a * y) * (π a)⁻¹ := by rw [ha]
        _ = y * (π a)⁻¹ := by group
  set Dbar : Sylow 2 (X ⧸ O) := D.mapSurjective hπs
  obtain ⟨PC, hPC⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq C Dbar
  have hPCcent : ∀ s ∈ (PC : Subgroup C), ∀ c : C, s * c = c * s := by
    intro s hs c
    rw [hPC] at hs
    obtain ⟨e, heD, hes⟩ : ∃ e ∈ (D : Subgroup X), π e = (s : X ⧸ O) := hs
    have hsC : (s : X ⧸ O) ∈ Subgroup.centralizer (Xh₀ : Set (X ⧸ O)) := s.2
    rw [Subgroup.mem_centralizer_iff] at hsC
    have he0 : e * d₀ = d₀ * e := by
      have := hsC (π d₀) ⟨d₀, hd₀X₀, rfl⟩
      rw [← hes, ← map_mul, ← map_mul] at this
      exact (eq_of_mk_eq_of_mem_sylow D ((D : Subgroup X).mul_mem h.mem₀ heD)
        ((D : Subgroup X).mul_mem heD h.mem₀) this).symm
    have hd₁X₀ : d₁ ∈ X₀ := hisoX₀ d₁ h.isConj₁
    have he1 : e * d₁ = d₁ * e := by
      have := hsC (π d₁) ⟨d₁, hd₁X₀, rfl⟩
      rw [← hes, ← map_mul, ← map_mul] at this
      exact (eq_of_mk_eq_of_mem_sylow D ((D : Subgroup X).mul_mem h.mem₁ heD)
        ((D : Subgroup X).mul_mem heD h.mem₁) this).symm
    have heX₀ : e ∈ X₀ := by
      rcases hcent e heD he0 he1 with h1 | h1 | h1 | h1
      · rw [h1]; exact X₀.one_mem
      · rw [h1]; exact hd₀X₀
      · rw [h1]; exact hd₁X₀
      · rw [h1]; exact X₀.mul_mem hd₀X₀ hd₁X₀
    have hcC : (c : X ⧸ O) ∈ Subgroup.centralizer (Xh₀ : Set (X ⧸ O)) := c.2
    rw [Subgroup.mem_centralizer_iff] at hcC
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hes]
    exact hcC (π e) ⟨e, heX₀, rfl⟩
  have hPCle : (PC : Subgroup C) ≤ CFSG.centerIn (Subgroup.normalizer (PC : Subgroup C)) := by
    intro s hs
    exact ⟨Subgroup.le_normalizer hs,
      Subgroup.mem_centralizer_iff.mpr fun c _ => (hPCcent s hs c).symm⟩
  have hcompl := CFSG.hasNormalPComplement_of_sylow_le_center_normalizer 2 PC hPCle
  have hquot := CFSG.isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 C hcompl
  have hOC : pPrimeCore 2 C = ⊥ := by
    have h1 : (pPrimeCore 2 C).map C.subtype ≤ pPrimeCore 2 (X ⧸ O) := map_pPrimeCore_le
    rw [CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two, le_bot_iff,
      Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at h1
    exact h1
  have hC2 : ∀ c : C, ∃ k : ℕ, c ^ 2 ^ k = 1 := by
    intro c
    obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk c)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hOC] at hk
    exact hk
  have hX2 : IsPGroup 2 (X ⧸ O) := by
    intro y
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    refine ⟨k, ?_⟩
    have hord : orderOf (y ^ 2 ^ k) = m := by
      rw [orderOf_pow' y (pow_ne_zero k two_ne_zero), hkm,
        Nat.gcd_eq_right (Dvd.intro m rfl), Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    have hodd : Odd (orderOf (y ^ 2 ^ k)) := by rw [hord]; exact hm
    obtain ⟨h0, h1⟩ := hodd₀ _ hodd
    have hyC : y ^ 2 ^ k ∈ C := hmemC _ (by
      calc y ^ 2 ^ k * π d₀ = y ^ 2 ^ k * π d₀ * (y ^ 2 ^ k)⁻¹ * y ^ 2 ^ k := by group
        _ = π d₀ * y ^ 2 ^ k := by rw [h0]) (by
      calc y ^ 2 ^ k * π d₁ = y ^ 2 ^ k * π d₁ * (y ^ 2 ^ k)⁻¹ * y ^ 2 ^ k := by group
        _ = π d₁ * y ^ 2 ^ k := by rw [h1])
    obtain ⟨j, hj⟩ := hC2 ⟨_, hyC⟩
    have hj' : (y ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    exact eq_one_of_pow_two_pow_of_odd hj' hodd
  exact hnc ⟨O, pPrimeCore_normal, pPrimeCore_coprime_card, hX2⟩

end TvHyp

end CFSG.CGT.Foote81L6.Normalizer
