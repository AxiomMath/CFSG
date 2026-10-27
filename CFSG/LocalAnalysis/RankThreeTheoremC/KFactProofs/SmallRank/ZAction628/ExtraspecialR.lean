module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Clifford
public import CFSG.GF2Type.Aschbacher1976Full.ShapeStructure
public import CFSG.GF2Type.Aschbacher1976Full.ShapeBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
  CFSG.GF2Type.Aschbacher1976Full.Shape
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem hallR_conj_coe {R : Subgroup K} {z : K} (hzR : z ∈ normalizer (R : Set K)) (x : ↥R) :
    ((Subgroup.normalizerMonoidHom R ⟨z, hzR⟩ x : ↥R) : K) = z * x * z⁻¹ := rfl

theorem hallR_normalizer_lift_of_char {R : Subgroup K} {z : K}
    (hzR : z ∈ normalizer (R : Set K)) {A : Subgroup ↥R} (hA : A.Characteristic) :
    z ∈ normalizer ((A.map R.subtype : Subgroup K) : Set K) := by
  set φ : MulAut ↥R := Subgroup.normalizerMonoidHom R ⟨z, hzR⟩ with hφ
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨φ a, CFSG.SectionRank.Ccomm.char_apply_mem hA φ ha, hallR_conj_coe hzR a⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨φ.symm a, CFSG.SectionRank.Ccomm.char_apply_mem hA φ.symm ha, ?_⟩
    have h1 : φ (φ.symm a) = a := φ.apply_symm_apply a
    have h2 : z * ((φ.symm a : ↥R) : K) * z⁻¹ = (a : K) := by
      rw [← hallR_conj_coe hzR, h1]
    have h3 : (a : K) = z * h * z⁻¹ := hax
    rw [h3] at h2
    have h4 : z * ((φ.symm a : ↥R) : K) * z⁻¹ = z * h * z⁻¹ := h2
    simpa using h4

theorem hallR_symplectic {R : Subgroup K} {z : K} (hzR : z ∈ normalizer (R : Set K))
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z)
    (hcyc : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, z * a = a * z) → IsCyclic A) :
    ∀ A : Subgroup ↥R, A.Characteristic → IsMulCommutative A → IsCyclic A := by
  intro A hA hAc
  have hcomm : ∀ a ∈ A.map R.subtype, ∀ b ∈ A.map R.subtype, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := isMulCommutative_iff.mp hAc ⟨a, ha⟩ ⟨b, hb⟩
    have h2 := congrArg (fun x : ↥A => ((x : ↥R) : K)) this
    exact h2
  have hz : ∀ a ∈ A.map R.subtype, z * a = a * z :=
    hstar _ (Subgroup.map_subtype_le A) hcomm (hallR_normalizer_lift_of_char hzR hA)
  have hc := hcyc _ (Subgroup.map_subtype_le A) hcomm hz
  exact (MulEquiv.isCyclic (liftEquiv A)).mpr hc

theorem hallR_zpowers_comm {z x g : K} (h : z * x = x * z) (hg : g ∈ zpowers z) :
    g * x = x * g := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  exact (Commute.zpow_left (show Commute z x from h) n).eq

theorem hallR_coe_mem_zpowers {R : Subgroup K} {a b : ↥R} (h : a ∈ zpowers b) :
    (a : K) ∈ zpowers (b : K) := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp h
  exact mem_zpowers_iff.mpr ⟨n, by simp⟩

theorem hallR_mem_zpowers_of_coe {R : Subgroup K} {a b : ↥R} (h : (a : K) ∈ zpowers (b : K)) :
    a ∈ zpowers b := by
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h
  exact mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩

theorem hallR_Z_fixed {R : Subgroup K} {z : K} (hzR : z ∈ normalizer (R : Set K))
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z)
    {D E Rc : Subgroup ↥R} {t' : ↥R} (c : CritData D E Rc t') :
    ∀ w ∈ Zof D, z * (w : K) = (w : K) * z := by
  have hcomm : ∀ a ∈ (Zof D).map R.subtype, ∀ b ∈ (Zof D).map R.subtype, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg (fun x : ↥R => (x : K)) (CritData.Z_comm D hb (CritData.Z_le_D D ha))
  have := hstar _ (Subgroup.map_subtype_le _) hcomm (hallR_normalizer_lift_of_char hzR c.char)
  intro w hw
  exact this _ ⟨w, hw, rfl⟩

theorem hallR_commutator_le {R : Subgroup K} {z : K} (hzR : z ∈ normalizer (R : Set K))
    {D E Rc : Subgroup ↥R} {t' : ↥R} (c : CritData D E Rc t')
    (hfixZ : ∀ w ∈ Zof D, z * (w : K) = (w : K) * z) :
    ⁅R, zpowers z⁆ ≤ D.map R.subtype := by
  rw [commutator_le]
  intro x hx g hg
  have hgR : g ∈ normalizer (R : Set K) := (zpowers_le.mpr hzR) hg
  set φ : MulAut ↥R := Subgroup.normalizerMonoidHom R ⟨g, hgR⟩ with hφ
  have hφZ : ∀ w ∈ Zof D, φ w = w := by
    intro w hw
    apply Subtype.ext
    rw [hallR_conj_coe, hallR_zpowers_comm (hfixZ w hw) hg, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨x, rfl⟩ : ∃ x' : ↥R, (x' : K) = x := ⟨⟨x, hx⟩, rfl⟩
  have hmem : x * (φ x)⁻¹ ∈ D := by
    rw [← c.cent, mem_centralizer_iff]
    intro w hw
    have hw'' : x⁻¹ * w * x ∈ Zof D := by
      have := c.Z_normal.conj_mem w hw x⁻¹
      simpa using this
    have h1 : φ (x⁻¹ * w * x) = x⁻¹ * w * x := hφZ _ hw''
    rw [map_mul, map_mul, map_inv, hφZ w hw] at h1
    calc w * (x * (φ x)⁻¹) = x * (x⁻¹ * w * x) * (φ x)⁻¹ := by group
      _ = x * ((φ x)⁻¹ * w * φ x) * (φ x)⁻¹ := by rw [h1]
      _ = x * (φ x)⁻¹ * w := by group
  refine ⟨x * (φ x)⁻¹, hmem, ?_⟩
  · show ((x * (φ x)⁻¹ : ↥R) : K) = _
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hallR_conj_coe, commutatorElement_def]
    group

theorem hallR_D_top {R : Subgroup K} {z : K} (hperf : ⁅R, zpowers z⁆ = R)
    {D : Subgroup ↥R} (hle : ⁅R, zpowers z⁆ ≤ D.map R.subtype) : ∀ x : ↥R, x ∈ D := by
  intro x
  have hx : (x : K) ∈ D.map R.subtype := hle (by rw [hperf]; exact x.2)
  exact (Subgroup.mem_map_iff_mem R.subtype_injective).mp hx

theorem hallR_comm_mul_central {G : Type*} [Group G] {e₁ e₂ y₁ y₂ : G}
    (h₁ : ∀ d, d * y₁ = y₁ * d) (h₂ : ∀ d, d * y₂ = y₂ * d) :
    ⁅e₁ * y₁, e₂ * y₂⁆ = ⁅e₁, e₂⁆ := by
  simp only [commutatorElement_def]
  have a1 : (e₁ * y₁)⁻¹ * y₂ = y₂ * (e₁ * y₁)⁻¹ := h₂ _
  have a2 : y₁ * e₂ = e₂ * y₁ := (h₁ e₂).symm
  calc e₁ * y₁ * (e₂ * y₂) * (e₁ * y₁)⁻¹ * (e₂ * y₂)⁻¹
      = e₁ * y₁ * e₂ * (y₂ * (e₁ * y₁)⁻¹) * y₂⁻¹ * e₂⁻¹ := by group
    _ = e₁ * y₁ * e₂ * ((e₁ * y₁)⁻¹ * y₂) * y₂⁻¹ * e₂⁻¹ := by rw [a1]
    _ = e₁ * (y₁ * e₂) * (e₁ * y₁)⁻¹ * e₂⁻¹ := by group
    _ = e₁ * (e₂ * y₁) * (e₁ * y₁)⁻¹ * e₂⁻¹ := by rw [a2]
    _ = e₁ * e₂ * e₁⁻¹ * e₂⁻¹ := by group

theorem hallR_mem_of_pow_mem {R : Subgroup K} (hR2 : IsPGroup 2 R) {B : Subgroup K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {r : K} (hr : r ∈ R) (h : r ^ p ∈ B) : r ∈ B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR2) ⟨r, hr⟩
  rw [Subgroup.orderOf_mk] at hk
  have hcop : Nat.Coprime p (orderOf r) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem h m

theorem hallR_case_bot {R : Subgroup K} {z : K} (hzR : z ∈ normalizer (R : Set K))
    (hperf : ⁅R, zpowers z⁆ = R) (hRne : R ≠ ⊥)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z)
    {D E Rc : Subgroup ↥R} {t' : ↥R} (c : CritData D E Rc t')
    (hDtop : ∀ x : ↥R, x ∈ D) (hE : E = ⊥) : False := by
  have hDZ : D = Zof D := c.D_eq_Z hE
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    have h1 : (⟨b, hb⟩ : ↥R) ∈ Zof D := by rw [← hDZ]; exact hDtop _
    have := CritData.Z_comm D h1 (hDtop ⟨a, ha⟩)
    exact congrArg (fun x : ↥R => (x : K)) this
  have hzc := hstar R le_rfl hRcomm hzR
  apply hRne
  rw [eq_bot_iff, ← hperf, commutator_le]
  intro x hx g hg
  rw [mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hallR_zpowers_comm (hzc x hx) hg).symm

theorem hallR_case_ext {R : Subgroup K} {z : K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hz : z ^ p = 1) (hR2 : IsPGroup 2 R) (hzR : z ∈ normalizer (R : Set K))
    (hperf : ⁅R, zpowers z⁆ = R)
    {D E Rc : Subgroup ↥R} {t' : ↥R} (c : CritData D E Rc t')
    (hfixZ : ∀ w ∈ Zof D, z * (w : K) = (w : K) * z) (hDtop : ∀ x : ↥R, x ∈ D)
    (hEZ : E ⊓ Zof D = zpowers t') (hEc : (center E).map E.subtype = zpowers t') :
    ∃ t : K, IsExt2 R t ∧ z * t = t * z ∧ ∀ r ∈ R, z * r = r * z → r ∈ zpowers t := by
  have hZc : ∀ y ∈ Zof D, ∀ d : ↥R, d * y = y * d := fun y hy d => CritData.Z_comm D hy (hDtop d)
  have hcomm : ∀ a b : ↥R, ⁅a, b⁆ ∈ zpowers t' := by
    intro a b
    obtain ⟨e₁, he₁, y₁, hy₁, rfl⟩ := c.exists_mul_of_mem_D (hDtop a)
    obtain ⟨e₂, he₂, y₂, hy₂, rfl⟩ := c.exists_mul_of_mem_D (hDtop b)
    rw [hallR_comm_mul_central (hZc y₁ hy₁) (hZc y₂ hy₂)]
    exact c.E_comm e₁ he₁ e₂ he₂
  have hRR : ⁅R, R⁆ ≤ zpowers (t' : K) := by
    rw [commutator_le]
    intro a ha b hb
    exact hallR_coe_mem_zpowers (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
  have hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers (t' : K) := by
    intro r hr hrz
    have hr' : r ∈ ⁅zpowers z, R⁆ := by rw [commutator_comm, hperf]; exact hr
    have h1 := pow_mem_commutator_of_fixed (P := R) hz hzR hr' hrz
    exact hallR_mem_of_pow_mem hR2 hp hp2 hr (hRR h1)
  have hZle : ∀ w ∈ Zof D, w ∈ zpowers t' := fun w hw =>
    hallR_mem_zpowers_of_coe (hfix w w.2 (hfixZ w hw))
  have hzE : zpowers t' ≤ E := hEZ ▸ inf_le_left
  have hEtop : ∀ x : ↥R, x ∈ E := by
    intro x
    obtain ⟨e, he, y, hy, rfl⟩ := c.exists_mul_of_mem_D (hDtop x)
    exact E.mul_mem he (hzE (hZle y hy))
  have ht2 : t' ^ 2 = 1 := by
    have := pow_orderOf_eq_one t'
    rwa [c.z_ord] at this
  refine ⟨(t' : K), ⟨t'.2, ?_, ?_, ?_, ?_, ?_, ?_⟩, hfixZ t' c.z_mem, hfix⟩
  · have := congrArg (fun x : ↥R => (x : K)) ht2
    simpa using this
  · intro h
    have h1 : t' = 1 := Subtype.ext h
    have := c.z_ord
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  · intro r hr
    have := mem_center_iff.mp c.z_center ⟨r, hr⟩
    exact congrArg (fun x : ↥R => (x : K)) this
  · intro y hy hyc
    have hyE : (⟨y, hy⟩ : ↥R) ∈ E := hEtop _
    have hcen : (⟨⟨y, hy⟩, hyE⟩ : ↥E) ∈ center E := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      apply Subtype.ext
      exact (hyc _ g.1.2).symm
    have : (⟨y, hy⟩ : ↥R) ∈ zpowers t' := by
      rw [← hEc]
      exact ⟨_, hcen, rfl⟩
    exact hallR_coe_mem_zpowers this
  · intro r hr
    exact hallR_coe_mem_zpowers (c.E_sq ⟨r, hr⟩ (hEtop _))
  · intro r hr s hs
    exact hallR_coe_mem_zpowers (hcomm ⟨r, hr⟩ ⟨s, hs⟩)

theorem extraspecial_of_zperfect {R : Subgroup K} {z : K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hz : z ^ p = 1) (hR2 : IsPGroup 2 R) (hRne : R ≠ ⊥) (hzR : z ∈ normalizer (R : Set K))
    (hperf : ⁅R, zpowers z⁆ = R)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z)
    (hcyc : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, z * a = a * z) → IsCyclic A) :
    ∃ t : K, IsExt2 R t ∧ z * t = t * z ∧ ∀ r ∈ R, z * r = r * z → r ∈ zpowers t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
  obtain ⟨D, hD⟩ := (CFSG.SectionRank.Ccomm.thompson_critical_subgroup hR2).1
  obtain ⟨E, Rc, t', c⟩ := exists_critData hR2 (hallR_symplectic hzR hstar hcyc) hD
  have hfixZ := hallR_Z_fixed hzR hstar c
  have hDtop := hallR_D_top hperf (hallR_commutator_le hzR c hfixZ)
  rcases c.cases with ⟨hE, -⟩ | ⟨w, -, -, -, -, hEZ, hEc, -⟩
  · exact (hallR_case_bot hzR hperf hRne hstar c hDtop hE).elim
  · exact hallR_case_ext hp hp2 hz hR2 hzR hperf c hfixZ hDtop hEZ hEc
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem R_isExt2 {p f : ℕ} {S X N : Subgroup K} {z : K} (h : Setup628 p f S X N z) :
    ∃ t : K, IsExt2 (RR S z) t ∧ z * t = t * z ∧
      ∀ r ∈ RR S z, z * r = r * z → r ∈ zpowers t :=
  extraspecial_of_zperfect h.hp h.hp2 h.hzp (h.hS.to_le (RR_le_S h.hzS)) h.hR
    (normalizer_commutator_ge_left _ _ (mem_zpowers z))
    (commutator_RR_eq h.hp h.hp2 h.hS h.hzp h.hz1 h.hzS)
    (fun A hAR hAc hzA => z_centralizes_abelian h (hAR.trans (RR_le_S h.hzS)) hAc hzA)
    (fun A hAR hAc hzA => isCyclic_of_abelian_centralizer h (hAR.trans (RR_le_S h.hzS)) hAc hzA)
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
