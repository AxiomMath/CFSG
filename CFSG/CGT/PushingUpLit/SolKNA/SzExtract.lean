module

public import CFSG.CGT.PushingUpLit.SolKNA.SzCommAux
public import CFSG.CGT.PushingUpLit.SolKNA.SzFpf
public import CFSG.CGT.PushingUpLit.SolKNA.SzWeightDef
public import CFSG.CGT.PushingUpLit.SolKNA.Prop18Norm

public section

open scoped IsMulCommutative

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.SzExplicit

variable {X : Type} [Group X] [Finite X]

theorem torusSz_inv (a : ℕ) (x : (F a)ˣ) : torusSz a x⁻¹ = (torusSz a x)⁻¹ :=
  Subtype.ext (Units.ext rfl)

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N)
include S

theorem mul_mem_L_of_mk_eq [N.Normal] {r r' : X} (hr : r ∈ R) (hr' : r' ∈ R)
    (h : QuotientGroup.mk' N r = QuotientGroup.mk' N r') : r⁻¹ * r' ∈ L := by
  have h1 : r⁻¹ * r' ∈ N := by
    rw [← QuotientGroup.eq]
    exact h
  have h2 : r⁻¹ * r' ∈ R ⊓ N := Subgroup.mem_inf.mpr ⟨R.mul_mem (R.inv_mem hr) hr', h1⟩
  rwa [S.inf_N] at h2

theorem comm_mem_N {r s : X} (hr : r ∈ R) (hs : s ∈ R) : r * s * r⁻¹ * s⁻¹ ∈ N :=
  S.L_le_N (S.comm_R r hr s hs)

theorem abelian_of_weight_data [N.Normal] (hW : SzCommutatorWeight) {a : ℕ} (ha : 1 ≤ a)
    (e : X ⧸ N ≃* ↥(Sz a)) (g₀ : ↥(Sz a))
    (hRg : ∀ y : ↥(Sz a), (∃ r ∈ R, e (QuotientGroup.mk' N r) = y) ↔
      ∃ b : F a, y = g₀ * rootSz a 0 b * g₀⁻¹)
    (hadd : ∀ b b' : F a, rootSz a 0 b * rootSz a 0 b' = rootSz a 0 (b + b'))
    (hcent : ∀ α β b : F a, rootSz a α β * rootSz a 0 b = rootSz a 0 b * rootSz a α β)
    (htor : ∀ (x : (F a)ˣ) (b : F a), torusSz a x * rootSz a 0 b * (torusSz a x)⁻¹ =
      rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1)) * b))
    (hfpf : ∃ g : X, orderOf (e (QuotientGroup.mk' N g)) = 5 ∧
      ∀ n ∈ N, g * n = n * g → n = 1) :
    ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
  classical
  have : IsMulCommutative ↥N := ⟨⟨fun x y => Subtype.ext (S.comm_N x.2 y.2)⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Module (ZMod 2) (Additive ↥N) := AddCommGroup.zmodModule fun v => by
    rw [two_nsmul]
    exact Additive.toMul.injective (Subtype.ext (S.sq_N _ v.toMul.2))
  have hnorm : ∀ x : X, x ∈ Subgroup.normalizer (N : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top]
    trivial
  set φ₀ : X →* Module.End (ZMod 2) (Additive ↥N) :=
    (conjEndHom N).comp ((MonoidHom.id X).codRestrict (Subgroup.normalizer (N : Set X)) hnorm)
    with hφ₀
  have hφ₀x : ∀ (x : X) (v : Additive ↥N), ((φ₀ x v).toMul : X) = x * (v.toMul : X) * x⁻¹ :=
    fun _ _ => rfl
  have hker : N ≤ φ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine LinearMap.ext fun v => Additive.toMul.injective (Subtype.ext ?_)
    rw [hφ₀x, S.comm_N hx v.toMul.2, mul_inv_cancel_right]
    rfl
  set ρ : Representation (ZMod 2) ↥(Sz a) (Additive ↥N) :=
    (QuotientGroup.lift N φ₀ hker).comp e.symm.toMonoidHom with hρ
  have hρx : ∀ x : X, ρ (e (QuotientGroup.mk' N x)) = φ₀ x := by
    intro x
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  have hsurj : ∀ y : ↥(Sz a), ∃ p : X, e (QuotientGroup.mk' N p) = y := fun y => by
    obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective N (e.symm y)
    exact ⟨p, by rw [hp, MulEquiv.apply_symm_apply]⟩
  have hfpf' : ∃ g : ↥(Sz a), orderOf g = 5 ∧ ∀ v, ρ g v = v → v = 0 := by
    obtain ⟨g, hg5, hgfix⟩ := hfpf
    refine ⟨e (QuotientGroup.mk' N g), hg5, fun v hv => ?_⟩
    rw [hρx] at hv
    have h' := congrArg (fun w : Additive ↥N => ((w.toMul : ↥N) : X)) hv
    simp only [hφ₀x] at h'
    have hc : g * (v.toMul : X) = (v.toMul : X) * g := by
      calc g * (v.toMul : X) = g * v.toMul * g⁻¹ * g := by group
        _ = (v.toMul : X) * g := by rw [h']
    exact Additive.toMul.injective (Subtype.ext (hgfix _ v.toMul.2 hc))
  choose xb hxbR hxb using fun b : F a => (hRg (g₀ * rootSz a 0 b * g₀⁻¹)).mpr ⟨b, rfl⟩
  let c : F a → F a → Additive ↥N := fun b b' =>
    Additive.ofMul ⟨xb b * xb b' * (xb b)⁻¹ * (xb b')⁻¹, S.comm_mem_N (hxbR b) (hxbR b')⟩
  have hcv : ∀ b b', ((c b b').toMul : X) = xb b * xb b' * (xb b)⁻¹ * (xb b')⁻¹ :=
    fun _ _ => rfl
  have hmk : ∀ b b', QuotientGroup.mk' N (xb (b + b')) = QuotientGroup.mk' N (xb b * xb b') := by
    intro b b'
    apply e.injective
    calc e (QuotientGroup.mk' N (xb (b + b'))) = g₀ * rootSz a 0 (b + b') * g₀⁻¹ := hxb _
      _ = g₀ * (rootSz a 0 b * rootSz a 0 b') * g₀⁻¹ := by rw [hadd]
      _ = (g₀ * rootSz a 0 b * g₀⁻¹) * (g₀ * rootSz a 0 b' * g₀⁻¹) := by group
      _ = e (QuotientGroup.mk' N (xb b * xb b')) := by rw [map_mul, map_mul, hxb, hxb]
  have h₁ : ∀ b b' b'', c (b + b') b'' = c b b'' + c b' b'' := by
    intro b b' b''
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [hcv, toMul_add, Subgroup.coe_mul]
    have hm : (xb (b + b'))⁻¹ * (xb b * xb b') ∈ L :=
      S.mul_mem_L_of_mk_eq (hxbR _) (R.mul_mem (hxbR b) (hxbR b')) (hmk b b')
    have e1 := S.comm_eq_of_mul_mem_L (hxbR (b + b')) (hxbR b'') hm
      (show (xb b'')⁻¹ * xb b'' ∈ L by simp)
    rw [← e1]
    exact S.comm_mul_left (hxbR b) (hxbR b') (hxbR b'')
  have h₂ : ∀ b b' b'', c b (b' + b'') = c b b' + c b b'' := by
    intro b b' b''
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [hcv, toMul_add, Subgroup.coe_mul]
    have hm : (xb (b' + b''))⁻¹ * (xb b' * xb b'') ∈ L :=
      S.mul_mem_L_of_mk_eq (hxbR _) (R.mul_mem (hxbR b') (hxbR b'')) (hmk b' b'')
    have e1 := S.comm_eq_of_mul_mem_L (hxbR b) (hxbR (b' + b''))
      (show (xb b)⁻¹ * xb b ∈ L by simp) hm
    rw [← e1]
    exact S.comm_mul_right (hxbR b) (hxbR b') (hxbR b'')
  have halt : ∀ b, c b b = 0 := by
    intro b
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hcv]
    show xb b * xb b * (xb b)⁻¹ * (xb b)⁻¹ = 1
    group
  have hS : ∀ α β b b', ρ (g₀ * rootSz a α β * g₀⁻¹) (c b b') = c b b' := by
    intro α β b b'
    obtain ⟨p, hp⟩ := hsurj (g₀ * rootSz a α β * g₀⁻¹)
    rw [← hp, hρx]
    have hpc : ∀ r ∈ R, QuotientGroup.mk' N p * QuotientGroup.mk' N r =
        QuotientGroup.mk' N r * QuotientGroup.mk' N p := by
      intro r hr
      obtain ⟨b₁, hb₁⟩ := (hRg _).mp ⟨r, hr, rfl⟩
      apply e.injective
      rw [map_mul, map_mul, hp, hb₁]
      calc g₀ * rootSz a α β * g₀⁻¹ * (g₀ * rootSz a 0 b₁ * g₀⁻¹)
          = g₀ * (rootSz a α β * rootSz a 0 b₁) * g₀⁻¹ := by group
        _ = g₀ * (rootSz a 0 b₁ * rootSz a α β) * g₀⁻¹ := by rw [hcent]
        _ = g₀ * rootSz a 0 b₁ * g₀⁻¹ * (g₀ * rootSz a α β * g₀⁻¹) := by group
    have hconj : ∀ r ∈ R, r⁻¹ * (p * r * p⁻¹) ∈ L := by
      intro r hr
      have hl := S.comm_mem_L_of_image_centralizes hpc hr
      have hcen := S.L_cent _ hl r hr
      have : r⁻¹ * (p * r * p⁻¹) = p * r * p⁻¹ * r⁻¹ := by
        calc r⁻¹ * (p * r * p⁻¹) = r⁻¹ * ((p * r * p⁻¹ * r⁻¹) * r) := by group
          _ = r⁻¹ * (r * (p * r * p⁻¹ * r⁻¹)) := by rw [hcen]
          _ = p * r * p⁻¹ * r⁻¹ := by group
      rwa [this]
    apply Additive.toMul.injective
    apply Subtype.ext
    show p * ((c b b').toMul : X) * p⁻¹ = ((c b b').toMul : X)
    rw [hcv]
    have := S.comm_eq_of_mul_mem_L (hxbR b) (hxbR b') (hconj _ (hxbR b)) (hconj _ (hxbR b'))
    exact (by group : p * (xb b * xb b' * (xb b)⁻¹ * (xb b')⁻¹) * p⁻¹ =
      p * xb b * p⁻¹ * (p * xb b' * p⁻¹) * (p * xb b * p⁻¹)⁻¹ * (p * xb b' * p⁻¹)⁻¹).trans this
  have hmem : ∀ y : X ⧸ N, y ∈ R.map (QuotientGroup.mk' N) ↔
      ∃ b : F a, e y = g₀ * rootSz a 0 b * g₀⁻¹ := by
    intro y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (hRg _).mp ⟨r, hr, rfl⟩
    · rintro ⟨b, hb⟩
      obtain ⟨r, hr, hre⟩ := (hRg _).mpr ⟨b, hb⟩
      exact ⟨r, hr, e.injective (by rw [hre])⟩
  have hT : ∀ (x : (F a)ˣ) b b', ρ (g₀ * torusSz a x * g₀⁻¹) (c b b') =
      c ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) ((x : F a) ^ (1 + 2 ^ (a + 1)) * b') := by
    intro x b b'
    obtain ⟨τ, hτ⟩ := hsurj (g₀ * torusSz a x * g₀⁻¹)
    have hτn : τ ∈ Subgroup.normalizer (R : Set X) := by
      apply S.mem_normalizer_of_image
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hmem, hmem, map_mul, map_mul, map_inv, hτ]
      constructor
      · rintro ⟨b₁, hb₁⟩
        refine ⟨(x : F a) ^ (1 + 2 ^ (a + 1)) * b₁, ?_⟩
        rw [hb₁, ← htor x b₁]
        group
      · rintro ⟨b₁, hb₁⟩
        refine ⟨((x⁻¹ : (F a)ˣ) : F a) ^ (1 + 2 ^ (a + 1)) * b₁, ?_⟩
        rw [← htor x⁻¹ b₁, torusSz_inv]
        have h2 : e y = (g₀ * torusSz a x * g₀⁻¹)⁻¹ *
            (g₀ * torusSz a x * g₀⁻¹ * e y * (g₀ * torusSz a x * g₀⁻¹)⁻¹) *
              (g₀ * torusSz a x * g₀⁻¹) := by group
        rw [h2, hb₁]
        group
    have hτR : ∀ b, τ * xb b * τ⁻¹ ∈ R := fun b =>
      (Subgroup.mem_normalizer_iff.mp hτn (xb b)).mp (hxbR b)
    have hsame : ∀ b, (xb ((x : F a) ^ (1 + 2 ^ (a + 1)) * b))⁻¹ * (τ * xb b * τ⁻¹) ∈ L := by
      intro b
      refine S.mul_mem_L_of_mk_eq (hxbR _) (hτR b) (e.injective ?_)
      simp only [map_mul, map_inv, hτ, hxb]
      rw [← htor x b]
      group
    rw [← hτ, hρx]
    apply Additive.toMul.injective
    apply Subtype.ext
    show τ * ((c b b').toMul : X) * τ⁻¹ = (((c _ _).toMul : ↥N) : X)
    rw [hcv, hcv]
    have := S.comm_eq_of_mul_mem_L (hxbR ((x : F a) ^ (1 + 2 ^ (a + 1)) * b))
      (hxbR ((x : F a) ^ (1 + 2 ^ (a + 1)) * b')) (hsame b) (hsame b')
    exact (by group : τ * (xb b * xb b' * (xb b)⁻¹ * (xb b')⁻¹) * τ⁻¹ =
      τ * xb b * τ⁻¹ * (τ * xb b' * τ⁻¹) * (τ * xb b * τ⁻¹)⁻¹ * (τ * xb b' * τ⁻¹)⁻¹).trans this
  have hzero := hW a ha g₀ (Additive ↥N) ρ hfpf' c h₁ h₂ halt hS hT
  intro r hr s hs
  obtain ⟨b, hb⟩ := (hRg _).mp ⟨r, hr, rfl⟩
  obtain ⟨b', hb'⟩ := (hRg _).mp ⟨s, hs, rfl⟩
  have hr' : (xb b)⁻¹ * r ∈ L :=
    S.mul_mem_L_of_mk_eq (hxbR b) hr (e.injective (by rw [hxb, ← hb]))
  have hs' : (xb b')⁻¹ * s ∈ L :=
    S.mul_mem_L_of_mk_eq (hxbR b') hs (e.injective (by rw [hxb, ← hb']))
  have h1 := S.comm_eq_of_mul_mem_L (hxbR b) (hxbR b') hr' hs'
  have h0 : xb b * xb b' * (xb b)⁻¹ * (xb b')⁻¹ = 1 := by
    have := congrArg (fun w : Additive ↥N => ((w.toMul : ↥N) : X)) (hzero b b')
    simpa [hcv] using this
  rw [h0] at h1
  exact mul_comm_of_commutator_eq_one h1

end Prop18Setup

theorem lemma18SzAbelian_of_facts (hW : SzCommutatorWeight)
    (hadd : ∀ (a : ℕ) (b b' : F a), rootSz a 0 b * rootSz a 0 b' = rootSz a 0 (b + b'))
    (hcent : ∀ (a : ℕ) (α β b : F a),
      rootSz a α β * rootSz a 0 b = rootSz a 0 b * rootSz a α β)
    (htor : ∀ (a : ℕ) (x : (F a)ˣ) (b : F a), torusSz a x * rootSz a 0 b * (torusSz a x)⁻¹ =
      rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1)) * b))
    (hF1 : ∀ {a : ℕ}, 1 ≤ a → ∀ E : Subgroup ↥(Sz a), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card ↥E = 2 ^ (2 * a + 1) →
      ∃ g₀ : ↥(Sz a), ∀ y : ↥(Sz a), y ∈ E ↔ ∃ b : F a, y = g₀ * rootSz a 0 b * g₀⁻¹) :
    ∀ (X : Type) [Group X] [Finite X] (R Rb L Lb N : Subgroup X), Prop18Setup R Rb L Lb N →
      ∀ [N.Normal], (∃ a : ℕ, 1 ≤ a ∧ L.relIndex R = 2 ^ (2 * a + 1) ∧
        Nonempty (X ⧸ N ≃* Sz a)) → ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  intro X _ _ R Rb L Lb N S _ hsz r hr s hs
  obtain ⟨a, ha, hrel, ⟨e⟩⟩ := hsz
  let ψR : ↥R →* ↥(Sz a) := (e.toMonoidHom.comp (QuotientGroup.mk' N)).comp R.subtype
  have hker : ψR.ker = L.subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show e (QuotientGroup.mk' N (x : X)) = 1 ↔ (x : X) ∈ L
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hxN
      have : (x : X) ∈ R ⊓ N := Subgroup.mem_inf.mpr ⟨x.2, hxN⟩
      rwa [S.inf_N] at this
    · exact fun hxL => S.L_le_N hxL
  have hE : ∀ y : ↥(Sz a), y ∈ ψR.range ↔ ∃ r ∈ R, e (QuotientGroup.mk' N r) = y := by
    intro y
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨⟨r, hr⟩, rfl⟩
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  have hc : ∀ x ∈ ψR.range, ∀ y ∈ ψR.range, x * y = y * x := by
    intro x hx y hy
    obtain ⟨r, hr, rfl⟩ := (hE x).mp hx
    obtain ⟨s, hs, rfl⟩ := (hE y).mp hy
    have hmk : QuotientGroup.mk' N (r * s) = QuotientGroup.mk' N (s * r) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := S.L_le_N (S.comm_R s⁻¹ (R.inv_mem hs) r⁻¹ (R.inv_mem hr))
      simpa [mul_inv_rev, mul_assoc] using this
    calc e (QuotientGroup.mk' N r) * e (QuotientGroup.mk' N s)
        = e (QuotientGroup.mk' N (r * s)) := by simp [map_mul]
      _ = e (QuotientGroup.mk' N (s * r)) := by rw [hmk]
      _ = e (QuotientGroup.mk' N s) * e (QuotientGroup.mk' N r) := by simp [map_mul]
  have hsq : ∀ x ∈ ψR.range, x * x = 1 := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (hE x).mp hx
    rw [← map_mul, ← map_mul, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact S.L_le_N (S.sq_R r hr)
  have hcard : Nat.card ψR.range = 2 ^ (2 * a + 1) := by
    rw [← hrel, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψR).toEquiv, hker]
    rfl
  obtain ⟨g₀, hg₀⟩ := hF1 ha ψR.range hc hsq hcard
  have hRg : ∀ y : ↥(Sz a), (∃ r ∈ R, e (QuotientGroup.mk' N r) = y) ↔
      ∃ b : F a, y = g₀ * rootSz a 0 b * g₀⁻¹ := fun y => by rw [← hE, hg₀]
  obtain ⟨a₁, -, b₁, -, -, -, hord, hfix⟩ := S.exists_fpf_five ha e
  exact Prop18Setup.abelian_of_weight_data S hW ha e g₀ hRg (hadd a) (hcent a) (htor a)
    ⟨a₁ * b₁, hord, hfix⟩ r hr s hs

end CFSG.CGT.PushingUpLit.SolKNA
